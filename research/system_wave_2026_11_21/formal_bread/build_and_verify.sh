#!/usr/bin/env bash
# Build and kernel-verify:
#   - Bfv/ScaleLiftRefinement.lean
#   - Bfv.lean (updated to import Bfv.ScaleLiftRefinement before #assert_namespace_axioms Bfv)
#   - Dregg2/Crypto/Deriv/PaddedAbsence.lean
#   - Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean
# against /Users/ember/dev/breadstuffs/metatheory (strictly read-only; all .olean artifacts go into ./build/),
# plus verify zero sorry/axiom/native_decide/#guard, #guard_msgs-pinned #print axioms,
# and clean git apply --check on breadstuffs-holeb-dfa-weld8.patch.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
BREADSTUFFS="/Users/ember/dev/breadstuffs"
METATHEORY="$BREADSTUFFS/metatheory"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"

python3 - "$FORMAL_DIR" "$BREADSTUFFS" "$METATHEORY" "$LEAN_BIN" "$LAKE_BIN" <<'PY'
import concurrent.futures, os, re, subprocess, sys, time

formal, breadstuffs, metatheory, lean_bin, lake_bin = sys.argv[1:6]
build = os.path.join(formal, "build")
meta_lib = os.path.join(metatheory, ".lake", "build", "lib", "lean")
TARGET_VER = "4.35.0"

local_mods = [
    ("Bfv.ScaleLiftRefinement", "Bfv/ScaleLiftRefinement.lean", True),
    ("Bfv", "Bfv.lean", False),
    ("Dregg2.Crypto.Deriv.PaddedAbsence", "Dregg2/Crypto/Deriv/PaddedAbsence.lean", True),
    ("Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure", "Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean", True),
]
local_mod_set = {m for m, _, _ in local_mods}

# 1. Verify forbidden-token hygiene & #guard_msgs #print axioms pins
for mod, rel, require_guard_msgs in local_mods:
    p = os.path.join(formal, rel)
    with open(p, encoding="utf-8") as f:
        text = f.read()
    stripped = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
    stripped = re.sub(r"--[^\n]*", "", stripped)
    for pat, label in [
        (r"\bsorry\b", "sorry"),
        (r"^\s*axiom\b", "custom axiom"),
        (r"\bnative_decide\b", "native_decide"),
        (r"#guard\b(?!_msgs)", "#guard unit test"),
    ]:
        if re.search(pat, stripped, flags=re.M):
            print(f"FAIL: forbidden `{label}` found in {rel}", file=sys.stderr)
            sys.exit(1)
    if require_guard_msgs:
        if "#print axioms" not in text or "#guard_msgs" not in text:
            print(f"FAIL: missing #guard_msgs-pinned #print axioms in {rel}", file=sys.stderr)
            sys.exit(1)
        if "#assert_all_clean" not in text:
            print(f"FAIL: missing #assert_all_clean in {rel}", file=sys.stderr)
            sys.exit(1)
    else:
        if "#assert_namespace_axioms" not in text:
            print(f"FAIL: missing #assert_namespace_axioms in {rel}", file=sys.stderr)
            sys.exit(1)
print("OK: syntax hygiene check (0 sorry, 0 axiom, 0 native_decide, 0 #guard; #print axioms + #assert_all_clean pinned)")

def olean_ver(p):
    if not os.path.exists(p):
        return None
    try:
        with open(p, "rb") as f:
            data = f.read(128)
        m = re.search(rb"4\.\d+\.\d+", data)
        return m.group(0).decode() if m else None
    except OSError:
        return None

def strip_comments(text):
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i:i+2] == "--":
            nl = text.find("\n", i)
            if nl == -1:
                break
            out.append("\n")
            i = nl + 1
        elif text[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and text[i:i+2] == "-/":
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)

def header_imports(path):
    with open(path, encoding="utf-8") as f:
        text = strip_comments(f.read())
    imps = []
    for line in text.splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith("prelude"):
            continue
        if s.startswith("import "):
            parts = s.split()
            # handle `import public Foo` or `import Foo`
            mod = parts[2] if len(parts) >= 3 and parts[1] in {"public", "private", "meta"} else parts[1]
            imps.append(mod)
        else:
            break
    return imps

def src_and_root(mod):
    p = os.path.join(formal, *mod.split(".")) + ".lean"
    if os.path.exists(p):
        return p, formal
    p = os.path.join(metatheory, *mod.split(".")) + ".lean"
    if os.path.exists(p):
        return p, metatheory
    return None, None

# 2. Clean any incompatible-version symlinks in ./build/ and symlink compatible v4.35.0 oleans
os.makedirs(build, exist_ok=True)
for root, _, files in os.walk(build):
    for fn in files:
        p = os.path.join(root, fn)
        if os.path.islink(p):
            if not fn.endswith(".olean") or olean_ver(p) != TARGET_VER:
                os.unlink(p)

local_rel_stems = {rel[:-5] for _, rel, _ in local_mods}
if os.path.isdir(meta_lib):
    for root, _, files in os.walk(meta_lib):
        rel_dir = os.path.relpath(root, meta_lib)
        dst_dir = os.path.join(build, rel_dir) if rel_dir != "." else build
        for fn in files:
            if not fn.endswith(".olean"):
                continue
            src_ol = os.path.join(root, fn)
            if olean_ver(src_ol) != TARGET_VER:
                continue
            base_fn = fn[:-6]
            stem = os.path.join(rel_dir, base_fn) if rel_dir != "." else base_fn
            if stem in local_rel_stems:
                continue
            os.makedirs(dst_dir, exist_ok=True)
            dst = os.path.join(dst_dir, fn)
            if not os.path.exists(dst):
                os.symlink(src_ol, dst)

# 3. Collect transitive dependency DAG for our 4 target modules
deps_map = {}
vis = set()
def dfs(mod):
    if mod in vis:
        return
    vis.add(mod)
    src, _ = src_and_root(mod)
    if not src:
        return
    imps = []
    for imp in header_imports(src):
        s2, _ = src_and_root(imp)
        if s2:
            imps.append(imp)
            dfs(imp)
    deps_map[mod] = imps

for mod, _, _ in local_mods:
    dfs(mod)

pkg_path = subprocess.check_output(
    [lake_bin, "--dir", metatheory, "env", "printenv", "LEAN_PATH"],
    text=True
).strip()
parts = [p for p in pkg_path.split(":") if p and not p.startswith(meta_lib)]
lean_path = build + ":" + ":".join(parts)
env = os.environ.copy()
env["LEAN_PATH"] = lean_path

lean_opts = [
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
]

def needs_build(mod):
    if mod in local_mod_set:
        return True
    src, _ = src_and_root(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    if not os.path.exists(out):
        return True
    if olean_ver(out) != TARGET_VER:
        return True
    if os.path.getmtime(out) < os.path.getmtime(src):
        return True
    return False

# Propagate needs_build upward if any dep needs build
memo_nb = {}
def check_nb(mod):
    if mod in memo_nb:
        return memo_nb[mod]
    nb = needs_build(mod) or any(check_nb(d) for d in deps_map.get(mod, []))
    memo_nb[mod] = nb
    return nb

to_build = {m for m in deps_map if check_nb(m)}
print(f"DAG: {len(deps_map)} modules in cone, {len(to_build)} to compile ({len(local_mod_set)} local + {len(to_build) - len(local_mod_set)} deps into ./build/)", flush=True)

t0 = time.time()
remaining = {m: set(d for d in deps_map[m] if d in to_build) for m in to_build}
rdeps = {m: set() for m in to_build}
for m, ds in remaining.items():
    for d in ds:
        rdeps[d].add(m)

def compile_one(mod):
    src, rdir = src_and_root(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    if os.path.islink(out):
        os.unlink(out)
    t1 = time.time()
    res = subprocess.run([lean_bin, *lean_opts, "-R", rdir, "-o", out, src], env=env, capture_output=True, text=True)
    return mod, res.returncode, time.time() - t1, res.stdout, res.stderr

ready = [m for m, ds in remaining.items() if not ds]
max_workers = min(8, os.cpu_count() or 4)
failed = []
done_count = 0
with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as pool:
    in_flight = {}
    while ready or in_flight:
        while ready and len(in_flight) < max_workers and not failed:
            m = ready.pop(0)
            in_flight[pool.submit(compile_one, m)] = m
        if not in_flight:
            break
        done_futs, _ = concurrent.futures.wait(in_flight, return_when=concurrent.futures.FIRST_COMPLETED)
        for fut in done_futs:
            in_flight.pop(fut)
            mod, rc, dt, out_s, err_s = fut.result()
            done_count += 1
            is_local = mod in local_mod_set
            tag = "LOCAL" if is_local else "DEP  "
            if is_local or rc != 0 or done_count % 20 == 0:
                print(f"  [{tag} {dt:5.2f}s] ({done_count}/{len(to_build)}) {mod} -> rc={rc}", flush=True)
            if out_s.strip() and (is_local or rc != 0):
                print(out_s.rstrip(), flush=True)
            if err_s.strip() and (is_local or rc != 0):
                print(err_s.rstrip(), flush=True)
            if rc != 0:
                failed.append(mod)
            else:
                for nxt in rdeps[mod]:
                    remaining[nxt].discard(mod)
                    if not remaining[nxt]:
                        ready.append(nxt)

if failed:
    print(f"FAIL: {len(failed)} module(s) failed: {failed}", file=sys.stderr)
    sys.exit(1)
print(f"OK: Kernel-verified all {len(local_mods)} local modules cleanly in {time.time() - t0:.2f}s")

# 4. Verify patch applies cleanly to /Users/ember/dev/breadstuffs and target paths are untouched
patch_file = os.path.join(formal, "breadstuffs-holeb-dfa-weld8.patch")
if os.path.exists(patch_file):
    chk = subprocess.run(
        ["git", "-C", breadstuffs, "apply", "--check", patch_file],
        capture_output=True, text=True
    )
    if chk.returncode != 0:
        print(f"FAIL: git apply --check failed:\n{chk.stderr}", file=sys.stderr)
        sys.exit(1)
    print("OK: git -C /Users/ember/dev/breadstuffs apply --check breadstuffs-holeb-dfa-weld8.patch")

    st = subprocess.run(
        ["git", "-C", breadstuffs, "status", "--porcelain",
         "metatheory/Bfv.lean",
         "metatheory/Bfv/ScaleLiftRefinement.lean",
         "metatheory/Dregg2/Crypto/Deriv/PaddedAbsence.lean",
         "metatheory/Dregg2/Circuit/Emit/AttestedAutomatonWeld8Closure.lean"],
        capture_output=True, text=True
    )
    if st.stdout.strip():
        print(f"FAIL: target breadstuffs paths modified:\n{st.stdout}", file=sys.stderr)
        sys.exit(1)
    print("OK: /Users/ember/dev/breadstuffs target paths untouched (read-only discipline verified)")
PY
