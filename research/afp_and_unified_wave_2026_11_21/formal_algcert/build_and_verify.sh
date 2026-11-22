#!/usr/bin/env bash
# End-to-end overlay Lean 4.35.0 + Rust verifier for:
#   - /Users/ember/dev/minidregg/Compiler/Tower256AlgebraicCert.lean
#   - /Users/ember/dev/minidregg/Compiler/Tower256AlgebraicCertConformance.lean
#   - /Users/ember/dev/minidregg/prover/testdata/tower256_algebraic_cert_conformance.json
#   - /Users/ember/dev/minidregg/prover/src/tower256_algebraic_cert.rs
#   - /Users/ember/dev/minidregg/prover/tests/tower256_algebraic_cert.rs
#
# Never runs `lake build` in /Users/ember/dev/minidregg; compiles .olean/.ilean/.ir into ./build/.
# Pass `--lean-only` to run only the Lean + import-boundary verification and JSON conformance emission.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"
LEANC_BIN="$TOOLCHAIN_DIR/bin/leanc"
LEAN_ONLY=0
if [[ "${1:-}" == "--lean-only" ]]; then
  LEAN_ONLY=1
fi

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$LEANC_BIN" "$LAKE_BIN" <<'PY'
import concurrent.futures, json, os, re, subprocess, sys, time

formal, minidregg, lean_bin, leanc_bin, lake_bin = sys.argv[1:6]
build = os.path.join(formal, "build")
dep_cwd = os.path.join(formal, "build", "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")
dynlib = os.path.join(minidregg, ".lake", "native", "libmini_kernels_lean.so")

target_mods = [
    ("Compiler", "Compiler/Tower256AlgebraicCert.lean", "Compiler.Tower256AlgebraicCert"),
    ("Compiler", "Compiler/Tower256AlgebraicCertConformance.lean", "Compiler.Tower256AlgebraicCertConformance"),
]

# 1. Verify forbidden-token hygiene (ATLAS laws)
for _, rel, _ in target_mods:
    p = os.path.join(minidregg, rel)
    if not os.path.exists(p):
        print(f"FAIL: missing target file {p}", file=sys.stderr)
        sys.exit(1)
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
    pins = len(re.findall(r"#guard_msgs[^\n]*#print\s+axioms", text))
    if pins == 0:
        print(f"FAIL: missing #guard_msgs-pinned #print axioms in {rel}", file=sys.stderr)
        sys.exit(1)
    print(f"OK: ATLAS syntax check for {rel} (0 sorry, 0 axiom, 0 native_decide, 0 #guard; {pins} #print axioms pins)")

# 2. Check import boundary on target module and across minidregg
sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports

ALLOWED = {
    "Theory":    {"Mathlib", "Lean", "Std", "Theory"},
    "Selvage":   {"Mathlib", "Theory", "Selvage"},
    "Effects":   {"Mathlib", "Lean", "Theory", "Effects"},
    "Pred":      {"Mathlib", "Theory", "Pred"},
    "Kernel":    {"Mathlib", "Lean", "Std", "Init", "Theory", "Effects", "Pred", "Compiler", "Kernel"},
    "Compiler":  {"Mathlib", "Lean", "Std", "Init", "Theory", "Effects", "Pred", "Kernel", "Selvage", "Assurance", "Compiler"},
    "Assurance": {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"},
    "Host":      {"Mathlib", "Lean", "Std", "Theory", "Pred", "Kernel", "Compiler", "Host"},
}
for lib, rel, _ in target_mods:
    with open(os.path.join(minidregg, rel), encoding="utf-8") as f:
        t = f.read()
    for imp in header_imports(t):
        parts = imp.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        if tgt not in ALLOWED[lib]:
            print(f"FAIL: import-boundary violation in {rel}: import {imp} ({lib} -> {tgt})", file=sys.stderr)
            sys.exit(1)

ib = subprocess.run(["bash", os.path.join(minidregg, "scripts", "check-import-boundary.sh")],
                    cwd=minidregg, capture_output=True, text=True)
if ib.returncode != 0:
    print(f"FAIL: scripts/check-import-boundary.sh failed:\n{ib.stdout}\n{ib.stderr}", file=sys.stderr)
    sys.exit(1)
print("OK: scripts/check-import-boundary.sh passed")

# 3. Symlink valid Lean-4.35.0 prebuilt .olean/.ilean/.ir artifacts into ./build/
EXPECTED_MAGIC = b"olean\x02\x014.35.0"

def is_435_olean(path):
    try:
        with open(path, "rb") as f:
            return f.read(len(EXPECTED_MAGIC)) == EXPECTED_MAGIC
    except OSError:
        return False

target_stems = {rel[:-5] for _, rel, _ in target_mods}
target_mod_names = {m for _, _, m in target_mods}
os.makedirs(build, exist_ok=True)
if os.path.isdir(minidregg_lib):
    for root, _, files in os.walk(minidregg_lib):
        rel_dir = os.path.relpath(root, minidregg_lib)
        dst_dir = os.path.join(build, rel_dir) if rel_dir != "." else build
        os.makedirs(dst_dir, exist_ok=True)
        valid_base_fns = {
            fn[:-6] for fn in files
            if fn.endswith(".olean") and is_435_olean(os.path.join(root, fn))
        }
        for fn in files:
            if not (".olean" in fn or fn.endswith(".ilean") or ".ir" in fn):
                continue
            base_fn = fn.split(".")[0]
            if base_fn not in valid_base_fns:
                continue
            stem = os.path.join(rel_dir, base_fn) if rel_dir != "." else base_fn
            if stem in target_stems:
                continue
            dst = os.path.join(dst_dir, fn)
            if not os.path.exists(dst):
                os.symlink(os.path.join(root, fn), dst)

pkg_path = subprocess.check_output(
    [lake_bin, "--dir", minidregg, "env", "printenv", "LEAN_PATH"],
    text=True
).strip()
parts = [p for p in pkg_path.split(":") if not p.startswith(minidregg)]
lean_path = build + ":" + ":".join(parts)
env = os.environ.copy()
env["LEAN_PATH"] = lean_path

IMPORT_RE = re.compile(r"^\s*(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", re.M)
LOCAL_ROOTS = {"Theory", "Selvage", "Assurance", "Compiler", "Kernel", "Pred", "Effects", "Host", "Loom"}

def src_path(mod):
    p = os.path.join(minidregg, *mod.split(".")) + ".lean"
    return p if os.path.exists(p) else None

def get_imports(mod):
    p = src_path(mod)
    if not p:
        return []
    with open(p, encoding="utf-8") as f:
        text = f.read()
    stripped = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
    stripped = re.sub(r"--[^\n]*", "", stripped)
    seen, out = set(), []
    for m in IMPORT_RE.finditer(stripped):
        imp = m.group(1)
        if imp.startswith("Minidregg."):
            imp = imp[len("Minidregg."):]
        if imp.split(".")[0] in LOCAL_ROOTS and imp not in seen:
            seen.add(imp)
            out.append(imp)
    return out

order, vis = [], set()
def dfs(mod):
    if mod in vis:
        return
    vis.add(mod)
    src = src_path(mod)
    if not src:
        return
    out = os.path.join(build, *mod.split(".")) + ".olean"
    c_out = os.path.join(build, *mod.split(".")) + ".c"
    if (mod not in target_mod_names and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)
            and (os.path.islink(out) or os.path.exists(c_out))):
        return
    for imp in get_imports(mod):
        dfs(imp)
    order.append(mod)

for _, _, m in target_mods:
    dfs(m)

t0 = time.time()
lean_opts = []
if os.path.exists(dynlib):
    lean_opts.append(f"--load-dynlib={dynlib}")
lean_opts.extend([
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
])

def run_native_conformance_emitter(conf_c_path):
    ir_md = os.path.join(minidregg, ".lake", "build", "ir")
    pkg_ir = {"minidregg": ir_md}
    for p in parts:
        if p.endswith("/lib/lean"):
            ir_dir = p[:-len("/lib/lean")] + "/ir"
            pkg_name = os.path.basename(os.path.dirname(os.path.dirname(os.path.dirname(ir_dir))))
            if os.path.isdir(ir_dir):
                pkg_ir[pkg_name] = ir_dir
    obj_dir = os.path.join(build, "_c_obj")
    os.makedirs(obj_dir, exist_ok=True)
    seen, c_list = set(), []
    local_prefixes = tuple(r + "_" for r in LOCAL_ROOTS)
    builtin_mods = {"Init", "Std", "Lean", "Lake"}

    def unmangle_rel(s):
        return re.sub(r"(?<!_)_(?!_)", "/", s).replace("__", "_") + ".c"

    def resolve_init_c(init_name):
        if init_name in builtin_mods or init_name.split("_")[0] in builtin_mods:
            return None
        for pkg, ir_dir in pkg_ir.items():
            pref = pkg + "_"
            if init_name.startswith(pref):
                rel = unmangle_rel(init_name[len(pref):])
                search_dirs = (build, ir_dir) if pkg == "minidregg" else (ir_dir,)
                for base_dir in search_dirs:
                    cand = os.path.join(base_dir, rel)
                    if os.path.exists(cand):
                        return cand
        if init_name.startswith(local_prefixes):
            rel = unmangle_rel(init_name)
            for base_dir in (build, ir_md):
                cand = os.path.join(base_dir, rel)
                if os.path.exists(cand):
                    return cand
        return None

    # Iterative DFS over the exact `initialize_*` graph (avoids Python recursion limit on Mathlib)
    stack = [(conf_c_path, False)]
    while stack:
        c_path, expanded = stack.pop()
        if expanded:
            c_list.append(c_path)
            continue
        if c_path in seen or not os.path.exists(c_path):
            continue
        seen.add(c_path)
        stack.append((c_path, True))
        with open(c_path, encoding="utf-8") as f:
            txt = f.read()
        for m in re.findall(r"lean_object\*\s+initialize_([A-Za-z0-9_]+)\(uint8_t", txt):
            dep_c = resolve_init_c(m)
            if dep_c and dep_c not in seen:
                stack.append((dep_c, False))

    def compile_one(c_src):
        rel = os.path.relpath(c_src, "/")
        o_dst = os.path.join(obj_dir, rel.replace("/", "__") + ".o")
        if not os.path.exists(o_dst) or os.path.getmtime(o_dst) < os.path.getmtime(c_src):
            subprocess.run([leanc_bin, "-O2", "-fPIC", "-c", c_src, "-o", o_dst], check=True)
        return o_dst

    t_c = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as ex:
        objs = list(ex.map(compile_one, c_list))

    lean_o = os.path.join(minidregg, ".lake", "native", "mini_kernels_lean.o")
    static_a = os.path.join(minidregg, ".lake", "native", "libmini_kernels.a")
    exe_out = os.path.join(build, "emit_algcert_conformance")
    subprocess.run([leanc_bin, "-O2", *objs, lean_o, static_a, "-o", exe_out], check=True)
    t_run = time.time()
    subprocess.run([exe_out], cwd=minidregg, check=True)
    print(
        f"  [NATIVE   {time.time() - t_c:5.2f}s build / {time.time() - t_run:5.2f}s exec] "
        f"emit_algcert_conformance ({len(objs)} C units, 0 stubs)",
        flush=True
    )

for mod in order:
    src = src_path(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    c_out = os.path.join(build, *mod.split(".")) + ".c"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_target = mod in target_mod_names
    if (os.path.exists(out) and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)
            and (os.path.islink(out) or (os.path.exists(c_out) and os.path.getmtime(c_out) >= os.path.getmtime(src)))):
        if is_target:
            print(f"  [CACHED    0.00s] {mod} -> up-to-date 4.35.0 .olean + .c", flush=True)
        continue
    if is_target and os.path.islink(out):
        os.unlink(out)
    t1 = time.time()
    run_cwd = minidregg if is_target else dep_cwd
    cmd = [lean_bin, *lean_opts, "-R", minidregg, "-o", out, "-c", c_out, src]
    res = subprocess.run(cmd, cwd=run_cwd, env=env, capture_output=True, text=True)
    dt = time.time() - t1
    tag = "TARGET" if is_target else "DEP"
    print(f"  [{tag:8s} {dt:5.2f}s] {mod} -> rc={res.returncode}", flush=True)
    if (is_target or res.returncode != 0) and res.stdout.strip():
        print(res.stdout.rstrip(), flush=True)
    if res.stderr.strip():
        print(res.stderr.rstrip(), flush=True)
    if res.returncode != 0:
        sys.exit(1)
    if is_target and ("warning:" in res.stdout or "warning:" in res.stderr):
        print(f"FAIL: compiler warning emitted while building {mod}", file=sys.stderr)
        sys.exit(1)

conf_c = os.path.join(build, "Compiler", "Tower256AlgebraicCertConformance.c")
run_native_conformance_emitter(conf_c)

jf = os.path.join(minidregg, "prover", "testdata", "tower256_algebraic_cert_conformance.json")
if not os.path.exists(jf):
    print(f"FAIL: missing emitted conformance vector {jf}", file=sys.stderr)
    sys.exit(1)
with open(jf, encoding="utf-8") as f:
    data = json.load(f)
assert len(data.get("vectors", [])) >= 4, "expected at least 4 conformance vectors"
print(f"OK: Lean 4.35.0 kernel-verified {len(target_mods)} target module(s) & emitted {len(data['vectors'])} conformance vectors in {time.time() - t0:.2f}s")
PY

if [[ "$LEAN_ONLY" -eq 1 ]]; then
  exit 0
fi

echo "==> Running native Rust algebraic certificate prover, conformance, UD-100 bench & zero-byte-leakage tests..."
export CARGO_TARGET_DIR="/Users/ember/dev/minidregg/prover/target-algcert"
cargo test --release --manifest-path "$MINIDREGG/prover/Cargo.toml" --lib tower256_algebraic_cert
cargo test --release --manifest-path "$MINIDREGG/prover/Cargo.toml" --test tower256_algebraic_cert -- --nocapture
echo "OK: Full Lean + Rust algebraic zerocheck + LogUp256 verification & zero-byte-leakage audit suite passed."
