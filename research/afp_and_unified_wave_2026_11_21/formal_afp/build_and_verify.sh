#!/usr/bin/env bash
# Overlay Lean 4.35.0 verifier for AFP-grade wave deliverables:
#   - Theory/SumcheckHvzkMask.lean
#   - Selvage/WhirMultiRoundSoundness.lean
# Compiles .olean/.ir artifacts into ./build/ without running `lake build` in /Users/ember/dev/minidregg,
# verifies 0 sorry / 0 custom axiom / 0 native_decide / 0 #guard / 0 compiler warnings (-DwarningAsError=true),
# nested-comment-safe lexing, #assert_axioms & #guard_msgs-pinned #print axioms (standard-3 subset check),
# explicit per-tier import boundaries, and check-import-boundary.sh.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"
DYNLIB="$MINIDREGG/.lake/native/libmini_kernels_lean.so"

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$LAKE_BIN" "$DYNLIB" <<'PY'
import os, re, subprocess, sys, time

formal, minidregg, lean_bin, lake_bin, dynlib = sys.argv[1:6]
build = os.path.join(formal, "build")
dep_cwd = os.path.join(formal, "build", "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")

sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports

ALLOWED = {
    "Theory":  {"Mathlib", "Lean", "Std", "Theory"},
    "Selvage": {"Mathlib", "Theory", "Selvage"},
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def strip_lean_comments_and_strings(src: str) -> str:
    """State-machine lexer handling nested /- ... -/ comments, -- line comments, and strings."""
    out = []
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if in_str:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
                continue
            if ch == '"':
                in_str = False
            out.append(" " if ch != "\n" else "\n")
            i += 1
        elif depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        else:
            if ch == "/" and nxt == "-":
                depth = 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "-":
                while i < n and src[i] != "\n":
                    out.append(" ")
                    i += 1
            elif ch == '"':
                in_str = True
                out.append(" ")
                i += 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)

target_mods = [
    ("Theory",  "Theory/SumcheckHvzkMask.lean",         "Theory.SumcheckHvzkMask"),
    ("Selvage", "Selvage/WhirMultiRoundSoundness.lean", "Selvage.WhirMultiRoundSoundness"),
]

# 1. Verify forbidden-token hygiene (ATLAS laws), standard-axiom pins & untracked import boundary
GUARD_PRINT_RE = re.compile(
    r"/\-\-\s*info:\s*'[^']+'\s*(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*\-/\s*"
    r"#guard_msgs[^\n]*in\s+#print\s+axioms\s+([A-Za-z0-9_.']+)",
    re.S,
)

for lib, rel, _ in target_mods:
    p = os.path.join(minidregg, rel)
    if not os.path.exists(p):
        print(f"FAIL: missing target file {p}", file=sys.stderr)
        sys.exit(1)
    with open(p, encoding="utf-8") as f:
        text = f.read()
    lines = len(text.splitlines())
    for imp in header_imports(text):
        parts = imp.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        if tgt not in ALLOWED[lib]:
            print(f"FAIL: forbidden import `{imp}` in {rel} (tier {lib})", file=sys.stderr)
            sys.exit(1)
    stripped = strip_lean_comments_and_strings(text)
    for pat, label in [
        (r"\bsorry\b", "sorry"),
        (r"\baxiom\b", "custom axiom"),
        (r"\bnative_decide\b", "native_decide"),
        (r"#guard\b(?!_msgs)", "#guard unit test"),
    ]:
        if re.search(pat, stripped):
            print(f"FAIL: forbidden `{label}` found in {rel}", file=sys.stderr)
            sys.exit(1)
    assert_pins = len(re.findall(r"#assert_axioms\b", stripped))
    guard_matches = list(GUARD_PRINT_RE.finditer(text))
    if assert_pins == 0 or len(guard_matches) == 0:
        print(f"FAIL: missing #assert_axioms or #guard_msgs #print axioms pins in {rel}", file=sys.stderr)
        sys.exit(1)
    for m in guard_matches:
        ax_raw, thm_name = m.group(1), m.group(2)
        if ax_raw is not None:
            axs = {a.strip() for a in ax_raw.split(",") if a.strip()}
            bad_ax = axs - STANDARD_AXIOMS
            if bad_ax:
                print(f"FAIL: non-standard axiom {bad_ax} pinned on {thm_name} in {rel}", file=sys.stderr)
                sys.exit(1)
    print(f"OK: ATLAS & tier-import check for {rel} ({lines} lines; 0 sorry, 0 axiom, 0 native_decide, 0 #guard; {assert_pins} #assert_axioms, {len(guard_matches)} #print axioms pins)")

# 2. Run minidregg/scripts/check-import-boundary.sh
ib = subprocess.run(["bash", os.path.join(minidregg, "scripts", "check-import-boundary.sh")],
                    cwd=minidregg, capture_output=True, text=True)
if ib.returncode != 0:
    print(f"FAIL: check-import-boundary.sh failed:\n{ib.stdout}\n{ib.stderr}", file=sys.stderr)
    sys.exit(1)
print("OK: scripts/check-import-boundary.sh passed (rc=0)")

# 3. Overlay symlink Lean-4.35.0-compatible prebuilt .olean/.ilean/.ir artifacts into ./build/
EXPECTED_MAGIC = b"olean\x02\x014.35.0"

def is_435_olean(path):
    try:
        with open(path, "rb") as f:
            return f.read(len(EXPECTED_MAGIC)) == EXPECTED_MAGIC
    except OSError:
        return False

if os.path.isdir(build):
    bad_stems = set()
    for root, _, files in os.walk(build):
        for fn in files:
            p = os.path.join(root, fn)
            if fn.endswith(".olean") and os.path.islink(p) and not is_435_olean(p):
                bad_stems.add(os.path.join(root, fn.split(".")[0]))
    for root, _, files in os.walk(build):
        for fn in files:
            stem = os.path.join(root, fn.split(".")[0])
            p = os.path.join(root, fn)
            if stem in bad_stems and os.path.islink(p):
                os.unlink(p)

target_stems = {rel[:-5] for _, rel, _ in target_mods}
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
    stripped = strip_lean_comments_and_strings(text)
    seen, out = set(), []
    for m in IMPORT_RE.finditer(stripped):
        imp = m.group(1)
        if imp.startswith("Minidregg."):
            imp = imp[len("Minidregg."):]
        if imp.split(".")[0] in LOCAL_ROOTS and imp not in seen:
            seen.add(imp)
            out.append(imp)
    return out

target_mod_names = {m for _, _, m in target_mods}
order, vis = [], set()
def dfs(mod):
    if mod in vis:
        return
    vis.add(mod)
    src = src_path(mod)
    if not src:
        return
    out = os.path.join(build, *mod.split(".")) + ".olean"
    if (mod not in target_mod_names and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
        return
    for imp in get_imports(mod):
        dfs(imp)
    order.append(mod)

for _, _, m in target_mods:
    dfs(m)

t0 = time.time()
dep_opts = [
    f"--load-dynlib={dynlib}",
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
]
target_opts = [
    f"--load-dynlib={dynlib}",
    "-DwarningAsError=true",
]
failed = False
for mod in order:
    src = src_path(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_target = mod in target_mod_names
    if (not is_target and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
        continue
    t1 = time.time()
    run_cwd = minidregg if is_target else dep_cwd
    opts = target_opts if is_target else dep_opts
    res = subprocess.run(
        [lean_bin, *opts, "-R", minidregg, "-o", out, src],
        cwd=run_cwd, env=env, capture_output=True, text=True
    )
    dt = time.time() - t1
    tag = "TARGET" if is_target else "DEP"
    print(f"  [{tag:7s} {dt:5.2f}s] {mod} -> rc={res.returncode}", flush=True)
    if (is_target or res.returncode != 0) and res.stdout.strip():
        print(res.stdout.rstrip(), flush=True)
    if res.stderr.strip():
        print(res.stderr.rstrip(), flush=True)
    has_warn = is_target and ("warning:" in res.stdout or bool(res.stderr.strip()))
    if res.returncode != 0 or has_warn:
        failed = True
        break
if failed:
    sys.exit(1)

print(f"OK: Kernel-verified all AFP Lean modules with 0 warnings (-DwarningAsError=true) in {time.time() - t0:.2f}s")
PY
