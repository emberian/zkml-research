#!/usr/bin/env bash
# End-to-end isolated Lean v4.35.0 overlay + Rust `--release` verifier for Wearable SHE Organ #1:
#   - /Users/ember/dev/minidregg/Selvage/GoldilocksDregg180Bridge.lean
#   - /Users/ember/dev/zkml-research/native/qwen35audit/src/dregg180_hem_bridge.rs
#   - /Users/ember/dev/zkml-research/native/qwen35audit/tests/dregg180_op_hem_vm.rs
#
# NEVER runs `lake build` inside /Users/ember/dev/minidregg; compiles .olean/.ilean into ./build/.
# Pass `--lean-only` to run only the Lean v4.35.0 + ATLAS hygiene + import-boundary verification.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
ZKML_ROOT="/Users/ember/dev/zkml-research"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"
LEAN_ONLY=0
KEEP_ARTIFACTS=0
for arg in "$@"; do
  case "$arg" in
    --lean-only) LEAN_ONLY=1 ;;
    --keep-artifacts) KEEP_ARTIFACTS=1 ;;
  esac
done

rm -rf "$FORMAL_DIR/build"

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$LAKE_BIN" <<'PY'
import os, re, subprocess, sys, time

formal, minidregg, lean_bin, lake_bin = sys.argv[1:5]
build = os.path.join(formal, "build")
dep_cwd = os.path.join(formal, "build", "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")
dynlib = os.path.join(minidregg, ".lake", "native", "libmini_kernels_lean.so")

ver = subprocess.check_output([lean_bin, "--version"], text=True).strip()
if "4.35.0" not in ver:
    print(f"FAIL: expected Lean v4.35.0, got: {ver}", file=sys.stderr)
    sys.exit(1)

sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports, header_layout

ALLOWED = {
    "Selvage": {"Mathlib", "Theory", "Selvage"},
}

target_mods = [
    ("Selvage", "Selvage/GoldilocksDregg180Bridge.lean", "Selvage.GoldilocksDregg180Bridge"),
]

def strip_lean_comments_and_strings(src: str) -> str:
    out = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        if in_str:
            if src[i] == "\\" and i + 1 < n:
                i += 2
                continue
            if src[i] == '"':
                in_str = False
            i += 1
        elif depth > 0:
            if src[i:i+2] == "/-":
                depth += 1
                i += 2
            elif src[i:i+2] == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        else:
            if src[i:i+2] == "/-":
                depth = 1
                i += 2
            elif src[i:i+2] == "--":
                while i < n and src[i] != "\n":
                    i += 1
            elif src[i] == '"':
                in_str = True
                out.append('""')
                i += 1
            else:
                out.append(src[i])
                i += 1
    return "".join(out)

# 1. Verify line count (< 950), ATLAS forbidden-token hygiene & Selvage-tier import boundary
for lib, rel, _ in target_mods:
    p = os.path.join(minidregg, rel)
    if not os.path.exists(p):
        print(f"FAIL: missing target file {p}", file=sys.stderr)
        sys.exit(1)
    with open(p, encoding="utf-8") as f:
        text = f.read()
    lines = text.splitlines()
    if len(lines) >= 950:
        print(f"FAIL: {rel} has {len(lines)} lines (must be < 950)", file=sys.stderr)
        sys.exit(1)
    core_all = [
        m for (s, e, _, m) in header_layout(text)[1]
        if m.startswith("Init.") and text[s:e].split()[-2:-1] == ["all"]
    ]
    for imp in header_imports(text):
        if imp in core_all:
            continue
        parts = imp.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        if tgt not in ALLOWED[lib]:
            print(f"FAIL: import-boundary violation in {rel}: import {imp} ({lib} -> {tgt})", file=sys.stderr)
            sys.exit(1)
    stripped = strip_lean_comments_and_strings(text)
    for pat, label in [
        (r"\bsorry\b", "sorry"),
        (r"\bsorryAx\b", "sorryAx"),
        (r"\badmit\b", "admit"),
        (r"^\s*axiom\b", "custom axiom"),
        (r"\bnative_decide\b", "native_decide"),
        (r"\bunsafe\b", "unsafe"),
        (r"@\[implemented_by", "implemented_by"),
        (r"#guard\b(?!_msgs)", "#guard unit test"),
    ]:
        if re.search(pat, stripped, flags=re.M):
            print(f"FAIL: forbidden `{label}` found in {rel}", file=sys.stderr)
            sys.exit(1)
    pins = len(re.findall(r"#guard_msgs[^\n]*#print\s+axioms", text))
    if pins < 12:
        print(f"FAIL: expected >= 12 #guard_msgs-pinned #print axioms in {rel}, got {pins}", file=sys.stderr)
        sys.exit(1)
    for m in re.finditer(r"/-- info: '([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms) -/\s*\n#guard_msgs", text):
        if m.group(3) is not None:
            ax = {a.strip() for a in m.group(3).split(",")}
            if not ax <= {"propext", "Classical.choice", "Quot.sound"}:
                print(f"FAIL: non-standard axiom pinned for {m.group(1)}: {ax}", file=sys.stderr)
                sys.exit(1)
    print(f"OK: ATLAS & Selvage-tier import check for {rel} ({len(lines)} lines < 950; 0 sorry/axiom/native_decide; {pins} #print axioms pins)")

# 2. Run minidregg/scripts/check-import-boundary.sh (read-only)
ib = subprocess.run(
    ["bash", os.path.join(minidregg, "scripts", "check-import-boundary.sh")],
    cwd=minidregg, capture_output=True, text=True
)
if ib.returncode != 0:
    print(f"FAIL: scripts/check-import-boundary.sh failed:\n{ib.stdout}\n{ib.stderr}", file=sys.stderr)
    sys.exit(1)
print("OK: scripts/check-import-boundary.sh passed")

# 3. Symlink existing Lean-4.35.0 oleans from minidregg/.lake/build/lib/lean into ./build/
#    and build any pre-4.35.0 local dependencies into ./build/ (NEVER touching minidregg/.lake!)
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
env = os.environ.copy()
env["LEAN_PATH"] = build + ":" + ":".join(parts)

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
        t = f.read()
    t = re.sub(r"/\-.*?\-/", "", t, flags=re.S)
    t = re.sub(r"--[^\n]*", "", t)
    seen, out = set(), []
    for m in IMPORT_RE.finditer(t):
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
    if (mod not in target_mod_names and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
        return
    for imp in get_imports(mod):
        dfs(imp)
    order.append(mod)

for _, _, m in target_mods:
    dfs(m)

lean_opts = []
if os.path.exists(dynlib):
    lean_opts.append(f"--load-dynlib={dynlib}")
lean_opts.extend([
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
])

t0 = time.time()
for mod in order:
    src = src_path(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_target = mod in target_mod_names
    if is_target and os.path.exists(out):
        os.unlink(out)
    t1 = time.time()
    run_cwd = minidregg if is_target else dep_cwd
    extra_target_opts = ["-DwarningAsError=true"] if is_target else []
    res = subprocess.run(
        [lean_bin, *lean_opts, *extra_target_opts, "-R", minidregg, "-o", out, src],
        cwd=run_cwd, env=env, capture_output=True, text=True
    )
    dt = time.time() - t1
    tag = "TARGET" if is_target else "DEP"
    print(f"  [{tag:8s} {dt:5.2f}s] {mod} -> rc={res.returncode}", flush=True)
    if (is_target or res.returncode != 0) and res.stdout.strip():
        print(res.stdout.rstrip(), flush=True)
    if res.stderr.strip():
        print(res.stderr.rstrip(), flush=True)
    if res.returncode != 0:
        sys.exit(1)
    if is_target and ("warning:" in res.stdout.lower() or "warning:" in res.stderr.lower()):
        print(f"FAIL: compiler warning emitted while building {mod}", file=sys.stderr)
        sys.exit(1)

print(f"OK: Lean v4.35.0 kernel-verified {len(target_mods)} target module(s) with 0 warnings in {time.time() - t0:.2f}s")
PY

if [[ "$LEAN_ONLY" -eq 1 ]]; then
  if [[ "$KEEP_ARTIFACTS" -eq 0 ]]; then
    rm -rf "$FORMAL_DIR/build"
  fi
  exit 0
fi

echo "==> Running native Rust --release qwen35audit::dregg180_hem_bridge & dregg180_op_hem_vm tests (0 warnings enforced via #![deny(warnings)] + -D warnings)..."
TARGET_DIR="$ZKML_ROOT/native/target-dregg180-hem"
MANIFEST_PATH="$ZKML_ROOT/native/Cargo.toml"
TMP_RUST_OVERLAY=""
cleanup_all() {
  if [[ -n "$TMP_RUST_OVERLAY" && -d "$TMP_RUST_OVERLAY" ]]; then
    rm -rf "$TMP_RUST_OVERLAY"
  fi
  if [[ "$KEEP_ARTIFACTS" -eq 0 ]]; then
    rm -rf "$FORMAL_DIR/build" "$TARGET_DIR"
  fi
}
trap cleanup_all EXIT

if ! CARGO_TARGET_DIR="$TARGET_DIR" cargo check --release --manifest-path "$MANIFEST_PATH" -p qwen35audit --lib >/dev/null 2>&1; then
  ERR_OUT="$(CARGO_TARGET_DIR="$TARGET_DIR" cargo check --release --manifest-path "$MANIFEST_PATH" -p qwen35audit --lib 2>&1 || true)"
  if echo "$ERR_OUT" | grep -q "dregg180_hem_bridge.rs"; then
    echo "$ERR_OUT" >&2
    exit 1
  fi
  echo "    [overlay] Sibling module in qwen35audit mid-edit; verifying dregg180_hem_bridge + dregg180_op_hem_vm in isolated mktemp overlay..."
  TMP_RUST_OVERLAY="$(mktemp -d)"
  cp "$ZKML_ROOT/native/Cargo.lock" "$TMP_RUST_OVERLAY/Cargo.lock"
  cp -R "$ZKML_ROOT/native/qwen35audit/src" "$TMP_RUST_OVERLAY/src"
  mkdir -p "$TMP_RUST_OVERLAY/tests"
  cp "$ZKML_ROOT/native/qwen35audit/tests/dregg180_op_hem_vm.rs" "$TMP_RUST_OVERLAY/tests/dregg180_op_hem_vm.rs"
  printf '// Isolated stub while sibling worker edits live streaming_gdn_carry.rs\n' > "$TMP_RUST_OVERLAY/src/streaming_gdn_carry.rs"
  cp "$ZKML_ROOT/native/qwen35audit/Cargo.toml" "$TMP_RUST_OVERLAY/Cargo.toml"
  MANIFEST_PATH="$TMP_RUST_OVERLAY/Cargo.toml"
fi

CARGO_TARGET_DIR="$TARGET_DIR" \
  cargo rustc --release --manifest-path "$MANIFEST_PATH" \
  -p qwen35audit --lib -- -D warnings
CARGO_TARGET_DIR="$TARGET_DIR" \
  cargo rustc --release --manifest-path "$MANIFEST_PATH" \
  -p qwen35audit --test dregg180_op_hem_vm -- -D warnings
CARGO_TARGET_DIR="$TARGET_DIR" \
  cargo test --release --manifest-path "$MANIFEST_PATH" \
  -p qwen35audit --test dregg180_op_hem_vm -- --nocapture --test-threads=1

echo "OK: Full Lean v4.35.0 GoldilocksDregg180Bridge + native Rust Dregg-180 < 16 KiB OP_FOLD/OP_HEM suite passed."
