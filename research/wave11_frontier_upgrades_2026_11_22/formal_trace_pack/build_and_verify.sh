#!/usr/bin/env bash
# Wave 11 Lane 2: End-to-end overlay Lean 4.35.0 + Rust verifier for Frigo–shelat (`eprint 2026/2770`)
# Trace-Duality 256-Bit Bijective Packing & Additive Hilbert-90 Single-Mask ZK in `Tower256`:
#   - /Users/ember/dev/minidregg/Theory/Tower256TraceBitPacking.lean
#   - /Users/ember/dev/minidregg/prover/testdata/tower256_trace_pack_conformance.json
#   - /Users/ember/dev/minidregg/prover/src/tower256_trace_pack.rs
#   - /Users/ember/dev/minidregg/prover/tests/tower256_trace_packing.rs
#
# Never runs `lake build` in /Users/ember/dev/minidregg; compiles .olean into ./build/.
# Pass `--lean-only` to run only Lean 4.35.0 + import-boundary verification + JSON emission.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"
LEAN_ONLY=0
for arg in "$@"; do
  case "$arg" in
    --lean-only) LEAN_ONLY=1 ;;
    --rebuild-lean) : ;; # Targets are always elaborated to regenerate their vectors.
    *) echo "Unknown option $arg" >&2; exit 2 ;;
  esac
done

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$LAKE_BIN" <<'PY'
import json, os, re, subprocess, sys, time

formal, minidregg, lean_bin, lake_bin = sys.argv[1:5]
build = os.path.join(formal, "build")
dep_cwd = os.path.join(formal, "build", "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")
dynlib = os.path.join(minidregg, ".lake", "native", "libmini_kernels_lean.so")

sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports

ALLOWED = {"Theory": {"Mathlib", "Lean", "Std", "Theory"}}

target_mods = [
    ("Theory", "Theory/Tower256TraceBitPacking.lean", "Theory.Tower256TraceBitPacking"),
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

# 1. Verify ATLAS forbidden-token hygiene, line budget (< 950), & tier import boundary
for lib, rel, _ in target_mods:
    p = os.path.join(minidregg, rel)
    if not os.path.exists(p):
        print(f"FAIL: missing target file {p}", file=sys.stderr)
        sys.exit(1)
    with open(p, encoding="utf-8") as f:
        text = f.read()
    line_count = len(text.splitlines())
    if line_count >= 950:
        print(f"FAIL: {rel} has {line_count} lines (must be < 950)", file=sys.stderr)
        sys.exit(1)
    for imp in header_imports(text):
        parts = imp.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        if tgt not in ALLOWED[lib]:
            print(f"FAIL: import-boundary violation in {rel}: import {imp} ({lib} -> {tgt})", file=sys.stderr)
            sys.exit(1)
    stripped = strip_lean_comments_and_strings(text)
    for pat, label in [
        (r"\bsorry\b", "sorry"),
        (r"\bsorryAx\b", "sorryAx"),
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
    print(f"OK: ATLAS & tier-import check for {rel} ({line_count} lines < 950; 0 sorry, 0 axiom, 0 native_decide; {pins} #print axioms pins)")

# 2. Run minidregg/scripts/check-import-boundary.sh
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
    if (mod not in target_mod_names and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
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

for mod in order:
    src = src_path(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_target = mod in target_mod_names
    if (not is_target and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
        continue
    # Dependencies may have been symlinked from the shared mini cache. Detach
    # the overlay links before emitting any compiler sidecars at this stem.
    import glob
    for cached in glob.glob(out[:-6] + ".*"):
        if os.path.islink(cached):
            os.unlink(cached)
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
    if is_target and ("warning:" in res.stdout or "warning:" in res.stderr):
        print(f"FAIL: compiler warning emitted while building {mod}", file=sys.stderr)
        sys.exit(1)

jf = os.path.join(minidregg, "prover", "testdata", "tower256_trace_pack_conformance.json")
if not os.path.exists(jf):
    print(f"FAIL: missing emitted conformance vector {jf}", file=sys.stderr)
    sys.exit(1)
with open(jf, encoding="utf-8") as f:
    data = json.load(f)
assert data["schema"] == "minidregg.tower256_trace_pack_conformance.v1"
checks = data["lean_self_checks"]
assert set(checks) == {"trace_mask_ok", "rho_trace_one", "top_monomial_trace_zero", "dual_basis_ok", "artin_schreier_ok", "tensor_z0_ok", "tensor_z128_ok"} and all(value is True for value in checks.values()), f"Lean self checks failed: {checks}"
assert len(data["dual_basis_hex"]) == 256
print(f"OK: Verified Lean-emitted JSON {os.path.basename(jf)} ({os.path.getsize(jf)} bytes)")
print(f"OK: Lean 4.35.0 kernel-verified {len(target_mods)} target module(s) with 0 warnings in {time.time() - t0:.2f}s")
PY

if [[ "$LEAN_ONLY" -eq 1 ]]; then
  exit 0
fi

echo "==> Running native Rust Wave 11 Frigo–shelat Tower256 Trace-Packing & Hilbert-90 ZK suite (--release)..."
export CARGO_TARGET_DIR="/tmp/target-w11-t256"
cargo test --locked --release --manifest-path "$MINIDREGG/prover/Cargo.toml" --lib tower256_trace_pack
cargo test --locked --release --manifest-path "$MINIDREGG/prover/Cargo.toml" --test tower256_trace_packing -- --nocapture --test-threads=1
echo "OK: Full Wave 11 Lean 4.35.0 + Rust Frigo–shelat Tower256 Trace-Packing suite passed."
