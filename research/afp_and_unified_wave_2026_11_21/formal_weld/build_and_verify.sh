#!/usr/bin/env bash
# Isolated-Overlay Lean 4.35.0 + Native Rust `--release` Verifier for:
#   1. `minidregg/Assurance/VerifiableAgentTurnWeld.lean` (compiled into `./build/` overlay; never runs `lake build` in `minidregg/.lake`)
#   2. `qwen35audit` `--release` integration & `1T == 12T` determinism suite (`tests/verifiable_agent_e2e.rs`)
#   3. Live `verifiable_qwen_agent` CLI (`Qwen3.5-0.8B` 24L + `Qwen3.8-27B` `.npz`) + Lean 4.35.0 `#eval` check on freshly emitted `VAGENT01` bytes

set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
ZKML_DIR="/Users/ember/dev/zkml-research"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="${TOOLCHAIN_DIR}/bin/lean"
LAKE_BIN="${TOOLCHAIN_DIR}/bin/lake"
DYNLIB="${MINIDREGG}/.lake/native/libmini_kernels_lean.so"
export CARGO_TARGET_DIR="${ZKML_DIR}/native/target-vagent"
TMP_OUT="$(mktemp -d /tmp/vagent01_verify.XXXXXX)"
trap 'rm -rf "${TMP_OUT}" "${FORMAL_DIR}/build"' EXIT

echo "=== [1/4] Checking minidregg import boundaries & VerifiableAgentTurnWeld.lean ATLAS hygiene ==="
(cd "${MINIDREGG}" && ./scripts/check-import-boundary.sh)

echo "=== [2/4] Isolated-Overlay Lean 4.35.0 kernel check + #guard_msgs axiom pins + #eval golden VAGENT01 check ==="
python3 - "${FORMAL_DIR}" "${MINIDREGG}" "${LEAN_BIN}" "${LAKE_BIN}" "${DYNLIB}" <<'PY'
import os, re, subprocess, sys, time

formal, minidregg, lean_bin, lake_bin, dynlib = sys.argv[1:6]
build = os.path.join(formal, "build")
dep_cwd = os.path.join(formal, "build", "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")

sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports

ALLOWED_ASSURANCE = {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"}
target_rel = "Assurance/VerifiableAgentTurnWeld.lean"
target_mod = "Assurance.VerifiableAgentTurnWeld"
target_path = os.path.join(minidregg, target_rel)

with open(target_path, encoding="utf-8") as f:
    text = f.read()

imports = header_imports(text)
assert imports, "Expected non-empty imports in Assurance/VerifiableAgentTurnWeld.lean"
for imp in imports:
    parts = imp.split(".")
    tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
    if tgt not in ALLOWED_ASSURANCE:
        print(f"FAIL: forbidden import `{imp}` in {target_rel} (tier {tgt})", file=sys.stderr)
        sys.exit(1)

stripped = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
stripped = re.sub(r"--[^\n]*", "", stripped)
for pat, label in [
    (r"\bsorry\b", "sorry"),
    (r"\bsorryAx\b", "sorryAx"),
    (r"(?m)^\s*(?:private\s+|protected\s+)?axiom\b", "custom axiom"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bdebug\.skipKernelTC\b", "skipKernelTC"),
    (r"#guard\b(?!_msgs)", "#guard"),
]:
    if re.search(pat, stripped):
        print(f"FAIL: forbidden `{label}` found in {target_rel}", file=sys.stderr)
        sys.exit(1)
if "sorryAx" in text:
    print(f"FAIL: `sorryAx` found in {target_rel} (including #guard_msgs docstrings)", file=sys.stderr)
    sys.exit(1)

pins = len(re.findall(r"#guard_msgs[^\n]*#print\s+axioms", stripped))
assert pins >= 20, f"Expected >= 20 #print axioms pins, found {pins}"
print(f"OK: {target_rel} imports {imports} (all in ALLOWED['Assurance']); 0 sorry, 0 axiom, 0 native_decide, 0 #guard; {pins} #print axioms pins.")

EXPECTED_MAGIC = b"olean\x02\x014.35.0"
def is_435_olean(path):
    try:
        with open(path, "rb") as f:
            return f.read(len(EXPECTED_MAGIC)) == EXPECTED_MAGIC
    except OSError:
        return False

target_stems = {"Assurance/VerifiableAgentTurnWeld"}
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
            if os.path.islink(dst) and not os.path.exists(dst):
                os.unlink(dst)
            if not os.path.lexists(dst):
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
    s = re.sub(r"/\-.*?\-/", "", t, flags=re.S)
    s = re.sub(r"--[^\n]*", "", s)
    seen, out = set(), []
    for m in IMPORT_RE.finditer(s):
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
    if (mod != target_mod and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
        return
    for imp in get_imports(mod):
        dfs(imp)
    order.append(mod)

dfs(target_mod)

t0 = time.time()
base_opts = [
    f"--load-dynlib={dynlib}",
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
]
for mod in order:
    src = src_path(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_target = (mod == target_mod)
    opts = base_opts + (["-DwarningAsError=true"] if is_target else [])
    run_cwd = minidregg if is_target else dep_cwd
    t1 = time.time()
    res = subprocess.run(
        [lean_bin, *opts, "-R", minidregg, "-o", out, src],
        cwd=run_cwd, env=env, capture_output=True, text=True
    )
    dt = time.time() - t1
    tag = "TARGET" if is_target else "DEP"
    print(f"  [{tag:6s} {dt:5.2f}s] {mod} -> rc={res.returncode}", flush=True)
    if (is_target or res.returncode != 0) and res.stdout.strip():
        print(res.stdout.rstrip(), flush=True)
    if res.stderr.strip():
        print(res.stderr.rstrip(), flush=True)
    if res.returncode != 0 or (is_target and res.stderr.strip()):
        sys.exit(1)

print(f"OK: Overlay Lean 4.35.0 kernel + #eval verified in {time.time() - t0:.2f} s")
PY

echo "=== [3/4] Rust --release verifiable_agent_e2e integration & 1T==12T determinism tests ==="
cargo test --release \
  --manifest-path "${ZKML_DIR}/native/qwen35audit/Cargo.toml" \
  --test verifiable_agent_e2e -- --nocapture

echo "=== [4/4] Live verifiable_qwen_agent CLI + Lean 4.35.0 verification of fresh VAGENT01 wire bytes ==="

cargo run --release \
  --manifest-path "${ZKML_DIR}/native/qwen35audit/Cargo.toml" \
  --bin verifiable_qwen_agent -- --emit-dir "${TMP_OUT}"

PKG_PATH="$("${LAKE_BIN}" --dir "${MINIDREGG}" env printenv LEAN_PATH)"
CLEAN_PKG_PATH="$(python3 -c 'import sys; print(":".join(p for p in sys.argv[1].split(":") if not p.startswith(sys.argv[2])))' "${PKG_PATH}" "${MINIDREGG}")"

(cd "${MINIDREGG}" && \
  VAGENT01_VERIFY_DIR="${TMP_OUT}" \
  LEAN_PATH="${FORMAL_DIR}/build:${CLEAN_PKG_PATH}" \
  "${LEAN_BIN}" -DwarningAsError=true --load-dynlib="${DYNLIB}" -R "${MINIDREGG}" \
  Assurance/VerifiableAgentTurnWeld.lean)

echo "OK: Lean 4.35.0 verifyAgentTurnBytes accepted freshly emitted live VASTMT01 ($(wc -c < "${TMP_OUT}/vagent01_stmt.bin" | tr -d ' ') B) and VAGENT01 ($(wc -c < "${TMP_OUT}/vagent01_receipt.bin" | tr -d ' ') B)!"
echo "=== ALL CHECKS PASSED (EXIT 0) ==="
