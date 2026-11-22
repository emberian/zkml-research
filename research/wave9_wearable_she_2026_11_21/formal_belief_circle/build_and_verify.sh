#!/usr/bin/env bash
# Isolated Lean 4.35.0 overlay + `--release` Rust verifier for Wave-9 Wearable SHE Organ #3:
#   - /Users/ember/dev/minidregg/Assurance/WearableBeliefCircle.lean
#   - /Users/ember/dev/minidregg/prover/testdata/belief_circle_conformance.json
#   - /Users/ember/dev/minidregg/prover/src/belief_circle.rs
#   - /Users/ember/dev/minidregg/prover/tests/wearable_belief_circle.rs
#   - /Users/ember/dev/zkml-research/notes/she-wearable-belief-circles-and-tof.md
#
# Never runs `lake build` in /Users/ember/dev/minidregg; compiles .olean/.ilean/.ir into ./build/.
# Pass `--lean-only` to run only Lean 4.35.0 verification, import-boundary checks, and JSON emission.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
NOTE_FILE="/Users/ember/dev/zkml-research/notes/she-wearable-belief-circles-and-tof.md"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"
LEAN_ONLY=0
REBUILD_LEAN=1
for arg in "$@"; do
  case "$arg" in
    --lean-only) LEAN_ONLY=1 ;;
    --cached-lean) REBUILD_LEAN=0 ;;
  esac
done

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$LAKE_BIN" "$REBUILD_LEAN" "$NOTE_FILE" <<'PY'
import json, os, re, subprocess, sys, time

formal, minidregg, lean_bin, lake_bin = sys.argv[1:5]
rebuild_lean = sys.argv[5] == "1"
note_file = sys.argv[6]
build = os.path.join(formal, "build")
dep_cwd = os.path.join(formal, "build", "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")
dynlib = os.path.join(minidregg, ".lake", "native", "libmini_kernels_lean.so")

sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports, header_layout

ALLOWED_ASSURANCE = {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"}
target_mods = [
    ("Assurance", "Assurance/WearableBeliefCircle.lean", "Assurance.WearableBeliefCircle"),
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
        if tgt not in ALLOWED_ASSURANCE:
            print(f"FAIL: import-boundary violation in {rel}: import {imp} ({lib} -> {tgt})", file=sys.stderr)
            sys.exit(1)
    stripped = strip_lean_comments_and_strings(text)
    for pat, label in [
        (r"\bsorry\b", "sorry"),
        (r"\bsorryAx\b", "sorryAx"),
        (r"^\s*(?:@\[[^\]]*\]\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|nonrec\s+)*axiom\b", "custom axiom"),
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
    print(f"OK: Hygiene & tier-import check for {rel} ({len(lines)} lines, 0 sorry, 0 axiom, 0 native_decide; {pins} #print axioms pins)")

ib = subprocess.run(["bash", os.path.join(minidregg, "scripts", "check-import-boundary.sh")],
                    cwd=minidregg, capture_output=True, text=True)
if ib.returncode != 0:
    print(f"FAIL: scripts/check-import-boundary.sh failed:\n{ib.stdout}\n{ib.stderr}", file=sys.stderr)
    sys.exit(1)
print("OK: scripts/check-import-boundary.sh passed")

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
    if ((not is_target or not rebuild_lean) and os.path.exists(out)
            and is_435_olean(out) and os.path.getmtime(out) >= os.path.getmtime(src)):
        if is_target:
            print(f"  [CACHED    0.00s] {mod} -> up-to-date 4.35.0 .olean", flush=True)
        continue
    if is_target and os.path.islink(out):
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
    if is_target and ("warning:" in res.stdout or "warning:" in res.stderr):
        print(f"FAIL: compiler warning emitted while building {mod}", file=sys.stderr)
        sys.exit(1)

jf = os.path.join(minidregg, "prover", "testdata", "belief_circle_conformance.json")
if not os.path.exists(jf):
    print(f"FAIL: missing emitted conformance vector {jf}", file=sys.stderr)
    sys.exit(1)
with open(jf, encoding="utf-8") as f:
    data = json.load(f)
assert data["schema"] == "minidregg.belief_circle_conformance.v1"
assert data["tof_in_range_accepted"] is True
assert data["tof_wormhole_5m_rejected"] is True
assert data["tof_early_trigger_rejected"] is True
assert len(bytes.fromhex(data["p2_idle_cell_hex"])) == 1024
assert len(bytes.fromhex(data["p2_hazard_cell_hex"])) == 1024
assert len(bytes.fromhex(data["p2_duty_cell_hex"])) == 1024
assert len(bytes.fromhex(data["p1_hazard_cell_hex"])) == 256
assert data["overlay_order_invariant"] is True
assert data["admitted_all_three"] is True
assert data["revoked_bob_kills_carol_delegation"] is True
print(f"OK: Verified Lean-emitted JSON {os.path.basename(jf)} ({os.path.getsize(jf)} bytes)")
if os.path.exists(note_file):
    nlines = len(open(note_file, encoding="utf-8").read().splitlines())
    if nlines > 95:
        print(f"FAIL: note {note_file} has {nlines} lines (must be <= 95)", file=sys.stderr)
        sys.exit(1)
    print(f"OK: Companion research note line budget ({nlines} <= 95 lines)")
print(f"OK: Lean 4.35.0 kernel-verified {len(target_mods)} target module(s) with 0 warnings in {time.time() - t0:.2f}s")
PY

if [[ "$LEAN_ONLY" -eq 1 ]]; then
  exit 0
fi

echo "==> Running native Rust belief_circle conformance, adversarial & benchmark suite (--release)..."
export CARGO_TARGET_DIR="/Users/ember/dev/minidregg/prover/target-beliefcircle"
export RUSTFLAGS="-D warnings"
cargo test --release --manifest-path "$MINIDREGG/prover/Cargo.toml" --lib belief_circle
cargo test --release --manifest-path "$MINIDREGG/prover/Cargo.toml" --test wearable_belief_circle -- --nocapture --test-threads=1
echo "OK: Full Lean 4.35.0 + Rust Wearable Belief Circle Organ #3 suite passed."
