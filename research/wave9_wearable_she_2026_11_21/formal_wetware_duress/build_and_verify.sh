#!/usr/bin/env bash
# Build and verify the Rainbows End wearable SHE organ #5 (wetware safety + duress vault):
#   - /Users/ember/dev/minidregg/Theory/WetwareSafetyAndDuress.lean   (Lean v4.35.0, isolated overlay)
#   - /Users/ember/dev/minidregg/prover/src/wetware_duress_guard.rs   (--release Rust tests + benches)
#   - /Users/ember/dev/minidregg/prover/tests/wetware_and_duress.rs
#   - /Users/ember/dev/minidregg/prover/testdata/wetware_duress_conformance.json
#
# Never runs `lake build` in minidregg and writes nothing there: the .olean goes to ./build/,
# cargo artifacts to ./target-wetware/; both are removed on exit (set KEEP_BUILD=1 to keep).
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
BUILD="$FORMAL_DIR/build"
TARGET="$FORMAL_DIR/target-wetware"

cleanup() {
  if [[ "${KEEP_BUILD:-0}" != "1" ]]; then
    rm -rf "$BUILD" "$TARGET"
  fi
}
trap cleanup EXIT

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$BUILD" <<'PY'
import json, os, re, subprocess, sys, time

formal, minidregg, lean_bin, build = sys.argv[1:5]
rel = "Theory/WetwareSafetyAndDuress.lean"
src_path = os.path.join(minidregg, rel)
text = open(src_path, encoding="utf-8").read()

# 1. Hygiene (ATLAS laws): 0 sorry, 0 custom axiom, 0 native_decide, 0 bare #guard; size; pins.
stripped = re.sub(r"/-.*?-/", "", text, flags=re.S)
stripped = re.sub(r"--[^\n]*", "", stripped)
for pat, label in [(r"\bsorry\b", "sorry"), (r"^\s*axiom\b", "custom axiom"),
                   (r"\bnative_decide\b", "native_decide"), (r"#guard\b(?!_msgs)", "#guard unit test"),
                   (r"\badmit\b", "admit")]:
    if re.search(pat, stripped, flags=re.M):
        sys.exit(f"FAIL: forbidden `{label}` in {rel}")
nlines = text.count("\n")
if nlines >= 950:
    sys.exit(f"FAIL: {rel} has {nlines} lines (limit < 950)")
pinned_axioms = re.findall(r"/-- info: '[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms) -/\n"
                           r"#guard_msgs \(whitespace := lax\) in #print axioms (\S+)", text)
if len(pinned_axioms) < 20:
    sys.exit(f"FAIL: only {len(pinned_axioms)} #guard_msgs-pinned #print axioms (need >= 20)")
for ax in re.findall(r"depends on axioms: \[([^\]]*)\]", text):
    extra = {a.strip() for a in ax.split(",")} - {"propext", "Classical.choice", "Quot.sound"}
    if extra:
        sys.exit(f"FAIL: non-standard axiom(s) pinned: {extra}")
print(f"OK: hygiene ({nlines} lines; 0 sorry/axiom/native_decide/#guard; "
      f"{len(pinned_axioms)} pinned #print axioms, all within [propext, Classical.choice, Quot.sound])")

# 2. Import boundary: a Theory/ module imports only Mathlib, Lean, Std, Theory.
sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports
bad = [i for i in header_imports(text) if i.split(".")[0] not in {"Mathlib", "Lean", "Std", "Theory"}]
if bad:
    sys.exit(f"FAIL: import-boundary violation in {rel}: {bad}")
print("OK: import boundary (Theory -> Mathlib only)")

# 3. Compile in an isolated overlay: LEAN_PATH = the prebuilt package oleans; output to ./build.
pkgs = os.path.join(minidregg, ".lake", "packages")
lean_path = ":".join(os.path.join(pkgs, d, ".lake", "build", "lib", "lean") for d in sorted(os.listdir(pkgs))
                     if os.path.isdir(os.path.join(pkgs, d, ".lake", "build", "lib", "lean")))
env = dict(os.environ, LEAN_PATH=lean_path)
out = os.path.join(build, "Theory", "WetwareSafetyAndDuress.olean")
os.makedirs(os.path.dirname(out), exist_ok=True)
t0 = time.time()
res = subprocess.run([lean_bin, "-Dbackward.privateInPublic=true", "-Dbackward.privateInPublic.warn=false",
                      "-Dbackward.proofsInPublic=true", "-Dcompiler.relaxedMetaCheck=true",
                      "-R", minidregg, "-o", out, src_path], env=env, capture_output=True, text=True)
msg = (res.stdout + res.stderr).strip()
if res.returncode != 0 or msg:
    print(msg)
    sys.exit(f"FAIL: lean rc={res.returncode}; any message (warning, error, unpinned output) fails the build")
print(f"OK: kernel-checked {rel} in {time.time() - t0:.2f}s (rc=0, 0 messages, 0 warnings)")

# 4. The conformance JSON is the Lean pins, list for list.
pins = {cmd.strip(): json.loads(info) for info, cmd in re.findall(
    r"/-- info: (\[[^\]]*\]) -/\n#guard_msgs \(whitespace := lax\) in #eval ([^\n]*)", text)}
conf = json.load(open(os.path.join(minidregg, "prover/testdata/wetware_duress_conformance.json")))
expr = {
    "strobe15_15hz": ("(List.range 48).map strobe15", "emitted wearable60 0 strobe15 48"),
    "stego_lsb_key_A": ("(List.range 32).map stegoA", "emitted wearable60 128 stegoA 32"),
    "stego_lsb_key_B": ("(List.range 32).map stegoB", "emitted wearable60 128 stegoB 32"),
    "triangle_safe_canonical": ("(List.range 48).map triangle", "emitted wearable60 0 triangle 48"),
    "chaotic_wearable60": ("(List.range 48).map chaotic", "emitted wearable60 128 chaotic 48"),
    "chaotic_noQuant": ("(List.range 48).map chaotic", "emitted noQuant 128 chaotic 48"),
    "chaotic_q8_d24_h6": ("(List.range 48).map chaotic", "emitted ⟨8, 24, 6⟩ 0 chaotic 48"),
}
for v in conf["scrubber_vectors"]:
    i, e = expr[v["name"]]
    if v["input"] != pins[i] or v["emitted"] != pins[e]:
        sys.exit(f"FAIL: conformance vector {v['name']} disagrees with the Lean pin")
cad = [k for k in pins if "snapRelease" in k][0]
aud = [k for k in pins if "quantAudio" in k][0]
if [c["release"] for c in conf["cadence"]] != pins[cad] or [a["q"] for a in conf["audio"]] != pins[aud]:
    sys.exit("FAIL: cadence/audio vectors disagree with the Lean pins")
print(f"OK: conformance JSON == Lean #guard_msgs pins ({len(conf['scrubber_vectors'])} scrubber vectors, "
      f"{len(conf['cadence'])} cadence, {len(conf['audio'])} audio)")
PY

# 5. Rust: --release conformance, theorem-mirror fuzz, #tooth and 60 fps benchmarks.
#    Isolated crate overlay: the owned module + its one dependency (hash_kernels.rs) under the same
#    crate name, so in-flight edits of other lanes in prover/src cannot break or mask this check.
OVERLAY="$TARGET/overlay"
rm -rf "$OVERLAY"; mkdir -p "$OVERLAY/src" "$OVERLAY/tests" "$OVERLAY/testdata"
cp "$MINIDREGG/prover/Cargo.toml" "$OVERLAY/Cargo.toml"
printf '\n[workspace]\n' >> "$OVERLAY/Cargo.toml"
cp "$MINIDREGG/Cargo.lock" "$OVERLAY/Cargo.lock"
cp "$MINIDREGG/prover/src/hash_kernels.rs" "$MINIDREGG/prover/src/wetware_duress_guard.rs" "$OVERLAY/src/"
printf '//! Overlay root: hash_kernels + wetware_duress_guard only (see build_and_verify.sh).\npub mod hash_kernels;\npub mod wetware_duress_guard;\n' > "$OVERLAY/src/lib.rs"
cp "$MINIDREGG/prover/tests/wetware_and_duress.rs" "$OVERLAY/tests/"
cp "$MINIDREGG/prover/testdata/wetware_duress_conformance.json" "$OVERLAY/testdata/"
LOG="$(mktemp)"
if ! CARGO_TARGET_DIR="$TARGET/cargo" RUSTFLAGS="-D warnings" cargo test --offline --release \
  --manifest-path "$OVERLAY/Cargo.toml" --test wetware_and_duress -- --nocapture --test-threads=1 2>&1 | tee "$LOG"; then
  echo "FAIL: cargo test failed" >&2; rm -f "$LOG"; exit 1
fi
if grep -qE "^(warning|error)" "$LOG"; then
  echo "FAIL: compiler warnings/errors under RUSTFLAGS=-D warnings" >&2; rm -f "$LOG"; exit 1
fi
rm -f "$LOG"
echo "OK: cargo test --release (RUSTFLAGS=-D warnings, 0 warnings) wetware_and_duress passed"
echo "ALL OK"
