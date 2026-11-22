#!/usr/bin/env bash
# End-to-end isolated Lean v4.35.0 overlay + standalone `--release` Rust verifier for
# Wearable SHE Organ #6 (Gap #1 Pocket-FPGA Companion):
#   1. /Users/ember/dev/minidregg/Compiler/PocketFpgaCaptpVat.lean
#   2. /Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/
#   3. /Users/ember/dev/zkml-research/notes/she-pocket-fpga-captp-vat-and-fram.md
#
# NEVER runs `lake build` in /Users/ember/dev/minidregg; compiles .olean into ./build/.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
LEAN_FILE="$MINIDREGG/Compiler/PocketFpgaCaptpVat.lean"
NOTE_FILE="/Users/ember/dev/zkml-research/notes/she-pocket-fpga-captp-vat-and-fram.md"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
BUILD_DIR="$SCRIPT_DIR/build"

echo "==> [1/5] Checking ATLAS hygiene, line budget (< 950), & import-boundary tier rules..."
python3 - "$MINIDREGG" "$LEAN_FILE" <<'PY'
import os, re, subprocess, sys

minidregg, lean_file = sys.argv[1:3]
sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports, header_layout

ALLOWED_COMPILER = {
    "Mathlib", "Lean", "Std", "Init", "Theory", "Effects",
    "Pred", "Kernel", "Selvage", "Assurance", "Compiler",
}

with open(lean_file, encoding="utf-8") as f:
    text = f.read()

lines = len(text.splitlines())
if lines >= 950:
    print(f"FAIL: {lean_file} has {lines} lines (must be < 950)", file=sys.stderr)
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
    if tgt not in ALLOWED_COMPILER:
        print(f"FAIL: import-boundary violation: {imp} (Compiler -> {tgt})", file=sys.stderr)
        sys.exit(1)

def strip_comments_and_strings(src: str) -> str:
    out, i, n, depth, in_str = [], 0, len(src), 0, False
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
                depth += 1; i += 2
            elif src[i:i+2] == "-/":
                depth -= 1; i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        else:
            if src[i:i+2] == "/-":
                depth = 1; i += 2
            elif src[i:i+2] == "--":
                while i < n and src[i] != "\n":
                    i += 1
            elif src[i] == '"':
                in_str = True; out.append('""'); i += 1
            else:
                out.append(src[i]); i += 1
    return "".join(out)

stripped = strip_comments_and_strings(text)
for pat, label in [
    (r"\bsorry\b", "sorry"),
    (r"\bsorryAx\b", "sorryAx"),
    (r"^\s*axiom\b", "custom axiom"),
    (r"\bnative_decide\b", "native_decide"),
    (r"#guard\b(?!_msgs)", "#guard"),
]:
    if re.search(pat, stripped, flags=re.M):
        print(f"FAIL: forbidden `{label}` found in {lean_file}", file=sys.stderr)
        sys.exit(1)

pins = len(re.findall(r"#guard_msgs[^\n]*#print\s+axioms", text))
if pins < 10:
    print(f"FAIL: expected >= 10 #guard_msgs #print axioms pins, found {pins}", file=sys.stderr)
    sys.exit(1)

ib = subprocess.run(
    ["bash", os.path.join(minidregg, "scripts", "check-import-boundary.sh")],
    cwd=minidregg, capture_output=True, text=True
)
if ib.returncode != 0:
    print(f"FAIL: scripts/check-import-boundary.sh failed:\n{ib.stdout}\n{ib.stderr}", file=sys.stderr)
    sys.exit(1)

print(f"    OK: PocketFpgaCaptpVat.lean ({lines} lines < 950; 0 sorry, 0 axiom, 0 native_decide; {pins} axiom pins; check-import-boundary OK)")
PY

echo "==> [2/5] Kernel-verifying Compiler/PocketFpgaCaptpVat.lean on Lean v4.35.0 (-DwarningAsError=true)..."
mkdir -p "$BUILD_DIR/Compiler"
T0=$(python3 -c 'import time; print(time.time())')
"$LEAN_BIN" \
  -DwarningAsError=true \
  -R "$MINIDREGG" \
  -o "$BUILD_DIR/Compiler/PocketFpgaCaptpVat.olean" \
  "$LEAN_FILE"
T1=$(python3 -c 'import time; print(time.time())')
python3 -c "print(f'    OK: Lean v4.35.0 kernel verified with 0 warnings in {float($T1)-float($T0):.2f}s')"

echo "==> [3/5] Emitting golden vectors directly from Lean v4.35.0 kernel definitions..."
EMIT_LEAN="$BUILD_DIR/_emit_golden.lean"
GOLDEN_JSON="$BUILD_DIR/lean_golden_vectors.json"
cat > "$EMIT_LEAN" <<'LEAN'
import Compiler.PocketFpgaCaptpVat

open Minidregg.Compiler.PocketFpgaCaptpVat

def hex64 (b : BitVec 64) : String :=
  let ds := "0123456789abcdef".toList
  let nibbles := (List.range 16).reverse.map fun i =>
    ds[((b.toNat >>> (i * 4)) &&& 0xF)]!
  "0x" ++ String.ofList nibbles

def main (args : List String) : IO Unit := do
  let outPath := args.headD "lean_golden_vectors.json"
  let c1 := computeFramCrcTag goldenPolicyDigest 0#64 0#64 1#64
  let c2 := computeFramCrcTag goldenPolicyDigest 42#64 7#64 2#64
  let bs := vatGoldenBitstream
  let tp := trojanPipBitstream
  let tl := trojanLutBitstream
  let lines := [
    s!"  \"schema\": \"minidregg.pocket_fpga_vat.v1\"",
    s!"  \"crc_epoch1_leaf0\": \"{hex64 c1}\"",
    s!"  \"crc_epoch2_leaf42\": \"{hex64 c2}\"",
    s!"  \"golden_bs_w0\": \"{hex64 bs.w0}\"",
    s!"  \"golden_bs_w1\": \"{hex64 bs.w1}\"",
    s!"  \"golden_bs_w2\": \"{hex64 bs.w2}\"",
    s!"  \"golden_bs_w3\": \"{hex64 bs.w3}\"",
    s!"  \"golden_bs_w4\": \"{hex64 bs.w4}\"",
    s!"  \"golden_bs_w5\": \"{hex64 bs.w5}\"",
    s!"  \"golden_bs_w6\": \"{hex64 bs.w6}\"",
    s!"  \"golden_bs_w7\": \"{hex64 bs.w7}\"",
    s!"  \"trojan_pip_w3\": \"{hex64 tp.w3}\"",
    s!"  \"trojan_pip_w7\": \"{hex64 tp.w7}\"",
    s!"  \"trojan_lut_w6\": \"{hex64 tl.w6}\"",
    s!"  \"trojan_lut_w7\": \"{hex64 tl.w7}\""
  ]
  IO.FS.writeFile outPath ("{\n" ++ String.intercalate ",\n" lines ++ "\n}\n")
LEAN
LEAN_PATH="$BUILD_DIR" "$LEAN_BIN" --run "$EMIT_LEAN" "$GOLDEN_JSON"
echo "    OK: Emitted $(wc -c < "$GOLDEN_JSON" | tr -d ' ')B Lean golden vector fixture"

echo "==> [4/5] Running standalone Rust pocket_fpga_vat suite (--release, -D warnings, #![forbid(unsafe_code)])..."
(
  cd "$SCRIPT_DIR"
  LEAN_GOLDEN_JSON="$GOLDEN_JSON" RUSTFLAGS="-D warnings" cargo test --release -- --nocapture
)

echo "==> [5/5] Checking companion note line budget (<= 95 lines)..."
if [[ -f "$NOTE_FILE" ]]; then
  NOTE_LINES="$(wc -l < "$NOTE_FILE" | tr -d ' ')"
  if [[ "$NOTE_LINES" -gt 95 ]]; then
    echo "FAIL: $NOTE_FILE has $NOTE_LINES lines (must be <= 95)" >&2
    exit 1
  fi
  echo "    OK: $(basename "$NOTE_FILE") ($NOTE_LINES lines <= 95)"
fi

echo "OK: Full Lean v4.35.0 + Rust pocket_fpga_vat verification suite passed with 0 warnings."
