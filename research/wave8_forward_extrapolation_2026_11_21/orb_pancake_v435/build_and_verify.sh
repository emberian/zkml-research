#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"

if [ ! -x "$LEAN_BIN" ]; then
  echo "ERROR: Lean v4.35.0 binary not found at $LEAN_BIN" >&2
  exit 1
fi

echo "=== [1/3] Static Hygiene Gate (Init-only, 0 Mathlib, 0 sorry, 0 axiom, 0 native_decide) ==="
FILES=(
  "PanSemV435.lean"
  "CondSClk.lean"
  "RefinesClkPan.lean"
  "LcnfToPancake.lean"
  "PancakeTeethTest.lean"
)

for f in "${FILES[@]}"; do
  path="$DIR/$f"
  if [ ! -f "$path" ]; then
    echo "ERROR: Missing expected file $path" >&2
    exit 1
  fi
  if grep -Eq '^[[:space:]]*import[[:space:]]+(Mathlib|Std|Batteries)\b' "$path"; then
    echo "ERROR: Forbidden external import in $f" >&2
    exit 1
  fi
  # Strip line comments and check for forbidden proof escapes
  stripped="$(sed 's/--.*$//' "$path")"
  if printf '%s\n' "$stripped" | grep -Eq '\bsorry\b'; then
    echo "ERROR: Found sorry in $f" >&2
    exit 1
  fi
  if printf '%s\n' "$stripped" | grep -Eq '^[[:space:]]*axiom\b'; then
    echo "ERROR: Found custom axiom in $f" >&2
    exit 1
  fi
  if printf '%s\n' "$stripped" | grep -Eq '\bnative_decide\b'; then
    echo "ERROR: Found native_decide in $f" >&2
    exit 1
  fi
  if ! grep -q '#guard_msgs' "$path" || ! grep -q '#print axioms' "$path"; then
    echo "ERROR: Missing #guard_msgs-pinned #print axioms in $f" >&2
    exit 1
  fi
done
echo "Static hygiene checks passed across ${#FILES[@]} files."

echo "=== [2/3] Kernel Verification with Lean v4.35.0 (-DwarningAsError=true) ==="
BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/orb_pancake_v435_build.XXXXXX")"
cleanup() {
  rm -rf "$BUILD_DIR"
}
trap cleanup EXIT

for f in "${FILES[@]}"; do
  stem="${f%.lean}"
  printf "  Checking %-24s ... " "$f"
  t0="$(python3 -c 'import time; print(time.time())')"
  LEAN_PATH="$BUILD_DIR" "$LEAN_BIN" -DwarningAsError=true \
    "$DIR/$f" -o "$BUILD_DIR/$stem.olean"
  t1="$(python3 -c 'import time; print(time.time())')"
  dt="$(python3 -c "print(f'{$t1 - $t0:.2f}s')")"
  echo "OK ($dt)"
done

echo "=== [3/3] Verification Summary ==="
"$LEAN_BIN" --version
wc -l "${FILES[@]/#/$DIR/}"
echo "ALL G6 STANDALONE VERIFICATION GATES PASSED (0 warnings, 0 sorry, 0 custom axioms)."
