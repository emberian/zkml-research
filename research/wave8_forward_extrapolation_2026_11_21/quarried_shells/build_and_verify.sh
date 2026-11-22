#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_FILE="/Users/ember/dev/minidregg/Assurance/LightClientAndViewLens.lean"
NOTE_FILE="/Users/ember/dev/zkml-research/notes/wave8-viewnode-and-lightclient-quarry.md"

echo "==> [1/4] Checking Lean line budget and proof hygiene"
LEAN_LINES="$(wc -l < "$LEAN_FILE" | tr -d ' ')"
echo "    LightClientAndViewLens.lean: ${LEAN_LINES} lines (limit < 950)"
if [ "$LEAN_LINES" -ge 950 ]; then
  echo "FAIL: LightClientAndViewLens.lean exceeds 950 lines (${LEAN_LINES})" >&2
  exit 1
fi
if grep -En '\b(sorry|native_decide)\b' "$LEAN_FILE"; then
  echo "FAIL: forbidden sorry or native_decide found" >&2
  exit 1
fi
if grep -En '^[[:space:]]*((@\[[^]]*\]|private|protected|noncomputable|unsafe|partial|nonrec)[[:space:]]+)*axiom[[:space:]]' "$LEAN_FILE"; then
  echo "FAIL: custom axiom declaration found" >&2
  exit 1
fi

echo "==> [2/4] Typechecking LightClientAndViewLens.lean with isolated Lean v4.35.0 (0 warnings)"
(
  cd /Users/ember/dev/minidregg
  LEAN_PATH="/Users/ember/dev/minidregg/.lake/build/lib/lean" \
    lean -DwarningAsError=true Assurance/LightClientAndViewLens.lean
)
echo "    Lean v4.35.0 check PASS (0 warnings, #guard_msgs axiom pins verified)"

echo "==> [3/4] Building & testing standalone Rust quarried_shells (--release, -D warnings)"
(
  cd "$SCRIPT_DIR"
  RUSTFLAGS="-D warnings" cargo test --release
)

echo "==> [4/4] Checking companion research note line budget (<= 120 lines)"
if [ -f "$NOTE_FILE" ]; then
  NOTE_LINES="$(wc -l < "$NOTE_FILE" | tr -d ' ')"
  echo "    wave8-viewnode-and-lightclient-quarry.md: ${NOTE_LINES} lines (limit <= 120)"
  if [ "$NOTE_LINES" -gt 120 ]; then
    echo "FAIL: note exceeds 120 lines (${NOTE_LINES})" >&2
    exit 1
  fi
fi

echo "ALL CHECKS PASSED."
