#!/usr/bin/env bash
# Isolated Lean v4.35.0 overlay verifier for
#   /Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean   (gate G8 / #125)
#
# Never runs `lake build` (or any `lake` command) in /Users/ember/dev/minidregg.
# Reads prebuilt Lean-4.35.0 package oleans (Mathlib & deps) from
# /Users/ember/dev/minidregg/.lake/packages/*/.lake/build/lib/lean and the tree's own
# /Users/ember/dev/minidregg/.lake/build/lib/lean (read-only), and writes the target's
# .olean/.ilean into ./build/ (wiped at the start of every run).
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
LEAN_BIN="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
REL="Theory/Char2Degree4SumcheckHvzk.lean"
SRC="$MINIDREGG/$REL"
BUILD="$FORMAL_DIR/build"
MAX_LINES=1100

rm -rf "$BUILD"
mkdir -p "$BUILD/Theory"

[[ -f "$SRC" ]] || { echo "FAIL: missing $SRC" >&2; exit 1; }
"$LEAN_BIN" --version | grep -q "4.35.0" || { echo "FAIL: toolchain is not v4.35.0" >&2; exit 1; }

python3 - "$SRC" "$REL" "$MAX_LINES" "$MINIDREGG" <<'PY'
import re, subprocess, sys, os
src, rel, max_lines, minidregg = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
text = open(src, encoding="utf-8").read()
n = text.count("\n")
if n >= max_lines:
    sys.exit(f"FAIL: {rel} has {n} lines (budget < {max_lines})")
stripped = re.sub(r"/-.*?-/", "", text, flags=re.S)
stripped = re.sub(r"--[^\n]*", "", stripped)
for pat, label in [(r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"),
                   (r"^\s*axiom\b", "custom axiom"), (r"\bnative_decide\b", "native_decide"),
                   (r"\bunsafe\b", "unsafe"), (r"@\[implemented_by", "implemented_by")]:
    if re.search(pat, stripped, flags=re.M):
        sys.exit(f"FAIL: forbidden `{label}` in {rel}")
pins = re.findall(r"#guard_msgs[^\n]*#print\s+axioms\s+(\S+)", text)
if not pins:
    sys.exit(f"FAIL: no #guard_msgs-pinned #print axioms in {rel}")
# every pin must expect exactly the three standard axioms (or none)
for m in re.finditer(r"/-- info: '([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms) -/\s*\n#guard_msgs", text):
    if m.group(3) is not None:
        ax = {a.strip() for a in m.group(3).split(",")}
        if not ax <= {"propext", "Classical.choice", "Quot.sound"}:
            sys.exit(f"FAIL: non-standard axiom pinned for {m.group(1)}: {ax}")
# import boundary: Theory/ may import only Mathlib/Lean/Std/Theory
sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports
for imp in header_imports(text):
    root = imp.split(".")[0]
    if root not in {"Mathlib", "Lean", "Std", "Theory"}:
        sys.exit(f"FAIL: import-boundary violation in {rel}: import {imp}")
print(f"OK: hygiene {rel}: {n} lines, 0 sorry/admit/axiom/native_decide, {len(pins)} #print axioms pins")
PY

# Tree-wide import boundary script (read-only check).
(cd "$MINIDREGG" && bash scripts/check-import-boundary.sh) > "$BUILD/import_boundary.log" 2>&1 \
  || { cat "$BUILD/import_boundary.log" >&2; echo "FAIL: scripts/check-import-boundary.sh" >&2; exit 1; }
echo "OK: scripts/check-import-boundary.sh passed"

LEAN_PATH="$BUILD"
for d in "$MINIDREGG"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$d"; done
LEAN_PATH="$LEAN_PATH:$MINIDREGG/.lake/build/lib/lean"
export LEAN_PATH

T0=$(date +%s)
set +e
( cd "$MINIDREGG" && "$LEAN_BIN" -R "$MINIDREGG" \
    -o "$BUILD/Theory/Char2Degree4SumcheckHvzk.olean" \
    -i "$BUILD/Theory/Char2Degree4SumcheckHvzk.ilean" "$SRC" ) > "$BUILD/lean.log" 2>&1
RC=$?
set -e
cat "$BUILD/lean.log"
[[ $RC -eq 0 ]] || { echo "FAIL: lean exited $RC" >&2; exit 1; }
if grep -qiE "warning|error|declaration uses 'sorry'" "$BUILD/lean.log"; then
  echo "FAIL: diagnostics emitted while building $REL" >&2; exit 1
fi
[[ -s "$BUILD/Theory/Char2Degree4SumcheckHvzk.olean" ]] || { echo "FAIL: no olean" >&2; exit 1; }
echo "OK: Lean v4.35.0 kernel-checked $REL (0 warnings, 0 errors) in $(( $(date +%s) - T0 ))s"
