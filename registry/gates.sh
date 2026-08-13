#!/usr/bin/env bash
# The gates.  Each one prints its own PASS/FAIL and the script exits nonzero
# if any failed.
#
# Exit codes are read from the TOOL, never from a pipeline: a `| tail` or
# `| grep` answers with ITS status and would report a passing gate for a
# crashed tool.  Output goes to a file; the verdict comes from $? of the
# unpiped call.
#
# Usage: ./gates.sh <full-manifest.json> <small-tensor-name> [rerun-manifest.json]
set -u
cd "$(dirname "$0")"
TOOL="python3 registry_tool.py"
MAN="${1:?usage: gates.sh <manifest> <small-tensor-name> [rerun-manifest]}"
SMALL="${2:?need a small tensor name to keep the audit cheap}"
RERUN="${3:-}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
FAILED=0

pass() { echo "PASS  $1"; }
fail() { echo "FAIL  $1"; FAILED=$((FAILED + 1)); }

echo "gates for $MAN"
echo

# --- G1: verify passes on the honest manifest ---------------------------
$TOOL verify "$MAN" --tensors "$SMALL" --all-shards > "$WORK/g1.out" 2>&1
rc=$?
if [ $rc -eq 0 ]; then pass "G1 verify accepts the honest manifest (exit 0)"
else fail "G1 verify REJECTED the honest manifest (exit $rc)"; cat "$WORK/g1.out"; fi

# --- G2..G6: verify fails on each deliberate corruption ------------------
for mode in tensor-hash commitment byte-len aux-hash header-hash offsets file-hash; do
  $TOOL tamper "$MAN" --out "$WORK/bad.$mode.json" --mode "$mode" \
      --tensor-name "$SMALL" > "$WORK/t.$mode.out" 2>&1
  trc=$?
  if [ $trc -ne 0 ]; then
    fail "G2:$mode tamper itself failed (exit $trc) -- the falsifier is broken"
    cat "$WORK/t.$mode.out"
    continue
  fi
  $TOOL verify "$WORK/bad.$mode.json" --tensors "$SMALL" --all-shards \
      > "$WORK/v.$mode.out" 2>&1
  vrc=$?
  if [ $vrc -eq 1 ]; then
    pass "G2:$mode verify REFUSES the corrupted manifest (exit 1)"
  else
    fail "G2:$mode verify returned $vrc on a corrupted manifest (wanted 1)"
    cat "$WORK/v.$mode.out"
  fi
done

# --- G7: two independent runs commit to the same value ------------------
if [ -n "$RERUN" ] && [ -f "$RERUN" ]; then
  $TOOL canon "$MAN" > "$WORK/a.canon" 2>"$WORK/a.err"; arc=$?
  $TOOL canon "$RERUN" > "$WORK/b.canon" 2>"$WORK/b.err"; brc=$?
  if [ $arc -ne 0 ] || [ $brc -ne 0 ]; then
    fail "G7 canon failed ($arc/$brc)"
  elif cmp -s "$WORK/a.canon" "$WORK/b.canon"; then
    ca=$($TOOL canon "$MAN" --digest-only)
    cb=$($TOOL canon "$RERUN" --digest-only)
    if [ "$ca" = "$cb" ]; then
      pass "G7 rerun-from-scratch reproduces the preimage AND the commitment"
      echo "      $ca"
    else
      fail "G7 identical preimage but different commitment ($ca vs $cb)"
    fi
  else
    fail "G7 rerun produced a DIFFERENT canonical preimage"
    diff <(fold -w120 "$WORK/a.canon") <(fold -w120 "$WORK/b.canon") | head -20
  fi
else
  echo "SKIP  G7 (no rerun manifest given)"
fi

# --- G8: the canonical form is stable under re-serialization ------------
python3 - "$MAN" > "$WORK/g8.out" 2>&1 <<'PY'
import json, subprocess, sys, os
p = sys.argv[1]
m = json.load(open(p))
core = m["core"]
# round-trip the core through a DIFFERENT serialization (indented, unsorted)
# and re-canonicalize: the preimage must be byte-identical.
alt = json.loads(json.dumps(core, indent=4, sort_keys=False))
sys.path.insert(0, os.path.dirname(os.path.abspath(p)) + "/..")
import registry_tool as rt
a = rt.commitment_preimage(core)
b = rt.commitment_preimage(alt)
assert a == b, "canonical form is not invariant under re-serialization"
assert rt.compute_commitment(alt) == m["commitment"], "commitment not reproduced"
print("ok")
PY
if [ $? -eq 0 ]; then
  pass "G8 canonical preimage is invariant under key order / whitespace"
else
  fail "G8 canonicalization is serialization-dependent"; cat "$WORK/g8.out"
fi

# --- G9: the documented test vector still comes out of the code ---------
# MANIFEST-FORMAT.md quotes an exact preimage length and digest.  If the
# canonicalization ever changes, this is what makes the document go red
# instead of quietly describing a format nobody implements any more.
TV_EXPECT="1b34613e012a472aa38b25f760f4ca17ed016058b49d4e95aab141a4a9b2a0e0"
TV_LEN=880
if [ -f test-vector.json ]; then
  got=$($TOOL canon test-vector.json --digest-only 2>"$WORK/g9.err")
  glen=$($TOOL canon test-vector.json 2>/dev/null | wc -c | tr -d ' ')
  doc_digest=$(grep -o '[0-9a-f]\{64\}' MANIFEST-FORMAT.md | grep -c "$TV_EXPECT")
  if [ "$got" = "$TV_EXPECT" ] && [ "$glen" = "$TV_LEN" ] && [ "$doc_digest" -ge 1 ]; then
    pass "G9 test vector reproduces ($TV_LEN-byte preimage) and matches the doc"
  else
    fail "G9 test vector drift: digest=$got len=$glen doc_hits=$doc_digest"
  fi
else
  fail "G9 test-vector.json is missing"
fi

# --- G10: the commitments table matches the manifests -------------------
# A digest transcribed by hand into a document is a digest that will be wrong.
python3 - > "$WORK/g10.out" 2>&1 <<'G10PY'
import glob, json, re, sys
sys.path.insert(0, ".")
import registry_tool as rt
doc = open("COMMITMENTS.md").read()
found = set(re.findall(r"[0-9a-f]{64}", doc))
bad = []
seen = set()
files = sorted(glob.glob("manifests/*.json") + glob.glob("manifests/*.json.gz"))
if not files:
    print("no manifests found -- the gate would pass vacuously"); sys.exit(1)
for f in files:
    m = rt.load_manifest(f)
    seen.add(m["commitment"])
    if m["commitment"] not in found:
        bad.append(f"{f}: commitment {m['commitment'][:16]} absent from COMMITMENTS.md")
for d in sorted(found - seen):
    bad.append(f"COMMITMENTS.md names {d[:16]}... which is no manifest commitment")
if bad:
    print(chr(10).join(bad)); sys.exit(1)
print(f"ok: {len(seen)} manifests, all present and all accounted for")
G10PY
if [ $? -eq 0 ]; then
  pass "G10 COMMITMENTS.md digests match the manifests exactly"
else
  fail "G10 commitments table drifted from the manifests"; cat "$WORK/g10.out"
fi

echo
if [ $FAILED -eq 0 ]; then echo "ALL GATES PASSED"; exit 0; fi
echo "$FAILED GATE(S) FAILED"; exit 1
