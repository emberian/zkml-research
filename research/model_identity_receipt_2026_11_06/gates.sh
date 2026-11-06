#!/bin/bash
# Gates G11-G16 of the model-identity receipt (extending registry/gates.sh G1-G10). Exit 0 iff all pass.
#   ./gates.sh MAVERICK_DIR [--sample]     MAVERICK_DIR holds manifest-v2.json, wsums.txt, files.sha256 from mir-stream
# --sample also runs G11, which re-fetches tensors from Hugging Face (needs the network and ~10 GB of transfer).
# Needs: cargo, lake, python3, openssl; FlashProve at $FLASHPROVE (default /Users/ember/src/FlashProve).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
M=${1:?MAVERICK_DIR}
FP=${FLASHPROVE:-/Users/ember/src/FlashProve}
BIN=$here/stream/target/release/mir-stream
V=$here/lean/.lake/build/bin/mir-verify
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
fail=0
gate() { if [ "$2" = 0 ]; then echo "PASS $1"; else echo "FAIL $1"; fail=1; fi; }

(cd "$here/stream" && cargo build --release -q) && (cd "$here/lean" && lake build -q mir-verify Mir) || exit 2

# G11: v2 roots and integer digests reproduce from a seeded sample of tensors re-fetched by range request
if [ "${2:-}" = --sample ]; then
  base=https://huggingface.co/unsloth/Llama-4-Maverick-17B-128E-Instruct-GGUF/resolve/41032e5471dd6ea5b349062d978626215d6c5bba/UD-Q4_K_XL
  "$BIN" sample --manifest "$M/manifest-v2.json" --base "$base" --count 6 --seed "${G11_SEED:-20261106}"
  gate "G11 sample of tensors re-fetched and recomputed equals the manifest" $?
else
  echo "SKIP G11 (pass --sample)"
fi

# G12: our wsums.txt is FlashProve's, by the digest they published
want=$(awk '$2=="model/wsums.txt"{print $1}' "$FP/examples/maverick/expected.txt")
got=$(shasum -a 256 "$M/wsums.txt" | cut -d' ' -f1)
[ "$want" = "$got" ] && python3 -c "import json,sys; sys.exit(0 if json.load(open('$M/manifest-v2.json'))['wsums_sha256']=='$want' else 1)"
gate "G12 sha256(wsums.txt) = FlashProve expected.txt ($want)" $?

# G13: the streamed files are the published ones
cmp -s "$M/files.sha256" "$FP/examples/maverick/weights.sha256"
gate "G13 files.sha256 = FlashProve weights.sha256, byte for byte" $?

# G14: teeth on synthetic shards from FlashProve's oracle: one flipped weight byte, two swapped experts, another e_res
python3 -I "$FP/weight_sums/tests/oracle.py" 7 11 "$W/o" >/dev/null 2>&1
"$BIN" local --eres 11 --out "$W/base" "$W/o"/oracle-0000{1,2}-of-00002.gguf >/dev/null 2>&1
python3 -I "$here/receipt/teeth.py" "$BIN" "$W/o" "$W/base/manifest-v2.json" "$W"
gate "G14 teeth: a flipped byte, swapped experts and another e_res each change the named roots" $?

# G15: the conversion equals FlashProve's exact-rational oracle on six shard pairs
ok=0
for seed in 1 7 12345; do for er in 3 11; do
  python3 -I "$FP/weight_sums/tests/oracle.py" $seed $er "$W/s$seed-$er" >/dev/null 2>&1
  "$BIN" local --eres $er --out "$W/s$seed-$er.out" "$W/s$seed-$er"/oracle-0000{1,2}-of-00002.gguf >/dev/null 2>&1
  cmp -s "$W/s$seed-$er.out/wsums.txt" "$W/s$seed-$er/expected.txt" || ok=1
done; done
gate "G15 wsums.txt = oracle expected.txt on 3 seeds x 2 e_res" $ok

# G16: the committed receipt verifies under its evaluator key; every falsifier is refused, including colluding-
# evaluator cases and strict-mode recomputer cases, on receipts built here from the real manifest with fresh keys;
# the axioms are as pinned
"$V" check "$here/receipt/maverick-receipt.json" --cid "$(awk '$2=="commitment-id"{print $1}' "$FP/examples/maverick/expected.txt")" \
  --trust "$(cat "$here/receipt/demo-evaluator.pub.hex")" >/dev/null
gate "G16a the committed Maverick receipt verifies" $?
openssl genpkey -algorithm ed25519 -out "$W/ev.pem" 2>/dev/null; openssl genpkey -algorithm ed25519 -out "$W/rc.pem" 2>/dev/null
mk() { python3 -I "$here/receipt/make_receipt.py" --manifest "$M/manifest-v2.json" --expected "$FP/examples/maverick/expected.txt" \
  --weights-sha "$FP/examples/maverick/weights.sha256" --key "$W/ev.pem" --mir-verify "$V" "$@" >/dev/null; }
mk --out "$W/h.json" && mk --out "$W/n.json" --eval-node meta-bf16 --benchmark "Meta model card" --scores "MMLU Pro 80.5" &&
  mk --out "$W/s.json" --recomputer-key "$W/rc.pem" --recompute converts,commits
rpk=$(openssl pkey -in "$W/rc.pem" -pubout -outform DER | tail -c 32 | xxd -p -c 64)
python3 -I "$here/receipt/falsify.py" "$W/h.json" "$V" --negative "$W/n.json" --eval-key "$W/ev.pem" \
  --strict-receipt "$W/s.json" --recomputer "$rpk" >"$W/falsify.log"
gate "G16b falsifiers (receipt/falsify.py; $(grep -c REFUSE "$W/falsify.log") refusals)" $?
"$here/lean/check-axioms.sh" >/dev/null
gate "G16c axioms as pinned" $?
exit $fail
