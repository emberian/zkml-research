# A proved update service for a class model

[EXECUTED] Actual learner events 65 (`card_arrival`) and 66
(`cash_withdrawal_charge`) committed consecutively under one durable global
head. Each accepted proof replaced only its selected class accumulator and
bound the resulting model root in its receipt. A stale global-parent request
refused; process reopen preserved both heads; retrying event 65 returned its
original receipt with no new proof execution or journal row.
[Report](REPORT.md), [result](results/sequence001/RESULT.json),
[scope](SCOPE.md).

[SOURCE interface] `service.py` is a separate successor to the preserved
[single-class service](../README.md). Its model is a fixed class-name map to
`{acc_sha256, learner_event}` entries. A model root is SHA-256 of canonical JSON
`{"schema":"proved-class-model-map-v1","classes":MODEL}`. It is a digest of the
whole map, not a Merkle tree. The global head contains that map/root, global
learner event, journal revision, genesis, recipient and last receipt hash.

[SOURCE interface] Genesis imports an explicit checkpoint. The demonstrated
checkpoint contains two classes at global learner event 64; it does not claim
to represent or prove the complete original eight-class history. A new journal
can import a larger explicitly approved class set through the same interface.
Class insertion/removal or migration is not implemented by an update request.

## Initialize and submit

From this directory, initialize with a fresh absolute state path:

```sh
python3 -B service.py init --root /absolute/new-state \
  --binary /absolute/vfhe-proved-operation --template /absolute/template.json \
  --expected-binary-sha256 BINARY_SHA256 --expected-template-sha256 TEMPLATE_SHA256 \
  --checkpoint /absolute/checkpoint.json --initial-files /absolute/initial-files.json \
  --recipient READER_ID
```

[SOURCE interface] The checkpoint schema is
`proved-model-checkpoint-v1`, with `global_learner_event`, `classes` and
`provenance`. The class entries have the fields above. `initial-files.json`
maps exactly those class names to absolute ciphertext file paths; initialization
checks each byte hash and declared key/parameter envelope. Genesis retains the
checkpoint's exact bytes/hash, model root and provenance. The caller approves
the imported checkpoint; old transition proofs are not required or implied.

```sh
python3 -B service.py request --root /absolute/new-state \
  --case /absolute/case --proof /absolute/proof.bin \
  --request-id UNIQUE_REQUEST_ID --out /absolute/request.json
python3 -B service.py submit --root /absolute/new-state --bundle /absolute/request.json
python3 -B service.py head --root /absolute/new-state
python3 -B service.py history --root /absolute/new-state
```

[SOURCE interface] A case contains `acc.ct`, `fresh.ct`, `old.ct`, `out.ct`,
native-exported `public_ntt_rows.json`, and `source_event.json` under schema
`useful-prototype-expiry-proof-join-v1`. Its class, event, prior class event and
four ciphertext hashes are bound in the request. The case's accumulator must
equal that class's current head, while the request's parent hash/revision and
parent model root must equal the current global state. Its event must be the
next global learner event. The server independently calculates the map with
exactly that one class replaced and checks the proposed next model root.

[SOURCE interface] The same implementation runs as a local Unix-socket service:

```sh
python3 -B service.py serve --root /absolute/new-state --socket /tmp/vfhe-model.sock
python3 -B service.py rpc --socket /tmp/vfhe-model.sock --request /absolute/rpc.json
```

RPC bodies remain `{"op":"head"}`, `{"op":"history"}` or
`{"op":"submit","bundle":"/absolute/request.json"}`. Exact historical
request retries return the retained receipt; a new request using an obsolete
global parent refuses. Accepted ciphertexts remain available under
`cas/<sha256>` for the existing full BFV reader. No private key is loaded by the
journal. The source, native binary and approved template are genesis-pinned;
preserve their bytes to reopen this state.

## Retained execution

[EXECUTED] The command was:

```sh
python3 -B research/vfhe_2026_09_08/proved_journal/multiclass_successor/run_sequence.py
```

[SOURCE interface] A new `--run sequence002` repeats that small saved-input
sequence in a new state directory. It imports public saved records and verifies
the two existing proofs; it does not generate new proofs or rerun learning.
`checkpoint_from_records.py` exports the selected public prefix and checks
recorded accumulator lineages and selected ciphertext bytes. Its checks are
provenance checks, not retrospective proofs of that prefix.

