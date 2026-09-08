# Fast live teach → prove → commit → proved query

[EXECUTED] A fresh two-class run completed in **21.20 seconds**, including process
startup, model loading, two teachings, four fresh proofs and verification before
the first two private receives. [Report](REPORT.md),
[result](results/fast001/RESULT.json), [scope](SCOPE.md).

[SOURCE interface] Run the complete fixed semantic fixture in a fresh instance:

```sh
python3 -B research/vfhe_2026_09_08/proved_journal/fast_live_successor/run.py --run another001
```

[SOURCE interface] For a custom local teaching session, from the repository root:

```sh
FAST_PYTHON=research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python
FAST_APP=research/vfhe_2026_09_08/proved_journal/fast_live_successor/gate.py
FAST_MODEL=/absolute/new-fast-live-model

"$FAST_PYTHON" -B "$FAST_APP" init "$FAST_MODEL" \
  --class card_arrival --class cash_withdrawal_charge

"$FAST_PYTHON" -B "$FAST_APP" teach "$FAST_MODEL" \
  --request-id card-example --label card_arrival \
  --text 'My replacement bank card has still not arrived after three weeks.'

"$FAST_PYTHON" -B "$FAST_APP" teach "$FAST_MODEL" \
  --request-id fee-example --label cash_withdrawal_charge \
  --text 'A cash machine charged an extra fee when I withdrew money from my account.'

"$FAST_PYTHON" -B "$FAST_APP" query "$FAST_MODEL" \
  --request-id new-fee-query \
  --text 'Why was I charged a fee for taking cash out at an ATM?'
```

[SOURCE interface] `teach` stages the ciphertext update, generates a fresh proof,
verifies it at the journal and commits the current parent before returning
success. `query` proves every active class result against the current accepted
model, verifies each again and records public acceptance before calling the
full reader. `status` returns the accepted head. New query IDs must be fresh;
stale model bindings refuse. Reuse one `QueryGate` object in a Python process to
retain the loaded encoder across operations, as the measured driver does; the
separate shell commands above have their own process/model loading costs.

[SOURCE interface] `live.Live.stage` / `commit` and `QueryGate.prepare` / `accept`
/ `receive` expose the stages. Staged states supply no successful teaching/query
response. The underlying capacity-eight FIFO and global model journal remain
unchanged. The demo checks initial updates with declared zero outgoing inputs;
it does not add another expiry demonstration.

[SOURCE configuration] The new instance explicitly selects native witness
pipelines through `PIPELINES.json`. Their generators execute Lean-generated
plans but remain untrusted. The approved update/query templates and native
provers/verifiers are the same as the preserved predecessor. No automatic
pipeline upgrade or fallback modifies an existing instance. This workspace
command uses its existing ML environment, cached E5 model and frozen native
binaries; it does not download models or build companions.

[SOURCE retention] The completed sources, `launches/fast001/` and
`results/fast001/` are frozen. Public cases, proof files, pipeline commands,
acceptance and model history are retained; private keys/features and large
witness traces stay under ignored `runtime/`. The full key survives, so the
protocol gate is not a cryptographic decryption restriction.

