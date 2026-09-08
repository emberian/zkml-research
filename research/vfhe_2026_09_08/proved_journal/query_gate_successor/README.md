# Prove every active class score before receiving an answer

[EXECUTED] A fresh two-class run completed two genuine proved teaches and two
new class-query proofs before its first private receive. An omitted-active-class
proposal refused without a read. The actual answer selected
`cash_withdrawal_charge` with score 238,227 versus 211,756; both scores matched
the later integer comparisons. The complete run took 306.24 seconds.
[Report](REPORT.md), [result](results/gated001/RESULT.json).

[SOURCE implementation] `gate.py` extends the live learner with a public query
proof gate. It proves both signed ciphertext/plaintext products and their final
subtraction for every active class, verifies each proof against exact
accumulator/query/output bytes, checks the current accepted model head, and
only then allows the adapter's private receive call. The existing full BFV key
still exists; this is an executed protocol boundary, not a decryption
restriction. See [scope](SCOPE.md).

[SOURCE interface] From the repository root, use the existing ML environment
and the frozen native/Lean query pipeline:

```sh
GATE_PYTHON=research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python
GATE_APP=research/vfhe_2026_09_08/proved_journal/query_gate_successor/gate.py
GATE_MODEL=/absolute/new-query-gated-model

"$GATE_PYTHON" -B "$GATE_APP" init "$GATE_MODEL" \
  --class card_arrival --class cash_withdrawal_charge

"$GATE_PYTHON" -B "$GATE_APP" teach "$GATE_MODEL" \
  --request-id card-example --label card_arrival \
  --text 'My replacement bank card has still not arrived after three weeks.'

"$GATE_PYTHON" -B "$GATE_APP" teach "$GATE_MODEL" \
  --request-id fee-example --label cash_withdrawal_charge \
  --text 'A cash machine charged an extra fee when I withdrew money from my account.'

"$GATE_PYTHON" -B "$GATE_APP" query "$GATE_MODEL" \
  --request-id new-fee-query \
  --text 'Why was I charged a fee for taking cash out at an ATM?'
```

[SOURCE interface] `teach` uses the preserved live adapter's staged update,
fresh update proof and durable model commit. `query` generates a new public
query, evaluates each active class from accepted CAS heads, runs the joined
query proof pipeline for each, independently reconstructs/verifies each case
again at the gate, then returns the full-reader answer. Empty classes are
excluded by the existing committed-count ranking policy. Every nonempty class
must be included exactly once. Query IDs must be new; a request prepared against
an obsolete global head refuses before private receive.

[SOURCE interface] The Python `QueryGate.prepare`, `accept` and `receive`
methods expose the stages for applications that need separate public proof
work. `prepare` explicitly returns `prepared_not_received`. `accept` writes a
durable public receipt only after complete proof coverage and an authoritative
current-head check under the journal write lock. `receive` rechecks request,
current head, all accepted class bindings and output byte hashes. The normal
CLI uses all three in order; there is no query answer from a tentative stage.

[SOURCE prerequisites] The native runtime and fixed template come from
[`query_runtime`](../../query_runtime/REPORT.md) and
[`query_arithmetic`](../../query_arithmetic/README.md). The production runner
uses its frozen Lean source/compiled dependency policy. This research-workspace
command also needs the existing local E5 cache and useful learner environment.
No model download or benchmark is part of the command. The query gate pins its
source, pipeline/config, native verifier, template and underlying model genesis;
preserve those bytes to resume the instance.

[SOURCE preservation] `run_demo.py` builds a fresh two-class instance and runs
the genuine path plus one omitted-active-class refusal. It does not reuse or
relabel the already decrypted `live_learner/results/live001` query. Its new
private state and large witness traces stay under ignored `runtime/`; selected
public records and exact proof cases are retained under `results/`.

[EXECUTED reproduction] The actual command was the existing ML Python running
`research/vfhe_2026_09_08/proved_journal/query_gate_successor/run_demo.py`.
Use a fresh `--run gated002` to repeat it in a new instance. The retained
`results/gated001/class0/` and `class1/` contain public cases and proofs for
`card_arrival` and `cash_withdrawal_charge`, respectively. They can be checked
with the frozen native `verify TEMPLATE CASE PROOF` command without a model or
reader key.
