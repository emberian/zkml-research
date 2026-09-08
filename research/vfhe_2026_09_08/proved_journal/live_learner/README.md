# Teach new text, prove the update, then query the committed model

[EXECUTED] A newly encoded bank-card teaching example reached a freshly
generated native proof, durable model commit and real BFV query in 42.37 seconds.
The query used only committed class ciphertexts. Its decoded score, 241,320,
matched the direct integer comparison performed afterward. A failed proposal
left the accepted state unchanged. See [the report](REPORT.md),
[recorded result](results/live001/RESULT.json) and [scope](SCOPE.md).

[SOURCE interface] `live.py` provides `init`, `teach`, `query`, `teach-query`,
`status`, and separate `stage`/`commit` commands. It uses the existing useful
learner's plaintext E5 encoder and native BFV issuer/host/reader operations,
the production [proof pipeline](../../update_pipeline/README.md), and the frozen
[multiclass journal](../multiclass_successor/README.md). Completed predecessor
sources, model states, keys and feature caches remain unchanged.

From the repository root, using the existing local ML environment:

```sh
LIVE_PYTHON=research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python
LIVE_APP=research/vfhe_2026_09_08/proved_journal/live_learner/live.py
LIVE_MODEL=/absolute/new-proved-model

"$LIVE_PYTHON" -B "$LIVE_APP" init "$LIVE_MODEL" \
  --class card_arrival --class cash_withdrawal_charge

"$LIVE_PYTHON" -B "$LIVE_APP" teach-query "$LIVE_MODEL" \
  --request-id my-first-teach --label card_arrival \
  --text 'My replacement bank card still has not arrived after three weeks.' \
  --query-text 'The bank mailed my new card, but I am still waiting for it.'

"$LIVE_PYTHON" -B "$LIVE_APP" status "$LIVE_MODEL"
```

[SOURCE behavior] Initialization creates a fresh BFV key pair and canonical
zero ciphertext in the new instance. The declared class set starts empty under
an explicitly imported zero checkpoint. The first update uses zero accumulator
and outgoing operands. The adapter derives counts and FIFO entries from
committed receipts, with capacity eight and zero outgoing before capacity.
Those application rules are trusted adapter logic, not conclusions of the
arithmetic proof. Only the initial update was exercised in this demonstration.

[SOURCE behavior] `teach-query` keeps one encoder object for teaching and
querying. It reads the already cached E5 model locally and writes feature-cache
entries only inside the new instance. Teaching runs actual issuer encryption
and host arithmetic into a tentative case. The production Lean exporter creates
a witness, the native prover generates a new proof, a fresh verifier accepts it,
and the journal independently verifies it before checking/committing the
current global parent. A successful teaching response is emitted only after
that commit. Querying evaluates the exact accepted CAS heads and then invokes
the instance's surviving full BFV reader.

[SOURCE behavior] Use a new request ID for a new teaching example. Repeating an
already completed ID with the same class/text returns its original committed
receipt. A reused ID with changed class/text refuses. A stale or failed proposal
does not become visible to queries; use a new ID to stage against the current
head. The stage command explicitly returns `committed:false` and
`visible_to_query:false`; it is not a successful teaching response.

```sh
"$LIVE_PYTHON" -B "$LIVE_APP" stage "$LIVE_MODEL" \
  --request-id next-teach --label card_arrival --text 'Another teaching example'
"$LIVE_PYTHON" -B "$LIVE_APP" commit "$LIVE_MODEL" --request-id next-teach
"$LIVE_PYTHON" -B "$LIVE_APP" query "$LIVE_MODEL" --text 'A query about my card'
```

[SOURCE prerequisites] This is a research-workspace command. It requires the
existing E5 cache/ML environment, pinned native binaries and the proof
pipeline's compiled Lean overlay/dependencies. No package installation, model
download, benchmark or fine-tuning occurs. Source/binary/template identities
are pinned into the new instance and journal genesis; preserve those source
bytes to resume it.

[EXECUTED reproduction] `run_demo.py` runs one fresh teaching/query fixture plus
the model-root refusal through these same methods. Its retained instance is
under ignored `runtime/live001/`; public evidence is under `results/live001/`.
A new `--run live002` selects a fresh instance. The retained
[public case](results/live001/case/source_event.json) and
[fresh proof](results/live001/proof.bin) can also be supplied to the existing
native `verify-update` command with the approved expiry template.

