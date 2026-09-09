# Continuing live nonlinear verified learner

[EXECUTED] The fresh two-class flow completed in **23 minutes 49 seconds**: two
proved teachings, one all-class nonlinear query, **248 new proof objects**,
then two private reads. All expected values matched and the intended class
`cash_withdrawal_charge` was returned. There was no saved proof reuse.
[Report](REPORT.md), [result](RESULT.json), [public export](PUBLIC_EXPORT.md).

[SOURCE interface] From the repository root, initialize a new instance once:

```sh
PYTHON=research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python
APP=research/vfhe_2026_09_08/proved_journal/live_nonlinear/live.py
"$PYTHON" -B "$APP" init /absolute/new-model \
  --class card_arrival --class cash_withdrawal_charge
```

Then continue teaching and querying the same durable model:

```sh
"$PYTHON" -B "$APP" teach /absolute/new-model --request-id example1 \
  --label cash_withdrawal_charge \
  --text 'An extra withdrawal fee appeared after I used the ATM.'
"$PYTHON" -B "$APP" query /absolute/new-model --request-id question1 \
  --text 'Why did the cash machine charge me an additional fee?'
"$PYTHON" -B "$APP" status /absolute/new-model
```

[SOURCE] `Live.teach` issues the supplied text into the next class lane, proves
all four-prime ciphertext update equations and freshly verifies them before
committing the new global model revision under SQLite's write lock. Each class
retains an eight-entry FIFO; the ninth and later teaches subtract the exact
oldest committed issued ciphertext and reuse its lane. New request IDs are
required. The class set is fixed at initialization. Reuse one `Live` object to
keep the encoder loaded across calls. The initial run does not exercise expiry.

[SOURCE] `Live.query` evaluates every active class against the current accepted
model, generates all 116 fresh proof chunks per class, freshly verifies every
class, and checks the current head again before durably publishing acceptance.
Only then does it call the full reader. It ranks the resulting mean squared-dot
kernel scores using exact rational comparison. `prepare_query`, `accept_query`
and `receive` expose the public/private phases. Partial proof production is
never a successful query result.

[SOURCE] `pipeline.py` supplies reusable `produce-update`, `verify-update`,
`produce-infer` and `verify-infer` entrypoints. Its approved profile selects
existing Lean-derived relations and native readers/verifiers; the producer
selects caller input/capture paths and creates fresh proofs for every phase.
There are no historical case or proof paths in `PIPELINE.json`. The only new
native code maps raw four-prime teaching ciphertexts to the already generated
paired-MAC relation and invokes the unchanged backend. It writes no AIR.

[SOURCE] The fixed initial example is `run.py --run live001`: two supplied
teaching texts, one query, one fresh encoder batch, 16 update proofs and 232
complete-kernel proofs, then exactly two private reads and plaintext comparison.
It is a single functional two-class example, not a benchmark or accuracy study.
Later calls use the same interface and accepted state, without another setup.

[SCOPE] Public text encoding, encryption and initial key/zero setup, key
membership/custody, raw decoding, public seed expansion, NTT/linear maps,
request/lane/FIFO policy, journal and proof backend remain explicit TCB. The full
reader survives, so this is not a private resident or a cryptographically
restricted reader. The arithmetic source includes exact updates, packed
products/key switching, basis extension, tensor products and whole rescale.
[CONTRACT.md](CONTRACT.md) fixes the phase ordering and remaining limits.
