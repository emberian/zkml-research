# Public semantic fixture prepared for later encrypted consistency testing

[EXECUTED] Deterministic materialization and its independent audit completed.
The actual schedule is exactly 384 signed Learn vectors, 96 query evaluations,
256 same-contribution expiries, and 480 total chronological events. Six
checkpoints contain 12 route-state vectors. Of the 96 queries, 16 address an
empty route and 80 address a nonempty route; none of those 80 scores is zero.
No cryptographic program or model encoder was run in this tranche.

[DERIVED: scope] This is an integration-correctness subset of the already
frozen full utility experiment. It is not a new utility estimate. The histories
were selected by the first two identifiers, 67000/67001. Query selection takes
the lowest two IDs per task and gold attribute stratum, frozen before vector
materialization:

```text
256,257,272,273,288,289,304,305,
320,321,336,337,352,353,368,369
```

[EXECUTED] Features use only the parent's exact model-predicted bits:
Q=127*e_(4*route+2*a+b), padded to577. The history's true category rule supplies
the signed teaching label. Gold attributes are used for balanced identifier
selection and the test oracle, never in place of inferred feature bits.
All 96 integer scores and 12 checkpoint vectors match the corresponding
already frozen full run. Every parent manifest entry—53 files—remains unchanged.

## Artifacts and schema

[EXECUTED] `fixture.json` is the canonical combined **PUBLIC synthetic research
fixture**. It contains `histories`, `source_records`, `query_records`,
`learn_vectors`, `events`, `checkpoints`, `counts` and source hashes. Every Learn
event indexes its full signed577-vector and identifies its `expired_event_id`
or null. Every Infer indexes a public query row. `event_ordinal` counts both
operations; `learn_step` counts only updates. Queue identity matters: a later
encrypted implementation must expire the ciphertext from that same event,
not a newly encrypted equivalent clear vector.

[EXECUTED] `public_query_records.json` supplies all 16 public577D row records,
source IDs, inferred bits, separate selection-only gold bits and source-error
labels. Duplicate predicted rows are retained. `public_event_index.json`
contains only event ID, ordinal, history index, operation and route. It carries
no source text, teaching label or clear contribution.

[EXECUTED] `integer_oracle.json` maps each Infer event ID to exact scalar,
sign, target, correctness, public empty-route status and source-error status.
It also preserves the original full-survey semantic, baseline and privileged
diagnostic records for that same history/checkpoint/query. It is a test-oracle
input, not a host/authority input, even though the fixture is public.

[EXECUTED] `full_survey_reference.json` retains the full original denominators,
all 15 fresh factual errors, original comparison counts and acceptance gates:
semantic 7,462/8,192; original mean10 4,178/8,192; gold 8,192/8,192. The full source
study's wet-soil weakness is not replaced by the selected subset. Selected
query records 256 and 288 retain their actual wrong wet-soil classification.
Their paired second-template records 257 and 289 retain their different inferred
rows. No subset accuracy estimate is emitted.

## Regeneratable role inputs

[EXECUTED] `runtime/` is ignored derived data. It currently contains 384
issuer vector JSON files, 16 public query JSON files, an issuer input index
and a test-oracle scalar map. All 402 files have a complete hash census in
`runtime_hash_census.json`; the independent audit verifies their bytes and
mode0600. These are **PUBLIC research vectors**, not confidential observations.
The file modes express local role layout and do not supply OS isolation.

[EXECUTED] The ready issuer/coordinator path is:

```text
runtime/issuer/input_index.json
```

[DERIVED: replay interface] Learn entries expose `issuer_vector_path`; Infer
entries expose `public_query_vector_path`. Each vector file is exactly a JSON
array of577 integers plus a newline. Future source issuance may consume a
Learn vector and publish only its resulting ciphertext/authorization to the
host. The fixture itself grants no approval to execute encryption, admission,
delivery or a model. Use a distinct run directory/genesis when a later run is
authorized; the earlier full E2E fixture is unchanged.

[EXECUTED] `emit_runtime.py` reconstructs the ignored files from retained
fixture/oracle data, or byte-verifies them if they already exist. It is a
standalone regeneration entry point after a checkout where ignored inputs
are absent. At the original repository path it checks the retained 402-file
census. Moving the repository changes absolute paths inside the index; clear
vector bytes remain identical. No cryptographic executable is dispatched.

```text
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/materialized/emit_runtime.py
```

## Rank and recipient-coalition limit

[EXECUTED] There are eight query records on each route but only four unique
rows. Exact rational elimination gives rank 4 per route and rank 8 globally.
All eight duplicate row records remain in the 16-record/96-evaluation
denominator. Basis-covering plant source IDs are 257,256,289,288 for coordinates
0,1,2,3; letter IDs 320,336,352,368 cover 4,5,6,7. No teaching occurs between the
16 queries of a checkpoint, so each checkpoint's rows refer to one unchanged
learner aggregate.

[DERIVED] On each route the effective aggregate is C=127*z for four integer
net label counts. An exact basis score is127*C_j=16129*z_j. Recipients who
collectively hold a spanning set of these exact scores at one checkpoint
determine that whole aggregate. Padding to577 does not conceal effective
aggregate coordinates. This fixture therefore carries **no recipient-coalition
aggregate-state privacy claim**. Sign-only outputs do not determine exact
magnitudes, and queue order is a distinct state object. This is algebraic
image accounting, not an executed cryptographic or interface-disclosure test.

## Verification and pins

[EXECUTED] The independent audit recomputes all 384 signed vectors from saved
inferred bits and integer labels, replays96 exact query scores and256 identity
expiries, checks12 checkpoint vectors and16 empty-route cases, verifies all
402 generated files, and computes row rank using `Fraction` elimination.
Materialization took0.601 seconds and audit0.315 seconds on this shared machine.
Their logged commands and outputs are retained as `prepare.*`, `build.*`
and `audit.*`. All stages use the existing Python environment; no dependency
installation, metered search, new model score or crypto run occurred.

[EXECUTED] Pre-materialization freeze SHA-256:
`1fe42024b756c5af49b2a27c210e35ed0b5660148d749cff8667e7989a107198`.
Canonical fixture SHA-256:
`bcdda47d227853e546427e9fb42de489b7c227ace65b10a9099cec81f4481b11`.
Integer-oracle SHA-256:
`119b66dd3e39730897948f5f3021e73a234fa163adf43c9e27189c3264dc31cd`.

[OPEN] A later authorized encrypted consistency run must still execute and
compare its own ciphertext results. No prepared plaintext fixture, correct
integer oracle or materialization success counts as that encrypted result.
