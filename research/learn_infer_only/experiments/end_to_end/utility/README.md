# Text, learning history and exact output: the frozen E2E utility fixture

[EXECUTED] This directory maps **all384 teaching events and all96 preselected
queries** to their original text, phase, public skill route and label. Independent
integer replay checks every score and all12 phase/route state vectors. A second
audit reconstructs all480 event vectors from the cached model features. No model
was run, trained or downloaded in this mapping tranche. These are issuer/oracle
artifacts; an actual E2E admission/release run is reported by the integration lane.

[DERIVED exposure] `issuer_oracle/mapping.json`, the human transcripts and oracle
summaries contain plaintext synthetic teaching text and labels. They are owner,
issuer and test-oracle analysis artifacts. **They are not host/authority inputs
or public execution logs.** The entire corpus was already public research data;
directory separation and file permissions do not establish OS isolation or make
this a confidentiality experiment. Fresh unknown-ingress smoke data is a different
integration fixture and is not copied or reported here.

## The actual task, without a stronger story

[SOURCE: original `representation_PROTOCOL.md` and records] A fixed pretrained
SmolLM2-135M converts short descriptions into vectors. An external window learns
arbitrary binary categories from those vectors and observed labels. It does not
generate a letter, recommend plant care or finetune the language-model weights.
There are two public routes: plant descriptions and recipient/occasion descriptions.
The categories ±1 are randomly chosen balanced synthetic rules, not real-world
horticultural or social judgments.

[SOURCE + EXECUTED] Each frozen history teaches64 plant examples, then64 letter
examples, then64 plant examples with the original rule reversed. The resident
retains the last32 signed feature contributions per route and their sum. Query
answers are the sign of the sum's dot product with a public query vector.
The tie convention is `score >= 0 → +1`; thus the untrained route is a known
constant answer, not a successful encrypted inference.

[SOURCE] Teaching histories do not appear in the model's query context. Teaching,
selection and test names, full templates and cue phrases are disjoint. Every
logical cue combination was taught: this tests transfer to new textual surface
forms, not unseen logical combinations. The selected representation is the masked
mean after10 decoder blocks, plus a bias and teacher-only per-route centering and
scaling. Its vector has577 coordinates, quantized with nearest-even rounding to
signed integers in[-127,127]. No target labels enter query feature extraction.

## An illustrative sequence selected before inspecting its scores

[EXECUTED] `TRANSCRIPT_SELECTION.md` chose the first history63000, teacher
records0/64 and held-out records256/320 by metadata alone. The plant teaching
example is “Inspect Acacia for plant care: flexible leaves grow above soggy soil.
Category:” with label+1 in phase1 and−1 in phase3. Its held-out paraphrase asks
about Rudbeckia with “bendable greenery” above “muddy ground.” The letter teacher
uses Anna, a “longtime acquaintance” at an “awards banquet”; the held-out example
uses Rosa, a “recognizable colleague” at a “diplomatic function.” Full exact text
is retained in the two complete issuer/oracle transcripts.

| Fixed query | After plant teaching | After letter teaching | After plant reversal |
|---|---|---|---|
| Rudbeckia / plant | score−7697, sign−1, target+1: wrong | unchanged, wrong | score2154, sign+1, target−1: wrong |
| Rosa / letter | structuralzero, sign+1, target+1 | score4512, sign+1, target+1 | unchanged4512, correct |

[DERIVED] The plant answer changes with learning but remains wrong. This example
does **not** establish successful adaptation. The letter score is retained exactly
while the other route changes. That retention comes from separate routed memories;
it is not a learned interference-avoidance mechanism. The chosen example is kept
despite its failure, and no successful query replaces it.

## Every selected query remains in the denominator

[EXECUTED] The frozen integration uses seeds63000/63001 and the two lowest test
record IDs in each `(skill,a,b)` group:16 queries per checkpoint, three checkpoints
per history. This exact metadata rule was registered in the earlier encrypted
window tranche before its scores were generated. It yields96 queries, including
16 empty-route structuralzeros and80 nonempty encrypted arithmetic targets.

| History | Phase1 plant / letter | Phase2 plant / letter | Phase3 changed plant / retained letter |
|---|---|---|---|
| 63000 | 4/8, 4/8(empty) | 4/8, 6/8 | 4/8, 6/8 |
| 63001 | 4/8, 4/8(empty) | 4/8, 4/8 | 4/8, 4/8 |

[EXECUTED] Across both histories, phase accuracy is16/32,18/32,18/32; the final
subset is **18/32=56.25%**. All checkpoints together are52/96=54.17%; the nonempty
queries are44/80=55%. These descriptive subset counts are not a fresh utility
estimate or benchmark confidence interval. `issuer_oracle/summary.json` retains
the complete phase/skill/history breakdown. Both complete transcripts contain
every192 teaching events and every48 checkpoint queries for their history.

[SOURCE: original frozen utility result] On the original full32 held-out histories
and all128 test texts per history, this selected routed window attained
**63.16% ±4.19 percentage points**, with changed plants56.93% and retained letters
69.38%. The ± quantity is the original descriptive normal history-level interval
half-width. The earlier study's nonlinear XOR/XNOR strata remained near chance;
its true-attribute positive control used privileged generator metadata. That broader
study and the fixed E2E subset have different denominators. Neither the modest
utility nor exact encrypted arithmetic proves no-master-read execution.

## Files and the integration interface

[EXECUTED] `mapping_manifest.json` pins the frozen fixture, original protocols,
model/cache/selection sources and complete mapping outputs. The unchanged fixture
SHA256 is `41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0`.
Exact copies of the original representation protocol and encrypted-window
preregistration are in `original_preregistrations/`.

[DERIVED API] `public_event_index.json` contains only
`{event_id, history_index, event_ordinal, kind, route}`. IDs are
`h0-e0001`…`h0-e0240` and `h1-e0001`…`h1-e0240`.
For each history,64 Learn events precede16 Infer events in each of three phases.
This chronology contains480 actual commands; the12 oracle state checkpoints
are not additional public commands. Opaque IDs are bookkeeping, not a hiding
primitive against this small known corpus.

[DERIVED API] The private mapping joins an event to `history_seed`, `phase`,
Learn `step` or Infer `record_id`, original record text/attributes, exact source
fixture line, and vector hash. Learn entries include observed labels and the
identity of the original contribution expired from that route. Infer entries
include exact oracle score, sign, target and public-empty status. The host must
not load this file; the trusted driver may attach its metadata only at the issuer
or test-oracle reporting boundary.

[EXECUTED] `materialize_inputs.py` regenerates384 issuer vector JSON arrays
(mode0600 in a mode0700 directory),16 public query arrays, an issuer-only input
index and96 oracle scalar records. `materialized_inputs_manifest.json` pins each
derived file. These redundant split inputs and indices are gitignored: recreate
them from the retained script and frozen combined fixture. The journal lane's
coordinator reads `issuer_oracle/input_index.json`; only the issuer subprocess
receives an `issuer_vector_path`. Host/authority receive its actual ciphertext,
not the vector, text, label or oracle. Public query arrays may enter the explicit
public-query path. `issuer_oracle/expected_scalars.json` remains oracle-only.

## Encoder feasibility and cost boundary

[EXECUTED, read-only] `check_encoder_feasibility.py` finds the original local
Python3.14.7 environment with torch2.10.0, transformers4.57.3 and NumPy2.4.2.
All eight model/tokenizer/config files match their original hashes at revision
`93efa2f097d58c2a74874c7e644dbc9b0cee75a2`; their total is272,437,465 bytes.
The original model manifest counts134,515,008 parameters. No dependency install,
model construction or forward pass was needed for this check.

[OPEN prepared command] `issuer_encode_prepared.py` is a separate issuer command
for `{text,route,label}`. It uses only that cached revision and the exported
public teacher calibration in `encoder_policy.json`, emits a mode0600 vector
and offers an exact comparison against a named cached record. Only its syntax
and CLI help were checked here. Its actual single-prompt execution, timing and
quantized agreement with the original batched cache remain unexecuted. It does
not encrypt, authenticate source provenance or certify a plaintext range to a
keyless verifier. No parent pipeline silently substitutes this untested path.

[DERIVED] The final-only window has two577-coordinate accumulators,64 retained
vectors and public route/head/count metadata. Source encoding can run at an
issuer already entitled to see the observation because its fixed feature map
does not depend on prior private resident state. All source token processing,
attention and pooling still cost the issuer work. If the operator must not see
those tokens, running that same encoder at the operator would taint all executed
layers and require a separate protected-computation solution. Small learned
state alone does not measure that cost.

[SOURCE + DERIVED] Actual source extraction used all30 blocks while collecting
block9 output; a10-block prefix count is not a measured speedup. The original
HE fixture's stable state payload is64 queued ciphertexts plus2 accumulators,
5,611,452 serialized bytes at85,022 bytes each. This is a standalone reference,
not a new E2E cost: verification, signatures, durable journals, retained history,
reader key, issuer model and process memory must be counted by the integration.
The parent benchmark has an explicit full-key trusted reader, not master-read
credential absence or a distributed custody ceremony.

## Reproduction and limits

[EXECUTED] From the repository root, with output retained in matching logs:

```sh
python3 research/learn_infer_only/experiments/end_to_end/utility/build_mapping.py
python3 research/learn_infer_only/experiments/end_to_end/utility/materialize_inputs.py
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/audit_mapping.py
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/check_encoder_feasibility.py
```

[EXECUTED] All four commands exit0; `audit_mapping.json` verifies all480 event
vectors against the actual cached representation, their source record bindings,
every materialized vector and the public index's exact field allowlist. This
lane makes no E2E encrypted-delivery claim beyond the earlier frozen arithmetic
results it cites. Model runs0; training0; downloads0; metered searches0.
