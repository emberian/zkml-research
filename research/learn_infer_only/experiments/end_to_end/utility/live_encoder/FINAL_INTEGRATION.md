# Normal live-text and frozen-utility integration: completed

[EXECUTED, read-only consolidation] **Yes: `journal/results/live_text_002`
completed actual text → model feature encoding → signed public-key input
encryption → BFV Learn → durable authority installation → finalized reader Infer.**
The interpreter repair is in the executed source. The normal frozen
`utility_002` run also completes both histories, all 480 commands and all 96 oracle
comparisons. This note resolves the earlier frontend “retry pending” state.
No model, cryptographic benchmark or additional experiment was rerun for this
consolidation; only normal reports, logs and their source dependencies were read.

## The normal live path actually executed

[SOURCE + EXECUTED] `journal/live_text.py:12` first issues an authorized Infer
against the initial state. At `:16` it calls the live issuer frontend as a real
subprocess; `:20` imports only its ciphertext and signed authorization into the
ordinary host proposal path. `:22` admits the Learn, and `:23` issues the second
Infer through the same authorization/admission/reader path. The private oracle
comparison at `:25`–`:26` checks the first answer is zero and the second equals the
integer dot product of the live vector and public query. The report retains the
match/change predicates without exporting text, features or scalar answers.

[EXECUTED] `live_frontend_call.json` records exit 0 from system Python invoking
`utility/live_encoder/issue_text.py`, with a new synthetic text JSON as issuer
input, the run's ordinary issuer config/current head, and request id `live-learn`.
The opaque record id is `opaque-live-observation-1`. Its exact argv is retained
there; the source-derived outer reproduction command is:

```sh
python3 research/learn_infer_only/experiments/end_to_end/journal/live_text.py \
  --root NEW_NORMAL_JOURNAL_RUN_DIRECTORY \
  --input research/learn_infer_only/experiments/end_to_end/utility/issuer_oracle/live_encoder/future_new_text.json
```

[DERIVED reproduction boundary] Use a new directory; preserve completed runs.
The ignored private input and public query fixtures must exist. This command
was **not** rerun by this consolidation. The exact executed frontend argv,
role commands and outputs already exist in `live_text_002`.

[EXECUTED] The private frontend process record shows two successful children:

| Child | Interpreter | Result |
|---|---|---|
| `issuer_encode_prepared.py` | Existing adaptation model venv | Actual 577-coordinate encoding; exit 0; no cached-record substitution |
| `journal/roles.py issue` | `/opt/homebrew/opt/python@3.14/bin/python3.14` | Actual issuer encryption and Learn signature; exit 0 |

[EXECUTED] The earlier `live_text_001` encoder succeeded but journal issuance
failed because the model venv lacked `cryptography`. The repaired wrapper uses
`sys.executable` for that second child and retains the model venv for encoding.
No dependency installation was required. Its executed SHA256 is
`f084c71abf6f903c89fec34c1a2dcdb526baccafc153749a1d9b722874523365`.

[EXECUTED] The normal event log contains exactly these accepted admissions:

| Request | Authority revision | Delivery |
|---|---:|---|
| `before-live-observation` | 1 | Reader received; acknowledged |
| `live-learn` | 2 | Learn installation, not a release |
| `after-live-observation` | 3 | Reader received; acknowledged |

[EXECUTED] Both oracle comparisons pass; the post-Learn answer differs from the
initial zero. Public replay recomputes the ciphertext transitions and reaches
revision 3, route 0 admissions 1/queue 1, route 1 admissions 0/queue 0. The learned state
ciphertext differs from the canonical zero. The 47 retained crypto commands all
exit 0 and include one issuer encryption, one host Learn plus independent
authority recomputation, two host Infers plus authority recomputation, two reader
decryptions, and a separate public replay of all three operations.

[SOURCE] Normal authority `authority.py:59` recomputes the proposed ciphertext
transition; `:64` records the finalization and state in one SQLite transaction;
COMMIT at`:66` precedes publication at`:71`. The reader verifies the selected
query ticket/finalization context before its full-key decryption at
`reader.py:58`. These are the actual normal implementation paths, not a claim
of a Python-to-Lean refinement or of security against compromised trusted roles.

## Model, arithmetic and source provenance

[SOURCE + EXECUTED] The live encoder is the source previously checked on records
0/64/256/320, where 2,308 quantized coordinates exactly matched the cached study.
It loads local SmolLM2-135M revision
`93efa2f097d58c2a74874c7e644dbc9b0cee75a2`, with 134,515,008 parameters. Each live
invocation checks the pinned model/tokenizer/config files. CPU float32, eager
attention, eval/inference mode, two torch threads and one interop thread are
fixed by the source. It executes all 30 blocks and takes the masked mean of direct
block 9 output, then applies the public teacher-only per-route calibration/bias,
float64 normalization and nearest-even signed-int8 quantization. The new normal
text invocation has `cached_quantized_comparison=false`: it performs the model
forward and does not fetch an old feature vector as its result.

[SOURCE] The runtime inventory pins torch 2.10.0, transformers 4.57.3 and NumPy 2.4.2
on Python 3.14.7/macOS arm64. This consolidation adds no model execution or runtime
measurement. The normal frontend's retained child metadata supplies the timing
below. Its model encoder/policy/source hashes agree with current bytes.

[SOURCE + EXECUTED] Genesis fixes two public routes, W=32 per route, 577 signed
coordinates bounded by 127, BFV degree 4096, plaintext modulus 4,294,828,033,
ciphertext moduli 2,199,023,190,017 and 4,398,046,486,529, variance 10 and selected
coefficient 576. The signed-score bound is 297,805,856. Learn adds the fresh input
and expires the exact original queued ciphertext; Infer uses reversed positive
and negative public query polynomials. The actual normal source and binary match
their genesis pins.

| Artifact | Verified SHA256 |
|---|---|
| `utility/issuer_encode_prepared.py` | `7fb22689e1abafc4dbf6a55c90a88ad9643af02c33112002b0b1b0dac9f97689` |
| `utility/encoder_policy.json` | `de2e7356049a76bba16a09d1ac38ee8de622004f28df0c7e3aa70d7b5d347ce3` |
| `journal/live_text.py` | `b2bea81321c617e95e8b860da1cf55369a7e571f9b8088c8d907f1fa6c15a498` |
| `crypto/src/main.rs` | `22f0cbe304772263094c228f6598eb4cbfa00432902ba9e5de0993f6735e1b7c` |
| `crypto/target/release/resident-crypto` | `9c79c02e7d919ecdc24851c6f77e50ed6990397bd669f571a886f8e2b85058c2` |
| `journal/results/live_text_002/report.json` | `d50b9c703be75c1612daf2f74ea36cfab3acefebc25ec9e5190a36bd1369f141` |
| `journal/results/utility_002/report.json` | `abd662f8572965f2e4c126455e68694e1e7ab0135802179fa797f6c32e77ddaa` |

[EXECUTED] Current normal `roles.py`, `model.py`, `common.py`, `authority.py`,
`reader.py`, `run.py` and `datasets.py` also match the respective retained report
pins. Private input/vector/scalar contents and their hashes are not republished
in this note. Source/code/model policy hashes are public provenance.

## Both complete frozen utility histories

[EXECUTED] `utility_002` retains the original seeds 63000/63001 and the exact
metadata-selected event chronology. Per history: 192 Learn, 48 Infer, 128 original
ciphertext expiries, 240 committed revisions and one historical exact retry.
Each route finishes with 32 queued contributions; admissions are 128 on route 0
and 64 on route 1. Every oracle score matches, and ciphertext replay is exact.

[EXECUTED, independent retained-log census] The two histories together contain
384 host Learn commands,384 corresponding authority Learn recomputations, 96 host
Infers and96 authority Infer recomputations. **All96 Infer events actually call
the reader decryption command.** The semantic denominator remains80 outputs
from nonempty encrypted state plus16 known empty-route zeros. In this integration,
those zeros traverse the same ciphertext/finality/reader path; they are still
known zeros and are not evidence of private learned content.

[EXECUTED] Every command exits0:14,867 crypto subprocess records per history.
Every first admission is accepted; the241st response is the original request's
recorded replay. The event IDs, kinds and routes exactly match
`utility/public_event_index.json`. Reader scalar stdout is omitted from public
command logs. Host/authority/replay crypto argv contain only inspect/Learn/Infer
commands and no `--sk` or plaintext `--vector` argument. This is concrete
argv/data-flow evidence, not OS isolation or a noninterference proof.

[SOURCE: unchanged utility results] This integration does not improve semantic
accuracy. The fixed subset remains 18/32=56.25% final accuracy and 52/96=54.17%
across its selected checkpoints. The original full 32-history mean10 window study
reported 63.16%±4.19points; its text/domain and denominator differ from this subset.
The later PCA/product successor failed: 56.99% versus 59.90% for the original
features on 64 new histories, despite a small nonlinear-stratum gain. One live
text changing one score is computational integration, not a new adaptation result.

## Costs and limits that remain visible

[EXECUTED] The normal live frontend takes 3.5925s end-to-end: its model child takes
3.4345s, and encrypted/signed issuer child 0.1027s. Inside the model child, reported
load is 0.2062s and feature forward 0.0557s; these subdivisions exclude framework
startup and other work. The three authority submission round trips are 58.06ms,
26.20ms and57.28ms. Those intervals include nested work; do not add them to
subprocess subtotals as if they were disjoint. The normal report does not retain
a complete overall wall time or RSS for this live integration. Separate four-record
encoder probes peaked near 1.42GB RSS; that is contextual evidence, not a measured
RSS for `live_text_002`.

[EXECUTED] The full utility histories take 387.259s and 362.684s, about 749.943s
combined, including setup, verification, orchestration, persistence and replay.
Each ends with 67 unique current ciphertext references (the 64 queued originals,
two accumulators and canonical zero),5,701,901 ciphertext bytes and7,601 state
manifest bytes. Retained authority CAS is 34,663,205 bytes/423 blobs per history;
the delta replay artifact is709,660bytes. SQLite database+WAL+SHM totals 3,674,008
bytes per history. The CAS, database and replay artifacts overlap in information
but are separate retained files; none is process RSS. Current window storage is
bounded by W; preserved ciphertext/history evidence continues growing with history.

[DERIVED trust boundary] This is benchmark R: a plaintext observation issuer,
a trusted command authorizer, an honest keyless continuity authority and a single
explicitly trusted full-key BFV reader. Ed25519 authenticates those roles. The
issuer's feature/range assertion is trusted; a signature does not prove a hidden
feature originated from SmolLM2, its range, noise or honest encryption coins.
The reader contains the unrestricted BFV secret and the baseline relies on honest
authority recomputation. Separate local processes and mode0600 files do not isolate
roles from their shared machine operator. Availability, independent persistence,
physical delivery behavior, PQ composition and implementation refinement remain
separate from these successful normal-path observations.

## One bounded next utility experiment

[HYPOTHESIS recommendation; not executed] Test whether **public semantic feature
calibration** repairs the specific failure exposed by the privileged-attribute
control. Fit two small ridge readouts per public skill to predict its two written
cue attributes from teacher mean10 features. Attribute supervision comes only
from public synthetic teacher metadata and must be disclosed as extra supervision.
Choose one ridge strength from a fixed small grid using selection-text attribute
accuracy, then freeze it. Do not fit the private history's category rule at this
stage or use test attribute labels in query features.

[DERIVED proposed functionality] Clip the two predicted attribute probabilities
into[0,1] and form the four fixed conjunction features: `(1-a)(1-b)`, `(1-a)b`,
`a(1-b)`, `ab`. Put them in that route's four slots, pad to 577 and retain the exact
signed-int8 W=32 window. This directly tests whether the missing semantic attribute
readout can be learned from public examples. It differs from the failed unsupervised
PCA/product expansion and from supplying true query attributes to the learner.

[DERIVED proposed bounds] Preregister at most 128 new test texts with new names,
templates and cue paraphrases, plus 64 new history seeds, before extraction or
outcomes. Use one cached-model pass for all new texts, no backbone training,
no downloads and a 60-minute total cap. A dual ridge solve needs only 64×64 matrices
per route on the current teacher corpus. The added per-text map has 1152 fixed
coefficient products for its two attribute heads and four conjunction products;
resident BFV state/operations remain unchanged. Record actual CPU/RSS and source
visibility rather than claiming small learned state makes private computation cheap.

[DERIVED proposed acceptance] Compare original 577 features, the frozen calibrated
features, no memory and the privileged true-attribute control on every new history.
Require a preregistered material paired gain (for example≥10 points with a positive
descriptive interval) and a substantial XOR/XNOR gain, while retaining all joint
strata, reversal and independent-skill retention results. Also report attribute
prediction accuracy independently: failure there would constrain this simple
readout family, while good attributes with poor utility would locate a different
problem. Keep failure; do not replace test texts or tune after seeing outcomes.

[DERIVED confidentiality scope] That calibration and its feature products run at
an already-entitled plaintext issuer or public-query processor. It is not an
operator-private encoder. A positive utility result would justify a new explicitly
named fixture, not changing the completed fixture or claiming master-read absence.
