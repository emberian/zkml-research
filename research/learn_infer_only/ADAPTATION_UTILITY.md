# History-dependent adaptation utility control

[EXECUTED] An actual cached **SmolLM2-135M** supplied frozen features for a synthetic
continual-learning task. A 577-scalar learned readout attained **77.84%** held-out
post-change accuracy, against **82.76%** for retrieval over the same model features.
Reset and unrelated-memory swap reduced the readout to **52.03% / 52.64%**. This is
history-dependent utility after teaching context is removed, with a negative result
for preferring the learned neural readout over retrieval on this task.

[EXECUTED] A second two-skill text/paraphrase task failed near chance with the
frozen-model features. An exact additive sliding-window control succeeded on both
skills only when given the generator's structured attributes; that is a useful
small arithmetic target. A later preregistered pooling study improves simple-cue
transfer (below); XOR-like transfer remains near chance.

[EXECUTED] A separate bounded-integer readout retained essentially the same utility
on **32 fresh histories**. Its transition agrees with an independent Python-bigint
reference on **108 random/extremal cases**. No encryption, proof system, private
input issuer or output-release mechanism ran. Every observation, label, state and
model activation was ordinary inspectable plaintext. This is not a Shielded or Dark
resident, a consciousness test, or an A/B no-master-read construction.

## Question, provenance, and protocol

[SOURCE: design reads] The task is `swarm/astra-handoff/ASTRA_HANDOFF.md` §7, read
followed by its companion §7; `SECURITY_GAME.md` supplies the private-observation
origin/exposure model. `docs/DARK-TRAINING.md` §§3–7 and
`notes/low-rank-updates.md` distinguish small updated state from the computation
through which its private information propagates. Current `CANDIDATES.md` supplies
the scope corrections to Route 1 and the explicit remaining release gap.

[SOURCE: model card/implementation read] Model/tokenizer is
`HuggingFaceTB/SmolLM2-135M@93efa2f097d58c2a74874c7e644dbc9b0cee75a2`;
its [pinned card](https://huggingface.co/HuggingFaceTB/SmolLM2-135M/raw/93efa2f097d58c2a74874c7e644dbc9b0cee75a2/README.md) identifies Apache 2.0 (metadata/License).
Weights SHA-256: `80521b40281d6ce74e35c9282c22539e75aa0ac8578892b2a59955ef78d55da1`.
`config.json` and Transformers 4.57.3 `modeling_llama.py` RMSNorm/MLP/attention were read.
Hashes: `model_manifest.json`/`audit.json`; local files only, remote code disabled.

[EXECUTED] Isolated runtime: Python 3.14.7, torch 2.10.0, transformers 4.57.3,
NumPy 2.4.2, CPU float32, eager attention, two torch threads, evaluation mode,
no gradients and no KV cache. Exact dependency versions are in
`experiments/adaptation_utility/requirements-lock.txt`. Offline uv resolution failed;
a bounded pinned install downloaded torch 75.8 MiB and transformers 11.4 MiB.
No model weights were downloaded. Runtime installation output is retained.

[DERIVED specification] Protocol v1 was written before extracting features or seeing
outcomes (`experiments/adaptation_utility/PROTOCOL.md`, hash in each run).
The synthetic public domain contains 289 integer sensor-coordinate pairs
`(x,y) ∈ {-8,…,8}²`. A fixed split reserves 192 pairs for teaching and 97 disjoint
pairs for queries. Each history samples a private balanced quadratic sign rule over
`[1,x/8,y/8,xy/64,x²/64,y²/64]`; first it teaches 96 distinct pairs, then teaches
those same pairs under the opposite rule. This creates a known change point.

[EXECUTED] Development seeds 11000–11007, selection seeds 22000–22007, test seeds
33000–33031 are disjoint. Hyperparameters are selected on the eight selection
histories and persisted before evaluating the 32 test histories. Each query prompt
is only `Sensor reading: x=…, y=…. Response class:`. All 289 actual prompts contain
14 tokenizer tokens. Teaching labels/history never enter a model prompt or KV cache.
The model executes once per public-domain pair, yielding a 576-dimensional final-token
feature. The utility evaluator reuses these fixed features; this does not claim that
secret input-index selection from that cache is free in a protected implementation.

[DERIVED specification] Controls are the frozen model's A/B token preference, no
memory (+1), a fading label mean, kNN over model features, kNN over raw coordinates,
an online normalized-LMS readout over model features (576 + bias), a fixed projected
feature readout (64 + bias), and an explicitly task-engineered quadratic six-feature
readout. The learned readouts **replace the task's output head**; they do not update
transformer weights or establish language-model fine-tuning. The memory evolves as
`m' = rho*m + eta*(label - dot(m,phi))*phi`. Feature centering/scaling uses only
unlabeled teaching-domain features. All methods release one synthetic class.

## Held-out utility and controls

[EXECUTED] Post-change accuracy over 32 independent test histories, each with 97
unseen coordinate queries. Intervals below are mean ± 1.96 history-level standard
error; they are descriptive normal intervals, not 3,104 independent trials.

| Method | Post-change accuracy | Reset | Unrelated memory swap | Stored learned readout |
|---|---:|---:|---:|---:|
| Frozen LM A/B / no memory | 52.03 ± 5.70% | 52.03% | 52.03% | none |
| Fading label mean | 62.89 ± 3.52% | 52.03% | 55.03% | 1 scalar |
| Model-feature kNN, k=1, last 64 | 82.76 ± 2.60% | 52.03% | 50.10% | 64 retained events |
| Coordinate kNN, k=1, last 64 | **91.72 ± 1.42%** | 52.03% | 50.29% | 64 retained events |
| Model-feature LMS, 577 scalars | 77.84 ± 2.74% | 52.03% | 52.64% | 4,616 bytes float64 |
| Projected-model LMS, 65 scalars | 75.55 ± 2.92% | 52.03% | 53.06% | 520 bytes float64 |
| Engineered quadratic LMS | 86.31 ± 2.86% | 52.03% | 53.64% | 48 bytes float64 |

[EXECUTED] The full model-feature readout loses **4.93 ± 1.92 percentage points**
to model-feature kNN in a paired history comparison. The engineered quadratic
readout loses **5.41 ± 2.58 points** to coordinate kNN. Its smaller state is a real
representation tradeoff, not evidence of higher utility. Learned model-feature
readout improves **25.81 ± 5.68 points** over no memory; the reset/swap controls
support attributing this change to individual history rather than the fixed backbone.

[EXECUTED] Reordering each same event multiset from AB to BA changes **100%** of
adaptive-method answers and 0% of frozen/no-memory answers. This is deliberately
strong: phase B is the exact label complement of A. Before-change full-feature LMS
accuracy is 79.67%; after-change accuracy is 77.84%. Raw-coordinate and model kNN
retain only the recent 64 events, so their pre/post-change scores match exactly.
The raw frozen A/B preference is always A on this domain. Saved per-query outputs
and all rule/observation seeds permit recomputing every reported score.

[DERIVED limits] This is nonlinear **interpolation on novel coordinate pairs**, not
an out-of-distribution extrapolation or natural-language understanding result.
The same coordinates recur in the two teaching phases, and the quadratic feature
map is engineered using the task family. Opposite labels make old-rule retention
exactly one minus current accuracy: this does not measure catastrophic forgetting
of unrelated skills. A small sensor classifier is not a cognitive-organism utility
benchmark. The experiment supports retaining adaptation as a useful subproblem,
without justifying a dense learned neural memory over retrieval.

## A fixed-point contract that actually ran

[DERIVED specification] `FIXED_POINT_PROTOCOL.md` was written after v1, before its
own fresh history evaluation (seeds 44000–44031). Hyperparameters remain frozen
from v1; every scale is reported, with no post-test selection. Import features as
`P = clip(round_even(Q*phi), -Q,Q)` and state as integers `M ∈ [-16Q,16Q]^r`.
With public `R = round_even(rho*Q)` and label `y∈{-1,+1}`, the chosen eta=1 transition is:

```text
D = sum_i M_i P_i
s = floor((D + Q/2)/Q)
e = Q*y - s
M'_i = clip(floor((R*M_i + e*P_i + Q/2)/Q), -16Q,16Q)
Infer(P_query) = +1 iff sum_i M_i P_query_i >= 0
```

[DERIVED] Saturation gives the state invariant by construction. For `r≤577` and
`Q≤65536`, a conservative bound on each update numerator is
`(16r+17)Q² + 3Q/2 ≤ 39,724,152,619,008 < 2^63`; dot products are bounded separately
by `16rQ²`. These bounds cover all legal inputs/states, not merely the measured run.
Integer rounding uses nearest, ties upward, including negatives. This is a chosen
bounded-integer specification; an accepted proof must enforce it exactly.

[EXECUTED] Vectorized int64 transitions agree with an independent Python-bigint
reference in 108 random/extremal state/input cases, with explicit positive/negative
rounding-tie checks and range-bound assertions. These are executable tests plus the
stated elementary bound, not Lean theorems. Float64 feature import and the float32
backbone remain outside an exact kernel-refinement result.

| Integer readout | Q=256 accuracy / float agreement | Q=4096 | Q=65536 |
|---|---:|---:|---:|
| 577 scalars | 78.90% / 99.68% | 78.83% / 100% | 78.83% / 100% |
| 65 scalars | 78.13% / 99.71% | 78.16% / 99.94% | 78.09% / 100% |
| Engineered 6 scalars | 87.24% / 99.87% | 87.27% / 99.97% | 87.27% / 99.97% |

[EXECUTED] These are fresh-history outcomes and are not directly paired with the
v1 table. The small discrepancies are retained. The fixed-point script records
saturation counts, max states/intermediates, reset/swap accuracy and all per-history
scores. No learned update or imported feature saturated in these measured histories;
the extremal reference cases separately exercised the bounded contract. It does not silently discard boundary errors or grant approximation slack.

## Private information flow and cost

[DERIVED] A final-only readout permits this division **when queries are public**:

```text
public query -> public tokenizer/backbone -> public phi(query) ---+
                                                               |
private learned memory M --------------------------------------> private score
                                                               |
                                          private sign + authorized class release

private observation -> private tokenization/embedding lookup -> ALL backbone layers
                    -> private phi and label -> private recurrent update -> M'
```

[DERIVED] If the observation issuer is already authorized to know its plaintext,
it can run the fixed public feature extractor itself and send authenticated
`Enc(phi,y)`. This relocates the full-backbone work to an already-informed role;
it does not expose prior learned memory. The issuer computation/quantization and
input origin must be bound to the authorized transition. This option fails if feature
extraction needs the resident's prior private state, or if the issuer is not entitled
to see the observation. It is an architectural option suggested during coordination
with the HE lane, not a proved private-ingress construction.

[DERIVED] If private memory enters any earlier activation, subsequent public-weight
linear maps, attention scores, softmax, RMSNorm, gating, caches and output selection
become private computations. Public weights do not make those activations public.
Private query text also taints tokenization, embeddings and the entire backbone.
Any hidden expert/routing/index choice needs access-pattern protection.

[DERIVED: scalar circuit counts] The pinned model has 30 layers, hidden width 576,
KV width 192, MLP width 1,536, nine query heads. One 14-token private-input feature
pass contains **1,486,356,480 private×public linear-map scalar products**,
**6,773,760 private×private attention products**, and **645,120 gated-MLP element
products**, plus **645,120 SiLU calls**, **854 reciprocal-square-root calls**, and
**3,780 length-14 softmax vectors**. RoPE, RMS scaling/squares, reductions, residual
adds and token lookup are separate rows in `costs.csv`. These are expansion counts,
not packed ciphertext operations, machine instruction counts, or encrypted latency.

[DERIVED] Exact integer readout Learn with private features/label needs `2r`
private×private products, `r` public-rho products, `3r+1` additions, `r+1` private
power-of-two floors and `r` private clamps in this chosen schedule. Infer with public
features needs `r` private×public products, `r-1` sums and a private sign before
recipient-bound release. Secret queries change that multiply role. For the six-state
control, “12 products” therefore omits seven floors and six clamps; it is not a full
cost. Modular multiplication by `Q^-1` does not implement signed integer flooring.

[DERIVED] kNN's generic encrypted representation must protect stored keys/labels,
distance comparisons, selection and accesses. With 64 stored 576-vectors and public
query, dot products using stored private key norms cost 36,864 private×public products
plus 63 private comparisons for k=1; label selection and norm creation remain costs.
The *executed finite-grid evaluator* instead keeps 64 indices and 64 labels (1,024
int64 bytes), plus shared 289² public distance tables (668,168 bytes each). Private
index lookup into these tables was not implemented. That representation shortcut
must not be mistaken for a measured oblivious kNN system.

[EXECUTED] The frozen model contains 134,515,008 parameters and occupied 538,060,032
parameter bytes in float32 (not measured process peak RSS). Feature extraction took
9.839 seconds total for 289 prompts in 19 CPU batches, with 1.530 seconds model load.
The main selection/evaluation script took 4.427 seconds, and fixed-point controls
8.951 seconds. These host times came from a shared workstation and are not HE/proof
benchmarks or amortized production throughput.

[OPEN: full system bill] Ciphertext/key sizes, authenticated private ingress,
oblivious tokenization/table lookup, secure floors/clamps/nonlinearities, proofs,
release, bootstrapping/refresh, communication, continuity, deployment randomness,
serialization and multi-epoch exposure remain unimplemented. Plaintext state bytes
are not encrypted state bytes. No model utility percentage prices any of these.
An authorized class oracle may reveal its learned boundary; confidentiality would
still be relative to that oracle, with query/fork/update budgets specified.

## Text transfer and independent-skill retention follow-on

[EXECUTED] The second task executed **384 actual frozen-model text prompts** in
20.242 CPU seconds, with no new weights/training. Two arbitrary individual skills
classify (soft/rigid leaves × wet/dry soil) and (familiar/unfamiliar addressee ×
formal/casual event). Each skill's hidden rule is balanced over its four combinations,
including projection and XOR/XNOR rules. Teacher, selection-query and final-query
entities, templates and cue paraphrases are disjoint. Query prompts contain only
unlabeled descriptions; final hidden features never consume history, labels or a KV
cache. All four logical cue combinations occur in teaching: this tests transfer to
new surface forms, not unseen logical combinations or open-ended language ability.

[DERIVED specification] `TEXT_TRANSFER_PROTOCOL.md` preceded execution. Eight
independent development histories, 16 selection histories and 32 final histories use
separate seeds 51000…, 52000…, 53000…. Each teaches skill0 A, then independent skill1 B,
then changes skill0 to -A, with 64 events per phase. Both skills are tested after each
phase on 64 held-out text queries apiece. Shared/routed model readouts store 577/1,154
scalars; routed kNN divides the SAME total item budget across two skill queues.
The public skill identifier selects a route. An eight-dimensional feature control
gets the generator's TRUE cue/skill attributes; that is an explicitly privileged
structured-input control, not evidence that a neural model parsed the text.

[EXECUTED] Final two-skill accuracy (mean ± normal history-level 95% half-width):

| Selected method | Final held-out text accuracy | Skill0 changed | Skill1 retained |
|---|---:|---:|---:|
| No memory | 50.00% | 50.00% | 50.00% |
| Shared model kNN, 128 items | 51.25 ± 2.13% | 52.73% | 49.76% |
| Routed model kNN, total128 items | 50.49 ± 0.63% | 48.58% | 52.39% |
| Shared model LMS | 50.37 ± 0.44% | 50.10% | 50.63% |
| Routed model LMS | 48.71 ± 1.60% | 47.17% | 50.24% |
| Routed lexical kNN / LMS | 50.00% | 50.00% | 50.00% |
| True-attribute eight-state LMS | 100.00% | 100.00% | 100.00% |

[DERIVED] The frozen-feature approaches failed to demonstrate useful held-out
paraphrase transfer on this constructed task. The result cannot judge language models
generally: this is one small base model, final-token features, particular synthetic
surface forms and a narrow online readout. Routed methods have zero cross-skill
interference **by construction**, because another skill never updates their state;
zero interference at chance accuracy is not successful skill retention. The structured
attribute control both retains B and learns -A, proving the task/update evaluator has
a nonvacuous positive case. Its unrelated-memory swap score is 50.78%.

[EXECUTED] Reversing only skill0's update order changes 100% of routed model answers
on skill0 and 0% on skill1, although those answers remain near chance. Shared model
kNN also changes 74.51% of skill1 answers under that reversal: the independent skill
is affected. Order sensitivity alone is therefore not a utility or retention result.
`text_transfer_results.json` retains every phase/interference metric; selection grids,
records, seeds, decisions, model manifest and exact scripts have matching prefixes.

[DERIVED: costs] Public query features still permit private final-only readouts.
Private text observations taint the full transformer or must be encoded by an issuer
already entitled to know them. Actual text lengths and batch padding are retained in
`text_transfer_model_manifest.json`; the longest executed padded batch has 25 tokens.
At n=25, the same scalar formulas give 2,654,208,000 public-weight products and
21,600,000 attention private×private products, before nonlinearities and feature
normalization. Skill routing, text length, queue slot and access pattern are declared
metadata here. Concealing them needs extra machinery. No text-transfer percentage
changes the private-ingress, numerical-refinement or restricted-release residuals.

## Exact additive window: bounded forgetting without LMS feedback

[DERIVED specification] The coordinator requested a windowed signed-feature control;
`TEXT_WINDOW_PROTOCOL.md` was written before its outputs. An issuer who already knows
the observation and label supplies `Z=y*clip(round_even(127*phi),-127,127)` as signed
int8 entries. Store a queue and `C=sum(queue)` as int32. A full-queue Learn is exactly
`C'=C+Z_new-Z_expired`; Infer is `sign(C·P_query)`. No learned-error product, inverse,
resident floor or clamp occurs in this update. Source feature extraction/quantization
and private input authenticity remain obligations. It is a different learner from LMS.

[EXECUTED] Window settings were selected only on the original text-selection histories.
This follow-on shares the original held-out test histories and is a related control,
not an independent validation set. Every window size is retained in the selection log.

| Selected integer window | Final text accuracy | Plain queue | Plain accumulator |
|---|---:|---:|---:|
| Model shared, W128, r577 | 48.24% | 73,856 bytes | 2,308 bytes |
| Model routed, totalW128, r577 | 49.78% | 73,856 bytes | 4,616 bytes |
| Lexical routed, totalW64, r52 | 50.00% | 3,328 bytes | 416 bytes |
| Structured attributes shared, W128, r8 | **100.00%** | 1,024 bytes | 32 bytes |
| Structured attributes routed, totalW64, r8 | **100.00%** | 512 bytes | 64 bytes |

[EXECUTED] Both structured controls learn the changed skill0 and retain independent
skill1 at 100%; reversing skill0 history changes its answers and leaves skill1 alone.
Reset gives 50%, unrelated-memory swap 50.78%. Every update's incremental accumulator
was checked against an independent full Python-integer queue sum: **122,880 checks**.
Every evaluated int32 score matched a Python-bigint dot: **143,360 agreements**.
Max observed score magnitude was 258,064. The full script took 252.221 seconds,
dominated by these deliberately redundant references; it is not an update benchmark.

[DERIVED] For W≤128,r≤577, the queue invariant gives `|C_i|≤127W≤16256` and
`|C·P|≤rW127²≤1,191,223,424<2^31`. These are universal range bounds for the declared
inputs, not a cryptographic noise proof. Resident Learn costs 2r integer add/subtracts,
and public-query Infer r products, r-1 adds and private sign. Queue cost is O(Wr),
plus per-route head/count and state-authentication data. `text_window_costs.csv`
separates these counts from source encoding and the unimplemented protected bill.

[DERIVED, conditional] An additive ciphertext realization can remove an expired
contribution's noise algebraically when it subtracts the **identical retained old
ciphertext**. Re-encryption of its plaintext is not that cancellation. The HE lane owns
the actual construction/parameter audit. This experiment ran no ciphertext operations,
bootstrapping or release. The required proof must bind queue admission/eviction,
current state, issuer/feature origin and authorized release, including rollback policy.

[EXECUTED diagnostic] Re-querying original teacher surface forms with the ORIGINAL
selected settings gives model kNN 76.05%, routed model LMS 62.35%, shared LMS 57.15%,
and structured attributes 100%. These are explicitly **in-sample** fit checks,
not held-out success. Partial fitting and failure of transfer coexist; the evidence
does not isolate a single cause or justify changing model settings on test outcomes.
`text_transfer_audit.json` recomputes 416 saved method/history accuracy rows and
checks disjoint surface forms, balanced rules and exact event-multiset reversal.

## Preregistered representation study on fresh text

[EXECUTED] `representation_PROTOCOL.md` fixed final-last-token and masked means after
10/20/30 blocks before execution, using NEW entities/templates/cues and history seeds
61000…/62000…/63000…. All settings were selected/persisted before final evaluation.
One 384-prompt actual-model pass collected all features; no downloads or training.
Selection chose mean-after10 for routed LMS and additive windows. On 32 test histories,
LMS attained **64.53 ± 4.52%**, against its fresh last-token baseline 53.74%; paired
improvement **10.79 ± 4.18 points**. Routed window attained **63.16 ± 4.19%**;
shared window **63.23 ± 3.79%**. Selected routed kNN attained 60.52%; the routed-LMS
advantage over it was **4.00 ± 4.10 points**, so this comparison remains uncertain.

[EXECUTED] Routed LMS retained skill1 at 72.31% and adapted changed skill0 at 56.74%;
routed window 69.38%/56.93%. A posthoc diagnostic attributes gains to linear cue rules;
XOR/XNOR strata remain near 50%. Routed retention follows separate memories, not a
learned protection mechanism. Selection also chose a shared-kNN representation that
performed worse than its last-token baseline; every prespecified outcome is retained.
`representation_audit.json` recomputes 960 accuracy rows and 30 selection decisions.

[DERIVED] All model features still have 576 coordinates (577 with bias). Mean pooling
at public length n adds 576(n-1) sums and 576 public scalings. At n=27, the 10-block prefix
counts 955,514,880 public-weight products plus 8,398,080 private attention products when
source tokens are private. Actual extraction ran all 30 blocks; this is no measured
prefix speedup. Public skill/length and entitled-issuer conditions remain explicit.
`representation_costs.csv`/`representation_results.csv` retain costs and full results.

## Evidence, searches, and resume

[EXECUTED] Evidence is under `experiments/adaptation_utility/`: manifests pin models,
runtime and hashes; selection/results/history/decision files retain all outcomes;
audit and cost files keep verification/roles separate, with task prefixes as named above.
Generated `.npz` caches are local, ignored and reproducible; hashes are retained.
No companion tree or shared verdict/ledger was edited by this lane.

[EXECUTED] Commands run from repository root (stdout/stderr kept in same-name logs):

```sh
A=research/learn_infer_only/experiments/adaptation_utility
uv venv --python /opt/homebrew/bin/python3 "$A/.venv"
uv pip install --python "$A/.venv/bin/python" -r "$A/requirements-lock.txt"
"$A/.venv/bin/python" "$A/extract_features.py"
"$A/.venv/bin/python" "$A/run_controls.py"
"$A/.venv/bin/python" "$A/fixed_point_controls.py"
"$A/.venv/bin/python" "$A/cost_and_audit.py"
"$A/.venv/bin/python" "$A/extract_text_features.py"
"$A/.venv/bin/python" "$A/text_transfer_controls.py"
"$A/.venv/bin/python" "$A/text_window_controls.py"
"$A/.venv/bin/python" "$A/text_transfer_audit.py"
"$A/.venv/bin/python" "$A/representation_extract.py"
"$A/.venv/bin/python" "$A/representation_controls.py"
"$A/.venv/bin/python" "$A/representation_audit.py"
```

[DERIVED correction] Initial install used four pins, then `uv pip freeze` made the replay lock; logs retain script outputs.

[EXECUTED] Scry/Kagi: **0/0**; one primary model-card read/fetch; local caches searched
with `ls`, notes/docs with `rg`. No literature-absence claim or private logs/state read.

[DERIVED decision] Keep the exact readout/window contracts and all retrieval controls.
Pooling supplied a narrow positive for simple cues; neither small state nor that utility establishes protected computation. No `VERDICTS.md` change is proposed.

[OPEN next] Nonlinear cue transfer remains unresolved. The 577-coordinate mean10
window is a useful new arithmetic/utility target alongside the eight-coordinate
structured control. Neither has authenticated protected feature extraction or an
actual restricted release gate here; a retained full reader key is not tier-A/B absence.
