# A useful restricted semantic issuer, with a small exposed aggregate image

[EXECUTED] The frozen SmolLM3 factual scorer followed by the existing W32
learner achieved 7,462/8,192 final labels (91.0889%) on 128 new text surfaces
across 64 new histories. The original mean10 representation achieved
4,178/8,192 (51.0010%); the privileged true-attribute diagnostic achieved
8,192/8,192. Every preregistered gate passed. This is evidence for a trusted
plaintext semantic issuer feeding a restricted four-bin learner. No encryption,
restricted release, operator-private 3B cognition or no-master-read property
is established by these results.

[EXECUTED] The positive aggregate does not remove a specific weakness:
15/256 factual bits were wrong, all wet-soil classifications. On the
hard-leaf/wet-soil combination, only 8/16 new text pairs were factually
correct. Final utility on that same semantic stratum was 696/1,024 (67.9688%),
passing the frozen 65% threshold with little margin. All errors, including
their full source text and logits, are in `ERRORS.md`; all 128 predictions
are in `test_decisions.csv`.

## What was fixed and what learned

[DERIVED: executed protocol] Framing A, its four public axis definitions,
model revision, float16 MPS forward, batch8 position/padding policy, token
alternatives 15/16 and tie-to-0 rule were reused unchanged from teacher
selection. The previous actual teacher predictions were reused; no teacher
was re-encoded. The new source-scorer code is asserted identical to the
selected scorer except four result-metadata changes. No prompt, decoder,
feature map, model weight or acceptance gate was selected after a new score.

[DERIVED] For public route s and inferred bits a,b, Q is 127 at coordinate
4*s+2*a+b and zero elsewhere, padded to 577. This is the existing privileged
attribute control's feature map with actual model-predicted bits substituted.
Each route keeps the most recent 32 signed label contributions, adds new
contributions and subtracts the identical expired contribution. A public
query receives sign(C dot Q), with zero mapped to +1. The history's balanced
Boolean category rule is learned through its labels; it is not provided to
the source model. The source model and its explicit semantic instructions
provide the attribute abstraction. The learner itself is a four-bin recency
vote, not a learned neural representation.

[EXECUTED] All 128 new texts, names, full templates and full cue phrases were
checked against the two original generators and the attribute-calibration
and E5 tests. They use two templates and eight new names per task, balanced
over four attribute combinations. Meanings and ordinary words overlap; this
is fresh surface transfer within the same public semantic task. Seeds
67000–67063 were frozen after a local JSON numeric-seed search found no prior
use. Each history has 64 plant updates, 64 letter updates, then 64 plant
updates with its original balanced rule reversed. None of the new test
texts enters a teaching stream or another example's model context.

## Full utility denominator and retention

[EXECUTED] Three methods, 64 histories, three checkpoints and 128 queries
produce 73,728 scores. Each method has 24,576 checkpoint scores and 8,192
final queries. The table shows correct/total for the task after its relevant
learning phase; it includes all fixed histories.

| Measure | Semantic A | Original mean10 | Gold-attribute diagnostic |
|---|---:|---:|---:|
| Plant after initial learning | 3,398/4,096 | 2,016/4,096 | 4,096/4,096 |
| Plant retained while letters learn | 3,398/4,096 | 2,016/4,096 | 4,096/4,096 |
| Letter after learning | 4,096/4,096 | 2,145/4,096 | 4,096/4,096 |
| Plant after rule reversal | 3,366/4,096 | 2,033/4,096 | 4,096/4,096 |
| Letter retained after plant reversal | 4,096/4,096 | 2,145/4,096 | 4,096/4,096 |
| Final total | 7,462/8,192 | 4,178/8,192 | 8,192/8,192 |

[EXECUTED] The paired semantic-minus-original gain is +40.0879 percentage
points with a descriptive history-paired 1.96*SE half-width of 1.4704 points
(range of history gains: +28.125 to +53.9063 points). Semantic performance
is 8.9111 points below the gold diagnostic. The 64 histories repeat the same
128 new texts; this interval measures history variation, not uncertainty
over an independent language population. The zero-state/reset prediction
has exactly 50% accuracy because every query target set is balanced.

[EXECUTED] Untouched-route states and outputs are exactly equal before and
after the other route learns. This is retention provided by separate routed
state/queues, not evidence that the source model's weights learned two skills
without neural interference. Plant accuracy changes slightly after reversal
because that phase has a separately frozen teaching order/window.

| Final rule type | Skill instances | Semantic A | Original mean10 | Gold |
|---|---:|---:|---:|---:|
| Simple balanced rules | 86 | 5,165/5,504 (93.8408%) | 2,830/5,504 (51.4172%) | 5,504/5,504 |
| XOR/XNOR rules | 42 | 2,297/2,688 (85.4539%) | 1,348/2,688 (50.1488%) | 2,688/2,688 |

[EXECUTED] Nonlinear-instance gain is +35.3051 points; simple-rule gain is
+42.4237 points. These six balanced Boolean rules operate on the same two
defined attributes. This is not arbitrary nonlinear learning or a new task
family. The joint rule strata below preserve both tasks' pairing; no history
was resampled after its rules or outcomes were known.

| Plant / letter rule types | Histories | Semantic A | Original mean10 | Gold |
|---|---:|---:|---:|---:|
| Simple / simple | 27 | 3,207/3,456 | 1,780/3,456 | 3,456/3,456 |
| Simple / XOR-XNOR | 12 | 1,446/1,536 | 757/1,536 | 1,536/1,536 |
| XOR-XNOR / simple | 20 | 2,252/2,560 | 1,319/2,560 | 2,560/2,560 |
| XOR-XNOR / XOR-XNOR | 5 | 557/640 | 322/640 | 640/640 |

| Task and true `(a,b)` | Semantic final labels | Original final labels | Gold |
|---|---:|---:|---:|
| Plant 00: flexible, wet | 702/1,024 | 502/1,024 | 1,024/1,024 |
| Plant 01: flexible, dry | 1,024/1,024 | 486/1,024 | 1,024/1,024 |
| Plant 10: hard, wet | 696/1,024 | 635/1,024 | 1,024/1,024 |
| Plant 11: hard, dry | 944/1,024 | 410/1,024 | 1,024/1,024 |
| Letter 00: known, formal | 1,024/1,024 | 435/1,024 | 1,024/1,024 |
| Letter 01: known, informal | 1,024/1,024 | 297/1,024 | 1,024/1,024 |
| Letter 10: unknown, formal | 1,024/1,024 | 832/1,024 | 1,024/1,024 |
| Letter 11: unknown, informal | 1,024/1,024 | 581/1,024 | 1,024/1,024 |

## Factual errors and frozen gates

[EXECUTED] The model correctly scored 241/256 new factual bits (94.1406%)
and 113/128 complete pairs (88.2813%). There were no exact ties. Plants:
113/128 bits and 49/64 pairs; letters: 128/128 bits and 64/64 pairs. Leaf
flexibility and both letter axes each scored 64/64; soil moisture scored
49/64 (76.5625%). All 15 errors predicted dry for a wet source in the first
template, which says `root soil holding a large amount of water`. Seven
occur in flexible/wet texts and eight in hard/wet texts. The full error list
is retained; the shared phrase is a descriptive association, not a proven
cause or a reason to patch individual texts.

| Factual stratum | Correct bits | Correct pairs |
|---|---:|---:|
| Plant 00 | 25/32 | 9/16 |
| Plant 01 | 32/32 | 16/16 |
| Plant 10 | 24/32 | 8/16 |
| Plant 11 | 32/32 | 16/16 |
| Each of the four letter strata | 32/32 | 16/16 |

[EXECUTED] All eleven frozen gates passed: factual >=90% overall and >=85%
per task; utility >=75% overall and per task; paired gain >=10 points with
positive descriptive lower endpoint; nonlinear gain >=10 points; simple
regression no worse than 5 points; exact untouched-route retention; >=65%
in every populated joint rule stratum and every task/attribute stratum.
The factual gates were per task, not per axis: the weaker soil axis was not
silently assigned a passing 85% threshold. The two lowest utility strata,
wet/flexible at 68.5547% and wet/hard at 67.9688%, remain material limits.

[EXECUTED] Mean full-vocabulary mass on the two allowed token alternatives
is 0.598060. This remains a fixed two-score decision interface, not proof
that unconstrained generation would emit the requested bare token or JSON.
Both old JSON preflights and their failures remain frozen and unaccepted.

## Exact arithmetic and effective image

[EXECUTED] The independent audit verifies all 73,728 score/sign/target
records, all 24,576 primary scores using Python integers, 384 primary
checkpoint vectors, every one of 12,288 update-to-direct-queue comparisons,
8,192 identical-contribution expiries, and 384 untouched-route state/output
equalities across the three methods. It also checks all 256 new factual
decisions, paired gains, input bounds and the observed feature image. No
model is rerun in the audit. Original teacher/selection baseline coordinates
match their earlier cached arrays exactly.

[EXECUTED] Each route exhibits all four one-hot basis vectors in both its
teacher and its new test predictions. The exact rank is 4 per route, 8 for
the two disjoint routes, inside 577 ambient coordinates per route. The
primary's largest observed absolute score is 225,806, below the exact
one-hot bound 516,128; its state coordinates stay in [-4,064,4,064]. Original
mean10's largest score is 75,356, below its generic bound 297,805,856.

[DERIVED] Four exact basis-score functionals determine the current route
aggregate: C=127*z and score_j=16129*z_j. Their matrix on z is 16129*I4,
with determinant 67,675,234,241,018,881. Ambient padding leaves no hidden
aggregate coordinates once such a spanning exact-score family is available.
Four sign-only results do not determine magnitudes, and aggregate scores do
not generally identify queue order. `IMAGE_SCOPE.md` and
`image_rank_scope.json` give this exact scope. No output keys, attack,
ciphertexts or release implementation were instantiated in this tranche.

## Source computation and cost

[EXECUTED] The new SmolLM3 pass performs 32 batch forwards covering 256
axis examples from 128 new texts. It processes 45,312 real input tokens
and 46,304 padded tokens, with no generated tokens. Process wall time is
61.428 seconds; forward intervals total 48.854 seconds; CPU model loading
takes 1.331 seconds and transfer to MPS 2.407 seconds. Float32 CPU likelihood
and transfer bookkeeping takes 0.487 seconds. The forward time is about
0.3817 seconds per two-axis text at the measured batch throughput, excluding
startup/bookkeeping; it is not measured singleton latency.

[EXECUTED] Model size is 3,075,098,624 parameters, sourced from 6,150,235,008
bytes of cached BF16 shards and executed as float16 on MPS. Peak process RSS
is 10,272,817,152 bytes. Final MPS current/driver counters are
6,150,197,504 / 7,586,217,984 bytes. Unified-memory counters are not additive.
No teacher model forward is repeated in this successor.

[EXECUTED] The original baseline executes 128 new texts in eight CPU
float32 batches: 4,376 real tokens, 4,704 padded tokens, 1.316 seconds of
forward intervals and 4.138 seconds process wall. Its loaded model has
134,515,008 parameters and peak RSS 1,153,826,816 bytes. These are different
models, input formats, batch sizes and backends; the observed comparison
does not isolate which architectural change caused the gain. Public task
instructions and one-hot semantic structure add supervision and constraints.

[EXECUTED] Converting the reused/new inferred bits and gold diagnostic
bits to features takes 0.000294 seconds; original hidden-feature calibration
takes 0.012965 seconds. The full three-method utility evaluation takes
0.266455 seconds, and the independent audit 1.530501 seconds. Source model
execution dominates these measured intervals. Full CPU timings, file sizes,
memory counters and overlap caveats are retained in `costs.csv` and the raw
extraction/score reports. Four trainable or effective coordinates would be
an invalid proxy for the plaintext source computation's cost.

[DERIVED] The trusted issuer sees text, tokens, all model activations/logits,
inferred bits and category labels before a learner contribution exists.
Query text/features and routes are public in this fixture. This task does
not perform those source forwards on encrypted data. The unchanged numerical
format is compatible with integer add/expire arithmetic, but no cryptographic
integration or security promotion follows from these utility numbers.

## Reproduction and provenance

[SOURCE] SmolLM3 revision:
`a07cc9a04f16550a088caea529712d1d335b0ac1`; original SmolLM2 revision:
`93efa2f097d58c2a74874c7e644dbc9b0cee75a2`. Python 3.14.7,
torch 2.10.0, transformers 4.57.3, NumPy 2.4.2, macOS 26.6.1 arm64.
Both snapshots and source programs are pinned; no downloads, package
installation, weight training, private user logs or metered search occurred.
`SOURCES.md` records the exact official/installed source scope.

[EXECUTED] Pre-test freeze:
`c9c74521b14dd9cb60743ccbf34a91c5e300fa33f03e187aba4117915cda31da`.
Actual frozen teacher prediction fixture:
`01e9581a03776d3fa4746f5d73b82800f557b83baf77d3cb0ffde5cae2abf165`.
Results:
`322b58077896ad2afb874481bb613069f45c7ca647b776064c438c8328e65746`.
Every stage's full command, return code, stdout and stderr is retained:

```text
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/launch.py prepare
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/launch.py score
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/launch.py extract_smol
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/launch.py evaluate
python3 -B research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/launch.py audit
```

[DERIVED: wording qualification] Source verification hashes oracle/record
file bytes. Oracle values are not parsed by the scorer or provided to its
model, but the file is technically opened for hashing. This corrects the
older teacher report's literal “first opened” wording without changing any
frozen score or source bytes; see `SOURCES.md`.

[OPEN] This one fresh synthetic surface set supports the restricted source
abstraction, with the named soil failure. A next evaluation would need new
linguistic inputs, preregistered ambiguity/missing-fact handling, and a query/
release target whose effective image matches its privacy claim. This tranche
does not tune those choices or run another model experiment.
