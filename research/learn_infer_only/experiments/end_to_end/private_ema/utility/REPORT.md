# Fixed private-address EMA retains utility on the reused semantic corpus

[EXECUTED] The unchanged selected-bin EMA scores **7,486/8,192 final labels
correct (91.3818%)**, compared with the saved semantic W32 learner's
7,462/8,192 (91.0889%). The saved original mean10 feature baseline remains
4,178/8,192 (51.0010%), and its privileged gold-attribute window diagnostic
remains 8,192/8,192. `results.json`, `query_scores.json` and retained
`evaluate.stdout` provide every denominator and integer score.

[DERIVED scope] This is a **reused-data exploratory comparison**, not a new
held-out utility estimate. The same saved 128 teacher texts, 128 query texts,
inferred semantic features and 64 histories were used. No encoder forward,
new text, hyperparameter change or test selection occurred. This comparison
supports trying the fixed nonlinear encrypted update on the useful fixture;
it does not establish that EMA improves on W32.

[EXECUTED] The history-paired EMA-minus-W32 difference is +0.29297 percentage
points, with a descriptive 1.96*SE half-width of 0.42527 points (interval
-0.13230 to +0.71824). Individual history changes range from -6.25 to +6.25
points. Final labels change in 120/8,192 cases: 72 improve and 48 regress;
216/24,576 labels differ across all checkpoints. The same 128 linguistic
queries recur across histories, so that interval describes history variation
and is not language-population uncertainty.

## Behavior and retained weaknesses

[EXECUTED] Two separate public routes each have four integer registers,
initially zero. A saved inferred address selects the sole updated register;
the true history label sets `u=±120`. Learn is
`s := floor((7*s+u)/8)`. Other registers do not decay. Infer's utility score
is the selected register, with zero predicting positive. The original TFHE
probe computes this update and returns its encrypted negative bit. Window
scores have different units; the reported gains compare correct labels.

| Measurement | EMA correct/total | Semantic W32 correct/total |
|---|---:|---:|
| Plant after initial learning | 3,382/4,096 | 3,398/4,096 |
| Plant retained while letters learn | 3,382/4,096 | 3,398/4,096 |
| Letter after learning | 4,096/4,096 | 4,096/4,096 |
| Plant after reversal | 3,390/4,096 | 3,366/4,096 |
| Letter retained after plant reversal | 4,096/4,096 | 4,096/4,096 |
| Final total | 7,486/8,192 | 7,462/8,192 |

[EXECUTED] The table is computed over all 64 fixed histories and all 128
queries at every original checkpoint. Initial unlearned letter queries are
2,048/4,096 for both learners. Exact retention checks cover 128 route-state
equalities and 8,192 corresponding query score/sign equalities. This retention
is provided by routed state, not by training the source model's weights.

| Final stratum | EMA correct/total | Semantic W32 correct/total |
|---|---:|---:|
| Simple rules | 5,181/5,504 | 5,165/5,504 |
| XOR/XNOR rules | 2,305/2,688 | 2,297/2,688 |
| Plant simple / letter simple | 3,223/3,456 | 3,207/3,456 |
| Plant simple / letter XOR-XNOR | 1,446/1,536 | 1,446/1,536 |
| Plant XOR-XNOR / letter simple | 2,252/2,560 | 2,252/2,560 |
| Both XOR/XNOR | 565/640 | 557/640 |
| Plant flexible/wet | 702/1,024 | 702/1,024 |
| Plant flexible/dry | 1,024/1,024 | 1,024/1,024 |
| Plant hard/wet | 672/1,024 | 696/1,024 |
| Plant hard/dry | 992/1,024 | 944/1,024 |
| Each letter attribute pair | 1,024/1,024 | 1,024/1,024 |

[EXECUTED] The hard/wet stratum regresses from 67.9688% to **65.6250%**,
while hard/dry improves from 92.1875% to 96.8750%. The aggregate result must
be read with that regression. No gates or parameter choices were introduced
after seeing these outcomes.

[SOURCE saved study] `../../utility/semantic_axis_successor/REPORT.md`,
“Factual errors and frozen gates,” and its saved `results.json` report
15 factual bit errors, all wet soil classified as dry, among the same 128
query texts. Their extracted features are reused exactly here. The scorer is
a frozen forced-choice 3B semantic issuer, and its four-bin abstraction plus
task instructions is substantive supervision. EMA adds no new language
understanding result and does not repair the saved source errors.

## Complete arithmetic and fixture checks

[EXECUTED] `evaluate.py` retains all 12,288 transitions, all 192 two-route
checkpoint states and all 24,576 EMA scores, with targets and all three saved
window comparators. It reconstructs every semantic W32 score directly from
the last 32 routed observations and verifies all 256 consumed feature rows
against the saved inferred bits and one-hot coordinates. Observed register
range is [-118,111], within the specified [-120,120].

[EXECUTED] The separate `audit.py` does not import the evaluator. It refolds
each bin's own label subsequence from zero using
`s + floor((u-s)/8)`, verifies all 12,288 transition states, 1,536 checkpoint
registers, 24,576 EMA scores and 73,728 saved comparator score records. It also
checks all 482 state/label range cases and the `0→15→-2` witness. Truncation
toward zero instead gives -1 in the second step, so it is explicitly rejected
as a different learner. This is an independently written implementation by
the same author, not independent reviewer approval.

[EXECUTED] `materialized_fixture.json` translates the unchanged first two
history IDs 67000/67001 and the previously selected 16 query IDs. It preserves
all 480 event IDs/orderings: **384 Learn, 96 Infer, zero expiry operations**.
EMA needs no W32 expiry queue. Every request and answer agrees with its full
survey entry. The same final 32 selected labels are 28/32 for both EMA and
W32; this is an integration subset, not another accuracy estimate. Clear
addresses, labels and oracle states in this file are PUBLIC synthetic data.

## Provenance, cost and next experiment

[EXECUTED] The contract and all programs were frozen before scoring. Freeze
SHA-256 is `63b798b519cbc5e7a8218a0e7811274f397cfb015e5c8f1f8c6364df8bf1e369`.
The 96-file pin set includes all 53 prior semantic manifest entries and all
30 prior materialized manifest entries. Before/after checks pass. The first
evaluation and first audit both exited zero, with all stdout/stderr retained:

```
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/private_ema/utility/launch.py freeze
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/private_ema/utility/launch.py evaluate
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/private_ema/utility/launch.py audit
```

[EXECUTED] Evaluation's measured interval is 0.531566 seconds and the separate
audit's is 1.421750 seconds. Launcher wall costs are retained separately in
the `.command.json` records. Results SHA-256 is
`d250ac49d115eb88127ace99042be09ba38a05b94989e322ca2e1332fef1c765`.
This utility tranche performed zero model, cryptographic, web or Scry calls.

[DERIVED proposal] A later distinct encrypted successor can reuse the pinned
TFHE binaries for all 384 Learn/96 Infer events, keeping separate four-register
ciphertexts for the two public routes. Replay every host operation in another
process from the same serialized inputs, hash those inputs immediately before
and after both invocations, and finish all public work before a private
correctness drain. Prior per-operation costs put this around two hours with
all replays; `costs.csv` records the exact projection inputs separately from
new measurements. Root coordinates launch to avoid CPU contention.

[DERIVED boundary] That proposed run would retain a full TFHE client key and
use public synthetic data on one operating-system account. It would test
encrypted continuation, signs and byte replay under a pinned backend. It
would not establish no-master-read, selected-output-only credentials,
post-quantum security, a journal/refinement theorem or physical isolation.
