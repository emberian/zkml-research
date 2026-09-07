# Public quadratic features did not improve this frozen adaptation task

[EXECUTED] The preregistered successor fails all four utility conditions. On64
new history seeds64000…64063, the selected quadratic map obtains **56.99%**
final accuracy versus **59.90%** for the unchanged577-coordinate baseline.
The paired difference is−2.91±2.28 percentage points (descriptive normal95%
history-level interval). The E2E fixture remains unchanged; this candidate is
not promoted to a new encrypted demonstration.

[EXECUTED] Root approved one≤60minute experiment after the original E2E mapping
finished. `PREREGISTRATION.md` fixed three PCA ranks, feature construction,
selection metric, success thresholds, seed range and joint-stratum reporting
before selection/test execution. `histories.json` freezes all new histories;
`selection.json` was written and hashed before `results.json`. No model was
executed, trained or downloaded. The original held-out text surfaces are reused:
only the history seeds are new. This is not a fresh-domain result.

## What changed and how it was selected

[DERIVED specification; EXECUTED] Per public skill, PCA fits only unlabelled
teacher embeddings. Component scores are divided by their teacher standard
deviation. The quadratic map contains linear terms, all unique products and
bias; nonbias terms are teacher-centered and the full vector is teacher-scaled.
Ranks8/16/32 give45/153/561 coordinates, then zero-padding to577. All outputs
use the original signed-int8 nearest-even rounding/clipping contract. The
routed window remains32 contributions per skill; no resident update changes.

[EXECUTED] Existing selection histories62000…62015 and selection text choose
quadratic rank8 at54.05% and linear rank16 at56.10%; the unchanged original
baseline gets58.98%. Every candidate remains in `selection.json`. We carry
the selected quadratic through final evaluation despite its selection deficit.
No test orientation flip, extra rank, capacity change or feature reselection occurs.

| Final method | Final two-skill accuracy | Changed plants | Retained letters | XOR/XNOR skill accuracy |
|---|---:|---:|---:|---:|
| Original577 window | 59.90%±2.68 | 55.93% | 63.87% | 50.51% |
| Selected linear PCA16 | 53.71%±2.01 | 52.76% | 54.66% | 49.63% |
| Selected quadratic PCA8 | 56.99%±2.12 | 57.81% | 56.18% | 54.18% |
| Privileged true-attribute8 | 100% | 100% | 100% | 100% |

[EXECUTED] The nonlinear column contains all55 XOR/XNOR skill instances among
128 final history/skill instances; it is not an independent-history confidence
interval. The ± quantities in the final-mean column use64 histories as units.
The true-attribute control reads generator metadata and is explicitly privileged.
Reset is50% because the query labels are balanced.

[EXECUTED] Quadratic plant accuracy is56.23% after initial training and remains
56.23% after letter training; changed plants reach57.81%. Letters reach56.18%
and retain that exact accuracy after plant reversal. All four methods have
exact state equality on the untouched route (512 retained equalities overall).
This is architectural route separation, not a learned interference solution.

## All joint rule strata

[EXECUTED] Rows list plant rule type / letter rule type. Every new history appears.

| Joint stratum | Histories | Original final | Quadratic final | Paired difference |
|---|---:|---:|---:|---:|
| Linear / linear | 22 | 68.22% | 59.30% | −8.91 points |
| Linear / XOR-XNOR | 14 | 53.68% | 55.97% | +2.29 points |
| XOR-XNOR / linear | 15 | 60.47% | 55.78% | −4.69 points |
| XOR-XNOR / XOR-XNOR | 13 | 51.86% | 55.59% | +3.73 points |

[EXECUTED] The registered success conditions all fail: final mean≥60% (actual
56.99%); paired gain≥5points (actual−2.91); positive paired descriptive interval
lower bound (actual−5.19); and XOR/XNOR gain≥10points (actual+3.66). Full
phase/skill metrics, strata and every prediction/score/target remain in
`results.json`. A small nonlinear-stratum gain does not outweigh the lost
linear-rule utility or meet the stated decision rule.

## Exactness and cost

[EXECUTED] Independent Python integers verify8192 final selected-quadratic
scores and384 checkpoint vectors. `audit.py` independently checks98,304
saved prediction/label pairs and recomputes256 history/method metric rows,
selection choices, disjoint seeds, source hashes and the decision rule.
The original encrypted fixture hash remains41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0.
No clipping occurs for the selected quadratic map on teacher, selection or test
records. These are plaintext numerical checks, not a cryptographic experiment.

[EXECUTED] PCA fitting (two route SVDs) takes0.0230s wall /0.00985s CPU, with
55,361,536B process high-water RSS. Encoding all384 cached vectors through the
selected quadratic map takes0.000766s wall /0.000767s CPU, with55,754,752B
high-water RSS. Full preparation peaks at66,830,336B. Final evaluation including
independent integer checks takes5.441s wall /1.691s CPU, with47,366,144B
high-water RSS. These are one local run's measurements; RSS includes Python,
NumPy and caches, is not an incremental allocation, and is not resident memory.
No per-observation latency is extrapolated from this tiny batched measurement.

[DERIVED] For rank8, an already-entitled issuer or public-query processor adds
4608 PCA coefficient products,4600 reduction additions,8 component scalings,
36 feature products,44 transformed-center subtractions,45 final scalings and45
round/clips after obtaining the backbone vector; there are also576 embedding
center subtractions. The selected two-route calibration needs10,474 float64
coefficients (83,792 payload bytes), excluding formats/metadata. The stored sweep
arrays include other candidates; this count is for the selected policy alone.
Exact counts and measured process costs are in `costs.csv`.

[DERIVED scope] The nonlinear products happen at the issuer or public-query
processor. If the feature input had to remain hidden from that processor, those
36 products would be private-by-private operations in addition to protected
backbone work. They do not occur inside this resident window. Padding preserves
the577-dimensional ciphertext arithmetic target and signed score bound297,805,856;
no BFV successor is executed here. Issuer feature provenance/range assertions,
source-token visibility, continuity and the explicit full-key reader remain
separate obligations. This failure concerns the fixed PCA/product family and
synthetic corpus, not nonlinear features, language models or HE in general.

## Reproduction

[EXECUTED] From repository root, using the existing utility environment:

```sh
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/nonlinear_successor/run.py prepare
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/nonlinear_successor/run.py select
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python -B research/learn_infer_only/experiments/end_to_end/utility/nonlinear_successor/run.py evaluate
python3 -B research/learn_infer_only/experiments/end_to_end/utility/nonlinear_successor/audit.py
```

[EXECUTED] Each command exits0; matching logs are retained. `features.npz` and
`parameters.npz` are ignored regeneratable arrays with hashes in preparation.
Model runs0; training0; downloads0; metered searches0. No original fixture,
shared ledger, companion tree or previous tranche artifact is edited.
