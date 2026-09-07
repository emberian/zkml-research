# Bounded public quadratic-feature successor — before selection and final outcomes

[DERIVED protocol, 2026-09-06] Root authorized a separate≤60minute utility study.
The original E2E fixture, scores, model and representation study stay unchanged.
This experiment uses the existing frozen mean10 cache; no model execution,
backbone update, training download or new text extraction is authorized here.

[DERIVED data] Fit transforms only on unlabelled teacher texts. Reuse the original
16 selection histories62000…62015 with selection texts. Independently generate
and freeze64 final history seeds64000…64063, using the unchanged history generator.
Final queries use the existing held-out test texts. These text surfaces were seen
in earlier studies: histories are new, text surfaces are reused. This is a
follow-on study of that synthetic corpus, not a fresh text-domain generalization claim.

[DERIVED fixed feature family] Compute one teacher-centered PCA per public route
on the576-coordinate mean10 features. Use topk∈{8,16,32} components only. Divide
component scores by their teacher population standard deviation (floor1e-8).
For eachk compare (a) linear coordinates and (b) the same linear coordinates plus
all unique products z_i*z_j for i≤j. Center every nonbias transformed coordinate
on teacher text only, append bias1, and divide by the maximum teacher vector norm.
Clip nearest-even-rounded127 times the normalized features to[-127,127]. Pad
with zeros to577. Quadratic dimensions are45/153/561 including bias; linear
comparators are9/17/33. Per-route PCA/normalization uses no labels, history rules
or selection/test-domain moments. SVD sign choices are pinned in saved arrays.

[DERIVED learner] Every method uses the unchanged routed sliding contribution
window of32 items per skill. Issuer contribution is observed label times the
signed-int8 feature. Learn adds the new vector and subtracts the exact retained
old vector when the queue exceeds32. Infer is sign of the exact integer dot,
with zero→+1. No hyperparameter other than the three prespecifiedk values is
selected. Baselines: original full577 mean10 window with its exact original
quantization, and privileged true-attribute one-hot8 window. The latter is an
engineered positive control, not language understanding.

[DERIVED selection] For quadratic and linear PCA families separately, choosek
by mean final two-skill accuracy over all16 selection histories and all128
selection texts. Break ties toward smallerk. Persist selection settings and a
source hash before any final test evaluation. The original577 baseline is fixed.
No test-derived orientation flips, clipping changes, reselection or extra kernels.

[DERIVED acceptance] A useful successor must meet all these final conditions:
selected quadratic final mean≥60%; paired gain over original577 baseline≥5
percentage points; descriptive normal95% interval for that paired history-level
gain has lower bound>0; and aggregate final XOR/XNOR skill-instance accuracy
improves by≥10points over baseline. These are prespecified descriptive decision
rules, not a calibrated confirmatory hypothesis test. Report every condition,
including failure. Selected linear PCA is a further attribution control.

[DERIVED reporting] Keep all64 histories and all128 final text queries per history.
Report initial plant learning, plant retention after letters, letter learning,
changed plant rule and retained letters after reversal. Give four joint strata
(plant linear/nonlinear × letter linear/nonlinear), with actual history counts,
phase/skill results and paired gains; do not omit poorly performing strata.
Report reset50%, exact route-isolation state equality, and uncertainty at history
level. Use independent Python integers to check checkpoint sums and every final
selected-quadratic score. Retain all source/cached-feature/setting hashes.

[DERIVED cost] Record wall/CPU time and process high-water RSS for transform fit,
encoding and full control evaluation, separately from the cached backbone cost.
Count issuer/public-query PCA products, degree2 products, normalization and stored
calibration coefficients. These public fixed transforms add no resident private
multiplications beyond the unchanged add/expire/dot core; source token visibility,
feature provenance/range assertions and the full-key-reader limitation remain.
No actual BFV successor run or E2E substitution follows from utility alone.
