# Added attribute supervision did not repair transfer to new text surfaces

[EXECUTED] The preregistered primary, soft attribute conjunctions, reached
**4,468/8,192 final predictions correct (54.5410%)**, below the unchanged mean10
baseline's **4,820/8,192 (58.8379%)**. It failed every utility acceptance condition;
exact retention of an untouched route passed. This preserves the negative
result. No setting was changed after selection or after test evaluation.

## What changed, and what stayed fixed

[EXECUTED] The source encoder received **256 explicit teacher attribute-label
bits** on 128 existing prompts and another **256 selection bits** on 128 existing
prompts. Each prompt supplies two binary attributes. Four ridge heads were fit
from frozen SmolLM2 mean10 representations; a five-value regularization grid
selected one global lambda, **0.01**, using attribute accuracy and then clipped
probability MSE. History-dependent category labels and rules did not enter this
fit. These 512 bits are a supervision count, not an independent-sample count:
the teacher pool has only eight distinct attribute cue phrases, repeated across
names, combinations and two templates. Selection has eight different phrases.

[DERIVED] The primary clips the two predicted attributes to [0,1], computes
their four soft conjunctions, and places them in the public route's four slots
of an eight-coordinate representation. It pads to 577 and quantizes by nearest
even rounding at scale127. The fixed secondary diagnostic thresholds attributes
before computing conjunctions. Public test feature generation accepts hidden
vectors and routes only; test gold attributes appear only in the privileged
control and scoring oracle. `audit.py` rebuilds all four model-derived feature
arrays through that interface.

[EXECUTED] The test has 128 genuinely new complete texts: 16 new entity names,
four new full templates and 16 new full cue phrases. `data.py` checks them
against both earlier synthetic generators and excludes the live-text name
Marigold. Ordinary words overlap, and all four logical attribute combinations
were taught. Thus this is transfer across fixed new linguistic surfaces, not
across previously unseen logical combinations or a broad language benchmark.

[EXECUTED] The 64 new histories, seeds65000–65063, each teach skill0 for64 steps,
skill1 for64, then reverse skill0's rule for64. Separate queues retain32 signed
int8 contribution vectors per public route. Query scores use exact integer dot
products and sign(score)>=0 predicts+1. The old mean10 normalization and the
previous selected quadratic8 PCA, scales and offsets were reused byte-for-byte;
295,424 teacher/selection coordinates matched their previous cached results.
No backbone was trained and no cryptographic or journal core changed.

## Complete paired results

[EXECUTED] Each method is evaluated on the same 128 query IDs after each of
three phases in every history: **24,576 predictions per method**, 122,880 total.
There are8,192 final predictions per method. All scores, labels, predictions
and per-history metrics are in `results.json`; all 64 histories and text
metadata are retained. The same128 test texts recur across histories.

| Fixed method | Final correct /8,192 | Final accuracy | Simple correct /5,760 | XOR/XNOR correct /2,432 |
|---|---:|---:|---:|---:|
| Original mean10,577 |4,820|58.8379%|3,616|1,204|
| Previous frozen quadratic8 |4,319|52.7222%|3,093|1,226|
| **Primary supervised soft conjunctions** |**4,468**|**54.5410%**|**3,231**|**1,237**|
| Fixed supervised hard diagnostic |4,288|52.3438%|3,168|1,120|
| Privileged true-attribute8 |8,192|100.0000%|5,760|2,432|
| No memory / reset, computed from balanced labels |4,096|50.0000%|2,880|1,216|

[EXECUTED] Primary minus original is **−352 correct predictions**, or
**−4.296875 percentage points**, with a descriptive history-paired1.96*SE
half-width of1.880036 points. Primary minus the prior negative quadratic is
+149 correct, or+1.818848 points (half-width1.677350). These intervals describe
variation across the64 generated histories with fixed texts; they do not
support population claims about novel language. The hard diagnostic loses532
predictions versus original and31 versus quadratic. It does not replace the
preregistered primary.

[EXECUTED] There are90 simple-rule skill instances and38 XOR/XNOR instances.
Primary simple accuracy is56.09375% versus62.77778% original (−6.68403 points);
nonlinear accuracy is50.86349% versus49.50658% (+1.35691 points).

| Joint rule strata (skill0/skill1) | Histories | Final queries/method | Original | Quadratic8 | Primary soft | Fixed hard | True attrs |
|---|---:|---:|---:|---:|---:|---:|---:|
| simple/simple |31|3,968|62.3488%|53.6038%|55.5444%|54.7379%|100%|
| simple/nonlinear |11|1,408|50.0710%|50.3551%|50.2841%|45.3125%|100%|
| nonlinear/simple |17|2,176|61.3511%|53.1250%|56.3419%|54.5956%|100%|
| nonlinear/nonlinear |5|640|47.8125%|51.0938%|51.5625%|45.3125%|100%|

## Learning, reversal and independent-skill retention

[EXECUTED] Every percentage below has4,096 queries per method/checkpoint/skill.

| Method | Skill0 after teaching | Skill0 after unrelated skill1 | Skill0 after reversal | Skill1 after teaching | Skill1 after unrelated reversal |
|---|---:|---:|---:|---:|---:|
| Original |51.0254%|51.0254%|50.4639%|67.2119%|67.2119%|
| Quadratic8 |51.2207%|51.2207%|51.2207%|54.2236%|54.2236%|
| Primary soft |49.6826%|49.6826%|49.9512%|59.1309%|59.1309%|
| Fixed hard |50.0000%|50.0000%|50.0000%|54.6875%|54.6875%|
| True attributes |100%|100%|100%|100%|100%|

[EXECUTED] All640 untouched-route state/output checks pass. This retention is
provided by explicitly routed independent queues. It is not evidence that a
shared neural parameter set learned to avoid interference. The true-attribute
control shows that these chosen histories and the W32 update can learn and
reverse the Boolean rules when the source features identify the attributes.
The model-derived primary does not establish useful rule reversal on new text.

## Where calibration failed

[EXECUTED] At selected lambda, teacher attribute accuracy was256/256 (100%);
selection was152/256 (59.375%), with both attributes correct45/128 times.
Test attribute accuracy fell to138/256 (53.90625%); both were correct34/128
times (26.5625%). The four test head accuracies are32/64,32/64,34/64,40/64.
All route/template cells are reported in `audit.json`; no example was selected
to illustrate a success.

[INFERRED] Perfect fitting of repeatedly phrased teacher attributes does not
establish semantic attribute extraction across new phrasing. In this bounded
experiment, supervision of those cached features left most attribute heads
near chance on selection and test. The conjunction layer cannot repair that
upstream identification error. This is a failure of this small supervised
readout, data regime and fixed representation; it says nothing general about
language models, encrypted learning, or a better trained source encoder.

## Executed model and costs

[EXECUTED] `extract.py` loaded the cached HuggingFaceTB/SmolLM2-135M revision
`93efa2f097d58c2a74874c7e644dbc9b0cee75a2`, checking all eight local asset hashes.
It used Python3.14.7, torch2.10.0, transformers4.57.3 and numpy2.4.2. CPU float32,
eager attention, two intra-op threads/one inter-op, seed7901, eval/inference
mode, batch16, right padding excluded in mean pooling, no gradients or KV
cache. The representation is direct decoder block9 output; the actual source
executes all30 blocks. The model has134,515,008 parameters; none were updated.

[EXECUTED] The one new128-text extraction processed4,280 real tokens,4,640
including padding. Forward work took2.352988s wall/2.813312s CPU; model loading
took0.403812s wall/0.341685s CPU. Total process time measured by the launcher
was7.029319s; interpreter-internal wall time including imports was6.480596s.
Peak process RSS was1,421,328,384B. Batched time per text is not single-request
latency. No downloads or new dependencies were needed.

[EXECUTED] Five-lambda fitting/selection including cache and hash checks took
0.073917s wall/0.019854s CPU, peak46,972,928B RSS. Encoding384 already extracted
vectors into BOTH calibrated methods took0.001310s wall/0.001251s CPU, excluding
the shared normalization timed with original encoding (0.002713s wall).
These small timings include file/array overhead and are not latency claims.
The complete five-method utility evaluation took2.692846s wall/1.501850s CPU;
independent auditing took0.164637s wall. `costs.json` records exact source fields.

[DERIVED] The added fitted public policy has2,308 float64 values (18,464 raw
bytes):2,304 coefficients and4 intercepts, in addition to the existing public
teacher normalization. Its JSON is87,500B. Per text after the backbone and
normalization, two affine heads require1,152 public scalar products and1,150
reduction adds plus2 intercept adds, then2 clips,4 conjunction products and
four active-coordinate quantizations. The declared representation remains577
signed bytes. These are plaintext issuer/query computations, not HE costs.

[DERIVED] In the resident, Learn remains one signed contribution addition and
one expired contribution subtraction per full-window update, per public route;
Infer remains a public-vector dot product. The contract's generic577-coordinate
score bound is297,805,856. The primary's observed maximum absolute score across
all checkpoints was185,931. The primary occupies only four active slots per
route; this experiment does not claim a measured ciphertext cost reduction.

## Role visibility and verification boundary

[DERIVED] The entitled source issuer sees source text, labels, tokens, all
model activations and predicted attributes, then would encrypt the contribution.
The public query encoder sees query text and its predicted attributes. The
fitted policy is public. An encrypted deployment still needs to account for
visible route, timing, queue occupancy, ingress/query shape and repeated query
outputs. The new policy's512 supervision bits are neither private history
state nor an absence-of-master-read guarantee. Plaintext feature extraction is
not operator-private computation. This study neither changes nor re-executes
the separate E2E system's trusted authority and full-key reader assumptions.

[EXECUTED] The independent audit replays every primary checkpoint with Python
integer lists and direct32-entry queue sums:384 state vectors and24,576 exact
scores match. It checks all122,880 recorded predictions and their independently
derived category targets, all paired denominators, int8 bounds and zero padding.
There are no model reruns in the audit. `freeze.json`, `selection.json` and
`extraction.json` link the source, pre-test selection and actual model outputs
by hash; `manifest.json` records the final artifact census.

[EXECUTED] Commands ran from the repository root, using the existing model venv
through `launch.py`; per-stage command, stdout, stderr and return code are kept:

```text
research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python research/learn_infer_only/experiments/end_to_end/utility/attribute_calibration/run.py prepare
python3 research/learn_infer_only/experiments/end_to_end/utility/attribute_calibration/launch.py select
python3 research/learn_infer_only/experiments/end_to_end/utility/attribute_calibration/launch.py extract
python3 research/learn_infer_only/experiments/end_to_end/utility/attribute_calibration/launch.py evaluate
python3 research/learn_infer_only/experiments/end_to_end/utility/attribute_calibration/launch.py audit
```

[OPEN] A later experiment would need a preregistered source encoder that
demonstrably transfers attributes across a richer training vocabulary before
testing resident utility. This run supplies neither that encoder nor permission
to relabel its negative outcome as success. No further tuning or model run was
performed here.
