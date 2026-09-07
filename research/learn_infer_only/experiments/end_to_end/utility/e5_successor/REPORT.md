# E5 projected features: executable, but the utility gates failed

[EXECUTED] The fixed E5 projected577 primary achieved **4,430/8,192 final
queries (54.0771%)** on the new texts/histories. Raw E5 reached4,504/8,192
(54.9805%), and original SmolLM2 mean10 reached4,340/8,192 (52.9785%). The
primary's+1.0986 percentage-point paired gain over original had a descriptive
1.9717-point half-width; this does not pass the preregistered positive lower
endpoint or10-point-gain requirements. Overall and nonlinear utility gates
also failed. Retention, the simple-rule regression bound and the projection
loss bound passed. **This is not a useful-successor result.**

## Frozen change and provenance

[SOURCE] E5 is a sentence-embedding model. We followed its official feature
interface: every input receives `query: `, final hidden states are averaged
with padding masked out, then L2-normalized. [Official E5-base-v2 card](https://huggingface.co/intfloat/e5-base-v2).
The cache inventory/card/method review is in `../encoder_feasibility/`; the
model's inherited text-pair/supervised training is source pretraining, not
evidence that this task is unsupervised in every sense.

[EXECUTED] E5 snapshot`f52bf8ec8c7124536f0efb74aca902b2995e5bcd` was fully
file-hash checked and actually loaded locally. It has109,482,240 parameters.
The single projection was drawn before model execution using numpy2.4.2
Generator(PCG64(66901)):768×576 int8 Rademacher signs, converted to float64 and
divided by24. Its raw sign-array SHA is
`37c448cae88ab74aee3f5357f418ff51e51dcfdca87356f542641dc742cfc731`.
No alternative projection, layer or prefix was compared or selected.

[EXECUTED] Per route, only128 total public teacher embeddings fit the center
and RMS centered radius. Centered embeddings are divided by that radius, then
projected and given bias1. The raw offline control omits projection. Each
representation divides by its own maximum teacher-vector norm including bias,
then uses nearest-even round(127*x) clipped to[-127,127]. This scale-invariant
calibration is part of the new public source policy; it differs from the older
baseline's frozen calibration and is not claimed to isolate encoder objective
as the only causal change. The primary has **zero added attribute labels**.

[EXECUTED] The original mean10, prior quadratic8, and prior supervised soft8
comparisons retain their exact old policies. The soft8 comparison still carries
its256 teacher+256 selection attribute-label bits. The primary source function
accepts embeddings and public routes, not gold attributes, history rules or
resident state. Its query features never use a category label. The privileged
true-attribute control alone uses generator attributes directly.

## New data and full paired denominator

[EXECUTED] `surfaces.py` and `records.json` fix128 new complete test texts with
16 new names, four new full templates and16 new full cue phrases, checked
against both original generators and the previous attribute-calibration test.
Common words and the four taught logical combinations overlap. No teaching
history or working model context contains a test text.

[EXECUTED] Seeds66000–66063 fix64 histories, each with64 skill0 updates,
64 skill1 updates and64 reversed-rule skill0 updates. W32 queues are separate
by public route. Every method receives the same signed teaching labels, order,
queries, >=0 tie rule and expiration policy. All128 queries run after all three
phases for all six methods: **147,456 scores**,24,576 per method,8,192 final
queries per method. The new figures are not merged with earlier test counts.

| Method | Final correct /8,192 | Accuracy | Simple correct /4,992 | XOR/XNOR correct /3,200 |
|---|---:|---:|---:|---:|
| **E5 projected577 primary** |**4,430**|**54.0771%**|**2,827**|**1,603**|
| E5 raw769, offline only |4,504|54.9805%|2,903|1,601|
| Original mean10-577 |4,340|52.9785%|2,729|1,611|
| Prior frozen quadratic8 |4,173|50.9399%|2,580|1,593|
| Prior frozen supervised soft8 |4,185|51.0864%|2,545|1,640|
| Privileged true-attribute8 |8,192|100%|4,992|3,200|
| No memory/reset, balanced-label control |4,096|50%|2,496|1,600|

[EXECUTED] There are78 simple-rule skill instances and50 XOR/XNOR instances.
Primary simple accuracy is56.6306%, versus54.6675% original (+1.9631 points);
nonlinear accuracy is50.09375%, versus50.34375% original (−0.25 points).

| Joint rule stratum | Histories | Final queries/method | Primary | Raw769 | Original | Quadratic8 | Supervised soft8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| simple/simple |24|3,072|55.9570%|57.6497%|54.1016%|51.8555%|50.2604%|
| simple/nonlinear |12|1,536|50.5208%|50.2604%|56.1198%|51.0417%|53.2552%|
| nonlinear/simple |18|2,304|56.2066%|57.3351%|50.9115%|49.9566%|51.3889%|
| nonlinear/nonlinear |10|1,280|50.0000%|50.0000%|50.2344%|50.3906%|49.9219%|

[EXECUTED] The true-attribute control is100% in every stratum. Primary minus
quadratic is+257 correct (+3.1372 points, paired half-width1.4718); minus
supervised soft8 is+245 (+2.9907 points, half-width1.7954). These are improvements
over two already negative controls, not the required usefulness result.
All paired intervals describe the64 generated histories with the same128
texts; they are not confidence intervals for language-wide generalization.

## Projection loss, order change and retention

[EXECUTED] Projection loses74 final correct predictions relative to raw769:
−0.90332 points, with a paired descriptive half-width0.72201. This passes the
fixed2-point loss bound. Raw769 still achieves only54.9805%; its result cannot
be substituted for a577-coordinate encrypted-compatible success. This gap
measures the full projected/renormalized/quantized pipeline, not a pure
floating-point linear-algebra distortion statistic.

[EXECUTED] Each skill/checkpoint percentage below has4,096 query predictions.

| Method | Skill0 taught | Skill0 after unrelated learning | Skill0 reversed | Skill1 taught | Skill1 retained |
|---|---:|---:|---:|---:|---:|
| E5 projected |49.5605%|49.5605%|50.1709%|57.9834%|57.9834%|
| E5 raw |49.9756%|49.9756%|50.4150%|59.5459%|59.5459%|
| Original |53.0518%|53.0518%|55.0293%|50.9277%|50.9277%|
| Quadratic8 |51.7334%|51.7334%|51.8066%|50.0732%|50.0732%|
| Supervised soft8 |51.5869%|51.5869%|53.0273%|49.1455%|49.1455%|
| True attributes |100%|100%|100%|100%|100%|

[EXECUTED] All768 untouched-route state/output checks pass. This retention
comes from explicit independent queues; it is not learned interference
avoidance inside a shared neural parameter set. E5 supplies no evidence of
useful plant-rule reversal here. The true-attribute control confirms that the
chosen histories and W32 update can represent and reverse those rules when
the source facts are correctly exposed to the learner.

## Selection order and actual model work

[EXECUTED] The contract, sources, new text/history fixtures and projection were
hashed first. E5 then encoded only256 teacher/selection texts; the source policy
and selection report were frozen before either test extraction. Selection was
55.8594% projected,55.8105% raw,58.9844% original. Nothing was changed in response.
Only afterward were128 new texts encoded by E5 and, for the paired old-policy
controls, by the original pinned SmolLM2. No model download, backbone update,
new dependency or encryption run occurred.

[EXECUTED] All model processes used Python3.14.7, torch2.10.0,
transformers4.57.3, numpy2.4.2; CPU float32/eager attention, batch16, two
intra-op/one inter-op threads, seed7901, right padding, inference/eval mode
and no gradients/cache. E5 runs12 blocks; the original mean10 extraction
executes all30 SmolLM2 blocks while pooling direct block9 output. E5 inputs
were checked not to exceed512 tokens, with no silent truncation.

| Actual extraction | Texts | Real/padded tokens | Forward wall /CPU seconds | Full process wall | Peak RSS bytes |
|---|---:|---:|---:|---:|---:|
| E5 teacher+selection |256|6,024/6,592|6.4751/3.2129|16.4376s|734,658,560|
| E5 fresh test |128|4,408/4,720|3.0633/2.0453|15.0312s|769,622,016|
| SmolLM2 fresh test controls |128|3,928/4,144|8.2652/2.8728|24.2006s|1,152,991,232|

[EXECUTED] These are individual observed runs under shared-machine load, not
a controlled latency comparison. Full process wall includes imports, hashing,
loading and output; forward times are nested and must not be added to it.
Model loading wall times were0.5295s,0.3635s and1.1832s respectively. Batched
per-text averages are not single-query latency. Complete timings and model
file inventories are retained in each extraction/command record.

[EXECUTED] Teacher calibration plus both E5 representations for256 vectors
took0.010494s wall/0.006813s CPU. Encoding384 already-extracted E5 vectors into
both final representations took0.006497s wall/0.006488s CPU. The integer
six-method evaluation took1.110265s wall/0.941458s CPU; the independent audit
took1.783971s wall. These small costs include file and array overhead. They do
not price the public backbone as free.

[DERIVED] The768→576 matrix adds442,368 public scalar products and441,792
reduction adds per source/query text. Stored as float64 it is3,538,944B;
the frozen sign NPZ is442,632B and can regenerate it. Teacher source-policy
JSON is49,547B. All six feature arrays occupy1,404,692B as NPZ. The primary
still has577 signed-int8 coordinates and W32 per route; raw769 is explicitly
outside that encrypted interface. Its generic bound is396,902,432, versus
297,805,856 for577. Maximum primary observed absolute score was94,649.

## Boundaries and audit

[DERIVED] The entitled issuer sees raw source text, teaching category label,
token IDs, every source-model activation and the projected contribution before
any encryption. Query text/features are public here. Public policy includes
weights, prefix, pooling, center/radius/scales and projection. Resident state
does not enter source encoding; its hypothetical encrypted computation still
needs all existing credential, release and continuity assumptions. This study
does not produce operator-private source encoding, restricted decryption,
no-master-read authority or a new encrypted execution. It does not imply a
general limitation of E5, LMs or encrypted learning.

[EXECUTED] `audit.py` independently replays384 primary checkpoint vectors
and24,576 primary scores with Python-integer lists and direct retained32-entry
queue sums. It validates all147,456 target/sign records and paired denominators,
dimension/range bounds, the one projection and feature rebuild without label
arguments. E5 embedding norm error was at most1.873e−7. All seven logged
commands returned0; their exact arguments/stdout/stderr remain in this directory.
`results.json` retains all outcomes (~9.4MB), not selected examples. The final
manifest pins all artifacts and the original source/selection chain remains
unchanged.

```text
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py prepare
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py e5_train
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py fit_select
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py e5_test
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py smol_test
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py evaluate
python3 research/learn_infer_only/experiments/end_to_end/utility/e5_successor/launch.py audit
```
