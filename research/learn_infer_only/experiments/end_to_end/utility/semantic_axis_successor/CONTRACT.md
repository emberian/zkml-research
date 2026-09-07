# Fresh semantic-issuer utility test: frozen A, no further selection

[HYPOTHESIS] The selected teacher-only factual scorer may convert new text
into useful attributes for a small history-dependent learner. This tranche
tests one already selected prompt and one already existing feature map. It
does not change model weights, prompt wording, numerical scoring, decoder,
teacher predictions or feature choices after seeing a new test score.
Budget at most two hours; cached local models, no downloads or new dependencies.

## Frozen semantic and feature interface

[DERIVED: protocol] Reuse framing A from `../semantic_axis_selection/prompts.json`
byte for byte, with SmolLM3-3B revision
`a07cc9a04f16550a088caea529712d1d335b0ac1`, MPS float16/eager, batch 8,
explicit left-padded cumulative positions, no cache, final-position logits,
float32 CPU likelihood calculation, alternatives token IDs 15/16 and tie to 0.
Use the same public axis definitions and cached no-thinking chat template.
Freeze rendered new prompts/token IDs before the first new forward. Compare
the exact one-token alternative likelihoods; no generation or parser repair.

[DERIVED] Reuse actual A predictions for all 128 original teacher texts from
the frozen selection run; no teacher model re-encoding. For each public route
s and inferred pair (a,b), feature Q has value 127 only at coordinate
4*s+2*a+b and zero elsewhere, padded to dimension 577. This is exactly the
existing true-attribute feature map with inferred bits substituted for gold
bits. No confidence weighting, products, learned calibration or fallback
is selected. Original selection rows 128..255 are unused in this tranche.
Teacher category labels remain the history's labels of the actual observed
attribute combination; they are never supplied to the source model.

## Fresh data and paired utility

[DERIVED] Retain the original teachers and create 128 new test texts: two
public tasks, four balanced attribute pairs, eight new names per task and
two new complete templates with new full cue phrases. Check exact names,
templates, cue phrases and full text against the original two generators,
attribute-calibration test and E5 test. Meanings and ordinary words overlap;
this is fresh surface transfer within the same defined task, not open-domain
generalization. Freeze every new text before scoring. Report every factual
error, axis and joint attribute stratum, including the known hard-leaf/wet-soil
teacher weakness. Gold bits live in the evaluation oracle, never model input.

[EXECUTED: seed-availability precheck] Before this contract, ripgrep searched
all JSON files under `research/learn_infer_only` for a numeric `seed` field
in 67000..67063 and returned no matches (exit 1). Save the exact instrument
and scope in the new freeze. This is not an absence claim outside that corpus.
Use precisely these 64 seeds; do not resample rules or histories for balance
after seeing outcomes. Histories use the original generator: 64 plant updates,
64 letter updates, then 64 plant updates with that plant rule reversed. Both
rules are independently sampled balanced Boolean functions. Test texts never
enter teaching histories or the model's working context with other examples.

[DERIVED] Compare exactly three methods on identical histories and query IDs:
semantic A one-hot577 primary, original frozen SmolLM2 mean10-577 baseline,
and privileged true-attribute one-hot577 diagnostic. The baseline reuses its
original cached teacher features/policy and executes only the 128 new test
texts through the pinned local SmolLM2 model, with the original CPU float32,
eager, batch16, right-padding, masked mean of direct block9 policy. Do not
recalibrate or tune it. No-memory/reset is the balanced 50% control.

[DERIVED] Keep the last W=32 contributions per public route. A contribution
is the signed integer category label times Q. Learn adds it and subtracts
the expired same contribution. Infer is the exact integer dot product with
the query Q, predicting +1 when score>=0. Report all 128 queries at all three
checkpoints for all 64 histories and all three methods: 73,728 scores,
24,576 per method, 8,192 final queries per method. Report initial learning,
plant retention while letters learn, plant reversal and letter retention.

## Acceptance before any new score

[DERIVED] Accept this as a useful restricted semantic-issuer successor only
if ALL gates pass: fresh factual bit accuracy >=90%, each task >=85%; primary
final utility >=75%; each task's final utility >=75%; paired gain over original
mean10 >=10 percentage points with a positive lower endpoint of its descriptive
history-paired 1.96*SE interval; nonlinear-rule-instance gain >=10 points;
simple-rule regression no worse than 5 points; exact untouched-route state and
output retention; final primary utility >=65% in every populated joint
simple/nonlinear history stratum AND every task/true-attribute-pair stratum.
All strata and paired denominators are reported even on failure. Repeated
histories are not independent new language samples, and this interval is not
a language-population significance claim. No gate is changed after results.

## Exact controls, costs and rank boundary

[DERIVED] Primary features are 0 or 127. Signed inputs stay in [-127,127],
state coordinates in [-4064,4064]. The primary absolute score bound is
32*127^2=516128 because each query selects one coordinate. The generic original
baseline bound is 577*32*127^2=297805856. Independently replay all primary
checkpoint scores with Python integers and direct retained-queue sums; verify
every update against a recomputed queue, all signs/targets/denominators, exact
retention, and baseline teacher-cache agreement. No extra model run is an audit.

[DERIVED: image/rank] Each route's possible feature image is four scaled unit
vectors inside the 577 coordinates. Its linear span has rank 4, and the two
routes together have rank 8. Compute the actual image census and exact rank
in the artifacts. The aggregate is C=127*z for four integer net label counts;
full-window reachable z has L1 norm <=32 and sum parity equal to 32. Four exact
score functionals on those basis queries reveal all four aggregate coordinates
via score/127, despite the ambient 577-dimensional padding. This does not
recover queue order, and sign-only answers do not by themselves give exact
magnitudes. This lane does not instantiate such functional keys or execute
a security attack. It records why utility here cannot be promoted to a
no-master-read or private-cognition result.

[DERIVED] The source issuer sees raw text, all tokens/activations/logits and
inferred features. Query text/features and route are public here; teacher
category labels are visible to the source issuer. Explicit public semantic
definitions and inherited model training are supervision. Count actual 3B
and 135M forwards, input/padding tokens, model/policy/feature bytes, wall/CPU/
MPS/RSS costs and the simple feature conversion. There is no private 3B
computation, cryptographic integration, reader/journal change, or new claim
about the designated 577D crypto lane.
