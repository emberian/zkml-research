# E5 with one fixed public projection: contract before test

[HYPOTHESIS] A model trained to produce sentence embeddings may support new-text
rule transfer better than pooled tiny causal-LM activations. This experiment
uses the already cached E5-base-v2 and the SAME integer W32 update. It adds no
attribute-label supervision to its primary and changes no encryption/journal
core. The raw769-dimensional diagnostic is offline only. A failed projection
must not be replaced by a selected one or silently promoted to a wider
encrypted interface. Budget: at most two hours, no downloads/new dependencies.

## Frozen encoder and sole projection

[SOURCE: usage contract] Use intfloat/e5-base-v2 snapshot
`f52bf8ec8c7124536f0efb74aca902b2995e5bcd`, whose local files are hashed in
`../encoder_feasibility/candidates.json`. Follow the official card: prefix every
teacher, selection and test text with `query: `; masked mean of the final hidden
states excluding padding; L2-normalize each768-vector. CPU float32, eager
attention, eval/inference mode, no gradients/cache, batch16, right padding,
two intra-op threads/one inter-op, seed7901. Reject texts beyond512 tokens
instead of silently truncating. No prompt, pooling or layer search.

[DERIVED: fixed numerical policy] Draw exactly one768×576 Rademacher matrix
using numpy2.4.2 Generator(PCG64(66901)), int8 draws0/1, mapping to−1/+1, then
float64 division by sqrt(576)=24. Save/hash the matrix before model execution;
do not draw or compare alternatives. Per public route, fit only the public
teacher embedding mean and RMS centered radius rho. Divide centered vectors
by rho. The primary projects this normalized vector and appends bias1. The
raw diagnostic appends bias1 without projection. Each separately divides by
its maximum teacher-vector L2 norm including bias, then applies nearest-even
round(127*x), clipping to[-127,127]. This scale-invariant teacher calibration
avoids making the arbitrary embedding unit set the relative bias magnitude.
It differs from the older frozen baseline calibration and will be disclosed.
No attribute or category labels enter these fits. If rho is zero, record the
pipeline failure rather than select a replacement policy.

## Data freeze and sequencing

[DERIVED: protocol] Preserve the original128 teacher and128 selection texts;
create128 new complete test texts covering two skills, four attribute pairs,
eight new names per skill and two new full templates with new full cue phrases.
Check exact names/templates/phrases against both original generators and the
attribute-calibration test; exclude Marigold. Common words and meanings overlap;
all logical attribute combinations have teacher examples. Do not add lexical
rules or change the public ontology based on previous test outcomes.

Freeze new history seeds66000..66063, using the same192 updates:64 skill0,
64 skill1,64 skill0 with its balanced Boolean rule reversed. Each route's
balanced rule is sampled independently; phase order and all permutations are
fixed before features/outcomes. The test texts never enter teaching histories
or model working context. The same128 texts recur across64 histories.

Sequence: freeze contract/source/data/history/projection; extract only256 E5
teacher/selection texts; fit public teacher calibration; record selection on
the old16 histories62000..62015 with no setting changes; hash/freeze selection
and policy; only then extract/evaluate the new128 E5 test texts and128 SmolLM2
test texts for paired frozen-baseline comparisons. All old test surfaces and
results remain unchanged. Re-encoding SmolLM2 is solely for this authorized new
paired denominator; its representation or policy will not be tuned.

## Fixed methods and exact denominators

[DERIVED: protocol] Evaluate six methods on exactly the same test IDs/histories:
E5 projected577 primary; E5 raw769 offline diagnostic; original mean10-577;
the prior selected frozen quadratic8; the prior selected frozen supervised
soft-attribute8; privileged true-attribute8. The latter supervised comparison
retains its256 teacher/256 selection attribute bits; the primary uses none.
No-memory/reset is the analytically balanced50% control. No hard-attribute
alternative or projection family is searched.

Each route keeps its32 latest signed-int8 contributions. Learn adds the new
contribution and subtracts the expired SAME contribution; Infer takes an exact
public-query dot product, predicting+1 when score>=0. Record all128 queries
after all three phases in all64 histories for all six methods:147,456 scores,
24,576 per method, with8,192 final queries per method. Report all four joint
simple/XOR-XNOR strata, both marginal rule types, skill0 initial/retained/reversed,
skill1 learned/retained and exact state/output retention. No example selection.

The primary is a useful successor only if ALL gates pass: final accuracy>=75%;
paired gain over original mean10>=10 percentage points; positive lower endpoint
of its descriptive history-paired1.96*SE interval; nonlinear-instance gain over
original>=10 points; simple-rule regression no worse than5 points; exact
untouched-route state/output retention; and primary final accuracy no more than
2 points below raw769. Report paired gaps to both negative methods and the
raw projection gap even on failure. The raw diagnostic cannot qualify as a
577-coordinate success. Repeated histories do not supply independent new
linguistic samples; no text-population significance claim will be made.

## Arithmetic, audit and role costs

[DERIVED] Contributions/queries stay in[-127,127]; state coordinates in
[-4064,4064]. Generic absolute score bounds are d*32*127^2 for d577 or769.
Use int64 and independently replay every primary checkpoint/score with Python
integers and direct retained-queue sums. Check full denominator/target/sign
records; teacher/selection coordinates of the three old frozen baselines must
match their old cached arrays exactly. A numerical mismatch is evidence to
retain, not permission to alter a frozen baseline.

[DERIVED: privacy/cost contract] The source issuer sees plaintext text, category
label, tokens, E5 or SmolLM2 activations and derived vectors before encryption.
Query text and query features are public here. Public policy includes the
projection, teacher centers/radii/scales and model assets; no learned resident
state enters feature generation. Count E5's inherited representation training
as source pretraining, not absence of supervision. Record model file hashes,
runtime/settings, actual token/padding counts, CPU/wall time/RSS and feature/
policy bytes. Extra projection work is442,368 public scalar products and441,792
reduction adds per source or query text. This does not estimate total private
computation from577 state coordinates or claim operator-private source encoding.
No new encrypted run, restricted reader or no-master-read claim is made.
