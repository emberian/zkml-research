# Supervised attribute calibration, frozen contract

[HYPOTHESIS] Public supervision of the two source attributes may repair the
previous text representation failure while leaving the resident update exactly
`C[route] += label * feature; C[route] -= expired_contribution`, with a queue of
32 contributions per route. This is an added supervised encoder, not
unsupervised adaptation, a new cryptographic construction, or private model
execution. Budget: one local model extraction of 128 new texts and at most two
hours of work. No downloads, backbone training, encryption runs, or core edits.

## Fit and selection, before new test evaluation

[DERIVED: protocol] Reuse the frozen 128 teacher and 128 selection prompts and
their cached SmolLM2 mean10 vectors. Give the source encoder two explicit binary
attribute labels per teacher prompt: 256 labeled bits, covering 64 prompts per
route. Selection uses another 256 explicit attribute bits. These attribute
labels were present in the public synthetic generator but were NOT supervision
for the original mean10 or PCA/quadratic baselines. No history-specific category
rule or category label enters encoder fitting or selection.

For each route, center mean10 on its 64 teacher vectors and divide by the same
teacher maximum norm used by the original frozen encoder. Fit two ridge heads
for attributes a,b, with unpenalized target-mean intercept. The only grid is
lambda = [0.0001, 0.001, 0.01, 0.1, 1.0]. Choose one global lambda by largest
mean selection accuracy across the four heads (threshold >=0.5 predicts 1),
then smallest clipped probability mean squared error, then largest lambda.
All teacher prompts are balanced in each attribute. No online utility score
selects the calibration or any other setting. Save selection, parameters and
their hashes before extracting/evaluating new test texts.

Clip a,b predictions to [0,1]. The primary representation contains the four
products [(1-a)(1-b),(1-a)b,a(1-b),ab] in that route's four slots of an 8-vector,
padded with zeros to 577. The prespecified secondary diagnostic is the same
one-hot vector after thresholding a,b at 0.5. This secondary method cannot
replace the primary after outcomes are seen. Quantize each coordinate by
clip(round-to-nearest-even(127*x),-127,127). Public query encoding uses no gold
attribute or category labels. The positive control alone uses gold attributes.

## New surfaces and histories

[DERIVED: protocol] Freeze a new generator and all 128 test texts before model
execution: two skills, four attribute combinations, eight new entity names
per skill, and two new full templates with new full cue phrases. Audit full
names, templates and cue phrases against BOTH earlier text generators, and
exclude the live-text name Marigold. Names/templates/phrases must be disjoint;
ordinary words and the underlying attribute meanings necessarily overlap.
All four logical attribute combinations remain represented in teacher data.
This tests new linguistic surfaces, not unseen logical combinations.

Freeze 64 new history seeds 65000..65063. Each history uses the original teacher
examples: 64 updates of skill0, 64 of skill1, then 64 of skill0 with its rule
reversed. Each route has an independently sampled balanced Boolean rule.
History seeds are independent; the same 128 test texts are reused across them.
No new test example occurs in a teacher stream or working model context.

## Fixed comparisons and acceptance

[DERIVED: protocol] Compare on exactly the same histories, updates and query IDs:
primary soft calibration; secondary hard calibration; original frozen 577-d
mean10; the previous selected negative quadratic8 with its EXACT frozen
teacher PCA/normalization; privileged true-attribute8; and no-memory (50%).
Every model-derived representation uses the same mean10 extraction for each
new text. No refit or reselection of the baseline or quadratic8 is allowed.

Run the same signed-int8 W32 update, route-isolated queues and >=0 score tie
convention. Record all 128 query scores at all three checkpoints for all 64
histories and five nonzero-memory methods: 122,880 paired predictions, including
40,960 final predictions (8,192 per method). Preserve failures and full records.
Report skill0 initial/retained/reversed and skill1 learned/retained, final mean,
both simple and XOR/XNOR strata and all four joint rule strata with their exact
counts. Never infer text-population significance from the history replication.

The primary is a useful successor only if ALL of these prespecified conditions
hold on final predictions: accuracy >=75%; paired mean gain over original
mean10 >=10 percentage points; its descriptive 1.96*SE history-paired interval
has positive lower endpoint; nonlinear skill-instance gain over original >=10
points; simple-rule skill-instance regression versus original <=5 points;
and both untouched-route state and output retention are exact. Report paired
comparisons with quadratic8 regardless of success. No representative example
selection is needed and no one-example result can qualify.

## Numerical, cost and privacy boundaries

[DERIVED] Values are in [-127,127], state coordinates in [-4064,4064], and a
generic 577-coordinate score has absolute bound 577*32*127^2=297,805,856. Use
int64 arithmetic and audit primary checkpoints/scores with Python integers.
This is the already studied BFV-compatible arithmetic shape; no claim of a new
encrypted execution or release restriction follows from this experiment.

[DERIVED: accounting] Keep model revision/file hashes, interpreter/dependency
versions, extraction settings, token counts, fit/encode CPU and wall time,
process RSS, generated bytes and fitted parameter bytes. Model: cached
HuggingFaceTB/SmolLM2-135M revision
93efa2f097d58c2a74874c7e644dbc9b0cee75a2; CPU float32, eager attention,
eval/inference mode, no gradients/cache, right padding excluded in masked mean,
direct block9 output, same two-thread/one-interop settings and seed7901.
The implementation may run all 30 blocks; count the work actually executed.

[DERIVED: taint] The entitled source issuer sees raw teaching text, route and
category label, all token IDs/activations, predicted attributes and contribution
vector. A public query encoder sees its query text and predicted attributes.
The fitted policy is public and carries added supervision. The encrypted host
would see public routes/timing/lengths and ciphertexts; neither plaintext source
processing nor the original full-key trusted reader becomes operator-private
because the resident stores only 577 encrypted coordinates. No label, oracle
attribute or private history state may enter query features. Gold attributes
exist only in the explicitly privileged control and evaluation oracle.
