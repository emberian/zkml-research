# Frozen protocol v1 (written before any feature extraction/results)

[DERIVED specification] This is a plaintext classification utility experiment, not a
cryptographic implementation. A public frozen SmolLM2-135M executes actual cached
weights at revision `93efa2f097d58c2a74874c7e644dbc9b0cee75a2`. `trust_remote_code=False`,
local-files-only loading, CPU float32, 2 torch threads, evaluation mode, no KV cache.
The classifier consumes its final-token hidden vector; no transformer weight changes.

[DERIVED specification] Public synthetic sensor domain is all pairs (x,y) in
{-8,...,8}². Each independent history privately samples a quadratic decision rule over
[1,x/8,y/8,xy/64,x²/64,y²/64]. A second phase uses the opposite rule: this deliberate
change makes the order test identifiable. Teaching events carry the rule's ±1 label;
query prompts carry only the coordinates. They contain no examples, teaching labels,
previous tokens or prior KV cache. No private user data is read.

[DERIVED specification] A fixed public seed partitions 289 coordinates into 192
teaching coordinates and 97 query coordinates; no query pair appears in teaching.
Each phase samples 96 teaching coordinates without replacement, then presents those
same coordinates under the opposite rule. Each history therefore has 192 events.
History seeds are disjoint: development 11000..11007, selection 22000..22007,
held-out test 33000..33031. Each history creates its own unrelated private rule.
Protocol/hyperparameter changes after inspecting held-out outcomes require a new
version and new held-out seeds; v1 results remain retained.

[DERIVED specification] Controls: frozen model's A-vs-B token preference; no-memory
constant; fading label mean; kNN over model features; kNN over normalized sensor
coordinates; normalized LMS over full model features; normalized LMS over a fixed
64-dimensional random projection of model features; LMS over the six engineered
quadratic features. A public center and scale use only the teaching coordinates'
unlabeled frozen features. Readout states initialize to zero. Numeric polynomial
features are an explicitly task-engineered comparator, not a pretrained model result.

[DERIVED specification] LMS step is m' = rho*m + eta*(label-dot(m,phi))*phi, with
phi scaled by max teaching-feature norm (bias included). Hyperparameters eta in
{0.03,0.1,0.3,1.0}, rho in {1.0,0.995,0.98,0.95}. kNN chooses k in {1,3,7,15} and
capacity in {32,64,192}, fixed recent suffix, unweighted majority with +1 ties.
Fading mean chooses rho in the same grid. Select by mean *post-change* query accuracy
on selection histories; stable lexical configuration order breaks ties. Development
results are recorded separately and cannot select on final test histories.

[DERIVED specification] Report before-change accuracy, post-change accuracy, prior-rule
retention (on the same held-out coordinate queries), memory-reset and unrelated-memory
swap accuracy, and disagreement under AB versus BA order of the same labeled event
multiset. Equal public queries plus different individual memories must change outputs.
Log per-history accuracy and history-level uncertainty, not 32×97 allegedly independent
samples. Include saved per-query decisions for auditing.

[DERIVED specification] Cost accounting separates measured CPU latency from scalar
operation formulas and secure operations not implemented. Private teaching inputs
would taint the entire feature-extracting transformer; a final-only private readout
on a public query can keep the frozen backbone public. Moving the memory earlier
would taint all subsequent layers. Count readout selection, stored data, and the
privacy of coordinates, labels, feature normalization and access patterns explicitly.
