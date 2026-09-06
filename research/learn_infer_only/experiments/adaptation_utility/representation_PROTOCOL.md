# Representation study v1 — preregistered before extraction and selection

[DERIVED specification] Separate follow-on to the failed last-token text transfer
control. No interface/security/recovery tests are part of this task. Use the same
cached, pinned SmolLM2-135M weights/tokenizer and local CPU runtime, without downloads
or backbone training. Four fixed candidates: final last-token hidden vector;
masked token mean after10 decoder blocks; mean after20 blocks; final mean after30
blocks and final RMSNorm. Each representation has576 coordinates. Forward hooks at
blocks9/19 pin the first two layer identities; pooling excludes padding tokens.

[DERIVED specification] The two arbitrary binary skills and latent balanced rules
are unchanged. A NEW teacher/selection/final text corpus has names, whole templates,
and complete cue phrases disjoint across its three pools and from corresponding
previous experiment surfaces. Exact tables are in representation_data.py. Every
latent cue combination is taught, so this is transfer to new textual surface forms,
not unseen logical combinations. No historical target label, rule, target decision,
or history identity enters model feature extraction. The true-attribute control uses
privileged generator metadata and is labeled accordingly.

[DERIVED specification] New independent history seeds: development61000..61007,
selection62000..62015, final63000..63031. Each history teaches64 examples of skill0 A,
then64 of independent skill1 B, then64 of changed skill0 -A. Reuse all queries per
surface pool (64 per skill) and the earlier phase/retention metrics. Teacher features
are public synthetic inputs; only teacher features fit normalization. Model-feature
centers/scales are per public skill and use no labels or query-domain statistics.

[DERIVED specification] For each representation, compare shared/routed LMS, shared/
routed kNN, and shared/routed exact signed-int8 contribution windows. LMS eta grid
{.03,.1,.3,1},rho{1,.995,.98,.95}; kNN k{1,3,7},TOTAL item capacity{32,64,128};
window TOTAL capacity{16,32,64,128}. A routed memory divides its total item budget
between2skills, and holds two learned readout/accumulator vectors. Window issuer
encoding is clip(round_even(127*phi),-127,127) times the observed label; resident update
adds new contribution and subtracts the identical queued expired contribution.
Include routed lexical LMS/kNN/window and shared true-attribute LMS/window controls,
plus no-memory. Do not invert predictions or change these settings on test outcomes.

[DERIVED specification] Select hyperparameters separately for each representation/
method by mean final TWO-skill accuracy on selection histories AND selection text.
Also choose the best representation for each of the six model methods by that same
selection criterion. Stable serialized settings/representation name resolve ties.
Persist selections before final evaluation. Record all representation test results as
prespecified comparisons, without post-test reselection. Development histories provide
separate descriptive output. No setting is tuned on final target labels.

[DERIVED specification] Report final accuracy, changed skill0, retained skill1,
interference after each other-skill training phase, and paired history-level differences
from final-last-token features and from retrieval. Use histories as uncertainty units.
No memory has exactly50% due to balanced query labels. A result above60% with a positive
paired descriptive interval would be useful on THIS synthetic task; it would not
establish general language competence, protected execution or resident autonomy.
If no representation transfers, preserve that failure and the positive control.

[DERIVED specification] Bound:384 short synthetic model prompts in one full-forward
pass per prompt, collecting all four representations; at most90minutes overall.
Actual extraction runs all30blocks, so a counted10-block prefix is NOT a measured
speedup. Pooling adds576*(n-1) scalar sums and576 public length scalings. Private
source tokens taint every executed prefix layer plus pooling; an already-informed
issuer may compute fixed features, but provenance/quantization binding is still due.
Public query features can remain public with final-only private memory. Public skill
routing and lengths remain declared metadata; no protected feature encoder is built.
