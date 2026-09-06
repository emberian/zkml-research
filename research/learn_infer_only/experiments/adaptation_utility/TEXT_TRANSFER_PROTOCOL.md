# Text transfer and independent-skill retention protocol v1

[DERIVED specification] Written before this task's model execution/results. This is
plaintext representation/readout adaptation on actual frozen SmolLM2-135M weights,
not protected execution or a broad test of language models. No weights are trained.

[DERIVED specification] Two independent synthetic skills map binary textual cues to
class ±1: plant care (soft/rigid leaves × wet/dry soil) and letter style
(familiar/unfamiliar recipient × formal/casual event). Each individual history draws
an independent balanced 4-entry rule for each skill. These arbitrary class meanings
must be learned from that history; no class label is put in any query feature.

[DERIVED specification] Teaching text uses eight names and two templates per skill,
16 texts for each of four cue combinations (64 examples per skill). Selection queries
use different names, templates and cue paraphrases. Final queries use a third disjoint
set of names, templates and cue paraphrases. All four latent cue combinations occur
in teaching, so this tests semantic/paraphrase transfer on unseen surface forms,
not generalization to unseen logical combinations. The interaction cases include
XOR/XNOR; full rule identities and results are retained. Engineered latent attributes
are an explicitly privileged upper control, not a model parsing accomplishment.

[DERIVED specification] History sequence: teach skill0 rule A on all64 teacher texts;
teach independent skill1 rule B on all64 teacher texts; teach skill0 opposite rule
-A on the same64 texts. Each phase order is independently permuted by history seed.
Measure both skills after every phase. Compare the same event multiset in reversed
skill0 order (-A, B, A), resets and unrelated history-memory swaps. Skill1 retention
after the final skill0 change measures interference with an independently taught skill.

[DERIVED specification] Development seeds51000..51007, selection52000..52015,
final53000..53031. Teacher strings are common public feature inputs; histories differ
in private rules/order. Development/selection use the selection-query text pool;
final evaluation alone uses final-query texts. No test labels select settings.
Hyperparameters are selected for mean final accuracy across BOTH skills, then frozen
before final evaluation. Exact seed/rule/order/query outputs are retained.

[DERIVED specification] Methods: no-memory constant, shared and skill-routed kNN over
frozen-model features, shared and routed normalized LMS over model features,
skill-routed lexical kNN and LMS controls, and an eight-state engineered cue/skill
one-hot LMS. Shared/routed model readouts have577/1154 scalars. Routed kNN divides a
fixed total item budget equally across skills (not twice the shared budget).
Lexical controls use a fixed public dictionary from teacher texts and discard unknown
words, making the loss of exact-word overlap visible. Model readout centers are
computed per skill from unlabeled teaching features and normalized by that skill's
max teaching-feature norm; the same map is used for shared/routed readouts. Query
features contain only query text and the public skill identifier. No teaching label,
rule coefficient, target class, history index, or private state enters the extractor.

[DERIVED specification] LMS eta in{.03,.1,.3,1},rho in{1,.995,.98,.95};
kNN k in{1,3,7},total capacity in{32,64,128}. Attribute control gets the same LMS grid.
Stable serialized configuration order resolves equal selection scores. Every grid
result is retained. Queries use no prior context or KV cache. kNN releases the label
of matched memory by majority, not an LM-generated answer from a retrieved prompt.

[DERIVED specification] Main outcomes: final accuracy per skill and mean, skill0 loss
after learning skill1, skill1 loss after changing skill0, order disagreement per skill,
reset/swap scores, learned/retrieval and learned/lexical paired differences. Histories
are uncertainty units. Report both interpolation/nonlookup strengths and limitations;
never infer a generic LM verdict from this small constructed task.

[DERIVED specification] Bound compute: at most384 short cached-model prompts and no
backbone training/download. Record model execution time separately from scalar-cost
estimates. Skill routing is public metadata in this experiment; private routing needs
oblivious access. The full private-taint bill is inherited from ADAPTATION_UTILITY.md
and adjusted for actual sequence lengths, feature maps and shared/routed memory size.
