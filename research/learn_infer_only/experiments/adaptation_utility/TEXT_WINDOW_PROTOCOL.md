# Exact windowed contribution follow-on (after text v1, before window results)

[DERIVED specification] Requested by the coordinator to separate additive bounded
forgetting from LMS error feedback. Preserve the original text-transfer results.
Use its same development/selection/test histories and frozen feature maps; select
new window settings only on original selection histories/texts. This is a related
control on the same held-out task, not a fresh independent benchmark.

[DERIVED specification] A feature issuer who knows the current observation and label
computes P=clip(round_even(127*phi),-127,127) and contributes Z=yP (signed int8).
Keep the most recent W contributions in a queue and C=sum_queue Z in signed int32.
On Learn, C'=C+Z_new-Z_expired; if not full, Z_expired=0. Infer is the sign of
C·P_query, with P_query from the public query. No residual error, inverse, mean,
private floor or saturation is in the resident update; feature quantization is at
the authorized issuer. Full-model/lexical features depend only on the current input.

[DERIVED specification] Compare shared/routed model windows, routed lexical windows,
and shared/routed engineered-attribute windows. W in{16,32,64,128} is TOTAL retained
items; a routed model divides this budget equally between2skills. Routed models hold
2 accumulator vectors; shared models hold1. Select mean final two-skill accuracy,
retain all selection candidates, and report test accuracy, interference, reset/swap,
order reversal, state/queue sizes and score bounds. Public routing is explicit leakage.

[DERIVED] For r<=577,W<=128,|Z_i|<=127, the invariant |C_i|<=127W<=16256 follows
from the actual queue sum. The score satisfies |C·P|<=rW127²<=1,191,223,424<2^31.
Independent recomputation of the queue sum after every update and a Python-bigint
score reference verify the executed integer path. In a ciphertext additive realization,
removing the identical old ciphertext can cancel its contribution/noise algebraically;
that conditional construction is being audited by the HE lane, not implemented here.

[DERIVED specification] Also run a diagnostic using the SELECTED v1 methods on the
same teacher surface forms after learning. This is in-sample diagnostic evidence,
clearly labeled, to distinguish lack of fitting from failure of paraphrase transfer.
It cannot be promoted to held-out success or used to alter the original selections.
