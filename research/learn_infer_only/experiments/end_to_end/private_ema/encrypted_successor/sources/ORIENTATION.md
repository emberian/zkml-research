# Primary-source orientation after the fixed utility comparison

[SOURCE] Read Zhou et al., arXiv:2605.27782v1 (27 May 2026), introduction,
Theorem 3.3/proof sketch, Remark 5.4, §7 and Appendix F Algorithm 5. The client
generates and retains the FHE secret key; Algorithm 5 ends by decrypting model
weights. The setting protects outsourced training from a semi-honest server;
DP addresses downstream model disclosure. [Primary HTML](https://arxiv.org/html/2605.27782v1#S1).

[SOURCE] Theorem 3.3 assumes strongly convex original objective, smooth
surrogate and bounded gradient/objective discrepancy. Its optimization bound
is conditional on these premises. Remark 5.4 says experiments use a DP
data-dependent refinement. §7 excludes PCA from DP accounting. These details
qualify an abstract-only reading of data-independent hyperparameter selection.
[Theorem](https://arxiv.org/html/2605.27782v1#S3),
[experimental setup](https://arxiv.org/html/2605.27782v1#S7).

[DERIVED] This is useful guidance for bounding approximation intervals before
encrypted training. It does not supply our fixed signed-floor EMA's theorem,
restricted-release credential or no-master-read construction. No published
convergence result is transferred to the eight-register learner here.

[OPEN] The implementation, complete reductions and DP numerical accounting
were not independently reproduced. No VERDICTS change follows from this source
read; no novelty or field-wide absence claim is made.

[EXECUTED] `access.json` pins the archived HTML and read scope: three web-tool
calls (zero searches, three opens, four find actions), one direct HTML archive
fetch, zero Scry SQL/schema and zero PDF downloads. Root's earlier two search
queries are recorded separately and not charged again to this lane.
