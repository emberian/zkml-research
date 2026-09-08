# Preserved first arithmetic attempt

[EXECUTED, 2026-09-08] The first invocation of derive_costs.py exited1 at
the assertion checking the normalized Lemma4/5 parameter inequalities for the
fixed-coordinate polynomial family. It had used sigma2=n^8 and xi=n^10 exactly
at finite n, although the reviewer's family is only asymptotically satisfying.
The terminal traceback ended in details at the assertion
all(normalized_checks.values()). No result was emitted and no crypto ran.

[DERIVED repair] The finite arithmetic illustration now rounds sigma2 upward
to the larger of n^8 and the explicit constant-one Lemma4 expression, then xi
to the larger of n^10 and the constant-one Lemma5 expression. This is recorded
as a normalization/sensitivity choice; it does not determine the source's
unknown constants or turn this point into a security recommendation.
