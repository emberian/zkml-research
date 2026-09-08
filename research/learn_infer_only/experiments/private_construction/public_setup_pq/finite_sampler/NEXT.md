# Next steps

[EXECUTED] SPEC.md was frozen and sent to root/reviewer before the
deterministic arithmetic helper. check_bounds.py passes, with no sampler
implementation or random outputs. Preserve the frozen spec and source/result
hashes while the independent review completes.

[OPEN] The reference is expensive. After independent review, root can
decide whether a faster bounded sampler deserves a separately specified
implementation task. Exact laws, cap and arithmetic errors, CSPRNG security,
timing leakage and credential ownership must remain distinct.

[OPEN] Integrate the sampler error into the existing strict-QPT privacy
ledger only at the stated scope; do not infer numerical LWE hardness or
cover unrelated multivariate Gaussian reductions.
