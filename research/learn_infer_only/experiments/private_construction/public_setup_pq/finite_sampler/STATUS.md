# Finite sampler source/math checkpoint

[DERIVED, 2026-09-08] SPEC.md gives a bounded independent-bit rejection
reference with cutoff 8σ, 256-bit acceptance thresholds, 320-bit directed
arithmetic and 4096 attempts. The per-Gaussian bound is below 68·2^-256;
the conservative combined repaired ring/scalar proof allowance is below
2^-208. Uniform-range caps and CSPRNG assumptions are separated.

[EXECUTED] SPEC.md was frozen before implementation at SHA256
2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576.
The subsequent deterministic check_bounds.py exits 0; RESULTS.json records
the certified inequalities, repaired-input counts and resource totals.
AUDIT.md distinguishes bounded mathematical existence from practical cost.
Independent reviewer polynomial_kernel owns adversarial_review/finite_sampler/.

[EXECUTED scope] No random sampler, private key, encryption, Gaussian draw,
estimator or attack was run. Two primary web search queries, three page-open
calls covering two pages, two in-page finds; zero Scry queries and zero PDF
downloads. The exact source locations and narrow reuse limitations are in
SPEC.md. No literature absence claim is made.
