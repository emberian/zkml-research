# Finite reduction constants — bounded result

[DERIVED, 2026-09-08] `FINITE_THEOREM.md` supplies explicit quality,
Gaussian-image, gadget operator-norm, convolution, discretization and
prime-power rank bounds. It replaces hidden constants by conservative
finite inequalities and corrects the balancing noise in ALS's printed
Lemma 5 recipe by a factor `sqrt(2)`.

[REPORTED] The construction author independently confirmed the printed
recipe discrepancy from the rendered ALS p.22. A separate mathematical
review is in progress in `adversarial_review/pq_finite_reduction/`. Its
first pass corrected one proof sentence: the hint is integral via
`h=Z(b'+c)-[I_d|0]b`; the pre-discretization quantity `Zb'` need not be
integral. The candidate theorem was then frozen for further review at
SHA256 `7ae20bc50552283e4688466b966c7e2d1265613f4fb8a49c2909aaeb77bd7bd4`.

[EXECUTED] The public integer/rational checker exits 0. All three original
cost profiles fail this conservative finite reduction certificate; two
adjusted fixed-coordinate profiles pass. The 1024 profile retains its
encryption parameters and changes the base LWE hypothesis to width
`βq=2^18`. The 4096 profile doubles its row count and uses `βq=2^13`.
See `PARAMETERS.md`, `INPUTS.json`, and `RESULTS.json`.

[DERIVED boundary] All mathematical statistical losses are explicit. The
finite-bit reduction sampler's entire output-tuple discrepancy remains an
explicit hypothesis `δs`, not a computed zero. If `δs≤2^-160`, the fixture's
non-LWE privacy term is below `2^-139`; the full bound still includes
`768 εLWE`. Correctness tails, application score encoding, and any scheme
sampling approximation are separate obligations. No numerical computational
hardness or security level is inferred.

[DERIVED resolved route choice] A direct quality-witness argument gives
`s_min(X)≥1/q2`; no new random-matrix net lemma is needed. The earlier
spectral-net lead in the initial status was not used. This chooses a larger
explicit gadget norm rather than leaving a spectral constant unspecified.

[EXECUTED scope] Only this new directory was written. Frozen earlier notes
and the author's artifacts are unchanged. No cryptography, Gaussian sampling,
estimator, private-state or attack execution occurred. Four exact primary
source files and extracts are pinned in `SOURCES.json`; ePrint sources were
read solely from the absolute local mirror. The non-ePrint AR PDF is retained
as local source evidence, not a generated result.

[EXECUTED network meter] Two targeted web search queries; one arXiv abstract
open; one arXiv PDF download; zero ePrint downloads; Scry SQL/schema 0/0;
Kagi 0. No broad survey was performed.
