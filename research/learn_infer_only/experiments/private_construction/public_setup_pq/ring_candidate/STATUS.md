# Ring fixed-coordinate candidate — source/math result

[DERIVED, 2026-09-08] `CANDIDATE.md` gives a concrete compressed ring
construction with independent private recipient rows, direct-uniform absent
public rows, uniform-secret ordinary Ring-LWE, scalar flooding and complete
fixed-coalition privacy/correctness contracts. `RING_REGULARITY.md` proves
an explicit structured setup and augmented-mask bound using CRT ideals,
short vectors and lattice smoothing. No ordinary uniform scalar-matrix
lemma is silently reused.

[DERIVED source correction] The source's global nonmultiple/unit-component
check does not imply local surjectivity in every CRT slot. The public
idempotent example in `RESULTS.json` refutes that sufficient-test claim.
The new candidate omits the tests and charges exact CRT rank failure.
This is not a field-wide impossibility or implementation attack.

[EXECUTED] `check_public_math.py` exits 0. It checks all finite inequalities,
an exact split-prime certificate, 6,642 negacyclic coefficient identities,
224 integer interval shifts, and the source-test counterexample. The
witness has N=4096, module width 64, q of 289 bits, Gaussian key width 2^24,
Gaussian error width 2^10 in the exp(-πx²/σ²) convention, and flood radius 2^244.
For T=384 the ideal-distribution privacy bound is 768ε_RLWE+2^-168;
correctness failure is separately below 2^-203. No hardness estimate is
assigned. The full source algorithms and changed conventions are explicit.

[EXECUTED counts] Ciphertext 9,490,797 B; public A+P 94,847,488 B; each
recipient row 917,504 B on the strict tail event. These are mathematical
bit-packed sizes, not timing, allocator or implementation measurements.
Only w ring ciphertext components remain full polynomials; the d second
components retain scalar constant coefficients. The complete F_p^d plaintext
space is retained through the invertible B transform.

[REPORTED review status] Root assigned an independent source/math review to
`adversarial_review/ring_fixed_coordinate/`. Draft hashes held unchanged:
CANDIDATE.md: 5010b72b024aa7154504a7c0dd0de306fe0068b3af3b33b5026b444c510a0dc2;
RING_REGULARITY.md: 2926555d5842bb71af7b16caec3eef512a9c7cfea99e877b862bcfea79d30e85;
PARAMETERS.md: c23732e366fe5966ddf971c0f69fdf51cec41bee134d0bf3e4da19367631b78d.

[OPEN] The exact QPT Ring-LWE assumption, same quantum-advice class,
finite sampler discrepancy/resource certificate, measured implementation,
and application semantic nonvacuity remain explicit obligations. Existing
scalar-LWE estimates and published RLWE library parameters do not settle them.

[EXECUTED scope/meter] Owned only this new directory. Earlier frozen notes,
companions, shared ledgers and VERDICTS were not changed. No keys,
ciphertexts, Gaussian samples, estimator or attack ran. Two Scry SQL calls
(one saved capacity error, one successful retry), zero schema calls, four
primary web search queries, zero primary page opens, zero PDF downloads,
zero ePrint downloads, zero Kagi queries. All six PDFs read came from the absolute local
mirror. Sources, extraction hashes and the narrow-search scope are recorded.
