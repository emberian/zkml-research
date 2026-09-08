# Finite Gaussian obligation: a bounded reference and its price

[DERIVED/EXECUTED, 2026-09-08] A strict finite independent-bit reference
can instantiate the product-Gaussian sampling used by the repaired ring
and direct smudged-scalar proofs with additional statistical loss below
`2^-207` across a conservative combined proof ledger. Its direct arithmetic
is expensive. This closes the bounded sampler's mathematical existence
and finite error accounting at the stated scope; it does not provide an
audited practical sampler, a CSPRNG security argument, or a hardness proof.

[EXECUTED freeze] SPEC.md was frozen before any sampler implementation at
SHA256 `2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576`.
The subsequent `python3 check_bounds.py` exits 0 using only deterministic
rational/integer arithmetic. It computes a public π interval, verifies
the factorial, precision/cap inequalities and draw/resource counts, and
pins the repaired input sources. It does not evaluate a random proposal,
generate a Gaussian output, or run an encryption/estimator/attack.

## 1. What the certificate covers

[DERIVED] The reference uses a power-of-two uniform integer proposal,
cutoff `|k|<8σ`, lower-rounded 256-bit acceptance thresholds, 320-bit
directed arithmetic, and at most 4096 attempts. Its exact infinite
target law has weights `exp(-πk²/σ²)`. The deterministic error terms are

| comparison | per-output total variation upper bound |
|---|---:|
| excluded ideal Gaussian tail | 3·2^-256 |
| finite acceptance threshold | 64·2^-256 |
| attempt-cap fallback | 2^-256 |
| combined Gaussian output | 68·2^-256 |

[DERIVED] Poisson summation gives `Zσ≥σ`; this cancels the extraneous
width factor in the tail estimate. Machin's rational sums are exact before
one outward rounding. The directed Taylor/squaring proof bounds the
acceptance error uniformly, without an unresolved irrational comparison
or a floating-point exponential assumption. The cap is unconditional;
fallback zero is included in the output law.

[EXECUTED] The helper's π interval has one 320-bit grid unit of width,
inside the specified three-unit allowance. The certified post-squaring
interval-width upper count is 164,606 units, below the proof's `2^19`
allowance. The check validates `81!>2^320` and the exact rational cap
inequality. No Gaussian density was used in place of a normalized discrete
probability.

## 2. The proof-wide budget

[SOURCE/EXECUTED] SOURCES.json pins the repaired ring's hardness/GRID.json
point `N=16384,w=64,σK=2^25,σe=2^10`, and the scalar hardness/REBUILT.json
point `n=16384,l=262144,σK=2^32,σe=2^10`. These replace the earlier
smaller dimensions for this calculation. Both retain d=577,r=16,T=384.

[EXECUTED] The actual ring workload requires 419,430,400 Gaussian draws;
the scalar workload requires 104,857,600. Actual setup counts only the
16 privately sampled recipient rows. A one-shot reduction may instead
sample all 577 rows in its comparison and conservatively allows all 384
error vectors, giving 1,007,681,536 and 251,920,384 draws, respectively.

[DERIVED] The safe Gaussian-loss multiplier is
`2Qactual+4TQred`: two actual bit worlds, and both computational challenge
worlds for the theorem's `2T` reduction term. The extra target-error
allowance also permits comparison of the ideal LWE error distribution
with a bounded sampled error distribution; it is not a demand that the
reduction know its challenge's secret error. For a bounded-LWE formulation,
charge the corresponding uniform challenge draws in the uniform allowance.

[EXECUTED] The combined Gaussian multiplier is 1,935,797,125,120,
below `2^41`, so its loss is below `2^-208`. A bounded uniform-integer
sampler with a 512-attempt cap has output error at most `2^-512`.
Charging each reduction even for an entire scalar public matrix yields
a combined uniform-output multiplier of 6,655,579,293,184, below `2^45`.
Its loss is below `2^-467`. The sum is below `2^-207`, inside the
predeclared aggregate sampler budget `2^-192`.

[DERIVED] These additive terms can instantiate the corresponding ideal
privacy ledger with bounded independent-bit circuits, while preserving the
same exact LWE hypothesis or explicitly charging the challenge-distribution
comparison. They do not establish that hypothesis. In particular, the
estimated work of a selected lattice heuristic is not an advantage-versus-
resource curve for the now-explicit reduction overhead.

[DERIVED correctness consequence] Every finite Gaussian output, including
fallback, obeys the strict cutoff deterministically. The finite uniform
flood output also stays in its specified interval, including fallback.
Thus the existing bounded-error decoder inequalities apply to every
reference-sampler output under exact arithmetic and the stated plaintext/
window premises. The ideal Gaussian tail term remains part of the
distribution comparison, rather than an unhandled finite execution event.

## 3. Resource burden

[DERIVED/EXECUTED] Each Gaussian output uses at most 17 expected proposals
and at most 4096 proposals. The direct threshold recipe takes at most
179 bounded integer products per attempt, plus divisions, shifts and
comparisons. The actual-workload upper counts are:

| reference upper count | repaired ring | scalar repair |
|---|---:|---:|
| expected proposals | 7,130,316,800 | 1,782,579,200 |
| maximum proposals | 1,717,986,918,400 | 429,496,729,600 |
| expected integer products | 1,276,326,707,200 | 319,081,676,800 |
| maximum integer products | 307,519,658,393,600 | 76,879,914,598,400 |
| expected random-bit byte equivalent | 241,182,965,760 | 60,358,131,712 |
| maximum random-bit byte equivalent | 58,110,907,514,880 | 14,542,759,264,256 |

[DERIVED] These are upper bounds from the fixed reference's probability
and operation ledger; they are not measured runtimes, lower bounds on
sampling cost, or a claim that a whole random tape must reside in memory.
Streaming generates only the bits actually needed. The worst-case bounds
still matter for strict bounded-QPT resource accounting. The uniform-modulus
and flood draws, matrix/ring arithmetic, metadata and application work are
additional costs.

[EXECUTED] Full 256-bit acceptance tables would need 524,256 bytes for
the error width, 17,179,869,152 bytes for the ring key width, and
2,199,023,255,520 bytes for the scalar key width. The known k=0 index
is interpreted as full acceptance without storing a 257-bit threshold.
No table was generated. Table lookup changes memory/access-pattern costs
and does not by itself establish a safe constant-time implementation.

[INFERRED practical scope] The direct arithmetic reference is a poor
candidate for this workload without substantial optimization. The
certificate demonstrates finite samplability; it should not be counted
as a practical latency result. Karney's exact discrete sampler and Falcon's
specialized narrow-width reference were inspected as primary leads, but
neither is imported as a drop-in strict-cap sampler for these distributions
and this aggregate error budget. Their precise source limitations and
links are in SPEC.md §8.

## 4. Remaining boundaries

[OPEN] A faster implementation requires a separately frozen specification,
complete distribution error, bounded runtime/memory and an independent
review. No sampler implementation or random experiment was performed here.
The arithmetic helper's success does not replace implementation validation.
The assigned independent reviewer is checking this frozen mathematical
certificate without generating random outputs.

[DERIVED] Replacing independent unbiased bits with CSPRNG output introduces
a computational assumption at the full tape length, with appropriate
independent private seeds and matching quantum-advice class. That assumption
cannot be converted into a tiny statistical error merely by choosing a
large seed. Leaking sampler logs, variable-time traces or private seeds is
outside the accepted-output transcript theorem.

[OPEN] This package does not implement the other ALS proofs' continuous,
correlated or singular-covariance Gaussian steps. It covers the repaired
ring and direct smudged-scalar product-Gaussian constructions only. Numerical
LWE hardness, structured attack coverage, application semantic nonvacuity
and ciphertext integrity remain separate obligations.

[EXECUTED meter] Two primary search queries; three page-open calls covering
two pages; two in-page finds; zero Scry calls, zero PDF downloads, zero
estimator or Sage calls, zero random Gaussian/key/ciphertext outputs. Local
source and result hashes are recorded. The search was targeted orientation;
no absence claim is made.
