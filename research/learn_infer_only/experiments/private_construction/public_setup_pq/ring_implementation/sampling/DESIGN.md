# Practical finite coefficient Gaussian sampler

[DERIVED implementation, 2026-09-08] `sampler.py` supplies
`sample(sigma, count) -> list[int]`, or `GaussianSampler().sample(...)` for
separate aggregate counters. `sigma` is a positive integer power of two.
The ring prototype uses `sigma_e=2^10` and `sigma_K=2^25`. Coefficients
remain in caller memory; this module writes no files. It uses Python's
`os.urandom` for private random bytes and has no production deterministic
seed or caller-supplied random-tape interface.

[SOURCE: specification, fully read] The target is the **finite output law**
in `../../finite_sampler/SPEC.md`, §§2–5: propose uniformly from
`[-8 sigma,8 sigma)`, reject the negative boundary, accept with the lower
256-bit threshold derived by 320-bit directed integer arithmetic, cap
each output at 4,096 proposals, and return zero on cap exhaustion. Its
ideal comparison law has mass proportional to `exp(-pi*k^2/sigma^2)`.
The source hash is pinned in `MANIFEST.json`.

[DERIVED] The implementation uses the same exact Machin rational interval,
80 Taylor terms, eight directed squarings, and threshold floor as that
specification. It is neither a continuous normal rounded to an integer nor
a floating exponential threshold. All production sampling arithmetic is
integer/rational Python; NumPy, SciPy and Arb are unnecessary at runtime.
The separate verifier uses Arb as an independent numerical enclosure oracle.

## Certified table acceleration

[DERIVED] A shared table has 4,096 cells on the normalized absolute-value
axis `x=|k|/sigma`, with boundaries `j/512`, for `0<=j<=4096`.
For a boundary `j`, compute the specified interval `[vL_j,vU_j]` at
`(k,sigma)=(j,512)`; it encloses `Q*exp(-pi*(j/512)^2)`, where `Q=2^320`,
and has width below `W=2^19`. The final endpoint `x=8` is valid because
the reduced exponent `pi/4` is below one, the Taylor domain bound.

[DERIVED] For cell `j` use

```
lo_j = max(0, floor(vL_(j+1)/2^64) - 1)
hi_j = min(2^256, ceil(vU_j/2^64)).
```

Let `L(k)` be the specification's direct threshold. Monotonicity of the
**real** Gaussian gives
`vL(k) >= Q*rho(k)-W >= vL_(j+1)-W` and
`vL(k) <= Q*rho(k) <= vU_j`. Since `W<2^64`, flooring yields
`lo_j <= L(k) <= hi_j`. This proof does not assume that separately rounded
Taylor outputs are monotone. A full 256-bit coin below `lo_j` must accept;
a coin at least `hi_j` must reject. Only the gap needs a direct threshold.

## Lazy acceptance bits

[DERIVED] A proposal first draws a 32-bit acceptance prefix `p`.
Write a conceptual 256-bit uniform coin as `U=p*2^224+s`, with an independent
224-bit suffix `s`. The sampler immediately accepts when
`p < floor(lo_j/2^224)` and rejects when `p >= ceil(hi_j/2^224)`.
Both decisions hold for **every** suffix. Otherwise compute `L(k)`, split
it as `q*2^224+r`, accept if `p<q`, reject if `p>q`, and on equality draw
the suffix and compare `s<r` (or reject immediately when `r=0`). Thus each
proposal has exactly the prescribed acceptance probability `L(k)/2^256`.
Unused suffixes need not be generated. The zero-coefficient shortcut
always accepts, also as permitted by the specification.

[DERIVED] Candidate bits are obtained by masking a uniform byte word down
to `a+4` bits for `sigma=2^a`, so candidate reduction has no modulo bias.
Proposal and prefix use disjoint bytes; a suffix, when needed, uses fresh
OS bytes. Rejection of the negative boundary gives symmetric support
`|k|<8 sigma`. Accepted/rejected prefix decisions, including suffix cases,
are counted toward the same per-output 4,096-attempt cap. OS byte buffering
and discarded bytes change resource use but not the output distribution
under the independent-byte model. This is equality of output laws, not
equality of consumed bit tapes with the reference ordering.

[DERIVED: conditional transfer] Consequently the specification's per-output
statistical bound `TV < 68*2^-256 < 2^-249` transfers to this algorithm under
independent unbiased input bits, subject to the mathematical argument and
source implementation being correct. Its previously derived workload hybrid
ledger can be reused for the same workloads. No statistical closeness of
the operating system's finite-seed generator to an unbounded independent
random tape is claimed: its computational security is a separate assumption.

## Validation and limitations

[EXECUTED] `MEASUREMENTS.json` records the exact invocation, platform, source
hashes, aggregate tests, and timed sample counts. `RUN.log` keeps stdout.
The test driver evaluates public deterministic points with a 420-bit Arb
`exp`/`pi` oracle, checks direct thresholds and both fast-decision boundaries,
forces the full rejection cap, and forces acceptance/rejection immediately
around a rare suffix threshold. The benchmark measures actual in-memory
samples at both ring widths. No sampled coefficient, seed, key or ciphertext
is persisted. Test-only synthetic byte tapes exercise branch boundaries;
they are not used by the normal API.

[EXECUTED] The saved run completed at 2026-09-08 15:51:59 UTC. It measured
2,200,000 coefficients; an earlier unfrozen smoke run measured another
2,000. All 20,481 public interval/threshold cases and both forced suffix
decisions passed; the forced cap rejected exactly 4,096 proposals.
No natural benchmark cap fallback occurred. Table construction took
0.256 seconds and its four Python endpoint/prefix arrays occupied
753,148 bytes by `sys.getsizeof` accounting in the saved environment.

| Width | Count | Measured seconds | Coefficients/second |
|---|---:|---:|---:|
| `sigma_e=1024` | 100,000 | 0.6871 | 145,546 |
| `sigma_K=33,554,432` | 100,000 | 0.7646 | 130,783 |
| `sigma_e=1024` | 1,000,000 | 7.9582 | 125,657 |
| `sigma_K=33,554,432` | 1,000,000 | 8.4217 | 118,741 |

[EXECUTED scope] These are single runs on a shared machine, with setup
separate and output-list allocation included. They measure sampling only.
The million-coefficient calls requested 95,997,792 error-width OS bytes
and 128,250,496 key-width OS bytes; no 224-bit suffix was needed naturally.

[OPEN] This is variable-time Python research code. Rejection counts,
table accesses, integer arithmetic, and suffix paths are not constant-time.
The OS/host can observe or access process memory; this sampler alone gives
no private execution boundary or absent-master credential property. It
does not implement the construction, audit its lattice assumptions, or
establish production cryptographic suitability. Finite tests are not a
formal refinement proof and sample moments are only gross-error controls.

[DERIVED resource limit] Runtime is bounded by `4096*count` proposals plus
finite table construction; direct evaluations occur at most once per
proposal. Output storage is linear in `count`. The implementation buffers
at most 8,192 proposal words. On the repaired ring widths each word uses
6 bytes (error) or 8 bytes (key) before any rare 28-byte suffix. The table
holds two 256-bit threshold endpoints per cell plus their prefix versions;
`MEASUREMENTS.json` records the actual Python object size. The public
`sigma,count` API imposes no independent application memory quota.
