# Actual ring construction execution

[EXECUTED] The repaired ring candidate now has a reusable implementation.
`ring.py` supplies recipient-local key generation, public-only registration,
absent-key public setup, full-vector encoding, signed combination, exact
window expiry and designated integer decoding. `run.py` is the runnable CLI.
The complete repaired parameter point executed successfully, rather than
being extrapolated from a toy run.

| Full repaired run | Measured result |
|---|---:|
| Ring dimension N / module width w | 16,384 / 64 |
| Plaintext coordinates / actual recipients | 577 / 16 |
| Fresh encryptions | 3 |
| Fresh / live-window / signed designated reads matched | 48 / 48 / 16 |
| Total run | 265.738 s |
| Peak process RSS | 2,188,001,280 bytes (2.038 GiB) |
| Public A generation | 1.112 s |
| Recipient key generation and publication | 172.527 s |
| Direct-uniform missing public rows | 10.994 s |
| Encode times | 12.827 / 10.490 / 10.985 s |
| All-16-recipient fresh read times | 6.628 / 6.463 / 6.332 s |
| Window update times | 0.072 / 0.137 / 0.150 s |
| Signed combination / all-recipient read | 0.248 / 6.362 s |

[EXECUTED provenance] Exact command:

```sh
./.venv/bin/python -B run.py --profile candidate_full --inputs 3 --output results/candidate_full_001.json > results/candidate_full_001.log 2> results/candidate_full_001.stderr.log
```

[EXECUTED] Exit status was zero. The JSON contains the platform, Python/FLINT
versions, original command, exact parameters, source hashes, all per-input
times and counters. Source hashes before and after the run matched. Reports
contain no secret row, encryption coins, raw ciphertext or private input.
All inputs are public deterministic synthetic fixtures. The two-item live
window's final update actually expires the original first ciphertext; its
state matched a rebuilt sum coefficient-for-coefficient. A signed
`2*ciphertext0-ciphertext1` combination also decoded correctly.

[SOURCE/EXECUTED] The point uses the frozen repaired grid's 289-bit prime,
key width `2^25`, error width `2^10`, flood radius `2^247`, `W=32` and
encoding denominator `8204908842`. Only 16 actual recipient rows were
sampled. All 561 missing public rows were sampled directly uniformly, without
creating corresponding private keys. Actors are simulated in one process;
the public registration API accepts a public product, not a secret row.

## Where time went

[EXECUTED] Actual key sampling drew 16,777,216 Gaussian coefficients in
146.712 seconds. Error sampling drew 3,145,728 coefficients in 23.758 seconds
across the three encodes. Thus the full run generated 19,922,944 Gaussian
coefficients. It made 318,910,957 proposals and 78,104 direct threshold
evaluations, with zero cap fallbacks. Most proposals used certified squeeze
table decisions. The Gaussian calls requested 2,451,639,648 OS random bytes;
this is measured byte consumption, not an independent-entropy claim about
the OS generator.

[EXECUTED] Error sampling took 8.920, 7.243 and 7.596 seconds inside the
three encodes. Remaining encode work took 3.908, 3.247 and 3.389 seconds,
including uniform randomness, exact polynomial multiplication, scalar
products and basis/encoding operations. A separate saved arithmetic probe
measured one exact N=16384 negacyclic product at 0.024747 seconds and one
length-16384 constant-product dot at 0.003089 seconds. These are individual
measurements on a shared machine, not distributional performance claims.

[INFERRED] Native or batched handling of Gaussian proposals is the first
measured optimization target. Reusing extracted ciphertext coefficients
across recipients would also remove repeated Python/FLINT conversion during
the all-recipient read benchmark. The current result does not measure either
optimization or extrapolate a 384-input throughput guarantee.

## Smaller executions and arithmetic controls

[EXECUTED] `toy_002` uses the final core source and ran five encodes at
N=64,w=4,d=9,r=2, including repeated expiry. `candidate_n_probe_001` ran
three encodes at candidate N/modulus/Gaussian widths with w=8,d=33,r=2;
setup took 2.952 seconds and encodes took 1.179–1.369 seconds. The initial
toy/probe reports retain their earlier core source hashes, before the public
registration API split and timing-breakdown additions. They are developmental
measurements; `toy_002` and `candidate_full_001` pin the final code.

[EXECUTED] Six small exact polynomial cases were compared with an independent
quadratic negacyclic convolution oracle, including the constant-product sign.
Every actual plaintext basis transformation was inverted. Oversized signed
combinations were rejected. These checks accompany real construction runs;
they are not substitutes for them.

## Scope and storage

[DERIVED] The mathematical bit-packed storage targets at this point remain
37,900,653 bytes per ciphertext, 379,389,952 bytes for public A and P, and
3,801,088 bytes for one cutoff-bounded recipient key. Packing is **not
implemented**; measured RSS describes this Python/FLINT execution instead.
The ring operations are exact arbitrary-precision operations, without a
floating FFT approximation. The practical sampler implements the finite
SPEC threshold law using a rigorously bounded integer squeeze table and lazy
acceptance bits; see `sampling/DESIGN.md` for its independent-bit premise.

[OPEN] The full computation uses ordinary expected-time uniform rejection
and variable-time Python/FLINT operations. It has no constant-time claim,
secure-memory boundary, authenticated registration, integrity layer,
serialized credential lifecycle or complete bounded-QPT implementation
claim. Functional success is not a Ring-LWE hardness test or a computational
security proof. The fixed-coordinate/scalar-window scope remains; arbitrary
matrix updates and nonlinear encrypted computation are not implemented.
All original ring, hardness and finite-sampler packages remain frozen.
