# The composed model: leaf proving, recursion, audit and verification, per design and per target

2026-11-06, redesign lane. Script: `notes/redesign/composed.py` (stdlib; `python3 -I composed.py [--markdown |
--breakdown a c | --sensitivity]`). It is a sibling of `notes/construction-search/space.py`, not a fork: space.py
prices one zkML token position in proxy units, this file prices the certificate pipeline in seconds on named
hardware. Every input in the script carries [MEASURED:run], [X:source], [MODEL:source] or [A].

## 1. What is composed

A **record** is one 4 KiB content certificate (a DFA with at most 256 states over cSHAKE-committed bytes, the
leaf of LEAF-PROVER-DECISION section 6). Per record:

| workload | composition |
|---|---|
| leaf | one proof, handed over as is |
| aggregate-recursive | leaf + one recursive verification of it inside a binary-field prover |
| aggregate-batch | one proof over 1,024 records; one recursion per batch (x1.3 for the batch proof's verifier) |
| audit@0.01 | commit-then-audit: the store's cSHAKE commit is paid anyway; prove (batched) with probability 1% |
| stream | 64 KiB windows (16 records) proved as one relation, then accumulated at 0.3x a recursion [A] |
| verify | native light-client verification on one Kaggle core |

GPU and TPU rows are **batch throughput per record**. A single 4 KiB leaf on a GPU is launch-bound
(T4: ~300 launches, TOWER256.md section 4); one CPU core is the right device for a single leaf.

## 2. Inputs

| input | value | tag |
|---|---|---|
| Keccak-f, Kaggle Xeon core | 536 ns | [MEASURED accel-tower-dryrun-04] (this lane's plain C Keccak: 1,191 ns, runs/redesign-encode-t4-01) |
| Tower256 multiply, Kaggle Xeon core (PCLMUL + Barrett) | 22.9 ns | [MEASURED accel-tower-dryrun-04] |
| Keccak-f/s, T4 | 4.35e8 (6.9e8 in another session) | [MEASURED accel-tower-dryrun-04, tune-03] |
| Tower256 multiply, T4 log/exp tables | 2.87e8/s | [MEASURED] |
| T4 calibration for design (a) | measured 0.82 ms per batched ell-14 word against the model's 0.55 ms: efficiency 0.67 on (a)/(b) GPU rows | [MEASURED] |
| Keccak-f/s, H100/B200/B300 | SASS bound x 0.8 (3.6e9/3.9e9/4.2e9 bound) | [MODEL predict.py section 1] |
| Tower256 multiply, H100/B200/B300 | T4 x SIMT lanes x clock (4.1x, 4.4x, 4.8x) | [MODEL TOWER256.md section 5, OPTIMAL Rule 2] |
| Tensor GF(2) route speedup on arithmetic, design (b) | 2.9x T4, 3.9x H100, 4.7x B200, 4.5x B300 (fused, unbuilt) | [MODEL ROTATION 2(c)]; the unfused T4 kernel measured 5-8x **slower** than the table (MMA.md section 9) |
| Packed GF(2^16) encode, ns per codeword byte | Xeon core 4.3-10.2 (5.5 used); T4 per-layer 0.106-0.15; T4 fused 0.074-0.14; **T4 fused, basis tables 0.055-0.079 (0.063 used)**; H100+ = T4 x SIMT ratio | [MEASURED runs/redesign-encode-t4-01, -02, redesign-piop-t4-03]; [MODEL] beyond T4 |
| 64-core CPU box | 64 Genoa-class cores = 78 Kaggle cores (1.3x per core, 94% thread scaling, both measured on the PIOP kernel on dregg-forge) | [MEASURED ratio, MODEL extrapolation]; was 128 [A] |
| TPU v5e | Keccak-f 6.1e8/s (1.0e4 VPU int32 ops, 32-bit bit-interleaved, no rotate); Tower256 at T4's op-equivalents | [A]: VPU rate unpublished, uncalibrated |
| PIOP for the packed design (zerocheck + Shout read-check + one-hot openings) | measured minimal layer: **8.00 Tower256 mults/row, 161-186 ns/row** on one Kaggle core; DFA leaf = 2x that (16/row) | [MEASURED kernels/piop.c, section 8] x [INFERRED 2x composition] |
| PIOP for design (a) | 8 Tower256 mults per row per column, 4 columns | [A] |
| Packed trace width | byte 8 + state 8 + Shout one-hot d = 4 x 16 = 80 bits per row; position virtual | [A] |
| Recursion | verifier Keccak-f x 38,400 binary constraints; BinarySpartan 287k Keccak-f/s on 12 M4 Max cores | [X ePrint 2026/1656 section 4] |
| BLAKE3 against Keccak-f | SIMT: 5.8x per 64-byte node, 2.7x per leaf byte; binary R1CS: 2.7x per node (14k vs 38.4k) | [MODEL OPTIMAL 3.2 SASS count; X 2026/1656] |
| BabyBear design (d) | Keccak content binding in-circuit, 63,192 cells per Keccak-f; 1.3e9 cells/s per H100 | [READ LEAF-PROVER-DECISION section 1; X SASH via space.py --calibrate] |
| Prices | H100 $2.33/h, B200 $7.50/h (vast.ai, RUNBOOK section 1); v5e spot $0.36/chip-h (GCP-LEDGER); T4 $0.35/h, 64-core box $1.50/h, B300 = B200 | [READ] / [A] |

## 3. The prototype kernel (measured, bit-exact)

`notes/redesign/kernels/`: `encode.c` (CPU: NEON on aarch64, SSSE3 on x86, scalar tail), `encode_gpu.cu`
(per-layer and fused kernels), `check_encode.py` (Lagrange reference over GF(2^16) with an independent port of
minidregg's Fan-Paar multiply; also checks that a T_4 scalar acts coordinate-wise on Tower256, 50 random pairs),
`kaggle_entry.py`. Algorithm: systematic rate-1/4 additive Reed-Solomon (Lin-Chung-Han novel basis) over GF(2^16)
= T_4, interleaved across R lanes; then a cSHAKE-shaped Keccak Merkle tree with one wide leaf per codeword column.
Because Tower256 is a T_4-vector space with T_4 scalars acting coordinate-wise, R = 16 x (Tower256 lanes) is
exactly the packed-Tower256 encode with T_4 twiddles.

Checks (all pass): Lagrange at (ell, R) = (2,1), (3,3), (4,17), (5,33) on the Mac and (3,3), (4,17), (5,36) on the
Kaggle Xeon; the codeword's SHAKE digest is identical across Mac NEON, Xeon SSSE3, the T4 per-layer kernel and the
T4 fused kernel at every shape run on two or more of them.

| run | shape (ell, R) | codeword | Xeon core encode | Xeon core Merkle (plain Keccak) | T4 per-layer | T4 fused |
|---|---|---:|---:|---:|---:|---:|
| t4-01/-02 | 8, 16 | 32 KiB | 0.30 ms (9.1-9.9 ns/B) | 2.4 ms | 0.20 ms (launch-bound) | - |
| | 10, 256 | 2 MiB | 9.8 ms (4.7-4.9) | 24 ms | 0.35 ms (0.17) | 0.19 ms (0.090) |
| | 12, 256 | 8 MiB | 47 ms (5.7-5.9) | 97 ms | 0.97 ms (0.115) | 0.62 ms (0.074) |
| | 12, 1024 | 32 MiB | 175 ms (5.2-7.8) | 334 ms | 3.9 ms (0.116) | 2.95 ms (0.088) |
| | 14, 1024 | 128 MiB | - | - | 17.1 ms (0.128) | 13.7 ms (0.102) |

What the kernel says:
- **CPU:** encode and Merkle are the same order (5.5 vs ~4.5 ns per codeword byte with the tuned 536 ns Keccak).
  The encode is unblocked (one memory pass per layer); a cache-blocked LCH is the known 2-3x.
- **T4:** the fused kernel is 1.2-1.6x the per-layer one, and still ~3x above its HBM floor: the four nibble
  lookups per element hit shared-memory bank conflicts (16 random indices over 8 banks). The fix is a bit-sliced
  constant multiply (16 planes per GF(2^16) element fit in registers, unlike Tower256's 256), predicted ~0.03 ns/B
  [MODEL]. **Correction (run redesign-piop-t4-03):** the bank-conflict diagnosis was wrong. A table of 16 u16
  entries spans 8 consecutive words, i.e. 8 distinct banks, and equal words broadcast, so these lookups are
  conflict-free. The measured overhead was the per-tile table build (64 dependent global gathers per twiddle):
  gathering only t x 2^m (16 per twiddle) and building entries by XOR gives 0.055-0.067 ns/B (1.2-1.4x), and
  5 layers per pass with 64 row-words gives 0.072-0.079 at ell 14. What remains is ALU + LDS per element
  (~20 ops and 4 table loads per constant multiply); a bit-sliced constant multiply is still the next step. Even unfixed, per byte of record content the T4 encode costs ~3.5 ns for the whole packed 80-bit
  trace (160 KiB codeword x 0.088 ns/B per 4 KiB record), against ~146 ns **per trace column** today (0.6 ms per
  ell-14 column: 114,688 Tower256 multiplies at 2.87e8/s and the measured 0.67 efficiency).

## 4. Results (`composed.py --markdown`, after the measured PIOP of section 8)

**leaf** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 62.27 ms | 798.4 us | 3.32 ms | 780.5 us | 722.5 us | 672.6 us | 1.71 ms |
| b | - | - | 1.49 ms | 295.8 us | 250.1 us | 236.1 us | - |
| c | 4.45 ms | 57.1 us | 282.5 us | 67.5 us | 62.5 us | 58.2 us | 141.3 us |
| c128 | 3.21 ms | 41.1 us | 106.5 us | 24.5 us | 22.7 us | 21.2 us | 54.3 us |
| cB | 2.19 ms | 28.1 us | 102.5 us | 23.9 us | 22.2 us | 20.6 us | 51.5 us |
| d | 611.58 ms | 7.84 ms | 7.64 ms | 1.53 ms | 1.18 ms | 1.09 ms | 4.59 ms |

**aggregate-recursive** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 2.29 s | 29.35 ms | 42.39 ms | 10.46 ms | 9.63 ms | 8.92 ms | 75.94 ms |
| b | - | - | 15.96 ms | 3.88 ms | 3.55 ms | 3.29 ms | - |
| c | 222.11 ms | 2.85 ms | 4.10 ms | 1.01 ms | 933.1 us | 864.3 us | 7.40 ms |
| c128 | 220.86 ms | 2.83 ms | 3.92 ms | 970.9 us | 893.3 us | 827.3 us | 7.31 ms |
| cB | 82.80 ms | 1.06 ms | 1.52 ms | 374.4 us | 344.6 us | 319.2 us | 2.74 ms |
| d | 1036.24 s | 13.29 s | 12.95 s | 2.59 s | 1.99 s | 1.85 s | 7.77 s |

**aggregate-batch** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 69.75 ms | 894.3 us | 5.33 ms | 1.27 ms | 1.18 ms | 1.10 ms | 2.76 ms |
| b | - | - | 2.16 ms | 420.2 us | 346.7 us | 328.7 us | - |
| c | 4.52 ms | 57.9 us | 286.4 us | 68.5 us | 63.5 us | 59.1 us | 149.9 us |
| c128 | 3.27 ms | 41.9 us | 110.4 us | 25.6 us | 23.7 us | 22.1 us | 62.9 us |
| cB | 2.08 ms | 26.7 us | 103.4 us | 24.3 us | 22.5 us | 20.9 us | 54.3 us |
| d | 1.32 s | 16.98 ms | 16.55 ms | 3.31 ms | 2.55 ms | 2.36 ms | 9.93 ms |

**audit@0.01** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 697.5 us | 8.9 us | 53.3 us | 12.7 us | 11.8 us | 11.0 us | 27.6 us |
| b | - | - | 21.6 us | 4.2 us | 3.5 us | 3.3 us | - |
| c | 45.2 us | 0.6 us | 2.9 us | 0.7 us | 0.6 us | 0.6 us | 1.5 us |
| c128 | 32.7 us | 0.4 us | 1.1 us | 0.3 us | 0.2 us | 0.2 us | 0.6 us |
| cB | 20.8 us | 0.3 us | 1.0 us | 0.2 us | 0.2 us | 0.2 us | 0.5 us |
| d | 13.24 ms | 169.8 us | 165.5 us | 33.1 us | 25.5 us | 23.6 us | 99.3 us |

**stream** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 103.68 ms | 1.33 ms | 4.82 ms | 1.15 ms | 1.07 ms | 991.1 us | 3.47 ms |
| b | - | - | 2.01 ms | 408.9 us | 346.9 us | 327.0 us | - |
| c | 8.33 ms | 106.8 us | 353.2 us | 85.1 us | 78.7 us | 73.2 us | 276.7 us |
| c128 | 7.09 ms | 90.9 us | 177.2 us | 42.2 us | 38.9 us | 36.2 us | 189.8 us |
| cB | 3.50 ms | 44.9 us | 128.2 us | 30.4 us | 28.1 us | 26.1 us | 101.3 us |
| d | 19.46 s | 249.55 ms | 243.31 ms | 48.66 ms | 37.43 ms | 34.76 ms | 145.98 ms |

**verify** (seconds per record)

| design | cpu1 |
|---|---|
| a | 28.55 ms |
| b | 28.55 ms |
| c | 2.79 ms |
| c128 | 2.79 ms |
| cB | 2.79 ms |
| d | 28.55 ms |

**$ per million records, aggregate-batch**

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 0.45 | 0.37 | 0.52 | 0.82 | 2.46 | 2.29 | 0.28 |
| b | - | - | 0.21 | 0.27 | 0.72 | 0.68 | - |
| c | 0.03 | 0.02 | 0.03 | 0.04 | 0.13 | 0.12 | 0.01 |
| c128 | 0.02 | 0.02 | 0.01 | 0.02 | 0.05 | 0.05 | 0.01 |
| cB | 0.01 | 0.01 | 0.01 | 0.02 | 0.05 | 0.04 | 0.01 |
| d | 8.62 | 7.07 | 1.61 | 2.14 | 5.31 | 4.93 | 0.99 |


Phase split for one record (`--breakdown`, abridged): design (a) on one Xeon core is hash 48 ms + encode/fold 11 ms
+ PIOP 3 ms; design (c) is hash 1.9 ms + encode/fold 1.1 ms + PIOP 1.5 ms. On a T4, (a) is arithmetic-bound
(as measured) and (c) is PIOP-bound (multiplies measured on CPUs, section 8; no GPU PIOP kernel).

## 5. Sensitivity (`--sensitivity`)

```
ratio a / c, aggregate-batch: cpu1 15.4x, cpu64 15.4x, T4 18.6x, H100 18.6x, B200 18.6x, B300 18.6x, TPUv5e 18.4x
packed encode x0.25: cpu1 18.2x, cpu64 18.2x, T4 19.1x, H100 19.1x, B200 19.1x, B300 19.1x, TPUv5e 19.0x
packed encode x4.0: cpu1 9.7x, cpu64 9.7x, T4 16.8x, H100 13.2x, B200 13.2x, B300 13.2x, TPUv5e 12.2x
piop mults/row 4: a/c cpu1 20.2x, cpu64 20.2x, T4 46.3x, H100 47.6x, B200 47.6x, B300 47.6x, TPUv5e 42.3x
piop mults/row 64: a/c cpu1 7.9x, cpu64 7.9x, T4 5.5x, H100 5.4x, B200 5.4x, B300 5.4x, TPUv5e 5.7x
```

The ranking of (c) over (a) holds at every target under a 4x move of either uncertain input: 5.4-50x per record.
The PIOP constant decides whether the packed leaf is 5x or 50x better on GPUs; it is the next thing to measure.

## 6. What the composition says (not visible from any one kernel)

1. **Per-leaf recursion is the largest cost in the system.** Verifying one leaf proof inside a binary recursion
   prover costs 37x the leaf for (a) and ~50x for (c) on one core (53k and 5k verifier Keccak-f x 38,400
   constraints). Batching 1,024 records into one proof removes ~99.9% of it. No hash or field change comes close
   to that lever. Codex reached the same conclusion blind (CODEX.md).
2. **Packing is the second lever: 15-18x per record, every target.** Today's leaf commits 32 bytes per byte of
   content and hashes one element per Merkle leaf (65k Keccak-f per column for 31 Keccak-f of content).
3. **After packing, the hot operation is the extension-field multiply in the PIOP, and CPUs do it natively**
   (PCLMUL: 22.9 ns per Tower256 multiply against 12,000-17,400 int32-op equivalents on SIMT). A 64-core CPU box
   (Genoa-class, per-core rate and thread scaling measured on dregg-forge, section 8) is modelled at 58 us per
   record against an H100's 69 us, at half the H100's $ per record.
   GPUs pay for the packed leaf only if the PIOP's multiplies move to a tensor path (folds by a sampled r are
   fixed-r multiplies: ROTATION 2(b)) or get a bit-sliced GF(2^128) kernel; neither is built.
4. **Audit sampling multiplies everything by p.** At 1%, the packed design costs 0.3-0.7 us per record on any
   accelerator; the store's own cSHAKE commit (31-47 Keccak-f per 4 KiB) is then the bill, and it is paid anyway.
5. **Internal BLAKE3 (cB vs c128) buys 1.0-1.6x batched and 2.7x on per-leaf recursion.** With batch-first
   aggregation it is a small lever; it is not worth a ruling change before the packed prover exists.
6. **TPU:** nothing in this pipeline is MXU-shaped after packing (no CLMUL, no byte shuffle, Keccak on a 32-bit
   VPU without rotates). Its rows rest on [A] VPU rates; it is not a leaf-prover target.

## 7. What would change these numbers

- ~~A measured PIOP~~ done (section 8): 8.00 multiplies and 161-186 ns per row for the minimal layer; the full DFA
  layer's 2x is still a composition from measured parts, not a run of the full layer.
- The B200/H100 runs in flight (accel-b200-mma-01): Keccak-f/s and Tower256 table rate on Hopper/Blackwell.
- A bit-sliced fused GF(2^16) encode on the T4 (predicted 0.03 ns/B; the unbuilt fix in section 3).
- A measured binary recursion step for a Keccak-path verifier (BinarySpartan's rate is on M4 Max, not ours).

## 8. The measured PIOP (closes the model's one guessed input)

`kernels/piop.c` (+ `gf256.h`), checked by `kernels/piop_ref.py`. The minimal packed-binary leaf layer:

1. **zerocheck** `sum_x eq(tau,x) (a b + c) = 0` over three committed binary columns packed 64 rows per word,
   Gruen-factored eq (`eq(t,x) = 1 + t + x` in characteristic 2), round 0 on bits with no field multiplies,
   rounds >= 1 at 9 multiplies per pair, the eq tables for later rounds by pairwise XOR;
2. **Shout read-check** (one 16-entry Tower256 table, 4-bit address column): round 0 bucketed (16 multiplies),
   its fold by a 16-entry `rho * val` table, later rounds 3 multiplies per pair;
3. **one-hot opening claims** `ra~(rho, v)` for v < 16: one eq table and bucketed XORs.

Challenges and arithmetic in GF(2^256) in the polynomial basis mod x^256 + x^10 + x^5 + x^2 + 1 (Rabin-checked
irreducible in the reference), isomorphic to Tower256 (minidregg's fast prover computes the same way and converts
at the boundary). Multiply: PMULL (aarch64) or Karatsuba PCLMULQDQ (x86) plus a two-step sparse reduction.

**Checks (all pass, on the Mac, dregg-forge and the Kaggle Xeon):** `piop_ref.py` regenerates the instance from
the same SplitMix64 stream, recomputes every prover message with Python integers and unfactored sums (0
mismatches at ell 3, 5, 7, 8, 9), then runs the verifier: round consistency for both sumchecks, the final
zerocheck claim against the trace's multilinear extensions evaluated directly, the lookup claim and final value
against `sum_x eq val[addr]` directly, the 16 one-hot claims against their MLEs and `sum_v val[v] ra~ = g~`. With
one violated row (`bad` 5, 77, 300) the zerocheck **rejects** while the transcript still matches the reference.

| machine | ell | ns/row, one core | mults/row | multi-core |
|---|---:|---:|---:|---|
| Kaggle Xeon @2.0 GHz (redesign-piop-t4-03) | 12 / 14 / 18 | 161 / 174 / 186 | 8.01 / 8.00 / 8.00 | 4 threads on 4 vCPU: 1.46e7 rows/s (2.5x) |
| dregg-forge, EPYC Genoa, 16 cores | 14 / 18 | 139-141 / 128 | 8.00 | 16 threads: 8.3e7 (ell 14), 1.18e8 (ell 18) rows/s = 94% of linear |
| Mac (M-series, load ~40) | 12-18 | 57-60 | 8.00 | - |

Per multiply inside the proof: ~20-23 ns on the Xeon (the minidregg prover's 22.9 ns standalone), ~16-17 ns on
Genoa, ~7 ns on the Mac. bb2 (32 cores) was not used: its load was 35 on 32 vCPUs from obend's jobs, so a
throughput number there would have measured the neighbour and slowed it.

**Into the model.** The DFA leaf's layer is the measured one with four address chunks sharing one eq table and
~6 zerocheck columns: 15.5 multiplies per row by the measured per-component counts (zerocheck 5n for 3 columns,
lookup 0.5n + 1.5n per chunk, openings n). The model keeps 16 multiplies per row and, on CPUs, uses the measured
174 ns/row x 2 instead of multiplies x rate. The [A] it replaces predicted 366 ns/row on the Kaggle core; the
measurement gives 348. **The guessed input was right to 5%;** the ranking and every headline number stand. On
GPUs the PIOP is still multiplies x the measured table rate (no GPU PIOP kernel): it is 80% of a packed leaf on a
T4 and H100, the one place left where a GPU kernel (bit-sliced GF(2^128)/Tower256, or fixed-r tensor folds)
would change a ranking.

## 9. Native openings (migration step 1), measured

minidregg `lane/redesign-native-openings` 95463f3ae: `prover/cuda/tower256_openings.c` assembles each round's
openings (leaf pair, `encode_nat(k - 1)`, base-255 sibling digests) through ctypes; the Python path is kept as the
fallback and, with `--openings-check`, compared byte for byte every round. Entry: `kernels/openings_entry.py`.
Every receipt below is identical to the CPU prover's expected bytes (`expect_ell*.json`).

| T4, ms (runs/redesign-openings-t4-02, -03) | ell 14 wall | ell 18 wall | ell 20 wall | ell 20 openings |
|---|---:|---:|---:|---:|
| Python openings | 119.1 | 202.8 | 334.6 | 212.0 |
| native assembly | 42.6 | 78.7 | 153.8 | 42.8 |
| + device-side sibling indices | 40.6 | 76.2 | **143.5** | **31.5** |

The remaining 31.5 ms are k - 1 small gathers per round plus their copies; one gather kernel per round is the next
cut. Host emulation on the Mac: ell 20 openings 77.7 -> 7.2 ms. Run t4-01 failed before proving (the entry parsed
two GPUs' compute capabilities as one); kept in `runs/` as the record.
