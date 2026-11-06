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
| Packed GF(2^16) encode, ns per codeword byte | Xeon core 4.7-9.9 (5.5 used); T4 per-layer 0.115-0.15; **T4 fused 0.074-0.14 (0.088 used)**; H100+ = T4 x SIMT ratio | [MEASURED runs/redesign-encode-t4-01, -02]; [MODEL] beyond T4 |
| 64-core CPU box | 128x one Kaggle core (2x per core, linear: leaves are independent) | [MODEL TOWER256.md section 5] |
| TPU v5e | Keccak-f 6.1e8/s (1.0e4 VPU int32 ops, 32-bit bit-interleaved, no rotate); Tower256 at T4's op-equivalents | [A]: VPU rate unpublished, uncalibrated |
| PIOP for the packed design (zerocheck + Shout read-check + ring switching) | 16 Tower256 mults per row | **[A]**, the largest open input; --sensitivity varies it 4x |
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
  [MODEL]. Even unfixed, per byte of record content the T4 encode costs ~3.5 ns for the whole packed 80-bit
  trace (160 KiB codeword x 0.088 ns/B per 4 KiB record), against ~146 ns **per trace column** today (0.6 ms per
  ell-14 column: 114,688 Tower256 multiplies at 2.87e8/s and the measured 0.67 efficiency).

## 4. Results (`composed.py --markdown`)

**leaf** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 62.27 ms | 486.5 us | 3.32 ms | 780.5 us | 722.5 us | 672.6 us | 1.71 ms |
| b | - | - | 1.49 ms | 295.8 us | 250.1 us | 236.1 us | - |
| c | 4.53 ms | 35.4 us | 286.6 us | 68.2 us | 63.2 us | 58.8 us | 143.3 us |
| c128 | 3.23 ms | 25.2 us | 110.5 us | 25.3 us | 23.4 us | 21.8 us | 56.4 us |
| cB | 2.21 ms | 17.3 us | 106.6 us | 24.7 us | 22.9 us | 21.3 us | 53.5 us |
| d | 611.58 ms | 4.78 ms | 7.64 ms | 1.53 ms | 1.18 ms | 1.09 ms | 4.59 ms |

**aggregate-recursive** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 2.29 s | 17.89 ms | 42.39 ms | 10.46 ms | 9.63 ms | 8.92 ms | 75.94 ms |
| b | - | - | 15.96 ms | 3.88 ms | 3.55 ms | 3.29 ms | - |
| c | 222.18 ms | 1.74 ms | 4.11 ms | 1.01 ms | 933.8 us | 864.9 us | 7.40 ms |
| c128 | 220.88 ms | 1.73 ms | 3.93 ms | 971.6 us | 894.0 us | 827.9 us | 7.31 ms |
| cB | 82.82 ms | 647.1 us | 1.52 ms | 375.2 us | 345.3 us | 319.8 us | 2.74 ms |
| d | 1036.24 s | 8.10 s | 12.95 s | 2.59 s | 1.99 s | 1.85 s | 7.77 s |

**aggregate-batch** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 69.75 ms | 544.9 us | 5.33 ms | 1.27 ms | 1.18 ms | 1.10 ms | 2.76 ms |
| b | - | - | 2.16 ms | 420.2 us | 346.7 us | 328.7 us | - |
| c | 4.59 ms | 35.9 us | 290.5 us | 69.3 us | 64.1 us | 59.7 us | 151.9 us |
| c128 | 3.29 ms | 25.7 us | 114.5 us | 26.3 us | 24.4 us | 22.7 us | 64.9 us |
| cB | 2.10 ms | 16.4 us | 107.5 us | 25.0 us | 23.1 us | 21.5 us | 56.3 us |
| d | 1.32 s | 10.35 ms | 16.55 ms | 3.31 ms | 2.55 ms | 2.36 ms | 9.93 ms |

**audit@0.01** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 697.5 us | 5.4 us | 53.3 us | 12.7 us | 11.8 us | 11.0 us | 27.6 us |
| b | - | - | 21.6 us | 4.2 us | 3.5 us | 3.3 us | - |
| c | 45.9 us | 0.4 us | 2.9 us | 0.7 us | 0.6 us | 0.6 us | 1.5 us |
| c128 | 32.9 us | 0.3 us | 1.1 us | 0.3 us | 0.2 us | 0.2 us | 0.6 us |
| cB | 21.0 us | 0.2 us | 1.1 us | 0.2 us | 0.2 us | 0.2 us | 0.6 us |
| d | 13.24 ms | 103.5 us | 165.5 us | 33.1 us | 25.5 us | 23.6 us | 99.3 us |

**stream** (seconds per record)

| design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPUv5e |
|---|---|---|---|---|---|---|---|
| a | 103.68 ms | 810.0 us | 4.82 ms | 1.15 ms | 1.07 ms | 991.1 us | 3.47 ms |
| b | - | - | 2.01 ms | 408.9 us | 346.9 us | 327.0 us | - |
| c | 8.41 ms | 65.7 us | 357.3 us | 85.8 us | 79.4 us | 73.8 us | 278.7 us |
| c128 | 7.11 ms | 55.5 us | 181.3 us | 42.9 us | 39.6 us | 36.8 us | 191.8 us |
| cB | 3.52 ms | 27.5 us | 132.3 us | 31.1 us | 28.8 us | 26.8 us | 103.3 us |
| d | 19.46 s | 152.07 ms | 243.31 ms | 48.66 ms | 37.43 ms | 34.76 ms | 145.98 ms |

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
| a | 0.45 | 0.23 | 0.52 | 0.82 | 2.46 | 2.29 | 0.28 |
| b | - | - | 0.21 | 0.27 | 0.72 | 0.68 | - |
| c | 0.03 | 0.01 | 0.03 | 0.04 | 0.13 | 0.12 | 0.02 |
| c128 | 0.02 | 0.01 | 0.01 | 0.02 | 0.05 | 0.05 | 0.01 |
| cB | 0.01 | 0.01 | 0.01 | 0.02 | 0.05 | 0.04 | 0.01 |
| d | 8.62 | 4.31 | 1.61 | 2.14 | 5.31 | 4.93 | 0.99 |

Phase split for one record (`--breakdown`, abridged): design (a) on one Xeon core is hash 48 ms + encode/fold 11 ms
+ PIOP 3 ms; design (c) is hash 1.9 ms + encode/fold 1.1 ms + PIOP 1.5 ms. On a T4, (a) is arithmetic-bound
(as measured) and (c) is PIOP-bound (the [A] input).

## 5. Sensitivity (`--sensitivity`)

```
ratio a / c, aggregate-batch: cpu1 15.2x, cpu64 15.2x, T4 18.3x, H100 18.4x, B200 18.4x, B300 18.4x, TPUv5e 18.2x
packed encode x0.25: cpu1 17.8x, cpu64 17.8x, T4 19.0x, H100 19.0x, B200 19.0x, B300 19.0x, TPUv5e 19.0x
packed encode x4.0: cpu1 9.6x, cpu64 9.6x, T4 16.0x, H100 11.8x, B200 11.8x, B300 11.8x, TPUv5e 10.7x
piop mults/row 4: a/c cpu1 20.1x, cpu64 20.1x, T4 44.7x, H100 46.3x, B200 46.3x, B300 46.3x, TPUv5e 41.1x
piop mults/row 64: a/c cpu1 7.7x, cpu64 7.7x, T4 5.5x, H100 5.4x, B200 5.4x, B300 5.4x, TPUv5e 5.6x
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
   is modelled at 36 us per record against an H100's 69 us, and at about a quarter of the H100's $ per record.
   GPUs pay for the packed leaf only if the PIOP's multiplies move to a tensor path (folds by a sampled r are
   fixed-r multiplies: ROTATION 2(b)) or get a bit-sliced GF(2^128) kernel; neither is built.
4. **Audit sampling multiplies everything by p.** At 1%, the packed design costs 0.3-0.7 us per record on any
   accelerator; the store's own cSHAKE commit (31-47 Keccak-f per 4 KiB) is then the bill, and it is paid anyway.
5. **Internal BLAKE3 (cB vs c128) buys 1.0-1.6x batched and 2.7x on per-leaf recursion.** With batch-first
   aggregation it is a small lever; it is not worth a ruling change before the packed prover exists.
6. **TPU:** nothing in this pipeline is MXU-shaped after packing (no CLMUL, no byte shuffle, Keccak on a 32-bit
   VPU without rotates). Its rows rest on [A] VPU rates; it is not a leaf-prover target.

## 7. What would change these numbers

- A measured PIOP: the binary zerocheck + Shout read-check over a packed DFA trace, per row (the [A] 16).
- The B200/H100 runs in flight (accel-b200-mma-01): Keccak-f/s and Tower256 table rate on Hopper/Blackwell.
- A bit-sliced fused GF(2^16) encode on the T4 (predicted 0.03 ns/B; the unbuilt fix in section 3).
- A measured binary recursion step for a Keccak-path verifier (BinarySpartan's rate is on M4 Max, not ours).
