# Workload 3: tensor-core exactness probe, T4 subset and paid-box protocol (initiative 17, lane w3-mma)

2026-11-06. Owner of the science: the hardware lane (initiative 14, F3:
`notes/tensor-core-holography/F3-MODEL.md`, `notes/construction-search/mma_counts.py`, Lean premise minidregg
`lane/mma-exact` `Theory/MmaAccumulatorExact.lean`). This lane: compile, port to Turing, dry-run, and make the
one-hour protocol (degg-research `experiments/mma-accumulator-probe/README.md`) runnable on a fresh box.
Tags: [MEASURED] [READ] [A] (assumed, not checked).

## 1. What was built

degg-research `experiments/mma-accumulator-probe/` (new files beside the hardware lane's; theirs untouched):

| file | what |
|---|---|
| `probe_sm75.cu` | Turing shapes: m8n8k16 u8/s8 wrap, m8n8k128 b1 xor.popc (layout-free chain + random words through the fragment layout), m16n8k8 f16 fragment probes (C path, integer-addend C path, in-instruction gaps), issue rates (u8, u4, b1, f16, lop3) |
| `probe_sm80.cu` | sm_80+: m16n8k32 u8/s8 wrap, m16n8k256 b1 and/xor, m16n8k32 u8/s8/e4m3 fragments and gaps, mma.sync rates; sm_90a wgmma (IGMMA, BGMMA, QGMMA, HGMMA) rates and patterned width probes (layout-robust: every row repeats one 16-byte K pattern) |
| `gemm_probe.cu` | copy bandwidth; BabyBear^8 inner product as batched INT8 GEMM (`cublasGemmStridedBatchedEx` 8I -> 32I, every output against a SIMT int64 kernel, three batches against the host); FP16/FP8 limb GEMMs (cuBLASLt); accumulator probes through the GEMM API (sanity, gap, count) for f16, e4m3 (fast accum on/off), e2m1 (unit block scales); split-K forced to 1 variants; dense peak rates |
| `probe_fixed.cu` | probe.cu with the two interpretation fixes (section 3); patch `patches/probe-cu-e4m3-path.patch` |
| `mma_run.py` | driver: compile check of every .cu for sm_75..sm_103a with a SASS opcode census, builds for the device, runs, decides every check on the host from exact Python integers/Fractions, `results.json` per section |
| `t4_entry.py` | Kaggle entry for `mma_run.py --shrink` |

zkml-research `notes/accelerator-readiness/`: `runbook/mma.sh` (paid box), `runbook/mma-bundle.sh` (bundle from a
degg-research commit, sha256 MANIFEST checked on the box), `runbook/mma_kaggle_entry.py` (the script's own T4 dry
run), `mma_t4_model.py` (F3 model rescaled to T4, against the measurements), `patches/probe-cu-e4m3-path.patch`.

probe.cu as written compiles unchanged for sm_80, sm_89, sm_90a, sm_100a, sm_103a (nvcc 13.0.88, Kaggle and forge;
sm_75 fails as expected on m16n8k32). No compile fix was needed.

## 2. Kaggle runs (T4, all harvested under `runs/`)

| id | what | result |
|---|---|---|
| `accel-mma-t4-dry-01` | `mma_run.py --shrink` | 40/40 checks, 76 s |
| `accel-mma-t4-dry-02` | + integer C path, split-K=1 variants, peak | 40/40 checks, 70 s |
| `accel-mma-t4-runbook-01` | `mma.sh --shrink --sku T4 --toolkit conda` (internet on: conda toolkit + CUTLASS) | 44/44 checks (conda env 50 s, probes 82 s); CUTLASS failed in 15 s: conda env lacked curand headers (fixed) |
| `accel-mma-t4-runbook-02` | same, fixed script | 44/44 checks, mma.sh rc 0, 1,648 s; CUTLASS b1 profiler build hit its 1,500 s bound at 26/78 objects on Kaggle's 4 cores (recorded as `rc_cutlass` 124) |

T4 GPU time used by this lane: about 33 min of the 3 h budget (dry-01 1.3, dry-02 1.2, runbook-01 2.7, runbook-02 27.5).

Bit-exact checks (each decided on the host from the stated inputs; none compares the device with itself):
- **u8 wrap** (m8n8k16, layout-free, 64 lanes equal): products 16, 33,024, **33,025, 33,026**, 33,040, 66,048,
  **66,051, 66,052**, 66,064, 10^6, 2^24: register == exact mod 2^32 every time; signed read exact iff P <= 33,025
  (`tensorzkp_bound`), unsigned exact iff P <= 66,051 (`u8_unsigned_bound`). The 33,025/33,026 boundary is hit
  exactly with a C preload of P mod 16 products (instruction granularity is 16).
- **s8 wrap**: (-128)(-128) at 131,071 / **131,072** (= 2^31 exactly, first signed failure, no preload) / 131,088 /
  262,144; (-128)(127) at 132,104 (last exact negative) / **132,105**.
- **b1 xor.popc chain**: 1, 2^24 - 1, **2^24** (reads -2^31), **2^25 + 5** (wraps to 640), C = -7, C = -2^31 + 3:
  all == exact mod 2^32 with parity equal (`s32_parity_exact`, `parity_through_wrap` with u8-legal-size leaves).
- **b1 random words** through the fragment layout, 64 sequences x 1,024 instructions, 1,009 of 4,096 sums
  crossing 2^32: 0 mismatches mod 2^32; and the **GF(2) inner product from an xor-only MMA**
  (AND = (popc a + popc b - XOR)/2, parity needs XOR mod 4, which survives the wrap): 0 mismatches against the
  direct AND parity. So Turing's xor-only BMMA computes GF(2) inner products exactly at any length.
- **f16 fragment layout sanity** (16 random m16n8k8 tiles, 2,048 elements): exact.
- **INT8 inner product** 2^20, 2^22, 2^24, 2^25 (limb-plane layout): every output equal to a SIMT int64 kernel, and
  three batches equal to numpy int64 on the host.
- **FP16 limb inner product** (base-16 digits, 64 limbs/element, sums < 2^23) 2^20, 2^22, 2^24: exact.
- **cuBLASLt f16 sanity** (sparse +-1, K = 2,048) on all 8 heuristic algorithms (+8 split-K=1 variants in dry-02).

## 3. Found before any paid hour (SASS census, nvcc 13.0.88 ptxas) [MEASURED]

| source / kind | sm_80 | sm_89 | sm_90a | sm_100a, sm_103a |
|---|---|---|---|---|
| mma.sync u8/s8 m16n8k32 | IMMA.16832 | IMMA.16832 | IMMA.16832 | IMMA.16832 |
| mma.sync e4m3 m16n8k32 | n/a | **QMMA.16832** | **F2FP unpack + HMMA.16816** | **F2FP unpack + HMMA.16816** |
| mma.sync b1 and.popc m16n8k256 | BMMA | BMMA | BMMA | **software (CALL + IMMA)** |
| mma.sync b1 xor.popc | BMMA | BMMA | **software (CALL)** | **software** |
| wgmma s8 / b1 / e4m3 / f16 | - | - | IGMMA / BGMMA / QGMMA / HGMMA | - |

CUTLASS v4.8.1 agrees: its b1 GEMMs are `max_cc 89` for xor.popc and `max_cc 90` for and.popc
(`python/cutlass_library/generator.py`, GenerateSM80_TensorOp_168256) [READ].

Consequences:
1. **probe.cu's e4m3 C-path on H100/B200/B300 would measure FP16 HMMA, not the FP8 datapath** (e4m3 widens exactly
   to fp16). Only sm_89 runs it natively. The native FP8 width is measured here by wgmma QGMMA (H100) and by
   cuBLASLt (whatever cuBLAS issues: wgmma on sm_90a, tcgen05 on sm_100a).
2. **Blackwell has no 1-bit MMA in hardware.** F3 section 1.5 said "Blackwell's binary-tower path is legacy
   mma.sync .b1 or nothing": it is nothing; the legacy instruction is emulated. Tower256 on B200/B300 is bit-sliced
   SIMT or INT8 0/1 operands with the unpack (F3: 21.8 ms vs 7.2 ms SIMT on H100). The B200 hour still measures the
   emulated b1 rate, but the decision does not wait for it.
3. On Hopper, b1 must be and.popc (xor is emulated). Turing has only xor; the parity identity above makes it enough.

Interpretation fix in probe.cu (patch + `probe_fixed.cu`): the C-path rows use products 2^-5 and read
`m = j + 1`. On T4 HMMA the fp16 analogue gives j_max + 1 = 22 with fractional products (1/8 each) but the
integer-addend C path (C = 2^j, every product 1) is exact through j = 24: the hardware aligns each product
separately and drops it below the window, so fractional rows under-read the window by log2(1/product). For
integer limb sums (Lean `HoldsBelow`), use integer addends; `probe_fixed.cu` prints both and labels the datapath.

## 4. T4 measurements [MEASURED, dry-01 / dry-02; two different T4 instances]

| quantity | dry-01 | dry-02 | model / datasheet |
|---|---|---|---|
| copy D2D, read+write | 237.5 GB/s | 241.7 GB/s | 320 GB/s [A] (0.74-0.76) |
| streaming read | 277.3 GB/s | 277.5 GB/s | |
| mma.sync u8 (m8n8k16) | 4.98e13 MAC/s | 6.28e13 | 6.5e13 [A] (0.77 / 0.97) |
| u4 / u8 | 1.89 | 1.98 | 2.00 |
| **b1 xor / u8 (step 6)** | **7.05** | **7.94** | A100 published 8.00 |
| f16 HMMA / u8 | 0.52 | 0.48 | 0.50 |
| lop3 (SIMT) | 3.11e12 /s | 3.00e12 | 4.07e12 [A] |
| cuBLAS INT8 8192^3 | - | 2.20e13 MAC/s | (0.35 of mma.sync: cuBLAS's Turing INT8 path) |
| cuBLAS f16 8192^3 | - | 1.58e13 MAC/s | |

Accumulator widths on T4 (f16 inputs, f32 accumulate):
- HMMA.1688 fragment probes: in-instruction gaps exact through g = 23 (+) / 24 (-), every k position: exactly the
  fp32 output limit, so the 2-term path is at least fp32 wide. Integer-addend C path exact through 2^24 + 8
  (window 25 bit positions, one guard position beyond fp32), dropped at 2^25 + 8, which fp32 could represent. So
  integer limb sums are exact while they stay below 2^24: **m = 24 on this path**.
- cuBLASLt f16: gap probe m = 24 (+) / 25 (-) at every position 1..2,047 (output-limited); count probe (sum of n
  ones, n up to 2^20) exact on all 16 algorithms including split-K forced to 1.

Model comparison (`python3 -I notes/accelerator-readiness/mma_t4_model.py`), INT8 BabyBear^8 inner product,
dry-02 (dry-01 within 10%):

| N | floor (320 GB/s) | tc term | floor at measured copy | measured | x floor | x copy |
|---|---|---|---|---|---|---|
| 2^20 | 0.210 ms (hbm) | 0.017 | 0.278 | 0.404 | 1.92 | 1.45 |
| 2^22 | 0.839 | 0.066 | 1.110 | 1.592 | 1.90 | 1.43 |
| 2^24 | 3.355 | 0.264 | 4.442 | 5.398 | 1.61 | 1.22 |
| 2^25 | 6.711 | 0.529 | 8.883 | 13.832 | 2.06 | 1.56 |

FP16 limbs (128 B/element): 1.61-1.69x the datasheet floor, 1.22-1.28x copy.

Reading: the model's classification holds on T4 (HBM-bound, tensor term 12x below, time tracks bytes; never more
than 2x above copy bandwidth, so not refuted). The 1.5x acceptance is met against measured copy bandwidth from
2^22 up except at 2^25 (1.56x), and not met against the datasheet number, because T4's GDDR6 copy itself reaches
only 0.75 of 320 GB/s. The 2^25 step (1,024 batches) is slower per byte than 2^24 (512 batches) on both
instances: a cuBLAS kernel-choice or TLB effect to check on the paid box (the run records both). The element-major
layout (`NT`, lda 32) is `CUBLAS_STATUS_NOT_SUPPORTED` for INT8 on T4; the limb-plane layout (`TN`, K-contiguous)
runs. The paid script tries both.

## 5. The paid-box script

`runbook/mma.sh` (bundle: `runbook/mma-bundle.sh ~/dev/degg-research <rev>`; on the box
`tar xzf mma-bundle.tar.gz && bash mma/mma.sh --sku B300`):
1. hardware check (`--any-gpu` overrides), `nvidia-smi -q`, sha256 of the sources against the bundle MANIFEST;
2. toolkit: the system nvcc if new enough for the GPU (12.0 sm_90a, 12.8 sm_100a, 12.9 sm_103a) plus pinned pip
   numpy/cmake/ninja if missing; otherwise a rootless, pinned conda-forge CUDA 12.9 env (micromamba 2.3.3-0 by
   sha256; cuda-nvcc 12.9.86, cudart-dev 12.9.79, libcublas-dev 12.9.1.4, cuobjdump 12.9.82, nvdisasm 12.9.88,
   gxx 13.3.0, python 3.12.16, numpy 2.1.3, cmake 3.31.8, ninja 1.13.2). The pip cu12 nvcc wheels carry no `nvcc`
   and the cu13 ones need driver >= 580, so conda is the route that works on any driver >= 575;
   checked on forge (Debian 13, whose glibc 2.41 headers break CUDA 12.9 with the system g++, hence conda's g++);
3. `mma_run.py` (steps 1-6 with own kernels) under the common watchdog;
4. CUTLASS v4.8.1 (sha 2c85f49...): on sm_75..sm_90a `cutlass_profiler` restricted to the b1 kernels
   (`CUTLASS_LIBRARY_KERNELS`, gemm operations only), one small verified b1 GEMM then the rate; on sm_100a/103a the
   tcgen05 example GEMMs `70_blackwell_fp8_gemm` and `72a_blackwell_nvfp4_bf16_gemm` (rate + their own check);
   build bounded at 1,500 s;
5. one `results.json` (+ `cutlass/`, `log.txt`, `toolkit-packages.txt`). Step 7 (Keccak-f) is workload 2's:
   `runbook/tower256.sh` reports `keccak_f_per_s`; not duplicated.
`--shrink` = the T4 parameters exactly (`mma_run.py --shrink`).

CUTLASS build timing (compile-only, forge, same flags and conda toolkit): sm_75 b1 subset 1,124 s at -j4;
sm_90a b1 subset 320 s at -j12. Most of the time is CUTLASS's reference kernels for every type, not the b1
kernels. On a 16+ vCPU paid box expect about 5 min; on Kaggle's 4 slower cores it does not fit. Not run on a GPU
yet: the `cutlass_profiler --A=b1:row --B=b1:column --C=s32:column` invocation and the Blackwell example GEMMs.
The probe's own b1 kernels (BMMA, BGMMA) are the primary b1 measurement and need no CUTLASS.

## 6. What only a paid box answers, and what each answer decides

| SKU | measurement (where in results.json) | decides |
|---|---|---|
| H100 | `rates_sm80.wg_b1` vs `wg_s8` (BGMMA vs IGMMA) and `cutlass/profiler_b1.txt` (BMMA) | Tower256 on Hopper: b1 >= 8x INT8 means HBM-bound inner products (F3 5.3 ms class); near INT8 means unpack/SIMT (7.2-21.8 ms) |
| H100 | `wgmma.e4m3_group`, `e4m3_cint_jmax`, `e4m3_count` (QGMMA, native) | the FP8 m premise (`HoldsBelow m`); m < 12 refutes PTX's "higher than half"; F3 uses m = 14 |
| H100, B200, B300 | `ltprobe.e4m3_fast0/fast1` count and gap per cuBLAS algorithm | whether cuBLAS's FP8 path (fast accum on/off) keeps integer sums exact: the FP8-limb block length (72 at m = 14) |
| B200, B300 | `ltprobe.e2m1_fast0.count` (tcgen05 via cuBLASLt, unit block scales) | the unpublished tcgen05 f8f6f4 accumulator width; the FP4 promotion interval K_p |
| all | `i8ip`, `ltip` e4m3 vs `copy` | the model's HBM-floor claim (acceptance 1.5x, refutation 2x); FP8 limbs at 64 B/element vs INT8 at 32 |
| B300 | `peak.i8` vs `peak.e4m3`, `rates_sm80.s8` | INT8 at 1/30 of FP8 on sm_103a (F3's B300 column rests on it) |
| B200, B300 | `rates_sm80.b1and` (emulated) | how slow the emulated legacy b1 is (decision already made: no 1-bit MMA on Blackwell) |

## 7. Box, wall, cost

- **Ask for**: one B300 (or B200) GPU; optional second hour on one H100 SXM. One GPU suffices (no multi-GPU step).
  16+ vCPU (CUTLASS build), 64 GB RAM, 100 GB disk, Ubuntu 22.04/24.04, NVIDIA driver >= 575 (>= 580 preferred),
  outbound internet (conda-forge, GitHub). Root not needed.
- **Wall**: toolkit env 3-5 min (forge: about 3 min), probes about 5-10 min (T4: 70 s; paid sizes add the 8 GiB copy
  and 2^25 FP8), CUTLASS build bounded at 25 min (B200 examples / H100 profiler subset), runs 2-5 min. Expected
  35-45 min; hard wall 3,300 s inside the script.
- **Cost** [A, public on-demand list prices not re-checked]: H100 SXM about $2-3/h, B200 about $4-6/h, B300 about
  $6-9/h. One hour each: about $6-9 (B300) plus $2-3 (H100).

## 8. Verdict

Worth one paid hour on a Blackwell box and one on an H100, not more. Both FP8 accumulator widths (QGMMA on Hopper,
tcgen05 on Blackwell) and the Hopper `wgmma .b1` rate are unpublished, decide F3's format table and Tower256 on
Hopper, and are now one command away with every check bit-exact and dry-run. Not needed from paid hardware any more:
whether Blackwell has a 1-bit MMA (it has none: SASS), the INT8-limb exactness boundaries (bit-exact on T4, same PTX
semantics), and the HBM-bound classification of the INT8 inner product (holds on T4).
