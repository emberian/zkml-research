# hw-optimality: grounding (scholar lane under initiatives 14/17/18)

2026-11-06. Theory and prediction tools under the hardware lane's per-target table
(`notes/tensor-core-holography/ROTATION.md`, which owns "which tensor datapath is exact and fastest per chip").
This lane owns: what an optimal kernel looks like per architecture and workload shape (OPTIMAL.md), which
predictors can be trusted and how far (PREDICTORS.md), and the predicted optimum, the gap and the top changes per
workload (MAPPING.md). Tags: [READ] source read this session, [MEASURED] we ran it, [INFERRED] derived here,
[A] assumed (datasheet values from memory, consistent with `mma_counts.py` SKUS, not re-fetched).

## 1. Sources read this session

| source | what it settles for us |
|---|---|
| CUDA C++ Best Practices Guide 13.5, Table 5 (throughput of native arithmetic, per SM per clock, CC 7.5 to 12.x) [READ] | the SIMT rates under every integer kernel; see section 2 |
| PTX ISA 9.x (docs.nvidia.com, fetched 2026-11-06) [READ] | `tcgen05.mma .kind::i8` exists only on sm_100a / sm_110a (not sm_103a: B300 has no tensor INT8 path); `.kind::ti16` on sm_107f; wgmma e4m3/e5m2 accumulate "higher than half, lower than single"; integer MMA wraps unless `.satfinite`; sm_100a/103a static smem 228 KB per CTA |
| Luo et al., "Benchmarking and Dissecting the Nvidia Hopper GPU Architecture", arXiv 2402.13499 (H800 PCIe) [READ] | `mma.sync` on Hopper reaches only ~65% of peak (INT8 m16n8k32 978 of 1,513 TOPS; FP16 494 of 756); wgmma reaches >95% (INT8 m64n256k32 1,449 TOPS, SS and RS alike); wgmma throughput drops for N < 64 (N = 32: 477 vs 729 TFLOPS SS; N = 16: 287); random data under a 350 W cap loses 5-9% to clock |
| Jarmusch et al., "Dissecting the NVIDIA Blackwell Architecture with Microbenchmarks", arXiv 2507.10789 (GB203 vs GH100) [READ] | GH100 L2 hit ~273 cycles, GB203 ~358; GH100 smem 227 KB/SM configurable; L2 read bandwidth GH100 15.8 TB/s |
| "Microbenchmarking NVIDIA's Blackwell Architecture" (B200), arXiv 2512.02189 v1 and v2 [READ] | B200: 148 SMs, 8 GPCs, 4 L2 partitions, 8 HBM3e stacks, 192 GB; TMEM 256 KB/SM; **STREAM Triad 4.13-4.14 TB/s (52%) at 4-16 GB, 7.42-7.48 TB/s (93%) at 64-128 GB in v1** (v2 drops the large rows); H200 2.88-2.91 (60%) and 4.35-4.38 (91%). Its tensor tables list shapes PTX does not define (Codex): qualified |
| JAX scaling book, TPU chapter (jax-ml.github.io/scaling-book/tpus) [READ] | v5e: 8.2e11 B/s HBM, 1.97e14 bf16, 3.94e14 int8; v6e: 1.6e12, 9.2e14, 1.84e15; VPU is (8, 128) lanes x 4 ALUs per cycle (stated for TPU7x; prior generations "fp32-only VPU ops", v6e adds packed bf16); VMEM-to-VREG 3 loads + 1 store per cycle |
| hashcat 6.2.x benchmark logs (Chick3nman gists; hashcat forum; onlinehashcrack) [READ] | Keccak-256 (mode 17800: 23 full rounds + a pruned last round per candidate, ~4-5% less than a full Keccak-f): T4 689-729 MH/s, A100 PCIe 2,138, H100 PCIe 2,795, RTX 4090 5,059; SHA2-256 H100 SXM 16,552 vs PCIe 12,200 (SXM/PCIe 1.36). An external, cross-architecture calibration set for SIMT integer throughput |
| our own runs (`notes/accelerator-readiness/runs/`, `MMA.md`, `BFV.md`, `TOWER256.md`) [MEASURED] | T4: copy 238-242 GB/s, read 277; lop3 3.0-3.1e12/s; mma.sync u8 5.0-6.3e13 MAC/s; Keccak-f 3.15e8 (rate probe) to 6.9e8 (Merkle); NTT N = 8192 1.77 us sustained; INT8 BabyBear^8 inner product 1.2-1.6x copy |
| Mazumder et al., Ozaki II on INT8/FP8/FP4, arXiv 2609.37693 [READ sections IV-C, VIII-D]; Ozaki II, arXiv 2504.08009 [READ abstract]; base-13 E2M1 Ozaki, arXiv 2608.06812 [READ abstract] | B200 tcgen05 E4M3 accumulators driven to 2^24 at K = 2^14 via CUTLASS, bitwise exact (not B300, not cuBLASLt, not E2M1); Hopper/Ada FP8 accumulate with ~13 fractional bits (their refs 50, 51); 4-bit integer MMA on Blackwell issues as two 8-bit MMAs |
| readiness lane TOWER256.md section 8 [READ] | bit-sliced Tower256 multiply on T4: 52,700 op-eq, loses to tables (12,000-17,400) |
| hardware lane: F3-MODEL.md, ROTATION.md, `mma_counts.py` [READ] | the tensor datapath per target, exactness blocks, workload remaps |
| TPU lane: `notes/tpu-perf/GROUNDING.md` [READ] | deviceless real-libtpu compile on hbox, `cost_analysis()["optimal_seconds"]`, VMEM 128 MiB per the compiler |

## 2. The SIMT rates (Table 5, results per clock per SM) and three consequences

| operation | 7.5 | 8.0 | 8.6/8.9 | 9.0 | 10.0 | 10.3 | 12.x |
|---|---:|---:|---:|---:|---:|---:|---:|
| 32-bit and/or/xor (LOP3), shift (SHF) | 64 | 64 | 64 | 64 | 64 | 64 | 64 |
| 32-bit add | 128 | 128 | 128 | 128 | 128 | 128 | 128 |
| 3-operand / extended add (IADD3, .X) | 64 | 64 | 64 | 64 | 64 | 64 | 64 |
| 32-bit multiply, mad.lo (IMAD) | 64 | 64 | 64 | 64 | 64 | 64 | 64 |
| extended-precision multiply (mad.hi, .wide, madc) | 32 | 32 | 32 | 32 | 32 | 32 | 32 |
| fp32 FMA | 64 | 64 | 128 | 128 | 128 | 128 | 128 |
| fp64 FMA | 2 | 32 | 2 | 64 | 64 | **2** | 2 |
| popc, clz | 16 | 16 | 16 | 16 | 16 | 16 | 16 |
| cvt f32 -> s32 | 16 | 16 | 16 | 16 | 16 | **2** | **2** |
| cvt s32 -> f32 | 16 | 16 | 64 | 64 | 64 | 64 | 64 |

1. **Integer SIMT does not grow per SM.** LOP3, SHF, IMAD are 64 lanes per SM per clock on every generation from
   Turing to Blackwell Ultra. Keccak and 64-bit modular arithmetic scale only with SMs x clock. The `simt` constant
   of 128 lanes/SM/clk for B200/B300 in `mma_counts.py` holds for IADD and FP32 only; for LOP3/SHF/IMAD it is 2x
   optimistic for those [INFERRED from Table 5]. This is a statement about PEAK rates; kernel efficiency differs.
2. **B300 (CC 10.3) converts float to int at 2 per SM per clock** (footnote 11: "16 for float->32-bit integer type
   (SM <= 10.0), 2 ... (SM > 10.0)"), and runs FP64 at 2. Any FP-tensor promotion that uses `cvt.rni.s32.f32` is 64x
   slower there than an IADD (128). The fix is the classic magic-number conversion (FADD 1.5 * 2^23, reinterpret the bits;
   exact for |x| < 2^22, 128/clk) or the bias read in ROTATION.md section 2(b) [INFERRED].
3. **The extended-precision multiply is half rate everywhere.** A 64x64-bit Shoup or Montgomery product is bound by
   IMAD.WIDE / IMAD.X on the FMA pipe, not by issue (sassbound, PREDICTORS.md).

## 3. Per-target constants used by the models

[A] datasheet unless tagged. "eff" columns are what a well-written kernel sustains, with the source.

| target | SMs | clock GHz (boost; sustained) | HBM TB/s (peak; eff) | L2 MB | smem KB/SM | dense tensor MAC/clk/SM (f16 / s8 / fp8 / fp4) |
|---|---:|---|---|---:|---:|---|
| T4 (sm_75) | 40 | 1.59; **0.6-1.3 measured** (70 W cap; idle-ramp in short windows) | 0.32; 0.24 [MEASURED copy] | 4 | 64 | 512 / 1024 / - / - (b1 8192, MEASURED 7-8x u8) |
| A100 SXM (sm_80) | 108 | 1.41 | 2.04; ~1.7 [A] | 40 | 164 | 1024 / 2048 / - / - (b1 16384) |
| H100 SXM (sm_90a) | 132 | 1.98; ~1.75 under tensor load [A] | 3.35; ~2.9 [A] | 50 | 228 | 2048 / 4096 / 4096 / - (wgmma; mma.sync ~0.65x [READ]) |
| H200 (sm_90a) | 132 | as H100 | 4.8; ~4.1 [A] | 50 | 228 | as H100 |
| B200 (sm_100a) | 148 [READ] | ~1.9 [A] | 8.0; **4.1-7.5 STREAM by array size [READ]**, 6.0 assumed by F3 | ~126 [A] | 228 + TMEM 256 [READ] | 4096 / 8192 / 8192 / 16384 |
| B300 (sm_103a) | 160 [A] | ~1.9 [A] | 8.0 (Codex in ROTATION: 7.7); unmeasured | [A] | 228 + TMEM 256 | 4096 / ~256 (no `kind::i8`) / 8192 / ~24576 |
| TPU v5e | 1 TC, 4 MXU 128x128 | 1.5 [A] | 0.82 [READ] | VMEM 128 MiB | - | int8 3.94e14 OPS, bf16 1.97e14 [READ] |
| TPU v6e | 1 TC, 2 MXU 256x256 [A] | [A] | 1.6 [READ] | VMEM 128 MiB [compiler] | - | int8 1.84e15, bf16 9.2e14 [READ] |

## 4. What this lane does not redo

- The exactness of each tensor datapath and the per-target exact table: ROTATION.md (hardware lane). This lane uses
  its blocks and flags three inputs it contradicts (MAPPING.md section 0).
- Kernel ports and bit-exact checks: readiness lane (initiative 17). This lane predicts and inspects their kernels.
- TPU static analysis tooling: TPU lane (initiative 18). This lane evaluates its predictor, not rebuilds it.

## 5. Machines and toolchain used

- dregg-forge `/srv/lanes/hw-opt/`: pinned conda-forge CUDA 12.9 (cuda-nvcc 12.9.86, cuobjdump 12.9.82, nvdisasm
  12.9.88, gxx 13.3.0 as `-ccbin`, because Debian 13's glibc 2.41 headers break nvcc 12.9 with the system g++).
  `nice -n 15`, `systemd-run --scope -p MemoryMax=12G`, PID files. No GPU anywhere; nothing rented.
- Helper lanes: cycle-level simulators (`sim/`), analytical and learned models (`models/`).
