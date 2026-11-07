hw-opt-sim: GPGPU-Sim / Accel-Sim on a CPU-only box, run on our kernels (lane hw-opt-sim, 2026-11-06)
================================================================================================

Where it lives (bb2, user build): ~/lanes/hw-opt-sim/
  accel-sim-framework/                 accel-sim dev @ 7ba54ded (v2.0.1); gpu-simulator/gpgpu-sim = gpgpu-sim dev @ 4195dd4f
  cuda128/                             micromamba conda-forge env: nvcc 12.8.93 + cudart/cuobjdump/bison/flex/zlib/GL/python
  work/{t4,a100,h100}/                 configs (t4 = SM75_RTX2060 + t4_vs_rtx2060.diff; a100/h100 = tested-cfgs as shipped)
  work/runs/<name>/out.log             full simulator logs; filtered copies in logs/ here

Rebuild from scratch: setup_bb2.sh (clones, env, lane patch, both builds).

Files here
  setup_bb2.sh, build-gpgpusim.sh, build-accelsim.sh   environment and builds (swarm-build, SWARM_MEM_MAX=16G)
  gpgpusim-lane.patch    five GPGPU-Sim fixes without which our kernels crash or mis-simulate:
                           1. wmma operand decode dereferenced the f16 bit pattern as a pointer (regression 68a91076, 2023-06):
                              every PTX-mode wmma segfaulted.
                           2. mul.hi.u64 asserted; mul.hi.s64 silently returned the LOW half.  (__umul64hi: every NTT.)
                           3. dynamic shared memory (<<<g, b, smem>>>) was stored and never read: a 64 KiB dynamic-smem
                              kernel ran 4 CTAs/SM on a 64 KiB SM. Now counted in occupancy and the L1 carve-out.
                           4. bfi.b64 ran on the low 32 bits only (32-bit shifts on .u32).
                           5. integer immediates were lexed with atoi / %x into an int: every 64-bit literal
                              (e.g. Keccak's 0x9e3779b97f4a7c15, 0x80ull << 56 folded) was silently truncated.
                              Keccak digests were 100% wrong before 4+5, 0 wrong after.
  t4_vs_rtx2060.diff     T4 config: 40 SMs, 1590 MHz core/icnt/L2, 16 x 16-bit GDDR6 channels at 2500 MHz command clock
                         (x4 data = 10 Gbps -> 320 GB/s), 4 MiB L2 (falls out of 16 channels x 2 subpartitions), 64 KiB
                         smem per block (opt-in). DRAM timings left in RTX 2060 cycles (slightly pessimistic ns).
                         Trace mode: SM75_RTX2060/trace.config as shipped.
  simrun.sh NAME CFG CMD...     PTX-mode run (LD_LIBRARY_PATH -> GPGPU-Sim libcudart)
  tracerun.sh NAME CFG TRACE    Accel-Sim trace-mode run
  micro_sim.cu           copy (uint4 kernel, proxy for cudaMemcpy D2D) + gemm_probe.cu k_read, xor3 SIMT rate, wmma f16 rate
  lop3_only.cu           one inline lop3: records the PTX parser rejecting it
  ntt_host.cu, gen_ntt.py   standalone fwdBr<Shoup,G=3> one-pass N=8192 L=3 256 thr from accel_rns_ntt.cu (copied
                         verbatim on bb2), input/tables/expected words from accel_rns_ref.py; every output word checked
  keccak_sim.cu          Keccak section of tower256_fri.cu (minidregg lane/accel-tower256-gpu @367f9370) + host check
  gen_trace.py           synthetic SASS .traceg (no NVBit): U=8 independent IMMA/BMMA/HMMA/LOP3/GMMA chains per warp,
                         i.e. probe_sm75.cu k_rate in SASS, for trace-mode issue-rate predictions
  logs/                  filtered simulator outputs (thread-block and shader-bind lines dropped)

Apps are built with:  nvcc -O2 -arch=sm_75 -cudart shared -ccbin x86_64-conda-linux-gnu-g++ -Xlinker --enable-new-dtags
(conda's nvcc writes an RPATH to its own libcudart; --enable-new-dtags makes it a RUNPATH so GPGPU-Sim's wins.)
Seconds = gpu_sim_cycle / core clock. Multi-wave runs are differenced (rows 80 minus rows 40) to drop launch and tail.

Results, 2026-11-06 (T4 measured = notes/accelerator-readiness MMA.md, BFV.md, TOWER256.md; sim = this dir)
-----------------------------------------------------------------------------------------------------------
Mode P = GPGPU-Sim PTX mode (execution-driven), T = Accel-Sim trace mode on a synthetic SASS trace (gen_trace.py).
"pred @1.59" = simulator cycles converted at the T4 boost clock in the config. T4 under its 70 W cap ran 0.6-1.6 GHz.

T4 (config t4)                          pred                       measured T4            pred/meas
copy D2D r+w, 64 MiB uint4 kernel  P    289 GB/s (16 MiB: 310*)    237-242 GB/s           1.20-1.22
streaming read k_read, 64 MiB      P    298 GB/s (16 MiB: 256*)    277 GB/s               1.08
lop3 rate                          T    57.7 LOP3/SM/clk = 3.67e12 3.0-3.1e12/s           1.18-1.22 at 1.59 GHz; 0.90/clk vs 64
  (PTX has no lop3; xor3 in C)     P    56.1 xor3/SM/clk = 3.57e12 (2 PTX xor each, issued 112/SM/clk: >64 INT lanes)
mma u8 m8n8k16                     T    235 MAC/SM/clk = 1.50e13   4.98e13-6.28e13         0.24-0.30
u4/u8                              T    2.00                        1.89-1.98             ok
b1 xor/u8                          T    8.00                        7.05-7.94             ok (1.01-1.13)
f16 HMMA/u8                        T    1.00                        0.48-0.52             2x wrong
  every Turing MMA = one unit, one II (16 cycles, the GeForce RTX 2060's half-rate f32-accumulate HMMA)
mma.sync any shape                 P    PTX parse error (no mma.sync / ldmatrix / cp.async / lop3 in the lexer)
wmma f16 m16n16k16 (only TC path)  P    163 MAC/SM/clk = 1.04e13   f16 HMMA ~2.5-3.1e13    0.33-0.42 (after patch 1)
NTT N=8192 L=3 Shoup 1-pass r8 256 P    2962 cyc/NTT = 1.86 us     1.77 us at 1.2-1.4 GHz  1.05 wall; 1.20-1.39 slower/clk
  (all 655,360 words = accel_rns_ref after patch 2; without patch 3: 1573 cyc/NTT, occupancy 4x too high)
Keccak-f dependent chain           P    1.25e9/s (51 cyc/SM)       3.15-3.18e8/s           3.9-4.0 (optimistic)
Keccak merkle_leaves 61,440        P    7.31e8/s                    4.35-6.9e8/s (Merkle)  1.06-1.68; ordering vs chain reversed
  (every digest word correct only after patches 4-5)
* 16 MiB runs: the 4 MiB L2 holds a quarter of the read set; use the 64 MiB numbers.

H100 (tested-cfgs SM90_H100, trace mode, synthetic)  per SM per clock      datasheet (dense)
HGMMA 64x256x16 f32                                   2010 MAC               2048    (= the N->latency table)
IGMMA 64x256x32 s8                                    4020 MAC               4096
mma.sync IMMA.16832 / HMMA.16816                      2539 / 1270 MAC        (no measurement)

A100 (tested-cfgs SM80_A100, PTX mode, 1410 MHz): NTT N=8192 L=3 one-pass r8 256 thr, 432 rows (2 waves at 2 CTA/SM):
  221,575 cycles = 157 us = 0.364 us/NTT incl. launch and tail; all 3,538,944 words correct. No measurement to compare.
H100 (tested-cfgs SM90_H100, PTX mode, 1980 MHz): copy kernel 128 MiB r+w: 125,193 cycles = 63 us = 4.25 TB/s, ABOVE the
  3.35 TB/s HBM3 datasheet: the H100 PTX-mode memory model is not credible for bandwidth (L2 50 MB, simple_dram_model).
Still running when the lane closed (bb2, PID files = process-group leaders, logs in work/runs/<name>/out.log):
  h100-ntt792 (runs/h100-ntt792.pid), a100-copy128m (runs/a100-copy128m.pid), h100-copy128m read kernel.
  Harvest: grep -E "kernel_name|gpu_sim_cycle|^\{" ~/lanes/hw-opt-sim/work/runs/<name>/out.log ; stop: kill -- -$(cat <pid>)

What these simulators can and cannot do for us
  Configs shipped: SM2 GTX480, SM3 Kepler Titan, SM6 TitanX, SM7 GV100/QV100/TitanV, SM75 RTX2060(+_S), SM80 A100,
  SM86 RTX3070, SM90 H100/H200. No T4, no Blackwell (B200/B300 "incoming" per the v2.0.0 notes; branch
  b300-hw-run-fixes is hardware-stat collection only; no tcgen05/UTCMMA/TMEM opcode anywhere in ISA_Def).
  PTX mode: tensor = wmma f16 only (m16n16k16, m32n8k16, m8n32k16); no mma.sync, ldmatrix, cp.async, lop3, wgmma, mbarrier,
  cp.bulk. Every PTX op is one issue at a per-class latency: 64-bit int ops (mul.hi.u64, xor.b64, shf pairs) cost one
  instruction, where SASS needs 2-5; ptxas fusions (LOP3, IMAD.WIDE) are invisible.
  Trace mode: needs NVBit on a real GPU (SASS is captured at run time). No GPU here, so no traces of our kernels; only
  synthetic SASS streams (gen_trace.py) for issue-rate questions. Hopper: HGMMA/IGMMA/QGMMA latency = f(N) table only
  (no BGMMA: unknown opcode asserts), TMA/mbarrier/cluster modelled. Turing/Ampere: HMMA/IMMA/BMMA share one unit, one II.
  Calibration that would fix it, all on free Kaggle T4 (NVBit runs there): trace our NTT, Keccak, copy and probe_sm75
  rate kernels with util/tracer_nvbit, replay on bb2 with the t4 config; set the tensor II per measured rate (needs a
  per-opcode II: one code change in trace_driven.cc). For H100/B200 there is nothing to calibrate against yet.
