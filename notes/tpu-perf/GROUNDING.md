# TPU performance discipline (initiative 18): grounding

2026-11-06. Lane: tpu-perf. Method revised by the root on ember's word: CPU-backend optimized HLO says nothing
about TPU and is dropped from the method.

## 0. Result first: the real TPU compiler runs on hbox with no TPU attached [MEASURED 2026-11-06]

**Deviceless AOT compilation against a TPU topology description works on hbox** (Linux x86_64, no TPU).
Setup: `~/lanes/tpu-perf/.venv` on hbox, `uv pip install "jax[tpu]"` -> jax/jaxlib 0.12.0.1, libtpu 0.0.50.1
(venv 1.2 GB). Probes: `tpuperf/aot_probe.py`, `tpuperf/aot_probe2.py` (this directory).

What happened, exactly:
- `jax.experimental.topologies.get_topology_desc(platform="tpu", topology_name=...)` returns devices for
  `v5e:1x1` ("TPU v5 lite"), `v6e:1x1` ("TPU v6 lite"), `v5p:2x2x1` ("TPU v5"), `v4:2x2x1` ("TPU v4").
  libtpu prints warnings (no `TPU_ACCELERATOR_TYPE`, no `TPU_WORKER_HOSTNAMES`, one `INVALID_ARGUMENT` log
  line from `libtpu_init_utils.cc`); none is fatal, and `jax.default_backend()` stays `cpu`.
- `jax.jit(f).lower(*ShapeDtypeStruct(..., sharding=SingleDeviceSharding(topo_dev))).compile()` succeeds and
  returns a real TPU executable's metadata: `as_text()` is the scheduled TPU HLO with TPU tiled layouts
  (`s8[1024,1024]{1,0:T(32,128)(4,1)}`, `s32[...]{1,0:T(8,128)}`, memory-space annotations `S(1)`),
  `cost_analysis()` (flops, bytes accessed per operand, and the compiler's own `optimal_seconds`), and
  `memory_analysis()` (argument/output/temp/generated-code sizes).
- `XLA_FLAGS="--xla_dump_to=DIR --xla_dump_hlo_as_text"` dumps `before_optimizations`, `after_optimizations`,
  buffer assignment, live ranges, the memory-usage report, `tpu_comp_env` and `after_codegen` per module.
- **Pallas kernels go through Mosaic at compile time**: a legal (256,1024)x(1024,256) int8 kernel compiles
  (73 KB code); a block shape not divisible by (8,128) is rejected at lowering; a whole-array 8192^2 block is
  rejected by the compiler with `RESOURCE_EXHAUSTED ... would exceed memory (size=134217728) ... space=vmem`
  (so the compiler's VMEM capacity for v5e is 128 MiB); a u64 multiply inside a Pallas kernel fails Mosaic
  compilation (the same multiply in plain XLA compiles: XLA emulates 64-bit, Mosaic does not).
- First finding from the real compiler: a plain `jnp.dot(s8, s8 -> s32)` at 1024^3 inserts two `copy` fusions
  that relayout each int8 operand from the default parameter tiling `T(32,128)(4,1)` to `T(8,128)(4,1)`;
  `optimal_seconds` = 16.6 us, against 5.45 us for 2^31 int8 ops at the published 394 TOPS. The Pallas
  version of the same matmul has no copies. To be explained before any tuning claim.

Where the static check ends: everything up to the compiled TPU executable (optimized HLO, layouts, fusions,
inserted copies/transposes/padding, buffer assignment, VMEM and HBM footprints, Mosaic legality of Pallas
kernels, the compiler's cost model) runs on hbox for free. Nothing is executed: no timing, no exactness of
the executed program, no profile of DMA/compute overlap. `optimal_seconds` is the compiler's model, never a
measurement. Those three come only from a TPU (Kaggle).

Consequences for the method:
1. Mac: correctness only (numpy reference, Pallas `interpret=True`) and op/byte counts from the
   pre-optimization StableHLO for the bound.
2. hbox (deviceless libtpu, `nice -n 15`, small memory): every static check, against v5e and v6e topologies.
3. Kaggle TPU v5e-8: measurement only (JAX profiler, %-of-bound). No compile-only Kaggle jobs are needed, so
   the ~20 TPU h/week quota (dated note; the UI is authoritative) goes entirely to profiles. Kaggle offers
   v5e-8 only (`TpuV5E8`); v6e is static-checked on hbox but not measured unless ember provides one.
   Queue and quota are not expected to bottleneck iteration at a few profile jobs per day; reassessed with
   numbers after the first profile.

dregg-forge was not tried: hbox suffices, and forge is shared with fn2's measurement box.

## 1. Method and tools (2026-11-06 evening)

- `tpuperf/counts.py`: op and byte counts from the pre-optimization StableHLO (Mac). MXU MACs per dtype;
  VPU element-ops (64-bit flagged); compulsory HBM bytes. `bound()` = max over units of work / peak
  (`hw.py`, tagged). The VPU peak is **not published** for v5e/v6e: the v5e value is an unverified
  placeholder until the Kaggle calibration measures it. v6e bounds omit the VPU and say so.
- `tpuperf/inspect_hlo.py`: reads the optimized TPU HLO. Flags copies, transposes and pads by location,
  non-MXU dot dtypes, MXU underfill, 64-bit types, while loops and custom calls. Sums `estimated_cycles`
  and scoped VMEM.
- `tpuperf/pallas_lint.py`: block shapes vs (8|16|32, 128) tiles, in-kernel dot dims vs the MXU edge,
  double-buffered VMEM vs the scoped limit, 64-bit values, grid steps.
- `tpuperf/static_check.py` and `run_static.sh` (one command from the Mac): every kernel and config on
  v5e and v6e. Results land in `results/static/`; the HLO stays on hbox under `~/lanes/tpu-perf/src/out-*`.
- Kernels (`tpuperf/kernels/`), each bit-exact against an independent reference on the Mac:
  `mxfp4_w4a8` (Pallas, interpret mode, vs int64 from the E2M1 codes), `rns_ntt61` (vs a Python-int radix-2
  negacyclic NTT, itself checked against the O(N^2) definition), `sumcheck_bb4_round` (vs Python-int
  BabyBear^4 fold and round sums).

## 2. What "the bound" means here

- **Per kernel, for its algorithm:** the best time a perfectly pipelined implementation of THIS algorithm
  could reach on the chip. That is the max over units of (work / peak). MXU work is padded to the
  128-granular K and output-lane dims (`mxu@pad`), since the hardware cannot do less. The unpadded value is
  kept so the padding gap can be named, e.g. K = 2880 caps gpt-oss matmuls at 97.8%. HBM work is the
  compulsory bytes (inputs read once, outputs written once). VPU work is the elementwise ops of the
  counted formulation at the measured int32 rate.
- **Algorithm choice is a separate, documented decision.** Examples: full vs lazy reduction in the NTT,
  per-k1 twiddle matrices (64 MiB, more HBM) vs a diagonal twiddle on the VPU, and prefolded 1-byte
  MXFP4 weights vs packed 0.53-byte weights decoded on the VPU. A kernel at 95% of a worse algorithm's
  bound is reported with the better algorithm's bound beside it.
- v6e: VMEM 128 MiB per the compiler, same as v5e. The VPU rate is unknown, so v6e bounds are lower bounds.
