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
