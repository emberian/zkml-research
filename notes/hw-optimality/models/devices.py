"""Device parameters fed to every tool, one place, each tagged.
[DS] vendor datasheet number (dense, no sparsity), [M] measured by us (MMA.md), [F3] mma_counts.py SKUS,
[SB] scaling-book / tpuperf hw.py, [A] assumed, [INF] inferred from the others.
Rates in MAC/s (1 MAC = 2 ops). The systolic-array view (LLMCompass) is chosen so arrays*256*mac_per_cycle*SMs*clock
reproduces the dense peak; LLMCompass only ever uses that product, so the split is cosmetic."""

DEV = {
  "T4":   dict(sm=40,  clk=1.59e9, fp16=32.5e12, int8=65e12, fp8=None, hbm=320e9, l2=4 << 20, l2_bpc=1024, smem_kb=64,
               src="[DS] 65 TF fp16 /130 TOPS int8, 320 GB/s; clock [M] clocks.max.sm 1590 MHz; L2 4 MB [DS]; L2 B/clk [A]",
               measured=dict(int8_mma_sync=6.28e13, cublas_int8=2.20e13, cublas_f16=1.58e13, copy=242e9, read=277e9)),
  "A100": dict(sm=108, clk=1.41e9, fp16=156e12, int8=312e12, fp8=None, hbm=2.039e12, l2=40 << 20, l2_bpc=5120, smem_kb=192,
               src="[DS] A100 SXM 80GB; LLMCompass's own GA100 numbers"),
  "H100": dict(sm=132, clk=1.83e9, fp16=494.7e12, int8=989.5e12, fp8=989.5e12, hbm=3.35e12, l2=50 << 20, l2_bpc=5120, smem_kb=228,
               src="[DS] H100 SXM dense 989 TF fp16, 1979 TOPS int8 = fp8 [F3]; L2 B/clk [A]; FP8 only via wgmma (no mma.sync FP8 on sm_90a)"),
  "B200": dict(sm=148, clk=1.856e9, fp16=1.125e15, int8=2.25e15, fp8=2.25e15, hbm=8.0e12, l2=126 << 20, l2_bpc=8192, smem_kb=228,
               src="[F3] int8 = fp8 = 4.5 P dense ops; 8 TB/s; clock [INF] from the peak; L2 size and B/clk [A]; no 1-bit MMA"),
  "B300": dict(sm=160, clk=1.717e9, fp16=1.125e15, int8=0.075e15, fp8=2.25e15, hbm=8.0e12, l2=126 << 20, l2_bpc=8192, smem_kb=228,
               src="[F3] fp8 4.5 P dense ops, INT8 = fp8/30 (0.15 P ops); 160 SM [F3,A]; 8 TB/s; clock [INF]"),
  "v5e":  dict(mxu=4, mxu_dim=128, clk=1.5e9, bf16=98.5e12, int8=197e12, hbm=8.2e11, vmem=128 << 20,
               src="[SB] 197 TF bf16, 394 TOPS int8, 820 GB/s, 4x128^2 MXU; VMEM 128 MiB [compiler]; clock [INF]"),
  "v6e":  dict(mxu=4, mxu_dim=256, clk=1.75e9, bf16=459e12, int8=920e12, hbm=1.6e12, vmem=128 << 20,
               src="[SB] 918 TF bf16, 1.84 POPS int8, 1.6 TB/s; MXU 256^2; count 4 at 1.75 GHz [INF] (sb says 2 MXUs: then clock 3.5 GHz, implausible; only the product matters)"),
}
