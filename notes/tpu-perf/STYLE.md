# Writing TPU code that hits its bound (this project's rules, from the real compiler and, later, Kaggle)

Every rule cites what it rests on: [READ] published, [CC] read off the real TPU compiler (deviceless, hbox),
[MEASURED] Kaggle v5e profile. Rules without a measurement yet are marked provisional.

## Page 1: what the compiler did to a plain int8 matmul, and how to read its numbers

`jnp.dot(s8[1024,1024], s8[1024,1024], preferred_element_type=int32)` on v5e [CC, `tpuperf/aot_probe.py`]:

1. **The two "copies" are relayouts inside the matmul fusion, not HBM passes.** An int8 parameter arrives in
   the default HBM tiling `T(32,128)(4,1)`: 32x128 bytes per tile, four rows packed into each 32-bit word, so
   one tile is a full (8,128) vreg. The convolution emitter feeds the MXU from `T(8,128)(4,1)`. XLA puts that
   relayout (`copy_fusion`) INSIDE the `kOutput` convolution fusion, applied to each VMEM window as it streams.
   bf16 inputs (`T(8,128)(2,1)`) get no copy. Separately, operand `a` is `copy-start`ed into memory space
   `S(1)` (VMEM) as a cross-program prefetch. Neither costs an extra HBM pass. The cost of the in-VMEM
   relayout, if any, is a vector-unit cost that only a profile shows. The same matmul as a Pallas kernel has no
   copy in its HLO, because Mosaic owns the layout.
   *Rule:* tell a relayout inside an MXU fusion (on-the-fly) from one in a standalone fusion or at ENTRY
   (an HBM round trip). `inspect_hlo.py` classifies every copy, transpose and pad by location.
2. **5.45 us was the wrong bound. It is HBM, 7.7 us.** 2^31 int8 ops / 394 TOPS = 5.45 us, but the program
   must also read 2 MiB and write a 4 MiB int32 result: 6 MiB / 820 GB/s = 7.7 us. The arithmetic intensity
   is 341 ops/byte, under v5e's ridge of 394e12/820e9 = 480 ops/byte. *Rule:* the int32 output of an int8
   matmul is 4 bytes per element. An int8 GEMM is HBM-bound until M, N, K are all well above ~1500, unless the
   epilogue narrows the output (requantize or reduce before you store).
3. **`optimal_seconds` from `cost_analysis()` is not a bound.** It does not follow bytes (an s8-output
   variant moves 30% fewer bytes and gets the same 16.6 us). It works out to flops at 1.29e14 / 1.74e14 /
   1.85e14 ops/s for 1024^3 / 4096^3 / 8192^3, i.e. close to the **bf16** peak with a size-dependent
   efficiency. Its `bytes accessed` counts re-reads (operand `a` twice: prefetch plus use; output 1.75x).
4. **The per-fusion `estimated_cycles` in `backend_config` is the compiler's real model, and it uses the int8
   rate.** 8192^3: 4.33 M cycles = 2.89 ms at the inferred 1.5 GHz, i.e. 97% of the 394 TOPS compute bound
   (2.79 ms). At 1024^3, 20,412 cycles = 13.6 us is about its own byte count (10.5 MB) at 820 GB/s. Mosaic
   (Pallas) kernels carry no estimate. `static_check.py` sums it when it covers the whole program.
   Provisional until the Kaggle calibration runs the same three shapes.

## Rules so far, from the three workload kernels [CC unless marked]

- **Never let a size-4 or size-8 axis be minor.** Byte limbs, extension-field coordinates and RNS limbs go on
  MAJOR axes (planar / structure-of-arrays). The 128-lane axis must be a long data axis. The first NTT
  (limbs minor) made XLA relayout the 64 MiB twiddle tensor through VMEM and fail to compile
  (`CompileTimeScopedVmemOom`, 16.01M > 16.00M). Planar, it compiles.
- **Long VPU chains do not stay on chip in XLA.** A 61-bit limb reduction (~150 int32 ops per element) gets
  split into many fusions, and the boolean masks between them go through HBM: NTT `pred[64,1024,128]` copies,
  706 MB of temporaries, a compiler estimate of 12.6 ms against a 0.54 ms bound. The sumcheck round does the
  same (2.1 GB of temporaries, 14 while loops, 65 ms against 1.8 ms). *Rule:* matmul plus a long integer
  epilogue is one Pallas kernel that writes only the reduced result.
- **No 64-bit integer anywhere in a TPU kernel.** Mosaic rejects a u64 multiply. XLA emulates it. Use byte
  or 16-bit limbs in int32 with arithmetic-shift carries, and a float32 quotient estimate (error <= 1) plus
  two conditional corrections for the reduction.
- **Fill the MXU edge.** A 16x16 limb matrix (BabyBear^4 multiply-by-r) uses 1/64 of a 128x128 MXU. Put 8
  copies on the block diagonal and pack 8 column groups. 2880 = 22.5 x 128 (gpt-oss hidden size) caps an
  int8 GEMM at 97.8% of MXU peak. Pad weights to 23 x 128 offline, or accept the 2.2% and name it.
- **Exactness by construction:** offset-128 bytes and balanced-digit constant matrices keep every int8
  product within 2^14, so an int32 accumulator is exact for K <= 2^17. Chunk longer contractions.
- **BabyBear residues are 31-bit, so x + y overflows int32 (2P > 2^31).** Write x - (P - y) and add P back
  when the result is negative. The first Pallas fold got 44% of its outputs wrong this way. In XLA, u32
  hid the bug.
- **The four-step transpose is a strided VMEM load, not an HBM pass.** NTT stage 2 reads `x[a, :, kk, :]`,
  which is one sublane of each (b, k1) tile. With the layouts chosen this way the two-kernel NTT has zero
  HBM copies [CC]. The first planar version reshaped between kernels, and the compiler inserted two
  64 MiB relayout copies, estimated at 0.62 and 0.53 ms against a 0.54 ms bound.
- **Pack small matrices onto the MXU through the row axis of the storage layout.** Storing a table as
  [coords, ..., rows, 1024 lanes] makes 8 consecutive rows the 8 block-diagonal groups, so packing is a
  merge of major dims (free) and not a lane shuffle.

## Measured on a spot Cloud TPU v5e (`v5litepod-1`, us-east1-c, jax 0.12.0.1, session tpuperf-s3) [MEASURED]

| rate | measured | published | % |
|---|---|---|---|
| HBM read (`sum` over 1 GiB int32) | 752 GB/s | 820 | 92 |
| HBM copy (read + write, `x + 1`) | 656 GB/s | 820 | 80 |
| XLA int8 matmul 8192^3 | 384 TOPS | 394 | 97.4 |
| XLA int8 matmul 4096^3 | 376 TOPS | 394 | 95.3 |
| XLA int8 matmul 1024^3 | 46 TOPS (46 us) | 394 | HBM and launch bound; the bound is 7.7 us |
| XLA bf16 matmul 8192^3 | 182 TFLOPS | 197 | 92.6 |
| Pallas int8 8192^3, (512, 512, 2048) tiles | 300 TOPS | 394 | 76: XLA's emitter beats a naive Pallas tiling |
| VPU int32, chain of mul, add, shift, xor | 2.65e12 ops/s | unpublished | |
| VPU int32, chain of and, shift, sub, compare, add, select | 4.11e12 ops/s | unpublished | |
| Pallas grid step | 0.20 us | | |

- **A dimension that is not a multiple of 128 flips XLA's default parameter layout.** `s8[2048, 2880]`
  is stored column-major (`{0,1}`), because 2048 tiles cleanly and 2880 does not. Every Pallas consumer
  then pays a relayout copy: 14 us of the MXFP4 kernel's 301 us. *Rule:* pad such dims to a multiple of
  128 at the data's source, not inside the kernel.
- **A tiny trailing dim makes XLA move it.** The packed MXFP4 shifts `s8[90, 2816, 2]` got layout
  `{1,0,2}`, and the relayout cost 158 us, more than the kernel itself. Never end an array in a 2.
- **Cross-program prefetch hides weight reads between back-to-back calls.** XLA prefetches a parameter
  into VMEM (`S(1)`) during the previous execution. Freivalds read W this way and measured 79.5 us
  against an 85 us bound that charges W's bytes. Benchmark with the operand pattern of the real workload.
- **E2M1 decode on the v5e VPU costs about 17 int32 ops per weight.** At the measured VPU rate that is
  slower than reading a prefolded int8 weight from HBM (1 B per weight). The packed-nibble MXFP4 kernel
  measured 312 us against the prefolded 57 us, so prefolded int8 is the v5e format. Packed only pays on
  a part with a narrow-int VPU or MXU (MXFP4-native hardware).
