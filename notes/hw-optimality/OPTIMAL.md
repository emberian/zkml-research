# What an optimal kernel looks like, per architecture and per workload shape

2026-11-06, hw-optimality lane. Sources and constants: GROUNDING.md. Per-target exact tensor datapaths:
`notes/tensor-core-holography/ROTATION.md` (used here, not redone). Numbers: `predict.py` (bounds), `sassbound/`
(SASS instruction counts). Codex (gpt-6-astra) attacked this file once: 19 findings, all applied. The ones that
changed a verdict: the 718-op bit-sliced multiply is withdrawn (measured 52,700, TOWER256.md 8); 31-bit Harvey primes
are 30-bit (7 for 183 bits); B200 m = 24 is E4M3/CUTLASS only; sumcheck fusion must respect Fiat-Shamir; Keccak's floor
is 4,320, not nvcc's 4,656; FP16 activations do not enter MX kinds. Tags: [READ] [MEASURED] [SASS] (counted on nvcc 12.9 SASS for that target) [INFERRED] [A].

## 0. The bound, and three rules that decide most of our kernels

- **The bound for an algorithm** is max over units of (work / sustained rate): HBM bytes, tensor MACs, and the SIMT
  pipes (ALU: LOP3/SHF/IADD3; FMA: IMAD, FFMA; XU: popc/cvt/MUFU; LSU), plus the issue limit of one warp-instruction
  per sub-partition per clock (4 per SM). A kernel at the bound of a worse algorithm is reported against the better
  algorithm's bound too. Latency and occupancy do not enter the bound; they decide how close a kernel gets.
- **Rule 1: bytes first.** Every prime-field primitive we have (inner products, folds, sumcheck rounds, Freivalds)
  is HBM-bound on every target with a tensor path [ROTATION 2(a), MEASURED on T4: 1.2-1.6x copy]. The tensor format
  is not the lever; bytes per element and passes over memory are.
- **Rule 2: peak integer SIMT is flat per SM.** LOP3, SHF, IMAD are 64 lanes/SM/clk from Turing to Blackwell Ultra; the
  extended-precision multiply is 32 [READ Table 5; the SASS mapping of IMAD.WIDE/.X to that row is A]. So the PEAK of
  Keccak and 64-bit modular arithmetic grows only with SMs x clock: T4 -> B300 is 6.5x, not the 20-100x of the
  tensor rates. Efficiency (occupancy, latency, instruction mix) is a separate factor per kernel.
- **Rule 3: an exactness block is a promotion schedule.** An accumulator that is exact below 2^m holds K products of
  size P exactly while K*P < 2^m (ROTATION, Lean `hw_exact`). Each promotion costs SIMT work per accumulator, so m
  sets the SIMT/tensor balance. On B300, float -> int conversion runs at 2/SM/clk [READ Table 5, CC 10.3; 64x below
  IADD's 128]: promote with the magic-number add (FADD 1.5*2^23, reinterpret; exact for |x| < 2^22) or the bias read.

## 1. Per architecture

### Turing T4 (sm_75)
- **Units.** `mma.sync` only: m8n8k16 u8/s8 (IMMA), m8n8k32 u4, m8n8k128 b1 **xor.popc only** (BMMA), m16n8k8 f16.
  Dense per SM per clock: 512 f16, 1,024 s8, 2,048 s4, 8,192 b1 MACs [b1 MEASURED 7-8x u8]. No FP8, no cp.async, no TMA.
- **Memory plan.** 64 KB smem/L1 per SM, 4 MB L2, 320 GB/s GDDR6 (242 measured copy). Registers are the main
  operand store: ldmatrix exists (sm_75), but with 64 KB smem a one-pass NTT of 8,192 words (64 KB) leaves one block
  of 8 warps per SM.
- **Clock is the dominant uncertainty.** 70 W cap; LOP3 measured at 3.0-3.1e12/s (1.19 GHz effective, 0.75 of
  boost). The same Keccak permutation reads 3.15e8/s (rate probe, 8 ms windows) and 6.9e8/s (Merkle build); if both
  ran at the SASS bound they imply 0.58 and 1.26 GHz [INFERRED: assumes efficiency 1; no clock was recorded]. Every
  T4 rate must carry a same-window clock reference (MAPPING.md section 5).
- **Pitfalls.** cuBLAS INT8 reaches only 0.35 of `mma.sync` peak on T4 [MEASURED 8192^3]; element-major INT8 layout
  (`NT`, lda 32) is unsupported, use K-contiguous limb planes [MEASURED]; f16 HMMA is half the u8 rate.

### Ampere A100 (sm_80)
- **Units.** `mma.sync` m16n8k32 s8, m16n8k64 s4, m16n8k256 b1 **and.popc and xor.popc** (both native), m16n8k16
  f16/bf16, m8n8k4 f64 (DMMA 19.5 TF), TF32. Per SM per clock: 1,024 f16, 2,048 s8, 4,096 s4, 16,384 b1.
  Measured by others: `mma.sync` reaches >95% of peak on A100 [READ Luo et al.].
- **Memory plan.** `cp.async` (LDGSTS) global -> smem without registers, multi-stage pipelines (CUTLASS sm80
  mainloops); 164 KB smem/SM; 40 MB L2 with residency control; 2.0 TB/s HBM2e.
- **Best exact paths.** b1 is native and 8x INT8: the GF(2) inner product needs no unpack and no parity trick
  beyond and.popc. FP64 DMMA holds 26-bit integer products exactly (53-bit significand), a further exact unit.

### Hopper H100 / H200 (sm_90a)
- **Units.** `wgmma.mma_async` (warpgroup of 4 warps, M = 64, N = 8..256, operands A from registers or smem, B from
  smem): IGMMA s8, QGMMA e4m3/e5m2 (accumulate 12-23 bits, ~13 fractional bits [READ PTX 9.2, Mazumder et al. citing
  two measurements]), HGMMA f16/bf16, BGMMA b1 **and.popc** (xor is emulated [SASS]). Per SM per clock: 2,048 f16,
  4,096 s8/e4m3.
- **Use wgmma, not mma.sync.** `mma.sync` INT8 reaches 978 of 1,513 TOPS (65%) on H800, wgmma 1,449 (96%)
  [READ Luo et al.]. wgmma throughput falls for N < 64 (N = 32: 65%, N = 16: 39%) [READ]: a BabyBear^8 limb tile is
  32 x 32, so pack several field elements' tiles into one N >= 64 instruction or accept the padding (it is HBM-bound
  anyway, Rule 1).
- **Memory plan.** TMA (`cp.async.bulk.tensor`) moves tiles HBM -> smem with an mbarrier, no thread instructions;
  thread-block clusters and distributed smem (SM-to-SM 180 cycles vs L2 ~273 [READ]); 228 KB smem/SM; 50 MB L2;
  3.35 TB/s (H200 4.8). Warp specialization: one producer warp issues TMA, consumer warpgroups issue wgmma, double or
  triple buffered (CUTLASS sm90 "pingpong"/"cooperative" kernels).
- **Clock.** Integer SIMT appears to run near the 1.98 GHz boost [INFERRED: hashcat SHA2-256 SXM/PCIe = 1.36 against
  SMs x boost 1.31; Keccak SXM extrapolated from that ratio, not measured]; tensor-heavy kernels at 700 W run lower [A].
- **Pitfalls.** `mma.sync` e4m3 compiles to F2FP + HMMA on sm_90a (it measures FP16) [SASS]; QGMMA's narrow
  accumulator makes FP8 integer blocks 18-72 products (ROTATION); sparse wgmma gives only 1.42x.

### Blackwell B200 (sm_100a) and Blackwell Ultra B300 (sm_103a)
- **Units.** `tcgen05.mma` issued by one thread for the CTA (or a CTA pair, `cta_group::2`), operands from smem
  descriptors (A optionally from TMEM), **accumulator in TMEM** (256 KB per SM, 128 lanes x 512 columns x 32 bit)
  [READ]. Kinds: tf32, f16, f8f6f4, mxf8f6f4, mxf4, mxf4nvf4, i8 (**sm_100a only; not on sm_103a**) [READ PTX].
  No 1-bit kind; legacy `mma.sync .b1` is emulated [SASS].
- **Rates per SM per clock** [A datasheet]: B200 4,096 f16, 8,192 s8/e4m3, 16,384 e2m1; B300 4,096 f16, 8,192
  e4m3, ~24,576 e2m1, s8 ~1/30 of e4m3 [READ arXiv 2608.11693 via ROTATION], fp64 2 (vs 64 on B200), f32->s32
  cvt 2 [READ Table 5].
- **Accumulator width.** B200 tcgen05 **E4M3 through CUTLASS** accumulated integers exactly with every accumulator
  driven to 2^24 at K = 2^14, checked bitwise against a host CRT [READ arXiv 2609.37693 section VIII-D]. A finite
  experiment, one format, one library: E2M1, block-scaled kinds, B300 and cuBLASLt are unverified. ROTATION's
  placeholder m = 12 is very likely pessimistic for B200 E4M3, and the B300 hour can test m = 24 directly.
- **Memory plan.** TMA into smem (multicast across a cluster), tcgen05.mma reads smem descriptors, accumulates in
  TMEM, `tcgen05.ld` moves results TMEM -> registers for the epilogue. TMEM frees the register file from
  accumulators, so the SIMT epilogue (promotion, scale application, modular reduction) runs in registers while the
  next tile accumulates. 228 KB smem, 8 TB/s HBM3e; STREAM Triad 4.13-4.14 TB/s (52%) at 4-16 GB arrays and
  7.42-7.48 TB/s (93%) at 64-128 GB in v1 of arXiv 2512.02189 (v2 drops the large rows) [READ]: the sustained figure
  for our working sets (0.1-2 GB tables) is unknown between 4.1 and 7.5 TB/s. That paper also lists a tcgen05 INT8
  m64n8k16 shape PTX does not define (Codex): treat its tensor tables as qualified.
- **Integer SIMT** is 64 lanes/SM/clk for LOP3/SHF/IMAD (Rule 2): B200 = 148/132 x (1.9/1.98) = 1.08x H100 for
  Keccak, B300 1.16x [INFERRED, SASS-identical round body on all three].
- **Pitfalls.** INT8 on B300 (tensor 1/30, no `kind::i8`); FP64 on B300 (2/clk: no FP64 limb tricks); `cvt.f32->s32`
  on B300 (2/clk); counting on the emulated `.b1` (ROTATION: use FP4/FP8 0/1 counts).

### TPU v5e / v6e
- **Units.** MXU: 128x128 systolic arrays (v5e: 4 per core; v6e: 256x256 [A]) for bf16 and int8 (int32
  accumulate); VPU: (8 sublanes, 128 lanes), 4 ALUs per lane per cycle (stated for TPU7x; 32-bit integer multiply
  low word exists, high word and 64-bit are emulated by XLA, rejected by Mosaic) [READ scaling book; MEASURED by the
  TPU lane]. v5e: 3.94e14 int8 OPS, 0.82 TB/s; v6e: 1.84e15, 1.6 TB/s [READ].
- **Memory plan.** HBM -> VMEM (128 MiB scoped, programmer-managed through Pallas BlockSpecs, double-buffered by the
  pipeline) -> VREGs -> MXU/VPU. Block shapes must be (8|16|32, 128)-tiled; a mis-tiled int8 operand gets a relayout
  copy fusion inserted (the TPU lane found two on a plain `jnp.dot` [MEASURED compiler]).
- **Exact arithmetic.** int8 x int8 -> int32 on the MXU; whether it wraps is unverified (ROTATION). Modular
  reduction is VPU work at 32-bit, so a 61-bit Montgomery is ~180 VPU ops (BFV.md section 5); NTT goes through the
  MXU as a four-step int8 matrix product (CROSS/MORPH style).

## 2. The exact-arithmetic toolkit (what each trick costs, where it wins)

1. **Limb decomposition into a narrow exact unit.** w = sum_i d_i B^i with balanced digits; a modular product
   becomes l^2 digit products (16 for 31-bit fields in bytes, 64 for 61-bit). Exact while K*P < 2^m (Rule 3).
   Choose the digit set to the unit: bytes for INT8 and FP16 (exact integers to 2,048), nibbles {-8..8} for E4M3,
   base-13 digits for E2M1 (prior art: the base-13 E2M1 Ozaki scheme, arXiv 2608.06812 [READ abstract]).
2. **Ozaki scheme II (CRT form).** Instead of splitting each operand into slices whose cross products all run, map
   the integer problem to residues modulo several small coprime moduli, run one low-precision GEMM per residue
   channel, reconstruct by CRT [READ arXiv 2504.08009]. For our exact integer products this is the same structure
   as an RNS, and the GEMM count is optimizable per format and accumulator width (Mazumder et al. 2026 give minimal
   counts for INT8, FP8, FP6, FP4 and lower bounds; they run on B200 and B300 [READ]). This is the systematic form
   of ROTATION's "FP16 byte limbs on B300": for a prime field it pays when the CRT reconstruction is cheaper than the
   l^2 cross products.
3. **Lazy reduction.** Harvey butterflies keep values in [0, 4p) (needs 4p below the word: p < 2^62 in u64, p < 2^30
   in u32) and drop two of three conditional subtractions;
   64-bit: 11.9 vs 14.6 SM-clk per warp-butterfly for Shoup [SASS sm_75; same on sm_90a, sm_100a]. For limb sums,
   the int32 wrap is lazy reduction for free (the register holds the exact residue mod 2^32, Lean `hwWrap_eq`).
4. **Small primes help on SIMT, less than it looks.** A 30-bit Harvey butterfly is 3.0-4.0 SM-clk per warp-butterfly
   against 11.9 for 61-bit Harvey [SASS]; replacing 3 x 61-bit primes needs 7 x 30-bit, so the compute ratio is
   0.54-0.67 against 61-bit Harvey, and bytes grow 7/6. On T4 and H100 the 30-bit NTT is then HBM-bound.
5. **GF(2) via integer parity** (ROTATION 2(b), Lean `gf2_dot_*`): count 0/1 products on the fastest exact unit,
   read the parity. On A100 use native b1 and.popc; on T4 xor.popc with AND = (popc a + popc b - XOR)/2 [MEASURED
   exact]; on B200/B300 FP4/FP8 0/1 with unit scales.
6. **Bit-slicing.** 32 independent field elements per 32-bit word; a GF(2^k) multiply becomes LOP3 networks with no
   tables and no data-dependent loads. Its cost is the transpose in and out (SHFL or PRMT/LOP3 networks), amortized
   over a whole layer. **Measured against us on T4** (TOWER256.md section 8): a per-thread bit-sliced Tower256
   multiply costs 52,700 op-eq (256 planes per operand spill to local memory, 8 warps/SM) vs 12,000-17,400 for log/exp
   tables. Bit-slicing wins only if the planes are spread across a warp's lanes or registers, which is unbuilt.
7. **NTT as matrix multiplication.** Four-step N = N1 N2 with twiddles folded into per-column matrices; the MXU path
   in BFV.md and CROSS/MORPH [READ via HARDWARE.md], TensorFHE and WarpDrive on GPUs [READ abstracts]. The matmul
   carries O(N1 + N2) MACs per point instead of O(log N) butterflies, so it wins only where the tensor rate per
   SIMT op is large and the limb count small (section 3.4).
8. **Keccak on SIMT.** nvcc emits 136 LOP3 + 58 SHF per round on every target [SASS] (4,656 per Keccak-f). It is
   not the floor: applying theta as A' = xor3(A, C[x-1], rot(C[x+1], 1)) without materializing D gives <= 180 ops
   per round, 4,320 per Keccak-f, 7% less (Codex; identity checked on random states, unbuilt). A further lever is
   pipe balance: the FMA pipe is idle, and part of a rotation can be built from IMAD.WIDE.U32 by 2^k [INFERRED,
   unbuilt]. No competitive tensor mapping is known (ROTATION 2(c): a dense theta GEMM is 240x slower).

## 3. Per workload: the optimal kernel

### 3.1 Prime-field sumcheck rounds and Freivalds (BabyBear^8 limbs)
- **Shape.** Each round reads every table once (2^mu elements, 32 B in canonical u32x8 or bytes-limb form), forms
  degree-d evaluations (inner products of limb vectors), folds by a challenge r (scalar x vector), writes half.
  Freivalds is matrix-vector work: read each matrix once.
- **Unit.** Tensor (INT8 everywhere it exists; FP16 byte limbs on B300 per ROTATION) for the limb products; SIMT for
  the reduction mod p and the fold. Neither binds: HBM does (Rule 1).
- **Memory plan.** One pass per round, respecting Fiat-Shamir: r_i exists only after round i's message is reduced,
  so the pass for round i+1 loads the round-i table, folds it by r_i on the fly, computes round i+1's d+1 evaluations
  from the folded values, and writes the folded table once (TMA on sm_90+/sm_100, cp.async on sm_80). Round sums
  stay in registers/TMEM and reduce across CTAs at the end. Rounds whose table fits in L2 (H100: table <= 50 MB,
  i.e. the last ~20 of 25 rounds at 2^25) run from L2 [INFERRED; ~5% of bytes]. This is the "fused read" schedule
  F3 found TensorZKP must use; the 10.7 GB is ROTATION's count and is not re-derived for this schedule here.
- **Bound** (predict.py section 3; bytes from ROTATION): T4 44 ms, A100 7.0, H100 3.7-4.3, H200 2.6-3.0, B200/B300
  1.8-2.6 at 2^25. The B200/B300 range is the unmeasured sustained bandwidth (4.1 STREAM vs 6.0 assumed).
- **Pitfalls.** Streaming four separate products costs 1.4x the fused bytes (F3: 15 GB vs 10.7); cuBLAS strided-batched
  small GEMMs (32 x N x 32) get the library's worst tiles; INT8 on B300.

### 3.2 Tower256 additive NTT and FRI prover (Keccak/cSHAKE Merkle)
- **Merkle (hash).** SIMT, ALU-pipe bound: 4,656 int32 ops per Keccak-f [SASS], one Keccak-f per leaf and per node
  from a cached cSHAKE midstate. Optimal kernel: one persistent kernel per tree (or per batch of trees) that walks
  levels with a grid-wide barrier or a cluster, keeping each level's digests in L2/smem, instead of one launch per
  level (the T4 build is launch-bound below ell 18 [MEASURED: ~300 launches per proof]). Occupancy: 72 registers per
  thread (sm_75..sm_103a [SASS]) allows 28 warps/SM; the ALU bound needs only ~4 independent warps per sub-partition.
  Bound: 4.2e9 Keccak-f/s on B300, 3.6e9 H100, 6.5e8 T4 at 1.19 GHz (predict.py section 1).
- **Encode (additive NTT, Gao-Mateer).** n/2 multiplies per depth plus XORs. Three kernels compete:
  1. table Karatsuba to GF(2^8) log/exp: 14,200 op-eq per multiply [MEASURED T4], bank-conflicted smem loads;
  2. bit-sliced, one thread per 32 products: **52,700 op-eq [MEASURED T4, TOWER256.md 8], loses 3-4x** (the 718
     of F3/ROTATION is below even the 860-op ideal LOP3 count of Karatsuba-to-bits for this tower);
  3. tensor parity path for fixed-r multiplies (twiddles shared by 2^layer butterflies; ROTATION 2(b)).
  The predicted optimum is the tensor fixed-r route for coarse layers plus tables for fine layers; a warp-cooperative
  bit-slice (planes across lanes, no local memory) is the open SIMT alternative.
- **Bound per proof at ell 20** (one column): Merkle 6.4 ms T4 at 1.19 GHz, 1.2 ms H100 (1.98 GHz), 1.0 ms B300;
  encode + folds on the tensor route 13.7 T4, 2.5 H100, 0.95 B300 [ROT]; with tables only 65 T4, 12 H100, 10 B300
  (predict.py 1b). The prover stays arithmetic-bound unless the tensor route lands.
- **Batch shape.** Many leaves of one shape: parallelize across words (embarrassingly parallel), one word per CTA
  cluster at ell >= 18; a single proof at ell 14 does not fill a GPU (65k Keccak-f = 0.02 ms on H100).

### 3.3 MXFP4 exact recompute of gpt-oss-20b
- **Decode (batch 1).** HBM-bound on weights. Proxy: 3.6e9 active parameters [A model card] x 4.25 bits = 1.9 GB per
  token if the MXFP4 bytes are read once and unpacked in registers; 3.7 GB unpacked to int8 with scales (1.94x). Only
  the MoE weights are MXFP4 (attention and embeddings are BF16), so the true figure is higher; KV traffic is extra.
  Bound: 7.9 ms T4, 0.66 H100, 0.32 B200/B300 (predict.py section 4).
- **Verification of a transcript (batch T).** Compute-bound once each expert sees >~100 tokens. The block-32 E8M0
  scale is the obstacle: one K = 32 tensor instruction per block, then SIMT shift-add into a wide accumulator
  (ROTATION 2(d): SIMT-bound, 7x over tensor on B300). Optimal designs, in order of preference:
  1. **mxf8f6f4 / mxf4 with hardware block scales and a per-tile certificate** (ROTATION's "faster variant"): exact
     when, for the actual operands, (max product magnitude in units of the smallest product exponent in the tile) x K
     < 2^m and every product stays in FP32's normal range (ROTATION's span + 13 + log2(K/32) < m is the FP4 x FP4
     case: 32*6*6*4 = 4,608 < 2^13; Codex). For FP4 x FP4 at m = 24, K = 2,880: product-exponent span <= 4. Both
     operands must be in an MX format: the int8 activation limbs of jaxint.py do not enter these kinds.
  2. **Per-row exponent normalization into wider integer weights** (w * 2^(e - e_min) as int16-in-two-int8-limbs or
     FP16, which holds E2M1 x 2^k exactly): moves the scale into the weight once, offline; costs a limb when the span
     exceeds 3 bits.
  3. SIMT shift-add per block (current design; jaxint.py): correct everywhere, SIMT-bound.
- **Activations.** Two balanced int8 limbs (|x| < 2^15) as jaxint.py does: 2x the weight-limb MACs. On B300 there is
  no INT8 tensor path: widen both operands to FP16 (byte limbs and E2M1 x 2^k weights are exact in FP16; kind::f16),
  or split activations into E4M3-exact digits (|d| <= 16) and charge the extra products.

### 3.4 RNS NTT and BFV returns (dark learning)
- **SIMT NTT.** FMA-pipe bound: 64-bit Shoup radix-8 (current kernel) 15.0-16.0 SM-clk per warp-butterfly [SASS], so
  N = 8,192 costs 0.56 us T4 (1.19 GHz), 0.10 H100, 0.089 B200, 0.082 B300 per NTT in a batch. Harvey: 0.75x. 30-bit
  primes: 0.54-0.67x of Harvey. One-pass HBM for one 64-bit polynomial (16N bytes, twiddles assumed L2-resident) is
  below the 61-bit compute on every target except T4, where they tie; the 30-bit variant is HBM-bound on T4 and H100.
- **Memory plan.** One kernel per NTT row with all log N stages in smem/registers (radix-8 or radix-16 register
  groups), twiddles from L1/L2 (shared by all rows of one prime); fuse the pointwise MAC into the inverse NTT's
  load and the finalize into its store (BFV.md tuning items 1-2). The 1.25 MB per return used in predict.py is the
  ledger of one assumed fused schedule (keys and plaintext spectra L2-resident, randomness generated on chip), not a
  lower bound, and predict.py prices only the NTTs: pointwise, finalize and HPS arithmetic are not in it. Occupancy: at N = 8,192 one row is 64 KB of smem, so T4 runs one 8-warp block per SM
  (latency-bound: measured 3.2x above the FMA bound) [SASS + MEASURED]. Use two rows per CTA with E = 4,096
  two-pass, or registers-first radix-2^4 with 2 KB per warp, to reach 24+ warps.
- **Tensor NTT.** Four-step int8 products (BFV.md 5b): 1.0e8 int8 MACs per NTT at N = 8,192 with byte limbs of
  61-bit words. H100: 0.10 us at wgmma peak, tying SIMT; B200: 0.045 us (2x SIMT); B300: dead in INT8, 0.21 ms per
  batch with FP16 byte digits (ROTATION 2(e)). With 30-bit primes the limb count drops 4x per prime (16 vs 64
  products), ~1.7x per 61 bits [INFERRED].
- **Per return and per step.** predict.py section 2 (partial-work roofline): 8.4 us T4 (vs 49.5 measured), 1.50 H100,
  1.34 B200, 1.24 B300 with the current butterfly; 0.58-0.77 us on H100-B300 with 30-bit primes. Enc_pk(0) offline
  (BFV.md) removes L of the 5L online NTTs.

## 4. Pitfalls collected (each cost us or another lane time)

- Timing windows on a power-capped part without a clock reference (T4: the same kernel reads 3.15e8 and 6.9e8).
- `mma.sync` on Hopper (65% of peak); `mma.sync` e4m3 on sm_90+ (FP16 underneath); `.b1` on Blackwell (emulated).
- `cvt.rni.s32.f32` and FP64 on B300 (2/clk/SM); INT8 on B300 (1/30); assuming 128 integer lanes/SM/clk on
  Blackwell for LOP3/IMAD (it is 64).
- Library small-GEMM shapes (32 x N x 32 batched) and unsupported INT8 layouts (T4 `NT`).
- One-pass smem kernels that leave one block per SM (8 warps) on parts with 64 KB smem.
- Assuming 0.75 of datasheet HBM on B200 (STREAM reads 0.52).
- For TPU: mis-tiled int8 operands (relayout copies), 64-bit integer ops inside Pallas (rejected), and reading the
  compiler's `optimal_seconds` for Pallas custom calls (it reports -1 or ~0; PREDICTORS.md).
