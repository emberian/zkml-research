# Mapping our workloads onto each target: predicted optimum, gap to our kernels, top changes

2026-11-06, hw-optimality lane. Optimum = the bound of the stated algorithm (`predict.py`, OPTIMAL.md section 0),
not a promise; its trust per term is in PREDICTORS.md. "Current" is our kernel as measured (T4, Kaggle) or as
modelled by the owning lane. Tags as in GROUNDING.md.

## 0. Four inputs the hardware lane's model should change (ROTATION.md / `mma_counts.py`)

1. **tcgen05 E4M3 on B200 accumulated integers exactly to 2^24 (published, one format, one library).** Mazumder et al.
   drove every accumulator to 2^24 at E4M3, K = 2^14, through CUTLASS, and checked bitwise against a host CRT [READ
   arXiv 2609.37693 section VIII-D]. ROTATION uses m = 12 as a placeholder. If m = 24 holds, the FP8 0/1 parity block
   is ~16.7M (not 4,095) and FP8 nibble limbs hold 74,000+ products (not 18). **Unverified:** E2M1 and block-scaled
   kinds, B300 (sm_103a), cuBLASLt on either part. The paid B300 hour tests m = 24 directly instead of searching
   from 12; a finite boundary test is evidence, not a proof of exactness for every operand pattern.
2. **Integer SIMT on Blackwell is 64 lanes/SM/clk for LOP3/SHF/IMAD**, not 128 [READ CUDA 13.5 Best Practices
   Table 5]; only IADD and FP32 are 128. `mma_counts.py` TARGETS/SKUS `simt = sms * 128 * clk` overstates B200/B300
   Keccak and every SIMT promotion term by 2x. ROTATION's B300 Keccak 6.6e9/s becomes 4.2e9 (sassbound bound).
3. **Keccak-f is 4,656 int32 ops on every target** (136 LOP3 + 58 SHF per round, [SASS] sm_75, sm_80, sm_90a,
   sm_100a, sm_103a). The T4's "5,900 op-eq [MEASURED]" divides by the 1.59 GHz boost clock; at the T4's measured
   1.19-1.26 GHz [INFERRED, no clock recorded] the same runs give 4,400-4,700. Hashcat Keccak-256 on A100 PCIe and
   H100 PCIe lands at 1.02-1.03x the 4,656-op bound at their boost clocks [READ]; hashcat does ~4-5% less work per
   candidate (pruned last round, constant lanes), so the match is within ~5%. Use 4,656 (nvcc's count; a 4,320-op
   formulation exists, OPTIMAL 2.8) and a real clock.
4. **B300 converts f32 -> s32 at 2/SM/clk** [READ Table 5, footnote 11, CC > 10.0] and runs FP64 at 2. ROTATION's
   promotion "scale, cvt, iadd" spends 16 SM-clk per warp on the `cvt` alone on B300 (vs 0.25-0.5 for an add). Use the bias read
   (ROTATION 2(b)) or the magic-number add (exact for |x| < 2^22). Also: **B200 sustained HBM may be 4.1 TB/s**
   at small working sets (STREAM Triad 52% of 8 TB/s at 4-16 GB; 93% at 64-128 GB in v1 of arXiv 2512.02189,
   withdrawn in v2 [READ]); every B200/B300 HBM-bound floor moves by up to 1.45x until the paid hour measures copy
   at our sizes.

## 1. Prime-field sumcheck and Freivalds (BabyBear^8, degree 2, 2^25)

| target | optimum (fused, HBM-bound) | current | gap |
|---|---:|---|---|
| T4 | 44 ms | primitive only: INT8 inner product via cuBLAS strided-batched, 1.22-1.56x copy [MEASURED] | ~1.4x on the primitive; no end-to-end kernel |
| A100 | 7.0 ms | none | - |
| H100 | 3.7-4.3 ms | TensorZKP (published, H100) degree-2 sumcheck 4.04 ms [READ via F3] | 1.0-1.1x (theirs) |
| H200 | 2.6-3.0 ms | none | - |
| B200 | 1.8-2.6 ms (INT8) | none | - |
| B300 | 1.8-2.6 ms (FP16 byte limbs, ROTATION) | none | - |

Top changes (for whoever writes the GPU sumcheck):
1. **One pass per round that folds by the previous challenge on load** (r_i is known only after round i's message;
   OPTIMAL 3.1): ROTATION counts 10.7 GB at 2^25 against the 15 GB of four streamed products (1.4x) [F3 + INFERRED].
2. **Own tensor kernel, not cuBLAS strided-batched**: 32 x N x 32 tiles are the library's worst case; on Hopper pack
   >= 2 elements' limb tiles per wgmma (N >= 64, otherwise 65% throughput [READ]); on B300 FP16 byte limbs through
   tcgen05 kind::f16 (ROTATION).
3. **Rounds that fit in L2 run from L2** (last ~20 of 25 at 2^25 on H100), and fold the challenge into the next
   round's load. Worth ~5-10% [INFERRED]; do it after 1 and 2.

## 2. Tower256 additive-FRI prover (one column, ell 20)

The 718-op bit-sliced multiply that F3 and ROTATION compared against is withdrawn: the readiness lane built it
(TOWER256.md section 8) and measured 52,700 op-eq per multiply against 12,000-17,400 for the tables.

| target | optimum: Merkle + encode/folds on the tensor fixed-r route [ROT] | tables only (predict.py 1b) | current | gap to optimum |
|---|---:|---:|---|---|
| T4 | 6.4 + 13.7 = ~20 ms (1.19 GHz) | 6.4 + 65 = ~72 ms | device 108 ms: encode 86.8, Merkle 14.1, folds 6.9 [MEASURED] | ~5x |
| H100 | 1.2 + 2.5 = ~3.7 ms | ~13 ms | modelled 26 ms (TOWER256.md) | ~7x |
| B300 | 1.0 + 0.95 = ~2.0 ms | ~11 ms | - | - |

Top changes:
1. **Tensor fixed-r route for the coarse layers** (ROTATION 2(b); B300 probe item 6), tables for the fine layers:
   encode + folds 94 -> ~14 ms on T4 if ROTATION's counts hold. T4 can run it as INT8 0/1 or b1 xor.popc for free.
2. **Persistent Merkle kernel** (one launch per tree with a grid barrier or clusters; ~300 launches per proof
   today): 14.1 -> ~6.4 ms at T4 clocks. After change 1 the hash is ~30-45% of the prover.
3. **Warp-cooperative bit-slice** (planes spread across a warp's lanes so they never reach local memory): the only
   SIMT route that could undercut the tables; unbuilt, and `sassbound` counts its SASS before any run.
- Batching words and a Rust host stay as TOWER256.md says (the Python openings are 100-220 ms of wall, not device).

## 3. MXFP4 exact recompute of gpt-oss-20b

| target | optimum, decode per token (packed MXFP4 read once) | current | gap |
|---|---:|---|---|
| T4 | 7.9 ms | G2: layer 0, 12 tokens, 152.5 s (JAX int8 limbs, cuBLASLt s8; a correctness harness) [MEASURED] | ~4x10^4 per token-layer; measures the harness, not a kernel |
| H100 | 0.66 ms | - | - |
| B200 / B300 | 0.32 ms (4.1 TB/s: 0.46) | - | - |

Top changes:
1. **One fused kernel per layer** that reads packed MXFP4 once (unpack in registers; 2x fewer bytes than int8
   weights), runs one K = 32 int8 MMA per block, and applies the E8M0 shift-add in registers (T4/A100/H100 INT8;
   B200 kind::i8).
2. **Verify transcripts in batches** (T tokens per weight read): decode is HBM-bound, verification of a whole
   transcript is compute-bound and 1-2 orders cheaper per token.
3. **On Blackwell, hardware block scales with a per-tile certificate** (OPTIMAL 3.3 option 1): with m = 24 (B200,
   published) most tiles skip SIMT scale handling, which ROTATION found 7x over tensor on B300. Needs m on B300.

## 4. RNS NTT and BFV returns (dark learning, N = 8,192, L = 3)

| target | optimum per return (current butterfly / Harvey / 30-bit primes) | current per return | optimum per step (outer, current butterfly) | current per step |
|---|---|---|---:|---|
| T4 | 8.4 / 6.2 / 6.0 us | 49.5 us [MEASURED] | 0.41 s | 2.45 s outer, 2.77 s step [MEASURED] |
| A100 | 2.6 / 2.0 / 1.5 | - | 0.13 | - |
| H100 | 1.50 / 1.13 / 0.77 | modelled 4.3-7.0 (BFV.md) | 0.074 | modelled 0.25-0.4 |
| B200 | 1.34 / 1.00 / 0.63 | modelled 3.1-5.5 | 0.066 | modelled 0.18-0.3 |
| B300 | 1.24 / 0.93 / 0.58 | - | 0.061 | - |

These are a partial-work roofline: NTTs plus the HBM ledger of one fused schedule; pointwise, finalize, HPS and
randomness arithmetic are not priced, so the true optimum is somewhat higher. Gap: ~5.9x on T4, ~3-5x against the
H100/B200 models. The NTT itself is 3.2x over its FMA bound on T4 (1.77 vs 0.56 us),
the rest is unfused elementwise passes.

Top changes:
1. **Fuse and fill**: MAC into the inverse NTT's load, finalize into its store, decrypt's pointwise into its INTT
   (BFV.md items 1-2), and raise occupancy above one 8-warp block per SM (two rows per CTA at E = 4,096, or radix-16
   register groups). Closes most of the 5.9x on T4; on H100/B200 it is what separates 4-7 us from ~1.5 us.
2. **Harvey lazy butterflies** (1.33x on the FMA bound, [SASS]); free, word-identical outputs after a final reduce.
3. **Enc_pk(0) offline** (removes L of 5L online NTTs, 1.25x; BFV.md) or **30-bit RNS primes** (Harvey needs
   p < 2^30: 7 primes replace 3, 0.54-0.67x of 61-bit Harvey compute, 7/6 the bytes, HBM-bound on T4/H100). Both are the dark-learning lane's parameter calls. Tensor four-step NTT pays only on B200 (2x SIMT,
   INT8); on H100 it ties SIMT and on B300 it loses.

## 5. What the paid hours must measure to calibrate the predictors (for initiative 17)

Priority is "fixes a predictor input that moves many rows", not "one more number". Every item goes into `results.json`.

**Every box, every script (cheap; makes every other number interpretable):**
1. SM clock during each timed window (NVML `clocks.sm` sampled inside the process, or `nvidia-smi dmon -s c` logged
   beside), plus a 1-second same-process LOP3 throughput kernel as a clock reference. The T4 runs read 3.15e8 and
   6.9e8 Keccak-f/s for one kernel because nothing recorded the clock.
2. Copy and read bandwidth at 1, 4, 16 and 64 GB (and on B200/B300 the CUDA `nvbandwidth`-style D2D copy): settles
   0.52 (STREAM) vs 0.75 of datasheet, which scales every HBM-bound floor in sections 1 and 3.

**H100 (calibrates the SIMT and HBM predictors at Hopper; ~10 min on top of mma.sh):**
3. `tower256.sh` Keccak-f rate (`keccak_f_per_s`) with clock: predicted 3.57e9 at 1.98 GHz (sassbound). Within 10%
   confirms the SIMT predictor for every SIMT row; outside it, sassbound's pipe table is wrong for sm_90a.
4. BFV NTT microbench (`bfv.sh`, the best shape) against the sassbound FMA bound of 0.10 us: gives the
   latency/occupancy efficiency factor the bound omits (T4: 3.2x over).
5. mma.sh's wgmma rates incl. BGMMA, and the INT8 inner product against copy (ROTATION H100 list; unchanged).

**B300 first, then B200 (tensor exactness and the Blackwell-specific SIMT facts):**
6. tcgen05 FP8 and FP4 0/1 integer count at K = 2^14 .. 2^20 **through CUTLASS and through cuBLASLt**, driving
   accumulators to 2^24 and 2^24 + 1: confirms or refutes m = 24 on sm_103a (published for sm_100a/CUTLASS only).
   This replaces ROTATION's "search from m = 12".
7. `cvt.rni.s32.f32` throughput vs the magic-number conversion vs IADD on sm_103a (Table 5 says 2 vs 128/clk): one
   microkernel, a few seconds. Decides how the FP-path promotions are written.
8. Keccak-f rate (SIMT flat-per-SM claim: predicted 4.2e9 on B300, 3.9e9 on B200 at 1.9 GHz).
9. ROTATION's B300 list items 1-5 otherwise unchanged (FP16 byte-limb inner product, peak rates).

**Free, before any paid hour (T4, Kaggle):** the tensor fixed-r Tower256 multiply as INT8 0/1 or b1 (row 2's
decider) and the NTT occupancy fix (row 4), each with the clock reference of item 1.
