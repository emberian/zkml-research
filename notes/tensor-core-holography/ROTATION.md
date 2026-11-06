# The rotation: the fastest exact-integer datapath per target, and our workloads remapped onto it

2026-11-06, initiative 14 (hardware lane), after the readiness lane's T4 dry run
(`notes/accelerator-readiness/MMA.md`).

## What the dry run showed

- Blackwell has no hardware 1-bit MMA: sm_100/103 emulate `.b1`.
- Hopper emulates `xor.popc` but runs `and.popc` natively (BGMMA).
- `mma.sync e4m3` runs native only on sm_89. On H100 and Blackwell it widens to FP16 (HMMA).
- B300 runs INT8 at 1/30 of FP8.
- On T4: integer-addend accumulator m = 24; INT8 wrap exact at 33,026 and 66,052; 1-bit rate 7-8x INT8.

## Where things live

- Counts: `notes/construction-search/mma_counts.py --rotation` (section 7).
- Lean: minidregg `lane/mma-exact`, `Theory/MmaAccumulatorExact.lean`. Kernel-checked with lean v4.35.0;
  axioms are `propext` and `Quot.sound`, plus `Classical.choice` in `gf2_dot_blocks`.
- Codex (gpt-6-astra) attacked the parity-through-FP8 claim and these tables before landing. Every finding
  is applied; the ones that changed a number are marked (Codex).
- Tags: [MEASURED] [READ] [X] (published) [A] (assumed) [INFERRED].

## 0. The rotation in one paragraph

Stop asking for a narrow integer unit. Ask which unit multiplies small integers exactly and keeps their
sum exact, and use the fastest such unit on each chip:

- **B300:** INT8 is withdrawn, but FP8 / FP4 with 0/1 or digit operands, and FP16 with byte operands, are
  exact under a stated block length.
- **GF(2) inner products:** they need no 1-bit unit. A GF(2) inner product is the parity of an exact
  integer count of 0/1 products, so it runs on whatever unit counts fastest.
- **Proved:** this is proved for every accumulator that holds integers below `2^m`, together with the
  block bound and the promotion that makes it unbounded.
- **Not proved:** that a given tensor core is such an accumulator. That is the premise the paid hour
  measures.

## 1. Per-target exact datapaths

Rates are dense MAC/s. The exact block is the number of products per accumulator before reduction or
promotion.

| target | datapath | MAC/s | m (integer-exact) | block, BabyBear limbs | block, 0/1 parity | status |
|---|---|---:|---:|---:|---:|---|
| T4 | INT8 (IMMA) | 6.3e13 | int32 wrap | 33,025 | unbounded | [MEASURED] |
| T4 | FP16 (HMMA) | 3.0e13 | **24** | 258 (byte limbs) | 16.7M | [MEASURED] m = 24 |
| T4 | b1 xor.popc | 5.0e14 | int32 wrap | — | unbounded (xor identity) | [MEASURED] 7.9x INT8 |
| A100 | INT8 | 3.1e14 | wrap | 33,025 | unbounded | [X] |
| A100 | b1 and/xor | 2.5e15 | wrap | — | unbounded | [X], native (SASS) |
| A100 | FP16 | 1.6e14 | 24 (PTX: at least single precision) | 258 | 16.7M | [READ] |
| H100 | INT8 (IGMMA) | 9.9e14 | wrap | 33,025 | unbounded | [X] |
| H100 | FP8 (QGMMA, wgmma only) | 9.9e14 | **12 to 23**, unmeasured (PTX 9.2) | 18 at m = 12 (72 at 14) | 4,095 at m = 12 | probe |
| H100 | FP16 | 4.9e14 | 24 (PTX) | 258 | 16.7M | [READ] |
| H100 | b1 and.popc (BGMMA) | **unmeasured** | wrap | — | unbounded | native; rate is the probe |
| B200 | INT8 | 2.25e15 | wrap | 33,025 | unbounded | [X] |
| B200 | FP8 / FP4 (tcgen05) | 2.25e15 / 4.5e15 | **unpublished** (placeholder 12) | 18 / 63 | 4,095 | probe |
| B200 | FP16 | 1.1e15 | 24 [A: tcgen05 has no precision text] | 258 | 16.7M | [A] |
| B300 | INT8 | 7.5e13 | wrap | 33,025 | unbounded | [X] 1/30 FP8; no `kind::i8` |
| B300 | FP8 / FP4 (mxf4) | 2.25e15 / 7.0e15 | unpublished (placeholder 12) | 18 / 63 | 4,095 | probe (Codex: HGX B300 is 14 PF FP4, 7.7 TB/s) |
| B300 | FP16 | 1.1e15 | 24 [A] | 258 | 16.7M | [X] rate, [A] m |
| B200, B300 | b1 | — | — | — | — | **emulated**: not a datapath |
| TPU v5e / v6e | INT8 (MXU) | 2.0e14 / 9.2e14 | int32; overflow semantics unverified | 33,025 if it wraps | unbounded if it wraps | [X] rate |
| TPU v5e / v6e | bf16 (MXU) | 9.9e13 / 4.6e14 | f32 accumulate, m = 24 [A] | 258 if products are exact | 16.7M | [X] Google |

Two corrections changed this table (Codex):

- **m = 14 is not conservative for FP8 on Hopper.** PTX's "higher than half precision" allows 12, so the
  table uses 12 as the floor. Tcgen05 has no precision text at all.
- **bf16 byte limbs need 16-bit products, and PTX promises bf16 only "specified precision".** FP16 byte
  limbs (multiply and accumulate at least single precision) carry the integer work. bf16 keeps only 0/1
  operands, whose products are trivially exact.

Promotion changes the bounds:

- Promotion by **parity XOR** makes the 0/1 column exact at every length (`gf2_dot_blocks`).
- Integer totals promoted by `cvt + iadd.s32` stay bounded by the INT32 total, unless reduced mod p on the way.

## 2. Workloads remapped (counts from `--rotation`; proxies, with HBM at 0.75 of datasheet as T4 measured)

### (a) Prime-field sumcheck and Freivalds, BabyBear^8, degree 2, 2^25

| target | best exact path | floor | binding |
|---|---|---:|---|
| T4 | INT8 | 44.4 ms | HBM |
| A100 | INT8 | 7.0 ms | HBM |
| H100 | INT8 | 4.3 ms | HBM (FP8: 4.45 ms, SIMT-bound) |
| B200 | INT8 | 1.79 ms | HBM |
| **B300** | **FP16 byte limbs** | **1.86 ms** | HBM. Then FP8 nibbles 1.91 (SIMT), FP4 2.73 (SIMT), INT8 2.98 (tensor) |
| TPU v5e / v6e | INT8 | 17.5 / 8.7 ms | HBM (no VPU term) |

- **The rotation for primes is FP16 with byte limbs on B300.** It gives the same limb count as INT8 (16
  products per base multiply) at 15x B300's INT8 rate. The block is 258 by spec, so promotion is cheap.
- Everywhere else INT8 stays, and every target is HBM-bound. Tensor format is not the lever. Bytes per
  element are.

### (b) Binary tower: the GF(2) parity path

- **Algebra, proved in Lean:**
  - `gf2_dot_via_fp`: for any accumulator with `HoldsBelow m`, N 0/1 products with `N + 1 < 2^m` read for
    parity give the GF(2) inner product.
  - `gf2_dot_via_s32`: the INT8 and `.b1` integer register wraps, so the parity read needs no bound.
  - `gf2_dot_blocks`: block-wise promotion by parity XOR is exact at every length.
  - `gf2_fp_fails_past_block`: falsifier; nine products through a 3-bit truncating accumulator read 8.
  - `gf2_fp_inside`: a mixed non-vacuity witness.
  - `lazy_bilinear`: any fixed GF(2)-bilinear map commutes with lazy accumulation, so a Tower256 inner product
    is "count S_jk on the tensor core, take parities, apply T once". `gf4_lazy_check` checks one coordinate.
- **Tower256 qualifies** (Codex, reading minidregg `Theory/BinaryTowerFanPaar.lean:225` and
  `BinaryTowerTrace.lean:343`): its multiply is fixed GF(2)-bilinear in the Fan–Paar coordinates. The
  end-to-end Lean instance is not written.
- **Operands:** e4m3 one is `0x38`; e2m1 one is nibble `0x2`; the unit UE8M0 scale is `0x7f`.
  - For FP4 0/1 the unit-scaled `mxf4` kind (K = 64) earns the FP4 rate. Mixing two blocks is harmless here,
    because every scale is 1.
  - `f8f6f4` runs e2m1 at the FP8 rate (Codex).
- **Parity read (Codex):** initialise the FP32 accumulator to `2^(m-1)` and keep the count below it. Then raw
  bit `24 - m` of the register is the parity, with no conversion: 2 ops per output bit (`and` plus `ballot`).
  It halves the block. The fragment-to-word layout is not costed.

**SIMT baselines, corrected 2026-11-06 by the readiness lane's T4 measurement (`notes/accelerator-readiness/
TOWER256.md` §8, zkml-research 7821648b):**

| SIMT Tower256 multiply | ops per multiply (T4 int32-op equivalents) | status |
|---|---:|---|
| log/exp table kernel | 12,000-17,400 (2.3-3.4e8/s) | [MEASURED], the GPU path today |
| bit-sliced, resident planes | 52,700 (fused with transposes: 71,500) | [MEASURED], bit-exact; loses to the table |
| ideal Karatsuba-to-bits instruction count | 860 with LOP3 fusion (1,284 two-input) | [D] unreachable: 256 planes per operand do not fit 255 registers |
| warp-cooperative bit slicing | ~1,700 | readiness lane's estimate, unbuilt |

The earlier 718 sat below the ideal instruction count. It is withdrawn.

Per element pair (ns, proxy). The SIMT columns scale T4 op-equivalents by each target's SIMT rate. "Win" is
the fixed-r multiply, the harder case.

| target | path | inner product | fixed-r multiply | table (12,000) | win vs table | vs ideal 860 |
|---|---|---:|---:|---:|---:|---:|
| H100 | INT8 or FP8 0/1 | 0.066 | 0.066 | 0.719 | **10.8x** | 0.78x |
| B200 | FP4 0/1 | 0.015 | 0.019 | 0.333 | **17.9x** | 1.28x |
| B300 | FP4 0/1 (mxf4, unit scales) | 0.011 (HBM) | 0.017 (SIMT) | 0.308 | **17.9x** | 1.28x |
| B300 | FP8 0/1 | 0.029 | 0.029 | 0.308 | 10.6x | 0.76x |
| B300 | INT8 0/1 | 0.276 | 0.874 | 0.308 | 0.4x (loses) | — |
| A100 | b1 (native) | 0.042 | 0.063 | 1.231 | **19.6x** | 1.41x |
| T4 | b1 xor | 0.264 | 0.397 | 2.948 | 7.4x | 0.53x |

**Yes, the tensor GF(2) routes now win by more:**

- **Fixed-r multiply:** 10.6-19.6x the measured SIMT multiply on every target with a counting unit, against
  the old 12-21x over a 14,200 table and roughly a tie against 718. They beat even the unreachable ideal SIMT
  count wherever FP4 or native b1 exists (1.28-1.41x).
- **Inner products:** they win by more again, 11-29x.
- **B300's INT8 is the one route that loses.**

- **NTT reuse (Codex):** a twiddle is shared by 2^layer butterflies. Fine layers pad the tile (1/64 at layer 0),
  so the model falls back to the table there.

### (c) Keccak / cSHAKE Merkle and the Tower256 prover

- **No tensor mapping exists for Keccak.** Theta is its only arithmetic linear step; a dense GF(2) GEMM of it
  is 240x slower at INT8 peak. Rho and pi permute bits; iota is affine.
- **The SIMT bound comes from T4:** 5,900 op-eq per Keccak-f [MEASURED], against the model's 4,320.
  Scaled: H100 2.8e9/s, B300 6.6e9/s.

Tower256 FRI prover (one column), ms per proof, with the measured table baseline (12,000):

| target, ell | hash | arith: table | arith: tensor (fine NTT layers on the table) | proof: table → tensor | hash share |
|---|---:|---:|---:|---|---|
| T4, 20 | 6.1 | 37.1 | 12.6 (b1x) | 43.2 → 18.6 (**2.3x**) | 0.14 → 0.33 |
| H100, 20 | 1.5 | 9.0 | 2.3 (INT8) | 10.5 → 3.8 (**2.8x**) | 0.14 → 0.39 |
| B200, 20 | 0.69 | 4.2 | 0.90 (FP4) | 4.9 → 1.6 (**3.1x**) | 0.14 → 0.43 |
| B300, 20 | 0.64 | 3.9 | 0.86 (FP4) | 4.5 → 1.5 (**3.0x**) | 0.14 → 0.43 |
| B300, 22 | 2.5 | 16.8 | 3.5 (FP4) | 19.4 → 6.1 (**3.2x**) | 0.13 → 0.42 |

- **The GPU prover is arithmetic-bound today.** Hash share is 0.13-0.18, matching T4's measured 80% encode.
  The tensor route makes it 2.3-3.2x faster per proof; the arithmetic alone drops 3-5x.
- **The fine NTT layers are what cap that win.** Layers 0-5, where a twiddle is shared by fewer than 64
  butterflies, stay on the table.
- If those layers also ran on the tensor path (twiddles in a small subfield, or a reordered or fused radix
  block), B300 ell 20 would reach about 0.21 ms of arithmetic and 0.85 ms per proof: **5.3x**, with the hash
  at 75% [INFERRED].
- **No reachable SIMT multiply changes the ranking.** The ideal 860 is register-infeasible, and the
  warp-cooperative ~1,700 estimate would still lose 2.6x to B300 FP4.

### (d) MXFP4 exact recompute (4096^3 GEMM)

- **Per 32-block exactness:** a block's dot is at most 1,152, i.e. 4,608 quarter-units < 2^13. That is exact
  in any accumulator with m ≥ 13.
- **The exact path:** run one 32-block per instruction (`f8f6f4`, K = 32, at the FP8 rate) and apply E8M0
  scales on SIMT into a wide accumulator. That is 4 ops per output per block in the common two-word window.
  The worst case over finite scales is 529 bits, 17 words (Codex).

| target | time | binding |
|---|---:|---|
| B300 | 0.22 ms | SIMT, 7x over tensor |
| B200 | 0.24 ms | SIMT |
| H100 | 0.51 ms | SIMT |

- **Faster variant [INFERRED]:** use `mxf4` with hardware scales, certified per tile. It needs scale span +
  13 + log2(chunk/32) < m **and** absolute FP32 range; span alone fails at 2^-127 scales (Codex).

### (e) RNS NTT for dark learning (N = 16,384, L = 4, P = 128 polynomials, forward)

| target | best path | time | binding |
|---|---|---:|---|
| H100 | INT8 | 0.27 ms | HBM |
| B200 | INT8 | 0.11 ms | HBM |
| B300 | **FP16 byte digits** | **0.21 ms** | HBM. INT8 1.83 (tensor), FP8 nibbles 0.71 (SIMT promotion and reconstruction) |
| TPU v6e | INT8 | 0.55 ms | HBM, no VPU term |

- **The bounds hold at m = 24** (Codex sharpened them): |Y| ≤ 15,204,352 < 2^24 for byte digits, 124,928 <
  2^17 for nibbles.
- FP8 on B300 is the earlier "7.5x" idea. Promotion and reconstruction leave it at 2.6x over INT8. FP16 bytes
  give 8.7x.

## 3. What changed from F3-MODEL

1. **B300 prime path:** FP16 byte limbs, not FP4 base-13 or FP8.
2. **Binary tower on Blackwell:** FP4/FP8 0/1 parity path. It was "nothing / bit-sliced SIMT".
3. **The Tower256 GPU prover is arithmetic-bound.** The measured SIMT multiply is 12,000-17,400 op-eq (table)
   or 52,700 (bit-sliced), not 718. The tensor fixed-r route is the lever, at 10.6-19.6x per multiply and
   2.3-3.2x per proof (5.3x with tensor fine layers). F3-MODEL said hash-bound.
4. **m = 12, not 14, is the FP8 floor.**
5. **bf16 byte limbs are not spec-backed;** FP16 byte limbs are.
6. **MXFP4 recompute runs at the FP8 rate on SIMT scale handling, not at the FP4 rate.**

## 4. What is not established

- The `m` for QGMMA and tcgen05 FP8/FP4.
- The H100 BGMMA rate.
- That tcgen05 FP16 accumulates at m = 24.
- TPU int32 overflow semantics.
- The repack layout cost.
- Whether the fine NTT layers can be moved onto the tensor path.
- Lean: the Tower256 instance of `lazy_bilinear`, and any hardware refinement theorem. The proved bound
  carries one product of slack: `N + 1 < 2^m`, i.e. N ≤ 2^m − 2.

## 5. Revised probe list for initiative 17's paid hours ($30 vast.ai: B300 hour first, then H100)

All checks are decided on the host from exact integers, as in `mma_run.py`.

**B300 (priority order):**

1. **FP4 0/1 parity path (`mxf4`, unit UE8M0 0x7f):**
   - Run a cuBLASLt or CUTLASS `72a`-derived GEMM with A, B ∈ {0, 0x2} at K = 2^10 .. 2^20.
   - Check every output's integer count and its parity against numpy.
   - Record the first K where the count is inexact; that gives m for tcgen05 `mxf4`.
2. **FP8 0/1** (e4m3 `0x38`) through cuBLASLt with fast accumulation on and off: the same count and parity
   checks, giving m for tcgen05 `f8f6f4`.
3. **Bias-read check:** set C = 2^(m-1) and read raw bit 24 − m against the parity, for m from step 1/2.
4. **FP16 byte-limb BabyBear^8 inner product** (cuBLASLt f16 → f32, K = 258 per batch, promoted):
   bit-exact against numpy, plus bytes/s against copy. This is the rotation's B300 prime path.
5. **Peak rates:** INT8 (expect 1/30 FP8), FP8, FP4 `mxf4`, FP16; and copy bandwidth.
6. **Tower256 fixed-r multiply** as a dense 0/1 GEMM (data N × 256 unpacked, M_r 256 × 256), with parity
   repack: ns per element against the T4 table rate. Spec for the kernel is §2(b).

**H100:**

1. wgmma rates IGMMA / QGMMA / HGMMA / **BGMMA `and.popc`** (`rates_sm80.wg_*`). BGMMA ≥ 4x IGMMA makes the
   b1 path the Hopper binary unit.
2. QGMMA m (count and gap probes, integer addends) and the bias read on HGMMA and QGMMA.
3. FP8 0/1 parity through cuBLASLt (as B300 step 2).
4. TensorZKP-shape INT8 inner product against copy (acceptance 1.5x).

**Free (Kaggle T4), before the paid hours:**

- the bit-sliced Tower256 multiply: **done** (§8 of TOWER256.md, 52,700 op-eq; the baseline is now the
  measured table, 12,000-17,400);
- the INT8 0/1 fixed-r Tower256 multiply on T4 (dense 0/1 GEMM plus parity repack), measured against the
  table kernel in the same session. It is the first real test of §2(b)'s 7.4x (b1 xor) / 2.8x (INT8)
  prediction, and it is free;
- the FP16 0/1 parity path with the bias read (m = 24 measured, so it is a live check of the trick).

**Dropped:** the emulated Blackwell b1 rate (decision made), and the probe.cu e4m3 `mma.sync` C path on
sm_90+ (it measures HMMA).
