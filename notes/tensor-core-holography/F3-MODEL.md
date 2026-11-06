# F3: field kernels as tensor-core MMA work, counted (initiative 14), 2026-11-06

- Script: `notes/construction-search/mma_counts.py` (stdlib, `python3 -I`); also `space.py --hw-axis`.
- Lean: minidregg branch `lane/mma-exact`, `Theory/MmaAccumulatorExact.lean`. Core Lean only; checks
  standalone with lean v4.35.0; axioms at most `propext` and `Quot.sound`.
- GPU protocol: degg-research `experiments/mma-accumulator-probe/`.
- Audit: one Codex (gpt-6-astra) adversarial pass on the model and the Lean. Every finding is accepted and
  repaired below; the findings that changed a verdict are marked (Codex).
- Tags: [READ] [MEASURED] [INFERRED] [CLAIM] [A].

## 1. Verdicts

1. **TensorZKP's inner product and scalar-vector are consistent with HBM-bound kernels** [INFERRED, model].
   - At 2^25 with BabyBear^8 (32 B/element), the inner product moves 2.15 GB, which takes 0.64 ms at
     3.35 TB/s. Its 3.4e10 INT8 MACs take 0.035 ms at peak, so the tensor cores are ~4% busy.
   - Measured over the model floor: 1.32 (inner product) and 1.41 (scalar-vector).
   - Degree-2 sumcheck, counted as their Algorithm 1 literally (four inner products; two scalar-vector
     products per fold): **1.17, but only under a fused-read schedule the paper does not publish.**
     Streaming the four products separately would need 15.03 GB, an HBM floor of 4.49 ms, which is above
     the measured 4.04 ms. Either they fuse, or the model is wrong (Codex).
   - The zero-check (16.96 ms) is not a check. Its eq·q_M·w_a·w_b term is degree 4.
   - The 215 ms end to end is not reproduced: the perm-check's GKR schedule is not given at count level.
   - Low MAC utilisation alone does not identify the bottleneck (Codex). The GPU protocol measures it.

2. **No single prime-field format wins on Blackwell; the decider is bytes and SIMT encode, not TOPS.**
   [INFERRED, scenario table in the script] Degree-2 sumcheck at 2^25, BabyBear^8, with FP partials
   promoted to INT32 at m = 14. Storage is either canonical coefficients in HBM, or limbs in HBM:

   | SKU | INT8 | FP8, canonical | FP8, limb | FP4, canonical | FP4, limb |
   |---|---|---|---|---|---|
   | H100 | **3.21 ms** (HBM) | 4.15 (SIMT) | 6.41 | n/a | n/a |
   | B200 | **1.34** (HBM) | 1.92 (SIMT) | 2.68 | 3.49 (SIMT) | 1.51 |
   | B300 | 2.98 (tensor) | 1.78 (SIMT) | 2.68 | 3.22 (SIMT) | **1.51** (HBM) |

   - On B300, FP4 base-13 with limbs stored in HBM (36 B/element) leads FP8 by 1.18x.
   - That lead rests on two assumed costs, both of which the probe measures:
     - the encode cost per limb (4 ops for FP4 and 1 for FP8, [A]); at 3 ops per FP4 limb, canonical
       FP4 ties FP8 (Codex);
     - the unpublished `tcgen05` accumulator width.
   - Earlier draft: "FP8 is the B300 format; FP4 loses on encoding". That is withdrawn. It charged
     pre-encoded FP8 its canonical 32 bytes when it actually needs 64 (Codex).

3. **Exactness per shape** (script table; Lean §2):
   - u8 limbs into `.s32`:
     - signed read: 33,025 products (TensorZKP eq. 23);
     - unsigned (zero-extended) read: 66,051 (`s32_unsigned_exact`, `u8_unsigned_bound`);
     - partial sums are irrelevant: wrapped intermediates still give the exact final residue.
   - GF(2) bits (`.s8` 0/1 operands, or `.b1 and.popc`): **unbounded under a parity read**.
   - e4m3 base-16 limbs: 18..37,282 products under PTX 9.2's "higher than half, lower than single"; 72 at
     m = 14.
   - e2m1 base-13 limbs: 255 at m = 14, 262,143 at m = 24.
   - **Promotion:**
     - Integer promotion every K_p ≤ (2^m - 1)/P products makes the FP4 block N·64 < 2^31. The 14-bit
       accumulator caps the promotion interval; it does not kill the design.
     - Cost: 3 ops (scale the doubled-E2M1 1/4, cvt, iadd) per accumulator per promotion. For
       BabyBear^8 FP4 that is 5,184 accumulators, about **61 ops per element pair at K_p = 255**, not
       "about one" (Codex). The script charges it.
     - Promotion cannot recover bits lost to alignment, so the measured `m` must be the alignment width.
   - Folds by a sampled challenge, as a precomputed multiply-by-r matrix, sum ≤ k·L products per
     accumulator. They are exact on every kind at m = 14.
   - TensorZKP's own C-matrix layout sums ≤ kL = 32 products per accumulator (2,080,800 < 2^31), not L
     (Codex).

4. **The bound is sufficient, and the first failure is found by exact search, not by formula** (Codex
   caught the formula):
   - FP4 encoder (P = 64), m = 14: bound 255, 256 still exact (2^14 is representable), first failure 257
     (256·64 + 1).
   - FP8 (P = 225), m = 14: bound 72, first failure 73 (73·225 = 16,425 needs 15 bits).
   - Lean falsifier at m = 7: [64, 64] exact, [64, 64, 1] fails.

5. **Binary tower on tensor cores needs a 1-bit MMA; with byte or nibble operands it loses to bit-sliced
   SIMT** [INFERRED].
   - The algebra holds. A GF(2^k) inner product is a bit outer-product sum, read for parity and reduced
     once by the fixed bilinear map. Karatsuba commutes with that lazy reduction at every tower level,
     because the Fan-Paar step `(U+V, W+U+V+gV)` is GF(2)-linear in U, V, W (Codex, citing minidregg
     `Theory/BinaryTowerFanPaar.lean:235`). Tower256 at 16-bit pieces costs 20,736 bit-MACs per product.
   - The cost is the operands. Spreading packed bits into 0/1 bytes costs about 4 ops per 4 output bytes
     (shift, and, multiply by 0x00204081, and with 0x01010101; Codex). Degree-2 Tower256 sumcheck at 2^25:
     - H100, INT8 0/1 operands: 21.8 ms, bound by the unpack;
     - bit-sliced SIMT alone: 7.2 ms [A: 718 ops per multiply];
     - A100 `b1` (no unpack): 5.3 ms, HBM-bound.
   - So the H100 decision rests on one unpublished number, the `wgmma .b1` rate. Blackwell's `tcgen05` has
     no 1-bit kind [READ PTX], so its binary-tower path is legacy `mma.sync .b1` or nothing.
   - 16x16 pieces pad 4x on a wgmma M = 64 tile; `mma.sync m16n8` fits.
   - DATE'26 SumCATS (A100, GF(2^128), no tensor cores) sits ~83x above the `b1` HBM floor. That is how far
     its SIMT kernel is from HBM, not proof that an MMA mapping closes the gap (Codex).

6. **The Tower256 FRI prover is hash-heavy; how heavy rests on two assumed op counts** [INFERRED].
   - Keccak-f is ~4,320 int32 ops with LOP3 [D]. Theta is the only step that does arithmetic (rho and pi
     permute bits, iota is affine). As a dense GF(2) GEMM, theta loses 240x at INT8 peak. That rejects the
     dense mapping, not every mapping (Codex).
   - With the Tower256 multiply at 718 SIMT ops [A], the hash share is 65-73% and the tensor column buys
     1.00-1.02x.
   - At 4x that multiply cost, the hash share falls to 32-40% and the GF(2^32)-basis tensor column buys
     **1.8-2.1x**.
   - The additive NTT is tensor-friendly only if the statement's basis lies in a small subfield (GF(2^32)
     twiddles: 8,192 bit-MACs per butterfly instead of 65,536; general twiddles pad to 1.6%). That is a
     statement-design lever.
   - The Keccak-f rate and the bit-sliced multiply rate are steps 6-7 of the GPU protocol.

## 2. Lean statements (`Theory/MmaAccumulatorExact.lean`, all checked)

- **`hw_exact`.** A post-addition rounding machine over any summation tree. For any `rnd` with
  `HoldsBelow m rnd`, products bounded by `P` and `size·P < 2^m`, the hardware sum equals the exact sum.
  The bound is derived per subtree.
- **`groupAdd` / `group_exact`.** The multi-term fused adder (Fasi et al.): addends aligned to the group's
  largest exponent before adding. Exact when every addend and the result are below `2^m`, because the
  quantum is then 1. This answers the Codex objection that `rnd` alone cannot express pre-addition
  alignment. Witnesses: `group_inside` (non-vacuity) and `group_fails_outside` (128 + 1 → 128 at m = 7).
- **`trunc_holdsBelow`** and the m = 7 falsifiers.
- **Integer wrap.**
  - `hwWrap_eq`: the register is the exact sum mod 2^32, in any order.
  - `s32_signed_exact` needs a nonnegative total. `s32_unsigned_exact` and `u8_unsigned_bound`.
  - `tensorzkp_bound` and `s32_signed_fails_past_bound`.
  - `s32_parity_exact`, with `parity_through_wrap` as the witness. That witness uses large leaves; a
    witness from u8-legal products only would need ~66k leaves.
- **`kar_lazy_commutes`.** Bit-coordinate Karatsuba middle term only. The tower-level statement with the
  `gV` term is stated in the docstring and **not proved**.
- **Scope.** None of this is a tensor-core refinement theorem. The measured `m` (alignment width per SKU,
  kind and path) is the premise that connects it to a real tensor core.

## 3. What would refute this

- A primitive the model calls HBM-bound running more than 2x above copy bandwidth.
- A measured `m` that breaks a block the script uses.
- Keccak-f or the bit-sliced multiply rate more than 2x off the assumed counts.
- A `wgmma .b1` rate near INT8's (then Tower256 on Hopper stays unpack-bound or SIMT).
