# Initiative 14 grounding: tensor-core field experiment (F3) and holography accumulation (F4)

2026-11-06. Lane: initiative 14 (`whatember/INITIATIVES.md`). Tags: [READ] inspected source, [MEASURED] we
ran it, [INFERRED] derived here, [CLAIM] someone's assertion we have not checked.

## 1. What exists, and what this lane does with it

| object | where | state | this lane |
|---|---|---|---|
| MMA limb model (INT8 / FP8-E4M3 / FP4-E2M1 base 13, four primes) | `degg-research/experiments/mma-field-mapping/` | [MEASURED] rerun 2026-11-06: output byte-identical to `RESULTS.txt` | **reused** as the prime-field limb layer; its numbers (16 / 64 / 81 products, break-even 4.00 / 5.06, N = 33,025 / 262,143 / 255) are asserted by the new model, not recomputed differently |
| Accumulator contract R2a-R2c | `redregg/designs/SILICON-THEOREM-REPAIRS-2026-11-06.md` | PROPOSED, unbuilt | **extended**: per-shape exactness with an arbitrary (unspecified-order) summation tree, integer wrap, parity, and a promotion interval; checked as a core-Lean file |
| Ozaki base-13 identities | `obend/lean/Obend/Hardware/Accelerators.lean` (not `Obend/SiliconKernel.lean`: that path does not exist; the kernel file is `Lower/Proofs/SiliconKernel.lean`, the RTL node checker, unrelated to tensor cores) | [READ] ring identities over unbounded `Int` | spec side only; not built (owner's box) |
| Hardware axis of the construction space | `zkml-research/notes/construction-search/space.py` (`HARDWARE = [cpu, simt, tc]`, one H100 INT8 constant, GF(2^128) excluded from `tc`, holography overhead 0.25 a placeholder [A]) | live | **extended, not forked**: per-SKU, per-format tensor rows; GF(2) on tensor cores admitted; holography placeholder replaced by the F4 count |
| Tower256 additive-FRI prover counts | minidregg `docs/TOWER256-FRI-PROVER-WORK.md` (branch `lane/tower256-prover-exe` @ 107697663), `notes/construction-search/tower256_fri_counts.py` | [READ] prover ~4·2^ell Keccak-f, encode (n/2)·ell mults | **reused** as the binary-tower workload and the F4 leaf shape |
| HARDWARE.md, hpu-seam-study, VERDICTS §4b, §4c, §9, §9a | zkml-research | [READ] | §4b's 1.26x Amdahl ceiling and §9's "BAT not free for a fold is partly refuted" are the priors this lane tests |
| AccRbrFold / AccRbrBcs / AccRbrBcsShifted / Depth | minidregg `Selvage/` (1413 / 1121 / 588 / 2015 lines) | [READ headers] additive-alphabet accumulation with an MSIS residual; shifted BCS for lagging Merkle roots | F4 comparator; a helper lane reads them against 2026/538 |

## 2. Outside sources read for this grounding

- **TensorZKP, ePrint 2026/1250** (mirror PDF) [READ in full]. H100 SXM 80 GB, nvcc 12.6, **BabyBear extended to
  degree 8** (x^8 - 11; the method section says k = 4, the evaluation says k = 8), u8 limbs, so 32 bytes and 32 limbs
  per element. Inner product = `V^T U` (32 x N x 32), lazy reduction, chunk B = 32,768 under the INT32 bound
  N < 33,025, SINT64 cross-chunk sums. Fold = `V x C` with a 32 x 128 structured scalar matrix. Degree 3 uses SIMT
  Hadamard products g∘h and TC inner products. At 2^25: inner product 0.85 ms, scalar-vector 0.91 ms, degree-2
  sumcheck 4.04 ms, encoder 11.58 ms, end to end 215.28 ms (Table 1: perm-check 134.00, zero-check 16.96, encoder
  50.64, Merkle 8.59, open 6.30).
- **First count against those numbers** [INFERRED, to be scripted]: an inner product of two 2^25 x 32 B vectors
  moves 2.15 GB, which is 0.64 ms at 3.35 TB/s, while its 3.4e10 INT8 MACs take 0.035 ms at peak. TensorZKP's
  primitives are **HBM-bound with the tensor cores about 4% busy**. Their gain over SIMT is that the arithmetic left
  the critical path, not that MMA throughput was used. The model must therefore carry bytes, not only MACs.
- **Chimera 2026/1388** [READ abstract]: BN254 Spartan on SIMT, 1.27-1.64x end to end. Amdahl comparator only.
- **zkDuel arXiv 2610.37710** [READ abstract]: SIMT sumcheck kernels on H100 are "shaped not by bandwidth but by
  multi-limb arithmetic". Consistent with the above: on SIMT the arithmetic binds; on tensor cores it does not.
- **DATE'26 SumCATS** (Fan, Wu, Han, Arafin) [READ]: GF(2^128) tower, bit-sliced SIMT on RTX 3090 Ti and A100,
  **no tensor cores** ("future work"). n = 24, d = 2: 108.65 ms on A100; n = 28: 1.17-1.35 s. Per table entry this
  is ~50x TensorZKP's prime-field rate. The "different mapping" is therefore not a tensor-core mapping at all.
- **PTX ISA 9.x** (docs.nvidia.com, fetched 2026-11-06) [READ]:
  - integer MMA (`.s8/.u8`, `.b1 .and.popc`) accumulates in `.s32` and **wraps** unless `.satfinite`;
  - PTX 9.2 clarification: **`wgmma` with `.e4m3/.e5m2` inputs and `.f32` output accumulates "at higher than half
    precision but lower than single precision"**, which is NVIDIA's own statement of the DeepSeek-V3 ~14-bit
    observation;
  - FP16/BF16/TF32 accumulate "with at least single precision", order unspecified;
  - `wgmma ... m64n8k256 .s32.b1.b1.and.popc` exists (sm_90a); `tcgen05.mma` kinds are tf32, f16, f8f6f4, i8,
    mxf8f6f4, mxf4, mxf4nvf4: **no 1-bit kind on Blackwell's 5th-generation path**.
- **arXiv 2608.11693** (INT8 on Blackwell Ultra) [READ]: dense INT8 1,979 TOPS (H200), 4.5 POPS (B200), **0.15 POPS
  (B300, 1/30 of FP8)**; `tcgen05 .kind::i8` is not exposed on sm_103a. TensorZKP's INT8 design does not carry to
  B300.
- **Holography accumulation 2026/538** (mirror, August version; the SCN version may differ) [READ abstract]; full
  read delegated to the F4 helper lane, against our `Selvage/AccRbr*`.

## 3. Corrections to what we had (each will be landed or answered where it lives)

1. `space.py` inadequacy 4, "binary fields cannot do integer matmul natively": GF(2) matrix products run on integer
   or 0/1-valued FP MMA, with the parity bit read off. With an `.s32` wrapping accumulator the parity is exact for
   every block length (wrap is reduction mod 2^32, which preserves the low bit). This is the binary-tower mapping;
   it is a statement to prove, not a hope.
2. Governance critique W2 / repairs R2: "at 14 bits the FP4 point is probably dead" assumes no promotion. DeepSeek-V3
   promotes the tensor-core partial to FP32 CUDA-core registers every 128 elements; with an integer promotion the
   exact block becomes N·64 < 2^31 for FP4 base 13, at roughly one SIMT op per field-element pair. The 14-bit
   accumulator caps the promotion interval, not the design.
3. The break-even ratio 5.06 is per SKU: B200 has FP4/INT8 = 2 (FP4 loses); B300 has FP4/INT8 = 100 (INT8 is gone).
   But when the kernel is HBM-bound neither ratio decides: the binding term is bytes, then the SIMT cost of limb
   encoding (base-13 digit extraction is several times the nibble split of FP8 base 16).
4. Tower256 prover (FRI, one column) is Keccak-bound (~4·2^ell Keccak-f); Keccak-f has no profitable MMA form (theta
   is linear but 1600x1600 sparse with 11 ones per row; chi is nonlinear). Tensor cores bound the Tower256 prover by
   its non-hash fraction.

## 4. The bar, restated (and where I move it)

- F3 bar kept: a counts-exact model per (MMA shape, operand kind, accumulator), field and operation; validated
  against TensorZKP's published primitives and against `mma-field-mapping`; Pareto table; Lean exactness per shape
  with falsifiers. **Raised**: the model carries bytes and SIMT ops beside MMA ops, because TensorZKP's own numbers
  are bandwidth-bound, so a MAC-only model would "validate" against nothing. **Lowered honestly**: the 215 ms end to
  end cannot be reproduced from the paper (the perm-check's GKR layer schedule is not published at count level);
  the model validates the three primitives and bounds the zero-check, and says so.
- F3 kernel: no GPU granted. Deliverable is a probe-and-kernel protocol that runs in one hour (accumulator width per
  kind, inner product and fold at 2^20-2^25 against HBM peak, Keccak-f rate).
- F4 bar kept, with the leaf shape fixed to the Tower256 receipt at ell = 14..22 and a required answer on
  homomorphism for a hash-based PCS.

## 5. Not reused, and why

- `obend` is read, not built (its owner's box is bb2; heavy). Its `Int` identities are the spec side of the new
  exactness file; nothing here edits obend.
- MoMA / MORPH (VERDICTS §4b already dropped them from the tensor thread).
- `vast` and other `~/.ssh/config` hosts: not ours without ember's word; bb2 and persvati have no GPU.
