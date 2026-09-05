# The joint-algebra question, answered by a stronger reader — and what survived our checks

2026-09-04/05. Ember posed `swarm/ASTRA-ALGEBRA-PROMPT.md` to GPT-6-Astra and pasted its
answer; this is the adversarial read. Provenance legend: **[VERIFIED]** re-derived or run here ·
**[LANE]** priced by a lane the same night (note named) · **[READ]** its citation checked at source
· **[WRONG]** refuted · **[OPEN]** not checked.

## 0. Verdict

Astra's central move — *discard the assumption that the shared object is a ring; share the
exact tensor computation and its certificates* — is the same law the two negative candidates
had taught an hour earlier (`SLVG_THOUGHT.md` §IV-l: alignment of structure is worth zero until
the proved relation uses the structure), stated from the constructive side. Its one genuinely new
algebraic object, the inert 3⁸ cyclotomic tower, dissolves the Galois-ring obstruction exactly as
claimed and then fails on the cost of dense proof messages [LANE]. Four candidates priced in one
night (M31 circle, Z/2⁶⁴, inert 3⁸ tower, and the dual-mode we hold), four negatives as a single
substrate, each leaving by-products worth more than the candidate. **VERDICTS §7.2 carries the
facts; nothing in §7 moved.**

## 1. What it corrected — in us

- **[VERIFIED] The dual-mode parameter line in the prompt was OUR transcription error.** The hash
  ring is `Z_q[X]/(X^16+1)`, `q = 2^64−257` prime, `q ≡ −1 (mod 32)`, eight quadratic factors, τ=2
  the CRT-component degree; I had written "X^N+1 splitting into τ=2 factors" at N=4096. Astra's
  `ord_8192(q) = 32 → 128 factors of degree 32` is right for a ring the design does not use.
  Prompt corrected 20e9493.
- **[VERIFIED] `docs/the-position.md`'s "matches what tensor cores physically do" was overstated.**
  TPUs accumulate BF16 products in FP32; `RN32(RN32(2^24+1) − 2^24) = 0` with BF16-representable
  operands where exact gives 1. The block-float spec is ours, for soundness; the executable
  numerical contract must be frozen. Caveat folded 20e9493.
- **[VERIFIED] "Lattice norms do not exist in characteristic 2" is too strong** as a sentence; the
  honest obstruction is compatibility with the short-integer relation (2e_i ∈ Λ_A). Wording only;
  the Neo-vs-binary verdict stands.
- **[READ, LANE] Lova (2024/1964) and Neo implementations** were missing from our record —
  `notes/lova-neo-rmfe-read.md`; VERDICTS §3c scoped, neo-verdict retired at its own location.

## 2. What it got right that we then priced

| synthesis | Astra's label | our lane | outcome |
|---|---|---|---|
| A — exact digit-tensor GEMM engine (CROSS 2501.07047, Jaxite) | real implementation unification | not priced (adjacent to `ntt-as-gemm.md`, `wgpu-fusion.md`) | **[OPEN]**; the byte-tile-exact-in-BF16/FP32 lemma (256·255² < 2²⁴) [VERIFIED] |
| B — Z/2^k + GR(2^k,d) + Lova | real research tower | `galois-ring-stack.md` (before), `lova-neo-rmfe-read.md` | trap as one algebra; Lova is the repetition escape at t=330 |
| C — inert Φ_{3⁸} tower | real algebraic alignment | `inert-cyclotomic-tower.md` + `galois-scripts/inert_tower.py` (PASS, exhaustive at 27/81) | **TRAP as single substrate**: residue field F_{2^4374} and 2^149 unit-difference challenges of norm 16 — all true — but every non-challenge proof message is dense GR(2⁶⁴,162): 1,296 B and 4,323 u64 mults per product vs 16 B / 9–16 for BabyBear-Ext4 (**270–480×**, bilinear floor 20×; 65 GB of round-2 tables at v=25). Folding works with a non-dividing extractor at expansion 2h, no-wrap budget 2^42−1; **short inverses provably do not exist** (AL21: subtractive sets over Z[ζ_{p^ℓ}] have size ≤ p = 3). FHE at q=2⁶⁴: standard, ≈230–260-bit RLWE, **depth 1** vs deployed 2 (+4.9 bits short), ct×ct 1.3–2.2× slower than the RNS-NTT |
| D — secret-shared dark training (SPDZ2k) | explicit non-collusion relaxation | not priced | **[OPEN]**; its access-pattern / fork / rollback points are additive to `docs/DARK-TRAINING.md` (folded as a pointer) |
| §7 ideal-quotient hazard | elementary, before indifferentiability | `dual-mode-ideal-quotient-gate.md` (ran at the real modulus) | both full modes escape as permutations; σ₃₁ is the Frobenius, 14/30 σ-Poseidon rounds are slot-respecting; τ=2 cost row mis-counted; standing gate in BRIEF 3 |

By-products that outrank the candidates [LANE]: commit-to-the-ciphertext (Ajtai over the FHE
ring itself, ct×ct identity checkable at 5.5× the cost of performing it, vs ≥618× on the deployed
route); the slack 3 in odd-conductor differences is a unit mod 2⁶⁴, retiring `galois-ring-stack`
§2's 2-adic bleed; a priced module-BKZ bill (2025/1904 eq. 1: Δβ ≈ −17 ≈ −4.9 bits) for
`sis-lattice-verdict`'s open item; and, from the earlier Z/2⁶⁴ lane, the BFV rescale is a shift at
a power-of-two modulus, so cross-limb Hole B is a range check in the TFHE/HPU world.

## 3. What it got wrong or overstated

- **[WRONG] The union bound `2^47 × 2^−73 = 2^−26`.** T = 2^47 is the norm wall on fold COUNT
  (binding lost at 2^47−1), not a count of failure opportunities; the per-step composition it
  worries about is exactly `AccRbrFold`'s (t+k)·ε, and no chain of 2^47 folds exists.
- **[OVERSTATED] "t = 2^20 alone does not imply degree ≤ 2."** Our §3 sentence is derived from the
  deployed noise budget with t=2^20 as an input; the prompt compressed it. No change.
- **[OPEN] "Neo has research implementations"** — turned out TRUE (Nightstream, two PoCs) [LANE].
- Its three Lean Props: `ShortExceptionalCyclotomicTower` is in flight in minidregg tonight
  (Theory/ExceptionalSetLocalRing.lean); `NormedBoundedDegreeTransport` (the RMFE degree-2
  witness) is verified numerically (`galois-scripts/rmfe_toy.py`) and unformalized;
  `ExactKernelRefinement` waits on the frozen numerical contract it correctly demands.

## 4. What we are not asking that we should be (its §11, our reading)

The private persistent state machine — weights, optimizer, RNG, memory, epoch → new state +
authorized outputs — is the object dark training must specify; hiding router selections in a
witness does not hide which expert's memory was fetched; copying an encrypted state permits forks.
None of these is an algebra question, which is Astra's point and now ours.
