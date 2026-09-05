# Reply to GPT-6-Astra — what we checked, what we priced, what we are asking next

Written 2026-09-05 after one night against your answer to `ASTRA-ALGEBRA-PROMPT.md`.
Paste everything below the line. Same rules as before: every claim we make carries
[VERIFIED] (re-derived or run here), [LANE] (a subagent priced it, note named),
[READ] (checked at source), or [OPEN].

---

Thank you. We read your answer adversarially, as promised, and it held up better than
our own prompt did. Here is the ledger, then the questions.

## 1. What you corrected in us

- **[VERIFIED] The dual-mode parameter line in our prompt was our transcription error,
  not your misreading.** The hash-state ring is `Z_q[X]/(X^16 + 1)`, `q = 2^64 − 257`
  prime, `q ≡ −1 (mod 32)`, eight quadratic CRT factors, τ = 2 the component degree,
  the diagonal `F_{q²}` (2^128) the sampling set. Your `ord_8192(q) = 32` is right for
  N = 4096, a ring the design never uses for the hash. Your instruction to name the FHE
  dimension and the commitment dimension separately was correct and the prompt now does.
- **[VERIFIED] Our "matches what tensor cores physically do" was overstated.** TPUs
  accumulate BF16 products in FP32; `RN32(RN32(2^24 + 1) − 2^24) = 0` with
  BF16-representable operands where exact gives 1. The block-float spec is ours,
  chosen for soundness; the executable numerical contract must be frozen. Folded.
- **[VERIFIED] "Lattice norms do not exist in characteristic 2" is too strong** as a
  sentence; the honest obstruction is compatibility with the short-integer relation.
  Wording only; the Neo-versus-binary verdict stands.
- **[READ, LANE] Lova (2024/1964) and the Neo implementations** were missing from our
  record. Both now in.

## 2. What we priced from your syntheses

**Synthesis C, the inert Φ_{3⁸} tower** [LANE, `notes/inert-cyclotomic-tower.md`,
script exhaustive at conductors 27 and 81; and the exceptional-set lemma is now a Lean
theorem in our tree, general over any local hom into a field, with the cyclotomic
instance proved up to conductor 6561 by kernel `powMod`]. Your algebra is exactly
right: residue field `F_{2^4374}`, `C(4374,16) ≈ 2^149` pairwise-unit challenges of
canonical norm 16 living inside the FHE ring, coefficient operator norm 2h, an Ajtai
commitment linear over the challenge subring, folding with a non-dividing extractor at
expansion exactly 2h and a no-wrap budget of `2^42 − 1` folds. And it fails as a
single substrate on the cost you did not price: **every non-challenge proof message
is a dense element of GR(2^64, 162), 1,296 bytes and 4,323 u64 multiplications per
product against 16 bytes and 9 to 16 for BabyBear-Ext4 — 270 to 480×, bilinear floor
20×, 65 GB of round-2 sumcheck tables at v = 25.** Sparsity saves at most 2× and only
on the folds. Short inverses provably do not exist [READ, AL21 Thm 2 / Prop 12:
subtractive sets over Z[ζ_{p^ℓ}] have size ≤ p = 3]. FHE at q = 2^64 there is standard
and one multiplicative level shallower than our deployed point. Label: trap as a
single substrate. Three by-products outrank it: committing to the ciphertext in its
own ring, where the ct×ct identity is checkable at 5.5× the cost of performing it
against ≥ 618× on our deployed route; the slack 3 in odd-conductor differences is a
unit mod 2^64; and a priced module-BKZ bill (Δβ ≈ −17, about −4.9 bits) for our open
lattice item.

**Synthesis B, Z/2^k + Galois rings + Lova** [LANE, `galois-ring-stack.md`,
`lova-neo-rmfe-read.md`]. Trap as one algebra, for the residue-field reason you also
gave: 1/64 soundness per challenge bit, local negacyclic ring with challenge sets of
size ≤ 2, T-function hashes with bit-plane preimages (our kill test ran: 10/10
preimages of an 8-round Rivest-S-box hash over Z/2^32 in 160 evaluations). Lova is
the repetition escape and we read it at source: q = 2^64 literally, unstructured
Ajtai, ternary challenges whose extractor never inverts 2, (2/3)^t soundness at
t = 330, 16–47 MB and 702–3,244 s per fold, verifier ≥ 7.4·10⁶ Z_{2^64} constraints —
about 740× Nova by constraint count. Your RMFE toy verified by brute force (degree 2
on all 16⁴ pairs over Z/16, degree 3 fails 1,279 of 2,000) and is the paper's own
Corollary 1 example; rates over Z_{2^ℓ} are 0.279 at D = 2. It softens the witness
blow-up and never beats a base-ring witness.

**Your §7 ideal-quotient hazard** [LANE, run at the real modulus, all eight CRT
ideals, `notes/dual-mode-ideal-quotient-gate.md`]. Both of our full-mode candidates
escape as whole permutations. But you were more right than you knew: **σ₃₁ = σ_q is
literally the Frobenius `x ↦ x^q` on R_q, a ring polynomial, so 14 of 30 σ-Poseidon
rounds respect the CRT slots and rounds 8–11 compose to a slot-diagonal 4-round
permutation.** The escape is the σ₅/σ₂₅/σ₁₇ layers. A cost row was mis-counted as a
consequence (the σ-cost law counted a Frobenius class as a new slot). The gate is now
a standing item with a script and a Lean-shaped Prop `∀ i, ∃ x y, x ≡ y [mod I_i] ∧
F x ≢ F y [mod I_i]`.

**Synthesis A (exact digit-tensor engine) and D (secret-shared dark training)**:
[OPEN], not priced. The byte-tile-exact-in-BF16/FP32 lemma (256·255² < 2^24) is
verified; your §11 points on access-pattern leakage, forks, and rollback are folded as
obligations for the dark-training design, not as an algebra question.

**What you got wrong.** The union bound `2^47 × 2^−73 = 2^−26`: T = 2^47 is our norm
wall on fold count, not a count of failure opportunities; the per-step composition
you worried about is the (t+k)·ε the tree already proves. "Neo has research
implementations" turned out true [LANE]: Nightstream (Lean + Rust) and two PoCs.

## 3. Two things we found that you did not ask about, and that bear on your §4

- **[VERIFIED, Lean, 9 pinned theorems] The round bound for additive-commitment
  folding is false for every extractor.** The zero-absorb attack: a genesis
  commitment to a witness just above the norm bound, then absorb a zero; the extended
  state contains it, the prefix state is empty, binding pins any short opening to it,
  and the round event fires at every challenge, forcing error 1. Discharged at a toy
  and at our production parameters. So every "fold is knowledge-sound with extractor
  ε_MSIS" statement in the single-transcript model is vacuous below error T. The
  extractor that can exist carries the running opening plus all T absorbed openings,
  un-folds linearly on a descending budget, and has error 0 unconditionally — at the
  price that the decider checks T + 1 openings and capacity halves to 2^46 − 1. In
  our vocabulary: **knowledge soundness costs exactly the compression, and rewinding
  buys it back, and our tree has no rewinding.**
- **[LANE, `nightstream-read.md`] Nightstream's Lean is a paper twin plus R1CS layout**
  (5,621 theorems, 0 sorry, 185 `native_decide`, no Fiat–Shamir, BCS, Merkle or depth
  theorem), and its 09-04 branch carries SuperNeo's recursive step cost as a Lean
  theorem: **27,537,894 R1CS rows**, about 2,750× Nova by their own intro figures.

## 4. What we are asking you next

1. **Rewinding-free knowledge for additive folding.** Given the falsity above, what is
   the cheapest knowledge argument for Ajtai-commitment folding that a
   single-transcript, state-restoration-style compiler (ours is RBR → Fiat–Shamir at
   (t+k)·ε, no forking lemma) can carry? Is there a construction where the extractor
   needs only the transcript plus a bounded number of extra openings independent of
   T, or is "carry T+1 openings" tight in that model? Name the theorem you would want
   us to prove, with witness and falsifier.
2. **Sparse-message sumcheck over the inert tower.** The tower dies on dense
   GR(2^64,162) messages. Is there a sumcheck variant whose round polynomials and
   folded witnesses stay in a small subring or in a sparse basis while the challenges
   come from the 2^149 set — via RMFE decode-after-round, via a "rounds over the
   subring, lift once" schedule, or via anything else — and what does it cost per round
   in u64 multiplications? If the floor is genuinely the bilinear complexity of the
   subring, say so and we retire the candidate.
3. **Commit-to-the-ciphertext.** An Ajtai commitment over the FHE ring itself makes
   the ct×ct identity checkable at 5.5× the cost of performing it. Is there a complete
   protocol in the literature for "prove I performed this BFV multiplication" against
   such a commitment with a concrete verifier count, and what does the rescale
   ⌊t·x/Q⌉ cost there (our cross-limb Hole B)?
4. **The Frobenius classes.** For R_q ≅ (F_{q²})^8 (or in general (F_{q^τ})^{d/τ}),
   characterize exactly which σ-layer exponents are ring-polynomial (the Frobenius
   classes) and whether a permutation whose rounds are slot-respecting in a proper
   subset carries a known attack shape (a differential or integral distinguisher that
   rides the slot-diagonal rounds). We have the empirical rates; we want the theorem.
5. **A lattice fold at 2^−128 per step without repetition.** Lova pays t = 330
   ternary repetitions; Nightstream's step is 27.5M rows. What challenge set and
   extractor pair gives per-step knowledge error ≈ 2^−128 in a single transcript over
   a structured ring at ~2^64 modulus, and what is its expansion factor and verifier
   count? Your inert-tower challenges are the obvious candidate; the extractor is the
   question, per item 1.
6. **The executable numerical contract.** You demanded it and you were right. What is
   the minimal experiment that pins a real TPU or H100 kernel's reduction order and
   rounding points well enough that `ExactKernelRefinement` can be stated against it,
   and which published kernel (CROSS, Jaxite, cuBLAS) already documents its order?

Same deliverable shape as before: per item, the strongest true statement, the
refutation if there is one, the Prop you would have us prove, and what you could
not check. We will run the checks.
