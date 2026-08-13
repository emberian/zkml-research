/-
# Selvage.AccExtract — [ACC-extract] advanced: KNOWLEDGE soundness of the γ-fold.

`Selvage/AccSound.lean` and `Selvage/LightClientSound.lean` bound the probability
that an accumulated claim verifies while some constituent is UNSATISFIABLE —
soundness at the resolution "∃ a word satisfying it". A skeptic's "sound" asks
for more: that a prover producing verifying folds KNOWS the witnesses — that a
straightline EXTRACTOR recovers the actual witness words from the prover's
committed folds, with no rewinding. This file builds that extractor for the
fold algebra and PROVES it recovers exact witnesses.

**The two-point erasure-extraction core** (WARP 2025/753 §4 + App. B's relaxed
RBR knowledge, rendered on `foldClaims`): the folded word at challenge γ is
`h = f + γ • g` (`foldClaims_satisfies`). Given folds of the SAME pair at TWO
distinct challenges γ ≠ γ', linear algebra inverts the fold:

    g = (γ − γ')⁻¹ • (h − h'),    f = h − γ • g.

* `extractPair` — that map, the two-point straightline extractor.
* `extractPair_sound` — it recovers `(f, g)` EXACTLY; with
  `fold_decomposition_unique`, the two-transcript witness pair is UNIQUE.
* `accKnowledgeSound` — the claim-level statement: two VERIFYING folds at
  distinct challenges yield, through `extractPair`, genuine witnesses
  satisfying the INDIVIDUAL claims `A` and `B`, plus the transcript-consistency
  identities `h = f + γ•g`, `h' = f + γ'•g`.
* `extractPair_peel₂` — the peel iterated backwards through a depth-2 fold:
  outer extraction recovers the inner folded word, inner extraction recovers
  the constituents — `Selvage/Depth.lean`'s Construction B.5 recursion (`wAt`:
  each level's extractor consumes the next level's output) realized on the
  fold algebra.

**Transcription notes (read before auditing):**

* **Straightline means no rewinding, and that is all it means here.** The
  extractor is a pure FUNCTION of transcript data — two folded words and two
  challenges — never a re-execution of the prover from a reset state. This is
  the same discipline as `Selvage/Depth.lean`'s `srExtract` (reads the output
  statement, messages, and final challenges; the game trace argument is
  unused) and `Selvage/LightClientSound.lean`'s schedule-pair extractor. How a
  SINGLE Fiat–Shamir execution furnishes the second evaluation that
  `extractPair` consumes — WARP's answer: the `t` opened columns plus erasure
  correction inside the mutual-agreement set, never a second run — is
  precisely the commitment-layer seam `[ACC-extract-bind]` below.

* **Two transcripts are necessary, not an artifact.** `extractPair_self`
  computes the diagonal collapse: at γ = γ' the difference vanishes and
  `0⁻¹ = 0` erases the second witness — the output is `(h, 0)` regardless of
  what was folded. And `single_fold_ambiguous` exhibits (over F₅) two DISTINCT
  witness pairs, each genuinely satisfying the same claim pair, with the SAME
  folded word at one challenge — no function of one verifying fold can return
  "the" witness. The γ ≠ γ' hypothesis is load-bearing information, exactly
  the information the commitment layer's opened columns supply.

* **The word is the knowledge object; the root is not.** Everything here
  consumes the folded WORDS `h, h'` as data. That the prover's committed root
  `rt` binds those words (Merkle/BCS binding, opened-column consistency,
  erasure recovery of the full word from `t` columns) is `[ACC-extract-bind]`
  — the fold algebra keeps `Root` opaque for exactly this reason
  (`Selvage/Accumulator.lean`'s module header).

* **`hshare` is the post-alignment state**, as in `foldClaims_satisfies`:
  WARP aligns both inputs to a common functional channel before folding; the
  extractor works at the same interface.

* **This is erasure extraction.** Recovering `(f, g)` from evaluations of the
  γ-linear combination at two challenge points is solving a 2×2 Vandermonde
  system — the degenerate-diagonal failure IS the vanishing determinant. This
  is the per-step algebraic content of WARP's "erasure correction only,
  available for every linear code" extraction route; no unique/list decoder
  appears anywhere.
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.LinearCombination
import Selvage.Accumulator
import Selvage.Depth

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r : ℕ}

/-! ## The two-point straightline extractor -/

/-- **The two-point straightline extractor**: from the folds `h, h'` of one
witness pair at challenges `γ, γ'`, recover the pair by inverting the fold's
linear algebra — `g := (γ − γ')⁻¹ • (h − h')`, `f := h − γ • g`. A pure
function of transcript data: no rewinding, no decoder, one field inversion. -/
def extractPair (h h' : ι → F) (γ γ' : F) : (ι → F) × (ι → F) :=
  (h - γ • ((γ - γ')⁻¹ • (h - h')), (γ - γ')⁻¹ • (h - h'))

@[simp] theorem extractPair_fst (h h' : ι → F) (γ γ' : F) :
    (extractPair h h' γ γ').1 = h - γ • ((γ - γ')⁻¹ • (h - h')) := rfl

@[simp] theorem extractPair_snd (h h' : ι → F) (γ γ' : F) :
    (extractPair h h' γ γ').2 = (γ - γ')⁻¹ • (h - h') := rfl

/-- **Soundness of the two-point extractor** — the load-bearing knowledge core:
if `h` and `h'` are the folds of ONE pair `(f, g)` at two DISTINCT challenges,
the extractor returns exactly `(f, g)`. Real field algebra (`(γ−γ')⁻¹` against
the fold difference); the γ ≠ γ' hypothesis is where the Vandermonde
determinant lives, and `extractPair_self` below shows its failure mode. -/
theorem extractPair_sound {h h' f g : ι → F} {γ γ' : F} (hne : γ ≠ γ')
    (hh : h = f + γ • g) (hh' : h' = f + γ' • g) :
    extractPair h h' γ γ' = (f, g) := by
  have hc : γ - γ' ≠ 0 := sub_ne_zero_of_ne hne
  have hg : (γ - γ')⁻¹ • (h - h') = g := by
    rw [hh, hh']
    have hd : (f + γ • g) - (f + γ' • g) = (γ - γ') • g := by
      rw [sub_smul]; abel
    rw [hd, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine Prod.ext ?_ hg
  show h - γ • ((γ - γ')⁻¹ • (h - h')) = f
  rw [hg, hh]
  abel

/-- Uniqueness of the two-transcript decomposition, immediate from
`extractPair_sound`: folds at two distinct challenges DETERMINE the witness
pair. Contrast `single_fold_ambiguous` below — one transcript does not. -/
theorem fold_decomposition_unique {h h' f g f₁ g₁ : ι → F} {γ γ' : F}
    (hne : γ ≠ γ') (hh : h = f + γ • g) (hh' : h' = f + γ' • g)
    (hh₁ : h = f₁ + γ • g₁) (hh₁' : h' = f₁ + γ' • g₁) :
    f = f₁ ∧ g = g₁ := by
  have h2 := (extractPair_sound hne hh hh').symm.trans
    (extractPair_sound hne hh₁ hh₁')
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- **The degenerate diagonal**: at equal challenges the extractor collapses —
`(γ − γ)⁻¹ = 0⁻¹ = 0` — and the output is `(h, 0)` REGARDLESS of the witnesses
folded into `h`. The division by zero is not hidden by the junk-value
convention: the second witness is erased unconditionally, so the
two-distinct-challenge hypothesis of `extractPair_sound` is load-bearing. -/
theorem extractPair_self (h h' : ι → F) (γ : F) :
    extractPair h h' γ γ = (h, 0) := by
  unfold extractPair
  rw [sub_self, inv_zero, zero_smul, smul_zero, sub_zero]

/-! ## Knowledge soundness of the accumulation step -/

section Fold

variable (foldRoot : Root → F → Root → Root)

/-- **Knowledge soundness of the γ-fold** — the [ACC-extract] upgrade at the
single-step level: a prover producing words that VERIFY the folded claim at
two distinct challenges yields, via `extractPair`, genuine witnesses
satisfying the INDIVIDUAL claims — `(extractPair h h' γ γ').1` witnesses `A`,
`.2` witnesses `B` — together with the transcript-consistency identities
(the extracted pair actually explains both folded words, so by
`fold_decomposition_unique` it is THE pair). This inverts
`foldClaims_satisfies`: completeness folds two witnesses into one; knowledge
soundness recovers the two from folds at two challenges. The root component is
untouched — binding the words to the prover's commitments is
`[ACC-extract-bind]`. -/
theorem accKnowledgeSound {C : Submodule F (ι → F)} {A B : AccClaim Root F ι r}
    {h h' : ι → F} {γ γ' : F} (hne : γ ≠ γ')
    (hshare : ∀ i, B.weights i = A.weights i)
    (hfold : AccClaim.Satisfies C (foldClaims foldRoot A B γ) h)
    (hfold' : AccClaim.Satisfies C (foldClaims foldRoot A B γ') h') :
    AccClaim.Satisfies C A (extractPair h h' γ γ').1 ∧
    AccClaim.Satisfies C B (extractPair h h' γ γ').2 ∧
    h = (extractPair h h' γ γ').1 + γ • (extractPair h h' γ γ').2 ∧
    h' = (extractPair h h' γ γ').1 + γ' • (extractPair h h' γ γ').2 := by
  have hc : γ - γ' ≠ 0 := sub_ne_zero_of_ne hne
  -- the channel equations of the two verifying folds
  have hch : ∀ i, (A.channel i).1 h = (A.channel i).2 + γ * (B.channel i).2 :=
    fun i => hfold.2 i
  have hch' : ∀ i, (A.channel i).1 h' = (A.channel i).2 + γ' * (B.channel i).2 :=
    fun i => hfold'.2 i
  -- the extracted second component meets B's channel (through A's shared
  -- functionals): the fold difference isolates (γ − γ')·τᵢ
  have hg : ∀ i, (A.channel i).1 ((γ - γ')⁻¹ • (h - h')) = (B.channel i).2 := by
    intro i
    rw [map_smul, map_sub, smul_eq_mul, hch i, hch' i]
    have hd : ((A.channel i).2 + γ * (B.channel i).2)
        - ((A.channel i).2 + γ' * (B.channel i).2)
        = (γ - γ') * (B.channel i).2 := by ring
    rw [hd, inv_mul_cancel_left₀ hc]
  -- the extracted first component meets A's channel: subtracting γ·τᵢ back out
  have hf : ∀ i, (A.channel i).1 (h - γ • ((γ - γ')⁻¹ • (h - h')))
      = (A.channel i).2 := by
    intro i
    rw [map_sub, map_smul, smul_eq_mul, hch i, hg i]
    ring
  -- code membership of both extracted words, by linearity of C
  have hgmem : (γ - γ')⁻¹ • (h - h') ∈ C :=
    C.smul_mem _ (C.sub_mem hfold.1 hfold'.1)
  have hfmem : h - γ • ((γ - γ')⁻¹ • (h - h')) ∈ C :=
    C.sub_mem hfold.1 (C.smul_mem _ hgmem)
  refine ⟨⟨hfmem, fun i => hf i⟩, ⟨hgmem, fun i => ?_⟩, ?_, ?_⟩
  · -- B's constraints, through the shared channel
    rw [hshare i]
    exact hg i
  · -- transcript consistency at γ
    show h = (h - γ • ((γ - γ')⁻¹ • (h - h'))) + γ • ((γ - γ')⁻¹ • (h - h'))
    abel
  · -- transcript consistency at γ'
    show h' = (h - γ • ((γ - γ')⁻¹ • (h - h'))) + γ' • ((γ - γ')⁻¹ • (h - h'))
    have hgh : (γ - γ') • ((γ - γ')⁻¹ • (h - h')) = h - h' := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc h' = h - (h - h') := by abel
      _ = h - (γ - γ') • ((γ - γ')⁻¹ • (h - h')) := by rw [hgh]
      _ = (h - γ • ((γ - γ')⁻¹ • (h - h')))
            + γ' • ((γ - γ')⁻¹ • (h - h')) := by
          rw [sub_smul]; abel

end Fold

/-! ## The backwards peel: iterating the extractor down a chain -/

/-- **The backwards peel at depth 2** — Construction B.5's recursion (`wAt`:
each level's extractor consumes the NEXT level's output) realized on the fold
algebra: extracting at the outer challenge pair recovers the inner folded word
`f + γ • g` (and the outer witness `k`); extracting at the inner pair then
recovers `(f, g)`. Two straightline applications, no rewinding at either
level. The unbounded-depth generalization is `[ACC-extract-chain]` below. -/
theorem extractPair_peel₂ (f g k : ι → F) {γ γ' η η' : F}
    (hγ : γ ≠ γ') (hη : η ≠ η') :
    extractPair
      (extractPair (f + γ • g + η • k) (f + γ • g + η' • k) η η').1
      (extractPair (f + γ' • g + η • k) (f + γ' • g + η' • k) η η').1
      γ γ' = (f, g) := by
  rw [extractPair_sound (f := f + γ • g) (g := k) hη rfl rfl,
    extractPair_sound (f := f + γ' • g) (g := k) hη rfl rfl]
  exact extractPair_sound hγ rfl rfl

/-- The depth-composition carrier the chain residual rides is PROVED upstream
(`Selvage/Depth.lean`, WARP Thm B.4 repaired): cited here so the import is
load-bearing and `[ACC-extract-chain]`'s realizer is checkable. -/
example : OB2_depth_composition_nonneg := OB2_depth_composition_nonneg_proved

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT and computing over `RS[F₅, {0,1,2,3}, 2]`, reusing
`Selvage/Accumulator.lean`'s `AccExample` vocabulary (`xWord`, `oneWord`,
`evalA`, `evalB1`, `fold_honest_nonzero`, `trivialRoot`):

* **satisfiable / the extractor computes** — `extract_recovers`: from the two
  folds of the honest pair `(xWord, oneWord)` at challenges 1 ≠ 2, the
  extractor returns exactly `(xWord, oneWord)`, by `decide` (the field
  inversion `(1−2)⁻¹ = 4` computed in the kernel, not routed through
  `extractPair_sound`).
* **premise inhabitation** — `knowledge_fires`: `accKnowledgeSound` fires
  non-vacuously — every hypothesis discharged by built objects
  (`fold_honest_nonzero` at challenges 1 and 2), the conclusion delivering
  satisfaction of the INDIVIDUAL claims `evalA`, `evalB1`.
* **teeth, the diagonal** — `extract_teeth_diagonal`: at γ = γ' the extractor
  does NOT return the witnesses (it returns `(h, 0)` — `extractPair_self`);
  the two-distinct-challenge requirement is load-bearing.
* **teeth, information-theoretic** — `single_fold_ambiguous`: two DISTINCT
  witness pairs, each satisfying the same claims, with the SAME folded word at
  one challenge — no extractor whatsoever succeeds from one fold; the failure
  at the diagonal is inherent, not an artifact of this extractor. -/

namespace AccExtractExample

open RSExample AccExample

/-- **Satisfiable / the extractor computes**: the two-point extractor recovers
the honest pair from its folds at challenges 1 ≠ 2, decided by kernel
computation over F₅. -/
theorem extract_recovers :
    extractPair (xWord + (1 : ZMod 5) • oneWord)
      (xWord + (2 : ZMod 5) • oneWord) 1 2 = (xWord, oneWord) := by
  decide

/-- **Premise inhabitation**: `accKnowledgeSound` fires on concrete verifying
folds — the honest accumulator × link pair of `Selvage/Accumulator.lean`'s
keystones folded at challenges 1 and 2 yields, via `extractPair`, genuine
witnesses for the individual claims `evalA` and `evalB1`. -/
theorem knowledge_fires :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA
      (extractPair (xWord + (1 : ZMod 5) • oneWord)
        (xWord + (2 : ZMod 5) • oneWord) 1 2).1 ∧
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalB1
      (extractPair (xWord + (1 : ZMod 5) • oneWord)
        (xWord + (2 : ZMod 5) • oneWord) 1 2).2 := by
  have hne : (1 : ZMod 5) ≠ 2 := by decide
  have hshare : ∀ i, evalB1.weights i = evalA.weights i := fun _ => rfl
  have h := accKnowledgeSound trivialRoot hne hshare
    (fold_honest_nonzero 1) (fold_honest_nonzero 2)
  exact ⟨h.1, h.2.1⟩

/-- **Teeth, the diagonal**: at equal challenges the extractor FAILS on the
honest instance — the γ = γ' collapse (`extractPair_self`) cannot separate the
witnesses. Exhibited by computation. -/
theorem extract_teeth_diagonal :
    extractPair (xWord + (1 : ZMod 5) • oneWord)
      (xWord + (1 : ZMod 5) • oneWord) 1 1 ≠ (xWord, oneWord) := by
  decide

/-- **Teeth, information-theoretic**: the diagonal failure is inherent — two
DISTINCT witness pairs (`(xWord, oneWord)` and `(2•oneWord, xWord − oneWord)`),
each genuinely satisfying the same claim pair `(evalA, evalB1)` over the code,
fold to the SAME word at the single challenge γ = 1. No function of one
verifying fold can return "the" witness pair; the second transcript (in
deployment: the opened columns, `[ACC-extract-bind]`) is what breaks the tie. -/
theorem single_fold_ambiguous :
    ∃ f₁ g₁ f₂ g₂ : Fin 4 → ZMod 5,
      (f₁, g₁) ≠ (f₂, g₂) ∧
      f₁ + (1 : ZMod 5) • g₁ = f₂ + (1 : ZMod 5) • g₂ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA f₁ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalB1 g₁ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA f₂ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalB1 g₂ := by
  refine ⟨xWord, oneWord, (2 : ZMod 5) • oneWord, xWord - oneWord,
    by decide, by decide,
    ⟨xWord_mem, fun _ => q2_xWord⟩,
    ⟨oneWord_mem, fun _ => rfl⟩,
    ⟨Submodule.smul_mem _ _ oneWord_mem, by decide⟩,
    ⟨Submodule.sub_mem _ xWord_mem oneWord_mem, by decide⟩⟩

end AccExtractExample

/-! ## Residual obligations — prose, not stubs

Named residuals with their realizers; each becomes a real theorem, never a
`def : Prop := True` (the vacuous-obligation sin — audit discipline).

**[ACC-extract-chain]** — unbounded-depth iteration of the peel.
`extractPair_peel₂` realizes the backwards recursion at depth 2; the general
form is a single recursion over `Selvage/LightClientSound.lean`'s `Chain`:
upgrade `link_satisfiable_of_verifies_pair` (which extracts ∃-satisfiability
from schedule pairs differing at one link) to return the `extractPair`-built
witness of EVERY link from `n + 1` verifying schedules — the flat-schedule
rendering of WARP's per-step backwards extraction, with the same subtraction
algebra this file proves at the step level. The error composition across depth
is already PROVED: `OB2_depth_composition_nonneg_proved` (`Selvage/Depth.lean`,
WARP Thm B.4 repaired — `ε_sr ≤ (t+k)·ε_rbr`, loss-free, straightline), whose
`wAt`/`srExtract` chain is exactly the recursion `extractPair_peel₂` exhibits
algebraically; what remains is stating the chain extractor as that one
recursion and attaching it to the SR game's RBR knowledge states (adjacent to
`[LC-sound-fs]`'s FS transport).

**[ACC-extract-bind]** — commitment binding of the extracted word: the seam
between this file's algebra and the commitment layer, dual to `Selvage/Decider`'s
`[DEC-open]`. Everything here consumes the folded WORDS `h, h'` as transcript
data. In deployment the prover commits a Merkle root and reveals `t` opened
columns; the obligations are (a) binding — `rt` opens to at most one word
(Merkle/BCS collision-resistance, the `[FS-ROM]`-adjacent hash assumption);
(b) recovery — the full folded word is reconstructible from the `t` opened
columns by ERASURE CORRECTION inside the mutual-agreement set (WARP App. B;
mutual correlated agreement is PROVED at unique decoding in
`Selvage/CorrelatedAgreement.lean` — the erasure step rides it), which is also
what furnishes `extractPair`'s second evaluation within a SINGLE straightline
FS execution, no rewinding; (c) attribution — the recovered word is the one
`rt` binds, so the extracted witnesses attach to the prover's commitments,
not merely to algebraically consistent words. Until this lands, the honest
label for this file is: knowledge soundness AT THE WORD LEVEL — witnesses
recovered from and bound to the folded words, with the words' binding to the
roots the named seam.

## Ledger

* `extractPair` — the two-point straightline extractor, DEFINED (one field
  inversion, no decoder, no rewinding).
* `extractPair_sound` — PROVED: folds of one pair at distinct challenges are
  inverted exactly; `fold_decomposition_unique` — PROVED: the two-transcript
  witness pair is unique.
* `extractPair_self` — PROVED: the diagonal collapse `(h, 0)` — the γ ≠ γ'
  hypothesis is load-bearing, failure mode exhibited generically.
* `accKnowledgeSound` — PROVED: verifying folds at two distinct challenges
  yield genuine witnesses of the individual claims + transcript consistency.
* `extractPair_peel₂` — PROVED: the backwards peel iterates (depth 2), the
  `wAt` recursion shape on the fold algebra.
* Keystones — `extract_recovers`, `knowledge_fires`,
  `extract_teeth_diagonal`, `single_fold_ambiguous`: all by construction /
  `decide` over F₅.
* Residuals — `[ACC-extract-chain]`, `[ACC-extract-bind]` (prose above).
* `#print axioms accKnowledgeSound`: `propext`, `Classical.choice`,
  `Quot.sound`. -/

end Minidregg.Selvage
