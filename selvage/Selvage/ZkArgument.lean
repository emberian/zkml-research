/-
# Selvage.ZkArgument — [OB-4-hiding-rbr] gap (2): hiding and knowledge-soundness
coexisting in ONE straightline argument.

`Selvage/AccExtract.lean` built the straightline knowledge extractor for the
γ-fold (`extractPair`, needs the mask PEELABLE — two accepting transcripts at
distinct challenges). `Selvage/ZKHiding.lean` + `Selvage/ConstrainedMask.lean` built
the opening simulator (`MaskedOpeningHiding`, needs the mask to HIDE — a
uniform, witness-free opened tuple from ONE transcript). Read naively these
pull opposite directions: an extractor "sees through" the mask across two
runs while a simulator must show ONE run leaks nothing. This file states and
composes a single object, `ZkArgument`, that carries BOTH properties (plus
completeness) for the masked accumulator claim, and proves they coexist
NON-VACUOUSLY on one built instance — the tension resolves at the level of
QUANTIFIER POSITION, not by weakening either property:

* **Knowledge-soundness** ranges over a CHEATING PROVER's choice of a SECOND
  challenge `γ'` and a second accepting transcript `h'` — `∀ {h h' γ'}, γ ≠
  γ' → …`. Extraction is a fact about PAIRS of transcripts.
* **Zero-knowledge** is a fact about ONE transcript at the fixed challenge
  `γ` — `MaskedOpeningHiding M q γ` mentions no `γ'` at all, because the
  honest verifier the simulator fools never sees a second run.

Nothing in `MaskedOpeningHiding`'s statement depends on `A`, `B`, `foldRoot`,
or `extractPair`; nothing in `accKnowledgeSound`'s conclusion depends on the
query `q`. The two properties are proved from DISJOINT premises
(`Selvage/AccExtract.lean`'s fold algebra vs. `Selvage/ZKHiding.lean`'s MDS
interpolation) and combine into one structure by straight conjunction — the
NEW content here is exhibiting that combination non-vacuously: a single mask
draw that is simultaneously (a) a valid completeness witness
(`foldClaims_satisfies`), (b) exactly recovered by `extractPair` from two
transcripts, and (c) hidden by `MaskedOpeningHiding` at either transcript
alone. The keystones below build exactly that triple-witness instance, and
the teeth exhibit the properties genuinely pulling apart: at `γ = 0`
extraction still works but hiding is refuted (hiding is the binding
constraint, not knowledge); with only ONE transcript, extraction is
information-theoretically impossible (`single_fold_ambiguous`-style) while
hiding of that same transcript still holds (zero-knowledge needs no second
run).

**The bridge this file supplies.** `Selvage/ZK.lean`'s `mask_bijOn` draws the
mask from `satWords C B` — the mask CLAIM's satisfying set (an `AccClaim`,
the vocabulary the fold algebra speaks). `Selvage/ConstrainedMask.lean`'s
`constrainedMask_hiding` speaks of `constrainedMaskSpace dom d pt` — a
`Submodule` (the vocabulary the reduction theorem `maskedOpeningHiding_of_surj`
needs). For a single-evaluation-constraint mask claim (weight `evalAtPt pt`,
target `0`) these are the SAME set, pointwise
(`mem_constrainedMaskSpace_iff_satisfies`) — the object `Selvage/AccExtract.lean`
peels is, on the nose, the object `Selvage/ZKHiding.lean`/`Selvage/ConstrainedMask.lean`
hide. That identification is what lets one `ZkArgument` instance cite both
without re-deriving either.

**Honest scope — what closes and what is `[ZK-RBR-game]`.** Every field of
`ZkArgument` is proved by CITATION (no re-derivation): completeness from
`foldClaims_satisfies`, knowledge-soundness from `accKnowledgeSound`,
zero-knowledge from `constrainedMask_hiding` (which itself rides
`maskedOpeningHiding_of_surj`). This closes gap (2) at the SINGLE-STEP,
SINGLE-ROUND level: one fold, one query set, one pair of challenges. What
remains — the full RBR-game instance where EVERY round of a depth-`k`
accumulation chain is simultaneously extractable (two-point, chain-level,
per `Selvage/AccSoundRbr.lean`'s `[ACC-sound-rbr-game]` diagnosis) and
simulatable (fresh per-round masks, per `Selvage/ZKHiding.lean`'s named
multi-step-schedule residual), with the two obligations interleaved across
`k` rounds without either compromising the other — is named precisely at the
bottom, `[ZK-RBR-game]`. It is NOT faked here: no `Reduction` /
`RbrKnowledgeSoundness` pair is built, and no RBR-shaped zero-knowledge
vocabulary exists yet in `Selvage/Rbr.lean` to even state the round-level
simulator obligation in that game's terms. What this file closes is real and
non-trivial (the single-round coexistence, proved, keystoned, and given
teeth); what is open is a genuinely new composition, sharpened below.
No `sorry`, no vacuous `Prop := True`.
-/
import Selvage.ZKHiding
import Selvage.ZK
import Selvage.AccExtract
import Selvage.ConstrainedMask

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r t : ℕ}

/-! ## The mask-space bridge

`Selvage/ZK.lean`'s fold-level mask space (`satWords C B`, an `AccClaim`'s
satisfying set) and `Selvage/ConstrainedMask.lean`'s opening-level mask space
(`constrainedMaskSpace`, a `Submodule`) coincide exactly for a
single-evaluation-constraint mask claim — the SAME mask serves both roles. -/

/-- **The bridge**: for the mask claim `⟨rt, fun _ => (evalAtPt pt, 0)⟩` — one
homogeneous evaluation constraint, `Selvage/ConstrainedMask.lean`'s exact shape —
the claim's satisfying set (what `Selvage/ZK.lean`'s `mask_bijOn` draws from) is
membership in `constrainedMaskSpace dom d pt` (what
`Selvage/ConstrainedMask.lean`'s `constrainedMask_hiding` hides). Pointwise, so it
transports through either direction without a `Set`-coercion detour. -/
theorem mem_constrainedMaskSpace_iff_satisfies (dom : ι ↪ F) (d : ℕ) (pt : ι)
    (rt : Root) {f : ι → F} :
    f ∈ constrainedMaskSpace dom d pt ↔
      AccClaim.Satisfies (reedSolomonCode dom d)
        (⟨rt, fun _ => (evalAtPt pt, (0 : F))⟩ : AccClaim Root F ι 1) f := by
  rw [mem_constrainedMaskSpace, AccClaim.Satisfies]
  simp [AccClaim.weights, AccClaim.targets]

/-! ## `ZkArgument` — completeness, knowledge-soundness, zero-knowledge, one
structure

Each field's type is the REAL conclusion of the theorem it will be built
from, instantiated on the masked accumulator claim `foldClaims foldRoot A B
γ` with mask space `M` (the object `Selvage/ZK.lean`'s fold and
`Selvage/ZKHiding.lean`'s opening both draw from — the bridge above supplies a
concrete `M` for which that is literally true). Nothing here is a
restatement in weaker form: `knowledge_sound`'s conclusion is
`accKnowledgeSound`'s four-way conjunction verbatim; `zero_knowledge` is
`MaskedOpeningHiding` verbatim. -/

/-- **`ZkArgument`** — a zero-knowledge argument for the accumulator's γ-fold,
at ONE step: the running claim `A` folds the mask claim `B` (mask space `M`)
at challenge `γ`, under the query `q`. -/
structure ZkArgument (C : Submodule F (ι → F)) (foldRoot : Root → F → Root → Root)
    (A B : AccClaim Root F ι r) (M : Submodule F (ι → F)) (q : Fin t → ι)
    (γ : F) : Prop where
  /-- **Completeness**: an honest witness `f` of the running claim, masked by
  ANY `g` drawn from the mask space `M` that also satisfies `B`'s shared
  channel, produces a witness of the folded claim — `foldClaims_satisfies`
  run at the mask, unconditional on `γ`. -/
  completeness : ∀ f g, (∀ i, B.weights i = A.weights i) →
      AccClaim.Satisfies C A f → g ∈ M →
      AccClaim.Satisfies C (foldClaims foldRoot A B γ) (mask f γ g)
  /-- **Knowledge-soundness**: for ANY second challenge `γ'` a cheating
  prover chooses and ANY second accepting transcript `h'` it produces, the
  straightline extractor `extractPair` recovers genuine witnesses of the
  INDIVIDUAL claims from the pair `(h, h')` — `accKnowledgeSound`'s
  conclusion verbatim. Quantified over TWO transcripts: this is where a
  cheating prover's choices live. -/
  knowledge_sound : ∀ {h h' γ'}, γ ≠ γ' →
      (∀ i, B.weights i = A.weights i) →
      AccClaim.Satisfies C (foldClaims foldRoot A B γ) h →
      AccClaim.Satisfies C (foldClaims foldRoot A B γ') h' →
      AccClaim.Satisfies C A (extractPair h h' γ γ').1 ∧
      AccClaim.Satisfies C B (extractPair h h' γ γ').2 ∧
      h = (extractPair h h' γ γ').1 + γ • (extractPair h h' γ γ').2 ∧
      h' = (extractPair h h' γ γ').1 + γ' • (extractPair h h' γ γ').2
  /-- **Zero-knowledge**: the `t` symbols the verifier opens of the masked
  transcript AT `γ` — the ONE transcript the honest verifier ever runs — are
  simulatable without the witness. No second challenge appears in this
  field's type: that absence, contrasted with `knowledge_sound`'s `γ'`, IS
  the quantifier-position separation the module header names. -/
  zero_knowledge : MaskedOpeningHiding M q γ

/-- **The coexistence theorem**: `ZkArgument` fires by straight composition
of three cited theorems, given only the mask-space bridge `hMB` (the mask
space `M` really is `B`'s satisfying set — supplied for the constrained-mask
case by `mem_constrainedMaskSpace_iff_satisfies` above) and the opening-hiding
fact `hZK` itself. Nothing here is re-derived: `completeness` is
`foldClaims_satisfies`, `knowledge_sound` is `accKnowledgeSound`,
`zero_knowledge` is exactly `hZK`. The NEW content is that these three
citations discharge the SAME structure's three fields on the SAME `(C,
foldRoot, A, B, M, q, γ)` — the coexistence is definitional, not a new
inequality to prove, once the bridge identifies the two mask-space
vocabularies. -/
theorem zkArgument_of_hiding {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {M : Submodule F (ι → F)} {q : Fin t → ι} {γ : F}
    (hMB : ∀ g ∈ M, AccClaim.Satisfies C B g) (hZK : MaskedOpeningHiding M q γ) :
    ZkArgument C foldRoot A B M q γ where
  completeness f g hshare hf hg := foldClaims_satisfies foldRoot γ hshare hf (hMB g hg)
  knowledge_sound := fun {h h' γ'} hne hshare hfold hfold' =>
    accKnowledgeSound foldRoot hne hshare hfold hfold'
  zero_knowledge := hZK

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]` (`RSExample`), the running accumulator `evalA`
(functional `q2`, target `2`, honest for `xWord`) folding the mask claim
`Bmask` (functional `evalAtPt 2` — which IS `q2`, so `evalA`/`Bmask` share a
channel — target `0`), mask space `constrainedMaskSpace dom₅ 2 pt2`, single
query point `qz = 0`. -/

namespace ZkArgumentExample

open RSExample AccExample

/-- The constraint point: vanish at domain index `2` — chosen so the mask
claim shares `evalA`'s functional (`q2 = evalAtPt 2`, proved below), letting
ONE running accumulator anchor completeness, knowledge-soundness, and
zero-knowledge together. -/
def pt2 : Fin 4 := 2

/-- `q2` (the running accumulator's functional) IS `evalAtPt pt2` — both are
literally `f ↦ f 2`. This is what makes `evalA` and the constrained mask
claim below a genuinely shared-channel pair, not a coincidence of names. -/
theorem q2_eq_evalAtPt2 : (q2 : (Fin 4 → ZMod 5) →ₗ[ZMod 5] ZMod 5) = evalAtPt pt2 :=
  LinearMap.ext fun _ => rfl

/-- The mask claim: one homogeneous evaluation constraint at `pt2`. -/
def Bmask : AccClaim Unit (ZMod 5) (Fin 4) 1 :=
  ⟨(), fun _ => (evalAtPt pt2, (0 : ZMod 5))⟩

/-- The shared-channel hypothesis `foldClaims_satisfies` / `accKnowledgeSound`
need: `Bmask`'s functional is `evalA`'s. -/
theorem hshare_mask (i : Fin 1) : Bmask.weights i = evalA.weights i := by
  show evalAtPt pt2 = q2
  exact q2_eq_evalAtPt2.symm

/-- **The mask-space bridge, instantiated**: `Bmask`'s satisfying set is
membership in `constrainedMaskSpace dom₅ 2 pt2` — the exact hypothesis
`zkArgument_of_hiding` needs. -/
theorem Bmask_hMB :
    ∀ g ∈ constrainedMaskSpace dom₅ 2 pt2,
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) Bmask g :=
  fun _ hg => (mem_constrainedMaskSpace_iff_satisfies dom₅ 2 pt2 ()).mp hg

/-- The single query point `0`, distinct from `pt2 = 2`, at the tight bound
`t + 1 = d = 2` (`t = 1`). -/
def qz : Fin 1 → Fin 4 := ![0]

theorem qz_inj : Function.Injective (dom₅ ∘ qz) := by decide

theorem qz_ne_pt2 : ∀ j, qz j ≠ pt2 := by decide

/-- **The nonzero mask, computed**: the line `2 − X` (`= lineOf 2 1`) vanishes
at `pt2 = 2` (`2 − 2 = 0`) and is a genuine nonzero codeword — the mask space
is nontrivial, not just `{0}`. -/
theorem maskWord_mem : ZkHidingExample.lineOf 2 1 ∈ constrainedMaskSpace dom₅ 2 pt2 := by
  rw [mem_constrainedMaskSpace]
  exact ⟨ZkHidingExample.lineOf_mem 2 1, by decide⟩

theorem maskWord_ne_zero : ZkHidingExample.lineOf 2 1 ≠ 0 := by decide

/-- **The instance**: `ZkArgument` fires on `evalA`/`Bmask` at every nonzero
challenge — pure composition of `zkArgument_of_hiding` with `Bmask_hMB` and
`constrainedMask_hiding` (which itself rides `maskedOpeningHiding_of_surj`).
Nothing here is re-derived. -/
theorem zkArgument_F5 {γ : ZMod 5} (hγ : γ ≠ 0) :
    ZkArgument (reedSolomonCode dom₅ 2) trivialRoot evalA Bmask
      (constrainedMaskSpace dom₅ 2 pt2) qz γ :=
  zkArgument_of_hiding trivialRoot Bmask_hMB
    (constrainedMask_hiding dom₅ pt2 (by norm_num) qz_inj qz_ne_pt2 hγ)

/-! ### Satisfiable: all three fields fire together on ONE transcript

`xWord` (honest witness of `evalA`) masked by `lineOf 2 1` (a genuine nonzero
element of the mask space) at challenge `2`: the SAME masked word is (a) a
real completeness witness, (b) exactly what `extractPair` recovers from two
such transcripts, and (c) whose opened symbols are hidden by
`zero_knowledge`. Non-vacuous on every count. -/

theorem xWord_sat_evalA : AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA xWord :=
  ⟨xWord_mem, fun _ => q2_xWord⟩

theorem maskWord_sat_Bmask :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) Bmask (ZkHidingExample.lineOf 2 1) :=
  (mem_constrainedMaskSpace_iff_satisfies dom₅ 2 pt2 ()).mp maskWord_mem

/-- **Completeness, fired**: the masked witness is genuine — `completeness`
applied to `xWord` and the nonzero mask. -/
theorem completeness_fired :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) (foldClaims trivialRoot evalA Bmask 2)
      (mask xWord 2 (ZkHidingExample.lineOf 2 1)) :=
  (zkArgument_F5 (γ := 2) (by decide)).completeness xWord (ZkHidingExample.lineOf 2 1)
    hshare_mask xWord_sat_evalA maskWord_mem

/-- The same closure fact at a second challenge `1` — the SECOND transcript
`knowledge_sound` needs. -/
theorem completeness_fired' :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) (foldClaims trivialRoot evalA Bmask 1)
      (mask xWord 1 (ZkHidingExample.lineOf 2 1)) :=
  (zkArgument_F5 (γ := 1) (by decide)).completeness xWord (ZkHidingExample.lineOf 2 1)
    hshare_mask xWord_sat_evalA maskWord_mem

/-- **The extractor, computed**: from the two masked transcripts at `2` and
`1`, `extractPair` recovers exactly `(xWord, lineOf 2 1)` — kernel
computation, the same idiom as `AccExtractExample.extract_recovers`. -/
theorem extract_recovers_masked :
    extractPair (mask xWord 2 (ZkHidingExample.lineOf 2 1))
        (mask xWord 1 (ZkHidingExample.lineOf 2 1)) 2 1
      = (xWord, ZkHidingExample.lineOf 2 1) := by
  decide

/-- **Knowledge-soundness, fired**: `knowledge_sound` applied to the two
transcripts at `2` and `1` recovers genuine witnesses of `evalA` and `Bmask`
— which, by `extract_recovers_masked`, are exactly `xWord` and the mask. -/
theorem knowledge_sound_fired :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA xWord ∧
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) Bmask (ZkHidingExample.lineOf 2 1) := by
  have h := (zkArgument_F5 (γ := 2) (by decide)).knowledge_sound
    (h' := mask xWord 1 (ZkHidingExample.lineOf 2 1)) (γ' := 1)
    (by decide) hshare_mask completeness_fired completeness_fired'
  rw [extract_recovers_masked] at h
  exact ⟨h.1, h.2.1⟩

/-- **Zero-knowledge, fired**: the SAME `γ = 2` transcript's opened symbols
are hidden — `zero_knowledge` at the instance `completeness_fired` and
`knowledge_sound_fired` both use. -/
theorem zero_knowledge_fired :
    MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qz (2 : ZMod 5) :=
  (zkArgument_F5 (γ := 2) (by decide)).zero_knowledge

/-! ### Teeth: the two properties genuinely pull opposite directions

Neither is a restatement of the other, exhibited both ways. -/

/-- **Teeth 1** — hiding is the binding constraint, not knowledge: at `γ =
0`, zero-knowledge is REFUTED (`not_maskedOpeningHiding_zero`; the query is
nonempty, `t = 1 > 0`), so no `ZkArgument` exists at `γ = 0`. Knowledge is
NOT what fails: `extractPair` still recovers the honest pair from folds at
`0` and any `γ' ≠ 0` — computed directly on `accKnowledgeSound`'s underlying
algebra, with no `ZkArgument` instance in sight (there is none to cite). -/
theorem zeroKnowledge_fails_at_zero :
    ¬ MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qz (0 : ZMod 5) :=
  not_maskedOpeningHiding_zero _ (by norm_num)

theorem extraction_survives_at_zero :
    extractPair (mask xWord 0 (ZkHidingExample.lineOf 2 1))
        (mask xWord 1 (ZkHidingExample.lineOf 2 1)) 0 1
      = (xWord, ZkHidingExample.lineOf 2 1) := by
  decide

/-- **Teeth 2** — one transcript is never enough for knowledge, but IS
enough for hiding: two genuinely DISTINCT witness pairs — `(xWord, lineOf 2
1)` and `(twoWord, 0)` (`ZkExample.twoWord`, the constant-`2` codeword,
satisfies `evalA`; the zero codeword trivially satisfies `Bmask`) — fold to
the SAME word `twoWord` at the single challenge `γ = 1`
(`xWord + lineOf 2 1 = twoWord = twoWord + 0`, computed). No function of one
fold recovers `(f, g)`; `single_fold_ambiguous` (`Selvage/AccExtract.lean`) is
this phenomenon in general, exhibited here on the SAME claim pair
`zkArgument_F5` uses. -/
theorem single_fold_ambiguous_masked :
    ∃ f₁ g₁ f₂ g₂ : Fin 4 → ZMod 5,
      (f₁, g₁) ≠ (f₂, g₂) ∧
      f₁ + (1 : ZMod 5) • g₁ = f₂ + (1 : ZMod 5) • g₂ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA f₁ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) Bmask g₁ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) evalA f₂ ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) Bmask g₂ :=
  ⟨xWord, ZkHidingExample.lineOf 2 1, ZkExample.twoWord, 0,
    by decide, by decide,
    xWord_sat_evalA, maskWord_sat_Bmask, ZkExample.twoWord_sat_evalA,
    (mem_constrainedMaskSpace_iff_satisfies dom₅ 2 pt2 ()).mp (Submodule.zero_mem _)⟩

/-- **Zero-knowledge survives the ambiguity**: the very fold at `γ = 1` that
`single_fold_ambiguous_masked` shows no extractor can invert is STILL hidden
— `zero_knowledge` fires there. One transcript is never enough to extract,
but is exactly what zero-knowledge is a statement about. -/
theorem zeroKnowledge_holds_at_one :
    MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qz (1 : ZMod 5) :=
  (zkArgument_F5 (γ := 1) (by decide)).zero_knowledge

end ZkArgumentExample

/-! ## Residual obligation — prose, not a stub

**`[ZK-RBR-game]`** — the full RBR-game instance in which EVERY round of a
depth-`k` accumulation chain is simultaneously extractable and simulatable,
composed over depth. What `ZkArgument` closes above is the single-round,
single-query-set slice: one fold, one pair of challenges for extraction, one
challenge and one query set for hiding — real, and now built on a concrete
non-vacuous instance with teeth. What `[ZK-RBR-game]` needs beyond that,
named precisely (not faked):

* **A round-level object that carries BOTH obligations, and does not exist
  yet.** `Selvage/Rbr.lean`'s `RbrKnowledgeSoundness` (WARP Def 4.2) is the
  ONLY round-level vocabulary this codebase has — an `extract` field and an
  `err` bound, nothing zero-knowledge-shaped. There is no
  `RbrZeroKnowledge`-style structure pairing a per-round SIMULATOR with a
  per-round hiding bound in `Rbr.lean`'s idiom (challenge-indexed,
  `uniformProb`-measured). Authoring that vocabulary — not just
  instantiating it — is part of this residual: `MaskedOpeningHiding` is
  stated over ONE query set and ONE challenge; casting it as a round-level
  RBR object (a `uniformProb`-measured simulator-success bound, dual to
  `Selvage/AccSoundRbr.lean`'s `accRbrError`) is unbuilt.
* **The chain-level extractor is two-point; the naive per-round shape is
  one-point — `Selvage/AccSoundRbr.lean`'s `[ACC-sound-rbr-game]` diagnosis,
  inherited verbatim.** WARP Def 4.2's backward round extractor is seeded
  from a SINGLE extended transcript; `extractPair` (this file's
  `knowledge_sound`, cited unchanged) needs TWO. `Selvage/AccSoundRbr.lean`
  proved that the naive one-transcript embedding does NOT discharge
  `RbrKnowledgeSoundness.extract_sound` for the fold (the linear code's
  kernel makes closeness of the SUM say nothing about closeness of the
  SUMMANDS without the mutual-correlated-agreement structure) and named the
  realizer as the CHAIN-level two-point extractor
  (`Selvage/AccExtractChain.lean`'s `extractChain`), not a single-round fix.
  `[ZK-RBR-game]` inherits this obstruction unchanged: whatever `extract`
  field the new `k`-round `Reduction` carries must be the chain extractor,
  not `k` independent one-round extractors.
* **The genuinely NEW coupling this file's residual adds** (absent from
  `[ACC-sound-rbr-game]`, which is extraction-only, and from
  `Selvage/ZKHiding.lean`'s named "multi-step schedule" piece, which is
  hiding-only): the chain extractor's SECOND transcript per round — in
  deployment, the `t` opened columns plus erasure correction
  (`[ACC-extract-bind]`, `AccExtract.lean`'s module header) — and the
  simulator's PER-ROUND mask draw must be shown NOT to interfere across `k`
  rounds. Concretely: the erasure-corrected second evaluation that furnishes
  `extractPair`'s `h'` at round `i` is read off the SAME opened columns the
  round-`i` simulator must also produce (honestly) or hide (against a
  distinguisher) — one straightline FS execution, one set of openings,
  serving both a soundness reduction that runs the chain extractor over ALL
  rounds' output-prefix queries (WARP Thm B.4's SR game, `Selvage/Depth.lean`)
  and a zero-knowledge reduction that must simulate those SAME openings
  without the witness, round by round. Whether FRESH per-round masks
  (`Selvage/ZKHiding.lean`'s residual: "that each committed word is opened at
  ONE step only is what should make fresh per-step masks sufficient") are
  enough to make the two reductions independent, or whether the chain
  extractor's cross-round algebra (`extractPair_peel₂`'s `wAt` recursion)
  creates a real coupling a fresh-mask argument does not automatically kill,
  is the open mathematical question — genuinely open, not bureaucratic.
* **What is NOT at risk.** Nothing above casts doubt on either landed
  bound: `accRbrError`/`accSound_rbr` (`Selvage/AccSoundRbr.lean`) and
  `MaskedOpeningHiding`/`rs_maskedOpeningHiding`/`constrainedMask_hiding`
  (`Selvage/ZKHiding.lean`, `Selvage/ConstrainedMask.lean`) are real, unconditional
  theorems this file cites without re-derivation. The obstruction is
  entirely in ASSEMBLING a `k`-round game object whose OWN
  `extract_sound`/simulator fields refine into (imply) those per-round
  bounds AND coexist with each other across depth — the same
  bureaucratic-looking-but-substantive gap `[ACC-sound-rbr-game]` names for
  extraction alone, now doubled by a genuinely new interleaving question on
  the hiding side.

What THIS file closes: gap (2) of `[OB-4-hiding-rbr]` at the single-round
level — `ZkArgument` bundles completeness, knowledge-soundness, and
zero-knowledge as one `Prop`, built by straight composition from
`foldClaims_satisfies`, `accKnowledgeSound`, and `constrainedMask_hiding`
with no re-derivation, non-vacuous on a concrete F₅ instance where all THREE
fire on the SAME transcript (`completeness_fired`, `knowledge_sound_fired`,
`zero_knowledge_fired`), and with teeth in BOTH directions
(`zeroKnowledge_fails_at_zero` + `extraction_survives_at_zero`;
`single_fold_ambiguous_masked` + `zeroKnowledge_holds_at_one`) showing the
two properties are independent, not one a shadow of the other. The
quantifier-position argument that RESOLVES the apparent tension —
knowledge-soundness quantifies over a cheating prover's SECOND transcript,
zero-knowledge is a fact about the ONE transcript the honest verifier runs —
is visible directly in `ZkArgument`'s two field types, not asserted only in
prose. `[ZK-RBR-game]` — the multi-round game composing both — remains
genuinely open, sharpened above to a specific coupling question between the
chain extractor's opened-column source and the per-round simulator's mask
draws, not a restatement of either `[ACC-sound-rbr-game]` or `Selvage/ZKHiding.lean`'s
residuals in isolation.

## Ledger

* `mem_constrainedMaskSpace_iff_satisfies` — PROVED: the bridge identifying
  `Selvage/ZK.lean`'s fold-level mask space with `Selvage/ConstrainedMask.lean`'s
  opening-level mask space for a single-evaluation-constraint claim.
* `ZkArgument` — DEFINED: completeness + knowledge-soundness (`extractPair`,
  two transcripts) + zero-knowledge (`MaskedOpeningHiding`, one transcript),
  one structure, real conclusions in every field.
* `zkArgument_of_hiding` — PROVED: the coexistence theorem, pure composition
  of `foldClaims_satisfies`, `accKnowledgeSound`, and a supplied
  `MaskedOpeningHiding` fact, given the mask-space bridge.
* Keystones — `zkArgument_F5` (the instance, every nonzero challenge),
  `completeness_fired` / `knowledge_sound_fired` / `zero_knowledge_fired`
  (all three fields fired on ONE concrete transcript, non-vacuously),
  `zeroKnowledge_fails_at_zero` + `extraction_survives_at_zero` (teeth 1: γ =
  0 kills hiding, not knowledge), `single_fold_ambiguous_masked` +
  `zeroKnowledge_holds_at_one` (teeth 2: one transcript kills knowledge, not
  hiding).
* Residual — `[ZK-RBR-game]` (prose above): the multi-round game, sharpened
  to the extractor/simulator opened-column coupling question.

`#print axioms` on `mem_constrainedMaskSpace_iff_satisfies`, `zkArgument_of_hiding`,
`ZkArgumentExample.zkArgument_F5`, `ZkArgumentExample.completeness_fired`,
`ZkArgumentExample.knowledge_sound_fired`, `ZkArgumentExample.zero_knowledge_fired`,
`ZkArgumentExample.zeroKnowledge_fails_at_zero`,
`ZkArgumentExample.extraction_survives_at_zero`,
`ZkArgumentExample.single_fold_ambiguous_masked`,
`ZkArgumentExample.zeroKnowledge_holds_at_one`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
