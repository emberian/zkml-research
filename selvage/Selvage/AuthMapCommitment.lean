/-
# Selvage.AuthMapCommitment — words committed in an authenticated map

`Selvage/Commitment.lean`'s `BindingCommitment` carries *unconditional*
position binding, so every inhabitant has an injective `commit`
(`BindingCommitment.commit_injective`): none exists at a root type smaller than
the word space (`BindingCommitment.isEmpty_of_card_lt`).  A deployed Merkle
root cannot be one.

This module states the same two seams — "the word opened from this root is the
committed word" and "the columns the prover opened are the committed fold's
columns" — over `Theory.AuthMap`, whose soundness is a *reduction*:

* `column_or_collision` / `opened_word_or_collision` — a verifying opening of a
  wrong value exhibits a collision of `H` among the pairs that one check
  compared (`Scheme.forgery_exhibits_collision`).  The collision is named by
  the transcript, not merely asserted to exist: "`H` has a collision" is true
  of every compressing hash by pigeonhole, and a disjunct of that shape would
  make the statement provable outright.
* `authMap_extract_bind` — the binding seam as that reduction:
  `e = w ∧ Satisfies C A w`, or a collision exhibited by the opening of some
  position where `e` and `w` differ.
* `authMap_extract_bind_of_pathBinding` — the same under the per-check carrier
  `Scheme.PathBinding`, which is satisfiable at every hash (`honest_binding`)
  and refutable at a length hash (`LengthToy.lengthHash_binding_fails`).
* `lightClientKnowledgeSound_authMap` — the one-prover knowledge bound with
  the columns entering through AuthMap openings of the recommitted partial
  folds: `Pr[verifies ∧ extraction fails] ≤ n·(err⋆(δ) + 2/|F|) +
  Pr[the prover's openings exhibit a collision]`.  No carrier is assumed; the
  collision event is the price.

Word layout: a word `w : ι → F` is committed as a map holding `w i` at every
position (`HoldsWord`); `wordMap` builds one from an enumeration of `ι` when
the index is injective (`holdsWord_wordMap`).
-/
import Theory.AuthMap
import Selvage.LightClientKnowledge

namespace Minidregg.Selvage

open Minidregg.Theory

set_option autoImplicit false

section Word

variable {ι F D : Type} [DecidableEq ι] (S : AuthMap.Scheme ι F D)

/-- `m` holds the word `w`: every position reads `w i`. -/
def HoldsWord (m : AuthMap.Map ι F) (w : ι → F) : Prop :=
  ∀ i, AuthMap.lookup S.ix m i = some (w i)

/-- The map that places `w i` at the index path of `i`, for `i` in `all`. -/
def wordMap (all : List ι) (w : ι → F) : AuthMap.Map ι F :=
  fun p => (all.find? fun i => S.ix i = p).map fun i => (i, w i)

theorem holdsWord_wordMap {all : List ι} (hall : ∀ i, i ∈ all)
    (hix : Function.Injective S.ix) (w : ι → F) :
    HoldsWord S (wordMap S all w) w := by
  intro i
  have hsome : (all.find? fun k => S.ix k = S.ix i).isSome := by
    rw [List.find?_isSome]
    exact ⟨i, hall i, by simp⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
  have hji : j = i := hix (by simpa using List.find?_some hj)
  subst hji
  simp [AuthMap.lookup, wordMap, hj, AuthMap.readAt]

/-- The collision that one opening check exhibits: two distinct hash inputs
at the same level of the honest chain (of `m` at `k`) and the claimed chain,
with equal digests.  This is exactly the conclusion of
`Scheme.forgery_exhibits_collision`. -/
def OpeningCollision (m : AuthMap.Map ι F) (k : ι) (v : Option F)
    (π : AuthMap.Scheme.Opening ι F D) : Prop :=
  ∃ leafIn, S.claimLeaf k v π.occupant = some leafIn ∧
    ∃ x y, (x, y) ∈ (S.honestInputs m [] (S.ix k)).zip
        (S.claimInputs leafIn (S.ix k) π.siblings) ∧
      x ≠ y ∧ S.H x = S.H y

theorem OpeningCollision.collision {S : AuthMap.Scheme ι F D} {m : AuthMap.Map ι F}
    {k : ι} {v : Option F} {π : AuthMap.Scheme.Opening ι F D}
    (h : OpeningCollision S m k v π) : ∃ x y, x ≠ y ∧ S.H x = S.H y := by
  obtain ⟨_, _, x, y, _, hne, hH⟩ := h
  exact ⟨x, y, hne, hH⟩

/-- At an injective hash no opening exhibits a collision. -/
theorem not_openingCollision_of_injective (hH : Function.Injective S.H)
    (m : AuthMap.Map ι F) (k : ι) (v : Option F) (π : AuthMap.Scheme.Opening ι F D) :
    ¬ OpeningCollision S m k v π := fun h =>
  let ⟨_, _, hne, hH'⟩ := h.collision
  hne (hH hH')

variable [DecidableEq D]

/-- One column: a verifying opening against a map holding `w` reads `w i`, or
it exhibits a collision. -/
theorem column_or_collision {m : AuthMap.Map ι F} {w : ι → F} (hm : HoldsWord S m w)
    {i : ι} {v : F} {π : AuthMap.Scheme.Opening ι F D}
    (h : S.verify (S.root m) i (some v) π = true) :
    v = w i ∨ OpeningCollision S m i (some v) π := by
  by_cases hv : v = w i
  · exact Or.inl hv
  · refine Or.inr (S.forgery_exhibits_collision m i (some v) π h ?_)
    rw [hm i]
    exact fun h' => hv (Option.some.inj h')

/-- One column under the per-check carrier. -/
theorem column_of_pathBinding {m : AuthMap.Map ι F} {w : ι → F} (hm : HoldsWord S m w)
    {i : ι} {v : F} {π : AuthMap.Scheme.Opening ι F D}
    (hb : S.PathBinding m i (some v) π)
    (h : S.verify (S.root m) i (some v) π = true) : v = w i :=
  Option.some.inj ((S.verify_sound m i (some v) π hb h).trans (hm i))

/-- A word fully opened from a map holding `w` is `w`, or the opening of some
position where they differ exhibits a collision. -/
theorem opened_word_or_collision {m : AuthMap.Map ι F} {w e : ι → F}
    (hm : HoldsWord S m w) {πe : ι → AuthMap.Scheme.Opening ι F D}
    (hopen : ∀ i, S.verify (S.root m) i (some (e i)) (πe i) = true) :
    e = w ∨ ∃ i, e i ≠ w i ∧ OpeningCollision S m i (some (e i)) (πe i) := by
  by_cases h : ∃ i, e i ≠ w i
  · obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨i, hi, (column_or_collision S hm (hopen i)).resolve_left hi⟩
  · refine Or.inl (funext fun i => ?_)
    by_contra hi
    exact h ⟨i, hi⟩

section Seams

variable [Field F] {r : ℕ}

/-- **The binding seam, as a reduction.**  If the accumulated claim's root is
the root of a map holding `w`, and the word `e` the algebra worked on is fully
opened from that root, then either `e = w` and satisfaction transfers to the
committed word, or the opening of a position where they differ exhibits a
collision of `H`. -/
theorem authMap_extract_bind {C : Submodule F (ι → F)} {A : AccClaim D F ι r}
    {m : AuthMap.Map ι F} {w e : ι → F} {πe : ι → AuthMap.Scheme.Opening ι F D}
    (hrt : A.rt = S.root m) (hm : HoldsWord S m w)
    (hopen : ∀ i, S.verify A.rt i (some (e i)) (πe i) = true)
    (hsat : AccClaim.Satisfies C A e) :
    (e = w ∧ AccClaim.Satisfies C A w) ∨
      ∃ i, e i ≠ w i ∧ OpeningCollision S m i (some (e i)) (πe i) := by
  rcases opened_word_or_collision S hm (fun i => hrt ▸ hopen i) with h | h
  · exact Or.inl ⟨h, h ▸ hsat⟩
  · exact Or.inr h

/-- The binding seam under the per-check carrier `PathBinding` at every
position. -/
theorem authMap_extract_bind_of_pathBinding {C : Submodule F (ι → F)}
    {A : AccClaim D F ι r} {m : AuthMap.Map ι F} {w e : ι → F}
    {πe : ι → AuthMap.Scheme.Opening ι F D}
    (hrt : A.rt = S.root m) (hm : HoldsWord S m w)
    (hb : ∀ i, S.PathBinding m i (some (e i)) (πe i))
    (hopen : ∀ i, S.verify A.rt i (some (e i)) (πe i) = true)
    (hsat : AccClaim.Satisfies C A e) :
    e = w ∧ AccClaim.Satisfies C A w := by
  have he : e = w := funext fun i => column_of_pathBinding S hm (hb i) (hrt ▸ hopen i)
  exact ⟨he, he ▸ hsat⟩

end Seams

end Word

/-! ## Knowledge with the columns opened from AuthMap roots -/

section Knowledge

variable {F : Type} [Field F] {ι D : Type} {r : ℕ} [DecidableEq ι] [DecidableEq D]

/-- The event that some opening the prover supplied, at schedule `γv`,
exhibits a collision: at recommitment `c ≤ n`, column `j`. -/
def ColumnCollision (S : AuthMap.Scheme ι F D) {n t : ℕ} (q : Fin t → ι)
    (maps : (Fin n → F) → ℕ → AuthMap.Map ι F)
    (cols : (Fin n → F) → ℕ → Fin t → F)
    (πs : (Fin n → F) → ℕ → Fin t → AuthMap.Scheme.Opening ι F D)
    (γv : Fin n → F) : Prop :=
  ∃ c ≤ n, ∃ j, OpeningCollision S (maps γv c) (q j) (some (cols γv c j)) (πs γv c j)

/-- The columns with every collision-exhibiting schedule replaced by the
honest partial-fold columns.  Only a proof device: it agrees with `cols`
wherever `bad` fails. -/
noncomputable def patchCols {n t : ℕ} (bad : (Fin n → F) → Prop)
    (cols honest : (Fin n → F) → ℕ → Fin t → F) : (Fin n → F) → ℕ → Fin t → F := by
  classical
  exact fun γv => if bad γv then honest γv else cols γv

omit [Field F] in
theorem patchCols_of_not {n t : ℕ} {bad : (Fin n → F) → Prop}
    {cols honest : (Fin n → F) → ℕ → Fin t → F} {γv : Fin n → F} (h : ¬ bad γv) :
    patchCols bad cols honest γv = cols γv := by
  unfold patchCols
  exact if_neg h

omit [Field F] in
theorem patchCols_of_bad {n t : ℕ} {bad : (Fin n → F) → Prop}
    {cols honest : (Fin n → F) → ℕ → Fin t → F} {γv : Fin n → F} (h : bad γv) :
    patchCols bad cols honest γv = honest γv := by
  unfold patchCols
  exact if_pos h

variable (foldRoot : D → F → D → D)

/-- **Knowledge soundness through AuthMap openings, as a reduction.**  The
prover recommits each partial fold as a map (`hmaps`) and opens `t` columns
of each against its root (`hver`).  The probability that its transcript
verifies and the one-execution extractor fails is at most the bound of
`lightClientKnowledgeSound_oneProver` plus the probability that the openings
it supplied exhibit a collision of `H`. -/
theorem lightClientKnowledgeSound_authMap [Fintype ι] [DecidableEq F] [Fintype F]
    [Nonempty ι]
    {C : Submodule F (ι → F)} {A₀ : AccClaim D F ι r} {ch : Chain D F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2) (herr0 : 0 ≤ errstar δ)
    (S : AuthMap.Scheme ι F D) (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {maps : (Fin ch.length → F) → ℕ → AuthMap.Map ι F}
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    {πs : (Fin ch.length → F) → ℕ → Fin t → AuthMap.Scheme.Opening ι F D}
    (hmaps : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length →
      HoldsWord S (maps γv c) (partialFold (padSched γv) f₀ ms c))
    (hver : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      S.verify (S.root (maps γv c)) (q j) (some (cols γv c j)) (πs γv c j) = true) :
    uniformProb (Fin ch.length → F) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
        ¬ (attests C ch ∧
          List.Forall₂ (fun (l : Link D F ι r) w =>
              ∃ v, relDist w v ≤ δ ∧ AccClaim.Satisfies C l.claim v) ch
            (lcExtract dom d q ch.length (padSched γv)
              (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
      ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ)) +
        uniformProb (Fin ch.length → F) (ColumnCollision S q maps cols πs) := by
  set bad := ColumnCollision S q maps cols πs with hbad
  set honest : (Fin ch.length → F) → ℕ → Fin t → F :=
    fun γv c j => partialFold (padSched γv) f₀ ms c (q j) with hhonest
  have hcols : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      patchCols bad cols honest γv c j = partialFold (padSched γv) f₀ ms c (q j) := by
    intro γv c hc j
    by_cases hγ : bad γv
    · rw [patchCols_of_bad hγ]
    · rw [patchCols_of_not hγ]
      rcases column_or_collision S (hmaps γv c hc) (hver γv c hc j) with h | h
      · exact h
      · exact absurd ⟨c, hc, j, h⟩ hγ
  have hK := lightClientKnowledgeSound_oneProver foldRoot halign hseam hdC hMCA hδ0 hδB
    hδC herr0 dom hdt hq hms (cols := patchCols bad cols honest) hcols
  refine le_trans (uniformProb_mono fun γv hE => ?_)
    (le_trans (uniformProb_or_le _ _) (add_le_add hK le_rfl))
  by_cases hγ : bad γv
  · exact Or.inr hγ
  · refine Or.inl ?_
    rw [patchCols_of_not hγ]
    exact hE

end Knowledge

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.holdsWord_wordMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holdsWord_wordMap
/-- info: 'Minidregg.Selvage.column_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms column_or_collision
/-- info: 'Minidregg.Selvage.opened_word_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opened_word_or_collision
/-- info: 'Minidregg.Selvage.authMap_extract_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authMap_extract_bind
/-- info: 'Minidregg.Selvage.authMap_extract_bind_of_pathBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authMap_extract_bind_of_pathBinding
/-- info: 'Minidregg.Selvage.not_openingCollision_of_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms not_openingCollision_of_injective
/-- info: 'Minidregg.Selvage.lightClientKnowledgeSound_authMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lightClientKnowledgeSound_authMap

end Minidregg.Selvage
