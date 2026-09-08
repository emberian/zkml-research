/- Two-round supplied BinaryMerkle reduction. Every source/input checkpoint
is fixed before its fresh scalar; the final checkpoint depends only on the
challenge pair, never on query seeds. Observed hash-log failures stay explicit. -/
import Selvage.ArityEightTwoRound
import Selvage.ArityEightSupplied

namespace Minidregg.Selvage.ArityEight.TwoRound
open scoped Classical

abbrev Checkpoint (F Digest : Type) := EfficientRootOpening.Log F Digest × Digest

/-- The five actual log/root checkpoints, with their allowed prefix dependence. -/
structure Checkpoints (F Digest : Type) where
  source : Checkpoint F Digest
  input0 : Checkpoint F Digest
  middle : F → Checkpoint F Digest
  input1 : F → Checkpoint F Digest
  final : F → F → Checkpoint F Digest

section Extraction
variable {F Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest] {ell : ℕ}

/-- Existing deterministic extractor at the actual three tower levels. -/
def extracted (st : Checkpoints F Digest) (default : F) : Words F (PowerTwoFriLevels ell) where
  source := EfficientRootOpening.word st.source.1 default ell st.source.2
  input0 := EfficientRootOpening.word st.input0.1 default (ell-3) st.input0.2
  middle a := EfficientRootOpening.word (st.middle a).1 default (ell-3) (st.middle a).2
  input1 a := EfficientRootOpening.word (st.input1 a).1 default (ell-6) (st.input1 a).2
  final a b := EfficientRootOpening.word (st.final a b).1 default (ell-6) (st.final a b).2

/-- Checkpoint inclusion in the actual finite execution log. -/
def CheckpointsLogged (st : Checkpoints F Digest) (L : EfficientRootOpening.Log F Digest)
    (r : F × F) : Prop :=
  (∀ e ∈ st.source.1, e ∈ L) ∧ (∀ e ∈ st.input0.1, e ∈ L) ∧
  (∀ e ∈ (st.middle r.1).1, e ∈ L) ∧ (∀ e ∈ (st.input1 r.1).1, e ∈ L) ∧
  (∀ e ∈ (st.final r.1 r.2).1, e ∈ L)

/-- The two actual observed round failures; the middle root is shared. -/
def Failure (st : Checkpoints F Digest) (L : EfficientRootOpening.Log F Digest) (r : F × F) : Prop :=
  RoundBad st.source.1 st.input0.1 (st.middle r.1).1 L
    st.source.2 st.input0.2 (st.middle r.1).2 ∨
  RoundBad (st.middle r.1).1 (st.input1 r.1).1 (st.final r.1 r.2).1 L
    (st.middle r.1).2 (st.input1 r.1).2 (st.final r.1 r.2).2

/-- Supplied paths are allowed to depend on both challenges and all queries. -/
structure Openings (F Digest : Type) (q : ℕ) where
  first : Fin q → RowOpening F Digest
  second : Fin q → RowOpening F Digest

def SuppliedAccepts (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) 6) (st : Checkpoints F Digest)
    (default : F) (d q : ℕ) (hell : 6 ≤ ell)
    (r : F × F) (seed : Fin q → PowerTwoFriLevels ell 1) (o : Openings F Digest q) : Prop :=
  (extracted st default).final r.1 r.2 ∈ reedSolomonCode (T.dom 6) d ∧
  (∀ a, RowVerified H (T.data 0 (by decide)) (T.data 1 (by decide)) (T.data 2 (by decide))
    st.source.2 st.input0.2 (st.middle r.1).2 r.1
    (powerTwoCoherentRound hell (⟨2,by decide⟩ : Fin 6) seed a) (o.first a)) ∧
  (∀ a, RowVerified H (T.data 3 (by decide)) (T.data 4 (by decide)) (T.data 5 (by decide))
    (st.middle r.1).2 (st.input1 r.1).2 (st.final r.1 r.2).2 r.2
    (powerTwoCoherentRound hell (⟨5,by decide⟩ : Fin 6) seed a) (o.second a))

def OpeningsLogged (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) 6) (L : EfficientRootOpening.Log F Digest)
    (q : ℕ) (hell : 6 ≤ ell) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest q) : Prop :=
  (∀ a, RowLogged H L (T.data 0 (by decide)) (T.data 1 (by decide)) (T.data 2 (by decide))
    (powerTwoCoherentRound hell (⟨2,by decide⟩ : Fin 6) seed a) (o.first a)) ∧
  (∀ a, RowLogged H L (T.data 3 (by decide)) (T.data 4 (by decide)) (T.data 5 (by decide))
    (powerTwoCoherentRound hell (⟨5,by decide⟩ : Fin 6) seed a) (o.second a))

/-- Off observed log failures, both supplied transitions pin to the same
prefix-selected middle word. No global event bound is a premise. -/
theorem supplied_cover (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) 6) (st : Checkpoints F Digest)
    (default : F) (d q : ℕ) (hell : 6 ≤ ell)
    (r : F × F) (seed : Fin q → PowerTwoFriLevels ell 1) (o : Openings F Digest q)
    (L : EfficientRootOpening.Log F Digest)
    (hsub : CheckpointsLogged st L r) (hlog : OpeningsLogged H T L q hell seed o)
    (ha : SuppliedAccepts H T st default d q hell r seed o) :
    Accepts T (extracted st default) d q hell r seed ∨ Failure st L r := by
  by_cases hb : Failure st L r
  · exact Or.inr hb
  · refine Or.inl ⟨ha.1,?_,?_⟩
    · intro a
      exact supplied_row_pins H (T.data 0 (by decide)) (T.data 1 (by decide))
        (T.data 2 (by decide)) st.source.1 st.input0.1 (st.middle r.1).1 L default
        st.source.2 st.input0.2 (st.middle r.1).2 hsub.1 hsub.2.1 hsub.2.2.1
        (fun h => hb (Or.inl h)) r.1
        (powerTwoCoherentRound hell (⟨2,by decide⟩ : Fin 6) seed a) (o.first a)
        (hlog.1 a) (ha.2.1 a)
    · intro a
      exact supplied_row_pins H (T.data 3 (by decide)) (T.data 4 (by decide))
        (T.data 5 (by decide)) (st.middle r.1).1 (st.input1 r.1).1 (st.final r.1 r.2).1 L default
        (st.middle r.1).2 (st.input1 r.1).2 (st.final r.1 r.2).2
        hsub.2.2.1 hsub.2.2.2.1 hsub.2.2.2.2 (fun h => hb (Or.inr h)) r.2
        (powerTwoCoherentRound hell (⟨5,by decide⟩ : Fin 6) seed a) (o.second a)
        (hlog.2 a) (ha.2.2 a)

set_option maxHeartbeats 800000 in
/-- Two actual externally challenged rounds with supplied openings: summed
challenge errors, one coherent-query tail, and the observed execution-log residual. -/
theorem supplied_sound [Fintype F] (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) 6) (st : Checkpoints F Digest)
    (default : F) {d : ℕ} (hd : 1 ≤ d) (q : ℕ) (hell : 6 ≤ ell)
    {ρ₀ ρ₁ τ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (hτ : τ ≤ 1)
    (hgap₀ : ρ₁+τ ≤ ρ₀) (hgap₁ : τ ≤ ρ₁)
    (hrate₀ : (8*d:ℕ) < (1-2*ρ₀)*(Fintype.card (PowerTwoFriLevels ell 3):ℝ))
    (hrate₁ : (d:ℝ) < (1-2*ρ₁)*(Fintype.card (PowerTwoFriLevels ell 6):ℝ))
    (openings : (F × F) × (Fin q → PowerTwoFriLevels ell 1) → Openings F Digest q)
    (logs : (F × F) × (Fin q → PowerTwoFriLevels ell 1) → EfficientRootOpening.Log F Digest)
    (hsub : ∀ x, CheckpointsLogged st (logs x) x.1)
    (hlog : ∀ x, OpeningsLogged H T (logs x) q hell x.2 (openings x))
    (hfar : EfficientRootOpening.Far_E ρ₀ ell (reedSolomonCode (T.dom 0) (64*d))
      st.source.1 default st.source.2) :
    uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => SuppliedAccepts H T st default d q hell x.1 x.2 (openings x)) ≤
      ((8*Fintype.card (PowerTwoFriLevels ell 3):ℕ):ℝ)/Fintype.card F +
      ((8*Fintype.card (PowerTwoFriLevels ell 6):ℕ):ℝ)/Fintype.card F + (1-τ)^q +
      uniformProb ((F × F) × (Fin q → PowerTwoFriLevels ell 1))
        (fun x => Failure st (logs x) x.1) := by
  let Ω := (F × F) × (Fin q → PowerTwoFriLevels ell 1)
  let ideal : Ω → Prop := fun x => Accepts T (extracted st default) d q hell x.1 x.2
  let raw : Ω → Prop := fun x => SuppliedAccepts H T st default d q hell x.1 x.2 (openings x)
  let bad : Ω → Prop := fun x => Failure st (logs x) x.1
  have hf : ¬close ρ₀ (reedSolomonCode (T.dom 0) (64*d)) (extracted st default).source := hfar
  have h : uniformProb Ω ideal ≤
      ((8*Fintype.card (PowerTwoFriLevels ell 3):ℕ):ℝ)/Fintype.card F +
      ((8*Fintype.card (PowerTwoFriLevels ell 6):ℕ):ℝ)/Fintype.card F + (1-τ)^q :=
    sound T (extracted st default) hd q hell hρ₀ hρ₁ hτ hgap₀ hgap₁ hrate₀ hrate₁ hf
  have hcover : ∀ x : Ω, raw x → ideal x ∨ bad x := by
    intro x hx
    exact supplied_cover H T st default d q hell x.1 x.2 (openings x) (logs x) (hsub x) (hlog x) hx
  have hsplit : uniformProb Ω raw ≤ uniformProb Ω ideal + uniformProb Ω bad :=
    le_trans (uniformProb_mono hcover) (uniformProb_or_le ideal bad)
  change uniformProb Ω raw ≤ _
  linarith

end Extraction
end Minidregg.Selvage.ArityEight.TwoRound

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.supplied_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.supplied_cover

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.supplied_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.supplied_sound
