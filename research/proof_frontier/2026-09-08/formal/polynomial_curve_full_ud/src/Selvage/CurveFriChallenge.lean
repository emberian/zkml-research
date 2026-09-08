/- Single-scalar challenge bounds for width-eight folding and fixed input
injection. These are coefficient-curve statements, not a runtime adapter,
independent binary-round composition, or a new sampled verifier budget. -/
import Selvage.CurveProximityGapFullUD
import Selvage.Sumcheck

namespace Minidregg.Selvage
open scoped BigOperators Classical

section Algebra
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem curveWord_snoc {M : ℕ} (u : Fin (M+1) → ι → F) (g : ι → F) (z : F) :
    curveWord (M := M+1) (Fin.snoc u g) z =
      fun i => curveWord u z i + z^(M+1)*g i := by
  ext i
  simp [curveWord, comb, Fin.sum_univ_castSucc]

theorem correlatedAgreement_of_snoc {M : ℕ} (C : Submodule F (ι → F)) (δ : ℝ)
    (u : Fin (M+1) → ι → F) (g : ι → F)
    (h : CorrelatedAgreement C δ (Fin.snoc u g)) : CorrelatedAgreement C δ u := by
  obtain ⟨S,hS,hw⟩ := h
  refine ⟨S,hS,?_⟩
  intro j
  simpa using hw j.castSucc

end Algebra

section Probability
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem curve_uniform_sound (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F)
    {d : ℕ} (hd : 1 ≤ d) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (u : Fin (M+1) → ι → F)
    (hfar : ¬ CorrelatedAgreement (reedSolomonCode dom d) δ u) :
    uniformProb F (fun z => close δ (reedSolomonCode dom d) (curveWord u z)) ≤
      ((M*Fintype.card ι : ℕ) : ℝ) / Fintype.card F := by
  have h := curve_bad_card_le M hM dom hd hδ0 hδ2 u hfar
  have hcast : ((Finset.univ.filter (fun z => close δ (reedSolomonCode dom d)
      (curveWord u z))).card : ℝ) ≤ ((M*Fintype.card ι : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)

/-- Width-eight folding is one geometric challenge of degree seven. -/
theorem arity8_curve_sound (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (u : Fin 8 → ι → F)
    (hfar : ¬ CorrelatedAgreement (reedSolomonCode dom d) δ u) :
    uniformProb F (fun z => close δ (reedSolomonCode dom d) (curveWord u z)) ≤
      ((7*Fintype.card ι : ℕ) : ℝ) / Fintype.card F :=
  curve_uniform_sound 7 (by decide) dom hd hδ0 hδ2 u hfar

/-- The additional beta^8 coefficient is fixed before beta is sampled. No
premise says that this injected word is a codeword. -/
theorem arity8_injected_curve_sound (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (u : Fin 8 → ι → F) (g : ι → F)
    (hfar : ¬ CorrelatedAgreement (reedSolomonCode dom d) δ u) :
    uniformProb F (fun z => close δ (reedSolomonCode dom d)
      (fun i => curveWord u z i + z^8*g i)) ≤
      ((8*Fintype.card ι : ℕ) : ℝ) / Fintype.card F := by
  have hf : ¬ CorrelatedAgreement (reedSolomonCode dom d) δ (Fin.snoc u g) :=
    fun h => hfar (correlatedAgreement_of_snoc _ _ _ _ h)
  simpa only [curveWord_snoc] using
    curve_uniform_sound 8 (by decide) dom hd hδ0 hδ2 (Fin.snoc u g) hf

/-- At each prior prefix, both coefficient family and injected input are
selected before the fresh scalar. Prefix may contain earlier challenges;
this theorem does not establish a runtime's timing discipline. -/
theorem arity8_injected_fixed_prefix_sound {Prefix : Type*}
    (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (u : Prefix → Fin 8 → ι → F) (g : Prefix → ι → F)
    (hfar : ∀ p, ¬ CorrelatedAgreement (reedSolomonCode dom d) δ (u p)) :
    ∀ p, uniformProb F (fun z => close δ (reedSolomonCode dom d)
      (fun i => curveWord (u p) z i + z^8*g p i)) ≤
      ((8*Fintype.card ι : ℕ) : ℝ) / Fintype.card F :=
  fun p => arity8_injected_curve_sound dom hd hδ0 hδ2 (u p) (g p) (hfar p)

end Probability
end Minidregg.Selvage

/-- info: 'Minidregg.Selvage.curveWord_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curveWord_snoc

/-- info: 'Minidregg.Selvage.correlatedAgreement_of_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.correlatedAgreement_of_snoc

/-- info: 'Minidregg.Selvage.curve_uniform_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_uniform_sound

/-- info: 'Minidregg.Selvage.arity8_curve_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.arity8_curve_sound

/-- info: 'Minidregg.Selvage.arity8_injected_curve_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.arity8_injected_curve_sound

/-- info: 'Minidregg.Selvage.arity8_injected_fixed_prefix_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.arity8_injected_fixed_prefix_sound

