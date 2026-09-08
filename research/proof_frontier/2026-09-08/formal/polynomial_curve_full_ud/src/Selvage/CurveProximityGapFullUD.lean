/- The direct geometric-generator full-UD bound of BCIKS20 Theorem 6.1.
All coding hypotheses are discharged by CurveFullUDCore; the random challenge
is one scalar, not independent binary coordinates. -/
import Selvage.CurveFullUDCore
import Selvage.ProximityGapFullUD

namespace Minidregg.Selvage
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

noncomputable def geometricGenerator (F : Type*) [Field F] [Fintype F]
    (M : ℕ) : ProximityGenerator F (M+1) where
  Seed := F
  gen z j := z ^ j.val
  weight _ := ((Fintype.card F : ℝ))⁻¹
  weight_nonneg _ := by positivity
  weight_sum_one := by
    have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hF)]

omit [DecidableEq ι] in
theorem curve_correlatedAgreement_of_many_close [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ) * (Fintype.card ι : ℝ))
    (u : Fin (M+1) → ι → F) (A : Finset F)
    (hclose : ∀ z ∈ A, close δ (reedSolomonCode dom d) (curveWord u z))
    (hcard : M*Fintype.card ι < A.card) :
    CorrelatedAgreement (reedSolomonCode dom d) δ u := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  let e := Nat.floor (δ * (Fintype.card ι : ℝ))
  have he : (e : ℝ) ≤ δ * (Fintype.card ι : ℝ) := Nat.floor_le (by positivity)
  have hradius : 2*e+d ≤ Fintype.card ι := by
    have h : (2 : ℝ)*(e : ℝ)+(d : ℝ) ≤ (Fintype.card ι : ℝ) := by nlinarith
    exact_mod_cast h
  have he_le : e ≤ Fintype.card ι := by omega
  obtain ⟨S,hScard,hjoint⟩ := curveFullUDCardCore M dom d e hM hd hradius u A (by
    intro z hz
    obtain ⟨w,hw,hrel⟩ := hclose z hz
    refine ⟨w,hw,?_⟩
    have hh : (hammingDist (curveWord u z) w : ℝ) ≤
        δ * (Fintype.card ι : ℝ) := (div_le_iff₀ hn).mp hrel
    exact Nat.le_floor hh) hcard
  refine ⟨S,?_,hjoint⟩
  have hcast : (Fintype.card ι : ℝ) - (e : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (show Fintype.card ι-e ≤ S.card from hScard)
  nlinarith

omit [DecidableEq ι] in
theorem curve_bad_card_le [Nonempty ι] [Fintype F]
    (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ) * (Fintype.card ι : ℝ))
    (u : Fin (M+1) → ι → F)
    (hfar : ¬ CorrelatedAgreement (reedSolomonCode dom d) δ u) :
    (Finset.univ.filter (fun z => close δ (reedSolomonCode dom d) (curveWord u z))).card
      ≤ M*Fintype.card ι := by
  classical
  by_contra h
  exact hfar (curve_correlatedAgreement_of_many_close M hM dom hd hδ0 hδ2 u _
    (fun z hz => (Finset.mem_filter.mp hz).2) (Nat.lt_of_not_ge h))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
theorem geometricGenerator_pr_eq [Fintype F] (M : ℕ) (u : Fin (M+1) → ι → F)
    (E : (ι → F) → Prop) :
    (geometricGenerator F M).pr (fun r => E (comb r u)) =
      ((Finset.univ.filter (fun z => E (curveWord u z))).card : ℝ) / Fintype.card F := by
  classical
  unfold ProximityGenerator.pr
  change (∑ _z ∈ Finset.univ.filter (fun z => E (curveWord u z)),
      (Fintype.card F : ℝ)⁻¹) = _
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

omit [DecidableEq ι] in
theorem reedSolomonCode_isGeometricProximityGenerator_fullUD [Nonempty ι] [Fintype F]
    (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F) (d : ℕ) (hd : 1 ≤ d) :
    IsProximityGenerator (geometricGenerator F M) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => (M*Fintype.card ι : ℕ) / (Fintype.card F : ℝ)) := by
  classical
  intro u δ hδ0 hδB hpr
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδ2 : (d : ℝ) < (1-2*δ) * (Fintype.card ι : ℝ) := by
    have hρ : (d : ℝ) / (Fintype.card ι : ℝ) < 1-2*δ := by linarith
    exact (div_lt_iff₀ hn).mp hρ
  have hcard : M*Fintype.card ι <
      (Finset.univ.filter (fun z => close δ (reedSolomonCode dom d) (curveWord u z))).card := by
    rw [geometricGenerator_pr_eq, div_lt_div_iff_of_pos_right hF] at hpr
    exact_mod_cast hpr
  exact curve_correlatedAgreement_of_many_close M hM dom hd hδ0 hδ2 u _
    (fun z hz => (Finset.mem_filter.mp hz).2) hcard

theorem hasGeometricMutualCorrelatedAgreement_fullUD [Nonempty ι] [Fintype F]
    (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) :
    HasMutualCorrelatedAgreement (geometricGenerator F M) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => ((M*Fintype.card ι : ℕ) : ℝ) / (Fintype.card F : ℝ)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := reedSolomonCode_hasMutualCorrelatedAgreement (geometricGenerator F M)
    dom d (reedSolomonCode_isGeometricProximityGenerator_fullUD M hM dom d hd)
    (fun _ _ _ => le_refl _)
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hle : 1 - (1 - ((d : ℝ)-1)/(Fintype.card ι : ℝ))/2 ≤
      (1+(d : ℝ)/(Fintype.card ι : ℝ))/2 := by
    have hsub : ((d : ℝ)-1)/(Fintype.card ι : ℝ) =
        (d : ℝ)/(Fintype.card ι : ℝ)-1/(Fintype.card ι : ℝ) := sub_div _ _ _
    rw [hsub]
    have h1n : (0 : ℝ) < 1/(Fintype.card ι : ℝ) := by positivity
    linarith
  rwa [max_eq_right hle] at h

end Minidregg.Selvage


/-- info: 'Minidregg.Selvage.curve_correlatedAgreement_of_many_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_correlatedAgreement_of_many_close

/-- info: 'Minidregg.Selvage.curve_bad_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_bad_card_le

/-- info: 'Minidregg.Selvage.geometricGenerator_pr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.geometricGenerator_pr_eq

/-- info: 'Minidregg.Selvage.reedSolomonCode_isGeometricProximityGenerator_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.reedSolomonCode_isGeometricProximityGenerator_fullUD

/-- info: 'Minidregg.Selvage.hasGeometricMutualCorrelatedAgreement_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.hasGeometricMutualCorrelatedAgreement_fullUD

