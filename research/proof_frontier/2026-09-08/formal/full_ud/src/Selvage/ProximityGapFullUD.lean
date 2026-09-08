/-
# Full unique-decoding proximity generator over the existing RS code

The integer BW/gluing core is `fullUDCardCore`. This module provides the
existing IsProximityGenerator, mutual-agreement and FRI-fold interfaces.
The error is still n/|F|; the admissible open radius grows to (1-d/n)/2.
-/
import Selvage.FullUDCore
import Selvage.FullUDTeeth

namespace Minidregg.Selvage
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- Integer full-UD core converted to the existing relative-distance
correlated-agreement predicate. -/
theorem correlatedAgreement_of_many_close_fullUD [Nonempty ι]
    (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ) * (Fintype.card ι : ℝ))
    (f : Fin 2 → ι → F) (A : Finset F)
    (hclose : ∀ z ∈ A, close δ (reedSolomonCode dom d) (f 0 + z • f 1))
    (hcard : Fintype.card ι < A.card) :
    CorrelatedAgreement (reedSolomonCode dom d) δ f := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  let e := Nat.floor (δ * (Fintype.card ι : ℝ))
  have he : (e : ℝ) ≤ δ * (Fintype.card ι : ℝ) := Nat.floor_le (by positivity)
  have hradius : 2*e+d ≤ Fintype.card ι := by
    have h : (2 : ℝ)*(e : ℝ)+(d : ℝ) ≤ (Fintype.card ι : ℝ) := by nlinarith
    exact_mod_cast h
  have he_le : e ≤ Fintype.card ι := by omega
  obtain ⟨S,hScard,hjoint⟩ := fullUDCardCore dom d e hd hradius f A (by
    intro z hz
    obtain ⟨w,hw,hrel⟩ := hclose z hz
    refine ⟨w,hw,?_⟩
    have hh : (hammingDist (f 0 + z • f 1) w : ℝ) ≤
        δ * (Fintype.card ι : ℝ) := by
      exact (div_le_iff₀ hn).mp hrel
    exact Nat.le_floor hh) hcard
  refine ⟨S,?_,hjoint⟩
  have hcast : (Fintype.card ι : ℝ) - (e : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (show Fintype.card ι-e ≤ S.card from hScard)
  nlinarith

/-- Full conservative unique-decoding proximity generator. Positive code
dimension and nonempty domain are explicit; the error remains n/|F|. -/
theorem reedSolomonCode_isProximityGenerator_fullUD [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) (d : ℕ) (hd : 1 ≤ d) :
    IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  classical
  intro f δ hδ0 hδB hpr
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδ2 : (d : ℝ) < (1-2*δ) * (Fintype.card ι : ℝ) := by
    have hρ : (d : ℝ) / (Fintype.card ι : ℝ) < 1-2*δ := by linarith
    exact (div_lt_iff₀ hn).mp hρ
  let A : Finset F := Finset.univ.filter
    (fun z => close δ (reedSolomonCode dom d) (f 0 + z • f 1))
  have hpr_eq : (affineGenerator F).pr
      (fun r => close δ (reedSolomonCode dom d) (comb r f)) =
      (A.card : ℝ) / (Fintype.card F : ℝ) := by
    unfold ProximityGenerator.pr
    have hcomb : ∀ z : F, comb ((affineGenerator F).gen z) f = f 0 + z • f 1 :=
      fun z => funext fun x => by rw [comb_affineGenerator]; rfl
    have hfilter : (Finset.univ.filter fun ω : (affineGenerator F).Seed =>
        close δ (reedSolomonCode dom d) (comb ((affineGenerator F).gen ω) f)) = A := by
      refine Finset.filter_congr fun z _ => ?_
      rw [hcomb z]
    rw [hfilter]
    calc ∑ ω ∈ A, (affineGenerator F).weight ω
        = ∑ _ω ∈ A, ((Fintype.card F : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun ω _ => rfl
      _ = (A.card : ℝ) * ((Fintype.card F : ℝ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (A.card : ℝ) / (Fintype.card F : ℝ) := (div_eq_mul_inv _ _).symm
  have hcard : Fintype.card ι < A.card := by
    rw [hpr_eq, div_lt_div_iff_of_pos_right hF] at hpr
    exact_mod_cast hpr
  exact correlatedAgreement_of_many_close_fullUD dom hd hδ0 hδ2 f A
    (fun z hz => (Finset.mem_filter.mp hz).2) hcard

/-- Mutual correlated agreement at the same full-UD radius, via the existing
RS minimum-distance and WHIR CA-to-MCA theorem. -/
theorem hasMutualCorrelatedAgreement_fullUD [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F)
    dom d (reedSolomonCode_isProximityGenerator_fullUD dom d hd)
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

/-- Existing FRI fold-distance interface, now discharged up to full UD. -/
theorem foldDistancePreserving_fullUD {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype F] [Nonempty ι] [Nonempty κ] {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) (d : ℕ) (hd : 1 ≤ d) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδB : δ < 1-(1+(d : ℝ)/(Fintype.card κ : ℝ))/2) :
    FoldDistancePreserving D (2*d) d δ (Fintype.card κ) := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact foldDistancePreserving_of_isProximityGenerator D d
    (reedSolomonCode_isProximityGenerator_fullUD domSq d hd) hδ0 hδB
    (le_of_eq (div_mul_cancel₀ _ (ne_of_gt hF)))

/-- info: 'Minidregg.Selvage.reedSolomonCode_isProximityGenerator_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reedSolomonCode_isProximityGenerator_fullUD

/-- info: 'Minidregg.Selvage.hasMutualCorrelatedAgreement_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasMutualCorrelatedAgreement_fullUD

/-- info: 'Minidregg.Selvage.foldDistancePreserving_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms foldDistancePreserving_fullUD

/-- info: 'Minidregg.Selvage.correlatedAgreement_of_many_close_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms correlatedAgreement_of_many_close_fullUD

end Minidregg.Selvage
