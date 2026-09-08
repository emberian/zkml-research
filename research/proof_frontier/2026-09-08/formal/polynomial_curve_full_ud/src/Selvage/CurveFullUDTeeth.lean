/- Positive-radius non-codeword premises and a concrete RS falsifier for
removing the curve-degree factor from the exceptional-scalar bound. -/
import Selvage.CurveProximityGapFullUD

namespace Minidregg.Selvage
open Polynomial Finset
open scoped BigOperators Classical

namespace CurveFullUDWitness
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def legalWord (j : ℕ) (i : Fin 5) : ZMod 101 := j + dom i
def corruptedWord (j : ℕ) (i : Fin 5) : ZMod 101 := legalWord j i + if i=0 then 1 else 0

theorem legalWord_mem (j : ℕ) : legalWord j ∈ reedSolomonCode dom 2 := by
  apply mem_reedSolomonCode_iff.mpr
  refine ⟨Polynomial.C (j : ZMod 101) + Polynomial.X, ?_, ?_⟩
  · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)) (by norm_num))
  · intro i
    simp [legalWord]

theorem corrupted_premise_inhabited (M : ℕ) (hM : 1 ≤ M) (hM8 : M ≤ 8) :
    CurveFullUDPremise M dom 2 1 (fun j => corruptedWord j.val) Finset.univ := by
  refine ⟨hM, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
    omega
  · intro z hz
    let v : Fin (M+1) → Fin 5 → ZMod 101 := fun j => legalWord j.val
    refine ⟨comb (fun j => z^j.val) v, comb_mem _ (fun j => legalWord_mem j.val), ?_⟩
    have hsubset : (Finset.univ.filter (fun i => curveWord (M := M) (fun j => corruptedWord j.val) z i ≠
        comb (fun j => z^j.val) v i)) ⊆ ({0} : Finset (Fin 5)) := by
      intro i hi
      by_contra hn
      have hi0 : i ≠ 0 := by simpa using hn
      have heq : curveWord (fun j : Fin (M+1) => corruptedWord j.val) z i =
          comb (fun j => z^j.val) v i := by
        simp [curveWord, comb, corruptedWord, v, hi0]
      exact (Finset.mem_filter.mp hi).2 heq
    simpa [hammingDist] using Finset.card_le_card hsubset

theorem zero_error_premise_inhabited (M : ℕ) (hM : 1 ≤ M) (hM8 : M ≤ 8) :
    CurveFullUDPremise M dom 2 0 (fun j => legalWord j.val) Finset.univ := by
  refine ⟨hM, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
    omega
  · intro z hz
    refine ⟨curveWord (M := M) (fun j => legalWord j.val) z,
      comb_mem _ (fun j => legalWord_mem j.val), ?_⟩
    simp

theorem zero_error_core_fires :
    ∃ S : Finset (Fin 5), 5 ≤ S.card ∧
      ∀ j : Fin 8, ∃ w ∈ reedSolomonCode dom 2,
        AgreesOn S (legalWord j.val) w := by
  have h := zero_error_premise_inhabited 7 (by decide) (by decide)
  exact curveFullUDCardCore 7 dom 2 0 h.1 h.2.1 h.2.2.1
    (fun j => legalWord j.val) Finset.univ h.2.2.2.2 h.2.2.2.1

theorem corrupted_actual_error (j : ℕ) : corruptedWord j 0 ≠ legalWord j 0 := by
  simp [corruptedWord]

theorem corrupted_distance_one (j : ℕ) :
    hammingDist (corruptedWord j) (legalWord j) = 1 := by
  have hs : (Finset.univ.filter (fun i : Fin 5 => i=0)) = {0} := by
    ext i
    simp
  simpa [hammingDist, corruptedWord] using congrArg Finset.card hs

theorem corrupted_not_mem (j : ℕ) : corruptedWord j ∉ reedSolomonCode dom 2 := by
  intro hmem
  have hne : corruptedWord j ≠ legalWord j := fun h =>
    corrupted_actual_error j (congrFun h 0)
  have h := reedSolomonCode_minDist dom 2 (corruptedWord j) hmem
    (legalWord j) (legalWord_mem j) hne
  norm_num [relDist, corrupted_distance_one] at h

end CurveFullUDWitness

namespace CurveDegreeTeeth
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def dom : Fin 2 ↪ ZMod 17 where
  toFun i := i.val
  inj' := by
    intro a b h
    apply Fin.ext
    have ha : a.val < 17 := lt_trans a.isLt (by decide)
    have hb : b.val < 17 := lt_trans b.isLt (by decide)
    have := congrArg ZMod.val h
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

def coeffs : Fin 8 → ZMod 17 := ![0,2,-3,1,0,0,0,0]
def words (j : Fin 8) (i : Fin 2) : ZMod 17 := coeffs j * dom i

theorem curve_at_three_roots (z : ZMod 17) (hz : z ∈ ({0,1,2} : Finset (ZMod 17))) :
    curveWord words z = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl <;>
    ext i <;> fin_cases i <;>
    norm_num [curveWord, comb, words, coeffs, dom, Fin.sum_univ_succ]

theorem three_good_challenges :
    ∃ A : Finset (ZMod 17), 2 < A.card ∧
      ∀ z ∈ A, close (1/5 : ℝ) (reedSolomonCode dom 1) (curveWord words z) := by
  refine ⟨{0,1,2}, by decide, ?_⟩
  intro z hz
  rw [curve_at_three_roots z hz]
  exact close_of_mem (reedSolomonCode dom 1).zero_mem (by norm_num)

theorem no_correlated_agreement :
    ¬ CorrelatedAgreement (reedSolomonCode dom 1) (1/5 : ℝ) words := by
  intro h
  obtain ⟨S,hS,hag⟩ := h
  have hS2 : 2 ≤ S.card := by
    norm_num at hS
    have hlt : (1 : ℝ) < S.card := by linarith
    exact_mod_cast hlt
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by
    have hle := Finset.card_le_univ S
    norm_num at hle ⊢
    omega)
  obtain ⟨w,hw,ha⟩ := hag (3 : Fin 8)
  obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hp0 : p.natDegree = 0 := by
    by_cases hz : p = 0
    · simp [hz]
    · have hn := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp
      omega
  have hpC := Polynomial.eq_C_of_natDegree_eq_zero hp0
  have h0 := (ha 0 (by simp [hSuniv])).trans (heval 0)
  have h1 := (ha 1 (by simp [hSuniv])).trans (heval 1)
  rw [hpC] at h0 h1
  norm_num [words, coeffs, dom] at h0 h1
  exact zero_ne_one (h0.trans h1.symm)

theorem strict_radius_admissible :
    (0 : ℝ) < 1/5 ∧ (1 : ℝ) < (1-2*(1/5 : ℝ))*Fintype.card (Fin 2) := by
  norm_num

/-- The curve family is admissible, has more than n good scalars, yet lacks
CA: retaining the affine error n/|F| would be false. -/
theorem unscaled_affine_bound_falsifier :
    (∃ A : Finset (ZMod 17), 2 < A.card ∧
      ∀ z ∈ A, close (1/5 : ℝ) (reedSolomonCode dom 1) (curveWord words z)) ∧
    ¬ CorrelatedAgreement (reedSolomonCode dom 1) (1/5 : ℝ) words :=
  ⟨three_good_challenges, no_correlated_agreement⟩

end CurveDegreeTeeth
end Minidregg.Selvage

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.legalWord_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.legalWord_mem

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.corrupted_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.corrupted_premise_inhabited

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.zero_error_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.zero_error_premise_inhabited

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.zero_error_core_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.zero_error_core_fires

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.corrupted_actual_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.corrupted_actual_error

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.corrupted_distance_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.corrupted_distance_one

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.corrupted_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.corrupted_not_mem

/-- info: 'Minidregg.Selvage.CurveDegreeTeeth.curve_at_three_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveDegreeTeeth.curve_at_three_roots

/-- info: 'Minidregg.Selvage.CurveDegreeTeeth.three_good_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveDegreeTeeth.three_good_challenges

/-- info: 'Minidregg.Selvage.CurveDegreeTeeth.no_correlated_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveDegreeTeeth.no_correlated_agreement

/-- info: 'Minidregg.Selvage.CurveDegreeTeeth.strict_radius_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveDegreeTeeth.strict_radius_admissible

/-- info: 'Minidregg.Selvage.CurveDegreeTeeth.unscaled_affine_bound_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveDegreeTeeth.unscaled_affine_bound_falsifier

