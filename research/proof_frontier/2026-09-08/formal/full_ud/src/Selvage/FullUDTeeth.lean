/-
# A falsifier for dropping the full unique-decoding radius premise

The concrete pair was found by evidence/derive.py in the 2026-09-08 research
lane. The conclusions here are kernel proofs, over the existing RS code.
-/
import Selvage.FullUDStatement
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

namespace Minidregg.Selvage.FullUDTeeth

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def dom : Fin 6 ↪ ZMod 7 where
  toFun i := i.val
  inj' := by
    intro a b hab
    have ha : a.val < 7 := lt_trans a.isLt (by decide)
    have hb : b.val < 7 := lt_trans b.isLt (by decide)
    apply Fin.ext
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

private def f0 : Fin 6 → ZMod 7 := ![3,0,4,1,3,3]
private def f1 : Fin 6 → ZMod 7 := ![6,4,1,1,6,3]
private def pair : Fin 2 → Fin 6 → ZMod 7 := ![f0,f1]
private def affine (a b : ZMod 7) : Fin 6 → ZMod 7 := fun i => a + b * dom i
private def bestA : ZMod 7 → ZMod 7 := ![3,0,1,0,3,2,2]
private def bestB : ZMod 7 → ZMod 7 := ![4,4,0,0,6,6,4]

private theorem affine_mem (a b : ZMod 7) :
    affine a b ∈ reedSolomonCode dom 2 := by
  apply mem_reedSolomonCode_iff.mpr
  refine ⟨Polynomial.C b * Polynomial.X + Polynomial.C a,
    Polynomial.degree_linear_lt, ?_⟩
  intro i
  simp [affine, add_comm]

private theorem codeword_affine {w : Fin 6 → ZMod 7}
    (hw : w ∈ reedSolomonCode dom 2) : ∃ a b, w = affine a b := by
  obtain ⟨p, hp, heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hnat : p.natDegree ≤ 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
      omega
  obtain ⟨b,a,hpaff⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hnat
  refine ⟨a,b,funext fun i => ?_⟩
  rw [heval i, hpaff]
  simp [affine, add_comm]

/-- Every scalar has a nearby codeword at the forbidden radius. -/
theorem all_folds_close :
    ∀ z : ZMod 7, ∃ w ∈ reedSolomonCode dom 2,
      hammingDist (f0 + z • f1) w ≤ 3 := by
  intro z
  refine ⟨affine (bestA z) (bestB z), affine_mem _ _, ?_⟩
  fin_cases z <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem common_affine_card : ∀ a b c d : ZMod 7,
    (Finset.univ.filter fun i : Fin 6 =>
      f0 i = affine a b i ∧ f1 i = affine c d i).card ≤ 2 := by
  decide +kernel

/-- No pair of degree-below-two polynomials explains three common positions. -/
theorem no_joint_three :
    ¬ ∃ S : Finset (Fin 6), 3 ≤ S.card ∧
      ∀ j, ∃ w ∈ reedSolomonCode dom 2, AgreesOn S (pair j) w := by
  rintro ⟨S,hScard,hjoint⟩
  obtain ⟨w0,hw0,h0⟩ := hjoint 0
  obtain ⟨w1,hw1,h1⟩ := hjoint 1
  obtain ⟨a,b,rfl⟩ := codeword_affine hw0
  obtain ⟨c,d,rfl⟩ := codeword_affine hw1
  have hsub : S ⊆ Finset.univ.filter (fun i : Fin 6 =>
      f0 i = affine a b i ∧ f1 i = affine c d i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      exact ⟨by simpa [pair] using h0 i hi, by simpa [pair] using h1 i hi⟩⟩
  have hcard := (Finset.card_le_card hsub).trans (common_affine_card a b c d)
  omega

/-- Deleting `2e+d≤n` makes the proposed core false, despite all seven
scalars satisfying the good-slope premise on a six-point domain. -/
theorem radius_hypothesis_necessary : ¬ FullUDCardCore dom 2 3 := by
  intro h
  apply no_joint_three
  have h' := h pair Finset.univ (by
    intro z hz
    simpa [pair] using all_folds_close z) (by norm_num)
  simpa using h'

/-- info: 'Minidregg.Selvage.FullUDTeeth.radius_hypothesis_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radius_hypothesis_necessary

/-- info: '_private.Selvage.FullUDTeeth.0.Minidregg.Selvage.FullUDTeeth.affine_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_mem

/-- info: '_private.Selvage.FullUDTeeth.0.Minidregg.Selvage.FullUDTeeth.codeword_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codeword_affine

/-- info: 'Minidregg.Selvage.FullUDTeeth.all_folds_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_folds_close

/-- info: '_private.Selvage.FullUDTeeth.0.Minidregg.Selvage.FullUDTeeth.common_affine_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms common_affine_card

/-- info: 'Minidregg.Selvage.FullUDTeeth.no_joint_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_joint_three

end Minidregg.Selvage.FullUDTeeth
