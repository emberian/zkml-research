/- Small exact witness for the actual eightfold source-farness consumer. -/
import Selvage.ArityEightSampling
import Selvage.PowerTwoRootFolding
import Mathlib.Tactic.ReduceModChar

namespace Minidregg.Selvage.ArityEight.Witnesses
open Polynomial
open scoped Classical
instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
abbrev F := ZMod 17

/-- Certified exact root, with only fifteen small exponent checks. -/
theorem root_primitive : IsPrimitiveRoot (3 : F) (2^4) := by
  apply IsPrimitiveRoot.mk_of_lt
  · norm_num
  · decide
  · intro l hl hlt
    interval_cases l <;> decide

abbrev D₀ := PowerTwoRootFolding.data root_primitive (by decide) 0 (by decide)
abbrev D₁ := PowerTwoRootFolding.data root_primitive (by decide) 1 (by decide)
abbrev D₂ := PowerTwoRootFolding.data root_primitive (by decide) 2 (by decide)
abbrev dom (n : ℕ) := PowerTwoRootFolding.domain root_primitive n

def farWord : Fin 16 → F := fun i => (dom 0 i)^8

/-- Actual source degree is outside the legal window. -/
theorem farWord_not_mem : farWord ∉ reedSolomonCode (dom 0) 8 := by
  intro hw
  obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hne : (X^8 : Polynomial F) ≠ p := by
    intro heq
    rw [←heq] at hp
    norm_num at hp
  have hc := card_agreeSet_lt_of_ne (dom 0) (d := 9)
    (p := (X^8 : Polynomial F)) (by norm_num) (q := p) (hp.trans (by norm_num)) hne
  have hall : (Finset.univ.filter fun i =>
      (X^8 : Polynomial F).eval (dom 0 i) = p.eval (dom 0 i)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    simpa [farWord] using heval i
  rw [hall,Finset.card_univ] at hc
  norm_num [PowerTwoFriLevels] at hc

/-- Existing RS minimum distance supplies substantial positive farness. -/
theorem farWord_far : ¬close (1/5 : ℝ) (reedSolomonCode (dom 0) 8) farWord := by
  rintro ⟨w,hw,hclose⟩
  have hmem : farWord ∈ reedSolomonCode (dom 0) 9 :=
    mem_reedSolomonCode_iff.mpr ⟨X^8,by norm_num,fun i => by simp [farWord]⟩
  have hw' : w ∈ reedSolomonCode (dom 0) 9 := by
    obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
    exact mem_reedSolomonCode_iff.mpr ⟨p,hp.trans (by norm_num),heval⟩
  have h := reedSolomonCode_minDist (dom 0) 9 farWord hmem w hw'
    (fun heq => farWord_not_mem (heq ▸ hw))
  norm_num [PowerTwoFriLevels] at h
  linarith

/-- Every scalar sends the actual far source to [1,-1]. -/
theorem fold_zero (β : F) : fold8 D₀ D₁ D₂ farWord β 0 = 1 := by
  simp [fold8,fold,foldEven,foldOdd,farWord,dom,D₀,D₁,D₂,
    PowerTwoRootFolding.data,PowerTwoRootFolding.domain,PowerTwoRootFolding.levelRoot,
    PowerTwoRootFolding.sectionIndex,PowerTwoRootFolding.negativeIndex, F]
  reduce_mod_char
  norm_num [div_eq_mul_inv, show (2:F)⁻¹ = 9 by decide]
  reduce_mod_char

theorem fold_one (β : F) : fold8 D₀ D₁ D₂ farWord β 1 = -1 := by
  simp [fold8,fold,foldEven,foldOdd,farWord,dom,D₀,D₁,D₂,
    PowerTwoRootFolding.data,PowerTwoRootFolding.domain,PowerTwoRootFolding.levelRoot,
    PowerTwoRootFolding.sectionIndex,PowerTwoRootFolding.negativeIndex, F]
  reduce_mod_char
  norm_num [div_eq_mul_inv, show (2:F)⁻¹ = 9 by decide]
  reduce_mod_char

/-- A real far source and accepting query schedule coexist. -/
theorem accepted_zero_seed (β : F) (q : ℕ) :
    Crossing (reedSolomonCode (dom 3) 1) (1/10 : ℝ)
      (fold8 D₀ D₁ D₂ farWord) (fun _ _ => 1) q (β,fun _ => 0) := by
  refine ⟨⟨fun _ => 1,mem_reedSolomonCode_one_iff.mpr (fun _ _ => rfl),?_⟩,?_⟩
  · norm_num [relDist,hammingDist]
  · intro a
    exact (fold_zero β).symm

/-- The same actual source and next word reject query one. -/
theorem rejected_one_seed (β : F) :
    ¬Crossing (reedSolomonCode (dom 3) 1) (1/10 : ℝ)
      (fold8 D₀ D₁ D₂ farWord) (fun _ _ => 1) 1 (β,fun _ => 1) := by
  intro h
  have heq := h.2 0
  change (1:F) = fold8 D₀ D₁ D₂ farWord β 1 at heq
  rw [fold_one] at heq
  exact (by decide : (1:F) ≠ -1) heq

/-- All radius, rate, positive-degree and source-farness premises fire. -/
theorem sampled_bound_fires (q : ℕ) :
    uniformProb (F × (Fin q → Fin 2))
      (Crossing (reedSolomonCode (dom 3) 1) (1/10 : ℝ)
        (fold8 D₀ D₁ D₂ farWord) (fun _ _ => 1) q) ≤ 14/17+(9/10:ℝ)^q := by
  have h := fold8_sampled_crossing D₀ D₁ D₂ (d := 1) (by decide)
    (θ := (1/5:ℝ)) (δ := (1/10:ℝ)) (τ := (1/10:ℝ)) (by norm_num)
    (by norm_num [PowerTwoFriLevels]) (by norm_num) (by norm_num)
    farWord (fun _ _ => 1) q farWord_far
  norm_num [PowerTwoFriLevels,ZMod.card] at h ⊢
  exact h

/-- The sampled expression is already nontrivial at this small positive instance. -/
theorem bound_nontrivial : (14/17 : ℝ)+(9/10:ℝ)^32 < 1 := by norm_num

end Minidregg.Selvage.ArityEight.Witnesses


/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.root_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.root_primitive

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.farWord_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.farWord_not_mem

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.farWord_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.farWord_far

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.fold_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.fold_zero

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.fold_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.fold_one

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.accepted_zero_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.accepted_zero_seed

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.rejected_one_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.rejected_one_seed

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.sampled_bound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.sampled_bound_fires

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.bound_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.bound_nontrivial

