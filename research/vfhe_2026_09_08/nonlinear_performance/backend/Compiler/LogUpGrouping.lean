/- Algebraic certificate for the existing LogUp multi-element fraction.
The Rust successor preserves tuple/count order and uses this four-term grouping.
This module does not prove native code refinement or a cryptographic soundness bound. -/
import Mathlib

namespace Minidregg.Compiler.LogUpGrouping
set_option autoImplicit false

variable {F : Type*} [Field F]

def denominator (d : Fin 4 → F) : F := d 0*d 1*d 2*d 3
def numerator (m d : Fin 4 → F) : F :=
  m 0*d 1*d 2*d 3 + d 0*m 1*d 2*d 3 +
  d 0*d 1*m 2*d 3 + d 0*d 1*d 2*m 3

def fractions (m d : Fin 4 → F) : F :=
  m 0/d 0 + m 1/d 1 + m 2/d 2 + m 3/d 3

def Transition (s t : F) (m d : Fin 4 → F) : Prop :=
  (t-s)*denominator d=numerator m d

/-- Signed multiplicities are arbitrary field values; each denominator is the
existing shared-bus challenge minus its compressed tuple. Zero denominators are
an explicit excluded event, just as for ungrouped LogUp. -/
theorem cleared_fraction (m d : Fin 4 → F) (hd : ∀ i,d i≠0) :
    fractions m d * denominator d = numerator m d := by
  unfold fractions denominator numerator
  field_simp [hd 0,hd 1,hd 2,hd 3]

theorem transition_iff (s t : F) (m d : Fin 4 → F) (hd : ∀ i,d i≠0) :
    Transition s t m d ↔ t-s=fractions m d := by
  have hden : denominator d≠0 := by
    unfold denominator
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hd 0) (hd 1)) (hd 2)) (hd 3)
  unfold Transition
  rw [←cleared_fraction m d hd]
  exact mul_left_inj' hden

/-- Group boundaries do not alter the rational contribution's total. The native
patch separately checks that flattening its groups reproduces the input list. -/
theorem regroup_sum (groups : List (List F)) :
    (groups.map List.sum).sum = groups.flatten.sum := by
  exact List.sum_flatten.symm

def SignedWitness : Prop :=
  let m : Fin 4 → ℚ := ![1,-2,3,-4]
  let d : Fin 4 → ℚ := ![1,2,3,4]
  (∀ i,d i≠0) ∧ Transition 5 5 m d

theorem signedWitness : SignedWitness := by
  dsimp [SignedWitness,Transition,denominator,numerator]
  constructor
  · intro i
    fin_cases i <;> norm_num
  · norm_num

def ZeroDenominatorFalsifier : Prop :=
  let m : Fin 4 → ℚ := fun _ => 1
  let d : Fin 4 → ℚ := fun _ => 0
  Transition 0 1 m d ∧ ¬(1-0=fractions m d)

theorem zeroDenominatorFalsifier : ZeroDenominatorFalsifier := by
  norm_num [ZeroDenominatorFalsifier,Transition,denominator,numerator,fractions]

def SignFalsifier : Prop :=
  let d : Fin 4 → ℚ := fun _ => 1
  Transition 0 (-2) ![1,-2,3,-4] d ∧ ¬Transition 0 (-2) ![1,2,3,4] d

theorem signFalsifier : SignFalsifier := by
  dsimp [SignFalsifier,Transition,denominator,numerator]
  norm_num

end Minidregg.Compiler.LogUpGrouping

/-- info: 'Minidregg.Compiler.LogUpGrouping.cleared_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.LogUpGrouping.cleared_fraction

/-- info: 'Minidregg.Compiler.LogUpGrouping.transition_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.LogUpGrouping.transition_iff

/-- info: 'Minidregg.Compiler.LogUpGrouping.regroup_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.LogUpGrouping.regroup_sum

/-- info: 'Minidregg.Compiler.LogUpGrouping.signedWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.LogUpGrouping.signedWitness

/-- info: 'Minidregg.Compiler.LogUpGrouping.zeroDenominatorFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.LogUpGrouping.zeroDenominatorFalsifier

/-- info: 'Minidregg.Compiler.LogUpGrouping.signFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.LogUpGrouping.signFalsifier
