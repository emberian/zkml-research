import Compiler.BfvExpiryLayout

namespace Minidregg.Compiler.BfvOperationWitness
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

inductive Wire where
  | value (kind digit : Nat)
  | slack (kind digit : Nat)
  | bound (digit : Nat)
  | valueBit (kind digit bit : Nat)
  | slackBit (kind digit bit : Nat)
  | boundBit (digit bit : Nat)
  | addCarry (kind digit : Nat)
  | quotient
  | quotientBit (bit : Nat)
  | carry (digit : Nat)
  | carryBit (digit bit : Nat)

def canonical (kind : Nat) : AirBignum.AddWires Wire 7 6 where
  x := fun i => .value kind i.val
  y := fun i => .slack kind i.val
  z := fun i => .bound i.val
  xBit := fun i j => .valueBit kind i.val j.val
  yBit := fun i j => .slackBit kind i.val j.val
  zBit := fun i j => .boundBit i.val j.val
  carry := fun i => .addCarry kind i.val

def weightedWires : BfvLinearCombination.RowWires Wire where
  canonical := fun kind => canonical kind.val
  quotient := .quotient
  quotientBit := fun j => .quotientBit j.val
  carry := fun i => .carry i.val
  carryBit := fun i j => .carryBit i.val j.val

def expiryWires : BfvExpiry.RowWires Wire where
  canonical := fun kind => canonical kind.val
  quotient := .quotient
  quotientBit := fun j => .quotientBit j.val
  carry := fun i => .carry i.val
  carryBit := fun i j => .carryBit i.val j.val

def natAsg (values : Nat → Nat) (quotient offset : Nat) : Wire → Nat
  | .value k i => if i=0 then values k else 0
  | .slack k i => if i=0 then 30-values k else 0
  | .bound i => if i=0 then 30 else 0
  | .valueBit k i j => if i=0 then (values k/2^j)%2 else 0
  | .slackBit k i j => if i=0 then ((30-values k)/2^j)%2 else 0
  | .boundBit i j => if i=0 then (30/2^j)%2 else 0
  | .addCarry _ _ => 0
  | .quotient => quotient
  | .quotientBit j => (quotient/2^j)%2
  | .carry _ => offset
  | .carryBit _ j => (offset/2^j)%2

def asg (values : Nat → Nat) (quotient offset : Nat) (wire : Wire) : BabyBear :=
  natAsg values quotient offset wire

def weightedAsg := asg (fun k => if k=0 then 1 else if k=1 then 2 else 13) 0 8
def expiryAsg := asg (fun k => if k=0 then 17 else if k=1 then 23 else if k=2 then 9 else 0) 2 4

def WeightedPremise : Prop := systemAccepts weightedAsg (BfvLinearCombination.rowSystem 31 weightedWires)
def ExpiryPremise : Prop := systemAccepts expiryAsg (BfvExpiry.rowSystem 31 expiryWires)
def WeightedFalsifier : Prop := ∀ a : Wire → BabyBear,
  BfvLinearCombination.word a weightedWires 0 = 1 →
  BfvLinearCombination.word a weightedWires 1 = 2 →
  BfvLinearCombination.word a weightedWires 2 = 14 →
  ¬ systemAccepts a (BfvLinearCombination.rowSystem 31 weightedWires)
def ExpiryFalsifier : Prop := ∀ a : Wire → BabyBear,
  BfvExpiry.word a expiryWires 0 = 17 → BfvExpiry.word a expiryWires 1 = 23 →
  BfvExpiry.word a expiryWires 2 = 9 → BfvExpiry.word a expiryWires 3 = 1 →
  ¬ systemAccepts a (BfvExpiry.rowSystem 31 expiryWires)

theorem weightedCheck : (BfvLinearCombination.rowSystem 31 weightedWires).all
    (fun term => eval weightedAsg term == 0) = true := by decide +kernel

theorem expiryCheck : (BfvExpiry.rowSystem 31 expiryWires).all
    (fun term => eval expiryAsg term == 0) = true := by decide +kernel

theorem weightedPremise : WeightedPremise := by
  simpa [WeightedPremise,List.all_eq_true,systemAccepts,accepts] using weightedCheck

theorem expiryPremise : ExpiryPremise := by
  simpa [ExpiryPremise,List.all_eq_true,systemAccepts,accepts] using expiryCheck

theorem weightedFalsifier : WeightedFalsifier := by
  intro a ha hb ho hs
  have h := (BfvLinearCombination.rowSystem_sound 31 (by decide) (by decide) weightedWires a hs).2
  rw [ha,hb,ho] at h
  norm_num at h

theorem expiryFalsifier : ExpiryFalsifier := by
  intro a ha hf hold ho hs
  have h := (BfvExpiry.rowSystem_sound 31 (by decide) (by decide) expiryWires a hs).2
  rw [ha,hf,hold,ho] at h
  norm_num at h

theorem weightedWords :
    BfvLinearCombination.word weightedAsg weightedWires 0 = 1 ∧
    BfvLinearCombination.word weightedAsg weightedWires 1 = 2 ∧
    BfvLinearCombination.word weightedAsg weightedWires 2 = 13 := by decide +kernel

theorem expiryWords :
    BfvExpiry.word expiryAsg expiryWires 0 = 17 ∧ BfvExpiry.word expiryAsg expiryWires 1 = 23 ∧
    BfvExpiry.word expiryAsg expiryWires 2 = 9 ∧ BfvExpiry.word expiryAsg expiryWires 3 = 0 := by decide +kernel

/-- info: 'Minidregg.Compiler.BfvOperationWitness.weightedCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weightedCheck
/-- info: 'Minidregg.Compiler.BfvOperationWitness.expiryCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expiryCheck
/-- info: 'Minidregg.Compiler.BfvOperationWitness.weightedPremise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weightedPremise
/-- info: 'Minidregg.Compiler.BfvOperationWitness.expiryPremise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expiryPremise
/-- info: 'Minidregg.Compiler.BfvOperationWitness.weightedFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weightedFalsifier
/-- info: 'Minidregg.Compiler.BfvOperationWitness.expiryFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expiryFalsifier
/-- info: 'Minidregg.Compiler.BfvOperationWitness.weightedWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weightedWords
/-- info: 'Minidregg.Compiler.BfvOperationWitness.expiryWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expiryWords

end Minidregg.Compiler.BfvOperationWitness
