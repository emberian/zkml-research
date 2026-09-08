import Compiler.SignedMatrix

namespace Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.IntegerCertificateEmission Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000

structure Layout where
  groups : Nat
  digits : Nat
  rows : Nat
  limbBits : Nat
  width : Nat
  carryBits : Nat

def Layout.base (p : Layout) := 2^p.limbBits
def Layout.scalars (p : Layout) := p.groups*p.digits
def Layout.rowVars (p : Layout) := p.width*(1+p.limbBits)+2*(p.width+1)*(1+p.carryBits)
def Layout.nVars (p : Layout) := p.scalars*(1+p.limbBits)+p.rows*p.rowVars
def groupDigit (p : Layout) : Fin p.groups × Fin p.digits ≃ Fin p.scalars := finProdFinEquiv
def scalarWire (p : Layout) (i : Fin p.scalars) : Nat := i.val
def scalarBits (p : Layout) (i : Fin p.scalars) (j : Fin p.limbBits) : Nat := p.scalars+p.limbBits*i.val+j.val
def resultStart (p : Layout) (row : Fin p.rows) := p.scalars*(1+p.limbBits)+row.val*p.rowVars

def rowWires (p : Layout) (row : Fin p.rows) (right : Bool) : WeightedSumWires Nat p.width p.limbBits p.carryBits where
  result := fun i => resultStart p row+i.val
  resultBit := fun i j => resultStart p row+p.width+p.limbBits*i.val+j.val
  carry := fun i => resultStart p row+p.width*(1+p.limbBits)+(if right then (p.width+1)*(1+p.carryBits) else 0)+i.val
  carryBit := fun i j => resultStart p row+p.width*(1+p.limbBits)+(if right then (p.width+1)*(1+p.carryBits) else 0)+(p.width+1)+p.carryBits*i.val+j.val

def digitCoefficient (p : Layout) (matrix : Fin p.groups → Nat) (i : Fin p.scalars) : Nat :=
  matrix (groupDigit p|>.symm i).1*p.base^(groupDigit p|>.symm i).2.val

def decoded (p : Layout) (v : Nat → BabyBear) (g : Fin p.groups) : Nat :=
  ∑ d : Fin p.digits,p.base^d.val*(v (scalarWire p (groupDigit p (g,d)))).val

def rowSystem (p : Layout) (rows : Fin p.rows → Row p.groups) (i : Fin p.rows) : ConstraintSystem BabyBear Nat :=
  weightedSumGadget (leftConstant (rows i)) (digitCoefficient p (leftCoefficient (rows i))) (scalarWire p) (rowWires p i false) ++
  weightedSumGadget (rightConstant (rows i)) (digitCoefficient p (rightCoefficient (rows i))) (scalarWire p) (rowWires p i true)

def system (p : Layout) (rows : Fin p.rows → Row p.groups) : ConstraintSystem BabyBear Nat :=
  AirBignum.limbRangeSystem (scalarWire p) (scalarBits p) ++ (List.finRange p.rows).flatMap (rowSystem p rows)

structure Capacity (p : Layout) (rows : Fin p.rows → Row p.groups) : Prop where
  baseField : p.base ≤ babyBearP
  carryField : 2^p.carryBits ≤ babyBearP
  leftBudget : p.base-1+p.scalars*(p.base-1)*(p.base-1)+(2^p.carryBits-1) < babyBearP
  rightBudget : p.base-1+p.base*(2^p.carryBits-1) < babyBearP
  constants : ∀ i,leftConstant (rows i) < p.base^p.width ∧ rightConstant (rows i) < p.base^p.width
  coefficients : ∀ i j,digitCoefficient p (leftCoefficient (rows i)) j < p.base^p.width ∧
    digitCoefficient p (rightCoefficient (rows i)) j < p.base^p.width

def SourceSound : Prop := ∀ p rows,Capacity p rows → ∀ v,systemAccepts v (system p rows) →
  ∀ i,eval (rows i) (decoded p v)=0

theorem digit_linearization (p : Layout) (matrix : Fin p.groups → Nat) (v : Nat → BabyBear) :
    (∑ i : Fin p.scalars,digitCoefficient p matrix i*(v (scalarWire p i)).val) =
      ∑ g,matrix g*decoded p v g := by
  rw [← (groupDigit p).sum_comp]
  simp only [digitCoefficient,Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp [decoded,Finset.mul_sum,mul_assoc]

theorem sourceSound : SourceSound := by
  intro p rows cap v hs i
  obtain ⟨hr,hh⟩ := (systemAccepts_append v _ _).mp hs
  have hrow : systemAccepts v (rowSystem p rows i) := by
    intro t ht
    exact hh t (List.mem_flatMap.mpr ⟨i,by simp,ht⟩)
  obtain ⟨hl,hrr⟩ := (systemAccepts_append v _ _).mp hrow
  have run (c : Nat) (matrix : Fin p.groups → Nat) (w : WeightedSumWires Nat p.width p.limbBits p.carryBits)
      (hc : c < p.base^p.width) (hm : ∀ j,digitCoefficient p matrix j < p.base^p.width)
      (ha : systemAccepts v (weightedSumGadget c (digitCoefficient p matrix) (scalarWire p) w)) :
      Bignum.denoteNat p.base (AirBignum.limbVals v w.result) = c+∑ g,matrix g*decoded p v g := by
    have h := ranged_weighted_sound cap.baseField cap.carryField cap.baseField hc
      (digitCoefficient p matrix) hm cap.leftBudget cap.rightBudget v (scalarWire p) (scalarBits p) w hr ha
    simpa only [digit_linearization] using h
  have hleft := run _ _ _ (cap.constants i).1 (fun j => (cap.coefficients i j).1) hl
  have hright := run _ _ _ (cap.constants i).2 (fun j => (cap.coefficients i j).2) hrr
  apply (splitSound (rows i) (decoded p v)).mp
  exact hleft.symm.trans hright

end Minidregg.Compiler.SignedMatrix

/-- info: 'Minidregg.Compiler.SignedMatrix.digit_linearization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.digit_linearization

/-- info: 'Minidregg.Compiler.SignedMatrix.sourceSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.sourceSound
