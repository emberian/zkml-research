/- A row-sensitive layout for the same signed matrix. Scalar decompositions are
shared once; each result/carry chain receives its own compile-time capacity. -/
import Compiler.SignedMatrixEmit

namespace Minidregg.Compiler.ProfiledMatrix
open Minidregg.Compiler Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler.BfvSignedAccumulatorAir Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000

structure RowLayout (rows : Nat) where
  width : Fin rows → Nat
  carryBits : Fin rows → Nat

def rowVars {p : Layout} (q : RowLayout p.rows) (i : Fin p.rows) :=
  q.width i*(1+p.limbBits)+2*(q.width i+1)*(1+q.carryBits i)
def nVars (p : Layout) (q : RowLayout p.rows) := p.scalars*(1+p.limbBits)+∑ i,rowVars q i
def resultStart (p : Layout) (q : RowLayout p.rows) (row : Fin p.rows) :=
  p.scalars*(1+p.limbBits)+∑ i : Fin p.rows,if i.val<row.val then rowVars q i else 0

def rowWires (p : Layout) (q : RowLayout p.rows) (row : Fin p.rows) (right : Bool) :
    WeightedSumWires Nat (q.width row) p.limbBits (q.carryBits row) :=
  let start := resultStart p q row
  let width := q.width row
  let bits := q.carryBits row
  let carryStart := start+width*(1+p.limbBits)+(if right then (width+1)*(1+bits) else 0)
  { result := fun i => start+i.val
    resultBit := fun i j => start+width+p.limbBits*i.val+j.val
    carry := fun i => carryStart+i.val
    carryBit := fun i j => carryStart+(width+1)+bits*i.val+j.val }

def rowSystem (p : Layout) (q : RowLayout p.rows) (rows : Fin p.rows → Row p.groups) (i : Fin p.rows) : ConstraintSystem BabyBear Nat :=
  weightedSumGadget (leftConstant (rows i)) (digitCoefficient p (leftCoefficient (rows i))) (scalarWire p) (rowWires p q i false) ++
  weightedSumGadget (rightConstant (rows i)) (digitCoefficient p (rightCoefficient (rows i))) (scalarWire p) (rowWires p q i true)

def system (p : Layout) (q : RowLayout p.rows) (rows : Fin p.rows → Row p.groups) : ConstraintSystem BabyBear Nat :=
  AirBignum.limbRangeSystem (scalarWire p) (scalarBits p) ++ (List.finRange p.rows).flatMap (rowSystem p q rows)

structure Capacity (p : Layout) (q : RowLayout p.rows) (rows : Fin p.rows → Row p.groups) : Prop where
  baseField : p.base ≤ babyBearP
  carryField : ∀ i,2^(q.carryBits i) ≤ babyBearP
  leftBudget : ∀ i,p.base-1+p.scalars*(p.base-1)*(p.base-1)+(2^(q.carryBits i)-1) < babyBearP
  rightBudget : ∀ i,p.base-1+p.base*(2^(q.carryBits i)-1) < babyBearP
  constants : ∀ i,leftConstant (rows i) < p.base^(q.width i) ∧ rightConstant (rows i) < p.base^(q.width i)
  coefficients : ∀ i j,digitCoefficient p (leftCoefficient (rows i)) j < p.base^(q.width i) ∧
    digitCoefficient p (rightCoefficient (rows i)) j < p.base^(q.width i)

def SourceSound : Prop := ∀ p q rows,Capacity p q rows → ∀ asg,systemAccepts asg (system p q rows) →
  ∀ i,SignedMatrix.eval (rows i) (decoded p asg)=0

theorem sourceSound : SourceSound := by
  intro p q rows cap asg hs i
  obtain ⟨hr,hh⟩ := (systemAccepts_append asg _ _).mp hs
  have hrow : systemAccepts asg (rowSystem p q rows i) := by
    intro t ht
    exact hh t (List.mem_flatMap.mpr ⟨i,by simp,ht⟩)
  obtain ⟨hl,hrr⟩ := (systemAccepts_append asg _ _).mp hrow
  have run (c : Nat) (matrix : Fin p.groups → Nat)
      (w : WeightedSumWires Nat (q.width i) p.limbBits (q.carryBits i))
      (hc : c < p.base^(q.width i)) (hm : ∀ j,digitCoefficient p matrix j < p.base^(q.width i))
      (ha : systemAccepts asg (weightedSumGadget c (digitCoefficient p matrix) (scalarWire p) w)) :
      Bignum.denoteNat p.base (AirBignum.limbVals asg w.result)=c+∑ g,matrix g*decoded p asg g := by
    have h := ranged_weighted_sound cap.baseField (cap.carryField i) cap.baseField hc
      (digitCoefficient p matrix) hm (cap.leftBudget i) (cap.rightBudget i) asg (scalarWire p) (scalarBits p) w hr ha
    simpa only [digit_linearization] using h
  have hl' := run _ _ _ (cap.constants i).1 (fun j => (cap.coefficients i j).1) hl
  have hr' := run _ _ _ (cap.constants i).2 (fun j => (cap.coefficients i j).2) hrr
  exact (splitSound (rows i) (decoded p asg)).mp (hl'.symm.trans hr')

/-- Worst unsigned mass for bounded scalar groups; it contains no runtime witness. -/
def sideMassBound (p : Layout) (c : Nat) (matrix : Fin p.groups → Nat) :=
  c+(p.base^p.digits-1)*∑ g,matrix g

def digitMass (base : Nat) (x : Nat) := (Nat.digits base x).sum
/-- Conservative carry allocation from all coefficient digits. -/
def sideCarryBound (p : Layout) (matrix : Fin p.groups → Nat) := 1+∑ g,digitMass p.base (matrix g)

def autoLayout (p : Layout) (rows : Fin p.rows → Row p.groups) : RowLayout p.rows where
  width := fun i => 1+Nat.log2 (max (sideMassBound p (leftConstant (rows i)) (leftCoefficient (rows i)))
    (sideMassBound p (rightConstant (rows i)) (rightCoefficient (rows i))))/p.limbBits
  carryBits := fun i => 1+Nat.log2 (max (sideCarryBound p (leftCoefficient (rows i))) (sideCarryBound p (rightCoefficient (rows i))))

/-- info: 'Minidregg.Compiler.ProfiledMatrix.sourceSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.sourceSound

end Minidregg.Compiler.ProfiledMatrix
