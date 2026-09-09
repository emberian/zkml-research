/- Bit witness elimination for the existing row-profiled signed matrix. The
arithmetic terms are the unchanged weightedSumGadget constructors. -/
import Compiler.ProfiledMatrix
import Compiler.RangeCompletedMac
namespace Minidregg.Compiler.RangeProfiledMatrix
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.IntegerCertificateEmission
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

def weightedGates {J : Type} {n width limbBits carryBits : Nat} (c : Nat)
    (coeff : Fin n → Nat) (scalar : Fin n → J)
    (w : WeightedSumWires J width limbBits carryBits) : ConstraintSystem BabyBear J :=
  [vr (w.carry 0),vr (w.carry (Fin.last width))] ++ weightedEquationSystem c coeff scalar w

noncomputable def complete {J : Type} {width limbBits carryBits : Nat}
    (a : J → BabyBear) (w : WeightedSumWires J width limbBits carryBits) :
    WeightedSumWires BabyBear width limbBits carryBits where
  result := a ∘ w.result
  carry := a ∘ w.carry
  resultBit := fun i => RangeCompletedMac.bits limbBits (a (w.result i))
  carryBit := fun i => RangeCompletedMac.bits carryBits (a (w.carry i))

def rowGates (p : Layout) (q : ProfiledMatrix.RowLayout p.rows)
    (rows : Fin p.rows → Row p.groups) (i : Fin p.rows) : ConstraintSystem BabyBear Nat :=
  weightedGates (leftConstant (rows i)) (digitCoefficient p (leftCoefficient (rows i)))
    (scalarWire p) (ProfiledMatrix.rowWires p q i false) ++
  weightedGates (rightConstant (rows i)) (digitCoefficient p (rightCoefficient (rows i)))
    (scalarWire p) (ProfiledMatrix.rowWires p q i true)
def gates (p : Layout) (q : ProfiledMatrix.RowLayout p.rows)
    (rows : Fin p.rows → Row p.groups) := (List.finRange p.rows).flatMap (rowGates p q rows)
def Bounds (p : Layout) (q : ProfiledMatrix.RowLayout p.rows) (a : Nat → BabyBear) : Prop :=
  (∀ i,(a (scalarWire p i)).val<2^p.limbBits) ∧
  (∀ i j,(a ((ProfiledMatrix.rowWires p q i false).result j)).val<2^p.limbBits) ∧
  (∀ i b j,(a ((ProfiledMatrix.rowWires p q i b).carry j)).val<2^(q.carryBits i))

/-- Same integer conclusion and capacities as ProfiledMatrix.SourceSound,
with explicit canonical field ranges replacing Boolean witness columns. -/
def SourceSound : Prop := ∀ p q rows,ProfiledMatrix.Capacity p q rows →
  ∀ a,systemAccepts a (gates p q rows) → Bounds p q a →
  ∀ i,SignedMatrix.eval (rows i) (decoded p a)=0

theorem weighted_completion {J : Type} {n width limbBits carryBits : Nat}
    (c : Nat) (coeff : Fin n → Nat) (scalar : Fin n → J)
    (w : WeightedSumWires J width limbBits carryBits) (a : J → BabyBear)
    (hg : systemAccepts a (weightedGates c coeff scalar w))
    (hr : ∀ i,(a (w.result i)).val<2^limbBits)
    (hc : ∀ i,(a (w.carry i)).val<2^carryBits) :
    systemAccepts id (weightedSumGadget c coeff (a ∘ scalar) (complete a w)) := by
  obtain ⟨hb,he⟩ := (systemAccepts_append a _ _).mp hg
  apply (weightedSumGadget_correct id c coeff (a ∘ scalar) (complete a w)).mpr
  refine ⟨fun i => RangeCompletedMac.bits_complete _ _ (hr i),
    fun i => RangeCompletedMac.bits_complete _ _ (hc i),?_,?_,?_⟩
  · have h := hb (vr (w.carry 0)) (by simp)
    simpa [accepts,eval_vr,complete] using h
  · have h := hb (vr (w.carry (Fin.last width))) (by simp)
    simpa [accepts,eval_vr,complete] using h
  · exact (weightedEquationSystem_correct a c coeff scalar w).mp he

theorem sourceSound : SourceSound := by
  intro p q rows cap a hg hb i
  have hrow : systemAccepts a (rowGates p q rows i) :=
    fun t ht => hg t (List.mem_flatMap.mpr ⟨i,List.mem_finRange i,ht⟩)
  obtain ⟨hl,hr⟩ := (systemAccepts_append a _ _).mp hrow
  have run (c : Nat) (matrix : Fin p.groups → Nat) (b : Bool)
      (hc : c < p.base^(q.width i)) (hm : ∀ j,digitCoefficient p matrix j < p.base^(q.width i))
      (ha : systemAccepts a (weightedGates c (digitCoefficient p matrix) (scalarWire p)
        (ProfiledMatrix.rowWires p q i b))) :
      Bignum.denoteNat p.base (AirBignum.limbVals a (ProfiledMatrix.rowWires p q i b).result)=
        c+∑ g,matrix g*decoded p a g := by
    let w := ProfiledMatrix.rowWires p q i b
    have hs := weighted_completion c (digitCoefficient p matrix) (scalarWire p) w a ha
      (hb.2.1 i) (hb.2.2 i b)
    have hscalar : systemAccepts id (AirBignum.limbRangeSystem (a ∘ scalarWire p)
        (fun j => RangeCompletedMac.bits p.limbBits (a (scalarWire p j)))) :=
      (AirBignum.limbRangeSystem_correct id _ _).mpr
        (fun j => RangeCompletedMac.bits_complete _ _ (hb.1 j))
    have h := ranged_weighted_sound cap.baseField (cap.carryField i) cap.baseField hc
      (digitCoefficient p matrix) hm (cap.leftBudget i) (cap.rightBudget i) id
      (a ∘ scalarWire p) (fun j => RangeCompletedMac.bits p.limbBits (a (scalarWire p j)))
      (complete a w) hscalar hs
    simpa only [complete,AirBignum.limbVals,Function.comp_apply,id_eq,digit_linearization] using h
  have hl' := run _ _ false (cap.constants i).1 (fun j => (cap.coefficients i j).1) hl
  have hr' := run _ _ true (cap.constants i).2 (fun j => (cap.coefficients i j).2) hr
  exact (splitSound (rows i) (decoded p a)).mp (hl'.symm.trans hr')

end Minidregg.Compiler.RangeProfiledMatrix

/-- info: 'Minidregg.Compiler.RangeProfiledMatrix.weighted_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledMatrix.weighted_completion

/-- info: 'Minidregg.Compiler.RangeProfiledMatrix.sourceSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledMatrix.sourceSound
