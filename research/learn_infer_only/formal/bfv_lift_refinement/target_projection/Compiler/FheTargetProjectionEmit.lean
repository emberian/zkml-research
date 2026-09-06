/- Existing-compiler lowering of the pinned scalar source certificate.
The layout is intentionally conservative:10 groups of19 radix64 digits, six
shared-result balances,26 columns and14-bit carries. The actual descriptor is
built by existing weightedSumGadget, limbRangeSystem and emit. -/
import Compiler.FheTargetProjectionLayout

namespace Minidregg.Compiler.FheTargetProjection
open Minidregg.Compiler
open Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def scalarWire (i : Fin 190) : Fin 7282 := ⟨i.val,by omega⟩
def scalarBits (i : Fin 190) (j : Fin 6) : Fin 7282 := ⟨190+6*i.val+j.val,by omega⟩
def groupDigit : Fin 10 × Fin 19 ≃ Fin 190 := finProdFinEquiv

def digitCoefficient (matrix : Fin 10 → ℕ) (i : Fin 190) : ℕ :=
  matrix (groupDigit.symm i).1 * 64^(groupDigit.symm i).2.val

def decoded (v : ℕ → BabyBear) (g : Fin 10) : ℕ :=
  ∑ d : Fin 19, 64^d.val * (v (scalarWire (groupDigit (g,d))).val).val

def resultStart (row : Fin 6) : ℕ := 1330+992*row.val

def rowWires (row : Fin 6) (right : Bool) : WeightedSumWires (Fin 7282) 26 6 14 where
  result := fun i => ⟨resultStart row+i.val,by dsimp [resultStart]; omega⟩
  resultBit := fun i j => ⟨resultStart row+26+6*i.val+j.val,by dsimp [resultStart]; omega⟩
  carry := fun i => ⟨resultStart row+182+(if right then 405 else 0)+i.val,by
    dsimp [resultStart]; split_ifs <;> omega⟩
  carryBit := fun i j => ⟨resultStart row+182+(if right then 405 else 0)+27+14*i.val+j.val,by
    dsimp [resultStart]; split_ifs <;> omega⟩

def rowSystem (row : Fin 6) : ConstraintSystem BabyBear (Fin 7282) :=
  weightedSumGadget (leftConstant row) (digitCoefficient (leftMatrix row)) scalarWire (rowWires row false) ++
  weightedSumGadget (rightConstant row) (digitCoefficient (rightMatrix row)) scalarWire (rowWires row true)

def sourceSystem : ConstraintSystem BabyBear (Fin 7282) :=
  AirBignum.limbRangeSystem scalarWire scalarBits ++
  (List.finRange 6).flatMap rowSystem

def sourceDescriptor : ConstraintDescriptor BabyBear := emit Fin.val 0 7282 sourceSystem

def EmittedTargetSound (d : ConstraintDescriptor BabyBear) : Prop :=
  ∀ v : ℕ → BabyBear,descriptorHolds d v →
    ∀ i,readLimbs (decoded v) i=decoded v 0%targetPrime i

/-- The emitted wire layout is a well-formed instance of the existing compiler. -/
theorem sourceDescriptor_wellFormed : sourceDescriptor.WellFormed :=
  emit_wellFormed Fin.val 0 7282 (by omega) (fun i => i.isLt) sourceSystem

/-- Range-derived column budgets are strictly below the deployed proof field. -/
theorem source_column_budgets :
    63+190*63*63+(2^14-1) < babyBearP ∧
    63+64*(2^14-1) < babyBearP := by norm_num [babyBearP]

theorem digit_coefficient_capacity (matrix : Fin 10 → ℕ)
    (h : ∀ i, matrix i < 2^38) (i : Fin 190) : digitCoefficient matrix i < 64^26 := by
  have hp : 64^(groupDigit.symm i).2.val ≤ 64^18 :=
    Nat.pow_le_pow_right (by omega) (by have hh := (groupDigit.symm i).2.isLt; omega)
  have hh := Nat.mul_le_mul (h (groupDigit.symm i).1).le hp
  exact lt_of_le_of_lt hh (by decide)

/-- Reindexing the exact radix expansion preserves every pinned linear form. -/
theorem digit_linearization (matrix : Fin 10 → ℕ) (v : ℕ → BabyBear) :
    (∑ i : Fin 190, digitCoefficient matrix i * (v (scalarWire i).val).val) =
      dot matrix (decoded v) := by
  rw [← groupDigit.sum_comp]
  simp only [digitCoefficient,Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp [dot,decoded,Finset.mul_sum,mul_assoc]

/-- Existing emitted constraints force every exact nonnegative balance. -/
theorem sourceDescriptor_balanced (v : ℕ → BabyBear)
    (hd : descriptorHolds sourceDescriptor v) : Balanced (decoded v) := by
  let asg : Fin 7282 → BabyBear := fun i => v i.val
  have hs := (emit_accepts_iff_fin 7282 0 asg sourceSystem).mp ⟨v,fun _ => rfl,hd⟩
  obtain ⟨hr,hh⟩ := (systemAccepts_append asg _ _).mp hs
  intro row
  have hrow : systemAccepts asg (rowSystem row) := by
    intro t ht
    exact hh t (List.mem_flatMap.mpr ⟨row,by simp,ht⟩)
  obtain ⟨hl,hrr⟩ := (systemAccepts_append asg _ _).mp hrow
  have run (c : ℕ) (matrix : Fin 10 → ℕ) (w : WeightedSumWires (Fin 7282) 26 6 14)
      (hc : c < 64^26) (hm : ∀ i, matrix i < 2^38)
      (ha : systemAccepts asg (weightedSumGadget c (digitCoefficient matrix) scalarWire w)) :
      Bignum.denoteNat 64 (AirBignum.limbVals asg w.result) = c+dot matrix (decoded v) := by
    have h := ranged_weighted_sound
      (by norm_num [babyBearP]) (by norm_num [babyBearP]) (by norm_num [babyBearP])
      hc (digitCoefficient matrix) (digit_coefficient_capacity matrix hm)
      source_column_budgets.1 source_column_budgets.2 asg scalarWire scalarBits w hr ha
    simpa only [asg,digit_linearization] using h
  have hleft := run _ _ _ (matrix_capacities.2 row).1
    (fun i => (matrix_capacities.1 row i).1) hl
  have hright := run _ _ _ (matrix_capacities.2 row).2
    (fun i => (matrix_capacities.1 row i).2) hrr
  exact hleft.symm.trans hright

/-- Every target is fixed by the descriptor's own QR and range constraints. -/
theorem targetDescriptor_sound : EmittedTargetSound sourceDescriptor := by
  intro v hd
  exact balanced_limbs (decoded v) (sourceDescriptor_balanced v hd)

end Minidregg.Compiler.FheTargetProjection

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheTargetProjection.sourceDescriptor_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.sourceDescriptor_wellFormed

/-- info: 'Minidregg.Compiler.FheTargetProjection.source_column_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.source_column_budgets

/-- info: 'Minidregg.Compiler.FheTargetProjection.digit_coefficient_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.digit_coefficient_capacity

/-- info: 'Minidregg.Compiler.FheTargetProjection.digit_linearization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.digit_linearization

/-- info: 'Minidregg.Compiler.FheTargetProjection.sourceDescriptor_balanced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.sourceDescriptor_balanced

/-- info: 'Minidregg.Compiler.FheTargetProjection.targetDescriptor_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.targetDescriptor_sound
