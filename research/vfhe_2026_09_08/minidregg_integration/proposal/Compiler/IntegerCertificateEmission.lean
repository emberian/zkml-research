/-
Compiler-native signed quotient/remainder certificates, over deployed BabyBear.

Statement-first: `CertificateSound` requires the actual emitted descriptor to force
the integer QR equation and the remainder range. Positive and negative witnesses
below inhabit its premises and expose a forged quotient. This module composes the
existing weighted accumulator, range gadgets, emitter, evaluator and checker.
It is not an integer-convolution, runtime-engine, or proof-protocol refinement.
-/
import Compiler.BfvSignedAccumulatorAir
import Compiler.DescriptorEval

namespace Minidregg.Compiler.IntegerCertificateEmission

open Minidregg.Compiler
open Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

def CertificateSound (d : ConstraintDescriptor BabyBear) : Prop :=
  forall v : Nat -> BabyBear, descriptorHolds d v ->
    4 * ((v 0).val : Int) + 263 =
      31 * ((v 1).val : Int) + ((v 2).val : Int) + 128 /\
    (v 2).val < 31

theorem constDigit_lt (base width value : Nat) (hb : 0 < base) (i : Fin width) :
    AirModularView.constDigit base width value i < base := by
  exact Bignum.digitsLE_ranged hb width value _
    (List.get_mem (Bignum.digitsLE base width value)
      (Fin.cast (Bignum.digitsLE_length base width value).symm i))

theorem sum_products_bound {n : Nat} (d s : Fin n -> Nat) (D S : Nat)
    (hd : forall i, d i <= D) (hs : forall i, s i <= S) (is : List (Fin n)) :
    (is.map fun i => d i * s i).sum <= is.length * D * S := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hmul := Nat.mul_le_mul (hd i) (hs i)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- The range gadgets, not an unverified witness claim, discharge both local
field-to-integer lift premises. The two arithmetic budgets are compile-time facts. -/
theorem ranged_weighted_sound {n width limbBits carryBits scalarBits constant : Nat}
    (hbasep : 2 ^ limbBits <= babyBearP) (hcarryp : 2 ^ carryBits <= babyBearP)
    (hscalarp : 2 ^ scalarBits <= babyBearP)
    (hconstant : constant < (2 ^ limbBits) ^ width)
    (coefficient : Fin n -> Nat)
    (hcoefficient : forall j, coefficient j < (2 ^ limbBits) ^ width)
    (hleftBudget : (2 ^ limbBits - 1) +
      n * (2 ^ limbBits - 1) * (2 ^ scalarBits - 1) + (2 ^ carryBits - 1) < babyBearP)
    (hrightBudget : (2 ^ limbBits - 1) +
      2 ^ limbBits * (2 ^ carryBits - 1) < babyBearP)
    {J : Type} (asg : J -> BabyBear) (scalar : Fin n -> J)
    (scalarBit : Fin n -> Fin scalarBits -> J)
    (w : WeightedSumWires J width limbBits carryBits)
    (hrange : systemAccepts asg (AirBignum.limbRangeSystem scalar scalarBit))
    (haccept : systemAccepts asg (weightedSumGadget constant coefficient scalar w)) :
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.result) =
      constant + ∑ j, coefficient j * (asg (scalar j)).val := by
  have hscalar : forall j, (asg (scalar j)).val < 2 ^ scalarBits := by
    intro j
    exact rangeGadget_val_lt hscalarp asg _ _
      ((AirBignum.limbRangeSystem_correct asg scalar scalarBit).mp hrange j)
  obtain ⟨hresult, hcarry, -, -, -⟩ :=
    (weightedSumGadget_correct asg constant coefficient scalar w).mp haccept
  have hres : forall j, (asg (w.result j)).val < 2 ^ limbBits :=
    fun j => rangeGadget_val_lt hbasep asg _ _ (hresult j)
  have hcar : forall j, (asg (w.carry j)).val < 2 ^ carryBits :=
    fun j => rangeGadget_val_lt hcarryp asg _ _ (hcarry j)
  apply (weightedSumGadget_sound hbasep hcarryp hconstant coefficient hcoefficient
    asg scalar w haccept ?_ ?_).2
  · intro column
    have hc := constDigit_lt (2 ^ limbBits) width constant (by positivity) column
    have hs := sum_products_bound
      (fun j => AirModularView.constDigit (2 ^ limbBits) width (coefficient j) column)
      (fun j => (asg (scalar j)).val) (2 ^ limbBits - 1) (2 ^ scalarBits - 1)
      (fun j => by dsimp only; have := constDigit_lt (2 ^ limbBits) width (coefficient j)
                    (by positivity) column; omega)
      (fun j => by dsimp only; have := hscalar j; omega) (List.finRange n)
    simp only [List.length_finRange] at hs
    have := hcar column.castSucc
    omega
  · intro column
    have hh := Nat.mul_le_mul_left (2 ^ limbBits)
      (show (asg (w.carry column.succ)).val <= 2 ^ carryBits - 1 from by
        have := hcar column.succ; omega)
    have := hres column
    omega

/- The concrete layout: four six-bit scalars (z+32,y+8,r,30-r); three
radix-16 shared result digits; four eight-bit carries on each side. -/
def scalar : Fin 4 -> Fin 115 := fun i => ⟨i.val, by omega⟩
def scalarBit (i : Fin 4) (j : Fin 6) : Fin 115 := ⟨91 + 6 * i.val + j.val, by omega⟩
def left : WeightedSumWires (Fin 115) 3 4 8 where
  result := fun i => ⟨4 + i.val, by omega⟩
  resultBit := fun i j => ⟨7 + 4 * i.val + j.val, by omega⟩
  carry := fun i => ⟨19 + i.val, by omega⟩
  carryBit := fun i j => ⟨23 + 8 * i.val + j.val, by omega⟩
def right : WeightedSumWires (Fin 115) 3 4 8 where
  result := left.result
  resultBit := left.resultBit
  carry := fun i => ⟨55 + i.val, by omega⟩
  carryBit := fun i j => ⟨59 + 8 * i.val + j.val, by omega⟩
def leftCoefficient : Fin 4 -> Nat := ![4, 0, 0, 0]
def rightCoefficient : Fin 4 -> Nat := ![0, 31, 1, 0]
def remainderTerm : Term (AirSig BabyBear (Fin 115)) :=
  add' (add' (vr (scalar 2)) (vr (scalar 3))) (cst (-30))
def certificateSystem : ConstraintSystem BabyBear (Fin 115) :=
  AirBignum.limbRangeSystem scalar scalarBit ++
  weightedSumGadget 263 leftCoefficient scalar left ++
  weightedSumGadget 128 rightCoefficient scalar right ++ [remainderTerm]
def certificateDescriptor : ConstraintDescriptor BabyBear :=
  emit Fin.val 3 115 certificateSystem

theorem certificateSystem_sound (asg : Fin 115 -> BabyBear)
    (h : systemAccepts asg certificateSystem) :
    4 * (asg (scalar 0)).val + 263 =
      31 * (asg (scalar 1)).val + (asg (scalar 2)).val + 128 /\
    (asg (scalar 2)).val < 31 := by
  simp only [certificateSystem, systemAccepts_append,
    systemAccepts_cons, systemAccepts_nil, and_true] at h
  obtain ⟨⟨⟨hr, hl⟩, hh⟩, ht⟩ := h
  have hleft := ranged_weighted_sound
    (by norm_num [babyBearP]) (by norm_num [babyBearP])
    (by norm_num [babyBearP]) (by norm_num)
    leftCoefficient (by intro j; fin_cases j <;> norm_num [leftCoefficient])
    (by norm_num [babyBearP]) (by norm_num [babyBearP])
    asg scalar scalarBit left hr hl
  have hright := ranged_weighted_sound
    (by norm_num [babyBearP]) (by norm_num [babyBearP])
    (by norm_num [babyBearP]) (by norm_num)
    rightCoefficient (by intro j; fin_cases j <;> norm_num [rightCoefficient])
    (by norm_num [babyBearP]) (by norm_num [babyBearP])
    asg scalar scalarBit right hr hh
  have heq : 263 + ∑ j, leftCoefficient j * (asg (scalar j)).val =
      128 + ∑ j, rightCoefficient j * (asg (scalar j)).val :=
    hleft.symm.trans hright
  simp [leftCoefficient, rightCoefficient, Fin.sum_univ_succ] at heq
  constructor
  · omega
  · have hranges := (AirBignum.limbRangeSystem_correct asg scalar scalarBit).mp hr
    have hr2 := rangeGadget_val_lt (by norm_num [babyBearP] : 2 ^ 6 <= babyBearP)
      asg (scalar 2) (scalarBit 2) (hranges 2)
    have hr3 := rangeGadget_val_lt (by norm_num [babyBearP] : 2 ^ 6 <= babyBearP)
      asg (scalar 3) (scalarBit 3) (hranges 3)
    have ht' : asg (scalar 2) + asg (scalar 3) = 30 := by
      simp only [accepts, remainderTerm, eval_add', eval_vr, eval_cst] at ht
      linear_combination ht
    have heqCast : (((asg (scalar 2)).val + (asg (scalar 3)).val : Nat) : BabyBear) = 30 := by
      simpa using ht'
    have hlt : (asg (scalar 2)).val + (asg (scalar 3)).val < babyBearP := by
      norm_num [babyBearP] at *; omega
    have hv := congrArg ZMod.val heqCast
    rw [ZMod.val_cast_of_lt hlt] at hv
    have hv30 : (30 : BabyBear).val = 30 := by decide +kernel
    rw [hv30] at hv
    omega

theorem certificateDescriptor_sound : CertificateSound certificateDescriptor := by
  intro v h
  have hs := (emit_accepts_iff_fin 115 3 (fun i => v i.val) certificateSystem).mp
    ⟨v, fun _ => rfl, h⟩
  have hc := certificateSystem_sound (fun i => v i.val) hs
  change 4 * (v 0).val + 263 = 31 * (v 1).val + (v 2).val + 128 /\
    (v 2).val < 31 at hc
  exact ⟨by exact_mod_cast hc.1, hc.2⟩

/-- The offset normalization recovers signed coefficients, including negatives. -/
theorem certificateDescriptor_signed (v : Nat -> BabyBear)
    (h : descriptorHolds certificateDescriptor v) :
    4 * (((v 0).val : Int) - 32) + 15 =
      31 * (((v 1).val : Int) - 8) + ((v 2).val : Int) /\ (v 2).val < 31 := by
  obtain ⟨heq, hr⟩ := certificateDescriptor_sound v h
  exact ⟨by omega, hr⟩

/-- The selected nearest/ties-up quotient is forced, not merely bound as a field word. -/
theorem certificateDescriptor_quotient (v : Nat -> BabyBear)
    (h : descriptorHolds certificateDescriptor v) :
    ((v 1).val : Int) - 8 = (4 * (((v 0).val : Int) - 32) + 15) / 31 := by
  obtain ⟨heq, hr⟩ := certificateDescriptor_signed v h
  have hr0 : (0 : Int) <= (v 2).val := Int.natCast_nonneg _
  have hr31 : ((v 2).val : Int) < 31 := by exact_mod_cast hr
  omega

/-- A forged quotient is representable but every auxiliary assignment is refused. -/
theorem forged_quotient_refused (v : Nat -> BabyBear)
    (hz : v 0 = 24) (hy : v 1 = 8) :
    ¬ descriptorHolds certificateDescriptor v := by
  intro h
  have hq := certificateDescriptor_quotient v h
  rw [hz, hy] at hq
  have hv24 : (24 : BabyBear).val = 24 := by decide +kernel
  have hv8 : (8 : BabyBear).val = 8 := by decide +kernel
  rw [hv24, hv8] at hq
  norm_num at hq

def digit (base value index : Nat) : Nat := value / base ^ index % base
def carryValue (constant : Nat) (coefficient value : Fin 4 -> Nat) : Nat -> Nat
  | 0 => 0
  | i + 1 => (digit 16 constant i +
      ∑ j, digit 16 (coefficient j) i * value j + carryValue constant coefficient value i) / 16
def values (zEnc yEnc r : Nat) : Fin 4 -> Nat := ![zEnc, yEnc, r, 30-r]
def variableValue (v : Fin 4 -> Nat) (i : Nat) : Nat :=
  if h : i < 4 then v ⟨i, h⟩
  else if i < 7 then digit 16 (4 * v 0 + 263) (i-4)
  else if i < 19 then digit 2 (digit 16 (4 * v 0 + 263) ((i-7)/4)) ((i-7)%4)
  else if i < 23 then carryValue 263 leftCoefficient v (i-19)
  else if i < 55 then digit 2 (carryValue 263 leftCoefficient v ((i-23)/8)) ((i-23)%8)
  else if i < 59 then carryValue 128 rightCoefficient v (i-55)
  else if i < 91 then digit 2 (carryValue 128 rightCoefficient v ((i-59)/8)) ((i-59)%8)
  else if h : (i-91)/6 < 4 then digit 2 (v ⟨(i-91)/6, h⟩) ((i-91)%6)
  else 0
def assignment (zEnc yEnc r : Nat) : Fin 115 -> BabyBear :=
  fun i => (variableValue (values zEnc yEnc r) i.val : BabyBear)
def candidate (zEnc yEnc r : Nat) : Array BabyBear :=
  fillAux certificateDescriptor (Array.ofFn (assignment zEnc yEnc r))
def check (a : Array BabyBear) : Bool :=
  descriptorHoldsCheck certificateDescriptor (fun i => a.getD i 0)

set_option maxHeartbeats 1000000 in
theorem honest_assignment_accepts : systemAccepts (assignment 24 7 14) certificateSystem := by
  decide +kernel

theorem honest_candidate_holds : descriptorHolds certificateDescriptor
    (fun i => (candidate 24 7 14).getD i 0) :=
  fillAux_emit_holds 115 3 (by omega) (assignment 24 7 14) certificateSystem
    honest_assignment_accepts

theorem premise_inhabited : exists v : Nat -> BabyBear,
    descriptorHolds certificateDescriptor v :=
  ⟨_, honest_candidate_holds⟩

theorem honest_candidate_pins (i : Fin 3) :
    (candidate 24 7 14).getD i.val 0 = (![24, 7, 14] : Fin 3 -> BabyBear) i := by
  have hwf : certificateDescriptor.WellFormed := emit_wellFormed Fin.val 3 115 (by omega)
    (fun i : Fin 115 => i.isLt) certificateSystem
  have hsize : (Array.ofFn (assignment 24 7 14)).size = certificateDescriptor.nVars :=
    Array.size_ofFn
  unfold candidate
  rw [fillAux_getD_of_lt _ _ hwf hsize (by show i.val < 115; omega)]
  fin_cases i <;> decide +kernel

/-- The accepting set contains an actual negative signed coefficient and quotient. -/
theorem signed_premise_inhabited : exists v : Nat -> BabyBear,
    descriptorHolds certificateDescriptor v /\
    ((v 0).val : Int)-32 = -8 /\ ((v 1).val : Int)-8 = -1 := by
  refine ⟨fun i => (candidate 24 7 14).getD i 0, honest_candidate_holds, ?_, ?_⟩
  · have hp := honest_candidate_pins 0
    change (candidate 24 7 14).getD 0 0 = 24 at hp
    dsimp only
    rw [hp]
    decide +kernel
  · have hp := honest_candidate_pins 1
    change (candidate 24 7 14).getD 1 0 = 7 at hp
    dsimp only
    rw [hp]
    decide +kernel

/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.constDigit_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms constDigit_lt
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.sum_products_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sum_products_bound
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.ranged_weighted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ranged_weighted_sound
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.certificateSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificateSystem_sound
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.certificateDescriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificateDescriptor_sound
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.certificateDescriptor_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificateDescriptor_signed
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.certificateDescriptor_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificateDescriptor_quotient
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.forged_quotient_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forged_quotient_refused
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.honest_assignment_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_assignment_accepts
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.honest_candidate_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_candidate_holds
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms premise_inhabited
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.honest_candidate_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_candidate_pins
/-- info: 'Minidregg.Compiler.IntegerCertificateEmission.signed_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_premise_inhabited

end Minidregg.Compiler.IntegerCertificateEmission
