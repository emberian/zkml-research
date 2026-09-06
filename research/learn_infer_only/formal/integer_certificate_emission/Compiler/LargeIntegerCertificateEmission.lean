/- Full-modulus compiler-native signed QR slice. The inherited rounding reference remains
separate from actual engine semantics, convolution, and source-ciphertext binding. -/
import Compiler.IntegerCertificateEmission

namespace Minidregg.Compiler.LargeIntegerCertificateEmission
open Minidregg.Compiler
open Minidregg.Compiler.BfvSignedAccumulatorAir
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
open scoped BigOperators
open Lean (Json toJson)

set_option autoImplicit false
set_option maxRecDepth 10000

def Q : Nat := 649033470896967801447398927572993
def t : Nat := 2^20
def zOffset : Nat := 2^231
def yOffset : Nat := 2^142
def scalar : Fin 101 -> Fin 3773 := fun i => ⟨i.val, by omega⟩
def scalarBit (i : Fin 101) (j : Fin 6) : Fin 3773 :=
  ⟨101 + 6*i.val + j.val, by omega⟩
def wireSet (resultBase carryBase : Nat)
    (hresult : resultBase+301 <= 3773) (hcarry : carryBase+616 <= 3773) :
    WeightedSumWires (Fin 3773) 43 6 13 where
  result := fun i => ⟨resultBase+i.val, by omega⟩
  resultBit := fun i j => ⟨resultBase+43+6*i.val+j.val, by omega⟩
  carry := fun i => ⟨carryBase+i.val, by omega⟩
  carryBit := fun i j => ⟨carryBase+44+13*i.val+j.val, by omega⟩
def qleft := wireSet 707 1008 (by omega) (by omega)
def qright := wireSet 707 1624 (by omega) (by omega)
def rleft := wireSet 2240 2541 (by omega) (by omega)
def rright := wireSet 2240 3157 (by omega) (by omega)
def zCoefficient (i : Fin 101) : Nat := if i.val < 39 then 64^i.val else 0
def yCoefficient (i : Fin 101) : Nat :=
  if 39 <= i.val ∧ i.val < 63 then 64^(i.val-39) else 0
def rCoefficient (i : Fin 101) : Nat :=
  if 63 <= i.val ∧ i.val < 82 then 64^(i.val-63) else 0
def sCoefficient (i : Fin 101) : Nat :=
  if 82 <= i.val then 64^(i.val-82) else 0
def leftCoefficient (i : Fin 101) : Nat := t*zCoefficient i
def rightCoefficient (i : Fin 101) : Nat := Q*yCoefficient i+rCoefficient i
def remainderCoefficient (i : Fin 101) : Nat := rCoefficient i+sCoefficient i
def system : ConstraintSystem BabyBear (Fin 3773) :=
  AirBignum.limbRangeSystem scalar scalarBit ++
  weightedSumGadget (Q/2+Q*yOffset) leftCoefficient scalar qleft ++
  weightedSumGadget (t*zOffset) rightCoefficient scalar qright ++
  weightedSumGadget 0 remainderCoefficient scalar rleft ++
  weightedSumGadget (Q-1) (fun _ : Fin 101 => 0) scalar rright
def descriptor := emit Fin.val 0 3773 system

theorem descriptor_wellFormed : descriptor.WellFormed :=
  emit_wellFormed Fin.val 0 3773 (by omega) (fun i => i.isLt) system

/-- The exact generic range-derived bounds for all four chosen accumulators. -/
theorem column_budgets :
    63 + 101*63*63 + (2^13-1) < babyBearP /\
    63 + 64*(2^13-1) < babyBearP /\
    Q/2+Q*yOffset < 64^43 /\ t*zOffset < 64^43 /\ Q-1 < 64^43 := by
  norm_num [babyBearP,Q,t,yOffset,zOffset]

def encoded (coefficient : Fin 101 -> Nat) (v : Nat -> BabyBear) : Nat :=
  ∑ i, coefficient i * (v (scalar i).val).val

def CertificateSound (d : ConstraintDescriptor BabyBear) : Prop := forall v : Nat -> BabyBear,
  descriptorHolds d v ->
    (t : Int) * ((encoded zCoefficient v : Int) - zOffset) + (Q/2 : Nat) =
      (Q : Int) * ((encoded yCoefficient v : Int) - yOffset) + encoded rCoefficient v /\
    encoded rCoefficient v < Q

theorem coefficient_capacities :
    (forall i, leftCoefficient i < 64^43) /\
    (forall i, rightCoefficient i < 64^43) /\
    (forall i, remainderCoefficient i < 64^43) := by
  constructor
  · intro i; fin_cases i <;> norm_num [leftCoefficient,zCoefficient,t]
  constructor
  · intro i; fin_cases i <;> norm_num [rightCoefficient,yCoefficient,rCoefficient,Q]
  · intro i; fin_cases i <;> norm_num [remainderCoefficient,rCoefficient,sCoefficient]

theorem descriptor_sound : CertificateSound descriptor := by
  intro v hd
  let asg : Fin 3773 -> BabyBear := fun i => v i.val
  have hs := (emit_accepts_iff_fin 3773 0 asg system).mp ⟨v,fun _ => rfl,hd⟩
  simp only [system, systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨hr,hql⟩,hqr⟩,hrl⟩,hrr⟩ := hs
  have run (c : Nat) (cf : Fin 101 -> Nat)
      (w : WeightedSumWires (Fin 3773) 43 6 13)
      (hc : c < 64^43) (hcf : forall i, cf i < 64^43)
      (ha : systemAccepts asg (weightedSumGadget c cf scalar w)) :
      Bignum.denoteNat 64 (AirBignum.limbVals asg w.result) =
        c + ∑ i, cf i * (v (scalar i).val).val := by
    exact ranged_weighted_sound
      (by norm_num [babyBearP]) (by norm_num [babyBearP])
      (by norm_num [babyBearP]) hc cf hcf
      (by norm_num [babyBearP]) (by norm_num [babyBearP])
      asg scalar scalarBit w hr ha
  have eql := run _ _ _ column_budgets.2.2.1 coefficient_capacities.1 hql
  have eqr := run _ _ _ column_budgets.2.2.2.1 coefficient_capacities.2.1 hqr
  have erl := run _ _ _ (by norm_num) coefficient_capacities.2.2 hrl
  have err := run _ _ _ column_budgets.2.2.2.2 (by intro i; norm_num) hrr
  have heq := eql.symm.trans eqr
  have hre := erl.symm.trans err
  change Q/2+Q*yOffset+encoded leftCoefficient v =
    t*zOffset+encoded rightCoefficient v at heq
  change 0+encoded remainderCoefficient v = Q-1+encoded (fun _ => 0) v at hre
  have ez : encoded leftCoefficient v = t*encoded zCoefficient v := by
    simp [encoded,leftCoefficient,Finset.mul_sum,mul_assoc]
  have ey : encoded rightCoefficient v = Q*encoded yCoefficient v+encoded rCoefficient v := by
    simp [encoded,rightCoefficient,Finset.mul_sum,add_mul,Finset.sum_add_distrib,mul_assoc]
  have er : encoded remainderCoefficient v = encoded rCoefficient v+encoded sCoefficient v := by
    simp [encoded,remainderCoefficient,add_mul,Finset.sum_add_distrib]
  rw [ez,ey] at heq
  rw [er] at hre
  have hz0 : encoded (fun _ => 0) v = 0 := by simp [encoded]
  rw [zero_add,hz0,add_zero] at hre
  constructor
  · have heqi := congrArg (fun n : Nat => (n : Int)) heq
    simp only [Nat.cast_add,Nat.cast_mul] at heqi
    linear_combination heqi
  · have hQ : 0 < Q := by norm_num [Q]
    omega

theorem descriptor_quotient (v : Nat -> BabyBear) (hd : descriptorHolds descriptor v) :
    (encoded yCoefficient v : Int)-yOffset =
      ((t : Int)*((encoded zCoefficient v : Int)-zOffset)+(Q/2 : Nat))/(Q : Int) := by
  obtain ⟨heq,hr⟩ := descriptor_sound v hd
  have hr0 : (0 : Int) <= encoded rCoefficient v := Int.natCast_nonneg _
  have hrQ : (encoded rCoefficient v : Int) < Q := by exact_mod_cast hr
  have hQ : (0 : Int) < Q := by norm_num [Q]
  apply le_antisymm
  · rw [Int.le_ediv_iff_mul_le hQ]
    nlinarith
  · have hh : ((t : Int)*((encoded zCoefficient v : Int)-zOffset)+(Q/2 : Nat))/(Q : Int)
        < ((encoded yCoefficient v : Int)-yOffset)+1 := by
      rw [Int.ediv_lt_iff_lt_mul hQ]
      nlinarith
    omega

theorem forged_quotient_refused (v : Nat -> BabyBear)
    (hz : (encoded zCoefficient v : Int)-zOffset = -(Q : Int))
    (hy : (encoded yCoefficient v : Int)-yOffset = 1-(t : Int)) :
    ¬ descriptorHolds descriptor v := by
  intro hd
  have hq := descriptor_quotient v hd
  rw [hz,hy] at hq
  norm_num [Q,t] at hq

instance : Hashable BabyBear := ⟨fun x => hash x.val⟩
def sharedDescriptor : ConstraintDescriptor BabyBear := cse descriptor

/-- The already-proved generic compiler CSE pass preserves this exact certificate. -/
theorem sharedDescriptor_sound : CertificateSound sharedDescriptor := by
  intro v hd
  let asg : Fin 3773 -> BabyBear := fun i => v i.val
  have hs := (cse_emit_accepts_iff_fin 3773 0 asg system).mp ⟨v,fun _ => rfl,hd⟩
  obtain ⟨v',hpin,hd'⟩ := (emit_accepts_iff_fin 3773 0 asg system).mpr hs
  have hc := descriptor_sound v' hd'
  have he (cf : Fin 101 -> Nat) : encoded cf v' = encoded cf v := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hpin (scalar i)]
  simpa only [he] using hc

def scalarValues (z y : Int) (r : Nat) (i : Fin 101) : Nat :=
  if i.val < 39 then digit 64 (z+zOffset).toNat i.val
  else if i.val < 63 then digit 64 (y+yOffset).toNat (i.val-39)
  else if i.val < 82 then digit 64 r (i.val-63)
  else digit 64 (Q-1-r) (i.val-82)
def carryValues (constant : Nat) (coefficient value : Fin 101 -> Nat) : Nat -> Nat
  | 0 => 0
  | i+1 => (digit 64 constant i +
      ∑ j, digit 64 (coefficient j) i * value j + carryValues constant coefficient value i)/64
def install (a : Array BabyBear) (offset : Nat) (values : Array Nat) : Array BabyBear :=
  (List.range values.size).foldl (fun a i => a.set! (offset+i) (values[i]! : BabyBear)) a
def bitArray (width : Nat) (values : Array Nat) : Array Nat :=
  values.flatMap fun value => (List.range width).toArray.map fun i => digit 2 value i
def setGroup (a : Array BabyBear) (offset width : Nat) (values : Array Nat) : Array BabyBear :=
  install (install a offset values) (offset+values.size) (bitArray width values)
def setAccumulator (a : Array BabyBear) (resultBase carryBase : Nat)
    (constant : Nat) (coefficient value : Fin 101 -> Nat) : Array BabyBear :=
  let total := constant + ∑ j, coefficient j * value j
  let ds := (List.range 43).toArray.map (digit 64 total)
  let cs := (List.range 44).toArray.map (carryValues constant coefficient value)
  setGroup (setGroup a resultBase 6 ds) carryBase 13 cs
def variableArray (z y : Int) (r : Nat) : Array BabyBear := Id.run do
  let v := scalarValues z y r
  let mut a : Array BabyBear := Array.replicate 3773 0
  a := setGroup a 0 6 (Array.ofFn v)
  a := setAccumulator a 707 1008 (Q/2+Q*yOffset) leftCoefficient v
  -- The right gadget shares the left result; only its carry values are installed.
  a := setGroup a 1624 13 ((List.range 44).toArray.map
    (carryValues (t*zOffset) rightCoefficient v))
  a := setAccumulator a 2240 2541 0 remainderCoefficient v
  a := setGroup a 3157 13 ((List.range 44).toArray.map
    (carryValues (Q-1) (fun _ => 0) v))
  return a
def candidate (z y : Int) (r : Nat) : Array BabyBear := fillAux descriptor (variableArray z y r)
def check (a : Array BabyBear) : Bool := descriptorHoldsCheck descriptor (fun i => a.getD i 0)

/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.descriptor_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms descriptor_wellFormed
/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.column_budgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms column_budgets
/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.coefficient_capacities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coefficient_capacities
/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.descriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms descriptor_sound
/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.descriptor_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms descriptor_quotient
/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.forged_quotient_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forged_quotient_refused
/-- info: 'Minidregg.Compiler.LargeIntegerCertificateEmission.sharedDescriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sharedDescriptor_sound


end Minidregg.Compiler.LargeIntegerCertificateEmission
