import Compiler.BfvQueryMul
namespace Minidregg.Compiler.BfvQueryMul.Teeth
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.BfvQueryMul
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def lo (n : Nat) (i : Fin 7) : BabyBear := if i.val=0 then (n : BabyBear) else 0
def bits (n : Nat) (i : Fin 7) (j : Fin 6) : BabyBear := if i.val=0 then (n/2^j.val%2 : Nat) else 0

def wires : RowWires BabyBear where
  canonical := fun k => {
    x := lo ((![3,5,15] : Fin 3 → Nat) k)
    y := lo ((![13,11,1] : Fin 3 → Nat) k)
    z := lo 16
    xBit := bits ((![3,5,15] : Fin 3 → Nat) k)
    yBit := bits ((![13,11,1] : Fin 3 → Nat) k)
    zBit := bits 16
    carry := fun _=>0 }
  quotient := fun _=>0
  quotientBit := fun _ _=>0
  carry := fun _=>512
  carryBit := fun _ j=> if j.val=9 then 1 else 0

def NonzeroPremise : Prop := systemAccepts id (rowSystem 17 wires) ∧
  word id wires 0=3 ∧ word id wires 1=5 ∧ word id wires 2=15

theorem canonical_accepts (k : Fin 3) :
    systemAccepts id (BfvLinearCombination.canonicalSystem 17 (wires.canonical k)) := by
  rw [BfvLinearCombination.canonicalSystem,systemAccepts_append,
    AirBignum.addGadget_correct,AirModularView.pinWordSystem_correct]
  fin_cases k <;>
    norm_num [wires,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ,
      AirModularView.constDigit,Bignum.digitsLE,List.getD]

theorem nonzero_premise : NonzeroPremise := by
  constructor
  · simp only [rowSystem,systemAccepts_append]
    refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
    · intro t ht
      obtain ⟨k,_,ht⟩ := List.mem_flatMap.mp ht
      exact canonical_accepts k t ht
    · rw [AirBignum.limbRangeSystem_correct]
      intro i
      norm_num [wires,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
    · rw [AirBignum.limbRangeSystem_correct]
      intro i
      norm_num [wires,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
    · norm_num [wires,systemAccepts_cons,systemAccepts_nil,accepts,eval_add',eval_vr,eval_cst]
    · intro t ht
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
      rw [column_correct]
      fin_cases i <;>
        norm_num [wires,lo,padded,convolution,Fin.sum_univ_succ,AirModularView.constDigit,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  · norm_num [word,AirBignum.limbVals,wires,lo,List.ofFn_succ,Bignum.denoteNat,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,babyBearP,ZMod.val_natCast]
    decide +kernel

theorem inhabited_core_fire : word id wires 2=(word id wires 0*word id wires 1)%17 :=
  (rowSystem_sound 17 (by decide) (by decide) wires id nonzero_premise.1).2

/-- The theorem rules out an incorrect output for any assignment and wiring;
this is independent of the deterministic producer used by the runtime. -/
theorem changed_output_refused {J : Type} (w : RowWires J) (asg : J → BabyBear)
    (ha : word asg w 0=3) (hb : word asg w 1=5) (ho : word asg w 2=14) :
    ¬ systemAccepts asg (rowSystem 17 w) := by
  intro hs
  have h := (rowSystem_sound 17 (by decide) (by decide) w asg hs).2
  norm_num [ha,hb,ho] at h

/-- Literal coefficientwise multiplication loses carries: 63*63 has two
radix64 digits [1,62], even before reduction by the BFV modulus. -/
theorem digitwise_falsifier : (63*63)%64=1 ∧ (63*63)/64=62 ∧ 63*63≠1 := by decide

def wrongWires : RowWires BabyBear :=
  { wires with
    canonical := fun k =>
      if k.val = 2 then
        { wires.canonical k with x := lo 14, y := lo 2, xBit := bits 14, yBit := bits 2 }
      else wires.canonical k }

theorem wrong_values : word id wrongWires 0=3 ∧ word id wrongWires 1=5 ∧ word id wrongWires 2=14 := by
  norm_num [word,wrongWires,wires,AirBignum.limbVals,lo,List.ofFn_succ,Bignum.denoteNat]
  decide +kernel

/-- All three canonical word gadgets still accept this wrong answer; the
multiplication equation, rather than a broken range witness, refuses it. -/
theorem wrong_canonical (k : Fin 3) :
    systemAccepts id (BfvLinearCombination.canonicalSystem 17 (wrongWires.canonical k)) := by
  rw [BfvLinearCombination.canonicalSystem,systemAccepts_append,
    AirBignum.addGadget_correct,AirModularView.pinWordSystem_correct]
  fin_cases k <;>
    norm_num [wrongWires,wires,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ,
      AirModularView.constDigit,Bignum.digitsLE,List.getD]

theorem wrong_output_refused : ¬ systemAccepts id (rowSystem 17 wrongWires) :=
  changed_output_refused wrongWires id wrong_values.1 wrong_values.2.1 wrong_values.2.2
end Minidregg.Compiler.BfvQueryMul.Teeth

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.canonical_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.canonical_accepts

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.nonzero_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.nonzero_premise

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.inhabited_core_fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.inhabited_core_fire

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.changed_output_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.changed_output_refused

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.digitwise_falsifier' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.digitwise_falsifier

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.wrong_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.wrong_values

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.wrong_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.wrong_canonical

/-- info: 'Minidregg.Compiler.BfvQueryMul.Teeth.wrong_output_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.Teeth.wrong_output_refused
