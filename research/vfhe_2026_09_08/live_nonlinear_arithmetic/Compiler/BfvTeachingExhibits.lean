/- Cheap, nonzero inhabited witness for the exact teaching operand binding. -/
import Compiler.BfvTeachingUpdate
import Compiler.BfvKeyswitchExhibits
namespace Minidregg.Compiler.BfvTeachingUpdate.Exhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open BfvKeyswitchCore BfvKeyswitchMac
open Minidregg.Compiler.BfvKeyswitchCore.Exhibits (lo bits)
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option maxErrors 5

def acc : Pair := ![7,8]
def fresh : Pair := ![2,3]
def old : Pair := ![5,7]
def out : Pair := ![4,4]
def vals : Fin 16 → Nat := ![2,3,5,7,1,0,36,0,0,1,0,36,7,8,4,4]
def quotients : Fin 2 → Nat := ![5,7]
def good : Wires BabyBear where
  canonical := fun g => {
    x := lo (vals g)
    y := lo (36-vals g)
    z := lo 36
    xBit := bits (vals g)
    yBit := bits (36-vals g)
    zBit := bits 36
    carry := fun _ => 0 }
  quotient := fun h => lo (quotients h)
  quotientBit := fun h => bits (quotients h)
  carry := fun _ _ => 32768
  carryBit := fun _ _ j => if j.val=15 then 1 else 0

def NonzeroUpdateInhabited : Prop := ∃ w : Wires BabyBear,
  systemAccepts id (BfvKeyswitchCore.system 37 w) ∧
  BfvInferComposition.Bound w id (operands 37 acc fresh old) out

theorem canonical_accepts (g : Fin 16) :
    systemAccepts id (canonicalSystem 37 (good.canonical g)) := by
  rw [canonicalSystem,systemAccepts_append,AirBignum.addGadget_correct,
    AirModularView.pinWordSystem_correct]
  fin_cases g <;>
    norm_num [good,vals,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ,
      AirModularView.constDigit,Bignum.digitsLE,List.getD]

theorem mac_accepts (h : Fin 2) :
    systemAccepts id (rowSystem 37 (macWires good h)) := by
  simp only [rowSystem,systemAccepts_append]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro t ht
    obtain ⟨g,_,ht⟩ := List.mem_flatMap.mp ht
    exact canonical_accepts (kindMap h g) t ht
  · rw [AirBignum.limbRangeSystem_correct]
    intro i
    fin_cases h <;> fin_cases i <;>
      norm_num [macWires,good,quotients,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · rw [AirBignum.limbRangeSystem_correct]
    intro i
    norm_num [macWires,good,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · norm_num [macWires,good,systemAccepts_cons,systemAccepts_nil,accepts,eval_add',eval_vr,eval_cst]
  · intro t ht
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    rw [column_correct]
    fin_cases h <;> fin_cases i <;>
      norm_num [macWires,kindMap,good,vals,quotients,lo,padded,products,convolution,lhs,rhs,
        Fin.sum_univ_succ,AirModularView.constDigit,Bignum.digitsLE,List.getD,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem good_values (g : Fin 16) : value id good g=vals g := by
  fin_cases g <;>
    norm_num [value,AirBignum.limbVals,good,vals,lo,List.ofFn_succ,Bignum.denoteNat] <;> decide +kernel

theorem good_bound : BfvInferComposition.Bound good id (operands 37 acc fresh old) out := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; rw [good_values]; fin_cases i <;> rfl
  · intro h i; rw [good_values]; fin_cases h <;> fin_cases i <;> rfl
  · intro h; rw [good_values]; fin_cases h <;> rfl
  · intro h; rw [good_values]; fin_cases h <;> rfl

theorem nonzeroUpdateInhabited : NonzeroUpdateInhabited := by
  refine ⟨good,?_,good_bound⟩
  intro t ht
  obtain ⟨h,_,ht⟩ := List.mem_flatMap.mp ht
  exact mac_accepts h t ht

/-- Omitting the expired ciphertext changes both outputs while leaving the
claimed values canonical. The falsifier quantifies over every auxiliary. -/
def OmittedExpiryRefused : Prop := ∀ (J : Type) (w : Wires J) (asg : J → BabyBear),
  ¬(systemAccepts asg (BfvKeyswitchCore.system 37 w) ∧
    BfvInferComposition.Bound w asg (operands 37 acc fresh old) ![9,11])

theorem omittedExpiryRefused : OmittedExpiryRefused := by
  intro J w asg hc
  have h := BfvInferComposition.boundRowSound J 37 (by decide) (by decide) w asg
    (operands 37 acc fresh old) ![9,11] hc.1 hc.2 0
  have hv : BfvInferComposition.output 37 (operands 37 acc fresh old) 0=4 := by decide
  have hn : (![9,11] : Fin 2 → Nat) 0=9 := rfl
  omega
end Minidregg.Compiler.BfvTeachingUpdate.Exhibits

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.Exhibits.canonical_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.Exhibits.canonical_accepts

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.Exhibits.mac_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.Exhibits.mac_accepts

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.Exhibits.good_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.Exhibits.good_values

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.Exhibits.good_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.Exhibits.good_bound

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.Exhibits.nonzeroUpdateInhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.Exhibits.nonzeroUpdateInhabited

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.Exhibits.omittedExpiryRefused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.Exhibits.omittedExpiryRefused
