/- Nonzero inhabitation and a canonical-but-wrong cross-output witness for the
same shared source constructor. These are proof teeth, not workload coverage. -/
import Compiler.BfvTensorCore
namespace Minidregg.Compiler.BfvTensorCore.Exhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.BfvTensorMul
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def lo (n : Nat) (i : Fin 11) : BabyBear := if i.val=0 then (n : BabyBear) else 0
def bits (n : Nat) (i : Fin 11) (j : Fin 6) : BabyBear :=
  if i.val=0 then (n/2^j.val%2 : Nat) else 0

def good : Wires BabyBear where
  canonical := fun g => {
    x := lo ((![3,5,9,30,25] : Fin 5 → Nat) g)
    y := lo ((![33,31,27,6,11] : Fin 5 → Nat) g)
    z := lo 36
    xBit := bits ((![3,5,9,30,25] : Fin 5 → Nat) g)
    yBit := bits ((![33,31,27,6,11] : Fin 5 → Nat) g)
    zBit := bits 36
    carry := fun _ => 0 }
  quotient := fun _ _ => 0
  quotientBit := fun _ _ _ => 0
  carry := fun _ _ => 2048
  carryBit := fun _ _ j => if j.val=11 then 1 else 0

/-- Explicit nonzero source acceptance, not only semantic equation inhabitation. -/
def NonzeroPremise : Prop := systemAccepts id (BfvTensorCore.system 37 good) ∧
  value id good 0=3 ∧ value id good 1=5 ∧ value id good 2=9 ∧
  value id good 3=30 ∧ value id good 4=25

theorem canonical_accepts (g : Fin 5) :
    systemAccepts id (canonicalSystem 37 (good.canonical g)) := by
  rw [canonicalSystem,systemAccepts_append,AirBignum.addGadget_correct,
    AirModularView.pinWordSystem_correct]
  fin_cases g <;>
    norm_num [good,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ,
      AirModularView.constDigit,Bignum.digitsLE,List.getD]

theorem weighted_accepts (k : Fin 3) :
    systemAccepts id (rowSystem 37 (factor k) (weightedWires good k)) := by
  simp only [rowSystem,systemAccepts_append]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro t ht
    obtain ⟨g,_,ht⟩ := List.mem_flatMap.mp ht
    have hcan : systemAccepts id (canonicalSystem 37 ((weightedWires good k).canonical g)) := by
      fin_cases g
      · exact canonical_accepts (lhs k)
      · exact canonical_accepts (rhs k)
      · exact canonical_accepts (out k)
    exact hcan t ht
  · rw [AirBignum.limbRangeSystem_correct]
    intro i
    norm_num [weightedWires,good,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · rw [AirBignum.limbRangeSystem_correct]
    intro i
    norm_num [weightedWires,good,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · norm_num [weightedWires,good,systemAccepts_cons,systemAccepts_nil,accepts,eval_add',eval_vr,eval_cst]
  · intro t ht
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    rw [column_correct]
    fin_cases k <;> fin_cases i <;>
      norm_num [weightedWires,good,lo,padded,convolution,lhs,rhs,out,factor,
        Fin.sum_univ_succ,AirModularView.constDigit,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> decide +kernel

theorem nonzero_premise : NonzeroPremise := by
  constructor
  · intro t ht
    obtain ⟨k,_,ht⟩ := List.mem_flatMap.mp ht
    exact weighted_accepts k t ht
  · norm_num [value,AirBignum.limbVals,good,lo,List.ofFn_succ,Bignum.denoteNat,
      babyBearP,ZMod.val_natCast]
    decide +kernel

theorem premise_inhabited : ∃ w : Wires BabyBear,
    systemAccepts id (BfvTensorCore.system 37 w) ∧ value id w 0≠0 ∧ value id w 1≠0 := by
  refine ⟨good,nonzero_premise.1,?_,?_⟩
  · rw [nonzero_premise.2.1]; decide
  · rw [nonzero_premise.2.2.1]; decide

def wrong : Wires BabyBear where
  canonical := fun g =>
    if g.val=3 then
      { x := lo 15
        y := lo 21
        z := lo 36
        xBit := bits 15
        yBit := bits 21
        zBit := bits 36
        carry := fun _ => 0 }
    else good.canonical g
  quotient := good.quotient
  quotientBit := good.quotientBit
  carry := good.carry
  carryBit := good.carryBit

theorem wrong_canonical (g : Fin 5) :
    systemAccepts id (canonicalSystem 37 (wrong.canonical g)) := by
  rw [canonicalSystem,systemAccepts_append,AirBignum.addGadget_correct,
    AirModularView.pinWordSystem_correct]
  fin_cases g <;>
    norm_num [wrong,good,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ,
      AirModularView.constDigit,Bignum.digitsLE,List.getD]

theorem wrong_values : value id wrong 0=3 ∧ value id wrong 1=5 ∧ value id wrong 3=15 := by
  norm_num [value,wrong,good,AirBignum.limbVals,lo,List.ofFn_succ,Bignum.denoteNat]
  decide +kernel

/-- Omitting the factor2 still gives a canonical output, but the source refuses it
for any wiring/assignment with these values, independent of witness generation. -/
theorem missing_cross_factor_refused {J : Type} (w : Wires J) (asg : J → BabyBear)
    (ha : value asg w 0=3) (hb : value asg w 1=5) (ho : value asg w 3=15) :
    ¬systemAccepts asg (BfvTensorCore.system 37 w) := by
  intro hs
  have h := (sound 37 (by decide) (by decide) w asg hs).2.2.1
  norm_num [ha,hb,ho] at h

theorem wrong_refused : ¬systemAccepts id (BfvTensorCore.system 37 wrong) :=
  missing_cross_factor_refused wrong id wrong_values.1 wrong_values.2.1 wrong_values.2.2

theorem capacity_inhabited : ∃ q : Nat,0<q ∧ q<64^11 ∧ 37≤q := ⟨37,by decide,by decide,by decide⟩

/-- The double-product quotient fits the same eleven-digit witness word for all
canonical inputs under the strengthened deployed-prime capacity. -/
theorem quotient_capacity (q a b f : Nat) (hq : 0<q) (hcap : 2*q<64^11)
    (ha : a<q) (hb : b<q) (hf : f≤2) : f*a*b/q<64^11 := by
  have hab : a*b<q*q := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) hq
  have hfprod : f*(a*b)≤2*(a*b) := Nat.mul_le_mul_right (a*b) hf
  have hp : f*a*b<(2*q)*q := by nlinarith
  have hd : f*a*b/q<2*q := (Nat.div_lt_iff_lt_mul hq).2 hp
  omega

theorem field_column_capacity :
    2*(121*3969)+4095+131072<babyBearP ∧
    63+121*3969+64*4095+2048<babyBearP := by decide
end Minidregg.Compiler.BfvTensorCore.Exhibits
