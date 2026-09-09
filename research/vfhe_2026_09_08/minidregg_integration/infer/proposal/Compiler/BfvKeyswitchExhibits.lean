/- Nonzero acceptance and a canonical omitted-term falsifier for the same source. -/
import Compiler.BfvKeyswitchCore
namespace Minidregg.Compiler.BfvKeyswitchCore.Exhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.BfvKeyswitchMac
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

def vals : Fin 16 → Nat := ![1,2,3,4,2,2,2,2,3,3,3,3,7,5,27,35]
def lo (n : Nat) (i : Fin 6) : BabyBear := if i.val=0 then (n : BabyBear) else 0
def bits (n : Nat) (i : Fin 6) (j : Fin 9) : BabyBear :=
  if i.val=0 then (n/2^j.val%2 : Nat) else 0
def good : Wires BabyBear where
  canonical := fun g => {
    x := lo (vals g)
    y := lo (36-vals g)
    z := lo 36
    xBit := bits (vals g)
    yBit := bits (36-vals g)
    zBit := bits 36
    carry := fun _ => 0 }
  quotient := fun _ _ => 0
  quotientBit := fun _ _ _ => 0
  carry := fun _ _ => 32768
  carryBit := fun _ _ j => if j.val=15 then 1 else 0

def NonzeroPremise : Prop := systemAccepts id (BfvKeyswitchCore.system 37 good) ∧
  ∀ g,value id good g=vals g

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
    norm_num [macWires,good,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · rw [AirBignum.limbRangeSystem_correct]
    intro i
    norm_num [macWires,good,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · norm_num [macWires,good,systemAccepts_cons,systemAccepts_nil,accepts,eval_add',eval_vr,eval_cst]
  · intro t ht
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    rw [column_correct]
    fin_cases h <;> fin_cases i <;>
      norm_num [macWires,kindMap,good,vals,lo,padded,products,convolution,lhs,rhs,
        Fin.sum_univ_succ,AirModularView.constDigit,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem good_values (g : Fin 16) : value id good g=vals g := by
  fin_cases g <;>
    norm_num [value,AirBignum.limbVals,good,vals,lo,List.ofFn_succ,Bignum.denoteNat] <;> decide +kernel

theorem nonzero_premise : NonzeroPremise := by
  constructor
  · intro t ht
    obtain ⟨h,_,ht⟩ := List.mem_flatMap.mp ht
    exact mac_accepts h t ht
  · exact good_values

theorem premise_inhabited : ∃ w : Wires BabyBear,
    systemAccepts id (BfvKeyswitchCore.system 37 w) ∧ value id w 0≠0 ∧ value id w 14≠0 := by
  refine ⟨good,nonzero_premise.1,?_,?_⟩
  · rw [good_values]; decide
  · rw [good_values]; decide

def wrong : Wires BabyBear where
  canonical := fun g =>
    if g.val=14 then
      { x := lo 19
        y := lo 17
        z := lo 36
        xBit := bits 19
        yBit := bits 17
        zBit := bits 36
        carry := fun _ => 0 }
    else good.canonical g
  quotient := good.quotient
  quotientBit := good.quotientBit
  carry := good.carry
  carryBit := good.carryBit

theorem wrong_canonical (g : Fin 16) :
    systemAccepts id (canonicalSystem 37 (wrong.canonical g)) := by
  rw [canonicalSystem,systemAccepts_append,AirBignum.addGadget_correct,
    AirModularView.pinWordSystem_correct]
  fin_cases g <;>
    norm_num [wrong,good,vals,lo,bits,rangeGadget_correct,Fin.forall_fin_succ,Fin.sum_univ_succ,
      AirModularView.constDigit,Bignum.digitsLE,List.getD]

theorem wrong_values (g : Fin 16) : value id wrong g=if g.val=14 then 19 else vals g := by
  fin_cases g <;>
    norm_num [value,wrong,good,vals,AirBignum.limbVals,lo,List.ofFn_succ,Bignum.denoteNat] <;> decide +kernel

/-- The missing final2*4 term leaves every public word canonical but source
acceptance is impossible. The theorem uses source soundness, not a producer check. -/
theorem wrong_refused : ¬systemAccepts id (BfvKeyswitchCore.system 37 wrong) := by
  intro hs
  have h := (sound 37 (by decide) (by decide) wrong id hs).2 0
  norm_num [wrong_values,vals,oIndex,aIndex,dIndex,kIndex,Fin.sum_univ_succ] at h

theorem capacity_inhabited : ∃ q : Nat,0<q ∧ 5*q<512^6 := ⟨37,by decide,by decide⟩

theorem quotient_capacity (q ad : Nat) (a b : Fin 4 → Nat) (hq : 0<q)
    (hcap : 5*q<512^6) (had : ad<q) (ha : ∀ i,a i<q) (hb : ∀ i,b i<q) :
    (ad+∑ i : Fin 4,a i*b i)/q<512^6 := by
  have hs : (∑ i : Fin 4,a i*b i)≤4*(q*q) := by
    calc
      _ ≤ ∑ _i : Fin 4,q*q := Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul (Nat.le_of_lt (ha i)) (Nat.le_of_lt (hb i))
      _ = _ := by simp
  have hp : ad+(∑ i : Fin 4,a i*b i)<(5*q)*q := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul hq).2 hp
  omega

theorem field_column_capacity :
    4*(36*261121)+511+65535+16777216<babyBearP ∧
    511+36*261121+512*65535+32768<babyBearP := by decide
end Minidregg.Compiler.BfvKeyswitchCore.Exhibits
