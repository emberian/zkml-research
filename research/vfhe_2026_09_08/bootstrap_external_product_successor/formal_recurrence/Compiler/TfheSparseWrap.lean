/- A radix64 modular wrap source in the existing arithmetic DSL. Its lift uses
bounded BabyBear columns and concludes in the composite ring ZMod(2^24). -/
import Compiler.BfvQueryMul
namespace Minidregg.Compiler.TfheSparseWrap
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

def modulus : ℕ := 16777216
abbrev SmallRing := ZMod modulus

def wrapColumn {J : Type} (a b : Fin 4 → Term (AirSig BabyBear J)) (c : Fin 5 → J) (i : Fin 4) : Term (AirSig BabyBear J) :=
  add' (add' (add' (a i) (vr (c i.castSucc))) (cst 256))
    (mul' (cst (-1)) (add' (add' (b i) (mul' (cst 64) (vr (c i.succ)))) (cst 4)))
def wrapSystem {J : Type} (a b : Fin 4 → Term (AirSig BabyBear J)) (c : Fin 5 → J) (cb : Fin 5 → Fin 3 → J) : ConstraintSystem BabyBear J :=
  AirBignum.limbRangeSystem c cb ++ [add' (vr (c 0)) (cst (-4))] ++
  (List.finRange 4).map (wrapColumn a b c)
def WrapSound : Prop := ∀ (J : Type) (asg : J → BabyBear)
    (a b : Fin 4 → Term (AirSig BabyBear J)) (c : Fin 5 → J) (cb : Fin 5 → Fin 3 → J)
    (av bv : Fin 4 → ℕ),
    (∀ i, eval asg (a i)=(av i : BabyBear) ∧ eval asg (b i)=(bv i : BabyBear)) →
    (∀ i,av i<512 ∧ bv i<512) → systemAccepts asg (wrapSystem a b c cb) →
    (Bignum.denoteNat 64 (List.ofFn av) : SmallRing)=Bignum.denoteNat 64 (List.ofFn bv)

theorem wrapColumn_correct {J : Type} (asg : J → BabyBear)
    (a b : Fin 4 → Term (AirSig BabyBear J)) (c : Fin 5 → J) (i : Fin 4) :
    accepts asg (wrapColumn a b c i) ↔
    eval asg (a i)+asg (c i.castSucc)+256=eval asg (b i)+64*asg (c i.succ)+4 := by
  simp only [accepts,wrapColumn,eval_add',eval_mul',eval_vr,eval_cst]
  constructor <;> intro h <;> linear_combination h

theorem radix_balance : ∀ {n : ℕ} (a b : Fin n → ℕ) (c : Fin (n+1) → ℕ),
    (∀ i,a i+c i.castSucc+256=b i+64*c i.succ+4) →
    Bignum.denoteNat 64 (List.ofFn a)+c 0+4*64^n =
    Bignum.denoteNat 64 (List.ofFn b)+64^n*c (Fin.last n)+4 := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro a b c h
    have hlo := h (0 : Fin (n+1))
    have ht := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ,Bignum.denoteNat_cons,pow_succ]
    have hz : (0 : Fin (n+1)).castSucc=(0 : Fin (n+2)) := by rfl
    have hl : (Fin.last n).succ=Fin.last (n+1) := by apply Fin.ext; rfl
    rw [hz] at hlo
    dsimp only at ht
    rw [hl] at ht
    nlinarith [hlo,ht]

theorem wrap_sound : WrapSound := by
  intro J asg a b c cb av bv heval hb hs
  simp only [wrapSystem,systemAccepts_append] at hs
  obtain ⟨⟨hr,hzero⟩,he⟩ := hs
  have hc (i : Fin 5) : (asg (c i)).val<8 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^3≤babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg c cb).mp hr i)
  have hc0 : (asg (c 0)).val=4 := by
    have hf : asg (c 0)=4 := by simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_add',eval_vr,eval_cst,add_neg_eq_zero] using hzero
    rw [hf]; decide +kernel
  have hcol (i : Fin 4) : av i+(asg (c i.castSucc)).val+256=bv i+64*(asg (c i.succ)).val+4 := by
    have hf := (wrapColumn_correct asg a b c i).mp (he _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    rw [(heval i).1,(heval i).2] at hf
    have hl : av i+(asg (c i.castSucc)).val+256<babyBearP := by have := hb i; have := hc i.castSucc; norm_num [babyBearP]; omega
    have hr : bv i+64*(asg (c i.succ)).val+4<babyBearP := by have := hb i; have := hc i.succ; norm_num [babyBearP]; omega
    have hh : ((av i+(asg (c i.castSucc)).val+256 : ℕ) : BabyBear)=((bv i+64*(asg (c i.succ)).val+4 : ℕ) : BabyBear) := by simpa using hf
    have hv := congrArg ZMod.val hh
    simpa only [ZMod.val_cast_of_lt hl,ZMod.val_cast_of_lt hr] using hv
  have ht := radix_balance av bv (fun i => (asg (c i)).val) hcol
  dsimp only at ht
  rw [hc0] at ht
  have hf := congrArg (fun n : ℕ => (n : SmallRing)) ht
  have hq : (16777216 : SmallRing)=0 := ZMod.natCast_self modulus
  push_cast at hf
  have hm : (67108864 : SmallRing)=0 := by
    calc _=4*(16777216 : SmallRing) := by ring
         _=0 := by rw [hq]; ring
  rw [hq,hm,zero_mul,add_zero,add_zero] at hf
  exact add_right_cancel hf

theorem denote_linear (a b : Fin 4 → ℕ) (k : ℕ) :
    Bignum.denoteNat 64 (List.ofFn (fun i => a i+k*b i)) =
    Bignum.denoteNat 64 (List.ofFn a)+k*Bignum.denoteNat 64 (List.ofFn b) := by
  simp [List.ofFn_succ,Bignum.denoteNat]
  ring
end Minidregg.Compiler.TfheSparseWrap

/-- info: 'Minidregg.Compiler.TfheSparseWrap.wrapColumn_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseWrap.wrapColumn_correct

/-- info: 'Minidregg.Compiler.TfheSparseWrap.radix_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseWrap.radix_balance

/-- info: 'Minidregg.Compiler.TfheSparseWrap.wrap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseWrap.wrap_sound

/-- info: 'Minidregg.Compiler.TfheSparseWrap.denote_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseWrap.denote_linear
