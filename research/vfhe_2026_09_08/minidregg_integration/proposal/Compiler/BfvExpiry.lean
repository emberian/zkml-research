import Compiler.BfvLinearCombination

namespace Minidregg.Compiler.BfvExpiry
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

structure RowWires (J : Type) where
  canonical : Fin 4 → AirBignum.AddWires J 7 6
  quotient : J
  quotientBit : Fin 2 → J
  carry : Fin 8 → J
  carryBit : Fin 8 → Fin 3 → J

def word {J : Type} (asg : J → BabyBear) (w : RowWires J) (kind : Fin 4) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (w.canonical kind).x)

def column {J : Type} (q : Nat) (w : RowWires J) (i : Fin 7) : Term (AirSig BabyBear J) :=
  let qd := cst (AirModularView.constDigit 64 7 q i : BabyBear)
  add' (add' (add' (vr ((w.canonical 0).x i)) (vr ((w.canonical 1).x i)))
    (add' qd (add' (vr (w.carry i.castSucc)) (cst 256))))
    (mul' (cst (-1))
      (add' (add' (vr ((w.canonical 2).x i)) (vr ((w.canonical 3).x i)))
        (add' (mul' qd (vr w.quotient))
          (add' (mul' (cst 64) (vr (w.carry i.succ))) (cst 4)))))

def rowSystem {J : Type} (q : Nat) (w : RowWires J) : ConstraintSystem BabyBear J :=
  (List.finRange 4).flatMap (fun kind => BfvLinearCombination.canonicalSystem q (w.canonical kind)) ++
  rangeGadget w.quotient w.quotientBit ++ AirBignum.limbRangeSystem w.carry w.carryBit ++
  [add' (vr (w.carry 0)) (cst (-4)),add' (vr (w.carry 7)) (cst (-4))] ++
  (List.finRange 7).map (column q w)

/-- Complete expiry arithmetic with canonical accumulator, fresh, old and output
words; adding q makes the integer numerator nonnegative before reduction. -/
def RowSound {J : Type} (q : Nat) (w : RowWires J) : Prop :=
  ∀ asg : J → BabyBear, systemAccepts asg (rowSystem q w) →
    (∀ kind,word asg w kind < q) ∧
    word asg w 3 = (word asg w 0+word asg w 1+q-word asg w 2)%q

theorem radix_balance : ∀ {n : Nat} (a fresh old out qd : Fin n → Nat)
    (carry : Fin (n+1) → Nat) (j : Nat),
    (∀ i,a i+fresh i+qd i+carry i.castSucc+256 =
      old i+out i+qd i*j+64*carry i.succ+4) →
    Bignum.denoteNat 64 (List.ofFn a)+Bignum.denoteNat 64 (List.ofFn fresh)+
      Bignum.denoteNat 64 (List.ofFn qd)+carry 0+4*64^n =
    Bignum.denoteNat 64 (List.ofFn old)+Bignum.denoteNat 64 (List.ofFn out)+
      Bignum.denoteNat 64 (List.ofFn qd)*j+64^n*carry (Fin.last n)+4 := by
  intro n
  induction n with
  | zero => intro a fresh old out qd carry j _; simp
  | succ n ih =>
    intro a fresh old out qd carry j heq
    have hlo := heq (0 : Fin (n+1))
    have htail := ih (fun i => a i.succ) (fun i => fresh i.succ)
      (fun i => old i.succ) (fun i => out i.succ) (fun i => qd i.succ)
      (fun i => carry i.succ) j (fun i => heq i.succ)
    simp only [List.ofFn_succ,Bignum.denoteNat_cons,pow_succ]
    have hzero : (0 : Fin (n+1)).castSucc = (0 : Fin (n+2)) := by apply Fin.ext; rfl
    have hlast : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
    rw [hzero] at hlo
    dsimp only at htail
    rw [hlast] at htail
    nlinarith [hlo,htail]

theorem column_correct {J : Type} (q : Nat) (w : RowWires J) (asg : J → BabyBear) (i : Fin 7) :
    accepts asg (column q w i) ↔
    asg ((w.canonical 0).x i)+asg ((w.canonical 1).x i)+
      (AirModularView.constDigit 64 7 q i : BabyBear)+asg (w.carry i.castSucc)+256 =
    asg ((w.canonical 2).x i)+asg ((w.canonical 3).x i)+
      (AirModularView.constDigit 64 7 q i : BabyBear)*asg w.quotient+
      64*asg (w.carry i.succ)+4 := by
  simp only [accepts,column,eval_add',eval_mul',eval_vr,eval_cst]
  constructor <;> intro h <;> linear_combination h

theorem rowSystem_sound {J : Type} (q : Nat) (hq : 0 < q) (hqcap : q < 64^7)
    (w : RowWires J) : RowSound q w := by
  intro asg hs
  simp only [rowSystem,systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨hcan,hqr⟩,hcr⟩,hend⟩,hcols⟩ := hs
  have hcan' (kind : Fin 4) : systemAccepts asg (BfvLinearCombination.canonicalSystem q (w.canonical kind)) := by
    intro term ht
    exact hcan term (List.mem_flatMap.mpr ⟨kind,List.mem_finRange kind,ht⟩)
  have hwords := fun kind => BfvLinearCombination.canonicalSystem_sound q hq hqcap (w.canonical kind) asg (hcan' kind)
  have hj : (asg w.quotient).val < 4 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^2 ≤ babyBearP) asg _ _ hqr
  have hc : ∀ i,(asg (w.carry i)).val < 8 := fun i => rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^3 ≤ babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg w.carry w.carryBit).mp hcr i)
  have hcol (i : Fin 7) :
    (asg ((w.canonical 0).x i)).val+(asg ((w.canonical 1).x i)).val+
      AirModularView.constDigit 64 7 q i+(asg (w.carry i.castSucc)).val+256 =
    (asg ((w.canonical 2).x i)).val+(asg ((w.canonical 3).x i)).val+
      AirModularView.constDigit 64 7 q i*(asg w.quotient).val+
      64*(asg (w.carry i.succ)).val+4 := by
    have hf := (column_correct q w asg i).mp
      (hcols _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    have ha := (hwords 0).2 i
    have hfr := (hwords 1).2 i
    have hold := (hwords 2).2 i
    have hout := (hwords 3).2 i
    have hc0 := hc i.castSucc
    have hc1 := hc i.succ
    have hqd := constDigit_lt 64 7 q (by omega) i
    have hm := Nat.mul_le_mul (show AirModularView.constDigit 64 7 q i ≤ 63 by omega)
      (show (asg w.quotient).val ≤ 3 by omega)
    have hl : (asg ((w.canonical 0).x i)).val+(asg ((w.canonical 1).x i)).val+
      AirModularView.constDigit 64 7 q i+(asg (w.carry i.castSucc)).val+256 < babyBearP := by
      norm_num [babyBearP]; omega
    have hr : (asg ((w.canonical 2).x i)).val+(asg ((w.canonical 3).x i)).val+
      AirModularView.constDigit 64 7 q i*(asg w.quotient).val+
      64*(asg (w.carry i.succ)).val+4 < babyBearP := by norm_num [babyBearP]; omega
    have heq : (((asg ((w.canonical 0).x i)).val+(asg ((w.canonical 1).x i)).val+
      AirModularView.constDigit 64 7 q i+(asg (w.carry i.castSucc)).val+256 : Nat) : BabyBear) =
      (((asg ((w.canonical 2).x i)).val+(asg ((w.canonical 3).x i)).val+
        AirModularView.constDigit 64 7 q i*(asg w.quotient).val+
        64*(asg (w.carry i.succ)).val+4 : Nat) : BabyBear) := by simpa using hf
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_cast_of_lt hl,ZMod.val_cast_of_lt hr] using hv
  have hends : asg (w.carry 0) = 4 ∧ asg (w.carry 7) = 4 := by
    simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,
      eval_add',eval_vr,eval_cst,add_neg_eq_zero] using hend
  have h0 : (asg (w.carry 0)).val = 4 := by rw [hends.1]; decide +kernel
  have h7 : (asg (w.carry 7)).val = 4 := by rw [hends.2]; decide +kernel
  have ht := radix_balance (fun i => (asg ((w.canonical 0).x i)).val)
    (fun i => (asg ((w.canonical 1).x i)).val) (fun i => (asg ((w.canonical 2).x i)).val)
    (fun i => (asg ((w.canonical 3).x i)).val) (AirModularView.constDigit 64 7 q)
    (fun i => (asg (w.carry i)).val) (asg w.quotient).val hcol
  have hqd : Bignum.denoteNat 64 (List.ofFn (AirModularView.constDigit 64 7 q)) = q := by
    rw [AirModularView.constDigits_eq]
    exact Bignum.denoteNat_digitsLE (by omega) 7 q hqcap
  change _+_+_+(asg (w.carry 0)).val+_ = _+_+_+_*(asg (w.carry 7)).val+_ at ht
  rw [h0,h7,hqd] at ht
  have heq : word asg w 0+word asg w 1+q-word asg w 2 = word asg w 3+q*(asg w.quotient).val := by
    dsimp [word,AirBignum.limbVals]
    omega
  refine ⟨fun kind => (hwords kind).1,?_⟩
  rw [heq,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (hwords 3).1).symm

/-- info: 'Minidregg.Compiler.BfvExpiry.radix_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms radix_balance
/-- info: 'Minidregg.Compiler.BfvExpiry.column_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms column_correct
/-- info: 'Minidregg.Compiler.BfvExpiry.rowSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSystem_sound

end Minidregg.Compiler.BfvExpiry
