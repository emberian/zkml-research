/- Whole-coefficient BFV linear-combination arithmetic, generated from the existing
range/addition gadgets and one reusable signed-carry source constructor. -/
import Compiler.IntegerCertificateEmission

namespace Minidregg.Compiler.BfvLinearCombination
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

structure RowWires (J : Type) where
  canonical : Fin 3 → AirBignum.AddWires J 7 6
  quotient : J
  quotientBit : Fin 3 → J
  carry : Fin 8 → J
  carryBit : Fin 8 → Fin 4 → J

def word {J : Type} (asg : J → BabyBear) (w : RowWires J) (kind : Fin 3) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (w.canonical kind).x)

def canonicalSystem {J : Type} (q : Nat) (w : AirBignum.AddWires J 7 6) :
    ConstraintSystem BabyBear J :=
  AirBignum.addGadget w ++ AirModularView.pinWordSystem (limbBits := 6) (q-1) w.z

def column {J : Type} (q : Nat) (w : RowWires J) (i : Fin 7) : Term (AirSig BabyBear J) :=
  add'
    (add' (add' (mul' (cst 3) (vr ((w.canonical 0).x i)))
      (mul' (cst 5) (vr ((w.canonical 1).x i))))
      (add' (vr (w.carry i.castSucc)) (cst 512)))
    (mul' (cst (-1))
      (add' (add' (vr ((w.canonical 2).x i))
        (mul' (cst (AirModularView.constDigit 64 7 q i : BabyBear)) (vr w.quotient)))
        (add' (mul' (cst 64) (vr (w.carry i.succ))) (cst 8))))

def rowSystem {J : Type} (q : Nat) (w : RowWires J) : ConstraintSystem BabyBear J :=
  (List.finRange 3).flatMap (fun kind => canonicalSystem q (w.canonical kind)) ++
  rangeGadget w.quotient w.quotientBit ++
  AirBignum.limbRangeSystem w.carry w.carryBit ++
  [add' (vr (w.carry 0)) (cst (-8)), add' (vr (w.carry 7)) (cst (-8))] ++
  (List.finRange 7).map (column q w)

/-- Acceptance forces the complete modular linear combination, with all three
input/output word bounds supplied by the emitted relation itself. -/
def RowSound {J : Type} (q : Nat) (w : RowWires J) : Prop :=
  ∀ asg : J → BabyBear, systemAccepts asg (rowSystem q w) →
    (∀ kind, word asg w kind < q) ∧
    word asg w 2 = (3 * word asg w 0 + 5 * word asg w 1) % q

theorem canonicalSystem_sound {J : Type} (q : Nat) (hq : 0 < q) (hqcap : q < 64^7)
    (w : AirBignum.AddWires J 7 6) (asg : J → BabyBear)
    (h : systemAccepts asg (canonicalSystem q w)) :
    Bignum.denoteNat 64 (AirBignum.limbVals asg w.x) < q ∧
    ∀ i, (asg (w.x i)).val < 64 := by
  obtain ⟨ha,hp⟩ := (systemAccepts_append asg _ _).mp h
  have hh := AirBignum.addGadget_sound (by norm_num [babyBearP] : 2*2^6 ≤ babyBearP) asg w ha
  have hpin := (AirModularView.pinWordSystem_correct asg (q-1) w.z).mp hp
  have hz := AirModularView.denote_pinned_word (by positivity : 0 < 2^6)
    (by norm_num [babyBearP] : 2^6 ≤ babyBearP)
    (show q-1 < (2^6)^7 by norm_num at *; omega) asg w.z hpin
  constructor
  · norm_num at hz hh
    omega
  · intro i
    have hr := (AirBignum.addGadget_correct asg w).mp ha
    exact rangeGadget_val_lt (by norm_num [babyBearP] : 2^6 ≤ babyBearP)
      asg (w.x i) (w.xBit i) (hr.1 i)

/-- Signed carry c is encoded as c+8. The endpoint correction telescopes;
there is no coefficientwise reduction or discarded integer quotient. -/
theorem radix_balance : ∀ {n : Nat} (a b out qd : Fin n → Nat)
    (carry : Fin (n+1) → Nat) (k : Nat),
    (∀ i, 3*a i + 5*b i + carry i.castSucc + 512 =
      out i + qd i*k + 64*carry i.succ + 8) →
    3*Bignum.denoteNat 64 (List.ofFn a) + 5*Bignum.denoteNat 64 (List.ofFn b) +
      carry 0 + 8*64^n =
    Bignum.denoteNat 64 (List.ofFn out) + Bignum.denoteNat 64 (List.ofFn qd)*k +
      64^n*carry (Fin.last n) + 8 := by
  intro n
  induction n with
  | zero => intro a b out qd carry k _; simp
  | succ n ih =>
    intro a b out qd carry k heq
    have hlo := heq (0 : Fin (n+1))
    have htail := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => out i.succ) (fun i => qd i.succ) (fun i => carry i.succ) k
      (fun i => heq i.succ)
    simp only [List.ofFn_succ, Bignum.denoteNat_cons, pow_succ]
    have hzero : (0 : Fin (n+1)).castSucc = (0 : Fin (n+2)) := by apply Fin.ext; rfl
    have hlast : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
    rw [hzero] at hlo
    dsimp only at htail
    rw [hlast] at htail
    nlinarith [hlo, htail]

theorem column_correct {J : Type} (q : Nat) (w : RowWires J) (asg : J → BabyBear) (i : Fin 7) :
    accepts asg (column q w i) ↔
      3*asg ((w.canonical 0).x i) + 5*asg ((w.canonical 1).x i) +
        asg (w.carry i.castSucc) + 512 =
      asg ((w.canonical 2).x i) +
        (AirModularView.constDigit 64 7 q i : BabyBear)*asg w.quotient +
        64*asg (w.carry i.succ) + 8 := by
  simp only [accepts, column, eval_add', eval_mul', eval_cst, eval_vr]
  constructor <;> intro h <;> linear_combination h

theorem rowSystem_sound {J : Type} (q : Nat) (hq : 0 < q) (hqcap : q < 64^7)
    (w : RowWires J) : RowSound q w := by
  intro asg hs
  simp only [rowSystem, systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨hcan,hqrange⟩,hcrange⟩,hend⟩,hcols⟩ := hs
  have hcan' (kind : Fin 3) : systemAccepts asg (canonicalSystem q (w.canonical kind)) := by
    intro term ht
    exact hcan term (List.mem_flatMap.mpr ⟨kind,List.mem_finRange kind,ht⟩)
  have hwords := fun kind => canonicalSystem_sound q hq hqcap (w.canonical kind) asg (hcan' kind)
  have hkr : (asg w.quotient).val < 8 :=
    rangeGadget_val_lt (by norm_num [babyBearP] : 2^3 ≤ babyBearP) asg _ _ hqrange
  have hcr : ∀ i, (asg (w.carry i)).val < 16 := fun i =>
    rangeGadget_val_lt (by norm_num [babyBearP] : 2^4 ≤ babyBearP) asg _ _
      ((AirBignum.limbRangeSystem_correct asg w.carry w.carryBit).mp hcrange i)
  have hcol (i : Fin 7) :
      3*(asg ((w.canonical 0).x i)).val + 5*(asg ((w.canonical 1).x i)).val +
        (asg (w.carry i.castSucc)).val + 512 =
      (asg ((w.canonical 2).x i)).val +
        AirModularView.constDigit 64 7 q i*(asg w.quotient).val +
        64*(asg (w.carry i.succ)).val + 8 := by
    have hf := (column_correct q w asg i).mp
      (hcols _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    have ha := (hwords 0).2 i
    have hb := (hwords 1).2 i
    have ho := (hwords 2).2 i
    have hc0 := hcr i.castSucc
    have hc1 := hcr i.succ
    have hqd := constDigit_lt 64 7 q (by omega) i
    have hm := Nat.mul_le_mul (show AirModularView.constDigit 64 7 q i ≤ 63 by omega)
      (show (asg w.quotient).val ≤ 7 by omega)
    have hl : 3*(asg ((w.canonical 0).x i)).val + 5*(asg ((w.canonical 1).x i)).val +
        (asg (w.carry i.castSucc)).val + 512 < babyBearP := by norm_num [babyBearP]; omega
    have hr : (asg ((w.canonical 2).x i)).val +
        AirModularView.constDigit 64 7 q i*(asg w.quotient).val +
        64*(asg (w.carry i.succ)).val + 8 < babyBearP := by norm_num [babyBearP]; omega
    have heq : ((3*(asg ((w.canonical 0).x i)).val + 5*(asg ((w.canonical 1).x i)).val +
        (asg (w.carry i.castSucc)).val + 512 : Nat) : BabyBear) =
      (( (asg ((w.canonical 2).x i)).val +
        AirModularView.constDigit 64 7 q i*(asg w.quotient).val +
        64*(asg (w.carry i.succ)).val + 8 : Nat) : BabyBear) := by simpa using hf
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_cast_of_lt hl,ZMod.val_cast_of_lt hr] using hv
  have hends : asg (w.carry 0) = 8 ∧ asg (w.carry 7) = 8 := by
    simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,
      eval_add',eval_vr,eval_cst,add_neg_eq_zero] using hend
  have h0 : (asg (w.carry 0)).val = 8 := by rw [hends.1]; decide +kernel
  have h7 : (asg (w.carry 7)).val = 8 := by rw [hends.2]; decide +kernel
  have ht := radix_balance (fun i => (asg ((w.canonical 0).x i)).val)
    (fun i => (asg ((w.canonical 1).x i)).val) (fun i => (asg ((w.canonical 2).x i)).val)
    (AirModularView.constDigit 64 7 q) (fun i => (asg (w.carry i)).val) (asg w.quotient).val hcol
  have hqd : Bignum.denoteNat 64 (List.ofFn (AirModularView.constDigit 64 7 q)) = q := by
    rw [AirModularView.constDigits_eq]
    exact Bignum.denoteNat_digitsLE (by omega) 7 q hqcap
  change _ + _ + (asg (w.carry 0)).val + _ = _ + _ + _*(asg (w.carry 7)).val + _ at ht
  rw [h0,h7,hqd] at ht
  have heq : 3*word asg w 0 + 5*word asg w 1 = word asg w 2 + q*(asg w.quotient).val := by
    dsimp [word,AirBignum.limbVals]
    omega
  refine ⟨fun kind => (hwords kind).1,?_⟩
  rw [heq,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (hwords 2).1).symm


/-- info: 'Minidregg.Compiler.BfvLinearCombination.canonicalSystem_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonicalSystem_sound

/-- info: 'Minidregg.Compiler.BfvLinearCombination.radix_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms radix_balance

/-- info: 'Minidregg.Compiler.BfvLinearCombination.column_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms column_correct

/-- info: 'Minidregg.Compiler.BfvLinearCombination.rowSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSystem_sound

end Minidregg.Compiler.BfvLinearCombination
