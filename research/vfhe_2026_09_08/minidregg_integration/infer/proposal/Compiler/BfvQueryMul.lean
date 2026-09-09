/- Compiler-native whole-coefficient schoolbook multiplication for the actual
BFV primes. The source itself supplies all input/output canonical bounds. -/
import Compiler.BfvLinearCombination
namespace Minidregg.Compiler.BfvQueryMul
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.IntegerCertificateEmission Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
structure RowWires (J : Type) where
  canonical : Fin 3 → AirBignum.AddWires J 7 6
  quotient : Fin 7 → J
  quotientBit : Fin 7 → Fin 6 → J
  carry : Fin 15 → J
  carryBit : Fin 15 → Fin 10 → J

def word {J : Type} (asg : J → BabyBear) (w : RowWires J) (kind : Fin 3) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (w.canonical kind).x)
def convolution {R : Type} [Semiring R] (a b : Fin 7 → R) (t : Fin 14) : R :=
  ∑ i : Fin 7, ∑ j : Fin 7, if i.val+j.val=t.val then a i*b j else 0
def padded {R : Type} [Zero R] (a : Fin 7 → R) (t : Fin 14) : R :=
  if h : t.val < 7 then a ⟨t.val,h⟩ else 0
def sumTerm {J : Type} (f : Fin 7 → Term (AirSig BabyBear J)) : Term (AirSig BabyBear J) :=
  (List.ofFn f).foldr add' (cst 0)
def convolutionTerm {J : Type} (a b : Fin 7 → Term (AirSig BabyBear J)) (t : Fin 14) : Term (AirSig BabyBear J) :=
  sumTerm fun i => sumTerm fun j => if i.val+j.val=t.val then mul' (a i) (b j) else cst 0

def column {J : Type} (q : Nat) (w : RowWires J) (t : Fin 14) : Term (AirSig BabyBear J) :=
  let ab := convolutionTerm (fun i => vr ((w.canonical 0).x i)) (fun i => vr ((w.canonical 1).x i)) t
  let qk := convolutionTerm (fun i => cst (AirModularView.constDigit 64 7 q i : BabyBear)) (fun i => vr (w.quotient i)) t
  let o := if h : t.val < 7 then vr ((w.canonical 2).x ⟨t.val,h⟩) else cst 0
  add' (add' (add' ab (vr (w.carry t.castSucc))) (cst 32768))
    (mul' (cst (-1)) (add' (add' (add' o qk) (mul' (cst 64) (vr (w.carry t.succ)))) (cst 512)))
def rowSystem {J : Type} (q : Nat) (w : RowWires J) : ConstraintSystem BabyBear J :=
  (List.finRange 3).flatMap (fun kind => BfvLinearCombination.canonicalSystem q (w.canonical kind)) ++
  AirBignum.limbRangeSystem w.quotient w.quotientBit ++
  AirBignum.limbRangeSystem w.carry w.carryBit ++
  [add' (vr (w.carry 0)) (cst (-512)),add' (vr (w.carry 14)) (cst (-512))] ++
  (List.finRange 14).map (column q w)
def RowSound {J : Type} (q : Nat) (w : RowWires J) : Prop :=
  ∀ asg : J → BabyBear, systemAccepts asg (rowSystem q w) →
    (∀ kind,word asg w kind < q) ∧ word asg w 2 = (word asg w 0*word asg w 1)%q

theorem sumTerm_eval {J : Type} (asg : J → BabyBear) (f : Fin 7 → Term (AirSig BabyBear J)) :
    eval asg (sumTerm f) = ∑ i : Fin 7, eval asg (f i) := by
  simp [sumTerm, List.ofFn_succ, Fin.sum_univ_succ, eval_add', eval_cst]
theorem convolutionTerm_eval {J : Type} (asg : J → BabyBear) (a b : Fin 7 → Term (AirSig BabyBear J)) (t : Fin 14) :
    eval asg (convolutionTerm a b t) = convolution (fun i => eval asg (a i)) (fun i => eval asg (b i)) t := by
  simp only [convolutionTerm, sumTerm_eval, convolution]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp [eval_mul', eval_cst]
theorem convolution_denote (a b : Fin 7 → Nat) :
    Bignum.denoteNat 64 (List.ofFn (convolution a b)) =
      Bignum.denoteNat 64 (List.ofFn a)*Bignum.denoteNat 64 (List.ofFn b) := by
  norm_num [convolution,Fin.sum_univ_succ,List.ofFn_succ,Bignum.denoteNat]
  ring
theorem padded_denote (a : Fin 7 → Nat) :
    Bignum.denoteNat 64 (List.ofFn (padded a)) = Bignum.denoteNat 64 (List.ofFn a) := by
  norm_num [padded,List.ofFn_succ,Bignum.denoteNat]
  rfl
theorem convolution_bound (a b : Fin 7 → Nat) (ha : ∀ i,a i<64) (hb : ∀ i,b i<64) (t : Fin 14) :
    convolution a b t ≤ 49*3969 := by
  unfold convolution
  calc
    _ ≤ ∑ _i : Fin 7, ∑ _j : Fin 7, 3969 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split
      · exact Nat.mul_le_mul (show a i ≤ 63 by have := ha i; omega) (show b j ≤ 63 by have := hb j; omega)
      · omega
    _ = _ := by norm_num
theorem column_correct {J : Type} (q : Nat) (w : RowWires J) (asg : J → BabyBear) (t : Fin 14) :
    accepts asg (column q w t) ↔
      convolution (fun i => asg ((w.canonical 0).x i)) (fun i => asg ((w.canonical 1).x i)) t + asg (w.carry t.castSucc) + 32768 =
      padded (fun i => asg ((w.canonical 2).x i)) t +
        convolution (fun i => (AirModularView.constDigit 64 7 q i : BabyBear)) (fun i => asg (w.quotient i)) t +64*asg (w.carry t.succ)+512 := by
  simp only [accepts,column,eval_add',eval_mul',eval_cst,eval_vr,convolutionTerm_eval]
  have ho : eval asg (if h : t.val<7 then vr ((w.canonical 2).x ⟨t.val,h⟩) else cst 0) =
      padded (fun i => asg ((w.canonical 2).x i)) t := by unfold padded; split <;> rfl
  simp only [ho]
  constructor <;> intro h <;> linear_combination h
/-- Offset512 represents signed schoolbook carries without field subtraction.
The final endpoint cancels exactly, including the otherwise unused top column. -/
theorem radix_balance : ∀ {n : Nat} (a b : Fin n → Nat) (carry : Fin (n+1) → Nat),
    (∀ i,a i+carry i.castSucc+32768=b i+64*carry i.succ+512) →
    Bignum.denoteNat 64 (List.ofFn a)+carry 0+512*64^n =
    Bignum.denoteNat 64 (List.ofFn b)+64^n*carry (Fin.last n)+512 := by
  intro n
  induction n with
  | zero => intro a b c _; simp
  | succ n ih =>
    intro a b c heq
    have hlo := heq (0 : Fin (n+1))
    have htail := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ) (fun i => heq i.succ)
    simp only [List.ofFn_succ,Bignum.denoteNat_cons,pow_succ]
    have hzero : (0 : Fin (n+1)).castSucc = (0 : Fin (n+2)) := by apply Fin.ext; rfl
    have hlast : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
    rw [hzero] at hlo
    dsimp only at htail
    rw [hlast] at htail
    nlinarith [hlo,htail]
theorem denote_add : ∀ {n : Nat} (a b : Fin n → Nat),
    Bignum.denoteNat 64 (List.ofFn (fun i => a i+b i)) =
      Bignum.denoteNat 64 (List.ofFn a)+Bignum.denoteNat 64 (List.ofFn b) := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih => intro a b; simp only [List.ofFn_succ,Bignum.denoteNat_cons,ih]; ring
theorem convolution_cast (a b : Fin 7 → Nat) (t : Fin 14) :
    ((convolution a b t : Nat) : BabyBear) = convolution (fun i => (a i : BabyBear)) (fun i => (b i : BabyBear)) t := by
  simp [convolution]
theorem padded_cast (a : Fin 7 → Nat) (t : Fin 14) :
    ((padded a t : Nat) : BabyBear) = padded (fun i => (a i : BabyBear)) t := by
  unfold padded
  split <;> simp

theorem rowSystem_sound {J : Type} (q : Nat) (hq : 0<q) (hqcap : q<64^7)
    (w : RowWires J) : RowSound q w := by
  intro asg hs
  simp only [rowSystem,systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨hcan,hqr⟩,hcr⟩,hend⟩,hcols⟩ := hs
  have hcan' (k : Fin 3) : systemAccepts asg (BfvLinearCombination.canonicalSystem q (w.canonical k)) := by
    intro t ht
    exact hcan t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩)
  have hw := fun k => BfvLinearCombination.canonicalSystem_sound q hq hqcap (w.canonical k) asg (hcan' k)
  let a : Fin 7 → Nat := fun i => (asg ((w.canonical 0).x i)).val
  let b : Fin 7 → Nat := fun i => (asg ((w.canonical 1).x i)).val
  let o : Fin 7 → Nat := fun i => (asg ((w.canonical 2).x i)).val
  let k : Fin 7 → Nat := fun i => (asg (w.quotient i)).val
  let qd := AirModularView.constDigit 64 7 q
  let c : Fin 15 → Nat := fun i => (asg (w.carry i)).val
  have hk (i : Fin 7) : k i<64 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^6 ≤ babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hqr i)
  have hc (i : Fin 15) : c i<1024 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^10 ≤ babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hcr i)
  have hqd (i : Fin 7) : qd i<64 := constDigit_lt 64 7 q (by omega) i
  have hcol (t : Fin 14) : convolution a b t+c t.castSucc+32768 =
      (padded o t+convolution qd k t)+64*c t.succ+512 := by
    have hf := (column_correct q w asg t).mp
      (hcols _ (List.mem_map.mpr ⟨t,List.mem_finRange t,rfl⟩))
    have hab := convolution_bound a b (hw 0).2 (hw 1).2 t
    have hqk := convolution_bound qd k hqd hk t
    have ho : padded o t<64 := by unfold padded; split; exact (hw 2).2 _; omega
    have hc0 := hc t.castSucc
    have hc1 := hc t.succ
    have hl : convolution a b t+c t.castSucc+32768<babyBearP := by norm_num [babyBearP]; omega
    have hr : (padded o t+convolution qd k t)+64*c t.succ+512<babyBearP := by norm_num [babyBearP]; omega
    have heq : ((convolution a b t+c t.castSucc+32768 : Nat) : BabyBear) =
        (((padded o t+convolution qd k t)+64*c t.succ+512 : Nat) : BabyBear) := by
      simpa [convolution_cast,padded_cast,a,b,o,k,qd,c] using hf
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_cast_of_lt hl,ZMod.val_cast_of_lt hr] using hv
  have he : asg (w.carry 0)=512 ∧ asg (w.carry 14)=512 := by
    simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_add',eval_vr,eval_cst,add_neg_eq_zero] using hend
  have h0 : c 0=512 := by dsimp [c]; rw [he.1]; decide +kernel
  have h14 : c 14=512 := by dsimp [c]; rw [he.2]; decide +kernel
  have ht := radix_balance (convolution a b) (fun t => padded o t+convolution qd k t) c hcol
  rw [convolution_denote,denote_add,padded_denote,convolution_denote] at ht
  have hqden : Bignum.denoteNat 64 (List.ofFn qd)=q := by
    rw [show List.ofFn qd=Bignum.digitsLE 64 7 q from AirModularView.constDigits_eq 64 7 q]
    exact Bignum.denoteNat_digitsLE (by omega) 7 q hqcap
  change _+c 0+_=_+_*c 14+_ at ht
  rw [h0,h14,hqden] at ht
  have hb : word asg w 0*word asg w 1=word asg w 2+q*Bignum.denoteNat 64 (List.ofFn k) := by
    change Bignum.denoteNat 64 (List.ofFn a)*Bignum.denoteNat 64 (List.ofFn b)=
      Bignum.denoteNat 64 (List.ofFn o)+q*Bignum.denoteNat 64 (List.ofFn k)
    omega
  refine ⟨fun kind => (hw kind).1,?_⟩
  rw [hb,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (hw 2).1).symm
end Minidregg.Compiler.BfvQueryMul

/-- info: 'Minidregg.Compiler.BfvQueryMul.sumTerm_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.sumTerm_eval

/-- info: 'Minidregg.Compiler.BfvQueryMul.convolutionTerm_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.convolutionTerm_eval

/-- info: 'Minidregg.Compiler.BfvQueryMul.convolution_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.convolution_denote

/-- info: 'Minidregg.Compiler.BfvQueryMul.padded_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.padded_denote

/-- info: 'Minidregg.Compiler.BfvQueryMul.convolution_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.convolution_bound

/-- info: 'Minidregg.Compiler.BfvQueryMul.column_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.column_correct

/-- info: 'Minidregg.Compiler.BfvQueryMul.radix_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.radix_balance

/-- info: 'Minidregg.Compiler.BfvQueryMul.denote_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.denote_add

/-- info: 'Minidregg.Compiler.BfvQueryMul.convolution_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.convolution_cast

/-- info: 'Minidregg.Compiler.BfvQueryMul.padded_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.padded_cast

/-- info: 'Minidregg.Compiler.BfvQueryMul.rowSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryMul.rowSystem_sound
