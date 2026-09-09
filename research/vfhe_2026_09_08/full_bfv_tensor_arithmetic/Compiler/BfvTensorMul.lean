/- Compiler-native whole-coefficient schoolbook multiplication for the actual
BFV primes. The source itself supplies all input/output canonical bounds. -/
import Compiler.IntegerCertificateEmission
namespace Minidregg.Compiler.BfvTensorMul
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.IntegerCertificateEmission Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
structure RowWires (J : Type) where
  canonical : Fin 3 → AirBignum.AddWires J 11 6
  quotient : Fin 11 → J
  quotientBit : Fin 11 → Fin 6 → J
  carry : Fin 23 → J
  carryBit : Fin 23 → Fin 12 → J

def word {J : Type} (asg : J → BabyBear) (w : RowWires J) (kind : Fin 3) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (w.canonical kind).x)
def convolution {R : Type} [Semiring R] (a b : Fin 11 → R) (t : Fin 22) : R :=
  ∑ i : Fin 11, ∑ j : Fin 11, if i.val+j.val=t.val then a i*b j else 0
def padded {R : Type} [Zero R] (a : Fin 11 → R) (t : Fin 22) : R :=
  if h : t.val < 11 then a ⟨t.val,h⟩ else 0
def sumTerm {J : Type} (f : Fin 11 → Term (AirSig BabyBear J)) : Term (AirSig BabyBear J) :=
  (List.ofFn f).foldr add' (cst 0)
def convolutionTerm {J : Type} (a b : Fin 11 → Term (AirSig BabyBear J)) (t : Fin 22) : Term (AirSig BabyBear J) :=
  sumTerm fun i => sumTerm fun j => if i.val+j.val=t.val then mul' (a i) (b j) else cst 0

def canonicalSystem {J : Type} (q : Nat) (w : AirBignum.AddWires J 11 6) :
    ConstraintSystem BabyBear J :=
  AirBignum.addGadget w ++ AirModularView.pinWordSystem (limbBits := 6) (q-1) w.z


def column {J : Type} (q factor : Nat) (w : RowWires J) (t : Fin 22) : Term (AirSig BabyBear J) :=
  let ab := convolutionTerm (fun i => vr ((w.canonical 0).x i)) (fun i => vr ((w.canonical 1).x i)) t
  let qk := convolutionTerm (fun i => cst (AirModularView.constDigit 64 11 q i : BabyBear)) (fun i => vr (w.quotient i)) t
  let o := if h : t.val < 11 then vr ((w.canonical 2).x ⟨t.val,h⟩) else cst 0
  add' (add' (add' (mul' (cst (factor : BabyBear)) ab) (vr (w.carry t.castSucc))) (cst 131072))
    (mul' (cst (-1)) (add' (add' (add' o qk) (mul' (cst 64) (vr (w.carry t.succ)))) (cst 2048)))
def rowSystem {J : Type} (q factor : Nat) (w : RowWires J) : ConstraintSystem BabyBear J :=
  (List.finRange 3).flatMap (fun kind => canonicalSystem q (w.canonical kind)) ++
  AirBignum.limbRangeSystem w.quotient w.quotientBit ++
  AirBignum.limbRangeSystem w.carry w.carryBit ++
  [add' (vr (w.carry 0)) (cst (-2048)),add' (vr (w.carry 22)) (cst (-2048))] ++
  (List.finRange 22).map (column q factor w)
def RowSound {J : Type} (q factor : Nat) (w : RowWires J) : Prop :=
  ∀ asg : J → BabyBear, systemAccepts asg (rowSystem q factor w) →
    (∀ kind,word asg w kind < q) ∧ word asg w 2 = (factor*word asg w 0*word asg w 1)%q

theorem canonicalSystem_sound {J : Type} (q : Nat) (hq : 0 < q) (hqcap : q < 64^11)
    (w : AirBignum.AddWires J 11 6) (asg : J → BabyBear)
    (h : systemAccepts asg (canonicalSystem q w)) :
    Bignum.denoteNat 64 (AirBignum.limbVals asg w.x) < q ∧
    ∀ i, (asg (w.x i)).val < 64 := by
  obtain ⟨ha,hp⟩ := (systemAccepts_append asg _ _).mp h
  have hh := AirBignum.addGadget_sound (by norm_num [babyBearP] : 2*2^6 ≤ babyBearP) asg w ha
  have hpin := (AirModularView.pinWordSystem_correct asg (q-1) w.z).mp hp
  have hz := AirModularView.denote_pinned_word (by positivity : 0 < 2^6)
    (by norm_num [babyBearP] : 2^6 ≤ babyBearP)
    (show q-1 < (2^6)^11 by norm_num at *; omega) asg w.z hpin
  constructor
  · norm_num at hz hh
    omega
  · intro i
    have hr := (AirBignum.addGadget_correct asg w).mp ha
    exact rangeGadget_val_lt (by norm_num [babyBearP] : 2^6 ≤ babyBearP)
      asg (w.x i) (w.xBit i) (hr.1 i)


theorem sumTerm_eval {J : Type} (asg : J → BabyBear) (f : Fin 11 → Term (AirSig BabyBear J)) :
    eval asg (sumTerm f) = ∑ i : Fin 11, eval asg (f i) := by
  simp [sumTerm, List.ofFn_succ, Fin.sum_univ_succ, eval_add', eval_cst]
theorem convolutionTerm_eval {J : Type} (asg : J → BabyBear) (a b : Fin 11 → Term (AirSig BabyBear J)) (t : Fin 22) :
    eval asg (convolutionTerm a b t) = convolution (fun i => eval asg (a i)) (fun i => eval asg (b i)) t := by
  simp only [convolutionTerm, sumTerm_eval, convolution]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp [eval_mul', eval_cst]
theorem convolution_denote (a b : Fin 11 → Nat) :
    Bignum.denoteNat 64 (List.ofFn (convolution a b)) =
      Bignum.denoteNat 64 (List.ofFn a)*Bignum.denoteNat 64 (List.ofFn b) := by
  norm_num [convolution,Fin.sum_univ_succ,List.ofFn_succ,Bignum.denoteNat]
  ring
theorem padded_denote (a : Fin 11 → Nat) :
    Bignum.denoteNat 64 (List.ofFn (padded a)) = Bignum.denoteNat 64 (List.ofFn a) := by
  norm_num [padded,List.ofFn_succ,Bignum.denoteNat]
  rfl
theorem convolution_bound (a b : Fin 11 → Nat) (ha : ∀ i,a i<64) (hb : ∀ i,b i<64) (t : Fin 22) :
    convolution a b t ≤ 121*3969 := by
  unfold convolution
  calc
    _ ≤ ∑ _i : Fin 11, ∑ _j : Fin 11, 3969 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split
      · exact Nat.mul_le_mul (show a i ≤ 63 by have := ha i; omega) (show b j ≤ 63 by have := hb j; omega)
      · omega
    _ = _ := by norm_num
theorem column_correct {J : Type} (q factor : Nat) (w : RowWires J) (asg : J → BabyBear) (t : Fin 22) :
    accepts asg (column q factor w t) ↔
      (factor : BabyBear)*convolution (fun i => asg ((w.canonical 0).x i)) (fun i => asg ((w.canonical 1).x i)) t + asg (w.carry t.castSucc) + 131072 =
      padded (fun i => asg ((w.canonical 2).x i)) t +
        convolution (fun i => (AirModularView.constDigit 64 11 q i : BabyBear)) (fun i => asg (w.quotient i)) t +64*asg (w.carry t.succ)+2048 := by
  simp only [accepts,column,eval_add',eval_mul',eval_cst,eval_vr,convolutionTerm_eval]
  have ho : eval asg (if h : t.val<11 then vr ((w.canonical 2).x ⟨t.val,h⟩) else cst 0) =
      padded (fun i => asg ((w.canonical 2).x i)) t := by unfold padded; split <;> rfl
  simp only [ho]
  constructor <;> intro h <;> linear_combination h
/-- Offset2048 represents signed schoolbook carries without field subtraction.
The final endpoint cancels exactly, including the otherwise unused top column. -/
theorem radix_balance : ∀ {n : Nat} (a b : Fin n → Nat) (carry : Fin (n+1) → Nat),
    (∀ i,a i+carry i.castSucc+131072=b i+64*carry i.succ+2048) →
    Bignum.denoteNat 64 (List.ofFn a)+carry 0+2048*64^n =
    Bignum.denoteNat 64 (List.ofFn b)+64^n*carry (Fin.last n)+2048 := by
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
theorem denote_scale : ∀ {n : Nat} (factor : Nat) (a : Fin n → Nat),
    Bignum.denoteNat 64 (List.ofFn (fun i => factor*a i)) =
      factor*Bignum.denoteNat 64 (List.ofFn a) := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih => intro factor a; simp only [List.ofFn_succ,Bignum.denoteNat_cons,ih]; ring

theorem convolution_cast (a b : Fin 11 → Nat) (t : Fin 22) :
    ((convolution a b t : Nat) : BabyBear) = convolution (fun i => (a i : BabyBear)) (fun i => (b i : BabyBear)) t := by
  simp only [convolution,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp only [Nat.cast_mul,Nat.cast_zero]
theorem padded_cast (a : Fin 11 → Nat) (t : Fin 22) :
    ((padded a t : Nat) : BabyBear) = padded (fun i => (a i : BabyBear)) t := by
  unfold padded
  split <;> simp

theorem rowSystem_sound {J : Type} (q factor : Nat) (hq : 0<q) (hqcap : q<64^11) (hfactor : factor≤2)
    (w : RowWires J) : RowSound q factor w := by
  intro asg hs
  simp only [rowSystem,systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨hcan,hqr⟩,hcr⟩,hend⟩,hcols⟩ := hs
  have hcan' (k : Fin 3) : systemAccepts asg (canonicalSystem q (w.canonical k)) := by
    intro t ht
    exact hcan t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩)
  have hw := fun k => canonicalSystem_sound q hq hqcap (w.canonical k) asg (hcan' k)
  let a : Fin 11 → Nat := fun i => (asg ((w.canonical 0).x i)).val
  let b : Fin 11 → Nat := fun i => (asg ((w.canonical 1).x i)).val
  let o : Fin 11 → Nat := fun i => (asg ((w.canonical 2).x i)).val
  let k : Fin 11 → Nat := fun i => (asg (w.quotient i)).val
  let qd := AirModularView.constDigit 64 11 q
  let c : Fin 23 → Nat := fun i => (asg (w.carry i)).val
  have hk (i : Fin 11) : k i<64 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^6 ≤ babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hqr i)
  have hc (i : Fin 23) : c i<4096 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^12 ≤ babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hcr i)
  have hqd (i : Fin 11) : qd i<64 := constDigit_lt 64 11 q (by omega) i
  have hcol (t : Fin 22) : factor*convolution a b t+c t.castSucc+131072 =
      (padded o t+convolution qd k t)+64*c t.succ+2048 := by
    have hf := (column_correct q factor w asg t).mp
      (hcols _ (List.mem_map.mpr ⟨t,List.mem_finRange t,rfl⟩))
    have hab := convolution_bound a b (hw 0).2 (hw 1).2 t
    have hqk := convolution_bound qd k hqd hk t
    have ho : padded o t<64 := by unfold padded; split; exact (hw 2).2 _; omega
    have hab2 : factor*convolution a b t ≤ 2*(121*3969) := Nat.mul_le_mul hfactor hab
    have hc0 := hc t.castSucc
    have hc1 := hc t.succ
    have hl : factor*convolution a b t+c t.castSucc+131072<babyBearP := by norm_num [babyBearP]; omega
    have hr : (padded o t+convolution qd k t)+64*c t.succ+2048<babyBearP := by norm_num [babyBearP]; omega
    have heq : ((factor*convolution a b t+c t.castSucc+131072 : Nat) : BabyBear) =
        (((padded o t+convolution qd k t)+64*c t.succ+2048 : Nat) : BabyBear) := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,convolution_cast,padded_cast,
        a,b,o,k,qd,c,ZMod.natCast_zmod_val] using hf
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_cast_of_lt hl,ZMod.val_cast_of_lt hr] using hv
  have he : asg (w.carry 0)=2048 ∧ asg (w.carry 22)=2048 := by
    simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_add',eval_vr,eval_cst,add_neg_eq_zero] using hend
  have h0 : c 0=2048 := by dsimp [c]; rw [he.1]; decide +kernel
  have h14 : c 22=2048 := by dsimp [c]; rw [he.2]; decide +kernel
  have ht := radix_balance (fun t => factor*convolution a b t) (fun t => padded o t+convolution qd k t) c hcol
  rw [denote_scale,convolution_denote,denote_add,padded_denote,convolution_denote] at ht
  have hqden : Bignum.denoteNat 64 (List.ofFn qd)=q := by
    rw [show List.ofFn qd=Bignum.digitsLE 64 11 q from AirModularView.constDigits_eq 64 11 q]
    exact Bignum.denoteNat_digitsLE (by omega) 11 q hqcap
  change _+c 0+_=_+_*c 22+_ at ht
  rw [h0,h14,hqden] at ht
  have hb : factor*word asg w 0*word asg w 1=word asg w 2+q*Bignum.denoteNat 64 (List.ofFn k) := by
    change factor*Bignum.denoteNat 64 (List.ofFn a)*Bignum.denoteNat 64 (List.ofFn b)=
      Bignum.denoteNat 64 (List.ofFn o)+q*Bignum.denoteNat 64 (List.ofFn k)
    rw [Nat.mul_assoc]
    omega
  refine ⟨fun kind => (hw kind).1,?_⟩
  rw [hb,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (hw 2).1).symm
end Minidregg.Compiler.BfvTensorMul

