/- Source-native four-term modular multiply-accumulate for actual BFV switching. -/
import Compiler.IntegerCertificateEmission
namespace Minidregg.Compiler.BfvKeyswitchMac
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.IntegerCertificateEmission Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
structure RowWires (J : Type) where
  canonical : Fin 10 → AirBignum.AddWires J 6 9
  quotient : Fin 6 → J
  quotientBit : Fin 6 → Fin 9 → J
  carry : Fin 13 → J
  carryBit : Fin 13 → Fin 16 → J

def word {J : Type} (asg : J → BabyBear) (w : RowWires J) (kind : Fin 10) : Nat :=
  Bignum.denoteNat 512 (AirBignum.limbVals asg (w.canonical kind).x)
def convolution {R : Type} [Semiring R] (a b : Fin 6 → R) (t : Fin 12) : R :=
  ∑ i : Fin 6, ∑ j : Fin 6, if i.val+j.val=t.val then a i*b j else 0
def products {R : Type} [Semiring R] (a b : Fin 4 → Fin 6 → R) (t : Fin 12) : R :=
  ∑ k : Fin 4,convolution (a k) (b k) t
def padded {R : Type} [Zero R] (a : Fin 6 → R) (t : Fin 12) : R :=
  if h : t.val<6 then a ⟨t.val,h⟩ else 0
def sumTerm {J : Type} (f : Fin 6 → Term (AirSig BabyBear J)) : Term (AirSig BabyBear J) :=
  (List.ofFn f).foldr add' (cst 0)
def convolutionTerm {J : Type} (a b : Fin 6 → Term (AirSig BabyBear J)) (t : Fin 12) : Term (AirSig BabyBear J) :=
  sumTerm fun i => sumTerm fun j => if i.val+j.val=t.val then mul' (a i) (b j) else cst 0

def lhs (k : Fin 4) : Fin 10 := ⟨k.val,by omega⟩
def rhs (k : Fin 4) : Fin 10 := ⟨4+k.val,by omega⟩
def canonicalSystem {J : Type} (q : Nat) (w : AirBignum.AddWires J 6 9) : ConstraintSystem BabyBear J :=
  AirBignum.addGadget w ++ AirModularView.pinWordSystem (limbBits := 9) (q-1) w.z

def productTerm {J : Type} (w : RowWires J) (t : Fin 12) : Term (AirSig BabyBear J) :=
  ((List.finRange 4).map fun k => convolutionTerm
    (fun i => vr ((w.canonical (lhs k)).x i))
    (fun i => vr ((w.canonical (rhs k)).x i)) t).foldr add' (cst 0)
def column {J : Type} (q : Nat) (w : RowWires J) (t : Fin 12) : Term (AirSig BabyBear J) :=
  let ab := productTerm w t
  let qk := convolutionTerm (fun i => cst (AirModularView.constDigit 512 6 q i : BabyBear)) (fun i => vr (w.quotient i)) t
  let o := if h : t.val<6 then vr ((w.canonical 9).x ⟨t.val,h⟩) else cst 0
  let ad := if h : t.val<6 then vr ((w.canonical 8).x ⟨t.val,h⟩) else cst 0
  add' (add' (add' (add' ab ad) (vr (w.carry t.castSucc))) (cst 16777216))
    (mul' (cst (-1)) (add' (add' (add' o qk) (mul' (cst 512) (vr (w.carry t.succ)))) (cst 32768)))
def rowSystem {J : Type} (q : Nat) (w : RowWires J) : ConstraintSystem BabyBear J :=
  (List.finRange 10).flatMap (fun kind => canonicalSystem q (w.canonical kind)) ++
  AirBignum.limbRangeSystem w.quotient w.quotientBit ++
  AirBignum.limbRangeSystem w.carry w.carryBit ++
  [add' (vr (w.carry 0)) (cst (-32768)),add' (vr (w.carry 12)) (cst (-32768))] ++
  (List.finRange 12).map (column q w)
def RowSound {J : Type} (q : Nat) (w : RowWires J) : Prop := ∀ asg : J → BabyBear,
  systemAccepts asg (rowSystem q w) → (∀ k,word asg w k<q) ∧
    word asg w 9=(word asg w 8+∑ k : Fin 4,word asg w (lhs k)*word asg w (rhs k))%q

theorem canonicalSystem_sound {J : Type} (q : Nat) (hq : 0 < q) (hqcap : q < 512^6)
    (w : AirBignum.AddWires J 6 9) (asg : J → BabyBear)
    (h : systemAccepts asg (canonicalSystem q w)) :
    Bignum.denoteNat 512 (AirBignum.limbVals asg w.x) < q ∧
    ∀ i, (asg (w.x i)).val < 512 := by
  obtain ⟨ha,hp⟩ := (systemAccepts_append asg _ _).mp h
  have hh := AirBignum.addGadget_sound (by norm_num [babyBearP] : 2*2^9 ≤ babyBearP) asg w ha
  have hpin := (AirModularView.pinWordSystem_correct asg (q-1) w.z).mp hp
  have hz := AirModularView.denote_pinned_word (by positivity : 0 < 2^9)
    (by norm_num [babyBearP] : 2^9 ≤ babyBearP)
    (show q-1 < (2^9)^6 by norm_num at *; omega) asg w.z hpin
  constructor
  · norm_num at hz hh
    omega
  · intro i
    have hr := (AirBignum.addGadget_correct asg w).mp ha
    exact rangeGadget_val_lt (by norm_num [babyBearP] : 2^9 ≤ babyBearP)
      asg (w.x i) (w.xBit i) (hr.1 i)


theorem sumTerm_eval {J : Type} (asg : J → BabyBear) (f : Fin 6 → Term (AirSig BabyBear J)) :
    eval asg (sumTerm f) = ∑ i : Fin 6, eval asg (f i) := by
  simp [sumTerm, List.ofFn_succ, Fin.sum_univ_succ, eval_add', eval_cst]
theorem convolutionTerm_eval {J : Type} (asg : J → BabyBear) (a b : Fin 6 → Term (AirSig BabyBear J)) (t : Fin 12) :
    eval asg (convolutionTerm a b t) = convolution (fun i => eval asg (a i)) (fun i => eval asg (b i)) t := by
  simp only [convolutionTerm, sumTerm_eval, convolution]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp [eval_mul', eval_cst]
theorem convolution_denote (a b : Fin 6 → Nat) :
    Bignum.denoteNat 512 (List.ofFn (convolution a b)) =
      Bignum.denoteNat 512 (List.ofFn a)*Bignum.denoteNat 512 (List.ofFn b) := by
  norm_num [convolution,Fin.sum_univ_succ,List.ofFn_succ,Bignum.denoteNat]
  ring
theorem padded_denote (a : Fin 6 → Nat) :
    Bignum.denoteNat 512 (List.ofFn (padded a)) = Bignum.denoteNat 512 (List.ofFn a) := by
  norm_num [padded,List.ofFn_succ,Bignum.denoteNat]
  rfl
theorem convolution_bound (a b : Fin 6 → Nat) (ha : ∀ i,a i<512) (hb : ∀ i,b i<512) (t : Fin 12) :
    convolution a b t ≤ 36*261121 := by
  unfold convolution
  calc
    _ ≤ ∑ _i : Fin 6, ∑ _j : Fin 6, 261121 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split
      · exact Nat.mul_le_mul (show a i ≤ 511 by have := ha i; omega) (show b j ≤ 511 by have := hb j; omega)
      · omega
    _ = _ := by norm_num
theorem radix_balance : ∀ {n : Nat} (a b : Fin n → Nat) (carry : Fin (n+1) → Nat),
    (∀ i,a i+carry i.castSucc+16777216=b i+512*carry i.succ+32768) →
    Bignum.denoteNat 512 (List.ofFn a)+carry 0+32768*512^n =
    Bignum.denoteNat 512 (List.ofFn b)+512^n*carry (Fin.last n)+32768 := by
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
    Bignum.denoteNat 512 (List.ofFn (fun i => a i+b i)) =
      Bignum.denoteNat 512 (List.ofFn a)+Bignum.denoteNat 512 (List.ofFn b) := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih => intro a b; simp only [List.ofFn_succ,Bignum.denoteNat_cons,ih]; ring
theorem denote_scale : ∀ {n : Nat} (factor : Nat) (a : Fin n → Nat),
    Bignum.denoteNat 512 (List.ofFn (fun i => factor*a i)) =
      factor*Bignum.denoteNat 512 (List.ofFn a) := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih => intro factor a; simp only [List.ofFn_succ,Bignum.denoteNat_cons,ih]; ring

theorem convolution_cast (a b : Fin 6 → Nat) (t : Fin 12) :
    ((convolution a b t : Nat) : BabyBear) = convolution (fun i => (a i : BabyBear)) (fun i => (b i : BabyBear)) t := by
  simp only [convolution,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp only [Nat.cast_mul,Nat.cast_zero]
theorem padded_cast (a : Fin 6 → Nat) (t : Fin 12) :
    ((padded a t : Nat) : BabyBear) = padded (fun i => (a i : BabyBear)) t := by
  unfold padded
  split <;> simp


theorem denote_sum : ∀ {m n : Nat} (a : Fin m → Fin n → Nat),
    Bignum.denoteNat 512 (List.ofFn (fun i => ∑ k : Fin m,a k i)) =
      ∑ k : Fin m,Bignum.denoteNat 512 (List.ofFn (a k)) := by
  intro m
  induction m with
  | zero =>
    intro n a
    simp only [Fin.sum_univ_zero,List.ofFn_const]
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ,Bignum.denoteNat] using ih
  | succ m ih =>
    intro n a
    simp only [Fin.sum_univ_succ]
    rw [denote_add,ih]

theorem products_denote (a b : Fin 4 → Fin 6 → Nat) :
    Bignum.denoteNat 512 (List.ofFn (products a b)) =
      ∑ k : Fin 4,Bignum.denoteNat 512 (List.ofFn (a k))*Bignum.denoteNat 512 (List.ofFn (b k)) := by
  change Bignum.denoteNat 512 (List.ofFn (fun i => ∑ k : Fin 4,convolution (a k) (b k) i))=_
  rw [denote_sum]
  simp only [convolution_denote]

theorem products_bound (a b : Fin 4 → Fin 6 → Nat)
    (ha : ∀ k i,a k i<512) (hb : ∀ k i,b k i<512) (t : Fin 12) :
    products a b t≤4*(36*261121) := by
  calc
    _ ≤ ∑ _k : Fin 4,36*261121 := Finset.sum_le_sum fun k _ => convolution_bound (a k) (b k) (ha k) (hb k) t
    _ = _ := by simp

theorem products_cast (a b : Fin 4 → Fin 6 → Nat) (t : Fin 12) :
    ((products a b t : Nat) : BabyBear)=products (fun k i => (a k i : BabyBear)) (fun k i => (b k i : BabyBear)) t := by
  simp only [products,Nat.cast_sum,convolution_cast]

theorem productTerm_eval {J : Type} (w : RowWires J) (asg : J → BabyBear) (t : Fin 12) :
    eval asg (productTerm w t)=products
      (fun k i => asg ((w.canonical (lhs k)).x i))
      (fun k i => asg ((w.canonical (rhs k)).x i)) t := by
  simp [productTerm,products,List.finRange_succ,Fin.sum_univ_succ,eval_add',eval_cst,
    convolutionTerm_eval,eval_vr]

theorem column_correct {J : Type} (q : Nat) (w : RowWires J) (asg : J → BabyBear) (t : Fin 12) :
    accepts asg (column q w t) ↔
    products (fun k i => asg ((w.canonical (lhs k)).x i)) (fun k i => asg ((w.canonical (rhs k)).x i)) t+
      padded (fun i => asg ((w.canonical 8).x i)) t+asg (w.carry t.castSucc)+16777216 =
      padded (fun i => asg ((w.canonical 9).x i)) t+
      convolution (fun i => (AirModularView.constDigit 512 6 q i : BabyBear)) (fun i => asg (w.quotient i)) t+
      512*asg (w.carry t.succ)+32768 := by
  simp only [accepts,column,eval_add',eval_mul',eval_cst,eval_vr,productTerm_eval,convolutionTerm_eval]
  have ho : eval asg (if h : t.val<6 then vr ((w.canonical 9).x ⟨t.val,h⟩) else cst 0) =
      padded (fun i => asg ((w.canonical 9).x i)) t := by unfold padded; split <;> rfl
  have ha : eval asg (if h : t.val<6 then vr ((w.canonical 8).x ⟨t.val,h⟩) else cst 0) =
      padded (fun i => asg ((w.canonical 8).x i)) t := by unfold padded; split <;> rfl
  simp only [ho,ha]
  constructor <;> intro h <;> linear_combination h



theorem rowSystem_sound {J : Type} (q : Nat) (hq : 0<q) (hcap : q<512^6)
    (w : RowWires J) : RowSound q w := by
  intro asg hs
  simp only [rowSystem,systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨hcan,hqr⟩,hcr⟩,hend⟩,hcols⟩ := hs
  have hcan' (k : Fin 10) : systemAccepts asg (canonicalSystem q (w.canonical k)) := by
    intro t ht
    exact hcan t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩)
  have hw := fun k => canonicalSystem_sound q hq hcap (w.canonical k) asg (hcan' k)
  let a : Fin 4 → Fin 6 → Nat := fun k i => (asg ((w.canonical (lhs k)).x i)).val
  let b : Fin 4 → Fin 6 → Nat := fun k i => (asg ((w.canonical (rhs k)).x i)).val
  let ad : Fin 6 → Nat := fun i => (asg ((w.canonical 8).x i)).val
  let o : Fin 6 → Nat := fun i => (asg ((w.canonical 9).x i)).val
  let k : Fin 6 → Nat := fun i => (asg (w.quotient i)).val
  let qd := AirModularView.constDigit 512 6 q
  let c : Fin 13 → Nat := fun i => (asg (w.carry i)).val
  have hk (i : Fin 6) : k i<512 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^9≤babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hqr i)
  have hc (i : Fin 13) : c i<65536 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^16≤babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hcr i)
  have hqd (i : Fin 6) : qd i<512 := constDigit_lt 512 6 q (by omega) i
  have hcol (t : Fin 12) : products a b t+padded ad t+c t.castSucc+16777216 =
      (padded o t+convolution qd k t)+512*c t.succ+32768 := by
    have hf := (column_correct q w asg t).mp
      (hcols _ (List.mem_map.mpr ⟨t,List.mem_finRange t,rfl⟩))
    have hab := products_bound a b (fun j => (hw (lhs j)).2) (fun j => (hw (rhs j)).2) t
    have hqk := convolution_bound qd k hqd hk t
    have ho : padded o t<512 := by unfold padded; split; exact (hw 9).2 _; omega
    have had : padded ad t<512 := by unfold padded; split; exact (hw 8).2 _; omega
    have hc0 := hc t.castSucc
    have hc1 := hc t.succ
    have hl : products a b t+padded ad t+c t.castSucc+16777216<babyBearP := by norm_num [babyBearP]; omega
    have hr : (padded o t+convolution qd k t)+512*c t.succ+32768<babyBearP := by norm_num [babyBearP]; omega
    have heq : ((products a b t+padded ad t+c t.castSucc+16777216 : Nat) : BabyBear)=
        (((padded o t+convolution qd k t)+512*c t.succ+32768 : Nat) : BabyBear) := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,products_cast,convolution_cast,padded_cast,
        a,b,ad,o,k,qd,c,ZMod.natCast_zmod_val] using hf
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_cast_of_lt hl,ZMod.val_cast_of_lt hr] using hv
  have he : asg (w.carry 0)=32768 ∧ asg (w.carry 12)=32768 := by
    simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_add',eval_vr,eval_cst,add_neg_eq_zero] using hend
  have h0 : c 0=32768 := by dsimp [c]; rw [he.1]; decide +kernel
  have hn : c 12=32768 := by dsimp [c]; rw [he.2]; decide +kernel
  have ht := radix_balance (fun t => products a b t+padded ad t) (fun t => padded o t+convolution qd k t) c hcol
  rw [denote_add,products_denote,padded_denote,denote_add,padded_denote,convolution_denote] at ht
  have hqden : Bignum.denoteNat 512 (List.ofFn qd)=q := by
    rw [show List.ofFn qd=Bignum.digitsLE 512 6 q from AirModularView.constDigits_eq 512 6 q]
    exact Bignum.denoteNat_digitsLE (by omega) 6 q hcap
  change _+c 0+_=_+_*c 12+_ at ht
  rw [h0,hn,hqden] at ht
  have hb : word asg w 8+(∑ j : Fin 4,word asg w (lhs j)*word asg w (rhs j))=
      word asg w 9+q*Bignum.denoteNat 512 (List.ofFn k) := by
    change Bignum.denoteNat 512 (List.ofFn ad)+(∑ j : Fin 4,
      Bignum.denoteNat 512 (List.ofFn (a j))*Bignum.denoteNat 512 (List.ofFn (b j)))=
      Bignum.denoteNat 512 (List.ofFn o)+q*Bignum.denoteNat 512 (List.ofFn k)
    omega
  refine ⟨fun kind => (hw kind).1,?_⟩
  rw [hb,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (hw 9).1).symm
end Minidregg.Compiler.BfvKeyswitchMac
