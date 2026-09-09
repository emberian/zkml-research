/- Selected first-external-product source: two sparse shifts, checked prefix,
anchored output, and explicit 8-bit torus scaling. -/
import Compiler.TfheSparseWrap
import Compiler.AirAssertionShare
namespace Minidregg.Compiler.TfheSparseRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.TfheSparseWrap Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
local instance : Hashable BabyBear where hash x := hash x.val

def nVars : ℕ := 279
def w (g : Fin 8) (i : Fin 4) : Fin nVars := ⟨8+4*g.val+i.val,by dsimp [nVars]; omega⟩
def wb (g : Fin 8) (i : Fin 4) (j : Fin 6) : Fin nVars := ⟨46+24*g.val+6*i.val+j.val,by dsimp [nVars]; omega⟩
def flag (i : Fin 5) : Fin nVars := ⟨3+i.val,by dsimp [nVars]; omega⟩
def carry (k : Fin 2) (i : Fin 5) : Fin nVars := ⟨238+20*k.val+i.val,by dsimp [nVars]; omega⟩
def carryBit (k : Fin 2) (i : Fin 5) (j : Fin 3) : Fin nVars := ⟨243+20*k.val+3*i.val+j.val,by dsimp [nVars]; omega⟩
def zeroWire : Fin nVars := ⟨278,by decide⟩
def raw (i : Fin 6) : Fin nVars := ⟨40+i.val,by dsimp [nVars]; omega⟩
def rawBit (i : Fin 6) (j : Fin 6) : Fin nVars :=
  let t := 6*i.val+j.val
  if h : 8≤t ∧ t<32 then ⟨46+72+(t-8),by dsimp [nVars]; omega⟩ else zeroWire

def leftTerm (k : Fin 2) (i : Fin 4) : Term (AirSig BabyBear (Fin nVars)) :=
  if k.val=0 then add' (vr (w 5 i)) (mul' (vr (flag 3)) (vr (w 0 i)))
  else add' (add' (vr (w 4 i)) (mul' (mul' (cst 2) (vr (flag 1))) (vr (w 1 i))))
    (mul' (mul' (cst 2) (vr (flag 2))) (vr (w 2 i)))
def rightTerm (k : Fin 2) (i : Fin 4) : Term (AirSig BabyBear (Fin nVars)) :=
  if k.val=0 then add' (vr (w 6 i)) (mul' (vr (flag 4)) (vr (w 0 i)))
  else add' (add' (vr (w 3 i)) (vr (w 1 i))) (vr (w 2 i))
def anchorSystem : ConstraintSystem BabyBear (Fin nVars) :=
  (List.finRange 4).flatMap fun i => [mul' (vr (flag 0)) (vr (w 5 i)),
    mul' (vr (flag 0)) (add' (vr (w 3 i)) (mul' (cst (-1)) (vr (w 7 i))))]
def system : ConstraintSystem BabyBear (Fin nVars) :=
  (List.finRange 8).flatMap (fun g => AirBignum.limbRangeSystem (w g) (wb g)) ++
  (List.finRange 5).map (fun i => boolGadget (flag i)) ++
  (List.finRange 2).flatMap (fun k => wrapSystem (leftTerm k) (rightTerm k) (carry k) (carryBit k)) ++
  anchorSystem ++ [vr zeroWire] ++ AirBignum.limbRangeSystem raw rawBit

def value (asg : Fin nVars → BabyBear) (g : Fin 8) : ℕ :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (w g))
def rawValue (asg : Fin nVars → BabyBear) : ℕ :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg raw)
def fval (asg : Fin nVars → BabyBear) (i : Fin 5) : ℕ := (asg (flag i)).val

def RowMeaning (asg : Fin nVars → BabyBear) : Prop :=
  (∀ g,value asg g<modulus) ∧ (∀ i,fval asg i=0 ∨ fval asg i=1) ∧
  ((value asg 5 : SmallRing)+fval asg 3*value asg 0=value asg 6+fval asg 4*value asg 0) ∧
  ((value asg 4 : SmallRing)+2*fval asg 1*value asg 1+2*fval asg 2*value asg 2=
    value asg 3+value asg 1+value asg 2) ∧
  (fval asg 0=1 → value asg 5=0 ∧ value asg 3=value asg 7) ∧
  rawValue asg=256*value asg 3

def RowSound : Prop := ∀ asg : Fin nVars → BabyBear,systemAccepts asg system → RowMeaning asg

def emittedSystem : ConstraintSystem BabyBear (Fin nVars) := AirAssertionShare.optimize system

theorem range_value {J : Type} {k : ℕ} (hk : 2^k≤babyBearP) (asg : J → BabyBear)
    (xi : J) (bits : Fin k → J) (h : systemAccepts asg (rangeGadget xi bits)) :
    (asg xi).val=∑ i : Fin k,(asg (bits i)).val*2^i.val := by
  obtain ⟨hb,hs⟩ := (rangeGadget_correct asg xi bits).mp h
  have hbit (i : Fin k) : (asg (bits i)).val≤1 := by
    rcases hb i with h0|h1
    · rw [h0]; simp
    · rw [h1]; decide +kernel
  have hbound := boolDigit_sum_lt (fun i => (asg (bits i)).val) hbit
  have hcast : asg xi=((∑ i : Fin k,(asg (bits i)).val*2^i.val : ℕ) : BabyBear) := by
    simpa using hs
  have hv := congrArg ZMod.val hcast
  simpa only [ZMod.val_cast_of_lt (lt_of_lt_of_le hbound hk)] using hv

theorem row_sound : RowSound := by
  intro asg hs
  simp only [system,systemAccepts_append] at hs
  obtain ⟨⟨⟨⟨⟨hwords,hflags⟩,hwrap⟩,hanchor⟩,hzero⟩,hraw⟩ := hs
  have hword (g : Fin 8) : systemAccepts asg (AirBignum.limbRangeSystem (w g) (wb g)) := by
    intro t ht
    exact hwords t (List.mem_flatMap.mpr ⟨g,List.mem_finRange g,ht⟩)
  have hd (g : Fin 8) (i : Fin 4) : (asg (w g i)).val<64 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^6≤babyBearP) asg _ _
    ((AirBignum.limbRangeSystem_correct asg _ _).mp (hword g) i)
  have hval (g : Fin 8) : value asg g<modulus := by
    have hh := Bignum.denoteNat_lt_pow (by decide : 0<64) (AirBignum.limbVals asg (w g))
    have hr : Bignum.Ranged 64 (AirBignum.limbVals asg (w g)) := by
      intro d hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      exact hd g i
    simpa [AirBignum.limbVals,value,modulus] using hh hr
  have hf (i : Fin 5) : fval asg i=0 ∨ fval asg i=1 := by
    have hh := (boolGadget_correct asg (flag i)).mp
      (hflags _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    rcases hh with h0|h1
    · left; simp [fval,h0]
    · right; dsimp [fval]; rw [h1]; decide +kernel
  have hfb (i : Fin 5) : fval asg i≤1 := by rcases hf i with h|h <;> omega
  have hw (k : Fin 2) : systemAccepts asg (wrapSystem (leftTerm k) (rightTerm k) (carry k) (carryBit k)) := by
    intro t ht
    exact hwrap t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩)
  let d : Fin 8 → Fin 4 → ℕ := fun g i => (asg (w g i)).val
  have hp := wrap_sound (Fin nVars) asg (leftTerm 0) (rightTerm 0) (carry 0) (carryBit 0)
    (fun i => d 5 i+fval asg 3*d 0 i) (fun i => d 6 i+fval asg 4*d 0 i)
    (by intro i; simp [leftTerm,rightTerm,d,fval,eval_add',eval_mul',eval_vr])
    (by intro i; have := hd 5 i; have := hd 6 i; have := hd 0 i; have := hfb 3; have := hfb 4; constructor <;> nlinarith) (hw 0)
  rw [denote_linear,denote_linear] at hp
  have hr := wrap_sound (Fin nVars) asg (leftTerm 1) (rightTerm 1) (carry 1) (carryBit 1)
    (fun i => (d 4 i+2*fval asg 1*d 1 i)+2*fval asg 2*d 2 i) (fun i => d 3 i+d 1 i+d 2 i)
    (by intro i; simp [leftTerm,rightTerm,d,fval,eval_add',eval_mul',eval_vr,eval_cst])
    (by intro i; have := hd 4 i; have := hd 3 i; have := hd 1 i; have := hd 2 i; have := hfb 1; have := hfb 2; constructor <;> nlinarith) (hw 1)
  rw [denote_linear,denote_linear,BfvQueryMul.denote_add,BfvQueryMul.denote_add] at hr
  have haz : fval asg 0=1 → value asg 5=0 ∧ value asg 3=value asg 7 := by
    intro hone
    have hone' : asg (flag 0)=1 := by
      have hh := congrArg (fun n : ℕ => (n : BabyBear)) hone
      simpa [fval] using hh
    have hrows (i : Fin 4) : asg (w 5 i)=0 ∧ asg (w 3 i)=asg (w 7 i) := by
      have hh : systemAccepts asg [mul' (vr (flag 0)) (vr (w 5 i)),
          mul' (vr (flag 0)) (add' (vr (w 3 i)) (mul' (cst (-1)) (vr (w 7 i))))] := by
        intro t ht
        exact hanchor t (List.mem_flatMap.mpr ⟨i,List.mem_finRange i,ht⟩)
      simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_mul',eval_vr,eval_add',eval_cst,
        hone',one_mul,neg_one_mul,add_neg_eq_zero] using hh
    constructor
    · simp [value,AirBignum.limbVals,fun i => (hrows i).1]
    · simp only [value,AirBignum.limbVals,fun i => (hrows i).2]
  have hz : asg zeroWire=0 := by
    simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_vr] using hzero
  have hrawsum (i : Fin 6) := range_value (by norm_num [babyBearP] : 2^6≤babyBearP) asg (raw i) (rawBit i)
    ((AirBignum.limbRangeSystem_correct asg _ _).mp hraw i)
  have hysum (i : Fin 4) := range_value (by norm_num [babyBearP] : 2^6≤babyBearP) asg (w 3 i) (wb 3 i)
    ((AirBignum.limbRangeSystem_correct asg _ _).mp (hword 3) i)
  have hscale : rawValue asg=256*value asg 3 := by
    simp only [rawValue,value,AirBignum.limbVals,List.ofFn_succ,Bignum.denoteNat_cons,hrawsum,hysum]
    norm_num [Fin.sum_univ_succ,rawBit,wb,hz]
    ring
  refine ⟨hval,hf,?_,?_,haz,hscale⟩
  · simpa [value,AirBignum.limbVals,d] using hp
  · simpa [value,AirBignum.limbVals,d] using hr

theorem emitted_sound (asg : Fin nVars → BabyBear) (h : systemAccepts asg emittedSystem) : RowMeaning asg :=
  row_sound asg ((AirAssertionShare.optimize_preserves asg system).mp h)
end Minidregg.Compiler.TfheSparseRow

/-- info: 'Minidregg.Compiler.TfheSparseRow.range_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseRow.range_value

/-- info: 'Minidregg.Compiler.TfheSparseRow.row_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseRow.row_sound

/-- info: 'Minidregg.Compiler.TfheSparseRow.emitted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseRow.emitted_sound
