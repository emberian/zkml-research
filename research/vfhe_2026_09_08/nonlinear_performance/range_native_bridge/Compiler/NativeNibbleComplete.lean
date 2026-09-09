/- Every bounded value admits the exact native auxiliary relation. This makes
the lowering an equivalence, not an uninhabited strengthening of source ranges. -/
import Compiler.NativeNibbleRange
namespace Minidregg.Compiler.NativeNibbleComplete
open Minidregg.Compiler Minidregg.Compiler.NativeNibbleRange
set_option autoImplicit false
set_option maxHeartbeats 600000

def Complete : Prop := ∀ bits v,Supported bits → v.val<2^bits →
  ∃ a,Equations bits v a ∧ ∀ x∈sent bits a,x.val<16

theorem natWeighted_head (a : Nat → Nat) (n b : Nat) :
    natWeighted a (n+1) b=a 0+b*natWeighted (fun i => a (i+1)) n b := by
  simp only [natWeighted,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.sum_cons,pow_zero,mul_one]
  rw [←List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  dsimp
  rw [pow_succ]
  ring

theorem digitsExist (n b v : Nat) (hb : 0<b) (hv : v<b^n) :
    ∃ a : Nat → Nat,(∀ i<n,a i<b) ∧ natWeighted a n b=v := by
  induction n generalizing v with
  | zero =>
    have : v=0 := by simpa using hv
    subst v
    exact ⟨fun _ => 0,by simp,by simp [natWeighted]⟩
  | succ n ih =>
    have hdiv : v/b<b^n := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa [pow_succ,Nat.mul_comm] using hv
    obtain ⟨a,ha,he⟩ := ih (v/b) hdiv
    let d := fun i => if i=0 then v%b else a (i-1)
    refine ⟨d,?_,?_⟩
    · intro i hi
      by_cases hz : i=0
      · simp [d,hz,Nat.mod_lt v hb]
      · simpa [d,hz] using ha (i-1) (by omega)
    · rw [natWeighted_head]
      have hd : (fun i => d (i+1))=a := by funext i; simp [d]
      rw [hd,he]
      simpa [d] using Nat.mod_add_div v b

theorem weighted_congr (a c : Nat → BabyBear) (n b : Nat)
    (h : ∀ i<n,a i=c i) : weighted a n b=weighted c n b := by
  unfold weighted
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem cast_weighted_nat (a : Nat → Nat) (n b : Nat) :
    weighted (fun i => (a i : BabyBear)) n b=(natWeighted a n b : BabyBear) := by
  induction n with
  | zero => simp [weighted,natWeighted]
  | succ n ih =>
    rw [natWeighted_succ]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    simpa [weighted,List.range_succ] using congrArg
      (fun x => x+(a n : BabyBear)*(b : BabyBear)^n) ih

theorem complete : Complete := by
  intro bits v hw hv
  obtain ⟨hn,ht,ht4,hpow,hfield⟩ := geometry bits hw
  have htopcap : 2^(topBits bits)≤16 := by
    simpa using Nat.pow_le_pow_right (by decide : 1≤(2 : Nat)) ht4
  have hfull : v.val<16^(limbCount bits) := by
    have hpred : limbCount bits=(limbCount bits-1)+1 := by omega
    rw [hpred,pow_succ]
    rw [←hpow] at hv
    exact lt_of_lt_of_le hv (Nat.mul_le_mul_left _ htopcap)
  obtain ⟨d,hd,hde⟩ := digitsExist (limbCount bits) 16 v.val (by decide) hfull
  have hlast : d (limbCount bits-1)<2^(topBits bits) := by
    have hpred : limbCount bits=(limbCount bits-1)+1 := by omega
    have he := hde
    rw [hpred,natWeighted_succ] at he
    rw [←hpow] at hv
    have hpos : 0<(16 : Nat)^(limbCount bits-1) := by positivity
    nlinarith
  obtain ⟨bd,hbd,hbe⟩ := digitsExist (topBits bits) 2 (d (limbCount bits-1)) (by decide) hlast
  let a : Nat → BabyBear := fun i =>
    if i<limbCount bits then (d i : BabyBear) else (bd (i-limbCount bits) : BabyBear)
  have ha (i : Nat) (hi : i<limbCount bits) : a i=(d i : BabyBear) := by simp [a,hi]
  have hab (i : Nat) : a (limbCount bits+i)=(bd i : BabyBear) := by simp [a]
  refine ⟨a,⟨?_,?_⟩,?_⟩
  · apply sub_eq_zero.mpr
    rw [weighted_congr a (fun i => (d i : BabyBear)) _ _ ha,
      cast_weighted_nat,hde,ZMod.natCast_zmod_val]
  · intro i hi hp
    obtain ⟨rfl,hp⟩ := hp
    refine ⟨?_,?_⟩
    · intro b hb
      rw [hab]
      have hb01 : bd b=0 ∨ bd b=1 := by have := hbd b hb; omega
      rcases hb01 with h | h <;> simp [h]
    · apply sub_eq_zero.mpr
      have hab' : (fun b => a (limbCount bits+b))=(fun b => (bd b : BabyBear)) := by
        funext b; exact hab b
      rw [hab',cast_weighted_nat,hbe,ha _ (by omega)]
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hil := List.mem_range.mp (List.mem_filter.mp hi).1
    rw [ha i hil,ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (hd i hil)

theorem native_iff_range (bits : Nat) (v : BabyBear) (hw : Supported bits) :
    (∃ a,Equations bits v a ∧ ∀ x∈sent bits a,x.val<16) ↔ v.val<2^bits := by
  constructor
  · rintro ⟨a,he,hs⟩
    exact supportedSound bits v a hw he hs
  · exact complete bits v hw

end Minidregg.Compiler.NativeNibbleComplete

/-- info: 'Minidregg.Compiler.NativeNibbleComplete.natWeighted_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleComplete.natWeighted_head
/-- info: 'Minidregg.Compiler.NativeNibbleComplete.digitsExist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleComplete.digitsExist
/-- info: 'Minidregg.Compiler.NativeNibbleComplete.weighted_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleComplete.weighted_congr
/-- info: 'Minidregg.Compiler.NativeNibbleComplete.cast_weighted_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleComplete.cast_weighted_nat
/-- info: 'Minidregg.Compiler.NativeNibbleComplete.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleComplete.complete
/-- info: 'Minidregg.Compiler.NativeNibbleComplete.native_iff_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleComplete.native_iff_range
