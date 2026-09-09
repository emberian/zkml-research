/- Source-grounded mathematical semantics of descriptor_ir2.rs eval_decomp.
The limb width is four, including the full-top branch. This is an interpretation
of native field equations and sends, not another circuit or witness generator.
Cryptographic extraction of the sent keys is a separate premise. -/
import Compiler.EmitSerialize
import Mathlib.Data.ZMod.Basic
namespace Minidregg.Compiler.NativeNibbleRange
open Minidregg.Compiler
set_option autoImplicit false
set_option maxHeartbeats 600000

def limbCount (bits : Nat) : Nat := (bits+3)/4
def topBits (bits : Nat) : Nat := bits-(limbCount bits-1)*4
def partialTop (bits i : Nat) : Prop := i=limbCount bits-1 ∧ topBits bits<4
instance (bits i : Nat) : Decidable (partialTop bits i) := inferInstanceAs (Decidable (_ ∧ _))

def weighted (a : Nat → BabyBear) (count base : Nat) : BabyBear :=
  ((List.range count).map fun i => a i*(base : BabyBear)^i).sum

/-- Exactly the unconditional final recomposition and the partial-top local
constraints emitted by the native loop. There is no transition selector here. -/
def Equations (bits : Nat) (v : BabyBear) (a : Nat → BabyBear) : Prop :=
  weighted a (limbCount bits) 16-v=0 ∧
  ∀ i<limbCount bits,partialTop bits i →
    (∀ b<topBits bits,a (limbCount bits+b)*(a (limbCount bits+b)-1)=0) ∧
    weighted (fun b => a (limbCount bits+b)) (topBits bits) 2-a i=0

/-- Each native byte-bus send has multiplicity one. The full top nibble is
sent; only a partial top limb is replaced by local Boolean equations. -/
def sent (bits : Nat) (a : Nat → BabyBear) : List BabyBear :=
  ((List.range (limbCount bits)).filter fun i => ¬partialTop bits i).map a

def Sound : Prop := ∀ bits v a,
  (bits=9 ∨ bits=16) → Equations bits v a →
  (∀ x∈sent bits a,x.val<16) → v.val<2^bits

theorem shape9 (v : BabyBear) (a : Nat → BabyBear) :
    Equations 9 v a ↔
    a 0+16*a 1+256*a 2=v ∧ a 3*(a 3-1)=0 ∧ a 3=a 2 := by
  simp only [Equations,limbCount,topBits,partialTop,weighted]
  norm_num [List.range_succ] at *
  constructor
  · rintro ⟨hr,ht⟩
    have hh := ht 2 (by omega) rfl
    constructor
    · linear_combination hr
    · exact ⟨hh.1,sub_eq_zero.mp hh.2⟩
  · rintro ⟨hr,hb,ht⟩
    constructor
    · linear_combination hr
    · intro i hi hit
      subst i
      exact ⟨hb,sub_eq_zero.mpr ht⟩

theorem shape16 (v : BabyBear) (a : Nat → BabyBear) :
    Equations 16 v a ↔ a 0+16*a 1+256*a 2+4096*a 3=v := by
  norm_num [Equations,limbCount,topBits,partialTop,weighted,List.range_succ]
  constructor <;> intro h <;> linear_combination h

theorem sends9 (a : Nat → BabyBear) : sent 9 a=[a 0,a 1] := by
  norm_num [sent,limbCount,partialTop,topBits,List.range_succ]

theorem sends16 (a : Nat → BabyBear) : sent 16 a=[a 0,a 1,a 2,a 3] := by
  norm_num [sent,limbCount,partialTop,topBits,List.range_succ]

theorem bool_val (b : BabyBear) (hb : b*(b-1)=0) : b.val≤1 := by
  rcases mul_eq_zero.mp hb with h | h
  · simp [h]
  · have : b=1 := sub_eq_zero.mp h
    rw [this]
    decide

theorem cast_value (v : BabyBear) (n : Nat) (hn : n<2013265921)
    (he : (n : BabyBear)=v) : v.val=n := by
  rw [←he,ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hn

theorem range9 (v : BabyBear) (a : Nat → BabyBear) (he : Equations 9 v a)
    (hs : ∀ x∈sent 9 a,x.val<16) : v.val<512 := by
  obtain ⟨hr,hb,ht⟩ := (shape9 v a).mp he
  have h0 := hs (a 0) (by simp [sends9])
  have h1 := hs (a 1) (by simp [sends9])
  have h2 : (a 2).val≤1 := by rw [←ht]; exact bool_val _ hb
  let n := (a 0).val+16*(a 1).val+256*(a 2).val
  have hn : n<512 := by dsimp [n]; omega
  have hc : (n : BabyBear)=v := by
    simpa only [n,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] using hr
  rw [cast_value v n (by omega) hc]
  exact hn

theorem range16 (v : BabyBear) (a : Nat → BabyBear) (he : Equations 16 v a)
    (hs : ∀ x∈sent 16 a,x.val<16) : v.val<65536 := by
  have hr := (shape16 v a).mp he
  have h0 := hs (a 0) (by simp [sends16])
  have h1 := hs (a 1) (by simp [sends16])
  have h2 := hs (a 2) (by simp [sends16])
  have h3 := hs (a 3) (by simp [sends16])
  let n := (a 0).val+16*(a 1).val+256*(a 2).val+4096*(a 3).val
  have hn : n<65536 := by dsimp [n]; omega
  have hc : (n : BabyBear)=v := by
    simpa only [n,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] using hr
  rw [cast_value v n (by omega) hc]
  exact hn

theorem sound : Sound := by
  intro bits v a hbits he hs
  rcases hbits with rfl | rfl
  · exact range9 v a he hs
  · exact range16 v a he hs

/-- Additional widths needed by the compiler-derived matrix/rescale successor.
The native loop is shared; only this finite capacity check is profile-specific. -/
def Supported (bits : Nat) : Prop := bits∈[2,9,11,14,15,16]

def natWeighted (a : Nat → Nat) (count base : Nat) : Nat :=
  ((List.range count).map fun i => a i*base^i).sum

theorem natWeighted_succ (a : Nat → Nat) (n b : Nat) :
    natWeighted a (n+1) b=natWeighted a n b+a n*b^n := by
  simp [natWeighted,List.range_succ]

theorem natWeighted_bound (a : Nat → Nat) (n b : Nat) (hb : 0<b)
    (ha : ∀ i<n,a i<b) : natWeighted a n b<b^n := by
  induction n with
  | zero => simp [natWeighted]
  | succ n ih =>
    have hp := ih (fun i hi => ha i (by omega))
    have hn := ha n (by omega)
    have hpow : 0<b^n := pow_pos hb n
    rw [natWeighted_succ,pow_succ]
    nlinarith

theorem weighted_cast (a : Nat → BabyBear) (n b : Nat) :
    (natWeighted (fun i => (a i).val) n b : BabyBear)=weighted a n b := by
  induction n with
  | zero => simp [natWeighted,weighted]
  | succ n ih =>
    simp only [natWeighted_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      ZMod.natCast_zmod_val,ih]
    simp [weighted,List.range_succ]

theorem geometry (bits : Nat) (h : Supported bits) :
    0<limbCount bits ∧ 0<topBits bits ∧ topBits bits≤4 ∧
    16^(limbCount bits-1)*2^(topBits bits)=2^bits ∧ 2^bits<2013265921 := by
  simp only [Supported,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [limbCount,topBits]

theorem sent_mem (bits : Nat) (a : Nat → BabyBear) (i : Nat)
    (hi : i<limbCount bits) (hf : ¬partialTop bits i) : a i∈sent bits a := by
  apply List.mem_map.mpr
  exact ⟨i,List.mem_filter.mpr ⟨List.mem_range.mpr hi,by simp [hf]⟩,rfl⟩

/-- The same exact decomposition proves every width currently emitted by the
compact MAC and the compact extension/rescale successor, including full top16. -/
theorem supportedSound (bits : Nat) (v : BabyBear) (a : Nat → BabyBear)
    (hw : Supported bits) (he : Equations bits v a)
    (hs : ∀ x∈sent bits a,x.val<16) : v.val<2^bits := by
  obtain ⟨hn,ht,hcap,hpow,hfield⟩ := geometry bits hw
  have hbefore : ∀ i<limbCount bits-1,(a i).val<16 := by
    intro i hi
    exact hs _ (sent_mem bits a i (by omega) (by unfold partialTop; omega))
  have hlast : (a (limbCount bits-1)).val<2^(topBits bits) := by
    by_cases hp : topBits bits<4
    · obtain ⟨hb,hr⟩ := he.2 (limbCount bits-1) (by omega) ⟨rfl,hp⟩
      have hbits : ∀ i<topBits bits,(a (limbCount bits+i)).val<2 := by
        intro i hi
        have := bool_val _ (hb i hi)
        omega
      have hnat := natWeighted_bound (fun i => (a (limbCount bits+i)).val)
        (topBits bits) 2 (by decide) hbits
      have hsmall : 2^(topBits bits)≤16 := by
        have := Nat.pow_le_pow_right (by decide : 1≤(2 : Nat)) hcap
        norm_num at this
        exact this
      have hc : (natWeighted (fun i => (a (limbCount bits+i)).val)
          (topBits bits) 2 : BabyBear)=a (limbCount bits-1) :=
        (weighted_cast _ _ _).trans (sub_eq_zero.mp hr)
      rw [cast_value _ _ (by omega) hc]
      exact hnat
    · have ht4 : topBits bits=4 := by omega
      have hh := hs _ (sent_mem bits a (limbCount bits-1) (by omega)
        (by simp [partialTop,hp]))
      simpa [ht4] using hh
  let n := natWeighted (fun i => (a i).val) (limbCount bits) 16
  have hprefix := natWeighted_bound (fun i => (a i).val) (limbCount bits-1) 16
    (by decide) hbefore
  have hnval : n<2^bits := by
    have hn' : limbCount bits=(limbCount bits-1)+1 := by omega
    dsimp [n]
    rw [hn',natWeighted_succ]
    rw [←hpow]
    have hz : 0<(16 : Nat)^(limbCount bits-1) := by positivity
    nlinarith
  have hc : (n : BabyBear)=v := (weighted_cast a (limbCount bits) 16).trans
    (sub_eq_zero.mp he.1)
  rw [cast_value _ _ (lt_trans hnval hfield) hc]
  exact hnval

def nineWitness (i : Nat) : BabyBear := if i<2 then 15 else 1
def sixteenWitness (_ : Nat) : BabyBear := 15
def missingTopWitness (i : Nat) : BabyBear := if i=3 then 16 else 0

theorem nonzero9 : Equations 9 511 nineWitness ∧
    (∀ x∈sent 9 nineWitness,x.val<16) ∧ (511 : BabyBear).val≠0 := by
  refine ⟨(shape9 _ _).mpr ?_,?_,by decide⟩
  · norm_num [nineWitness]
  · simp only [sends9,List.mem_cons,List.not_mem_nil,or_false]
    intro x hx
    rcases hx with rfl | rfl <;> norm_num [nineWitness] <;> decide

theorem nonzero16 : Equations 16 65535 sixteenWitness ∧
    (∀ x∈sent 16 sixteenWitness,x.val<16) ∧ (65535 : BabyBear).val≠0 := by
  refine ⟨(shape16 _ _).mpr ?_,?_,by decide⟩
  · norm_num [sixteenWitness]
  · simp only [sends16,List.mem_cons,List.not_mem_nil,or_false]
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [sixteenWitness] <;> decide

/-- Omitting the full top-nibble send permits 65536. The three lower sends
and the native recomposition equations still hold. This is the old seam's tooth. -/
theorem omittedFullTopFalsifier : Equations 16 65536 missingTopWitness ∧
    (∀ i<3,(missingTopWitness i).val<16) ∧
    ¬(∀ x∈sent 16 missingTopWitness,x.val<16) := by
  refine ⟨(shape16 _ _).mpr ?_,?_,?_⟩
  · norm_num [missingTopWitness]
  · intro i hi
    have : i≠3 := by omega
    simp [missingTopWitness,this]
  · intro h
    have hh := range16 (65536 : BabyBear) missingTopWitness ((shape16 _ _).mpr (by norm_num [missingTopWitness])) h
    have : ¬(65536 : BabyBear).val<65536 := by decide
    exact this hh

theorem overflow9Refused (a : Nat → BabyBear) :
    ¬(Equations 9 512 a ∧ ∀ x∈sent 9 a,x.val<16) := by
  rintro ⟨he,hs⟩
  have := range9 _ _ he hs
  exact (by decide : ¬(512 : BabyBear).val<512) this

theorem premiseInhabited : ∃ bits v a,Supported bits ∧ Equations bits v a ∧
    (∀ x∈sent bits a,x.val<16) ∧ v.val≠0 :=
  ⟨16,65535,sixteenWitness,by simp [Supported],nonzero16⟩

/-- The last row is not exempt. Removing all equations from a one-row trace
would accept a non-range value; the real all-row relation cannot do so. -/
theorem terminalRowRefused : ¬∃ a : Fin 1 → Nat → BabyBear,
    (∀ r,Equations 9 (512 : BabyBear) (a r)) ∧
    (∀ r x,x∈sent 9 (a r) → x.val<16) := by
  rintro ⟨a,he,hs⟩
  exact overflow9Refused (a 0) ⟨he 0,hs 0⟩

end Minidregg.Compiler.NativeNibbleRange

/-- info: 'Minidregg.Compiler.NativeNibbleRange.shape9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.shape9
/-- info: 'Minidregg.Compiler.NativeNibbleRange.shape16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.shape16
/-- info: 'Minidregg.Compiler.NativeNibbleRange.sends9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.sends9
/-- info: 'Minidregg.Compiler.NativeNibbleRange.sends16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.sends16
/-- info: 'Minidregg.Compiler.NativeNibbleRange.bool_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.bool_val
/-- info: 'Minidregg.Compiler.NativeNibbleRange.cast_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.cast_value
/-- info: 'Minidregg.Compiler.NativeNibbleRange.range9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.range9
/-- info: 'Minidregg.Compiler.NativeNibbleRange.range16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.range16
/-- info: 'Minidregg.Compiler.NativeNibbleRange.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.sound
/-- info: 'Minidregg.Compiler.NativeNibbleRange.natWeighted_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.natWeighted_succ
/-- info: 'Minidregg.Compiler.NativeNibbleRange.natWeighted_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.natWeighted_bound
/-- info: 'Minidregg.Compiler.NativeNibbleRange.weighted_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.weighted_cast
/-- info: 'Minidregg.Compiler.NativeNibbleRange.geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.geometry
/-- info: 'Minidregg.Compiler.NativeNibbleRange.sent_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.sent_mem
/-- info: 'Minidregg.Compiler.NativeNibbleRange.supportedSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.supportedSound
/-- info: 'Minidregg.Compiler.NativeNibbleRange.nonzero9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.nonzero9
/-- info: 'Minidregg.Compiler.NativeNibbleRange.nonzero16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.nonzero16
/-- info: 'Minidregg.Compiler.NativeNibbleRange.omittedFullTopFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.omittedFullTopFalsifier
/-- info: 'Minidregg.Compiler.NativeNibbleRange.overflow9Refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.overflow9Refused
/-- info: 'Minidregg.Compiler.NativeNibbleRange.premiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.premiseInhabited
/-- info: 'Minidregg.Compiler.NativeNibbleRange.terminalRowRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleRange.terminalRowRefused
