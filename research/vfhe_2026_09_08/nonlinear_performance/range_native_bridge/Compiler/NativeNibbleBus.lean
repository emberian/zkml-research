/- Exact multiset boundary for the native nibble bus. The caller flattens every
row/range send into `sends`; receives use natural multiplicities on the actual
sixteen values 0,...,15. This is an extracted-bus theorem, not a proof that the
grouped LogUp argument supplies exact conservation. Field conservation requires
an explicit no-wrap premise; field multiplicities are not silently integers. -/
import Compiler.NativeNibbleRange
namespace Minidregg.Compiler.NativeNibbleBus
open Minidregg.Compiler
set_option autoImplicit false
set_option maxHeartbeats 600000

def receives (multiplicity : Nat → Nat) : List BabyBear :=
  (List.range 16).flatMap fun i => List.replicate (multiplicity i) (i : BabyBear)

def ExactNat (sends : List BabyBear) (multiplicity : Nat → Nat) : Prop :=
  ∀ x, sends.count x = (receives multiplicity).count x

def ExactField (sends : List BabyBear) (multiplicity : Nat → Nat) : Prop :=
  ∀ x, (sends.count x : BabyBear) = ((receives multiplicity).count x : BabyBear)

/-- Only the number of sends of a particular key needs a no-wrap bound. The
total number of receives need not be bounded for the support conclusion. -/
def NoSendWrap (sends : List BabyBear) : Prop :=
  ∀ x ∈ sends, sends.count x < 2013265921

def Sound : Prop := ∀ sends multiplicity, ExactNat sends multiplicity →
  ∀ x ∈ sends, x.val < 16

def FieldSound : Prop := ∀ sends multiplicity, ExactField sends multiplicity →
  NoSendWrap sends → ∀ x ∈ sends, x.val < 16

theorem receive_range (multiplicity : Nat → Nat) (x : BabyBear)
    (hx : x ∈ receives multiplicity) : x.val < 16 := by
  obtain ⟨i,hi,hx⟩ := List.mem_flatMap.mp hx
  have hi' : i < 16 := List.mem_range.mp hi
  have hx' : x = (i : BabyBear) := (List.mem_replicate.mp hx).2
  rw [hx', ZMod.val_natCast]
  change i % 2013265921 < 16
  rw [Nat.mod_eq_of_lt (by omega : i < 2013265921)]
  exact hi'

theorem sound : Sound := by
  intro sends multiplicity he x hx
  apply receive_range multiplicity x
  apply List.count_pos_iff.mp
  rw [←he x]
  exact List.count_pos_iff.mpr hx

theorem field_sound : FieldSound := by
  intro sends multiplicity he hn x hx
  by_contra hout
  have hnot : x ∉ receives multiplicity := fun hm => hout (receive_range _ _ hm)
  have hz := List.count_eq_zero.mpr hnot
  have heq := congrArg (fun y : BabyBear => y.val) (he x)
  rw [hz] at heq
  have heq' : sends.count x % 2013265921 = 0 := by
    simpa only [ZMod.val_natCast, Nat.zero_mod] using heq
  have hcount : sends.count x = 0 := by
    rwa [Nat.mod_eq_of_lt (hn x hx)] at heq'
  exact List.count_eq_zero.mp hcount hx

theorem noWrap_of_length (sends : List BabyBear) (h : sends.length < 2013265921) :
    NoSendWrap sends := by
  intro x hx
  exact lt_of_le_of_lt (List.count_le_length) h

/-- A caller identifies its row sends inside the global multiset. Individual
lookup membership is a conclusion of conservation, not an input premise. -/
theorem row_range (sends : List BabyBear) (multiplicity : Nat → Nat)
    (bits : Nat) (v : BabyBear) (a : Nat → BabyBear)
    (hb : bits = 9 ∨ bits = 16) (he : NativeNibbleRange.Equations bits v a)
    (hc : ExactNat sends multiplicity)
    (included : ∀ x ∈ NativeNibbleRange.sent bits a, x ∈ sends) : v.val < 2^bits := by
  exact NativeNibbleRange.sound bits v a hb he
    (fun x hx => sound sends multiplicity hc x (included x hx))

theorem field_row_range (sends : List BabyBear) (multiplicity : Nat → Nat)
    (bits : Nat) (v : BabyBear) (a : Nat → BabyBear)
    (hb : bits = 9 ∨ bits = 16) (he : NativeNibbleRange.Equations bits v a)
    (hc : ExactField sends multiplicity) (hn : NoSendWrap sends)
    (included : ∀ x ∈ NativeNibbleRange.sent bits a, x ∈ sends) : v.val < 2^bits := by
  exact NativeNibbleRange.sound bits v a hb he
    (fun x hx => field_sound sends multiplicity hc hn x (included x hx))

def good (i : Nat) : BabyBear := if i=0 then 3 else if i=1 then 5 else 0
def goodMultiplicity (i : Nat) : Nat := if i=0 then 2 else if i=3 ∨ i=5 then 1 else 0

def NonzeroPremise : Prop :=
  NativeNibbleRange.Equations 16 83 good ∧
  ExactNat (NativeNibbleRange.sent 16 good) goodMultiplicity ∧
  (83 : BabyBear) ≠ 0

theorem nonzeroPremise : NonzeroPremise := by
  refine ⟨?_,?_,by decide⟩
  · rw [NativeNibbleRange.shape16]
    norm_num [good]
  · intro x
    simp [NativeNibbleRange.sends16,good,receives,goodMultiplicity,List.range_succ,
      List.count_cons]
    omega

theorem premiseInhabited : ∃ sends multiplicity, ExactNat sends multiplicity ∧
    ∃ x ∈ sends, x ≠ 0 := by
  refine ⟨NativeNibbleRange.sent 16 good,goodMultiplicity,nonzeroPremise.2.1,3,?_,by decide⟩
  simp [NativeNibbleRange.sends16,good]

theorem exactField_of_exactNat (sends : List BabyBear) (multiplicity : Nat → Nat)
    (h : ExactNat sends multiplicity) : ExactField sends multiplicity := by
  intro x
  exact congrArg (fun n : Nat => (n : BabyBear)) (h x)

theorem fieldPremiseInhabited : ∃ sends multiplicity,
    ExactField sends multiplicity ∧ NoSendWrap sends ∧ ∃ x ∈ sends, x ≠ 0 := by
  refine ⟨NativeNibbleRange.sent 16 good,goodMultiplicity,
    exactField_of_exactNat _ _ nonzeroPremise.2.1,?_,3,?_,by decide⟩
  · apply noWrap_of_length
    rw [NativeNibbleRange.sends16]
    decide
  · simp [NativeNibbleRange.sends16,good]

def bad (i : Nat) : BabyBear := if i=0 then 3 else if i=3 then 16 else 0
def omittedMultiplicity (i : Nat) : Nat := if i=0 then 2 else if i=3 then 1 else 0

/-- If the full top limb were omitted from the sends, the remaining multiset
could balance while recomposition exceeds the requested 16-bit range. -/
def OmittedTopFalsifier : Prop :=
  NativeNibbleRange.Equations 16 65539 bad ∧
  ExactNat [bad 0,bad 1,bad 2] omittedMultiplicity ∧
  ¬(65539 : BabyBear).val < 65536 ∧
  ¬ExactNat (NativeNibbleRange.sent 16 bad) omittedMultiplicity

theorem omittedTopFalsifier : OmittedTopFalsifier := by
  refine ⟨?_,?_,by decide,?_⟩
  · rw [NativeNibbleRange.shape16]
    norm_num [bad]
  · intro x
    simp [bad,receives,omittedMultiplicity,List.range_succ,List.count_cons]
    omega
  · intro hc
    have hh := sound _ _ hc 16 (by simp [NativeNibbleRange.sends16,bad])
    have hn : ¬(16 : BabyBear).val < 16 := by decide
    exact hn hh

/-- Field equality alone cannot rule out a positive number of invalid sends
equal to the characteristic. This exhibits the exact missing arithmetic fact
without allocating a list of two billion entries. -/
def FieldWrapFalsifier : Prop :=
  0 < (2013265921 : Nat) ∧ (2013265921 : BabyBear) = 0

theorem fieldWrapFalsifier : FieldWrapFalsifier := by
  constructor <;> decide

/-- A complete field-conservation premise is inhabited by invalid sends when
the per-key count wraps. `replicate` remains symbolic in this proof. -/
def WrappedBusFalsifier : Prop :=
  ExactField (List.replicate 2013265921 (16 : BabyBear)) (fun _ => 0) ∧
  (16 : BabyBear) ∈ List.replicate 2013265921 (16 : BabyBear) ∧
  ¬(16 : BabyBear).val < 16

theorem wrapped_conserves (n : Nat) (hn : (n : BabyBear) = 0) :
    ExactField (List.replicate n (16 : BabyBear)) (fun _ => 0) := by
  intro x
  have hr : receives (fun _ => 0) = [] := by simp [receives]
  rw [hr, List.count_nil]
  rw [List.count_replicate]
  split
  · exact hn
  · rfl

theorem wrappedBusFalsifier : WrappedBusFalsifier := by
  refine ⟨wrapped_conserves 2013265921 fieldWrapFalsifier.2,?_,by decide⟩
  exact List.mem_replicate.mpr ⟨by decide,rfl⟩

end Minidregg.Compiler.NativeNibbleBus

/-- info: 'Minidregg.Compiler.NativeNibbleBus.receive_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.receive_range

/-- info: 'Minidregg.Compiler.NativeNibbleBus.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.sound

/-- info: 'Minidregg.Compiler.NativeNibbleBus.field_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.field_sound

/-- info: 'Minidregg.Compiler.NativeNibbleBus.noWrap_of_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.noWrap_of_length

/-- info: 'Minidregg.Compiler.NativeNibbleBus.row_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.row_range

/-- info: 'Minidregg.Compiler.NativeNibbleBus.field_row_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.field_row_range

/-- info: 'Minidregg.Compiler.NativeNibbleBus.nonzeroPremise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.nonzeroPremise

/-- info: 'Minidregg.Compiler.NativeNibbleBus.premiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.premiseInhabited

/-- info: 'Minidregg.Compiler.NativeNibbleBus.omittedTopFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.omittedTopFalsifier

/-- info: 'Minidregg.Compiler.NativeNibbleBus.fieldWrapFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.fieldWrapFalsifier

/-- info: 'Minidregg.Compiler.NativeNibbleBus.wrapped_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.wrapped_conserves

/-- info: 'Minidregg.Compiler.NativeNibbleBus.wrappedBusFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.wrappedBusFalsifier

/-- info: 'Minidregg.Compiler.NativeNibbleBus.exactField_of_exactNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.exactField_of_exactNat

/-- info: 'Minidregg.Compiler.NativeNibbleBus.fieldPremiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeNibbleBus.fieldPremiseInhabited
