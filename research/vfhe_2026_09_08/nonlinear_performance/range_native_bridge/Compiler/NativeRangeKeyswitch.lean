/- The actual nibble lowering, global byte-bus support, and the existing
compiler-derived compact MAC/Infer theorem. Source arithmetic includes every row.
This module does not turn a verifier Boolean into either local equations or
global multiset extraction: those cryptographic/refinement obligations stay typed. -/
import Compiler.NativeNibbleBus
import Compiler.NativeNibbleComplete
import Compiler.RangeKeyswitchLookup
import Compiler.RangeKeyswitchInfer
namespace Minidregg.Compiler.NativeRangeKeyswitch
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.RangeKeyswitchRow
open Minidregg.Compiler.BfvInferComposition
open Minidregg.Compiler.BfvInferLinear (primes)
open Minidregg.Compiler.BfvSquareComposition (KernelCiphertext)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000

abbrev Aux := RangeSpec → Nat → BabyBear
def Local (a : Idx → BabyBear) (aux : Aux) : Prop :=
  ∀ r∈ranges,NativeNibbleRange.Equations r.bits (a r.wire) (aux r)
def rowSends (aux : Aux) : List BabyBear :=
  ranges.flatMap fun r => NativeNibbleRange.sent r.bits (aux r)
def allSends {n : Nat} (aux : Fin n → Aux) : List BabyBear :=
  (List.finRange n).flatMap fun row => rowSends (aux row)
def NativeRanges (a : Idx → BabyBear) : Prop :=
  ∃ aux,Local a aux ∧ ∀ x∈rowSends aux,x.val<16

def Checked (l : Fin 4) (operands : Operands) (out : Fin 2 → Nat) : Prop :=
  ∃ a : Idx → BabyBear,systemAccepts a (system (primes l)) ∧
    NativeRanges a ∧ Bound wires a operands out

def AllRowsSound : Prop := ∀ n l (trace : Fin n → Idx → BabyBear) aux multiplicity,
  (∀ row,systemAccepts (trace row) (system (primes l))) →
  (∀ row,Local (trace row) (aux row)) →
  NativeNibbleBus.ExactField (allSends aux) multiplicity →
  NativeNibbleBus.NoSendWrap (allSends aux) →
  ∀ row h,value (trace row) (BfvKeyswitchCore.oIndex h)=
    (value (trace row) (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
      value (trace row) (BfvKeyswitchCore.dIndex k)*
      value (trace row) (BfvKeyswitchCore.kIndex h k))%primes l

theorem range_widths (r : RangeSpec) (hr : r∈ranges) : r.bits=9 ∨ r.bits=16 := by
  have hm : r∈allRanges := by simpa [ranges] using hr
  have hf {n : Nat} (bits : Nat) (f : Fin n → Idx) (h : r∈rangeFamily bits f) :
      r.bits=bits := by
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    exact congrArg RangeSpec.bits he.symm
  rcases List.mem_append.mp hm with h | h
  · obtain ⟨g,hg,h⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (hf 9 _ h)
      · exact Or.inl (hf 9 _ h)
    · exact Or.inl (hf 9 _ h)
  · obtain ⟨g,hg,h⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (hf 9 _ h)
    · exact Or.inr (hf 16 _ h)

theorem range_supported (r : RangeSpec) (hr : r∈ranges) :
    NativeNibbleRange.Supported r.bits := by
  rcases range_widths r hr with h | h <;> simp [NativeNibbleRange.Supported,h]

theorem local_ranges (a : Idx → BabyBear) (aux : Aux) (he : Local a aux)
    (hs : ∀ x∈rowSends aux,x.val<16) : RangeHolds a := by
  intro r hr
  apply NativeNibbleRange.supportedSound r.bits (a r.wire) (aux r)
    (range_supported r hr) (he r hr)
  intro x hx
  exact hs x (List.mem_flatMap.mpr ⟨r,hr,hx⟩)

/-- Completeness is inherited for arbitrary accepted source values: introducing
the native auxiliary relation cannot empty an already inhabited source premise. -/
theorem nativeRanges_iff (a : Idx → BabyBear) : NativeRanges a ↔ RangeHolds a := by
  constructor
  · rintro ⟨aux,he,hs⟩
    exact local_ranges a aux he hs
  · intro hr
    classical
    have hex (r : RangeSpec) (hm : r∈ranges) :=
      NativeNibbleComplete.complete r.bits (a r.wire) (range_supported r hm) (hr r hm)
    let aux : Aux := fun r => if h : r∈ranges then Classical.choose (hex r h) else fun _ => 0
    have ha (r : RangeSpec) (hm : r∈ranges) :
        NativeNibbleRange.Equations r.bits (a r.wire) (aux r) ∧
        ∀ x∈NativeNibbleRange.sent r.bits (aux r),x.val<16 := by
      simpa only [aux,dif_pos hm] using Classical.choose_spec (hex r hm)
    refine ⟨aux,fun r hm => (ha r hm).1,?_⟩
    intro x hx
    obtain ⟨r,hr,hx⟩ := List.mem_flatMap.mp hx
    exact (ha r hr).2 x hx

theorem checked_iff (l : Fin 4) (operands : Operands) (out : Fin 2 → Nat) :
    Checked l operands out ↔ RangeKeyswitchInfer.Checked l operands out := by
  simp only [Checked,RangeKeyswitchInfer.Checked,nativeRanges_iff]

theorem rowSends_length (aux : Aux) : (rowSends aux).length=524 := by
  simp only [rowSends,List.length_flatMap,NativeNibbleRange.sent,List.length_map]
  decide

theorem allSends_length {n : Nat} (aux : Fin n → Aux) :
    (allSends aux).length=n*524 := by
  simp [allSends,List.length_flatMap,rowSends_length]

theorem noWrap_of_domain {n : Nat} (aux : Fin n → Aux) (hn : n≤131072) :
    NativeNibbleBus.NoSendWrap (allSends aux) := by
  apply NativeNibbleBus.noWrap_of_length
  rw [allSends_length]
  omega

/-- The semantic range-table statement formerly assumed by the MAC bridge is
now obtained from native local equations and bus support. Its table definition
remains a caller-supplied faithful semantic table, distinct from LogUp extraction. -/
theorem semanticLookups (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (ht : RangeKeyswitchLookup.FaithfulRanges tf) (a : Idx → BabyBear)
    (hn : NativeRanges a) : RangeKeyswitchLookup.LookupChecked tf a := by
  intro r hr
  apply (IR2RangeLookupBridge.lookup_iff_val_lt r.bits tf (ht r hr)
    (RangeKeyswitchLookup.extend a) r.wire.val).mpr
  have hh := (nativeRanges_iff a).mp hn r hr
  simpa [RangeKeyswitchLookup.extend,r.wire.isLt] using hh

theorem allRowsSound : AllRowsSound := by
  intro n l trace aux multiplicity hg he hb hn row
  apply (actualRowSound l (trace row) (hg row) ?_).2
  apply local_ranges (trace row) (aux row) (he row)
  intro x hx
  apply NativeNibbleBus.field_sound (allSends aux) multiplicity hb hn x
  exact List.mem_flatMap.mpr ⟨row,List.mem_finRange row,hx⟩

/-- The actual complete-class domain size gives a concrete no-wrap sufficient
condition without assuming receive multiplicities themselves are bounded. -/
theorem allRowsSound_of_length (n : Nat) (l : Fin 4)
    (trace : Fin n → Idx → BabyBear) (aux : Fin n → Aux) (multiplicity : Nat → Nat)
    (hg : ∀ row,systemAccepts (trace row) (system (primes l)))
    (he : ∀ row,Local (trace row) (aux row))
    (hb : NativeNibbleBus.ExactField (allSends aux) multiplicity)
    (hlen : (allSends aux).length<2013265921) :
    ∀ row h,value (trace row) (BfvKeyswitchCore.oIndex h)=
      (value (trace row) (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
        value (trace row) (BfvKeyswitchCore.dIndex k)*
        value (trace row) (BfvKeyswitchCore.kIndex h k))%primes l :=
  allRowsSound n l trace aux multiplicity hg he hb (NativeNibbleBus.noWrap_of_length _ hlen)

theorem inferSound (op : BfvInferContract.PublicTransforms) (key : EvaluationKey)
    (model : Ciphertext) (query : Plaintext) (kernel : KernelCiphertext)
    (trace : Nat → Ciphertext)
    (hi : ∀ l j,Checked l (initialOperands model query l j) (fun h => trace 0 h l j))
    (hr : ∀ s : Fin 10,∀ l j,Checked l (rotationOperands op.base key (trace s.val) s l j)
      (fun h => trace (s.val+1) h l j))
    (hrt : BfvSquareComposition.BaseRoundTrip (BfvInferContract.squareTransforms op) (trace 10))
    (hs : BfvSquareComposition.SquareChecked (BfvInferContract.squareTransforms op)
      (trace 10) kernel) : kernel=BfvInferContract.result op key model query := by
  apply RangeKeyswitchInfer.inferSound op key model query kernel
  exact ⟨trace,fun l j => (checked_iff l _ _).mp (hi l j),
    fun s l j => (checked_iff l _ _).mp (hr s l j),hrt,hs⟩

theorem checked_premise_transfer (l : Fin 4) :
    (∃ a out,RangeKeyswitchInfer.Checked l a out) ↔ ∃ a out,Checked l a out := by
  simp only [checked_iff]

end Minidregg.Compiler.NativeRangeKeyswitch

/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.range_widths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.range_widths
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.range_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.range_supported
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.local_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.local_ranges
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.nativeRanges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.nativeRanges_iff
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.checked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.checked_iff
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.rowSends_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.rowSends_length
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.allSends_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.allSends_length
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.noWrap_of_domain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.noWrap_of_domain
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.semanticLookups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.semanticLookups
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.allRowsSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.allRowsSound
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.allRowsSound_of_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.allRowsSound_of_length
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.inferSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.inferSound
/-- info: 'Minidregg.Compiler.NativeRangeKeyswitch.checked_premise_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeRangeKeyswitch.checked_premise_transfer
