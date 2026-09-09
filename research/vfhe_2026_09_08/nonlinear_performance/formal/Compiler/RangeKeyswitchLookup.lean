/- Existing declared-table lookup semantics closes the range premise. -/
import Compiler.RangeKeyswitchRow
import Compiler.IR2RangeLookupBridge
namespace Minidregg.Compiler.RangeKeyswitchLookup
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.RangeKeyswitchRow
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
set_option autoImplicit false

def extend (a : Idx → BabyBear) (i : Nat) : BabyBear :=
  if h : i<nVars then a ⟨i,h⟩ else 0

def LookupChecked (tf : TraceFamily) (a : Idx → BabyBear) : Prop :=
  ∀ r ∈ ranges,IR2RangeLookupBridge.LookupHolds r.bits tf (extend a) r.wire.val

def FaithfulRanges (tf : TraceFamily) : Prop :=
  ∀ r ∈ ranges,tf (rangeTidW r.bits)=rangeRows r.bits

/-- Exact existing IR2 range tables, not a native verifier-success premise. -/
theorem ranges_of_lookups (tf : TraceFamily) (ht : FaithfulRanges tf) (a : Idx → BabyBear)
    (hl : LookupChecked tf a) : RangeHolds a := by
  intro r hr
  have hh := IR2RangeLookupBridge.lookup_val_lt r.bits tf (ht r hr) (extend a) r.wire.val (hl r hr)
  simpa [extend,r.wire.isLt] using hh

theorem lookupRowSound (l : Fin 4) (tf : TraceFamily) (ht : FaithfulRanges tf)
    (a : Idx → BabyBear) (hg : systemAccepts a (system (BfvKeyswitchRow.primes l)))
    (hl : LookupChecked tf a) :
    (∀ g,value a g<BfvKeyswitchRow.primes l) ∧ ∀ h,value a (BfvKeyswitchCore.oIndex h)=
    (value a (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
      value a (BfvKeyswitchCore.dIndex k)*value a (BfvKeyswitchCore.kIndex h k))%BfvKeyswitchRow.primes l :=
  actualRowSound l a hg (ranges_of_lookups tf ht a hl)

/-- The source theorem quantifies every row, including the final one. The
whole-row serializer is required at the separate descriptor interpretation seam. -/
theorem allRowsSound {n : Nat} (l : Fin 4) (tf : TraceFamily) (ht : FaithfulRanges tf)
    (trace : Fin n → Idx → BabyBear)
    (hg : ∀ r,systemAccepts (trace r) (system (BfvKeyswitchRow.primes l)))
    (hl : ∀ r,LookupChecked tf (trace r)) :
    ∀ r h,value (trace r) (BfvKeyswitchCore.oIndex h)=
    (value (trace r) (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
      value (trace r) (BfvKeyswitchCore.dIndex k)*value (trace r) (BfvKeyswitchCore.kIndex h k))%BfvKeyswitchRow.primes l :=
  fun r => (lookupRowSound l tf ht (trace r) (hg r) (hl r)).2
end Minidregg.Compiler.RangeKeyswitchLookup

/-- info: 'Minidregg.Compiler.RangeKeyswitchLookup.ranges_of_lookups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchLookup.ranges_of_lookups

/-- info: 'Minidregg.Compiler.RangeKeyswitchLookup.lookupRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchLookup.lookupRowSound

/-- info: 'Minidregg.Compiler.RangeKeyswitchLookup.allRowsSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchLookup.allRowsSound

