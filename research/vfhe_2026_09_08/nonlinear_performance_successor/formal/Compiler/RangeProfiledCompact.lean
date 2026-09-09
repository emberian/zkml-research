import Compiler.RangeProfiledMatrix
import Compiler.AirSimplify
import Compiler.PredCompile
import Compiler.IR2RangeLookupBridge
namespace Minidregg.Compiler.RangeProfiledCompact
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.SignedMatrix
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure Profile where
  layout : Layout
  rowsLayout : ProfiledMatrix.RowLayout layout.rows
  rows : Fin layout.rows → Row layout.groups
  publicArity : Nat
  oldMap : Nat → Nat

def family {n : Nat} (bits : Nat) (f : Fin n → Nat) : List (Nat × Nat) :=
  (List.finRange n).map fun i => (f i,bits)
def oldRanges (s : Profile) : List (Nat × Nat) :=
  family s.layout.limbBits (s.oldMap ∘ scalarWire s.layout) ++
  (List.finRange s.layout.rows).flatMap fun i =>
    family s.layout.limbBits (s.oldMap ∘ (ProfiledMatrix.rowWires s.layout s.rowsLayout i false).result) ++
    family (s.rowsLayout.carryBits i) (s.oldMap ∘ (ProfiledMatrix.rowWires s.layout s.rowsLayout i false).carry) ++
    family (s.rowsLayout.carryBits i) (s.oldMap ∘ (ProfiledMatrix.rowWires s.layout s.rowsLayout i true).carry)
def privateData (s : Profile) : List Nat :=
  ((s.publicArity :: (oldRanges s).map Prod.fst).filter (fun j => s.publicArity≤j)).eraseDups
def nVars (s : Profile) := s.publicArity+(privateData s).length
def indexMap (s : Profile) (j : Nat) :=
  if j<s.publicArity then j else s.publicArity+(privateData s).idxOf j
def oldIndex (s : Profile) (j : Nat) :=
  if j<s.publicArity then j else (privateData s)[j-s.publicArity]?.getD 0
def ranges (s : Profile) := ((oldRanges s).map fun r => (indexMap s r.1,r.2)).eraseDups
def RangeHolds (s : Profile) (a : Nat → BabyBear) : Prop :=
  ∀ r ∈ ranges s,(a r.1).val<2^r.2
def source (s : Profile) : ConstraintSystem BabyBear Nat :=
  [vr s.publicArity] ++ renameS s.oldMap (RangeProfiledMatrix.gates s.layout s.rowsLayout s.rows)
def system (s : Profile) := renameS (indexMap s) (AirSimplify.simplifySystem (source s))

/-- Compact source forces the original signed matrix, decoded through the
existing public wire map; no native witness-plan correctness is a premise. -/
def Sound (s : Profile) : Prop := ProfiledMatrix.Capacity s.layout s.rowsLayout s.rows →
  ∀ a,systemAccepts a (system s) → RangeHolds s a →
  (a (indexMap s s.publicArity)=0) ∧ ∀ i,
    SignedMatrix.eval (s.rows i) (decoded s.layout (a ∘ indexMap s ∘ s.oldMap))=0

theorem publicPrefix (s : Profile) (j : Nat) (hj : j<s.publicArity) : indexMap s j=j := by
  simp [indexMap,hj]
theorem oldPublicPrefix (s : Profile) (j : Nat) (hj : j<s.publicArity) : oldIndex s j=j := by
  simp [oldIndex,hj]
theorem ranges_complete (s : Profile) (a : Nat → BabyBear) (hr : RangeHolds s a) :
    RangeProfiledMatrix.Bounds s.layout s.rowsLayout (a ∘ indexMap s ∘ s.oldMap) := by
  have hh (r : Nat × Nat) (hm : r ∈ oldRanges s) : (a (indexMap s r.1)).val<2^r.2 :=
    hr _ (by simpa only [ranges,List.mem_eraseDups] using
      (List.mem_map.mpr ⟨r,hm,rfl⟩ : (indexMap s r.1,r.2) ∈ (oldRanges s).map (fun r => (indexMap s r.1,r.2))))
  have hm {n : Nat} (b : Nat) (f : Fin n → Nat) (i : Fin n) : (f i,b) ∈ family b f :=
    List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
  refine ⟨?_,?_,?_⟩
  · intro i
    exact hh _ (List.mem_append_left _ (hm _ _ i))
  · intro i j
    exact hh _ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨i,List.mem_finRange i,List.mem_append_left _ (List.mem_append_left _ (hm _ _ j))⟩))
  · intro i b j
    cases b with
    | false => exact hh _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨i,List.mem_finRange i,List.mem_append_left _ (List.mem_append_right _ (hm _ _ j))⟩))
    | true => exact hh _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨i,List.mem_finRange i,List.mem_append_right _ (hm _ _ j)⟩))

theorem sound (s : Profile) : Sound s := by
  intro cap a hs hr
  have h := (AirSimplify.simplifySystem_accepts_iff (a ∘ indexMap s) (source s)).mp
    ((systemAccepts_renameS a (indexMap s) _).mp hs)
  obtain ⟨hz,hg⟩ := (systemAccepts_append _ _ _).mp h
  refine ⟨?_,RangeProfiledMatrix.sourceSound s.layout s.rowsLayout s.rows cap _
    ((systemAccepts_renameS _ s.oldMap _).mp hg) (ranges_complete s a hr)⟩
  simpa [systemAccepts_cons,systemAccepts_nil,accepts,eval_vr] using hz

open Dregg2.Circuit.DescriptorIR2 Dregg2.Circuit.Emit.EffectVmEmitV2
def LookupChecked (s : Profile) (tf : TraceFamily) (a : Nat → BabyBear) : Prop :=
  ∀ r ∈ ranges s,IR2RangeLookupBridge.LookupHolds r.2 tf a r.1
def FaithfulRanges (s : Profile) (tf : TraceFamily) : Prop :=
  ∀ r ∈ ranges s,tf (rangeTidW r.2)=rangeRows r.2
theorem ranges_of_lookups (s : Profile) (tf : TraceFamily) (ht : FaithfulRanges s tf)
    (a : Nat → BabyBear) (hl : LookupChecked s tf a) : RangeHolds s a :=
  fun r hr => IR2RangeLookupBridge.lookup_val_lt r.2 tf (ht r hr) a r.1 (hl r hr)
theorem lookupSound (s : Profile) (cap : ProfiledMatrix.Capacity s.layout s.rowsLayout s.rows)
    (tf : TraceFamily) (ht : FaithfulRanges s tf) (a : Nat → BabyBear)
    (hs : systemAccepts a (system s)) (hl : LookupChecked s tf a) :
    (a (indexMap s s.publicArity)=0) ∧ ∀ i,
      SignedMatrix.eval (s.rows i) (decoded s.layout (a ∘ indexMap s ∘ s.oldMap))=0 :=
  sound s cap a hs (ranges_of_lookups s tf ht a hl)
end Minidregg.Compiler.RangeProfiledCompact

/-- info: 'Minidregg.Compiler.RangeProfiledCompact.publicPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompact.publicPrefix

/-- info: 'Minidregg.Compiler.RangeProfiledCompact.oldPublicPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompact.oldPublicPrefix

/-- info: 'Minidregg.Compiler.RangeProfiledCompact.ranges_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompact.ranges_complete

/-- info: 'Minidregg.Compiler.RangeProfiledCompact.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompact.sound

/-- info: 'Minidregg.Compiler.RangeProfiledCompact.ranges_of_lookups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompact.ranges_of_lookups

/-- info: 'Minidregg.Compiler.RangeProfiledCompact.lookupSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompact.lookupSound
