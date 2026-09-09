/- The existing IR2 range-lookup semantics, applied to the existing compiler's
canonical BabyBear values. This is a local semantic bridge, not an assumption
that a native proof is sound or a new range-table AIR. -/
import Compiler.EmitSerialize
import Dregg2.Circuit.Emit.EffectVmEmitV2

namespace Minidregg.Compiler.IR2RangeLookupBridge
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
set_option autoImplicit false
set_option maxHeartbeats 500000

def canonicalEnv (asg : Nat → BabyBear) : VmRowEnv where
  loc w := ((asg w).val : Int)
  nxt _ := 0
  pub _ := 0

def LookupHolds (bits : Nat) (tf : TraceFamily) (asg : Nat → BabyBear) (w : Nat) : Prop :=
  Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt tf (canonicalEnv asg)
    ⟨rangeTidW bits,[.var w]⟩

/-- The faithful semantic table is explicit. The existing theorem proves the
interval; only the canonical nat-to-int conversion is discharged here. -/
theorem lookup_val_lt (bits : Nat) (tf : TraceFamily)
    (hr : tf (rangeTidW bits)=rangeRows bits) (asg : Nat → BabyBear) (w : Nat)
    (h : LookupHolds bits tf asg w) : (asg w).val < 2^bits := by
  have hv := lookup_replaces_rangeW bits tf hr (canonicalEnv asg) w h
  change 0 ≤ ((asg w).val : Int) ∧ ((asg w).val : Int) < (2 : Int)^bits at hv
  exact_mod_cast hv.2

theorem lookup_iff_val_lt (bits : Nat) (tf : TraceFamily)
    (hr : tf (rangeTidW bits)=rangeRows bits) (asg : Nat → BabyBear) (w : Nat) :
    LookupHolds bits tf asg w ↔ (asg w).val < 2^bits := by
  constructor
  · exact lookup_val_lt bits tf hr asg w
  · intro h
    unfold LookupHolds Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt
    rw [hr]
    change [((asg w).val : Int)] ∈ rangeRows bits
    apply (range_row_mem_iff _ bits).mpr
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast h⟩

theorem lookup9_iff (tf : TraceFamily) (hr : tf (rangeTidW 9)=rangeRows 9)
    (asg : Nat → BabyBear) (w : Nat) : LookupHolds 9 tf asg w ↔ (asg w).val < 512 :=
  lookup_iff_val_lt 9 tf hr asg w

theorem lookup16_iff (tf : TraceFamily) (hr : tf (rangeTidW 16)=rangeRows 16)
    (asg : Nat → BabyBear) (w : Nat) : LookupHolds 16 tf asg w ↔ (asg w).val < 65536 :=
  lookup_iff_val_lt 16 tf hr asg w

/-- The existing width-indexed Lean IDs serialize to the proposed declared IDs. -/
theorem declared_wire_ids : (rangeTidW 9).wireId=78 ∧ (rangeTidW 16).wireId=85 := by
  decide

def NonzeroWitness : Prop :=
  LookupHolds 9 (fun _ => rangeRows 9) (fun _ => (511 : BabyBear)) 0

theorem nonzeroWitness : NonzeroWitness := by
  exact (lookup9_iff (fun _ => rangeRows 9) rfl (fun _ => (511 : BabyBear)) 0).mpr (by decide)

def OverflowFalsifier : Prop := ∀ (tf : TraceFamily),
  tf (rangeTidW 9)=rangeRows 9 → ¬LookupHolds 9 tf (fun _ => (512 : BabyBear)) 0

theorem overflowFalsifier : OverflowFalsifier := by
  intro tf hr h
  have hv := (lookup9_iff tf hr _ _).mp h
  have hn : ¬(512 : BabyBear).val < 512 := by decide
  exact hn hv

end Minidregg.Compiler.IR2RangeLookupBridge

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.lookup_val_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.lookup_val_lt

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.lookup_iff_val_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.lookup_iff_val_lt

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.lookup9_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.lookup9_iff

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.lookup16_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.lookup16_iff

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.declared_wire_ids' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.declared_wire_ids

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.nonzeroWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.nonzeroWitness

/-- info: 'Minidregg.Compiler.IR2RangeLookupBridge.overflowFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.IR2RangeLookupBridge.overflowFalsifier
