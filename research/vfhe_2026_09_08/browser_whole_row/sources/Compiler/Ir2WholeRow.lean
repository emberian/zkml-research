/- Row-local AIR emission to the existing DescriptorIR-v2 whole-domain gate.
Source contract: descriptor_ir2.rs:1624-1653,1892-1902,4080-4115.
The existing `gate` is transition-only. `window_gate` with on_transition=false
asserts its local body on every row. This is a serializer and scope contract
over the existing AirSig terms, not a new arithmetic expression language or a
formal verification of the native JSON parser. -/
import Compiler.AirRange

namespace Minidregg.Compiler.Ir2WholeRow
open Minidregg.Compiler
universe u
variable {F Idx : Type u}

/-- Existing row-window grammar: local leaves use `c`, unlike base var leaves' `v`. -/
def localJson (i : Nat) : String := "{\"t\":\"loc\",\"c\":"++toString i++"}"

/-- One fold reading of the source arithmetic; only variable spelling changes
from the base expression grammar. Constants and both binary operations are preserved. -/
def bodyAlg (encodeConst : F → Nat) (encodeIndex : Idx → Nat) : Alg (AirSig F Idx) String :=
  fun op => match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString (encodeConst c)++"}"
  | .var i => fun _ => localJson (encodeIndex i)
  | .add => fun c => "{\"t\":\"add\",\"l\":"++c false++",\"r\":"++c true++"}"
  | .mul => fun c => "{\"t\":\"mul\",\"l\":"++c false++",\"r\":"++c true++"}"

/-- The sole row-local assertion wrapper: the native transition flag is false. -/
def gateJson (encodeConst : F → Nat) (encodeIndex : Idx → Nat)
    (t : Term (AirSig F Idx)) : String :=
  "{\"t\":\"window_gate\",\"on_transition\":false,\"body\":"++
    fold (bodyAlg encodeConst encodeIndex) t++"}"

section Semantics
variable [Field F]

/-- Exact logical scope of the existing native gate forms on trace-domain rows.
This contract does not identify Rust evaluation with Lean; that remains the
recorded source/conformance boundary. Arithmetic itself is the existing DSL. -/
def scopeHolds (onTransition isLast : Bool) (asg : Idx → F)
    (sys : ConstraintSystem F Idx) : Prop :=
  if onTransition then isLast=false → systemAccepts asg sys else systemAccepts asg sys

def ScopeContract : Prop :=
  (∀ asg sys isLast,scopeHolds (F := F) (Idx := Idx) false isLast asg sys ↔ systemAccepts asg sys) ∧
  (∀ asg sys,scopeHolds (F := F) (Idx := Idx) true true asg sys)

theorem scope_contract : ScopeContract (F := F) (Idx := Idx) := by
  constructor
  · intros; rfl
  · intro asg sys h
    contradiction

/-- On a nonzero selector, the native multiplied assertion is precisely the
source assertion; at the last-row zero selector no body is constrained. -/
theorem selected_iff (selector : F) (hs : selector ≠ 0) (asg : Idx → F)
    (sys : ConstraintSystem F Idx) :
    (∀ t ∈ sys,selector*eval asg t=0) ↔ systemAccepts asg sys := by
  simp only [mul_eq_zero,or_iff_right hs]
  rfl

theorem zero_selector (asg : Idx → F) (sys : ConstraintSystem F Idx) :
    ∀ t ∈ sys,(0:F)*eval asg t=0 := by simp

/-- With the emitted false flag, arithmetic applies also to the physical last row. -/
theorem all_rows {Row : Type u} (isLast : Row → Bool) (trace : Row → Idx → F)
    (sys : ConstraintSystem F Idx) (h : ∀ r,scopeHolds false (isLast r) (trace r) sys) :
    ∀ r,systemAccepts (trace r) sys := h

/-- Any refusing source row is an exact terminal-row counterexample for the
old transition-only wrapper, and is refused by the whole-domain wrapper. -/
theorem terminal_falsifier (asg : Idx → F) (sys : ConstraintSystem F Idx)
    (h : ¬systemAccepts asg sys) :
    scopeHolds true true asg sys ∧ ¬scopeHolds false true asg sys :=
  ⟨scope_contract.2 asg sys,h⟩

end Semantics
end Minidregg.Compiler.Ir2WholeRow

/-- info: 'Minidregg.Compiler.Ir2WholeRow.scope_contract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2WholeRow.scope_contract

/-- info: 'Minidregg.Compiler.Ir2WholeRow.selected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2WholeRow.selected_iff

/-- info: 'Minidregg.Compiler.Ir2WholeRow.zero_selector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2WholeRow.zero_selector

/-- info: 'Minidregg.Compiler.Ir2WholeRow.all_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2WholeRow.all_rows

/-- info: 'Minidregg.Compiler.Ir2WholeRow.terminal_falsifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2WholeRow.terminal_falsifier

