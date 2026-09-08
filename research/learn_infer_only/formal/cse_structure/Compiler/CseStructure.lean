/-
[DERIVED statement-first] The existing CSE pass preserves SSA and allocation bounds.
No evaluator or compiler pass is defined here. The proof reasons about the existing
HashMap lookup/insert laws rather than computing opaque hashes.

Keystone CseStructurePreservation below. Emitted source descriptors inhabit its
premises universally. Single-gate counterexamples distinguish the ordering/SSA and
allocation premises. SharedExecutionTotal then removes the shape premise from the
frozen emitted EMA execution bridge through the existing fillAux evaluator.
-/
import Compiler.EmittedScheduleExecution

namespace Minidregg.Compiler.CseStructure
open Minidregg.Compiler
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.PrivateAddressEmaSchedule
open Minidregg.Compiler.EmittedScheduleExecution (execute)
open Minidregg.Theory.PrivateAddressEma

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

universe u
variable {F : Type u} [DecidableEq F] [Hashable F]

def CseStructurePreservation : Prop :=
  ∀ d : ConstraintDescriptor F, d.SSA → d.WellFormed →
    (cse d).SSA ∧ (cse d).WellFormed

def SharedExecutionTotal : Prop :=
  ∀ (m : Nat) (es : List (Expr m)) (inputs : Fin m → F2),
    execute (shared es) (Array.ofFn inputs) = es.map (eval inputs)

def GateShape (lo hi : Nat) (g : DGate F) : Prop :=
  lo ≤ g.out ∧ g.out < hi ∧ g.a.bounded g.out ∧ g.b.bounded g.out

structure CseGood (lo hi : Nat) (s : CseState F) : Prop where
  subst_le : ∀ x, s.subst.getD x x ≤ x
  sig_kept : ∀ op a b w, s.sigs[((op, a, b) : GateSig F)]? = some w →
    (⟨op, a, b, w⟩ : DGate F) ∈ s.kept
  kept_shape : ∀ g ∈ s.kept, GateShape lo hi g
  kept_descending : s.kept.Pairwise (fun g₁ g₂ => g₂.out < g₁.out)

omit [DecidableEq F] [Hashable F] in
theorem subst_bounded (σ : Std.HashMap Nat Nat) (hσ : ∀ x, σ.getD x x ≤ x)
    (w : DWire F) (bound : Nat) (hw : w.bounded bound) :
    (w.subst σ).bounded bound := by
  cases w with
  | cnst c => trivial
  | wire i => exact (hσ i).trans_lt hw

omit [DecidableEq F] [Hashable F] in
theorem bounded_up (w : DWire F) (lo hi : Nat) (h : lo ≤ hi)
    (hw : w.bounded lo) : w.bounded hi := by
  cases w with
  | cnst c => trivial
  | wire i => exact hw.trans_le h

theorem insert_subst_le (σ : Std.HashMap Nat Nat) (hσ : ∀ x, σ.getD x x ≤ x)
    (key value : Nat) (hv : value ≤ key) :
    ∀ x, (σ.insert key value).getD x x ≤ x := by
  intro x
  rw [Std.HashMap.getD_insert]
  split
  · next h => have he : key = x := eq_of_beq h; simpa [← he] using hv
  · exact hσ x

/-- Structural map support; the existing pass's analogous semantic helper is private. -/
theorem insert_signature_kept (s : CseState F)
    (hs : ∀ op a b w, s.sigs[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ s.kept) (g : DGate F) :
    ∀ op a b w, (s.sigs.insert (g.op, g.a, g.b) g.out)[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ g :: s.kept := by
  intro op a b w h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · next hb =>
    have he : ((g.op, g.a, g.b) : GateSig F) = (op, a, b) := eq_of_beq hb
    simp only [Prod.mk.injEq] at he
    obtain ⟨hop, ha, hb⟩ := he
    have hw : g.out = w := Option.some.inj h
    have hg : (⟨op, a, b, w⟩ : DGate F) = g := by cases g; simp_all
    exact List.mem_cons.mpr (Or.inl hg)
  · exact List.mem_cons_of_mem _ (hs op a b w h)

theorem cseGo_good (lo hi : Nat) (gs : List (DGate F)) :
    ∀ s : CseState F,
      (∀ g ∈ gs, GateShape lo hi g) →
      gs.Pairwise (fun g₁ g₂ => g₁.out < g₂.out) →
      CseGood lo hi s →
      (∀ k ∈ s.kept, ∀ g ∈ gs, k.out < g.out) →
      CseGood lo hi (cseGo gs s) := by
  induction gs with
  | nil => intro s _ _ hs _; exact hs
  | cons g gs ih =>
    intro s hg hsorted hs hbefore
    have hhead := hg g (List.mem_cons_self ..)
    have htail : ∀ k ∈ gs, GateShape lo hi k :=
      fun k hk => hg k (List.mem_cons_of_mem _ hk)
    obtain ⟨hordered, htailSorted⟩ := List.pairwise_cons.mp hsorted
    cases hhit : s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
    | some w =>
      rw [cseGo_cons, hhit]
      have hw : w < g.out := hbefore _ (hs.sig_kept _ _ _ _ hhit) g (List.mem_cons_self ..)
      apply ih _ htail htailSorted
      · exact ⟨insert_subst_le s.subst hs.subst_le g.out w (Nat.le_of_lt hw),
          hs.sig_kept, hs.kept_shape, hs.kept_descending⟩
      · intro k hk j hj
        exact hbefore k hk j (List.mem_cons_of_mem _ hj)
    | none =>
      rw [cseGo_cons, hhit]
      let k : DGate F := ⟨g.op, g.a.subst s.subst, g.b.subst s.subst, g.out⟩
      have hkshape : GateShape lo hi k :=
        ⟨hhead.1, hhead.2.1, subst_bounded s.subst hs.subst_le g.a g.out hhead.2.2.1,
          subst_bounded s.subst hs.subst_le g.b g.out hhead.2.2.2⟩
      apply ih _ htail htailSorted
      · refine ⟨hs.subst_le, insert_signature_kept s hs.sig_kept k, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hkshape
          · exact hs.kept_shape j hj
        · exact List.pairwise_cons.mpr ⟨fun j hj =>
            hbefore j hj g (List.mem_cons_self ..), hs.kept_descending⟩
      · intro j hj z hz
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hordered z hz
        · exact hbefore j hj z (List.mem_cons_of_mem _ hz)

theorem empty_good (lo hi : Nat) : CseGood (F := F) lo hi ⟨∅, ∅, []⟩ := by
  refine ⟨?_, ?_, ?_, by simp⟩
  · intro x
    simp only [Std.HashMap.getD_empty]
    exact Nat.le_refl x
  · intro op a b w h
    simp only [Std.HashMap.getElem?_empty] at h
    contradiction
  · intro g h
    contradiction

theorem cse_structure_preservation : CseStructurePreservation (F := F) := by
  intro d hssa hwf
  have hg : ∀ g ∈ d.gates, GateShape d.nVars d.nWires g := by
    intro g hm
    exact ⟨(hwf.gates_in g hm).2.2.1, (hwf.gates_in g hm).2.2.2,
      (hssa.1 g hm).1, (hssa.1 g hm).2⟩
  have hs := cseGo_good d.nVars d.nWires d.gates ⟨∅, ∅, []⟩ hg hssa.2
    (empty_good d.nVars d.nWires) (by intro k hk; contradiction)
  have hkept : ∀ g ∈ (cse d).gates, GateShape d.nVars d.nWires g := by
    intro g hm
    exact hs.kept_shape g (List.mem_reverse.mp hm)
  refine ⟨⟨fun g hm => (hkept g hm).2.2, ?_⟩, ⟨hwf.public_le, hwf.vars_le, ?_, ?_⟩⟩
  · simpa only [cse_gates, List.pairwise_reverse] using hs.kept_descending
  · intro g hm
    obtain ⟨hlo, hhi, ha, hb⟩ := hkept g hm
    exact ⟨bounded_up g.a g.out d.nWires (Nat.le_of_lt hhi) ha,
      bounded_up g.b g.out d.nWires (Nat.le_of_lt hhi) hb, hlo, hhi⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact subst_bounded _ hs.subst_le w d.nWires (hwf.zeros_in w hw)

theorem raw_premises_inhabited (m : Nat) (es : List (Expr m)) :
    (raw es).SSA ∧ (raw es).WellFormed :=
  ⟨emit_ssa Fin.val 0 m (fun i => i.isLt) es,
    emit_wellFormed Fin.val 0 m (by omega) (fun i => i.isLt) es⟩

theorem shared_structure (m : Nat) (es : List (Expr m)) :
    (shared es).SSA ∧ (shared es).WellFormed := by
  obtain ⟨hssa, hwf⟩ := raw_premises_inhabited m es
  exact cse_structure_preservation (raw es) hssa hwf

theorem shared_execution_total : SharedExecutionTotal := by
  intro m es inputs
  obtain ⟨hssa, hwf⟩ := shared_structure m es
  have hs : (Array.ofFn inputs).size = (shared es).nVars := Array.size_ofFn
  have hg := fillAux_gates_hold (shared es) (Array.ofFn inputs) hssa hwf hs
  have hi : ∀ i : Fin m, (fillAux (shared es) (Array.ofFn inputs)).getD i.val 0 = inputs i := by
    intro i
    rw [fillAux_getD_of_lt (shared es) _ hwf hs i.isLt,
      Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos i.isLt]
    rfl
  simpa only [execute, readArr_eq_read] using
    shared_output_correctness m es inputs _ hi hg

theorem learn_execution_total (s : State) (a : Address) (u : Byte) :
    (execute learnSchedule (Array.ofFn (fun i => enc (learnInputs s a u i)))).map dec =
      stateBits (learn s a u) := by
  have h := congrArg (List.map dec)
    (shared_execution_total 42 learnTerms (fun i => enc (learnInputs s a u i)))
  simp only [List.map_map, Function.comp_def] at h
  exact h.trans (learn_source_outputs s a u)

theorem infer_execution_total (s : State) (a : Address) :
    (execute inferSchedule (Array.ofFn (fun i => enc (inferInputs s a i)))).map dec = [infer s a] := by
  have h := congrArg (List.map dec)
    (shared_execution_total 34 inferTerms (fun i => enc (inferInputs s a i)))
  simp only [List.map_map, Function.comp_def] at h
  exact h.trans (infer_source_outputs s a)

theorem learn_total_subject :
    (execute learnSchedule (Array.ofFn (fun i => enc (learnInputs zeroState 3 (BitVec.ofInt 8 120) i)))).map dec =
      stateBits (learn zeroState 3 (BitVec.ofInt 8 120)) ∧
    learn zeroState 3 (BitVec.ofInt 8 120) 3 ≠ zeroState 3 :=
  ⟨learn_execution_total _ _ _, by decide +kernel⟩

theorem wrong_learn_answer_refused :
    (execute learnSchedule (Array.ofFn (fun i => enc (learnInputs zeroState 3 (BitVec.ofInt 8 120) i)))).map dec ≠
      stateBits zeroState := by
  rw [learn_execution_total]
  decide +kernel

omit [DecidableEq F] [Hashable F] in
theorem subst_empty (w : DWire F) : w.subst (∅ : Std.HashMap Nat Nat) = w := by
  cases w <;> simp [DWire.subst, Std.HashMap.getD_empty]

theorem singleton_cse (np nv nw : Nat) (g : DGate F) (zs : List (DWire F)) :
    cse (⟨np, nv, nw, [g], zs⟩ : ConstraintDescriptor F) = ⟨np, nv, nw, [g], zs⟩ := by
  simp [cse, cseGo, subst_empty]
  have he : (DWire.subst (∅ : Std.HashMap Nat Nat) : DWire F → DWire F) = id :=
    funext subst_empty
  rw [he, List.map_id]

def selfRead : ConstraintDescriptor F2 :=
  ⟨0, 0, 1, [⟨.add, .wire 0, .cnst 0, 0⟩], [.wire 0]⟩

def inputWrite : ConstraintDescriptor F2 :=
  ⟨0, 1, 1, [⟨.add, .cnst 0, .cnst 0, 0⟩], [.wire 0]⟩

/-- Allocation bounds alone do not force SSA after CSE. -/
theorem missing_ssa_refused : selfRead.WellFormed ∧ ¬ (cse selfRead).SSA := by
  have hc : cse selfRead = selfRead := singleton_cse 0 0 1 _ _
  rw [hc]
  constructor
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · intro g hg
      simp only [selfRead, List.mem_singleton] at hg
      subst g
      simp [selfRead, DWire.bounded]
    · intro z hz
      simp only [selfRead, List.mem_singleton] at hz
      subst z
      simp [selfRead, DWire.bounded]
  · simp [selfRead, ConstraintDescriptor.SSA, DWire.bounded]

/-- SSA alone does not exclude overwriting an input after CSE. -/
theorem missing_bounds_refused : inputWrite.SSA ∧ ¬ (cse inputWrite).WellFormed := by
  have hc : cse inputWrite = inputWrite := singleton_cse 0 1 1 _ _
  rw [hc]
  constructor
  · simp [inputWrite, ConstraintDescriptor.SSA, DWire.bounded]
  · intro hw
    have h := hw.gates_in ⟨.add, .cnst 0, .cnst 0, 0⟩ (by simp [inputWrite])
    have hbad : 1 ≤ 0 := h.2.2.1
    omega

/-- info: 'Minidregg.Compiler.CseStructure.subst_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subst_bounded
/-- info: 'Minidregg.Compiler.CseStructure.bounded_up' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bounded_up
/-- info: 'Minidregg.Compiler.CseStructure.insert_subst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insert_subst_le
/-- info: 'Minidregg.Compiler.CseStructure.insert_signature_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insert_signature_kept
/-- info: 'Minidregg.Compiler.CseStructure.cseGo_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseGo_good
/-- info: 'Minidregg.Compiler.CseStructure.empty_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_good
/-- info: 'Minidregg.Compiler.CseStructure.cse_structure_preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cse_structure_preservation
/-- info: 'Minidregg.Compiler.CseStructure.raw_premises_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_premises_inhabited
/-- info: 'Minidregg.Compiler.CseStructure.shared_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shared_structure
/-- info: 'Minidregg.Compiler.CseStructure.shared_execution_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shared_execution_total
/-- info: 'Minidregg.Compiler.CseStructure.learn_execution_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms learn_execution_total
/-- info: 'Minidregg.Compiler.CseStructure.infer_execution_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms infer_execution_total
/-- info: 'Minidregg.Compiler.CseStructure.learn_total_subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms learn_total_subject
/-- info: 'Minidregg.Compiler.CseStructure.wrong_learn_answer_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_learn_answer_refused
/-- info: 'Minidregg.Compiler.CseStructure.subst_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subst_empty
/-- info: 'Minidregg.Compiler.CseStructure.singleton_cse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms singleton_cse
/-- info: 'Minidregg.Compiler.CseStructure.missing_ssa_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_ssa_refused
/-- info: 'Minidregg.Compiler.CseStructure.missing_bounds_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_bounds_refused

end Minidregg.Compiler.CseStructure
