/-
[DERIVED audit tooth; EXECUTED only against the recorded old helper hash]
The genuine gated result for one Plan can be passed to releasedPacket with a
second Plan. The accepted receipt and installed state remain genuine, while
that helper returns a packet naming an unapproved recipient. This refutes only
the old helper/API composition; same-plan theorems remain valid.
ATLAS positive pole is Closed.subject's actual accepted receipt and descriptor;
negative pole substitutes only the independently supplied packet-selection Plan.
-/
import Assurance.ResidentDurableIntegration

namespace Minidregg.Assurance.ReleasePacketSeamReview
open Minidregg.Theory.CellStateWitness (materializer)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Assurance.ResidentReleaseContext
open Minidregg.Assurance.ResidentDurableIntegration
open Minidregg.Compiler.CommittedTerminalFiatShamir (FsReceipt)
open Minidregg.Compiler.CommittedTerminalRealizer (Ext6L traceOf)
open Minidregg.Compiler (descriptorHolds)
open Minidregg.Compiler.EvmAddAir (evmAddDescriptor)
open Minidregg.Selvage (SrMove)

set_option autoImplicit false

def substituted : Plan materializer :=
  { Closed.p with context := { Closed.p.context with recipient := 24 } }

def ReleasePacketPlanSubstitution : Prop :=
  ∀ O : SrMove (reduction Closed.p.context) 0 → Ext6L,
    ∃ rc : FsReceipt Root 4131 13,
      authorized Closed.q Closed.book Closed.selected Closed.before Closed.p Closed.cert O rc = true ∧
      descriptorHolds evmAddDescriptor (traceOf rc.word) ∧
      releasedPacket substituted
        (gatedExecute Closed.q Closed.book .complete Closed.selected Closed.before
          Closed.p Closed.cert O rc) = some substituted.packet ∧
      substituted.packet ≠ Closed.p.packet ∧
      substituted.context.recipient ≠ Closed.selected.recipient

theorem recipient_different : substituted.context.recipient ≠ Closed.selected.recipient := by decide

theorem packet_different : substituted.packet ≠ Closed.p.packet := by
  intro equal
  have same := substituted.packet_binds_context Closed.p equal
  have recipients := congrArg Context.recipient same
  change (24 : Nat) = 23 at recipients
  omega

theorem accepted_result_can_be_relabelled : ReleasePacketPlanSubstitution := by
  intro O
  obtain ⟨rc, approved, ready, _, _, _, descriptor⟩ := Closed.subject O
  have installed := gated_commit_ready Closed.q Closed.book Closed.selected Closed.before
    Closed.p Closed.cert O rc approved ready rfl
  refine ⟨rc, approved, descriptor, ?_, packet_different, recipient_different⟩
  rw [installed]
  rfl

/-- info: 'Minidregg.Assurance.ReleasePacketSeamReview.recipient_different' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recipient_different
/-- info: 'Minidregg.Assurance.ReleasePacketSeamReview.packet_different' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packet_different
/-- info: 'Minidregg.Assurance.ReleasePacketSeamReview.accepted_result_can_be_relabelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_result_can_be_relabelled

end Minidregg.Assurance.ReleasePacketSeamReview
