/-
[DERIVED audit fixture; EXECUTED only after recorded check]
A scoped falsifier of treating the original restore adapter as a durable
execution gate. The independently finalized event is valid public addition,
but the intent's writes and charge are unrelated. No theorem in the original
patch promises otherwise; this makes its named preflight residual executable.
Positive pole: the original Closed.honest_accepted and its actual FS receipt.
Negative pole: stale arbitrary writes accepted by the adapter and refused by
full preflight; all carriers and PrefixDiscipline are inhabited below.
-/
import Assurance.ResidentRestoreFinality

namespace Minidregg.Assurance.AdversarialRestoreReview
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Assurance.ResidentReleaseContext
open Minidregg.Assurance.ResidentRestoreFinality

set_option autoImplicit false

/-- The intended post root must equal the state certified in the Context. -/
def EffectsLinked (a : Authority) (p : Proposal) : Prop :=
  (advance a p).durable.roots 0 = ⟨p.intent.event.next⟩

def badIntent : Intent Nat Nat Token Context :=
  ⟨0, [⟨0, ⟨42⟩, ⟨99⟩⟩], [(7, 0)], fun _ => 1, honestContext 1 2⟩
def badProposal : Proposal := ⟨0, [], badIntent⟩
def badBook : VoteBook (Node := Closed.Node) (TxId := Nat) (CellId := Nat)
    (Nullifier := Token) (Event := Context) := fun _ => [badProposal]

def badBookDiscipline : PrefixDiscipline badBook where
  compatible := by
    intro node left right hl hr
    have hl' : left = badProposal := List.mem_singleton.mp hl
    have hr' : right = badProposal := List.mem_singleton.mp hr
    subst left; subst right
    exact Or.inl ⟨[], by simp⟩

theorem mismatched_effects_accepted :
    check Closed.q badBook Closed.a (manifestOf badProposal) badProposal Closed.cert = true := by decide

theorem accepted_event_arithmetic : Forced badProposal.intent.event := by
  unfold Forced
  decide

theorem unrelated_root_installed :
    (advance Closed.a badProposal).durable.roots 0 = ⟨99⟩ := by decide

theorem accepted_does_not_force_linked_effects : ¬ EffectsLinked Closed.a badProposal := by
  unfold EffectsLinked
  decide

theorem full_preflight_refuses_same_intent :
    badProposal.intent.preflight Closed.a.durable = .error .stalePreRoot := by decide

/-- Both the finality adapter and actual full-word arithmetic receipt accept
this event, while the installed durable state still has the unrelated root. -/
theorem accepted_receipt_with_unrelated_install
    (O : Minidregg.Selvage.SrMove (reduction badProposal.intent.event) 0 →
      Minidregg.Compiler.CommittedTerminalRealizer.Ext6L) :
    ∃ rc : Minidregg.Compiler.CommittedTerminalFiatShamir.FsReceipt Root 4131 13,
      check Closed.q badBook Closed.a (manifestOf badProposal) badProposal Closed.cert = true ∧
      Minidregg.Assurance.ResidentReleaseContext.check badProposal.intent.event O rc = true ∧
      ¬ EffectsLinked Closed.a badProposal := by
  obtain ⟨rc, hrc⟩ := honest_context_receipt 1 2 (by norm_num) (by norm_num) O
  exact ⟨rc, mismatched_effects_accepted, hrc, accepted_does_not_force_linked_effects⟩

/-- info: 'Minidregg.Assurance.AdversarialRestoreReview.mismatched_effects_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mismatched_effects_accepted
/-- info: 'Minidregg.Assurance.AdversarialRestoreReview.accepted_event_arithmetic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_event_arithmetic
/-- info: 'Minidregg.Assurance.AdversarialRestoreReview.unrelated_root_installed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms unrelated_root_installed
/-- info: 'Minidregg.Assurance.AdversarialRestoreReview.accepted_does_not_force_linked_effects' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_does_not_force_linked_effects
/-- info: 'Minidregg.Assurance.AdversarialRestoreReview.full_preflight_refuses_same_intent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms full_preflight_refuses_same_intent
/-- info: 'Minidregg.Assurance.AdversarialRestoreReview.accepted_receipt_with_unrelated_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_receipt_with_unrelated_install

end Minidregg.Assurance.AdversarialRestoreReview
