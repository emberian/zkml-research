/-
[DERIVED target; EXECUTED only after the recorded Lean check]
restore(manifest) against the REAL FinalityGate and durable consumption map.

Statement-first: accepted release uses the independent authority's current
prefix/head, not the manifest's restored view. After install, replay of the
same finalized candidate is refused; a reused parent token is also refused.
Under the existing PrefixDiscipline, two checked candidates at one slot have
equal entire Context events. Combine with ResidentReleaseContext.check for
the conditional arithmetic theorem. No state decryption key occurs here.

ATLAS witness: Closed starts at public state 1 and finalizes addition of 2;
actual quorum checking and the accepted Stage-0 receipt are both inhabited.
Teeth: finality alone still accepts the old certificate; restore gate refuses;
restoring the AUTHORITY too permits another authorization. The head cannot
prevent silent copied computation; it only orders fresh releases. Network
authentication, cross-time vote discipline, atomic durable install/delivery,
policy interpretation and hidden-state commitments remain explicit residuals.

This adapter is an authorization model, not a complete Durable preflight:
the witness has no cell rootWrites. Snapshot.install is reused for consumption;
a production adapter must enter through DataIntent/preflight with real roots.
-/
import Assurance.ResidentReleaseContext
import Kernel.FinalityGate

namespace Minidregg.Assurance.ResidentRestoreFinality

open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Kernel.FinalityGate (Cert)
open Minidregg.Assurance.ResidentReleaseContext
open Minidregg.Compiler.CommittedTerminalFiatShamir (FsReceipt)
open Minidregg.Compiler.CommittedTerminalRealizer (traceOf)
open Minidregg.Compiler (descriptorHolds)
open Minidregg.Compiler.EvmAddAir (evmAddDescriptor)
open Minidregg.Selvage (SrMove)
open Minidregg.Compiler.CommittedTerminalRealizer (Ext6L)

set_option autoImplicit false

abbrev Token := Nat × Nat
abbrev Proposal := Candidate Nat Nat Token Context
abbrev Durable := Snapshot Nat Nat Token Context

structure Manifest where
  genesis : Nat
  parent : Nat
  slot : Nat
  deriving DecidableEq

structure Authority where
  genesis : Nat
  head : Nat
  log : List (Intent Nat Nat Token Context)
  durable : Durable
  policy : Context → Bool

def manifestOf (p : Proposal) : Manifest :=
  ⟨p.intent.event.genesis, p.intent.event.parent, p.slot⟩

/-- The local restore changes only the host-side manifest. -/
def restore (_old : Manifest) (saved : Manifest) : Manifest := saved

def pins (a : Authority) (m : Manifest) (p : Proposal) : Bool :=
  decide (m.genesis = a.genesis ∧ m.parent = a.head ∧ m.slot = p.slot ∧
    p.intent.event.genesis = m.genesis ∧ p.intent.event.parent = m.parent ∧
    p.intent.nullifiers = [(a.genesis, p.slot)])

def check {Node : Type} [DecidableEq Node]
    (q : QuorumSystem Node) [DecidablePred q.isQuorum]
    (book : VoteBook (Node := Node) (TxId := Nat) (CellId := Nat)
      (Nullifier := Token) (Event := Context))
    (a : Authority) (m : Manifest) (p : Proposal) (cert : Cert Node) : Bool :=
  Minidregg.Kernel.FinalityGate.check q book p cert &&
    decide (p.priorLog = a.log) && pins a m p &&
    p.intent.nullifiersFreshCheck a.durable && a.policy p.intent.event

def advance (a : Authority) (p : Proposal) : Authority :=
  { a with
    head := p.intent.event.next
    log := p.log
    durable := Snapshot.install a.durable p.intent }

def Current (a : Authority) (p : Proposal) : Prop :=
  p.priorLog = a.log ∧ p.intent.event.genesis = a.genesis ∧ p.intent.event.parent = a.head

section Generic
variable {Node : Type} [DecidableEq Node]
variable (q : QuorumSystem Node) [DecidablePred q.isQuorum]
variable (book : VoteBook (Node := Node) (TxId := Nat) (CellId := Nat)
  (Nullifier := Token) (Event := Context))

theorem accepted_parts (a : Authority) (m : Manifest) (p : Proposal) (cert : Cert Node)
    (h : check q book a m p cert = true) :
    Minidregg.Kernel.FinalityGate.check q book p cert = true ∧
    p.priorLog = a.log ∧ pins a m p = true ∧
    p.intent.nullifiersFreshCheck a.durable = true ∧ a.policy p.intent.event = true := by
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem accepted_current (a : Authority) (m : Manifest) (p : Proposal) (cert : Cert Node)
    (h : check q book a m p cert = true) : Current a p := by
  obtain ⟨_, hp, hm, _, _⟩ := accepted_parts q book a m p cert h
  obtain ⟨hg, hh, _, heg, heh, _⟩ := of_decide_eq_true hm
  exact ⟨hp, heg.trans hg, heh.trans hh⟩

/-- Finality can remain true; the exact independent prefix is now longer.
No assumption that the arithmetic changes the state (no-op transitions too). -/
theorem restore_replay_refused (a : Authority) (m : Manifest) (p : Proposal)
    (cert : Cert Node) : check q book (advance a p) m p cert = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hp := (accepted_parts q book (advance a p) m p cert h).2.1
  have hl := congrArg List.length hp
  simp only [advance, Candidate.log, List.length_append, List.length_singleton] at hl
  omega

/-- Reusing a spent parent token fails even under a new candidate/manifest. -/
theorem consumed_parent_refused (a : Authority) (m : Manifest) (old p : Proposal)
    (cert : Cert Node) (token : Token)
    (ho : token ∈ old.intent.nullifiers) (hp : token ∈ p.intent.nullifiers) :
    check q book (advance a old) m p cert = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have fresh := (accepted_parts q book (advance a old) m p cert h).2.2.2.1
  have hf := (Intent.nullifiersFreshCheck_eq_true_iff _ _).mp fresh token hp
  have hs := Snapshot.install_consumes a.durable old.intent token ho
  change (Snapshot.install a.durable old.intent).consumed token = false at hf
  rw [hs] at hf
  contradiction

/-- Every field is in the exact durable event, reusing the finality theorem.
This is conditional on the actual cross-epoch PrefixDiscipline, not merely
on the presence of a quorum-shaped voter list. -/
theorem context_unique_at_slot (discipline : PrefixDiscipline book)
    (a b : Authority) (ma mb : Manifest) (p r : Proposal) (cp cr : Cert Node)
    (hp : check q book a ma p cp = true) (hr : check q book b mb r cr = true)
    (slot : p.slot = r.slot) : p.intent.event = r.intent.event := by
  exact congrArg Intent.event
    (Minidregg.Kernel.FinalityGate.checked_transaction_unique_at_slot q book discipline
      (accepted_parts q book a ma p cp hp).1 (accepted_parts q book b mb r cr hr).1 slot)

/-- End-to-end CONDITIONAL integrity, with the descriptor-failure event left
visible for the existing ROM price. No hiding or random-state theorem. -/
theorem authorized_step (a : Authority) (m : Manifest) (p : Proposal) (cert : Cert Node)
    (O : SrMove (reduction p.intent.event) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (hc : check q book a m p cert = true)
    (hr : Minidregg.Assurance.ResidentReleaseContext.check p.intent.event O rc = true)
    (hd : descriptorHolds evmAddDescriptor (traceOf rc.word)) :
    Current a p ∧ rc.root.1 = p.intent.event ∧ Forced p.intent.event :=
  ⟨accepted_current q book a m p cert hc,
    context_binding p.intent.event O rc hr, arithmetic_binding p.intent.event O rc hr hd⟩

end Generic

namespace Closed
abbrev Node := Fin 3
def q := Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance.quorums
instance : DecidablePred q.isQuorum :=
  Minidregg.Kernel.FinalityGate.ClosedInstance.quorumsDecidable

def intent : Intent Nat Nat Token Context :=
  ⟨0, [], [(7, 0)], fun _ => 0, honestContext 1 2⟩
def p : Proposal := ⟨0, [], intent⟩
def book : VoteBook (Node := Node) (TxId := Nat) (CellId := Nat)
    (Nullifier := Token) (Event := Context) := fun _ => [p]
def cert : Cert Node := ⟨{0, 1}⟩
def durable : Durable := ⟨fun _ => ⟨0⟩, fun _ => false, fun _ => 0, [], []⟩
def a : Authority := ⟨7, 1, [], durable,
  fun c => decide (c.program = 0 ∧ c.version = 1 ∧ c.authorization = 19 ∧ c.recipient = 23)⟩

def discipline : PrefixDiscipline book where
  compatible := by
    intro node left right hl hr
    have hl' : left = p := List.mem_singleton.mp hl
    have hr' : right = p := List.mem_singleton.mp hr
    subst left; subst right
    exact Or.inl ⟨[], by simp⟩

theorem honest_accepted : check q book a (manifestOf p) p cert = true := by decide

theorem finality_survives_restore :
    Minidregg.Kernel.FinalityGate.check q book p cert = true := by decide

theorem restored_manifest_refused :
    check q book (advance a p) (restore (manifestOf p) (manifestOf p)) p cert = false :=
  restore_replay_refused q book a _ p cert

/-- Resetting the independent authority re-enables the same release. -/
theorem authority_rollback_reaccepts :
    check q book a (restore (manifestOf p) (manifestOf p)) p cert = true := honest_accepted

theorem nontrivial_arithmetic_witness (O : SrMove (reduction p.intent.event) 0 → Ext6L) :
    ∃ rc : FsReceipt Root 4131 13,
      check q book a (manifestOf p) p cert = true ∧
      Minidregg.Assurance.ResidentReleaseContext.check p.intent.event O rc = true ∧
      p.intent.event.next ≠ a.head := by
  obtain ⟨rc, hrc⟩ := honest_context_receipt 1 2 (by norm_num) (by norm_num) O
  exact ⟨rc, honest_accepted, hrc, by decide⟩

end Closed
end Minidregg.Assurance.ResidentRestoreFinality

/- Exact-output axiom pins, observed and checked against the kernel. -/

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.accepted_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.accepted_parts

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.accepted_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.accepted_current

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.restore_replay_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.restore_replay_refused

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.consumed_parent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.consumed_parent_refused

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.context_unique_at_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.context_unique_at_slot

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.authorized_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.authorized_step

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.Closed.honest_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.Closed.honest_accepted

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.Closed.finality_survives_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.Closed.finality_survives_restore

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.Closed.restored_manifest_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.Closed.restored_manifest_refused

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.Closed.authority_rollback_reaccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.Closed.authority_rollback_reaccepts

/-- info: 'Minidregg.Assurance.ResidentRestoreFinality.Closed.nontrivial_arithmetic_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentRestoreFinality.Closed.nontrivial_arithmetic_witness
