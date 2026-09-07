/- [DERIVED target] Mixed durable histories with a per-window admission projection.
The frozen exclusive window44 relation remains unchanged. Actual journal entries
are classified under an explicit dispatch premise; a non-admission must preserve
the selected window and genesis canonical bytes. A routing label alone does not
prove admission/source validity, framing, cryptographic authorization or noise.
-/
import Assurance.CiphertextWindowCell

namespace Minidregg.Assurance.CiphertextWindowFrame
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.CiphertextWindow
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Assurance.ResidentDurableIntegration (Selection WalIntent)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot)
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

/-- A projection of actual recorded semantic intents, in journal order.
This is not an independently mutable learning counter. -/
def admissionProjection (classify : WalIntent → Bool) {hash : List UInt8 → Digest}
    (data : DataSnapshot hash) : List WalIntent :=
  (data.model.journal.map Prod.snd).filter classify

def admissionCount (classify : WalIntent → Bool) {hash : List UInt8 → Digest}
    (data : DataSnapshot hash) : Nat := (admissionProjection classify data).length

theorem projection_install {hash : List UInt8 → Digest} (classify : WalIntent → Bool)
    (before : DataSnapshot hash) (intent : DataIntent hash) :
    admissionProjection classify (DataSnapshot.install before intent)=
      if classify intent.erase then intent.erase::admissionProjection classify before
      else admissionProjection classify before := by
  cases h : classify intent.erase <;> simp [admissionProjection,DataSnapshot.install,Snapshot.install,h]

theorem count_admission {hash : List UInt8 → Digest} (classify : WalIntent → Bool)
    (before : DataSnapshot hash) (intent : DataIntent hash) (h : classify intent.erase=true) :
    admissionCount classify (DataSnapshot.install before intent)=admissionCount classify before+1 := by
  simp [admissionCount,projection_install,h]

theorem count_frame {hash : List UInt8 → Digest} (classify : WalIntent → Bool)
    (before : DataSnapshot hash) (intent : DataIntent hash) (h : classify intent.erase=false) :
    admissionCount classify (DataSnapshot.install before intent)=admissionCount classify before := by
  simp [admissionCount,projection_install,h]

/-- Inspect the existing write lookup, including no-op writes to this cell.
A colliding root never suffices: the proposed canonical bytes must be equal. -/
def frameCheck {hash : List UInt8 → Digest} (cellId : Digest)
    (before : DataSnapshot hash) (intent : DataIntent hash) : Bool :=
  match DataSnapshot.lookupPostBytes cellId intent.writes with
  | none => true
  | some bytes => decide (bytes=before.canonicalBytes cellId)

theorem frameCheck_iff {hash : List UInt8 → Digest} (cellId : Digest)
    (before : DataSnapshot hash) (intent : DataIntent hash) :
    frameCheck cellId before intent=true ↔
      (DataSnapshot.install before intent).canonicalBytes cellId=before.canonicalBytes cellId := by
  unfold frameCheck
  change (match DataSnapshot.lookupPostBytes cellId intent.writes with
    | none => true | some bytes => decide (bytes=before.canonicalBytes cellId))=true ↔
    (DataSnapshot.lookupPostBytes cellId intent.writes).getD (before.canonicalBytes cellId)=before.canonicalBytes cellId
  cases DataSnapshot.lookupPostBytes cellId intent.writes <;> simp

def framesSelected {hash : List UInt8 → Digest} (selected : Selection)
    (before : DataSnapshot hash) (intent : DataIntent hash) : Bool :=
  frameCheck selected.stateId before intent && frameCheck selected.genesisId before intent

theorem framesSelected_iff {hash : List UInt8 → Digest} (selected : Selection)
    (before : DataSnapshot hash) (intent : DataIntent hash) :
    framesSelected selected before intent=true ↔
      (DataSnapshot.install before intent).canonicalBytes selected.stateId=before.canonicalBytes selected.stateId ∧
      (DataSnapshot.install before intent).canonicalBytes selected.genesisId=before.canonicalBytes selected.genesisId := by
  simp only [framesSelected,Bool.and_eq_true,frameCheck_iff]

theorem changed_window_refused {hash : List UInt8 → Digest} (selected : Selection)
    (before : DataSnapshot hash) (intent : DataIntent hash)
    (changed : (DataSnapshot.install before intent).canonicalBytes selected.stateId≠before.canonicalBytes selected.stateId) :
    framesSelected selected before intent=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact changed ((framesSelected_iff selected before intent).mp h).1

/-- Concrete routing discriminator over the ACTUAL journal replay envelope:
versioned resident event, a write to this window cell, selected genesis, and
program2/version1 in the existing canonical context encoding. Its tag is not
an authentication assertion; the history also needs checked admission or frame.
Malformed or noncanonical context bytes are outside the admission class. -/
def windowAdmission (selected : Selection) (intent : WalIntent) : Bool :=
  let event:=intent.event.event
  decide (event.codecVersion=1 ∧ event.domain=⟨102⟩) &&
  intent.event.writes.any (fun write=>decide (write.cellId=selected.stateId)) &&
  match (StreamCodec.list StreamCodec.nat).toLawful.decode event.canonicalBytes with
  | some words => decide (words.length=11 ∧ words[0]?.getD 0=selected.genesisId.value ∧
      words[2]?.getD 0=2 ∧ words[3]?.getD 0=1 ∧
      (StreamCodec.list StreamCodec.nat).encode words=event.canonicalBytes)
  | none => false


/-- Permissive decoding does not silently assign a canonical admission tag. -/
theorem noncanonical_tag_refused (selected : Selection) (intent : WalIntent) (words : List Nat)
    (decoded : (StreamCodec.list StreamCodec.nat).toLawful.decode intent.event.event.canonicalBytes=some words)
    (different : (StreamCodec.list StreamCodec.nat).encode words≠intent.event.event.canonicalBytes) :
    windowAdmission selected intent=false := by
  simp [windowAdmission,decoded,different]

variable {Ct : Type} [AddCommGroup Ct]

/-- Each edge is an actual fresh, preflight-ready DataIntent install. Learn
edges refine the window transition; other edges must frame selected bytes.
Classification is fixed across the history and read from recorded intents. -/
inductive MixedHistory (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (classify : WalIntent → Bool) (initialData : DataSnapshot hash) :
    DataSnapshot hash → State Ct → Prop
  | start (empty : initialData.model.journal=[])
      (opened : initialData.canonicalBytes selected.stateId=(stateStream ct).encode initial)
      (genesis : initialData.canonicalBytes selected.genesisId=selected.genesisBytes) :
      MixedHistory ct hash admit W selected classify initialData initialData initial
  | learn {before : DataSnapshot hash} {logical : State Ct}
      (past : MixedHistory ct hash admit W selected classify initialData before logical)
      (p : WindowPlan ct hash W) (current : p.beforeState=logical)
      (opened : p.plan.opens selected before=true)
      (checked : check ct.toLawful admit W p.beforeState p.command=true)
      (tagged : classify p.plan.intent.erase=true)
      (ready : p.plan.intent.preflight before=.ok ())
      (fresh : Snapshot.lookupRecorded p.plan.transactionId before.model.journal=none) :
      MixedHistory ct hash admit W selected classify initialData
        (DataSnapshot.install before p.plan.intent) (advance W p.beforeState p.command)
  | frame {before : DataSnapshot hash} {logical : State Ct}
      (past : MixedHistory ct hash admit W selected classify initialData before logical)
      (intent : DataIntent hash) (tagged : classify intent.erase=false)
      (framed : framesSelected selected before intent=true)
      (ready : intent.preflight before=.ok ())
      (fresh : Snapshot.lookupRecorded intent.transactionId before.model.journal=none) :
      MixedHistory ct hash admit W selected classify initialData
        (DataSnapshot.install before intent) logical

/-- Statement-first apex: arbitrary valid interleavings preserve the exact
window algebra and provenance, while only admission-projected entries count
as learning steps. The total authority journal may have additional entries. -/
def MixedInvariant (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (classify : WalIntent → Bool) : Prop :=
  ∀ initialData data logical,MixedHistory ct hash admit W selected classify initialData data logical →
    data.canonicalBytes selected.stateId=(stateStream ct).encode logical ∧
    data.canonicalBytes selected.genesisId=selected.genesisBytes ∧
    logical.nextId=admissionCount classify data ∧ Reachable ct.toLawful admit W logical ∧
    SumBound W logical ∧ Provenance ct.toLawful admit logical

theorem mixed_invariant (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (classify : WalIntent → Bool) : MixedInvariant ct hash admit W selected classify := by
  intro initialData data logical h
  induction h with
  | start empty opened genesis =>
    refine ⟨opened,genesis,?_,.start,?_,?_⟩
    · simp [initial,admissionCount,admissionProjection,empty]
    · simp [initial,SumBound,queueSum]
    · simp [initial,Provenance]
  | @learn before logical past p current opened checked tagged ready fresh ih =>
    have hop := (p.plan.opens_iff selected before).mp opened
    have reached : Reachable ct.toLawful admit W (advance W p.beforeState p.command) :=
      .next (by simpa only [current] using ih.2.2.2.1) p.command checked
    have inv := window_invariant ct.toLawful admit W _ reached
    refine ⟨?_,?_,?_,reached,inv.1,inv.2⟩
    · rw [←hop.2.1]
      exact (p.plan.installed_exact before).1.trans p.postOpening
    · have kept : (DataSnapshot.install before p.plan.intent).canonicalBytes p.plan.genesisId=
          before.canonicalBytes p.plan.genesisId := p.plan.installed_genesis before
      simpa only [hop.1] using kept.trans (by simpa only [hop.1] using ih.2.1)
    · rw [checked_next_id ct.toLawful admit W p.beforeState p.command checked,current,
        ih.2.2.1,count_admission classify before p.plan.intent tagged]
  | @frame before logical past intent tagged framed ready fresh ih =>
    have kept := (framesSelected_iff selected before intent).mp framed
    refine ⟨kept.1.trans ih.1,kept.2.trans ih.2.1,?_,ih.2.2.2.1,ih.2.2.2.2.1,ih.2.2.2.2.2⟩
    rw [count_frame classify before intent tagged]
    exact ih.2.2.1

theorem mixed_queue_sum (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (classify : WalIntent → Bool) (initialData data : DataSnapshot hash) (logical : State Ct)
    (h : MixedHistory ct hash admit W selected classify initialData data logical) :
    logical.accumulator=(logical.queue.map Entry.ciphertext).sum ∧ logical.queue.length≤W ∧
    logical.nextId=admissionCount classify data := by
  have inv := mixed_invariant ct hash admit W selected classify initialData data logical h
  exact ⟨inv.2.2.2.2.1.1,inv.2.2.2.2.1.2,inv.2.2.1⟩

/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.projection_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms projection_install
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.count_admission' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms count_admission
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.count_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms count_frame
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.frameCheck_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms frameCheck_iff
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.framesSelected_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms framesSelected_iff
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.changed_window_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms changed_window_refused
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.noncanonical_tag_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms noncanonical_tag_refused
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.mixed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixed_invariant
/-- info: 'Minidregg.Assurance.CiphertextWindowFrame.mixed_queue_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixed_queue_sum

end Minidregg.Assurance.CiphertextWindowFrame
