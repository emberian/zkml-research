/-
[DERIVED target; EXECUTED after source-matching compilation]
Statement-first: a context-linked accepted receipt and exact independently
selected genesis/current canonical openings, entering the existing full data
preflight and execute path, install exactly the validated materialized post.
The receipt's next equals that installed root's Nat value. The closed witness
is the EXISTING Bool cell, false -> true, and its EXISTING validator-minted
patch. Its root is the encoded byte, NOT a cryptographic commitment.

ATLAS witness: Closed.ready, Closed.subject; one nonempty write, one genesis
read guard, nonzero exact charge, spent slot token, actual Candidate.ofData and
FinalityGate, real Stage-0 FS receipt. Teeth: wrong openings/next refused,
crash-before/after, exact retry packet, stale current state, authority rollback,
and the broken split check/install schedule. The physical implementation must
still realize DurableDataIntent.ImplementationRefinement. No hiding, secret
entropy, actual encrypted-root opening descriptor, transport, or new ROM price.
-/
import Assurance.ResidentReleaseContext
import Kernel.FinalityGate
import Kernel.GuardedDurableCommit
import Theory.CellStateWitness

namespace Minidregg.Assurance.ResidentDurableIntegration

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot Intent Schedule)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Assurance.ResidentReleaseContext
open Minidregg.Compiler.CommittedTerminalFiatShamir (FsReceipt)
open Minidregg.Compiler.CommittedTerminalFiatShamir (fsProve fsCheck fsProve_complete)
open Minidregg.Compiler.CommittedTerminalRealizer (Ext6L)
open Minidregg.Compiler.CommittedTerminalRealizer (traceOf)
open Minidregg.Compiler.CommittedTerminalRealizer.Stage0Exhibit (wordOf stage0_residuals_fit)
open Minidregg.Compiler.CommittedTerminalRealizer (residualEmbedding bitCorner)
open Minidregg.Compiler.DescriptorEval (evmAddCandidate evmAddCandidate_holds evmAddCandidate_pins)
open Minidregg.Compiler (descriptorHolds)
open Minidregg.Compiler.EvmAddAir (evmAddDescriptor encodeBoundary)
open Minidregg.Assurance.ReleaseGateRouting (traceOf_wordOf_candidate)
open Minidregg.Selvage (SrMove)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)

set_option autoImplicit false

abbrev WalIntent := Intent TransactionId CellId StableNullifier ReplayEnvelope
abbrev Proposal := Candidate TransactionId CellId StableNullifier ReplayEnvelope

/-- Expose the word equality of the existing constructive FS prover, so the
descriptor premise is inhabited by the SAME accepted receipt in the apex. -/
theorem receipt_retains_proved_word (c : Context) (w : Word)
    (O : SrMove (reduction c) 0 → Ext6L) (linked : Linked c w)
    (descriptor : descriptorHolds evmAddDescriptor (traceOf w)) :
    ∃ rc : FsReceipt Root 4131 13, check c O rc = true ∧ rc.word = w := by
  let rc := fsProve (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num) O ((S c).commit w) w
  have complete := fsProve_complete (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num : 0 < 4131) O w
    (residualEmbedding evmAddDescriptor (traceOf w) stage0_residuals_fit)
    (fun _ => rfl) descriptor
  refine ⟨rc, ?_, rfl⟩
  unfold check
  have root : rc.root.1 = c := rfl
  have word : rc.word = w := rfl
  rw [decide_eq_true root, word, decide_eq_true linked]
  change (match fsCheck (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num) O rc with | .ok _ => true | .error _ => false) = true
  rw [complete]

/-- Independent selected genesis and active state cell, with exact genesis
bytes. The host manifest does not select these values. -/
structure Selection where
  genesisId : Digest
  stateId : Digest
  genesisBytes : List UInt8
  authorization : Nat
  recipient : Nat

/-- The post can only be produced by an existing validated typed patch. -/
structure Plan {schema : Schema} [DecidableEq schema.Field]
    [DecidableEq schema.Resource] (M : Materializer schema Digest) where
  transactionId : Digest
  genesisId : Digest
  stateId : Digest
  distinct : genesisId ≠ stateId
  genesis : Materialized M
  pre : Materialized M
  patch : Patch schema Digest
  validated : ValidatedPatch M pre patch
  context : Context
  prior : List WalIntent
  epoch : Nat

namespace Plan
variable {schema : Schema} [DecidableEq schema.Field] [DecidableEq schema.Resource]
variable {M : Materializer schema Digest}

def post (p : Plan M) : Materialized M := p.validated.apply

def token (p : Plan M) : StableNullifier :=
  ⟨1, ⟨101⟩, p.genesisId,
    (StreamCodec.list StreamCodec.nat).encode [p.genesisId.value, p.prior.length]⟩

/-- The exact context bytes are the replay packet, including recipient/output.
This public packet is neither encryption nor a randomized rerun. -/
def packet (p : Plan M) : StableEvent :=
  ⟨1, ⟨102⟩, p.transactionId,
    (StreamCodec.list StreamCodec.nat).encode (contextWords p.context)⟩

def intent (p : Plan M) : DataIntent M.rootBytes where
  transactionId := p.transactionId
  writes := [⟨p.stateId, p.pre.root, p.post.root, p.post.bytes⟩]
  readGuards := [⟨p.genesisId, p.genesis.root⟩]
  nullifiers := [p.token]
  exactCharge := fun _ => 1
  event := p.packet
  postRootsBound := by
    intro write member
    simp only [List.mem_singleton] at member
    subst write
    rfl
  guardsReadOnly := by
    intro guard member
    simp only [List.mem_singleton] at member
    subst guard
    simpa using p.distinct

def candidate (p : Plan M) : Proposal := Candidate.ofData p.epoch p.prior p.intent

/-- Equal roots do not imply equal logical openings. Exact bytes are checked
at both reads, without any hash-injectivity premise. -/
def opens (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) : Bool :=
  decide (p.genesisId = selected.genesisId ∧ p.stateId = selected.stateId ∧
    p.genesis.bytes = selected.genesisBytes ∧
    before.canonicalBytes p.genesisId = p.genesis.bytes ∧
    before.canonicalBytes p.stateId = p.pre.bytes ∧
    p.context.genesis = p.genesisId.value ∧
    p.context.parent = p.pre.root.value ∧ p.context.next = p.post.root.value ∧
    p.prior = before.model.journal.reverse.map Prod.snd)

def Openings (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) : Prop :=
  p.genesisId = selected.genesisId ∧ p.stateId = selected.stateId ∧
    p.genesis.bytes = selected.genesisBytes ∧
    before.canonicalBytes p.genesisId = p.genesis.bytes ∧
    before.canonicalBytes p.stateId = p.pre.bytes ∧
    p.context.genesis = p.genesisId.value ∧
    p.context.parent = p.pre.root.value ∧ p.context.next = p.post.root.value ∧
    p.prior = before.model.journal.reverse.map Prod.snd

theorem opens_iff (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) : p.opens selected before = true ↔ p.Openings selected before := by
  simp only [opens, Openings, decide_eq_true_eq]

theorem installed_exact (before : DataSnapshot M.rootBytes) (p : Plan M) :
    (DataSnapshot.install before p.intent).canonicalBytes p.stateId = p.post.bytes ∧
    (DataSnapshot.install before p.intent).model.roots p.stateId = p.post.root := by
  constructor <;> simp [DataSnapshot.install, DataSnapshot.lookupPostBytes,
    intent, DataIntent.erase, Snapshot.install, Snapshot.lookupPost]

theorem installed_consumed (before : DataSnapshot M.rootBytes) (p : Plan M) :
    (DataSnapshot.install before p.intent).model.consumed p.token = true := by
  exact Snapshot.install_consumes before.model p.intent.erase p.token (by simp [intent])

theorem installed_genesis (before : DataSnapshot M.rootBytes) (p : Plan M) :
    (DataSnapshot.install before p.intent).canonicalBytes p.genesisId =
      before.canonicalBytes p.genesisId := by
  exact (Minidregg.Kernel.GuardedDurableCommit.install_preserves_read_guard
    before p.intent ⟨p.genesisId, p.genesis.root⟩ (by simp [intent])).2

theorem exact_retry (schedule : Schedule) (before : DataSnapshot M.rootBytes)
    (p : Plan M) :
    execute schedule (DataSnapshot.install before p.intent) p.intent =
      .replayed p.intent.erase := by
  simp [execute, DataSnapshot.install, Snapshot.install, Snapshot.lookupRecorded]

theorem replay_packet (p : Plan M) : p.intent.erase.event.event = p.packet := rfl

theorem packet_binds_context (p r : Plan M) (equal : p.packet = r.packet) :
    p.context = r.context := by
  have bytes := congrArg StableEvent.canonicalBytes equal
  exact contextWords_injective
    (Minidregg.Compiler.CommittedTerminalFiatShamir.streamEncode_injective
      (StreamCodec.list StreamCodec.nat) bytes)

/-- A retry cannot substitute a recipient, output, or other context field
while retaining the same transaction id, even with colliding post roots. -/
theorem same_id_changed_packet_refused (schedule : Schedule)
    (before : DataSnapshot M.rootBytes) (p r : Plan M)
    (sameId : r.transactionId = p.transactionId) (different : p.packet ≠ r.packet) :
    execute schedule (DataSnapshot.install before p.intent) r.intent =
      .rejected (.durable .transactionConflict) := by
  have notSame : p.intent.erase.sameCheck r.intent.erase = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    have payload := (DataIntent.erase_sameCheck_eq_true_iff p.intent r.intent).mp same
    exact different payload.2.2.2.2
  have ids : r.intent.transactionId = p.intent.transactionId := sameId
  unfold execute
  have lookup : Snapshot.lookupRecorded r.intent.transactionId
      (DataSnapshot.install before p.intent).model.journal = some p.intent.erase := by
    change Snapshot.lookupRecorded r.intent.transactionId
      (Snapshot.install before.model p.intent.erase).journal = some p.intent.erase
    rw [ids]
    exact Snapshot.lookupRecorded_install before.model p.intent.erase
  simp only [lookup, notSame, Bool.false_eq_true, ↓reduceIte]

theorem wrong_next_refused (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) (wrong : p.context.next ≠ p.post.root.value) :
    p.opens selected before = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact wrong ((p.opens_iff selected before).mp h).2.2.2.2.2.2.2.1

theorem changed_parent_refused (selected : Selection)
    (before : DataSnapshot M.rootBytes) (p : Plan M)
    (changed : p.post.bytes ≠ p.pre.bytes) :
    p.opens selected (DataSnapshot.install before p.intent) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have same := ((p.opens_iff selected _).mp h).2.2.2.2.1
  rw [(p.installed_exact before).1] at same
  exact changed same

/-- This current-prefix refusal also covers no-op state updates. -/
theorem installed_prefix_refused (selected : Selection)
    (before : DataSnapshot M.rootBytes) (p : Plan M)
    (current : p.opens selected before = true) :
    p.opens selected (DataSnapshot.install before p.intent) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have old := ((p.opens_iff selected before).mp current).2.2.2.2.2.2.2.2
  have fresh := ((p.opens_iff selected _).mp h).2.2.2.2.2.2.2.2
  have ho := congrArg List.length old
  have hn := congrArg List.length fresh
  simp only [DataSnapshot.install, Snapshot.install, List.reverse_cons,
    List.map_append, List.map_cons, List.map_nil, List.length_append,
    List.length_cons, List.length_nil, List.length_map, List.length_reverse] at hn
  simp only [List.length_map, List.length_reverse] at ho
  omega

end Plan

section Reachability
variable {schema : Schema} [DecidableEq schema.Field] [DecidableEq schema.Resource]
variable {M : Materializer schema Digest}

/-- A structural durable-reachability invariant, using the actual executable
data step. It rules out freely replacing roots or journal fields between
commits. Cryptographic authorization remains the separate `authorized` gate;
a physical authority must establish that its snapshots follow this history. -/
inductive DurableReachable (selected : Selection) (initial : DataSnapshot M.rootBytes) :
    DataSnapshot M.rootBytes → Prop
  | start : DurableReachable selected initial initial
  | commit {before : DataSnapshot M.rootBytes}
      (previous : DurableReachable selected initial before) (p : Plan M)
      (opened : p.opens selected before = true)
      (ready : p.intent.preflight before = .ok ())
      (fresh : Snapshot.lookupRecorded p.transactionId before.model.journal = none) :
      DurableReachable selected initial (DataSnapshot.install before p.intent)

theorem reachable_preserves_genesis (selected : Selection)
    (initial after : DataSnapshot M.rootBytes)
    (reached : DurableReachable selected initial after) :
    after.canonicalBytes selected.genesisId = initial.canonicalBytes selected.genesisId := by
  induction reached with
  | start => rfl
  | commit previous p opened ready fresh ih =>
      have sameId := ((p.opens_iff selected _).mp opened).1
      rw [← sameId, p.installed_genesis]
      simpa only [sameId] using ih

theorem reachable_journal_monotone (selected : Selection)
    (initial after : DataSnapshot M.rootBytes)
    (reached : DurableReachable selected initial after) :
    initial.model.journal.length ≤ after.model.journal.length := by
  induction reached with
  | start => exact Nat.le_refl _
  | commit previous p opened ready fresh ih =>
      change _ ≤ _ + 1
      omega

end Reachability

section Binding
variable {schema : Schema} [DecidableEq schema.Field] [DecidableEq schema.Resource]
variable {M : Materializer schema Digest}
variable {Node : Type} [DecidableEq Node]
variable (q : QuorumSystem Node) [DecidablePred q.isQuorum]
variable (book : VoteBook (Node := Node) (TxId := TransactionId) (CellId := CellId)
  (Nullifier := StableNullifier) (Event := ReplayEnvelope))

/-- Only fresh authorization is checked here; exact lost-response retry goes
through the existing journal-first execute path, as Plan.exact_retry proves. -/
def authorized (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13) : Bool :=
  Minidregg.Kernel.FinalityGate.check q book p.candidate cert &&
    p.opens selected before && check p.context O rc &&
    decide (p.context.authorization = selected.authorization ∧
      p.context.recipient = selected.recipient)

inductive GatedOutcome (rootBytes : List UInt8 → Digest)
  | gateRefused
  | durable (outcome : Outcome rootBytes)

/-- A thin adapter over the existing executor, not a second store machine.
Journal lookup is first: retries may recover the exact committed old packet,
while every fresh attempt passes context/finality before full data preflight. -/
def gatedExecute (schedule : Schedule) (selected : Selection)
    (before : DataSnapshot M.rootBytes) (p : Plan M)
    (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13) :
    GatedOutcome M.rootBytes :=
  match Snapshot.lookupRecorded p.transactionId before.model.journal with
  | some _ => .durable (execute schedule before p.intent)
  | none =>
      if authorized q book selected before p cert O rc then
        .durable (execute schedule before p.intent)
      else .gateRefused

/-- The caller cannot relabel a successful result with another Plan. Fresh
packets come from the installed journal head; retries from the recorded intent. -/
def releasedPacket {rootBytes : List UInt8 → Digest} :
    GatedOutcome rootBytes → Option StableEvent
  | .durable (.accepted after) => after.model.journal.head?.map (fun entry => entry.2.event.event)
  | .durable (.replayed recorded) => some recorded.event.event
  | _ => none

theorem released_packet_after_install (before : DataSnapshot M.rootBytes) (p : Plan M) :
    releasedPacket (.durable (.accepted (DataSnapshot.install before p.intent))) =
      some p.packet := rfl

theorem installed_packet_cannot_be_relabelled (before : DataSnapshot M.rootBytes)
    (p r : Plan M) (different : p.packet ≠ r.packet) :
    releasedPacket (.durable (.accepted (DataSnapshot.install before p.intent))) ≠
      some r.packet := by
  rw [released_packet_after_install]
  exact fun equal => different (Option.some.inj equal)

theorem gated_commit_ready (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (approved : authorized q book selected before p cert O rc = true)
    (ready : p.intent.preflight before = .ok ())
    (fresh : Snapshot.lookupRecorded p.transactionId before.model.journal = none) :
    gatedExecute q book .complete selected before p cert O rc =
      .durable (.accepted (DataSnapshot.install before p.intent)) := by
  simp only [gatedExecute, fresh, approved, ↓reduceIte]
  rw [execute_complete_ready before p.intent fresh ready]

theorem gated_retry_exact (schedule : Schedule) (selected : Selection)
    (before : DataSnapshot M.rootBytes) (p : Plan M)
    (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13) :
    gatedExecute q book schedule selected (DataSnapshot.install before p.intent)
      p cert O rc = .durable (.replayed p.intent.erase) := by
  have lookup : Snapshot.lookupRecorded p.transactionId
      (DataSnapshot.install before p.intent).model.journal = some p.intent.erase :=
    Snapshot.lookupRecorded_install before.model p.intent.erase
  simp only [gatedExecute, lookup]
  rw [p.exact_retry schedule before]

theorem fresh_unapproved_refused (schedule : Schedule) (selected : Selection)
    (before : DataSnapshot M.rootBytes) (p : Plan M)
    (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (unapproved : authorized q book selected before p cert O rc = false)
    (fresh : Snapshot.lookupRecorded p.transactionId before.model.journal = none) :
    gatedExecute q book schedule selected before p cert O rc = .gateRefused := by
  simp only [gatedExecute, fresh, unapproved, Bool.false_eq_true, ↓reduceIte]

theorem consume_before_packet (selected : Selection) (before : DataSnapshot M.rootBytes)
    (p : Plan M) (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (approved : authorized q book selected before p cert O rc = true)
    (ready : p.intent.preflight before = .ok ())
    (fresh : Snapshot.lookupRecorded p.transactionId before.model.journal = none) :
    releasedPacket (gatedExecute q book .complete selected before p cert O rc) = some p.packet ∧
    (DataSnapshot.install before p.intent).model.consumed p.token = true := by
  rw [gated_commit_ready q book selected before p cert O rc approved ready fresh]
  exact ⟨rfl, p.installed_consumed before⟩

/-- Statement-first keystone. The only store transition is the existing
DurableDataIntent.execute; the adapter contributes materialized semantics. -/
def MaterializedDurableBinding : Prop :=
  ∀ selected before (p : Plan M) cert O rc,
    authorized q book selected before p cert O rc = true →
    p.intent.preflight before = .ok () →
    Snapshot.lookupRecorded p.transactionId before.model.journal = none →
    ∃ after,
      execute .complete before p.intent = .accepted after ∧
      p.Openings selected before ∧ rc.root.1 = p.context ∧
      p.context.authorization = selected.authorization ∧
      p.context.recipient = selected.recipient ∧
      after.canonicalBytes p.stateId = p.post.bytes ∧
      after.model.roots p.stateId = p.post.root ∧
      rc.root.1.next = (after.model.roots p.stateId).value ∧
      after.model.consumed p.token = true

theorem materialized_durable_binding : MaterializedDurableBinding q book (M := M) := by
  intro selected before p cert O rc accepted ready fresh
  simp only [authorized, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have opened := (p.opens_iff selected before).mp accepted.1.1.2
  have context := context_binding p.context O rc accepted.1.2
  have installed := p.installed_exact before
  refine ⟨DataSnapshot.install before p.intent,
    execute_complete_ready before p.intent fresh ready, opened, context,
    accepted.2.1, accepted.2.2,
    installed.1, installed.2, ?_, p.installed_consumed before⟩
  rw [context, installed.2]
  exact opened.2.2.2.2.2.2.2.1

/-- The arithmetic leg keeps descriptor satisfaction explicit. This is the
proper composed conclusion; receipt acceptance alone is not asserted to make
every Fiat-Shamir statement true outside its probabilistic soundness game. -/
theorem authorized_materialized_arithmetic (selected : Selection)
    (before : DataSnapshot M.rootBytes) (p : Plan M)
    (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (accepted : authorized q book selected before p cert O rc = true)
    (ready : p.intent.preflight before = .ok ())
    (fresh : Snapshot.lookupRecorded p.transactionId before.model.journal = none)
    (descriptor : descriptorHolds evmAddDescriptor (traceOf rc.word)) :
    Forced p.context ∧
    gatedExecute q book .complete selected before p cert O rc =
      .durable (.accepted (DataSnapshot.install before p.intent)) ∧
    (DataSnapshot.install before p.intent).canonicalBytes p.stateId = p.post.bytes ∧
    ((DataSnapshot.install before p.intent).model.roots p.stateId).value =
      (p.context.parent + p.context.command) % 2^256 := by
  have parts := accepted
  simp only [authorized, Bool.and_eq_true] at parts
  have forced := arithmetic_binding p.context O rc parts.1.2 descriptor
  have opened := (p.opens_iff selected before).mp parts.1.1.2
  refine ⟨forced, gated_commit_ready q book selected before p cert O rc accepted ready fresh,
    (p.installed_exact before).1, ?_⟩
  rw [(p.installed_exact before).2, ← opened.2.2.2.2.2.2.2.1]
  exact forced.1

/-- The existing finality uniqueness theorem reaches the resident context
through the actual DataIntent replay envelope and its injective encoding. -/
theorem finalized_context_unique (discipline : PrefixDiscipline book)
    (p r : Plan M) (cp cr : Minidregg.Kernel.FinalityGate.Cert Node)
    (hp : Minidregg.Kernel.FinalityGate.check q book p.candidate cp = true)
    (hr : Minidregg.Kernel.FinalityGate.check q book r.candidate cr = true)
    (slot : p.candidate.slot = r.candidate.slot) : p.context = r.context := by
  have same := Minidregg.Kernel.FinalityGate.checked_transaction_unique_at_slot
    q book discipline hp hr slot
  apply p.packet_binds_context r
  exact congrArg (fun i : WalIntent => i.event.event) same

theorem authorized_preserves_reachability (selected : Selection)
    (initial before : DataSnapshot M.rootBytes) (p : Plan M)
    (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.context) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (reached : DurableReachable selected initial before)
    (accepted : authorized q book selected before p cert O rc = true)
    (ready : p.intent.preflight before = .ok ())
    (fresh : Snapshot.lookupRecorded p.transactionId before.model.journal = none) :
    DurableReachable selected initial (DataSnapshot.install before p.intent) := by
  simp only [authorized, Bool.and_eq_true] at accepted
  exact .commit reached p accepted.1.1.2 ready fresh

end Binding

namespace Closed
open Minidregg.Theory.CellStateWitness

def p : Plan materializer where
  transactionId := ⟨91⟩
  genesisId := ⟨7⟩
  stateId := ⟨22⟩
  distinct := by decide
  genesis := cellTrue
  pre := cell
  patch := honestPatch
  validated := honestPatch_accepted.choose
  context := honestContext 0 1
  prior := []
  epoch := 0

def selected : Selection := ⟨⟨7⟩, ⟨22⟩, cellTrue.bytes, 19, 23⟩
def beforeBytes (id : CellId) : List UInt8 :=
  if id = p.genesisId then cellTrue.bytes else cell.bytes
def before : DataSnapshot materializer.rootBytes where
  model := ⟨fun id => materializer.rootBytes (beforeBytes id),
    fun _ => false, fun _ => 10, [], []⟩
  canonicalBytes := beforeBytes
  coherent := fun _ => rfl

abbrev Node := Fin 3
def q := Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance.quorums
instance : DecidablePred q.isQuorum :=
  Minidregg.Kernel.FinalityGate.ClosedInstance.quorumsDecidable
def book : VoteBook (Node := Node) (TxId := TransactionId) (CellId := CellId)
    (Nullifier := StableNullifier) (Event := ReplayEnvelope) := fun _ => [p.candidate]
def cert : Minidregg.Kernel.FinalityGate.Cert Node := ⟨{0, 1}⟩

theorem ready : p.intent.preflight before = .ok () := by decide
theorem openings : p.opens selected before = true := by decide
theorem finalized : Minidregg.Kernel.FinalityGate.check q book p.candidate cert = true :=
  by decide
theorem changed : p.post.bytes ≠ p.pre.bytes := by decide
theorem one_materialized_write : p.intent.writes.length = 1 := rfl
theorem post_is_true : p.post.logical.fields () = some true := by
  change (some true : Option Bool) = some true
  rfl

/-- In this public Bool witness the canonical values themselves are 0 and 1;
the root equalities derive from the existing one-byte materializer. -/
theorem public_value_openings :
    p.context.parent = 0 ∧ before.canonicalBytes p.stateId = [0] ∧
    p.context.next = 1 ∧
    (DataSnapshot.install before p.intent).canonicalBytes p.stateId = [1] := by decide

theorem reached : DurableReachable selected before (DataSnapshot.install before p.intent) :=
  .commit .start p openings ready rfl

/-- The keystone premises all have a subject, including a real FS receipt. -/
theorem subject (O : SrMove (reduction p.context) 0 → Ext6L) :
    ∃ rc : FsReceipt Root 4131 13,
      authorized q book selected before p cert O rc = true ∧
      p.intent.preflight before = .ok () ∧
      execute .complete before p.intent = .accepted (DataSnapshot.install before p.intent) ∧
      rc.root.1.next = ((DataSnapshot.install before p.intent).model.roots p.stateId).value ∧
      p.post.bytes ≠ p.pre.bytes ∧
      descriptorHolds evmAddDescriptor (traceOf rc.word) := by
  let w := wordOf (evmAddCandidate 0 1)
  have boundary : ∀ i : Fin 48, traceOf w i.val = encodeBoundary 0 1 ((0+1) % 2^256) i := by
    intro i
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_pins 0 1 i
  have descriptor : descriptorHolds evmAddDescriptor (traceOf w) := by
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_holds 0 1 (by norm_num) (by norm_num)
  have linked : Linked p.context w :=
    ⟨by norm_num [p, honestContext], by norm_num [p, honestContext],
      by norm_num [p, honestContext], rfl, rfl, rfl, rfl, rfl, boundary⟩
  obtain ⟨rc, hrc, sameWord⟩ := receipt_retains_proved_word p.context w O linked descriptor
  have ha : authorized q book selected before p cert O rc = true := by
    have policy : decide (p.context.authorization = selected.authorization ∧
        p.context.recipient = selected.recipient) = true := by decide
    simp only [authorized, finalized, openings, policy, Bool.true_and, Bool.and_true]
    exact hrc
  have h := materialized_durable_binding q book selected before p cert O rc ha ready rfl
  obtain ⟨after, he, _, hc, _, _, _, hr, hn, _⟩ := h
  refine ⟨rc, ha, ready, execute_complete_ready before p.intent rfl ready, ?_, changed, ?_⟩
  · rw [hc]
    decide
  · rwa [sameWord]

theorem crash_before : execute (.crash .beforeAtomicInstall) before p.intent =
    .crashed .beforeAtomicInstall before := by
  unfold execute
  have lookup : Snapshot.lookupRecorded p.intent.transactionId before.model.journal = none := rfl
  rw [lookup, ready]

theorem crash_after : execute (.crash .afterAtomicInstall) before p.intent =
    .crashed .afterAtomicInstall (DataSnapshot.install before p.intent) := by
  unfold execute
  have lookup : Snapshot.lookupRecorded p.intent.transactionId before.model.journal = none := rfl
  rw [lookup, ready]

theorem exact_lost_response_retry :
    execute .complete (DataSnapshot.install before p.intent) p.intent =
      .replayed p.intent.erase := p.exact_retry .complete before

theorem restore_refused :
    p.opens selected (DataSnapshot.install before p.intent) = false :=
  p.installed_prefix_refused selected before openings

/-- Rolling back the supposedly independent data authority re-enables fresh
preflight. This is a scoped broken implementation, not encryption recovery. -/
theorem authority_rollback_reaccepts : p.intent.preflight before = .ok () ∧
    p.opens selected before = true := ⟨ready, openings⟩

/-- A distinct transaction naming the same parent and slot-consumption token. -/
def racing : Plan materializer := { p with transactionId := ⟨92⟩ }

/-- Broken sibling: both workers can cache successful preflight at the old
snapshot. Blind installation after the first commit then journals both and
charges twice, although the existing fresh preflight now refuses the second.
This is a falsifier of split check/install, NOT of finality prefix discipline. -/
theorem split_check_install_duplicates :
    p.intent.preflight before = .ok () ∧ racing.intent.preflight before = .ok () ∧
    racing.intent.preflight (DataSnapshot.install before p.intent) =
      .error (.durable .stalePreRoot) ∧
    (DataSnapshot.install (DataSnapshot.install before p.intent) racing.intent).model.journal.length = 2 ∧
    (DataSnapshot.install (DataSnapshot.install before p.intent) racing.intent).model.available
      .feeDebit = 8 := by decide

end Closed
end Minidregg.Assurance.ResidentDurableIntegration


/- Exact-output axiom pins, observed in lean_ResidentDurableIntegration_11.json. -/

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.receipt_retains_proved_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.receipt_retains_proved_word

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.opens_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.opens_iff

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_exact

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_consumed

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_genesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_genesis

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.exact_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.exact_retry

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.replay_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.replay_packet

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.packet_binds_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.packet_binds_context

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.same_id_changed_packet_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.same_id_changed_packet_refused

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.wrong_next_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.wrong_next_refused

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.changed_parent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.changed_parent_refused

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_prefix_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Plan.installed_prefix_refused

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.reachable_preserves_genesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.reachable_preserves_genesis

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.reachable_journal_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.reachable_journal_monotone

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.gated_commit_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.gated_commit_ready

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.gated_retry_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.gated_retry_exact

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.fresh_unapproved_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.fresh_unapproved_refused

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.consume_before_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.consume_before_packet

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.materialized_durable_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.materialized_durable_binding

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.authorized_materialized_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.authorized_materialized_arithmetic

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.finalized_context_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.finalized_context_unique

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.authorized_preserves_reachability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.authorized_preserves_reachability

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.ready

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.openings

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.finalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.finalized

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.changed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.changed

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.one_materialized_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.one_materialized_write

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.post_is_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.post_is_true

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.public_value_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.public_value_openings

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.reached

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.subject

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.crash_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.crash_before

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.crash_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.crash_after

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.exact_lost_response_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.exact_lost_response_retry

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.restore_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.restore_refused

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.authority_rollback_reaccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.authority_rollback_reaccepts

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.Closed.split_check_install_duplicates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.Closed.split_check_install_duplicates

/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.released_packet_after_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.released_packet_after_install
/-- info: 'Minidregg.Assurance.ResidentDurableIntegration.installed_packet_cannot_be_relabelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableIntegration.installed_packet_cannot_be_relabelled
