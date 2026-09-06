/- [DERIVED target] A canonical PUBLIC ciphertext queue/accumulator cell.
The codec is built from the repository streaming-codec product/list nucleus.
Ciphertext arrays remain logical group objects; digest roots are arbitrary.
No plaintext, decryption credential, new FS protocol or Rust serde refinement. -/
import Theory.CiphertextWindow
import Assurance.ResidentDurableIntegration

namespace Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CellState
open Minidregg.Theory.CiphertextWindow
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Assurance.ResidentDurableIntegration (Selection Plan)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot)
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

variable {Ct : Type}

/-- Canonical logical modular coefficients; arbitrary positive modulus,
not a claim that the implementation is one flat coefficient-domain array. -/
def coeffStream (q : Nat) [NeZero q] : StreamCodec (ZMod q) :=
  StreamCodec.xmap StreamCodec.nat ZMod.val (fun n=>(n : ZMod q))
    (by intro value;exact ZMod.natCast_zmod_val value)

def vectorStream {A : Type} [Inhabited A] (n : Nat) (c : StreamCodec A) : StreamCodec (Fin n → A) :=
  StreamCodec.xmap (StreamCodec.list c) List.ofFn (fun ls i=>ls.getD i.val default)
    (by intro value;funext i;simp [i.isLt])

def ciphertextStream (q n : Nat) [NeZero q] : StreamCodec (Fin 2 → Fin n → ZMod q) :=
  vectorStream 2 (vectorStream n (coeffStream q))


def entryStream (ct : StreamCodec Ct) : StreamCodec (Entry Ct) :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat ct)
    (fun e=>(e.admissionId,e.ciphertext)) (fun e=>⟨e.1,e.2⟩) (by intro e;cases e;rfl)

def stateStream (ct : StreamCodec Ct) : StreamCodec (State Ct) :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.list (entryStream ct))
    (StreamCodec.product ct StreamCodec.nat))
    (fun s=>(s.queue,s.accumulator,s.nextId)) (fun s=>⟨s.1,s.2.1,s.2.2⟩)
    (by intro s;cases s;rfl)

/-- The one resource is total. Trivial authority/evidence carry no custody or
input-validity claim; admission is the separate checked byte predicate. -/
def schema (Ct : Type) : Schema.{0,0,0,0} where
  Field:=Empty
  FieldType:=fun f=>f.elim
  Resource:=Unit
  ResourceType:=fun _=>State Ct
  Authority:=fun _ _=>Unit
  Evidence:=fun _ _ _=>Unit
instance : DecidableEq (schema Ct).Field := fun f=>f.elim
instance : DecidableEq (schema Ct).Resource := inferInstanceAs (DecidableEq Unit)

def stateOf (s : State Ct) : LogicalState (schema Ct) where
  fields:=0
  resources:=fun _=>⟨s,(),()⟩
def stateValue (s : LogicalState (schema Ct)) : State Ct := (s.resources ()).value

theorem state_ext (s : LogicalState (schema Ct)) : s=stateOf (stateValue s) := by
  cases s with
  | mk fields resources =>
    have hf : fields=(0 : FieldStore (schema Ct)) := by
      apply DFinsupp.ext;intro f;exact f.elim
    have hr : resources=fun _=>⟨(resources ()).value,(),()⟩ := by
      funext r;cases r
      cases resources () with
      | mk value authority evidence => cases authority;cases evidence;rfl
    rw [hf,hr];rfl

def logicalStream (ct : StreamCodec Ct) : StreamCodec (LogicalState (schema Ct)) :=
  StreamCodec.xmap (stateStream ct) stateValue stateOf (fun s=>(state_ext s).symm)

def materializer (ct : StreamCodec Ct) (hash : List UInt8 → Digest) : Materializer (schema Ct) Digest :=
  ⟨(logicalStream ct).toLawful,hash⟩

def cell (ct : StreamCodec Ct) (hash : List UInt8 → Digest) (s : State Ct) :=
  materialize (materializer ct hash) (stateOf s)

theorem canonical_state_opens (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (s : Materialized (materializer ct hash)) (logical : State Ct)
    (h : s.bytes=(stateStream ct).encode logical) : stateValue s.logical=logical := by
  have hd := congrArg (stateStream ct).toLawful.decode h
  change (stateStream ct).toLawful.decode ((stateStream ct).toLawful.encode (stateValue s.logical))=
    (stateStream ct).toLawful.decode ((stateStream ct).toLawful.encode logical) at hd
  rw [(stateStream ct).toLawful.decode_encode,(stateStream ct).toLawful.decode_encode] at hd
  exact Option.some.inj hd

def writePatch (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (pre : Materialized (materializer ct hash)) (post : State Ct) : Patch (schema Ct) Digest where
  expectedPreRoot:=pre.root
  fieldFootprint:=∅
  resourceFootprint:={()}
  fieldWrites:=[]
  resourceWrites:=[⟨(),⟨post,(),()⟩⟩]

theorem writePatch_accepted (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (pre : Materialized (materializer ct hash)) (post : State Ct) :
    ∃ v : ValidatedPatch (materializer ct hash) pre (writePatch ct hash pre post),
      validate (materializer ct hash) pre (writePatch ct hash pre post)=.accepted v := by
  unfold validate
  rw [dif_pos (show (writePatch ct hash pre post).expectedPreRoot=pre.root from rfl)]
  rw [dif_pos (show (writePatch ct hash pre post).fieldFootprint=(writePatch ct hash pre post).namedFields from rfl)]
  rw [dif_pos (show (writePatch ct hash pre post).resourceFootprint=(writePatch ct hash pre post).namedResources from rfl)]
  exact ⟨_,rfl⟩

theorem patch_post (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (pre : Materialized (materializer ct hash)) (post : State Ct)
    (v : ValidatedPatch (materializer ct hash) pre (writePatch ct hash pre post)) :
    stateValue v.apply.logical=post ∧ v.apply.bytes=(stateStream ct).encode post := by
  constructor <;> rfl

variable [AddCommGroup Ct]

/-- An existing materialized plan whose canonical resource bytes exactly open
the source and the proposed checked window transition. -/
structure WindowPlan (ct : StreamCodec Ct) (hash : List UInt8 → Digest) (W : Nat) where
  plan : Plan (materializer ct hash)
  beforeState : State Ct
  command : Command Ct
  preOpening : plan.pre.bytes=(stateStream ct).encode beforeState
  postOpening : plan.post.bytes=(stateStream ct).encode (advance W beforeState command)

/-- No Stage0/EMA arithmetic receipt is reused. This is the exact typed bridge
from the public window relation into the existing full DataIntent installation. -/
def MaterializedWindowBinding (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) : Prop :=
  ∀ selected before (p : WindowPlan ct hash W),
    p.plan.opens selected before=true →
    Reachable ct.toLawful admit W p.beforeState →
    check ct.toLawful admit W p.beforeState p.command=true →
    p.plan.intent.preflight before=.ok () →
    Snapshot.lookupRecorded p.plan.transactionId before.model.journal=none →
    ∃ after,
      execute .complete before p.plan.intent=.accepted after ∧
      before.canonicalBytes p.plan.stateId=(stateStream ct).encode p.beforeState ∧
      after.canonicalBytes p.plan.stateId=(stateStream ct).encode (advance W p.beforeState p.command) ∧
      stateValue p.plan.pre.logical=p.beforeState ∧
      stateValue p.plan.post.logical=advance W p.beforeState p.command ∧
      SumBound W (stateValue p.plan.post.logical) ∧
      Provenance ct.toLawful admit (stateValue p.plan.post.logical) ∧
      p.plan.context.next=(after.model.roots p.plan.stateId).value

theorem materialized_window_binding (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) :
    MaterializedWindowBinding ct hash admit W := by
  intro selected before p opened reached checked ready fresh
  have hop := (p.plan.opens_iff selected before).mp opened
  have hp := canonical_state_opens ct hash p.plan.pre p.beforeState p.preOpening
  have hn := canonical_state_opens ct hash p.plan.post (advance W p.beforeState p.command) p.postOpening
  have reachedPost : Reachable ct.toLawful admit W (advance W p.beforeState p.command) :=
    .next reached p.command checked
  have invariant := window_invariant ct.toLawful admit W _ reachedPost
  refine ⟨DataSnapshot.install before p.plan.intent,
    execute_complete_ready before p.plan.intent fresh ready,hop.2.2.2.2.1.trans p.preOpening,
    (p.plan.installed_exact before).1.trans p.postOpening,hp,hn,?_,?_,?_⟩
  · rw [hn];exact invariant.1
  · rw [hn];exact invariant.2
  · exact hop.2.2.2.2.2.2.2.1.trans (congrArg Digest.value (p.plan.installed_exact before).2.symm)


/-- Refinement of the existing data-execution history by an exact logical
window state. Initial storage really contains the empty queue and empty
journal; every edge is the same existing install justified by full preflight.
No independent mutable head, queue history or counter can be supplied. -/
inductive ExecutedHistory (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (initialData : DataSnapshot hash) : DataSnapshot hash → State Ct → Prop
  | start (empty : initialData.model.journal=[])
      (opened : initialData.canonicalBytes selected.stateId=(stateStream ct).encode initial) :
      ExecutedHistory ct hash admit W selected initialData initialData initial
  | next {before : DataSnapshot hash} {logical : State Ct}
      (past : ExecutedHistory ct hash admit W selected initialData before logical)
      (p : WindowPlan ct hash W) (current : p.beforeState=logical)
      (opened : p.plan.opens selected before=true)
      (checked : check ct.toLawful admit W p.beforeState p.command=true)
      (ready : p.plan.intent.preflight before=.ok ())
      (fresh : Snapshot.lookupRecorded p.plan.transactionId before.model.journal=none) :
      ExecutedHistory ct hash admit W selected initialData
        (DataSnapshot.install before p.plan.intent) (advance W p.beforeState p.command)

/-- Arbitrarily many accepted window transitions are tied to the actual
materialized data/journal carrier. Counter equality rules out a detached
logical history with a forged smaller durable journal. -/
theorem executed_history_invariant (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (initialData data : DataSnapshot hash) (logical : State Ct)
    (h : ExecutedHistory ct hash admit W selected initialData data logical) :
    data.canonicalBytes selected.stateId=(stateStream ct).encode logical ∧
    logical.nextId=data.model.journal.length ∧ Reachable ct.toLawful admit W logical ∧
    SumBound W logical ∧ Provenance ct.toLawful admit logical := by
  induction h with
  | start empty opened =>
    refine ⟨opened,?_,.start,?_,?_⟩
    · simp [initial,empty]
    · simp [initial,SumBound,queueSum]
    · simp [initial,Provenance]
  | @next before logical past p current opened checked ready fresh ih =>
    have hop := (p.plan.opens_iff selected before).mp opened
    have reached : Reachable ct.toLawful admit W (advance W p.beforeState p.command) :=
      .next (by simpa only [current] using ih.2.2.1) p.command checked
    have inv := window_invariant ct.toLawful admit W _ reached
    refine ⟨?_,?_,reached,inv.1,inv.2⟩
    · rw [←hop.2.1]
      exact (p.plan.installed_exact before).1.trans p.postOpening
    · rw [checked_next_id ct.toLawful admit W p.beforeState p.command checked,current,ih.2.1]
      rfl

/-- Forgetting the logical refinement gives the already-existing durable
reachability relation, retaining its genesis/frame/atomicity obligations. -/
theorem executed_is_durable_reachable (ct : StreamCodec Ct) (hash : List UInt8 → Digest)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (selected : Selection)
    (initialData data : DataSnapshot hash) (logical : State Ct)
    (h : ExecutedHistory ct hash admit W selected initialData data logical) :
    Minidregg.Assurance.ResidentDurableIntegration.DurableReachable (M:=materializer ct hash) selected initialData data := by
  induction h with
  | start _ _ => exact .start
  | next _ p _ opened _ ready fresh ih => exact .commit ih p.plan opened ready fresh

/-- info: 'Minidregg.Assurance.CiphertextWindowCell.state_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms state_ext
/-- info: 'Minidregg.Assurance.CiphertextWindowCell.canonical_state_opens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms canonical_state_opens
/-- info: 'Minidregg.Assurance.CiphertextWindowCell.writePatch_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms writePatch_accepted
/-- info: 'Minidregg.Assurance.CiphertextWindowCell.patch_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms patch_post
/-- info: 'Minidregg.Assurance.CiphertextWindowCell.materialized_window_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms materialized_window_binding
/-- info: 'Minidregg.Assurance.CiphertextWindowCell.executed_history_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executed_history_invariant
/-- info: 'Minidregg.Assurance.CiphertextWindowCell.executed_is_durable_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executed_is_durable_reachable

end Minidregg.Assurance.CiphertextWindowCell
