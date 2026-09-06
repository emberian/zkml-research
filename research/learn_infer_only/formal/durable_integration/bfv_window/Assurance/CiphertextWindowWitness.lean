/- [DERIVED target] Public nonzero ciphertext-vector subjects and exact-expiry
teeth. The canonical codec uses existing streaming products/lists; it is NOT
fhe-dregg protobuf/RNS/NTT serialization. Two group objects with the same toy
linear plaintext image still differ as ciphertexts and must not substitute. -/
import Assurance.CiphertextWindowCell

namespace Minidregg.Assurance.CiphertextWindowWitness
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CellState
open Minidregg.Theory.CiphertextWindow
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Assurance.ResidentDurableIntegration (Selection)
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000


abbrev Ct := Fin 2 → Fin 1 → ZMod 17
def ct : StreamCodec Ct := ciphertextStream 17 1
def a : Ct := fun i _=>(![3,5] : Fin 2 → ZMod 17) i
def b : Ct := fun i _=>(![7,1] : Fin 2 → ZMod 17) i
def c : Ct := fun i _=>(![2,6] : Fin 2 → ZMod 17) i
def rerandomizedA : Ct := fun i _=>(![4,4] : Fin 2 → ZMod 17) i

def admit (id : Nat) (bytes : List UInt8) : Bool :=
  decide (bytes=ct.encode (if id=0 then a else if id=1 then b else c))

def cmd0 : Command Ct := ⟨⟨0,a⟩,none⟩
def s1 : State Ct := advance 2 initial cmd0
def cmd1 : Command Ct := ⟨⟨1,b⟩,none⟩
def s2 : State Ct := advance 2 s1 cmd1
def cmd2 : Command Ct := ⟨⟨2,c⟩,some ⟨0,a⟩⟩
def s3 : State Ct := advance 2 s2 cmd2

theorem checked0 : check ct.toLawful admit 2 initial cmd0=true := by decide +kernel
theorem checked1 : check ct.toLawful admit 2 s1 cmd1=true := by decide +kernel
theorem checked2 : check ct.toLawful admit 2 s2 cmd2=true := by decide +kernel

theorem reached3 : Reachable ct.toLawful admit 2 s3 :=
  .next (.next (.next .start cmd0 checked0) cmd1 checked1) cmd2 checked2

theorem honest_nonzero_add_and_expiry :
    s1.accumulator≠0 ∧ s2.accumulator=a+b ∧ s3.accumulator=b+c ∧
    s3.queue.map Entry.admissionId=[1,2] ∧ s3.nextId=3 ∧
    SumBound 2 s3 ∧ Provenance ct.toLawful admit s3 := by
  have inv := window_invariant ct.toLawful admit 2 s3 reached3
  refine ⟨by decide,by decide,by decide,rfl,rfl,inv.1,inv.2⟩

def wrongExpiry : Command Ct := ⟨cmd2.fresh,some ⟨0,rerandomizedA⟩⟩
def staleExpiry : Command Ct := ⟨cmd2.fresh,some ⟨1,a⟩⟩
def staleFresh : Command Ct := ⟨⟨1,c⟩,cmd2.expiry⟩
def deniedFresh : Command Ct := ⟨⟨2,a⟩,cmd2.expiry⟩

/-- This toy image only illustrates why plaintext equality is insufficient.
It is not BFV decryption or an assumed integer additive phase map. -/
def toyPlain (x : Ct) : ZMod 17 := x 0 0+x 1 0

theorem same_plaintext_different_ciphertext :
    toyPlain a=toyPlain rerandomizedA ∧ a≠rerandomizedA ∧
    ct.encode a≠ct.encode rerandomizedA := by decide +kernel

theorem wrong_serialized_expiry_refused :
    check ct.toLawful admit 2 s2 wrongExpiry=false ∧
    step ct.toLawful admit 2 s2 wrongExpiry=none := by decide +kernel

theorem stale_id_and_denied_input_refused :
    check ct.toLawful admit 2 s2 staleExpiry=false ∧
    check ct.toLawful admit 2 s2 staleFresh=false ∧
    check ct.toLawful admit 2 s2 deniedFresh=false := by decide +kernel

/-- Deliberately bypass the byte check: a same-plaintext replacement leaves
nonzero group debt even when this toy plaintext image initially agrees. -/
theorem bypassed_byte_check_breaks_sum :
    (advance 2 s2 wrongExpiry).accumulator≠queueSum (advance 2 s2 wrongExpiry).queue ∧
    (advance 2 s2 wrongExpiry).accumulator=queueSum (advance 2 s2 wrongExpiry).queue+(a-rerandomizedA) ∧
    toyPlain (advance 2 s2 wrongExpiry).accumulator=toyPlain s3.accumulator := by decide +kernel

/-- A nontrivial state-codec round trip includes the whole queue, accumulator
and next admission counter. It carries ciphertexts only, no plaintext reference. -/
theorem canonical_roundtrip : (stateStream ct).toLawful.decode ((stateStream ct).encode s3)=some s3 :=
  (stateStream ct).toLawful.decode_encode s3

def hash (_ : List UInt8) : Digest := ⟨0⟩
def pre := cell ct hash s2
def post := cell ct hash s3

def wp : WindowPlan ct hash 2 where
  plan:={
    transactionId:=⟨301⟩,genesisId:=⟨7⟩,stateId:=⟨22⟩,distinct:=by decide
    genesis:=cell ct hash initial,pre:=pre,patch:=writePatch ct hash pre s3
    validated:=(writePatch_accepted ct hash pre s3).choose
    context:=⟨7,0,2,1,2,19,23,0,0,0,0⟩,prior:=[],epoch:=0 }
  beforeState:=s2
  command:=cmd2
  preOpening:=rfl
  postOpening:=rfl

def selected : Selection := ⟨⟨7⟩,⟨22⟩,(cell ct hash initial).bytes,19,23⟩
def beforeBytes (id : CellId) : List UInt8 :=
  if id=wp.plan.genesisId then (cell ct hash initial).bytes else pre.bytes

def before : DataSnapshot hash where
  model:=⟨fun id=>hash (beforeBytes id),fun _=>false,fun _=>10,[],[]⟩
  canonicalBytes:=beforeBytes
  coherent:=fun _=>rfl

theorem durable_ready : wp.plan.intent.preflight before=.ok () := by decide +kernel
theorem durable_opened : wp.plan.opens selected before=true := by decide +kernel

theorem actual_materialized_subject :
    execute .complete before wp.plan.intent=.accepted (DataSnapshot.install before wp.plan.intent) ∧
    (DataSnapshot.install before wp.plan.intent).canonicalBytes wp.plan.stateId=(stateStream ct).encode s3 ∧
    stateValue wp.plan.post.logical=s3 ∧ SumBound 2 s3 ∧
    wp.plan.pre.root=wp.plan.post.root ∧ wp.plan.pre.bytes≠wp.plan.post.bytes := by
  have inv := (window_invariant ct.toLawful admit 2 s3 reached3).1
  refine ⟨execute_complete_ready before wp.plan.intent rfl durable_ready,
    (wp.plan.installed_exact before).1.trans wp.postOpening,rfl,inv,rfl,?_⟩
  decide +kernel


/-- An isolated materialized install is weaker than a coherent history: the
fixture above contains a two-entry logical queue but an empty durable journal. -/
theorem detached_history_is_not_reachable :
    ¬ExecutedHistory ct hash admit 2 selected before before s2 := by
  intro h
  have count := (executed_history_invariant ct hash admit 2 selected before before s2 h).2.1
  change 2=0 at count
  contradiction

/-- Actual three-step materialized history, starting from canonical empty
queue and empty journal, with a new existing DataIntent at every admission. -/
def planFor (tx : Nat) (data : DataSnapshot hash) (s : State Ct) (cmd : Command Ct) : WindowPlan ct hash 2 where
  plan:={
    transactionId:=⟨tx⟩,genesisId:=⟨7⟩,stateId:=⟨22⟩,distinct:=by decide
    genesis:=cell ct hash initial,pre:=cell ct hash s
    patch:=writePatch ct hash (cell ct hash s) (advance 2 s cmd)
    validated:=(writePatch_accepted ct hash (cell ct hash s) (advance 2 s cmd)).choose
    context:=⟨7,0,2,1,cmd.fresh.admissionId,19,23,0,0,0,0⟩
    prior:=data.model.journal.reverse.map Prod.snd,epoch:=0 }
  beforeState:=s
  command:=cmd
  preOpening:=rfl
  postOpening:=rfl

def data0 : DataSnapshot hash where
  model:=⟨fun _=>⟨0⟩,fun _=>false,fun _=>10,[],[]⟩
  canonicalBytes:=fun _=>(cell ct hash initial).bytes
  coherent:=fun _=>rfl

def p0 := planFor 401 data0 initial cmd0
def data1 := DataSnapshot.install data0 p0.plan.intent
def p1 := planFor 402 data1 s1 cmd1
def data2 := DataSnapshot.install data1 p1.plan.intent
def p2 := planFor 403 data2 s2 cmd2
def data3 := DataSnapshot.install data2 p2.plan.intent

theorem data_steps_ready :
    p0.plan.intent.preflight data0=.ok () ∧ p1.plan.intent.preflight data1=.ok () ∧
    p2.plan.intent.preflight data2=.ok () := by decide +kernel

theorem data_steps_opened :
    p0.plan.opens selected data0=true ∧ p1.plan.opens selected data1=true ∧
    p2.plan.opens selected data2=true := by decide +kernel

theorem executed3 : ExecutedHistory ct hash admit 2 selected data0 data3 s3 := by
  have h0 : ExecutedHistory ct hash admit 2 selected data0 data1 s1 :=
    .next (.start rfl rfl) p0 rfl data_steps_opened.1 checked0 data_steps_ready.1 rfl
  have h1 : ExecutedHistory ct hash admit 2 selected data0 data2 s2 :=
    .next h0 p1 rfl data_steps_opened.2.1 checked1 data_steps_ready.2.1 (by decide)
  exact .next h1 p2 rfl data_steps_opened.2.2 checked2 data_steps_ready.2.2 (by decide)

/-- The full history keystone has a changed-state/expiry subject and the
exact serialized queue, accumulator and counter at the installed state cell. -/
theorem executed_history_subject :
    data3.canonicalBytes selected.stateId=(stateStream ct).encode s3 ∧
    s3.nextId=data3.model.journal.length ∧ SumBound 2 s3 ∧
    Provenance ct.toLawful admit s3 ∧ data3.model.journal.length=3 ∧
    s3.queue.map Entry.admissionId=[1,2] := by
  have inv := executed_history_invariant ct hash admit 2 selected data0 data3 s3 executed3
  exact ⟨inv.1,inv.2.1,inv.2.2.2.1,inv.2.2.2.2,rfl,rfl⟩

theorem exact_durable_retry : execute .complete data3 p2.plan.intent=.replayed p2.plan.intent.erase :=
  p2.plan.exact_retry .complete data2


/-- The constructive continuation premise is inhabited for arbitrarily many
nonzero public-vector admissions, not only the three-step display above. -/
theorem unbounded_public_fixture (n : Nat) :
    SumBound 2 (run 2 (fun id=>if id=0 then a else if id=1 then b else c) n) ∧
    Provenance ct.toLawful admit (run 2 (fun id=>if id=0 then a else if id=1 then b else c) n) := by
  have admitted : ∀ id,admit id (ct.encode (if id=0 then a else if id=1 then b else c))=true := by
    intro id;unfold admit;exact decide_eq_true rfl
  have h := all_finite_horizons ct.toLawful admit 2
    (fun id=>if id=0 then a else if id=1 then b else c) (by decide) admitted n
  exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩

/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.checked0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked0
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.checked1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked1
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.checked2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked2
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.reached3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reached3
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.honest_nonzero_add_and_expiry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms honest_nonzero_add_and_expiry
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.same_plaintext_different_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_plaintext_different_ciphertext
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.wrong_serialized_expiry_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_serialized_expiry_refused
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.stale_id_and_denied_input_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_id_and_denied_input_refused
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.bypassed_byte_check_breaks_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bypassed_byte_check_breaks_sum
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.canonical_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms canonical_roundtrip
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.durable_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms durable_ready
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.durable_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms durable_opened
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.actual_materialized_subject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_materialized_subject
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.detached_history_is_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms detached_history_is_not_reachable
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.data_steps_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms data_steps_ready
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.data_steps_opened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms data_steps_opened
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.executed3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms executed3
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.executed_history_subject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executed_history_subject
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.exact_durable_retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exact_durable_retry
/-- info: 'Minidregg.Assurance.CiphertextWindowWitness.unbounded_public_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unbounded_public_fixture

end Minidregg.Assurance.CiphertextWindowWitness
