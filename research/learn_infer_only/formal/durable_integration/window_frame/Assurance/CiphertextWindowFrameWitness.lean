/- [DERIVED target] Nonzero materialized mixed-history witness and falsifiers.
Three existing checked public window admissions, an actual same-window no-op
with an infer-style event tag, and an unrelated cell commit. The no-op tag is
not a cryptographic inference/output theorem. Constant roots keep canonical
bytes and checked effects load-bearing. Frozen window44 files are reused.
-/
import Assurance.CiphertextWindowFrame
import Assurance.CiphertextWindowWitness

namespace Minidregg.Assurance.CiphertextWindowFrameWitness
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.CiphertextWindow
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Assurance.CiphertextWindowFrame
open Minidregg.Assurance.CiphertextWindowWitness
open Minidregg.Assurance.ResidentReleaseContext (Context contextWords)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot)
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def classifier := windowAdmission selected

def frameContext : Context := ⟨7,0,3,1,0,19,23,0,0,0,0⟩

def frameIntent (tx : Nat) (target : Digest) (bytes : List UInt8) : DataIntent hash where
  transactionId:=⟨tx⟩
  writes:=[⟨target,⟨0⟩,⟨0⟩,bytes⟩]
  readGuards:=[]
  nullifiers:=[⟨1,⟨201⟩,⟨tx⟩,(StreamCodec.list StreamCodec.nat).encode [tx]⟩]
  exactCharge:=fun _=>1
  event:=⟨1,⟨102⟩,⟨tx⟩,(StreamCodec.list StreamCodec.nat).encode (contextWords frameContext)⟩
  postRootsBound:=by
    intro write h;simp only [List.mem_singleton] at h;subst write;rfl
  guardsReadOnly:=by intro guard h;cases h

/-- The installed window itself is written back byte-for-byte, so this is
not merely a disjoint-cell special case. It spends a separate nonce/charge. -/
def inferNoop := frameIntent 501 selected.stateId (data1.canonicalBytes selected.stateId)
def afterInfer := DataSnapshot.install data1 inferNoop
/-- `planFor` reads the FULL actual journal prefix, including framed entries;
its continuation token is not synthesized from the smaller admission count. -/
def learn1 := planFor 502 afterInfer s1 cmd1
def afterLearn1 := DataSnapshot.install afterInfer learn1.plan.intent

def unrelated := frameIntent 503 ⟨23⟩ (afterLearn1.canonicalBytes ⟨23⟩)
def afterUnrelated := DataSnapshot.install afterLearn1 unrelated
def learn2 := planFor 504 afterUnrelated s2 cmd2
def finalData := DataSnapshot.install afterUnrelated learn2.plan.intent

theorem classifications : classifier p0.plan.intent.erase=true ∧
    classifier inferNoop.erase=false ∧ classifier learn1.plan.intent.erase=true ∧
    classifier unrelated.erase=false ∧ classifier learn2.plan.intent.erase=true := by decide +kernel

theorem actual_frames : framesSelected selected data1 inferNoop=true ∧
    framesSelected selected afterLearn1 unrelated=true := by decide +kernel

theorem all_ready : p0.plan.intent.preflight data0=.ok () ∧
    inferNoop.preflight data1=.ok () ∧ learn1.plan.intent.preflight afterInfer=.ok () ∧
    unrelated.preflight afterLearn1=.ok () ∧ learn2.plan.intent.preflight afterUnrelated=.ok () := by decide +kernel

theorem actual_openings : p0.plan.opens selected data0=true ∧
    learn1.plan.opens selected afterInfer=true ∧ learn2.plan.opens selected afterUnrelated=true := by decide +kernel

theorem mixed_subject_history : MixedHistory ct hash admit 2 selected classifier data0 finalData s3 := by
  have h0 : MixedHistory ct hash admit 2 selected classifier data0 data1 s1 :=
    .learn (.start rfl rfl rfl) p0 rfl actual_openings.1 checked0 classifications.1 all_ready.1 rfl
  have hf : MixedHistory ct hash admit 2 selected classifier data0 afterInfer s1 :=
    .frame h0 inferNoop classifications.2.1 actual_frames.1 all_ready.2.1 (by decide +kernel)
  have h1 : MixedHistory ct hash admit 2 selected classifier data0 afterLearn1 s2 :=
    .learn hf learn1 rfl actual_openings.2.1 checked1 classifications.2.2.1 all_ready.2.2.1 (by decide +kernel)
  have hg : MixedHistory ct hash admit 2 selected classifier data0 afterUnrelated s2 :=
    .frame h1 unrelated classifications.2.2.2.1 actual_frames.2 all_ready.2.2.2.1 (by decide +kernel)
  exact .learn hg learn2 rfl actual_openings.2.2 checked2 classifications.2.2.2.2
    all_ready.2.2.2.2 (by decide +kernel)

/-- The same physical journal has five commits but only three admissions,
with expiry retaining exactly ids1,2 and the existing nonzero group sum. -/
theorem mixed_subject :
    finalData.canonicalBytes selected.stateId=(stateStream ct).encode s3 ∧
    finalData.canonicalBytes selected.genesisId=selected.genesisBytes ∧
    s3.nextId=admissionCount classifier finalData ∧
    admissionCount classifier finalData=3 ∧ finalData.model.journal.length=5 ∧
    SumBound 2 s3 ∧ Provenance ct.toLawful admit s3 ∧
    s3.queue.map Entry.admissionId=[1,2] ∧ s3.accumulator=b+c := by
  have inv := mixed_invariant ct hash admit 2 selected classifier data0 finalData s3 mixed_subject_history
  exact ⟨inv.1,inv.2.1,inv.2.2.1,by decide +kernel,rfl,inv.2.2.2.2.1,inv.2.2.2.2.2,rfl,
    honest_nonzero_add_and_expiry.2.2.1⟩

/-- Every edge is the existing full preflight/fresh execute, including the
same-cell no-op and unrelated cell. No blind installer or independent counter. -/
theorem actual_five_executes :
    execute .complete data0 p0.plan.intent=.accepted data1 ∧
    execute .complete data1 inferNoop=.accepted afterInfer ∧
    execute .complete afterInfer learn1.plan.intent=.accepted afterLearn1 ∧
    execute .complete afterLearn1 unrelated=.accepted afterUnrelated ∧
    execute .complete afterUnrelated learn2.plan.intent=.accepted finalData := by
  exact ⟨execute_complete_ready data0 p0.plan.intent rfl all_ready.1,
    execute_complete_ready data1 inferNoop (by decide +kernel) all_ready.2.1,
    execute_complete_ready afterInfer learn1.plan.intent (by decide +kernel) all_ready.2.2.1,
    execute_complete_ready afterLearn1 unrelated (by decide +kernel) all_ready.2.2.2.1,
    execute_complete_ready afterUnrelated learn2.plan.intent (by decide +kernel) all_ready.2.2.2.2⟩

theorem projection_is_actual_entries :
    (admissionProjection classifier finalData).map (fun entry=>entry.transactionId.value)=[504,502,401] ∧
    finalData.model.journal.map (fun entry=>entry.1.value)=[504,503,502,501,401] := by decide +kernel

theorem frame_advances_only_authority_revision :
    afterInfer.canonicalBytes selected.stateId=data1.canonicalBytes selected.stateId ∧
    admissionCount classifier afterInfer=admissionCount classifier data1 ∧
    afterInfer.model.journal.length=data1.model.journal.length+1 ∧
    afterInfer.model.available .feeDebit=data1.model.available .feeDebit-1 ∧
    inferNoop.nullifiers.head?.isSome=true := by
  exact ⟨((framesSelected_iff selected data1 inferNoop).mp actual_frames.1).1,
    count_frame classifier data1 inferNoop classifications.2.1,rfl,rfl,rfl⟩

theorem exact_retry_after_interleaved_expiry :
    execute .complete finalData learn2.plan.intent=.replayed learn2.plan.intent.erase :=
  learn2.plan.exact_retry .complete afterUnrelated

/-- Same colliding root, same infer-style tag and a genuine preflight-ready
DataIntent, but it changes canonical window bytes: framing must reject it. -/
def dishonestFrame := frameIntent 505 selected.stateId ((stateStream ct).encode s2)

theorem false_frame_refused :
    dishonestFrame.preflight data1=.ok () ∧ classifier dishonestFrame.erase=false ∧
    framesSelected selected data1 dishonestFrame=false ∧
    (DataSnapshot.install data1 dishonestFrame).model.roots selected.stateId=data1.model.roots selected.stateId ∧
    (DataSnapshot.install data1 dishonestFrame).canonicalBytes selected.stateId≠data1.canonicalBytes selected.stateId := by decide +kernel

theorem false_frame_cannot_preserve_current_logical_state :
    ¬MixedHistory ct hash admit 2 selected classifier data0
      (DataSnapshot.install data1 dishonestFrame) s1 := by
  intro h
  have inv := mixed_invariant ct hash admit 2 selected classifier data0 _ s1 h
  have bad : (DataSnapshot.install data1 dishonestFrame).canonicalBytes selected.stateId≠(stateStream ct).encode s1 := by decide +kernel
  exact bad inv.1

/-- Writing the selected genesis under a colliding digest is not a frame,
even when the actual window bytes are unchanged. -/
def falseGenesisFrame := frameIntent 506 selected.genesisId []

theorem false_genesis_frame_refused :
    falseGenesisFrame.preflight data1=.ok () ∧ classifier falseGenesisFrame.erase=false ∧
    frameCheck selected.stateId data1 falseGenesisFrame=true ∧
    framesSelected selected data1 falseGenesisFrame=false := by decide +kernel

/-- Base255 natural decoding accepts a redundant high zero in the list-length
prefix; the concrete journal classifier additionally enforces re-encoding. -/
def aliasedTag : Minidregg.Assurance.ResidentDurableIntegration.WalIntent :=
  { p0.plan.intent.erase with
    event:={ p0.plan.intent.erase.event with
      event:={ p0.plan.packet with canonicalBytes:=11::0::255::p0.plan.packet.canonicalBytes.drop 2 } } }

theorem noncanonical_context_tag_refused :
    (StreamCodec.list StreamCodec.nat).toLawful.decode aliasedTag.event.event.canonicalBytes=
      some (contextWords p0.plan.context) ∧
    classifier p0.plan.intent.erase=true ∧ classifier aliasedTag=false := by decide +kernel

/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms classifications
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.actual_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_frames
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.all_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_ready
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.actual_openings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_openings
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.mixed_subject_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_subject_history
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.mixed_subject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_subject
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.actual_five_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_five_executes
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.projection_is_actual_entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms projection_is_actual_entries
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.frame_advances_only_authority_revision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frame_advances_only_authority_revision
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.exact_retry_after_interleaved_expiry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exact_retry_after_interleaved_expiry
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.false_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_frame_refused
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.false_frame_cannot_preserve_current_logical_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_frame_cannot_preserve_current_logical_state
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.false_genesis_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_genesis_frame_refused
/-- info: 'Minidregg.Assurance.CiphertextWindowFrameWitness.noncanonical_context_tag_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms noncanonical_context_tag_refused

end Minidregg.Assurance.CiphertextWindowFrameWitness
