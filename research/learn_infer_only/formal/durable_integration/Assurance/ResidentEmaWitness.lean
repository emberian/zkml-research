/- [DERIVED target] Inhabitation and teeth for the NEW EMA path. Both the public
byte root and a deliberately constant root admit a genuine accepted NEW FS
receipt for a changed logical state. Constant roots do not weaken the exact
opening/descriptor implication. Wrong logical output and wrong next are separate
falsifiers. Ciphertexts and encrypted opening witnesses remain out of scope. -/
import Assurance.ResidentEmaRelease
namespace Minidregg.Assurance.ResidentEmaWitness
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Assurance.ResidentDurableIntegration (Selection releasedPacket)
open Minidregg.Assurance.ResidentEmaCell
open Minidregg.Assurance.ResidentEmaRelease
open Minidregg.Compiler.ResidentEmaCertificate
open Minidregg.Compiler.CommittedTerminalRealizer (Ext6L traceOf)
open Minidregg.Compiler (descriptorHolds BabyBear)
open Minidregg.Selvage (SrMove)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def publicHash (bs : List UInt8) : Digest := ⟨(bs.headD 0).toNat⟩
def constantHash (_ : List UInt8) : Digest := ⟨0⟩

def p (hash : List UInt8 → Digest) : OpenedPlan hash where
  plan := {
    transactionId:=⟨91⟩,genesisId:=⟨7⟩,stateId:=⟨22⟩,distinct:=by decide
    genesis:=cell hash 128,pre:=cell hash 128,patch:=writePatch hash 128 143
    validated:=(writePatch_accepted hash 128 143).choose
    context:=⟨7,(hash [128]).value,1,1,248,19,23,0,0,(hash [143]).value,0⟩
    prior:=[],epoch:=0 }
  preByte:=128
  postByte:=143
  preOpening:=rfl
  postOpening:=rfl

def selected : Selection := ⟨⟨7⟩,⟨22⟩,[128],19,23⟩
def before (hash : List UInt8 → Digest) : DataSnapshot hash where
  model:=⟨fun _=>hash [128],fun _=>false,fun _=>10,[],[]⟩
  canonicalBytes:=fun _=>[128]
  coherent:=fun _=>rfl
abbrev Node := Fin 3
def q := Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance.quorums
instance : DecidablePred q.isQuorum :=
  Minidregg.Kernel.FinalityGate.ClosedInstance.quorumsDecidable

def book (hash : List UInt8 → Digest) : VoteBook (Node:=Node)
    (TxId:=TransactionId) (CellId:=CellId) (Nullifier:=StableNullifier) (Event:=ReplayEnvelope) :=
  fun _=>[(p hash).plan.candidate]
def cert : Minidregg.Kernel.FinalityGate.Cert Node := ⟨{0,1}⟩

theorem public_ready : (p publicHash).plan.intent.preflight (before publicHash)=.ok () := by decide +kernel
theorem public_openings : (p publicHash).plan.opens selected (before publicHash)=true := by decide +kernel
theorem public_finality : Minidregg.Kernel.FinalityGate.check q (book publicHash)
    (p publicHash).plan.candidate cert=true := by decide +kernel

theorem constant_ready : (p constantHash).plan.intent.preflight (before constantHash)=.ok () := by decide +kernel
theorem constant_openings : (p constantHash).plan.opens selected (before constantHash)=true := by decide +kernel
theorem constant_finality : Minidregg.Kernel.FinalityGate.check q (book constantHash)
    (p constantHash).plan.candidate cert=true := by decide +kernel

theorem witness_linked (hash : List UInt8 → Digest) : Linked (p hash) (candidateWord 128 248 143 0) := by
  have h0 : traceOf (candidateWord 128 248 143 0) 0=128 := by
    rw [trace_candidate]; exact candidate_pins 128 248 143 0 0
  have h1 : traceOf (candidateWord 128 248 143 0) 1=248 := by
    rw [trace_candidate]; exact candidate_pins 128 248 143 0 1
  have h2 : traceOf (candidateWord 128 248 143 0) 2=143 := by
    rw [trace_candidate]; exact candidate_pins 128 248 143 0 2
  refine ⟨rfl,rfl,rfl,rfl,by change 248<256; decide,rfl,?_,?_,?_⟩
  · rw [h0]; change (128 : BabyBear).val=128; decide +kernel
  · rw [h1]; change (248 : BabyBear).val=248; decide +kernel
  · rw [h2]; change (143 : BabyBear).val=143; decide +kernel

theorem witness_descriptor : descriptorHolds descriptor (traceOf (candidateWord 128 248 143 0)) := by
  rw [trace_candidate]; exact honest_descriptor

/-- All apex premises, including descriptor satisfaction, hold for the SAME
actual FS receipt. This is generic in the root function, even a constant one. -/
theorem subject (hash : List UInt8 → Digest)
    (ready : (p hash).plan.intent.preflight (before hash)=.ok ())
    (opened : (p hash).plan.opens selected (before hash)=true)
    (finalized : Minidregg.Kernel.FinalityGate.check q (book hash) (p hash).plan.candidate cert=true)
    (O : SrMove (reduction (p hash).plan.context) 0 → Ext6L) :
    ∃ rc : Receipt, authorized q (book hash) selected (before hash) (p hash) cert O rc=true ∧
      descriptorHolds descriptor (traceOf rc.word) ∧
      LogicalStep (p hash) ∧
      (DataSnapshot.install (before hash) (p hash).plan.intent).canonicalBytes (p hash).plan.stateId=[143] ∧
      releasedPacket (gatedExecute q (book hash) .complete selected (before hash) (p hash) cert O rc)=
        some (p hash).plan.packet := by
  obtain ⟨rc,hcheck,same⟩ := receipt_of_linked (p hash) (candidateWord 128 248 143 0)
    O (witness_linked hash) witness_descriptor
  have ha : authorized q (book hash) selected (before hash) (p hash) cert O rc=true := by
    have policy : decide ((p hash).plan.context.authorization=selected.authorization ∧
        (p hash).plan.context.recipient=selected.recipient)=true := by change decide ((19 : Nat)=19 ∧ (23 : Nat)=23)=true; decide
    simp only [authorized,finalized,opened,hcheck,policy,Bool.true_and]
  have hd : descriptorHolds descriptor (traceOf rc.word) := by rw [same]; exact witness_descriptor
  have all := ema_durable_binding q (book hash) selected (before hash) (p hash) cert O rc ha hd ready rfl
  exact ⟨rc,ha,hd,all.1,all.2.2.2.1,all.2.2.2.2.2.2⟩

theorem public_subject (O : SrMove (reduction (p publicHash).plan.context) 0 → Ext6L) :
    ∃ rc : Receipt, authorized q (book publicHash) selected (before publicHash) (p publicHash) cert O rc=true ∧
      descriptorHolds descriptor (traceOf rc.word) ∧ LogicalStep (p publicHash) := by
  obtain ⟨rc,ha,hd,hs,_,_⟩ := subject publicHash public_ready public_openings public_finality O
  exact ⟨rc,ha,hd,hs⟩

theorem constant_subject (O : SrMove (reduction (p constantHash).plan.context) 0 → Ext6L) :
    ∃ rc : Receipt, authorized q (book constantHash) selected (before constantHash) (p constantHash) cert O rc=true ∧
      descriptorHolds descriptor (traceOf rc.word) ∧ LogicalStep (p constantHash) ∧
      (p constantHash).plan.pre.root=(p constantHash).plan.post.root ∧
      (p constantHash).plan.pre.bytes≠(p constantHash).plan.post.bytes := by
  obtain ⟨rc,ha,hd,hs,_,_⟩ := subject constantHash constant_ready constant_openings constant_finality O
  exact ⟨rc,ha,hd,hs,rfl,by decide⟩

/-- Valid materialization alone can carry the wrong logical value even with
identical roots: the EMA descriptor is the necessary extra premise. -/
def forged : OpenedPlan constantHash where
  plan:={ (p constantHash).plan with
    patch:=writePatch constantHash 128 144
    validated:=(writePatch_accepted constantHash 128 144).choose
    }
  preByte:=128
  postByte:=144
  preOpening:=rfl
  postOpening:=rfl

theorem constant_wrong_post_materializes :
    forged.plan.pre.root=forged.plan.post.root ∧ forged.plan.opens selected (before constantHash)=true ∧
    forged.plan.intent.preflight (before constantHash)=.ok () ∧ ¬LogicalStep forged := by unfold LogicalStep; decide +kernel


/-- The failed-descriptor tooth has inhabited boundary-link premises. -/
theorem forged_linked : Linked forged (candidateWord 128 248 144 0) := by
  have h0 : traceOf (candidateWord 128 248 144 0) 0=128 := by
    rw [trace_candidate]; exact candidate_pins 128 248 144 0 0
  have h1 : traceOf (candidateWord 128 248 144 0) 1=248 := by
    rw [trace_candidate]; exact candidate_pins 128 248 144 0 1
  have h2 : traceOf (candidateWord 128 248 144 0) 2=144 := by
    rw [trace_candidate]; exact candidate_pins 128 248 144 0 2
  refine ⟨rfl,rfl,rfl,rfl,by decide,rfl,?_,?_,?_⟩
  · rw [h0]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h2]; decide +kernel

theorem constant_wrong_post_descriptor_refused (w : Word) (linked : Linked forged w) :
    ¬descriptorHolds descriptor (traceOf w) := by
  intro hd
  have hs := descriptor_semantic (traceOf w) hd
  obtain ⟨_,_,_,_,_,_,hp,hu,hn⟩ := linked
  rw [hp,hu,hn] at hs
  change (144 : Int)-128=ema ((128 : Int)-128) ((248 : Int)-128) at hs
  norm_num [ema] at hs

def wrongNext : OpenedPlan publicHash :=
  { p publicHash with plan:={ (p publicHash).plan with context:={ (p publicHash).plan.context with next:=144 } } }

theorem wrong_next_refused : wrongNext.plan.opens selected (before publicHash)=false := by decide +kernel

end Minidregg.Assurance.ResidentEmaWitness

/- Exact-output axiom pins, observed from the recorded matching Lean check. -/

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.public_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.public_ready

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.public_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.public_openings

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.public_finality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.public_finality

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.constant_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.constant_ready

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.constant_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.constant_openings

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.constant_finality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.constant_finality

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.witness_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.witness_linked

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.witness_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.witness_descriptor

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.subject

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.public_subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.public_subject

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.constant_subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.constant_subject

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.constant_wrong_post_materializes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.constant_wrong_post_materializes

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.constant_wrong_post_descriptor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.constant_wrong_post_descriptor_refused

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.wrong_next_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.wrong_next_refused

/-- info: 'Minidregg.Assurance.ResidentEmaWitness.forged_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaWitness.forged_linked
