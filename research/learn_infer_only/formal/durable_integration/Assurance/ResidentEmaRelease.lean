/- [DERIVED target] NEW EMA descriptor/FS instance (program1/version1), not the
old Stage0 addition receipt. Exact public canonical openings feed its scalar
boundary. The existing DataIntent executor installs and journals the same plan;
release reads that journal using the repaired no-Plan helper. No secret-opening
or encryption refinement, PQ soundness, transport or physical atomicity claim. -/
import Assurance.ResidentEmaCell

namespace Minidregg.Assurance.ResidentEmaRelease
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot Schedule)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Assurance.ResidentReleaseContext (Context contextScheme)
open Minidregg.Assurance.ResidentDurableIntegration (Selection Plan GatedOutcome releasedPacket)
open Minidregg.Assurance.ResidentEmaCell
open Minidregg.Compiler
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.ResidentEmaCertificate
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Selvage
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem descriptor_nonempty : 0<descriptor.nWires := by decide +kernel
theorem residuals_fit : descriptor.gates.length+descriptor.zeros.length≤2^8 := by decide +kernel
abbrev Word := Fin descriptor.nWires → BabyBear
abbrev Root := Context × Word
def scheme (c : Context) := contextScheme c (idealCommitment BabyBear (Fin descriptor.nWires))
noncomputable abbrev reduction (c : Context) :=
  gateReduction (scheme c).commit descriptor (bitCorner 8) descriptor_nonempty
abbrev Receipt := FsReceipt Root descriptor.nWires 8

/-- Digest-valued parent/next remain context metadata. The three EMA values
come from independently checked canonical byte openings and command.
The learn packet releases only the fixed acknowledgement0. The full-word
receipt itself is public and therefore still reveals all certificate values. -/
def Linked {hash : List UInt8 → Digest} (p : OpenedPlan hash) (w : Word) : Prop :=
  p.plan.context.program=1 ∧ p.plan.context.version=1 ∧
  p.plan.context.randomnessRule=0 ∧ p.plan.context.randomnessCommitment=0 ∧
  p.plan.context.command<256 ∧ p.plan.context.output=0 ∧
  (traceOf w 0).val=p.preByte.toNat ∧
  (traceOf w 1).val=p.plan.context.command ∧ (traceOf w 2).val=p.postByte.toNat
instance {hash : List UInt8 → Digest} (p : OpenedPlan hash) (w : Word) : Decidable (Linked p w) :=
  by unfold Linked; infer_instance

def check {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt) : Bool :=
  decide (rc.root.1=p.plan.context) && decide (Linked p rc.word) &&
  (match fsCheck (scheme p.plan.context).commit descriptor (bitCorner 8) descriptor_nonempty O rc with
    | .ok _ => true | .error _ => false)

theorem checked_context {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt)
    (h : check p O rc=true) : rc.root.1=p.plan.context ∧ Linked p rc.word := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.1


/-- Acceptance really enters the existing FS checker; the public boundary
checks do not substitute for the proof protocol. -/
theorem checked_fiatShamir {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt)
    (h : check p O rc=true) :
    fiatShamir (reduction p.plan.context) 0 O
      (rc.output (scheme p.plan.context).commit descriptor (bitCorner 8) descriptor_nonempty)=
      some ((),fun _=>()) := by
  simp only [check,Bool.and_eq_true] at h
  cases hf : fsCheck (scheme p.plan.context).commit descriptor (bitCorner 8) descriptor_nonempty O rc with
  | ok r =>
    exact fsCheck_ok_fiatShamir (scheme p.plan.context).commit descriptor
      (bitCorner 8) descriptor_nonempty O rc r hf
  | error e => simp [hf] at h

theorem checked_logical_step {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt)
    (h : check p O rc=true) (hd : descriptorHolds descriptor (traceOf rc.word)) : LogicalStep p := by
  obtain ⟨_,_,_,_,_,_,hp,hu,hn⟩ := (checked_context p O rc h).2
  have hs := descriptor_semantic (traceOf rc.word) hd
  rw [hp,hu,hn] at hs
  unfold LogicalStep
  rw [signed_opening hash p.plan.post p.postByte p.postOpening,
    signed_opening hash p.plan.pre p.preByte p.preOpening]
  exact hs

theorem bad_step_implies_bad_descriptor {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt)
    (h : check p O rc=true) (bad : ¬LogicalStep p) :
    ¬descriptorHolds descriptor (traceOf rc.word) := fun hd => bad (checked_logical_step p O rc h hd)

/-- A fresh generic committed-terminal instance gets its OWN symbolic ROM
price. No Stage0 wire count, descriptor, or addition theorem is reused. -/
theorem receipt_price (c : Context) :
    FsStraightlineKnowledgeSoundness (reduction c) Set.univ
      (fun _s t _δ => ((t : ℝ)+((8+1 : Nat) : ℝ))*gatePrice descriptor 8) :=
  gateProof_fs_sound (scheme c).commit descriptor (bitCorner 8)
    (fun wv => residualEmbedding descriptor wv residuals_fit) (fun _ _ => rfl) descriptor_nonempty


/-- The numerical coefficient is derived from 154 residuals and eight
sumcheck coordinates; it is a ROM error term, not a deployment security claim. -/
theorem gate_price_explicit : gatePrice descriptor 8 = 161/((2013265921 : ℝ)^6) := by
  unfold gatePrice
  rw [descriptor_shape.2.2.2.1,descriptor_shape.2.2.2.2,
    Minidregg.Compiler.CommittedTerminalCompose.card_ext6]
  norm_num [babyBearP]

theorem receipt_of_linked {hash : List UInt8 → Digest} (p : OpenedPlan hash) (w : Word)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (hl : Linked p w)
    (hd : descriptorHolds descriptor (traceOf w)) :
    ∃ rc : Receipt, check p O rc=true ∧ rc.word=w := by
  let rc := fsProve (scheme p.plan.context).commit descriptor (bitCorner 8)
    descriptor_nonempty O ((scheme p.plan.context).commit w) w
  have hc := fsProve_complete (scheme p.plan.context).commit descriptor (bitCorner 8)
    descriptor_nonempty O w (residualEmbedding descriptor (traceOf w) residuals_fit) (fun _ => rfl) hd
  refine ⟨rc,?_,rfl⟩
  unfold check
  have rt : rc.root.1=p.plan.context := rfl
  have wd : rc.word=w := rfl
  rw [decide_eq_true rt,wd,decide_eq_true hl]
  change (match fsCheck (scheme p.plan.context).commit descriptor (bitCorner 8)
    descriptor_nonempty O rc with | .ok _ => true | .error _ => false)=true
  rw [hc]

section Durable
variable {hash : List UInt8 → Digest} {Node : Type} [DecidableEq Node]
variable (q : QuorumSystem Node) [DecidablePred q.isQuorum]
variable (book : VoteBook (Node:=Node) (TxId:=TransactionId) (CellId:=CellId)
  (Nullifier:=StableNullifier) (Event:=ReplayEnvelope))

def authorized (selected : Selection) (before : DataSnapshot hash) (p : OpenedPlan hash)
    (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt) : Bool :=
  Minidregg.Kernel.FinalityGate.check q book p.plan.candidate cert &&
  p.plan.opens selected before && check p O rc &&
  decide (p.plan.context.authorization=selected.authorization ∧ p.plan.context.recipient=selected.recipient)


/-- The fresh finality/context checks constrain the same installed plan,
including genesis, parent, next, recipient and fixed learn acknowledgement. -/
theorem authorized_context (selected : Selection) (before : DataSnapshot hash)
    (p : OpenedPlan hash) (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt)
    (h : authorized q book selected before p cert O rc=true) :
    rc.root.1=p.plan.context ∧ p.plan.Openings selected before ∧ Linked p rc.word ∧
    p.plan.context.authorization=selected.authorization ∧ p.plan.context.recipient=selected.recipient := by
  simp only [authorized,Bool.and_eq_true,decide_eq_true_eq] at h
  have hc := checked_context p O rc h.1.2
  exact ⟨hc.1,(p.plan.opens_iff selected before).mp h.1.1.2,hc.2,h.2⟩

def gatedExecute (schedule : Schedule) (selected : Selection) (before : DataSnapshot hash)
    (p : OpenedPlan hash) (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt) : GatedOutcome hash :=
  match Snapshot.lookupRecorded p.plan.transactionId before.model.journal with
  | some _ => .durable (execute schedule before p.plan.intent)
  | none => if authorized q book selected before p cert O rc then
      .durable (execute schedule before p.plan.intent) else .gateRefused

/-- Keystone: accepted NEW descriptor and exact logical openings entail the
actual resident Step AND exact installed bytes/root, consumed token and packet. -/
def EmaDurableBinding : Prop :=
  ∀ selected before (p : OpenedPlan hash) cert O rc,
    authorized q book selected before p cert O rc=true →
    descriptorHolds descriptor (traceOf rc.word) →
    p.plan.intent.preflight before=.ok () →
    Snapshot.lookupRecorded p.plan.transactionId before.model.journal=none →
    LogicalStep p ∧
    gatedExecute q book .complete selected before p cert O rc=
      .durable (.accepted (DataSnapshot.install before p.plan.intent)) ∧
    before.canonicalBytes p.plan.stateId=[p.preByte] ∧
    (DataSnapshot.install before p.plan.intent).canonicalBytes p.plan.stateId=[p.postByte] ∧
    rc.root.1.next=((DataSnapshot.install before p.plan.intent).model.roots p.plan.stateId).value ∧
    (DataSnapshot.install before p.plan.intent).model.consumed p.plan.token=true ∧
    releasedPacket (gatedExecute q book .complete selected before p cert O rc)=some p.plan.packet

theorem ema_durable_binding : EmaDurableBinding q book (hash:=hash) := by
  intro selected before p cert O rc ha hd ready fresh
  have parts := ha
  simp only [authorized,Bool.and_eq_true,decide_eq_true_eq] at parts
  have opened := (p.plan.opens_iff selected before).mp parts.1.1.2
  have hc := checked_context p O rc parts.1.2
  have executed : gatedExecute q book .complete selected before p cert O rc=
      .durable (.accepted (DataSnapshot.install before p.plan.intent)) := by
    simp only [gatedExecute,fresh,ha,↓reduceIte]
    rw [execute_complete_ready before p.plan.intent fresh ready]
  refine ⟨checked_logical_step p O rc parts.1.2 hd,executed,?_,?_,?_,
    p.plan.installed_consumed before,?_⟩
  · exact opened.2.2.2.2.1.trans p.preOpening
  · exact (p.plan.installed_exact before).1.trans p.postOpening
  · rw [hc.1]
    exact opened.2.2.2.2.2.2.2.1.trans (congrArg Digest.value (p.plan.installed_exact before).2.symm)
  · rw [executed]; rfl

theorem retry_exact_packet (schedule : Schedule) (selected : Selection)
    (before : DataSnapshot hash) (p : OpenedPlan hash) (cert : Minidregg.Kernel.FinalityGate.Cert Node)
    (O : SrMove (reduction p.plan.context) 0 → Ext6L) (rc : Receipt) :
    releasedPacket (gatedExecute q book schedule selected (DataSnapshot.install before p.plan.intent)
      p cert O rc)=some p.plan.packet := by
  have lookup : Snapshot.lookupRecorded p.plan.transactionId
      (DataSnapshot.install before p.plan.intent).model.journal=some p.plan.intent.erase :=
    Snapshot.lookupRecorded_install before.model p.plan.intent.erase
  simp only [gatedExecute,lookup]
  have retry := p.plan.exact_retry schedule before
  exact congrArg (fun out => releasedPacket (GatedOutcome.durable out)) retry

end Durable

def candidateWord (C U N r : Nat) : Word := fun i => (candidate C U N r).getD i.val 0

theorem trace_candidate (C U N r : Nat) :
    traceOf (candidateWord C U N r)=fun i => (candidate C U N r).getD i 0 := by
  have wf := emit_wellFormed Fin.val 4 31 (by omega) (fun i : Fin 31 => i.isLt) system
  have size : (candidate C U N r).size=descriptor.nWires :=
    fillAux_size descriptor _ wf Array.size_ofFn
  funext i
  by_cases h : i<descriptor.nWires
  · simp [traceOf,candidateWord,h]
  · have hs : (candidate C U N r).size ≤ i := by rw [size]; omega
    simp [traceOf,h,Array.getD_eq_getD_getElem?,Array.getElem?_eq_none hs]

end Minidregg.Assurance.ResidentEmaRelease

/- Exact-output axiom pins, observed from the recorded matching Lean check. -/

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.descriptor_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.descriptor_nonempty

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.residuals_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.residuals_fit

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.checked_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.checked_context

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.checked_fiatShamir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.checked_fiatShamir

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.checked_logical_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.checked_logical_step

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.bad_step_implies_bad_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.bad_step_implies_bad_descriptor

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.receipt_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.receipt_price

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.receipt_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.receipt_of_linked

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.ema_durable_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.ema_durable_binding

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.retry_exact_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.retry_exact_packet

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.trace_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.trace_candidate

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.gate_price_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.gate_price_explicit

/-- info: 'Minidregg.Assurance.ResidentEmaRelease.authorized_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaRelease.authorized_context
