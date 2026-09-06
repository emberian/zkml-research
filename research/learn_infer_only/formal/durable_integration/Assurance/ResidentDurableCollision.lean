/-
[DERIVED target; EXECUTED after source-matching compilation]
Scoped negative sibling: exact durable installation plus arithmetic on root
values does NOT force the logical resident Step. The existing lawful Bool
codec is retained, but the root function is intentionally constant. A genuine
validator-minted false->true patch then has parent=next=0. A real FS receipt
for addition 0+0, actual finality, exact byte openings and full preflight all
accept. This is not a break of any imported theorem, commitment, or real hash.
It exhibits the remaining root-opening/semantic relation premise directly.
ATLAS: actual accepted positive subject plus byte/logical mismatch, kernel
proofs and exact axiom pins; no hash injectivity or cryptographic claim.
-/
import Assurance.ResidentDurableIntegration

namespace Minidregg.Assurance.ResidentDurableCollision

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellStateWitness (schema stateCodec stateOf honestPatch)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Assurance.ResidentReleaseContext
open Minidregg.Assurance.ResidentDurableIntegration
open Minidregg.Compiler.CommittedTerminalFiatShamir (FsReceipt)
open Minidregg.Compiler.CommittedTerminalRealizer (Ext6L)
open Minidregg.Compiler.CommittedTerminalRealizer (traceOf)
open Minidregg.Compiler.CommittedTerminalRealizer.Stage0Exhibit (wordOf)
open Minidregg.Compiler.DescriptorEval (evmAddCandidate evmAddCandidate_holds evmAddCandidate_pins)
open Minidregg.Compiler.EvmAddAir (evmAddDescriptor encodeBoundary)
open Minidregg.Assurance.ReleaseGateRouting (traceOf_wordOf_candidate)
open Minidregg.Compiler (descriptorHolds)
open Minidregg.Selvage (SrMove)

set_option autoImplicit false

def M : Materializer schema Digest := ⟨stateCodec, fun _ => ⟨0⟩⟩
def pre : Materialized M := materialize M (stateOf false)

theorem validated_exists : ∃ v : ValidatedPatch M pre honestPatch,
    validate M pre honestPatch = .accepted v := by
  unfold validate
  rw [dif_pos (show honestPatch.expectedPreRoot = pre.root from rfl)]
  rw [dif_pos (show honestPatch.fieldFootprint = honestPatch.namedFields by decide)]
  rw [dif_pos (show honestPatch.resourceFootprint = honestPatch.namedResources by decide)]
  exact ⟨_, rfl⟩

def p : Plan M where
  transactionId := ⟨191⟩
  genesisId := ⟨7⟩
  stateId := ⟨22⟩
  distinct := by decide
  genesis := materialize M (stateOf true)
  pre := pre
  patch := honestPatch
  validated := validated_exists.choose
  context := honestContext 0 0
  prior := []
  epoch := 0

def selected : Selection := ⟨⟨7⟩, ⟨22⟩, [1], 19, 23⟩
def beforeBytes (id : CellId) : List UInt8 := if id = p.genesisId then [1] else [0]
def before : DataSnapshot M.rootBytes where
  model := ⟨fun _ => ⟨0⟩, fun _ => false, fun _ => 10, [], []⟩
  canonicalBytes := beforeBytes
  coherent := fun _ => rfl

abbrev Node := ResidentDurableIntegration.Closed.Node
def q := ResidentDurableIntegration.Closed.q
instance : DecidablePred q.isQuorum :=
  Minidregg.Kernel.FinalityGate.ClosedInstance.quorumsDecidable
def book : VoteBook (Node := Node) (TxId := TransactionId) (CellId := CellId)
    (Nullifier := StableNullifier) (Event := ReplayEnvelope) := fun _ => [p.candidate]
def cert : Minidregg.Kernel.FinalityGate.Cert Node := ⟨{0, 1}⟩

theorem ready : p.intent.preflight before = .ok () := by decide
theorem openings : p.opens selected before = true := by decide
theorem finalized : Minidregg.Kernel.FinalityGate.check q book p.candidate cert = true := by decide

def RootArithmeticDoesNotForceLogicalStep : Prop :=
  ∀ O : SrMove (reduction p.context) 0 → Ext6L,
    ∃ rc : FsReceipt Root 4131 13,
      authorized q book selected before p cert O rc = true ∧
      p.intent.preflight before = .ok () ∧
      Forced p.context ∧ p.context.command = 0 ∧ p.context.parent = p.context.next ∧
      p.pre.bytes ≠ p.post.bytes ∧
      p.pre.logical.fields () ≠ p.post.logical.fields () ∧
      descriptorHolds evmAddDescriptor (traceOf rc.word)

theorem root_arithmetic_not_logical_step : RootArithmeticDoesNotForceLogicalStep := by
  intro O
  let w := wordOf (evmAddCandidate 0 0)
  have boundary : ∀ i : Fin 48, traceOf w i.val = encodeBoundary 0 0 ((0+0) % 2^256) i := by
    intro i
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_pins 0 0 i
  have descriptor : descriptorHolds evmAddDescriptor (traceOf w) := by
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_holds 0 0 (by norm_num) (by norm_num)
  have linked : Linked p.context w :=
    ⟨by norm_num [p, honestContext], by norm_num [p, honestContext],
      by norm_num [p, honestContext], rfl, rfl, rfl, rfl, rfl, boundary⟩
  obtain ⟨rc, hr, sameWord⟩ := receipt_retains_proved_word p.context w O linked descriptor
  have policy : decide (p.context.authorization = selected.authorization ∧
      p.context.recipient = selected.recipient) = true := by decide
  refine ⟨rc, ?_, ready, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [authorized, finalized, openings, policy, Bool.true_and, Bool.and_true]
    exact hr
  · constructor <;> rfl
  · decide
  · change (some false : Option Bool) ≠ some true
    decide
  · rwa [sameWord]

/-- Exact canonical installation still holds in this broken semantic sibling.
This scopes the refutation to the stronger logical-Step interpretation. -/
theorem exact_install_survives :
    execute .complete before p.intent = .accepted (DataSnapshot.install before p.intent) ∧
    (DataSnapshot.install before p.intent).canonicalBytes p.stateId = [1] ∧
    (DataSnapshot.install before p.intent).model.roots p.stateId = ⟨0⟩ := by
  exact ⟨execute_complete_ready before p.intent rfl ready, by decide, by decide⟩

end Minidregg.Assurance.ResidentDurableCollision

/- Exact-output axiom pins, observed in lean_ResidentDurableCollision_03.json. -/

/-- info: 'Minidregg.Assurance.ResidentDurableCollision.validated_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableCollision.validated_exists

/-- info: 'Minidregg.Assurance.ResidentDurableCollision.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableCollision.ready

/-- info: 'Minidregg.Assurance.ResidentDurableCollision.openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableCollision.openings

/-- info: 'Minidregg.Assurance.ResidentDurableCollision.finalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableCollision.finalized

/-- info: 'Minidregg.Assurance.ResidentDurableCollision.root_arithmetic_not_logical_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableCollision.root_arithmetic_not_logical_step

/-- info: 'Minidregg.Assurance.ResidentDurableCollision.exact_install_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentDurableCollision.exact_install_survives
