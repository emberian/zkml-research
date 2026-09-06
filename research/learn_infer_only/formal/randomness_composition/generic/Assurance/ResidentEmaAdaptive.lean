/-
Statement-first: instantiate the reusable ContextualGate reduction and complete
shared-query-log selector at the ACTUAL EMA descriptor: 153 wires, eight
sumcheck coordinates, nine verifier queries, price 161/p^6, and delta<1/153.
Bad accepted logical Steps of opened plans are mapped to the same global false
descriptor event. All contexts and receipts share ONE queried oracle log.

ATLAS: same-receipt public EMA witness 128→143 with command248 is accepted by
the old wrapper, its exact descriptor, and the generic adaptive verifier. An
explicit nine-query schedule is inhabited even under its own sampled log.
The forged 128→144 plan still materializes and links but fails the descriptor;
an empty query log fails completeness. No hidden-state, QROM, concrete-hash,
or runtime before-publication theorem is asserted.
-/
import Compiler.ContextualGate
import Assurance.ResidentEmaWitness
import Assurance.ResidentAdaptiveContext

namespace Minidregg.Assurance.ResidentEmaAdaptive

open Minidregg.Selvage
open Minidregg.Compiler
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Compiler.ResidentEmaCertificate
open Minidregg.Assurance.ResidentReleaseContext
  (Context honestContext contextWords rootCodec word_values_injective contextWords_injective)
open Minidregg.Assurance.ResidentEmaCell
open Minidregg.Assurance.ResidentEmaRelease
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def baseContext : Context := honestContext 0 0
noncomputable abbrev R := ContextualGate.contextReduction baseContext descriptor 8 descriptor_nonempty

/-- The previous Stage0 reduction is literally an instance of the reusable
construction, so this factorization introduces no parallel Stage0 protocol. -/
theorem stage0_reduction_is_existing :
    ContextualGate.contextReduction (honestContext 0 0) EvmAddAir.evmAddDescriptor 13
      (by norm_num : 0 < 4131) = ResidentAdaptiveContext.adaptiveReduction := rfl

def receiptOutput (rc : Receipt) : SrOutput R 0 := ContextualGate.output rc

def wrapperCheck {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove R 0 → Ext6L) (rc : Receipt) : Bool :=
  ResidentEmaRelease.check p (fun q => O (ContextualGate.fromFixed p.plan.context q)) rc

theorem wrapper_acceptance_transport {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove R 0 → Ext6L) (rc : Receipt) (h : wrapperCheck p O rc=true) :
    fiatShamir R 0 O (receiptOutput rc)=some ((),fun _=>()) := by
  have hc := (checked_context p (fun q => O (ContextualGate.fromFixed p.plan.context q)) rc h).1
  have hf := checked_fiatShamir p (fun q => O (ContextualGate.fromFixed p.plan.context q)) rc h
  exact ContextualGate.fixed_acceptance_transport p.plan.context O rc hc hf

theorem bad_step_is_global_bad {hash : List UInt8 → Digest} (p : OpenedPlan hash)
    (O : SrMove R 0 → Ext6L) (rc : Receipt) (h : wrapperCheck p O rc=true)
    (bad : ¬LogicalStep p) : ¬ R.R () rc.root rc.word () := by
  have hd := bad_step_implies_bad_descriptor p
    (fun q => O (ContextualGate.fromFixed p.plan.context q)) rc h bad
  exact fun hR => hd hR.2

theorem descriptor_parameters : R.n=153 ∧ R.k=9 := by
  exact ⟨descriptor_shape.2.2.1,rfl⟩

theorem single_bad_receipt_bound (s t : Nat) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (153 : ℝ))) (P : SrProver R s) :
    uniformProb ((Fin t → R.Chal) × (Fin R.k → R.Chal))
      (fun coins =>
        let o := P.out ((srTrace P coins.1).map Prod.snd)
        ¬ R.R o.stmt.idx o.stmt.x o.stmt.y () ∧
          fiatShamir R s (fsOracle o (srFinalChal P coins.1 coins.2)) o ≠ none) ≤
      ((t : ℝ)+9) * (161 / ((2013265921 : ℝ)^6)) := by
  have hδ' : δ ∈ Set.Ioo (0 : ℝ) (1 / (descriptor.nWires : ℝ)) := by
    rw [descriptor_shape.2.2.1]; exact hδ
  have hb := ContextualGate.sound_reading residuals_fit s t hδ' P
  simpa only [gate_price_explicit, show ((8+1 : Nat) : ℝ) = 9 by norm_num] using hb

theorem bad_wrapper_is_bad_logged {hash : List UInt8 → Digest} {t : Nat}
    (P : SrProver R 0) (p : List R.Chal → OpenedPlan hash)
    (rc : List R.Chal → Receipt) (coins : Fin t → R.Chal)
    (h : wrapperCheck (p ((srTrace P coins).map Prod.snd)) (ContextualGate.loggedOracle P coins)
      (rc ((srTrace P coins).map Prod.snd))=true)
    (bad : ¬LogicalStep (p ((srTrace P coins).map Prod.snd))) :
    ContextualGate.BadLoggedOutput P (fun responses => receiptOutput (rc responses)) coins := by
  refine ⟨bad_step_is_global_bad _ _ _ h bad,?_⟩
  rw [wrapper_acceptance_transport _ _ _ h]
  exact Option.some_ne_none _

/-- No extra M factor: every final verifier prefix has already been queried
in the same total budget t. Selecting a bad public full word needs no new query.
The common oracle may be queried adaptively across all the plans' contexts. -/
theorem all_logged_bad_steps_bound {hash : List UInt8 → Digest} {M t : Nat}
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (153 : ℝ))) (hM : 0<M)
    (P : SrProver R 0) (plans : Fin M → List R.Chal → OpenedPlan hash)
    (receipts : Fin M → List R.Chal → Receipt)
    (closed : ContextualGate.AllOutputQueriesLogged t P
      (fun j responses => receiptOutput (receipts j responses))) :
    uniformProb ((Fin t → R.Chal) × (Fin R.k → R.Chal))
      (fun coins => ∃ j : Fin M,
        wrapperCheck (plans j ((srTrace P coins.1).map Prod.snd))
          (ContextualGate.loggedOracle P coins.1) (receipts j ((srTrace P coins.1).map Prod.snd))=true ∧
        ¬LogicalStep (plans j ((srTrace P coins.1).map Prod.snd))) ≤
      ((t : ℝ)+9) * (161 / ((2013265921 : ℝ)^6)) := by
  have hδ' : δ ∈ Set.Ioo (0 : ℝ) (1 / (descriptor.nWires : ℝ)) := by
    rw [descriptor_shape.2.2.1]; exact hδ
  have hb := ContextualGate.all_logged_outputs_bound residuals_fit hδ' hM P
    (fun j responses => receiptOutput (receipts j responses)) closed
  rw [gate_price_explicit] at hb
  refine le_trans (uniformProb_mono ?_) hb
  rintro coins ⟨j,hj,hbad⟩
  exact ⟨j,bad_wrapper_is_bad_logged P (plans j) (receipts j) coins.1 hj hbad⟩

/-- Proposed EMA query encoder: use the existing prefix-decodable root/word
codec at the new descriptor width. No deployed EMA byte-oracle is assumed. -/
def emaRootBytes (rt : Root) : List UInt8 :=
  rootCodec.encode (contextWords rt.1, List.ofFn fun i => (rt.2 i).val)

theorem ema_root_bytes_injective : Function.Injective emaRootBytes := by
  intro a b h
  have hw := streamEncode_injective rootCodec h
  apply Prod.ext (contextWords_injective (congrArg Prod.fst hw))
  exact word_values_injective (congrArg Prod.snd hw)

def queryBytes (q : SrMove R 0) : List UInt8 := ContextualGate.queryBytes emaRootBytes q

theorem query_bytes_injective : Function.Injective queryBytes :=
  ContextualGate.query_bytes_injective emaRootBytes ema_root_bytes_injective

theorem query_bytes_match_fixed_encoder (c : Context) (q : SrMove R 0) :
    queryBytes q = encodeMove (scheme c).commit descriptor (bitCorner 8) descriptor_nonempty
      emaRootBytes (ContextualGate.toFixed c q) := rfl

/-- These existing full-word encodings are disjoint even for arbitrary queried
contexts: the decoded public-word vector has length4131 versus153. This is an
encoding theorem, not yet a mixed-program oracle-game reduction. -/
theorem program_query_domains_disjoint
    (a : SrMove ResidentAdaptiveContext.adaptiveReduction 0) (b : SrMove R 0) :
    ResidentAdaptiveContext.queryBytes a ≠ queryBytes b := by
  intro h
  have hw := streamEncode_injective moveStream h
  have hl := congrArg (fun w : List UInt8 × (List Nat × List (List Nat)) => w.2.1.length) hw
  have lengths : (4131 : Nat)=descriptor.nWires := by
    simpa only [moveWire,List.length_ofFn] using hl
  rw [descriptor_shape.2.2.1] at lengths
  norm_num at lengths

def programQueryBytes : Sum (SrMove ResidentAdaptiveContext.adaptiveReduction 0)
    (SrMove R 0) → List UInt8 := Sum.elim ResidentAdaptiveContext.queryBytes queryBytes

theorem program_query_bytes_injective : Function.Injective programQueryBytes := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (ResidentAdaptiveContext.query_bytes_injective h)
    | inr b => exact False.elim (program_query_domains_disjoint a b h)
  | inr a =>
    cases b with
    | inl b => exact False.elim (program_query_domains_disjoint b a h.symm)
    | inr b => exact congrArg Sum.inr (query_bytes_injective h)

theorem same_receipt_inhabited (O : SrMove R 0 → Ext6L) :
    ∃ rc : Receipt,
      wrapperCheck (ResidentEmaWitness.p ResidentEmaWitness.publicHash) O rc=true ∧
      descriptorHolds descriptor (traceOf rc.word) ∧
      LogicalStep (ResidentEmaWitness.p ResidentEmaWitness.publicHash) ∧
      fiatShamir R 0 O (receiptOutput rc)=some ((),fun _=>()) := by
  let p := ResidentEmaWitness.p ResidentEmaWitness.publicHash
  obtain ⟨rc,hcheck,same⟩ := receipt_of_linked p (candidateWord 128 248 143 0)
    (fun q => O (ContextualGate.fromFixed p.plan.context q))
    (ResidentEmaWitness.witness_linked _) ResidentEmaWitness.witness_descriptor
  have hd : descriptorHolds descriptor (traceOf rc.word) := by
    rw [same]; exact ResidentEmaWitness.witness_descriptor
  exact ⟨rc,hcheck,hd,checked_logical_step p _ rc hcheck hd,
    wrapper_acceptance_transport p O rc hcheck⟩

/-- The same receipt also inhabits the actual finality/opening/recipient gate,
not only the arithmetic wrapper. These facts are all for one oracle and one rc. -/
theorem same_authorized_receipt_inhabited (O : SrMove R 0 → Ext6L) :
    ∃ rc : Receipt,
      authorized ResidentEmaWitness.q (ResidentEmaWitness.book ResidentEmaWitness.publicHash)
        ResidentEmaWitness.selected (ResidentEmaWitness.before ResidentEmaWitness.publicHash)
        (ResidentEmaWitness.p ResidentEmaWitness.publicHash) ResidentEmaWitness.cert
        (fun q => O (ContextualGate.fromFixed
          (ResidentEmaWitness.p ResidentEmaWitness.publicHash).plan.context q)) rc=true ∧
      wrapperCheck (ResidentEmaWitness.p ResidentEmaWitness.publicHash) O rc=true ∧
      descriptorHolds descriptor (traceOf rc.word) ∧
      LogicalStep (ResidentEmaWitness.p ResidentEmaWitness.publicHash) ∧
      fiatShamir R 0 O (receiptOutput rc)=some ((),fun _=>()) := by
  obtain ⟨rc,ha,hd,hs⟩ := ResidentEmaWitness.public_subject
    (fun q => O (ContextualGate.fromFixed
      (ResidentEmaWitness.p ResidentEmaWitness.publicHash).plan.context q))
  have hc : wrapperCheck (ResidentEmaWitness.p ResidentEmaWitness.publicHash) O rc=true := by
    have parts := ha
    simp only [authorized,Bool.and_eq_true] at parts
    exact parts.1.2
  exact ⟨rc,ha,hc,hd,hs,wrapper_acceptance_transport _ O rc hc⟩

theorem exact_radius_inhabited :
    (1 / (306 : ℝ)) ∈ Set.Ioo (0 : ℝ) (1 / (153 : ℝ)) := by norm_num

theorem nine_query_same_receipt_premise_inhabited :
    ∃ rc : Receipt,
      let out := receiptOutput rc
      let P := ContextualGate.completeVerifier (M:=1) (by decide) (fun _=>out)
      ContextualGate.AllOutputQueriesLogged 9 P (fun _j : Fin 1 => fun _=>out) ∧
      wrapperCheck (ResidentEmaWitness.p ResidentEmaWitness.publicHash)
        (ContextualGate.loggedOracle P (fun _ : Fin 9 => ext6Zero)) rc=true ∧
      descriptorHolds descriptor (traceOf rc.word) ∧
      fiatShamir R 0 (ContextualGate.loggedOracle P (fun _ : Fin 9 => ext6Zero)) out=
        some ((),fun _=>()) := by
  obtain ⟨rc,hcheck,hd,_,hfs⟩ := same_receipt_inhabited (fun _=>ext6Zero)
  refine ⟨rc,ContextualGate.planned_verifier_logs_all (by decide) (fun _ : Fin 1=>receiptOutput rc),?_,hd,?_⟩
  · rw [ContextualGate.zero_sampled_oracle]; exact hcheck
  · rw [ContextualGate.zero_sampled_oracle]; exact hfs

theorem empty_query_log_fails (P : SrProver R 0) (rc : Receipt) :
    ¬ContextualGate.AllOutputQueriesLogged 0 P (fun _j : Fin 1=>fun _=>receiptOutput rc) :=
  ContextualGate.empty_log_not_complete P (receiptOutput rc)

theorem materialized_linked_wrong_step_fails_descriptor :
    ResidentEmaRelease.Linked ResidentEmaWitness.forged (candidateWord 128 248 144 0) ∧
      ¬descriptorHolds descriptor (traceOf (candidateWord 128 248 144 0)) :=
  ⟨ResidentEmaWitness.forged_linked,
    ResidentEmaWitness.constant_wrong_post_descriptor_refused _ ResidentEmaWitness.forged_linked⟩

end Minidregg.Assurance.ResidentEmaAdaptive

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.stage0_reduction_is_existing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.stage0_reduction_is_existing

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.wrapper_acceptance_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.wrapper_acceptance_transport

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.bad_step_is_global_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.bad_step_is_global_bad

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.descriptor_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.descriptor_parameters

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.single_bad_receipt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.single_bad_receipt_bound

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.bad_wrapper_is_bad_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.bad_wrapper_is_bad_logged

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.all_logged_bad_steps_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.all_logged_bad_steps_bound

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.ema_root_bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.ema_root_bytes_injective

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.query_bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.query_bytes_injective

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.query_bytes_match_fixed_encoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.query_bytes_match_fixed_encoder

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.program_query_domains_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.program_query_domains_disjoint

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.program_query_bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.program_query_bytes_injective

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.same_receipt_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.same_receipt_inhabited

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.same_authorized_receipt_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.same_authorized_receipt_inhabited

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.exact_radius_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.exact_radius_inhabited

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.nine_query_same_receipt_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.nine_query_same_receipt_premise_inhabited

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.empty_query_log_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.empty_query_log_fails

/-- info: 'Minidregg.Assurance.ResidentEmaAdaptive.materialized_linked_wrong_step_fails_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentEmaAdaptive.materialized_linked_wrong_step_fails_descriptor

