/-
[DERIVED target; EXECUTED only after the recorded Lean check]
Context binding on the EXISTING full-word Stage-0 receipt. Research patch for
minidregg, not installed there. Its ROM price is inherited, not re-derived.

Statement-first target: for an independently selected context c, an accepted
receipt names c; outside the existing descriptor-failure event its boundary
executes c.next = c.output = (c.parent + c.command) mod 2^256. The delivery
record uses c.recipient. The authorization/genesis fields must be selected by
the independent finality/policy gate; equality is not authorization.

ATLAS: contextScheme realizes the binding carrier from any existing realizer;
honest_context_receipt inhabits acceptance for every admitted in-range add;
wrong_context_refused is the context tooth; wrong_next_not_linked is the
semantic tooth. Hiding, authenticated recipient delivery, fresh private coins,
and a resident transition descriptor remain FLOOR obligations. Stage 0 uses
public integers and the explicitly deterministic randomness rule (0,0).
-/
import Assurance.ReleaseGateRouting

namespace Minidregg.Assurance.ResidentReleaseContext

open Minidregg.Selvage
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Compiler.CommittedTerminalFiatShamir.Stage0
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Compiler.CommittedTerminalRealizer.Stage0Exhibit (wordOf stage0_residuals_fit)
open Minidregg.Compiler.CommittedTerminalController (Receipt)
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.EvmAddAir
open Minidregg.Assurance.ReleaseGateRouting

set_option autoImplicit false
set_option maxRecDepth 10000

/-- Exact context values in this public Stage-0 witness. Production must use
canonical typed encodings/commitments and bind their openings in the relation. -/
structure Context where
  genesis : Nat
  parent : Nat
  program : Nat
  version : Nat
  command : Nat
  authorization : Nat
  recipient : Nat
  randomnessRule : Nat
  randomnessCommitment : Nat
  next : Nat
  output : Nat
  deriving DecidableEq, Repr

/-- Generalization of the live binding commitment, with context in the ROOT.
No fixed-length hash injectivity premise. The context is fixed by the caller. -/
def contextScheme {Root F I Op : Type} (c : Context)
    (S : BindingCommitment Root F I Op) :
    BindingCommitment (Context × Root) F I Op where
  commit := fun w => (c, S.commit w)
  openAt := S.openAt
  verifyOpen := fun rt i v op => rt.1 = c ∧ S.verifyOpen rt.2 i v op
  verifyOpen_commit := fun w i => ⟨rfl, S.verifyOpen_commit w i⟩
  binding := fun rt i v v' op op' h h' => S.binding rt.2 i v v' op op' h.2 h'.2

abbrev Word := Fin 4131 → BabyBear
abbrev Root := Context × Word
def S (c : Context) := contextScheme c (idealCommitment BabyBear (Fin 4131))
noncomputable abbrev reduction (c : Context) :=
  gateReduction (S c).commit evmAddDescriptor (bitCorner 13) (by norm_num : 0 < 4131)

/-- Semantic linking, not merely hashing labels. Program 0/version 1 is the
compiled EVM addition descriptor. This witness's randomness rule is deterministic. -/
def Linked (c : Context) (w : Word) : Prop :=
  c.parent < 2^256 ∧ c.command < 2^256 ∧ c.output < 2^256 ∧
  c.next = c.output ∧ c.program = 0 ∧ c.version = 1 ∧
  c.randomnessRule = 0 ∧ c.randomnessCommitment = 0 ∧
  ∀ i : Fin 48, traceOf w i.val = encodeBoundary c.parent c.command c.output i

instance (c : Context) (w : Word) : Decidable (Linked c w) :=
  by unfold Linked; infer_instance

def check (expected : Context)
    (O : SrMove (reduction expected) 0 → Ext6L) (rc : FsReceipt Root 4131 13) : Bool :=
  decide (rc.root.1 = expected) && decide (Linked expected rc.word) &&
    (match fsCheck (S expected).commit evmAddDescriptor (bitCorner 13)
        (by norm_num) O rc with
     | .ok _ => true
     | .error _ => false)

def Forced (c : Context) : Prop :=
  c.next = (c.parent + c.command) % 2^256 ∧ c.output = c.next

def ContextBinding : Prop :=
  ∀ c O rc, check c O rc = true → rc.root.1 = c

def ArithmeticBinding : Prop :=
  ∀ c O rc, check c O rc = true →
    descriptorHolds evmAddDescriptor (traceOf rc.word) → Forced c

/-- Chosen context for the inhabitation witness; the transition is nonconstant. -/
def honestContext (x y : Nat) : Context :=
  ⟨7, x, 0, 1, y, 19, 23, 0, 0, (x+y) % 2^256, (x+y) % 2^256⟩

theorem relation_context (c : Context) (rt : Root) (w : Word) :
    (reduction c).R () rt w () ↔
      ((c, w) = rt ∧ descriptorHolds evmAddDescriptor (traceOf w)) := Iff.rfl

theorem context_binding : ContextBinding := by
  intro c O rc h
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem accepted_linked (c : Context) (O : SrMove (reduction c) 0 → Ext6L)
    (rc : FsReceipt Root 4131 13) (h : check c O rc = true) : Linked c rc.word := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem arithmetic_binding : ArithmeticBinding := by
  intro c O rc h hd
  obtain ⟨hx, hy, hz, hn, _, _, _, _, hp⟩ := accepted_linked c O rc h
  have hz' := stage0_released_output_forced c.parent c.command c.output
    hx hy hz (traceOf rc.word) hp hd
  exact ⟨hn.trans hz', hn.symm⟩

/-- The only arithmetic failure after acceptance is in the already-priced
descriptor failure event. No deterministic soundness of Fiat–Shamir is assumed. -/
theorem bad_release_implies_bad_descriptor (c : Context)
    (O : SrMove (reduction c) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (h : check c O rc = true) (bad : ¬ Forced c) :
    ¬ descriptorHolds evmAddDescriptor (traceOf rc.word) :=
  fun hd => bad (arithmetic_binding c O rc h hd)

theorem wrong_context_refused (c : Context)
    (O : SrMove (reduction c) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (wrong : rc.root.1 ≠ c) : check c O rc = false := by
  exact Bool.eq_false_iff.mpr (fun h => wrong (context_binding c O rc h))

theorem wrong_next_not_linked (c : Context) (w : Word) (wrong : c.next ≠ c.output) :
    ¬ Linked c w := fun h => wrong h.2.2.2.1

/-- The extension uses the existing priced FS protocol. This is a FIXED
context instance, not a new adaptive-policy/multi-session reduction. -/
theorem context_receipt_price (c : Context) :
    FsStraightlineKnowledgeSoundness (reduction c) Set.univ
      (fun _s t _δ => ((t : ℝ) + (13 + 1 : ℝ)) *
        ((0 : ℝ) + ((4148 - 1 : Nat) : ℝ) / ((2013265921 : ℝ)^6) +
          (13 : ℝ) * (1 / ((2013265921 : ℝ)^6)))) :=
  stage0Receipt_price (S c)

theorem accepted_fs (c : Context) (O : SrMove (reduction c) 0 → Ext6L)
    (rc : FsReceipt Root 4131 13) (h : check c O rc = true) :
    ∃ r, fsCheck (S c).commit evmAddDescriptor (bitCorner 13) (by norm_num) O rc = .ok r := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hfs := h.2
  cases hh : fsCheck (S c).commit evmAddDescriptor (bitCorner 13) (by norm_num) O rc with
  | ok r => exact ⟨r, rfl⟩
  | error e => simp only [hh] at hfs; contradiction

/-- Generic completeness keeps the large compiled candidate opaque. -/
theorem receipt_of_linked (c : Context) (w : Word)
    (O : SrMove (reduction c) 0 → Ext6L) (hl : Linked c w)
    (hd : descriptorHolds evmAddDescriptor (traceOf w)) :
    ∃ rc : FsReceipt Root 4131 13, check c O rc = true := by
  let rc := fsProve (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num) O ((S c).commit w) w
  refine ⟨rc, ?_⟩
  have hf := fsProve_complete (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num : 0 < 4131) O w
    (residualEmbedding evmAddDescriptor (traceOf w) stage0_residuals_fit)
    (fun _ => rfl) hd
  unfold check
  have hr : rc.root.1 = c := rfl
  have hw : rc.word = w := rfl
  rw [decide_eq_true hr, hw, decide_eq_true hl]
  change (match fsCheck (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num) O rc with | .ok _ => true | .error _ => false) = true
  rw [hf]

/-- Nonempty accepted receipt carrier, on the actual 4,131-wire descriptor. -/
theorem honest_context_receipt (x y : Nat) (hx : x < 2^256) (hy : y < 2^256)
    (O : SrMove (reduction (honestContext x y)) 0 → Ext6L) :
    ∃ rc : FsReceipt Root 4131 13, check (honestContext x y) O rc = true := by
  let c := honestContext x y
  let w := wordOf (evmAddCandidate x y)
  have hp : ∀ i : Fin 48, traceOf w i.val = encodeBoundary x y ((x+y) % 2^256) i := by
    intro i
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_pins x y i
  have hd : descriptorHolds evmAddDescriptor (traceOf w) := by
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_holds x y hx hy
  have hl : Linked c w :=
    ⟨hx, hy, Nat.mod_lt _ (by norm_num), rfl, rfl, rfl, rfl, rfl, hp⟩
  exact receipt_of_linked c w O hl hd

/-- The recipient field controls the returned destination of this PUBLIC
record. No encryption or transport confidentiality is supplied by this pair. -/
def delivery (c : Context) : Nat × Nat := (c.recipient, c.output)

theorem delivery_recipient (c : Context) : (delivery c).1 = c.recipient := rfl

theorem honest_changes_state : (honestContext 1 2).next ≠ (honestContext 1 2).parent := by decide

/-- Fixed-order, length-delimited encoding using the existing StreamCodec.
Versioning of this new wire profile is distinct from the transition version. -/
def contextWords (c : Context) : List Nat :=
  [c.genesis, c.parent, c.program, c.version, c.command, c.authorization,
   c.recipient, c.randomnessRule, c.randomnessCommitment, c.next, c.output]

theorem contextWords_injective : Function.Injective contextWords := by
  intro c d h
  cases c; cases d
  simp only [contextWords, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

def rootCodec : StreamCodec (List Nat × List Nat) :=
  StreamCodec.product (StreamCodec.list StreamCodec.nat) (StreamCodec.list StreamCodec.nat)

def rootBytes (rt : Root) : List UInt8 :=
  rootCodec.encode (contextWords rt.1, List.ofFn fun i => (rt.2 i).val)

/-- Prove the list conversion with abstract width, keeping the concrete
4,131-element list out of elaboration's definitional-equality evaluator. -/
theorem word_values_injective {n : Nat} :
    Function.Injective (fun w : Fin n → BabyBear => List.ofFn fun i => (w i).val) := by
  intro a b h
  funext i
  exact ZMod.val_injective _ (congrFun (List.ofFn_inj.mp h) i)

theorem rootBytes_injective : Function.Injective rootBytes := by
  intro a b h
  have hw := streamEncode_injective rootCodec h
  have hc := contextWords_injective (congrArg Prod.fst hw)
  have hv := congrArg Prod.snd hw
  apply Prod.ext hc
  exact word_values_injective hv

/-- Concrete context-aware cSHAKE input, in a separate wire-profile domain.
Injective input encoding is proved; collision resistance/ROM realization is not. -/
def contextOracle (c : Context) (query : SrMove (reduction c) 0) : Ext6L :=
  digestToExt6L (fsHash.xofDigest
    (Tower256ConcreteBackend.utf8 "MINIDREGG/RESIDENT/CT/FS/V1")
    (encodeMove (S c).commit evmAddDescriptor (bitCorner 13) (by norm_num) rootBytes query))

theorem context_query_encoding_injective (c : Context) :
    Function.Injective (encodeMove (S c).commit evmAddDescriptor (bitCorner 13)
      (by norm_num : 0 < 4131) rootBytes) :=
  encodeMove_injective (S c).commit evmAddDescriptor (bitCorner 13)
    (by norm_num) rootBytes rootBytes_injective

theorem concrete_oracle_receipt_inhabited :
    ∃ rc : FsReceipt Root 4131 13,
      check (honestContext 1 2) (contextOracle (honestContext 1 2)) rc = true :=
  honest_context_receipt 1 2 (by norm_num) (by norm_num) _

theorem context_word_count (c : Context) : (contextWords c).length = 11 := rfl

/-- Accepted carrier supplies the premise; altering only the recipient gives
an actual refused sibling, independent of arithmetic/FS challenge choices. -/
theorem recipient_substitution_refused (c : Context)
    (O : SrMove (reduction c) 0 → Ext6L) (rc : FsReceipt Root 4131 13)
    (h : check c O rc = true) :
    check c O { rc with root :=
      ({ rc.root.1 with recipient := rc.root.1.recipient + 1 }, rc.root.2) } = false := by
  apply wrong_context_refused
  intro hs
  have hn := congrArg Context.recipient hs
  change rc.root.1.recipient + 1 = c.recipient at hn
  rw [context_binding c O rc h] at hn
  omega

end Minidregg.Assurance.ResidentReleaseContext

/- Exact-output axiom pins, observed and checked against the kernel. -/

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.relation_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.relation_context

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.context_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.context_binding

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.accepted_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.accepted_linked

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.arithmetic_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.arithmetic_binding

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.bad_release_implies_bad_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.bad_release_implies_bad_descriptor

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.wrong_context_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.wrong_context_refused

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.wrong_next_not_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.wrong_next_not_linked

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.context_receipt_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.context_receipt_price

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.accepted_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.accepted_fs

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.receipt_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.receipt_of_linked

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.honest_context_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.honest_context_receipt

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.delivery_recipient' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.delivery_recipient

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.honest_changes_state' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.honest_changes_state

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.contextWords_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.contextWords_injective

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.word_values_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.word_values_injective

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.rootBytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.rootBytes_injective

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.context_query_encoding_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.context_query_encoding_injective

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.concrete_oracle_receipt_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.concrete_oracle_receipt_inhabited

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.context_word_count' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.context_word_count

/-- info: 'Minidregg.Assurance.ResidentReleaseContext.recipient_substitution_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentReleaseContext.recipient_substitution_refused
