module
/-
# `Obend.Teeth.Extracted.CoreTeeth` — Core, Equiv, FFI, Ledger, Logic, Reasons, Kind, Law & Spec Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (33 mutation witnesses) extracted from
Tier-1 `Obend` modules so `lake build Obend` elaborates pure definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Analysis.Impact
import all Obend.Analysis.Hybrid
import all Obend.Analysis.SosLyapunov
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.SimplexTrace
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Check
import all Obend.Core.Checkpoint
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Packet
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraphHead
import all Obend.Digest.Cshake256
import all Obend.Digest.HashBytes
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Doc.WorkbookEngine
import all Obend.Elab.AutoCert
import all Obend.Elab.Gate
import all Obend.Elab.Work
import all Obend.Elab.Workbook
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Clairvoyant
import all Obend.Equiv.Simulation
import all Obend.FFI.Bridge
import all Obend.FFI.BridgeTypes
import all Obend.Fold
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Judge
import all Obend.Intention
import all Obend.Judge
import all Obend.Judge.AutomataConfinement
import all Obend.Judge.Certified
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Genealogy
import all Obend.Judge.Identity
import all Obend.Judge.Instances
import all Obend.Judge.Lrat
import all Obend.Judge.Netting
import all Obend.Judge.RealAnalysis
import all Obend.Judge.TranscriptPolicy
import all Obend.Kind
import all Obend.Kind.Proofs
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Specialize
import all Obend.Leaf.UpTo
import all Obend.Ledger.Book
import all Obend.Ledger.Commit
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.Lower.Judge
import all Obend.Lower.Proofs.Complete
import all Obend.Lower.Transport
import all Obend.Reasons
import all Obend.Reasons.UnifiedEquilibrium
import all Obend.Receipt.Merkle
import all Obend.Run.Core4
import all Obend.Run.Fork
import all Obend.Run.HyperLaw
import all Obend.Run.Proofs.Shared
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.Annotated
import all Obend.Spec.C4
import all Obend.Spec.Capture
import all Obend.Spec.CrossPackage
import all Obend.Spec.DataWire
import all Obend.Spec.Ecosystem
import all Obend.Spec.Elaborate
import all Obend.Spec.FrontEnd
import all Obend.Spec.Identity
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.PackageLaw
import all Obend.Spec.Parse
import all Obend.Spec.Preview
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.Ecosystem
import all Obend.Spec.Sha256
import all Obend.Spec.Syntax
import all Obend.Spec.Types
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Vault.WorldTree
import all Obend.Vault.Form
import all Obend.Vault.FormCheckCache
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Json
import all Obend.Vault.Law
import all Obend.Vault.Log
import all Obend.Vault.Merge
import all Obend.Vault.Replay
import all Obend.Vault.Retention
import all Obend.Vault.Store
import all Obend.Vault.Transport

public section
end

namespace Obend.Teeth.Extracted.CoreTeeth
/-! ## Extracted from `Obend.Core.Code` (1 teeth) -/
section Obend_Core_Code
open Obend.Core.Code
open Obend.Core.Term
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag Shape encode decode decode_encode)
open Obend.Core.Data (Data)
open Obend.Digest.HashBytes (Hash Collision ofBE be ofBE_lt)
open Obend.Core.Digest (digestWith deployed Admissible admissible_of_lt binds_or_collides lengthHash)
open Obend.Core.Ty (Ty Quantity Reuse LambdaAnnotation Context Binding)
open Obend.Core.Check (Assumptions AnnotatedTerm Checked PartialTyping HoleDecl)
open Obend.Core.Bidirectional (CheckRefusal checkAgainst checkAgainst_sound)
open Obend.Elab.Work (checkWork)
open Obend.Core.Proofs.BidirectionalCompleteness (AnnotationTree treeAnnotations)

#tooth quote_roundtrip by mutation tagData := lossyTagData

end Obend_Core_Code

/-! ## Extracted from `Obend.Equiv.Clairvoyant` (1 teeth) -/
section Obend_Equiv_Clairvoyant
open Obend.Equiv
open Obend.Core.Term

private def deadLetBindBroken (deadExpr _body : Term) : Term := deadExpr

#tooth Obend.Equiv.clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper by mutation
  Obend.Equiv.deadLetBind := deadLetBindBroken

end Obend_Equiv_Clairvoyant

/-! ## Extracted from `Obend.FFI.Bridge` (1 teeth) -/
section Obend_FFI_Bridge
open Obend.FFI
open Lean (Json toJson)
open Obend.Core
open Obend.Core.Data (Data)
open Obend.Vault
open Obend.Doc
open Obend.Receipt.Merkle
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

#tooth turnCommitCore_unproposed_tid_refused by mutation
  turnCommitCore := fun s _ => (s, 0)

end Obend_FFI_Bridge

/-! ## Extracted from `Obend.Ledger.Register` (1 teeth) -/
section Obend_Ledger_Register
open Obend.Ledger

-- Tooth: a register that never finds a document's live posting does not keep "posted once".
#tooth step_once by mutation Reg.liveOf := fun _ _ => none

end Obend_Ledger_Register

/-! ## Extracted from `Obend.Logic.Obligation` (3 teeth) -/
section Obend_Logic_Obligation
open Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Lean (Json toJson)

/-- Mutated `ClaimObj.withLhs` that replaces the whole claim with `lhs'` without equation binders. -/
private def withLhsBroken (o : ClaimObj) (lhs' : Term) : ClaimObj :=
  { o with claim := lhs' }

#tooth Obend.Logic.claimMeaning_of_bEquiv by mutation
  Obend.Logic.ClaimObj.withLhs := withLhsBroken

#tooth Obend.Logic.verifyByBisimRefinement_sound by mutation
  Obend.Logic.verifyByBisimRefinement := fun _ _ _ _ => .ok

#tooth Obend.Logic.obligationCheck_refuses_false_external_claim by mutation
  Obend.Logic.externalClaimBound := fun _ _ _ => true

end Obend_Logic_Obligation

/-! ## Extracted from `Obend.Reasons.UnifiedEquilibrium` (2 teeth) -/
section Obend_Reasons_UnifiedEquilibrium
open Obend.Reasons.UnifiedEquilibrium
open Obend

-- Mutation witnesses: breaking `checkGLStable` or `checkSameSet` is immediately caught by the kernel.
#tooth oddLoop_refused_by_judge by mutation checkGLStable := fun _ _ => true

#tooth checkGLStable_sound by mutation checkSameSet := fun _ _ => true

end Obend_Reasons_UnifiedEquilibrium

/-! ## Extracted from `Obend.Kind.Proofs` (4 teeth) -/
section Obend_Kind_Proofs
open Obend.Kind
open Obend.Core.Term (Term)
open Obend.Core.Data (Data)
open Obend.Law (Admits)

#tooth dispatch_sound by mutation dispatch := fun _ _ _ _ => .ok none

#tooth effectiveOf_ok by mutation effectiveOf := fun _ _ => .ok lawAdmit

#tooth create_carries by mutation create := fun _ k n l => .ok ⟨n, ⟨k, 0, []⟩, l, .natural 0⟩

-- A pin of the kind's own version alone (the pre-2026-11-01 pin) stays current when an ancestor moves.
#tooth stale_tooth by mutation KindPin.lineage := fun p => [⟨p.name, p.version⟩]

end Obend_Kind_Proofs

/-! ## Extracted from `Obend.Law.Proofs.Inherit` (2 teeth) -/
section Obend_Law_Proofs_Inherit
open Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)

#tooth precedence_local by mutation Obend.Spec.C4.cleanAll := fun _ ls => some (ls.map fun _ => [])

#tooth precedence_monotone by mutation Obend.Spec.C4.cleanAll := fun _ ls => some (ls.map fun _ => [])

end Obend_Law_Proofs_Inherit

/-! ## Extracted from `Obend.Spec.CrossPackage` (2 teeth) -/
section Obend_Spec_CrossPackage
open Obend.Spec.CrossPackage Obend.Spec.CrossPackage.CrossPackageLink
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Lower
open Obend.Slot
open Obend.Slot.World

/-- Mutated `rebindEquivPin` that leaves the stale pin untouched instead of re-pinning to `linkComposition C L`. -/
private def rebindEquivPinBroken {C : Composition} {L : Layer} {m : String}
    (_cert : EquivOverrideCert C L m) (p : LeafPin) : LeafPin :=
  p

/-- Mutated `compContext` that drops `F` and returns `C` unchanged. -/
private def compContextBroken (C _F : Term) : Term :=
  C

#tooth Obend.Spec.CrossPackage.crossPackage_bEquiv_override_preserves_semantics by mutation
  Obend.Spec.CrossPackage.compContext := compContextBroken

#tooth Obend.Spec.CrossPackage.crossPackage_bEquiv_rebinds_slot_usable by mutation
  Obend.Spec.CrossPackage.rebindEquivPin := rebindEquivPinBroken

end Obend_Spec_CrossPackage

/-! ## Extracted from `Obend.Spec.Proofs.Ecosystem` (3 teeth) -/
section Obend_Spec_Proofs_Ecosystem
open Obend.Spec.Ecosystem
open Obend.Slot

#tooth turn_pins_every_root by mutation covered := fun _ _ _ _ => none

#tooth admit_refuses_moved by mutation admit := fun _ _ => .diverged

#tooth stale_iff_blocked by mutation holds := fun _ _ => true

end Obend_Spec_Proofs_Ecosystem

/-! ## Extracted from `Obend.Spec.Proofs.PackageLaw` (1 teeth) -/
section Obend_Spec_Proofs_PackageLaw
open Obend.Spec.PackageLaw
open Obend.Law
open Obend.Core.Term
open Obend.Core.Data (Data)

#tooth package_law_eval by mutation packageClauses := fun _ _ => []

end Obend_Spec_Proofs_PackageLaw
end Obend.Teeth.Extracted.CoreTeeth

section FixedWidthCommitments
open Obend.Core.Digest
open Obend.Receipt.Merkle
#tooth Obend.Core.Digest.preimage256_injective by mutation
  Obend.Core.Digest.preimage256 := fun a _ => pair256DomainTag ++ bytes32OfDigest256 a
#tooth Obend.Core.Digest.binds256_or_collides by mutation
  Obend.Core.Digest.preimage256 := fun a _ => pair256DomainTag ++ bytes32OfDigest256 a
#tooth Obend.Receipt.Merkle.climb256_path256 by mutation
  Obend.Receipt.Merkle.climb256 := fun _ _ _ x _ => some x
#tooth Obend.Receipt.Merkle.opens256_binds_or_collides by mutation
  Obend.Receipt.Merkle.climb256 := fun _ _ _ _ _ => some 0
end FixedWidthCommitments

section MerkleInBounds
open Obend.Receipt.Merkle
/-- `climb` at size 1 returns its leaf whatever the index, so position 5 of a one-leaf map would
open against that leaf's own digest; `opens` refuses the position, under every hash. -/
theorem Obend.Receipt.Merkle.opens_refuses_oob_index (H : Obend.Digest.HashBytes.Hash) (v : Nat) :
    opens H ⟨1, 5, v, []⟩ (leaf H 5 v) = false := by
  simp [opens]
#tooth Obend.Receipt.Merkle.opens_refuses_oob_index by mutation
  Obend.Receipt.Merkle.opens := fun H o r =>
    Small o.index && climb H o.size o.index (leaf H o.index o.value) o.path == some r
end MerkleInBounds

section SignedSimplexAndCam
open Obend.Consensus.SimplexTrace
#tooth encodeMsgBytes_injective by mutation
  encodeMsgBytes := fun tag m => Obend.Receipt.Merkle.encodeFields [tag,Obend.Receipt.Merkle.leb128 m.sender]
#tooth checkSignedSimplex_sound by mutation checkSignedSimplex := fun _ _ => .ok
#tooth checkTraceExec_eq_checkTrace by mutation checkTraceExec := fun _ _ => .ok ()
#tooth QuorumIndex.lookupVotes_ofSent_eq_votesFor by mutation QuorumIndex.lookupVotes := fun _ _ _ => 0
#tooth Obend.Hardware.GeometryCAM.checkCamGouge_sound by mutation
  Obend.Hardware.GeometryCAM.checkCamGouge := fun _ _ => .ok
example : Obend.Hardware.GeometryCAM.radialClear ⟨2,3⟩ ⟨0,1⟩ 1 = true := by decide
example : Obend.Hardware.GeometryCAM.radialClear ⟨0,0⟩ ⟨0,0⟩ 1 = false := by decide
#tooth Obend.Hardware.GeometryCAM.checkKdZ_vertical_radial by mutation
  Obend.Hardware.GeometryCAM.radialClear := fun _ _ _ => true
end SignedSimplexAndCam

/-! ## Simplex quorum `n - f` (gate G5, 2026-11-21)

* At `n = 5, f = 1` the old threshold `2f + 1 = 3` fails: two 3-member quorums `{0, 1, 2}` and
  `{0, 3, 4}` meet only in the faulty node `0` (`old_threshold_no_honest_overlap`), and the same
  split is a reachable run in which two blocks of view 1 each collect `2f + 1` votes
  (`old_threshold_two_blocks`), neither the `n - f = 4` that notarizes
  (`new_threshold_refuses_split`).
* The `n - f` threshold intersects there (`new_threshold_overlap`, `new_threshold_honest`), and the
  protocol theorem applies to the 5-node committee (`p5_notarized_block_unique`).
* The stored proofs of `honest_of_quorum` and `accountable_protocol` are rejected when
  `Protocol.quorum` is mutated back to `2 * P.f + 1`. -/

namespace Obend.Teeth.Extracted.CoreTeeth.SimplexQuorum

open Obend.Consensus.Simplex (honest_quorum_intersection_nf quorum_overlap_nf)
open Obend.Consensus.SimplexProtocol

/-! ## (a) `2f + 1` fails at `n = 5, f = 1` -/

def committee5 : List Nat := [0, 1, 2, 3, 4]
def faulty5 : Nat → Bool := (· == 0)
def quorumA : Nat → Bool := fun n => [0, 1, 2].contains n
def quorumB : Nat → Bool := fun n => [0, 3, 4].contains n

/-- Both sets are `2f + 1 = 3` quorums of a committee of `5 ≥ 3f + 1` with one faulty member, and
no member of both is honest. -/
theorem old_threshold_no_honest_overlap :
    3 * 1 + 1 ≤ committee5.length ∧
    2 * 1 + 1 ≤ (committee5.filter quorumA).length ∧
    2 * 1 + 1 ≤ (committee5.filter quorumB).length ∧
    (committee5.filter faulty5).length ≤ 1 ∧
    ¬ ∃ x ∈ committee5, quorumA x = true ∧ quorumB x = true ∧ faulty5 x = false := by
  decide

/-- Their only common member is the faulty one. -/
theorem old_threshold_overlap_is_faulty :
    committee5.filter (fun x => quorumA x && quorumB x) = [0] ∧ faulty5 0 = true := by
  decide

/-- **The `2f + 1` intersection statement is false for `n > 3f + 1`.** -/
theorem old_threshold_lemma_false :
    ¬ ∀ (l : List Nat) (f : Nat) (p q faulty : Nat → Bool),
      3 * f + 1 ≤ l.length → 2 * f + 1 ≤ (l.filter p).length → 2 * f + 1 ≤ (l.filter q).length →
      (l.filter faulty).length ≤ f → ∃ x ∈ l, p x = true ∧ q x = true ∧ faulty x = false := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := old_threshold_no_honest_overlap
  exact h5 (h committee5 1 quorumA quorumB faulty5 h1 h2 h3 h4)

/-- The 5-node protocol, node `0` faulty (and the leader of view 1). -/
def p5 : Protocol := ⟨committee5, 1, faulty5, by decide, by decide, by decide⟩

theorem p5_quorum : p5.quorum = 4 := by decide

def blockA : Chain := [.block 1 10]
def blockB : Chain := [.block 1 11]

/-- The faulty leader proposes and votes for both blocks; honest `1, 2` vote for `A`, honest `3, 4`
for `B`. Newest first. -/
def splitRun : Sent :=
  [ ⟨4, 1, .vote, .block blockB⟩, ⟨3, 1, .vote, .block blockB⟩
  , ⟨2, 1, .vote, .block blockA⟩, ⟨1, 1, .vote, .block blockA⟩
  , ⟨0, 1, .vote, .block blockB⟩, ⟨0, 1, .vote, .block blockA⟩
  , ⟨0, 1, .propose, .block blockB⟩, ⟨0, 1, .propose, .block blockA⟩ ]

private theorem voteRule_view1 (sent : Sent) (x : Nat)
    (hp : (⟨p5.leader 1, 1, .propose, .block [.block 1 x]⟩ : Msg) ∈ sent) :
    VoteRule p5 sent 1 (.block [.block 1 x]) :=
  ⟨Nat.le_refl 1, [], x, rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩

private theorem reach_vote {sent : Sent} (n x : Nat) (hn : n ∈ committee5 ∧ faulty5 n = false)
    (hfresh : votedAny sent n 1 = false)
    (hp : (⟨p5.leader 1, 1, .propose, .block [.block 1 x]⟩ : Msg) ∈ sent) (h : Reach p5 sent) :
    Reach p5 (⟨n, 1, .vote, .block [.block 1 x]⟩ :: sent) :=
  .step h (.vote sent n 1 _ hn hfresh (voteRule_view1 sent x hp))

private theorem reach_inject {sent : Sent} (m : Msg) (hf : faulty5 m.sender = true)
    (h : Reach p5 sent) : Reach p5 (m :: sent) :=
  .step h (.inject sent m hf)

/-- **`splitRun` is reachable**: every message is a step of the protocol (the faulty leader's four
by `inject`, the honest four by `vote`, each its sender's first vote of view 1). -/
theorem splitRun_reach : Reach p5 splitRun :=
  reach_vote 4 11 (by decide) (by decide) (by decide) <|
  reach_vote 3 11 (by decide) (by decide) (by decide) <|
  reach_vote 2 10 (by decide) (by decide) (by decide) <|
  reach_vote 1 10 (by decide) (by decide) (by decide) <|
  reach_inject _ (by decide) <| reach_inject _ (by decide) <|
  reach_inject _ (by decide) <| reach_inject _ (by decide) .nil

/-- **Under `2f + 1`, one reachable view would notarize two blocks**: both collect `3` votes. -/
theorem old_threshold_two_blocks :
    Reach p5 splitRun ∧ blockA ≠ blockB ∧
      2 * p5.f + 1 ≤ votesFor p5 splitRun 1 (.block blockA) ∧
      2 * p5.f + 1 ≤ votesFor p5 splitRun 1 (.block blockB) :=
  ⟨splitRun_reach, by decide, by decide, by decide⟩

/-- Under `n - f`, neither block of the split is notarized. -/
theorem new_threshold_refuses_split :
    ¬ NotarizedBlock p5 splitRun 1 blockA ∧ ¬ NotarizedBlock p5 splitRun 1 blockB := by
  decide

/-! ## (b) `n - f` holds at `n = 5, f = 1` -/

/-- Two `4`-member quorums of the five share at least `3 ≥ f + 1` members. -/
theorem new_threshold_overlap (p q : Nat → Bool)
    (hp : 4 ≤ (committee5.filter p).length) (hq : 4 ≤ (committee5.filter q).length) :
    3 ≤ (committee5.filter fun x => p x && q x).length :=
  quorum_overlap_nf committee5 1 p q hp hq

/-- ... and, with at most one faulty member, an honest one. -/
theorem new_threshold_honest (p q faulty : Nat → Bool)
    (hp : 4 ≤ (committee5.filter p).length) (hq : 4 ≤ (committee5.filter q).length)
    (hf : (committee5.filter faulty).length ≤ 1) :
    ∃ x ∈ committee5, p x = true ∧ q x = true ∧ faulty x = false :=
  honest_quorum_intersection_nf committee5 1 p q faulty (by decide) hp hq hf

/-- The protocol theorem at the 5-node committee: one view notarizes one block. -/
theorem p5_notarized_block_unique {sent : Sent} (hr : Reach p5 sent) {v : Nat} {c₁ c₂ : Chain}
    (h₁ : NotarizedBlock p5 sent v c₁) (h₂ : NotarizedBlock p5 sent v c₂) : c₁ = c₂ :=
  notarized_block_unique (reach_inv hr) h₁ h₂

/-! ## (c) Mutation teeth

`notarized_block_unique` cannot be the target: its closure reaches the structure `Inv` (and
`Step`, `Reach`), whose fields mention `NotarizedBlock`, hence `Protocol.quorum`; `#tooth`
refuses to clone affected inductives. `honest_of_quorum` and `accountable_protocol` are the
quorum-dependent steps every safety theorem goes through and reach no affected inductive. -/

#tooth Obend.Consensus.SimplexProtocol.honest_of_quorum by mutation
  Obend.Consensus.SimplexProtocol.Protocol.quorum := fun P => 2 * P.f + 1

#tooth Obend.Consensus.SimplexProtocol.accountable_protocol by mutation
  Obend.Consensus.SimplexProtocol.Protocol.quorum := fun P => 2 * P.f + 1

end Obend.Teeth.Extracted.CoreTeeth.SimplexQuorum
