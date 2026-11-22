import Obend.Vault.Rehydration
import Obend.Consensus.Simplex
import Obend.Consensus.SimplexProtocol
import Obend.Analysis.Hybrid
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/InnerSeamWeldTest.lean` — Inner-System Seam Weld Verification & Axiom Audit

End-to-end verification of the inner-system welds:
1. **`Obend.Vault.Rehydration`** — `AttestedRoot`, `confined`, `classify`, `witnessChainOf`,
   `MembraneViewer`, `Membrane.reshare`, `Sturdyref`, `rehydrateSturdyref`, and `ReactiveAffordance`.
2. **`Obend.Consensus.Simplex` & `Obend.Consensus.SimplexProtocol`** — `Config`, `viewTimeout`,
   `honest_quorum_intersection`, `qc_same_view_unique`, `exponential_backoff_timing`, and
   `SimplexProtocol` (`Reach`, `FinCert.checks`, `FinCert.unique_per_height_reach`).
3. **`Obend.Analysis.Hybrid`** — `HybridProblem` / `HybridCert` `Core.Data` codecs,
   `stepHybrid`, `verifyFlowpipe` + unsafe-zone disjointness check, and
   `hybridFlowpipeFormat : Obend.Judge.Format` (`"hybrid-flowpipe@1"`).
-/

namespace Obend.Tests.InnerSeamWeldTest

open Obend.Core
open Obend.Vault.Affordance (Auth fireGate CellAffordance FireCtx)
open Obend.Vault.Rehydration
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Analysis

-- ============================================================================
-- 1. Vault Rehydration Inner-System Weld Tests
-- ============================================================================

def sampleGoodRoot : AttestedRoot := { root := 101, v4Complete := true, quorum := true }
def sampleBadRoot : AttestedRoot := { root := 101, v4Complete := true, quorum := false }

def sampleConfinedLog : InteractionLog := [.attested sampleGoodRoot, .attested sampleGoodRoot]
def sampleAmbientLog : InteractionLog := [.attested sampleGoodRoot, .ambient]
def sampleForgedLog : InteractionLog := [.attested sampleGoodRoot, .attested sampleBadRoot]

def sampleReceiptHash (r : WitnessReceipt) : Nat :=
  r.prevHash + r.oldCommit + r.newCommit + r.effectsHash + 1

#guard confined sampleConfinedLog == true
#guard classify sampleConfinedLog false == .ReplayedDeterministic
#guard classify sampleAmbientLog false == .ReconstructedApproximate
#guard classify sampleForgedLog false == .ReconstructedApproximate
#guard classify sampleAmbientLog true == .Live
#guard (witnessChainOf sampleReceiptHash sampleConfinedLog).length == 2
#guard (witnessChainOf sampleReceiptHash sampleAmbientLog).length == 1

def weldChairViewer : MembraneViewer :=
  { held := [.read, .write, .grant]
    permits := fun n => n == "vote" || n == "resolve"
    activeNames := ["vote", "resolve"] }

def weldMemberViewer : MembraneViewer :=
  { held := [.read, .write]
    permits := fun n => n == "vote"
    activeNames := ["vote"] }

def weldVoteAff : CellAffordance Nat :=
  { required := [.write], effect := 1, name := "vote" }

def weldResolveAff : CellAffordance Nat :=
  { required := [.grant], effect := 2, name := "resolve" }

def weldSturdyref : Sturdyref Nat :=
  { uri := "obend://weld/surface"
    surface := [weldVoteAff, weldResolveAff]
    log := sampleConfinedLog
    lineage := weldChairViewer
    reachable := false }

#guard (Membrane.reshare weldChairViewer weldMemberViewer).isSome == true
#guard (Membrane.reshare weldMemberViewer weldChairViewer).isNone == true
#guard (rehydrateSturdyref weldSturdyref weldChairViewer).1.length == 2
#guard (rehydrateSturdyref weldSturdyref weldMemberViewer).1.length == 1
#guard (rehydrateSturdyref weldSturdyref weldMemberViewer).2 == .ReplayedDeterministic

example (log : InteractionLog) :
    classify log false = .ReplayedDeterministic ↔ confined log = true :=
  replayedDeterministic_iff_confined log

theorem weld_confined_replays (log : InteractionLog) (hc : confined log = true) :
    classify log false = .ReplayedDeterministic := by
  unfold classify
  simp [hc]

theorem weld_amplifying_reshare_none (holder delegate : MembraneViewer)
    (hamp : fireGate delegate.held holder.held = false) :
    Membrane.reshare holder delegate = none := by
  unfold Membrane.reshare
  simp [hamp]

#tooth weld_confined_replays by mutation
  Obend.Vault.Rehydration.classify := fun _ _ => Rehydration.ReconstructedApproximate

#tooth weld_amplifying_reshare_none by mutation
  Obend.Vault.Rehydration.Membrane.reshare := fun _ d => some d

-- ============================================================================
-- 2. Consensus Simplex BFT Inner-System Weld Tests
-- ============================================================================

def demoSimplexConfig : Config :=
  { parties := 4, faults := 1, timeout := 100, pumpBudget := 64, backoffCap := 3 }

def badSimplexConfig : Config :=
  { parties := 5, faults := 1, timeout := 100, pumpBudget := 64, backoffCap := 3 }

#guard demoSimplexConfig.wellFormed == true
#guard badSimplexConfig.wellFormed == false
#guard demoSimplexConfig.quorum == 3
#guard viewTimeout 100 0 3 == 100
#guard viewTimeout 100 2 3 == 400
#guard viewTimeout 100 5 3 == 800

def demoProtocol : Protocol where
  committee := [0, 1, 2, 3]
  f := 1
  faulty := fun n => n == 3
  nodup := by decide
  size := by decide
  faultBound := by decide

def demoSentFinalized : Sent :=
  [ ⟨0, 1, .finalize, .block [.block 1 42]⟩
  , ⟨1, 1, .finalize, .block [.block 1 42]⟩
  , ⟨2, 1, .finalize, .block [.block 1 42]⟩ ]

def demoFinCert : FinCert :=
  { view := 1, chain := [.block 1 42], signers := [0, 1, 2] }

def demoUnderQuorumFinCert : FinCert :=
  { view := 1, chain := [.block 1 42], signers := [0, 1] }

#guard demoFinCert.checks demoProtocol demoSentFinalized == true
#guard demoUnderQuorumFinCert.checks demoProtocol demoSentFinalized == false

example (base views cap : Nat) :
    viewTimeout base views cap ≤ base * 2 ^ cap :=
  exponential_backoff_timing base views cap

#tooth Obend.Consensus.Simplex.exponential_backoff_timing by mutation
  Obend.Consensus.Simplex.viewTimeout := fun base views _ => base * (2 ^ views)

theorem weld_under_quorum_finCert_rejected (P : Protocol) (sent : Sent) (c : FinCert)
    (hshort : c.signers.length < P.quorum) :
    c.checks P sent = false := by
  unfold FinCert.checks
  have hdec : decide (P.quorum ≤ c.signers.length) = false :=
    decide_eq_false (Nat.not_le.mpr hshort)
  rw [hdec, Bool.and_false, Bool.false_and]

#tooth weld_under_quorum_finCert_rejected by mutation
  Obend.Consensus.SimplexProtocol.FinCert.checks := fun _ _ _ => true

-- ============================================================================
-- 3. Hybrid Flowpipe Judge (`"hybrid-flowpipe@1"`) Inner-System Weld Tests
-- ============================================================================

-- Format name and roundtrip codecs for `HybridProblem` and `HybridCert`.
#guard hybridFlowpipeFormat.name == "hybrid-flowpipe@1"
#guard HybridProblem.ofData? demoHybridProblem.toData == some demoHybridProblem
#guard HybridProblem.ofData? (.natural 42) == none
#guard HybridCert.ofData? validHybridCert.toData == some validHybridCert
#guard HybridCert.ofData? badHybridCert.toData == some badHybridCert
#guard HybridCert.ofData? (.label "bad") == none

example (p : HybridProblem) : HybridProblem.ofData? p.toData = some p :=
  HybridProblem.ofData_toData p

example (c : HybridCert) : HybridCert.ofData? c.toData = some c :=
  HybridCert.ofData_toData c

-- `verifyFlowpipe` and `checkHybridFlowpipe` accept `validHybridCert` and boundary intervals
-- (`lo = envLo`, `hi = unsafeLo - 1`) while rejecting `badHybridCert`, `badStepCountHybridCert`,
-- inverted intervals (`initLo > initHi`), bogus modes, and unsafe-zone collisions (`hi = unsafeLo`).
#guard verifyFlowpipe demoHybridProblem validHybridCert == true
#guard verifyFlowpipe { demoHybridProblem with unsafeLo := 31, unsafeHi := 50 } validHybridCert == true
#guard verifyFlowpipe { demoHybridProblem with unsafeLo := 30, unsafeHi := 50 } validHybridCert == false
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "cooling", initLo := 17, initHi := 20 }
  { schedule := [.flowStep], expectedFinalMode := "cooling", claimedSteps := 1 } == true
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "cooling", initLo := 15, initHi := 20 }
  { schedule := [.flowStep], expectedFinalMode := "cooling", claimedSteps := 1 } == false
#guard verifyFlowpipe { demoHybridProblem with initLo := 26, initHi := 24 } validHybridCert == false
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "bogus", initLo := 20, initHi := 22 }
  { schedule := [], expectedFinalMode := "bogus", claimedSteps := 0 } == false
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "heating", initLo := 34, initHi := 35 }
  { schedule := [], expectedFinalMode := "heating", claimedSteps := 0 } == false
#guard verifyFlowpipe demoHybridProblem badHybridCert == false
#guard verifyFlowpipe demoHybridProblem badStepCountHybridCert == false
#guard verifyFlowpipe { demoHybridProblem with unsafeLo := 25, unsafeHi := 30 } validHybridCert == false
#guard checkHybridFlowpipe 0 demoHybridProblem validHybridCert == .ok
#guard checkHybridFlowpipe 0 demoHybridProblem badHybridCert ==
  .refused "flowpipe_invariant_or_unsafe_zone_violation" []

example :
    ∃ msg cs,
      Obend.Judge.check hybridFlowpipeFormat.badGrade
        hybridFlowpipeFormat.bad.1 hybridFlowpipeFormat.bad.2 = .refused msg cs :=
  hybridFlowpipeFormat.bad_refused

-- `#tooth` probe: `verifyFlowpipe` rejects `badHybridCert`.
theorem test_badHybridCert_rejected :
    verifyFlowpipe demoHybridProblem badHybridCert = false := by decide +kernel

#tooth test_badHybridCert_rejected by mutation
  verifyFlowpipe := fun _ _ => true

-- ============================================================================
-- 4. Axiom Audit (`0 sorryAx`, `0 Classical.choice`)
-- ============================================================================

#print axioms replayedDeterministic_iff_confined
#print axioms reshare_chain_attenuates
#print axioms rehydrateSturdyref_reshare_monotone
#print axioms fireReactive_iff
#print axioms honest_quorum_intersection
#print axioms qc_same_view_unique
#print axioms exponential_backoff_timing
#print axioms FinCert.unique_per_height_reach
#print axioms HybridProblem.ofData_toData
#print axioms HybridCert.ofData_toData
#print axioms hybridFlowpipeFormat

end Obend.Tests.InnerSeamWeldTest
