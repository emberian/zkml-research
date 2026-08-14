/-
# Selvage.BaseFoldBcsFiatShamir — the exact BaseFold transcript alphabet

The BaseFold IOR and raw committed verifier already identify every algebraic,
query-miss, and commitment-equivocation event, while `FiatShamir` proves the
abstract public-coin-to-ROM compilation.  This module supplies the missing
construction-side alphabet for the BabyBear/Ext4/Poseidon2 profile.

The transcript is statement-first and causal.  Challenge `j` absorbs the
fixed profile and statement, all complete prior round frames, and the current
level root plus its three quadratic-sumcheck coefficients.  Only after all
round challenges does the query namespace absorb the terminal root and a
query label.  Opened values and all three binary-Merkle paths are retained in
the canonical proof alphabet, but do not influence the queries selecting them.

Every draw is also an actual `SpQuery.constr`.  Its `primitiveCalls` is proved
equal to the number of absorbed blocks, so the work-indexed sponge game—not
the number of public draws—is the named ROM target.

This closes deterministic framing, causality, domain separation, and work
accounting.  It does not prove the remaining adaptive eager/deferred sponge
coupling, the deployed Poseidon2 ideal-permutation hop, padding for a byte
codec, uniform query-index decoding, or native codec refinement.
-/

import Selvage.BaseFoldPoseidon2Rom

namespace Minidregg.Selvage.BaseFoldBcsFiatShamir

open BabyBearExt4
open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldPoseidon2Rom

set_option autoImplicit false

noncomputable section

abbrev Rate := BaseFoldPoseidon2Rom.Rate
abbrev Cap := BaseFoldPoseidon2Rom.Cap

/-! ## Typed in-band transcript domains -/

/-- Put one small semantic tag in lane zero and clear every other rate lane. -/
def tagBlock (tag : Nat) : Rate :=
  fun lane => if lane = 0 then (tag : F) else 0

def profileBlock : Rate := tagBlock 1001
def statementFrameTag : Rate := tagBlock 1002
def roundFrameTag : Rate := tagBlock 1003
def challengeResultTag : Rate := tagBlock 1004
def terminalRootTag : Rate := tagBlock 1005
def queryIndexTag : Rate := tagBlock 1006
def querySeedTag : Rate := tagBlock 1007
def openingFrameTag : Rate := tagBlock 1008
def leftPathTag : Rate := tagBlock 1009
def rightPathTag : Rate := tagBlock 1010
def nextPathTag : Rate := tagBlock 1011
def challengeDomain : Rate := tagBlock 1101
def queryDomain : Rate := tagBlock 1102

/-- Distinct identity for this transcript construction; it is not the IR-v2
suite id and does not promote the local Merkle profile to a deployed suite. -/
def transcriptProfileId : String := profileId ++ ".bcs-fs.v1"

theorem challenge_query_domains_distinct : challengeDomain ≠ queryDomain := by
  decide

theorem transcript_tags_nodup :
    [profileBlock, statementFrameTag, roundFrameTag, challengeResultTag,
      terminalRootTag, queryIndexTag, querySeedTag, openingFrameTag,
      leftPathTag, rightPathTag, nextPathTag, challengeDomain,
      queryDomain].Nodup := by
  decide

/-! ## Exact semantic alphabet -/

/-- Public data absorbed before any prover-selected round message. -/
structure Statement (m : Nat) where
  statementId : Digest
  evaluationPoint : Fin m → E
  claimedValue : E

/-- One BaseFold prover message before the corresponding challenge. -/
structure RoundMessage where
  levelRoot : Digest
  sumcheckCoefficients : Fin 3 → E

/-- All exact data opened for one sampled FRI fibre.  Query coordinates and
left/right direction bits are derived elsewhere and are not trusted fields. -/
structure Opening where
  left : E
  right : E
  next : E
  leftPath : List Digest
  rightPath : List Digest
  nextPath : List Digest

/-- A complete noninteractive transcript.  Stored challenges and query seeds
are neutral candidate data until checked against the derived values below. -/
structure Receipt (m queryCount : Nat) where
  round : Fin m → RoundMessage
  challenge : Fin m → E
  terminalRoot : Digest
  querySeed : Fin queryCount → Digest
  opening : Fin m → Fin queryCount → Opening

def indexBlock (index : Nat) : Rate := tagBlock index

/-- Ext4 uses exactly the proved power-basis coefficient block. -/
noncomputable def extBlock (value : E) : Rate := leafBlock value

/-- Interpret the first four output lanes in that same power basis. -/
noncomputable def rateChallenge (block : Rate) : E :=
  coefficients.symm fun i =>
    block (Fin.castAdd 4 (Fin.cast extensionPolynomial_natDegree i))

@[simp] theorem rateChallenge_extBlock (value : E) :
    rateChallenge (extBlock value) = value := by
  apply coefficients.injective
  funext i
  simp [rateChallenge, extBlock, leafBlock, coefficients4]

/-- Every vector coordinate is explicitly indexed. -/
noncomputable def statementBlocks {m : Nat} (statement : Statement m) :
    List Rate :=
  [profileBlock, statementFrameTag, statement.statementId,
      extBlock statement.claimedValue] ++
    (List.ofFn fun i : Fin m =>
      [indexBlock i, extBlock (statement.evaluationPoint i)]).flatten

/-- Root plus the exact three submitted sumcheck coefficients. -/
noncomputable def roundFrame (index : Nat) (message : RoundMessage) : List Rate :=
  [roundFrameTag, indexBlock index, message.levelRoot] ++
    List.ofFn fun coefficient : Fin 3 =>
      extBlock (message.sumcheckCoefficients coefficient)

/-- The challenge result is reabsorbed before every later round. -/
noncomputable def challengeFrame (index : Nat) (challenge : E) : List Rate :=
  [challengeResultTag, indexBlock index, extBlock challenge]

noncomputable def roundStepFrame (index : Nat) (message : RoundMessage)
    (challenge : E) : List Rate :=
  roundFrame index message ++ challengeFrame index challenge

noncomputable def completedRoundFrames {m queryCount : Nat}
    (receipt : Receipt m queryCount) : List (List Rate) :=
  List.ofFn fun i : Fin m =>
    roundStepFrame i (receipt.round i) (receipt.challenge i)

/-- Exact causal body for challenge `j`; `take j` excludes all future data. -/
noncomputable def challengeBody {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : List Rate :=
  statementBlocks statement ++
    ((completedRoundFrames receipt).take j).flatten ++
    roundFrame j (receipt.round j)

noncomputable def challengeMessage {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : List Rate :=
  challengeDomain :: challengeBody statement receipt j

/-- Post-round query body: all completed rounds and the terminal root, but no
opening data. -/
noncomputable def queryBody {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : List Rate :=
  statementBlocks statement ++
    (completedRoundFrames receipt).flatten ++
    [terminalRootTag, receipt.terminalRoot, queryIndexTag, indexBlock a]

noncomputable def queryMessage {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : List Rate :=
  queryDomain :: queryBody statement receipt a

/-! ## Construction-side Fiat--Shamir draws -/

noncomputable def challengeConstructionQuery {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : SpQuery Rate Cap :=
  .constr challengeDomain (challengeBody statement receipt j)

noncomputable def queryConstructionQuery {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : SpQuery Rate Cap :=
  .constr queryDomain (queryBody statement receipt a)

noncomputable def derivedChallengeRate {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : Rate :=
  sponge permutePair (0, 0) (challengeMessage statement receipt j)

noncomputable def derivedChallenge {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : E :=
  rateChallenge (derivedChallengeRate statement receipt j)

noncomputable def derivedQuerySeed {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : Digest :=
  sponge permutePair (0, 0) (queryMessage statement receipt a)

/-- Stored draws are accepted only when exactly construction-derived. -/
def DrawsExact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : Prop :=
  (∀ j, receipt.challenge j = derivedChallenge statement receipt j) ∧
    ∀ a, receipt.querySeed a = derivedQuerySeed statement receipt a

@[simp] theorem challenge_realAnswer_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) (j : Fin m) :
    realAnswer permutePair id (0, 0)
        (challengeConstructionQuery statement receipt j) =
      .rate (derivedChallengeRate statement receipt j) := by
  rfl

@[simp] theorem query_realAnswer_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) :
    realAnswer permutePair id (0, 0)
        (queryConstructionQuery statement receipt a) =
      .rate (derivedQuerySeed statement receipt a) := by
  rfl

/-- Same prior framed rounds and same current message imply the same draw,
regardless of all future receipt fields. -/
theorem challengeMessage_eq_of_samePrefix {m queryCount : Nat}
    (statement : Statement m) (left right : Receipt m queryCount) (j : Fin m)
    (prior : (completedRoundFrames left).take j =
      (completedRoundFrames right).take j)
    (current : roundFrame j (left.round j) =
      roundFrame j (right.round j)) :
    challengeMessage statement left j = challengeMessage statement right j := by
  simp [challengeMessage, challengeBody, prior, current]

theorem derivedChallenge_eq_of_samePrefix {m queryCount : Nat}
    (statement : Statement m) (left right : Receipt m queryCount) (j : Fin m)
    (prior : (completedRoundFrames left).take j =
      (completedRoundFrames right).take j)
    (current : roundFrame j (left.round j) =
      roundFrame j (right.round j)) :
    derivedChallenge statement left j = derivedChallenge statement right j := by
  rw [derivedChallenge, derivedChallenge, derivedChallengeRate,
    derivedChallengeRate,
    challengeMessage_eq_of_samePrefix statement left right j prior current]

theorem challenge_query_construction_domains_distinct {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) (a : Fin queryCount) :
    challengeConstructionQuery statement receipt j ≠
      queryConstructionQuery statement receipt a := by
  intro equal
  injection equal with domains _
  exact challenge_query_domains_distinct domains

/-! ## Exact primitive-work accounting -/

@[simp] theorem challengeQuery_primitiveCalls {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) (j : Fin m) :
    (challengeConstructionQuery statement receipt j).primitiveCalls =
      (challengeMessage statement receipt j).length := by
  rfl

@[simp] theorem queryQuery_primitiveCalls {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) :
    (queryConstructionQuery statement receipt a).primitiveCalls =
      (queryMessage statement receipt a).length := by
  rfl

noncomputable def constructionQueries {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    List (SpQuery Rate Cap) :=
  (List.ofFn fun j : Fin m =>
      challengeConstructionQuery statement receipt j) ++
    List.ofFn fun a : Fin queryCount =>
      queryConstructionQuery statement receipt a

/-- Total primitive work is a block sum, not `m + queryCount`. -/
noncomputable def transcriptPrimitiveWork {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : Nat :=
  (constructionQueries statement receipt).map SpQuery.primitiveCalls |>.sum

theorem transcriptPrimitiveWork_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    transcriptPrimitiveWork statement receipt =
      (List.ofFn fun j : Fin m =>
        (challengeMessage statement receipt j).length).sum +
      (List.ofFn fun a : Fin queryCount =>
        (queryMessage statement receipt a).length).sum := by
  unfold transcriptPrimitiveWork constructionQueries
  rw [List.map_append, List.sum_append, List.map_ofFn, List.map_ofFn]
  apply congrArg₂ (· + ·)
  · apply congrArg List.sum
    apply List.ofFn_inj.mpr
    funext j
    exact challengeQuery_primitiveCalls statement receipt j
  · apply congrArg List.sum
    apply List.ofFn_inj.mpr
    funext a
    exact queryQuery_primitiveCalls statement receipt a

/-! ## Openings retained after query derivation -/

def pathFrame (tag : Rate) (path : List Digest) : List Rate :=
  [tag, indexBlock path.length] ++ path

noncomputable def openingFrame (roundIndex queryIndex : Nat)
    (opening : Opening) : List Rate :=
  [openingFrameTag, indexBlock roundIndex, indexBlock queryIndex,
      extBlock opening.left, extBlock opening.right, extBlock opening.next] ++
    pathFrame leftPathTag opening.leftPath ++
    pathFrame rightPathTag opening.rightPath ++
    pathFrame nextPathTag opening.nextPath

noncomputable def querySeedFrame (index : Nat) (seed : Digest) : List Rate :=
  [querySeedTag, indexBlock index, seed]

/-- Complete canonical proof alphabet, including every sampled seed, value,
and authentication path consumed by the verifier. -/
noncomputable def proofBlocks {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : List Rate :=
  statementBlocks statement ++
    (completedRoundFrames receipt).flatten ++
    [terminalRootTag, receipt.terminalRoot] ++
    (List.ofFn fun a : Fin queryCount =>
      querySeedFrame a (receipt.querySeed a)).flatten ++
    (List.ofFn fun j : Fin m =>
      (List.ofFn fun a : Fin queryCount =>
        openingFrame j a (receipt.opening j a)).flatten).flatten

/-! ## The named ROM boundary -/

def romTarget : Prop := SpongeIndiffWorkGame Rate Cap (0, 0)

theorem romTarget_eq_construction_target :
    romTarget = BaseFoldPoseidon2Rom.romConstructionTarget := rfl

#check @DrawsExact
#check @challengeMessage_eq_of_samePrefix
#check @transcriptPrimitiveWork_exact
#check @romTarget

end


end Minidregg.Selvage.BaseFoldBcsFiatShamir
