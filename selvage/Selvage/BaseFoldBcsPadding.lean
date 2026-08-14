/-
# Selvage.BaseFoldBcsPadding — an injectively padded BaseFold transcript profile

`BaseFoldBcsFiatShamir` deliberately fixed an exact, nonempty rate-block
alphabet before choosing a deployed byte codec.  This module defines the next
profile without mutating that proved v1 object: every complete challenge or
query message receives one terminal rate-block marker.  Appending a fixed
block is injective on arbitrary block lists, so variable-length messages
cannot become equal through this padding layer.

The padded construction queries are literal `SpQuery.constr` values.  Their
primitive-work ledger is exact: the profile costs one additional permutation
call per public draw, hence `m + queryCount` calls per receipt.  This closes
rate-block padding only.  Canonical bytes-to-field packing, a decoder, and the
deployed Poseidon2 permutation boundary remain separate obligations.
-/

import Selvage.BaseFoldBcsSpongeGame

namespace Minidregg.Selvage.BaseFoldBcsPadding

open BabyBearExt4
open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldBcsFiatShamir

set_option autoImplicit false

noncomputable section

/-! ## A separate, injectively padded profile -/

/-- This identity is deliberately different from the already proved
unpadded rate-block profile. -/
def paddedTranscriptProfileId : String := transcriptProfileId ++ ".pad1"

/-- A terminal block reserved by the padded profile. -/
def paddingBlock : Rate := tagBlock 1201

theorem paddedTranscript_tags_nodup :
    [profileBlock, statementFrameTag, roundFrameTag, challengeResultTag,
      terminalRootTag, queryIndexTag, querySeedTag, openingFrameTag,
      leftPathTag, rightPathTag, nextPathTag, challengeDomain, queryDomain,
      paddingBlock].Nodup := by
  decide

/-- Append one full rate-block marker.  This is block-level padding; it does
not pretend to be a byte packing rule. -/
def padMessage (message : List Rate) : List Rate :=
  message ++ [paddingBlock]

@[simp] theorem padMessage_length (message : List Rate) :
    (padMessage message).length = message.length + 1 := by
  simp [padMessage]

theorem padMessage_ne_nil (message : List Rate) :
    padMessage message ≠ [] := by
  simp [padMessage]

/-- Right-terminal padding is injective even when the marker happens to occur
inside the unpadded message. -/
theorem padMessage_injective : Function.Injective padMessage := by
  intro left right equal
  have reversed :
      paddingBlock :: left.reverse = paddingBlock :: right.reverse := by
    simpa [padMessage] using congrArg List.reverse equal
  have tails : left.reverse = right.reverse := (List.cons.inj reversed).2
  simpa using congrArg List.reverse tails

/-! ## Exact padded construction draws -/

noncomputable def paddedChallengeMessage {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : List Rate :=
  padMessage (challengeMessage statement receipt j)

noncomputable def paddedQueryMessage {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : List Rate :=
  padMessage (queryMessage statement receipt a)

noncomputable def paddedChallengeConstructionQuery {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : SpQuery Rate Cap :=
  .constr challengeDomain
    (challengeBody statement receipt j ++ [paddingBlock])

noncomputable def paddedQueryConstructionQuery {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : SpQuery Rate Cap :=
  .constr queryDomain (queryBody statement receipt a ++ [paddingBlock])

@[simp] theorem paddedChallengeQuery_primitiveCalls {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) (j : Fin m) :
    (paddedChallengeConstructionQuery statement receipt j).primitiveCalls =
      (paddedChallengeMessage statement receipt j).length := by
  rfl

@[simp] theorem paddedQueryQuery_primitiveCalls {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) :
    (paddedQueryConstructionQuery statement receipt a).primitiveCalls =
      (paddedQueryMessage statement receipt a).length := by
  rfl

theorem padded_challenge_query_construction_domains_distinct
    {m queryCount : Nat} (statement : Statement m)
    (receipt : Receipt m queryCount) (j : Fin m) (a : Fin queryCount) :
    paddedChallengeConstructionQuery statement receipt j ≠
      paddedQueryConstructionQuery statement receipt a := by
  intro equal
  injection equal with domains _
  exact challenge_query_domains_distinct domains

/-- Padding preserves the statement-first prefix law because it is applied
only after the complete causal message has been formed. -/
theorem paddedChallengeMessage_eq_of_samePrefix {m queryCount : Nat}
    (statement : Statement m) (left right : Receipt m queryCount) (j : Fin m)
    (prior : (completedRoundFrames left).take j =
      (completedRoundFrames right).take j)
    (current : roundFrame j (left.round j) =
      roundFrame j (right.round j)) :
    paddedChallengeMessage statement left j =
      paddedChallengeMessage statement right j := by
  exact congrArg padMessage
    (challengeMessage_eq_of_samePrefix statement left right j prior current)

noncomputable def paddedDerivedChallengeRate {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : Rate :=
  sponge BaseFoldPoseidon2Rom.permutePair (0, 0)
    (paddedChallengeMessage statement receipt j)

noncomputable def paddedDerivedChallenge {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin m) : E :=
  rateChallenge (paddedDerivedChallengeRate statement receipt j)

noncomputable def paddedDerivedQuerySeed {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) : Digest :=
  sponge BaseFoldPoseidon2Rom.permutePair (0, 0)
    (paddedQueryMessage statement receipt a)

/-- Candidate draws are checked against the padded profile, never silently
against the unpadded profile. -/
def PaddedDrawsExact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : Prop :=
  (∀ j, receipt.challenge j = paddedDerivedChallenge statement receipt j) ∧
    ∀ a, receipt.querySeed a = paddedDerivedQuerySeed statement receipt a

@[simp] theorem padded_challenge_realAnswer_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) (j : Fin m) :
    realAnswer BaseFoldPoseidon2Rom.permutePair id (0, 0)
        (paddedChallengeConstructionQuery statement receipt j) =
      .rate (paddedDerivedChallengeRate statement receipt j) := by
  rfl

@[simp] theorem padded_query_realAnswer_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (a : Fin queryCount) :
    realAnswer BaseFoldPoseidon2Rom.permutePair id (0, 0)
        (paddedQueryConstructionQuery statement receipt a) =
      .rate (paddedDerivedQuerySeed statement receipt a) := by
  rfl

/-! ## Exact primitive-work delta -/

noncomputable def paddedConstructionQueries {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    List (SpQuery Rate Cap) :=
  (List.ofFn fun j : Fin m =>
      paddedChallengeConstructionQuery statement receipt j) ++
    List.ofFn fun a : Fin queryCount =>
      paddedQueryConstructionQuery statement receipt a

noncomputable def paddedTranscriptPrimitiveWork {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : Nat :=
  (paddedConstructionQueries statement receipt).map SpQuery.primitiveCalls
    |>.sum

theorem paddedTranscriptPrimitiveWork_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    paddedTranscriptPrimitiveWork statement receipt =
      (List.ofFn fun j : Fin m =>
        (paddedChallengeMessage statement receipt j).length).sum +
      (List.ofFn fun a : Fin queryCount =>
        (paddedQueryMessage statement receipt a).length).sum := by
  unfold paddedTranscriptPrimitiveWork paddedConstructionQueries
  rw [List.map_append, List.sum_append, List.map_ofFn, List.map_ofFn]
  apply congrArg₂ (fun left right => left + right)
  · apply congrArg List.sum
    apply List.ofFn_inj.mpr
    funext j
    exact paddedChallengeQuery_primitiveCalls statement receipt j
  · apply congrArg List.sum
    apply List.ofFn_inj.mpr
    funext a
    exact paddedQueryQuery_primitiveCalls statement receipt a

private theorem sum_map_add_one (values : List Nat) :
    (values.map fun value => value + 1).sum = values.sum + values.length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

/-- The padding price is exact, not an asymptotic estimate: one additional
primitive call for each of the `m + queryCount` public draws. -/
theorem paddedTranscriptPrimitiveWork_eq_add_draws {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    paddedTranscriptPrimitiveWork statement receipt =
      transcriptPrimitiveWork statement receipt + (m + queryCount) := by
  rw [paddedTranscriptPrimitiveWork_exact,
    transcriptPrimitiveWork_exact]
  simp only [paddedChallengeMessage, paddedQueryMessage, padMessage_length]
  rw [show (List.ofFn fun j : Fin m =>
        (challengeMessage statement receipt j).length + 1) =
      (List.ofFn fun j : Fin m =>
        (challengeMessage statement receipt j).length).map
          (fun value => value + 1) by
        rw [List.map_ofFn]
        apply List.ofFn_inj.mpr
        funext j
        rfl,
    show (List.ofFn fun a : Fin queryCount =>
        (queryMessage statement receipt a).length + 1) =
      (List.ofFn fun a : Fin queryCount =>
        (queryMessage statement receipt a).length).map
          (fun value => value + 1) by
        rw [List.map_ofFn]
        apply List.ofFn_inj.mpr
        funext a
        rfl,
    sum_map_add_one, sum_map_add_one]
  simp only [List.length_ofFn]
  omega

/-! ## The padded schedule in the work-indexed sponge game -/

/-- The exact public schedule for the padded profile. -/
def paddedConstructionQuerySchedule {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    Fin (m + queryCount) → SpQuery Rate Cap :=
  Fin.append
    (fun j => paddedChallengeConstructionQuery statement receipt j)
    (fun a => paddedQueryConstructionQuery statement receipt a)

theorem paddedConstructionQueries_eq_ofFn {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    paddedConstructionQueries statement receipt =
      List.ofFn (paddedConstructionQuerySchedule statement receipt) := by
  simp [paddedConstructionQueries, paddedConstructionQuerySchedule]

/-- A fixed candidate receipt viewed through the padded construction profile.
As in the original adapter, the verdict is kept abstract because the raw-IOR
acceptance predicate lives at the next proof layer. -/
def paddedConstructionDistinguisher {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    Distinguisher Rate Cap (m + queryCount) where
  move answers :=
    if h : answers.length < m + queryCount then
      paddedConstructionQuerySchedule statement receipt ⟨answers.length, h⟩
    else
      .fwd (0, 0)
  out := verdict

theorem paddedConstructionDistinguisher_move {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (answers : Fin (m + queryCount) → SpAnswer Rate Cap)
    (j : Fin (m + queryCount)) :
    (paddedConstructionDistinguisher statement receipt verdict).move
        ((List.ofFn answers).take j) =
      paddedConstructionQuerySchedule statement receipt j := by
  simp [paddedConstructionDistinguisher, List.length_take]

/-- Every hypothetical answer trace is charged by the exact padded receipt
ledger, including its terminal marker on every public draw. -/
theorem paddedConstructionDistinguisher_primitiveWorkOn_exact
    {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (answers : Fin (m + queryCount) → SpAnswer Rate Cap) :
    (paddedConstructionDistinguisher statement receipt verdict).primitiveWorkOn
        answers = paddedTranscriptPrimitiveWork statement receipt := by
  unfold Distinguisher.primitiveWorkOn paddedTranscriptPrimitiveWork
  conv_rhs =>
    rw [paddedConstructionQueries_eq_ofFn, List.map_ofFn, List.ofFn_eq_map]
  rw [bind_pure_comp]
  change
    (List.map
      (fun j =>
        ((paddedConstructionDistinguisher statement receipt verdict).move
          ((List.ofFn answers).take j)).primitiveCalls)
      (List.map Fin.val (List.finRange (m + queryCount)))).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [paddedConstructionDistinguisher_move]

theorem paddedConstructionDistinguisher_workBound {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    PrimitiveWorkBound
      (paddedConstructionDistinguisher statement receipt verdict)
      (paddedTranscriptPrimitiveWork statement receipt) := by
  intro answers
  rw [paddedConstructionDistinguisher_primitiveWorkOn_exact]

/-- The existing named ROM premise specializes to the padded profile at the
larger exact work ledger.  This still does not idealize deployed Poseidon2. -/
theorem paddedConstructionDistinguisher_romBound
    {m queryCount : Nat}
    (hrom : BaseFoldPoseidon2Rom.romConstructionTarget)
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    |realProb
        (paddedConstructionDistinguisher statement receipt verdict) (0, 0) -
        idealProb
          (paddedConstructionDistinguisher statement receipt verdict) (0, 0)|
      ≤ BaseFoldPoseidon2Rom.romError
          (paddedTranscriptPrimitiveWork statement receipt) := by
  have bound := hrom (m + queryCount)
    (paddedTranscriptPrimitiveWork statement receipt)
    (paddedConstructionDistinguisher statement receipt verdict)
    (paddedConstructionDistinguisher_workBound statement receipt verdict)
  unfold BaseFoldPoseidon2Rom.romError
  simp only [
    BaseFoldPoseidon2Rom.capacity_card,
    BaseFoldPoseidon2Rom.state_card, Nat.cast_pow] at bound
  simpa only [Nat.cast_pow] using bound

#check @padMessage_injective
#check @PaddedDrawsExact
#check @paddedChallengeMessage_eq_of_samePrefix
#check @paddedTranscriptPrimitiveWork_eq_add_draws
#check @paddedConstructionDistinguisher_primitiveWorkOn_exact
#check @paddedConstructionDistinguisher_romBound

/-- info: 'Minidregg.Selvage.BaseFoldBcsPadding.padMessage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms padMessage_injective
/-- info: 'Minidregg.Selvage.BaseFoldBcsPadding.paddedTranscriptPrimitiveWork_eq_add_draws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedTranscriptPrimitiveWork_eq_add_draws
/-- info: 'Minidregg.Selvage.BaseFoldBcsPadding.paddedConstructionDistinguisher_romBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedConstructionDistinguisher_romBound

end

end Minidregg.Selvage.BaseFoldBcsPadding
