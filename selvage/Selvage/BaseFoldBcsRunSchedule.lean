/-
# Selvage.BaseFoldBcsRunSchedule — the concrete padded BaseFold work schedule

The generic sponge game permits every public query and its primitive cost to
depend on earlier oracle answers.  A fixed candidate BaseFold receipt is a
strictly smaller fragment: its padded challenge/query list is already fixed,
and earlier answers affect only the eventual verdict.  This module records
that fact at the exact interfaces used by both the eager work-stream runner
and the deferred ideal runner.

The cumulative schedule below is the static spine on which a run-specific
eager/deferred coordinate reindexing can be built.  It does not claim the
remaining off-bad semantic agreement or the random-permutation switch.
-/

import Selvage.BaseFoldBcsPadding
import Selvage.SpongeIndiffAdaptiveCoupling

namespace Minidregg.Selvage.BaseFoldBcsRunSchedule

open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsPadding

set_option autoImplicit false

noncomputable section

/-! ## The remaining structural routing premise -/

/-- The exact padded message belonging to each public construction draw. -/
def paddedPublicMessageSchedule {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    Fin (m + queryCount) → List Rate :=
  Fin.append
    (paddedChallengeMessage statement receipt)
    (paddedQueryMessage statement receipt)

/-- No public full message may already occur as a prefix of a different
public message.  Under this structural property, the simple segment-last to
segment-head reindexing below is the correct public full-message routing.
Cross-domain, distinct-query, and causal challenge/challenge cases are
discharged in `BaseFoldBcsPadding`. -/
def PaddedFullMessageRoutingSafe {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : Prop :=
  ∀ left right : Fin (m + queryCount), left ≠ right →
    ¬ (paddedPublicMessageSchedule statement receipt left <+:
      paddedPublicMessageSchedule statement receipt right)

/-- The canonical-range bound closes every routing case: challenge messages
diverge at padding versus challenge-result tags, query messages use distinct
bounded labels, and the two domains differ in their first block. -/
theorem paddedFullMessageRoutingSafe {m queryCount : Nat}
    (hcount : queryCount ≤ BabyBearExt4.modulus)
    (statement : Statement m) (receipt : Receipt m queryCount) :
    PaddedFullMessageRoutingSafe statement receipt := by
  intro left
  refine Fin.addCases (motive := fun left =>
    ∀ right, left ≠ right →
      ¬ (paddedPublicMessageSchedule statement receipt left <+:
        paddedPublicMessageSchedule statement receipt right)) ?_ ?_ left
  · intro challenge right
    refine Fin.addCases (motive := fun right =>
      Fin.castAdd queryCount challenge ≠ right →
        ¬ (paddedPublicMessageSchedule statement receipt
            (Fin.castAdd queryCount challenge) <+:
          paddedPublicMessageSchedule statement receipt right)) ?_ ?_ right
    · intro challenge' hne
      have hchallenge : challenge ≠ challenge' := by
        intro equal
        subst challenge'
        exact hne rfl
      simpa [paddedPublicMessageSchedule, Fin.append_left] using
        padded_challenge_not_prefix_of_ne statement receipt challenge
          challenge' hchallenge
    · intro query _
      simpa [paddedPublicMessageSchedule, Fin.append_left, Fin.append_right]
        using padded_challenge_query_not_prefix statement receipt challenge query
  · intro query right
    refine Fin.addCases (motive := fun right =>
      Fin.natAdd m query ≠ right →
        ¬ (paddedPublicMessageSchedule statement receipt (Fin.natAdd m query) <+:
          paddedPublicMessageSchedule statement receipt right)) ?_ ?_ right
    · intro challenge _
      simpa [paddedPublicMessageSchedule, Fin.append_left, Fin.append_right]
        using padded_query_challenge_not_prefix statement receipt challenge query
    · intro query' hne
      have hquery : query ≠ query' := by
        intro equal
        subst query'
        exact hne rfl
      simpa [paddedPublicMessageSchedule, Fin.append_right] using
        padded_query_not_prefix_of_ne hcount statement receipt query query'
          hquery

/-! ## The public move is answer-independent -/

/-- At any valid public prefix length, the fixed-receipt adapter selects the
corresponding entry of its canonical padded schedule.  The answer values are
irrelevant. -/
theorem paddedConstructionDistinguisher_move_at_length
    {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (answers : List (SpAnswer Rate Cap))
    (h : answers.length < m + queryCount) :
    (paddedConstructionDistinguisher statement receipt verdict).move answers =
      paddedConstructionQuerySchedule statement receipt
        ⟨answers.length, h⟩ := by
  simp [paddedConstructionDistinguisher, h]

/-- Two hypothetical transcripts of the same valid length select literally
the same padded BaseFold construction query. -/
theorem paddedConstructionDistinguisher_move_answer_independent
    {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (left right : List (SpAnswer Rate Cap))
    (hlength : left.length = right.length)
    (hleft : left.length < m + queryCount) :
    (paddedConstructionDistinguisher statement receipt verdict).move left =
      (paddedConstructionDistinguisher statement receipt verdict).move right := by
  have hright : right.length < m + queryCount := by omega
  rw [paddedConstructionDistinguisher_move_at_length statement receipt verdict
      left hleft,
    paddedConstructionDistinguisher_move_at_length statement receipt verdict
      right hright]
  apply congrArg (paddedConstructionQuerySchedule statement receipt)
  exact Fin.ext hlength

/-! ## A static primitive-work partition -/

/-- Primitive calls charged to one public schedule entry. -/
def paddedRoundPrimitiveWork {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin (m + queryCount)) : Nat :=
  (paddedConstructionQuerySchedule statement receipt j).primitiveCalls

theorem paddedRoundPrimitiveWork_pos {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (j : Fin (m + queryCount)) :
    0 < paddedRoundPrimitiveWork statement receipt j :=
  SpQuery.primitiveCalls_pos _

/-- The concrete list of per-round primitive costs. -/
def paddedPrimitiveWorkSchedule {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) : List Nat :=
  (List.ofFn (paddedConstructionQuerySchedule statement receipt)).map
    SpQuery.primitiveCalls

@[simp] theorem paddedPrimitiveWorkSchedule_length {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    (paddedPrimitiveWorkSchedule statement receipt).length =
      m + queryCount := by
  simp [paddedPrimitiveWorkSchedule]

/-- Work consumed strictly before numeric public round `round`. -/
def paddedWorkPrefix {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Nat) : Nat :=
  ((paddedPrimitiveWorkSchedule statement receipt).take round).sum

@[simp] theorem paddedWorkPrefix_zero {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    paddedWorkPrefix statement receipt 0 = 0 := by
  simp [paddedWorkPrefix]

/-- Advancing one public round appends exactly that round's fixed primitive
segment. -/
theorem paddedWorkPrefix_succ {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Nat) (hround : round < m + queryCount) :
    paddedWorkPrefix statement receipt (round + 1) =
      paddedWorkPrefix statement receipt round +
        paddedRoundPrimitiveWork statement receipt ⟨round, hround⟩ := by
  have hindex : round <
      (paddedPrimitiveWorkSchedule statement receipt).length := by
    simpa using hround
  have htake :
      (paddedPrimitiveWorkSchedule statement receipt).take (round + 1) =
        (paddedPrimitiveWorkSchedule statement receipt).take round ++
          [(paddedPrimitiveWorkSchedule statement receipt).get
            ⟨round, hindex⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hindex]
    rfl
  rw [paddedWorkPrefix, paddedWorkPrefix, htake, List.sum_append]
  simp [paddedPrimitiveWorkSchedule, paddedRoundPrimitiveWork]

/-- Every nonterminal cumulative boundary is strictly larger than the prior
one, so the public-round segments cannot be empty. -/
theorem paddedWorkPrefix_strictMono_step {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Nat) (hround : round < m + queryCount) :
    paddedWorkPrefix statement receipt round <
      paddedWorkPrefix statement receipt (round + 1) := by
  rw [paddedWorkPrefix_succ statement receipt round hround]
  exact Nat.lt_add_of_pos_right
    (paddedRoundPrimitiveWork_pos statement receipt ⟨round, hround⟩)

/-- The terminal cumulative boundary is exactly the padded receipt work
ledger already used by the ROM theorem. -/
theorem paddedWorkPrefix_final {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    paddedWorkPrefix statement receipt (m + queryCount) =
      paddedTranscriptPrimitiveWork statement receipt := by
  unfold paddedWorkPrefix
  rw [show m + queryCount =
      (paddedPrimitiveWorkSchedule statement receipt).length by simp]
  have htake :
      (paddedPrimitiveWorkSchedule statement receipt).take
          (paddedPrimitiveWorkSchedule statement receipt).length =
        paddedPrimitiveWorkSchedule statement receipt :=
    (List.take_eq_self_iff _).2 (Nat.le_refl _)
  rw [htake]
  unfold paddedPrimitiveWorkSchedule paddedTranscriptPrimitiveWork
  rw [paddedConstructionQueries_eq_ofFn]

/-- Every cumulative boundary lies within the terminal receipt ledger, even
when `round` is larger than the public query count (where `List.take` has
already saturated). -/
theorem paddedWorkPrefix_le_final {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Nat) :
    paddedWorkPrefix statement receipt round ≤
      paddedTranscriptPrimitiveWork statement receipt := by
  let schedule := paddedPrimitiveWorkSchedule statement receipt
  have hsplit : schedule.take round ++ schedule.drop round = schedule :=
    List.take_append_drop round schedule
  have hle : (schedule.take round).sum ≤ schedule.sum := by
    calc
      (schedule.take round).sum ≤
          (schedule.take round).sum + (schedule.drop round).sum := by omega
      _ = (schedule.take round ++ schedule.drop round).sum := by
        rw [List.sum_append]
      _ = schedule.sum := congrArg List.sum hsplit
  change (schedule.take round).sum ≤ _
  calc
    (schedule.take round).sum ≤ schedule.sum := hle
    _ = paddedTranscriptPrimitiveWork statement receipt := by
      dsimp [schedule]
      unfold paddedPrimitiveWorkSchedule paddedTranscriptPrimitiveWork
      rw [paddedConstructionQueries_eq_ofFn]

/-! ## The eager runner reads the same static cost -/

/-- Whenever the eager prefix-programmed runner is at a valid public-prefix
length, it requests exactly the corresponding fixed BaseFold segment. -/
theorem paddedWorkHybrid_need_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (state : WorkHybridState Rate Cap)
    (h : state.core.ans.length < m + queryCount) :
    ((paddedConstructionDistinguisher statement receipt verdict).move
        state.core.ans).primitiveCalls =
      paddedRoundPrimitiveWork statement receipt
        ⟨state.core.ans.length, h⟩ := by
  rw [paddedConstructionDistinguisher_move_at_length statement receipt verdict
    state.core.ans h]
  rfl

/-- Recursive presentation of eager prefix-programmed execution, exposing its
numeric public prefix for the coupling induction. -/
noncomputable def paddedWorkHybridStateNat {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    (round : Nat) → round ≤ m + queryCount →
      Except WorkHybridError (WorkHybridState Rate Cap)
  | 0, _ => .ok (WorkHybridState.initial coins)
  | round + 1, hround =>
      (paddedWorkHybridStateNat statement receipt verdict coins round
        (Nat.le_trans (Nat.le_succ round) hround)).bind fun state =>
        workHybridStep
          (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) state ⟨round, Nat.lt_of_succ_le hround⟩

/-- The recursive eager presentation is the ordinary finite fold over the
same work-stream steps. -/
theorem paddedWorkHybridStateNat_eq_foldl {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hround : round ≤ m + queryCount) :
    paddedWorkHybridStateNat statement receipt verdict coins round hround =
      Fin.foldl round
        (fun result j => result.bind fun state =>
          workHybridStep
            (paddedConstructionDistinguisher statement receipt verdict)
            (0, 0) state
            ⟨j, Nat.lt_of_lt_of_le j.isLt hround⟩)
        (.ok (WorkHybridState.initial coins)) := by
  induction round with
  | zero => simp [paddedWorkHybridStateNat]
  | succ round ih =>
      rw [Fin.foldl_succ_last]
      unfold paddedWorkHybridStateNat
      rw [ih (Nat.le_trans (Nat.le_succ round) hround)]
      congr

/-- At full query count the recursive eager presentation is the landed
`workHybridRun` fold. -/
theorem paddedWorkHybridStateNat_full_eq_run {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    paddedWorkHybridStateNat statement receipt verdict coins
        (m + queryCount) (Nat.le_refl _) =
      workHybridRun
        (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0) coins := by
  rw [paddedWorkHybridStateNat_eq_foldl, Fin.foldl_eq_finRange_foldl]
  unfold workHybridRun
  congr 1

/-- On the exact receipt work vector, every eager prefix either has the same
static answer/work/suffix counters as the deferred prefix or has failed with a
named prefix-hybrid semantic error.  Exhaustion and malformed segmentation are
excluded. -/
theorem paddedWorkHybridStateNat_classify {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hround : round ≤ m + queryCount) :
    (∃ state,
      paddedWorkHybridStateNat statement receipt verdict coins round hround =
          .ok state ∧
        state.core.ans.length = round ∧
        state.core.work = paddedWorkPrefix statement receipt round ∧
        state.remaining = (List.ofFn coins).drop
          (paddedWorkPrefix statement receipt round)) ∨
      ∃ error,
        paddedWorkHybridStateNat statement receipt verdict coins round hround =
          .error (.hybrid error) := by
  induction round with
  | zero =>
      exact Or.inl ⟨WorkHybridState.initial coins, rfl, rfl,
        by simp [WorkHybridState.initial, PrefixHybridState.empty],
        by simp [WorkHybridState.initial]⟩
  | succ round ih =>
      have hprev : round ≤ m + queryCount :=
        Nat.le_trans (Nat.le_succ round) hround
      rcases ih hprev with hsuccess | hfailure
      · obtain ⟨state, hstate, hans, hwork, hremaining⟩ := hsuccess
        have hroundLt : round < m + queryCount := Nat.lt_of_succ_le hround
        have hneed :
            ((paddedConstructionDistinguisher statement receipt verdict).move
                state.core.ans).primitiveCalls =
              paddedRoundPrimitiveWork statement receipt
                ⟨round, hroundLt⟩ := by
          rw [paddedWorkHybrid_need_exact statement receipt verdict state
            (by omega)]
          congr
        have hprefixLe :=
          paddedWorkPrefix_le_final statement receipt (round + 1)
        have hprefixStep :=
          paddedWorkPrefix_succ statement receipt round hroundLt
        have henough :
            ((paddedConstructionDistinguisher statement receipt verdict).move
                state.core.ans).primitiveCalls ≤ state.remaining.length := by
          rw [hremaining, List.length_drop, List.length_ofFn, hneed]
          omega
        rcases workHybridStep_ok_or_hybrid_of_need_le
            (paddedConstructionDistinguisher statement receipt verdict)
            (0, 0) state ⟨round, hroundLt⟩ henough with hnext | herror
        · obtain ⟨next, hnext⟩ := hnext
          refine Or.inl ⟨next, ?_, ?_, ?_, ?_⟩
          · unfold paddedWorkHybridStateNat
            rw [hstate]
            exact hnext
          · rw [workHybridStep_ans_length _ _ state next _ hnext, hans]
          · rw [workHybridStep_work_exact _ _ state next _ hnext,
              hwork, hneed, hprefixStep]
          · rw [workHybridStep_remaining_exact _ _ state next _ hnext,
              hremaining, hneed, List.drop_drop, ← hprefixStep]
        · obtain ⟨error, herror⟩ := herror
          refine Or.inr ⟨error, ?_⟩
          unfold paddedWorkHybridStateNat
          rw [hstate]
          exact herror
      · obtain ⟨error, herror⟩ := hfailure
        refine Or.inr ⟨error, ?_⟩
        unfold paddedWorkHybridStateNat
        rw [herror]
        rfl

/-- A complete eager run on the exact BaseFold ledger therefore either
succeeds with the exact terminal counters or fails only at the explicit
semantic prefix-programming boundary. -/
theorem paddedWorkHybridRun_classify {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    (∃ state,
      workHybridRun
          (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) coins = .ok state ∧
        state.core.ans.length = m + queryCount ∧
        state.core.work = paddedTranscriptPrimitiveWork statement receipt ∧
        state.remaining = []) ∨
      ∃ error,
        workHybridRun
          (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) coins = .error (.hybrid error) := by
  rcases paddedWorkHybridStateNat_classify statement receipt verdict coins
      (Nat.le_refl (m + queryCount)) with hsuccess | hfailure
  · obtain ⟨state, hrun, hans, hwork, hremaining⟩ := hsuccess
    refine Or.inl ⟨state, ?_, hans, ?_, ?_⟩
    · rw [← paddedWorkHybridStateNat_full_eq_run]
      exact hrun
    · simpa [paddedWorkPrefix_final] using hwork
    · rw [hremaining, paddedWorkPrefix_final]
      simp
  · obtain ⟨error, hrun⟩ := hfailure
    refine Or.inr ⟨error, ?_⟩
    rw [← paddedWorkHybridStateNat_full_eq_run]
    exact hrun

/-! ## The deferred runner reads the same static cost -/

/-- Whenever the deferred runner is at a valid public-prefix length, the work
it requests is exactly the corresponding fixed BaseFold segment.  This is the
run-specific scheduling premise; no answer-dependent work allocation remains
to synthesize for a fixed receipt. -/
theorem paddedDeferredWork_need_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (state : DeferredWorkState Rate Cap)
    (h : state.core.ans.length < m + queryCount) :
    ((paddedConstructionDistinguisher statement receipt verdict).move
        state.core.ans).primitiveCalls =
      paddedRoundPrimitiveWork statement receipt
        ⟨state.core.ans.length, h⟩ := by
  rw [paddedConstructionDistinguisher_move_at_length statement receipt verdict
    state.core.ans h]
  rfl

/-! ## The full deferred run cannot exhaust the exact receipt ledger -/

/-- Recursive presentation of the deferred execution, exposing the numeric
public prefix for induction. -/
noncomputable def paddedDeferredStateNat {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    (round : Nat) → round ≤ m + queryCount →
      Except DeferredWorkError (DeferredWorkState Rate Cap)
  | 0, _ => .ok (DeferredWorkState.initial coins)
  | round + 1, hround =>
      (paddedDeferredStateNat statement receipt verdict coins round
        (Nat.le_trans (Nat.le_succ round) hround)).bind fun state =>
        deferredWorkStep
          (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) state ⟨round, Nat.lt_of_succ_le hround⟩

/-- The recursive presentation is the ordinary finite fold over the same
deferred steps. -/
theorem paddedDeferredStateNat_eq_foldl {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hround : round ≤ m + queryCount) :
    paddedDeferredStateNat statement receipt verdict coins round hround =
      Fin.foldl round
        (fun result j => result.bind fun state =>
          deferredWorkStep
            (paddedConstructionDistinguisher statement receipt verdict)
            (0, 0) state
            ⟨j, Nat.lt_of_lt_of_le j.isLt hround⟩)
        (.ok (DeferredWorkState.initial coins)) := by
  induction round with
  | zero => simp [paddedDeferredStateNat]
  | succ round ih =>
      rw [Fin.foldl_succ_last]
      unfold paddedDeferredStateNat
      rw [ih (Nat.le_trans (Nat.le_succ round) hround)]
      congr

/-- At full query count the recursive run is definitionally the landed
`deferredWorkRun` fold. -/
theorem paddedDeferredStateNat_full_eq_run {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    paddedDeferredStateNat statement receipt verdict coins
        (m + queryCount) (Nat.le_refl _) =
      deferredWorkRun
        (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0) coins := by
  rw [paddedDeferredStateNat_eq_foldl, Fin.foldl_eq_finRange_foldl]
  unfold deferredWorkRun
  congr 1

/-- Exact recursive-run invariant: after `round` public draws the transcript
has that length, consumed work is the static cumulative boundary, and the
unconsumed vector is the corresponding suffix of the original fixed sample. -/
theorem paddedDeferredStateNat_exact {m queryCount round : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap)
    (hround : round ≤ m + queryCount) :
    ∃ state,
      paddedDeferredStateNat statement receipt verdict coins round hround =
          .ok state ∧
        state.core.ans.length = round ∧
        state.work = paddedWorkPrefix statement receipt round ∧
        state.remaining = (List.ofFn coins).drop
          (paddedWorkPrefix statement receipt round) := by
  induction round with
  | zero =>
      refine ⟨DeferredWorkState.initial coins, rfl, ?_, ?_, ?_⟩
      · rfl
      · simp [DeferredWorkState.initial]
      · simp [DeferredWorkState.initial]
  | succ round ih =>
      have hprev : round ≤ m + queryCount :=
        Nat.le_trans (Nat.le_succ round) hround
      obtain ⟨state, hstate, hans, hwork, hremaining⟩ := ih hprev
      have hroundLt : round < m + queryCount := Nat.lt_of_succ_le hround
      have hneed :
          ((paddedConstructionDistinguisher statement receipt verdict).move
              state.core.ans).primitiveCalls =
            paddedRoundPrimitiveWork statement receipt
              ⟨round, hroundLt⟩ := by
        rw [paddedDeferredWork_need_exact statement receipt verdict state
          (by omega)]
        congr
      have hprefixLe :=
        paddedWorkPrefix_le_final statement receipt (round + 1)
      have hprefixStep :=
        paddedWorkPrefix_succ statement receipt round hroundLt
      have henough :
          ((paddedConstructionDistinguisher statement receipt verdict).move
              state.core.ans).primitiveCalls ≤ state.remaining.length := by
        rw [hremaining, List.length_drop, List.length_ofFn, hneed]
        omega
      obtain ⟨next, hnext⟩ := deferredWorkStep_exists_of_need_le
        (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0) state ⟨round, hroundLt⟩ henough
      refine ⟨next, ?_, ?_, ?_, ?_⟩
      · unfold paddedDeferredStateNat
        rw [hstate]
        exact hnext
      · rw [deferredWorkStep_ans_length _ _ state next _ hnext, hans]
      · rw [deferredWorkStep_work_exact _ _ state next _ hnext,
          hwork, hneed, hprefixStep]
      · rw [deferredWorkStep_remaining_exact _ _ state next _ hnext,
          hremaining, hneed, List.drop_drop, ← hprefixStep]

/-- A fixed padded BaseFold receipt's deferred execution succeeds on exactly
its proved primitive-work vector, consumes every coordinate, and returns one
answer per public draw.  The remaining eager/off-bad comparison is separate. -/
theorem paddedDeferredWorkRun_exact {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    ∃ state,
      deferredWorkRun
          (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) coins = .ok state ∧
        state.core.ans.length = m + queryCount ∧
        state.work = paddedTranscriptPrimitiveWork statement receipt ∧
        state.remaining = [] := by
  obtain ⟨state, hrun, hans, hwork, hremaining⟩ :=
    paddedDeferredStateNat_exact statement receipt verdict coins
      (Nat.le_refl (m + queryCount))
  refine ⟨state, ?_, hans, ?_, ?_⟩
  · rw [← paddedDeferredStateNat_full_eq_run]
    exact hrun
  · simpa [paddedWorkPrefix_final] using hwork
  · rw [hremaining, paddedWorkPrefix_final]
    simp

/-! ## A concrete segment-wise eager/deferred reindexing program -/

/-- First coordinate of one public round's primitive-work segment. -/
def paddedSegmentHead {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Fin (m + queryCount)) :
    Fin (paddedTranscriptPrimitiveWork statement receipt) :=
  ⟨paddedWorkPrefix statement receipt round, by
    have hnext := paddedWorkPrefix_le_final statement receipt (round + 1)
    have hstep := paddedWorkPrefix_strictMono_step statement receipt round
      round.isLt
    omega⟩

/-- Last coordinate of the same nonempty work segment.  In the eager prefix
hybrid, this is the fresh rate coin assigned to the full padded message. -/
def paddedSegmentLast {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Fin (m + queryCount)) :
    Fin (paddedTranscriptPrimitiveWork statement receipt) :=
  ⟨paddedWorkPrefix statement receipt (round + 1) - 1, by
    have hnext := paddedWorkPrefix_le_final statement receipt (round + 1)
    have hstep := paddedWorkPrefix_strictMono_step statement receipt round
      round.isLt
    omega⟩

theorem paddedSegmentLast_succ {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Fin (m + queryCount)) :
    (paddedSegmentLast statement receipt round : Nat) + 1 =
      paddedWorkPrefix statement receipt (round + 1) := by
  unfold paddedSegmentLast
  change
    (paddedWorkPrefix statement receipt (round + 1) - 1) + 1 =
      paddedWorkPrefix statement receipt (round + 1)
  have hstep := paddedWorkPrefix_strictMono_step statement receipt round
    round.isLt
  omega

/-- One unconditional whole-vector involution swaps the deferred segment head
with the eager full-message coordinate. -/
noncomputable def paddedSegmentSwapMove {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Fin (m + queryCount)) :
    GuardedInvolution
      (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap) :=
  guardedWorkReindex
    (Equiv.swap (paddedSegmentHead statement receipt round)
      (paddedSegmentLast statement receipt round))
    (by intro index; simp)
    (fun _ => True)
    (fun _ => inferInstance)
    (by intro; simp)

/-- The move places the eager full-message coin at the coordinate consumed by
the deferred round.  Singleton segments reduce to the identity. -/
theorem paddedSegmentSwapMove_head {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (round : Fin (m + queryCount))
    (coins : Fin (paddedTranscriptPrimitiveWork statement receipt) →
      Rate × Cap) :
    (paddedSegmentSwapMove statement receipt round).apply coins
        (paddedSegmentHead statement receipt round) =
      coins (paddedSegmentLast statement receipt round) := by
  simp [paddedSegmentSwapMove, GuardedInvolution.apply,
    guardedWorkReindex, permuteWorkCoins]

/-- The concrete fixed-receipt program contains one exact coordinate swap per
public construction draw. -/
noncomputable def paddedSegmentSwapProgram {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    List (GuardedInvolution
      (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap)) :=
  List.ofFn fun round : Fin (m + queryCount) =>
    paddedSegmentSwapMove statement receipt round

/-- Composition of the segment swaps is an actual equivalence of the whole
fixed work-vector space, not a marginal-distribution argument. -/
noncomputable def paddedSegmentReindex {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap) ≃
      (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap) :=
  guardedProgramReindex (paddedSegmentSwapProgram statement receipt)

/-- The run-specific segment program preserves exact uniform counting
measure on the entire primitive-work vector. -/
theorem uniformProb_paddedSegmentReindex {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (event :
      (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap) →
        Prop) :
    uniformProb
        (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap)
        (fun coins => event (paddedSegmentReindex statement receipt coins)) =
      uniformProb
        (Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap)
        event :=
  uniformProb_guardedProgram
    (paddedSegmentSwapProgram statement receipt) event

#check @paddedConstructionDistinguisher_move_answer_independent
#check @paddedFullMessageRoutingSafe
#check @paddedWorkPrefix_succ
#check @paddedWorkPrefix_final
#check @paddedDeferredWork_need_exact
#check @paddedDeferredWorkRun_exact
#check @paddedSegmentSwapMove_head
#check @uniformProb_paddedSegmentReindex

/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.paddedConstructionDistinguisher_move_answer_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedConstructionDistinguisher_move_answer_independent
/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.paddedFullMessageRoutingSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedFullMessageRoutingSafe
/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.paddedWorkPrefix_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedWorkPrefix_final
/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.paddedDeferredWorkRun_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedDeferredWorkRun_exact
/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.uniformProb_paddedSegmentReindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformProb_paddedSegmentReindex

end

end Minidregg.Selvage.BaseFoldBcsRunSchedule
