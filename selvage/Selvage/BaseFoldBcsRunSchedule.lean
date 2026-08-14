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
import Selvage.SpongeIndiffDeferredWork

namespace Minidregg.Selvage.BaseFoldBcsRunSchedule

open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsPadding

set_option autoImplicit false

noncomputable section

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

#check @paddedConstructionDistinguisher_move_answer_independent
#check @paddedWorkPrefix_succ
#check @paddedWorkPrefix_final
#check @paddedDeferredWork_need_exact

/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.paddedConstructionDistinguisher_move_answer_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedConstructionDistinguisher_move_answer_independent
/-- info: 'Minidregg.Selvage.BaseFoldBcsRunSchedule.paddedWorkPrefix_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedWorkPrefix_final

end

end Minidregg.Selvage.BaseFoldBcsRunSchedule
