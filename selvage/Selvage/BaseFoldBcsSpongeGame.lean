/-
# Selvage.BaseFoldBcsSpongeGame — put the exact receipt schedule in the ROM game

`BaseFoldBcsFiatShamir` defines the precise construction queries and charges
their absorbed blocks.  This module supplies the missing type-level adapter:
the same ordered challenge/query schedule is a `Distinguisher` in the
work-indexed sponge game, for any Boolean verdict over its answers.

The adapter is intentionally receipt-indexed.  It proves that a fixed
candidate receipt enters the game with exactly `transcriptPrimitiveWork`
primitive calls, rather than the smaller public draw count `m + queryCount`.
It does not turn the receipt into an online prover or prove the remaining
adaptive eager/deferred coupling.
-/

import Selvage.BaseFoldBcsFiatShamir

namespace Minidregg.Selvage.BaseFoldBcsSpongeGame

open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldBcsFiatShamir

set_option autoImplicit false

noncomputable section

/-- The exact public-query schedule: all causal challenge draws, followed by
all post-round query-seed draws. -/
def constructionQuerySchedule {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    Fin (m + queryCount) → SpQuery Rate Cap :=
  Fin.append
    (fun j => challengeConstructionQuery statement receipt j)
    (fun a => queryConstructionQuery statement receipt a)

/-- The schedule function enumerates literally the canonical query list used
by `transcriptPrimitiveWork`. -/
theorem constructionQueries_eq_ofFn {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount) :
    constructionQueries statement receipt =
      List.ofFn (constructionQuerySchedule statement receipt) := by
  simp [constructionQueries, constructionQuerySchedule]

/-- Put a fixed candidate receipt into the adaptive sponge-game interface.
The verdict remains a parameter because algebraic/Merkle acceptance is
already represented by `Accepts`; this adapter is responsible only for the
random-oracle interaction and its exact cost. -/
def constructionDistinguisher {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    Distinguisher Rate Cap (m + queryCount) where
  move answers :=
    if h : answers.length < m + queryCount then
      constructionQuerySchedule statement receipt ⟨answers.length, h⟩
    else
      .fwd (0, 0)
  out := verdict

/-- At public round `j`, every hypothetical answer trace has length `j`, so
the adapter selects exactly schedule entry `j`. -/
theorem constructionDistinguisher_move {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (answers : Fin (m + queryCount) → SpAnswer Rate Cap)
    (j : Fin (m + queryCount)) :
  (constructionDistinguisher statement receipt verdict).move
        ((List.ofFn answers).take j) =
      constructionQuerySchedule statement receipt j := by
  simp [constructionDistinguisher, List.length_take]

/-- Exact work identity for every hypothetical answer trace.  In particular,
adaptivity in the surrounding game cannot cause this receipt schedule to be
charged by public draw count instead of absorbed-block count. -/
theorem constructionDistinguisher_primitiveWorkOn_exact
    {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (answers : Fin (m + queryCount) → SpAnswer Rate Cap) :
    (constructionDistinguisher statement receipt verdict).primitiveWorkOn
        answers =
      transcriptPrimitiveWork statement receipt := by
  unfold Distinguisher.primitiveWorkOn
  simp_rw [constructionDistinguisher_move]
  unfold transcriptPrimitiveWork
  rw [constructionQueries_eq_ofFn, List.map_ofFn, List.ofFn_eq_map]

/-- The precise ledger is therefore a valid `PrimitiveWorkBound` witness for
the exact BaseFold receipt schedule in `SpongeIndiffWorkGame`. -/
theorem constructionDistinguisher_workBound {m queryCount : Nat}
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    PrimitiveWorkBound
      (constructionDistinguisher statement receipt verdict)
      (transcriptPrimitiveWork statement receipt) := by
  intro answers
  rw [constructionDistinguisher_primitiveWorkOn_exact]

#check @constructionQueries_eq_ofFn
#check @constructionDistinguisher_primitiveWorkOn_exact
#check @constructionDistinguisher_workBound

end

end Minidregg.Selvage.BaseFoldBcsSpongeGame
