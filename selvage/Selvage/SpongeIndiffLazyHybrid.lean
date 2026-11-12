/-
# Selvage.SpongeIndiffLazyHybrid — an adaptive construction/primitive table world

This is the operational random-function/permutation-hybrid precursor missing
from `SpongeIndiff`.  It carries both the lazy construction RO and a hidden
primitive table.  Construction queries execute every absorbed block through
that table and must squeeze to the RO answer; later forward or inverse public
primitive queries use the same table and therefore replay construction-created
edges exactly.

Each external round supplies a rate coin and a list of primitive block coins.
The list length must be the query's exact `SpQuery.primitiveCalls`, and the
state records the accumulated primitive work.  This module defines and
exercises the adaptive world.  It deliberately does not yet prove that its
coin distribution is a random permutation, nor couple it to `idealRun`; those
are the subsequent game hops.
-/
import Selvage.SpongeIndiffLazyConstruction

namespace Minidregg.Selvage

section Hybrid

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Randomness assigned to one public round.  Construction rounds use one
block coin per absorbed block; primitive rounds require a singleton list. -/
structure LazyHybridCoins (Rate Cap : Type) where
  rate : Rate
  blocks : List (Rate × Cap)

/-- Running state of the lazy-table hybrid. -/
structure LazyHybridState (Rate Cap : Type) where
  ro : Oracle (List Rate) Rate
  primitive : Oracle (Rate × Cap) (Rate × Cap)
  ans : List (SpAnswer Rate Cap)
  work : Nat

def LazyHybridState.empty : LazyHybridState Rate Cap :=
  ⟨Oracle.empty, Oracle.empty, [], 0⟩

inductive LazyHybridError where
  | wrongCoinCount
  | constructionMismatch

/-- One adaptive hybrid step.  Failure is semantic and fail-closed: malformed
coin allocation or an RO/primitive squeeze mismatch produces no next state. -/
noncomputable def lazyHybridStep {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → LazyHybridCoins Rate Cap)
    (st : LazyHybridState Rate Cap) (j : Fin q) :
    Except LazyHybridError (LazyHybridState Rate Cap) :=
  match D.move st.ans with
  | .constr x xs =>
      let message := x :: xs
      if (coins j).blocks.length = message.length then
        match coupledConstruction iv st.ro st.primitive message
            (coins j).rate (coins j).blocks with
        | some result =>
            .ok ⟨result.ro, result.primitive,
              st.ans ++ [.rate result.answer], st.work + message.length⟩
        | none => .error .constructionMismatch
      else .error .wrongCoinCount
  | .fwd s =>
      match (coins j).blocks with
      | [coin] =>
          let reply := st.primitive.respond s coin
          .ok ⟨st.ro, reply.2, st.ans ++ [.block reply.1], st.work + 1⟩
      | _ => .error .wrongCoinCount
  | .inv t =>
      match (coins j).blocks with
      | [coin] =>
          let reply := simInv st.primitive t coin
          .ok ⟨st.ro, reply.2, st.ans ++ [.block reply.1], st.work + 1⟩
      | _ => .error .wrongCoinCount

/-- Successful one-step execution increments the accumulated work by exactly
the primitive cost of the query chosen from the pre-state transcript. -/
theorem lazyHybridStep_work_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → LazyHybridCoins Rate Cap)
    (st next : LazyHybridState Rate Cap) (j : Fin q)
    (h : lazyHybridStep D iv coins st j = .ok next) :
    next.work = st.work + (D.move st.ans).primitiveCalls := by
  unfold lazyHybridStep at h
  cases hquery : D.move st.ans with
  | constr x xs =>
      rw [hquery] at h
      dsimp only at h
      split at h
      · split at h
        · injection h with hnext
          subst next
          rfl
        · contradiction
      · contradiction
  | fwd s =>
      rw [hquery] at h
      dsimp only at h
      cases hcoins : (coins j).blocks with
      | nil => rw [hcoins] at h; contradiction
      | cons coin rest =>
          cases rest with
          | nil =>
              rw [hcoins] at h
              injection h with hnext
              subst next
              rfl
          | cons coin' rest => rw [hcoins] at h; contradiction
  | inv t =>
      rw [hquery] at h
      dsimp only at h
      cases hcoins : (coins j).blocks with
      | nil => rw [hcoins] at h; contradiction
      | cons coin rest =>
          cases rest with
          | nil =>
              rw [hcoins] at h
              injection h with hnext
              subst next
              rfl
          | cons coin' rest => rw [hcoins] at h; contradiction

/-- Every successful step appends exactly one public answer. -/
theorem lazyHybridStep_ans_length {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → LazyHybridCoins Rate Cap)
    (st next : LazyHybridState Rate Cap) (j : Fin q)
    (h : lazyHybridStep D iv coins st j = .ok next) :
    next.ans.length = st.ans.length + 1 := by
  unfold lazyHybridStep at h
  cases hquery : D.move st.ans with
  | constr x xs =>
      rw [hquery] at h
      dsimp only at h
      split at h
      · split at h
        · injection h with hnext
          subst next
          simp
        · contradiction
      · contradiction
  | fwd s =>
      rw [hquery] at h
      dsimp only at h
      cases hcoins : (coins j).blocks with
      | nil => rw [hcoins] at h; contradiction
      | cons coin rest =>
          cases rest with
          | nil => rw [hcoins] at h; injection h with hnext; subst next; simp
          | cons coin' rest => rw [hcoins] at h; contradiction
  | inv t =>
      rw [hquery] at h
      dsimp only at h
      cases hcoins : (coins j).blocks with
      | nil => rw [hcoins] at h; contradiction
      | cons coin rest =>
          cases rest with
          | nil => rw [hcoins] at h; injection h with hnext; subst next; simp
          | cons coin' rest => rw [hcoins] at h; contradiction

/-- Fold the adaptive hybrid over the same external round indices as the
landed real and ideal games. -/
noncomputable def lazyHybridRun {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → LazyHybridCoins Rate Cap) :
    Except LazyHybridError (LazyHybridState Rate Cap) :=
  (List.finRange q).foldl
    (fun state j => state.bind fun st => lazyHybridStep D iv coins st j)
    (.ok LazyHybridState.empty)

end Hybrid

/-! ## Construction-first replay is operational, not aspirational -/

namespace SpongeLazyHybridExample

def iv : ZMod 2 × Fin 4 := (0, 0)

/-- First query a two-block construction.  After seeing its answer, expose the
first internal primitive input. -/
def constructionThenForward : Distinguisher (ZMod 2) (Fin 4) 2 where
  move answers :=
    if answers.isEmpty then .constr 1 [1] else .fwd (1, 0)
  out answers := answers.length = 2

def coins : Fin 2 → LazyHybridCoins (ZMod 2) (Fin 4)
  | 0 => ⟨1, [(0, 1), (1, 2)]⟩
  | 1 => ⟨0, [(1, 3)]⟩

noncomputable def firstState : LazyHybridState (ZMod 2) (Fin 4) :=
  ⟨SpongeLazyConstructionExample.coupledResult.ro,
    SpongeLazyConstructionExample.coupledResult.primitive,
    [.rate 1], 2⟩

noncomputable def finalState : LazyHybridState (ZMod 2) (Fin 4) :=
  ⟨SpongeLazyConstructionExample.coupledResult.ro,
    SpongeLazyConstructionExample.coupledResult.primitive,
    [.rate 1, .block (0, 1)], 3⟩

/-- The first construction succeeds, returns the RO answer `1`, and records
two primitive calls. -/
theorem first_step_exact :
    lazyHybridStep constructionThenForward iv coins LazyHybridState.empty 0 =
      .ok firstState := by
  simp only [lazyHybridStep, constructionThenForward, LazyHybridState.empty,
    List.isEmpty_nil, ↓reduceIte, coins, Fin.isValue, List.length_cons,
    List.length_nil, Nat.reduceAdd, ↓reduceIte]
  rw [show iv = SpongeLazyConstructionExample.iv by rfl]
  rw [SpongeLazyConstructionExample.two_block_coupled_exact_literals]
  rfl

theorem first_edge_lookup :
    SpongeLazyConstructionExample.coupledResult.primitive.lookup (1, 0) =
      some (0, 1) := by
  unfold SpongeLazyConstructionExample.coupledResult
  rw [Oracle.lookup_respond_ne _ (by decide)]
  rw [Oracle.lookup_respond_self,
    Oracle.respond_fresh_fst (Oracle.lookup_empty (1, 0))]

theorem second_step_exact :
    lazyHybridStep constructionThenForward iv coins firstState 1 =
      .ok finalState := by
  simp only [lazyHybridStep, constructionThenForward, firstState,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, coins, Fin.isValue]
  rw [Oracle.respond_hit first_edge_lookup]
  rfl

/-- The subsequent public forward query replays the first hidden construction
edge `(1,0) ↦ (0,1)`; its fresh supplied coin `(1,3)` is ignored. -/
theorem construction_first_forward_replays :
    lazyHybridRun constructionThenForward iv coins = .ok finalState ∧
      finalState.ans = [.rate 1, .block (0, 1)] ∧ finalState.work = 3 := by
  constructor
  · unfold lazyHybridRun
    rw [show List.finRange 2 = [0, 1] by decide]
    simp only [List.foldl_cons, List.foldl_nil, Except.bind]
    rw [first_step_exact]
    change lazyHybridStep constructionThenForward iv coins firstState 1 =
      .ok finalState
    exact second_step_exact
  · exact ⟨rfl, rfl⟩

end SpongeLazyHybridExample

/-- info: 'Minidregg.Selvage.lazyHybridStep_work_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lazyHybridStep_work_exact
/-- info: 'Minidregg.Selvage.SpongeLazyHybridExample.construction_first_forward_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeLazyHybridExample.construction_first_forward_replays

end Minidregg.Selvage
