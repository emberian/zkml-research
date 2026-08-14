/-
# Selvage.SpongeIndiffDeferredWork — work-indexed deferred ideal semantics

The prefix hybrid samples every construction prefix eagerly.  The ideal world
answers only the public construction query and defers hidden prefix samples
until a primitive query actually reveals them.  Both worlds nevertheless need
one fixed sample space indexed by total primitive work.

This module supplies the missing operational ideal side on exactly that space.
Every public round consumes its full primitive-work segment, but the deferred
ideal step uses only the segment's first pair.  For a construction this pair's
rate answers the full-message RO query and the rest of the segment is hidden
slack; for a primitive query the same pair supplies both the only branch-relevant
rate sample and the primitive capacity sample.  The step is definitionally the
landed `idealStep` under a constant current-round coin assignment.

No distributional equality is asserted here.  The eager construction must
reindex the work vector so its full-prefix rate coin moves to the deferred
segment head and each later reveal receives the corresponding earlier hidden
prefix coin.  `SpongeIndiffUniformCoupling` is the probability transport once
that adaptive bijection and the off-bad agreement proof are constructed.
-/
import Selvage.SpongeIndiffUniformCoupling

namespace Minidregg.Selvage

section DeferredWork

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- The landed ideal state plus a fixed unconsumed primitive-work suffix. -/
structure DeferredWorkState (Rate Cap : Type) where
  core : IdealState Rate Cap
  remaining : List (Rate × Cap)
  work : Nat

def DeferredWorkState.initial {work : Nat}
    (coins : Fin work → Rate × Cap) : DeferredWorkState Rate Cap :=
  ⟨⟨Oracle.empty, Oracle.empty, []⟩, List.ofFn coins, 0⟩

inductive DeferredWorkError where
  | exhausted
  | impossibleEmptySegment

/-- A pair carries exactly the branch-relevant randomness for one ideal step.
On a completing forward query `coin.1` is the RO response and `coin.2` is the
fresh capacity; on an unrooted forward/inverse query the pair itself is the
primitive response.  The unused duplicate rate component of the old ideal
coin shape is observationally dead on either branch. -/
def workCoinAsIdeal (coin : Rate × Cap) : Rate × (Rate × Cap) :=
  (coin.1, coin)

/-- One deferred semantic step with an explicitly selected work pair. -/
noncomputable def deferredIdealStepWithCoin {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : IdealState Rate Cap) (j : Fin q) (coin : Rate × Cap) :
    IdealState Rate Cap :=
  idealStep D iv (fun _ => workCoinAsIdeal coin) state j

omit [DecidableEq Rate] in
/-- The deferred step is literally the landed ideal step on its selected
current-round pair. -/
theorem deferredIdealStepWithCoin_eq_idealStep {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : IdealState Rate Cap) (j : Fin q) (coin : Rate × Cap) :
    deferredIdealStepWithCoin D iv state j coin =
      idealStep D iv (fun _ => workCoinAsIdeal coin) state j := rfl

omit [DecidableEq Rate] in
/-- Every deferred semantic step delivers exactly one public answer, just as
the landed ideal step does. -/
theorem deferredIdealStepWithCoin_ans_length {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : IdealState Rate Cap) (j : Fin q) (coin : Rate × Cap) :
    (deferredIdealStepWithCoin D iv state j coin).ans.length =
      state.ans.length + 1 := by
  unfold deferredIdealStepWithCoin idealStep
  cases D.move state.ans <;> simp

/-- One public round consumes the exact segment selected by its adaptive
primitive cost.  The segment head drives the deferred ideal step; the rest is
reserved randomness which the eager world may move to later reveal points. -/
noncomputable def deferredWorkStep {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : DeferredWorkState Rate Cap) (j : Fin q) :
    Except DeferredWorkError (DeferredWorkState Rate Cap) :=
  let need := (D.move state.core.ans).primitiveCalls
  let used := state.remaining.take need
  if used.length = need then
    match used with
    | [] => .error .impossibleEmptySegment
    | coin :: _ =>
        .ok ⟨deferredIdealStepWithCoin D iv state.core j coin,
          state.remaining.drop need, state.work + need⟩
  else .error .exhausted

omit [DecidableEq Rate] in
/-- Successful deferred execution charges exactly the current adaptive
query's primitive work. -/
theorem deferredWorkStep_work_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state next : DeferredWorkState Rate Cap) (j : Fin q)
    (h : deferredWorkStep D iv state j = .ok next) :
    next.work = state.work + (D.move state.core.ans).primitiveCalls := by
  unfold deferredWorkStep at h
  dsimp only at h
  split at h
  · split at h
    · contradiction
    · injection h with hnext
      subst next
      rfl
  · contradiction

omit [DecidableEq Rate] in
/-- Successful deferred execution removes exactly the current work segment. -/
theorem deferredWorkStep_remaining_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state next : DeferredWorkState Rate Cap) (j : Fin q)
    (h : deferredWorkStep D iv state j = .ok next) :
    next.remaining =
      state.remaining.drop (D.move state.core.ans).primitiveCalls := by
  unfold deferredWorkStep at h
  dsimp only at h
  split at h
  · split at h
    · contradiction
    · injection h with hnext
      subst next
      rfl
  · contradiction

omit [DecidableEq Rate] in
/-- A successful work-indexed deferred step also advances the public-prefix
length by exactly one.  This is the induction invariant that connects a
runner's numeric round with a static receipt schedule. -/
theorem deferredWorkStep_ans_length {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state next : DeferredWorkState Rate Cap) (j : Fin q)
    (h : deferredWorkStep D iv state j = .ok next) :
    next.core.ans.length = state.core.ans.length + 1 := by
  unfold deferredWorkStep at h
  dsimp only at h
  split at h
  · split at h
    · contradiction
    · injection h with hnext
      subst next
      exact deferredIdealStepWithCoin_ans_length D iv state.core j _
  · contradiction

omit [DecidableEq Rate] in
/-- On a construction query, an explicitly identified exact segment exposes
the precise head coin used by the deferred semantic step. -/
theorem deferredWorkStep_constr_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : DeferredWorkState Rate Cap) (j : Fin q)
    (x : Rate) (xs : List Rate) (coin : Rate × Cap)
    (rest : List (Rate × Cap))
    (hquery : D.move state.core.ans = .constr x xs)
    (hused : state.remaining.take (xs.length + 1) = coin :: rest)
    (hlength : (coin :: rest).length = xs.length + 1) :
    deferredWorkStep D iv state j =
      .ok ⟨deferredIdealStepWithCoin D iv state.core j coin,
        state.remaining.drop (xs.length + 1),
        state.work + (xs.length + 1)⟩ := by
  unfold deferredWorkStep
  dsimp only
  rw [hquery]
  simp only [SpQuery.primitiveCalls]
  rw [show (state.remaining.take (xs.length + 1)).length =
      xs.length + 1 by rw [hused, hlength]]
  rw [hused]
  simp

omit [DecidableEq Rate] in
/-- If the selected full construction message is fresh in the deferred RO,
its segment-head rate is exactly the appended public answer; construction
queries leave the primitive simulator log unchanged. -/
theorem deferredIdealStepWithCoin_constr_fresh {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : IdealState Rate Cap) (j : Fin q)
    (x : Rate) (xs : List Rate) (coin : Rate × Cap)
    (hquery : D.move state.ans = .constr x xs)
    (hfresh : state.ro.lookup (x :: xs) = none) :
    deferredIdealStepWithCoin D iv state j coin =
      ⟨(state.ro.respond (x :: xs) coin.1).2, state.sim,
        state.ans ++ [.rate coin.1]⟩ := by
  unfold deferredIdealStepWithCoin idealStep
  rw [hquery]
  simp [workCoinAsIdeal, Oracle.respond_fresh_fst hfresh]

omit [DecidableEq Rate] in
/-- The deferred runner has no semantic failure mode once enough work coins
remain.  Positivity of `SpQuery.primitiveCalls` also rules out the nominal
empty-segment error. -/
theorem deferredWorkStep_exists_of_need_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : DeferredWorkState Rate Cap) (j : Fin q)
    (hneed : (D.move state.core.ans).primitiveCalls ≤
      state.remaining.length) :
    ∃ next, deferredWorkStep D iv state j = .ok next := by
  have hlength :
      (state.remaining.take
          (D.move state.core.ans).primitiveCalls).length =
        (D.move state.core.ans).primitiveCalls := by
    rw [List.length_take]
    omega
  have hnonempty :
      state.remaining.take (D.move state.core.ans).primitiveCalls ≠ [] := by
    intro hempty
    have hzero := congrArg List.length hempty
    rw [hlength] at hzero
    exact (Nat.ne_of_gt (SpQuery.primitiveCalls_pos _)) hzero
  unfold deferredWorkStep
  dsimp only
  rw [if_pos hlength]
  cases hused :
      state.remaining.take (D.move state.core.ans).primitiveCalls with
  | nil => exact (hnonempty hused).elim
  | cons coin rest =>
      exact ⟨⟨deferredIdealStepWithCoin D iv state.core j coin,
        state.remaining.drop (D.move state.core.ans).primitiveCalls,
        state.work + (D.move state.core.ans).primitiveCalls⟩, rfl⟩

/-- Execute every public round against one fixed work vector. -/
noncomputable def deferredWorkRun {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) :
    Except DeferredWorkError (DeferredWorkState Rate Cap) :=
  (List.finRange q).foldl
    (fun result j => result.bind fun state => deferredWorkStep D iv state j)
    (.ok (DeferredWorkState.initial coins))

/-- Deferred ideal acceptance on the same fixed primitive-work space as the
eager prefix hybrid. -/
noncomputable def deferredWorkAccept {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) : Prop :=
  match deferredWorkRun D iv coins with
  | .ok state => D.out state.core.ans = true
  | .error _ => False

end DeferredWork

/-! ## A two-block construction requires a real coordinate move -/

namespace SpongeDeferredWorkExample

open SpongePrefixHybridExample

/-- The eager stream programs `[1]` from coordinate 0 and `[1,1]` from
coordinate 1, then exposes `[1]` at coordinate 2. -/
def eager : Fin 3 → ZMod 2 × Nat := SpongeWorkStreamExample.stream

/-- The deferred world needs the full-message coin first, ignores one unit of
construction slack, and receives the eager prefix coin at its later reveal.
This is the concrete permutation `(0 1 2) ↦ (1 2 0)`. -/
def deferred : Fin 3 → ZMod 2 × Nat
  | 0 => eager 1
  | 1 => eager 2
  | 2 => eager 0

noncomputable def fullMessageRo : Oracle (List (ZMod 2)) (ZMod 2) :=
  (Oracle.empty.respond [1, 1] 0).2

noncomputable def afterConstruction : DeferredWorkState (ZMod 2) Nat :=
  ⟨⟨fullMessageRo, Oracle.empty, [.rate 0]⟩, [(1, 1)], 2⟩

theorem deferred_list : List.ofFn deferred =
    [((0 : ZMod 2), (2 : Nat)), (0, 3), (1, 1)] := by
  rfl

theorem first_step_exact :
    deferredWorkStep constructionThenForward iv
      (DeferredWorkState.initial deferred) 0 = .ok afterConstruction := by
  unfold DeferredWorkState.initial
  rw [deferred_list]
  unfold deferredWorkStep
  simp only [constructionThenForward, List.isEmpty_nil, ↓reduceIte,
    SpQuery.primitiveCalls, List.take, List.length_cons, List.length_nil,
    Nat.reduceAdd, List.drop, deferredIdealStepWithCoin, idealStep,
    workCoinAsIdeal, fullMessageRo, afterConstruction]
  rw [Oracle.respond_fresh_fst (Oracle.lookup_empty [1, 1])]
  rfl

/-- The revealed first prefix is still fresh in the deferred primitive table,
and is programmed with the eager coordinate-0 pair after reindexing. -/
theorem revealed_prefix_answer :
    (simFwdRO iv fullMessageRo Oracle.empty (1, 0) 1 (1, 1)).1 =
      ((1 : ZMod 2), (1 : Nat)) := by
  have hcompletion :
      completion? (Oracle.empty : Oracle (ZMod 2 × Nat) (ZMod 2 × Nat))
        iv (1, 0) = some [1] := by
    simpa [iv] using
      (completion?_empty_iv
        (iv := iv) (s := ((1 : ZMod 2), (0 : Nat))) rfl)
  have hfresh : fullMessageRo.lookup [1] = none := by
    unfold fullMessageRo
    rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_empty]
  unfold simFwdRO
  rw [hcompletion]
  simp only
  rw [Oracle.respond_fresh_fst hfresh,
    Oracle.respond_fresh_fst (Oracle.lookup_empty (1, 0))]

noncomputable def revealReply :
    (ZMod 2 × Nat) × Oracle (List (ZMod 2)) (ZMod 2) ×
      Oracle (ZMod 2 × Nat) (ZMod 2 × Nat) :=
  simFwdRO iv fullMessageRo Oracle.empty (1, 0) 1 (1, 1)

noncomputable def afterReveal : DeferredWorkState (ZMod 2) Nat :=
  ⟨⟨revealReply.2.1, revealReply.2.2,
      [.rate 0, .block revealReply.1]⟩, [], 3⟩

theorem second_step_exact :
    deferredWorkStep constructionThenForward iv afterConstruction 1 =
      .ok afterReveal := by
  unfold deferredWorkStep
  simp only [constructionThenForward, afterConstruction, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte, SpQuery.primitiveCalls, List.take,
    List.length_cons, List.length_nil, List.drop, deferredIdealStepWithCoin,
    idealStep, workCoinAsIdeal, revealReply, afterReveal]
  rfl

/-- The deferred run consumes the same three work units and produces the same
public answer trace as the eager run, while sampling the hidden prefix only at
its later reveal. -/
theorem deferred_work_stream_replays :
    deferredWorkRun constructionThenForward iv deferred = .ok afterReveal := by
  unfold deferredWorkRun
  rw [show List.finRange 2 = [0, 1] by decide]
  simp only [List.foldl_cons, List.foldl_nil, Except.bind]
  rw [first_step_exact]
  exact second_step_exact

theorem deferred_public_trace :
    afterReveal.core.ans =
      [.rate 0, .block ((1 : ZMod 2), (1 : Nat))] := by
  unfold afterReveal revealReply
  rw [revealed_prefix_answer]

/-- The concrete eager/deferred move is an actual permutation of the fixed
work coordinates, not a matching-marginals assertion. -/
def rotateIndex : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

noncomputable def rotateIndexEquiv : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective rotateIndex (by decide)

theorem deferred_is_permuted_eager :
    permuteWorkCoins rotateIndexEquiv eager = deferred := by
  funext index
  fin_cases index <;> rfl

end SpongeDeferredWorkExample

/-- info: 'Minidregg.Selvage.deferredWorkStep_work_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deferredWorkStep_work_exact
/-- info: 'Minidregg.Selvage.deferredWorkStep_ans_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deferredWorkStep_ans_length
/-- info: 'Minidregg.Selvage.deferredWorkStep_exists_of_need_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deferredWorkStep_exists_of_need_le
/-- info: 'Minidregg.Selvage.SpongeDeferredWorkExample.revealed_prefix_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeDeferredWorkExample.revealed_prefix_answer
/-- info: 'Minidregg.Selvage.SpongeDeferredWorkExample.deferred_work_stream_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeDeferredWorkExample.deferred_work_stream_replays

end Minidregg.Selvage
