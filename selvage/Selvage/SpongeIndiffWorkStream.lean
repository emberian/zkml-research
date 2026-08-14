/-
# Selvage.SpongeIndiffWorkStream — fixed uniform coins indexed by primitive work

Construction messages have variable block length, so assigning one coin pair
per public query is not the sample space used by the sponge computation.  This
module feeds the prefix-programmed hybrid from a fixed `Fin work` vector of
`(rate, capacity)` pairs.  Each primitive evaluation consumes exactly one
pair: a construction consumes one pair per block, while a public forward or
inverse query consumes one pair.

The vector is a genuine finite uniform sample space.  If an adaptive execution
requests more than `work` pairs it fails with `exhausted`; no randomness is
conjured beyond the supplied vector.  This is the operational basis for the
work-indexed game.  A later coupling must still reorder deferred coins when
comparing construction-first programming with the landed ideal simulator.
-/
import Selvage.SpongeIndiffPrefixHybrid

namespace Minidregg.Selvage

section WorkStream

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Repackage an exact primitive-work segment into the coin shape expected by
the public query.  The caller separately checks the segment length. -/
def SpQuery.prefixCoins : SpQuery Rate Cap → List (Rate × Cap) →
    Option (PrefixHybridCoins Rate Cap)
  | .constr _ _, used =>
      some (.construction (used.map Prod.fst) (used.map Prod.snd))
  | .fwd _, [coin] => some (.primitive coin)
  | .inv _, [coin] => some (.primitive coin)
  | _, _ => none

omit [AddCommGroup Rate] [DecidableEq Rate] in
/-- Exact-length work segments always have the right public coin shape. -/
theorem SpQuery.prefixCoins_some_of_length (query : SpQuery Rate Cap)
    (used : List (Rate × Cap))
    (hlength : used.length = query.primitiveCalls) :
    ∃ coins, query.prefixCoins used = some coins := by
  cases query with
  | constr x xs => exact ⟨.construction (used.map Prod.fst) (used.map Prod.snd), rfl⟩
  | fwd s =>
      cases used with
      | nil => simp [SpQuery.primitiveCalls] at hlength
      | cons coin rest =>
          cases rest with
          | nil => exact ⟨.primitive coin, rfl⟩
          | cons coin' rest => simp [SpQuery.primitiveCalls] at hlength
  | inv t =>
      cases used with
      | nil => simp [SpQuery.primitiveCalls] at hlength
      | cons coin rest =>
          cases rest with
          | nil => exact ⟨.primitive coin, rfl⟩
          | cons coin' rest => simp [SpQuery.primitiveCalls] at hlength

/-- Prefix-programmed hybrid state plus the unconsumed work vector suffix. -/
structure WorkHybridState (Rate Cap : Type) where
  core : PrefixHybridState Rate Cap
  remaining : List (Rate × Cap)

def WorkHybridState.initial {work : Nat}
    (coins : Fin work → Rate × Cap) : WorkHybridState Rate Cap :=
  ⟨PrefixHybridState.empty, List.ofFn coins⟩

inductive WorkHybridError where
  | exhausted
  | malformedSegment
  | hybrid (error : PrefixHybridError)

/-- Consume the next exact work segment and execute one adaptive public step. -/
noncomputable def workHybridStep {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st : WorkHybridState Rate Cap) (j : Fin q) :
    Except WorkHybridError (WorkHybridState Rate Cap) :=
  let query := D.move st.core.ans
  let need := query.primitiveCalls
  let used := st.remaining.take need
  if used.length = need then
    match query.prefixCoins used with
    | some roundCoins =>
        match prefixHybridStep D iv (fun _ => roundCoins) st.core j with
        | .ok next => .ok ⟨next, st.remaining.drop need⟩
        | .error error => .error (.hybrid error)
    | none => .error .malformedSegment
  else .error .exhausted

/-- Every successful work-stream step charges exactly the selected query's
primitive cost in the underlying hybrid state. -/
theorem workHybridStep_work_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st next : WorkHybridState Rate Cap) (j : Fin q)
    (h : workHybridStep D iv st j = .ok next) :
    next.core.work = st.core.work + (D.move st.core.ans).primitiveCalls := by
  unfold workHybridStep at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        exact prefixHybridStep_work_exact D iv _ st.core _ j ‹_›
      · contradiction
    · contradiction
  · contradiction

/-- Every successful work-stream step appends exactly one public answer. -/
theorem workHybridStep_ans_length {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st next : WorkHybridState Rate Cap) (j : Fin q)
    (h : workHybridStep D iv st j = .ok next) :
    next.core.ans.length = st.core.ans.length + 1 := by
  unfold workHybridStep at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        exact prefixHybridStep_ans_length D iv _ st.core _ j ‹_›
      · contradiction
    · contradiction
  · contradiction

/-- A successful step drops exactly the selected query's primitive cost from
the front of the remaining work stream. -/
theorem workHybridStep_remaining_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st next : WorkHybridState Rate Cap) (j : Fin q)
    (h : workHybridStep D iv st j = .ok next) :
    next.remaining = st.remaining.drop (D.move st.core.ans).primitiveCalls := by
  unfold workHybridStep at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        rfl
      · contradiction
    · contradiction
  · contradiction

/-- With enough supplied work, the eager work-stream step cannot fail for an
administrative reason: exact segment shape is derivable from its length.  Its
only remaining failure is an explicit prefix-hybrid semantic error. -/
theorem workHybridStep_ok_or_hybrid_of_need_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st : WorkHybridState Rate Cap) (j : Fin q)
    (hneed : (D.move st.core.ans).primitiveCalls ≤ st.remaining.length) :
    (∃ next, workHybridStep D iv st j = .ok next) ∨
      ∃ error, workHybridStep D iv st j = .error (.hybrid error) := by
  have hlength :
      (st.remaining.take
          (D.move st.core.ans).primitiveCalls).length =
        (D.move st.core.ans).primitiveCalls := by
    rw [List.length_take]
    omega
  obtain ⟨roundCoins, hcoins⟩ :=
    SpQuery.prefixCoins_some_of_length (D.move st.core.ans)
      (st.remaining.take (D.move st.core.ans).primitiveCalls) hlength
  unfold workHybridStep
  dsimp only
  rw [if_pos hlength, hcoins]
  cases hstep : prefixHybridStep D iv (fun _ => roundCoins) st.core j with
  | ok next =>
      refine Or.inl ⟨⟨next,
        st.remaining.drop (D.move st.core.ans).primitiveCalls⟩, ?_⟩
      simp [hstep]
  | error error =>
      refine Or.inr ⟨error, ?_⟩
      simp [hstep]

/-- Execute all public rounds against one fixed primitive-work vector. -/
noncomputable def workHybridRun {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) :
    Except WorkHybridError (WorkHybridState Rate Cap) :=
  (List.finRange q).foldl
    (fun state j => state.bind fun st => workHybridStep D iv st j)
    (.ok (WorkHybridState.initial coins))

end WorkStream

section WorkProbability

variable (Rate Cap : Type) [AddCommGroup Rate]
  [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]

/-- Acceptance predicate of the corrected prefix-programmed random-function
hybrid on one fixed primitive-work vector.  Exhaustion or a semantic mismatch
rejects. -/
noncomputable def workHybridAccept {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) : Prop :=
    match workHybridRun D iv coins with
    | .ok state => D.out state.core.ans = true
    | .error _ => False

/-- Acceptance probability of the corrected prefix-programmed random-function
hybrid on a fixed `work`-pair uniform sample space. -/
noncomputable def workHybridProb {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) : Real :=
  uniformProb (Fin work → Rate × Cap) (workHybridAccept Rate Cap D iv)

/-- The honest interface still required to identify the prefix-programmed
work game with the ideal game.  The hybrid may reject on a consistency bad
event, so unconditional equality is not a sound target.  A witness must expose
that event, prove pointwise agreement away from it, and separately realize the
deferred ideal acceptance predicate on the same finite work space. -/
structure PrefixHybridIdealOffBadWitness {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) where
  bad : (Fin work → Rate × Cap) → Prop
  deferredAccept : (Fin work → Rate × Cap) → Prop
  agree_off_bad : ∀ coins, ¬ bad coins →
    (workHybridAccept Rate Cap D iv coins ↔ deferredAccept coins)
  deferred_probability_exact :
    uniformProb (Fin work → Rate × Cap) deferredAccept = idealProb D iv

/-- Work-indexed hybrid-to-ideal agreement is deliberately an off-bad witness
target.  A later coupling must construct the witness and price its `bad` event;
this declaration itself asserts neither existence nor a numerical bound. -/
def PrefixHybridIdealOffBadTarget (iv : Rate × Cap) : Prop :=
  ∀ (q work : Nat) (D : Distinguisher Rate Cap q),
    PrimitiveWorkBound D work →
      Nonempty (PrefixHybridIdealOffBadWitness Rate Cap (work := work) D iv)

end WorkProbability

/-! ## The fixed stream actually drives a construction-first replay -/

namespace SpongeWorkStreamExample

open SpongePrefixHybridExample

def stream : Fin 3 → ZMod 2 × Nat
  | 0 => (1, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)

noncomputable def initial : WorkHybridState (ZMod 2) Nat :=
  ⟨PrefixHybridState.empty, [(1, 1), (0, 2), (0, 3)]⟩

noncomputable def afterConstruction : WorkHybridState (ZMod 2) Nat :=
  ⟨firstState, [(0, 3)]⟩

noncomputable def afterReplay : WorkHybridState (ZMod 2) Nat :=
  ⟨finalState, []⟩

theorem first_step_exact :
    workHybridStep constructionThenForward iv initial 0 =
      .ok afterConstruction := by
  unfold workHybridStep
  simp only [initial, constructionThenForward, PrefixHybridState.empty,
    List.isEmpty_nil, ↓reduceIte, SpQuery.primitiveCalls, List.take,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.map,
    SpQuery.prefixCoins, List.drop]
  have hcoin :
      SpongePrefixHybridExample.coins 0 =
        (fun _ => PrefixHybridCoins.construction [1, 0] [1, 2]) 0 := rfl
  have hconstant :=
    (prefixHybridStep_eq_of_coin_eq
      (D := SpongePrefixHybridExample.constructionThenForward)
      (iv := iv) (coins := SpongePrefixHybridExample.coins)
      (coins' := fun _ => PrefixHybridCoins.construction [1, 0] [1, 2])
      (st := PrefixHybridState.empty) (j := 0) hcoin).symm.trans
        SpongePrefixHybridExample.first_step_exact
  unfold SpongePrefixHybridExample.constructionThenForward
    PrefixHybridState.empty at hconstant
  rw [hconstant]
  rfl

theorem second_step_exact :
    workHybridStep constructionThenForward iv afterConstruction 1 =
      .ok afterReplay := by
  unfold workHybridStep
  simp only [afterConstruction, constructionThenForward, firstState,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, SpQuery.primitiveCalls,
    List.take, List.length_cons, List.length_nil, SpQuery.prefixCoins,
    List.drop]
  have hcoin :
      SpongePrefixHybridExample.coins 1 =
        (fun _ => PrefixHybridCoins.primitive (0, 3)) 1 := rfl
  have hconstant :=
    (prefixHybridStep_eq_of_coin_eq
      (D := SpongePrefixHybridExample.constructionThenForward)
      (iv := iv) (coins := SpongePrefixHybridExample.coins)
      (coins' := fun _ => PrefixHybridCoins.primitive (0, 3))
      (st := SpongePrefixHybridExample.firstState) (j := 1) hcoin).symm.trans
        SpongePrefixHybridExample.second_step_exact
  unfold SpongePrefixHybridExample.constructionThenForward
    SpongePrefixHybridExample.firstState at hconstant
  rw [hconstant]
  rfl

theorem stream_as_list : List.ofFn stream = [(1, 1), (0, 2), (0, 3)] := by
  decide

/-- A fixed three-pair sample drives the two-block construction and subsequent
public replay, consuming the work vector exactly. -/
theorem fixed_work_stream_replays :
    workHybridRun constructionThenForward iv stream = .ok afterReplay := by
  unfold workHybridRun WorkHybridState.initial
  rw [stream_as_list]
  rw [show List.finRange 2 = [0, 1] by decide]
  simp only [List.foldl_cons, List.foldl_nil, Except.bind]
  rw [show workHybridStep constructionThenForward iv
      { core := PrefixHybridState.empty,
        remaining := [(1, 1), (0, 2), (0, 3)] } 0 =
        .ok afterConstruction by
    simpa only [initial] using first_step_exact]
  exact second_step_exact

end SpongeWorkStreamExample

/-- info: 'Minidregg.Selvage.workHybridStep_work_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms workHybridStep_work_exact
/-- info: 'Minidregg.Selvage.workHybridStep_ok_or_hybrid_of_need_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms workHybridStep_ok_or_hybrid_of_need_le
/-- info: 'Minidregg.Selvage.SpongeWorkStreamExample.fixed_work_stream_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeWorkStreamExample.fixed_work_stream_replays

end Minidregg.Selvage
