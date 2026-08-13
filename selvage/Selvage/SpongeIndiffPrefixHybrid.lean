/-
# Selvage.SpongeIndiffPrefixHybrid — adaptive prefix-programmed sponge world

The earlier diagnostic lazy hybrid sampled an independent primitive path and
only compared its final rate with one full-message RO answer.  That is useful
for finding mismatches, but it is not the construction-first simulator: every
nonempty prefix must instead program (or consistently replay) its primitive
edge to that prefix's RO answer.

This module gives that corrected operational world.  Construction rounds carry
one RO-rate coin and one fresh-capacity coin per absorbed block.  Public
forward/inverse rounds carry one primitive coin.  The sum type makes a query's
coin shape fail closed, while the state records exact primitive work separately
from the number of public rounds.

This is still an operational hybrid, not a probability theorem.  Coupling its
variable-length work stream to a fixed uniform sample space and switching the
lazy random function to a random permutation remain explicit later hops.
-/
import Selvage.SpongeIndiffPrefixProgramming

namespace Minidregg.Selvage

section PrefixHybrid

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Query-shaped randomness for one adaptive public round. -/
inductive PrefixHybridCoins (Rate Cap : Type) where
  | construction (rateCoins : List Rate) (capacityCoins : List Cap)
  | primitive (coin : Rate × Cap)

/-- State shared by the construction RO and the public primitive interfaces. -/
structure PrefixHybridState (Rate Cap : Type) where
  ro : Oracle (List Rate) Rate
  primitive : Oracle (Rate × Cap) (Rate × Cap)
  ans : List (SpAnswer Rate Cap)
  work : Nat

def PrefixHybridState.empty : PrefixHybridState Rate Cap :=
  ⟨Oracle.empty, Oracle.empty, [], 0⟩

inductive PrefixHybridError where
  | wrongCoinShape
  | wrongCoinCount
  | constructionMismatch

/-- One corrected adaptive step.  Construction answers are the final programmed
prefix rate.  Public primitive calls share the exact same primitive table. -/
noncomputable def prefixHybridStep {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → PrefixHybridCoins Rate Cap)
    (st : PrefixHybridState Rate Cap) (j : Fin q) :
    Except PrefixHybridError (PrefixHybridState Rate Cap) :=
  match D.move st.ans, coins j with
  | .constr x xs, .construction rateCoins capacityCoins =>
      let message := x :: xs
      if rateCoins.length = message.length ∧
          capacityCoins.length = message.length then
        match programConstruction iv st.ro st.primitive message rateCoins
            capacityCoins with
        | some result =>
            .ok ⟨result.ro, result.primitive,
              st.ans ++ [.rate result.state.1], st.work + message.length⟩
        | none => .error .constructionMismatch
      else .error .wrongCoinCount
  | .fwd s, .primitive coin =>
      let reply := st.primitive.respond s coin
      .ok ⟨st.ro, reply.2, st.ans ++ [.block reply.1], st.work + 1⟩
  | .inv t, .primitive coin =>
      let reply := simInv st.primitive t coin
      .ok ⟨st.ro, reply.2, st.ans ++ [.block reply.1], st.work + 1⟩
  | _, _ => .error .wrongCoinShape

/-- A public step reads only the coin assigned to its current round. -/
theorem prefixHybridStep_eq_of_coin_eq {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins coins' : Fin q → PrefixHybridCoins Rate Cap)
    (st : PrefixHybridState Rate Cap) (j : Fin q)
    (hcoin : coins j = coins' j) :
    prefixHybridStep D iv coins st j = prefixHybridStep D iv coins' st j := by
  unfold prefixHybridStep
  rw [hcoin]

/-- A successful step charges the exact primitive cost of the adaptive query. -/
theorem prefixHybridStep_work_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → PrefixHybridCoins Rate Cap)
    (st next : PrefixHybridState Rate Cap) (j : Fin q)
    (h : prefixHybridStep D iv coins st j = .ok next) :
    next.work = st.work + (D.move st.ans).primitiveCalls := by
  unfold prefixHybridStep at h
  cases hquery : D.move st.ans <;> cases hcoins : coins j <;>
    rw [hquery, hcoins] at h <;> dsimp only at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        rfl
      · contradiction
    · contradiction
  · contradiction
  · contradiction
  · injection h with hnext
    subst next
    rfl
  · contradiction
  · injection h with hnext
    subst next
    rfl

/-- Every successful public round appends exactly one answer. -/
theorem prefixHybridStep_ans_length {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → PrefixHybridCoins Rate Cap)
    (st next : PrefixHybridState Rate Cap) (j : Fin q)
    (h : prefixHybridStep D iv coins st j = .ok next) :
    next.ans.length = st.ans.length + 1 := by
  unfold prefixHybridStep at h
  cases hquery : D.move st.ans <;> cases hcoins : coins j <;>
    rw [hquery, hcoins] at h <;> dsimp only at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        simp
      · contradiction
    · contradiction
  · contradiction
  · contradiction
  · injection h with hnext
    subst next
    simp
  · contradiction
  · injection h with hnext
    subst next
    simp

/-- Fold the corrected adaptive hybrid over the public round indices. -/
noncomputable def prefixHybridRun {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → PrefixHybridCoins Rate Cap) :
    Except PrefixHybridError (PrefixHybridState Rate Cap) :=
  (List.finRange q).foldl
    (fun state j => state.bind fun st => prefixHybridStep D iv coins st j)
    (.ok PrefixHybridState.empty)

end PrefixHybrid

/-! ## Construction-first prefix replay is exact -/

namespace SpongePrefixHybridExample

def iv : ZMod 2 × Nat := SpongePrefixProgrammingExample.iv

def constructionThenForward : Distinguisher (ZMod 2) Nat 2 where
  move answers :=
    if answers.isEmpty then .constr 1 [1] else .fwd (1, 0)
  out answers := answers.length = 2

def coins : Fin 2 → PrefixHybridCoins (ZMod 2) Nat
  | 0 => .construction [1, 0] [1, 2]
  | 1 => .primitive (0, 3)

noncomputable def firstState : PrefixHybridState (ZMod 2) Nat :=
  ⟨SpongePrefixProgrammingExample.result.ro,
    SpongePrefixProgrammingExample.result.primitive, [.rate 0], 2⟩

noncomputable def finalState : PrefixHybridState (ZMod 2) Nat :=
  ⟨SpongePrefixProgrammingExample.result.ro,
    SpongePrefixProgrammingExample.result.primitive,
    [.rate 0, .block (1, 1)], 3⟩

theorem first_step_exact :
    prefixHybridStep constructionThenForward iv coins
        PrefixHybridState.empty 0 = .ok firstState := by
  simp only [prefixHybridStep, constructionThenForward, PrefixHybridState.empty,
    List.isEmpty_nil, ↓reduceIte, coins, List.length_cons,
    List.length_nil, Nat.reduceAdd, true_and, ↓reduceIte]
  rw [show iv = SpongePrefixProgrammingExample.iv by rfl]
  rw [SpongePrefixProgrammingExample.two_prefixes_programmed]
  rfl

theorem second_step_exact :
    prefixHybridStep constructionThenForward iv coins firstState 1 =
      .ok finalState := by
  simp only [prefixHybridStep, constructionThenForward, firstState,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, coins]
  rw [Oracle.respond_hit SpongePrefixProgrammingExample.first_edge_lookup]
  rfl

/-- The public forward query replays the edge programmed by the first message
prefix.  Its supplied fresh coin is ignored on the table hit. -/
theorem construction_first_forward_replays :
    prefixHybridRun constructionThenForward iv coins = .ok finalState ∧
      finalState.ans = [.rate 0, .block (1, 1)] ∧ finalState.work = 3 := by
  constructor
  · unfold prefixHybridRun
    rw [show List.finRange 2 = [0, 1] by decide]
    simp only [List.foldl_cons, List.foldl_nil, Except.bind]
    rw [first_step_exact]
    change prefixHybridStep constructionThenForward iv coins firstState 1 =
      .ok finalState
    exact second_step_exact
  · exact ⟨rfl, rfl⟩

/-- A construction query paired with a primitive coin is rejected before any
table mutation. -/
theorem construction_wrong_coin_shape :
    prefixHybridStep constructionThenForward iv
        (fun _ => .primitive (0, 0)) PrefixHybridState.empty 0 =
      .error .wrongCoinShape := by
  rfl

end SpongePrefixHybridExample

/-- info: 'Minidregg.Selvage.prefixHybridStep_work_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefixHybridStep_work_exact
/-- info: 'Minidregg.Selvage.SpongePrefixHybridExample.construction_first_forward_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongePrefixHybridExample.construction_first_forward_replays

end Minidregg.Selvage
