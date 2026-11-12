/-
# Selvage.SpongeIndiffCapacityBudget — exact per-step adaptive avoid sets

The run invariant in `Selvage.SpongeIndiffRunInvariant` records the precise
fresh-capacity condition needed by each adaptive ideal step.  This module
turns that condition into a finite avoid set and proves the cardinality budget
needed by `Selvage.AdaptiveFiniteSampling`.

For a simulator log of length `n`, `capsOf` mentions at most `2n + 1`
capacities (the IV plus each entry's input and output).  A forward step adds
its queried capacity to the avoid set, so every branch has at most `2n + 2`
bad capacity values.  One ideal step extends the simulator log by at most one
entry.  These are deterministic protocol facts; prefix measurability and the
probability transport over a whole run remain the next join.
-/
import Selvage.SpongeIndiffRunInvariant
import Selvage.AdaptiveFiniteSampling

namespace Minidregg.Selvage

section CapacityBudget

variable {Rate Cap : Type} [AddCommGroup Rate] [Fintype Rate] [Fintype Cap]
  [DecidableEq Rate] [DecidableEq Cap]

/-- The exact finite set forbidden to the capacity component of the current
ideal step.  Construction queries do not touch the simulator. -/
def idealCapacityAvoid {q : Nat} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) (st : IdealState Rate Cap) : Finset Cap :=
  match D.move st.ans with
  | .constr _ _ => ∅
  | .fwd s => (capsOf st.sim iv).toFinset ∪ {s.2}
  | .inv _ => (capsOf st.sim iv).toFinset

omit [AddCommGroup Rate] [Fintype Rate] [Fintype Cap] [DecidableEq Rate] in
/-- Avoid-set nonmembership is exactly sufficient for the branch-specific
`IdealFreshAt` premise used by the run invariant. -/
theorem idealFreshAt_of_not_mem_avoid {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap))
    (st : IdealState Rate Cap) (j : Fin q)
    (h : (coins j).2.2 ∉ idealCapacityAvoid D iv st) :
    IdealFreshAt D iv coins st j := by
  unfold idealCapacityAvoid at h
  unfold IdealFreshAt
  cases hmove : D.move st.ans with
  | constr x xs =>
      rw [hmove] at h
      trivial
  | fwd s =>
      rw [hmove] at h
      constructor
      · intro hc
        exact h (Finset.mem_union_left _ (by simpa using hc))
      · intro hs
        exact h (Finset.mem_union_right _ (by simpa using hs))
  | inv t =>
      rw [hmove] at h
      simpa using h

omit [AddCommGroup Rate] [Fintype Rate] [Fintype Cap] [DecidableEq Rate]
    [DecidableEq Cap] in
/-- A lazy handler response adds at most one log entry. -/
lemma Oracle.respond_log_length_le {Q C : Type} (O : Oracle Q C)
    (query : Q) (coin : C) :
    (O.respond query coin).2.log.length ≤ O.log.length + 1 := by
  cases h : O.lookup query with
  | some value =>
      simp [Oracle.respond_hit h]
  | none =>
      simp [Oracle.respond_fresh_log h]

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- A forward simulator/RO step adds at most one shared-log entry. -/
lemma simFwdRO_log_length_le (iv : Rate × Cap)
    (ro : Oracle (List Rate) Rate)
    (os : Oracle (Rate × Cap) (Rate × Cap))
    (s : Rate × Cap) (rc : Rate) (bc : Rate × Cap) :
    (simFwdRO iv ro os s rc bc).2.2.log.length ≤ os.log.length + 1 := by
  unfold simFwdRO
  cases completion? os iv s <;> exact Oracle.respond_log_length_le _ _ _

omit [AddCommGroup Rate] [Fintype Rate] [Fintype Cap] [DecidableEq Rate]
    [DecidableEq Cap] in
/-- An inverse simulator step adds at most one shared-log entry. -/
lemma simInv_log_length_le (os : Oracle (Rate × Cap) (Rate × Cap))
    (t coin : Rate × Cap) :
    (simInv os t coin).2.log.length ≤ os.log.length + 1 := by
  unfold simInv
  cases h : os.lookupInv t with
  | some entry => simp
  | none => simpa [h] using Oracle.respond_log_length_le os coin t

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- Every actual adaptive ideal step extends the simulator log by at most one
entry, independently of which query branch the distinguisher selects. -/
theorem idealStep_sim_log_length_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap))
    (st : IdealState Rate Cap) (j : Fin q) :
    (idealStep D iv coins st j).sim.log.length ≤ st.sim.log.length + 1 := by
  cases hmove : D.move st.ans with
  | constr x xs => simp [idealStep, hmove]
  | fwd s => simpa [idealStep, hmove] using
      simFwdRO_log_length_le iv st.ro st.sim s (coins j).1 (coins j).2
  | inv t => simpa [idealStep, hmove] using
      simInv_log_length_le st.sim t (coins j).2

omit [AddCommGroup Rate] [Fintype Rate] [Fintype Cap] [DecidableEq Rate]
    [DecidableEq Cap] in
/-- `capsOf` has one IV coordinate and two coordinates per log entry. -/
lemma capsOf_length (os : Oracle (Rate × Cap) (Rate × Cap))
    (iv : Rate × Cap) :
    (capsOf os iv).length = 2 * os.log.length + 1 := by
  simp [capsOf]
  omega

omit [AddCommGroup Rate] [Fintype Rate] [Fintype Cap] [DecidableEq Rate] in
/-- Deduplication can only shrink the capacity footprint. -/
lemma capsOf_toFinset_card_le (os : Oracle (Rate × Cap) (Rate × Cap))
    (iv : Rate × Cap) :
    (capsOf os iv).toFinset.card ≤ 2 * os.log.length + 1 := by
  calc
    (capsOf os iv).toFinset.card ≤ (capsOf os iv).length :=
      List.toFinset_card_le _
    _ = 2 * os.log.length + 1 := capsOf_length os iv

omit [AddCommGroup Rate] [Fintype Rate] [Fintype Cap] [DecidableEq Rate] in
/-- The branch-specific avoid set has size at most `2n + 2` when the current
simulator log has `n` entries. -/
theorem idealCapacityAvoid_card_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st : IdealState Rate Cap) :
    (idealCapacityAvoid D iv st).card ≤ 2 * st.sim.log.length + 2 := by
  unfold idealCapacityAvoid
  cases D.move st.ans with
  | constr x xs => simp
  | fwd s =>
      calc
        ((capsOf st.sim iv).toFinset ∪ {s.2}).card
            ≤ (capsOf st.sim iv).toFinset.card + ({s.2} : Finset Cap).card :=
              Finset.card_union_le _ _
        _ ≤ (2 * st.sim.log.length + 1) + 1 := by
          exact Nat.add_le_add (capsOf_toFinset_card_le st.sim iv) (by simp)
        _ = 2 * st.sim.log.length + 2 := by omega
  | inv t =>
      exact (capsOf_toFinset_card_le st.sim iv).trans (by omega)

end CapacityBudget

/-! ## The bound is attained at the empty-log forward branch -/

namespace SpongeCapacityBudgetExample

def iv : ZMod 2 × Fin 3 := (0, 0)

def forward : Distinguisher (ZMod 2) (Fin 3) 1 where
  move _ := .fwd (1, 1)
  out _ := true

theorem initial_avoid_exact :
    idealCapacityAvoid forward iv ⟨Oracle.empty, Oracle.empty, []⟩ = {0, 1} := by
  decide

theorem initial_avoid_card :
    (idealCapacityAvoid forward iv ⟨Oracle.empty, Oracle.empty, []⟩).card = 2 := by
  rw [initial_avoid_exact]
  decide

end SpongeCapacityBudgetExample

/-- info: 'Minidregg.Selvage.idealStep_sim_log_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealStep_sim_log_length_le
/-- info: 'Minidregg.Selvage.idealCapacityAvoid_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealCapacityAvoid_card_le

end Minidregg.Selvage
