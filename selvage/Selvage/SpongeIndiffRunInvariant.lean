/-
# Selvage.SpongeIndiffRunInvariant — fold the sponge simulator invariant over a run

`Selvage.SpongeIndiff` proves that one forward or inverse simulator step preserves
rooted-path uniqueness when the step's fresh capacity misses the capacities
already mentioned by the simulator log.  This module performs the missing
structural fold: an explicit proof-relevant `FreshIdealExecution` threads that
condition through the actual adaptive `idealStep` states, and the final theorem
proves `UniquePaths` for the actual `idealRun`.

This closes only the deterministic run-invariant part of
`[SPONGE-indiff-game]`.  It does not manufacture the probabilistic adaptive
schedule bridge: pricing the probability that every evolving step is fresh,
and coupling the resulting ideal transcript to a random permutation until the
first bad step, remain separate obligations.
-/
import Selvage.SpongeIndiff

namespace Minidregg.Selvage

section RunInvariant

variable {Rate Cap : Type} [AddCommGroup Rate] [Fintype Rate] [Fintype Cap]
  [DecidableEq Rate] [DecidableEq Cap]

/-- The exact capacity-freshness premise needed by one actual ideal-game step.
Construction queries do not mutate the simulator log.  Forward primitive
queries must miss every capacity already mentioned by the log and the queried
capacity itself; inverse queries need only miss the former set. -/
def IdealFreshAt {q : Nat} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) (coins : Fin q → Rate × (Rate × Cap))
    (st : IdealState Rate Cap) (j : Fin q) : Prop :=
  match D.move st.ans with
  | .constr _ _ => True
  | .fwd s =>
      (coins j).2.2 ∉ capsOf st.sim iv ∧ (coins j).2.2 ≠ s.2
  | .inv _ => (coins j).2.2 ∉ capsOf st.sim iv

/-- The proof-relevant off-bad schedule for an exact list of adaptive ideal
steps.  Crucially, the premise for the tail is evaluated in the state produced
by the head step, so this is not a fixed non-adaptive avoid set in disguise. -/
noncomputable def FreshIdealExecution {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) :
    List (Fin q) → IdealState Rate Cap → Prop
  | [], _ => True
  | j :: js, st =>
      IdealFreshAt D iv coins st j ∧
        FreshIdealExecution D iv coins js (idealStep D iv coins st j)

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- The simulator component threaded by `simFwdRO` is exactly the component
threaded by the already-proved `simFwd` preservation theorem. -/
lemma simFwdRO_sim (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (os : Oracle (Rate × Cap) (Rate × Cap)) (s : Rate × Cap)
    (rc : Rate) (bc : Rate × Cap) :
    (simFwdRO iv ro os s rc bc).2.2 =
      (simFwd (fun m => (ro.respond m rc).1) iv os s bc).2 := by
  unfold simFwdRO simFwd
  cases completion? os iv s <;> rfl

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- One actual `idealStep` preserves rooted-path uniqueness under precisely
the branch-specific condition recorded by `IdealFreshAt`. -/
theorem idealStep_uniquePaths {q : Nat} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) (coins : Fin q → Rate × (Rate × Cap))
    (st : IdealState Rate Cap) (j : Fin q)
    (hUnique : UniquePaths st.sim iv)
    (hFresh : IdealFreshAt D iv coins st j) :
    UniquePaths (idealStep D iv coins st j).sim iv := by
  unfold IdealFreshAt at hFresh
  cases hmove : D.move st.ans with
  | constr x xs =>
      rw [hmove] at hFresh
      simpa [idealStep, hmove] using hUnique
  | fwd s =>
      rw [hmove] at hFresh
      rcases hFresh with ⟨hcap, hquery⟩
      have h := uniquePaths_simFwd (O := st.sim) hUnique
        (fun m => (st.ro.respond m (coins j).1).1) hcap hquery
      simpa [idealStep, hmove, simFwdRO_sim] using h
  | inv t =>
      rw [hmove] at hFresh
      have h := uniquePaths_simInv (O := st.sim) (t := t) hUnique hFresh
      simpa [idealStep, hmove] using h

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- The deterministic run induction: every proof-relevant fresh execution
preserves the unique rooted-path invariant through its final state. -/
theorem freshIdealExecution_uniquePaths {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap))
    (steps : List (Fin q)) (st : IdealState Rate Cap)
    (hUnique : UniquePaths st.sim iv)
    (hFresh : FreshIdealExecution D iv coins steps st) :
    UniquePaths (steps.foldl (idealStep D iv coins) st).sim iv := by
  induction steps generalizing st with
  | nil => simpa using hUnique
  | cons j js ih =>
      exact ih (idealStep D iv coins st j)
        (idealStep_uniquePaths D iv coins st j hUnique hFresh.1) hFresh.2

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- The run-level spine for the actual ideal game.  The only premise left is
the exact adaptive off-bad schedule; no fixed avoid set or marginal-uniform
shortcut is assumed. -/
theorem idealRun_uniquePaths_of_fresh {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap))
    (hFresh : FreshIdealExecution D iv coins (List.finRange q)
      ⟨Oracle.empty, Oracle.empty, []⟩) :
    UniquePaths (idealRun D iv coins).sim iv := by
  unfold idealRun
  exact freshIdealExecution_uniquePaths D iv coins (List.finRange q)
    ⟨Oracle.empty, Oracle.empty, []⟩ (uniquePaths_empty iv) hFresh

end RunInvariant

/-! ## Non-vacuous one-step witness -/

namespace SpongeRunInvariantExample

def iv : ZMod 2 × Fin 3 := (0, 0)

def forwardOne : Distinguisher (ZMod 2) (Fin 3) 1 where
  move _ := .fwd (1, 0)
  out _ := true

def coins : Fin 1 → ZMod 2 × (ZMod 2 × Fin 3) :=
  fun _ => (0, (0, 1))

/-- The adaptive freshness package is inhabited for a real primitive step,
not merely for the zero-query base case. -/
theorem forwardOne_fresh : FreshIdealExecution forwardOne iv coins (List.finRange 1)
    ⟨Oracle.empty, Oracle.empty, []⟩ := by
  rw [show List.finRange 1 = [0] by decide, FreshIdealExecution]
  constructor
  · change (1 : Fin 3) ∉ capsOf Oracle.empty iv ∧ (1 : Fin 3) ≠ 0
    decide
  · trivial

/-- Consequently the actual one-step ideal run has unique rooted paths. -/
theorem forwardOne_uniquePaths : UniquePaths (idealRun forwardOne iv coins).sim iv :=
  idealRun_uniquePaths_of_fresh forwardOne iv coins forwardOne_fresh

end SpongeRunInvariantExample

/-- info: 'Minidregg.Selvage.idealRun_uniquePaths_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealRun_uniquePaths_of_fresh
/-- info: 'Minidregg.Selvage.SpongeRunInvariantExample.forwardOne_uniquePaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SpongeRunInvariantExample.forwardOne_uniquePaths

end Minidregg.Selvage
