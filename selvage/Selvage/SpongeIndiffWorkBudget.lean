/-
# Selvage.SpongeIndiffWorkBudget — count construction primitive calls honestly

`Distinguisher q` counts external interface queries.  A construction query
`.constr x xs`, however, evaluates one primitive call for every block in
`x :: xs`.  Thus external query count is not in general the primitive-query
budget used by the sponge capacity and permutation/function switching bounds.

This module adds the missing first-order work accounting.  It proves an exact
counterexample to treating `q` as primitive work, proves that the old count is
sound on the explicit single-block construction fragment, and states the
honest work-indexed indifferentiability target.  It does not prove the game
hop.  The later prefix-programming/work-stream modules now provide the
construction-first runner and fixed work coin space; the adaptive off-bad
eager/deferred coupling and permutation/function switch remain.
-/
import Selvage.SpongeIndiffProgrammedAgreement

namespace Minidregg.Selvage

namespace SpQuery

/-- Number of primitive evaluations performed by one public interface query.
Primitive forward/inverse queries cost one; a construction costs one per
absorbed rate block. -/
def primitiveCalls : SpQuery Rate Cap → Nat
  | .constr _ xs => xs.length + 1
  | .fwd _ => 1
  | .inv _ => 1

@[simp] theorem primitiveCalls_constr (x : Rate) (xs : List Rate) :
    primitiveCalls (SpQuery.constr (Cap := Cap) x xs) = xs.length + 1 := rfl

@[simp] theorem primitiveCalls_fwd (s : Rate × Cap) :
    primitiveCalls (SpQuery.fwd s) = 1 := rfl

@[simp] theorem primitiveCalls_inv (t : Rate × Cap) :
    primitiveCalls (SpQuery.inv t) = 1 := rfl

theorem primitiveCalls_pos (query : SpQuery Rate Cap) :
    0 < query.primitiveCalls := by
  cases query <;> simp [primitiveCalls]

end SpQuery

section Work

variable {Rate Cap : Type}

/-- Work charged to a hypothetical complete answer trace.  At round `j`, the
distinguisher sees exactly the first `j` answers.  Quantifying over all answer
traces below gives an input-independent worst-case primitive budget. -/
def Distinguisher.primitiveWorkOn {q : Nat}
    (D : Distinguisher Rate Cap q) (answers : Fin q → SpAnswer Rate Cap) : Nat :=
  ((List.finRange q).map fun j =>
    (D.move ((List.ofFn answers).take j)).primitiveCalls).sum

/-- `work` bounds every adaptive answer trace's total primitive evaluations.
This is the budget which belongs in capacity and permutation/function terms. -/
def PrimitiveWorkBound {q : Nat} (D : Distinguisher Rate Cap q)
    (work : Nat) : Prop :=
  ∀ answers, D.primitiveWorkOn answers ≤ work

/-- The fragment on which the old external query count is also an exact
primitive-work bound: every construction query is a singleton rate block. -/
def SingleBlockConstruction {q : Nat} (D : Distinguisher Rate Cap q) : Prop :=
  ∀ answers x xs, D.move answers = .constr x xs → xs = []

theorem primitiveCalls_eq_one_of_singleBlock {q : Nat}
    {D : Distinguisher Rate Cap q} (hsingle : SingleBlockConstruction D)
    (answers : List (SpAnswer Rate Cap)) :
    (D.move answers).primitiveCalls = 1 := by
  cases hmove : D.move answers with
  | constr x xs =>
      rw [hsingle answers x xs hmove]
      rfl
  | fwd s => rfl
  | inv t => rfl

/-- On the explicitly restricted fragment, every `q`-round trace performs
exactly `q` primitive evaluations. -/
theorem primitiveWorkOn_eq_queries_of_singleBlock {q : Nat}
    {D : Distinguisher Rate Cap q} (hsingle : SingleBlockConstruction D)
    (answers : Fin q → SpAnswer Rate Cap) :
    D.primitiveWorkOn answers = q := by
  unfold Distinguisher.primitiveWorkOn
  simp_rw [primitiveCalls_eq_one_of_singleBlock hsingle]
  simp

theorem primitiveWorkBound_queries_of_singleBlock {q : Nat}
    {D : Distinguisher Rate Cap q} (hsingle : SingleBlockConstruction D) :
    PrimitiveWorkBound D q := by
  intro answers
  rw [primitiveWorkOn_eq_queries_of_singleBlock hsingle]

end Work

/-! ## The undercount is executable -/

namespace SpongeWorkBudgetExample

/-- One external construction query absorbing `n + 1` primitive blocks. -/
def longConstruction (n : Nat) : Distinguisher (ZMod 2) (Fin 3) 1 where
  move _ := .constr 0 (List.replicate n 0)
  out _ := true

def oneAnswer : Fin 1 → SpAnswer (ZMod 2) (Fin 3) :=
  fun _ => .rate 0

/-- Its exact primitive work is `n + 1`, although its external query count is
one. -/
theorem longConstruction_work (n : Nat) :
    (longConstruction n).primitiveWorkOn oneAnswer = n + 1 := by
  simp [Distinguisher.primitiveWorkOn, longConstruction, SpQuery.primitiveCalls]

/-- **Counterexample to the old budget interpretation.**  For every positive
`n`, a one-query distinguisher need not have primitive work at most one. -/
theorem external_query_count_does_not_bound_primitive_work (n : Nat)
    (hn : 0 < n) : ¬ PrimitiveWorkBound (longConstruction n) 1 := by
  intro hbound
  have h := hbound oneAnswer
  rw [longConstruction_work] at h
  omega

end SpongeWorkBudgetExample

section CorrectedTarget

variable (Rate Cap : Type) [AddCommGroup Rate]
  [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]

/-- Work-indexed sponge indifferentiability.  External rounds still define the
interactive transcript; `work` separately bounds the primitive evaluations
hidden inside construction queries and exposed by primitive queries. -/
def SpongeIndifferentiableByWork (iv : Rate × Cap) (ε : Nat → Real) : Prop :=
  ∀ (q work : Nat) (D : Distinguisher Rate Cap q),
    PrimitiveWorkBound D work →
      |realProb D iv - idealProb D iv| ≤ ε work

/-- The honest replacement target: both capacity and full-block switching
terms are indexed by total primitive work, not merely public interface rounds.
This is stated, not asserted as proved. -/
def SpongeIndiffWorkGame (iv : Rate × Cap) : Prop :=
  SpongeIndifferentiableByWork Rate Cap iv fun work =>
    2 * (work : Real) ^ 2 / (Fintype.card Cap : Real)
      + (work : Real) ^ 2 / (Fintype.card (Rate × Cap) : Real)

end CorrectedTarget

/-- info: 'Minidregg.Selvage.primitiveWorkOn_eq_queries_of_singleBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms primitiveWorkOn_eq_queries_of_singleBlock
/-- info: 'Minidregg.Selvage.SpongeWorkBudgetExample.external_query_count_does_not_bound_primitive_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeWorkBudgetExample.external_query_count_does_not_bound_primitive_work

end Minidregg.Selvage
