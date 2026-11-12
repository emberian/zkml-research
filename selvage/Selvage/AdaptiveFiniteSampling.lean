/-
# Selvage.AdaptiveFiniteSampling — prefix-dependent sampling over finite alphabets

The sponge simulator's evolving capacity avoid set is not fixed before the
coin vector is sampled.  `Selvage.Sumcheck` already proves the required fibre
argument for field-valued challenges.  This module isolates the mathematical
content that does not use a field: for any nonempty finite alphabet, a bad set
at coordinate `i` may depend on all earlier coordinates, but not on the fresh
coordinate itself.  If every fibre has at most `d` values, the adaptive union
is bounded by `v * d / |C|`.

This is a real adaptive theorem.  The closing example's second bad set is the
singleton containing the first sampled value, so it is observably not a fixed
set.  Connecting this engine to `FreshIdealExecution` still requires proving
that the simulator's evolving `capsOf` is prefix-measurable and has the stated
cardinality; that protocol-specific bridge remains separate.
-/
import Selvage.Sumcheck

namespace Minidregg.Selvage

section FiniteAlphabet

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

omit [DecidableEq C] in
/-- A coordinate of a uniform finite-alphabet vector hits a prefix-measurable
bad set of size at most `d` with probability at most `d / |C|`. -/
theorem uniformProb_coord_mem_prefix_finite {v d : Nat} (i : Fin v)
    (bad : (Fin v → C) → Finset C)
    (hmeas : ∀ r r' : Fin v → C,
      (∀ j : Fin v, (j : Nat) < (i : Nat) → r j = r' j) → bad r = bad r')
    (hcard : ∀ r, (bad r).card ≤ d) :
    uniformProb (Fin v → C) (fun r => r i ∈ bad r)
      ≤ (d : Real) / Fintype.card C := by
  let c0 : C := Classical.choice (inferInstance : Nonempty C)
  have key : uniformProb (Fin v → C) (fun r => r i ∈ bad r)
      = uniformProb (({j : Fin v // j ≠ i} → C) × C)
          (fun x => x.2 ∈ bad ((splitCoord i).symm x)) := by
    rw [← uniformProb_equiv (splitCoord i)
      (fun x : ({j : Fin v // j ≠ i} → C) × C =>
        x.2 ∈ bad ((splitCoord i).symm x))]
    refine uniformProb_congr fun r => ?_
    rw [Equiv.symm_apply_apply]
    rfl
  rw [key]
  refine uniformProb_prod_le (by positivity) fun a => ?_
  show uniformProb C (fun b => b ∈ bad ((splitCoord i).symm (a, b)))
      ≤ (d : Real) / Fintype.card C
  have hconst : ∀ b : C,
      bad ((splitCoord i).symm (a, b)) =
        bad ((splitCoord i).symm (a, c0)) := by
    intro b
    refine hmeas _ _ fun j hji => ?_
    have hjne : j ≠ i := fun h => by
      rw [h] at hji
      exact Nat.lt_irrefl _ hji
    rw [splitCoord_symm_apply_of_ne _ hjne,
      splitCoord_symm_apply_of_ne _ hjne]
  calc
    uniformProb C (fun b => b ∈ bad ((splitCoord i).symm (a, b)))
        = uniformProb C (fun b => b ∈ bad ((splitCoord i).symm (a, c0))) :=
          uniformProb_congr fun b => by rw [hconst b]
    _ ≤ (d : Real) / Fintype.card C := by
      rw [uniformProb_mem_finset]
      gcongr
      exact_mod_cast hcard _

omit [DecidableEq C] in
/-- Fully adaptive finite-alphabet union bound.  Each round's bad set may be
chosen from the earlier sampled prefix. -/
theorem adaptiveFiniteUnionBound {v d : Nat}
    (bad : (Fin v → C) → Fin v → Finset C)
    (hmeas : ∀ (i : Fin v) (r r' : Fin v → C),
      (∀ j : Fin v, (j : Nat) < (i : Nat) → r j = r' j) →
        bad r i = bad r' i)
    (hcard : ∀ (r : Fin v → C) (i : Fin v), (bad r i).card ≤ d) :
    uniformProb (Fin v → C) (fun r => ∃ i : Fin v, r i ∈ bad r i)
      ≤ (v : Real) * ((d : Real) / Fintype.card C) := by
  calc
    uniformProb (Fin v → C) (fun r => ∃ i : Fin v, r i ∈ bad r i)
        ≤ ∑ i : Fin v,
            uniformProb (Fin v → C) (fun r => r i ∈ bad r i) :=
          uniformProb_exists_le _
    _ ≤ ∑ _i : Fin v, (d : Real) / Fintype.card C :=
      Finset.sum_le_sum fun i _ =>
        uniformProb_coord_mem_prefix_finite i (fun r => bad r i)
          (fun r r' hjr => hmeas i r r' hjr) (fun r => hcard r i)
    _ = (v : Real) * ((d : Real) / Fintype.card C) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end FiniteAlphabet

/-! ## A genuinely prefix-dependent witness -/

namespace AdaptiveFiniteSamplingExample

/-- Round zero avoids `0`; round one avoids the value actually sampled at
round zero. -/
def bad (r : Fin 2 → Fin 3) : Fin 2 → Finset (Fin 3)
  | i => if i = 0 then {0} else {r 0}

theorem bad_prefix_measurable (i : Fin 2) (r r' : Fin 2 → Fin 3)
    (hprefix : ∀ j : Fin 2, (j : Nat) < (i : Nat) → r j = r' j) :
    bad r i = bad r' i := by
  fin_cases i
  · simp [bad]
  · simp [bad, hprefix 0 (by decide)]

theorem bad_card (r : Fin 2 → Fin 3) (i : Fin 2) : (bad r i).card ≤ 1 := by
  fin_cases i <;> simp [bad]

/-- The generic theorem fires at `2/3` on the changing bad set. -/
theorem adaptive_bad_le :
    uniformProb (Fin 2 → Fin 3) (fun r => ∃ i : Fin 2, r i ∈ bad r i)
      ≤ (2 : Real) * ((1 : Real) / 3) := by
  simpa using adaptiveFiniteUnionBound bad bad_prefix_measurable bad_card

/-- Teeth: round one's bad set really changes with the first sample. -/
theorem bad_not_fixed :
    bad (fun _ => 0) 1 ≠ bad (fun _ => 1) 1 := by
  decide

end AdaptiveFiniteSamplingExample

/-- info: 'Minidregg.Selvage.adaptiveFiniteUnionBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adaptiveFiniteUnionBound
/-- info: 'Minidregg.Selvage.AdaptiveFiniteSamplingExample.adaptive_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdaptiveFiniteSamplingExample.adaptive_bad_le

end Minidregg.Selvage
