import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Pure pathwise lemma isolated from the incompatible Selvage cache.
`stopped` and `corrupt` are arbitrary history functions; no protocol is assumed. -/
namespace Astra.DarkLearningCore
variable {Ω V : Type} [NormedAddCommGroup V]

def count (stopped corrupt : List Ω → Bool) : List Ω → ℕ
  | [] => 0
  | _ :: h => if stopped h then count stopped corrupt h
    else if corrupt h then count stopped corrupt h + 1 else count stopped corrupt h

noncomputable def injected (stopped corrupt : List Ω → Bool) (delta honest : List Ω → V) : List Ω → ℝ
  | [] => 0
  | _ :: h => if stopped h then injected stopped corrupt delta honest h
    else injected stopped corrupt delta honest h + ‖delta h - honest h‖

theorem injected_le_count (stopped corrupt : List Ω → Bool) (delta honest : List Ω → V) (B : ℝ)
    (hactual : ∀ h, ‖delta h‖ ≤ B) (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, corrupt h = false → delta h = honest h) :
    ∀ h, injected stopped corrupt delta honest h ≤ (2 * B) * (count stopped corrupt h : ℝ) := by
  intro h
  induction h with
  | nil => simp [injected, count]
  | cons w h ih =>
    by_cases hs : stopped h = true
    · simpa [injected, count, hs] using ih
    · have hs' : stopped h = false := Bool.eq_false_iff.mpr hs
      by_cases hc : corrupt h = true
      · have hd : ‖delta h - honest h‖ ≤ 2 * B :=
          (norm_sub_le _ _).trans (by linarith [hactual h, hhonest h])
        simp only [injected, count, hs', Bool.false_eq_true, ↓reduceIte, hc,
          Nat.cast_add, Nat.cast_one]
        nlinarith
      · have hc' : corrupt h = false := Bool.eq_false_iff.mpr hc
        simpa [injected, count, hs', hc', hcoverage h hc'] using ih


theorem nonzero_injected_witness :
    injected (fun _ : List Unit => false) (fun _ => true)
      (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) [()] = 2 ∧
    count (fun _ : List Unit => false) (fun _ => true) [()] = 1 := by
  norm_num [injected, count]

/-- info: 'Astra.DarkLearningCore.injected_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms injected_le_count
/-- info: 'Astra.DarkLearningCore.nonzero_injected_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonzero_injected_witness
end Astra.DarkLearningCore
