/-
Degree-M curve full unique-decoding target. The probability source is BCIKS20
2020/654, Theorem 6.1 and §6.1. This contract reuses Selvage's RS, combination,
and agreement definitions; it is entered before the algebraic proof.
-/
import Selvage.FullUDStatement

namespace Minidregg.Selvage
open scoped BigOperators
variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

def curveWord {M : ℕ} (u : Fin (M+1) → ι → F) (z : F) : ι → F :=
  comb (fun j => z ^ j.val) u

def CurveFullUDCardCore (M : ℕ) (dom : ι ↪ F) (d e : ℕ) : Prop :=
  ∀ (u : Fin (M+1) → ι → F) (A : Finset F),
    (∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (curveWord u z) w ≤ e) →
    M * Fintype.card ι < A.card →
    ∃ S : Finset ι, Fintype.card ι - e ≤ S.card ∧
      ∀ j, ∃ w ∈ reedSolomonCode dom d, AgreesOn S (u j) w

def CurveFullUDPremise (M : ℕ) (dom : ι ↪ F) (d e : ℕ)
    (u : Fin (M+1) → ι → F) (A : Finset F) : Prop :=
  1 ≤ M ∧ 1 ≤ d ∧ 2*e+d ≤ Fintype.card ι ∧
    M * Fintype.card ι < A.card ∧
    ∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (curveWord u z) w ≤ e

namespace CurveFullUDWitness
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def dom : Fin 5 ↪ ZMod 101 where
  toFun i := i.val
  inj' := by
    intro a b hab
    apply Fin.ext
    have ha : a.val < 101 := lt_trans a.isLt (by decide)
    have hb : b.val < 101 := lt_trans b.isLt (by decide)
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem zero_premise_inhabited (M : ℕ) (hM : 1 ≤ M) (hM8 : M ≤ 8) :
    CurveFullUDPremise M dom 2 1 (fun _ _ => 0) Finset.univ := by
  refine ⟨hM, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
    omega
  · intro z hz
    refine ⟨0, (reedSolomonCode dom 2).zero_mem, ?_⟩
    have hz0 : curveWord (M := M) (fun _ _ => (0 : ZMod 101)) z = (0 : Fin 5 → ZMod 101) := by
      ext i
      simp [curveWord, Minidregg.Selvage.comb]
    rw [hz0]
    simp

theorem zero_conclusion_inhabited (M : ℕ) :
    ∃ S : Finset (Fin 5), 5-1 ≤ S.card ∧
      ∀ _j : Fin (M+1), ∃ w ∈ reedSolomonCode dom 2,
        AgreesOn S (fun _ => (0 : ZMod 101)) w := by
  exact ⟨Finset.univ, by simp, fun _ => ⟨0,
    (reedSolomonCode dom 2).zero_mem, fun _ _ => rfl⟩⟩

/-- Raising this witness radius from one error to two violates UD admissibility. -/
theorem impossible_radius_teeth (M : ℕ) (u : Fin (M+1) → Fin 5 → ZMod 101)
    (A : Finset (ZMod 101)) : ¬ CurveFullUDPremise M dom 2 2 u A := by
  intro h
  have hrad := h.2.2.1
  norm_num at hrad

end CurveFullUDWitness
end Minidregg.Selvage

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.zero_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.zero_premise_inhabited

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.zero_conclusion_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.zero_conclusion_inhabited

/-- info: 'Minidregg.Selvage.CurveFullUDWitness.impossible_radius_teeth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CurveFullUDWitness.impossible_radius_teeth

