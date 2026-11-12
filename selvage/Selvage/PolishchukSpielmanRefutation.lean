/-
# Selvage.PolishchukSpielmanRefutation — the un-fixed `[PROXGAP-BW-ps]` floor is FALSE

`Selvage/ProximityGapUDTight.lean` carried, as the one named residual of the
BCIKS Berlekamp–Welch route to the full unique-decoding radius, a `Prop`
`PolishchukSpielman F` stated in the shape of [Spi95] Lemma 4.2.18 / BCIKS
2020/654 rev.1 Lemma 4.4: plain divisibility on every column `x ∈ S_X` and
every row `z ∈ S_Z`, the two sum conditions `a_X + b_X < |S_X|`,
`a_Z + b_Z < |S_Z|`, and the budget `b_X·|S_Z| + b_Z·|S_X| < |S_X|·|S_Z|`,
concluding `A ∣ B`. Every full-band head was proved MODULO that `Prop`.

That shape is the one Spielman's proof has a gap in, and the gap is not only
in the proof: the statement is false. A line on which `A` degenerates (its
leading coefficient in the other variable vanishes there) makes plain
divisibility free on that line, and two such lines buy enough slack to place
`B` on the curve `A = 0` at every remaining grid point without `A ∣ B`. The
corrected statement (BCIKS rev.3 Appendix D, the fix due to Ronald Cramer
after Cramer–Nardi's diagnosis; cf. [Bég19]) demands that the per-line
QUOTIENTS have degree at most `b − a` in the line variable. The degenerate
lines below are exactly where that demand fails (`counterexample_violates_cramer`).

## The counterexample

Over any field with two distinct nonzero elements `x₁ ≠ x₂` (so every field
with at least three elements), in Mini's orientation (`F[Z][X]`, outer `X`):

* `A = 1 + X·Z`                       — `deg_X A = 1`, `deg_Z A = 1`;
* `B = X − (x₁ + x₂) − x₁x₂·Z`         — `deg_X B = 1`, `deg_Z B = 1`;
* `S_X = {0, x₁, x₂}`, `S_Z = {0, −x₁⁻¹, −x₂⁻¹}`.

On the columns: `A(0, Z) = 1` divides everything; `B(x₁, Z) = −x₂·(1 + x₁Z)`;
`B(x₂, Z) = −x₁·(1 + x₂Z)`. On the rows: `A(X, 0) = 1`;
`B(X, −x₁⁻¹) = −x₁·(1 − x₁⁻¹X)`; symmetrically at `−x₂⁻¹`. The counts are
`1 + 1 < 3`, `1 + 1 < 3`, `1·3 + 1·3 < 3·3`. Yet `A ∤ B`: the outer leading
coefficient of `A` is `Z`, of `B` is `1`, and `Z` is not a unit of `F[Z]`.

At `F₅`, `x₁ = 1`, `x₂ = 2`: `A = 1 + XZ`, `B = X + 2 + 3Z`,
`S_X = {0, 1, 2}`, `S_Z = {0, 4, 2}` (`polishchukSpielman_unfixed_false_F5`) —
the field of the deleted conditional keystone `good_line_CA_fullBand`.

The un-fixed statement is stated inline below, verbatim from the deleted
definition; it is deliberately NOT re-introduced as a named `Prop` anything
could bind.
-/
import Selvage.ProximityGapUDTight
import Theory.AssertAxioms

namespace Minidregg.Selvage

open Polynomial

namespace PolishchukSpielmanRefutation

variable {F : Type*} [Field F]

/-- `A = Z·X + 1` in `F[Z][X]` (outer `X`, inner `Z`). -/
noncomputable def cexA : Polynomial (Polynomial F) :=
  C (Polynomial.X : Polynomial F) * Polynomial.X + C 1

/-- `B = X + (−(x₁ + x₂) − x₁x₂·Z)` in `F[Z][X]`. -/
noncomputable def cexB (x₁ x₂ : F) : Polynomial (Polynomial F) :=
  Polynomial.X + C (C (-(x₁ + x₂)) + C (-(x₁ * x₂)) * Polynomial.X)

theorem cexA_eval (x : F) :
    (cexA : Polynomial (Polynomial F)).eval (C x)
      = Polynomial.X * C x + C 1 := by
  simp [cexA]

theorem cexB_eval (x₁ x₂ x : F) :
    (cexB x₁ x₂).eval (C x)
      = C x + (C (-(x₁ + x₂)) + C (-(x₁ * x₂)) * Polynomial.X) := by
  simp [cexB]

theorem cexA_map (z : F) :
    (cexA : Polynomial (Polynomial F)).map (evalRingHom z)
      = C z * Polynomial.X + C 1 := by
  simp [cexA, Polynomial.map_add, Polynomial.map_mul]

theorem cexB_map (x₁ x₂ z : F) :
    (cexB x₁ x₂).map (evalRingHom z)
      = Polynomial.X + C (-(x₁ + x₂) + -(x₁ * x₂) * z) := by
  simp [cexB, Polynomial.map_add]

theorem cexA_natDegree : (cexA : Polynomial (Polynomial F)).natDegree ≤ 1 :=
  natDegree_linear_le

theorem cexB_natDegree (x₁ x₂ : F) : (cexB x₁ x₂).natDegree ≤ 1 :=
  (natDegree_X_add_C _).le

theorem cexA_zdeg : ZDegLE (cexA : Polynomial (Polynomial F)) 1 := by
  intro i
  rw [cexA, coeff_add, coeff_C_mul_X, coeff_C]
  split_ifs
  · omega
  · rw [add_zero]; exact_mod_cast degree_X_le
  · rw [zero_add]; exact le_trans degree_C_le (by exact_mod_cast Nat.zero_le 1)
  · simp

theorem cexB_zdeg (x₁ x₂ : F) : ZDegLE (cexB x₁ x₂) 1 := by
  intro i
  rw [cexB, coeff_add, coeff_X, coeff_C]
  have hc : (C (-(x₁ + x₂)) + C (-(x₁ * x₂)) * (Polynomial.X : Polynomial F)).degree
      ≤ ((1 : ℕ) : WithBot ℕ) := by
    refine le_trans (degree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans degree_C_le (by exact_mod_cast Nat.zero_le 1)
    · exact_mod_cast degree_C_mul_X_le _
  split_ifs
  · omega
  · rw [add_zero]; exact le_trans degree_one_le (by exact_mod_cast Nat.zero_le 1)
  · rw [zero_add]; exact hc
  · simp

/-- `A ∤ B`: the outer leading coefficients are `Z` and `1`, and `Z` is not a
unit of `F[Z]` (evaluate at `0`). -/
theorem cexA_not_dvd (x₁ x₂ : F) : ¬ (cexA : Polynomial (Polynomial F)) ∣ cexB x₁ x₂ := by
  rintro ⟨Q, hQ⟩
  have hlc := congrArg Polynomial.leadingCoeff hQ
  rw [leadingCoeff_mul, cexB, leadingCoeff_X_add_C, cexA,
    leadingCoeff_linear Polynomial.X_ne_zero] at hlc
  have h0 := congrArg (Polynomial.eval (0 : F)) hlc
  simp at h0

/-- **The un-fixed Polishchuk–Spielman statement is false over every field with
two distinct nonzero elements.** The statement is the deleted
`Minidregg.Selvage.PolishchukSpielman F`, verbatim. -/
theorem polishchukSpielman_unfixed_false {x₁ x₂ : F}
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (h₁₂ : x₁ ≠ x₂) :
    ¬ ∀ (A B : Polynomial (Polynomial F)) (SX SZ : Finset F) (aX aZ bX bZ : ℕ),
      A.natDegree ≤ aX → ZDegLE A aZ → B.natDegree ≤ bX → ZDegLE B bZ →
      (∀ x ∈ SX, A.eval (C x) ∣ B.eval (C x)) →
      (∀ z ∈ SZ, A.map (evalRingHom z) ∣ B.map (evalRingHom z)) →
      aX + bX < SX.card → aZ + bZ < SZ.card →
      bX * SZ.card + bZ * SX.card < SX.card * SZ.card →
      A ∣ B := by
  classical
  intro hPS
  have hSX : ({0, x₁, x₂} : Finset F).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, x₁, x₂, h₁.symm, h₂.symm, h₁₂, rfl⟩
  have hi₁ : -x₁⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero h₁)
  have hi₂ : -x₂⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero h₂)
  have hi₁₂ : -x₁⁻¹ ≠ -x₂⁻¹ := fun h => h₁₂ (inv_injective (neg_injective h))
  have hSZ : ({0, -x₁⁻¹, -x₂⁻¹} : Finset F).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, -x₁⁻¹, -x₂⁻¹, hi₁.symm, hi₂.symm, hi₁₂, rfl⟩
  refine cexA_not_dvd x₁ x₂ (hPS cexA (cexB x₁ x₂) {0, x₁, x₂} {0, -x₁⁻¹, -x₂⁻¹}
    1 1 1 1 cexA_natDegree cexA_zdeg (cexB_natDegree x₁ x₂) (cexB_zdeg x₁ x₂)
    ?_ ?_ (by rw [hSX]; omega) (by rw [hSZ]; omega) (by rw [hSX, hSZ]; omega))
  · -- the columns
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [cexA_eval, cexB_eval]
    rcases hx with rfl | rfl | rfl
    · simp
    · refine ⟨C (-x₂), ?_⟩
      simp only [map_neg, map_add, map_mul, map_one]
      ring
    · refine ⟨C (-x₁), ?_⟩
      simp only [map_neg, map_add, map_mul, map_one]
      ring
  · -- the rows
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [cexA_map, cexB_map]
    rcases hz with rfl | rfl | rfl
    · simp
    · have hzC : C (-x₁⁻¹) * C x₁ = (-1 : Polynomial F) := by
        rw [← C_mul, neg_mul, inv_mul_cancel₀ h₁, map_neg, C_1]
      refine ⟨C (-x₁), ?_⟩
      simp only [map_neg, map_add, map_mul, map_one] at hzC ⊢
      linear_combination (Polynomial.X - C x₂) * hzC
    · have hzC : C (-x₂⁻¹) * C x₂ = (-1 : Polynomial F) := by
        rw [← C_mul, neg_mul, inv_mul_cancel₀ h₂, map_neg, C_1]
      refine ⟨C (-x₂), ?_⟩
      simp only [map_neg, map_add, map_mul, map_one] at hzC ⊢
      linear_combination (Polynomial.X - C x₁) * hzC

/-- **Where the fix bites.** On the degenerate column `x = 0` (`A(0, Z) = 1`),
the only quotient of `B(0, Z)` by `A(0, Z)` is `B(0, Z)` itself, of `Z`-degree
`1`, while the Cramer bound allows `b_Z − a_Z = 0`. The corrected statement's
quotient-degree hypothesis refuses this instance; the plain-divisibility one
admits it. -/
theorem counterexample_violates_cramer {x₁ x₂ : F} (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) :
    ¬ ∃ q : Polynomial F, (cexB x₁ x₂).eval (C 0)
        = (cexA : Polynomial (Polynomial F)).eval (C 0) * q ∧ q.natDegree ≤ 1 - 1 := by
  rintro ⟨q, hq, hdeg⟩
  rw [cexA_eval, cexB_eval] at hq
  simp only [map_zero, mul_zero, zero_add, map_one, one_mul] at hq
  have hc : (q.coeff 1) = -(x₁ * x₂) := by
    rw [← hq, coeff_add, coeff_C, coeff_C_mul_X]
    simp
  have hq1 : q.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hq1] at hc
  exact mul_ne_zero h₁ h₂ (neg_eq_zero.mp hc.symm)

/-- **The counterexample at `F₅`** (`x₁ = 1`, `x₂ = 2`: `A = 1 + XZ`,
`B = X + 2 + 3Z`, `S_X = {0, 1, 2}`, `S_Z = {0, 4, 2}`) — the field the
deleted conditional keystone `good_line_CA_fullBand` was stated over. -/
theorem polishchukSpielman_unfixed_false_F5 :
    ¬ ∀ (A B : Polynomial (Polynomial (ZMod 5))) (SX SZ : Finset (ZMod 5))
        (aX aZ bX bZ : ℕ),
      A.natDegree ≤ aX → ZDegLE A aZ → B.natDegree ≤ bX → ZDegLE B bZ →
      (∀ x ∈ SX, A.eval (C x) ∣ B.eval (C x)) →
      (∀ z ∈ SZ, A.map (evalRingHom z) ∣ B.map (evalRingHom z)) →
      aX + bX < SX.card → aZ + bZ < SZ.card →
      bX * SZ.card + bZ * SX.card < SX.card * SZ.card →
      A ∣ B :=
  polishchukSpielman_unfixed_false (x₁ := (1 : ZMod 5)) (x₂ := 2)
    (by decide) (by decide) (by decide)

#assert_axioms polishchukSpielman_unfixed_false
#assert_axioms counterexample_violates_cramer
#assert_axioms polishchukSpielman_unfixed_false_F5

end PolishchukSpielmanRefutation

end Minidregg.Selvage
