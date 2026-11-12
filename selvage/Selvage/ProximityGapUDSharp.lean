/-
# Selvage.ProximityGapUDSharp — the exact finite-field error threshold in the
# proved one-third-UD Reed--Solomon proximity gap.

`Selvage.ProximityGapUD` proves the affine PG(2) proximity-generator theorem on

  `0 < delta < (1 - d/n) / 3`

with the convenient error bound `n / |F|`.  Its counting core is stronger:
`correlatedAgreement_of_close_card` only needs `floor(delta*n) + 2` close
challenges.  This file exposes that exact integer threshold.  Consequently
the error is

  `(floor(delta*n) + 1) / |F|`,

which can be much smaller than `n / |F|` and is the strongest conclusion of
the already-proved counting argument.

The strict inequality in `IsProximityGenerator` matters.  Over the finite-rate
code `RS[F_5, {0,1,2,3}, 2]`, at `delta = 1/8`, the spike line from
`ProximityGapUDExample` has exactly one close challenge, probability `1/5`,
and no correlated agreement.  Thus the new error threshold is attained, not
merely an artifact of rounding.

This module does not claim WHIR Theorem 4.8 or the BCIKS full-UD/Johnson
theorem.  The remaining proof boundary is statement-first:

1. full unique decoding requires replacing the elementary transfer premise
   `d < (1-3*delta)n` by `d < (1-2*delta)n`;
2. that replacement needs a generic Berlekamp--Welch interpolant over `F(Z)`
   plus specialization away from the roots of a bounded-degree minor;
3. the Johnson regime additionally needs the corresponding list-size/
   correlated-agreement algebra and is not inferred from this finite count.
-/
import Selvage.ProximityGapUD

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The exact error mass certified by the one-third-UD counting proof: one
less than the number of close challenges that forces correlated agreement,
divided by the number of uniform affine challenges. -/
noncomputable def rsUdSharpError (ι F : Type*) [Fintype ι] [Fintype F]
    (δ : ℝ) : ℝ :=
  (Nat.floor (δ * (Fintype.card ι : ℝ)) + 1 : ℝ) /
    (Fintype.card F : ℝ)

/-- The one-third-UD proximity gap with its exact integer error threshold.
If more than `floor(delta*n)+1` affine challenges are close, the landed
counting core sees at least `floor(delta*n)+2` and forces correlated
agreement. -/
theorem rs_proximityGap_UD_sharp [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) {d : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ3 : (d : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ))
    (f : Fin 2 → ι → F) :
    (affineGenerator F).pr
        (fun r => close δ (reedSolomonCode dom d) (comb r f))
      ≤ rsUdSharpError ι F δ
    ∨ CorrelatedAgreement (reedSolomonCode dom d) δ f := by
  classical
  set A : Finset F := Finset.univ.filter fun γ : F =>
    close δ (reedSolomonCode dom d) (f 0 + γ • f 1) with hA
  have hpr :
      (affineGenerator F).pr
          (fun r => close δ (reedSolomonCode dom d) (comb r f)) =
        (A.card : ℝ) / (Fintype.card F : ℝ) := by
    unfold ProximityGenerator.pr
    have hcomb : ∀ γ : F,
        comb ((affineGenerator F).gen γ) f = f 0 + γ • f 1 :=
      fun γ => funext fun x => by rw [comb_affineGenerator]; rfl
    have hfilter :
        (Finset.univ.filter fun γ : (affineGenerator F).Seed =>
          close δ (reedSolomonCode dom d)
            (comb ((affineGenerator F).gen γ) f)) = A := by
      rw [hA]
      refine Finset.filter_congr fun γ _ => ?_
      rw [hcomb γ]
    rw [hfilter]
    calc
      ∑ ω ∈ A, (affineGenerator F).weight ω
          = ∑ _ω ∈ A, ((Fintype.card F : ℝ))⁻¹ :=
            Finset.sum_congr rfl fun _ _ => rfl
      _ = (A.card : ℝ) * ((Fintype.card F : ℝ))⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (A.card : ℝ) / (Fintype.card F : ℝ) :=
            (div_eq_mul_inv _ _).symm
  by_cases hsmall : (affineGenerator F).pr
      (fun r => close δ (reedSolomonCode dom d) (comb r f))
        ≤ rsUdSharpError ι F δ
  · exact Or.inl hsmall
  right
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcardR :
      (Nat.floor (δ * (Fintype.card ι : ℝ)) + 1 : ℝ) < (A.card : ℝ) := by
    have hnot : ¬(A.card : ℝ) / (Fintype.card F : ℝ) ≤
        (Nat.floor (δ * (Fintype.card ι : ℝ)) + 1 : ℝ) /
          (Fintype.card F : ℝ) := by
      simpa [hpr, rsUdSharpError] using hsmall
    exact (div_lt_div_iff_of_pos_right hF).mp (not_le.mp hnot)
  have hcard : Nat.floor (δ * (Fintype.card ι : ℝ)) + 2 ≤ A.card := by
    exact_mod_cast hcardR
  exact correlatedAgreement_of_close_card dom hδ0 hδ3
    (fun γ hγ => by
      rw [hA] at hγ
      exact (Finset.mem_filter.mp hγ).2) hcard

/-- The affine generator is a proximity generator for every finite-rate RS
code throughout the proved one-third-UD interval, now with the exact
radius-dependent error `(floor(delta*n)+1)/|F|`. -/
theorem reedSolomonCode_isProximityGenerator_UD_sharp [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) (d : ℕ) :
    IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      ((2 + (d : ℝ) / (Fintype.card ι : ℝ)) / 3)
      (rsUdSharpError ι F) := by
  intro f δ hδ0 hδB hpr
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hδ3 : (d : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ) := by
    have hρ : (d : ℝ) / (Fintype.card ι : ℝ) < 1 - 3 * δ := by
      linarith
    calc
      (d : ℝ) = (d : ℝ) / (Fintype.card ι : ℝ) *
          (Fintype.card ι : ℝ) := by field_simp
      _ < (1 - 3 * δ) * (Fintype.card ι : ℝ) :=
        mul_lt_mul_of_pos_right hρ hn
  rcases rs_proximityGap_UD_sharp dom hδ0 hδ3 f with hsmall | hCA
  · exact absurd hpr (not_lt.mpr hsmall)
  · exact hCA

namespace ProximityGapUDSharpExample

open RSExample ProximityGapUDExample

/-- At the rate-one-half F5 code and radius `1/8`, the sharp error is `1/5`:
`floor((1/8)*4)+1 = 1`. -/
theorem sharpError_eq_one_fifth :
    rsUdSharpError (Fin 4) (ZMod 5) (1 / 8 : ℝ) = 1 / 5 := by
  norm_num [rsUdSharpError, Fintype.card_fin, ZMod.card]

/-- The finite-rate theorem has a genuinely nonempty decoding interval. -/
theorem radius_in_sharp_interval :
    (0 : ℝ) < 1 / 8 ∧
      (1 / 8 : ℝ) <
        1 - (2 + (2 : ℝ) / (Fintype.card (Fin 4) : ℝ)) / 3 := by
  norm_num [Fintype.card_fin]

/-- The rate-one-half F5 instance of the sharp proximity generator. -/
theorem sharpPG_F5 :
    IsProximityGenerator (affineGenerator (ZMod 5))
      (reedSolomonCode dom₅ 2)
      ((2 + (2 : ℝ) / (Fintype.card (Fin 4) : ℝ)) / 3)
      (rsUdSharpError (Fin 4) (ZMod 5)) :=
  reedSolomonCode_isProximityGenerator_UD_sharp dom₅ 2

/-- The sharp theorem itself fires: the all-codeword line has probability
one, strictly above the new `1/5` error threshold. -/
theorem good_line_CA_sharp :
    CorrelatedAgreement (reedSolomonCode dom₅ 2) (1 / 8 : ℝ)
      ![xWord, oneWord] := by
  refine sharpPG_F5 ![xWord, oneWord] (1 / 8 : ℝ)
    radius_in_sharp_interval.1 radius_in_sharp_interval.2 ?_
  rw [line_pr_one, sharpError_eq_one_fifth]
  norm_num

/-- The spike line has probability exactly `1/5`, since its close-challenge
set is the landed singleton `{1}`. -/
theorem bad_line_pr_eq_one_fifth :
    (affineGenerator (ZMod 5)).pr (fun r =>
      close (1 / 8 : ℝ) (reedSolomonCode dom₅ 2)
        (comb r ![badWord, negBadWord])) = 1 / 5 := by
  classical
  have hfilter :
      (Finset.univ.filter fun γ : (affineGenerator (ZMod 5)).Seed =>
        close (1 / 8 : ℝ) (reedSolomonCode dom₅ 2)
          (comb ((affineGenerator (ZMod 5)).gen γ)
            ![badWord, negBadWord])) = badSet := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hcomb : ∀ γ : ZMod 5,
        comb ((affineGenerator (ZMod 5)).gen γ) ![badWord, negBadWord] =
          badWord + γ • negBadWord := by
      intro γ
      funext x
      rw [comb_affineGenerator]
      rfl
    rw [hcomb γ]
    exact mem_badSet.symm
  unfold ProximityGenerator.pr
  rw [hfilter, badSet_eq]
  calc
    ∑ ω ∈ ({1} : Finset (ZMod 5)),
          (affineGenerator (ZMod 5)).weight ω
        = ∑ _ω ∈ ({1} : Finset (ZMod 5)),
            ((Fintype.card (ZMod 5) : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun _ _ => rfl
    _ = ((Fintype.card (ZMod 5) : ℝ))⁻¹ := by
          rw [Finset.sum_const, Finset.card_singleton, nsmul_eq_mul]
          norm_num
    _ = 1 / 5 := by norm_num [ZMod.card]

/-- The sharp threshold is attained by a tuple with no correlated agreement.
This is the finite negative tooth showing why `IsProximityGenerator` uses the
strict premise `err delta < Pr[close]`: equality cannot force its conclusion. -/
theorem bad_line_attains_sharp_threshold :
    (affineGenerator (ZMod 5)).pr (fun r =>
      close (1 / 8 : ℝ) (reedSolomonCode dom₅ 2)
        (comb r ![badWord, negBadWord])) =
        rsUdSharpError (Fin 4) (ZMod 5) (1 / 8 : ℝ)
    ∧ ¬ CorrelatedAgreement (reedSolomonCode dom₅ 2) (1 / 8 : ℝ)
      ![badWord, negBadWord] := by
  rw [bad_line_pr_eq_one_fifth, sharpError_eq_one_fifth]
  exact ⟨rfl, bad_pair_no_CA⟩

end ProximityGapUDSharpExample

/-- info: 'Minidregg.Selvage.rs_proximityGap_UD_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rs_proximityGap_UD_sharp

/-- info: 'Minidregg.Selvage.reedSolomonCode_isProximityGenerator_UD_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reedSolomonCode_isProximityGenerator_UD_sharp

/-- info: 'Minidregg.Selvage.ProximityGapUDSharpExample.bad_line_attains_sharp_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGapUDSharpExample.bad_line_attains_sharp_threshold

end Minidregg.Selvage
