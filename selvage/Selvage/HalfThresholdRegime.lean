/-
# Selvage.HalfThresholdRegime — a proved post-Johnson route with one threshold halving

The 2024 WHIR roadmap treated same-threshold mutual correlated agreement near
capacity as a conjectural route.  The literature changed materially in 2025--26:

* capacity-level plain Reed--Solomon proximity/MCA conjectures were refuted;
* MCA up to Johnson was proved (Bordage--Chiesa--Guan--Manzur, ePrint
  2025/2051; Haboeck, ePrint 2025/2110); and
* Chai--Fan (ePrint 2026/858) gave an unconditional route *above* Johnson by
  halving the distance threshold once, then returning to the classical
  unique-decoding proximity gap in later rounds.

This file formalizes the algebraic heart of the third route directly in Selvage's
vocabulary.  For every linear code, if the pair `(f0,f1)` has no correlated
agreement at radius `delta`, then at most one scalar `gamma` makes
`f0 + gamma*f1` `delta/2`-close to the code.  Under the uniform affine
generator the bad mass is therefore at most `1/|F|`.

This theorem is characteristic-agnostic and therefore applies to both the
multiplicative fold and the additive GF(2)-tower fold once their respective
two-point decomposition/coupling lemmas identify the pair.  The local additive
transform and fold algebra are already in `Theory/AdditiveNTT*.lean`; the
remaining protocol assembly is `[HALF-FRI-assemble]`.

The proof is the direct 2x2 solve attributed to Raghavendra--Wootters (STOC
2013), in the exact half-threshold form used by Chai--Fan.  No Johnson list
bound, Reed--Solomon structure, or conjecture is required here.
-/
import Selvage.JohnsonRegime

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Two close folds force correlated agreement of the pair -/

/-- Two distinct `delta/2`-close points on the affine fold line force the
underlying pair to have correlated agreement at radius `delta`.

The witnesses `u1,u2` are solved back to codewords

`g1 = (gamma1-gamma2)^-1 * (u1-u2)` and
`g0 = u1 - gamma1*g1`.

The two agreement sets each cover a `(1-delta/2)` fraction; their intersection
covers `(1-delta)`, and on it the 2x2 system identifies both source words. -/
theorem correlatedAgreement_of_two_half_close
    {C : Submodule F (ι → F)} {f₀ f₁ : ι → F} {δ : ℝ}
    {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂)
    (h₁ : close (δ / 2) C (foldFamily f₀ f₁ γ₁))
    (h₂ : close (δ / 2) C (foldFamily f₀ f₁ γ₂)) :
    CorrelatedAgreement C δ ![f₀, f₁] := by
  classical
  obtain ⟨u₁, hu₁C, hclose₁⟩ := h₁
  obtain ⟨u₂, hu₂C, hclose₂⟩ := h₂
  let S₁ : Finset ι := Finset.univ.filter fun x =>
    foldFamily f₀ f₁ γ₁ x = u₁ x
  let S₂ : Finset ι := Finset.univ.filter fun x =>
    foldFamily f₀ f₁ γ₂ x = u₂ x
  have hS₁ : (1 - δ / 2) * (Fintype.card ι : ℝ) ≤ (S₁.card : ℝ) := by
    exact card_agreeFilter_ge_of_relDist_le hclose₁
  have hS₂ : (1 - δ / 2) * (Fintype.card ι : ℝ) ≤ (S₂.card : ℝ) := by
    exact card_agreeFilter_ge_of_relDist_le hclose₂
  let S := S₁ ∩ S₂
  have hS : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    have h := card_inter_agreement (δ := δ / 2) hS₁ hS₂
    dsimp [S]
    convert h using 1
    ring
  have hγsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hγ
  let g₁ : ι → F := (γ₁ - γ₂)⁻¹ • (u₁ - u₂)
  let g₀ : ι → F := u₁ - γ₁ • g₁
  have hg₁C : g₁ ∈ C := C.smul_mem _ (C.sub_mem hu₁C hu₂C)
  have hg₀C : g₀ ∈ C := C.sub_mem hu₁C (C.smul_mem _ hg₁C)
  refine ⟨S, hS, fun i => ?_⟩
  fin_cases i
  · refine ⟨g₀, hg₀C, fun x hx => ?_⟩
    change f₀ x = g₀ x
    have hx' : x ∈ S₁ ∩ S₂ := by simpa [S] using hx
    have hx12 : x ∈ S₁ ∧ x ∈ S₂ := Finset.mem_inter.mp hx'
    have hx₁ : foldFamily f₀ f₁ γ₁ x = u₁ x := by
      exact (Finset.mem_filter.mp hx12.1).2
    have hx₂ : foldFamily f₀ f₁ γ₂ x = u₂ x := by
      exact (Finset.mem_filter.mp hx12.2).2
    have hf₁ : f₁ x = g₁ x := by
      simp only [g₁, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [eq_comm, inv_mul_eq_div, div_eq_iff hγsub]
      rw [eq_comm, mul_comm]
      simp only [foldFamily_apply] at hx₁ hx₂
      linear_combination hx₁ - hx₂
    simp only [g₀, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hf₁]
    simp only [foldFamily_apply] at hx₁
    linear_combination hx₁
  · refine ⟨g₁, hg₁C, fun x hx => ?_⟩
    change f₁ x = g₁ x
    have hx' : x ∈ S₁ ∩ S₂ := by simpa [S] using hx
    have hx12 : x ∈ S₁ ∧ x ∈ S₂ := Finset.mem_inter.mp hx'
    have hx₁ : foldFamily f₀ f₁ γ₁ x = u₁ x := by
      exact (Finset.mem_filter.mp hx12.1).2
    have hx₂ : foldFamily f₀ f₁ γ₂ x = u₂ x := by
      exact (Finset.mem_filter.mp hx12.2).2
    simp only [g₁, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [eq_comm, inv_mul_eq_div, div_eq_iff hγsub]
    rw [eq_comm, mul_comm]
    simp only [foldFamily_apply] at hx₁ hx₂
    linear_combination hx₁ - hx₂

/-! ## At most one bad scalar, hence `1/|F|` -/

/-- The finite set of scalars whose affine fold is `delta/2`-close.  Naming
the set keeps its classical decidability choice out of theorem statements. -/
noncomputable def halfThresholdBadScalars [Fintype F]
    (C : Submodule F (ι → F)) (f₀ f₁ : ι → F) (δ : ℝ) : Finset F :=
  @Finset.filter F (fun γ : F => close (δ / 2) C (foldFamily f₀ f₁ γ))
    (Classical.decPred _) Finset.univ

/-- If the pair is `delta`-far from correlated agreement, the set of scalars
whose fold is `delta/2`-close to the code has cardinality at most one. -/
theorem halfThreshold_bad_card_le_one [Fintype F]
    (C : Submodule F (ι → F)) (f₀ f₁ : ι → F) (δ : ℝ)
    (hfar : ¬ CorrelatedAgreement C δ ![f₀, f₁]) :
    (halfThresholdBadScalars C f₀ f₁ δ).card ≤ 1 := by
  classical
  unfold halfThresholdBadScalars
  rw [Finset.card_le_one]
  intro γ₁ h₁ γ₂ h₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  by_contra hne
  exact hfar (correlatedAgreement_of_two_half_close hne h₁ h₂)

/-- **The half-threshold proximity bound.** Under uniform `gamma <- F`, a
pair with no radius-`delta` correlated explanation produces a
`delta/2`-close fold with probability at most `1/|F|`.

Unlike the historical same-threshold WHIR conjecture, this statement is
unconditional for every finite linear code. -/
theorem halfThreshold_pr_le [Fintype F]
    (C : Submodule F (ι → F)) (f₀ f₁ : ι → F) (δ : ℝ)
    (hfar : ¬ CorrelatedAgreement C δ ![f₀, f₁]) :
    (affineGenerator F).pr (fun r =>
        close (δ / 2) C (comb r ![f₀, f₁]))
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  have hcard := halfThreshold_bad_card_le_one C f₀ f₁ δ hfar
  unfold ProximityGenerator.pr
  simp only [affineGenerator]
  have hcomb (γ : F) :
      comb ![1, γ] ![f₀, f₁] = foldFamily f₀ f₁ γ := by
    rw [foldFamily_eq_comb]
    rfl
  simp_rw [hcomb]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hinv : 0 ≤ ((Fintype.card F : ℝ))⁻¹ := by positivity
  calc
    ((Finset.univ.filter fun γ : F =>
          close (δ / 2) C (foldFamily f₀ f₁ γ)).card : ℝ)
        * (Fintype.card F : ℝ)⁻¹
        ≤ 1 * (Fintype.card F : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by
        unfold halfThresholdBadScalars at hcard
        exact_mod_cast hcard) hinv
    _ = 1 / (Fintype.card F : ℝ) := by rw [one_mul, one_div]

/-! ## A non-vacuous F5 keystone -/

namespace HalfThresholdExample

def toothWord : Fin 2 → ZMod 5 := ![1, 0]

/-- The pair `(0,toothWord)` has no correlated explanation by the zero code
on a set covering `3/4` of the two-point domain. -/
theorem pair_far :
    ¬ CorrelatedAgreement (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5))
      (1 / 4) ![0, toothWord] := by
  rintro ⟨S, hS, hall⟩
  have hcard : S.card = 2 := by
    norm_num [Fintype.card_fin] at hS
    have hle : S.card ≤ 2 := by
      simpa [Fintype.card_fin] using Finset.card_le_univ S
    have hnot : ¬ S.card ≤ 1 := by
      intro hle1
      have hcast : (S.card : ℝ) ≤ 1 := by exact_mod_cast hle1
      linarith
    omega
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hcard)
  obtain ⟨u, huC, huAg⟩ := hall 1
  have hu0 : u = 0 := (Submodule.mem_bot (ZMod 5)).mp huC
  have hzero := huAg 0 (by rw [hSuniv]; simp)
  rw [hu0] at hzero
  norm_num [toothWord] at hzero

/-- The event is inhabited: at `gamma=0`, the fold is exactly the zero
codeword. -/
theorem zero_is_bad :
    close (1 / 8) (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5))
      (foldFamily 0 toothWord 0) := by
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  simp [foldFamily, relDist]

/-- The probability theorem fires at the concrete site and yields the sharp
one-scalar price `1/5`; `zero_is_bad` proves the event is not empty. -/
theorem halfThreshold_F5 :
    (affineGenerator (ZMod 5)).pr (fun r =>
        close (1 / 8) (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5))
          (comb r ![0, toothWord])) ≤ 1 / 5 := by
  convert halfThreshold_pr_le
    (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5)) 0 toothWord (1 / 4) pair_far using 1
  norm_num

end HalfThresholdExample

/-!
## Honest boundary

* **Closed:** the characteristic-independent 2x2 solve, the at-most-one bad
  scalar theorem, the exact `1/|F|` probability price, and a nonempty F5
  instance.
* **`[HALF-FRI-assemble]`:** connect Selvage's multiplicative or additive fold
  decomposition to the pair premise, apply this bound once, then use the
  landed UD proximity theorem without compounding the threshold.  Add the
  query miss term `(1-delta/2)^q` and transcript/FS composition.
* **Johnson/MCA status:** `WHIRConjecture412` remains a useful historical
  statement type, but it is no longer literature-open through Johnson:
  ePrint 2025/2051 and 2025/2110 establish that regime.  Capacity-level
  versions are false; post-Johnson positive regimes use different bounds or
  restrictions.  Formalizing those newer full theorems remains separate.
-/

/-- info: 'Minidregg.Selvage.correlatedAgreement_of_two_half_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correlatedAgreement_of_two_half_close
/-- info: 'Minidregg.Selvage.halfThreshold_pr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms halfThreshold_pr_le
/-- info: 'Minidregg.Selvage.HalfThresholdExample.halfThreshold_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdExample.halfThreshold_F5

end Minidregg.Selvage
