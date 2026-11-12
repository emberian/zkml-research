/-
# Selvage.JohnsonMcaBridge — exact interface to the 2025 RS/MCA theorems

This module records the small, proof-theoretically honest bridge from the
published Reed--Solomon mutual-correlated-agreement statements to Selvage's
`WHIRConjecture412` interface.  It does **not** assert the algebraic theorem.
Instead, `HaboeckTheorem2` names its exact finite bad-slope conclusion and the
headline theorems below consume that conclusion as an explicit hypothesis.

Primary sources:

* U. Haböck, *A note on mutual correlated agreement for Reed--Solomon codes*,
  ePrint 2025/2110, Theorem 2.
* S. Bordage, A. Chiesa, Z. Guan, I. Manzur, *All Polynomial Generators
  Preserve Distance with Mutual Correlated Agreement*, ePrint 2025/2051 / CCC
  2026, Theorem 5 (the affine-line specialization).

Haböck writes `RS[F,D,k]` for polynomials of degree at most `k`, hence its
dimension is `k+1`. Selvage's `reedSolomonCode dom d` uses degree `< d`, so the
paper's deliberately reduced rate is

`rho_H = k/n = (d-1)/n`,

not Selvage/WHIR's rounded dimension rate `rho_J = d/n`. For an integer
multiplicity `m >= 3`, Haböck sets

`gamma_m = 1 - (1 + 1/(2m)) * sqrt rho`,
`ell_m   = (m + 1/2) / sqrt rho`,

and proves that the number of bad slopes is at most

`(ell_m^7 / 3) * (rho*n)^2`.

Dividing by `|F|` is exactly Selvage's uniform affine-generator probability.  As
`m -> infinity`, `gamma_m` approaches the Johnson radius `1 - sqrt rho` from
below.  `HaboeckErrorEnvelope` is the precise remaining arithmetic choice of
`m` at every requested radius; it also prevents an invalid upgrade from the
paper's explicit error to an arbitrary error function.

The hard unformalized core is not this bridge.  It is Haböck's adaptation of
BCIKS: Guruswami--Sudan interpolation over `F(Z)`, factorization into
separable/inseparable components, a discriminant specialization, Hensel
lifting, and the useful-factor argument identifying a codeword line.  Keeping
that core in the single proposition `HaboeckTheorem2` makes the dependency
visible without changing `Selvage.JohnsonRegime` or any root import.
-/
import Selvage.JohnsonRegime

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The exact published parameters -/

/-- Haböck Theorem 2's radius for multiplicity `m`. -/
noncomputable def haboeckRadius (ρ : ℝ) (m : ℕ) : ℝ :=
  1 - (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ρ

/-- The auxiliary `ell` in Haböck Theorem 2.  This is unrelated to Selvage's
tuple arity (which is fixed to two here). -/
noncomputable def haboeckEll (ρ : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1 / 2) / Real.sqrt ρ

/-- Haböck Theorem 2's exact upper bound on the **number** of bad slopes. -/
noncomputable def haboeckBadCount (ρ n : ℝ) (m : ℕ) : ℝ :=
  haboeckEll ρ m ^ 7 / 3 * (ρ * n) ^ 2

/-- Haböck's `ρ = k/n` after translating its degree-`≤ k` convention to
Selvage's degree-`< d` convention (`k = d - 1`). -/
noncomputable def haboeckReducedRate (d : ℕ) (n : ℝ) : ℝ :=
  ((d : ℝ) - 1) / n

/-! ## Paper event to Selvage event -/

omit [DecidableEq ι] [DecidableEq F] in
/-- Increasing the decoding radius only relaxes the cardinality condition in
`MutualCAFailure`.  All other witnesses are unchanged. -/
theorem mutualCAFailure_mono_radius {C : Submodule F (ι → F)}
    {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) (f : Fin 2 → ι → F) (r : Fin 2 → F) :
    MutualCAFailure C δ₁ f r → MutualCAFailure C δ₂ f r := by
  rintro ⟨S, hS, hcomb, hinput⟩
  refine ⟨S, ?_, hcomb, hinput⟩
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  nlinarith

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The paper's notation `[f0,f1]|S ∉ C²|S` is exactly Selvage's final
`MutualCAFailure` conjunct. -/
theorem pair_restriction_failure_iff (C : Submodule F (ι → F))
    (S : Finset ι) (f : Fin 2 → ι → F) :
    (∃ i, ∀ u ∈ C, ¬AgreesOn S (f i) u) ↔
      ¬(∀ i, ∃ u ∈ C, AgreesOn S (f i) u) := by
  classical
  constructor
  · rintro ⟨i, hi⟩ hall
    obtain ⟨u, hu, hagree⟩ := hall i
    exact hi u hu hagree
  · intro hnot
    by_contra hnone
    apply hnot
    intro i
    by_contra hnoCodeword
    exact hnone ⟨i, fun u hu hagree => hnoCodeword ⟨u, hu, hagree⟩⟩

/-- For PG(2), Selvage's finitely-supported probability is literally the
cardinality of the bad-slope set divided by `|F|`. -/
noncomputable def affineSeedSet [Fintype F]
    (E : (Fin 2 → F) → Prop) : Finset F := by
  classical
  exact Finset.univ.filter fun z : F => E ((affineGenerator F).gen z)

theorem affineGenerator_pr_eq_seed_card [Fintype F]
    (E : (Fin 2 → F) → Prop) :
    (affineGenerator F).pr E =
      (affineSeedSet E).card / (Fintype.card F : ℝ) := by
  classical
  unfold ProximityGenerator.pr
  change (∑ z ∈ affineSeedSet E, (Fintype.card F : ℝ)⁻¹) = _
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The exact finite statement proved at one multiplicity in Haböck Theorem 2:
for every pair of received words, at most `badCount` slopes have a mutually
uncorrelated agreement witness at radius `γ`.

The paper writes the last conjunct as
`[f0,f1]|A ∉ C^2|A`.  Selvage's `MutualCAFailure` writes its classically
equivalent form: for one of the two inputs, no codeword agrees on `A`. -/
def HaboeckMCAAt [Fintype F] (dom : ι ↪ F) (d : ℕ) (γ badCount : ℝ) : Prop :=
  ∀ f : Fin 2 → ι → F,
    (affineSeedSet
      (MutualCAFailure (reedSolomonCode dom d) γ f)).card ≤ badCount

omit [DecidableEq ι] in
/-- Cardinality form of the paper's conclusion, converted to Selvage's weighted
probability form. -/
theorem haboeckMCAAt_probability [Fintype F] {dom : ι ↪ F} {d : ℕ}
    {γ badCount : ℝ} (h : HaboeckMCAAt dom d γ badCount)
    (f : Fin 2 → ι → F) :
    (affineGenerator F).pr
        (MutualCAFailure (reedSolomonCode dom d) γ f)
      ≤ badCount / (Fintype.card F : ℝ) := by
  rw [affineGenerator_pr_eq_seed_card]
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_div_iff_of_pos_right hF).2 (h f)

omit [DecidableEq ι] in
/-- A one-multiplicity Haböck bound supplies MCA on the entire band below its
endpoint.  This is the smallest useful, fully proved bridge: failure at a
smaller radius is a subset of failure at the published endpoint. -/
theorem hasMutualCorrelatedAgreement_of_haboeckMCAAt [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {γ badCount : ℝ}
    (h : HaboeckMCAAt dom d γ badCount) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      (1 - γ) (fun _ => badCount / (Fintype.card F : ℝ)) := by
  intro f δ _hδ0 hδγ
  have hle : δ ≤ γ := by linarith
  exact le_trans
    ((affineGenerator F).pr_mono
      (mutualCAFailure_mono_radius hle f))
    (haboeckMCAAt_probability h f)

omit [DecidableEq ι] in
/-- Consequently, the direct bad-slope theorem discharges the historical WHIR
implication on its finite-`m` band.  The proximity-generator premise is unused:
the newer theorem proves MCA directly. -/
theorem whirConjecture412_of_haboeckMCAAt [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {γ badCount : ℝ}
    (h : HaboeckMCAAt dom d γ badCount) :
    WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (1 - γ) (fun _ => badCount / (Fintype.card F : ℝ)) := by
  intro _hPG
  exact hasMutualCorrelatedAgreement_of_haboeckMCAAt h

omit [DecidableEq ι] in
/-- A Haböck endpoint that reaches Selvage's (slightly smaller) rounded Johnson
radius discharges the exact RS instance used by `Selvage.JohnsonRegime`.

This is where the convention correction matters: the paper runs at
`ρH = (d-1)/n`, while the target bound is `sqrt (d/n)`.  Thus one finite
multiplicity can already have `1 - sqrt (d/n) ≤ gamma_m`; no pointwise choice
of `m` is needed for the target seam. -/
theorem whirConjecture412_rs_of_haboeckMCAAt [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {γ badCount : ℝ}
    (h : HaboeckMCAAt dom d γ badCount)
    (hcovers :
      1 - Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)) ≤ γ) :
    WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)))
      (fun _ => badCount / (Fintype.card F : ℝ)) := by
  intro _hPG f δ _hδ0 hδJ
  have hδγ : δ ≤ γ := by linarith
  exact le_trans
    ((affineGenerator F).pr_mono
      (mutualCAFailure_mono_radius hδγ f))
    (haboeckMCAAt_probability h f)

/-- Convenient square-form sufficient condition for a Haböck radius to cover
a desired Johnson radius.  This is the form obtained after clearing Selvage's
common blocklength denominator:
`(1 + 1/(2m))² * (d-1) ≤ d`. -/
theorem haboeckRadius_covers_of_sq {ρJ ρH : ℝ} {m : ℕ}
    (hm : 0 < m) (hρJ : 0 ≤ ρJ) (hρH : 0 ≤ ρH)
    (hsq : (1 + 1 / (2 * (m : ℝ))) ^ 2 * ρH ≤ ρJ) :
    1 - Real.sqrt ρJ ≤ haboeckRadius ρH m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have ha : 0 ≤ 1 + 1 / (2 * (m : ℝ)) := by positivity
  have hsJ : (Real.sqrt ρJ) ^ 2 = ρJ := Real.sq_sqrt hρJ
  have hsH : (Real.sqrt ρH) ^ 2 = ρH := Real.sq_sqrt hρH
  have hsJ0 : 0 ≤ Real.sqrt ρJ := Real.sqrt_nonneg _
  have hprod0 : 0 ≤ (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ρH :=
    mul_nonneg ha (Real.sqrt_nonneg _)
  have hprodSq :
      ((1 + 1 / (2 * (m : ℝ))) * Real.sqrt ρH) ^ 2
        ≤ (Real.sqrt ρJ) ^ 2 := by
    rw [mul_pow, hsH, hsJ]
    exact hsq
  have hroot :
      (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ρH ≤ Real.sqrt ρJ := by
    nlinarith
  unfold haboeckRadius
  linarith

omit [DecidableEq ι] in
/-- A concrete uniform multiplicity: for every `d ≥ 2`,
`m = max 3 d` makes Haböck's reduced-rate endpoint cover Selvage's rounded
Johnson radius.  The load-bearing arithmetic is
`(1 + 1/(2m))²(d-1) ≤ d`. -/
theorem haboeckRadius_max_three_degree_covers {d : ℕ}
    (hd2 : 2 ≤ d) (hdn : d ≤ Fintype.card ι) :
    1 - Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)) ≤
      haboeckRadius (haboeckReducedRate d (Fintype.card ι : ℝ)) (max 3 d) := by
  let m : ℕ := max 3 d
  have hnNat : 0 < Fintype.card ι := lt_of_lt_of_le (by omega) hdn
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast hnNat
  have hm3 : 3 ≤ m := by exact le_max_left 3 d
  have hdm : d ≤ m := by exact le_max_right 3 d
  have hm0 : 0 < m := lt_of_lt_of_le (by omega) hm3
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hdmR : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdm
  have hdegree :
      (1 + 1 / (2 * (m : ℝ))) ^ 2 * ((d : ℝ) - 1) ≤ (d : ℝ) := by
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hdmR) (by positivity : (0 : ℝ) ≤ 4 * (m : ℝ))]
  have hρJ : 0 ≤ (d : ℝ) / (Fintype.card ι : ℝ) := by positivity
  have hρH : 0 ≤ haboeckReducedRate d (Fintype.card ι : ℝ) := by
    unfold haboeckReducedRate
    exact div_nonneg (by linarith) (le_of_lt hn)
  have hsq :
      (1 + 1 / (2 * (m : ℝ))) ^ 2 *
          haboeckReducedRate d (Fintype.card ι : ℝ)
        ≤ (d : ℝ) / (Fintype.card ι : ℝ) := by
    unfold haboeckReducedRate
    rw [show (1 + 1 / (2 * (m : ℝ))) ^ 2 *
        (((d : ℝ) - 1) / (Fintype.card ι : ℝ)) =
          ((1 + 1 / (2 * (m : ℝ))) ^ 2 * ((d : ℝ) - 1)) /
            (Fintype.card ι : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hn).2 hdegree
  exact haboeckRadius_covers_of_sq hm0 hρJ hρH hsq

/-! ## Exact theorem obligation and the full Johnson bridge -/

/-- The algebraic core of Haböck Theorem 2, with its exact constants.  This is
a proposition to be supplied as a hypothesis, not an axiom or local claim.
The condition `3 ≤ m` is the paper's multiplicity restriction. -/
def HaboeckTheorem2 [Fintype F] (dom : ι ↪ F) (d : ℕ) : Prop :=
  1 < d ∧ d ≤ Fintype.card ι ∧
    let ρH := haboeckReducedRate d (Fintype.card ι : ℝ)
    ∀ m : ℕ, 3 ≤ m →
      HaboeckMCAAt dom d (haboeckRadius ρH m)
        (haboeckBadCount ρH (Fintype.card ι : ℝ) m)

omit [DecidableEq ι] in
/-- **Smallest single-instance closure.** One multiplicity of the published
theorem suffices for Selvage's rounded Johnson target as soon as its endpoint
covers `1 - sqrt(d/n)`.  The resulting error is the exact constant bad-count
bound divided by `|F|`. -/
theorem whirConjecture412_rs_of_haboeck_single [Fintype F]
    (dom : ι ↪ F) (d m : ℕ) (hHab : HaboeckTheorem2 dom d) (hm3 : 3 ≤ m)
    (hcovers :
      1 - Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)) ≤
        haboeckRadius (haboeckReducedRate d (Fintype.card ι : ℝ)) m) :
    WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)))
      (fun _ =>
        haboeckBadCount (haboeckReducedRate d (Fintype.card ι : ℝ))
          (Fintype.card ι : ℝ) m / (Fintype.card F : ℝ)) := by
  apply whirConjecture412_rs_of_haboeckMCAAt
    (hHab.2.2 m hm3) hcovers

omit [DecidableEq ι] in
/-- The single-instance closure with every arithmetic side condition
discharged by `m = max 3 d`.  Only the corresponding published algebraic
bad-slope theorem remains as the explicit hypothesis `hHab`. -/
theorem whirConjecture412_rs_of_haboeck_max_three_degree
    [Fintype F] (dom : ι ↪ F) (d : ℕ)
    (hHab : HaboeckTheorem2 dom d) :
    WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)))
      (fun _ =>
        haboeckBadCount (haboeckReducedRate d (Fintype.card ι : ℝ))
          (Fintype.card ι : ℝ) (max 3 d) / (Fintype.card F : ℝ)) := by
  exact whirConjecture412_rs_of_haboeck_single dom d (max 3 d) hHab
    (le_max_left 3 d)
    (haboeckRadius_max_three_degree_covers hHab.1 hHab.2.1)

/-- A valid pointwise error envelope chooses a sufficiently large multiplicity
for every radius strictly below Johnson and upper-bounds the resulting bad
probability.  This is the exact compatibility condition missing from the
over-parametric `WHIRConjecture412 ... err`: the papers do not prove their
explicit MCA bound is below an arbitrary caller-supplied `err`. -/
def HaboeckErrorEnvelope (ρJ ρH n q : ℝ) (err : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 - Real.sqrt ρJ →
    ∃ m : ℕ, 3 ≤ m ∧ δ ≤ haboeckRadius ρH m ∧
      haboeckBadCount ρH n m / q ≤ err δ

omit [DecidableEq ι] in
/-- **Full Johnson seam discharge, modulo exactly the published algebraic
core.** `HaboeckTheorem2` supplies the bad-count theorem at each multiplicity;
`HaboeckErrorEnvelope` chooses a multiplicity at each requested Johnson radius
and checks that the explicit paper error fits the error function used by Selvage.

No Johnson-regime proximity-gap hypothesis is needed to prove this implication:
the direct MCA theorem is stronger, so the implication's premise is ignored.
Downstream `mutualCA_johnson` still separately consumes `hPG`, as its public
interface intentionally records the proximity-gap theorem too. -/
theorem whirConjecture412_rs_of_haboeck [Fintype F]
    (dom : ι ↪ F) (d : ℕ) (err : ℝ → ℝ)
    (hHab : HaboeckTheorem2 dom d)
    (henv : HaboeckErrorEnvelope
      ((d : ℝ) / (Fintype.card ι : ℝ))
      (haboeckReducedRate d (Fintype.card ι : ℝ))
      (Fintype.card ι : ℝ) (Fintype.card F : ℝ) err) :
    WHIRConjecture412 (affineGenerator F) (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err := by
  intro _hPG f δ hδ0 hδJ
  let ρH : ℝ := haboeckReducedRate d (Fintype.card ι : ℝ)
  obtain ⟨m, hm3, hδm, hmerr⟩ := henv δ hδ0 hδJ
  have hAt : HaboeckMCAAt dom d (haboeckRadius ρH m)
      (haboeckBadCount ρH (Fintype.card ι : ℝ) m) := by
    exact hHab.2.2 m hm3
  calc
    (affineGenerator F).pr
        (MutualCAFailure (reedSolomonCode dom d) δ f)
        ≤ (affineGenerator F).pr
            (MutualCAFailure (reedSolomonCode dom d)
              (haboeckRadius ρH m) f) :=
          (affineGenerator F).pr_mono
            (mutualCAFailure_mono_radius hδm f)
    _ ≤ haboeckBadCount ρH (Fintype.card ι : ℝ) m /
          (Fintype.card F : ℝ) := haboeckMCAAt_probability hAt f
    _ ≤ err δ := hmerr

end Minidregg.Selvage
