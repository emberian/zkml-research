/-
# Selvage.ReedSolomon — the RS instantiation: WHIR Corollary 4.11's unique-decoding shape.

Instantiates the PROVED generic theorem
`hasMutualCorrelatedAgreement_of_isProximityGenerator` (Selvage/CorrelatedAgreement.lean,
WHIR Lemma 4.10) at the Reed–Solomon code, producing Corollary 4.11's shape: a
proximity generator for RS with bound `B` upgrades to MUTUAL correlated agreement
with bound `B⋆ = max (1 − δ_RS/2) B` and the SAME error, on the unique-decoding
δ-interval.

**What is proved here, and against what:**

* The RS code over an evaluation domain `dom : ι ↪ F` (`Fintype ι`, `F` a field)
  with degree bound `d` is BY CONSTRUCTION a submodule of `ι → F`: it is the image
  of Mathlib's `Polynomial.degreeLT F d` under the evaluation linear map
  `LinearMap.pi (fun i => Polynomial.leval (dom i))`. Linearity of evaluation is
  the whole content of "it is a linear code".
* Minimum distance (`reedSolomonCode_minDist`): distinct polynomials of degree
  `< d` agree on FEWER than `d` domain points — the difference is a nonzero
  polynomial of `natDegree ≤ d − 1`, and the agreement points embed (injectively,
  via `dom`) into its roots (`Polynomial.card_le_degree_of_subset_roots` on top of
  `Polynomial.card_roots'`). Hence for `u ≠ v` in the code,
  `1 − (d−1)/n ≤ relDist u v` — exactly the `hdC` hypothesis shape of Lemma 4.10,
  in `relDist`'s normalization (`hammingDist / n`, division in ℝ).

**Off-by-one convention note (transcribed honestly, not fudged):** with `ρ = d/n`
(degree bound `d` = dimension, `n = |ι|`), the EXACT relative RS distance is
`δ_RS = 1 − (d−1)/n = (n − d + 1)/n` (Singleton, attained — MDS). WHIR §4.2 /
BCIKS use the ROUNDED-DOWN convention `δ_RS = 1 − ρ = 1 − d/n`, undercounting by
`1/n`, and Corollary 4.11 accordingly reports `B⋆ = (1+ρ)/2`. Our exact `dC`
gives the strictly better `B⋆ = 1 − dC/2 = (n + d − 1)/(2n) = (1+ρ)/2 − 1/(2n)`
(δ-interval wider by `1/(2n)`). BOTH forms are provided:
`reedSolomonCode_hasMutualCorrelatedAgreement` (exact, primary; closed form in
`…_closed`) and `…_sqrtRate` (the paper's printed Cor 4.11: rounded `dC := 1 − ρ`
— legitimate, since a lower bound of a lower bound — with `B = √ρ`, where the max
collapses to `(1+ρ)/2` by AM–GM exactly as printed).

**What stays a hypothesis (keystone TODO):** `IsProximityGenerator` for the RS
code — i.e. that the geometric generator actually IS a proximity generator with
`B = √ρ` and explicit `err` — is WHIR Theorem 4.8, imported there from BCIKS,
"Proximity Gaps for Reed–Solomon Codes" (eprint 2020/654). That is real future
proof work (the Johnson-regime rung of docs/LOOM-RECOMPOSITION.md §5's ladder);
here it enters only as the hypothesis `hPG`, never as an instance or axiom
(ATLAS law 1: naming is faking). Premise inhabitation is still exhibited
non-vacuously: at full rate `d = n` the RS code is ⊤ (Lagrange interpolation,
`reedSolomonCode_card_eq_top`), where `isProximityGenerator_top` FIRES and the
end-to-end corollary has a nonempty δ-interval.
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.CorrelatedAgreement

namespace Minidregg.Selvage

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {ℓ : ℕ}

/-! ## The Reed–Solomon code as a submodule of `ι → F`

Evaluation at every domain point is linear in the polynomial, so the code is the
image of the degree-window submodule `Polynomial.degreeLT` under a linear map —
a `Submodule` by construction, no closure lemmas to hand-prove. -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Evaluation of a polynomial at every point of the domain, as a linear map
`F[X] →ₗ[F] (ι → F)` — coordinatewise `Polynomial.leval`. -/
noncomputable def evalOnDomain (dom : ι ↪ F) : Polynomial F →ₗ[F] (ι → F) :=
  LinearMap.pi fun i => Polynomial.leval (dom i)

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp] theorem evalOnDomain_apply (dom : ι ↪ F) (p : Polynomial F) (i : ι) :
    evalOnDomain dom p i = p.eval (dom i) := rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **The Reed–Solomon code** `RS[F, dom, d]`: the functions `ι → F` that are
evaluations over the domain of some polynomial of degree `< d`. A submodule
(= linear code) by construction: the image of `Polynomial.degreeLT F d` under
the evaluation linear map. -/
noncomputable def reedSolomonCode (dom : ι ↪ F) (d : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F d).map (evalOnDomain dom)

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Membership unfolded to the textbook form. -/
theorem mem_reedSolomonCode_iff {dom : ι ↪ F} {d : ℕ} {f : ι → F} :
    f ∈ reedSolomonCode dom d ↔
      ∃ p : Polynomial F, p.degree < (d : WithBot ℕ) ∧ ∀ i, f i = p.eval (dom i) := by
  simp only [reedSolomonCode, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, Polynomial.mem_degreeLT.mp hp, fun i => rfl⟩
  · rintro ⟨p, hp, hf⟩
    exact ⟨p, Polynomial.mem_degreeLT.mpr hp, funext fun i => (hf i).symm⟩

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The carrier set of the submodule is EXACTLY the evaluation set — the
"it is a submodule" claim with its teeth visible. -/
theorem coe_reedSolomonCode (dom : ι ↪ F) (d : ℕ) :
    (reedSolomonCode dom d : Set (ι → F))
      = {f | ∃ p : Polynomial F, p.degree < (d : WithBot ℕ) ∧ ∀ i, f i = p.eval (dom i)} :=
  Set.ext fun _ => mem_reedSolomonCode_iff

/-! ## Minimum distance: root counting

Mathlib lemmas doing the work: `Polynomial.degree_sub_le` + `max_lt` (the
difference stays in the degree window), `Polynomial.natDegree_lt_iff_degree_lt`,
`Polynomial.mem_roots`, and `Polynomial.card_le_degree_of_subset_roots` (itself
`Polynomial.card_roots'`: a nonzero polynomial has at most `natDegree` roots,
counted with multiplicity). -/

omit [DecidableEq ι] in
/-- Distinct polynomials of degree `< d` agree on FEWER than `d` domain points:
their difference is nonzero of `natDegree < d`, and the agreement points inject
into its roots via `dom`. -/
theorem card_agreeSet_lt_of_ne (dom : ι ↪ F) {d : ℕ} {p q : Polynomial F}
    (hp : p.degree < (d : WithBot ℕ)) (hq : q.degree < (d : WithBot ℕ)) (hne : p ≠ q) :
    (Finset.univ.filter fun i => p.eval (dom i) = q.eval (dom i)).card < d := by
  classical
  have hr0 : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hrdeg : (p - q).degree < (d : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le p q) (max_lt hp hq)
  have hrnat : (p - q).natDegree < d :=
    (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hrdeg
  have hsub : ((Finset.univ.filter fun i =>
      p.eval (dom i) = q.eval (dom i)).image dom).val ⊆ (p - q).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hagree := (Finset.mem_filter.mp hi).2
    rw [Polynomial.mem_roots hr0]
    simp [Polynomial.IsRoot, Polynomial.eval_sub, hagree]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injective _ dom.injective] at hcard
  exact lt_of_le_of_lt hcard hrnat

omit [DecidableEq ι] in
/-- **RS minimum distance, in Lemma 4.10's `hdC` shape.** Distinct codewords are
at relative distance at least `dC := 1 − (d−1)/n` (the EXACT `(n − d + 1)/n`
Singleton distance; the papers' rounded `1 − d/n` is the weaker consequence used
in `…_sqrtRate` below). Normalization is `relDist`'s: `hammingDist / n` in ℝ.
No `Nonempty ι` hypothesis: an empty domain admits no distinct pair. -/
theorem reedSolomonCode_minDist (dom : ι ↪ F) (d : ℕ) :
    ∀ u ∈ reedSolomonCode dom d, ∀ v ∈ reedSolomonCode dom d, u ≠ v →
      1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ) ≤ relDist u v := by
  classical
  intro u hu v hv hne
  haveI : Nonempty ι := by
    by_contra h
    exact hne (funext fun i => absurd ⟨i⟩ h)
  obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
  obtain ⟨q, hq, hqv⟩ := mem_reedSolomonCode_iff.mp hv
  have hpq : p ≠ q := by
    rintro rfl
    exact hne (funext fun i => (hpu i).trans (hqv i).symm)
  -- agreement of the words = agreement of the polynomials, < d points
  have hagree : (Finset.univ.filter fun i => u i = v i).card < d := by
    have heq : (Finset.univ.filter fun i => u i = v i)
        = (Finset.univ.filter fun i => p.eval (dom i) = q.eval (dom i)) := by
      apply Finset.filter_congr
      intro i _
      rw [hpu i, hqv i]
    rw [heq]
    exact card_agreeSet_lt_of_ne dom hp hq hpq
  -- every coordinate either agrees or contributes to the Hamming distance
  have hcover : Fintype.card ι
      ≤ (Finset.univ.filter fun i => u i = v i).card + hammingDist u v := by
    have hh : hammingDist u v = (Finset.univ.filter fun i => u i ≠ v i).card := by
      simp [hammingDist]
    rw [hh, ← Finset.card_univ]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i _
    by_cases h : u i = v i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hnat : Fintype.card ι + 1 ≤ d + hammingDist u v := by omega
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn
  have hcast : (Fintype.card ι : ℝ) + 1 ≤ (d : ℝ) + (hammingDist u v : ℝ) := by
    exact_mod_cast hnat
  have hexp : (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) - ((d : ℝ) - 1) := by
    field_simp
  rw [relDist, le_div_iff₀ hn, hexp]
  linarith

/-! ## Corollary 4.11, unique-decoding shape -/

/-- `1 − dC/2` at the exact RS distance, in closed form: `(n + d − 1)/(2n)`. -/
private theorem one_sub_half_rsDist_eq {n dR : ℝ} (hn : n ≠ 0) :
    1 - (1 - (dR - 1) / n) / 2 = (n + dR - 1) / (2 * n) := by
  field_simp
  ring

/-- **WHIR Corollary 4.11, unique-decoding shape (exact distance).** If `Gen` is
a proximity generator for `RS[F, dom, d]` with bound `B` and error `err`, it has
MUTUAL correlated agreement with bound `B⋆ = max (1 − dC/2) B` at
`dC := 1 − (d−1)/n`, and the SAME error — the generic Lemma 4.10 fed the RS
minimum distance. The `IsProximityGenerator` hypothesis is WHIR Thm 4.8 /
BCIKS 2020/654: future work, carried honestly as `hPG`. -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement [Nonempty ι]
    (G : ProximityGenerator F ℓ) (dom : ι ↪ F) (d : ℕ) {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator G (reedSolomonCode dom d) B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement G (reedSolomonCode dom d)
      (max (1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2) B) err :=
  hasMutualCorrelatedAgreement_of_isProximityGenerator G (reedSolomonCode dom d)
    (reedSolomonCode_minDist dom d) hPG
    (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)

/-- The same corollary with `1 − dC/2` in closed form `(n + d − 1)/(2n)`
(= the paper's `(1+ρ)/2` minus the off-by-one dividend `1/(2n)`, `ρ = d/n`). -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_closed [Nonempty ι]
    (G : ProximityGenerator F ℓ) (dom : ι ↪ F) (d : ℕ) {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator G (reedSolomonCode dom d) B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement G (reedSolomonCode dom d)
      (max (((Fintype.card ι : ℝ) + (d : ℝ) - 1) / (2 * (Fintype.card ι : ℝ))) B)
      err := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt this
  have h := reedSolomonCode_hasMutualCorrelatedAgreement G dom d hPG
    (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)
  rwa [one_sub_half_rsDist_eq hn] at h

/-- When the proximity bound already sits below the half-distance point
(`B ≤ (n + d − 1)/(2n)`), the max collapses: `B⋆ = (n + d − 1)/(2n)`. -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_of_le [Nonempty ι]
    (G : ProximityGenerator F ℓ) (dom : ι ↪ F) (d : ℕ) {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator G (reedSolomonCode dom d) B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ)
    (hB : B ≤ ((Fintype.card ι : ℝ) + (d : ℝ) - 1) / (2 * (Fintype.card ι : ℝ))) :
    HasMutualCorrelatedAgreement G (reedSolomonCode dom d)
      (((Fintype.card ι : ℝ) + (d : ℝ) - 1) / (2 * (Fintype.card ι : ℝ))) err := by
  have h := reedSolomonCode_hasMutualCorrelatedAgreement_closed G dom d hPG
    (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)
  rwa [max_eq_left hB] at h

/-- **WHIR Corollary 4.11 as printed, at `ρ = d/n`.** Uses the papers' ROUNDED
distance `dC := 1 − ρ` (weaker than our exact bound, hence still sound) and the
Thm 4.8 proximity bound `B = √ρ` — carried as the `hPG` HYPOTHESIS (BCIKS
2020/654; future work, the keystone TODO of this file). The max collapses by
AM–GM: `√ρ ≤ (1+ρ)/2`, so `B⋆ = (1+ρ)/2` exactly as the paper reports. Honest
quantification: the conclusion's δ-interval `(0, (1−ρ)/2)` is nonempty iff
`d < n` — a rate-1 code has no unique-decoding radius. -/
theorem reedSolomonCode_hasMutualCorrelatedAgreement_sqrtRate [Nonempty ι]
    (G : ProximityGenerator F ℓ) (dom : ι ↪ F) (d : ℕ) {err : ℝ → ℝ}
    (hPG : IsProximityGenerator G (reedSolomonCode dom d)
      (Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))) err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ →
      δ₂ < 1 - Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)) → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ →
      δ < 1 - Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)) → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement G (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2) err := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hρ0 : 0 ≤ (d : ℝ) / (Fintype.card ι : ℝ) := by positivity
  -- rounded distance: 1 − d/n ≤ 1 − (d−1)/n ≤ relDist
  have hdC : ∀ u ∈ reedSolomonCode dom d, ∀ v ∈ reedSolomonCode dom d, u ≠ v →
      1 - (d : ℝ) / (Fintype.card ι : ℝ) ≤ relDist u v := by
    intro u hu v hv huv
    refine le_trans ?_ (reedSolomonCode_minDist dom d u hu v hv huv)
    have hdd : ((d : ℝ) - 1) / (Fintype.card ι : ℝ) ≤ (d : ℝ) / (Fintype.card ι : ℝ) :=
      (div_le_div_iff_of_pos_right hn).mpr (by linarith)
    linarith
  -- AM–GM: √ρ ≤ (1+ρ)/2
  have hAM : Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ))
      ≤ (1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2 := by
    nlinarith [Real.sq_sqrt hρ0, Real.sqrt_nonneg ((d : ℝ) / (Fintype.card ι : ℝ)),
      sq_nonneg (1 - Real.sqrt ((d : ℝ) / (Fintype.card ι : ℝ)))]
  have h := hasMutualCorrelatedAgreement_of_isProximityGenerator G
    (reedSolomonCode dom d) hdC hPG
    (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)
  have harith : 1 - (1 - (d : ℝ) / (Fintype.card ι : ℝ)) / 2
      = (1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2 := by ring
  rwa [harith, max_eq_left hAM] at h

/-! ## Keystone hygiene (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The theorems above are proved, so no obligation `Prop` is left behind; what must
be exhibited is that the hypotheses are inhabitable and the bounds are exercised
— i.e. nothing here is a vacuous implication.

* `hdC` premise: the tiny concrete code below (F₅, 4 points, `d = 2`) has a
  distinct pair on which the distance bound FIRES, with equality — the bound is
  tight, not slack.
* `hPG` premise: at full rate `d = n` the RS code is ⊤ (Lagrange interpolation),
  where `isProximityGenerator_top` provides a genuinely-firing proximity
  generator; the corollary then applies end-to-end with a NONEMPTY δ-interval.
  A macroscopic-rate realizer is WHIR Thm 4.8 / BCIKS 2020/654 — the keystone
  TODO, tracked as future work, never assumed. -/

omit [DecidableEq F] in
/-- At full rate `d = |ι|` the RS code is everything — Lagrange interpolation
(`Lagrange.interpolate`) provides a degree-`< n` polynomial through any values.
Degenerate as a code (distance bound `1 − (n−1)/n = 1/n`, the quantization
floor), but a genuine premise-inhabitation site for `IsProximityGenerator`. -/
theorem reedSolomonCode_card_eq_top (dom : ι ↪ F) :
    reedSolomonCode dom (Fintype.card ι) = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro f
  refine mem_reedSolomonCode_iff.mpr
    ⟨Lagrange.interpolate Finset.univ (⇑dom) f, ?_, fun i => ?_⟩
  · simpa [Finset.card_univ] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (v := ⇑dom) f
        dom.injective.injOn
  · exact (Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := ⇑dom) f
      dom.injective.injOn (Finset.mem_univ i)).symm

/-- End-to-end instantiation of the corollary at a genuinely-inhabited `hPG`:
PG(2) over the full-rate RS code (= ⊤), `B = 0`, `err = 0`. Every hypothesis is
discharged; `B⋆ = 1 − 1/(2n)` and the δ-interval `(0, 1/(2n))` is nonempty
(the `example` below). -/
theorem reedSolomonCode_full_hasMutualCA [Nonempty ι] [Fintype F] (dom : ι ↪ F) :
    HasMutualCorrelatedAgreement (affineGenerator F)
      (reedSolomonCode dom (Fintype.card ι))
      (max (1 - (1 - ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2) 0)
      (fun _ => 0) :=
  reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F) dom
    (Fintype.card ι) (B := 0) (err := fun _ => 0)
    (by rw [reedSolomonCode_card_eq_top]; exact isProximityGenerator_top _)
    (fun _ _ _ => le_refl 0) (fun _ _ => le_refl 0)

/-- Teeth: the δ-interval of the full-rate instantiation is nonempty — the
corollary's conclusion quantifies over something. -/
example [Nonempty ι] :
    ∃ δ : ℝ, 0 < δ ∧
      δ < 1 - max (1 - (1 - ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2) 0 := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn
  have h1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hfrac : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
  have hle : 1 / (Fintype.card ι : ℝ) ≤ 1 := by rw [div_le_one hn]; exact h1
  refine ⟨1 / (Fintype.card ι : ℝ) / 4, by positivity, ?_⟩
  have harith : 1 - (1 - ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2
      = 1 - 1 / (Fintype.card ι : ℝ) / 2 := by
    have hkey : ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)
        = 1 - 1 / (Fintype.card ι : ℝ) := by field_simp
    rw [hkey]; ring
  rw [harith, max_eq_left (by linarith)]
  linarith

/-! ### The concrete tiny code: `RS[F₅, {0,1,2,3}, 2]`

Four points of F₅, degree `< 2` (lines). `n = 4`, `d = 2`, exact distance bound
`dC = 1 − 1/4 = 3/4`. The pair (evaluations of `X`, evaluations of `0`) is a
distinct codeword pair realizing `relDist = 3/4`: the bound FIRES with equality. -/

namespace RSExample

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The evaluation domain `{0, 1, 2, 3} ⊂ F₅` (injectivity by `decide`). -/
def dom₅ : Fin 4 ↪ ZMod 5 :=
  ⟨fun i => (i.val : ZMod 5), by decide⟩

/-- The word `(0, 1, 2, 3)` — evaluations of the polynomial `X`. -/
def xWord : Fin 4 → ZMod 5 := fun i => (i.val : ZMod 5)

theorem xWord_mem : xWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.X, by rw [Polynomial.degree_X]; decide,
      fun i => by simp [xWord, dom₅]⟩

theorem xWord_ne_zero : xWord ≠ 0 := by decide

/-- Hamming distance to the zero codeword computed by `decide`: the words agree
only at the coordinate `0`. -/
theorem hammingDist_xWord_zero : hammingDist xWord (0 : Fin 4 → ZMod 5) = 3 := by
  decide

/-- `relDist = 3/4` — the exact minimum distance `1 − (d−1)/n = 3/4` is ATTAINED
by this pair (`norm_num` on top of the `decide`d Hamming distance). -/
theorem relDist_xWord_zero : relDist xWord (0 : Fin 4 → ZMod 5) = 3 / 4 := by
  rw [relDist, hammingDist_xWord_zero]
  norm_num [Fintype.card_fin]

/-- The general minimum-distance theorem EXERCISED at the tiny code: its bound
`3/4` is delivered on a concrete distinct pair (and is tight, by
`relDist_xWord_zero`). Non-vacuity of the `hdC` premise with a macroscopic
`dC` — compare the `1/n = 1/4` quantization floor. -/
example : (3 / 4 : ℝ) ≤ relDist xWord (0 : Fin 4 → ZMod 5) := by
  have h := reedSolomonCode_minDist dom₅ 2 xWord xWord_mem
    0 (Submodule.zero_mem _) xWord_ne_zero
  norm_num [Fintype.card_fin] at h
  linarith

end RSExample

end Minidregg.Selvage
