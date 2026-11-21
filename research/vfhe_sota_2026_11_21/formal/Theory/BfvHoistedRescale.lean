/-
# `Theory/BfvHoistedRescale.lean` — Hoisted Sum-Before-Rescale (`sumMulPhase`) and the `Hole B` Polynomial Certificate

**Substrate, said out loud: this is Lean-authored metatheory.** Pure `Mathlib` + `Theory.BfvMul`
imports (`scripts/check-import-boundary.sh`: `Theory/` tier only). Zero `sorry`, zero custom
`axiom`, zero `native_decide`, zero `#guard`.

## What this module closes

`Theory/BfvMul.lean` proved the single-product scalar phase model (`mulPhase P p₁ p₂`) and named
two Phase-2 obligations: (i) product-sum dot-product folds (`Σᵢ aᵢ · bᵢ`), and (ii) the polynomial
ring lift over `ℤ[X]/(X^N + 1)`. In verifiable FHE (`vFHE` / `vFHEML`), rescaling *eagerly* after
every individual `ct × ct` tensor product pays both:
1. **$K\times$ certificate & relinearization blowup** (`6,144` separate BEHZ rescale certificates per
   training step at $d = 4096$ when $K = 64$ column blocks are rescaled before row accumulation), and
2. **$K\times$ rounding-noise accumulation** (`+ K` worst-case rounding units vs `+ 1` when products
   are summed in `ℤ` / `ℤ[X]/(X^N + 1)` *before* a single `t / Q` rescale).

Meanwhile, at the ZK verification boundary (`VERDICTS.md` §7.5 `Hole B`, `rescale_certificates.py`),
checking the BEHZ rescale equation only **modulo $Q$** (`t · z + ⌊Q/2⌋ ≡ s (mod Q)`) deletes the
integer quotient `Q · y` and lets a cheating prover substitute a mod-$Q$ alias with a **forged**
rescaled output (`Q = 31, t = 4`: `z_true = 32 ≡ 1 = z_alias (mod 31)`, yet true output `4 ≠ 0`).

This file proves both halves and their falsifier teeth:

* **Part A — Hoisted Sum-Before-Rescale (`sumMulPhase`)**:
  - `sumMulPhase_singleton`: reduces identically to `BfvMul.mulPhase` at `K = 1`.
  - `sumMulPhase_encrypt_eq`: exact decomposition of `sumMulPhase` across `K` encrypted pairs
    `((Δ·m₁ᵢ + e₁ᵢ), (Δ·m₂ᵢ + e₂ᵢ))` into exact message dot-product `Δ · ∑ m₁ᵢ m₂ᵢ`, summed
    message-amplified cross-noise `∑ (m₁ᵢ e₂ᵢ + m₂ᵢ e₁ᵢ)`, and **one** shared rounding term
    `⌊(2 · sumMulRemainder + q) / (2q)⌋`.
  - `sumMulPhase_noise_le`: worst-case noise bound adding **only `+ 1`** rounding slack across the
    entire `K`-term dot product (vs `+ K` under `K` eager `mulPhase` calls, plus `1` relin vs `K`).
  - **Witness + Falsifier Tooth (`eager_vs_hoisted_rounding_gap`)**: explicit valid `Params`
    (`q = 16, t = 2, Δ = 8`) and `K = 4` honest encrypted pairs of `(0, 0)` whose `+1/2` roundings
    constructively bias in the same direction: eager per-product `mulPhase` summation deviates from
    `sumMulPhase` by `4 - 2 = 2 ≥ 2` and **mis-decrypts `0` as `1`**, whereas `sumMulPhase`
    decrypts to the **exact** dot-product `0`. Also `deployed_hoisted64_margin_holds` pins `K = 64`
    on `fheRs4096`.

* **Part B — Fused `d`-Free Polynomial Rescale Certificate (`Hole B` over `Polynomial ℤ`)**:
  - `HoistedRescaleCert N Q t P_sum y s K_quot`: fuses negacyclic ring reduction `mod (X^N + 1)`
    and BEHZ integer rescaling into a single `ℤ[X]` identity without materializing the intermediate
    remainder polynomial `d = P_sum %ₘ (X^N + 1)`:
      `t · P_sum + ⌊Q/2⌋ · ∑_{j<N} X^j = Q · y + s + t · (X^N + 1) · K_quot`
    paired with canonical degree bounds (`< N` on `y, s`) and range bounds (`0 ≤ s_j < Q`).
  - `hoistedRescaleCert_iff` & `hoistedRescaleCert_unique`: for `N > 0, Q > 0, t ≠ 0`,
    `HoistedRescaleCert` holds **if and only if** `K_quot = P_sum /ₘ (X^N + 1)` (`divByMonic`) and
    every coefficient `j < N` satisfies Euclidean division uniqueness
    `y_j = (t · (P_sum %ₘ (X^N + 1))_j + Q/2) / Q`,
    `s_j = (t · (P_sum %ₘ (X^N + 1))_j + Q/2) % Q` (with `y_j = s_j = 0` for `j ≥ N`).
  - **Witness + `Q = 31, t = 4` `Hole B` Falsifier Tooth**: `hoistedRescaleCert_witness_N2`
    exhibits a concrete `N = 2` certificate with nonzero negacyclic quotient `K_quot = 5`, while
    `holeB_modQ_alias_falsifier` mechanizes `rescale_certificates.py`'s `Q = 31, t = 4` alias
    (`z_true = 32` vs `z_alias = 1`): the mod-$Q$ check accepts forged output `y_forge = 0` (instead
    of true output `4`) with identical remainder `s = 19`, whereas `HoistedRescaleCert` **refuses**
    `y_forge = 0` for *every* choice of `s` and `K_quot`.
-/
import Mathlib.Algebra.Polynomial.Div
import Theory.BfvMul

namespace Minidregg.Theory.Bfv

open Polynomial

/-! ## Part A. Hoisted Sum-Before-Rescale (`sumMulPhase`) & Strict Rounding Savings -/

/-- **Hoisted BFV dot-product rescale (`sumMulPhase`)**: accumulate all unrescaled integer phase
products `∑ (p₁ᵢ · p₂ᵢ)` in `ℤ` first, then apply a SINGLE `round(t · (∑ p₁ᵢ p₂ᵢ) / q)` rescale
`⌊(2t · ∑ p₁ᵢ p₂ᵢ + q) / (2q)⌋`. -/
def sumMulPhase (P : Params) (ps : List (ℤ × ℤ)) : ℤ :=
  (2 * (P.t : ℤ) * (ps.map (fun x => x.1 * x.2)).sum + P.q) / (2 * (P.q : ℤ))

/-- **Eager per-product rescale sum**: rescaling each pair individually via `mulPhase` before
summing phases (incurring `K` separate roundings). -/
def eagerSumMulPhase (P : Params) (ps : List (ℤ × ℤ)) : ℤ :=
  (ps.map (fun x => mulPhase P x.1 x.2)).sum

/-- At length `1`, `sumMulPhase` reduces identically to `BfvMul.mulPhase`. -/
theorem sumMulPhase_singleton (P : Params) (p₁ p₂ : ℤ) :
    sumMulPhase P [(p₁, p₂)] = mulPhase P p₁ p₂ := by
  simp [sumMulPhase, mulPhase]

/-- Encrypt a list of `((m₁, e₁), (m₂, e₂))` operand descriptors into phase pairs
`((Δ·m₁ + e₁), (Δ·m₂ + e₂))`. -/
def encPhasePairs (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) : List (ℤ × ℤ) :=
  os.map (fun o => ((P.Δ : ℤ) * o.1.1 + o.1.2, (P.Δ : ℤ) * o.2.1 + o.2.2))

/-- Hoisted dot-product ciphertext before relinearization. -/
def hoistedDotCt (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) : Ct P :=
  ⟨sumMulPhase P (encPhasePairs P os)⟩

/-- Summed sub-`q` multiplicative remainder across a list of encrypted operand pairs. -/
def sumMulRemainder (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) : ℤ :=
  (os.map (fun o => mulRemainder P o.1.1 o.2.1 o.1.2 o.2.2)).sum

/-- Unrounded `t`-scaled product sum identity across `K` encrypted pairs:
`t · ∑ (Δ m₁ + e₁)(Δ m₂ + e₂) = q · (Δ · ∑ m₁ m₂ + ∑ (m₁ e₂ + m₂ e₁)) + sumMulRemainder`. -/
theorem scaled_encPhasePairs_sum_eq (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) :
    (P.t : ℤ) * ((encPhasePairs P os).map (fun x => x.1 * x.2)).sum =
      (P.q : ℤ) * ((P.Δ : ℤ) * (((os.map (fun o => o.1.1 * o.2.1)).sum : ℕ) : ℤ)
        + (os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum)
      + sumMulRemainder P os := by
  have hQeq : (P.q : ℤ) = (P.Δ : ℤ) * (P.t : ℤ) + (P.r : ℤ) := by exact_mod_cast P.q_eq
  induction os with
  | nil =>
      simp [encPhasePairs, sumMulRemainder]
  | cons o os ih =>
      simp only [encPhasePairs, sumMulRemainder, List.map_cons, List.sum_cons,
        Nat.cast_add, Nat.cast_mul] at ih ⊢
      rw [mul_add, ih]
      unfold mulRemainder
      rw [hQeq]
      ring

/-- **Exact `K`-pair hoisted multiplicative phase decomposition (`sumMulPhase_encrypt_eq`):**
generalizes `BfvMul.mulPhase_encrypt_eq` from one product to `K` summed products, yielding the
exact message dot-product `Δ · ∑ m₁ᵢ m₂ᵢ`, the summed cross-noise `∑ (m₁ᵢ e₂ᵢ + m₂ᵢ e₁ᵢ)`,
and **one single** shared rounding term `⌊(2 · sumMulRemainder + q) / (2q)⌋`. -/
theorem sumMulPhase_encrypt_eq (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) :
    sumMulPhase P (encPhasePairs P os) =
      (P.Δ : ℤ) * (((os.map (fun o => o.1.1 * o.2.1)).sum : ℕ) : ℤ)
        + (os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum
        + (2 * sumMulRemainder P os + P.q) / (2 * (P.q : ℤ)) := by
  have hq : (0 : ℤ) < (P.q : ℤ) := by exact_mod_cast P.q_pos
  have hq0 : (2 * (P.q : ℤ)) ≠ 0 := by linarith
  unfold sumMulPhase
  have hscaled := scaled_encPhasePairs_sum_eq P os
  have hnum :
      2 * (P.t : ℤ) * ((encPhasePairs P os).map (fun x => x.1 * x.2)).sum + (P.q : ℤ) =
        (2 * sumMulRemainder P os + (P.q : ℤ))
          + ((P.Δ : ℤ) * (((os.map (fun o => o.1.1 * o.2.1)).sum : ℕ) : ℤ)
              + (os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum)
            * (2 * (P.q : ℤ)) := by
    calc 2 * (P.t : ℤ) * ((encPhasePairs P os).map (fun x => x.1 * x.2)).sum + (P.q : ℤ)
        = 2 * ((P.t : ℤ) * ((encPhasePairs P os).map (fun x => x.1 * x.2)).sum) + (P.q : ℤ) := by
            ring
      _ = _ := by
            rw [hscaled]
            ring
  rw [hnum, Int.add_mul_ediv_right _ _ hq0]
  ring

/-- **Sound worst-case noise bound for a `K`-term hoisted dot-product + ONE relinearization:**
notice the rounding slack is **`+ 1` total** (not `+ K`), and `Bks` is paid **once** (not `K × Bks`). -/
def hoistedMulNoiseBound (P : Params) (K : ℕ) (M₁ M₂ B₁ B₂ Bks : ℤ) : ℤ :=
  (K : ℤ) * (M₁ * B₂ + M₂ * B₁)
    + ((K : ℤ) * ((P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
        + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁))) / (P.q : ℤ)
    + 1 + Bks

/-- **Hoisted dot-product noise bound (`sumMulPhase_noise_le`):** across `os.length ≤ K` encrypted
pairs with messages `≤ M₁, M₂`, noises `≤ B₁, B₂`, and one relinearization noise `|eks| ≤ Bks`,
the post-rescale noise relative to `∑ m₁ᵢ m₂ᵢ` is bounded by `hoistedMulNoiseBound` — paying
ONLY `+ 1` rounding unit total instead of `+ K`. -/
theorem sumMulPhase_noise_le (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) (eks : ℤ)
    (K : ℕ) (M₁ M₂ B₁ B₂ Bks : ℤ)
    (hlen : os.length ≤ K)
    (hm₁ : ∀ o ∈ os, (o.1.1 : ℤ) ≤ M₁)
    (hm₂ : ∀ o ∈ os, (o.2.1 : ℤ) ≤ M₂)
    (he₁ : ∀ o ∈ os, |o.1.2| ≤ B₁)
    (he₂ : ∀ o ∈ os, |o.2.2| ≤ B₂)
    (hks : |eks| ≤ Bks)
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂) :
    |((hoistedDotCt P os).relin eks).noiseAt ((os.map (fun o => o.1.1 * o.2.1)).sum)|
      ≤ hoistedMulNoiseBound P K M₁ M₂ B₁ B₂ Bks := by
  have hq : (0 : ℤ) < (P.q : ℤ) := by exact_mod_cast P.q_pos
  have ht0 : (0 : ℤ) ≤ (P.t : ℤ) := Int.natCast_nonneg _
  have hr0 : (0 : ℤ) ≤ (P.r : ℤ) := Int.natCast_nonneg _
  have hd0 : (0 : ℤ) ≤ (P.Δ : ℤ) := Int.natCast_nonneg _
  have hlenZ : (os.length : ℤ) ≤ (K : ℤ) := by exact_mod_cast hlen
  have hnoise_eq :
      ((hoistedDotCt P os).relin eks).noiseAt ((os.map (fun o => o.1.1 * o.2.1)).sum) =
        (os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum
          + (2 * sumMulRemainder P os + P.q) / (2 * (P.q : ℤ)) + eks := by
    simp only [hoistedDotCt, Ct.relin, Ct.noiseAt]
    rw [sumMulPhase_encrypt_eq]
    ring
  have hcross_each : ∀ x ∈ os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2),
      |x| ≤ M₁ * B₂ + M₂ * B₁ := by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    have hm1o : (0 : ℤ) ≤ (o.1.1 : ℤ) := Int.natCast_nonneg _
    have hm2o : (0 : ℤ) ≤ (o.2.1 : ℤ) := Int.natCast_nonneg _
    have h1 : (o.1.1 : ℤ) * |o.2.2| ≤ M₁ * B₂ :=
      mul_le_mul (hm₁ o ho) (he₂ o ho) (abs_nonneg _) hM₁0
    have h2 : (o.2.1 : ℤ) * |o.1.2| ≤ M₂ * B₁ :=
      mul_le_mul (hm₂ o ho) (he₁ o ho) (abs_nonneg _) hM₂0
    calc |(o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2|
        ≤ |(o.1.1 : ℤ) * o.2.2| + |(o.2.1 : ℤ) * o.1.2| := abs_add_le _ _
      _ = (o.1.1 : ℤ) * |o.2.2| + (o.2.1 : ℤ) * |o.1.2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hm1o, abs_of_nonneg hm2o]
      _ ≤ M₁ * B₂ + M₂ * B₁ := by linarith
  have hcross_sum :
      |(os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum|
        ≤ (K : ℤ) * (M₁ * B₂ + M₂ * B₁) := by
    have h1 := abs_sum_le_length_mul _ _ hcross_each
    simp only [List.length_map] at h1
    have hCB0 : 0 ≤ M₁ * B₂ + M₂ * B₁ := by positivity
    exact h1.trans (mul_le_mul_of_nonneg_right hlenZ hCB0)
  set E_unit : ℤ := (P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
    + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁)
  have hE_unit0 : 0 ≤ E_unit := by positivity
  have hrem_each : ∀ x ∈ os.map (fun o => mulRemainder P o.1.1 o.2.1 o.1.2 o.2.2),
      |x| ≤ E_unit := by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    have hm1o : (0 : ℤ) ≤ (o.1.1 : ℤ) := Int.natCast_nonneg _
    have hm2o : (0 : ℤ) ≤ (o.2.1 : ℤ) := Int.natCast_nonneg _
    have hcr : |(o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2| ≤ M₁ * B₂ + M₂ * B₁ :=
      hcross_each _ (List.mem_map_of_mem ho)
    have h1 : |(P.t : ℤ) * (o.1.2 * o.2.2)| ≤ (P.t : ℤ) * (B₁ * B₂) := by
      rw [abs_mul, abs_of_nonneg ht0, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (he₁ o ho) (he₂ o ho) (abs_nonneg _) hB₁0) ht0
    have h2 : |(P.r : ℤ) * (P.Δ : ℤ) * ((o.1.1 : ℤ) * o.2.1)|
        ≤ (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hr0 hd0), abs_mul,
        abs_of_nonneg hm1o, abs_of_nonneg hm2o]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hm₁ o ho) (hm₂ o ho) hm2o hM₁0) (mul_nonneg hr0 hd0)
    have h3 : |(P.r : ℤ) * ((o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)|
        ≤ (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁) := by
      rw [abs_mul, abs_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_left hcr hr0
    have hsplit : mulRemainder P o.1.1 o.2.1 o.1.2 o.2.2 =
        (P.t : ℤ) * (o.1.2 * o.2.2)
          + -((P.r : ℤ) * (P.Δ : ℤ) * ((o.1.1 : ℤ) * o.2.1))
          + -((P.r : ℤ) * ((o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)) := by
      unfold mulRemainder; ring
    calc |mulRemainder P o.1.1 o.2.1 o.1.2 o.2.2|
        ≤ |(P.t : ℤ) * (o.1.2 * o.2.2)
            + -((P.r : ℤ) * (P.Δ : ℤ) * ((o.1.1 : ℤ) * o.2.1))|
          + |-((P.r : ℤ) * ((o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2))| := by
            rw [hsplit]; exact abs_add_le _ _
      _ ≤ |(P.t : ℤ) * (o.1.2 * o.2.2)|
          + |-((P.r : ℤ) * (P.Δ : ℤ) * ((o.1.1 : ℤ) * o.2.1))|
          + |-((P.r : ℤ) * ((o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2))| := by
            have := abs_add_le ((P.t : ℤ) * (o.1.2 * o.2.2))
              (-((P.r : ℤ) * (P.Δ : ℤ) * ((o.1.1 : ℤ) * o.2.1)))
            linarith
      _ ≤ E_unit := by
            rw [abs_neg, abs_neg]; unfold E_unit; linarith
  have hrem_sum : |sumMulRemainder P os| ≤ (K : ℤ) * E_unit := by
    unfold sumMulRemainder
    have h1 := abs_sum_le_length_mul _ _ hrem_each
    simp only [List.length_map] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hlenZ hE_unit0)
  have hF := abs_mulRound_le (P.q : ℤ) (sumMulRemainder P os) hq
  have hdiv : |sumMulRemainder P os| / (P.q : ℤ) ≤ ((K : ℤ) * E_unit) / (P.q : ℤ) :=
    Int.ediv_le_ediv hq hrem_sum
  rw [hnoise_eq]
  unfold hoistedMulNoiseBound
  have htri :
      |(os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum
          + (2 * sumMulRemainder P os + P.q) / (2 * (P.q : ℤ)) + eks|
        ≤ |(os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum|
          + |(2 * sumMulRemainder P os + P.q) / (2 * (P.q : ℤ))| + |eks| := by
    have h1 := abs_add_le ((os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum
      + (2 * sumMulRemainder P os + P.q) / (2 * (P.q : ℤ))) eks
    have h2 := abs_add_le ((os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum)
      ((2 * sumMulRemainder P os + P.q) / (2 * (P.q : ℤ)))
    linarith
  linarith

/-- Computable `ℕ`-side hoisted margin check for `K` summed products + 1 relinearization. -/
def hoistedMulNoiseBoundN (P : Params) (K M₁ M₂ B₁ B₂ Bks : ℕ) : ℕ :=
  K * (M₁ * B₂ + M₂ * B₁)
    + (K * (P.t * (B₁ * B₂) + P.r * P.Δ * (M₁ * M₂) + P.r * (M₁ * B₂ + M₂ * B₁))) / P.q
    + 1 + Bks

/-- Deployed `fheRs4096` witness: `K = 64` column-block products hoisted before rescale (matching
the `4096 × 4096` dark-learning matvec's `64 → 1` row-group accumulation) stays safely inside the
decrypt noise margin even after `4096×` worst-case ring-expansion inflation. -/
theorem deployed_hoisted64_margin_holds :
    marginHolds fheRs4096 4096
      (hoistedMulNoiseBoundN fheRs4096 64 127 127 (2 ^ 20) (2 ^ 20) (2 ^ 40)) = true := by
  decide

/-- Concrete valid BFV parameters (`q = 16, t = 2, Δ = 8, r = 0`) for the constructive
rounding-bias tooth. -/
def gapParams : Params where
  q := 16
  t := 2
  t_pos := by decide
  t_lt_q := by decide

/-- Four honest encrypted pairs of `(m₁ = 0, m₂ = 0)` with noises `(e₁ = 1, e₂ = 4)`: each pair's
unrounded rescaled product `t · p₁ · p₂ / q = 2 · 4 / 16 = +1/2` hits the round-half-up tie in the
same positive direction. -/
def gapEncPairs : List ((ℕ × ℤ) × (ℕ × ℤ)) :=
  List.replicate 4 ((0, 1), (0, 4))

/-- **Witness + Falsifier Tooth (`eager_vs_hoisted_rounding_gap`):**
On valid `gapParams` (`q = 16, t = 2`) and `K = 4` encrypted `(0, 0)` pairs:
1. Eager per-product `mulPhase` summation yields `4` while hoisted `sumMulPhase` yields `2` —
   deviating by **`4 - 2 = 2 ≥ 2`**;
2. Hoisted `sumMulPhase` decrypts to the **exact** clear dot-product `0`, whereas eager `mulPhase`
   summation accumulates enough biased rounding error to **silently mis-decrypt `0` as `1`**! -/
theorem eager_vs_hoisted_rounding_gap :
    let ps := encPhasePairs gapParams gapEncPairs
    ps.length = 4 ∧
    eagerSumMulPhase gapParams ps = 4 ∧
    sumMulPhase gapParams ps = 2 ∧
    eagerSumMulPhase gapParams ps - sumMulPhase gapParams ps ≥ 2 ∧
    decryptPhase gapParams (sumMulPhase gapParams ps) = 0 ∧
    decryptPhase gapParams (eagerSumMulPhase gapParams ps) = 1 := by
  decide

/-! ## Part B. Fused `d`-Free Polynomial Rescale Certificate (`Hole B` over `Polynomial ℤ`) -/

/-- All-ones degree-`< N` polynomial `∑_{j=0}^{N-1} X^j`, carrying the uniform `+ ⌊Q/2⌋` rounding
offset across every ring slot simultaneously. -/
noncomputable def onesPoly (N : ℕ) : Polynomial ℤ :=
  (Finset.range N).sum (fun j => Polynomial.X ^ j)

@[simp] theorem coeff_onesPoly (N j : ℕ) :
    (onesPoly N).coeff j = if j < N then 1 else 0 := by
  unfold onesPoly
  rw [Polynomial.finsetSum_coeff]
  simp [Polynomial.coeff_X_pow]

/-- **`Hole B` Fused `d`-Free Polynomial Rescale Certificate (`HoistedRescaleCert`)**:
certifies in a single `ℤ[X]` equation that `y` is the exact coefficientwise `round(t · d / Q)`
rescale of `d := P_sum mod (X^N + 1)`, with sub-`Q` remainder `s` and ring quotient `K_quot`,
without committing `d`:
* `y` and `s` vanish in degree `≥ N`,
* `0 ≤ s.coeff j < Q` for every `j < N`, and
* `t · P_sum + (Q / 2) · ∑_{j<N} X^j = Q · y + s + t · (X^N + 1) · K_quot`. -/
def HoistedRescaleCert (N : ℕ) (Q t : ℤ) (P_sum y s K_quot : Polynomial ℤ) : Prop :=
  (∀ j ≥ N, y.coeff j = 0) ∧
  (∀ j ≥ N, s.coeff j = 0) ∧
  (∀ j < N, 0 ≤ s.coeff j ∧ s.coeff j < Q) ∧
  Polynomial.C t * P_sum + Polynomial.C (Q / 2) * (Finset.range N).sum (fun j => Polynomial.X ^ j) =
    Polynomial.C Q * y + s + Polynomial.C t * (Polynomial.X ^ N + 1) * K_quot

/-- Key degree-separation lemma: if `((X^N + 1) * R).coeff j = 0` for all `j ≥ N` (with `N > 0`),
then `R = 0`. -/
theorem eq_zero_of_X_pow_add_one_mul_coeff_zero {N : ℕ} (hN : 0 < N) {R : Polynomial ℤ}
    (h : ∀ j ≥ N, ((Polynomial.X ^ N + 1) * R).coeff j = 0) :
    R = 0 := by
  by_contra hR
  set m := R.natDegree
  have hcoeff := h (m + N) (Nat.le_add_left N m)
  rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul] at hcoeff
  have hhigh : R.coeff (m + N) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hhigh, add_zero] at hcoeff
  exact Polynomial.leadingCoeff_ne_zero.mpr hR hcoeff

/-- Monicity of the cyclotomic power-of-two modulus `X^N + 1` for `N > 0`. -/
theorem monic_X_pow_add_one {N : ℕ} (hN : 0 < N) :
    ((Polynomial.X : Polynomial ℤ) ^ N + 1).Monic := by
  simpa using Polynomial.monic_X_pow_add_C (1 : ℤ) (Nat.ne_of_gt hN)

/-- Every coefficient of `P_sum %ₘ (X^N + 1)` at index `j ≥ N` is zero (`N > 0`). -/
theorem coeff_modByMonic_X_pow_add_one_eq_zero {N : ℕ} (hN : 0 < N)
    (P_sum : Polynomial ℤ) {j : ℕ} (hj : j ≥ N) :
    (P_sum %ₘ (Polynomial.X ^ N + 1)).coeff j = 0 := by
  have hM := monic_X_pow_add_one hN
  by_cases h0 : P_sum %ₘ (Polynomial.X ^ N + 1) = 0
  · simp [h0]
  · have hdeg := Polynomial.degree_modByMonic_lt P_sum hM
    have hdegM : ((Polynomial.X : Polynomial ℤ) ^ N + 1).degree = (N : WithBot ℕ) := by
      have hnd : ((Polynomial.X : Polynomial ℤ) ^ N + 1).natDegree = N := by
        have h1 := Polynomial.natDegree_X_pow_add_C (n := N) (r := (1 : ℤ))
        simp at h1 ⊢
      rw [Polynomial.degree_eq_natDegree hM.ne_zero, hnd]
    rw [hdegM, Polynomial.degree_eq_natDegree h0] at hdeg
    have hlt : (P_sum %ₘ (Polynomial.X ^ N + 1)).natDegree < N := WithBot.coe_lt_coe.mp hdeg
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hlt hj)

/-- **Exact Characterization of `HoistedRescaleCert` (`hoistedRescaleCert_iff`):**
For `N > 0`, `Q > 0`, and `t ≠ 0`, `HoistedRescaleCert N Q t P_sum y s K_quot` holds **iff**:
1. `K_quot = P_sum /ₘ (X^N + 1)` (`divByMonic`),
2. `y.coeff j = 0` and `s.coeff j = 0` for all `j ≥ N`, and
3. for every `j < N`, `y.coeff j` and `s.coeff j` are uniquely pinned to the exact Euclidean
   quotient and remainder of `t · (P_sum %ₘ (X^N + 1)).coeff j + Q / 2` divided by `Q`. -/
theorem hoistedRescaleCert_iff {N : ℕ} {Q t : ℤ}
    (hN : 0 < N) (hQ : 0 < Q) (ht : t ≠ 0)
    (P_sum y s K_quot : Polynomial ℤ) :
    HoistedRescaleCert N Q t P_sum y s K_quot ↔
      K_quot = P_sum /ₘ (Polynomial.X ^ N + 1) ∧
      (∀ j ≥ N, y.coeff j = 0) ∧
      (∀ j ≥ N, s.coeff j = 0) ∧
      (∀ j < N,
        y.coeff j = (t * (P_sum %ₘ (Polynomial.X ^ N + 1)).coeff j + Q / 2) / Q ∧
        s.coeff j = (t * (P_sum %ₘ (Polynomial.X ^ N + 1)).coeff j + Q / 2) % Q) := by
  set M : Polynomial ℤ := Polynomial.X ^ N + 1
  have hdiv_id : P_sum %ₘ M + M * (P_sum /ₘ M) = P_sum := Polynomial.modByMonic_add_div P_sum M
  constructor
  · rintro ⟨hy, hs, hs_range, heq⟩
    set d := P_sum %ₘ M
    set K₀ := P_sum /ₘ M
    have h1 : (Finset.range N).sum (fun j => (Polynomial.X : Polynomial ℤ) ^ j) = onesPoly N := rfl
    rw [h1] at heq
    have hM_def : (Polynomial.X : Polynomial ℤ) ^ N + 1 = M := rfl
    rw [hM_def] at heq
    have hdiff :
        M * (Polynomial.C t * (K_quot - K₀)) =
          (Polynomial.C t * d + Polynomial.C (Q / 2) * onesPoly N)
            - (Polynomial.C Q * y + s) := by
      calc M * (Polynomial.C t * (K_quot - K₀))
          = (Polynomial.C Q * y + s + Polynomial.C t * M * K_quot)
              - (Polynomial.C Q * y + s) - Polynomial.C t * M * K₀ := by ring
        _ = (Polynomial.C t * P_sum + Polynomial.C (Q / 2) * onesPoly N)
              - (Polynomial.C Q * y + s) - Polynomial.C t * M * K₀ := by rw [← heq]
        _ = (Polynomial.C t * (d + M * K₀) + Polynomial.C (Q / 2) * onesPoly N)
              - (Polynomial.C Q * y + s) - Polynomial.C t * M * K₀ := by rw [hdiv_id]
        _ = (Polynomial.C t * d + Polynomial.C (Q / 2) * onesPoly N)
              - (Polynomial.C Q * y + s) := by ring
    have hhigh_zero : ∀ j ≥ N, (M * (Polynomial.C t * (K_quot - K₀))).coeff j = 0 := by
      intro j hj
      rw [hdiff]
      have hd0 : d.coeff j = 0 := coeff_modByMonic_X_pow_add_one_eq_zero hN P_sum hj
      have hones0 : (onesPoly N).coeff j = 0 := by simp [Nat.not_lt.mpr hj]
      simp [hd0, hones0, hy j hj, hs j hj]
    have hR0 : Polynomial.C t * (K_quot - K₀) = 0 :=
      eq_zero_of_X_pow_add_one_mul_coeff_zero hN hhigh_zero
    have hK : K_quot = K₀ := by
      apply sub_eq_zero.mp
      ext k
      have hk := congrArg (fun p => p.coeff k) hR0
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_zero, mul_eq_zero] at hk
      exact hk.resolve_left ht
    have hlow_poly :
        Polynomial.C t * d + Polynomial.C (Q / 2) * onesPoly N = Polynomial.C Q * y + s := by
      rw [hR0, mul_zero] at hdiff
      exact sub_eq_zero.mp hdiff.symm
    refine ⟨hK, hy, hs, fun j hj => ?_⟩
    have hcj := congrArg (fun p => p.coeff j) hlow_poly
    have hones1 : (onesPoly N).coeff j = 1 := by simp [hj]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hones1, mul_one] at hcj
    obtain ⟨hs0, hsQ⟩ := hs_range j hj
    have h_ediv : (t * d.coeff j + Q / 2) / Q = y.coeff j := by
      have h_eq : t * d.coeff j + Q / 2 = s.coeff j + y.coeff j * Q := by linarith
      rw [h_eq, Int.add_mul_ediv_right _ _ (ne_of_gt hQ), Int.ediv_eq_zero_of_lt hs0 hsQ, zero_add]
    have h_emod : (t * d.coeff j + Q / 2) % Q = s.coeff j := by
      have h_eq : t * d.coeff j + Q / 2 = s.coeff j + y.coeff j * Q := by linarith
      rw [h_eq, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hs0 hsQ]
    exact ⟨h_ediv.symm, h_emod.symm⟩
  · rintro ⟨rfl, hy, hs, hys⟩
    refine ⟨hy, hs, ?_, ?_⟩
    · intro j hj
      rw [(hys j hj).2]
      exact ⟨Int.emod_nonneg _ (ne_of_gt hQ), Int.emod_lt_of_pos _ hQ⟩
    · set d := P_sum %ₘ M
      have hlow_poly :
          Polynomial.C t * d + Polynomial.C (Q / 2) * onesPoly N = Polynomial.C Q * y + s := by
        ext j
        by_cases hj : j < N
        · obtain ⟨hyj, hsj⟩ := hys j hj
          have hones1 : (onesPoly N).coeff j = 1 := by simp [hj]
          simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hones1, mul_one, hyj, hsj]
          exact (Int.mul_ediv_add_emod (t * d.coeff j + Q / 2) Q).symm
        · have hjN : j ≥ N := Nat.le_of_not_lt hj
          have hd0 : d.coeff j = 0 := coeff_modByMonic_X_pow_add_one_eq_zero hN P_sum hjN
          have hones0 : (onesPoly N).coeff j = 0 := by simp [hj]
          simp [hd0, hones0, hy j hjN, hs j hjN]
      have h1 : (Finset.range N).sum (fun j => (Polynomial.X : Polynomial ℤ) ^ j) = onesPoly N := rfl
      have hM_def : (Polynomial.X : Polynomial ℤ) ^ N + 1 = M := rfl
      rw [h1, hM_def]
      calc Polynomial.C t * P_sum + Polynomial.C (Q / 2) * onesPoly N
          = Polynomial.C t * (d + M * (P_sum /ₘ M)) + Polynomial.C (Q / 2) * onesPoly N := by
              rw [hdiv_id]
        _ = (Polynomial.C t * d + Polynomial.C (Q / 2) * onesPoly N)
              + Polynomial.C t * M * (P_sum /ₘ M) := by ring
        _ = Polynomial.C Q * y + s + Polynomial.C t * M * (P_sum /ₘ M) := by rw [hlow_poly]

/-- Degree-bounded specialization of `hoistedRescaleCert_iff`: when `y` and `s` already sit on the
`N`-coefficient carrier (`coeff j = 0` for `j ≥ N`), `HoistedRescaleCert` holds iff `K_quot` is
`divByMonic` and every `j < N` matches the Euclidean quotient and remainder. -/
theorem hoistedRescaleCert_iff_of_deg_lt {N : ℕ} {Q t : ℤ}
    (hN : 0 < N) (hQ : 0 < Q) (ht : t ≠ 0)
    {P_sum y s K_quot : Polynomial ℤ}
    (hy : ∀ j ≥ N, y.coeff j = 0) (hs : ∀ j ≥ N, s.coeff j = 0) :
    HoistedRescaleCert N Q t P_sum y s K_quot ↔
      K_quot = P_sum /ₘ (Polynomial.X ^ N + 1) ∧
      (∀ j < N,
        y.coeff j = (t * (P_sum %ₘ (Polynomial.X ^ N + 1)).coeff j + Q / 2) / Q ∧
        s.coeff j = (t * (P_sum %ₘ (Polynomial.X ^ N + 1)).coeff j + Q / 2) % Q) := by
  rw [hoistedRescaleCert_iff hN hQ ht]
  exact ⟨fun ⟨hK, _, _, hys⟩ => ⟨hK, hys⟩, fun ⟨hK, hys⟩ => ⟨hK, hy, hs, hys⟩⟩

/-- **Full Witness Uniqueness (`hoistedRescaleCert_unique`):** for `N > 0, Q > 0, t ≠ 0`, at most
one triple `(y, s, K_quot)` of polynomials can satisfy `HoistedRescaleCert N Q t P_sum`. -/
theorem hoistedRescaleCert_unique {N : ℕ} {Q t : ℤ}
    (hN : 0 < N) (hQ : 0 < Q) (ht : t ≠ 0)
    {P_sum y₁ s₁ K₁ y₂ s₂ K₂ : Polynomial ℤ}
    (h₁ : HoistedRescaleCert N Q t P_sum y₁ s₁ K₁)
    (h₂ : HoistedRescaleCert N Q t P_sum y₂ s₂ K₂) :
    y₁ = y₂ ∧ s₁ = s₂ ∧ K₁ = K₂ := by
  rw [hoistedRescaleCert_iff hN hQ ht] at h₁ h₂
  obtain ⟨hK₁, hy₁, hs₁, hys₁⟩ := h₁
  obtain ⟨hK₂, hy₂, hs₂, hys₂⟩ := h₂
  refine ⟨Polynomial.ext fun j => ?_, Polynomial.ext fun j => ?_, hK₁.trans hK₂.symm⟩
  · by_cases hj : j < N
    · exact (hys₁ j hj).1.trans (hys₂ j hj).1.symm
    · exact (hy₁ j (Nat.le_of_not_lt hj)).trans (hy₂ j (Nat.le_of_not_lt hj)).symm
  · by_cases hj : j < N
    · exact (hys₁ j hj).2.trans (hys₂ j hj).2.symm
    · exact (hs₁ j (Nat.le_of_not_lt hj)).trans (hs₂ j (Nat.le_of_not_lt hj)).symm

/-! ### Satisfying Witness (`N = 2`) & `Q = 31, t = 4` `Hole B` Falsifier Tooth -/

/-- **Satisfying Witness (`hoistedRescaleCert_witness_N2`):**
At `N = 2, Q = 31, t = 4`, the degree-2 unreduced product sum `P_sum = 32 + 10·X + 5·X²` wraps
negacyclically by `K_quot = 5` to `d = 27 + 10·X`, inhabiting `HoistedRescaleCert` with
`y = 3 + X` (`4·27 + 15 = 31·3 + 30`, `4·10 + 15 = 31·1 + 24`) and `s = 30 + 24·X`. -/
theorem hoistedRescaleCert_witness_N2 :
    let P_sum : Polynomial ℤ := C 32 + C 10 * X + C 5 * X ^ 2
    let y : Polynomial ℤ := C 3 + X
    let s : Polynomial ℤ := C 30 + C 24 * X
    let K_quot : Polynomial ℤ := C 5
    K_quot ≠ 0 ∧ HoistedRescaleCert 2 31 4 P_sum y s K_quot := by
  refine ⟨by simp, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases j with _ | _ | j
    · omega
    · omega
    · simp [Polynomial.coeff_X]
  · intro j hj
    rcases j with _ | _ | j
    · omega
    · omega
    · simp [Polynomial.coeff_X]
  · intro j hj
    rcases j with _ | _ | j
    · simp [Polynomial.coeff_X]
    · simp [Polynomial.coeff_X]
    · omega
  · ext k
    rcases k with _ | _ | _ | k <;>
      simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one, pow_two]

/-- Buggy mod-`Q`-only polynomial rescale check: checking the `Hole B` polynomial identity only
modulo `Q` (coefficientwise `% Q = 0`) while checking `0 ≤ s_j < Q`. Because `Q · y` vanishes
modulo `Q`, any forged `y_forge` passes! -/
def ModQPolyRescaleCheck (N : ℕ) (Q t : ℤ) (P_sum y s K_quot : Polynomial ℤ) : Prop :=
  (∀ j ≥ N, y.coeff j = 0) ∧
  (∀ j ≥ N, s.coeff j = 0) ∧
  (∀ j < N, 0 ≤ s.coeff j ∧ s.coeff j < Q) ∧
  (∀ j, ((Polynomial.C t * P_sum
      + Polynomial.C (Q / 2) * (Finset.range N).sum (fun k => Polynomial.X ^ k)
      - (Polynomial.C Q * y + s + Polynomial.C t * (Polynomial.X ^ N + 1) * K_quot)).coeff j) % Q = 0)

/-- **`Q = 31, t = 4` `Hole B` Alias Falsifier Tooth (`holeB_modQ_alias_falsifier`):**
Mechanizes `rescale_certificates.py`'s `Q = 31, t = 4` attack (`z_true = 32` vs `z_alias = 1`):
1. `z_true = 32` and `z_alias = 1` have the SAME residue modulo `Q = 31` (`32 % 31 = 1 % 31 = 1`),
   yet their true BEHZ rescaled outputs DIFFER modulo `31` (`out(32) = 4` vs `out(1) = 0`);
2. On the true integer input `P_true = C 32` (`N = 2`), the honest certificate pins `y_true = C 4`
   (`s_true = C 19 + C 15 · X`, `K = 0`);
3. A mod-`Q`-only check (`ModQPolyRescaleCheck`) **ACCEPTS** the forged output `y_forge = 0` on
   `P_true = C 32` (with the exact same `s_true` and `K = 0`), whereas **`HoistedRescaleCert`
   REFUSES `y_forge = 0` for EVERY `s` and `K_quot` in `ℤ[X]`**! -/
theorem holeB_modQ_alias_falsifier :
    let Q : ℤ := 31
    let t : ℤ := 4
    let z_true : ℤ := 32
    let z_alias : ℤ := 1
    let P_true : Polynomial ℤ := C z_true
    let y_true : Polynomial ℤ := C 4
    let y_forge : Polynomial ℤ := 0
    let s_true : Polynomial ℤ := C 19 + C 15 * X
    -- (1) Same mod-Q residue, distinct rescaled outputs (4 vs 0):
    (z_true % Q = z_alias % Q ∧
      ((t * z_true + Q / 2) / Q) % Q = 4 ∧
      ((t * z_alias + Q / 2) / Q) % Q = 0) ∧
    -- (2) Honest integer certificate holds with y_true = C 4:
    HoistedRescaleCert 2 Q t P_true y_true s_true 0 ∧
    -- (3) Mod-Q-only check ACCEPTS forged output y_forge = 0 on P_true = C 32:
    ModQPolyRescaleCheck 2 Q t P_true y_forge s_true 0 ∧
    -- (4) HoistedRescaleCert REFUSES y_forge = 0 for EVERY s and K_quot:
    (∀ s K_quot : Polynomial ℤ, ¬ HoistedRescaleCert 2 Q t P_true y_forge s K_quot) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases j with _ | _ | j
      · omega
      · omega
      · simp
    · intro j hj
      rcases j with _ | _ | j
      · omega
      · omega
      · simp [Polynomial.coeff_X]
    · intro j hj
      rcases j with _ | _ | j
      · simp [Polynomial.coeff_X]
      · simp [Polynomial.coeff_X]
      · omega
    · ext k
      rcases k with _ | _ | _ | k <;>
        simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one, pow_two]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j _; simp
    · intro j hj
      rcases j with _ | _ | j
      · omega
      · omega
      · simp [Polynomial.coeff_X]
    · intro j hj
      rcases j with _ | _ | j
      · simp [Polynomial.coeff_X]
      · simp [Polynomial.coeff_X]
      · omega
    · intro j
      rcases j with _ | _ | j
      · simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one]
      · simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one]
      · simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one]
  · intro s K_quot hcert
    have hiff := (hoistedRescaleCert_iff (N := 2) (Q := 31) (t := 4)
      (by decide) (by decide) (by decide) (C 32) 0 s K_quot).mp hcert
    have hy0 := (hiff.2.2.2 0 (by decide)).1
    have hmod : (C (32 : ℤ) %ₘ ((Polynomial.X : Polynomial ℤ) ^ 2 + 1)) = C 32 := by
      apply (Polynomial.modByMonic_eq_self_iff (monic_X_pow_add_one (N := 2) (by decide))).mpr
      have hdegM : ((Polynomial.X : Polynomial ℤ) ^ 2 + 1).degree = 2 := by
        have hM := monic_X_pow_add_one (N := 2) (by decide)
        have hnd : ((Polynomial.X : Polynomial ℤ) ^ 2 + 1).natDegree = 2 := by
          have h1 := Polynomial.natDegree_X_pow_add_C (n := 2) (r := (1 : ℤ))
          simp at h1 ⊢
        rw [Polynomial.degree_eq_natDegree hM.ne_zero, hnd]
        rfl
      rw [hdegM]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
    rw [hmod] at hy0
    simp at hy0

/-! ## Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Theory.Bfv.sumMulPhase_singleton' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms sumMulPhase_singleton
/-- info: 'Minidregg.Theory.Bfv.sumMulPhase_encrypt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumMulPhase_encrypt_eq
/-- info: 'Minidregg.Theory.Bfv.sumMulPhase_noise_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumMulPhase_noise_le
/-- info: 'Minidregg.Theory.Bfv.deployed_hoisted64_margin_holds' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_hoisted64_margin_holds
/-- info: 'Minidregg.Theory.Bfv.eager_vs_hoisted_rounding_gap' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms eager_vs_hoisted_rounding_gap
/-- info: 'Minidregg.Theory.Bfv.hoistedRescaleCert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_iff
/-- info: 'Minidregg.Theory.Bfv.hoistedRescaleCert_iff_of_deg_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_iff_of_deg_lt
/-- info: 'Minidregg.Theory.Bfv.hoistedRescaleCert_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_unique
/-- info: 'Minidregg.Theory.Bfv.hoistedRescaleCert_witness_N2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_witness_N2
/-- info: 'Minidregg.Theory.Bfv.holeB_modQ_alias_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holeB_modQ_alias_falsifier

end Minidregg.Theory.Bfv
