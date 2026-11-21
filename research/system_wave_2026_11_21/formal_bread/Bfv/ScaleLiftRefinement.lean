/-
# Bfv.ScaleLiftRefinement — `BFVScaleLiftRefinement`, Hoisted Sum-Before-Rescale, and `Hole B` Closure

Closes `VERDICTS.md` §7.5 (`Hole B`, `BFVScaleLiftRefinement`) directly over `breadstuffs`'s actual
`Bfv` carriers (`Bfv.Params`, `Bfv.Rn`, `Bfv.negaMul`, `Bfv.toPoly`, `Bfv.RnsCt`, `Bfv.LimbMulRel`,
`Bfv.rescale`, `Bfv.perLimb_pins_modProd`, `Bfv.fheRs4096`).

## What is proved

1. **Exact integer rescale & `IntScaleCert`:**
   * `ediv_add_half_eq_rescale` — for every `Q > 0` (both even and odd) and `t, z : ℤ`,
     `(t * z + Q / 2) / Q = rescale t Q z`.
   * `intScaleCert_iff` — `IntScaleCert Q t z y s` (`0 ≤ s < Q ∧ t * z + Q / 2 = Q * y + s`)
     uniquely pins `y = rescale t Q z` and `s = (t * z + Q / 2) % Q`.
2. **`BFVScaleLiftRefinement` (`VERDICTS.md` §7.5):**
   * Given a pairwise-coprime extended RNS basis `q_ext : Fin L_ext → ℕ` with product
     `Q_ext = ∏ i, (q_ext i : ℤ)`, bounded operand representatives `NormInfLE a A`, `NormInfLE b B`
     with `(N : ℤ) * A * B < Q_ext / 2`, per-limb `LimbMulRel (q_ext i) a b (z_rns i)` where
     `z_rns i k = z k` and `NormInfLE z ((N : ℤ) * A * B)`, and coefficientwise
     `IntScaleCert Q t (z k) (y k) (s k)` (`0 < Q`):
     `perLimb_pins_modProd` pins `z = negaMul a b` in `ℤ` (NOT merely mod `Q`), and
     `y k = rescale t Q (negaMul a b k)` for every `k : Fin N`.
   * `bfvScaleLiftRefinement_witness` inhabits all premises concretely (`Q_ext = 3 · 5 = 15`,
     `N = 2`, `A = B = 1`, `Q = 31`, `t = 4`).
3. **Fused `d`-Free Polynomial Rescale Certificate (`HoistedRescaleCert`) + `Bfv.Ring` Bridge:**
   * `HoistedRescaleCert`, `hoistedRescaleCert_iff`, `hoistedRescaleCert_iff_of_deg_lt`,
     `hoistedRescaleCert_unique`, `hoistedRescaleCert_witness_N2`.
   * `hoistedRescaleCert_refines_negaMul_sum` — for `P_sum = ∑ c : Fin K, toPoly (a c) * toPoly (b c)`
     (`[NeZero N]`, `0 < Q`, `t ≠ 0`), `HoistedRescaleCert N Q t P_sum y_poly s_poly K_quot` pins
     `∀ k : Fin N, y_poly.coeff (k : ℕ) = rescale t Q (∑ c : Fin K, negaMul (a c) (b c) k)`.
4. **Hoisted Sum-Before-Rescale (`sumMulPhase`) on `Bfv.Params` / `Bfv.fheRs4096`:**
   * `sumMulPhase_singleton`, `sumMulPhase_encrypt_eq`, `sumMulPhase_noise_le`,
     `deployed_hoisted64_margin_holds`, and the constructive rounding-gap tooth
     `eager_vs_hoisted_rounding_gap`.
5. **`Q = 31, t = 4` `1`-vs-`32` (`1·1 = 1` vs `2·16 = 32 ≡ 1 mod 31`) Falsifiers:**
   * `bfvScaleLiftRefinement_modQ_falsifier` (integer / `IntScaleCert` / `negaMul` level) and
     `holeB_modQ_alias_falsifier` (polynomial / `HoistedRescaleCert` level): a mod-`Q`-only check
     accepts forged `y = 0` on `2·16 = 32`, while both `IntScaleCert` and `HoistedRescaleCert`
     refuse `y = 0` for every remainder `s` and quotient `K_quot`.

Pure. Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `#guard`.
-/
import Mathlib.Algebra.Polynomial.Div
import Bfv.Params
import Bfv.Fold
import Bfv.Mul
import Bfv.Ring
import Bfv.CrossLimb

namespace Bfv

open Finset Polynomial

/-! ## 1. Exact Integer Rescale & `IntScaleCert` -/

/-- **Exact equivalence of `⌊(t·z + ⌊Q/2⌋) / Q⌋` and `Bfv.rescale t Q z`** for EVERY `Q > 0`
(both even and odd). -/
theorem ediv_add_half_eq_rescale {Q : ℤ} (hQ : 0 < Q) (t z : ℤ) :
    (t * z + Q / 2) / Q = rescale t Q z := by
  unfold rescale
  set q := (t * z + Q / 2) / Q
  set r := (t * z + Q / 2) % Q
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have h2Q : (0 : ℤ) < 2 * Q := by linarith
  have h2Qne : (2 * Q) ≠ 0 := ne_of_gt h2Q
  have hqr : Q * q + r = t * z + Q / 2 := Int.mul_ediv_add_emod (t * z + Q / 2) Q
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hQne
  have hrQ : r < Q := Int.emod_lt_of_pos _ hQ
  have hQ2 : 2 * (Q / 2) + Q % 2 = Q := Int.mul_ediv_add_emod Q 2
  have hm0 : 0 ≤ Q % 2 := Int.emod_nonneg Q (by decide)
  have hm2 : Q % 2 < 2 := Int.emod_lt_of_pos Q (by decide)
  have hnum : 2 * t * z + Q = (2 * r + Q % 2) + q * (2 * Q) := by linarith
  have hrem0 : 0 ≤ 2 * r + Q % 2 := by omega
  have hrem_lt : 2 * r + Q % 2 < 2 * Q := by omega
  rw [hnum, Int.add_mul_ediv_right _ _ h2Qne, Int.ediv_eq_zero_of_lt hrem0 hrem_lt, zero_add]

/-- **Coefficientwise integer BEHZ rescale certificate (`IntScaleCert`)**: proves in `ℤ` (NOT
modulo `Q`) that `t · z + ⌊Q/2⌋ = Q · y + s` with `0 ≤ s < Q`. -/
def IntScaleCert (Q t z y s : ℤ) : Prop :=
  0 ≤ s ∧ s < Q ∧ t * z + Q / 2 = Q * y + s

/-- **`intScaleCert_iff`**: for `Q > 0`, `IntScaleCert Q t z y s` holds iff `y = rescale t Q z`
and `s = (t * z + Q / 2) % Q`. -/
theorem intScaleCert_iff {Q : ℤ} (hQ : 0 < Q) (t z y s : ℤ) :
    IntScaleCert Q t z y s ↔ y = rescale t Q z ∧ s = (t * z + Q / 2) % Q := by
  have hQne : Q ≠ 0 := ne_of_gt hQ
  constructor
  · rintro ⟨hs0, hsQ, heq⟩
    have hsplit : t * z + Q / 2 = s + y * Q := by linarith
    have hy : (t * z + Q / 2) / Q = y := by
      rw [hsplit, Int.add_mul_ediv_right _ _ hQne, Int.ediv_eq_zero_of_lt hs0 hsQ, zero_add]
    have hs : (t * z + Q / 2) % Q = s := by
      rw [hsplit, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hs0 hsQ]
    rw [ediv_add_half_eq_rescale hQ t z] at hy
    exact ⟨hy.symm, hs.symm⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨Int.emod_nonneg _ hQne, Int.emod_lt_of_pos _ hQ, ?_⟩
    rw [← ediv_add_half_eq_rescale hQ t z]
    exact (Int.mul_ediv_add_emod (t * z + Q / 2) Q).symm

/-! ## 2. `BFVScaleLiftRefinement` (`VERDICTS.md` §7.5) -/

/-- Helper: if `Q_ext ∣ d` and `|d| < Q_ext`, then `d = 0`. -/
private theorem eq_zero_of_dvd_of_abs_lt {Q d : ℤ} (hdvd : Q ∣ d) (habs : |d| < Q) : d = 0 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hQ0 : 0 ≤ Q := le_of_lt (lt_of_le_of_lt (abs_nonneg _) habs)
  rw [abs_mul, abs_of_nonneg hQ0] at habs
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
    have hle : Q * 1 ≤ Q * |m| := mul_le_mul_of_nonneg_left hm1 hQ0
    linarith

/-- **`BFVScaleLiftRefinement` (`VERDICTS.md` §7.5):**
Given:
* a pairwise-coprime extended RNS basis `q_ext : Fin L_ext → ℕ` with product
  `Q_ext = ∏ i, (q_ext i : ℤ)`,
* bounded operand representatives `NormInfLE a A`, `NormInfLE b B` (`0 ≤ A`) whose worst-case
  negacyclic product bound `(N : ℤ) * A * B` fits strictly below `Q_ext / 2`,
* per-limb `LimbMulRel (q_ext i) a b (z_rns i)` where every limb carries the SAME integer
  representative `z_rns i k = z k` with `NormInfLE z ((N : ℤ) * A * B)`, and
* coefficientwise integer rescale certificates `IntScaleCert Q t (z k) (y k) (s k)` (`0 < Q`),

then:
1. `perLimb_pins_modProd` lifts the per-limb congruences to EXACT integer equality
   `z = negaMul a b` in `ℤ` (NOT merely mod `Q`), and
2. every output coefficient is uniquely pinned to `y k = rescale t Q (negaMul a b k)`. -/
theorem BFVScaleLiftRefinement {L_ext N : ℕ}
    (q_ext : Fin L_ext → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (q_ext i) (q_ext j)))
    (a b z y s : Rn N) (z_rns : RnsCt L_ext N) (A B Q t : ℤ)
    (hA : 0 ≤ A)
    (ha : NormInfLE a A) (hb : NormInfLE b B)
    (hQext : (N : ℤ) * A * B < (∏ i : Fin L_ext, (q_ext i : ℤ)) / 2)
    (hz_eq : ∀ i : Fin L_ext, ∀ k : Fin N, z_rns i k = z k)
    (hlimb : ∀ i : Fin L_ext, LimbMulRel (q_ext i) a b (z_rns i))
    (hz_bound : NormInfLE z ((N : ℤ) * A * B))
    (hQ : 0 < Q)
    (hcert : ∀ k : Fin N, IntScaleCert Q t (z k) (y k) (s k)) :
    z = negaMul a b ∧ ∀ k : Fin N, y k = rescale t Q (negaMul a b k) := by
  have hcopZ : Pairwise (fun i j => IsCoprime (q_ext i : ℤ) (q_ext j : ℤ)) :=
    fun i j hij => Nat.isCoprime_iff_coprime.mpr (hcop hij)
  have hprod_bound : NormInfLE (negaMul a b) ((N : ℤ) * A * B) := negaMul_normInf_le ha hb hA
  have hz_eq_nega : z = negaMul a b := by
    funext k
    have hdvd_i : ∀ i : Fin L_ext, (q_ext i : ℤ) ∣ (negaMul a b k - z k) := by
      intro i
      have hrel := hlimb i k
      rw [hz_eq i k] at hrel
      exact Int.modEq_iff_dvd.mp hrel
    have hdvd_all : (∏ i : Fin L_ext, (q_ext i : ℤ)) ∣ (negaMul a b k - z k) :=
      perLimb_pins_modProd (fun i => (q_ext i : ℤ)) hcopZ (z k) (negaMul a b k) hdvd_i
    have habs_diff : |negaMul a b k - z k| < ∏ i : Fin L_ext, (q_ext i : ℤ) := by
      have htri : |negaMul a b k - z k| ≤ |negaMul a b k| + |z k| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (negaMul a b k) (-z k)
      have h1 := hprod_bound k
      have h2 := hz_bound k
      have htwice : 2 * ((N : ℤ) * A * B) < ∏ i : Fin L_ext, (q_ext i : ℤ) := by omega
      linarith
    have hzero : negaMul a b k - z k = 0 := eq_zero_of_dvd_of_abs_lt hdvd_all habs_diff
    linarith
  refine ⟨hz_eq_nega, fun k => ?_⟩
  have hy := ((intScaleCert_iff hQ t (z k) (y k) (s k)).mp (hcert k)).1
  rw [hz_eq_nega] at hy
  exact hy

/-- **Non-vacuity witness for `BFVScaleLiftRefinement`**: at `L_ext = 2`, `q_ext = (3, 5)`
(`Q_ext = 15`), `N = 2`, `a = b = (1, 1)` (`A = B = 1`, `2·1·1 = 2 < 7 = 15/2`), `Q = 31`,
`t = 4`, all premises of `BFVScaleLiftRefinement` are jointly inhabited and fire cleanly. -/
theorem bfvScaleLiftRefinement_witness :
    let a : Rn 2 := fun _ => 1
    let b : Rn 2 := fun _ => 1
    let z : Rn 2 := fun k => if k = 0 then 0 else 2
    let y : Rn 2 := fun _ => 0
    z = negaMul a b ∧ ∀ k : Fin 2, y k = rescale 4 31 (negaMul a b k) := by
  apply BFVScaleLiftRefinement exhibitQ
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [exhibitQ] at hij ⊢ <;> norm_num)
    (fun _ => 1) (fun _ => 1) (fun k => if k = 0 then 0 else 2) (fun _ => 0)
    (fun k => if k = 0 then 15 else 23) (fun _ k => if k = 0 then 0 else 2) 1 1 31 4
    (by decide)
    (fun k => by fin_cases k <;> decide)
    (fun k => by fin_cases k <;> decide)
    (by decide)
    (fun _ _ => rfl)
    (fun i => by fin_cases i <;> decide)
    (fun k => by fin_cases k <;> decide)
    (by decide)
    (fun k => by fin_cases k <;> (unfold IntScaleCert; decide))

/-! ## 3. Fused `d`-Free Polynomial Rescale Certificate (`HoistedRescaleCert`) + `Bfv.Ring` Bridge -/

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
without materializing `d`:
* `y` and `s` vanish in degree `≥ N`,
* `0 ≤ s.coeff j < Q` for every `j < N`, and
* `t · P_sum + (Q / 2) · ∑_{j<N} X^j = Q · y + s + t · (X^N + 1) · K_quot`. -/
def HoistedRescaleCert (N : ℕ) (Q t : ℤ) (P_sum y s K_quot : Polynomial ℤ) : Prop :=
  (∀ j ≥ N, y.coeff j = 0) ∧
  (∀ j ≥ N, s.coeff j = 0) ∧
  (∀ j < N, 0 ≤ s.coeff j ∧ s.coeff j < Q) ∧
  Polynomial.C t * P_sum + Polynomial.C (Q / 2) * (Finset.range N).sum (fun j => Polynomial.X ^ j) =
    Polynomial.C Q * y + s + Polynomial.C t * (Polynomial.X ^ N + 1) * K_quot

/-- Key degree-separation lemma: if `((X^N + 1) * R).coeff j = 0` for all `j ≥ N` (`N > 0`),
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

/-- **Exact characterization of `HoistedRescaleCert` (`hoistedRescaleCert_iff`)**:
for `N > 0, Q > 0, t ≠ 0`, `HoistedRescaleCert N Q t P_sum y s K_quot` holds iff `K_quot` is
`divByMonic`, `y` and `s` vanish at degrees `≥ N`, and for all `j < N`, `y.coeff j` and
`s.coeff j` equal the exact Euclidean quotient (`= rescale t Q`) and remainder mod `Q`. -/
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

/-- **Full witness uniqueness (`hoistedRescaleCert_unique`)**: at most one `(y, s, K_quot)` triple
satisfies `HoistedRescaleCert N Q t P_sum`. -/
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

/-- **Satisfying witness (`hoistedRescaleCert_witness_N2`)**: concrete `N = 2, Q = 31, t = 4`
certificate with nonzero negacyclic wrap quotient `K_quot = 5`. -/
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

/-- Every coefficient of `toPoly a` at index `j ≥ N` is zero. -/
theorem toPoly_coeff_eq_zero_of_ge {N : ℕ} (a : Rn N) {j : ℕ} (hj : j ≥ N) :
    (toPoly a).coeff j = 0 := by
  unfold toPoly
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (by omega), mul_zero]

/-- `toPoly` distributes over finite sums of `Rn N` elements. -/
theorem toPoly_sum {N K : ℕ} (f : Fin K → Rn N) :
    toPoly (fun k => ∑ c : Fin K, f c k) = ∑ c : Fin K, toPoly (f c) := by
  unfold toPoly
  have h1 : ∀ i : Fin N,
      Polynomial.C (∑ c : Fin K, f c i) * Polynomial.X ^ (i : ℕ) =
        ∑ c : Fin K, Polynomial.C (f c i) * Polynomial.X ^ (i : ℕ) := by
    intro i
    rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]

/-- **`P_sum %ₘ (X^N + 1)` equals `toPoly (∑ c, negaMul (a c) (b c))`**, bridging `Polynomial ℤ`
division by `X^N + 1` directly to `Bfv.Ring.negaMul`. -/
theorem modByMonic_sum_toPoly_mul_eq {N K : ℕ} [NeZero N] (a b : Fin K → Rn N) :
    (∑ c : Fin K, toPoly (a c) * toPoly (b c)) %ₘ (Polynomial.X ^ N + 1) =
      toPoly (fun k => ∑ c : Fin K, negaMul (a c) (b c) k) := by
  set M : Polynomial ℤ := Polynomial.X ^ N + 1
  set P_sum : Polynomial ℤ := ∑ c : Fin K, toPoly (a c) * toPoly (b c)
  set S_rn : Rn N := fun k => ∑ c : Fin K, negaMul (a c) (b c) k
  have hdvd : M ∣ (P_sum - toPoly S_rn) := by
    rw [toPoly_sum, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun c _ => negaMul_toPoly_dvd (a c) (b c)
  obtain ⟨q, hq⟩ := hdvd
  have hdiv : P_sum %ₘ M + M * (P_sum /ₘ M) = P_sum := Polynomial.modByMonic_add_div P_sum M
  have hdiff : M * (q - P_sum /ₘ M) = P_sum %ₘ M - toPoly S_rn := by
    calc M * (q - P_sum /ₘ M)
        = M * q - M * (P_sum /ₘ M) := by ring
      _ = (P_sum - toPoly S_rn) - M * (P_sum /ₘ M) := by rw [← hq]
      _ = (P_sum %ₘ M + M * (P_sum /ₘ M) - toPoly S_rn) - M * (P_sum /ₘ M) := by rw [hdiv]
      _ = P_sum %ₘ M - toPoly S_rn := by ring
  have hN : 0 < N := NeZero.pos N
  have hhigh : ∀ j ≥ N, (M * (q - P_sum /ₘ M)).coeff j = 0 := by
    intro j hj
    rw [hdiff, Polynomial.coeff_sub, coeff_modByMonic_X_pow_add_one_eq_zero hN P_sum hj,
      toPoly_coeff_eq_zero_of_ge S_rn hj, sub_self]
  have hq0 : q - P_sum /ₘ M = 0 := eq_zero_of_X_pow_add_one_mul_coeff_zero hN hhigh
  rw [hq0, mul_zero] at hdiff
  exact sub_eq_zero.mp hdiff.symm

/-- **Bridge Theorem (`hoistedRescaleCert_refines_negaMul_sum`):**
For `P_sum = ∑ c : Fin K, toPoly (a c) * toPoly (b c)` (`[NeZero N]`, `0 < Q`, `t ≠ 0`),
`HoistedRescaleCert N Q t P_sum y_poly s_poly K_quot` pins every coefficient `k : Fin N` of
`y_poly` to `rescale t Q (∑ c : Fin K, negaMul (a c) (b c) k)`. -/
theorem hoistedRescaleCert_refines_negaMul_sum {N K : ℕ} [NeZero N] {Q t : ℤ}
    (hQ : 0 < Q) (ht : t ≠ 0) (a b : Fin K → Rn N) (y_poly s_poly K_quot : Polynomial ℤ)
    (hcert : HoistedRescaleCert N Q t
      (∑ c : Fin K, toPoly (a c) * toPoly (b c)) y_poly s_poly K_quot) :
    ∀ k : Fin N, y_poly.coeff (k : ℕ) = rescale t Q (∑ c : Fin K, negaMul (a c) (b c) k) := by
  have hiff := (hoistedRescaleCert_iff (NeZero.pos N) hQ ht _ y_poly s_poly K_quot).mp hcert
  intro k
  have hy := (hiff.2.2.2 (k : ℕ) k.isLt).1
  rw [modByMonic_sum_toPoly_mul_eq a b, toPoly_coeff] at hy
  rw [hy, ediv_add_half_eq_rescale hQ]

/-! ## 4. Hoisted Sum-Before-Rescale (`sumMulPhase`) on `Bfv.Params` / `Bfv.fheRs4096` -/

/-- **Hoisted BFV dot-product rescale (`sumMulPhase`)**: accumulate all unrescaled integer phase
products `∑ (p₁ᵢ · p₂ᵢ)` in `ℤ` first, then apply a single `round(t · (∑ p₁ᵢ p₂ᵢ) / q)`. -/
def sumMulPhase (P : Params) (ps : List (ℤ × ℤ)) : ℤ :=
  (2 * (P.t : ℤ) * (ps.map (fun x => x.1 * x.2)).sum + P.q) / (2 * (P.q : ℤ))

/-- **Eager per-product rescale sum**: rescaling each pair individually via `mulPhase`. -/
def eagerSumMulPhase (P : Params) (ps : List (ℤ × ℤ)) : ℤ :=
  (ps.map (fun x => mulPhase P x.1 x.2)).sum

/-- At length `1`, `sumMulPhase` reduces identically to `Bfv.mulPhase`. -/
theorem sumMulPhase_singleton (P : Params) (p₁ p₂ : ℤ) :
    sumMulPhase P [(p₁, p₂)] = mulPhase P p₁ p₂ := by
  simp [sumMulPhase, mulPhase]

/-- Encrypt a list of `((m₁, e₁), (m₂, e₂))` operand descriptors into phase pairs. -/
def encPhasePairs (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) : List (ℤ × ℤ) :=
  os.map (fun o => ((P.Δ : ℤ) * o.1.1 + o.1.2, (P.Δ : ℤ) * o.2.1 + o.2.2))

/-- Hoisted dot-product ciphertext before relinearization. -/
def hoistedDotCt (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) : Ct P :=
  ⟨sumMulPhase P (encPhasePairs P os)⟩

/-- Summed sub-`q` multiplicative remainder across a list of encrypted operand pairs. -/
def sumMulRemainder (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) : ℤ :=
  (os.map (fun o => mulRemainder P o.1.1 o.2.1 o.1.2 o.2.2)).sum

/-- Unrounded `t`-scaled product sum identity across `K` encrypted pairs. -/
theorem scaled_encPhasePairs_sum_eq (P : Params) (os : List ((ℕ × ℤ) × (ℕ × ℤ))) :
    (P.t : ℤ) * ((encPhasePairs P os).map (fun x => x.1 * x.2)).sum =
      (P.q : ℤ) * ((P.Δ : ℤ) * (((os.map (fun o => o.1.1 * o.2.1)).sum : ℕ) : ℤ)
        + (os.map (fun o => (o.1.1 : ℤ) * o.2.2 + (o.2.1 : ℤ) * o.1.2)).sum)
      + sumMulRemainder P os := by
  have hQeq : (P.q : ℤ) = (P.Δ : ℤ) * (P.t : ℤ) + (P.r : ℤ) := by exact_mod_cast P.q_eq
  induction os with
  | nil => simp [encPhasePairs, sumMulRemainder]
  | cons o os ih =>
      simp only [encPhasePairs, sumMulRemainder, List.map_cons, List.sum_cons,
        Nat.cast_add, Nat.cast_mul] at ih ⊢
      rw [mul_add, ih]
      unfold mulRemainder
      rw [hQeq]
      ring

/-- **Exact `K`-pair hoisted multiplicative phase decomposition (`sumMulPhase_encrypt_eq`)**. -/
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

/-- **Sound worst-case noise bound for a `K`-term hoisted dot-product + ONE relinearization**:
rounding slack is `+ 1` total (not `+ K`), and `Bks` is paid once. -/
def hoistedMulNoiseBound (P : Params) (K : ℕ) (M₁ M₂ B₁ B₂ Bks : ℤ) : ℤ :=
  (K : ℤ) * (M₁ * B₂ + M₂ * B₁)
    + ((K : ℤ) * ((P.t : ℤ) * (B₁ * B₂) + (P.r : ℤ) * (P.Δ : ℤ) * (M₁ * M₂)
        + (P.r : ℤ) * (M₁ * B₂ + M₂ * B₁))) / (P.q : ℤ)
    + 1 + Bks

/-- **Hoisted dot-product noise bound (`sumMulPhase_noise_le`)**. -/
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

/-- Deployed `fheRs4096` witness: `K = 64` hoisted column-block products stay safely inside the
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

/-- Four honest encrypted pairs of `(m₁ = 0, m₂ = 0)` with noises `(e₁ = 1, e₂ = 4)`. -/
def gapEncPairs : List ((ℕ × ℤ) × (ℕ × ℤ)) :=
  List.replicate 4 ((0, 1), (0, 4))

/-- **Witness + Falsifier Tooth (`eager_vs_hoisted_rounding_gap`)**:
eager `mulPhase` summation deviates from hoisted `sumMulPhase` by `4 - 2 = 2` and silently
mis-decrypts `0` as `1`, whereas `sumMulPhase` decrypts to the exact clear dot-product `0`. -/
theorem eager_vs_hoisted_rounding_gap :
    let ps := encPhasePairs gapParams gapEncPairs
    ps.length = 4 ∧
    eagerSumMulPhase gapParams ps = 4 ∧
    sumMulPhase gapParams ps = 2 ∧
    eagerSumMulPhase gapParams ps - sumMulPhase gapParams ps ≥ 2 ∧
    decryptPhase gapParams (sumMulPhase gapParams ps) = 0 ∧
    decryptPhase gapParams (eagerSumMulPhase gapParams ps) = 1 := by
  decide

/-! ## 5. `Q = 31, t = 4` `1`-vs-`32` (`1·1 = 1` vs `2·16 = 32 ≡ 1 mod 31`) Falsifiers -/

/-- Buggy mod-`Q`-only integer rescale check: reduces `t · z + Q / 2 - (Q · y + s)` mod `Q`,
erasing `Q · y` completely. -/
def ModQIntScaleCheck (Q t z y s : ℤ) : Prop :=
  0 ≤ s ∧ s < Q ∧ (t * z + Q / 2 - (Q * y + s)) % Q = 0

/-- **`Q = 31, t = 4` `1`-vs-`32` Integer Falsifier (`bfvScaleLiftRefinement_modQ_falsifier`)**:
Over `Rn 1` (`1·1 = 1` vs `2·16 = 32`):
1. `negaMul (fun _ => 2) (fun _ => 16) 0 = 32` and `negaMul (fun _ => 1) (fun _ => 1) 0 = 1`
   agree modulo `Q = 31`, yet scale to `4` vs `0`;
2. `ModQIntScaleCheck 31 4 32 0 19` **ACCEPTS** forged output `y = 0` on `2·16 = 32`;
3. `IntScaleCert 31 4 32 0 s` **REFUSES** `y = 0` for EVERY remainder `s : ℤ`. -/
theorem bfvScaleLiftRefinement_modQ_falsifier :
    let Q : ℤ := 31
    let t : ℤ := 4
    let a₁ : Rn 1 := fun _ => 1
    let b₁ : Rn 1 := fun _ => 1
    let a₂ : Rn 1 := fun _ => 2
    let b₂ : Rn 1 := fun _ => 16
    negaMul a₁ b₁ 0 = 1 ∧
    negaMul a₂ b₂ 0 = 32 ∧
    negaMul a₂ b₂ 0 % Q = negaMul a₁ b₁ 0 % Q ∧
    rescale t Q (negaMul a₁ b₁ 0) = 0 ∧
    rescale t Q (negaMul a₂ b₂ 0) = 4 ∧
    ModQIntScaleCheck Q t (negaMul a₂ b₂ 0) 0 19 ∧
    (∀ s : ℤ, ¬ IntScaleCert Q t (negaMul a₂ b₂ 0) 0 s) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by unfold ModQIntScaleCheck; decide, ?_⟩
  intro s hcert
  have hy := ((intScaleCert_iff (Q := 31) (by decide) 4 (negaMul (fun _ : Fin 1 => (2 : ℤ))
    (fun _ : Fin 1 => (16 : ℤ)) 0) 0 s).mp hcert).1
  have h4 : rescale 4 31 (negaMul (fun _ : Fin 1 => (2 : ℤ)) (fun _ : Fin 1 => (16 : ℤ)) 0) = 4 := by
    decide
  rw [h4] at hy
  omega

/-- Buggy mod-`Q`-only polynomial rescale check: checking the `Hole B` polynomial identity only
modulo `Q` erases `Q · y` and accepts forged outputs. -/
def ModQPolyRescaleCheck (N : ℕ) (Q t : ℤ) (P_sum y s K_quot : Polynomial ℤ) : Prop :=
  (∀ j ≥ N, y.coeff j = 0) ∧
  (∀ j ≥ N, s.coeff j = 0) ∧
  (∀ j < N, 0 ≤ s.coeff j ∧ s.coeff j < Q) ∧
  (∀ j, ((Polynomial.C t * P_sum
      + Polynomial.C (Q / 2) * (Finset.range N).sum (fun k => Polynomial.X ^ k)
      - (Polynomial.C Q * y + s + Polynomial.C t * (Polynomial.X ^ N + 1) * K_quot)).coeff j) % Q = 0)

/-- **`Q = 31, t = 4` Polynomial Alias Falsifier (`holeB_modQ_alias_falsifier`)**:
1. `z_true = 32` and `z_alias = 1` have the same residue mod `31`, yet scale to `4` vs `0`;
2. On `P_true = C 32` (`N = 2`), the honest `HoistedRescaleCert` holds with `y_true = C 4`;
3. `ModQPolyRescaleCheck` **ACCEPTS** forged output `y_forge = 0` on `P_true = C 32`;
4. `HoistedRescaleCert` **REFUSES** `y_forge = 0` for EVERY `s, K_quot : Polynomial ℤ`. -/
theorem holeB_modQ_alias_falsifier :
    let Q : ℤ := 31
    let t : ℤ := 4
    let z_true : ℤ := 32
    let z_alias : ℤ := 1
    let P_true : Polynomial ℤ := C z_true
    let y_true : Polynomial ℤ := C 4
    let y_forge : Polynomial ℤ := 0
    let s_true : Polynomial ℤ := C 19 + C 15 * X
    (z_true % Q = z_alias % Q ∧
      ((t * z_true + Q / 2) / Q) % Q = 4 ∧
      ((t * z_alias + Q / 2) / Q) % Q = 0) ∧
    HoistedRescaleCert 2 Q t P_true y_true s_true 0 ∧
    ModQPolyRescaleCheck 2 Q t P_true y_forge s_true 0 ∧
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
      rcases j with _ | _ | j <;>
        simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one]
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

/-! ## 6. Axiom Hygiene (`#assert_all_clean` + `#guard_msgs in #print axioms`) -/

#assert_all_clean [
  Bfv.ediv_add_half_eq_rescale,
  Bfv.intScaleCert_iff,
  Bfv.BFVScaleLiftRefinement,
  Bfv.bfvScaleLiftRefinement_witness,
  Bfv.hoistedRescaleCert_iff,
  Bfv.hoistedRescaleCert_unique,
  Bfv.hoistedRescaleCert_witness_N2,
  Bfv.modByMonic_sum_toPoly_mul_eq,
  Bfv.hoistedRescaleCert_refines_negaMul_sum,
  Bfv.sumMulPhase_singleton,
  Bfv.sumMulPhase_encrypt_eq,
  Bfv.sumMulPhase_noise_le,
  Bfv.deployed_hoisted64_margin_holds,
  Bfv.eager_vs_hoisted_rounding_gap,
  Bfv.bfvScaleLiftRefinement_modQ_falsifier,
  Bfv.holeB_modQ_alias_falsifier
]

/-- info: 'Bfv.ediv_add_half_eq_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ediv_add_half_eq_rescale
/-- info: 'Bfv.intScaleCert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intScaleCert_iff
/-- info: 'Bfv.BFVScaleLiftRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BFVScaleLiftRefinement
/-- info: 'Bfv.bfvScaleLiftRefinement_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bfvScaleLiftRefinement_witness
/-- info: 'Bfv.hoistedRescaleCert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_iff
/-- info: 'Bfv.hoistedRescaleCert_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_unique
/-- info: 'Bfv.hoistedRescaleCert_witness_N2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_witness_N2
/-- info: 'Bfv.hoistedRescaleCert_refines_negaMul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hoistedRescaleCert_refines_negaMul_sum
/-- info: 'Bfv.sumMulPhase_encrypt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumMulPhase_encrypt_eq
/-- info: 'Bfv.sumMulPhase_noise_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumMulPhase_noise_le
/-- info: 'Bfv.deployed_hoisted64_margin_holds' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_hoisted64_margin_holds
/-- info: 'Bfv.eager_vs_hoisted_rounding_gap' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms eager_vs_hoisted_rounding_gap
/-- info: 'Bfv.bfvScaleLiftRefinement_modQ_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bfvScaleLiftRefinement_modQ_falsifier
/-- info: 'Bfv.holeB_modQ_alias_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holeB_modQ_alias_falsifier

end Bfv
