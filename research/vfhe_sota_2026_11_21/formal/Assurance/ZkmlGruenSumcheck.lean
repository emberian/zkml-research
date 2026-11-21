/-
# `Assurance/ZkmlGruenSumcheck.lean` — Gruen's (`ePrint 2024/108` §3.2) `eq`-Factored Sumcheck Round & Mode-2 Soundness

**Substrate, said out loud: this is Lean-authored protocol assurance.** Composes directly over
`Assurance/ZkmlEinSumcheck.lean` and `Selvage/` (`EqPolynomial`, `Sumcheck`). Zero `sorry`,
zero custom `axiom`, zero `native_decide`, zero `#guard`.

## What this file proves

In `Assurance/ZkmlEinSumcheck.lean`, every shared-free (`F_{≥2}`) round `u` of `EinSumcheck`
sums a degree-`(d + 1)` polynomial `s_u(X)` whose head factor is `Selvage.eqMle`:
  `s_u(X) = eqPrefix · eqLinPoly(r_u)(X) · q_u(X)`,   `deg(eqLinPoly r_u) ≤ 1`, `deg(q_u) ≤ d`.
For two-operand contractions (`d = 2`, covering GQA `tgrd,ngd -> tgrn` and MXFP4 `j`-rounds),
evaluating `s_u` directly as a cubic requires 4 evaluation points (`{0, 1, 2, 3}` or `{0, 1, 2, ∞}`).

Gruen (`ePrint 2024/108` §3.2–3.3 & App. A.3; `ePrint 2025/1117` §5.1) factors out the known
linear `eq` polynomial `ℓ(X) = eqLinPoly r = (1 - r)(1 - X) + r X`:

1. **`eqLinPoly` & `Selvage.eqMle` Factorization (`eqMle_update_eq_eqLinPoly_mul`)**:
   `eqLinPoly r` has `natDegree ≤ 1`, evaluates to `1 - r` at `0` and `r` at `1`, and factors
   `Selvage.eqMle z (Function.update x i t)` into `(eqLinPoly (z i)).eval t` times the `i`-erased
   product. Combined with `quadFromZeroOneInf`, a quadratic quotient `q(X)` (`d = 2`) is uniquely
   determined by `{q(0), q(1), q(∞)}` — so solving `q(1)` from the round sum cuts prover inner
   products from 4 points to **2 points (`{0, ∞}`, a `2×` point cut)**!

2. **Unique `q(1)` Reconstruction (`gruen_q1_unique_of_r_ne_zero`)**:
   Whenever `r ≠ 0`, the round-sum equation `ℓ(0) · q0 + ℓ(1) · q1 = σ` holds **if and only if**
   `q1 = r⁻¹ * (σ - (1 - r) * q0)`.

3. **Falsifier Tooth at `r = 0` (`gruen_r_zero_q1_unconstrained`)**:
   Dropping `r ≠ 0` breaks `q(1)` reconstruction completely: at `r = 0`, `ℓ(1) = 0`, so for *any*
   two degree-`≤ 1` polynomials `qA, qB` with `qA(0) = qB(0) = σ` and `qA(1) ≠ qB(1)`, BOTH
   satisfy the round-sum check `ℓ(0) q(0) + ℓ(1) q(1) = σ`, yet `qA(c) ≠ qB(c)` on **every**
   nonzero challenge `c ≠ 0` (and unstripped `(ℓ · qA)(c) ≠ (ℓ · qB)(c)` on every `c ≠ 0, 1`)!
   This proves why a Mode-1 wire-transparent prover must deterministically fall back to direct
   `q(1)` evaluation when `r = 0` (or why the verifier reconstructs `ℓ(1) q(1) = σ - ℓ(0) q(0)`
   without dividing by `r` when checking `r · q(X)`).

4. **Mode-2 Direct-`q` Tightened Soundness (`gruen_direct_claim_roots_le` & `gruen_direct_claim_prob_le`)**:
   When the verifier strips `ℓ(c)` and checks the degree-`≤ d` claim `q_prov(c)` directly against
   `q_true(c)` (`q_prov ≠ q_true`), the cheating challenge set `{c ∈ S | q_prov(c) = q_true(c)}`
   over **any** `S : Finset F` has cardinality **`≤ d`** (`≤ d / |F|` uniform error — `2 / |F|`
   instead of `3 / |F|` on GQA/MXFP4 `F_{≥2}` rounds, saving `1 / |F|` per round with **zero**
   prover inversions!).

5. **Sharp `(d + 1)`-Root Forgery Witness (`gruen_unstripped_admits_ell_root` &
   `gruen_d2_three_roots_vs_two_witness`) + Phase-Splice Tooth (`gruen_phase_splice_double_strip_tooth`)**:
   Over `ZMod 7` at `d = 2, r = 2`, we exhibit an explicit cheating polynomial `q_prov` that
   **passes** the round-sum check on a false incoming claim `σ_false = 5 ≠ 0`, succeeds on only
   **`2 = d`** challenges `{2, 3}` under Mode-2 direct-`q` checking, yet gets a **3rd (`d + 1`)
   free pass** at `c = 5` (`ℓ(5) = 0`) under unstripped `s(X) = ℓ(X) q(X)` checking! Finally,
   `gruen_phase_splice_double_strip_tooth` proves the Jolt PR `#1474` boundary invariant: a
   Mode-2 terminal claim already has `ℓ(c)` stripped, so dividing by `ℓ(c)` again corrupts any
   nonzero claim whenever `ℓ(c) ≠ 1`.
-/
import Assurance.ZkmlEinSumcheck

namespace Minidregg.Assurance.ZkmlGruenSumcheck

open Minidregg.Selvage Polynomial

/-! ## §1. `eqLinPoly`, `Selvage.eqMle` Factorization, and `{0, ∞}` Quadratic Parametrization -/

section EqLinPoly

/-- **Univariate linear equality factor (`eqLinPoly`)**:
`ℓ_r(X) = (1 - r)(1 - X) + r X`, matching one coordinate of `Selvage.eqMle`. -/
noncomputable def eqLinPoly {R : Type*} [CommRing R] (r : R) : Polynomial R :=
  Polynomial.C (1 - r) * (1 - Polynomial.X) + Polynomial.C r * Polynomial.X

@[simp] theorem eqLinPoly_eval {R : Type*} [CommRing R] (r x : R) :
    (eqLinPoly r).eval x = (1 - r) * (1 - x) + r * x := by
  simp [eqLinPoly]

@[simp] theorem eqLinPoly_eval_zero {R : Type*} [CommRing R] (r : R) :
    (eqLinPoly r).eval 0 = 1 - r := by
  simp [eqLinPoly]

@[simp] theorem eqLinPoly_eval_one {R : Type*} [CommRing R] (r : R) :
    (eqLinPoly r).eval 1 = r := by
  simp [eqLinPoly]

theorem eqLinPoly_eq_C_add_C_mul_X {R : Type*} [CommRing R] (r : R) :
    eqLinPoly r = Polynomial.C (1 - r) + Polynomial.C (2 * r - 1) * Polynomial.X := by
  unfold eqLinPoly
  simp only [map_sub, map_mul, map_one, map_ofNat]
  ring

theorem eqLinPoly_natDegree_le {R : Type*} [CommRing R] (r : R) :
    (eqLinPoly r).natDegree ≤ 1 := by
  rw [eqLinPoly_eq_C_add_C_mul_X]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le

/-- **Connection to `Selvage.eqMle`:** restricting coordinate `i` of `eqMle z` along `t` factors
out `(eqLinPoly (z i)).eval t` times the remaining coordinates' equality product. -/
theorem eqMle_update_eq_eqLinPoly_mul {R : Type*} [CommRing R] {m : ℕ}
    (z x : Fin m → R) (i : Fin m) (t : R) :
    eqMle z (Function.update x i t) =
      (eqLinPoly (z i)).eval t
        * ∏ j ∈ Finset.univ.erase i, (z j * x j + (1 - z j) * (1 - x j)) := by
  rw [eqMle, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self,
    eqLinPoly_eval]
  congr 1
  · ring
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Gruen `{0, ∞}` Quadratic Reconstruction (`quadFromZeroOneInf`):**
Given `q0 = q(0)` (evaluated at `0`), `qInf = q(∞)` (the leading `X²` coefficient = product of
slopes `ΔA · ΔB`), and `q1 = q(1)` (recovered algebraically from the round sum), reconstructs
`q(X) = q0 + (q1 - q0 - qInf) X + qInf X²` with zero `X = 1` inner-product pass. -/
noncomputable def quadFromZeroOneInf {R : Type*} [CommRing R] (q0 q1 qInf : R) : Polynomial R :=
  Polynomial.C q0 + Polynomial.C (q1 - q0 - qInf) * Polynomial.X
    + Polynomial.C qInf * Polynomial.X ^ 2

/-- Every degree-`≤ 2` polynomial `q` is uniquely reconstructed from `(q(0), q(1), q.coeff 2)`. -/
theorem eq_quadFromZeroOneInf_of_natDegree_le_two {R : Type*} [CommRing R]
    {q : Polynomial R} (hq : q.natDegree ≤ 2) :
    q = quadFromZeroOneInf (q.eval 0) (q.eval 1) (q.coeff 2) := by
  have h1 : q.eval 0 = q.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero q).symm
  have h2 : q.eval 1 = q.coeff 0 + q.coeff 1 + q.coeff 2 := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq)]
    simp [Finset.sum_range_succ]
  ext k
  rcases k with _ | _ | _ | k
  · simp [quadFromZeroOneInf, h1, Polynomial.coeff_X]
  · simp [quadFromZeroOneInf, h1, h2]
    ring
  · simp [quadFromZeroOneInf]
  · have hk : 2 < k + 3 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hk)]
    simp [quadFromZeroOneInf]

end EqLinPoly

/-! ## §2. `q(1)` Uniqueness for `r ≠ 0` & the `r = 0` Falsifier Tooth -/

section RoundSumSolver

/-- **Unique `q(1)` Reconstruction (`gruen_q1_unique_of_r_ne_zero`, `ePrint 2024/108` §3.2):**
Over any field `F`, whenever the round's `eq` coordinate `r ≠ 0`, the round-sum equation
`ℓ(0) · q0 + ℓ(1) · q1 = σ` uniquely pins `q1 = r⁻¹ * (σ - (1 - r) * q0)`. -/
theorem gruen_q1_unique_of_r_ne_zero {F : Type*} [Field F]
    {r q0 q1 σ : F} (hr : r ≠ 0) :
    (eqLinPoly r).eval 0 * q0 + (eqLinPoly r).eval 1 * q1 = σ ↔
      q1 = r⁻¹ * (σ - (1 - r) * q0) := by
  rw [eqLinPoly_eval_zero, eqLinPoly_eval_one]
  constructor
  · intro h
    have hrq1 : r * q1 = σ - (1 - r) * q0 := eq_sub_of_add_eq' h
    calc q1 = r⁻¹ * (r * q1) := (inv_mul_cancel_left₀ hr q1).symm
      _ = r⁻¹ * (σ - (1 - r) * q0) := by rw [hrq1]
  · intro h
    rw [h, mul_inv_cancel_left₀ hr]
    ring

/-- Helper: a degree-`≤ 1` polynomial `q` satisfies `q(X) = q(0) + (q(1) - q(0)) · X`. -/
theorem eval_eq_of_natDegree_le_one {R : Type*} [CommRing R]
    {q : Polynomial R} (hq : q.natDegree ≤ 1) (c : R) :
    q.eval c = q.eval 0 + (q.eval 1 - q.eval 0) * c := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq) 0,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq) 1]
  simp [Finset.sum_range_succ]

/-- **Falsifier Tooth (`gruen_r_zero_q1_unconstrained`):**
Drop the hypothesis `r ≠ 0` (setting `r = 0`, where `ℓ(0) = 1` and `ℓ(1) = 0`): for **any** two
linear polynomials `qA, qB` with `qA(0) = qB(0) = σ` and `qA(1) ≠ qB(1)`:
1. BOTH satisfy the round-sum equation `ℓ(0) q(0) + ℓ(1) q(1) = σ`,
2. Yet their stripped claims diverge (`qA(c) ≠ qB(c)`) on **every** nonzero challenge `c ≠ 0`
   (including `c = 1` and every `c ≠ 0, 1`), AND
3. Even their unstripped cubic/quadratic round messages `(eqLinPoly 0 * qA)(c)` and
   `(eqLinPoly 0 * qB)(c)` diverge on **every** challenge `c ≠ 0, 1`! -/
theorem gruen_r_zero_q1_unconstrained {F : Type*} [Field F]
    {qA qB : Polynomial F} {σ : F}
    (hdA : qA.natDegree ≤ 1) (hdB : qB.natDegree ≤ 1)
    (h0A : qA.eval 0 = σ) (h0B : qB.eval 0 = σ)
    (h1ne : qA.eval 1 ≠ qB.eval 1) :
    ((eqLinPoly (0 : F)).eval 0 * qA.eval 0 + (eqLinPoly (0 : F)).eval 1 * qA.eval 1 = σ) ∧
    ((eqLinPoly (0 : F)).eval 0 * qB.eval 0 + (eqLinPoly (0 : F)).eval 1 * qB.eval 1 = σ) ∧
    (∀ c : F, c ≠ 0 → qA.eval c ≠ qB.eval c) ∧
    (∀ c : F, c ≠ 0 → c ≠ 1 →
      (eqLinPoly (0 : F) * qA).eval c ≠ (eqLinPoly (0 : F) * qB).eval c) := by
  refine ⟨by simp [h0A], by simp [h0B], ?_, ?_⟩
  · intro c hc0 hEq
    rw [eval_eq_of_natDegree_le_one hdA c, eval_eq_of_natDegree_le_one hdB c, h0A, h0B] at hEq
    have hmul : (qA.eval 1 - σ) * c = (qB.eval 1 - σ) * c := add_left_cancel hEq
    have hsub : qA.eval 1 - σ = qB.eval 1 - σ := mul_right_cancel₀ hc0 hmul
    exact h1ne (by linear_combination hsub)
  · intro c hc0 hc1 hEq
    simp only [Polynomial.eval_mul, eqLinPoly_eval, sub_zero, one_mul, zero_mul, add_zero] at hEq
    have h1c : (1 - c : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
    have hqEq : qA.eval c = qB.eval c := mul_left_cancel₀ h1c hEq
    rw [eval_eq_of_natDegree_le_one hdA c, eval_eq_of_natDegree_le_one hdB c, h0A, h0B] at hqEq
    have hmul : (qA.eval 1 - σ) * c = (qB.eval 1 - σ) * c := add_left_cancel hqEq
    have hsub : qA.eval 1 - σ = qB.eval 1 - σ := mul_right_cancel₀ hc0 hmul
    exact h1ne (by linear_combination hsub)

/-- Concrete `ZMod 7` witness inhabiting `gruen_r_zero_q1_unconstrained` (`qA = 3 + X`,
`qB = 3 + 2X`, `σ = 3`). -/
theorem gruen_r_zero_witness_f7 :
    let qA : Polynomial (ZMod 7) := C 3 + X
    let qB : Polynomial (ZMod 7) := C 3 + C 2 * X
    (eqLinPoly (0 : ZMod 7)).eval 0 * qA.eval 0 + (eqLinPoly (0 : ZMod 7)).eval 1 * qA.eval 1 = 3 ∧
    (eqLinPoly (0 : ZMod 7)).eval 0 * qB.eval 0 + (eqLinPoly (0 : ZMod 7)).eval 1 * qB.eval 1 = 3 ∧
    qA.eval 2 ≠ qB.eval 2 ∧
    (eqLinPoly (0 : ZMod 7) * qA).eval 2 ≠ (eqLinPoly (0 : ZMod 7) * qB).eval 2 := by
  have h := gruen_r_zero_q1_unconstrained
    (qA := (C 3 + X : Polynomial (ZMod 7)))
    (qB := (C 3 + C 2 * X : Polynomial (ZMod 7)))
    (σ := (3 : ZMod 7))
    (by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ Polynomial.natDegree_X_le)
      rw [Polynomial.natDegree_C]; exact Nat.zero_le 1)
    (by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
      · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
    (by simp) (by simp) (by simp; decide)
  exact ⟨h.1, h.2.1, h.2.2.1 2 (by decide), h.2.2.2 2 (by decide) (by decide)⟩

end RoundSumSolver

/-! ## §3. Mode-2 Direct-`q` Tightened Soundness (`≤ d` vs `≤ d + 1`) & Extra-Root Witness -/

section Mode2Soundness

/-- **Mode-2 Direct-`q` Tightened Soundness (`gruen_direct_claim_roots_le`, `ePrint 2024/108` App. A.3):**
When the verifier checks the stripped claim `q_prov(c)` directly against true `q_true(c)` with
`natDegree ≤ d` and `q_prov ≠ q_true`, the set of challenges in ANY `S : Finset F` that launder
the lie has cardinality **`≤ d`** (eliminating the `ℓ(c) = 0` root of degree-`(d + 1)` unstripped
`s(X) = ℓ(X) q(X)`!). -/
theorem gruen_direct_claim_roots_le {F : Type*} [Field F] [DecidableEq F]
    {d : ℕ} {q_prov q_true : Polynomial F}
    (hp : q_prov.natDegree ≤ d) (ht : q_true.natDegree ≤ d)
    (hne : q_prov ≠ q_true) (S : Finset F) :
    (S.filter (fun c => q_prov.eval c = q_true.eval c)).card ≤ d := by
  have hsub_ne : q_prov - q_true ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (q_prov - q_true).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le q_prov q_true).trans (max_le hp ht)
  have hsub_roots :
      S.filter (fun c => q_prov.eval c = q_true.eval c) ⊆ (q_prov - q_true).roots.toFinset := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub_ne]
    simp [Polynomial.IsRoot, hc.2]
  calc (S.filter (fun c => q_prov.eval c = q_true.eval c)).card
      ≤ (q_prov - q_true).roots.toFinset.card := Finset.card_le_card hsub_roots
    _ ≤ Multiset.card (q_prov - q_true).roots := Multiset.toFinset_card_le _
    _ ≤ (q_prov - q_true).natDegree := Polynomial.card_roots' (q_prov - q_true)
    _ ≤ d := hdeg

/-- **Uniform-Probability Form (`gruen_direct_claim_prob_le`):** over a finite field `F`, Mode-2
direct-`q` checking accepts a false polynomial `q_prov ≠ q_true` of degree `≤ d` with probability
at most **`d / |F|`** (`2 / |F|` on quadratic `F_{≥2}` GQA/MXFP4 rounds vs `3 / |F|` unstripped). -/
theorem gruen_direct_claim_prob_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} {q_prov q_true : Polynomial F}
    (hp : q_prov.natDegree ≤ d) (ht : q_true.natDegree ≤ d)
    (hne : q_prov ≠ q_true) :
    uniformProb F (fun c => q_prov.eval c = q_true.eval c) ≤ (d : ℝ) / Fintype.card F := by
  have hcard := gruen_direct_claim_roots_le hp ht hne Finset.univ
  have hconv :
      uniformProb F (fun c => q_prov.eval c = q_true.eval c) =
        uniformProb F (fun c => c ∈ Finset.univ.filter (fun x => q_prov.eval x = q_true.eval x)) :=
    uniformProb_congr (fun x => by simp)
  rw [hconv, uniformProb_mem_finset]
  gcongr

/-- **General Extra-Root Theorem (`gruen_unstripped_admits_ell_root`):**
Whenever `2 * r ≠ 1`, `eqLinPoly r` has the unique root `c_ell = (1 - r) * (1 - 2 * r)⁻¹`.
At `c = c_ell`, unstripped `s(X) = eqLinPoly r * q(X)` collapses to `0 = 0` for **EVERY**
`q_prov` and `q_true` — granting a cheating prover an unconditional free pass even when
`q_prov(c_ell) ≠ q_true(c_ell)`! -/
theorem gruen_unstripped_admits_ell_root {F : Type*} [Field F]
    {r : F} (hr : 1 - 2 * r ≠ 0) (q_prov q_true : Polynomial F) :
    let c_ell : F := (1 - r) * (1 - 2 * r)⁻¹
    (eqLinPoly r).eval c_ell = 0 ∧
    (eqLinPoly r * q_prov).eval c_ell = (eqLinPoly r * q_true).eval c_ell := by
  intro c_ell
  have hell : (eqLinPoly r).eval c_ell = 0 := by
    rw [eqLinPoly_eval]
    have hcalc : (1 - r) * (1 - c_ell) + r * c_ell = (1 - r) - c_ell * (1 - 2 * r) := by ring
    rw [hcalc]
    dsimp [c_ell]
    rw [mul_assoc, inv_mul_cancel₀ hr, mul_one, sub_self]
  refine ⟨hell, ?_⟩
  simp [Polynomial.eval_mul, hell]

/-- **Sharp `(d + 1)`-Root Sumcheck Forgery Witness (`gruen_d2_three_roots_vs_two_witness`):**
Over `ZMod 7` at `d = 2` and `r = 2 ≠ 0` (`eqLinPoly 2 = 6 + 3X`, vanishing at `c = 5`):
take `q_true = 0` (`σ_true = 0`) and cheating `q_prov = (X - 2)(X - 3)` on FALSE incoming claim
`σ_false = 5 ≠ 0`:
1. `q_prov` **passes** the Gruen round-sum check `ℓ(0) q_prov(0) + ℓ(1) q_prov(1) = 5 = σ_false`;
2. `q_prov.natDegree ≤ 2`, `q_true.natDegree ≤ 2`, and `q_prov ≠ q_true`;
3. Under **Mode-2 direct-`q` checking**, `{c | q_prov(c) = q_true(c)} = {2, 3}` has cardinality
   **`2` (`= d`)**, rejecting `c = 5` (`q_prov(5) = 6 ≠ 0`);
4. Under **Mode-1 unstripped `s(X) = ℓ(X) q(X)` checking**, `{c | s_prov(c) = s_true(c)} = {2, 3, 5}`
   has cardinality **`3` (`= d + 1`)** — `c = 5` is an actual extra forgery challenge! -/
theorem gruen_d2_three_roots_vs_two_witness :
    let r : ZMod 7 := 2
    let q_true : Polynomial (ZMod 7) := 0
    let q_prov : Polynomial (ZMod 7) := (X - C 2) * (X - C 3)
    let s_true : Polynomial (ZMod 7) := eqLinPoly r * q_true
    let s_prov : Polynomial (ZMod 7) := eqLinPoly r * q_prov
    -- (1) Passes round-sum check for false incoming claim σ_false = 5 ≠ 0:
    ((eqLinPoly r).eval 0 * q_prov.eval 0 + (eqLinPoly r).eval 1 * q_prov.eval 1 = 5 ∧
      (5 : ZMod 7) ≠ (eqLinPoly r).eval 0 * q_true.eval 0 + (eqLinPoly r).eval 1 * q_true.eval 1) ∧
    -- (2) Degree ≤ 2:
    (q_prov.natDegree ≤ 2 ∧ q_true.natDegree ≤ 2) ∧
    -- (3) Mode-2 stripped agreement set has size 2 (= d) and REJECTS c = 5:
    ((Finset.univ.filter (fun c : ZMod 7 => q_prov.eval c = q_true.eval c)).card = 2 ∧
      q_prov.eval 5 ≠ q_true.eval 5) ∧
    -- (4) Mode-1 unstripped agreement set has size 3 (= d + 1) and ACCEPTS c = 5:
    ((Finset.univ.filter (fun c : ZMod 7 => s_prov.eval c = s_true.eval c)).card = 3 ∧
      s_prov.eval 5 = s_true.eval 5) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, by simp⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp [eqLinPoly]; decide
  · simp [eqLinPoly]; decide
  · have hX2 : ((X : Polynomial (ZMod 7)) - C 2).natDegree ≤ 1 := by
      rw [sub_eq_add_neg, ← C_neg]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le ?_)
      rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
    have hX3 : ((X : Polynomial (ZMod 7)) - C 3).natDegree ≤ 1 := by
      rw [sub_eq_add_neg, ← C_neg]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le ?_)
      rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
    exact (Polynomial.natDegree_mul_le (p := X - C 2) (q := X - C 3)).trans (by omega)
  · have hfilt :
        (Finset.univ.filter (fun c : ZMod 7 =>
          ((X - C 2) * (X - C 3) : Polynomial (ZMod 7)).eval c = (0 : Polynomial (ZMod 7)).eval c)) =
        Finset.univ.filter (fun c : ZMod 7 => (c - 2) * (c - 3) = 0) := by
      refine Finset.filter_congr fun c _ => ?_
      simp
    rw [hfilt]; decide
  · simp; decide
  · have hfilt :
        (Finset.univ.filter (fun c : ZMod 7 =>
          (eqLinPoly (2 : ZMod 7) * ((X - C 2) * (X - C 3))).eval c =
            (eqLinPoly (2 : ZMod 7) * 0).eval c)) =
        Finset.univ.filter (fun c : ZMod 7 =>
          ((1 - 2) * (1 - c) + 2 * c) * ((c - 2) * (c - 3)) = 0) := by
      refine Finset.filter_congr fun c _ => ?_
      simp [eqLinPoly]
    rw [hfilt]; decide
  · simp [eqLinPoly]; decide

/-- **Phase-1 → Phase-2 Boundary Splice Tooth (`gruen_phase_splice_double_strip_tooth`, Jolt PR `#1474`):**
In Mode 2, `claim_mode2 := q(c)` ALREADY strips `(eqLinPoly r).eval c` (unlike Mode 1's
`s(c) = ℓ(c) · q(c)`). A verifier that erroneously divides `claim_mode2` by `ℓ(c)` a second time
corrupts every nonzero sub-claim whenever `ℓ(c) ≠ 1` (`ℓ(c) ≠ 0`). -/
theorem gruen_phase_splice_double_strip_tooth {F : Type*} [Field F]
    {r c q_val : F}
    (hq : q_val ≠ 0)
    (hell0 : (eqLinPoly r).eval c ≠ 0)
    (hell1 : (eqLinPoly r).eval c ≠ 1) :
    ((eqLinPoly r).eval c)⁻¹ * ((eqLinPoly r).eval c * q_val) = q_val ∧
    ((eqLinPoly r).eval c)⁻¹ * q_val ≠ q_val := by
  refine ⟨inv_mul_cancel_left₀ hell0 q_val, ?_⟩
  intro hbad
  have hinv1 : ((eqLinPoly r).eval c)⁻¹ = 1 :=
    mul_right_cancel₀ hq (hbad.trans (one_mul q_val).symm)
  exact hell1 (inv_eq_one.mp hinv1)

end Mode2Soundness

/-! ## Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.eqMle_update_eq_eqLinPoly_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eqMle_update_eq_eqLinPoly_mul
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.eq_quadFromZeroOneInf_of_natDegree_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eq_quadFromZeroOneInf_of_natDegree_le_two
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_q1_unique_of_r_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_q1_unique_of_r_ne_zero
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_r_zero_q1_unconstrained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_r_zero_q1_unconstrained
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_r_zero_witness_f7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_r_zero_witness_f7
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_direct_claim_roots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_direct_claim_roots_le
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_direct_claim_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_direct_claim_prob_le
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_unstripped_admits_ell_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_unstripped_admits_ell_root
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_d2_three_roots_vs_two_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_d2_three_roots_vs_two_witness
/-- info: 'Minidregg.Assurance.ZkmlGruenSumcheck.gruen_phase_splice_double_strip_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gruen_phase_splice_double_strip_tooth

end Minidregg.Assurance.ZkmlGruenSumcheck
