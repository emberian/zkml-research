/-
# Selvage.ProximityGapUDTight — `[PROXGAP-tight]`(a): the BCIKS Berlekamp–Welch-
over-`F(Z)` route to the FULL unique-decoding radius `(1 − ρ)/2`, built to its
one genuinely-hard rung.

**What this file is.** `Selvage/ProximityGapUD.lean` PROVED the RS proximity gap
on `δ ∈ (0, (1 − ρ)/3)` and named the residual `[PROXGAP-tight]`(a): the
elementary transfer pays a `2δ` start cost, and the full radius is BCIKS
2020/654 Thm 4.1 — run the Berlekamp–Welch decoder over the rational function
field `K = F(Z)` on the received word `w(x) = u₀(x) + Z·u₁(x)`. This file
BUILDS that route. Following BCIKS §4.3 (read against the actual paper, ECCC
TR20-083):

1. *The interpolation system, SOLVED* (`exists_bw_solution`): nonzero
   `A, B ∈ F[Z][X]` with `deg_X A ≤ e`, `deg_Z A ≤ e`, `deg_X B ≤ n − e − 1`,
   `deg_Z B ≤ e + 1` and `A(xᵢ, Z)·(u₀(xᵢ) + Z·u₁(xᵢ)) = B(xᵢ, Z)` at every
   domain point, with `A ≠ 0`. BCIKS obtain this from Cramer's rule after
   showing every maximal minor of the system matrix — a degree-`≤ e + 1`
   polynomial in `Z` — vanishes on the `> n` close challenges (their
   "`≤ n` bad-challenge count"). Here the SAME degree profile is obtained
   UNCONDITIONALLY: padding `deg_X B` to `n − e − 1` (the largest degree the
   uniqueness step tolerates) makes the coefficient space exceed the
   constraint space by EXACTLY one F-dimension — `(e+1)² + (n−e)(e+2) =
   n(e+2) + 1` — so a nonzero solution exists by rank-nullity, no minors
   needed. The `|S| > n` threshold is NOT thereby dodged: it reappears as the
   third Polishchuk–Spielman inequality below, which is where BCIKS's proof
   spends it too (their minor argument only fed existence).
2. *Specialization* (`bw_specialize`, `bw_quotient_at`): at every close
   challenge `z` with `A(X, z) ≠ 0`, the specialized pair is a Berlekamp–
   Welch solution for the close word, hence `B(X, z) = A(X, z)·p_z` for THE
   close codeword `p_z` — root counting on `A(X,z)·p_z − B(X,z)` (degree
   `≤ n − e − 1`, vanishing on `≥ n − e` agreement points; the step that
   prices the FULL radius: it needs only `2e + d ≤ n`, i.e. δ up to
   `(1 − ρ)/2`, not the elementary route's `3e + d ≤ n`). At `z` with
   `A(X, z) = 0`, `B(X, z)` vanishes on the whole domain and is 0. Either
   way `A(X, z) ∣ B(X, z)` for EVERY close `z`.
3. *The divisibility rung* (`[PROXGAP-BW-ps]`): BCIKS Lemma 4.4, the
   Polishchuk–Spielman bivariate divisibility lemma. ⚠ 2026-10-04: the
   `Prop` this file carried for it, `PolishchukSpielman F` (plain per-line
   divisibility, no quotient-degree bounds — the [Spi95] / BCIKS rev.1 shape),
   is FALSE over every field with three elements
   (`Selvage/PolishchukSpielmanRefutation.lean`,
   `polishchukSpielman_unfixed_false`), so every theorem conditioned on it was
   true of nothing. The def and every consumer (the full-band core
   `correlatedAgreement_of_close_card_full`, the four `*_UD_full` heads, the
   keystones `ps_premises_inhabited` and `good_line_CA_fullBand`) are DELETED
   (docs/decisions/D-0006-polishchuk-spielman-unfixed-floor-refuted.md). The
   corrected statement carries the Cramer quotient-degree bounds; the route
   is restated on it, not on the refuted shape.

**What survives here.** The UNCONDITIONAL front half of the route: the
Berlekamp–Welch system and its solution, the specialization quotients at the
full `2e + d ≤ n` radius, and the Z-degree calculus. The full-band heads are
gone with the refuted floor; `(1 − ρ)/3` (`Selvage/ProximityGapUD.lean`) is
the proved band.

**Honest scope limits.** (i) Nothing here reaches past `(1 − ρ)/3`; the
divisibility rung is the missing step. (ii) `ℓ = 2` (the affine pair
generator), as everywhere in the landed stack.
-/
import Selvage.ProximityGapUD

namespace Minidregg.Selvage

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Z-degree calculus on `F[Z][X]`

Bivariate polynomials are carried as `Polynomial (Polynomial F)` — OUTER
variable `X`, coefficients in `F[Z]`. `ZDegLE p t` bounds the Z-degree of
every X-coefficient. -/

/-- Every X-coefficient of `p : F[Z][X]` has Z-degree at most `t`. -/
def ZDegLE (p : Polynomial (Polynomial F)) (t : ℕ) : Prop :=
  ∀ i, (p.coeff i).degree ≤ (t : WithBot ℕ)

private theorem withBot_lt_succ_iff {a : WithBot ℕ} {k : ℕ} :
    a < ((k + 1 : ℕ) : WithBot ℕ) ↔ a ≤ (k : WithBot ℕ) := by
  cases a with
  | bot => simp
  | coe n =>
      rw [Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe, WithBot.coe_le_coe]
      exact Nat.lt_succ_iff

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
theorem ZDegLE.evalC {p : Polynomial (Polynomial F)} {t : ℕ}
    (hp : ZDegLE p t) (x : F) : (p.eval (C x)).degree ≤ (t : WithBot ℕ) := by
  rw [eval_eq_sum, Polynomial.sum]
  refine le_trans (degree_sum_le _ _) (Finset.sup_le fun i _ => ?_)
  calc ((p.coeff i) * C x ^ i).degree
      ≤ (p.coeff i).degree + (C x ^ i).degree := degree_mul_le _ _
    _ ≤ (t : WithBot ℕ) + 0 := by
        refine add_le_add (hp i) ?_
        rw [← C_pow]
        exact degree_C_le
    _ = (t : WithBot ℕ) := add_zero _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Z-degree bound of a coefficient of a product: coefficients of `p * q`
have Z-degree at most `s + t` when `p`'s are `≤ s` and `q`'s are `≤ t`. -/
theorem ZDegLE.mul {p q : Polynomial (Polynomial F)} {s t : ℕ}
    (hp : ZDegLE p s) (hq : ZDegLE q t) : ZDegLE (p * q) (s + t) := by
  intro i
  rw [coeff_mul]
  refine le_trans (degree_sum_le _ _) (Finset.sup_le fun ab _ => ?_)
  calc (p.coeff ab.1 * q.coeff ab.2).degree
      ≤ (p.coeff ab.1).degree + (q.coeff ab.2).degree := degree_mul_le _ _
    _ ≤ (s : WithBot ℕ) + (t : WithBot ℕ) := add_le_add (hp _) (hq _)
    _ = ((s + t : ℕ) : WithBot ℕ) := by push_cast; rfl

/-- The Z-top slice of a bivariate polynomial: the X-polynomial of `Z^t`
coefficients. -/
private noncomputable def zslice (t : ℕ) (p : Polynomial (Polynomial F)) :
    Polynomial F :=
  p.sum fun i c => monomial i (c.coeff t)

omit [DecidableEq F] in
private theorem zslice_coeff (t : ℕ) (p : Polynomial (Polynomial F)) (a : ℕ) :
    (zslice t p).coeff a = (p.coeff a).coeff t := by
  classical
  rw [zslice, Polynomial.sum, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' p.support a fun i => (p.coeff i).coeff t]
  split_ifs with h
  · rfl
  · rw [Polynomial.notMem_support_iff.mp h, Polynomial.coeff_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **Z-degree of a factor is bounded by the Z-degree of the product** —
`F[Z][X]` is a domain, so the Z-top slices multiply and cannot cancel. This
is the "bidegree of the quotient" fact BCIKS use silently when dividing
`B(X, Z)` by `A(X, Z)`. -/
theorem ZDegLE.of_mul_left {A P : Polynomial (Polynomial F)} {t : ℕ}
    (hA : A ≠ 0) (hP : P ≠ 0) (hAP : ZDegLE (A * P) t) : ZDegLE P t := by
  classical
  set s : ℕ := A.support.sup fun i => (A.coeff i).natDegree with hs
  set u : ℕ := P.support.sup fun i => (P.coeff i).natDegree with hu
  have hAcoeff : ∀ a, (A.coeff a).natDegree ≤ s := by
    intro a
    by_cases ha : a ∈ A.support
    · exact Finset.le_sup (f := fun i => (A.coeff i).natDegree) ha
    · rw [Polynomial.notMem_support_iff.mp ha]; simp
  have hPcoeff : ∀ b, (P.coeff b).natDegree ≤ u := by
    intro b
    by_cases hb : b ∈ P.support
    · exact Finset.le_sup (f := fun i => (P.coeff i).natDegree) hb
    · rw [Polynomial.notMem_support_iff.mp hb]; simp
  -- the top slices multiply
  have hslice : ∀ j : ℕ,
      ((A * P).coeff j).coeff (s + u) = (zslice s A * zslice u P).coeff j := by
    intro j
    rw [coeff_mul, coeff_mul]
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [zslice_coeff, zslice_coeff, coeff_mul]
    refine Finset.sum_eq_single (s, u) (fun uv huv huvne => ?_) (fun habs => ?_)
    · rcases Nat.lt_or_ge s uv.1 with hlt | hge
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hAcoeff ab.1) hlt),
          zero_mul]
      · have h2 : u < uv.2 := by
          have := Finset.mem_antidiagonal.mp huv
          rcases Nat.lt_or_ge u uv.2 with h | h
          · exact h
          · exact absurd (Prod.ext (by omega) (by omega)) huvne
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hPcoeff ab.2) h2),
          mul_zero]
    · exact absurd (Finset.mem_antidiagonal (a := (s, u)) (n := s + u)
        |>.mpr rfl) habs
  -- the slices at the attained sups are nonzero
  have hAsupp : A.support.Nonempty := Polynomial.support_nonempty.mpr hA
  have hPsupp : P.support.Nonempty := Polynomial.support_nonempty.mpr hP
  obtain ⟨a₀, ha₀, hsa⟩ := Finset.exists_mem_eq_sup A.support hAsupp
    (fun i => (A.coeff i).natDegree)
  obtain ⟨b₀, hb₀, hub⟩ := Finset.exists_mem_eq_sup P.support hPsupp
    (fun i => (P.coeff i).natDegree)
  have hA0 : zslice s A ≠ 0 := by
    intro h0
    have := zslice_coeff s A a₀
    rw [h0, Polynomial.coeff_zero, hs.trans hsa] at this
    exact leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp ha₀) this.symm
  have hP0 : zslice u P ≠ 0 := by
    intro h0
    have := zslice_coeff u P b₀
    rw [h0, Polynomial.coeff_zero, hu.trans hub] at this
    exact leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp hb₀) this.symm
  -- hence the product has Z-degree ≥ s + u somewhere, so s + u ≤ t
  have hprod : zslice s A * zslice u P ≠ 0 := mul_ne_zero hA0 hP0
  set j : ℕ := (zslice s A * zslice u P).natDegree with hj'
  have hj : (zslice s A * zslice u P).coeff j ≠ 0 :=
    leadingCoeff_ne_zero.mpr hprod
  have hcoeff : ((A * P).coeff j).coeff (s + u) ≠ 0 := by rw [hslice j]; exact hj
  have hdeg : ((s + u : ℕ) : WithBot ℕ) ≤ ((A * P).coeff j).degree :=
    le_degree_of_ne_zero hcoeff
  have hsu : ((s + u : ℕ) : WithBot ℕ) ≤ (t : WithBot ℕ) := le_trans hdeg (hAP j)
  have hsu' : s + u ≤ t := by exact_mod_cast hsu
  -- conclude: every coefficient of P has degree ≤ u ≤ t
  intro i
  have h1 : (P.coeff i).natDegree ≤ t := le_trans (hPcoeff i) (by omega)
  exact le_trans degree_le_natDegree (by exact_mod_cast h1)

/-! ## The received line as a Z-polynomial -/

/-- The received line at coordinate `i`, as an element of `F[Z]`:
`u₀(i) + u₁(i)·Z` (BCIKS's `w(x) = u₀(x) + Z·u₁(x)`). -/
noncomputable def lineAt (f : Fin 2 → ι → F) (i : ι) : Polynomial F :=
  C (f 0 i) + C (f 1 i) * X

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp] theorem lineAt_eval (f : Fin 2 → ι → F) (i : ι) (z : F) :
    (lineAt f i).eval z = f 0 i + z * f 1 i := by
  rw [lineAt, eval_add, eval_mul, eval_C, eval_C, eval_X]
  ring

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
theorem lineAt_degree_le (f : Fin 2 → ι → F) (i : ι) :
    (lineAt f i).degree ≤ (1 : WithBot ℕ) := by
  refine le_trans (degree_add_le _ _) (max_le (le_trans degree_C_le zero_le_one) ?_)
  calc (C (f 1 i) * X).degree ≤ (C (f 1 i)).degree + X.degree := degree_mul_le _ _
    _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
    _ = 1 := zero_add _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp] theorem lineAt_coeff_zero (f : Fin 2 → ι → F) (i : ι) :
    (lineAt f i).coeff 0 = f 0 i := by
  simp [lineAt, coeff_C]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp] theorem lineAt_coeff_one (f : Fin 2 → ι → F) (i : ι) :
    (lineAt f i).coeff 1 = f 1 i := by
  simp [lineAt, coeff_C]

/-! ## Root-counting workhorse -/

/-- A polynomial over a domain vanishing on more points than its `natDegree`
is zero — the one root-counting shape every step below consumes. -/
private theorem eq_zero_of_eval_zero_on {R : Type*} [CommRing R] [IsDomain R]
    {p : Polynomial R} {S : Finset R} (hdeg : p.natDegree < S.card)
    (hz : ∀ z ∈ S, p.eval z = 0) : p = 0 := by
  by_contra hp
  have hsub : S.val ⊆ p.roots := by
    intro z hzS
    rw [Polynomial.mem_roots hp]
    exact hz z (Finset.mem_val.mp hzS)
  exact absurd (Polynomial.card_le_degree_of_subset_roots hsub) (by omega)

omit [Fintype ι] [DecidableEq ι] in
private theorem card_image_Cdom (dom : ι ↪ F) (s : Finset ι) :
    (s.image fun i => (C (dom i) : Polynomial F)).card = s.card :=
  Finset.card_image_of_injective _ fun _ _ hab =>
    dom.injective (Polynomial.C_injective hab)

/-! ## The Berlekamp–Welch system over `F[Z]`: existence with the BCIKS
degree profile

The coefficient grid `Fin m → Fin t → F` builds the bivariate polynomial
`∑ᵢⱼ cᵢⱼ · Zʲ · Xⁱ`; the system map sends `(A-grid, B-grid)` to the Z-Taylor
coefficients of the residuals `A(xᵢ, Z)·w(xᵢ, Z) − B(xᵢ, Z)`. Its domain
exceeds its codomain by exactly one F-dimension. -/

private noncomputable def ofGrid {m t : ℕ} (c : Fin m → Fin t → F) :
    Polynomial (Polynomial F) :=
  ∑ i : Fin m, monomial (i : ℕ) (∑ j : Fin t, monomial (j : ℕ) (c i j))

omit [DecidableEq F] in
private theorem ofGrid_coeff {m t : ℕ} (c : Fin m → Fin t → F) (a : Fin m) :
    (ofGrid c).coeff (a : ℕ) = ∑ j : Fin t, monomial (j : ℕ) (c a j) := by
  rw [ofGrid, finsetSum_coeff]
  rw [Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a) h)]
  · rw [coeff_monomial, if_pos rfl]
  · rw [coeff_monomial, if_neg (fun h => hb (Fin.val_injective h))]

omit [DecidableEq F] in
private theorem ofGrid_coeff_coeff {m t : ℕ} (c : Fin m → Fin t → F)
    (a : Fin m) (b : Fin t) : ((ofGrid c).coeff (a : ℕ)).coeff (b : ℕ) = c a b := by
  rw [ofGrid_coeff, finsetSum_coeff]
  rw [Finset.sum_eq_single b (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ b) h)]
  · rw [coeff_monomial, if_pos rfl]
  · rw [coeff_monomial, if_neg (fun h => hj (Fin.val_injective h))]

omit [DecidableEq F] in
private theorem ofGrid_degree_lt {m t : ℕ} (c : Fin m → Fin t → F) :
    (ofGrid c).degree < (m : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff ?_).mpr ?_)
  · exact_mod_cast WithBot.bot_lt_coe m
  · intro i _
    refine lt_of_le_of_lt (degree_monomial_le _ _) ?_
    exact_mod_cast WithBot.coe_lt_coe.mpr i.isLt

omit [DecidableEq F] in
private theorem ofGrid_zdeg {m t : ℕ} (c : Fin m → Fin t → F) (a : ℕ) :
    ((ofGrid c).coeff a).degree < (t : WithBot ℕ) := by
  by_cases ha : a < m
  · rw [show a = ((⟨a, ha⟩ : Fin m) : ℕ) from rfl, ofGrid_coeff]
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff ?_).mpr ?_)
    · exact_mod_cast WithBot.bot_lt_coe t
    · intro j _
      refine lt_of_le_of_lt (degree_monomial_le _ _) ?_
      exact_mod_cast WithBot.coe_lt_coe.mpr j.isLt
  · rw [Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (ofGrid_degree_lt c) (by exact_mod_cast Nat.le_of_not_lt ha))]
    exact lt_of_lt_of_le (WithBot.bot_lt_coe 0) (by exact_mod_cast Nat.zero_le t)

omit [DecidableEq F] in
private theorem ofGrid_add {m t : ℕ} (c d : Fin m → Fin t → F) :
    ofGrid (c + d) = ofGrid c + ofGrid d := by
  rw [ofGrid, ofGrid, ofGrid, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_add]
  rfl

omit [DecidableEq F] in
private theorem ofGrid_smul {m t : ℕ} (r : F) (c : Fin m → Fin t → F) :
    ofGrid (r • c) = r • ofGrid c := by
  rw [ofGrid, ofGrid, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.smul_monomial, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.smul_monomial]
  rfl

/-- The Berlekamp–Welch residual map: `(A-grid, B-grid)` to the low-order
Z-coefficients of `A(xᵢ, Z)·w(xᵢ, Z) − B(xᵢ, Z)` at every domain point. -/
private noncomputable def bwMap (dom : ι ↪ F) (f : Fin 2 → ι → F)
    (e n' t : ℕ) :
    ((Fin (e + 1) → Fin (e + 1) → F) × (Fin n' → Fin t → F)) →ₗ[F]
      (ι → Fin t → F) where
  toFun cb := fun i j =>
    ((ofGrid cb.1).eval (C (dom i)) * lineAt f i
      - (ofGrid cb.2).eval (C (dom i))).coeff (j : ℕ)
  map_add' x y := by
    funext i j
    simp only [Prod.fst_add, Prod.snd_add, ofGrid_add, eval_add, Pi.add_apply]
    rw [← Polynomial.coeff_add]
    congr 1
    ring
  map_smul' r x := by
    funext i j
    simp only [Prod.smul_fst, Prod.smul_snd, ofGrid_smul, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Polynomial.eval_smul, Polynomial.eval_smul, smul_mul_assoc, ← smul_sub,
      Polynomial.coeff_smul, smul_eq_mul]

omit [DecidableEq ι] in
/-- **The Berlekamp–Welch interpolation system over `F[Z]`, solved with the
BCIKS degree profile** (BCIKS §4.3.1, restructured): there is a NONZERO pair
`A, B ∈ F[Z][X]` with `deg_X A ≤ e`, `deg_Z A ≤ e`, `deg_X B < n − e`,
`deg_Z B ≤ e + 1`, satisfying `A(xᵢ, Z)·(u₀(xᵢ) + Z·u₁(xᵢ)) = B(xᵢ, Z)` at
every domain point — and `A ≠ 0` outright. Existence is by rank-nullity: the
coefficient space has dimension `(e+1)² + (n−e)(e+2) = n(e+2) + 1`, one more
than the `n(e+2)` Z-Taylor constraints (BCIKS's maximal-minor/Cramer step,
made unconditional by padding `deg_X B` to the largest value the uniqueness
argument tolerates). -/
theorem exists_bw_solution [Nonempty ι] (dom : ι ↪ F) (f : Fin 2 → ι → F)
    {e n' : ℕ} (hn : n' + e = Fintype.card ι) (hn' : 0 < n') :
    ∃ A B : Polynomial (Polynomial F),
      A ≠ 0 ∧ A.natDegree ≤ e ∧ ZDegLE A e ∧
      B.natDegree < n' ∧ ZDegLE B (e + 1) ∧
      ∀ i, A.eval (C (dom i)) * lineAt f i = B.eval (C (dom i)) := by
  classical
  set n := Fintype.card ι with hnn
  -- rank-nullity: the residual map cannot be injective
  have hgrid : ∀ m t : ℕ, Module.finrank F (Fin m → Fin t → F) = m * t := by
    intro m t
    rw [Module.finrank_pi_fintype]
    simp [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hnotinj : ¬ Function.Injective (bwMap dom f e n' (e + 2)) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank F
        ((Fin (e + 1) → Fin (e + 1) → F) × (Fin n' → Fin (e + 2) → F))
        = (e + 1) * (e + 1) + n' * (e + 2) := by
      rw [Module.finrank_prod, hgrid, hgrid]
    have hcod : Module.finrank F (ι → Fin (e + 2) → F) = n * (e + 2) := by
      rw [Module.finrank_pi_fintype]
      simp only [Module.finrank_pi, Fintype.card_fin, Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
      rw [hnn]
    rw [hdom, hcod] at hle
    have hcontra : n * (e + 2) + 1 ≤ n * (e + 2) := by
      calc n * (e + 2) + 1
          = (e + 1) * (e + 1) + n' * (e + 2) := by
            have h2 : n = n' + e := by omega
            rw [h2]; ring
        _ ≤ n * (e + 2) := hle
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnotinj
  -- the kernel vector
  set v := x - y with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hne
  have hker : bwMap dom f e n' (e + 2) v = 0 := by
    rw [hv, map_sub, hxy, sub_self]
  set A := ofGrid v.1 with hA
  set B := ofGrid v.2 with hB
  -- the residuals vanish: low coefficients by the kernel, high by degree
  have hsys : ∀ i, A.eval (C (dom i)) * lineAt f i = B.eval (C (dom i)) := by
    intro i
    have hdeg : (A.eval (C (dom i)) * lineAt f i - B.eval (C (dom i))).degree
        < ((e + 2 : ℕ) : WithBot ℕ) := by
      have hAe : (A.eval (C (dom i))).degree ≤ (e : WithBot ℕ) :=
        ZDegLE.evalC (fun a => withBot_lt_succ_iff.mp (ofGrid_zdeg v.1 a)) _
      have hBe : (B.eval (C (dom i))).degree ≤ ((e + 1 : ℕ) : WithBot ℕ) :=
        ZDegLE.evalC (fun a => withBot_lt_succ_iff.mp (ofGrid_zdeg v.2 a)) _
      have hmul : (A.eval (C (dom i)) * lineAt f i).degree
          ≤ ((e + 1 : ℕ) : WithBot ℕ) := by
        refine le_trans (degree_mul_le _ _) ?_
        calc (A.eval (C (dom i))).degree + (lineAt f i).degree
            ≤ (e : WithBot ℕ) + 1 := add_le_add hAe (lineAt_degree_le f i)
          _ = ((e + 1 : ℕ) : WithBot ℕ) := by push_cast; rfl
      refine lt_of_le_of_lt (degree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor <;> rw [withBot_lt_succ_iff] <;> assumption
    rw [← sub_eq_zero]
    ext j
    rcases Nat.lt_or_ge j (e + 2) with hj | hj
    · have := congrFun (congrFun hker i) ⟨j, hj⟩
      simpa [bwMap] using this
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hdeg (by exact_mod_cast hj)), Polynomial.coeff_zero]
  -- the pair is nonzero
  have hpair : A ≠ 0 ∨ B ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    have h1 : v.1 = 0 := by
      funext a b
      have := ofGrid_coeff_coeff v.1 a b
      rw [← hA, hcon.1] at this
      simpa using this.symm
    have h2 : v.2 = 0 := by
      funext a b
      have := ofGrid_coeff_coeff v.2 a b
      rw [← hB, hcon.2] at this
      simpa using this.symm
    exact Prod.ext h1 h2
  -- degree bounds
  have hAdeg : A.natDegree ≤ e := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0]; simp
    · have := (natDegree_lt_iff_degree_lt h0).mpr (ofGrid_degree_lt v.1)
      omega
  have hBdeg : B.natDegree < n' := by
    rcases eq_or_ne B 0 with h0 | h0
    · rw [h0]; simpa using hn'
    · exact (natDegree_lt_iff_degree_lt h0).mpr (ofGrid_degree_lt v.2)
  -- A ≠ 0: otherwise B vanishes on the whole domain yet deg_X B < n' ≤ n
  have hA0 : A ≠ 0 := by
    rcases hpair with h | hB0
    · exact h
    intro h0
    apply hB0
    refine eq_zero_of_eval_zero_on (S := Finset.univ.image fun i => C (dom i))
      ?_ fun z hz => ?_
    · rw [card_image_Cdom dom Finset.univ, Finset.card_univ, ← hnn]
      omega
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      have := hsys i
      rw [h0] at this
      simp only [eval_zero, zero_mul] at this
      exact this.symm
  exact ⟨A, B, hA0, hAdeg,
    fun a => withBot_lt_succ_iff.mp (ofGrid_zdeg v.1 a), hBdeg,
    fun a => withBot_lt_succ_iff.mp (ofGrid_zdeg v.2 a), hsys⟩

/-! ## Specialization: `Z ↦ z` -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Specializing then evaluating equals evaluating then specializing:
`(A mod (Z − z))(x) = A(x, Z)|_{Z = z}`. -/
theorem map_evalRingHom_eval (A : Polynomial (Polynomial F)) (z x : F) :
    (A.map (evalRingHom z)).eval x = (A.eval (C x)).eval z := by
  have h2 : A.eval₂ (evalRingHom z) ((evalRingHom z) (C x))
      = (evalRingHom z) (A.eval (C x)) := eval₂_at_apply (evalRingHom z) (C x)
  have h3 : (evalRingHom z) (C x) = x := by simp
  rw [eval_map]
  calc A.eval₂ (evalRingHom z) x
      = A.eval₂ (evalRingHom z) ((evalRingHom z) (C x)) := by rw [h3]
    _ = (evalRingHom z) (A.eval (C x)) := h2
    _ = (A.eval (C x)).eval z := rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The specialized system: at every `z`, the pair `(A(X,z), B(X,z))` is a
Berlekamp–Welch solution for the received word `u₀ + z·u₁`. -/
theorem bw_specialize {dom : ι ↪ F} {f : Fin 2 → ι → F}
    {A B : Polynomial (Polynomial F)}
    (hsys : ∀ i, A.eval (C (dom i)) * lineAt f i = B.eval (C (dom i))) (z : F) :
    ∀ i, (A.map (evalRingHom z)).eval (dom i) * (f 0 i + z * f 1 i)
      = (B.map (evalRingHom z)).eval (dom i) := by
  intro i
  rw [map_evalRingHom_eval, map_evalRingHom_eval, ← lineAt_eval f i z,
    ← Polynomial.eval_mul, hsys i]

omit [DecidableEq ι] in
/-- **Berlekamp–Welch uniqueness at a close challenge** (BCIKS Lemma 4.3
item 2, at the padded degree): any specialized solution `(Az, Bz)` with
`Az ≠ 0` satisfies `Bz = Az · p` for the close codeword `p` — the difference
`Az·p − Bz` has degree `< n − e` yet vanishes on the `≥ n − e` agreement
points. THIS is the step that prices the full `(1 − ρ)/2` radius: it needs
only `2e + d ≤ n`. -/
theorem bw_quotient_at (dom : ι ↪ F) {d e n' : ℕ}
    (hn : n' + e = Fintype.card ι) (hcount : d + (e + e) < Fintype.card ι)
    {Az Bz p : Polynomial F} (hAdeg : Az.natDegree ≤ e) (hBdeg : Bz.natDegree < n')
    (hp : p.degree < (d : WithBot ℕ)) {g : ι → F} {T : Finset ι}
    (hTcard : Fintype.card ι ≤ T.card + e)
    (hag : ∀ i ∈ T, g i = p.eval (dom i))
    (hsys : ∀ i, Az.eval (dom i) * g i = Bz.eval (dom i)) :
    Bz = Az * p := by
  classical
  have hn' : 0 < n' := by omega
  have hdiff : Az * p - Bz = 0 := by
    refine eq_zero_of_eval_zero_on (S := T.image dom) ?_ fun x hx => ?_
    · have hTn : n' ≤ T.card := by omega
      rw [Finset.card_image_of_injective _ dom.injective]
      have hmul : (Az * p).natDegree < n' := by
        rcases eq_or_ne p 0 with rfl | hp0
        · rw [mul_zero]; simpa using hn'
        · have hpd : p.natDegree < d := (natDegree_lt_iff_degree_lt hp0).mpr hp
          have := natDegree_mul_le (p := Az) (q := p)
          omega
      have := natDegree_sub_le (Az * p) Bz
      omega
    · obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hx
      have h1 := hsys i
      rw [hag i hiT] at h1
      rw [eval_sub, eval_mul, ← h1, sub_self]
  exact (sub_eq_zero.mp hdiff).symm

/-! ## Keystones (ATLAS law 2: satisfiable + teeth)

The landed `RS[F₅, {0,1,2,3}, 2]` (ρ = 1/2). The full-UD band at this code is
`δ ∈ (0, 1/4)`; the landed unconditional band is `(0, 1/6)`. δ = 1/5 sits
STRICTLY BETWEEN.

* **the band widens for real** (`band_widens`, UNCONDITIONAL): at δ = 1/5 the
  landed hypothesis `d < (1 − 3δ)n` FAILS and the full-band hypothesis
  `d < (1 − 2δ)n` HOLDS.
* **the Berlekamp–Welch system FIRES** (`bw_solution_F5`, UNCONDITIONAL): the
  proved existence theorem delivers a nonzero solution with the BCIKS degree
  profile at the concrete code.

The deleted `ps_premises_inhabited` exhibited the refuted floor's PREMISES
inhabited (at `A = 1`, where the conclusion is trivial) and was read as
"assuming it is not vacuous". Premise inhabitation at a toy says nothing about
whether the floor is TRUE; the refutation is at the same field. -/

namespace ProximityGapUDTightExample

open RSExample ProximityGapUDExample

/-- δ = 1/5 at ρ = 1/2, n = 4: the landed one-third hypothesis FAILS, the
full-UD hypothesis HOLDS. The extension band is real, unconditionally. -/
theorem band_widens :
    ¬ ((2 : ℝ) < (1 - 3 * (1/5 : ℝ)) * (Fintype.card (Fin 4) : ℝ))
    ∧ ((2 : ℝ) < (1 - 2 * (1/5 : ℝ)) * (Fintype.card (Fin 4) : ℝ)) := by
  constructor <;> norm_num [Fintype.card_fin]

/-- The Berlekamp–Welch interpolation system SOLVED at the tiny code
(`e = 1`, `n′ = 3`): nonzero `A` with the BCIKS degree profile. -/
theorem bw_solution_F5 :
    ∃ A B : Polynomial (Polynomial (ZMod 5)),
      A ≠ 0 ∧ A.natDegree ≤ 1 ∧ ZDegLE A 1 ∧
      B.natDegree < 3 ∧ ZDegLE B 2 ∧
      ∀ i, A.eval (C (dom₅ i)) * lineAt ![xWord, oneWord] i
        = B.eval (C (dom₅ i)) :=
  exists_bw_solution dom₅ ![xWord, oneWord]
    (by norm_num [Fintype.card_fin]) (by omega)

end ProximityGapUDTightExample

/-! ## Residual obligation — `[PROXGAP-BW-ps]`

The full unique-decoding band needs, after `bw_quotient_at`, bivariate
divisibility `A ∣ B` from the row and column divisibilities. The statement
that is TRUE is the Cramer-fixed one (BCIKS rev.3 Appendix D): the per-line
quotients have degree at most `b − a` in the line variable. On the Berlekamp–
Welch pair the row quotients are the close codewords `p_z` (`deg < d ≤
n − 2e − 1 = b_X − a_X`) and the column quotients are the lines
`u₀(x) + Z·u₁(x)` (`deg_Z ≤ 1 = b_Z − a_Z`), so the fixed form applies.

`#print axioms` on `exists_bw_solution`, `bw_quotient_at`,
`ProximityGapUDTightExample.band_widens`,
`ProximityGapUDTightExample.bw_solution_F5`: `propext`, `Classical.choice`,
`Quot.sound`. -/

end Minidregg.Selvage
