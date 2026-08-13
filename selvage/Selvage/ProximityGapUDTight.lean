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
3. *The one hard rung, named* (`PolishchukSpielman`, `[PROXGAP-BW-ps]`):
   BCIKS Lemma 4.4 — the Polishchuk–Spielman bivariate divisibility lemma
   ([Spi95] Lemma 4.2.18 after the eprint's Appendix-D reduction): from
   `A(x, Z) ∣ B(x, Z)` on `n_X` columns, `A(X, z) ∣ B(X, z)` on `n_Z` rows,
   and the three degree inequalities (the third is EXACTLY where `|S| > n`
   is spent, and is what prices `err = n/|F|`), conclude `A ∣ B` in
   `F[X, Z]`. Carried as the HYPOTHESIS `hPS`, stated in full precision as
   a `Prop` about bivariate polynomials — real content, its premises PROVED
   inhabited at a concrete instance below, never assumed, never `True`.
4. *The assembly, PROVED from the quotient* (inside
   `correlatedAgreement_of_close_card_full`): `P := B/A` has `deg_X P < d`
   (its high coefficients — Z-polynomials of degree ≤ e + 1, by the
   Z-degree-of-quotient lemma `ZDegLE.of_mul_left` — vanish on `> e + 1`
   specializations), `P` reproduces the received line on the `≥ n − e`
   domain points where `A(x, Z) ≠ 0`, and Lagrange interpolation through
   `d` of them forces `P = v₀ + Z·v₁` with `v₀, v₁` HONEST codewords —
   correlated agreement of `(u₀, u₁)` on ONE set of `≥ (1 − δ)n` points.

**The heads.** `rs_proximityGap_UD_full` — the two-case gap at
`d < (1 − 2δ)·n` (the FULL unique-decoding band, vs the landed
`(1 − 3δ)·n`) with the SAME `err = n/|F|`; `reedSolomonCode_isProximityGenerator_UD_full`
(`B = (1 + ρ)/2` — Cor 4.11's printed constant, no longer `(2 + ρ)/3`);
`hasMutualCorrelatedAgreement_UD_full` (mutual CA on all of UD);
`foldDistancePreserving_UD_full`. ALL carry `hPS` explicitly: covered scope
in the same sentence as the claim — the full-band gap is PROVED MODULO the
Polishchuk–Spielman lemma, and `(1 − ρ)/3` remains the unconditional floor
(`Selvage/ProximityGapUD.lean`, untouched, still the realizer consumers use).

**Honest scope limits.** (i) Nothing here is unconditional beyond what is
itemized in the ledger: the BW system + its solution, the specialization
quotients, the Z-degree calculus, the quotient assembly, and the numeric
teeth are PROVED; the single named gap is `[PROXGAP-BW-ps]`. (ii) The
residual is REAL mathematics with a real proof in the literature (resultants
+ derivative-of-determinant multiplicities + Gauss's lemma — [Spi95]
pp. 94–98); it is carried as a hypothesis precisely because that proof is a
formalization project of its own, not because it is doubtful. (iii) `ℓ = 2`
(the affine pair generator), as everywhere in the landed stack.
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

/-! ## `[PROXGAP-BW-ps]` — the Polishchuk–Spielman rung, stated sharp

The ONE unproved step of the BCIKS Thm 4.1 route. Everything feeding it and
everything consuming it is proved in this file; its premises are exhibited
inhabited (`PSExample` below); its own proof — [Spi95] Lemma 4.2.18 via
resultants, derivative-of-determinant root multiplicities, and Gauss's
lemma, reduced to here exactly as in BCIKS 2020/654 Appendix D — is real
future formalization work, not attempted, never assumed elsewhere. -/

/-- **BCIKS 2020/654 Lemma 4.4 (Polishchuk–Spielman bivariate divisibility,
[Spi95] Lemma 4.2.18), ℕ-cleared form.** If `A(x, Z) ∣ B(x, Z)` in `F[Z]`
for every `x` in a set `SX`, `A(X, z) ∣ B(X, z)` in `F[X]` for every `z` in
a set `SZ`, and the bidegree bounds `(aX, aZ)` of `A` and `(bX, bZ)` of `B`
satisfy (1) `aX + bX < |SX|`, (2) `aZ + bZ < |SZ|`, and (3)
`bX/|SX| + bZ/|SZ| < 1` (cleared: `bX·|SZ| + bZ·|SX| < |SX|·|SZ|`), then
`A ∣ B` in `F[Z][X]`. Condition (3) is EXACTLY where the `|S| > n` challenge
count is spent — it is what prices `err = n/|F|` on the full band. -/
def PolishchukSpielman (F : Type*) [Field F] : Prop :=
  ∀ (A B : Polynomial (Polynomial F)) (SX SZ : Finset F) (aX aZ bX bZ : ℕ),
    A.natDegree ≤ aX → ZDegLE A aZ → B.natDegree ≤ bX → ZDegLE B bZ →
    (∀ x ∈ SX, A.eval (C x) ∣ B.eval (C x)) →
    (∀ z ∈ SZ, A.map (evalRingHom z) ∣ B.map (evalRingHom z)) →
    aX + bX < SX.card → aZ + bZ < SZ.card →
    bX * SZ.card + bZ * SX.card < SX.card * SZ.card →
    A ∣ B

/-! ## The full-band correlated-agreement core -/

omit [DecidableEq ι] in
/-- The domain points where a nonzero `A ∈ F[Z][X]` does not vanish
identically in `Z` number at least `n − deg_X A` — `A` has at most
`deg_X A` roots in the domain `F[Z]`. -/
private theorem card_eval_ne_zero (dom : ι ↪ F) {A : Polynomial (Polynomial F)}
    (hA : A ≠ 0) {e : ℕ} (hAdeg : A.natDegree ≤ e) :
    Fintype.card ι
      ≤ (Finset.univ.filter fun i => A.eval (C (dom i)) ≠ 0).card + e := by
  classical
  have hsub : ((Finset.univ.filter fun i => ¬ A.eval (C (dom i)) ≠ 0).image
      fun i => C (dom i)).val ⊆ A.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Polynomial.mem_roots hA]
    exact not_not.mp (Finset.mem_filter.mp hi).2
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [card_image_Cdom dom] at hcard
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => A.eval (C (dom i)) ≠ 0)
  rw [Finset.card_univ] at hsplit
  omega

/-- **The full-band correlated-agreement core, counting form (field-size
free)** — BCIKS Thm 4.1 via Berlekamp–Welch over `F[Z]`, MODULO the
Polishchuk–Spielman rung `hPS`. If the line `f 0 + γ • f 1` is δ-close to
`RS[dom, d]` for MORE THAN `n` challenges, with `d < (1 − 2δ)·n` — the FULL
unique-decoding band — then the pair has correlated agreement at radius δ:
one common agreement set of `≥ (1 − δ)·n` coordinates. -/
theorem correlatedAgreement_of_close_card_full [Nonempty ι]
    (hPS : PolishchukSpielman F) (dom : ι ↪ F) {d : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : (d : ℝ) < (1 - 2 * δ) * (Fintype.card ι : ℝ))
    {f : Fin 2 → ι → F} {S : Finset F}
    (hSclose : ∀ γ ∈ S, close δ (reedSolomonCode dom d) (f 0 + γ • f 1))
    (hScard : Fintype.card ι < S.card) :
    CorrelatedAgreement (reedSolomonCode dom d) δ f := by
  classical
  set n := Fintype.card ι with hnn
  have hn : (0 : ℝ) < (n : ℝ) := by
    rw [hnn]; exact_mod_cast Fintype.card_pos
  -- e is kept opaque (an fvar with a defining equation, not a let-binding)
  -- so that `omega` can treat it as an atom downstream
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = ⌊δ * (n : ℝ)⌋₊ := ⟨_, rfl⟩
  have heδ : (e : ℝ) ≤ δ * (n : ℝ) := by
    rw [he]; exact Nat.floor_le (by positivity)
  -- the governing count: d + 2e < n
  have harith : d + (e + e) < n := by
    have : (d : ℝ) + ((e : ℝ) + (e : ℝ)) < (n : ℝ) := by nlinarith
    exact_mod_cast this
  set n' : ℕ := n - e with hn'
  have hne : n' + e = n := Nat.sub_add_cancel (by omega)
  have hn'0 : 0 < n' := by omega
  have hSn : n < S.card := hScard
  -- per-challenge close witnesses, in polynomial form
  have hex : ∀ γ ∈ S, ∃ p : Polynomial F, p.degree < (d : WithBot ℕ) ∧
      ∃ T : Finset ι, n ≤ T.card + e ∧
        ∀ i ∈ T, (f 0 + γ • f 1) i = p.eval (dom i) := by
    intro γ hγ
    obtain ⟨w, hwC, T, hTcard, hTag⟩ := exists_agreesOn_of_close (hSclose γ hγ)
    obtain ⟨p, hpdeg, hpw⟩ := mem_reedSolomonCode_iff.mp hwC
    refine ⟨p, hpdeg, T, ?_, fun i hi => by rw [hTag i hi, hpw i]⟩
    have hTn : T.card ≤ n := by rw [hnn]; exact_mod_cast Finset.card_le_univ T
    have hfloor : n - T.card ≤ e := by
      rw [he]
      refine Nat.le_floor ?_
      have : ((n - T.card : ℕ) : ℝ) = (n : ℝ) - (T.card : ℝ) := by
        rw [Nat.cast_sub hTn]
      rw [this]
      nlinarith
    omega
  choose! p hpdeg T hTcard hTag using hex
  -- the Berlekamp–Welch pair
  obtain ⟨A, B, hA0, hAdeg, hAz, hBdeg, hBz, hsys⟩ :=
    exists_bw_solution dom f hne hn'0
  -- z-side divisibility on ALL of S
  have hzdvd : ∀ z ∈ S, A.map (evalRingHom z) ∣ B.map (evalRingHom z) := by
    intro z hz
    by_cases hAzz : A.map (evalRingHom z) = 0
    · -- the specialized B vanishes on the whole domain, hence is 0
      have hB0 : B.map (evalRingHom z) = 0 := by
        refine eq_zero_of_eval_zero_on (S := Finset.univ.image dom) ?_
          fun x hx => ?_
        · rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ]
          have := natDegree_map_le (f := evalRingHom z) (p := B)
          omega
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
          have := bw_specialize hsys z i
          rw [hAzz] at this
          simpa using this.symm
      rw [hB0]
      exact dvd_zero _
    · -- Berlekamp–Welch uniqueness delivers the quotient
      exact ⟨p z, bw_quotient_at dom hne harith
        (le_trans (natDegree_map_le) hAdeg)
        (lt_of_le_of_lt (natDegree_map_le) hBdeg)
        (hpdeg z hz) (hTcard z hz)
        (fun i hi => by
          have := hTag z hz i hi
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this)
        (bw_specialize hsys z)⟩
  -- x-side divisibility on the whole domain (the system IS the witness)
  have hxdvd : ∀ x ∈ Finset.univ.image dom, A.eval (C x) ∣ B.eval (C x) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨lineAt f i, (hsys i).symm⟩
  -- the Polishchuk–Spielman inequalities
  have hSXcard : (Finset.univ.image dom).card = n := by
    rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ]
  have hc1 : e + (n' - 1) < (Finset.univ.image dom).card := by
    rw [hSXcard]; omega
  have hc2 : e + (e + 1) < S.card := by omega
  have hc3 : (n' - 1) * S.card + (e + 1) * (Finset.univ.image dom).card
      < (Finset.univ.image dom).card * S.card := by
    rw [hSXcard]
    have hs : n < S.card := hScard
    calc (n' - 1) * S.card + (e + 1) * n
        < (n' - 1) * S.card + (e + 1) * S.card :=
          Nat.add_lt_add_left (mul_lt_mul_of_pos_left hs (by omega)) _
      _ = ((n' - 1) + (e + 1)) * S.card := by ring
      _ = n * S.card := by
          congr 1
          omega
  -- the divisibility rung
  obtain ⟨P, hBP⟩ := hPS A B (Finset.univ.image dom) S e e (n' - 1) (e + 1)
    hAdeg hAz (by omega) hBz hxdvd hzdvd hc1 hc2 hc3
  -- the good domain points, shared by both endgames
  set D' : Finset ι := Finset.univ.filter fun i => A.eval (C (dom i)) ≠ 0
    with hD'
  have hD'card : n ≤ D'.card + e := card_eval_ne_zero dom hA0 hAdeg
  have hD'real : (1 - δ) * (n : ℝ) ≤ (D'.card : ℝ) := by
    have h1 : (n : ℝ) - (e : ℝ) ≤ (D'.card : ℝ) := by
      have : ((D'.card + e : ℕ) : ℝ) = (D'.card : ℝ) + (e : ℝ) := by push_cast; rfl
      have h2 : (n : ℝ) ≤ (D'.card : ℝ) + (e : ℝ) := by
        rw [← this]; exact_mod_cast hD'card
      linarith
    nlinarith
  rcases eq_or_ne P 0 with rfl | hP0
  · -- degenerate quotient: B = 0, the line vanishes on D′ — agreement with 0
    rw [mul_zero] at hBP
    refine ⟨D', hD'real, fun j => ⟨0, Submodule.zero_mem _, fun i hi => ?_⟩⟩
    have hiA : A.eval (C (dom i)) ≠ 0 := (Finset.mem_filter.mp hi).2
    have hline : lineAt f i = 0 := by
      have h1 := hsys i
      rw [hBP] at h1
      simp only [eval_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left hiA
    have h0 : f 0 i = 0 := by
      have := lineAt_coeff_zero f i
      rw [hline] at this
      simpa using this.symm
    have h1 : f 1 i = 0 := by
      have := lineAt_coeff_one f i
      rw [hline] at this
      simpa using this.symm
    induction j using Fin.cases with
    | zero => simpa using h0
    | succ jj =>
        have hj : jj.succ = (1 : Fin 2) := by fin_cases jj; rfl
        rw [hj]
        simpa using h1
  · -- main path: the quotient inherits Z-degree ≤ e + 1
    have hPz : ZDegLE P (e + 1) := ZDegLE.of_mul_left hA0 hP0 (hBP ▸ hBz)
    -- the good challenges: A(X, z) survives specialization
    set S' : Finset F := S.filter fun z => A.map (evalRingHom z) ≠ 0 with hS'
    have hS'card : S.card ≤ S'.card + e := by
      -- the bad challenges are roots of the nonzero leading coefficient of A
      have hi₀ : A.coeff A.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hA0
      have hbad : (S.filter fun z => ¬ A.map (evalRingHom z) ≠ 0).card ≤ e := by
        by_contra hcon
        apply hi₀
        refine eq_zero_of_eval_zero_on
          (S := S.filter fun z => ¬ A.map (evalRingHom z) ≠ 0) ?_ fun z hz => ?_
        · have : (A.coeff A.natDegree).natDegree ≤ e :=
            natDegree_le_iff_degree_le.mpr (hAz A.natDegree)
          omega
        · have hz0 := not_not.mp (Finset.mem_filter.mp hz).2
          have := congrArg (fun q => q.coeff A.natDegree) hz0
          simpa [Polynomial.coeff_map] using this
      have hsplit : S'.card
          + (S.filter fun z => ¬ A.map (evalRingHom z) ≠ 0).card = S.card := by
        rw [hS']
        exact Finset.card_filter_add_card_filter_not (s := S) _
      omega
    -- on the good challenges the quotient specializes to the close codeword
    have hPspec : ∀ z ∈ S', P.map (evalRingHom z) = p z := by
      intro z hz
      obtain ⟨hzS, hzA⟩ := Finset.mem_filter.mp hz
      have h1 : B.map (evalRingHom z)
          = A.map (evalRingHom z) * P.map (evalRingHom z) := by
        rw [hBP, Polynomial.map_mul]
      have h2 : B.map (evalRingHom z) = A.map (evalRingHom z) * p z :=
        bw_quotient_at dom hne harith
          (le_trans (natDegree_map_le) hAdeg)
          (lt_of_le_of_lt (natDegree_map_le) hBdeg)
          (hpdeg z hzS) (hTcard z hzS)
          (fun i hi => by
            have := hTag z hzS i hi
            simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this)
          (bw_specialize hsys z)
      exact mul_left_cancel₀ hzA (h1.symm.trans h2)
    -- Step 3: the quotient has X-degree < d
    have hPdeg : P.degree < (d : WithBot ℕ) := by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro i hi
      have hid : d ≤ i := by exact_mod_cast hi
      refine eq_zero_of_eval_zero_on (S := S') ?_ fun z hz => ?_
      · have h1 : (P.coeff i).natDegree ≤ e + 1 :=
          natDegree_le_iff_degree_le.mpr (hPz i)
        omega
      · have h2 := hPspec z hz
        have h3 : (P.map (evalRingHom z)).coeff i = (p z).coeff i := by rw [h2]
        rw [Polynomial.coeff_map] at h3
        have h4 : (p z).coeff i = 0 := by
          refine Polynomial.coeff_eq_zero_of_degree_lt ?_
          exact lt_of_lt_of_le (hpdeg z (Finset.mem_filter.mp hz).1)
            (by exact_mod_cast hid)
        simpa [h4] using h3
    -- Step 4: the quotient reproduces the line on D′
    have hPline : ∀ i ∈ D', lineAt f i = P.eval (C (dom i)) := by
      intro i hi
      have hiA : A.eval (C (dom i)) ≠ 0 := (Finset.mem_filter.mp hi).2
      have h1 := hsys i
      rw [hBP, Polynomial.eval_mul] at h1
      exact mul_left_cancel₀ hiA h1
    -- Step 5: interpolate through d good points; the quotient is the line
    obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq
      (s := D') (n := d) (by omega)
    have hT₀inj : Set.InjOn dom T₀ := dom.injective.injOn
    set v₀ : Polynomial F := Lagrange.interpolate T₀ (⇑dom) (f 0) with hv₀
    set v₁ : Polynomial F := Lagrange.interpolate T₀ (⇑dom) (f 1) with hv₁
    have hv₀deg : v₀.degree < (d : WithBot ℕ) := by
      rw [hv₀, ← hT₀card]
      exact Lagrange.degree_interpolate_lt _ hT₀inj
    have hv₁deg : v₁.degree < (d : WithBot ℕ) := by
      rw [hv₁, ← hT₀card]
      exact Lagrange.degree_interpolate_lt _ hT₀inj
    set CF : F →+* Polynomial F := Polynomial.C with hCF
    set Pline : Polynomial (Polynomial F) :=
      v₀.map CF + Polynomial.C (Polynomial.X : Polynomial F) * v₁.map CF
      with hPline'
    have hmapeval : ∀ (v : Polynomial F) (x : F),
        (v.map CF).eval (C x) = CF (v.eval x) := by
      intro v x
      rw [eval_map, show (C x : Polynomial F) = CF x from rfl,
        eval₂_at_apply]
    have hPlineEval : ∀ x : F, Pline.eval (C x)
        = CF (v₀.eval x) + Polynomial.X * CF (v₁.eval x) := by
      intro x
      rw [hPline', eval_add, eval_mul, eval_C, hmapeval, hmapeval]
    have hPlineDeg : Pline.degree < (d : WithBot ℕ) := by
      rw [hPline']
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (degree_map_le) hv₀deg
      · calc (Polynomial.C (Polynomial.X : Polynomial F) * v₁.map CF).degree
            ≤ (Polynomial.C (Polynomial.X : Polynomial F)).degree
              + (v₁.map CF).degree := degree_mul_le _ _
          _ ≤ 0 + (v₁.map CF).degree := add_le_add degree_C_le (le_refl _)
          _ = (v₁.map CF).degree := zero_add _
          _ ≤ v₁.degree := degree_map_le
          _ < (d : WithBot ℕ) := hv₁deg
    have hPeqLine : P = Pline := by
      rw [← sub_eq_zero]
      refine eq_zero_of_eval_zero_on (S := T₀.image fun i => C (dom i)) ?_
        fun x hx => ?_
      · rw [card_image_Cdom dom, hT₀card]
        rcases eq_or_ne (P - Pline) 0 with h0 | h0
        · rw [h0]
          simp only [natDegree_zero]
          by_contra hd0
          -- d = 0 forces P = 0, contradicting hP0
          have hdz : d = 0 := by omega
          apply hP0
          refine Polynomial.ext fun i => ?_
          rw [Polynomial.coeff_zero]
          exact (Polynomial.degree_lt_iff_coeff_zero P d).mp hPdeg i (by omega)
        · exact (natDegree_lt_iff_degree_lt h0).mpr
            (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hPdeg hPlineDeg))
      · obtain ⟨i, hiT₀, rfl⟩ := Finset.mem_image.mp hx
        have hiD' : i ∈ D' := hT₀sub hiT₀
        rw [eval_sub, ← hPline i hiD', hPlineEval]
        have h0 : v₀.eval (dom i) = f 0 i :=
          Lagrange.eval_interpolate_at_node _ hT₀inj hiT₀
        have h1 : v₁.eval (dom i) = f 1 i :=
          Lagrange.eval_interpolate_at_node _ hT₀inj hiT₀
        rw [h0, h1, lineAt]
        show C (f 0 i) + C (f 1 i) * X - (C (f 0 i) + X * C (f 1 i)) = 0
        ring
    -- extract the coordinatewise agreement on D′
    have hagree : ∀ i ∈ D', f 0 i = v₀.eval (dom i) ∧ f 1 i = v₁.eval (dom i) := by
      intro i hi
      have h1 : lineAt f i = Pline.eval (C (dom i)) := by
        rw [← hPeqLine]; exact hPline i hi
      rw [hPlineEval] at h1
      have hc0 := congrArg (fun q => q.coeff 0) h1
      have hc1 := congrArg (fun q => q.coeff 1) h1
      simp only [lineAt_coeff_zero, lineAt_coeff_one] at hc0 hc1
      constructor
      · rw [hc0]
        show (CF (v₀.eval (dom i)) + Polynomial.X * CF (v₁.eval (dom i))).coeff 0
          = v₀.eval (dom i)
        simp [hCF, coeff_C]
      · rw [hc1]
        show (CF (v₀.eval (dom i)) + Polynomial.X * CF (v₁.eval (dom i))).coeff 1
          = v₁.eval (dom i)
        simp [hCF, coeff_C]
    -- assemble correlated agreement
    refine ⟨D', hD'real, fun j => ?_⟩
    induction j using Fin.cases with
    | zero =>
        refine ⟨fun i => v₀.eval (dom i),
          mem_reedSolomonCode_iff.mpr ⟨v₀, hv₀deg, fun i => rfl⟩,
          fun i hi => (hagree i hi).1⟩
    | succ jj =>
        have hj : jj.succ = (1 : Fin 2) := by fin_cases jj; rfl
        rw [hj]
        refine ⟨fun i => v₁.eval (dom i),
          mem_reedSolomonCode_iff.mpr ⟨v₁, hv₁deg, fun i => rfl⟩,
          fun i hi => (hagree i hi).2⟩

/-! ## The gap heads on the FULL unique-decoding band -/

/-- **`rs_proximityGap_UD_full` — the RS proximity gap at the FULL
unique-decoding radius, two-case form, MODULO `[PROXGAP-BW-ps]`.** Same shape
as the landed `rs_proximityGap_UD`, hypothesis relaxed from `d < (1 − 3δ)·n`
to `d < (1 − 2δ)·n` (all of `δ ∈ (0, (1 − ρ)/2)`), same `err = n/|F|`:
either at most an `n/|F|` fraction of challenges lands the affine line
δ-close, or the pair has full correlated agreement at radius δ. -/
theorem rs_proximityGap_UD_full [Nonempty ι] [Fintype F]
    (hPS : PolishchukSpielman F) (dom : ι ↪ F) {d : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : (d : ℝ) < (1 - 2 * δ) * (Fintype.card ι : ℝ))
    (f : Fin 2 → ι → F) :
    (affineGenerator F).pr
        (fun r => close δ (reedSolomonCode dom d) (comb r f))
      ≤ (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
    ∨ CorrelatedAgreement (reedSolomonCode dom d) δ f := by
  classical
  set C' := reedSolomonCode dom d with hC'
  by_cases hpr : (affineGenerator F).pr (fun r => close δ C' (comb r f))
      ≤ (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
  · exact Or.inl hpr
  right
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  set S : Finset F := Finset.univ.filter
    (fun γ => close δ C' (f 0 + γ • f 1)) with hS
  -- the closeness probability is the close-challenge fraction
  have hpr_eq : (affineGenerator F).pr (fun r => close δ C' (comb r f))
      = (S.card : ℝ) / (Fintype.card F : ℝ) := by
    unfold ProximityGenerator.pr
    have hcomb : ∀ γ : F, comb ((affineGenerator F).gen γ) f = f 0 + γ • f 1 :=
      fun γ => funext fun x => by rw [comb_affineGenerator]; rfl
    have hfilter : (Finset.univ.filter fun ω : (affineGenerator F).Seed =>
        close δ C' (comb ((affineGenerator F).gen ω) f)) = S := by
      rw [hS]
      refine Finset.filter_congr fun γ _ => ?_
      rw [hcomb γ]
    rw [hfilter]
    calc ∑ ω ∈ S, (affineGenerator F).weight ω
        = ∑ _ω ∈ S, ((Fintype.card F : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun ω _ => rfl
      _ = (S.card : ℝ) * ((Fintype.card F : ℝ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (S.card : ℝ) / (Fintype.card F : ℝ) := (div_eq_mul_inv _ _).symm
  -- more than n close challenges
  have hSn : Fintype.card ι < S.card := by
    rw [hpr_eq] at hpr
    have h := not_le.mp hpr
    rw [div_lt_div_iff_of_pos_right hF] at h
    exact_mod_cast h
  exact correlatedAgreement_of_close_card_full hPS dom hδ0 hδ2
    (fun γ hγ => (Finset.mem_filter.mp hγ).2) hSn

/-- **The hPG realizer on the FULL unique-decoding band, MODULO
`[PROXGAP-BW-ps]`:** the affine generator PG(2) is a proximity generator for
`RS[dom, d]` with bound `B = (1 + ρ)/2` — Cor 4.11's printed constant, the
whole band `δ ∈ (0, (1 − ρ)/2)`, vs the landed unconditional `(2 + ρ)/3` —
and error `err = n/|F|`. -/
theorem reedSolomonCode_isProximityGenerator_UD_full [Nonempty ι] [Fintype F]
    (hPS : PolishchukSpielman F) (dom : ι ↪ F) (d : ℕ) :
    IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  intro f δ hδ0 hδB hpr
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδ2 : (d : ℝ) < (1 - 2 * δ) * (Fintype.card ι : ℝ) := by
    -- δ < 1 − (1 + ρ)/2 = (1 − ρ)/2  ⟺  ρ < 1 − 2δ  ⟺  d < (1 − 2δ)n
    have hρ : (d : ℝ) / (Fintype.card ι : ℝ) < 1 - 2 * δ := by linarith
    calc (d : ℝ) = (d : ℝ) / (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) := by
          field_simp
      _ < (1 - 2 * δ) * (Fintype.card ι : ℝ) :=
          mul_lt_mul_of_pos_right hρ hn
  rcases rs_proximityGap_UD_full hPS dom hδ0 hδ2 f with h | h
  · exact absurd hpr (not_lt.mpr h)
  · exact h

/-- **Mutual correlated agreement on the FULL unique-decoding band, MODULO
`[PROXGAP-BW-ps]`.** The landed WHIR Lemma 4.10 / Corollary 4.11 machinery
(`reedSolomonCode_hasMutualCorrelatedAgreement`, CITED, not re-derived) fed
the full-band realizer: `B⋆ = max(1 − dC/2, (1 + ρ)/2)` collapses to
`(1 + ρ)/2` (the exact half-distance point `(n + d − 1)/(2n)` sits `1/(2n)`
below it), same error `n/|F|`. With the residual discharged this would put
every hPG consumer hypothesis-free on ALL of `δ ∈ (0, (1 − ρ)/2)`. -/
theorem hasMutualCorrelatedAgreement_UD_full [Nonempty ι] [Fintype F]
    (hPS : PolishchukSpielman F) (dom : ι ↪ F) (d : ℕ) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F)
    dom d (reedSolomonCode_isProximityGenerator_UD_full hPS dom d)
    (fun _ _ _ => le_refl _)
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hle : 1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2
      ≤ (1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2 := by
    have hsub : ((d : ℝ) - 1) / (Fintype.card ι : ℝ)
        = (d : ℝ) / (Fintype.card ι : ℝ) - 1 / (Fintype.card ι : ℝ) :=
      sub_div _ _ _
    have h1n : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
    rw [hsub]
    linarith
  rwa [max_eq_right hle] at h

/-- **`[PROX-fold-distance]` on the FULL unique-decoding band, MODULO
`[PROXGAP-BW-ps]`:** one FRI fold round preserves δ-farness off at most `|κ|`
challenges for every `δ ∈ (0, (1 − ρ_κ)/2)` at the folded rate
`ρ_κ = d/|κ|` — the landed reduction of `Selvage/Proximity.lean` (CITED) fed
the full-band realizer. -/
theorem foldDistancePreserving_UD_full {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype F] [Nonempty ι] [Nonempty κ] {dom : ι ↪ F} {domSq : κ ↪ F}
    (hPS : PolishchukSpielman F) (D : FoldingData F dom domSq) (d : ℕ)
    {δ : ℝ} (hδ0 : 0 < δ)
    (hδB : δ < 1 - (1 + (d : ℝ) / (Fintype.card κ : ℝ)) / 2) :
    FoldDistancePreserving D (2 * d) d δ (Fintype.card κ) := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact foldDistancePreserving_of_isProximityGenerator D d
    (reedSolomonCode_isProximityGenerator_UD_full hPS domSq d) hδ0 hδB
    (le_of_eq (div_mul_cancel₀ _ (ne_of_gt hF)))

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The landed `RS[F₅, {0,1,2,3}, 2]` (ρ = 1/2). The full-UD band at this code is
`δ ∈ (0, 1/4)`; the landed unconditional band is `(0, 1/6)`. δ = 1/5 sits
STRICTLY BETWEEN — the extension is macroscopic even at the toy. What the
keystones exhibit:

* **the band widens for real** (`band_widens`, UNCONDITIONAL): at δ = 1/5 the
  landed hypothesis `d < (1 − 3δ)n` FAILS and the full-band hypothesis
  `d < (1 − 2δ)n` HOLDS — the new theorem speaks where the old is silent.
* **the Berlekamp–Welch system FIRES** (`bw_solution_F5`, UNCONDITIONAL): the
  proved existence theorem delivers a nonzero solution with the BCIKS degree
  profile at the concrete code — premise inhabitation for everything
  downstream of the system.
* **the residual's premises are inhabitable** (`ps_premises_inhabited`,
  UNCONDITIONAL): a concrete bivariate pair over F₅ satisfies EVERY premise
  of `[PROXGAP-BW-ps]` with the conclusion checkable — the hypothesis
  quantifies over a nonempty domain; assuming it is not vacuous.
* **conditional end-to-end** (`good_line_CA_fullBand`): given `hPS`, the
  all-codeword line has correlated agreement at δ = 1/5 — OUTSIDE the landed
  band — through the full pipeline (system → specialization → quotient →
  interpolation). -/

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

/-- The premises of `[PROXGAP-BW-ps]` are INHABITED over F₅: the pair
`A = 1`, `B = X + Z` (the lifted line `x + z`) satisfies every hypothesis
field of `PolishchukSpielman` with the conclusion holding — the residual
quantifies over a nonempty, nonvacuous domain. -/
theorem ps_premises_inhabited :
    ∃ (A B : Polynomial (Polynomial (ZMod 5))) (SX SZ : Finset (ZMod 5)),
      A.natDegree ≤ 0 ∧ ZDegLE A 0 ∧ B.natDegree ≤ 3 ∧ ZDegLE B 1 ∧
      (∀ x ∈ SX, A.eval (C x) ∣ B.eval (C x)) ∧
      (∀ z ∈ SZ, A.map (evalRingHom z) ∣ B.map (evalRingHom z)) ∧
      0 + 3 < SX.card ∧ 0 + 1 < SZ.card ∧
      3 * SZ.card + 1 * SX.card < SX.card * SZ.card ∧ A ∣ B := by
  have hcard : (Finset.univ : Finset (ZMod 5)).card = 5 := by
    rw [Finset.card_univ, ZMod.card]
  refine ⟨1, Polynomial.X + Polynomial.C Polynomial.X,
    Finset.univ, Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, one_dvd _⟩
  · simp
  · intro i
    simp only [Polynomial.coeff_one]
    split_ifs <;> simp
  · refine le_trans (natDegree_add_le _ _) ?_
    simp [natDegree_X]
  · intro i
    rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs with h1 h2
    · omega
    · rw [add_zero]
      refine le_trans (degree_one_le (R := ZMod 5)) ?_
      exact_mod_cast Nat.zero_le 1
    · rw [zero_add]
      exact_mod_cast degree_X_le
    · simp
  · intro x _
    rw [Polynomial.eval_one]
    exact one_dvd _
  · intro z _
    rw [Polynomial.map_one]
    exact one_dvd _
  · rw [hcard]; omega
  · rw [hcard]; omega
  · rw [hcard]; omega

/-- **Conditional end-to-end at δ = 1/5 — outside the landed band**: given
the residual, the all-codeword line `xWord + γ·oneWord` has correlated
agreement at radius 1/5 through the full Berlekamp–Welch pipeline. Compare
`ProximityGapUDExample.good_line_CA`, capped at δ < 1/6. -/
theorem good_line_CA_fullBand (hPS : PolishchukSpielman (ZMod 5)) :
    CorrelatedAgreement (reedSolomonCode dom₅ 2) (1/5 : ℝ)
      ![xWord, oneWord] := by
  refine correlatedAgreement_of_close_card_full hPS dom₅ (by norm_num)
    (by norm_num [Fintype.card_fin]) (S := Finset.univ)
    (fun γ _ => ?_) ?_
  · have hmem : xWord + γ • oneWord ∈ reedSolomonCode dom₅ 2 := line_mem γ
    exact close_of_mem hmem (by norm_num)
  · rw [Finset.card_univ, ZMod.card, Fintype.card_fin]
    omega

end ProximityGapUDTightExample

/-! ## Residual obligation — `[PROXGAP-BW-ps]`, prose not stub

What CLOSED here (all UNCONDITIONAL):

* `exists_bw_solution` — the Berlekamp–Welch interpolation system over
  `F[Z]` has a nonzero solution with EXACTLY the BCIKS degree profile
  (`deg_X A ≤ e`, `deg_Z A ≤ e`, `deg_X B < n − e`, `deg_Z B ≤ e + 1`,
  `A ≠ 0`), by rank-nullity on the padded system — the step BCIKS obtain
  from the vanishing of every maximal minor (a degree-`≤ e + 1` polynomial
  in `Z` killed by `> e + 1` close challenges). The padding to
  `deg_X B < n − e` makes existence free and moves the ENTIRE `|S| > n`
  budget into Polishchuk–Spielman condition (3), where BCIKS's own proof
  spends it; the task-brief's "nonzero maximal minor of degree ≤ n" rank
  lemma is thereby OBVIATED, not skipped — no minor is needed by any
  surviving step.
* `bw_quotient_at` / `bw_specialize` / `map_evalRingHom_eval` — every close
  challenge's specialization is a BW solution and yields the close codeword
  as exact quotient (`B(X,z) = A(X,z)·p_z`); every close challenge gives
  `A(X,z) ∣ B(X,z)` (zero specializations vanish identically). The radius
  arithmetic here is `2e + d ≤ n` — the FULL `(1 − ρ)/2`, the whole point.
* `ZDegLE` calculus with `ZDegLE.of_mul_left` — the Z-degree of a factor is
  bounded by the product's (top Z-slices multiply in a domain): the honest
  version of BCIKS's silent "the quotient has `deg_Z ≤ e + 1`".
* `correlatedAgreement_of_close_card_full` — BCIKS §4.3 Steps 3–5 in full:
  X-degree trim of the quotient by specialization counting, line
  reproduction on the `≥ n − e` good domain points, Lagrange interpolation
  pinning `P = v₀ + Z·v₁`, coefficientwise extraction to ONE common
  agreement set of `≥ (1 − δ)n` coordinates — given `hPS`.
* The four heads (`rs_proximityGap_UD_full`,
  `reedSolomonCode_isProximityGenerator_UD_full` at `B = (1 + ρ)/2`,
  `hasMutualCorrelatedAgreement_UD_full`, `foldDistancePreserving_UD_full`)
  — each PROVED from `hPS`, with the landed Lemma 4.10 / fold reductions
  CITED, not re-derived.
* Keystones — `band_widens` (the extension is macroscopic at the toy,
  unconditionally), `bw_solution_F5` (the system fires), 
  `ps_premises_inhabited` (the residual's premise set is nonvacuous),
  `good_line_CA_fullBand` (conditional end-to-end at δ = 1/5 ∉ old band).

What REMAINS — exactly ONE statement, named:

* **`[PROXGAP-BW-ps]`: `PolishchukSpielman F`** — BCIKS 2020/654 Lemma 4.4,
  i.e. [Spi95] Lemma 4.2.18 after the Appendix-D degree reduction: bivariate
  divisibility from row/column divisibility under the three degree
  inequalities. Its literature proof: WLOG `gcd(A, B) = 1` (divide by the
  gcd, restricting to the rows/columns where it survives — the parameter sum
  only shrinks); then view `A, B ∈ F(x)[y]`, form the Sylvester resultant
  `R(x)` (nonzero by coprimality + Gauss's lemma), show each of the `n_X`
  column points is a root of multiplicity `≥ deg_Z A · …` via the
  derivative-of-determinant expansion (the specialized system rows are
  dependent, so every determinant in the expansion of `R^{(k)}` keeps rank
  deficit until `k` reaches the row count), and the multiplicity count
  exceeds `deg R` — contradiction. Formalization-sized subprojects: Sylvester
  matrices/resultants over `F[x]`, Hasse-derivative (or row-divisibility)
  multiplicity bounds for determinants of polynomial matrices, coprime-lift
  via Gauss's lemma, and the gcd-reduction bookkeeping. REAL future work; the
  hypothesis is never instantiated by an axiom or a `True`-stub anywhere in
  this tree, and every theorem above states it explicitly in its signature.

Downstream: NOTHING in the landed tree consumes `hPS` silently — the
unconditional floor remains `Selvage/ProximityGapUD.lean`'s `(1 − ρ)/3`
realizer, and the consumers keep firing on that band exactly as before. When
`[PROXGAP-BW-ps]` is discharged, the four heads above make every hPG
consumer hypothesis-free on ALL of UD with `err = n/|F|`, and
`[PROXGAP-tight]`(a) closes.

`#print axioms` on `exists_bw_solution`, `bw_quotient_at`,
`correlatedAgreement_of_close_card_full`, `rs_proximityGap_UD_full`,
`hasMutualCorrelatedAgreement_UD_full`, `foldDistancePreserving_UD_full`,
`ProximityGapUDTightExample.band_widens`,
`ProximityGapUDTightExample.bw_solution_F5`,
`ProximityGapUDTightExample.ps_premises_inhabited`,
`ProximityGapUDTightExample.good_line_CA_fullBand`:
`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx` in this file.
(`hPS` is a HYPOTHESIS, visible in every signature that needs it, not an
axiom.) -/

end Minidregg.Selvage
