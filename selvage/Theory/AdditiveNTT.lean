/-
# Theory.AdditiveNTT — [BTOWER-additive-fri] the additive-NTT substrate: GF(2)-linear
evaluation domains, subspace-vanishing polynomials, the LCH novelpoly basis, and the
additive FRI fold (the Binius code layer the tower deployment needs).

WHY ADDITIVE: GF(2^(2^k)) has multiplicative group of ODD order 2^(2^k) − 1 — there is
no 2-adic multiplicative subgroup, so the standard multiplicative FRI (fold by squaring
over a 2^m-th root of unity) DOES NOT APPLY. What the binary tower has instead is
GF(2)-LINEAR structure: T_m is a GF(2)-vector space, its GF(2)-subspaces play the role
of the 2-adic subgroup chain, and the subspace-vanishing polynomials Ŵ_i (which are
ADDITIVE maps in characteristic 2) play the role of X ↦ X^(2^i). This file builds that
structure (Lin–Chung–Han 2014 "novel polynomial basis" / Binius).

Candidate-independent FIELD MATH over any char-2 field carrying GF(2) = `ZMod 2`
scalars — imports Mathlib + Theory only (boundary enforced by
`scripts/check-import-boundary.sh`).

## What is PROVED here (unconditional)

* `additiveDomain β k : Submodule (ZMod 2) F` — the evaluation domain W_k =
  span_{GF(2)}{β₀,…,β_{k−1}}, with its points `domainPoint β k c = ∑ cⱼ • βⱼ`;
  `additiveDomain_card` — |W_k| = 2^k for GF(2)-linearly-independent β.
* `subspaceVanishing β i` — the subspace-vanishing polynomials in their recursive LCH
  form Ŵ₀ = X, Ŵ_{i+1} = Ŵ_i² + Ŵ_i(β_i)·Ŵ_i (each level ONE FOLD of the previous:
  `subspaceVanishing_succ_eq_fold_comp`), monic of degree 2^i.
* **`subspaceVanishing_additive`** — Ŵ_i(x + y) = Ŵ_i(x) + Ŵ_i(y) for ALL x y ∈ F:
  the vanishing polynomial of a GF(2)-subspace is a GF(2)-LINEAR MAP
  (`subspaceVanishingHom : F →ₗ[ZMod 2] F` packages it). THE structural fact that
  makes the additive NTT/FRI work — the char-2 Frobenius (x+y)² = x²+y² pushed
  through the recursion. This is what replaces X^n − 1 factoring multiplicatively.
* `subspaceVanishing_eq_prod` — for independent β, Ŵ_k REALLY IS ∏_{a ∈ W_k}(X − a)
  (monic, degree 2^k = |W_k|, vanishing exactly on W_k:
  `subspaceVanishing_eval_eq_zero_iff`).
* `novelBasis β k c = ∏ᵢ Ŵ_i^{cᵢ}` — the LCH novelpoly basis, monic with
  `novelBasis_natDegree` = ∑ cᵢ·2^i: the 2^k basis polynomials have the 2^k DISTINCT
  degrees 0,…,2^k − 1 (binary representation) — a triangular basis of degree-< 2^k
  polynomials, which is what the transform residual [ANTT-transform] inverts.
* The ADDITIVE FOLD: `foldMap β x = x² + βx = x(x+β)` — additive (`foldMap_add`),
  kernel EXACTLY {0, β} (`foldMap_eq_zero_iff`), fibers exactly {x, x+β}
  (`foldMap_eq_iff`, `foldMap_two_to_one`): the genuine 2-to-1 GF(2)-linear
  projection W → W/{0,β} that replaces multiplicative squaring.
* `foldPoly_decompose` — the additive even/odd decomposition: every P with
  natDegree ≤ 2d+1 splits as P = P₀∘q_β + X·(P₁∘q_β) with natDegree Pᵢ ≤ d
  (division algorithm by the monic degree-2 fold polynomial, by induction).
* `friFold` — the challenge-λ FRI fold on FUNCTIONS,
  f ↦ (x ↦ f(x) + (x+λ)·(f(x)+f(x+β))/β): well-defined on fold-cosets
  (`friFold_coset_invariant`) and DEGREE-HALVING on polynomial words
  (`friFold_eval_poly`: folding a degree-≤ 2d+1 evaluation word yields a
  degree-≤ d evaluation word on the image domain) — the algebraic
  (completeness) half of the additive FRI fold, closed.
* CONTRAST teeth (why multiplicative FRI cannot run here):
  `charTwo_sq_eq_one_iff` — x² = 1 ↔ x = 1 (no order-2 element; the would-be μ₂ is
  degenerate) and `multiplicative_squaring_injective` — x ↦ x² is INJECTIVE in
  char 2 (Frobenius), i.e. squaring is 1-to-1 and folds NOTHING, while
  `foldMap` is honestly 2-to-1.
* Keystones at the tower (GF(16) = `binaryTower 2`, basis {1, x₁}):
  `keystoneBeta_linearIndependent`, `keystone_domain_card` (a concrete 2-dim
  GF(2)-subspace with 4 points), `keystone_subspaceVanishing_one` (Ŵ₁ = X² + X,
  computed) and `keystone_subspaceVanishing_two` (Ŵ₂ computed in fold form), and
  the TOOTH `keystone_additive_tooth`: Ŵ₁(x₁ + x₁²) = Ŵ₁(x₁) + Ŵ₁(x₁²) with BOTH
  summands provably NONZERO — additivity is exercised where it says something.

## Honest residuals (NAMED, not proved)

* **[ANTT-transform]** `NovelBasisTransform` — the additive NTT itself: for
  independent β over the tower, the coefficient-to-evaluation map (novelpoly
  coefficients ↦ values at the 2^k domain points) is a BIJECTION. Satisfiable:
  the 2^k basis polynomials have distinct degrees < 2^k (novelBasis_natDegree +
  binary-representation uniqueness), hence are a basis of degree-< 2^k
  polynomials; evaluation at the 2^k distinct points (additiveDomain_card) is
  injective there (`binaryTower_rs_eval_injective`); equal finite dimensions make
  it bijective. Teeth: the independence hypothesis is load-bearing — for
  dependent β the domain collapses (`additiveDomain_card_needs_independence`)
  and the map cannot be injective. Discharging it (and refining to the
  O(n log n) recursive butterfly the fold-composition structure
  `subspaceVanishing_succ_eq_fold_comp` provides) is the transform residual.
* **[ANTT-fri]** the additive-FRI DISTANCE PRESERVATION — the fold algebra is
  closed above (`foldPoly_decompose`, `friFold_coset_invariant`,
  `friFold_eval_poly` = completeness), and the missing half is soundness: a word
  δ-far from every low-degree word stays (with high probability over the
  challenge λ) far after folding — the proximity-gap / correlated-agreement
  statement over ADDITIVE cosets {x, x+β} instead of multiplicative pairs
  {x, −x}. Its Loom-side deployment (instantiating Loom/Proximity at the
  additive domain) CANNOT be stated here (the Theory boundary forbids naming
  Loom), and its correct quantitative statement (which distortion, which
  challenge-count bound — Ben-Sasson et al. proximity gaps, Binius) must enter
  statement-first WITH its satisfiability argument from the literature in hand;
  a guessed constant would be a wrong statement proved slowly. Both halves land
  Loom-side against Loom/ReedSolomon + Loom/Proximity.
-/
import Theory.BinaryTowerFanPaar
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

namespace Minidregg.Theory

open Polynomial

variable {F : Type*} [Field F]

/-! ### The GF(2)-linear evaluation domain -/

section Domain

variable [Algebra (ZMod 2) F]

/-- **The evaluation domain** W_k = span_{GF(2)}{β₀, …, β_{k−1}} — a
`ZMod 2`-submodule of the char-2 field `F` (which IS a GF(2)-vector space). This
replaces the multiplicative subgroup ⟨ω⟩ of standard FRI/NTT: the domain of the
additive NTT is a GF(2)-SUBSPACE, and its "subgroup chain" is
W₀ ⊂ W₁ ⊂ ⋯ ⊂ W_k by successive basis elements. -/
def additiveDomain (β : ℕ → F) (k : ℕ) : Submodule (ZMod 2) F :=
  Submodule.span (ZMod 2) (Set.range fun j : Fin k => β j)

/-- The domain point of coefficient vector `c ∈ GF(2)^k`: the GF(2)-linear
combination ∑ cⱼ • βⱼ. For linearly independent β these are the 2^k points of
W_k, each hit exactly once (`domainPoint_injective`). -/
def domainPoint (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) : F :=
  ∑ j : Fin k, c j • β j

theorem mem_additiveDomain_iff (β : ℕ → F) (k : ℕ) (x : F) :
    x ∈ additiveDomain β k ↔ ∃ c : Fin k → ZMod 2, domainPoint β k c = x := by
  unfold additiveDomain domainPoint
  exact Submodule.mem_span_range_iff_exists_fun (ZMod 2)

theorem domainPoint_mem (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    domainPoint β k c ∈ additiveDomain β k :=
  (mem_additiveDomain_iff β k _).mpr ⟨c, rfl⟩

theorem additiveDomain_coe (β : ℕ → F) (k : ℕ) :
    (additiveDomain β k : Set F) = Set.range (domainPoint β k) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_range, mem_additiveDomain_iff]

/-- Distinct coefficient vectors give distinct domain points when β is
GF(2)-linearly independent — the domain genuinely has 2^k points. -/
theorem domainPoint_injective {β : ℕ → F} {k : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin k => β j) :
    Function.Injective (domainPoint β k) := by
  intro c d h
  have hz : ∑ j : Fin k, (c j - d j) • β (j : ℕ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact h
  have hcd := Fintype.linearIndependent_iff.mp hβ (fun j => c j - d j) hz
  funext j
  exact sub_eq_zero.mp (hcd j)

/-- **|W_k| = 2^k** for GF(2)-linearly-independent β: the additive domain has
exactly 2^k points — the size a k-round additive FRI/NTT domain needs. -/
theorem additiveDomain_card {β : ℕ → F} {k : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin k => β j) :
    Nat.card (additiveDomain β k) = 2 ^ k := by
  have h1 : Nat.card (additiveDomain β k) = Nat.card (Set.range (domainPoint β k)) :=
    congrArg (fun s : Set F => Nat.card s) (additiveDomain_coe β k)
  rw [h1, Nat.card_range_of_injective (domainPoint_injective hβ), Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

end Domain

/-! ### The subspace-vanishing polynomials Ŵ_i, in recursive LCH form -/

/-- **The subspace-vanishing polynomials**, recursively (Lin–Chung–Han):
Ŵ₀ = X (vanishing of W₀ = {0}), and
Ŵ_{i+1} = Ŵ_i² + Ŵ_i(β_i)·Ŵ_i = Ŵ_i·(Ŵ_i + Ŵ_i(β_i)).
The recursion is exactly "the roots of Ŵ_{i+1} are W_i ∪ (W_i + β_i)":
∏_{a∈W_{i+1}}(X−a) = Ŵ_i(X)·Ŵ_i(X + β_i) = Ŵ_i·(Ŵ_i + Ŵ_i(β_i)) once Ŵ_i is
additive — and additivity is `subspaceVanishing_additive` below. For
independent β this IS ∏_{a ∈ W_i}(X − a): `subspaceVanishing_eq_prod`. -/
noncomputable def subspaceVanishing (β : ℕ → F) : ℕ → F[X]
  | 0 => X
  | i + 1 =>
    subspaceVanishing β i ^ 2 +
      C ((subspaceVanishing β i).eval (β i)) * subspaceVanishing β i

@[simp] theorem subspaceVanishing_zero (β : ℕ → F) : subspaceVanishing β 0 = X := rfl

theorem subspaceVanishing_succ (β : ℕ → F) (i : ℕ) :
    subspaceVanishing β (i + 1) =
      subspaceVanishing β i ^ 2 +
        C ((subspaceVanishing β i).eval (β i)) * subspaceVanishing β i := rfl

@[simp] theorem subspaceVanishing_eval_zero (β : ℕ → F) (i : ℕ) :
    (subspaceVanishing β i).eval 0 = 0 := by
  induction i with
  | zero => simp
  | succ i ih => rw [subspaceVanishing_succ]; simp [ih]

/-- Ŵ_i is monic of degree 2^i (joint induction: the square dominates the
linear correction term). -/
theorem subspaceVanishing_monic_natDegree (β : ℕ → F) (i : ℕ) :
    (subspaceVanishing β i).Monic ∧ (subspaceVanishing β i).natDegree = 2 ^ i := by
  induction i with
  | zero => exact ⟨monic_X, natDegree_X⟩
  | succ i ih =>
    obtain ⟨hm, hd⟩ := ih
    have hp2 : ((subspaceVanishing β i) ^ 2).Monic := hm.pow 2
    have hd2 : ((subspaceVanishing β i) ^ 2).natDegree = 2 * 2 ^ i := by
      rw [hm.natDegree_pow, hd]
    have h1 : (C ((subspaceVanishing β i).eval (β i)) * subspaceVanishing β i).degree ≤
        ((2 ^ i : ℕ) : WithBot ℕ) := by
      refine le_trans degree_le_natDegree ?_
      have hn : (C ((subspaceVanishing β i).eval (β i)) *
          subspaceVanishing β i).natDegree ≤ 2 ^ i :=
        le_trans (natDegree_C_mul_le _ _) (le_of_eq hd)
      exact_mod_cast hn
    have h2 : ((2 ^ i : ℕ) : WithBot ℕ) < ((subspaceVanishing β i) ^ 2).degree := by
      rw [degree_eq_natDegree hp2.ne_zero, hd2]
      exact_mod_cast (by have := Nat.two_pow_pos i; omega : 2 ^ i < 2 * 2 ^ i)
    have hlt : (C ((subspaceVanishing β i).eval (β i)) * subspaceVanishing β i).degree <
        ((subspaceVanishing β i) ^ 2).degree := lt_of_le_of_lt h1 h2
    constructor
    · rw [subspaceVanishing_succ]
      exact hp2.add_of_left hlt
    · rw [subspaceVanishing_succ,
        natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hlt), hd2,
        pow_succ]
      ring

theorem subspaceVanishing_monic (β : ℕ → F) (i : ℕ) : (subspaceVanishing β i).Monic :=
  (subspaceVanishing_monic_natDegree β i).1

theorem subspaceVanishing_natDegree (β : ℕ → F) (i : ℕ) :
    (subspaceVanishing β i).natDegree = 2 ^ i :=
  (subspaceVanishing_monic_natDegree β i).2

section Additive

variable [CharP F 2]

/-- **THE structural fact of the additive NTT: the subspace-vanishing polynomial
is ADDITIVE** — Ŵ_i(x + y) = Ŵ_i(x) + Ŵ_i(y) for ALL x, y (not just domain
points). In char 2 the Frobenius square is additive, and the LCH recursion
composes squares and scalar multiples, so every Ŵ_i is a GF(2)-linearized
polynomial. This is the additive analog of "squaring is a group homomorphism of
⟨ω⟩" in multiplicative FRI — and it is what X^n − 1 CANNOT provide over
GF(2^(2^k)) (see `charTwo_sq_eq_one_iff` / `multiplicative_squaring_injective`
below). -/
theorem subspaceVanishing_additive (β : ℕ → F) (i : ℕ) (x y : F) :
    (subspaceVanishing β i).eval (x + y) =
      (subspaceVanishing β i).eval x + (subspaceVanishing β i).eval y := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [subspaceVanishing_succ, eval_add, eval_mul, eval_pow, eval_C, ih,
      CharTwo.add_sq]
    ring

end Additive

section Smul

variable [Algebra (ZMod 2) F]

/-- GF(2)-homogeneity (with additivity: full GF(2)-linearity — the scalars are
only 0 and 1, so this is additivity plus Ŵ_i(0) = 0). -/
theorem subspaceVanishing_smul (β : ℕ → F) (i : ℕ) (c : ZMod 2) (x : F) :
    (subspaceVanishing β i).eval (c • x) = c • (subspaceVanishing β i).eval x := by
  rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
  · rw [zero_smul, zero_smul, subspaceVanishing_eval_zero]
  · rw [one_smul, one_smul]

end Smul

section Linear

variable [CharP F 2] [Algebra (ZMod 2) F]

/-- **Ŵ_i as an honest GF(2)-linear map** F →ₗ[GF(2)] F — the packaged form of
`subspaceVanishing_additive` + `subspaceVanishing_smul`. -/
noncomputable def subspaceVanishingHom (β : ℕ → F) (i : ℕ) : F →ₗ[ZMod 2] F where
  toFun x := (subspaceVanishing β i).eval x
  map_add' := subspaceVanishing_additive β i
  map_smul' c x := by simpa using subspaceVanishing_smul β i c x

@[simp] theorem subspaceVanishingHom_apply (β : ℕ → F) (i : ℕ) (x : F) :
    subspaceVanishingHom β i x = (subspaceVanishing β i).eval x := rfl

/-- Ŵ_i vanishes on every domain point of W_i (all 2^i of them) — by induction,
riding additivity: a W_{i+1}-point is w + t·β_i with w ∈ W_i, t ∈ {0,1}, and
Ŵ_{i+1} = Ŵ_i·(Ŵ_i + Ŵ_i(β_i)) kills both cosets. -/
theorem subspaceVanishing_eval_domainPoint (β : ℕ → F) :
    ∀ (i : ℕ) (c : Fin i → ZMod 2),
      (subspaceVanishing β i).eval (domainPoint β i c) = 0 := by
  intro i
  induction i with
  | zero => intro c; simp [domainPoint]
  | succ i ih =>
    intro c
    have hsplit : domainPoint β (i + 1) c =
        domainPoint β i (fun j => c j.castSucc) + c (Fin.last i) • β i := by
      unfold domainPoint
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
    rw [hsplit, subspaceVanishing_succ]
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) (c (Fin.last i)) with hl | hl
    · rw [hl, zero_smul, add_zero]
      simp only [eval_add, eval_mul, eval_pow]
      rw [ih fun j => c j.castSucc]
      simp
    · rw [hl, one_smul]
      simp only [eval_add, eval_mul, eval_pow, eval_C]
      rw [subspaceVanishing_additive, ih fun j => c j.castSucc, zero_add, pow_two]
      exact CharTwo.add_self_eq_zero _

theorem subspaceVanishing_eval_of_mem (β : ℕ → F) (k : ℕ) {x : F}
    (hx : x ∈ additiveDomain β k) : (subspaceVanishing β k).eval x = 0 := by
  obtain ⟨c, rfl⟩ := (mem_additiveDomain_iff β k x).mp hx
  exact subspaceVanishing_eval_domainPoint β k c

/-- **Ŵ_k really is the vanishing polynomial of the subspace**: for
GF(2)-linearly-independent β, Ŵ_k = ∏_{a ∈ W_k}(X − a) — monic of degree
2^k = |W_k| and vanishing on all of W_k, so the recursive LCH form and the
product form agree. (This is what earns the name; the recursion is the FAST
form of the same object.) -/
theorem subspaceVanishing_eq_prod {β : ℕ → F} {k : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin k => β j) :
    subspaceVanishing β k =
      ∏ c : Fin k → ZMod 2, (X - C (domainPoint β k c)) := by
  classical
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hPm : (∏ c : Fin k → ZMod 2, (X - C (domainPoint β k c))).Monic :=
    monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _
  have hPd : (∏ c : Fin k → ZMod 2, (X - C (domainPoint β k c))).natDegree = 2 ^ k := by
    rw [natDegree_prod _ _ fun c _ => X_sub_C_ne_zero _]
    simp [Finset.card_univ, hcard]
  have hsm := subspaceVanishing_monic β k
  have hsd := subspaceVanishing_natDegree β k
  refine eq_of_degree_sub_lt_of_eval_index_eq Finset.univ
    (domainPoint_injective hβ).injOn ?_ ?_
  · have hdeq : (subspaceVanishing β k).degree =
        (∏ c : Fin k → ZMod 2, (X - C (domainPoint β k c))).degree := by
      rw [degree_eq_natDegree hsm.ne_zero, degree_eq_natDegree hPm.ne_zero, hsd, hPd]
    have hsub := degree_sub_lt hdeq hsm.ne_zero
      (by rw [hsm.leadingCoeff, hPm.leadingCoeff])
    rw [degree_eq_natDegree hsm.ne_zero, hsd] at hsub
    simpa [Finset.card_univ, hcard] using hsub
  · intro c _
    rw [subspaceVanishing_eval_domainPoint β k c, eval_prod]
    exact (Finset.prod_eq_zero (Finset.mem_univ c) (by simp)).symm

/-- The roots of Ŵ_k are EXACTLY the subspace W_k (for independent β): the
evaluation kernel of the GF(2)-linear map Ŵ_k is the domain itself. -/
theorem subspaceVanishing_eval_eq_zero_iff {β : ℕ → F} {k : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin k => β j) (x : F) :
    (subspaceVanishing β k).eval x = 0 ↔ x ∈ additiveDomain β k := by
  constructor
  · intro hx
    rw [subspaceVanishing_eq_prod hβ, eval_prod] at hx
    obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.mp hx
    have hxc : x = domainPoint β k c := by simpa [sub_eq_zero] using hc
    rw [hxc]
    exact domainPoint_mem β k c
  · exact subspaceVanishing_eval_of_mem β k

end Linear

/-! ### The LCH novelpoly basis -/

/-- **The novel polynomial basis** (Lin–Chung–Han 2014): for a bit vector
c ∈ GF(2)^k, X̂_c = ∏_i Ŵ_i^{cᵢ} — take the subspace-vanishing polynomial of
each chain level W_i raised to the i-th bit. Monic of degree ∑ cᵢ·2^i
(`novelBasis_natDegree`): as c ranges over GF(2)^k the degrees are exactly
0, 1, …, 2^k − 1 (binary representation), a TRIANGULAR basis of the degree-< 2^k
polynomials. The additive NTT evaluates a polynomial given in THIS basis on the
domain W_k; the fold-composition structure `subspaceVanishing_succ_eq_fold_comp`
is what makes that evaluation O(n log n). (LCH normalize by Ŵ_i(β_i); the
normalization changes triangularity constants, not the basis property, and is
deferred to [ANTT-transform].) -/
noncomputable def novelBasis (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) : F[X] :=
  ∏ i : Fin k, subspaceVanishing β i ^ (c i).val

theorem novelBasis_monic (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    (novelBasis β k c).Monic :=
  monic_prod_of_monic _ _ fun i _ => (subspaceVanishing_monic β i).pow _

/-- deg X̂_c = ∑ cᵢ·2^i — the binary-weighted degree; distinct bit vectors give
distinct degrees (binary representation), which is the triangularity of the
novelpoly basis. -/
theorem novelBasis_natDegree (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    (novelBasis β k c).natDegree = ∑ i : Fin k, (c i).val * 2 ^ (i : ℕ) := by
  rw [novelBasis, natDegree_prod _ _ fun (i : Fin k) _ =>
    ((subspaceVanishing_monic β i).pow ((c i).val)).ne_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(subspaceVanishing_monic β (i : ℕ)).natDegree_pow, subspaceVanishing_natDegree]

/-! ### The additive fold: the 2-to-1 GF(2)-linear projection -/

/-- **The one-step additive fold map** q_β(x) = x² + βx = x·(x + β) — the
subspace-vanishing map of the one-dimensional subspace {0, β}. This is the
additive-FRI analog of x ↦ x² over a multiplicative domain: a degree-2 map
that is exactly 2-to-1, with GF(2)-LINEAR structure instead of group-square
structure. -/
def foldMap (β : F) (x : F) : F := x ^ 2 + β * x

section Fold

variable [CharP F 2]

/-- The fold map is additive (char-2 Frobenius again). -/
theorem foldMap_add (β x y : F) :
    foldMap β (x + y) = foldMap β x + foldMap β y := by
  unfold foldMap
  rw [CharTwo.add_sq]
  ring

/-- **The kernel of the fold is EXACTLY {0, β}** — a 2-element GF(2)-subspace,
the "μ₂" that the multiplicative group of a char-2 field does not have. -/
theorem foldMap_eq_zero_iff (β x : F) : foldMap β x = 0 ↔ x = 0 ∨ x = β := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hx : x * (x + β) = 0 := by
      unfold foldMap at h
      linear_combination h
    rcases mul_eq_zero.mp hx with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h0 - β * h2)
  · intro h
    rcases h with h0 | h0 <;> rw [h0] <;> unfold foldMap
    · ring
    · linear_combination β ^ 2 * h2

/-- **The fibers of the fold are EXACTLY the cosets {x, x + β}** — q_β is
2-to-1 for β ≠ 0 (for β = 0 the two fiber descriptions coincide, matching
Frobenius injectivity): the coset structure the additive FRI folds over,
replacing the {x, −x} pairs of multiplicative FRI. -/
theorem foldMap_eq_iff {β x y : F} :
    foldMap β y = foldMap β x ↔ y = x ∨ y = x + β := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hadd : foldMap β (y + x) = 0 := by
      rw [foldMap_add, h]
      exact CharTwo.add_self_eq_zero _
    rcases (foldMap_eq_zero_iff β (y + x)).mp hadd with h0 | h0
    · exact Or.inl (by linear_combination h0 - x * h2)
    · exact Or.inr (by linear_combination h0 - x * h2)
  · intro h
    rcases h with h0 | h0 <;> rw [h0]
    · rw [foldMap_add, (foldMap_eq_zero_iff β β).mpr (Or.inr rfl), add_zero]

/-- The fold genuinely identifies two DISTINCT points: q_β(x + β) = q_β(x) and
x + β ≠ x. Contrast `multiplicative_squaring_injective`. -/
theorem foldMap_two_to_one {β : F} (hβ : β ≠ 0) (x : F) :
    foldMap β (x + β) = foldMap β x ∧ x + β ≠ x :=
  ⟨foldMap_eq_iff.mpr (Or.inr rfl),
    fun h => hβ (by linear_combination h)⟩

/-! ### Why the multiplicative route is closed (the contrast teeth) -/

/-- **No μ₂ in characteristic 2**: x² = 1 forces x = 1 — the polynomial
X² − 1 = (X − 1)² has a DOUBLE root, not two roots. A char-2 field has no
element of order 2, hence no 2-adic multiplicative subgroup chain to fold over:
the multiplicative-FRI evaluation domain does not exist here. -/
theorem charTwo_sq_eq_one_iff (x : F) : x ^ 2 = 1 ↔ x = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hsq : (x + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, h, one_pow]
      exact CharTwo.add_self_eq_zero _
    have hx1 : x + 1 = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
    linear_combination hx1 - h2
  · intro h
    rw [h, one_pow]

/-- **Multiplicative squaring folds NOTHING in char 2**: x ↦ x² is INJECTIVE
(the Frobenius) — a 1-to-1 map cannot halve a domain. The additive fold
`foldMap` is honestly 2-to-1 (`foldMap_two_to_one`); this pair of facts IS the
reason Binius folds additively. -/
theorem multiplicative_squaring_injective :
    Function.Injective fun x : F => x ^ 2 := by
  intro x y h
  simp only at h
  have hsq : (x + y) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h]
    exact CharTwo.add_self_eq_zero _
  have hxy : x + y = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hxy - y * h2

end Fold

/-! ### The fold on polynomials: even/odd decomposition and the FRI fold -/

/-- The fold as a POLYNOMIAL: q_β = X² + βX (monic, degree 2). Composition with
it is the "even part" extraction of the additive world. -/
noncomputable def foldPoly (β : F) : F[X] := X ^ 2 + C β * X

theorem foldPoly_monic (β : F) : (foldPoly β).Monic := by
  unfold foldPoly
  monicity!

theorem foldPoly_natDegree (β : F) : (foldPoly β).natDegree = 2 := by
  unfold foldPoly
  compute_degree!

@[simp] theorem foldPoly_eval (β x : F) : (foldPoly β).eval x = foldMap β x := by
  simp [foldPoly, foldMap]

/-- **Ŵ₁ IS the fold polynomial** of its first basis element. -/
theorem subspaceVanishing_one (β : ℕ → F) :
    subspaceVanishing β 1 = foldPoly (β 0) := by
  rw [subspaceVanishing_succ, foldPoly]
  simp

/-- **The vanishing chain is an iterated fold**: Ŵ_{i+1} = q_{Ŵ_i(β_i)} ∘ Ŵ_i.
Each level of the subspace chain is ONE two-to-one fold of the previous level —
this composition structure is exactly the log-depth recursion of the additive
NTT/FRI ([ANTT-transform] refines it to the O(n log n) butterfly). -/
theorem subspaceVanishing_succ_eq_fold_comp (β : ℕ → F) (i : ℕ) :
    subspaceVanishing β (i + 1) =
      (foldPoly ((subspaceVanishing β i).eval (β i))).comp (subspaceVanishing β i) := by
  rw [subspaceVanishing_succ, foldPoly]
  simp [add_comp, mul_comp, X_comp, C_comp, pow_comp]

/-- **The additive even/odd decomposition** — the algebraic engine of the
additive FRI fold: every P with deg ≤ 2d+1 splits as
P = P₀(q_β) + X·P₁(q_β) with deg Pᵢ ≤ d. This replaces the multiplicative
even/odd split P(X) = P₀(X²) + X·P₁(X²); here the "square" is the 2-to-1
additive fold q_β. Proof: division algorithm by the monic degree-2 q_β,
digit by digit. -/
theorem foldPoly_decompose (β : F) :
    ∀ (d : ℕ) (P : F[X]), P.natDegree ≤ 2 * d + 1 →
      ∃ P₀ P₁ : F[X], P₀.natDegree ≤ d ∧ P₁.natDegree ≤ d ∧
        P = P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)
  | 0, P, hP => by
    refine ⟨C (P.coeff 0), C (P.coeff 1), by simp, by simp, ?_⟩
    have h1 : P.degree ≤ 1 := le_trans degree_le_natDegree (by exact_mod_cast hP)
    conv_lhs => rw [eq_X_add_C_of_degree_le_one h1]
    simp only [C_comp]
    ring
  | d + 1, P, hP => by
    have hqm : (foldPoly β).Monic := foldPoly_monic β
    obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hQ⟩ :=
      foldPoly_decompose β d (P /ₘ foldPoly β) (by
        rw [natDegree_divByMonic P hqm, foldPoly_natDegree]
        omega)
    have hRdeg : (P %ₘ foldPoly β).degree ≤ 1 := by
      have hlt := degree_modByMonic_lt P hqm
      rw [degree_eq_natDegree hqm.ne_zero, foldPoly_natDegree] at hlt
      rcases eq_or_ne (P %ₘ foldPoly β) 0 with h0 | h0
      · rw [h0, degree_zero]; exact bot_le
      · rw [degree_eq_natDegree h0] at hlt ⊢
        exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
    obtain ⟨r0, r1, hR⟩ : ∃ r0 r1 : F, P %ₘ foldPoly β = C r1 * X + C r0 :=
      ⟨(P %ₘ foldPoly β).coeff 0, (P %ₘ foldPoly β).coeff 1,
        eq_X_add_C_of_degree_le_one hRdeg⟩
    refine ⟨X * Q₀ + C r0, X * Q₁ + C r1, ?_, ?_, ?_⟩
    · refine le_trans (natDegree_add_le _ _) ?_
      rw [natDegree_C]
      refine max_le (le_trans natDegree_mul_le ?_) (Nat.zero_le _)
      rw [natDegree_X]
      omega
    · refine le_trans (natDegree_add_le _ _) ?_
      rw [natDegree_C]
      refine max_le (le_trans natDegree_mul_le ?_) (Nat.zero_le _)
      rw [natDegree_X]
      omega
    · conv_lhs => rw [← modByMonic_add_div P (foldPoly β)]
      rw [hQ, hR]
      simp only [add_comp, mul_comp, X_comp, C_comp]
      ring

/-- **The additive FRI fold at challenge λ**, on FUNCTIONS: from the two values
of f on the fold-coset {x, x + β}, interpolate the decomposition components and
combine with the challenge —
  friFold f (x) = f(x) + (x + λ)·(f(x) + f(x + β))/β
(char 2: sums are differences). Defined for arbitrary f : F → F — the verifier
applies it to a claimed word, not to a known polynomial. -/
def friFold (β lam : F) (f : F → F) (x : F) : F :=
  f x + (x + lam) * ((f x + f (x + β)) / β)

section FriFold

variable [CharP F 2]

/-- **The fold is well-defined on fold-cosets**: friFold f (x + β) = friFold f x —
the folded word genuinely lives on the half-size image domain q_β(W). -/
theorem friFold_coset_invariant (β lam : F) (f : F → F) (x : F) :
    friFold β lam f (x + β) = friFold β lam f x := by
  unfold friFold
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx : x + β + β = x := by linear_combination β * h2
  rw [hx]
  rcases eq_or_ne β 0 with rfl | hβ
  · norm_num
  · have hβi : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (f (x + β) + f x) * hβi + f (x + β) * h2

/-- **Folding a low-degree word gives a low-degree word (degree-halving /
completeness of the additive FRI fold)**: if f is the evaluation of a
polynomial of degree ≤ 2d+1, then friFold f is the evaluation of a polynomial
of degree ≤ d on the IMAGE domain — pointwise via the fold map q_β. Soundness
(distance preservation) is the [ANTT-fri] residual. -/
theorem friFold_eval_poly {β lam : F} (hβ : β ≠ 0) {d : ℕ} {P : F[X]}
    (hP : P.natDegree ≤ 2 * d + 1) :
    ∃ P' : F[X], P'.natDegree ≤ d ∧
      ∀ x : F, friFold β lam (fun t => P.eval t) x = P'.eval (foldMap β x) := by
  obtain ⟨P₀, P₁, h₀, h₁, hdecomp⟩ := foldPoly_decompose β d P hP
  refine ⟨P₀ + C lam * P₁, ?_, ?_⟩
  · exact le_trans (natDegree_add_le _ _)
      (max_le h₀ (le_trans (natDegree_C_mul_le _ _) h₁))
  · intro x
    have hev : ∀ t : F, P.eval t =
        P₀.eval (foldMap β t) + t * P₁.eval (foldMap β t) := by
      intro t
      conv_lhs => rw [hdecomp]
      simp [eval_comp]
    have hfold : foldMap β (x + β) = foldMap β x := foldMap_eq_iff.mpr (Or.inr rfl)
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    simp only [friFold]
    rw [hev x, hev (x + β), hfold, eval_add, eval_mul, eval_C]
    have hnum : P₀.eval (foldMap β x) + x * P₁.eval (foldMap β x) +
        (P₀.eval (foldMap β x) + (x + β) * P₁.eval (foldMap β x)) =
        β * P₁.eval (foldMap β x) := by
      linear_combination (P₀.eval (foldMap β x) + x * P₁.eval (foldMap β x)) * h2
    rw [hnum, mul_div_cancel_left₀ _ hβ]
    linear_combination (x * P₁.eval (foldMap β x)) * h2

end FriFold

/-! ### Keystones at the deployed tower: GF(16), basis {1, x₁} -/

/-- The keystone basis in GF(16) = `binaryTower 2`: β₀ = 1, β₁ = x₁ (the
Fan–Paar generator `fpGen 1`), zero above. W₂ = span{1, x₁} is a concrete
2-dimensional GF(2)-subspace — 4 of GF(16)'s 16 points. -/
noncomputable def keystoneBeta : ℕ → binaryTower 2
  | 0 => 1
  | 1 => fpGen 1
  | _ + 2 => 0

@[simp] theorem keystoneBeta_zero : keystoneBeta 0 = 1 := rfl

@[simp] theorem keystoneBeta_one : keystoneBeta 1 = fpGen 1 := rfl

/-- {1, x₁} is GF(2)-linearly independent in GF(16) (x₁ ∉ {0, 1}). -/
theorem keystoneBeta_linearIndependent :
    LinearIndependent (ZMod 2) fun j : Fin 2 => keystoneBeta j := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Fin.val_zero, Fin.val_one, keystoneBeta_zero, keystoneBeta_one] at hg
  have hcase : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  suffices h : g 0 = 0 ∧ g 1 = 0 by
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have h2 : (2 : binaryTower 2) = 0 := binaryTower_two_eq_zero 2
  rcases hcase (g 0) with h0 | h0 <;> rcases hcase (g 1) with h1 | h1 <;>
    rw [h0, h1] at hg <;>
    simp only [zero_smul, one_smul, add_zero, zero_add] at hg
  · exact ⟨h0, h1⟩
  · exact absurd hg (fpGen_ne_zero 1)
  · exact absurd hg one_ne_zero
  · exact absurd (by linear_combination hg - h2 : fpGen 1 = 1) (fpGen_ne_one 1)

/-- KEYSTONE (satisfiable): the concrete additive evaluation domain
W₂ = span{1, x₁} ⊆ GF(16) has exactly 4 points. -/
theorem keystone_domain_card :
    Nat.card (additiveDomain keystoneBeta 2) = 4 := by
  rw [additiveDomain_card keystoneBeta_linearIndependent]
  norm_num

/-- KEYSTONE (computed): Ŵ₁ = X² + X — the vanishing polynomial of
W₁ = {0, 1} = span{1}, concretely: X·(X − 1) in char 2. -/
theorem keystone_subspaceVanishing_one :
    subspaceVanishing keystoneBeta 1 = X ^ 2 + X := by
  rw [subspaceVanishing_succ]
  simp

/-- KEYSTONE (computed): Ŵ₂ in its fold form — Ŵ₂ = Ŵ₁² + Ŵ₁(x₁)·Ŵ₁ with
Ŵ₁ = X² + X and normalizer Ŵ₁(x₁) = x₁² + x₁. -/
theorem keystone_subspaceVanishing_two :
    subspaceVanishing keystoneBeta 2 =
      (X ^ 2 + X) ^ 2 + C (fpGen 1 ^ 2 + fpGen 1) * (X ^ 2 + X) := by
  rw [subspaceVanishing_succ, keystone_subspaceVanishing_one]
  simp

/-- **TEETH: additivity is exercised where it says something** — on the concrete
points x₁ and x₁² of GF(16), Ŵ₁(x₁ + x₁²) = Ŵ₁(x₁) + Ŵ₁(x₁²) with BOTH
summands NONZERO (both points lie outside W₁ = {0,1}, the root set). The
additive law is not the vacuous 0 = 0 + 0 of domain points: the vanishing
polynomial is a nontrivial GF(2)-linear map on all of GF(16). -/
theorem keystone_additive_tooth :
    (subspaceVanishing keystoneBeta 1).eval (fpGen 1 + fpGen 1 ^ 2) =
        (subspaceVanishing keystoneBeta 1).eval (fpGen 1) +
          (subspaceVanishing keystoneBeta 1).eval (fpGen 1 ^ 2) ∧
      (subspaceVanishing keystoneBeta 1).eval (fpGen 1) ≠ 0 ∧
      (subspaceVanishing keystoneBeta 1).eval (fpGen 1 ^ 2) ≠ 0 := by
  have h2 : (2 : binaryTower 2) = 0 := binaryTower_two_eq_zero 2
  refine ⟨subspaceVanishing_additive keystoneBeta 1 _ _, ?_, ?_⟩
  · rw [keystone_subspaceVanishing_one]
    simp only [eval_add, eval_pow, eval_X]
    intro h
    have hfac : fpGen 1 * (fpGen 1 + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact fpGen_ne_zero 1 h0
    · exact fpGen_ne_one 1 (by linear_combination h0 - h2)
  · rw [keystone_subspaceVanishing_one]
    simp only [eval_add, eval_pow, eval_X]
    intro h
    have hfac : fpGen 1 ^ 2 * (fpGen 1 + 1) ^ 2 = 0 := by
      linear_combination h + fpGen 1 ^ 3 * h2
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact fpGen_ne_zero 1 (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h0)
    · refine fpGen_ne_one 1 ?_
      have h1 : fpGen 1 + 1 = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h0
      linear_combination h1 - h2

/-- KEYSTONE (contrast, at the tower): GF(2^(2^m)) has no element of
multiplicative order 2 — the 2-adic subgroup multiplicative FRI needs does not
exist at any tower level. -/
theorem binaryTower_sq_eq_one_iff (m : ℕ) (x : binaryTower m) :
    x ^ 2 = 1 ↔ x = 1 :=
  charTwo_sq_eq_one_iff x

/-- KEYSTONE (contrast, concrete): over GF(16) the additive fold by β = x₁ is
honestly 2-to-1 on every point, while squaring is injective
(`multiplicative_squaring_injective`). -/
theorem keystone_fold_two_to_one (x : binaryTower 2) :
    foldMap (fpGen 1) (x + fpGen 1) = foldMap (fpGen 1) x ∧ x + fpGen 1 ≠ x :=
  foldMap_two_to_one (fpGen_ne_zero 1) x

/-! ### Named residuals — stated, satisfiable, NOT proved -/

/-- TEETH for the [ANTT-transform] hypothesis: with a DEPENDENT family the
domain collapses (span{0} has one point, not 2^k) — linear independence is
load-bearing in `NovelBasisTransform`, not decoration. -/
theorem additiveDomain_card_needs_independence :
    Nat.card (additiveDomain (fun _ => (0 : binaryTower 2)) 1) = 1 := by
  have hbot : additiveDomain (fun _ => (0 : binaryTower 2)) 1 = ⊥ := by
    rw [additiveDomain,
      show (Set.range fun _ : Fin 1 => (0 : binaryTower 2)) = {0} from Set.range_const]
    exact Submodule.span_singleton_eq_bot.mpr rfl
  rw [hbot]
  haveI : Nonempty (⊥ : Submodule (ZMod 2) (binaryTower 2)) := ⟨0⟩
  haveI : Subsingleton (⊥ : Submodule (ZMod 2) (binaryTower 2)) := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [Submodule.mem_bot] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  exact Nat.card_unique

/-- **[ANTT-transform] (RESIDUAL).** The additive NTT is invertible: for
GF(2)-linearly-independent β over the tower, the coefficient-to-evaluation map
(novelpoly coefficients a ↦ the function c ↦ ∑_j a_j·X̂_j(domainPoint c)) is a
BIJECTION.

Satisfiable: the 2^k novelpoly basis polynomials have the 2^k distinct degrees
0,…,2^k−1 (`novelBasis_natDegree` + uniqueness of binary representation), hence
form a basis of the degree-< 2^k polynomials; evaluation at the 2^k distinct
domain points (`additiveDomain_card`) is injective on that space
(`binaryTower_rs_eval_injective`); equal finite dimensions upgrade injective to
bijective. Teeth: independence is load-bearing
(`additiveDomain_card_needs_independence` — with dependent β the domain
collapses and the map cannot be injective). Discharging this, together with the
O(n log n) recursive evaluation the fold structure
(`subspaceVanishing_succ_eq_fold_comp`) provides, is the additive-NTT
transform residual. -/
def NovelBasisTransform : Prop :=
  ∀ (m k : ℕ) (β : ℕ → binaryTower m),
    LinearIndependent (ZMod 2) (fun j : Fin k => β j) →
    Function.Bijective fun (a : (Fin k → ZMod 2) → binaryTower m) =>
      fun c : Fin k → ZMod 2 =>
        ∑ j : Fin k → ZMod 2, a j * (novelBasis β k j).eval (domainPoint β k c)

end Minidregg.Theory
