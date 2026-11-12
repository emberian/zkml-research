/-
# Theory.AdditiveNTTTransform — [ANTT-transform] CLOSED (the additive NTT is a
linear bijection) + [ANTT-fri] REDUCED, AT THIS IMPORT LAYER ONLY, to the
additive proximity gap [ANTT-proximity].

⚑ READ THE STATUS LABEL CAREFULLY. `AdditiveProximityGap` is a hypothesis HERE
because `Theory` may not name `Selvage` — not because the tree lacks a proof.
`Selvage.additiveProximityGap_UD` DISCHARGES it unconditionally on the
macroscopic band `δ < (1−ρ)/3` (ρ = d/|R|), axiom-clean, and
`Selvage.additiveFold_distance_UD` fills this file's `hPG` slot in its own proof
term, so the additive cone PROVES a proximity gap rather than assuming one. An
auditor who reads "residual"/"floor" below as "unproved anywhere" is being
misled by an import boundary. What genuinely remains is the band ABOVE
`(1−ρ)/3` — full unique decoding and the Johnson regime — which still rides a
realizer.

Builds on `Theory.AdditiveNTT` (the domain W_k, the GF(2)-linear Ŵ_i, the LCH
novelpoly basis, the additive fold `friFold` with its completeness half
`friFold_eval_poly`).

## What is PROVED here (unconditional)

* **[ANTT-transform] CLOSED.** `novelBasis_natDegree_lt_two_pow` /
  `novelBasis_natDegree_injective` — the 2^k novelpoly polynomials have the 2^k
  pairwise-DISTINCT degrees ∑ cᵢ2^i < 2^k (binary representation, via
  `finFunctionFinEquiv`); **`novelBasis_linearIndependent`** — monic
  polynomials of distinct degrees cannot combine to zero (the degree of the
  combination is the max of its degrees), so the novelpoly family is
  F-linearly independent; `novelBasisBasis` — 2^k independent vectors in the
  2^k-dimensional `degreeLT F (2^k)` are a BASIS of the degree-< 2^k
  polynomials. **`novelBasisTransform_bijective`** — the coefficient-to-
  evaluation map (an F-linear ENDOMORPHISM of the 2^k-dimensional coefficient
  space) is injective (a nonzero combination is a nonzero polynomial of degree
  < 2^k, which cannot vanish at all 2^k distinct domain points —
  `domainPoint_injective` + `additiveDomain_card` + Lagrange), hence
  BIJECTIVE (injective endomorphism of a finite-dimensional space).
  **`novelBasisTransform_closed : NovelBasisTransform`** discharges the
  residual Prop of Theory/AdditiveNTT.lean at every tower level: the additive
  NTT is a genuine change of basis. (The O(n log n) butterfly SCHEDULE riding
  `subspaceVanishing_succ_eq_fold_comp` is an algorithmics refinement, not a
  correctness gap, and is out of scope here.)
* **The fold's affine structure.** `foldEven`/`foldOdd` — the even/odd
  components of a WORD (any f : F → F) with respect to the coset {x, x+β}:
  both COSET-INVARIANT (`foldEven_coset_invariant`, `foldOdd_coset_invariant`,
  so they are honest words on the image domain), with the RECONSTRUCTION
  identity `foldEven_add_mul_foldOdd` (f x = E x + x·O x, char 2) and the
  challenge-affine identity **`friFold_eq_even_add_mul_odd`**
  (friFold β λ f = E + λ·O pointwise) — the additive fold is an affine LINE
  through the two component words, exactly the shape a proximity gap consumes.
* **`agree_pair`** — the coset LIFT: if the two components agree with (P₀, P₁)
  at the image point q(r), then f agrees with Q = P₀∘q + X·(P₁∘q) at BOTH
  points r and r + β of the fiber — correlated agreement downstairs lifts
  2-for-2 upstairs, density preserved.
* **`close_of_correlatedAgreement`** — the lift, counted: correlated
  (1−δ)-agreement of (foldEven f, foldOdd f) with a degree-< d pair makes f
  itself δ-close to degree < 2d on the pair domain R ∪ (R+β) (|pair domain| =
  2|R| by transversality, `pairDomain_card`; the image domain honestly has |R|
  points, `foldMap_injOn_transversal`).
* **[ANTT-fri] REDUCED: `additiveFold_distance`** — GIVEN the additive
  proximity gap `AdditiveProximityGap R β d δ b` ([ANTT-proximity] below): a
  word δ-FAR from degree < 2d on the pair domain folds, off a bad set of ≤ b
  challenges, to a word still δ-FAR from degree < d on the image domain — NO
  loss in δ (bad-set form). Distance preservation of the additive FRI fold,
  proved from the named hypothesis; together with `friFold_eval_poly`
  (completeness, Theory/AdditiveNTT) the fold is a sound-and-complete round
  modulo [ANTT-proximity] — which `Selvage.additiveFold_distance_UD` discharges
  on `δ < (1−ρ)/3`, giving the same conclusion with NO gap hypothesis.
* **`additiveProximityGap_exact`** — the EXACT-agreement regime of the
  hypothesis, PROVED unconditionally with b = 1 (two challenges on the affine
  line u + λ·v determine both components as low-degree words — any field, no
  characteristic assumption): the additive analog of Selvage's sub-quantization
  `foldDistancePreserving_of_lt_inv_card`, and the satisfiability witness that
  the [ANTT-proximity] statement shape is inhabited. Hence
  **`additiveFold_distance_exact`**: at δ = 0 the additive fold preserves
  non-membership off ≤ 1 challenge, END-TO-END and unconditional.
* Keystones (GF(16) = `binaryTower 2`, the 4-point domain of
  Theory/AdditiveNTT): `keystone_transform_bijective` — the transform at the
  concrete 4-point domain W₂ = span{1, x₁} is a bijection; TEETH
  `eval_domain_not_injective_at_two_pow` / `keystone_transform_degree_tooth` —
  the strict degree bound is load-bearing: Ŵ₂ is a NONZERO degree-2² = 4
  polynomial with the SAME evaluations as 0 at all 4 domain points (evaluation
  does not determine degree-2^k polynomials, so `< 2^k` cannot be relaxed);
  TEETH `friFold_id` / `keystone_fold_degree_tooth` — the fold genuinely
  reduces degree, computed: the identity word (degree 1) folds to the constant
  word λ (degree 0); `keystone_transversal` + `keystone_fold_distance` — the
  unconditional exact-regime fold soundness instantiated at the concrete
  GF(16) domain; `keystone_pairDomain_eq_additiveDomain` — the fold domain IS
  the NTT domain, proved pointwise ({0,1} ∪ {x₁, 1+x₁} = W₂ = span{1, x₁});
  TEETH `keystone_far_word_exists` — far words EXIST (the indicator of
  1 + x₁ agrees with no affine polynomial), so the reduction's far-premise is
  inhabited, not vacuous.

## Honest residual (NAMED here; PROVED one import layer up)

* **[ANTT-proximity]** `AdditiveProximityGap` — correlated agreement for
  affine lines of words over the ADDITIVE image domain, bad-challenge-set
  form: unless (u, v) already have correlated (1−δ)-agreement with a
  degree-< d pair, all but ≤ b challenges λ leave u + λ·v δ-far from
  degree < d. This is the additive-coset analog of the multiplicative
  `IsProximityGenerator`/hPG floor (Selvage/ReedSolomon, Selvage/Proximity) — the
  SAME BCIKS 2020/654 / WHIR proximity-gap statement, whose proof is
  evaluation-domain-agnostic (BCIKS Thm 1.4 holds for RS codes over ANY set of
  distinct points; the domain structure enters only through the folding
  algebra, which is proved here). Satisfiable: the δ = 0 regime is PROVED here
  (`additiveProximityGap_exact`), and ⚑ the MACROSCOPIC regime is PROVED one
  import layer up — `Selvage.additiveProximityGap_UD` establishes
  `AdditiveProximityGap R β d δ |R|` for every `0 < δ < (1−ρ)/3` with no
  proximity hypothesis, by transporting the hypothesis-free
  `reedSolomonCode_isProximityGenerator_UD` through the domain-agnostic bridge
  `additiveProximityGap_of_isProximityGenerator`. So this is a residual OF THIS
  FILE, forced by the Theory boundary (which forbids naming Selvage), not a
  residual of the tree. The genuine remainder is the band at and above
  `(1−ρ)/3`: full unique decoding and Johnson, where a realizer is still
  assumed, exactly as on the multiplicative side.

Candidate-independent FIELD MATH — imports Mathlib + Theory only (boundary
enforced by `scripts/check-import-boundary.sh`).
-/
import Theory.AdditiveNTT
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace Minidregg.Theory

open Polynomial Module

variable {F : Type*} [Field F]

/-! ### The novelpoly degrees are the 2^k distinct values 0, …, 2^k − 1 -/

/-- The binary-weighted degree ∑ cᵢ·2^i of `novelBasis c`, as the value of the
`finFunctionFinEquiv` bijection (Fin k → Fin 2) ≃ Fin (2^k): binary
representation, packaged. -/
private theorem bitSum_eq_finFunctionFinEquiv (k : ℕ) (c : Fin k → ZMod 2) :
    ∑ i : Fin k, (c i).val * 2 ^ (i : ℕ) =
      (finFunctionFinEquiv (fun i => (⟨(c i).val, ZMod.val_lt (c i)⟩ : Fin 2)) : ℕ) := by
  rw [finFunctionFinEquiv_apply]

/-- deg X̂_c = ∑ cᵢ·2^i < 2^k: every novelpoly basis polynomial has degree
BELOW 2^k — the family lives in the degree-< 2^k space. -/
theorem novelBasis_natDegree_lt_two_pow (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    (novelBasis β k c).natDegree < 2 ^ k := by
  rw [novelBasis_natDegree, bitSum_eq_finFunctionFinEquiv]
  exact (finFunctionFinEquiv _).isLt

/-- **Distinct bit vectors give distinct degrees** (uniqueness of binary
representation): c ↦ deg X̂_c is injective — the triangularity of the novelpoly
basis. -/
theorem novelBasis_natDegree_injective (β : ℕ → F) (k : ℕ) :
    Function.Injective fun c : Fin k → ZMod 2 => (novelBasis β k c).natDegree := by
  intro c d h
  simp only [novelBasis_natDegree] at h
  rw [bitSum_eq_finFunctionFinEquiv, bitSum_eq_finFunctionFinEquiv] at h
  have h2 := finFunctionFinEquiv.injective (Fin.val_injective h)
  funext i
  exact ZMod.val_injective 2 (congrArg Fin.val (congrFun h2 i))

/-! ### The novelpoly family is a basis of the degree-< 2^k polynomials -/

/-- **The novelpoly basis is F-linearly independent**: its 2^k members are
monic of pairwise-distinct degrees, and the degree of a combination with
nonzero coefficients is the maximum of the degrees of its (nonzero) terms —
which is not ⊥, so the combination is not 0. -/
theorem novelBasis_linearIndependent (β : ℕ → F) (k : ℕ) :
    LinearIndependent F (novelBasis β k) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hpair : {j | j ∈ s ∧ g j • novelBasis β k j ≠ 0}.Pairwise
      (Function.onFun Ne (degree ∘ fun j => g j • novelBasis β k j)) := by
    intro a ha b hb hab
    simp only [Function.onFun, Function.comp_apply]
    have hga : g a ≠ 0 := fun h => ha.2 (by rw [h, zero_smul])
    have hgb : g b ≠ 0 := fun h => hb.2 (by rw [h, zero_smul])
    have hda : (g a • novelBasis β k a).degree =
        (((novelBasis β k a).natDegree : ℕ) : WithBot ℕ) := by
      rw [smul_eq_C_mul, degree_mul, degree_C hga, zero_add,
        degree_eq_natDegree (novelBasis_monic β k a).ne_zero]
    have hdb : (g b • novelBasis β k b).degree =
        (((novelBasis β k b).natDegree : ℕ) : WithBot ℕ) := by
      rw [smul_eq_C_mul, degree_mul, degree_C hgb, zero_add,
        degree_eq_natDegree (novelBasis_monic β k b).ne_zero]
    rw [hda, hdb]
    intro heq
    exact hab (novelBasis_natDegree_injective β k (by exact_mod_cast heq))
  have hdeg := degree_sum_eq_of_disjoint (fun j => g j • novelBasis β k j) s hpair
  rw [hsum, degree_zero] at hdeg
  have hle : (g i • novelBasis β k i).degree ≤
      s.sup fun j => (g j • novelBasis β k j).degree :=
    Finset.le_sup (f := fun j => (g j • novelBasis β k j).degree) hi
  rw [← hdeg] at hle
  have h0 : g i • novelBasis β k i = 0 := degree_eq_bot.mp (le_bot_iff.mp hle)
  rcases smul_eq_zero.mp h0 with h | h
  · exact hgi h
  · exact (novelBasis_monic β k i).ne_zero h

/-- Every novelpoly basis polynomial lies in the degree-< 2^k space. -/
theorem novelBasis_mem_degreeLT (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    novelBasis β k c ∈ degreeLT F (2 ^ k) :=
  mem_degreeLT.mpr (by
    rw [degree_eq_natDegree (novelBasis_monic β k c).ne_zero]
    exact_mod_cast novelBasis_natDegree_lt_two_pow β k c)

/-- The novelpoly family, valued in the degree-< 2^k subspace. -/
noncomputable def novelBasisLT (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    degreeLT F (2 ^ k) :=
  ⟨novelBasis β k c, novelBasis_mem_degreeLT β k c⟩

/-- **The novelpoly family is a BASIS of the degree-< 2^k polynomials**: 2^k
linearly independent vectors in the 2^k-dimensional space `degreeLT F (2^k)`. -/
noncomputable def novelBasisBasis (β : ℕ → F) (k : ℕ) :
    Basis (Fin k → ZMod 2) F (degreeLT F (2 ^ k)) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := novelBasisLT β k)
    (LinearIndependent.of_comp (degreeLT F (2 ^ k)).subtype
      (by exact novelBasis_linearIndependent β k))
    (by rw [Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Module.finrank_eq_card_basis (degreeLT.basis F (2 ^ k)), Fintype.card_fin])

@[simp] theorem novelBasisBasis_coe (β : ℕ → F) (k : ℕ) (c : Fin k → ZMod 2) :
    (novelBasisBasis β k c : F[X]) = novelBasis β k c := by
  rw [novelBasisBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-! ### [ANTT-transform] CLOSED: the transform is a linear bijection -/

section Transform

variable [Algebra (ZMod 2) F]

/-- **The additive-NTT transform**, packaged as an F-linear ENDOMORPHISM of
the 2^k-dimensional coefficient space: novelpoly coefficients
a : GF(2)^k → F ↦ the evaluations c ↦ ∑_j a_j·X̂_j(W_k-point c). Both sides
are the same 2^k-dimensional F-space, which is what makes injective ⇒
bijective free. -/
noncomputable def novelBasisTransform (β : ℕ → F) (k : ℕ) :
    ((Fin k → ZMod 2) → F) →ₗ[F] ((Fin k → ZMod 2) → F) where
  toFun a := fun c => ∑ j : Fin k → ZMod 2,
    a j * (novelBasis β k j).eval (domainPoint β k c)
  map_add' a b := by
    funext c
    simp only [Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' r a := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem novelBasisTransform_apply (β : ℕ → F) (k : ℕ)
    (a : (Fin k → ZMod 2) → F) (c : Fin k → ZMod 2) :
    novelBasisTransform β k a c =
      ∑ j : Fin k → ZMod 2, a j * (novelBasis β k j).eval (domainPoint β k c) :=
  rfl

/-- **The transform is injective** for GF(2)-independent β: a coefficient
vector in the kernel gives a polynomial of degree < 2^k vanishing at all 2^k
distinct domain points, hence the zero polynomial, hence (linear independence
of the novelpoly family) the zero coefficient vector. -/
theorem novelBasisTransform_injective {β : ℕ → F} {k : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin k => β j) :
    Function.Injective (novelBasisTransform β k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hcard : (Finset.univ : Finset (Fin k → ZMod 2)).card = 2 ^ k := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hP0 : (∑ j : Fin k → ZMod 2, a j • novelBasis β k j) = 0 := by
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.univ)
      (domainPoint_injective hβ).injOn ?_ ?_
    · rw [hcard]
      exact mem_degreeLT.mp (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (novelBasis_mem_degreeLT β k j))
    · intro c _
      have h := congrFun ha c
      simp only [novelBasisTransform_apply, Pi.zero_apply] at h
      rw [eval_finsetSum]
      simpa only [smul_eq_C_mul, eval_mul, eval_C] using h
  funext j
  exact Fintype.linearIndependent_iff.mp (novelBasis_linearIndependent β k) a hP0 j

/-- **[ANTT-transform], general form: the additive NTT is a BIJECTION** — for
GF(2)-linearly-independent β over any char-2-compatible field, the novelpoly
coefficient-to-evaluation map is a linear bijection (injective endomorphism of
a finite-dimensional space). The additive NTT is a genuine change of basis:
novelpoly coefficients ↔ evaluations on W_k. -/
theorem novelBasisTransform_bijective {β : ℕ → F} {k : ℕ}
    (hβ : LinearIndependent (ZMod 2) fun j : Fin k => β j) :
    Function.Bijective (novelBasisTransform β k) :=
  ⟨novelBasisTransform_injective hβ,
    LinearMap.injective_iff_surjective.mp (novelBasisTransform_injective hβ)⟩

end Transform

/-- **[ANTT-transform] DISCHARGED**: the residual Prop named in
Theory/AdditiveNTT.lean holds — at every binary-tower level, for every
GF(2)-linearly-independent β, the additive NTT is a bijection. -/
theorem novelBasisTransform_closed : NovelBasisTransform := by
  intro m k β hβ
  exact novelBasisTransform_bijective (F := binaryTower m) hβ

/-! ### The fold's affine structure: even/odd words and reconstruction -/

/-- The ODD component of a word on the fold-coset {x, x+β}:
O_f(x) = (f(x) + f(x+β))/β — the word-level analog of the polynomial odd part
P₁ in `foldPoly_decompose` (char 2: the sum is the difference). -/
def foldOdd (β : F) (f : F → F) (x : F) : F := (f x + f (x + β)) / β

/-- The EVEN component of a word on the fold-coset {x, x+β}:
E_f(x) = f(x) + x·O_f(x) — the word-level analog of the polynomial even part
P₀ in `foldPoly_decompose`. -/
def foldEven (β : F) (f : F → F) (x : F) : F := f x + x * foldOdd β f x

/-- **The additive FRI fold is AFFINE in the challenge**:
friFold β λ f = E_f + λ·O_f, pointwise. This is the structural shape the
proximity gap consumes — the folded words, as λ varies, sweep the affine line
through the two component words. (Pure algebra; no characteristic needed.) -/
theorem friFold_eq_even_add_mul_odd (β lam : F) (f : F → F) (x : F) :
    friFold β lam f x = foldEven β f x + lam * foldOdd β f x := by
  unfold friFold foldEven foldOdd
  ring

section FoldComponents

variable [CharP F 2]

/-- The odd component is COSET-INVARIANT: O_f(x+β) = O_f(x) — an honest word
on the image domain. -/
theorem foldOdd_coset_invariant (β : F) (f : F → F) (x : F) :
    foldOdd β f (x + β) = foldOdd β f x := by
  unfold foldOdd
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx : x + β + β = x := by linear_combination β * h2
  rw [hx, add_comm (f (x + β)) (f x)]

/-- The even component is COSET-INVARIANT: E_f(x+β) = E_f(x). -/
theorem foldEven_coset_invariant {β : F} (hβ : β ≠ 0) (f : F → F) (x : F) :
    foldEven β f (x + β) = foldEven β f x := by
  unfold foldEven
  rw [foldOdd_coset_invariant]
  unfold foldOdd
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  field_simp
  linear_combination (β * f (x + β)) * h2

/-- **The RECONSTRUCTION identity**: f(x) = E_f(x) + x·O_f(x) — the word is
recovered from its two components, the analog of P = P₀(q) + X·P₁(q)
(`foldPoly_decompose`) at word level. -/
theorem foldEven_add_mul_foldOdd (β : F) (f : F → F) (x : F) :
    foldEven β f x + x * foldOdd β f x = f x := by
  unfold foldEven
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (x * foldOdd β f x) * h2

/-- **The coset LIFT**: if the even/odd components of f agree with (P₀, P₁) at
the image point q_β(r), then f agrees with Q = P₀∘q_β + X·(P₁∘q_β) at BOTH
points r and r+β of the fiber — downstairs agreement lifts two-for-two
upstairs, preserving density. -/
theorem agree_pair {β : F} (hβ : β ≠ 0) {f : F → F} {P₀ P₁ : F[X]} {r : F}
    (h₀ : foldEven β f r = P₀.eval (foldMap β r))
    (h₁ : foldOdd β f r = P₁.eval (foldMap β r)) :
    f r = (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval r ∧
      f (r + β) = (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval (r + β) := by
  have hfold : foldMap β (r + β) = foldMap β r := foldMap_eq_iff.mpr (Or.inr rfl)
  constructor
  · rw [← foldEven_add_mul_foldOdd β f r, h₀, h₁]
    simp [eval_comp]
  · rw [← foldEven_add_mul_foldOdd β f (r + β), foldEven_coset_invariant hβ,
      foldOdd_coset_invariant, h₀, h₁]
    simp [eval_comp, hfold]

end FoldComponents

/-! ### Distance on finite domains, and the pair-domain structure -/

section Distance

variable [DecidableEq F]

/-- δ-closeness of a word to SOME degree-< d polynomial on the finite domain
D, counting form: at most δ·|D| disagreements. (¬closeToDeg is "δ-far".) -/
def closeToDeg (D : Finset F) (d : ℕ) (δ : ℝ) (f : F → F) : Prop :=
  ∃ P : F[X], P.natDegree < d ∧
    (((D.filter fun x => f x ≠ P.eval x).card : ℝ)) ≤ δ * D.card

/-- δ-closeness of a FOLDED word to degree < d on the IMAGE domain, indexed
through the transversal: the image domain is {q_β(r) : r ∈ R} (|R| honest
points by `foldMap_injOn_transversal`), and the folded word's value over the
image point q_β(r) is g(r) (coset-invariance makes the representative choice
immaterial). -/
def foldedCloseToDeg (R : Finset F) (β : F) (d : ℕ) (δ : ℝ) (g : F → F) : Prop :=
  ∃ P : F[X], P.natDegree < d ∧
    (((R.filter fun r => g r ≠ P.eval (foldMap β r)).card : ℝ)) ≤ δ * R.card

/-- The PAIR DOMAIN R ∪ (R + β): the full fold domain a transversal R
generates — each r ∈ R contributes its coset {r, r+β}. -/
def pairDomain (R : Finset F) (β : F) : Finset F := R ∪ R.image (· + β)

theorem mem_pairDomain {R : Finset F} {β x : F} :
    x ∈ pairDomain R β ↔ x ∈ R ∨ ∃ r ∈ R, r + β = x := by
  rw [pairDomain, Finset.mem_union, Finset.mem_image]

/-- |R ∪ (R+β)| = 2|R| for a transversal (R meets each coset once): the pair
domain genuinely doubles the transversal. -/
theorem pairDomain_card {R : Finset F} {β : F}
    (hR : ∀ r ∈ R, r + β ∉ R) : (pairDomain R β).card = 2 * R.card := by
  have hdisj : Disjoint R (R.image (· + β)) := by
    rw [Finset.disjoint_right]
    intro a ha haR
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
    exact hR r hr haR
  rw [pairDomain, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (add_left_injective β)]
  ring

omit [DecidableEq F] in
/-- **The image domain has |R| honest points**: q_β is injective on a
transversal (the only other preimage of q_β(r) is r + β, which the
transversal excludes) — the folded word lives on a genuinely half-size
domain. -/
theorem foldMap_injOn_transversal [CharP F 2] {β : F} {R : Finset F}
    (hR : ∀ r ∈ R, r + β ∉ R) : Set.InjOn (foldMap β) R := by
  intro x hx y hy hxy
  rcases foldMap_eq_iff.mp hxy.symm with h | h
  · exact h.symm
  · exact absurd (h ▸ Finset.mem_coe.mp hy) (hR x (Finset.mem_coe.mp hx))

/-! ### [ANTT-proximity]: the additive proximity gap, and the reduction -/

/-- **[ANTT-proximity] (hypothesis HERE; PROVED in `Selvage`).** Correlated agreement for
affine lines of words over the additive image domain, bad-challenge-set form:
for words u, v on the image domain (indexed by the transversal r ↦ q_β(r)),
UNLESS some degree-< d pair (P₀, P₁) already has CORRELATED
(1−δ)-agreement with (u, v) — a common agreement set of ≥ (1−δ)|R| image
points — all but at most b challenges λ leave the affine combination u + λ·v
δ-FAR from degree < d.

This is the additive-coset analog of the multiplicative proximity-gap floor
(BCIKS 2020/654 Thm 1.4 / WHIR Thm 4.8; over a finite field "except with
probability err" IS a bad set of ≤ err·|F| challenges). Satisfiable: the
BCIKS proof is evaluation-domain-agnostic — RS proximity gaps hold over ANY
set of distinct points, the domain's multiplicative (or here additive)
structure enters only through the folding algebra, which is proved in this
file — and the exact-agreement regime is PROVED below
(`additiveProximityGap_exact`, δ = 0, b = 1). ⚑ The macroscopic-δ profile is
NOT a standing floor: `Selvage.additiveProximityGap_UD` proves this very
predicate, with `b = |R|`, for every `0 < δ < (1−ρ)/3`, unconditionally and
axiom-clean. It is a hypothesis in THIS file only because the `Theory` boundary
forbids naming `Selvage`. Above `(1−ρ)/3` a realizer is still assumed. -/
def AdditiveProximityGap (R : Finset F) (β : F) (d : ℕ) (δ : ℝ) (b : ℕ) : Prop :=
  ∀ u v : F → F,
    (∀ P₀ P₁ : F[X], P₀.natDegree < d → P₁.natDegree < d →
      ((R.filter fun r => u r = P₀.eval (foldMap β r) ∧
        v r = P₁.eval (foldMap β r)).card : ℝ) < (1 - δ) * R.card) →
    ∃ bad : Finset F, bad.card ≤ b ∧ ∀ lam ∉ bad,
      ¬ foldedCloseToDeg R β d δ (fun r => u r + lam * v r)

/-- **Correlated agreement lifts to closeness upstairs** (the arrow that makes
the proximity gap imply folding soundness): if the even/odd components of f
have correlated (1−δ)-agreement with a degree-< d pair on the image domain,
then f itself is δ-close to degree < 2d on the pair domain — each agreeing
image point lifts to BOTH its preimages (`agree_pair`), so the disagreement
fraction cannot grow. -/
theorem close_of_correlatedAgreement [CharP F 2] {β : F} (hβ : β ≠ 0)
    {R : Finset F} (hR : ∀ r ∈ R, r + β ∉ R) {d : ℕ} {δ : ℝ}
    {f : F → F} {P₀ P₁ : F[X]} (h₀ : P₀.natDegree < d) (h₁ : P₁.natDegree < d)
    (hagree : (1 - δ) * R.card ≤
      ((R.filter fun r => foldEven β f r = P₀.eval (foldMap β r) ∧
        foldOdd β f r = P₁.eval (foldMap β r)).card : ℝ)) :
    closeToDeg (pairDomain R β) (2 * d) δ f := by
  refine ⟨P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β), ?_, ?_⟩
  · -- degree: < 2d
    have hc₀ : (P₀.comp (foldPoly β)).natDegree ≤ P₀.natDegree * 2 := by
      simpa [foldPoly_natDegree] using natDegree_comp_le (p := P₀) (q := foldPoly β)
    have hc₁ : (P₁.comp (foldPoly β)).natDegree ≤ P₁.natDegree * 2 := by
      simpa [foldPoly_natDegree] using natDegree_comp_le (p := P₁) (q := foldPoly β)
    have hx₁ : (X * P₁.comp (foldPoly β)).natDegree ≤ 1 + P₁.natDegree * 2 :=
      le_trans natDegree_mul_le (by rw [natDegree_X]; omega)
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_) <;> omega
  · -- distance: disagreements live over the non-agreeing transversal points
    set S := R.filter (fun r => foldEven β f r = P₀.eval (foldMap β r) ∧
      foldOdd β f r = P₁.eval (foldMap β r)) with hS
    have hSsub : S ⊆ R := Finset.filter_subset _ _
    have hagr : ∀ r ∈ S,
        f r = (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval r ∧
        f (r + β) = (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval (r + β) := by
      intro r hr
      obtain ⟨-, h0, h1⟩ := Finset.mem_filter.mp hr
      exact agree_pair hβ h0 h1
    have hsub : (pairDomain R β).filter
        (fun x => f x ≠ (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval x) ⊆
        (R \ S) ∪ (R \ S).image (· + β) := by
      intro x hx
      obtain ⟨hxD, hxne⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hxD with hxR | hxI
      · exact Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hxR, fun hxS => hxne (hagr x hxS).1⟩)
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hxI
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨r, Finset.mem_sdiff.mpr ⟨hr, fun hrS => hxne (hagr r hrS).2⟩, rfl⟩)
    have hcount : ((pairDomain R β).filter
        (fun x => f x ≠ (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval x)).card ≤
        2 * (R \ S).card := by
      refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
      rw [Finset.card_image_of_injective _ (add_left_injective β)]
      omega
    have hsdiff : ((R \ S).card : ℝ) = (R.card : ℝ) - S.card := by
      rw [Finset.card_sdiff_of_subset hSsub, Nat.cast_sub (Finset.card_le_card hSsub)]
    have hcount' : (((pairDomain R β).filter
        (fun x => f x ≠ (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval x)).card : ℝ) ≤
        2 * ((R.card : ℝ) - S.card) := by
      rw [← hsdiff]
      exact_mod_cast hcount
    have hDcard : ((pairDomain R β).card : ℝ) = 2 * R.card := by
      rw [pairDomain_card hR]
      push_cast
      ring
    rw [hDcard]
    rw [hS] at hagree
    linarith

/-- **[ANTT-fri]: the additive fold preserves distance, given the additive
proximity gap — which is PROVED, so see `Selvage.additiveFold_distance_UD` for
the same conclusion with the `hPG` slot already filled on `δ < (1−ρ)/3`.** If f is δ-FAR from every degree-< 2d polynomial on
the pair domain, then off a bad set of at most b challenges the folded word
friFold β λ f is still δ-FAR from degree < d on the image domain — no loss in
δ. Proof: the fold is the affine line E_f + λ·O_f
(`friFold_eq_even_add_mul_odd`); were the components correlated-agreeing, f
would be δ-close (`close_of_correlatedAgreement`), so they are not, and
[ANTT-proximity] bounds the good challenges by b. Together with
`friFold_eval_poly` (completeness) this closes the additive FRI round; on the
macroscopic band `δ < (1−ρ)/3` the `hPG` argument is supplied by
`Selvage.additiveProximityGap_UD`, so nothing there is left assumed. -/
theorem additiveFold_distance [CharP F 2] {β : F} (hβ : β ≠ 0)
    {R : Finset F} (hR : ∀ r ∈ R, r + β ∉ R) {d : ℕ} {δ : ℝ} {b : ℕ}
    (hPG : AdditiveProximityGap R β d δ b) {f : F → F}
    (hfar : ¬ closeToDeg (pairDomain R β) (2 * d) δ f) :
    ∃ bad : Finset F, bad.card ≤ b ∧ ∀ lam ∉ bad,
      ¬ foldedCloseToDeg R β d δ (friFold β lam f) := by
  have hprem : ∀ P₀ P₁ : F[X], P₀.natDegree < d → P₁.natDegree < d →
      ((R.filter fun r => foldEven β f r = P₀.eval (foldMap β r) ∧
        foldOdd β f r = P₁.eval (foldMap β r)).card : ℝ) < (1 - δ) * R.card := by
    intro P₀ P₁ h₀ h₁
    by_contra hno
    push Not at hno
    exact hfar (close_of_correlatedAgreement hβ hR h₀ h₁ hno)
  obtain ⟨bad, hbad, hlam⟩ := hPG (foldEven β f) (foldOdd β f) hprem
  refine ⟨bad, hbad, fun lam hl hclose => hlam lam hl ?_⟩
  have hfun : (fun r => foldEven β f r + lam * foldOdd β f r) = friFold β lam f := by
    funext x
    rw [friFold_eq_even_add_mul_odd]
  rw [hfun]
  exact hclose

/-- **The exact-agreement regime of [ANTT-proximity] is PROVED,
unconditionally, with b = 1** (any field — no characteristic assumption): at
δ = 0, closeness is exact agreement, and TWO distinct challenges on the
affine line u + λ·v determine both components as degree-< d words (solve the
2×2 linear system), forcing full correlated agreement. The additive analog of
the multiplicative sub-quantization result, and the satisfiability witness
for the [ANTT-proximity] statement shape. -/
theorem additiveProximityGap_exact (R : Finset F) (β : F) (d : ℕ) :
    AdditiveProximityGap R β d 0 1 := by
  intro u v hno
  by_cases hex : ∃ lam : F, foldedCloseToDeg R β d 0 (fun r => u r + lam * v r)
  · obtain ⟨lam₀, hlam₀⟩ := hex
    refine ⟨{lam₀}, by simp, ?_⟩
    intro lam hl hclose
    have hne0 : lam ≠ lam₀ := fun h => hl (Finset.mem_singleton.mpr h)
    have hne : lam - lam₀ ≠ 0 := sub_ne_zero.mpr hne0
    obtain ⟨A, hA, hAcard⟩ := hclose
    obtain ⟨B, hB, hBcard⟩ := hlam₀
    -- δ = 0 closeness is exact agreement on all of R
    have hAagree : ∀ r ∈ R, u r + lam * v r = A.eval (foldMap β r) := by
      have hA0 : (R.filter fun r => u r + lam * v r ≠ A.eval (foldMap β r)) = ∅ := by
        rw [← Finset.card_eq_zero]
        have h0 : ((R.filter fun r =>
            u r + lam * v r ≠ A.eval (foldMap β r)).card : ℝ) ≤ 0 := by
          simpa using hAcard
        exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
      intro r hr
      by_contra hne'
      exact Finset.filter_eq_empty_iff.mp hA0 hr hne'
    have hBagree : ∀ r ∈ R, u r + lam₀ * v r = B.eval (foldMap β r) := by
      have hB0 : (R.filter fun r => u r + lam₀ * v r ≠ B.eval (foldMap β r)) = ∅ := by
        rw [← Finset.card_eq_zero]
        have h0 : ((R.filter fun r =>
            u r + lam₀ * v r ≠ B.eval (foldMap β r)).card : ℝ) ≤ 0 := by
          simpa using hBcard
        exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
      intro r hr
      by_contra hne'
      exact Finset.filter_eq_empty_iff.mp hB0 hr hne'
    -- solve the 2×2 system: both components are low-degree words
    set P₁ : F[X] := C (lam - lam₀)⁻¹ * (A - B) with hP₁
    set P₀ : F[X] := A - C lam * P₁ with hP₀
    have hvP : ∀ r ∈ R, v r = P₁.eval (foldMap β r) := by
      intro r hr
      have h1 := hAagree r hr
      have h2 := hBagree r hr
      rw [hP₁]
      simp only [eval_mul, eval_C, eval_sub]
      field_simp
      linear_combination h1 - h2
    have huP : ∀ r ∈ R, u r = P₀.eval (foldMap β r) := by
      intro r hr
      have h1 := hAagree r hr
      have hv := hvP r hr
      rw [hP₀]
      simp only [eval_sub, eval_mul, eval_C]
      linear_combination h1 - lam * hv
    have hd₁ : P₁.natDegree < d :=
      lt_of_le_of_lt (le_trans (natDegree_C_mul_le _ _) (natDegree_sub_le _ _))
        (max_lt hA hB)
    have hd₀ : P₀.natDegree < d :=
      lt_of_le_of_lt (natDegree_sub_le _ _)
        (max_lt hA (lt_of_le_of_lt (natDegree_C_mul_le _ _) hd₁))
    have hcontra := hno P₀ P₁ hd₀ hd₁
    have hfull : R.filter (fun r => u r = P₀.eval (foldMap β r) ∧
        v r = P₁.eval (foldMap β r)) = R :=
      Finset.filter_eq_self.mpr fun r hr => ⟨huP r hr, hvP r hr⟩
    rw [hfull] at hcontra
    norm_num at hcontra
  · exact ⟨∅, by simp, fun lam _ hclose => hex ⟨lam, hclose⟩⟩

/-- **Unconditional end-to-end fold soundness at exact resolution**: a word
that is NOT exactly a degree-< 2d evaluation on the pair domain folds, off at
most ONE challenge, to a word that is not exactly a degree-< d evaluation on
the image domain. `additiveFold_distance` composed with the proved
exact-regime gap — no hypothesis left. -/
theorem additiveFold_distance_exact [CharP F 2] {β : F} (hβ : β ≠ 0)
    {R : Finset F} (hR : ∀ r ∈ R, r + β ∉ R) {d : ℕ} {f : F → F}
    (hfar : ¬ closeToDeg (pairDomain R β) (2 * d) 0 f) :
    ∃ bad : Finset F, bad.card ≤ 1 ∧ ∀ lam ∉ bad,
      ¬ foldedCloseToDeg R β d 0 (friFold β lam f) :=
  additiveFold_distance hβ hR (additiveProximityGap_exact R β d) hfar

end Distance

/-! ### Keystones at the deployed tower: GF(16), the 4-point domain -/

/-- KEYSTONE (satisfiable): **the transform at the concrete 4-point domain is
a bijection** — GF(16) = `binaryTower 2`, W₂ = span{1, x₁} with its 4 points
(`keystone_domain_card`), and the 4-coefficient ↔ 4-evaluation map is a
linear bijection. -/
theorem keystone_transform_bijective :
    Function.Bijective (novelBasisTransform keystoneBeta 2) :=
  novelBasisTransform_bijective keystoneBeta_linearIndependent

/-- **TEETH (general): the strict degree bound is load-bearing** — at degree
2^k (one above the transform's < 2^k) evaluation no longer determines the
polynomial: Ŵ_k is a NONZERO polynomial of degree exactly 2^k whose
evaluations at ALL 2^k domain points coincide with those of the ZERO
polynomial. -/
theorem eval_domain_not_injective_at_two_pow [CharP F 2] [Algebra (ZMod 2) F]
    (β : ℕ → F) (k : ℕ) :
    ∃ P : F[X], P ≠ 0 ∧ P.natDegree = 2 ^ k ∧
      ∀ c : Fin k → ZMod 2, P.eval (domainPoint β k c) = 0 :=
  ⟨subspaceVanishing β k, (subspaceVanishing_monic β k).ne_zero,
    subspaceVanishing_natDegree β k, subspaceVanishing_eval_domainPoint β k⟩

/-- KEYSTONE TEETH: at GF(16), Ŵ₂ ≠ 0 has degree 4 = 2² and evaluates to 0 at
every one of the 4 domain points — a degree-2^k polynomial is NOT determined
by its 2^k values; the bijection genuinely needs degree < 2^k. -/
theorem keystone_transform_degree_tooth :
    subspaceVanishing keystoneBeta 2 ≠ 0 ∧
      (subspaceVanishing keystoneBeta 2).natDegree = 2 ^ 2 ∧
      ∀ c : Fin 2 → ZMod 2,
        (subspaceVanishing keystoneBeta 2).eval (domainPoint keystoneBeta 2 c) = 0 :=
  ⟨(subspaceVanishing_monic keystoneBeta 2).ne_zero,
    subspaceVanishing_natDegree keystoneBeta 2,
    subspaceVanishing_eval_domainPoint keystoneBeta 2⟩

/-- **TEETH (general): the fold genuinely reduces degree, computed** — the
identity word (a degree-1 evaluation) folds to the CONSTANT word λ (a
degree-0 evaluation): friFold β λ id = const λ. The degree-halving of
`friFold_eval_poly` exercised at the smallest nontrivial instance. -/
theorem friFold_id [CharP F 2] {β : F} (hβ : β ≠ 0) (lam : F) (x : F) :
    friFold β lam (fun t => t) x = lam := by
  unfold friFold
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [show x + (x + β) = β by linear_combination x * h2, div_self hβ, mul_one]
  linear_combination x * h2

/-- KEYSTONE TEETH: over GF(16) with β = x₁, the degree-1 word folds to the
degree-0 word — concrete degree reduction at the deployed tower. -/
theorem keystone_fold_degree_tooth (lam x : binaryTower 2) :
    friFold (fpGen 1) lam (fun t => t) x = lam :=
  friFold_id (fpGen_ne_zero 1) lam x

open scoped Classical in
/-- KEYSTONE: {0, 1} is a TRANSVERSAL for the fold by β = x₁ in GF(16) — its
pair domain {0, 1} ∪ {x₁, 1 + x₁} is the 4-point keystone domain, one
representative per fold-coset. -/
theorem keystone_transversal :
    ∀ r ∈ ({0, 1} : Finset (binaryTower 2)),
      r + fpGen 1 ∉ ({0, 1} : Finset (binaryTower 2)) := by
  have h2 : (2 : binaryTower 2) = 0 := binaryTower_two_eq_zero 2
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  push Not
  rcases hr with rfl | rfl
  · exact ⟨by simpa using fpGen_ne_zero 1, by simpa using fpGen_ne_one 1⟩
  · constructor
    · intro h
      exact fpGen_ne_one 1 (by linear_combination h - h2)
    · intro h
      exact fpGen_ne_zero 1 (by linear_combination h)

open scoped Classical in
/-- KEYSTONE: **unconditional fold soundness at the concrete GF(16) domain** —
over the 4-point pair domain of `keystoneBeta`, a word that is not exactly
low-degree stays not-exactly-low-degree after folding, off at most one
challenge. The whole [ANTT-fri] reduction machinery exercised end-to-end with
zero hypotheses. -/
theorem keystone_fold_distance {d : ℕ} {f : binaryTower 2 → binaryTower 2}
    (hfar : ¬ closeToDeg (pairDomain {0, 1} (fpGen 1)) (2 * d) 0 f) :
    ∃ bad : Finset (binaryTower 2), bad.card ≤ 1 ∧ ∀ lam ∉ bad,
      ¬ foldedCloseToDeg {0, 1} (fpGen 1) d 0 (friFold (fpGen 1) lam f) :=
  additiveFold_distance_exact (fpGen_ne_zero 1) keystone_transversal hfar

open scoped Classical in
/-- TEETH (premise inhabitation for the fold-distance reduction): FAR WORDS
EXIST at the concrete domain — the indicator word of the point 1 + x₁ on the
4-point pair domain agrees with NO degree-< 2 polynomial: such a P would
vanish at 0 and 1 (two roots force the affine P to zero) and then miss the
value 1 at 1 + x₁. So `keystone_fold_distance` (at d = 1) speaks about a
nonempty class of words. -/
theorem keystone_far_word_exists :
    ∃ f : binaryTower 2 → binaryTower 2,
      ¬ closeToDeg (pairDomain {0, 1} (fpGen 1)) (2 * 1) 0 f := by
  have h2 : (2 : binaryTower 2) = 0 := binaryTower_two_eq_zero 2
  refine ⟨fun x => if x = 1 + fpGen 1 then 1 else 0, ?_⟩
  rintro ⟨P, hPdeg, hPcard⟩
  -- δ = 0 closeness is exact agreement on the whole pair domain
  have hagree : ∀ x ∈ pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1),
      (if x = 1 + fpGen 1 then (1 : binaryTower 2) else 0) = P.eval x := by
    have h0 : ((pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).filter
        fun x => (if x = 1 + fpGen 1 then (1 : binaryTower 2) else 0) ≠ P.eval x) = ∅ := by
      rw [← Finset.card_eq_zero]
      have hle : (((pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).filter
          fun x => (if x = 1 + fpGen 1 then (1 : binaryTower 2) else 0) ≠ P.eval x).card
            : ℝ) ≤ 0 := by
        simpa using hPcard
      exact_mod_cast le_antisymm hle (Nat.cast_nonneg _)
    intro x hx
    by_contra hne
    exact Finset.filter_eq_empty_iff.mp h0 hx hne
  -- the three pinning points
  have hx0 : (0 : binaryTower 2) ∈ pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1) :=
    mem_pairDomain.mpr (Or.inl (by simp))
  have hx1 : (1 : binaryTower 2) ∈ pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1) :=
    mem_pairDomain.mpr (Or.inl (by simp))
  have hxg : (1 + fpGen 1 : binaryTower 2) ∈
      pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1) :=
    mem_pairDomain.mpr (Or.inr ⟨1, by simp, rfl⟩)
  have hne0 : (0 : binaryTower 2) ≠ 1 + fpGen 1 := fun h =>
    fpGen_ne_one 1 (by linear_combination -h - h2)
  have hne1 : (1 : binaryTower 2) ≠ 1 + fpGen 1 := fun h =>
    fpGen_ne_zero 1 (by linear_combination -h)
  have hP0 : P.eval 0 = 0 := by
    have := hagree 0 hx0
    rw [if_neg hne0] at this
    exact this.symm
  have hP1 : P.eval 1 = 0 := by
    have := hagree 1 hx1
    rw [if_neg hne1] at this
    exact this.symm
  have hPg : P.eval (1 + fpGen 1) = 1 := by
    have := hagree (1 + fpGen 1) hxg
    rw [if_pos rfl] at this
    exact this.symm
  -- but an affine polynomial vanishing at 0 and 1 is zero
  have hdeg1 : P.degree ≤ 1 :=
    natDegree_le_iff_degree_le.mp (by omega : P.natDegree ≤ 1)
  obtain hP := eq_X_add_C_of_degree_le_one hdeg1
  rw [hP] at hP0 hP1 hPg
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add, mul_one] at hP0 hP1 hPg
  exact one_ne_zero (α := binaryTower 2)
    (by linear_combination -hPg + (1 + fpGen 1) * hP1 - fpGen 1 * hP0)

open scoped Classical in
/-- KEYSTONE (coherence): the pair domain of the transversal {0, 1} under the
fold by x₁ IS the 4-point additive-NTT domain W₂ = span{1, x₁} — the domain
the transform bijection (`keystone_transform_bijective`) evaluates on is
exactly the domain the fold folds: {0, 1} ∪ {x₁, 1 + x₁} = W₂, pointwise. -/
theorem keystone_pairDomain_eq_additiveDomain (x : binaryTower 2) :
    x ∈ pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1) ↔
      x ∈ additiveDomain keystoneBeta 2 := by
  rw [mem_pairDomain, mem_additiveDomain_iff]
  have hbit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  constructor
  · rintro (hx | ⟨r, hr, rfl⟩)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨![0, 0], by simp [domainPoint, Fin.sum_univ_two]⟩
      · exact ⟨![1, 0], by simp [domainPoint, Fin.sum_univ_two]⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨![0, 1], by simp [domainPoint, Fin.sum_univ_two]⟩
      · exact ⟨![1, 1], by simp [domainPoint, Fin.sum_univ_two]⟩
  · rintro ⟨c, rfl⟩
    have hsplit : domainPoint keystoneBeta 2 c =
        c 0 • (1 : binaryTower 2) + c 1 • fpGen 1 := by
      simp [domainPoint, Fin.sum_univ_two]
    rcases hbit (c 0) with h0 | h0 <;> rcases hbit (c 1) with h1 | h1 <;>
      rw [hsplit, h0, h1] <;>
      simp only [zero_smul, one_smul, add_zero, zero_add]
    · exact Or.inl (by simp)
    · exact Or.inr ⟨0, by simp, zero_add _⟩
    · exact Or.inl (by simp)
    · exact Or.inr ⟨1, by simp, rfl⟩

end Minidregg.Theory
