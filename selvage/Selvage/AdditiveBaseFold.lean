/-
# Selvage.AdditiveBaseFold — BaseFold's descent, ported to the additive (char-2) tower

The multiplicative BaseFold cone (`Selvage/BaseFoldCompleteness.lean`) opens a
multilinear commitment by folding a univariate codeword with
`p ↦ evenPart p + C α * oddPart p`, m times, and reading the terminal constant.
This file does the same thing over a CHARACTERISTIC-TWO field, where the
multiplicative even/odd split `P(X) = P₀(X²) + X·P₁(X²)` does not exist and is
replaced by the LCH additive split `P = P₀∘q_β + X·(P₁∘q_β)` with
`q_β = X² + βX` (`Theory/AdditiveNTT.lean`'s `foldPoly_decompose`).

## ⚠ THE `two_ne` VACUITY TRAP, AND HOW THIS FILE AVOIDS IT — stated as a THEOREM

`Selvage/Proximity.lean`'s `FoldingData` carries `two_ne : (2 : F) ≠ 0` as a
STRUCTURE FIELD. In characteristic two that field is uninhabitable, so **every
theorem quantified over a `FoldingData` (or a `FoldingTower`, which contains one
per level) is VACUOUSLY TRUE at a binary field, on a green build.** That is not
a warning here, it is `Selvage/CharTwoWall.lean`'s `foldingData_isEmpty_charTwo`
and `foldingData_vacuous_of_charTwo` — IMPORTED, not restated: the carrier is
provably `IsEmpty` under `[CharP F 2]` and every predicate over it is free, so
the trap is machine-checked rather than described. **Not one declaration below
takes a `FoldingData`, a `FoldingTower`, `fold`, `proximityTest` or `chalExt` as
an argument**, which is the only way a char-2 result over this tree can carry
content.

**This file therefore contains no `FoldingData`, no `FoldingTower`, no `fold`,
no `proximityTest`, and no `chalExt`.** The descent operator is
`Minidregg.Theory.friFold` — the additive fold, defined on functions, with no
characteristic-≠-2 side condition anywhere.

What it DOES reuse from the prime cone is exactly the part that never mentions a
`FoldingData`: the Boolean-Möbius/coefficient layer of
`Selvage/MultiplicativeMleTerminal.lean` and `Selvage/BaseFoldCompleteness.lean`
(`evenPart`, `oddPart`, `mleCoefficientFold`, `foldMleVariables`,
`booleanMobiusPolynomial`, `tableOfPoly`, `coeff_zero_foldMleVariables_eq_mle`).
Those are statements about coefficient vectors over an arbitrary `Field F`; they
are not vacuous in characteristic two, and the keystones at the end of this file
fire at `binaryTower 2 = GF(16)` with concrete non-equal values to prove it.

## The port, item by item (the prime structure is the map)

| prime object | status in char 2 |
|---|---|
| Möbius round trip (`booleanMobiusPolynomial` ↔ `tableOfPoly`) | **PORTS VERBATIM** — cited, not reproved; it is a change of basis on coefficient VECTORS with no field characteristic in it |
| the fold operator `fold`/`FoldingData` | **GENUINELY DIFFERENT** — replaced by `friFold`; the multiplicative one is not merely inconvenient here, it is uninhabited |
| `fold_eval` (fold of a codeword = codeword of a folded polynomial) | **CHAR-2 ANALOGUE**: `friFold_eval_decomp` below (derived from `Theory`'s already-proved `friFold_eq_even_add_mul_odd` + coset invariance) |
| the monomial packing `X^{Σ cᵢ2^i}` | **CHAR-2 ANALOGUE**: `novelPack`, the LCH novelpoly packing `∏ Ŵᵢ^{cᵢ}`; the recursion is `parityInterleave` with `expand F 2` replaced by `.comp (foldPoly (β 0))` |
| tower-fold induction (`word_eval_foldMleVariables`) | **CHAR-2 ANALOGUE**: `lchLevelWord_succ` — one `friFold` carries level `n` to level `n+1`, with the basis itself folding (`lchTowerBasis`) |
| terminal-word identity (`basefold_terminal_word_eq`) | **PORTS, through the analogue**: `lchLevelWord_terminal` / `lch_commit_terminal_eq` |
| the distance bound (`relDist_fold_le`) | **ALREADY PROVED ADDITIVELY** — `Selvage/AdditiveProximity.lean`'s `additiveFold_distance_UD`, on the unconditional band `δ < (1−ρ)/3`. Cited, not restated. |

## ⚑ The new ambiguity, and it is char-2-specific

The prime cone's teeth exhibit two commitments of "the same" data both passing
the descent and terminating at different constants; they were resolved as two
honest claims about DIFFERENT TABLES, and the resolution ports (the terminal is
`mle (tableOfPoly m p) r` for the same total `tableOfPoly` in both worlds).

But characteristic two has a second, strictly new one. The novelpoly basis is
parameterized by the ORDERED GF(2)-basis β, while the evaluation domain is only
its SPAN. So one and the same codeword, on one and the same domain, is an honest
commitment to two DIFFERENT tables under two bases of that domain:
`keystone_basis_ambiguity` exhibits it at GF(16) with β = (1, x₁) and
β' = (x₁, 1) — same four-point domain, same univariate polynomial, different
tables. **The additive-FRI transcript must bind the ordered basis, not just the
domain.** Nothing in this tree does that today; that is named, not repaired here.
-/
import Selvage.AdditiveProximity
import Selvage.BaseFoldCompleteness
import Selvage.CharTwoWall

namespace Minidregg.Selvage

open Polynomial
open Minidregg.Theory

variable {F : Type*} [Field F]

/-! ## 1. The additive fold reads off an additive decomposition

`Theory/AdditiveNTT.lean` proves `friFold_eval_poly`: folding the evaluation
word of a degree-≤ 2d+1 polynomial gives the evaluation word of SOME degree-≤ d
polynomial. For a descent we need the polynomial NAMED, so we state the sharp
form on an already-split polynomial. This is the char-2 analogue of the prime
cone's `fold_eval`. -/

section Decomp

variable [CharP F 2]

/-- ⭐ **THE OPERATOR IDENTITY, char-2 form.** One `friFold` of the evaluation
word of `P₀∘q_β + X·(P₁∘q_β)` is the evaluation word of `P₀ + λ·P₁` on the image
domain. (The prime statement `fold_eval` says the same thing with `X²` for `q_β`
and `evenPart`/`oddPart` for `P₀`/`P₁`.) -/
theorem friFold_eval_decomp {β : F} (hβ : β ≠ 0) (lam : F) (P₀ P₁ : F[X]) (x : F) :
    friFold β lam
        (fun t => (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval t) x
      = (P₀ + C lam * P₁).eval (foldMap β x) := by
  set f : F → F :=
    fun t => (P₀.comp (foldPoly β) + X * P₁.comp (foldPoly β)).eval t with hf
  have hev : ∀ t : F, f t = P₀.eval (foldMap β t) + t * P₁.eval (foldMap β t) := by
    intro t; simp [hf, eval_comp]
  have hfold : foldMap β (x + β) = foldMap β x := foldMap_eq_iff.mpr (Or.inr rfl)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hodd : Minidregg.Theory.foldOdd β f x = P₁.eval (foldMap β x) := by
    unfold Minidregg.Theory.foldOdd
    rw [hev x, hev (x + β), hfold]
    have hnum : P₀.eval (foldMap β x) + x * P₁.eval (foldMap β x) +
        (P₀.eval (foldMap β x) + (x + β) * P₁.eval (foldMap β x)) =
        β * P₁.eval (foldMap β x) := by
      linear_combination (P₀.eval (foldMap β x) + x * P₁.eval (foldMap β x)) * h2
    rw [hnum, mul_div_cancel_left₀ _ hβ]
  have heven : Minidregg.Theory.foldEven β f x = P₀.eval (foldMap β x) := by
    unfold Minidregg.Theory.foldEven
    rw [hodd, hev x]
    linear_combination (x * P₁.eval (foldMap β x)) * h2
  rw [friFold_eq_even_add_mul_odd, heven, hodd, eval_add, eval_mul, eval_C]

end Decomp

/-! ## 2. The LCH packing: the char-2 analogue of the monomial packing

The prime cone packs multilinear coefficients LSB-first into the MONOMIAL basis,
so that `evenPart`/`oddPart` peel the low variable. Here the same coefficients
are packed into the LCH NOVELPOLY basis `X̂_c = ∏ᵢ Ŵᵢ^{cᵢ}`, so that the ADDITIVE
split peels the low variable. The recursion is literally `parityInterleave` —
`expand F 2 e + X * expand F 2 o` — with `expand F 2` (i.e. `.comp (X²)`)
replaced by `.comp (foldPoly (β 0))` (i.e. `.comp (X² + β₀X)`).

`Theory.novelBasis`'s triangularity (`novelBasis_natDegree_lt_two_pow`,
`novelBasisBasis`) is the abstract statement that this is a change of basis;
`novelPack_bijOn_window` below is the constructive form the descent needs. -/

/-- The image of the GF(2)-basis under one additive fold: the ordered basis of
the next level's domain, `β'ⱼ = q_{β₀}(β_{j+1})`. -/
def additiveFoldedBasis (β : ℕ → F) : ℕ → F := fun j => foldMap (β 0) (β (j + 1))

/-- ⭐ **THE LCH PACKING.** Pack the first `2^m` monomial coefficients of `p` into
the novelpoly basis of the ordered GF(2)-basis `β`. Compare
`parityInterleave e o = expand F 2 e + X * expand F 2 o`: the only change is
which degree-2 map the two halves are composed with. -/
noncomputable def novelPack : (ℕ → F) → ℕ → F[X] → F[X]
  | _, 0, p => C (p.coeff 0)
  | β, m + 1, p =>
      (novelPack (additiveFoldedBasis β) m (evenPart p)).comp (foldPoly (β 0)) +
        X * (novelPack (additiveFoldedBasis β) m (oddPart p)).comp (foldPoly (β 0))

@[simp] theorem novelPack_zero (β : ℕ → F) (p : F[X]) :
    novelPack β 0 p = C (p.coeff 0) := rfl

theorem novelPack_succ (β : ℕ → F) (m : ℕ) (p : F[X]) :
    novelPack β (m + 1) p =
      (novelPack (additiveFoldedBasis β) m (evenPart p)).comp (foldPoly (β 0)) +
        X * (novelPack (additiveFoldedBasis β) m (oddPart p)).comp (foldPoly (β 0)) :=
  rfl

/-- At `m = 1` the packing is basis-INDEPENDENT: `X̂₀ = 1`, `X̂₁ = Ŵ₀ = X`. (This
is why the basis ambiguity below needs `m = 2`.) -/
theorem novelPack_one (β : ℕ → F) (p : F[X]) :
    novelPack β 1 p = C (p.coeff 0) + C (p.coeff 1) * X := by
  rw [novelPack_succ]
  simp only [novelPack_zero, C_comp, coeff_evenPart_terminal, coeff_oddPart_terminal]
  ring_nf

/-- At `m = 2` the basis enters: `X̂ = (1, X, Ŵ₁, X·Ŵ₁)` with `Ŵ₁ = q_{β₀}`. -/
theorem novelPack_two (β : ℕ → F) (p : F[X]) :
    novelPack β 2 p =
      C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * foldPoly (β 0) +
        C (p.coeff 3) * (X * foldPoly (β 0)) := by
  rw [novelPack_succ, novelPack_one, novelPack_one]
  simp only [coeff_evenPart_terminal, coeff_oddPart_terminal, add_comp, mul_comp,
    C_comp, X_comp]
  norm_num
  ring

/-! ### Linearity and the degree window -/

theorem novelPack_add : ∀ (m : ℕ) (β : ℕ → F) (p q : F[X]),
    novelPack β m (p + q) = novelPack β m p + novelPack β m q := by
  intro m
  induction m with
  | zero => intro β p q; simp
  | succ m ih =>
      intro β p q
      rw [novelPack_succ, novelPack_succ, novelPack_succ, evenPart_add_terminal,
        oddPart_add_terminal, ih, ih, add_comp, add_comp]
      ring

theorem novelPack_C_mul : ∀ (m : ℕ) (β : ℕ → F) (a : F) (p : F[X]),
    novelPack β m (C a * p) = C a * novelPack β m p := by
  intro m
  induction m with
  | zero => intro β a p; simp
  | succ m ih =>
      intro β a p
      rw [novelPack_succ, novelPack_succ, evenPart_C_mul_terminal,
        oddPart_C_mul_terminal, ih, ih, mul_comp, mul_comp, C_comp]
      ring

/-- **The packing stays inside the degree window** — unconditionally: the
level-`m` packing of ANY polynomial has `natDegree < 2^m`, because
`deg (A∘q) = 2·deg A` and `deg (X·B∘q) = 2·deg B + 1`. This is the base check of
the low-degree test, met by construction rather than by hypothesis. -/
theorem novelPack_natDegree_lt : ∀ (m : ℕ) (β : ℕ → F) (p : F[X]),
    (novelPack β m p).natDegree < 2 ^ m := by
  intro m
  induction m with
  | zero => intro β p; simp
  | succ m ih =>
      intro β p
      have hA := ih (additiveFoldedBasis β) (evenPart p)
      have hB := ih (additiveFoldedBasis β) (oddPart p)
      have hq : (foldPoly (β 0)).natDegree = 2 := foldPoly_natDegree _
      have h1 : ((novelPack (additiveFoldedBasis β) m (evenPart p)).comp
          (foldPoly (β 0))).natDegree ≤
          (novelPack (additiveFoldedBasis β) m (evenPart p)).natDegree * 2 := by
        simpa [hq] using natDegree_comp_le
          (p := novelPack (additiveFoldedBasis β) m (evenPart p)) (q := foldPoly (β 0))
      have h2 : (X * (novelPack (additiveFoldedBasis β) m (oddPart p)).comp
          (foldPoly (β 0))).natDegree ≤
          1 + (novelPack (additiveFoldedBasis β) m (oddPart p)).natDegree * 2 := by
        refine le_trans natDegree_mul_le ?_
        rw [natDegree_X]
        exact Nat.add_le_add_left (by
          simpa [hq] using natDegree_comp_le
            (p := novelPack (additiveFoldedBasis β) m (oddPart p))
            (q := foldPoly (β 0))) 1
      have hsum := natDegree_add_le
        ((novelPack (additiveFoldedBasis β) m (evenPart p)).comp (foldPoly (β 0)))
        (X * (novelPack (additiveFoldedBasis β) m (oddPart p)).comp (foldPoly (β 0)))
      rw [novelPack_succ]
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega

/-! ## 3. One round of the additive descent

⭐ The round theorem. Folding the level-`m+1` packing of `p` at challenge `λ` is
the level-`m` packing of `mleCoefficientFold p λ` — the SAME coefficient
operator the prime cone folds with. The multilinear layer is untouched; only the
basis the coefficients are packed into changed. -/

section Round

variable [CharP F 2]

/-- ⭐ **THE ROUND IDENTITY.** `friFold` on the LCH packing of `p` is the LCH
packing of `mleCoefficientFold p λ` on the folded basis, read at the folded
point. This is the char-2 counterpart of `fold_eval_mleCoefficientFold`. -/
theorem novelPack_friFold (β : ℕ → F) (hβ : β 0 ≠ 0) (m : ℕ) (p : F[X])
    (lam x : F) :
    friFold (β 0) lam (fun t => (novelPack β (m + 1) p).eval t) x
      = (novelPack (additiveFoldedBasis β) m (mleCoefficientFold p lam)).eval
          (foldMap (β 0) x) := by
  rw [novelPack_succ, friFold_eval_decomp hβ, mleCoefficientFold, novelPack_add,
    novelPack_C_mul]

end Round

/-! ## 4. The tower: the basis folds along with the word

Unlike the multiplicative tower, where the domain chain is `x ↦ x²` applied to a
fixed generator, here the ORDERED BASIS is the state: level `n` folds by the
pivot `βₙ⁽ⁿ⁾ = lchPivot β n`, and its basis is `β` folded `n` times. -/

/-- `β` after `n` additive folds — the ordered GF(2)-basis of the level-`n`
domain. -/
noncomputable def lchTowerBasis : (ℕ → F) → ℕ → (ℕ → F)
  | β, 0 => β
  | β, n + 1 => lchTowerBasis (additiveFoldedBasis β) n

@[simp] theorem lchTowerBasis_zero (β : ℕ → F) : lchTowerBasis β 0 = β := rfl

theorem lchTowerBasis_succ (β : ℕ → F) (n : ℕ) :
    lchTowerBasis β (n + 1) = lchTowerBasis (additiveFoldedBasis β) n := rfl

/-- Folding commutes with iterating: the basis at level `n+1` is one fold of the
basis at level `n`. -/
theorem additiveFoldedBasis_lchTowerBasis : ∀ (n : ℕ) (β : ℕ → F),
    additiveFoldedBasis (lchTowerBasis β n) = lchTowerBasis β (n + 1) := by
  intro n
  induction n with
  | zero => intro β; rfl
  | succ n ih =>
      intro β
      have h1 : lchTowerBasis β (n + 1) = lchTowerBasis (additiveFoldedBasis β) n := rfl
      have h2 : lchTowerBasis β (n + 1 + 1)
          = lchTowerBasis (additiveFoldedBasis β) (n + 1) := rfl
      rw [h1, h2]
      exact ih (additiveFoldedBasis β)

/-- The additive pivot the verifier folds by at round `n`. -/
noncomputable def lchPivot (β : ℕ → F) (n : ℕ) : F := lchTowerBasis β n 0

/-- **The level-`n` word**: the evaluation function, on the level-`n` domain, of
the LCH packing (in the level-`n` basis) of the first `n` coefficient folds of
`p`. `n` variables consumed, `k` still to go. -/
noncomputable def lchLevelWord (β : ℕ → F) (p : F[X]) (r : ℕ → F) (n k : ℕ) :
    F → F :=
  fun y => (novelPack (lchTowerBasis β n) k
    (foldMleVariables n p (fun j : Fin n => r j.val))).eval y

/-- The descent starts at the committed word. -/
@[simp] theorem lchLevelWord_zero (β : ℕ → F) (p : F[X]) (r : ℕ → F) (k : ℕ) :
    lchLevelWord β p r 0 k = fun y => (novelPack β k p).eval y := rfl

/-- **Every level word is a codeword of its level's degree window** — the base
check is met by construction at every round, not by hypothesis. -/
theorem lchLevelWord_natDegree_lt (β : ℕ → F) (p : F[X]) (r : ℕ → F) (n k : ℕ) :
    (novelPack (lchTowerBasis β n) k
      (foldMleVariables n p (fun j : Fin n => r j.val))).natDegree < 2 ^ k :=
  novelPack_natDegree_lt k _ _

section Tower

variable [CharP F 2]

/-- ⭐ **ROUND CONSISTENCY — the char-2 tower-fold induction.** One `friFold` at
the round-`n` pivot and challenge carries the level-`n` word to the level-`n+1`
word, evaluated at the folded point. This is the additive counterpart of
`FoldingTower.word_eval_foldMleVariables`'s inductive step, and unlike it, it
does not run through an uninhabited structure. -/
theorem lchLevelWord_succ (β : ℕ → F) (p : F[X]) (r : ℕ → F) (n k : ℕ)
    (hpiv : lchPivot β n ≠ 0) (x : F) :
    friFold (lchPivot β n) (r n) (lchLevelWord β p r n (k + 1)) x
      = lchLevelWord β p r (n + 1) k (foldMap (lchPivot β n) x) := by
  have hfold : foldMleVariables (n + 1) p (fun j : Fin (n + 1) => r j.val)
      = mleCoefficientFold
          (foldMleVariables n p (fun j : Fin n => r j.val)) (r n) := by
    rw [foldMleVariables_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
  unfold lchLevelWord lchPivot
  rw [novelPack_friFold (lchTowerBasis β n) hpiv k _ (r n) x,
    additiveFoldedBasis_lchTowerBasis n β, hfold]

end Tower

/-- ⭐ **THE TERMINAL IDENTITY, char-2.** After `m` rounds the word is the
CONSTANT `mle (tableOfPoly m p) r` — for **every** `p` in the degree window, not
only the honest packing. `tableOfPoly` is total, so "the terminal constant is the
multilinear of nothing in particular" is impossible here exactly as it is in the
prime cone; the cited fact `coeff_zero_foldMleVariables_eq_mle` mentions no
`FoldingData` and so is not vacuous at characteristic two. -/
theorem lchLevelWord_terminal (β : ℕ → F) (p : F[X]) (m : ℕ)
    (hp : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) (r : ℕ → F) (y : F) :
    lchLevelWord β p r m 0 y = mle (tableOfPoly m p) (fun j : Fin m => r j.val) := by
  unfold lchLevelWord
  rw [novelPack_zero, eval_C, coeff_zero_foldMleVariables_eq_mle m p hp]

/-! ## 5. The packing is a bijection of the window — every codeword has a table

The prime cone's `mem_range_booleanMobiusPolynomial_iff` says the Möbius
transform is a bijection onto the degree-`< 2^m` window. Its char-2 companion is
that the LCH packing is a bijection OF that window. Surjectivity is
`Theory`'s `foldPoly_decompose` (the additive division algorithm) run backwards
through `parityInterleave`; injectivity is the uniqueness of that decomposition,
which is a parity-of-degree argument. -/

section Window

/-- Composing with the degree-2 fold polynomial kills nothing. -/
theorem comp_foldPoly_ne_zero {β : F} {A : F[X]} (hA : A ≠ 0) :
    A.comp (foldPoly β) ≠ 0 := by
  intro h
  rcases comp_eq_zero_iff.mp h with h0 | ⟨-, hq⟩
  · exact hA h0
  · have hd := congrArg natDegree hq
    rw [foldPoly_natDegree, natDegree_C] at hd
    exact absurd hd (by norm_num)

/-- **The additive decomposition is UNIQUE**: an even part composed with `q_β`
and `X` times an odd part composed with `q_β` cannot cancel — their degrees have
opposite parity. This is the char-2 replacement for "even and odd monomials do
not collide". -/
theorem comp_foldPoly_decomp_eq_zero {β : F} {A B : F[X]}
    (h : A.comp (foldPoly β) + X * B.comp (foldPoly β) = 0) : A = 0 ∧ B = 0 := by
  have hq2 : (foldPoly β).natDegree = 2 := foldPoly_natDegree β
  have hB : B = 0 := by
    by_contra hB0
    have hBc : B.comp (foldPoly β) ≠ 0 := comp_foldPoly_ne_zero hB0
    have hA0 : A ≠ 0 := by
      intro hA
      rw [hA, zero_comp, zero_add] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact X_ne_zero h1
      · exact hBc h1
    have heq : A.comp (foldPoly β) = -(X * B.comp (foldPoly β)) := by
      linear_combination h
    have hdA : (A.comp (foldPoly β)).natDegree = A.natDegree * 2 := by
      rw [natDegree_comp, hq2]
    have hdB : (X * B.comp (foldPoly β)).natDegree = 1 + B.natDegree * 2 := by
      rw [natDegree_mul X_ne_zero hBc, natDegree_X, natDegree_comp, hq2]
    have hcon := congrArg natDegree heq
    rw [hdA, natDegree_neg, hdB] at hcon
    omega
  refine ⟨?_, hB⟩
  rw [hB, zero_comp, mul_zero, add_zero] at h
  by_contra hA0
  exact comp_foldPoly_ne_zero hA0 h

/-! ### The packing is injective and surjective on the window -/

theorem novelPack_sub : ∀ (m : ℕ) (β : ℕ → F) (p q : F[X]),
    novelPack β m (p - q) = novelPack β m p - novelPack β m q := by
  intro m
  induction m with
  | zero => intro β p q; simp
  | succ m ih =>
      intro β p q
      rw [novelPack_succ, novelPack_succ, novelPack_succ, evenPart_sub_terminal,
        oddPart_sub_terminal, ih, ih, sub_comp, sub_comp]
      ring

/-- The packing sees exactly the first `2^m` coefficients, and sees them all: if
the packing vanishes, so does every coefficient inside the window. -/
theorem novelPack_eq_zero : ∀ (m : ℕ) (β : ℕ → F) (p : F[X]),
    novelPack β m p = 0 → ∀ i, i < 2 ^ m → p.coeff i = 0 := by
  intro m
  induction m with
  | zero =>
      intro β p h i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using C_eq_zero.mp (by simpa using h)
  | succ m ih =>
      intro β p h i hi
      rw [novelPack_succ] at h
      obtain ⟨hA, hB⟩ := comp_foldPoly_decomp_eq_zero h
      have hE := ih (additiveFoldedBasis β) (evenPart p) hA
      have hO := ih (additiveFoldedBasis β) (oddPart p) hB
      rw [pow_succ] at hi
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk
        rw [← coeff_evenPart_terminal]
        exact hE k (by omega)
      · subst hk
        rw [← coeff_oddPart_terminal]
        exact hO k (by omega)

/-- ⭐ **THE PACKING IS INJECTIVE ON THE WINDOW.** Two coefficient vectors with
the same LCH packing are equal — so the committed codeword determines the
multilinear coefficients, GIVEN the basis. (That last clause is not decoration:
`keystone_basis_ambiguity` below shows it fails across two bases of the same
domain.) -/
theorem novelPack_injective_of_natDegree_lt {m : ℕ} {β : ℕ → F} {p q : F[X]}
    (hp : p.natDegree < 2 ^ m) (hq : q.natDegree < 2 ^ m)
    (h : novelPack β m p = novelPack β m q) : p = q := by
  have hz : novelPack β m (p - q) = 0 := by rw [novelPack_sub, h, sub_self]
  have hcoeff := novelPack_eq_zero m β (p - q) hz
  ext i
  rcases lt_or_ge i (2 ^ m) with hi | hi
  · have hi' := hcoeff i hi
    rw [coeff_sub, sub_eq_zero] at hi'
    exact hi'
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hi),
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq hi)]

/-- ⭐ **THE PACKING IS SURJECTIVE ONTO THE WINDOW.** Every codeword of the
level-`m` degree window is the LCH packing of some coefficient vector — so there
is no committed word "outside the basis". The engine is `Theory`'s
`foldPoly_decompose` (the additive division algorithm) run backwards through
`parityInterleave`. -/
theorem novelPack_surjective_on_window : ∀ (m : ℕ) (β : ℕ → F) (P : F[X]),
    P.natDegree < 2 ^ m → ∃ p : F[X], p.natDegree < 2 ^ m ∧ novelPack β m p = P := by
  intro m
  induction m with
  | zero =>
      intro β P hP
      refine ⟨P, hP, ?_⟩
      rw [novelPack_zero]
      exact (Polynomial.eq_C_of_natDegree_eq_zero (by omega)).symm
  | succ m ih =>
      intro β P hP
      have hp2 : 0 < 2 ^ m := Nat.two_pow_pos m
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      obtain ⟨P₀, P₁, h₀, h₁, hdec⟩ :=
        foldPoly_decompose (β 0) (2 ^ m - 1) P (by omega)
      obtain ⟨p₀, hp₀, hP₀⟩ := ih (additiveFoldedBasis β) P₀ (by omega)
      obtain ⟨p₁, hp₁, hP₁⟩ := ih (additiveFoldedBasis β) P₁ (by omega)
      refine ⟨parityInterleave p₀ p₁, ?_, ?_⟩
      · have he : (Polynomial.expand F 2 p₀).natDegree = p₀.natDegree * 2 :=
          Polynomial.natDegree_expand 2 p₀
        have ho : (X * Polynomial.expand F 2 p₁).natDegree ≤ 1 + p₁.natDegree * 2 := by
          refine le_trans natDegree_mul_le ?_
          rw [natDegree_X, Polynomial.natDegree_expand]
        have hsum := natDegree_add_le (Polynomial.expand F 2 p₀)
          (X * Polynomial.expand F 2 p₁)
        rw [parityInterleave]
        omega
      · rw [novelPack_succ, evenPart_parityInterleave, oddPart_parityInterleave,
          hP₀, hP₁, ← hdec]

end Window

/-! ## 6. Every committed codeword has a definite Boolean table

The composite `table ↦ novelPack β m (booleanMobiusPolynomial m table)` is a
bijection from Boolean tables onto the level-`m` window: the Möbius half is the
prime cone's `mem_range_booleanMobiusPolynomial_iff` (cited verbatim — it is a
statement about coefficient vectors, so characteristic two changes nothing), and
the packing half is §5. So "the terminal constant is the multilinear extension
of nothing in particular" is impossible in characteristic two for exactly the
reason it is impossible in the prime case. -/

theorem natDegree_lt_of_degree_lt {p : F[X]} {m : ℕ}
    (h : p.degree < ((2 ^ m : ℕ) : WithBot ℕ)) : p.natDegree < 2 ^ m := by
  by_cases hp0 : p = 0
  · subst hp0; simp
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr h

theorem degree_lt_of_natDegree_lt {p : F[X]} {m : ℕ} (h : p.natDegree < 2 ^ m) :
    p.degree < ((2 ^ m : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h)

/-- ⭐ **THE COMMITMENT DETERMINES A TABLE, AND ONLY ONE.** Every codeword of the
level-`m` window is the LCH packing of the Möbius packing of exactly one Boolean
table. This is the char-2 counterpart of `mem_range_booleanMobiusPolynomial_iff`
composed with `basefold_terminal_word_eq`'s totality clause. -/
theorem exists_unique_table_novelPack (β : ℕ → F) (m : ℕ) (P : F[X])
    (hP : P.natDegree < 2 ^ m) :
    ∃! table : (Fin m → Bool) → F,
      novelPack β m (booleanMobiusPolynomial m table) = P := by
  obtain ⟨p, hp, hpP⟩ := novelPack_surjective_on_window m β P hP
  refine ⟨tableOfPoly m p, ?_, ?_⟩
  · show novelPack β m (booleanMobiusPolynomial m (tableOfPoly m p)) = P
    rw [booleanMobiusPolynomial_tableOfPoly m p (degree_lt_of_natDegree_lt hp)]
    exact hpP
  · intro t ht
    have h1 : novelPack β m (booleanMobiusPolynomial m t) = novelPack β m p := by
      rw [ht, hpP]
    have h2 : booleanMobiusPolynomial m t = p :=
      novelPack_injective_of_natDegree_lt
        (natDegree_lt_of_degree_lt (degree_booleanMobiusPolynomial_lt m t)) hp h1
    rw [← h2, tableOfPoly_booleanMobiusPolynomial]

/-- ⭐ **THE HEADLINE: the additive BaseFold descent, both halves.** For every
codeword `P` of the level-`m` window there is a unique Boolean table whose LCH
commitment is `P`, and (i) the descent STARTS at `P`'s evaluation word, (ii)
every round is one `friFold` at that round's pivot, (iii) after `m` rounds the
word is the CONSTANT `mle table r`. The char-2 counterpart of
`basefold_opening_complete`, assembled from `lchLevelWord_succ` and
`lchLevelWord_terminal`. -/
theorem lch_opening_complete [CharP F 2] (β : ℕ → F) (m : ℕ)
    (hpiv : ∀ n, n < m → lchPivot β n ≠ 0)
    (P : F[X]) (hP : P.natDegree < 2 ^ m) (r : ℕ → F) :
    ∃ p : F[X], p.natDegree < 2 ^ m ∧
      lchLevelWord β p r 0 m = (fun y => P.eval y) ∧
      (∀ n, n < m → ∀ k : ℕ, ∀ x : F,
        friFold (lchPivot β n) (r n) (lchLevelWord β p r n (k + 1)) x
          = lchLevelWord β p r (n + 1) k (foldMap (lchPivot β n) x)) ∧
      (∀ y : F, lchLevelWord β p r m 0 y
        = mle (tableOfPoly m p) (fun j : Fin m => r j.val)) := by
  obtain ⟨p, hp, hpP⟩ := novelPack_surjective_on_window m β P hP
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · funext y; rw [lchLevelWord_zero, hpP]
  · intro n hn k x; exact lchLevelWord_succ β p r n k (hpiv n hn) x
  · intro y; exact lchLevelWord_terminal β p m (degree_lt_of_natDegree_lt hp) r y

/-! ## 7. Teeth

The prime cone's two-commitment ambiguity ports, and its resolution ports with
it: the terminal is `mle (tableOfPoly m p) r` for the SAME total `tableOfPoly`
in both worlds, so two words that terminate differently are two honest claims
about different tables, never one word with two values.

⚑ Characteristic two then adds one the prime case does not have. -/

/-- A challenge stream carrying a cube corner: `r ↾ Fin m` is `cubePt b`. -/
def cornerStream {m : ℕ} (b : Fin m → Bool) : ℕ → F :=
  fun n => if h : n < m then ofBool (b ⟨n, h⟩) else 0

@[simp] theorem cornerStream_restrict {m : ℕ} (b : Fin m → Bool) :
    (fun j : Fin m => (cornerStream (F := F) b) j.val) = cubePt b := by
  funext j
  rw [cornerStream, dif_pos j.isLt, cubePt, Fin.eta]

/-- ⭐ **THE AMBIGUITY, GENERALLY.** Two window codewords whose tables differ
terminate at different constants — on the SAME challenge stream, at ANY points of
their terminal domains, and under any two bases. Acceptance of the descent
therefore does not pin the value; only the table does. -/
theorem terminal_ne_of_tableOfPoly_ne (β β' : ℕ → F) (m : ℕ) (p q : F[X])
    (hp : p.natDegree < 2 ^ m) (hq : q.natDegree < 2 ^ m)
    (h : tableOfPoly m p ≠ tableOfPoly m q) :
    ∃ r : ℕ → F, ∀ y y' : F,
      lchLevelWord β p r m 0 y ≠ lchLevelWord β' q r m 0 y' := by
  obtain ⟨b, hb⟩ : ∃ b, tableOfPoly m p b ≠ tableOfPoly m q b := by
    by_contra hcon
    exact h (funext fun b => not_not.mp (fun hne => hcon ⟨b, hne⟩))
  refine ⟨cornerStream b, fun y y' => ?_⟩
  rw [lchLevelWord_terminal β p m (degree_lt_of_natDegree_lt hp),
    lchLevelWord_terminal β' q m (degree_lt_of_natDegree_lt hq),
    cornerStream_restrict, mle_agrees, mle_agrees]
  exact hb

/-! ## 8. Keystones at GF(16): the descent fires, and the basis ambiguity fires

`binaryTower 2 = GF(16)`, domain `W = span_{GF(2)}{1, x₁}` — four points, the
same domain `Selvage/AdditiveProximity.lean`'s proximity keystones run on. These
also discharge the non-vacuity obligation: every cited lemma from the prime cone
is used here at an actual characteristic-two field and produces concrete
DISTINCT values. -/

namespace AdditiveBaseFoldKeystone

open Minidregg.Theory

/-- `1 + x₁ ≠ 0` in GF(16), i.e. `x₁ ≠ 1` in characteristic two. -/
theorem one_add_fpGen_ne_zero : (1 : binaryTower 2) + fpGen 1 ≠ 0 := fun h =>
  fpGen_ne_one 1 (by linear_combination h - binaryTower_two_eq_zero 2)

/-- ⚑ **The OTHER ordering of the SAME GF(2)-basis**: β' = (x₁, 1) against
`keystoneBeta`'s (1, x₁). Same span, same evaluation domain, same Merkle leaves —
different novelpoly basis. -/
noncomputable def keystoneBetaSwap : ℕ → binaryTower 2
  | 0 => fpGen 1
  | 1 => 1
  | _ + 2 => 0

@[simp] theorem keystoneBetaSwap_zero : keystoneBetaSwap 0 = fpGen 1 := rfl

@[simp] theorem keystoneBetaSwap_one : keystoneBetaSwap 1 = 1 := rfl

theorem keystoneBetaSwap_range :
    (Set.range fun j : Fin 2 => keystoneBetaSwap j)
      = Set.range fun j : Fin 2 => keystoneBeta j := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Fin.val_zero, Fin.val_one,
    keystoneBetaSwap_zero, keystoneBetaSwap_one, keystoneBeta_zero,
    keystoneBeta_one]
  exact or_comm

/-- ⭐ **THE TWO BASES SPAN THE SAME DOMAIN.** Whatever a Merkle root over the
evaluation points commits to, it is the same object for both. -/
theorem keystoneBetaSwap_additiveDomain :
    additiveDomain keystoneBetaSwap 2 = additiveDomain keystoneBeta 2 := by
  unfold additiveDomain
  rw [keystoneBetaSwap_range]

theorem keystoneBetaSwap_linearIndependent :
    LinearIndependent (ZMod 2) fun j : Fin 2 => keystoneBetaSwap j := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Fin.val_zero, Fin.val_one, keystoneBetaSwap_zero,
    keystoneBetaSwap_one] at hg
  have hcase : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have h2 : (2 : binaryTower 2) = 0 := binaryTower_two_eq_zero 2
  suffices h : g 0 = 0 ∧ g 1 = 0 by
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  rcases hcase (g 0) with h0 | h0 <;> rcases hcase (g 1) with h1 | h1 <;>
    rw [h0, h1] at hg <;>
    simp only [zero_smul, one_smul, add_zero, zero_add] at hg
  · exact ⟨h0, h1⟩
  · exact absurd hg one_ne_zero
  · exact absurd hg (fpGen_ne_zero 1)
  · exact absurd (by linear_combination hg - h2 : fpGen 1 = 1) (fpGen_ne_one 1)

/-! ### One codeword, two coefficient vectors -/

/-- The committed codeword: `Ŵ₁ = X² + X`, a genuine level-2 codeword on the
four-point domain. -/
noncomputable def sharedWord : (binaryTower 2)[X] := X ^ 2 + X

/-- Its coefficient vector in the basis (1, x₁): `(0, 0, 1, 0)`. -/
noncomputable def preA : (binaryTower 2)[X] := X ^ 2

/-- Its coefficient vector in the basis (x₁, 1): `(0, 1+x₁, 1, 0)`. -/
noncomputable def preB : (binaryTower 2)[X] := C (1 + fpGen 1) * X + X ^ 2

theorem preA_natDegree_lt : preA.natDegree < 2 ^ 2 := by
  rw [preA, natDegree_X_pow]
  norm_num

theorem preB_natDegree_lt : preB.natDegree < 2 ^ 2 := by
  have h := natDegree_add_le (C (1 + fpGen 1) * X) ((X : (binaryTower 2)[X]) ^ 2)
  have h1 : (C (1 + fpGen 1) * (X : (binaryTower 2)[X])).natDegree ≤ 1 := by
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X]
  rw [natDegree_X_pow] at h
  rw [preB]
  omega

theorem novelPack_preA : novelPack keystoneBeta 2 preA = sharedWord := by
  rw [novelPack_two, foldPoly, keystoneBeta_zero, sharedWord]
  simp only [preA, coeff_X_pow]
  norm_num

theorem novelPack_preB : novelPack keystoneBetaSwap 2 preB = sharedWord := by
  have hcc : (C (fpGen 1) : (binaryTower 2)[X]) + C (fpGen 1) = 0 := by
    rw [← map_add, show fpGen 1 + fpGen 1 = 0 from by
      linear_combination fpGen 1 * binaryTower_two_eq_zero 2, map_zero]
  have c0 : preB.coeff 0 = 0 := by simp [preB, coeff_X_pow, Polynomial.coeff_one]
  have c1 : preB.coeff 1 = 1 + fpGen 1 := by
    simp [preB, coeff_X_pow, Polynomial.coeff_one]
  have c2 : preB.coeff 2 = 1 := by simp [preB, coeff_X_pow, Polynomial.coeff_one]
  have c3 : preB.coeff 3 = 0 := by simp [preB, coeff_X_pow, Polynomial.coeff_one]
  rw [novelPack_two, foldPoly, keystoneBetaSwap_zero, sharedWord, c0, c1, c2, c3,
    map_add, map_one]
  simp only [map_zero, zero_mul, add_zero, zero_add, one_mul]
  linear_combination (X : (binaryTower 2)[X]) * hcc

theorem preA_ne_preB : preA ≠ preB := by
  intro h
  have hc := congrArg (fun q : (binaryTower 2)[X] => q.coeff 1) h
  simp only [preA, preB, coeff_add, coeff_C_mul, coeff_X_one, coeff_X_pow,
    mul_one] at hc
  norm_num at hc
  exact one_add_fpGen_ne_zero hc.symm

theorem tableOfPoly_preA_ne_preB : tableOfPoly 2 preA ≠ tableOfPoly 2 preB := by
  intro h
  refine preA_ne_preB ?_
  have hA : booleanMobiusPolynomial 2 (tableOfPoly 2 preA) = preA :=
    booleanMobiusPolynomial_tableOfPoly 2 preA
      (degree_lt_of_natDegree_lt preA_natDegree_lt)
  have hB : booleanMobiusPolynomial 2 (tableOfPoly 2 preB) = preB :=
    booleanMobiusPolynomial_tableOfPoly 2 preB
      (degree_lt_of_natDegree_lt preB_natDegree_lt)
  rw [← hA, h, hB]

/-! ### The pivots are genuine -/

theorem keystone_pivot_zero_ne_zero : lchPivot keystoneBeta 0 ≠ 0 := one_ne_zero

theorem keystone_pivot_one_ne_zero : lchPivot keystoneBeta 1 ≠ 0 := by
  have h := keystone_additive_tooth.2.1
  rw [keystone_subspaceVanishing_one] at h
  simp only [eval_add, eval_pow, eval_X] at h
  show foldMap (keystoneBeta 0) (keystoneBeta 1) ≠ 0
  rw [foldMap, keystoneBeta_zero, keystoneBeta_one, one_mul]
  exact h

theorem keystoneSwap_pivot_zero_ne_zero : lchPivot keystoneBetaSwap 0 ≠ 0 :=
  fpGen_ne_zero 1

theorem keystoneSwap_pivot_one_ne_zero : lchPivot keystoneBetaSwap 1 ≠ 0 := by
  show foldMap (keystoneBetaSwap 0) (keystoneBetaSwap 1) ≠ 0
  rw [foldMap, keystoneBetaSwap_zero, keystoneBetaSwap_one, one_pow, mul_one]
  exact one_add_fpGen_ne_zero

theorem keystone_pivots : ∀ n, n < 2 → lchPivot keystoneBeta n ≠ 0 := by
  intro n hn
  interval_cases n
  · exact keystone_pivot_zero_ne_zero
  · exact keystone_pivot_one_ne_zero

theorem keystoneSwap_pivots : ∀ n, n < 2 → lchPivot keystoneBetaSwap n ≠ 0 := by
  intro n hn
  interval_cases n
  · exact keystoneSwap_pivot_zero_ne_zero
  · exact keystoneSwap_pivot_one_ne_zero

/-! ### The keystones -/

/-- **FIRES (satisfiability): the additive descent runs at GF(16).** The shared
codeword is opened by a two-round additive BaseFold descent whose every round is
one `friFold` at a genuine nonzero pivot and whose terminal is a constant. -/
theorem keystone_descent_runs (r : ℕ → binaryTower 2) :
    ∃ p : (binaryTower 2)[X], p.natDegree < 2 ^ 2 ∧
      lchLevelWord keystoneBeta p r 0 2 = (fun y => sharedWord.eval y) ∧
      (∀ n, n < 2 → ∀ k : ℕ, ∀ x : binaryTower 2,
        friFold (lchPivot keystoneBeta n) (r n)
            (lchLevelWord keystoneBeta p r n (k + 1)) x
          = lchLevelWord keystoneBeta p r (n + 1) k
              (foldMap (lchPivot keystoneBeta n) x)) ∧
      (∀ y : binaryTower 2, lchLevelWord keystoneBeta p r 2 0 y
        = mle (tableOfPoly 2 p) (fun j : Fin 2 => r j.val)) :=
  lch_opening_complete keystoneBeta 2 keystone_pivots sharedWord
    (by rw [← novelPack_preA]; exact novelPack_natDegree_lt 2 _ _) r

/-- ⭐⭐ **THE CHAR-2-SPECIFIC AMBIGUITY — one codeword, one domain, two tables.**

`X² + X` is a level-2 codeword on the four-point GF(16) domain
`W = span{1, x₁}`. Under the ordered basis (1, x₁) it is the LCH commitment of
`preA`; under (x₁, 1) — the SAME basis in the other order, hence the SAME
`additiveDomain`, hence the SAME evaluation points and the SAME Merkle leaves —
it is the LCH commitment of `preB`, and the two decode to DIFFERENT Boolean
tables.

This has no multiplicative counterpart: there the packing basis is the monomial
basis, which the domain does not get a say in. **An additive-FRI transcript that
binds the domain but not the ORDERED BASIS does not determine the committed
multilinear.** Nothing in this tree binds it today. -/
theorem keystone_basis_ambiguity :
    novelPack keystoneBeta 2 preA = novelPack keystoneBetaSwap 2 preB
      ∧ additiveDomain keystoneBetaSwap 2 = additiveDomain keystoneBeta 2
      ∧ LinearIndependent (ZMod 2) (fun j : Fin 2 => keystoneBeta j)
      ∧ LinearIndependent (ZMod 2) (fun j : Fin 2 => keystoneBetaSwap j)
      ∧ tableOfPoly 2 preA ≠ tableOfPoly 2 preB :=
  ⟨by rw [novelPack_preA, novelPack_preB], keystoneBetaSwap_additiveDomain,
    keystoneBeta_linearIndependent, keystoneBetaSwap_linearIndependent,
    tableOfPoly_preA_ne_preB⟩

/-- ⭐ **AND IT REACHES THE TERMINAL.** The two readings of the one codeword
terminate at DIFFERENT constants on a common challenge stream — so the ambiguity
is not a bookkeeping artefact of the packing, it is a value the verifier would
accept two answers for. -/
theorem keystone_basis_ambiguity_terminal :
    ∃ r : ℕ → binaryTower 2, ∀ y y' : binaryTower 2,
      lchLevelWord keystoneBeta preA r 2 0 y
        ≠ lchLevelWord keystoneBetaSwap preB r 2 0 y' :=
  terminal_ne_of_tableOfPoly_ne keystoneBeta keystoneBetaSwap 2 preA preB
    preA_natDegree_lt preB_natDegree_lt tableOfPoly_preA_ne_preB

end AdditiveBaseFoldKeystone

/-- info: 'Minidregg.Selvage.friFold_eval_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friFold_eval_decomp
/-- info: 'Minidregg.Selvage.novelPack_friFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_friFold
/-- info: 'Minidregg.Selvage.novelPack_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_natDegree_lt
/-- info: 'Minidregg.Selvage.lchLevelWord_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lchLevelWord_succ
/-- info: 'Minidregg.Selvage.lchLevelWord_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lchLevelWord_terminal
/-- info: 'Minidregg.Selvage.novelPack_injective_of_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_injective_of_natDegree_lt
/-- info: 'Minidregg.Selvage.novelPack_surjective_on_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms novelPack_surjective_on_window
/-- info: 'Minidregg.Selvage.exists_unique_table_novelPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_unique_table_novelPack
/-- info: 'Minidregg.Selvage.lch_opening_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lch_opening_complete
/-- info: 'Minidregg.Selvage.terminal_ne_of_tableOfPoly_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms terminal_ne_of_tableOfPoly_ne
/-- info: 'Minidregg.Selvage.AdditiveBaseFoldKeystone.keystone_descent_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdditiveBaseFoldKeystone.keystone_descent_runs
/-- info: 'Minidregg.Selvage.AdditiveBaseFoldKeystone.keystone_basis_ambiguity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdditiveBaseFoldKeystone.keystone_basis_ambiguity
/-- info: 'Minidregg.Selvage.AdditiveBaseFoldKeystone.keystone_basis_ambiguity_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdditiveBaseFoldKeystone.keystone_basis_ambiguity_terminal

end Minidregg.Selvage


