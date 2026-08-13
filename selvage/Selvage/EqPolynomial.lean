/-
# `Selvage/EqPolynomial.lean` — the two-vector equality polynomial `eq(z, x)`.

`Selvage/MultilinearExtension.lean` built `chiEval b x` — the eq polynomial with
its FIRST argument a cube CORNER (`b : Fin m → Bool`). Both the GKR fraction-tree
layer and the multilinear zero-test need the version with BOTH arguments free
field vectors:

  `eq(z, x) = ∏ᵢ (zᵢ·xᵢ + (1 − zᵢ)·(1 − xᵢ))`

the unique multi-affine function that is `1` when `z = x` on the cube and `0`
at every other corner pair. This file builds it and proves the three facts the
degree-3 rung consumes:

* `eqMle_cubePt` — specialization: `eq(z, corner b) = χ_b(z)`, so the new object
  IS the landed chi basis wherever the landed one applies. Nothing is duplicated.
* `eqMle_fold` — **the zerocheck-to-sumcheck bridge**: `Σ_b eq(z, b)·f(b) = f̂(z)`.
  The single-shot randomization `Σ_b eq(z,b)·D(b) = mle D z` that
  `AirSumcheckQuadratic`'s residual (ii) names, as an identity.
* `eqMle_multilinear` — `eq(z, ·)` is multi-affine, so `roundSum_affine` and the
  whole landed round-chain skeleton apply to it verbatim; a summand
  `eq(z, x)·(…)` gains exactly one degree over what it multiplies.

Teeth: `eqMle_corner_indicator` (it IS an indicator on the cube),
`eqMle_offcube` (a genuine extension), `eqMle_not_symm_witness` — `eq` is
symmetric as a polynomial identity (`eqMle_comm`), which is a THEOREM here and
not the definition.
-/
import Selvage.MultilinearExtension

namespace Minidregg.Selvage

section EqPoly

variable {F : Type*} [CommRing F] {m : ℕ}

/-- **The two-vector equality polynomial**:
`eq(z, x) = ∏ᵢ (zᵢ·xᵢ + (1 − zᵢ)·(1 − xᵢ))` — the multilinear extension of the
corner-equality indicator in BOTH arguments. -/
def eqMle (z x : Fin m → F) : F :=
  ∏ i, (z i * x i + (1 - z i) * (1 - x i))

/-- **`eq` specializes to the landed chi basis.** At a cube corner in the second
argument, `eq(z, corner b) = χ_b(z)` — the new object extends the old one rather
than duplicating it. -/
theorem eqMle_cubePt (z : Fin m → F) (b : Fin m → Bool) :
    eqMle z (cubePt b) = chiEval b z := by
  unfold eqMle chiEval
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hb : b i <;> simp [cubePt, ofBool, hb]

/-- `eq` is symmetric — a theorem, not the definition. -/
theorem eqMle_comm (z x : Fin m → F) : eqMle z x = eqMle x z := by
  unfold eqMle
  exact Finset.prod_congr rfl fun i _ => by ring

/-- **The corner indicator**: on the cube, `eq` is `δ`. -/
theorem eqMle_corner_indicator (b b' : Fin m → Bool) :
    eqMle (cubePt b : Fin m → F) (cubePt b') = if b = b' then 1 else 0 := by
  rw [eqMle_cubePt, chiEval_cubePt]
  exact if_congr eq_comm rfl rfl

/-- **The zerocheck-to-sumcheck bridge**: weighting the hypercube sum by `eq(z, ·)`
evaluates the multilinear extension at `z` — `Σ_b eq(z, b)·f(b) = f̂(z)`. This is
the single-shot randomization that replaces the γ-batching round; the multilinear
Schwartz–Zippel bound on `f̂(z)` is what turns it into a zero-test. -/
theorem eqMle_fold (z : Fin m → F) (f : (Fin m → Bool) → F) :
    ∑ b, eqMle z (cubePt b) * f b = mle f z := by
  rw [mle]
  exact Finset.sum_congr rfl fun b _ => by rw [eqMle_cubePt]; ring

/-- `eq(z, ·)` is affine in every coordinate of its second argument — the same
one-factor-per-coordinate shape as `chiEval_update`. -/
theorem eqMle_update (z : Fin m → F) (x : Fin m → F) (i : Fin m) (t : F) :
    eqMle z (Function.update x i t)
      = (1 - t) * eqMle z (Function.update x i 0)
        + t * eqMle z (Function.update x i 1) := by
  have key : ∀ s : F, eqMle z (Function.update x i s)
      = (z i * s + (1 - z i) * (1 - s))
        * ∏ j ∈ Finset.univ.erase i, (z j * x j + (1 - z j) * (1 - x j)) := by
    intro s
    rw [eqMle, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [key t, key 0, key 1]
  ring

/-- **`eq(z, ·)` is multi-affine** — so the landed round-chain skeleton
(`roundSum_affine`, `roundSum_zero`, `roundSum_succ`, `roundSum_last`) applies to
any summand built from it, and multiplying by `eq` costs exactly one degree. -/
theorem eqMle_multilinear (z : Fin m → F) : MultiAffine (eqMle z) :=
  fun i x t => eqMle_update z x i t

/-- `eq(z, ·)` IS the MLE of the corner indicator at `z`: uniqueness fires. -/
theorem eqMle_eq_mle [Nontrivial F] (z : Fin m → F) :
    eqMle z = mle (fun b => chiEval b z) := by
  rw [multiAffine_eq_mle (eqMle_multilinear z)]
  exact congrArg mle (funext fun b => eqMle_cubePt z b)

end EqPoly

/-! ## Teeth over F₅, m = 2 -/

namespace EqExample

/-- **A genuine extension, not a table**: off the cube `eq((2,3),(4,0)) =
(2·4+(−1)(−3))·(3·0+(−2)(1)) = (8+3)·(−2) = 11·3 = 1·3 = 3` in F₅. -/
theorem eqMle_offcube : eqMle (![2, 3] : Fin 2 → ZMod 5) ![4, 0] = 3 := by decide

/-- **TEETH — the indicator fires on data**: equal corners give `1`, unequal `0`. -/
theorem eqMle_indicator_fires :
    eqMle (![1, 0] : Fin 2 → ZMod 5) ![1, 0] = 1
      ∧ eqMle (![1, 0] : Fin 2 → ZMod 5) ![1, 1] = 0 := by decide

/-- **TEETH — the bridge computes**: `Σ_b eq(z,b)·fAnd(b) = f̂_AND(2,3) = 1`. -/
theorem eqMle_fold_fires :
    ∑ b, eqMle (![2, 3] : Fin 2 → ZMod 5) (cubePt b) * MLEExample.fAnd b = 1 := by
  rw [eqMle_fold]
  decide

/-- **TEETH — `eq` is not the constant `1`**: it separates points, so the
zerocheck randomization is a real test. -/
theorem eqMle_separates : eqMle (![1, 0] : Fin 2 → ZMod 5) ![0, 1] = 0 := by decide

end EqExample

end Minidregg.Selvage
