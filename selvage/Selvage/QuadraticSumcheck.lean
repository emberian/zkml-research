/-
# Selvage.QuadraticSumcheck — the reusable degree-2 product sumcheck

The generic quadratic engine belongs to Selvage's proof compiler, not to one AIR
consumer. It realizes the sumcheck for

  Σ_b (A b * B b - C b)

with actual degree-two round polynomials, prefix measurability, perfect completeness,
the factored terminal check, and the adaptive m*2/|F| soundness bound. AIR multiplication
gates and BaseFold's table-times-equality braid consume this same object.
-/
import Selvage.MultilinearExtension

namespace Minidregg.Selvage

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. The quadratic round engine — degree-2 claims `Σ_b (Â·B̂ − Ĉ)(b)`, honest side BUILT.

`Selvage/MultilinearExtension` built the degree-1 engine (`roundPoly`/`mleHonest`) for a single
MLE's hypercube sum. The mul-gate face needs the PRODUCT of two MLEs minus a third: still
prefix-measurable, still boolean-sum consistent (those are pure sum-splitting, cited), but
degree 2 per round variable — the round polynomial gains the cross term `ΔÂ·ΔB̂`. -/

section QuadEngine

variable {m : ℕ}

/-- The degree-2 summand's extension: `p(x) = Â(x)·B̂(x) − Ĉ(x)` — the product of two
multilinear extensions minus a third. On the cube it reads `A b·B b − C b` (`mle_agrees`);
off the cube it is the object whose round partial sums the quadratic sumcheck walks. -/
def prodDiff (A B C : (Fin m → Bool) → F) : (Fin m → F) → F :=
  fun x => mle A x * mle B x - mle C x

omit [Fintype F] [DecidableEq F] in
/-- The sum-claim on the cube: `Σ_b p(corner b) = Σ_b (A b·B b − C b)` — the extension's
hypercube sum is the table claim (`mle_agrees`, three times). -/
theorem prodDiff_cube_sum (A B C : (Fin m → Bool) → F) :
    ∑ b, prodDiff A B C (cubePt b) = ∑ b, (A b * B b - C b) :=
  Finset.sum_congr rfl fun b _ => by
    simp only [prodDiff, mle_agrees]

omit [Fintype F] [DecidableEq F] in
/-- **The line restriction is quadratic, explicitly.** On every axis-`i` line the product
minus the third term is the two-point interpolation PLUS the cross term `t(t−1)·ΔÂ·ΔB̂`:
multilinearity of all three extensions (`mle_multilinear`) and `ring`. This is the whole
reason the round polynomial has degree 2, in one identity. -/
theorem prodDiff_line (A B C : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) (t : F) :
    prodDiff A B C (Function.update x i t)
      = (1 - t) * prodDiff A B C (Function.update x i 0)
        + t * prodDiff A B C (Function.update x i 1)
        + (t * t - t) *
          ((mle A (Function.update x i 1) - mle A (Function.update x i 0))
            * (mle B (Function.update x i 1) - mle B (Function.update x i 0))) := by
  have hA := mle_multilinear A i x t
  have hB := mle_multilinear B i x t
  have hC := mle_multilinear C i x t
  simp only [prodDiff]
  rw [hA, hB, hC]
  ring

/-- **The cross term of round `i`**: the suffix-cube sum of `ΔÂ·ΔB̂` along coordinate `i` —
the leading (degree-2) coefficient of the round polynomial. -/
def quadCross (A B : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) : F :=
  ∑ b : SuffixCube m (i.val + 1),
    ((mle A (Function.update (glue r (i.val + 1) b) i 1)
        - mle A (Function.update (glue r (i.val + 1) b) i 0))
      * (mle B (Function.update (glue r (i.val + 1) b) i 1)
          - mle B (Function.update (glue r (i.val + 1) b) i 0)))

omit [Fintype F] [DecidableEq F] in
/-- **The round partial sum is quadratic in the running variable** — `prodDiff_line`, summed
over the suffix cube (`glue_update` rides the running coordinate outside the glue). -/
theorem roundSum_prodDiff (A B C : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) (t : F) :
    roundSum (prodDiff A B C) r i t
      = (1 - t) * roundSum (prodDiff A B C) r i 0
        + t * roundSum (prodDiff A B C) r i 1
        + (t * t - t) * quadCross A B r i := by
  simp only [roundSum, quadCross, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [glue_update t, glue_update 0, glue_update 1]
  exact prodDiff_line A B C i (glue r (i.val + 1) b) t

/-- The round polynomial of the quadratic engine, as an actual `Polynomial F`:
`ct·X² + (g(1) − g(0) − ct)·X + g(0)` with `ct` the cross term — degree ≤ 2 by shape,
evaluating to `roundSum` everywhere. -/
noncomputable def quadRoundPoly (A B C : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) :
    Polynomial F :=
  Polynomial.C (quadCross A B r i) * X ^ 2
    + Polynomial.C (roundSum (prodDiff A B C) r i 1 - roundSum (prodDiff A B C) r i 0
        - quadCross A B r i) * X
    + Polynomial.C (roundSum (prodDiff A B C) r i 0)

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial IS the round partial sum, at every point (no affineness hypothesis:
the quadratic identity `roundSum_prodDiff` carries it). -/
theorem quadRoundPoly_eval (A B C : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) (t : F) :
    (quadRoundPoly A B C r i).eval t = roundSum (prodDiff A B C) r i t := by
  rw [roundSum_prodDiff]
  simp only [quadRoundPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial has degree ≤ 2 — the `d = 2` the sumcheck bound consumes. -/
theorem quadRoundPoly_degree (A B C : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) :
    (quadRoundPoly A B C r i).degree < ((2 + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_quadratic_le (by decide)

/-- **The honest quadratic prover** — the mul-gate face's realizer. Round `i` sends the
degree-≤2 partial-sum polynomial of `Â·B̂ − Ĉ`; the challenge stream is read only below `i`
(constant `0` junk past the last round, never consulted). -/
noncomputable def quadHonest (A B C : (Fin m → Bool) → F) (χ : ℕ → F) (i : ℕ) :
    Polynomial F :=
  if h : i < m then quadRoundPoly A B C (fun j : Fin m => χ j.val) ⟨i, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
/-- The cross term reads the challenge tuple only strictly below `i` (the glue pins
coordinates `> i` to the corner and `i` to the explicit update). -/
theorem quadCross_congr_prefix {A B : (Fin m → Bool) → F} {i : Fin m}
    {r r' : Fin m → F} (h : ∀ j : Fin m, j.val < i.val → r j = r' j) :
    quadCross A B r i = quadCross A B r' i := by
  unfold quadCross
  refine Finset.sum_congr rfl fun b _ => ?_
  have hg : ∀ t : F,
      Function.update (glue r (i.val + 1) b) i t
        = Function.update (glue r' (i.val + 1) b) i t := by
    intro t
    funext j
    rcases eq_or_ne j i with rfl | hne
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hne, Function.update_of_ne hne]
      simp only [glue_apply]
      by_cases hj : i.val + 1 ≤ j.val
      · rw [dif_pos hj, dif_pos hj]
      · rw [dif_neg hj, dif_neg hj]
        have hv : j.val ≠ i.val := fun hv => hne (Fin.ext hv)
        exact h j (by omega)
  rw [hg 0, hg 1]

omit [Fintype F] [DecidableEq F] in
/-- The honest quadratic family is prefix-measurable: round `i`'s message depends on the
challenge stream only below `i` (`roundSum_congr_prefix` + `quadCross_congr_prefix`). -/
theorem quadHonest_prefixMeasurable (A B C : (Fin m → Bool) → F) :
    PrefixMeasurable (quadHonest A B C) := by
  intro χ χ' i hpre
  unfold quadHonest
  by_cases h : i < m
  · rw [dif_pos h, dif_pos h]
    unfold quadRoundPoly
    rw [roundSum_congr_prefix (i := ⟨i, h⟩) (fun j hj => hpre j.val hj) 0,
      roundSum_congr_prefix (i := ⟨i, h⟩) (fun j hj => hpre j.val hj) 1,
      quadCross_congr_prefix (i := ⟨i, h⟩) (fun j hj => hpre j.val hj)]
  · rw [dif_neg h, dif_neg h]

omit [Fintype F] [DecidableEq F] in
/-- The honest quadratic family's degree bound: `d = 2`, every round. -/
theorem quadHonest_degree (A B C : (Fin m → Bool) → F) (χ : ℕ → F) (i : ℕ) (hi : i < m) :
    (quadHonest A B C χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ) := by
  rw [quadHonest, dif_pos hi]
  exact quadRoundPoly_degree _ _ _ _ _

omit [Fintype F] [DecidableEq F] in
/-- **Boolean-sum consistency of the quadratic honest family**, along the truth chain
anchored at the table claim `Σ_b (A b·B b − C b)`: round 0's check target is the claimed
total (`roundSum_zero` + `prodDiff_cube_sum`), every later round's target is the previous
round polynomial folded at the challenge (`roundSum_succ`) — the landed sum-splitting,
cited, not re-derived. -/
theorem quadHonest_boolean_sum (A B C : (Fin m → Bool) → F) (r : Fin m → F) :
    ∀ i, i < m →
      (quadHonest A B C (chalOf r) i).eval 0 + (quadHonest A B C (chalOf r) i).eval 1
        = scChain (∑ b, (A b * B b - C b)) (quadHonest A B C (chalOf r)) (chalOf r) i := by
  intro i hi
  rw [quadHonest, dif_pos hi, chalOf_restrict, quadRoundPoly_eval, quadRoundPoly_eval]
  cases i with
  | zero =>
    show _ = ∑ b, (A b * B b - C b)
    rw [roundSum_zero hi (prodDiff A B C) r, prodDiff_cube_sum]
  | succ n =>
    show _ = (quadHonest A B C (chalOf r) n).eval (chalOf r n)
    have hn : n < m := Nat.lt_of_succ_lt hi
    rw [quadHonest, dif_pos hn, chalOf_restrict, quadRoundPoly_eval,
      chalOf_coe r ⟨n, hn⟩]
    exact roundSum_succ hi (prodDiff A B C) r

omit [Fintype F] [DecidableEq F] in
/-- **The final oracle check, FACTORED**: after all `m` rounds the honest truth chain's value
is `Â(r)·B̂(r) − Ĉ(r)` — the product of the two MLE openings minus the third, exactly the
factored terminal comparison the degree-1 engine could not provide (the MLE of a product ≠
the product of MLEs; the quadratic rounds make the factored check the honest one). -/
theorem scChain_quadHonest_final (A B C : (Fin m → Bool) → F) (r : Fin m → F) :
    scChain (∑ b, (A b * B b - C b)) (quadHonest A B C (chalOf r)) (chalOf r) m
      = mle A r * mle B r - mle C r := by
  cases m with
  | zero =>
    show ∑ b, (A b * B b - C b) = mle A r * mle B r - mle C r
    have key : ∀ f : (Fin 0 → Bool) → F, mle f r = f default := by
      intro f
      rw [mle,
        Fintype.sum_eq_single default fun b hb =>
          absurd (Subsingleton.elim b default) hb,
        chiEval, Fintype.prod_empty, mul_one]
    rw [key A, key B, key C,
      Fintype.sum_eq_single default fun b hb => absurd (Subsingleton.elim b default) hb]
  | succ n =>
    show (quadHonest A B C (chalOf r) n).eval (chalOf r n) = _
    have hn : n < n + 1 := Nat.lt_succ_self n
    rw [quadHonest, dif_pos hn, chalOf_restrict, quadRoundPoly_eval,
      chalOf_coe r ⟨n, hn⟩, roundSum_last rfl (prodDiff A B C) r,
      Function.update_eq_self]
    rfl

omit [Fintype F] [DecidableEq F] in
/-- **Completeness of the quadratic realizer**: the honest family, run as both prover and
truth chain on the true table total, passes every check on EVERY challenge vector. -/
theorem quadHonest_complete (A B C : (Fin m → Bool) → F) (r : Fin m → F) :
    SumcheckAccepts (v := m) (quadHonest A B C (chalOf r)) (quadHonest A B C (chalOf r))
      (∑ b, (A b * B b - C b)) (∑ b, (A b * B b - C b)) r :=
  ⟨fun i hi => quadHonest_boolean_sum A B C r i hi, rfl⟩

/-- **Soundness against the built quadratic realizer.** With the honest side INSTANTIATED at
`quadHonest` (not hypothesized), any prefix-measurable degree-≤2 prover opening with a false
total `H ≠ Σ_b (A·B − C)(b)` is accepted with probability at most `m·2/|F|` —
`adaptive_sumcheck_soundness` consumed at `d = 2`. Only adversary-side hypotheses remain. -/
theorem quad_sumcheck_soundness {A B C : (Fin m → Bool) → F}
    {prover : (ℕ → F) → ℕ → Polynomial F} {H : F}
    (hpm : PrefixMeasurable prover)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F)
      (AdaptiveAcceptsFalse prover (quadHonest A B C) H (∑ b, (A b * B b - C b)))
      ≤ (m : ℝ) * (2 / Fintype.card F) := by
  have h := adaptive_sumcheck_soundness (v := m) (d := 2) (H := H)
    hpm (quadHonest_prefixMeasurable A B C) hProverDeg
    (fun χ i hi => quadHonest_degree A B C χ i hi)
    (fun r i hi => quadHonest_boolean_sum A B C r i hi)
  simpa using h

end QuadEngine

/-- info: 'Minidregg.Selvage.quad_sumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quad_sumcheck_soundness

end Minidregg.Selvage

