/-
# `Selvage/Rank1GradientCheck.lean` — a linear layer's gradient is CHECKED, not proved.

For a linear layer `y = Wx`, backpropagation's weight gradient is a RANK-1 OUTER
PRODUCT, `∇W = δ·xᵀ`, i.e. `∇W(i,j) = δ(i)·x(j)`. The arithmetization consequence
is the point of this file:

  **the MLE of an outer product FACTORS**, `(δ⊗x)^(r_i, r_j) = δ̂(r_i)·x̂(r_j)`,

so a claimed gradient `G` is checked by ONE multiplication of TWO single-variable
openings at a common random point — **no sum over an inner index, hence no sumcheck
round at all.** That is strictly cheaper than the matmul boundary (`Ĉ(r) = Σ_k …`,
which needs a sumcheck over `k`): the rank-1 case needs none.

**What is proved here (no `sorry`, statement-first):**

* `mle_outerTable` — the factorization, over any `CommRing`. Reindexing the
  hypercube along `Fin.appendEquiv` and splitting the chi product with
  `Fin.prod_univ_add`; nothing about it is specific to gradients.
* `rank1_complete` — the true gradient is accepted at EVERY challenge.
* `rank1_sound` — for `G ≠ δ⊗x`, the check accepts with probability at most
  `(mi + mj)/|F|` over a uniform `r ← F^{mi+mj}`. This is the two-variable
  Schwartz–Zippel argument, and the bound falls out of the landed
  `mle_zero_uniform_bound` applied to the DEFECT table `G − δ⊗x`: the split into
  row and column halves is a fact about the CHECK, not about the probability, so
  no new probability toolkit appears. With `n × n` weights, `mi = mj = log₂ n` and
  the bound is `2·log₂ n / |F|`.
* `mle_outerSum` / `rankK_sound` — the BATCH shape. A batch of `K` samples gives
  `∇W = Σ_k δ_k·x_kᵀ`, rank ≤ K, and the check becomes `Σ_k δ̂_k(r_i)·x̂_k(r_j)`:
  `K` products the verifier does itself, still no sumcheck over the `n²` matrix.
* `mle_sgdStep` / `sgd_step_complete` / `sgd_step_sound` — **the whole SGD step for
  a linear layer, in three openings at one common point.** `W' = W − η·∇W` is
  linear, so `Ŵ'(r) = Ŵ(r) − η·δ̂(r_i)·x̂(r_j)`: the gradient is never committed,
  never materialized, and the step is certified with ZERO rounds.

**Scope, as theorems rather than prose** (§4) — the three things this check does
NOT do, each one machine-checked so it cannot quietly drift into a claim:

* `outerTable_rescale` — it pins the MATRIX `δ⊗x`, not the PAIR `(δ, x)`:
  `(c·δ, c⁻¹·x)` is the same gradient and is accepted identically. (That is the
  correct equivalence class — `∇W` is the matrix — but it must be said.)
* `rank1_blind_to_the_error` — for ANY `δ'`, the claim built from `δ'` is accepted
  at every challenge. **Whether `δ` is the correct backpropagated error is a
  SEPARATE obligation** (the chain rule, and the next piece); this check is
  entirely relative to the committed `δ` and `x`.
The third scope item — that the check never reads the forward pass, the layer
output, the nonlinearity or its derivative — is a SYNTACTIC fact about
`Rank1Accepts`, readable from its definition. It is deliberately NOT dressed up as
a theorem: "two runs with different `W` agree" is `Iff.rfl`, a vacuous statement of
exactly the class this repo keeps finding, and a reader who saw it in the list
would credit the file with a check it does not perform.

**Teeth over F₅** (§5), the vacuity this file could carry and does not:
`rank1_refuses_a_wrong_gradient` (a one-entry perturbation, refused);
`rank1_refuses_another_rank_one` — **the sharp one: a genuinely different rank-1
matrix `δ'⊗x` is refused**, so the check certifies THIS gradient, not "some outer
product"; `rank1_refuses_the_transpose` (an index-order bug in the row/column split
would survive a symmetric test — this one does not); the accept COUNTS computed
(9 of 25 challenges, against the theorem's 10/25 — the bound is nearly ATTAINED, so
it is not loose slack), and both false-accept events exhibited NONEMPTY, so the
bounds constrain real events rather than vacua.

**Substrate.** This is the constraint semantics, in Lean. `prover/src/rank1.rs`
re-computes the same shapes as UNVERIFIED COMPUTE bound to these objects by
conformance vectors — agreement on vectors is the whole claim there, and it is
never called refinement.
-/
import Selvage.MultilinearZeroTest

namespace Minidregg.Selvage

/-! ## §1. The row/column split of a matrix index

A matrix entry `(i, j)` of an `2^mi × 2^mj` matrix is ONE hypercube index on
`mi + mj` bits: the low `mi` coordinates are the row, the high `mj` are the column.
The same split applies to the challenge vector, which is what makes the check's two
openings single-variable. -/

section Split

variable {α : Type*} {mi mj : ℕ}

/-- The row half of a matrix index (or challenge): coordinates `0 … mi−1`. -/
def rowHalf (mi mj : ℕ) (v : Fin (mi + mj) → α) : Fin mi → α :=
  fun i => v (Fin.castAdd mj i)

/-- The column half of a matrix index (or challenge): coordinates `mi … mi+mj−1`. -/
def colHalf (mi mj : ℕ) (v : Fin (mi + mj) → α) : Fin mj → α :=
  fun j => v (Fin.natAdd mi j)

@[simp] theorem rowHalf_append (u : Fin mi → α) (w : Fin mj → α) :
    rowHalf mi mj (Fin.append u w) = u :=
  funext fun i => Fin.append_left u w i

@[simp] theorem colHalf_append (u : Fin mi → α) (w : Fin mj → α) :
    colHalf mi mj (Fin.append u w) = w :=
  funext fun j => Fin.append_right u w j

end Split

/-! ## §2. The MLE of an outer product FACTORS

The whole cost argument rests on this one identity, and it holds over any
commutative ring: no field, no finiteness, no randomness. -/

section Outer

variable {F : Type*} [CommRing F] {mi mj : ℕ}

/-- The chi basis splits along the row/column boundary — one product over
`Fin (mi + mj)` is the product of its two halves (`Fin.prod_univ_add`). -/
theorem chiEval_split (b : Fin (mi + mj) → Bool) (r : Fin (mi + mj) → F) :
    chiEval b r
      = chiEval (rowHalf mi mj b) (rowHalf mi mj r)
        * chiEval (colHalf mi mj b) (colHalf mi mj r) := by
  unfold chiEval rowHalf colHalf
  exact Fin.prod_univ_add _

/-- **The rank-1 outer product as a hypercube table**: `(δ ⊗ x)(i,j) = δ(i)·x(j)`.
For a linear layer this IS the weight gradient, `∇W = δ·xᵀ`. -/
def outerTable (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) :
    (Fin (mi + mj) → Bool) → F :=
  fun b => d (rowHalf mi mj b) * x (colHalf mi mj b)

/-- `mle` is linear in the table (addition side). -/
theorem mle_add {m : ℕ} (f g : (Fin m → Bool) → F) (x : Fin m → F) :
    mle (fun b => f b + g b) x = mle f x + mle g x := by
  simp only [mle, add_mul, Finset.sum_add_distrib]

/-- `mle` commutes with scaling the table by a constant. -/
theorem mle_const_mul {m : ℕ} (c : F) (f : (Fin m → Bool) → F) (x : Fin m → F) :
    mle (fun b => c * f b) x = c * mle f x := by
  simp only [mle, Finset.mul_sum, mul_assoc]

/-- `mle` commutes with a finite sum of tables — the batch case's engine. -/
theorem mle_finset_sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin m → Bool) → F) (x : Fin m → F) :
    mle (fun b => ∑ k ∈ s, f k b) x = ∑ k ∈ s, mle (f k) x := by
  simp only [mle, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **THE FACTORIZATION.** The multilinear extension of an outer product is the
PRODUCT of the two factors' extensions, each in its own half of the challenge:

  `(δ ⊗ x)^(r) = δ̂(r_row) · x̂(r_col)`.

There is no sum over an inner index — which is exactly why the rank-1 check needs
no sumcheck, unlike the matmul contraction `Ĉ(r) = Σ_k Â(r_i,k)·B̂(k,r_j)`. -/
theorem mle_outerTable (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F)
    (r : Fin (mi + mj) → F) :
    mle (outerTable d x) r
      = mle d (rowHalf mi mj r) * mle x (colHalf mi mj r) := by
  have key : ∀ (u : Fin mi → Bool) (v : Fin mj → Bool),
      outerTable d x (Fin.append u v) * chiEval (Fin.append u v) r
        = (d u * chiEval u (rowHalf mi mj r))
          * (x v * chiEval v (colHalf mi mj r)) := by
    intro u v
    unfold outerTable
    rw [chiEval_split, rowHalf_append, colHalf_append]
    ring
  calc mle (outerTable d x) r
      = ∑ p : ((Fin mi → Bool) × (Fin mj → Bool)),
          outerTable d x (Fin.append p.1 p.2) * chiEval (Fin.append p.1 p.2) r := by
        rw [mle]
        exact (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) mi mj)
          (fun p => outerTable d x (Fin.append p.1 p.2)
            * chiEval (Fin.append p.1 p.2) r)
          (fun b => outerTable d x b * chiEval b r) (fun _ => rfl)).symm
    _ = ∑ u : Fin mi → Bool, ∑ v : Fin mj → Bool,
          (d u * chiEval u (rowHalf mi mj r))
            * (x v * chiEval v (colHalf mi mj r)) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun u _ =>
          Finset.sum_congr rfl fun v _ => key u v
    _ = mle d (rowHalf mi mj r) * mle x (colHalf mi mj r) := by
        rw [mle, mle, Finset.sum_mul_sum]

/-- **The batch gradient**: `K` samples contribute `∇W = Σ_k δ_k·x_kᵀ`, a matrix of
rank at most `K`. -/
def outerSum {K : ℕ} (d : Fin K → (Fin mi → Bool) → F)
    (x : Fin K → (Fin mj → Bool) → F) : (Fin (mi + mj) → Bool) → F :=
  fun b => ∑ k, d k (rowHalf mi mj b) * x k (colHalf mi mj b)

/-- **The batch factorization**: still no sum over the `n²` matrix — only over the
BATCH index, which the verifier evaluates itself in `K` multiplications. -/
theorem mle_outerSum {K : ℕ} (d : Fin K → (Fin mi → Bool) → F)
    (x : Fin K → (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    mle (outerSum d x) r
      = ∑ k, mle (d k) (rowHalf mi mj r) * mle (x k) (colHalf mi mj r) := by
  have h : outerSum d x = fun b => ∑ k, outerTable (d k) (x k) b := rfl
  rw [h, mle_finset_sum]
  exact Finset.sum_congr rfl fun k _ => mle_outerTable (d k) (x k) r

/-- **The optimizer step**: `W' = W − η·(δ ⊗ x)`. Linear in `W` and in the
gradient, which is what makes it a one-opening check. -/
def sgdStep (W : (Fin (mi + mj) → Bool) → F) (η : F)
    (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) :
    (Fin (mi + mj) → Bool) → F :=
  fun b => W b - η * outerTable d x b

/-- **The whole SGD step, at one point.** `Ŵ'(r) = Ŵ(r) − η·δ̂(r_row)·x̂(r_col)` —
three openings at a COMMON challenge and no rounds. The gradient is never
committed and never materialized. -/
theorem mle_sgdStep (W : (Fin (mi + mj) → Bool) → F) (η : F)
    (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    mle (sgdStep W η d x) r
      = mle W r - η * (mle d (rowHalf mi mj r) * mle x (colHalf mi mj r)) := by
  have h : sgdStep W η d x
      = fun b => W b + (-η) * outerTable d x b := by
    funext b; unfold sgdStep; ring
  rw [h, mle_add, mle_const_mul, mle_outerTable]
  ring

/-! ### Scope, stated as theorems -/

/-- **SCOPE — the check pins the MATRIX, not the PAIR.** Rescaling
`(δ, x) ↦ (c·δ, c⁻¹·x)` leaves the outer product, hence every accept/reject
decision, unchanged. This is the correct equivalence class (`∇W` IS the matrix),
but it means the check says nothing about the individual factors beyond their
product. -/
theorem outerTable_rescale {F : Type*} [Field F] {mi mj : ℕ} (c : F) (hc : c ≠ 0)
    (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) :
    outerTable (fun b => c * d b) (fun b => c⁻¹ * x b) = outerTable d x := by
  funext b
  unfold outerTable
  field_simp

end Outer

/-! ## §3. The check, its completeness, and its soundness -/

section Check

variable {F : Type} [Field F] [Fintype F] {mi mj : ℕ}

/-- **The rank-1 gradient check.** Given openings of the committed gradient `G`, of
the backpropagated error `δ` and of the layer input `x` at a common random point
`r`, the verifier checks ONE product:

  `Ĝ(r) = δ̂(r_row) · x̂(r_col)`.

Freivalds' rank-1 identity in MLE form: `O(1)` verifier arithmetic on top of the
openings, against the `2^{mi+mj}` multiplications that recomputing `δ·xᵀ` costs. -/
def Rank1Accepts (G : (Fin (mi + mj) → Bool) → F) (d : (Fin mi → Bool) → F)
    (x : (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) : Prop :=
  mle G r = mle d (rowHalf mi mj r) * mle x (colHalf mi mj r)

omit [Fintype F] in
/-- **Completeness.** The true gradient is accepted at EVERY challenge — the check
is an identity on it, not a probabilistic statement. -/
theorem rank1_complete (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F)
    (r : Fin (mi + mj) → F) : Rank1Accepts (outerTable d x) d x r :=
  mle_outerTable d x r

omit [Fintype F] in
/-- The check is exactly the vanishing of the DEFECT table `G − δ⊗x` at `r`. -/
theorem rank1_iff_defect_zero (G : (Fin (mi + mj) → Bool) → F)
    (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    Rank1Accepts G d x r ↔ mle (fun b => G b - outerTable d x b) r = 0 := by
  unfold Rank1Accepts
  rw [mle_sub, mle_outerTable, sub_eq_zero]

omit [Fintype F] in
/-- A table equals another exactly when their difference is the zero table — the
step from `G ≠ δ⊗x` to a NONZERO defect the Schwartz–Zippel bound consumes. -/
theorem defect_ne_zero {m : ℕ} {f g : (Fin m → Bool) → F} (h : f ≠ g) :
    (fun b => f b - g b) ≠ 0 := by
  intro hzero
  refine h (funext fun b => sub_eq_zero.mp ?_)
  have hb := congrFun hzero b
  simpa using hb

/-- **SOUNDNESS.** A gradient claim that is NOT the outer product survives a
uniformly random challenge with probability at most `(mi + mj)/|F|`.

Two-variable Schwartz–Zippel: the defect `G − δ⊗x` is a nonzero table on
`mi + mj` variables, and the landed `mle_zero_uniform_bound` prices its vanishing.
At an `n × n` layer (`mi = mj = log₂ n`) the bound is `2·log₂ n/|F|`, e.g.
`24/2^31` at `n = 4096` over BabyBear — and it is the ONLY soundness cost, because
there are no rounds to union-bound over. -/
theorem rank1_sound {G : (Fin (mi + mj) → Bool) → F} {d : (Fin mi → Bool) → F}
    {x : (Fin mj → Bool) → F} (hG : G ≠ outerTable d x) :
    uniformProb (Fin (mi + mj) → F) (Rank1Accepts G d x)
      ≤ ((mi + mj : ℕ) : ℝ) / Fintype.card F := by
  refine le_trans (le_of_eq (uniformProb_congr fun r => ?_))
    (mle_zero_uniform_bound (defect_ne_zero hG))
  exact rank1_iff_defect_zero G d x r

/-- **The sharp corollary — it is not "some outer product", it is THIS one.** Any
OTHER rank-1 matrix `δ'⊗x'` is refused with the same probability bound. A check
that certified merely "the claim is rank 1" would be satisfied by every `δ'⊗x'`;
this one is not, and that is a theorem, not a test. -/
theorem rank1_refuses_other_outer_products {d d' : (Fin mi → Bool) → F}
    {x x' : (Fin mj → Bool) → F} (h : outerTable d' x' ≠ outerTable d x) :
    uniformProb (Fin (mi + mj) → F) (Rank1Accepts (outerTable d' x') d x)
      ≤ ((mi + mj : ℕ) : ℝ) / Fintype.card F :=
  rank1_sound h

/-- **The batch check** (`K` samples): `Ĝ(r) = Σ_k δ̂_k(r_row)·x̂_k(r_col)`. -/
def RankKAccepts {K : ℕ} (G : (Fin (mi + mj) → Bool) → F)
    (d : Fin K → (Fin mi → Bool) → F) (x : Fin K → (Fin mj → Bool) → F)
    (r : Fin (mi + mj) → F) : Prop :=
  mle G r = ∑ k, mle (d k) (rowHalf mi mj r) * mle (x k) (colHalf mi mj r)

omit [Fintype F] in
/-- Completeness of the batch check. -/
theorem rankK_complete {K : ℕ} (d : Fin K → (Fin mi → Bool) → F)
    (x : Fin K → (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    RankKAccepts (outerSum d x) d x r :=
  mle_outerSum d x r

/-- **Soundness of the batch check** — the SAME bound. The batch index costs the
verifier `K` multiplications and costs the SOUNDNESS nothing: no round is added,
so the `(mi+mj)/|F|` does not grow with `K`. -/
theorem rankK_sound {K : ℕ} {G : (Fin (mi + mj) → Bool) → F}
    {d : Fin K → (Fin mi → Bool) → F} {x : Fin K → (Fin mj → Bool) → F}
    (hG : G ≠ outerSum d x) :
    uniformProb (Fin (mi + mj) → F) (RankKAccepts G d x)
      ≤ ((mi + mj : ℕ) : ℝ) / Fintype.card F := by
  refine le_trans (le_of_eq (uniformProb_congr fun r => ?_))
    (mle_zero_uniform_bound (defect_ne_zero hG))
  unfold RankKAccepts
  rw [mle_sub, mle_outerSum, sub_eq_zero]

/-! ### The optimizer step: linear, hence certified with no rounds -/

/-- **The SGD step check**: `Ŵ'(r) = Ŵ(r) − η·δ̂(r_row)·x̂(r_col)`. Three openings
at one common point; the gradient itself is never committed. -/
def SgdStepAccepts (W W' : (Fin (mi + mj) → Bool) → F) (η : F)
    (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    Prop :=
  mle W' r = mle W r - η * (mle d (rowHalf mi mj r) * mle x (colHalf mi mj r))

omit [Fintype F] in
/-- Completeness of the step check. -/
theorem sgd_step_complete (W : (Fin (mi + mj) → Bool) → F) (η : F)
    (d : (Fin mi → Bool) → F) (x : (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    SgdStepAccepts W (sgdStep W η d x) η d x r :=
  mle_sgdStep W η d x r

/-- **Soundness of the step check.** A `W'` that is not `W − η·δ⊗x` — a wrong
gradient, a wrong learning rate, or a tampered weight — survives with probability
at most `(mi + mj)/|F|`. One boundary `(W, δ, x, W')`, zero rounds. -/
theorem sgd_step_sound {W W' : (Fin (mi + mj) → Bool) → F} {η : F}
    {d : (Fin mi → Bool) → F} {x : (Fin mj → Bool) → F}
    (hW : W' ≠ sgdStep W η d x) :
    uniformProb (Fin (mi + mj) → F) (SgdStepAccepts W W' η d x)
      ≤ ((mi + mj : ℕ) : ℝ) / Fintype.card F := by
  refine le_trans (le_of_eq (uniformProb_congr fun r => ?_))
    (mle_zero_uniform_bound (defect_ne_zero hW))
  unfold SgdStepAccepts
  rw [mle_sub, mle_sgdStep, sub_eq_zero]

/-! ### What the check does NOT cover — as theorems, not prose -/

omit [Fintype F] in
/-- **SCOPE — blind to whether `δ` is the CORRECT backpropagated error.** For any
`δ'` and `x'` whatsoever, the claim built from them is accepted at every challenge.
The check is entirely relative to the committed `δ` and `x`; that `δ` is the true
chain-rule error of the layer above is a SEPARATE obligation, and the next piece of
the training boundary. -/
theorem rank1_blind_to_the_error (d' : (Fin mi → Bool) → F)
    (x' : (Fin mj → Bool) → F) (r : Fin (mi + mj) → F) :
    Rank1Accepts (outerTable d' x') d' x' r :=
  rank1_complete d' x' r

end Check

/-! ## §4. Teeth over F₅, a 2 × 2 layer (`mi = mj = 1`)

The four ways this file could be true and worthless: the check could accept
everything; it could accept every rank-1 matrix (certifying "an outer product"
rather than "the gradient"); the row/column split could be transposed and no
symmetric test would notice; and the soundness bounds could be true of EMPTY
events. Each is refuted by computation.

`δ = (1, 2)` so `δ̂(t) = 1 + t`; `x = (3, 4)` so `x̂(t) = 3 + t`; the true gradient
is `δ⊗x = [[3, 4], [1, 3]]` with `Ĝ(r₀, r₁) = (1 + r₀)(3 + r₁)`. -/

namespace Rank1Example

/-- The backpropagated error `δ = (1, 2)`. -/
def dv : (Fin 1 → Bool) → ZMod 5 := fun b => if b 0 then 2 else 1

/-- The layer input `x = (3, 4)`. -/
def xv : (Fin 1 → Bool) → ZMod 5 := fun b => if b 0 then 4 else 3

/-- A DIFFERENT error, `δ' = (1, 3)` — used to build a different rank-1 matrix. -/
def dv' : (Fin 1 → Bool) → ZMod 5 := fun b => if b 0 then 3 else 1

/-- The true gradient `∇W = δ⊗x`. -/
def gTrue : (Fin (1 + 1) → Bool) → ZMod 5 := outerTable dv xv

/-- A gradient wrong in ONE entry: the `(1,1)` entry is off by one. Rank 2, and
the cheapest possible lie. -/
def gWrong : (Fin (1 + 1) → Bool) → ZMod 5 :=
  fun b => gTrue b + (if b (Fin.castAdd 1 0) && b (Fin.natAdd 1 0) then 1 else 0)

/-- **TEETH — completeness on data**: the true gradient is accepted at all 25
challenges (the general theorem is `rank1_complete`; this is it computed). -/
theorem rank1_complete_fires :
    ∀ r : Fin (1 + 1) → ZMod 5,
      mle gTrue r = mle dv (rowHalf 1 1 r) * mle xv (colHalf 1 1 r) := by decide

/-- **TEETH — a wrong gradient is REFUSED** at the challenge `(2, 3)`. -/
theorem rank1_refuses_a_wrong_gradient :
    mle gWrong (![2, 3] : Fin (1 + 1) → ZMod 5)
      ≠ mle dv (rowHalf 1 1 ![2, 3]) * mle xv (colHalf 1 1 ![2, 3]) := by decide

/-- **TEETH — the false-accept event is NONEMPTY**: at `(0, 3)` the wrong gradient
IS accepted, so `rank1_sound`'s bound constrains a real event rather than a
vacuum. -/
theorem rank1_wrong_accept_witness :
    mle gWrong (![0, 3] : Fin (1 + 1) → ZMod 5)
      = mle dv (rowHalf 1 1 ![0, 3]) * mle xv (colHalf 1 1 ![0, 3]) := by decide

/-- **TEETH — the bound is nearly ATTAINED, not loose slack**: exactly 9 of the 25
challenges accept the wrong gradient, against the theorem's `(mi+mj)/|F| = 2/5 =
10/25`. -/
theorem rank1_wrong_accept_count :
    (Finset.univ.filter fun r : Fin (1 + 1) → ZMod 5 =>
        mle gWrong r = mle dv (rowHalf 1 1 r) * mle xv (colHalf 1 1 r)).card
      = 9 := by decide

/-- **⚑ THE SHARP TOOTH — a different RANK-1 matrix is refused.** `δ'⊗x` is a
perfectly good outer product; the check refuses it, so what is certified is THIS
gradient and not "the claim is rank 1". A check with the weaker meaning would
accept here. -/
theorem rank1_refuses_another_rank_one :
    mle (outerTable dv' xv) (![2, 3] : Fin (1 + 1) → ZMod 5)
      ≠ mle dv (rowHalf 1 1 ![2, 3]) * mle xv (colHalf 1 1 ![2, 3]) := by decide

/-- The other rank-1 matrix really is a different matrix (so the tooth above is
not refusing a spelling). -/
theorem other_rank_one_is_different : outerTable dv' xv ≠ gTrue := by decide

/-- And its false-accept event is nonempty too: at `(1, 2)` the wrong rank-1 matrix
is accepted. 9 of 25 challenges again — the rank-1 lie is no easier to catch than
the one-entry lie, which is the honest reading of a `2·log₂ n/|F|` bound. -/
theorem rank1_other_accept_witness :
    mle (outerTable dv' xv) (![1, 2] : Fin (1 + 1) → ZMod 5)
      = mle dv (rowHalf 1 1 ![1, 2]) * mle xv (colHalf 1 1 ![1, 2]) := by decide

/-- **TEETH — the index ORDER is pinned, not just the counts.** The accepting SET
of the rank-1 lie above is `{r₀ = 0} ∪ {r₁ = 2}`, which is NOT symmetric: the
swapped point `(2, 1)` must be REFUSED. A transposed row/column convention
exchanges this verdict with `rank1_other_accept_witness` and leaves both accept
COUNTS at 9 — so counting alone cannot see the bug, and this pair can. The Rust
mirror carries the same pair (`prover/tests/rank1_gradient.rs`). -/
theorem rank1_other_refused_at_the_swapped_point :
    mle (outerTable dv' xv) (![2, 1] : Fin (1 + 1) → ZMod 5)
      ≠ mle dv (rowHalf 1 1 ![2, 1]) * mle xv (colHalf 1 1 ![2, 1]) := by decide

/-- **TEETH — the TRANSPOSE is refused.** `x⊗δ` is the transpose of `δ⊗x`; an
index-order bug in `rowHalf`/`colHalf` would make the check accept it, and no
symmetric test would ever notice. -/
theorem rank1_refuses_the_transpose :
    mle (outerTable xv dv) (![2, 3] : Fin (1 + 1) → ZMod 5)
      ≠ mle dv (rowHalf 1 1 ![2, 3]) * mle xv (colHalf 1 1 ![2, 3]) := by decide

/-- **TEETH — the check is not "always accept"**: over the 25 challenges the wrong
gradient is refused at 16 of them. -/
theorem rank1_refusal_is_the_common_case :
    (Finset.univ.filter fun r : Fin (1 + 1) → ZMod 5 =>
        mle gWrong r ≠ mle dv (rowHalf 1 1 r) * mle xv (colHalf 1 1 r)).card
      = 16 := by decide

/-- The soundness theorem FIRES on the wrong gradient: at most `2/5`, and the
computed count above is `9/25 < 10/25`. -/
theorem rank1_sound_fires :
    uniformProb (Fin (1 + 1) → ZMod 5) (Rank1Accepts gWrong dv xv) ≤ 2 / 5 := by
  have hne : gWrong ≠ outerTable dv xv := by decide
  have h := rank1_sound (F := ZMod 5) (mi := 1) (mj := 1) hne
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-! ### The optimizer step, computed -/

/-- A weight matrix: all ones. -/
def wOnes : (Fin (1 + 1) → Bool) → ZMod 5 := fun _ => 1

/-- **TEETH — the SGD step check fires on data** at `η = 2`, every challenge. -/
theorem sgd_step_fires :
    ∀ r : Fin (1 + 1) → ZMod 5,
      mle (sgdStep wOnes 2 dv xv) r
        = mle wOnes r
          - 2 * (mle dv (rowHalf 1 1 r) * mle xv (colHalf 1 1 r)) := by decide

/-- **TEETH — a WRONG LEARNING RATE is caught.** The update was computed with
`η = 2` and the verifier checks `η = 3`: refused at `(2, 3)`. The step check binds
the hyperparameter, not just the gradient. -/
theorem sgd_step_refuses_wrong_eta :
    mle (sgdStep wOnes 2 dv xv) (![2, 3] : Fin (1 + 1) → ZMod 5)
      ≠ mle wOnes ![2, 3]
        - 3 * (mle dv (rowHalf 1 1 ![2, 3]) * mle xv (colHalf 1 1 ![2, 3])) := by
  decide

/-- **TEETH — a tampered weight is caught at EVERY challenge.** Adding `1` to every
entry of `W'` shifts the defect to the constant table `1`, whose MLE never
vanishes: 0 of 25 challenges accept. -/
theorem sgd_step_refuses_tampered_weights :
    ∀ r : Fin (1 + 1) → ZMod 5,
      mle (fun b => sgdStep wOnes 2 dv xv b + 1) r
        ≠ mle wOnes r
          - 2 * (mle dv (rowHalf 1 1 r) * mle xv (colHalf 1 1 r)) := by decide

end Rank1Example

/-! ## §5. Axiom pins (house law) -/

/-- info: 'Minidregg.Selvage.chiEval_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms chiEval_split
/-- info: 'Minidregg.Selvage.mle_outerTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_outerTable
/-- info: 'Minidregg.Selvage.mle_outerSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_outerSum
/-- info: 'Minidregg.Selvage.mle_sgdStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_sgdStep
/-- info: 'Minidregg.Selvage.outerTable_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outerTable_rescale
/-- info: 'Minidregg.Selvage.rank1_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rank1_complete
/-- info: 'Minidregg.Selvage.rank1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rank1_sound
/-- info: 'Minidregg.Selvage.rank1_refuses_other_outer_products' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rank1_refuses_other_outer_products
/-- info: 'Minidregg.Selvage.rankK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rankK_sound
/-- info: 'Minidregg.Selvage.sgd_step_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sgd_step_sound
/-- info: 'Minidregg.Selvage.Rank1Example.rank1_refuses_another_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Rank1Example.rank1_refuses_another_rank_one
/-- info: 'Minidregg.Selvage.Rank1Example.rank1_refuses_the_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Rank1Example.rank1_refuses_the_transpose
/-- info: 'Minidregg.Selvage.Rank1Example.rank1_other_refused_at_the_swapped_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Rank1Example.rank1_other_refused_at_the_swapped_point
/-- info: 'Minidregg.Selvage.Rank1Example.rank1_wrong_accept_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Rank1Example.rank1_wrong_accept_count
/-- info: 'Minidregg.Selvage.Rank1Example.rank1_sound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Rank1Example.rank1_sound_fires
/-- info: 'Minidregg.Selvage.Rank1Example.sgd_step_refuses_tampered_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Rank1Example.sgd_step_refuses_tampered_weights

end Minidregg.Selvage
