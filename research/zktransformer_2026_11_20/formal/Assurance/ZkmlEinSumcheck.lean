/-
# `Assurance/ZkmlEinSumcheck.lean` — `EinSumcheck` completeness, naive-bug refutation, `cubicForm` reduction, and two-term soundness

**Substrate, said out loud: this is Lean-authored constraint and protocol assurance.** Every
theorem here composes directly over `Selvage/` (`MultilinearExtension`, `EqPolynomial`,
`MultilinearZeroTest`, `Rank1GradientCheck`) and `Assurance/` (`AirSumcheckCubic`,
`ZkmlMatmulSumcheck`, `ZkmlMatmulCommitment`), plus `Theory/ZkmlEinsum.lean`. Zero `sorry`,
zero `axiom`, zero `native_decide`.

## What this file proves (and the two paper claims it corrects)

`zkTransformer` (Chen, Tang & Kang, CCS 2026, §3 & App. F) introduces `EinSumcheck`, compiling
an arbitrary trace-free Einsum contraction into a single Sumcheck instance by:
* substituting verifier challenges `(xL, xR)` directly into **degree-1 free indices**
  (`F_1 = F_L ⊔ F_R`), and
* inserting the multilinear Lagrange kernel `eqMle xS` ONLY on **shared free indices**
  (`F_{≥2} = F_S`), summing over `{0,1}^{μS} × {0,1}^κ`.

Five formal results establish what is true, what breaks without `eqMle`, and what `zkTransformer`
Lemma 3.2 got wrong:

1. **Suffix / projection MLE invariance (`mle_extendRight`, `mle_extendLeft`,
   `mle₂_ignore_snd`, `mle₂_ignore_fst`)**: viewing a multilinear table on fewer cube variables
   as a table on a larger cube that ignores extra coordinates leaves `mle` identically
   unchanged on the retained coordinates. This is the algebraic engine behind `zkTransformer`
   Alg. 1's unequal-variable-count prover (`Eq. 10`) and projects terminal oracle openings onto
   each operand's native domain without padding or repeating tables.
2. **Theorem 1 (`einsum_mle_identity` — `zkTransformer` Thm 3.1)**: at EVERY outer field point
   `(xL, xR, xS)`, `mle₃ (einsumTable A B) xL xR xS` equals
   `∑ h, ∑ p, eqMle xS (cubePt h) * rowBoundA A xL h p * colBoundB B xR h p` — proved over any
   `CommRing` (and specialized to `[Field F]` by composing `Selvage.eqMle_fold` with
   `ZkmlMatmulSumcheck.mle₂_contraction`, zero appeal to `multiAffine_ext`).
3. **Theorem 2 (`naive_batched_matmul_incomplete` — refuting `zkGPT` Eq. 8)**: over `ZMod 7`
   on 2-batch 2×2 batched matmul (`bij,bjk->bik`, `μS = 1`), concrete honest tables `bA, bB`
   agree with the naive `eq`-free sum `∑ p, Â(xL, xS, p) * B̂(xR, xS, p)` at EVERY Boolean
   corner (`naive_batched_matmul_agrees_on_cube`), yet **disagree** at `xS = ![2]` (`4 ≠ 2`,
   `naive_batched_matmul_incomplete`) and on 5 of the 7 challenges in `ZMod 7`, while
   `EinSumcheck` succeeds everywhere.
4. **Theorem 3 (`einsum_is_cubicForm` + `einsumHonest_complete` + Factored Terminal Check)**:
   the `(μS + κ)`-variable summand is an exact instance of `AirSumcheckCubic.cubicForm` with
   `C ≡ 0, D ≡ 1`. Consequently `cubicHonest` gives completeness at every challenge, and
   `scChain_cubicHonest_final` + `mle_extendRight` factor the terminal check into
   `eqMle xS r_S * (Â₀(xL, r_S, r_κ1) * B̂₀(xR, r_S, r_κ2))` (and `zkTransformer` Eq. 10's
   `eqMle r r_x * T̂₁(r_x, r_y) * T̂₂(r_x, r_y, r_z)`) with **zero wiring commitments**.
5. **Theorem 4 (`einsumcheck_soundness` — fixing `zkTransformer` Lemma 3.2)**:
   `zkTransformer` Lemma 3.2 states soundness error `(m+1)·v/|F|` where `v = max_t |I_t|`. That
   lemma has TWO gaps:
   * **(a) Missing outer Schwartz–Zippel term**: for a wrong output table `Z ≠ einsumTable A B`,
     random outer evaluation at `(xL, xR, xS)` collides with `einsumTable A B` with probability
     up to `(μL + μR + μS)/|F|` (`einsum_forged_survives` + `einsum_forged_accepts_end_to_end`
     exhibit a concrete forgery over `ZMod 7` accepted with probability 1 across all sumcheck
     challenges once the outer point lands on the root!). The true bound against an adaptive
     degree-≤3 prover (even one that chooses its round polynomials after seeing `(xL, xR, xS)`)
     is
       `Pr[Accepts] ≤ (μL + μR + μS) / |F| + (μS + κ) * (3 / |F|)`.
   * **(b) Wrong round parameter `v`**: when operands carry disjoint summation indices
     (`κL > 0` and `κR > 0`, `lemma32_v_not_upper_bound_on_rounds`), `μS + κ` strictly exceeds
     `v = max_t |I_t|`; conversely, when `μL` or `μR` is large (GQA!), `μS + κ` is strictly
     smaller than `v`.
6. **Theorem 5 (`gqa_rounds_saved` — Grouped-Query Attention `igrc,jgc->grij`)**: placing the
   query-within-group index `r ∈ {0,1}^μG` (`H = KV · G`) in `μL` rather than `μS` runs
   `μKV + μC` sumcheck rounds instead of `(μKV + μG) + μC` rounds (9 vs 12 in `gpt-oss-20b`)
   and avoids a `2^μG`× (`8×`) committed-table blowup on `K` (and `V`).
-/
import Assurance.ZkmlMatmulCommitment
import Theory.ZkmlEinsum

namespace Minidregg.Assurance

open Minidregg.Selvage Minidregg.Theory.ZkmlEinsum Polynomial

/-! ## §1. Suffix / projection MLE invariance (`zkTransformer` Alg. 1's unequal-variable engine) -/

section ProjectionInvariance

/-- Reassembling `rowHalf` and `colHalf` recovers any vector on `Fin (mi + mj)`. -/
@[simp] theorem append_rowHalf_colHalf {α : Type*} {mi mj : ℕ} (r : Fin (mi + mj) → α) :
    Fin.append (rowHalf mi mj r) (colHalf mi mj r) = r := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [rowHalf]
  · simp [colHalf]

/-- `chiEval_lsbCons` over any `CommRing` (lifting `MultiplicativeMleTerminal`'s `[Field F]`
binder so `mle_extendRight` and `mle_extendLeft` carry no field hypothesis). -/
theorem chiEval_lsbCons_ring {F : Type*} [CommRing F] {m : ℕ}
    (head : Bool) (tail : Fin m → Bool) (x : F) (xs : Fin m → F) :
    chiEval (lsbCons head tail) (lsbCons x xs) =
      (if head then x else 1 - x) * chiEval tail xs := by
  simp [chiEval, Fin.prod_univ_succ, lsbCons]

/-- Partition of unity for the chi/Lagrange basis over any commutative ring:
`∑ b : Fin n → Bool, χ_b(y) = 1`. -/
theorem sum_chiEval_eq_one {F : Type*} [CommRing F] :
    ∀ {n : ℕ} (y : Fin n → F), (∑ b : Fin n → Bool, chiEval b y) = 1
  | 0, y => by
      rw [Fintype.sum_eq_single default fun b hb => absurd (Subsingleton.elim b default) hb]
      simp [chiEval]
  | n + 1, y => by
      have hy : y = lsbCons (y 0) (fun i => y i.succ) := (Fin.cons_self_tail y).symm
      rw [hy, ← (lsbCubeEquiv n).symm.sum_comp (fun b => chiEval b (lsbCons (y 0) _)),
        Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, lsbCubeEquiv_symm_apply, chiEval_lsbCons_ring]
      simp [← Finset.mul_sum, sum_chiEval_eq_one (fun i => y i.succ)]

/-- View an `m`-variable hypercube table as an `(m + n)`-variable table ignoring the high `n`
coordinates (`zkTransformer` Alg. 1's prefix-aligned operand lift). -/
def extendRight {F : Type*} (m n : ℕ) (f : (Fin m → Bool) → F) :
    (Fin (m + n) → Bool) → F :=
  fun b => f (rowHalf m n b)

/-- View an `n`-variable hypercube table as an `(m + n)`-variable table ignoring the low `m`
coordinates. -/
def extendLeft {F : Type*} (m n : ℕ) (g : (Fin n → Bool) → F) :
    (Fin (m + n) → Bool) → F :=
  fun b => g (colHalf m n b)

/-- **Suffix MLE invariance (`mle_extendRight`).** Viewing `f : {0,1}^m → F` on `{0,1}^{m+n}`
by ignoring the trailing `n` bits yields the exact same multilinear extension evaluated on the
first `m` coordinates — over any commutative ring. -/
theorem mle_extendRight {F : Type*} [CommRing F] {m n : ℕ}
    (f : (Fin m → Bool) → F) (x : Fin (m + n) → F) :
    mle (extendRight m n f) x = mle f (rowHalf m n x) := by
  have houter : extendRight m n f = outerTable f (fun _ : Fin n → Bool => (1 : F)) := by
    funext b; simp [extendRight, outerTable]
  rw [houter, mle_outerTable]
  simp [mle, sum_chiEval_eq_one]

@[simp] theorem mle_extendRight_append {F : Type*} [CommRing F] {m n : ℕ}
    (f : (Fin m → Bool) → F) (u : Fin m → F) (v : Fin n → F) :
    mle (extendRight m n f) (Fin.append u v) = mle f u := by
  rw [mle_extendRight, rowHalf_append]

/-- **Prefix MLE invariance (`mle_extendLeft`).** Symmetrically, ignoring the leading `m` bits
evaluates `mle` on the trailing `n` coordinates. -/
theorem mle_extendLeft {F : Type*} [CommRing F] {m n : ℕ}
    (g : (Fin n → Bool) → F) (x : Fin (m + n) → F) :
    mle (extendLeft m n g) x = mle g (colHalf m n x) := by
  have houter : extendLeft m n g = outerTable (fun _ : Fin m → Bool => (1 : F)) g := by
    funext b; simp [extendLeft, outerTable]
  rw [houter, mle_outerTable]
  simp [mle, sum_chiEval_eq_one]

@[simp] theorem mle_extendLeft_append {F : Type*} [CommRing F] {m n : ℕ}
    (g : (Fin n → Bool) → F) (u : Fin m → F) (v : Fin n → F) :
    mle (extendLeft m n g) (Fin.append u v) = mle g v := by
  rw [mle_extendLeft, colHalf_append]

/-- Curried two-block form: ignoring the second block in `mle₂` leaves `mle` of the first. -/
theorem mle₂_ignore_snd {F : Type} [Field F] {μ ν : ℕ}
    (f : (Fin μ → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (fun a _ => f a) x y = mle f x := by
  rw [← mle_flatten₂]
  exact mle_extendRight_append f x y

/-- Curried two-block form: ignoring the first block in `mle₂` leaves `mle` of the second. -/
theorem mle₂_ignore_fst {F : Type} [Field F] {μ ν : ℕ}
    (g : (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (fun _ b => g b) x y = mle g y := by
  rw [← mle_flatten₂]
  exact mle_extendLeft_append g x y

end ProjectionInvariance

/-! ## §2. Three-block multilinear extension (`mle₃`) and 3-block Schwartz–Zippel -/

section ThreeBlocks

variable {F : Type} [Field F] {μ₁ μ₂ μ₃ : ℕ}

/-- **The three-block multilinear extension.** Used for the output tensor `Z(aL, aR, h)` over
`(μL, μR, μS)` as well as 3-block input operands `A(aL, h, p)` and `B(aR, h, p)`. -/
def mle₃ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (x₃ : Fin μ₃ → F) : F :=
  ∑ a₁, ∑ a₂, ∑ a₃, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃

/-- Bind the first block of a 3-block table to `x₁`, leaving a 2-block table. -/
def bind₁ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F) (x₁ : Fin μ₁ → F) :
    (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F :=
  fun a₂ a₃ => mle (fun a₁ => f a₁ a₂ a₃) x₁

/-- Bind the first two blocks of a 3-block table to `(x₁, x₂)`, leaving a 1-block table on the
third cube (for an Einsum output `Z`, this binds `(xL, xR)` and leaves a table on `μS`). -/
def slice₃ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) : (Fin μ₃ → Bool) → F :=
  fun a₃ => mle₂ (fun a₁ a₂ => f a₁ a₂ a₃) x₁ x₂

/-- `mle₃` is `mle₂` applied to `bind₁` — every 2-block theorem transfers with no new proof. -/
theorem mle₃_as_mle₂_bind₁ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (x₃ : Fin μ₃ → F) :
    mle₃ f x₁ x₂ x₃ = mle₂ (bind₁ f x₁) x₂ x₃ := by
  simp only [mle₃, mle₂, bind₁, mle, Finset.sum_mul]
  calc
    (∑ a₁, ∑ a₂, ∑ a₃, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃)
        = ∑ a₂, ∑ a₁, ∑ a₃, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃ :=
          Finset.sum_comm
    _ = ∑ a₂, ∑ a₃, ∑ a₁, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- `mle₃` is `mle` applied to `slice₃` — how `eqMle_fold` enters on the shared free block. -/
theorem mle₃_as_mle_slice₃ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (x₃ : Fin μ₃ → F) :
    mle₃ f x₁ x₂ x₃ = mle (slice₃ f x₁ x₂) x₃ := by
  simp only [mle₃, mle, slice₃, mle₂, Finset.sum_mul]
  calc
    (∑ a₁, ∑ a₂, ∑ a₃, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃)
        = ∑ a₁, ∑ a₃, ∑ a₂, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₃, ∑ a₁, ∑ a₂, f a₁ a₂ a₃ * chiEval a₁ x₁ * chiEval a₂ x₂ * chiEval a₃ x₃ :=
          Finset.sum_comm

/-- **Cube agreement** for `mle₃`. -/
theorem mle₃_agrees (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (a₁ : Fin μ₁ → Bool) (a₂ : Fin μ₂ → Bool) (a₃ : Fin μ₃ → Bool) :
    mle₃ f (cubePt a₁) (cubePt a₂) (cubePt a₃) = f a₁ a₂ a₃ := by
  rw [mle₃_as_mle₂_bind₁, mle₂_agrees, bind₁, mle_agrees]

/-- Table subtraction linearity for `mle₃`. -/
theorem mle₃_sub (f g : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (x₃ : Fin μ₃ → F) :
    mle₃ (fun a₁ a₂ a₃ => f a₁ a₂ a₃ - g a₁ a₂ a₃) x₁ x₂ x₃
      = mle₃ f x₁ x₂ x₃ - mle₃ g x₁ x₂ x₃ := by
  simp only [mle₃, sub_mul, Finset.sum_sub_distrib]

/-- Evaluating the third block of `mle₃` at a Boolean corner `cubePt a₃` reduces to `mle₂`. -/
@[simp] theorem mle₃_cubePt_thd (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (a₃ : Fin μ₃ → Bool) :
    mle₃ f x₁ x₂ (cubePt a₃) = mle₂ (fun a₁ a₂ => f a₁ a₂ a₃) x₁ x₂ := by
  rw [mle₃_as_mle_slice₃, mle_agrees]
  rfl

/-- Suffix projection invariance on the third block of `mle₃` (used when an operand ignores
extra summation bits). -/
theorem mle₃_extendRight_thd {κ₁ κ₂ : ℕ}
    (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin κ₁ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (r : Fin (κ₁ + κ₂) → F) :
    mle₃ (fun a₁ a₂ p => f a₁ a₂ (rowHalf κ₁ κ₂ p)) x₁ x₂ r
      = mle₃ f x₁ x₂ (rowHalf κ₁ κ₂ r) := by
  rw [mle₃_as_mle_slice₃, mle₃_as_mle_slice₃]
  exact mle_extendRight (slice₃ f x₁ x₂) r

/-- Flatten a curried 3-block table onto one hypercube `Fin ((μ₁ + μ₂) + μ₃) → Bool`. -/
def flatten₃ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F) :
    (Fin ((μ₁ + μ₂) + μ₃) → Bool) → F :=
  flatten₂ (fun b₁₂ a₃ => flatten₂ (fun a₁ a₂ => f a₁ a₂ a₃) b₁₂)

/-- One-cube `mle` of `flatten₃ f` equals `mle₃ f` (connects `mle₃` to `MleEvalClaim`). -/
theorem mle_flatten₃ (f : (Fin μ₁ → Bool) → (Fin μ₂ → Bool) → (Fin μ₃ → Bool) → F)
    (x₁ : Fin μ₁ → F) (x₂ : Fin μ₂ → F) (x₃ : Fin μ₃ → F) :
    mle (flatten₃ f) (Fin.append (Fin.append x₁ x₂) x₃) = mle₃ f x₁ x₂ x₃ := by
  rw [flatten₃, mle_flatten₂, mle₂_row, mle₃_as_mle_slice₃]
  congr 1
  funext a₃
  exact mle_flatten₂ (fun a₁ a₂ => f a₁ a₂ a₃) x₁ x₂

end ThreeBlocks

section ThreeBlockSZ

variable {F : Type} [Field F] [Fintype F] {μL μR μS : ℕ}

/-- Outer random challenge tuple `(xL, xR, xS)` drawn before Sumcheck begins. -/
abbrev OuterChal (μL μR μS : ℕ) (F : Type) : Type :=
  (Fin μL → F) × (Fin μR → F) × (Fin μS → F)

/-- **Three-block multilinear Schwartz–Zippel.** A nonzero 3-block table's `mle₃` vanishes at a
uniformly random `(xL, xR, xS)` with probability at most `(μL + μR + μS) / |F|`.
Proved by composing `mle_zero_uniform_bound` (on `μL`) with `mle₂_zero_uniform_bound` (on
`μR + μS`) along `bind₁`. -/
theorem mle₃_zero_uniform_bound
    {f : (Fin μL → Bool) → (Fin μR → Bool) → (Fin μS → Bool) → F} (hf : f ≠ 0) :
    uniformProb (OuterChal μL μR μS F) (fun o => mle₃ f o.1 o.2.1 o.2.2 = 0)
      ≤ ((μL : ℝ) + μR + μS) / Fintype.card F := by
  obtain ⟨aL₀, haL₀⟩ := Function.ne_iff.mp hf
  obtain ⟨aR₀, haR₀⟩ := Function.ne_iff.mp haL₀
  obtain ⟨aS₀, haS₀⟩ := Function.ne_iff.mp haR₀
  have hfiber : (fun aL => f aL aR₀ aS₀) ≠ 0 := fun h => haS₀ (congrFun h aL₀)
  have hstep : ∀ o : OuterChal μL μR μS F, mle₃ f o.1 o.2.1 o.2.2 = 0 →
      (bind₁ f o.1 = 0 ∨ (bind₁ f o.1 ≠ 0 ∧ mle₂ (bind₁ f o.1) o.2.1 o.2.2 = 0)) := by
    intro o ho
    rw [mle₃_as_mle₂_bind₁] at ho
    by_cases h : bind₁ f o.1 = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, ho⟩
  refine le_trans (uniformProb_mono hstep) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  have hfirst : uniformProb (OuterChal μL μR μS F) (fun o => bind₁ f o.1 = 0)
      ≤ (μL : ℝ) / Fintype.card F := by
    refine uniformProb_fst_le _ (fun xL => bind₁ f xL = 0) (fun _ => Iff.rfl)
      (by positivity) ?_
    refine le_trans (uniformProb_mono (q := fun xL => mle (fun aL => f aL aR₀ aS₀) xL = 0) ?_)
      (mle_zero_uniform_bound hfiber)
    intro xL hxL
    exact congrFun (congrFun hxL aR₀) aS₀
  have hsecond : uniformProb (OuterChal μL μR μS F)
      (fun o => bind₁ f o.1 ≠ 0 ∧ mle₂ (bind₁ f o.1) o.2.1 o.2.2 = 0)
      ≤ ((μR : ℝ) + μS) / Fintype.card F := by
    refine uniformProb_prod_le (by positivity) fun xL => ?_
    show uniformProb ((Fin μR → F) × (Fin μS → F))
      (fun w => bind₁ f xL ≠ 0 ∧ mle₂ (bind₁ f xL) w.1 w.2 = 0) ≤ _
    by_cases hxL : bind₁ f xL = 0
    · rw [uniformProb_false fun _ h => h.1 hxL]
      positivity
    · exact le_trans
        (uniformProb_mono
          (p := fun w : (Fin μR → F) × (Fin μS → F) =>
            bind₁ f xL ≠ 0 ∧ mle₂ (bind₁ f xL) w.1 w.2 = 0)
          (q := fun w => mle₂ (bind₁ f xL) w.1 w.2 = 0) fun _ h => h.2)
        (mle₂_zero_uniform_bound hxL)
  have hadd : (μL : ℝ) / Fintype.card F + ((μR : ℝ) + μS) / Fintype.card F
      = ((μL : ℝ) + μR + μS) / Fintype.card F := by ring
  rw [← hadd]
  exact add_le_add hfirst hsecond

end ThreeBlockSZ

/-! ## §3. Theorem 1 (`einsum_mle_identity` — `zkTransformer` Theorem 3.1) -/

section EinsumIdentity

variable {F : Type} [Field F] {μL μR μS κ : ℕ}

/-- Output table of a two-operand Einsum on Boolean hypercubes:
`Z(aL, aR, h) = ∑ p : Fin κ → Bool, A(aL, h, p) * B(aR, h, p)`. -/
def einsumTable
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F) :
    (Fin μL → Bool) → (Fin μR → Bool) → (Fin μS → Bool) → F :=
  fun aL aR h => ∑ p : Fin κ → Bool, A aL h p * B aR h p

/-- Left operand partially evaluated at the outer degree-1 challenge `xL : Fin μL → F`:
`rowBoundA A xL h p = Â(xL, h, p)`. -/
def rowBoundA
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (h : Fin μS → Bool) (p : Fin κ → Bool) : F :=
  mle (fun aL => A aL h p) xL

/-- Right operand partially evaluated at the outer degree-1 challenge `xR : Fin μR → F`:
`colBoundB B xR h p = B̂(xR, h, p)`. -/
def colBoundB
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xR : Fin μR → F) (h : Fin μS → Bool) (p : Fin κ → Bool) : F :=
  mle (fun aR => B aR h p) xR

/-- **THEOREM 1 (`einsum_mle_identity` — `zkTransformer` Theorem 3.1).**
At EVERY outer challenge `(xL, xR, xS)`, the 3-block MLE of `einsumTable A B` equals

  `∑ h : Fin μS → Bool, ∑ p : Fin κ → Bool, eqMle xS (cubePt h) * rowBoundA A xL h p * colBoundB B xR h p`

with `eqMle` inserted ONLY on the shared free block `μS` (`F_{≥2}`) and `(xL, xR)` (`F_1`)
substituted directly into the partial evaluations. Proved with zero appeal to polynomial
uniqueness by composing `Selvage.eqMle_fold` on `μS` with `ZkmlMatmulSumcheck.mle₂_contraction`
on `(μL, μR, κ)` at each corner `h`. -/
theorem einsum_mle_identity
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F) :
    mle₃ (einsumTable A B) xL xR xS =
      ∑ h : Fin μS → Bool, ∑ p : Fin κ → Bool,
        eqMle xS (cubePt h) * rowBoundA A xL h p * colBoundB B xR h p := by
  rw [mle₃_as_mle_slice₃, ← eqMle_fold xS (slice₃ (einsumTable A B) xL xR)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hslice : slice₃ (einsumTable A B) xL xR h
      = mle₂ (matmulTable (fun aL p => A aL h p) (fun p aR => B aR h p)) xL xR := rfl
  rw [hslice, mle₂_contraction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [rowBoundA, colBoundB, rowPartial, colPartial]
  ring

/-- **Specialization (`μS = 0`):** when there are no shared free indices (`2D matmul`), the
`Fin 0 → Bool` outer sum has one corner `Fin.elim0` with `eqMle = 1`, collapsing
`einsum_mle_identity` back to Thaler's `eq`-free `mle₂_contraction`. -/
theorem einsum_zero_shared_is_matmul
    (A : (Fin μL → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin μR → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin 0 → F) :
    mle₃ (einsumTable (μS := 0) (fun aL _ p => A aL p) (fun aR _ p => B p aR)) xL xR xS
      = mle₂ (matmulTable A B) xL xR := by
  rw [einsum_mle_identity,
    Fintype.sum_eq_single Fin.elim0 fun h hh => absurd (Subsingleton.elim h Fin.elim0) hh]
  have heq : eqMle xS (cubePt (Fin.elim0 : Fin 0 → Bool)) = 1 := by
    simp [eqMle]
  simp only [heq, one_mul, rowBoundA, colBoundB]
  exact (mle₂_contraction A B xL xR).symm

end EinsumIdentity

/-! ## §4. Theorem 2 (`naive_batched_matmul_incomplete` — refuting `zkGPT` Eq. 8)

`zkGPT` Eq. (8) proposes checking batched matrix multiplication `bij,bjk->bik` at a random
challenge `(xS, xL, xR)` via the `eq`-free sum `∑ p, Â(xL, xS, p) · B̂(xR, xS, p)`. Because
`xS` appears in BOTH factors, the RHS has degree 2 in `xS` whereas `Ẑ(xL, xR, xS)` is
multilinear (degree 1 in `xS`). They agree at every Boolean corner and disagree off the cube,
breaking **completeness**: an honest prover with the true witness is rejected! -/

namespace NaiveBugRefutation

/-- The naive `eq`-free batched-matmul sum (`zkGPT` Eq. 8): substitutes `xS` directly into
both `A` and `B` instead of summing over `{0,1}^{μS}` against `eqMle xS`. -/
def naiveBatchedRhs {F : Type} [Field F] {μL μR μS κ : ℕ}
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F) : F :=
  ∑ p : Fin κ → Bool, mle₃ A xL xS (cubePt p) * mle₃ B xR xS (cubePt p)

/-- Concrete honest 2-batch 2×2 left operand `bA` over `ZMod 7` (`μL = 1, μS = 1, κ = 1`):
batch `0` is zero; batch `1` has top-left entry `1` (else `0`). -/
def bA : (Fin 1 → Bool) → (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7 :=
  fun aL h p => if h 0 && !aL 0 && !p 0 then 1 else 0

/-- Concrete honest 2-batch 2×2 right operand `bB` over `ZMod 7` (`μR = 1, μS = 1, κ = 1`):
batch `0` is zero; batch `1` has top-left entry `1` (else `0`). -/
def bB : (Fin 1 → Bool) → (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7 :=
  fun aR h p => if h 0 && !aR 0 && !p 0 then 1 else 0

/-- **Why the bug survived Boolean testing**: on ALL `2³ = 8` Boolean corners `(bL, bR, bS)`,
the naive `eq`-free RHS agrees with `Ẑ`. -/
theorem naive_batched_matmul_agrees_on_cube :
    ∀ (bL bR bS : Fin 1 → Bool),
      naiveBatchedRhs bA bB (cubePt bL) (cubePt bR) (cubePt bS)
        = mle₃ (einsumTable bA bB) (cubePt bL) (cubePt bR) (cubePt bS) := by
  decide

/-- **THEOREM 2 (`naive_batched_matmul_incomplete` — refuting `zkGPT` Eq. 8).**
At the verifier challenge `xS = ![2]` (with `xL = ![0], xR = ![0]`) over `ZMod 7`, the naive
`eq`-free sum evaluates to `2 · 2 = 4` whereas the true output MLE `Ẑ(![0], ![0], ![2])` is `2`.
Even an honest prover holding the exact batched product fails verification! -/
theorem naive_batched_matmul_incomplete :
    naiveBatchedRhs bA bB ![0] ![0] ![2] ≠ mle₃ (einsumTable bA bB) ![0] ![0] ![2] := by
  decide

/-- ...with both exact values pinned (`4` vs `2` in `ZMod 7`). -/
theorem naive_batched_matmul_values :
    naiveBatchedRhs bA bB ![0] ![0] ![2] = 4 ∧
    mle₃ (einsumTable bA bB) ![0] ![0] ![2] = 2 := by
  refine ⟨by decide, by decide⟩

/-- **Incompleteness rate**: at `xL = ![0], xR = ![0]`, the naive check rejects the HONEST
witness on **5 of the 7** batch challenges `xS ∈ F₇` (accepting only the Boolean corners
`0` and `1`). -/
theorem naive_batched_matmul_rejects_five_of_seven :
    (Finset.univ.filter fun xS : Fin 1 → ZMod 7 =>
      naiveBatchedRhs bA bB ![0] ![0] xS ≠ mle₃ (einsumTable bA bB) ![0] ![0] xS).card = 5 := by
  decide

/-- **`EinSumcheck` fixes completeness at the exact failing point `xS = ![2]`.** -/
theorem einsum_batched_matmul_complete_at_two :
    (∑ h : Fin 1 → Bool, ∑ p : Fin 1 → Bool,
      eqMle (![2] : Fin 1 → ZMod 7) (cubePt h) * rowBoundA bA ![0] h p * colBoundB bB ![0] h p)
      = mle₃ (einsumTable bA bB) ![0] ![0] ![2] := by
  decide

end NaiveBugRefutation

/-! ## §5. Theorem 3 (`einsum_is_cubicForm`, completeness, and factored terminal check) -/

section CubicReduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {μL μR μS κ : ℕ}

/-- Structured `eq` head table on `Fin (μS + κ) → Bool`: depends ONLY on the first `μS`
coordinates (`extendRight μS κ`), ignoring the `κ` summation coordinates. -/
def einsumEqTable (κ : ℕ) (xS : Fin μS → F) : (Fin (μS + κ) → Bool) → F :=
  extendRight μS κ (fun h => chiEval h xS)

/-- Flattened left partial-evaluation table on `Fin (μS + κ) → Bool`. -/
def einsumLeftTable
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) : (Fin (μS + κ) → Bool) → F :=
  flatten₂ (rowBoundA A xL)

/-- Flattened right partial-evaluation table on `Fin (μS + κ) → Bool`. -/
def einsumRightTable
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xR : Fin μR → F) : (Fin (μS + κ) → Bool) → F :=
  flatten₂ (colBoundB B xR)

omit [Fintype F] [DecidableEq F] in
/-- `mle` of `einsumEqTable κ xS` at `r : Fin (μS + κ) → F` evaluates `eqMle xS` on ONLY the
`μS`-bit prefix `rowHalf μS κ r` — zero commitment and `O(μS)` verifier arithmetic. -/
theorem mle_einsumEqTable (κ : ℕ) (xS : Fin μS → F) (r : Fin (μS + κ) → F) :
    mle (einsumEqTable κ xS) r = eqMle xS (rowHalf μS κ r) := by
  rw [einsumEqTable, mle_extendRight, ← eqMle_eq_mle xS]

omit [Fintype F] [DecidableEq F] in
/-- `mle` of `einsumLeftTable A xL` at `r` is the full 3-block MLE `Â(xL, r_S, r_κ)`. -/
theorem mle_einsumLeftTable
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (r : Fin (μS + κ) → F) :
    mle (einsumLeftTable A xL) r = mle₃ A xL (rowHalf μS κ r) (colHalf μS κ r) := by
  conv_lhs => rw [← append_rowHalf_colHalf r]
  rw [einsumLeftTable, mle_flatten₂, mle₃_as_mle₂_bind₁]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- `mle` of `einsumRightTable B xR` at `r` is the full 3-block MLE `B̂(xR, r_S, r_κ)`. -/
theorem mle_einsumRightTable
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xR : Fin μR → F) (r : Fin (μS + κ) → F) :
    mle (einsumRightTable B xR) r = mle₃ B xR (rowHalf μS κ r) (colHalf μS κ r) := by
  conv_lhs => rw [← append_rowHalf_colHalf r]
  rw [einsumRightTable, mle_flatten₂, mle₃_as_mle₂_bind₁]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- **THEOREM 3a (`einsum_is_cubicForm`).**
The `(μS + κ)`-variable `EinSumcheck` summand is an exact instance of
`AirSumcheckCubic.cubicForm` (`E = einsumEqTable κ xS`, `C ≡ 0`, `D ≡ 1`). -/
theorem einsum_is_cubicForm
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F) :
    cubicForm (einsumEqTable κ xS) (einsumLeftTable A xL) (einsumRightTable B xR)
      (fun _ => 0) (fun _ => 1)
      = fun r =>
          eqMle xS (rowHalf μS κ r)
            * (mle₃ A xL (rowHalf μS κ r) (colHalf μS κ r)
                * mle₃ B xR (rowHalf μS κ r) (colHalf μS κ r)) := by
  funext r
  rw [cubicForm, mle_einsumEqTable, mle_einsumLeftTable, mle_einsumRightTable,
    show mle (fun _ : Fin (μS + κ) → Bool => (0 : F)) = fun _ => 0 from mle_const 0,
    show mle (fun _ : Fin (μS + κ) → Bool => (1 : F)) = fun _ => 1 from mle_const 1]
  ring

/-- The hypercube total of the `EinSumcheck` cubic instance, in the syntactic shape
`cubicHonest` and `cubic_sumcheck_soundness` consume. -/
def einsumTrue
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F) : F :=
  ∑ b : Fin (μS + κ) → Bool,
    (einsumEqTable κ xS b * (einsumLeftTable A xL b * einsumRightTable B xR b + 0 * 1))

omit [Fintype F] [DecidableEq F] in
/-- **The `cubicForm` hypercube total equals `Ẑ(xL, xR, xS)` of the true Einsum output.** -/
theorem einsum_claim_total
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F) :
    einsumTrue A B xL xR xS = mle₃ (einsumTable A B) xL xR xS := by
  unfold einsumTrue
  rw [einsum_mle_identity]
  calc
    (∑ b : Fin (μS + κ) → Bool,
        (einsumEqTable κ xS b * (einsumLeftTable A xL b * einsumRightTable B xR b + 0 * 1)))
        = ∑ hp : (Fin μS → Bool) × (Fin κ → Bool),
            (einsumEqTable κ xS (Fin.append hp.1 hp.2)
              * (einsumLeftTable A xL (Fin.append hp.1 hp.2)
                  * einsumRightTable B xR (Fin.append hp.1 hp.2) + 0 * 1)) := by
          exact (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) μS κ)
            (fun hp => einsumEqTable κ xS (Fin.append hp.1 hp.2)
              * (einsumLeftTable A xL (Fin.append hp.1 hp.2)
                  * einsumRightTable B xR (Fin.append hp.1 hp.2) + 0 * 1))
            (fun b => einsumEqTable κ xS b
              * (einsumLeftTable A xL b * einsumRightTable B xR b + 0 * 1))
            (fun _ => rfl)).symm
    _ = ∑ h : Fin μS → Bool, ∑ p : Fin κ → Bool,
          eqMle xS (cubePt h) * rowBoundA A xL h p * colBoundB B xR h p := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p _ => ?_
          simp only [einsumEqTable, extendRight, rowHalf_append, einsumLeftTable,
            einsumRightTable, flatten₂_append, eqMle_cubePt]
          ring

/-- **The honest `EinSumcheck` prover**: `AirSumcheckCubic.cubicHonest` instantiated at the
`EinSumcheck` summand. Inherits prefix-measurability, degree ≤ 3, and boolean-sum consistency
without reproving a single polynomial lemma. -/
noncomputable def einsumHonest
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F) :
    (ℕ → F) → ℕ → Polynomial F :=
  cubicHonest (einsumEqTable κ xS) (einsumLeftTable A xL) (einsumRightTable B xR)
    (fun _ => 0) (fun _ => 1)

omit [Fintype F] [DecidableEq F] in
/-- **THEOREM 3b (`einsumHonest_complete`).**
For EVERY outer point `(xL, xR, xS)` and EVERY sumcheck challenge vector `r : Fin (μS + κ) → F`,
the honest `EinSumcheck` prover passes every round check and the terminal check on
`Ẑ(xL, xR, xS)`. -/
theorem einsumHonest_complete
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F)
    (r : Fin (μS + κ) → F) :
    SumcheckAccepts (v := μS + κ)
      (einsumHonest A B xL xR xS (chalOf r))
      (einsumHonest A B xL xR xS (chalOf r))
      (mle₃ (einsumTable A B) xL xR xS)
      (mle₃ (einsumTable A B) xL xR xS) r := by
  rw [← einsum_claim_total A B xL xR xS]
  exact cubicHonest_complete (einsumEqTable κ xS) (einsumLeftTable A xL)
    (einsumRightTable B xR) (fun _ => 0) (fun _ => 1) r

omit [Fintype F] [DecidableEq F] in
/-- **THEOREM 3c (`einsum_terminal_factored` — zero wiring commitments).**
After `μS + κ` rounds, `scChain` at `einsumHonest` equals

  `eqMle xS r_S * (Â(xL, r_S, r_κ) * B̂(xR, r_S, r_κ))`

where `r_S = rowHalf μS κ r` and `r_κ = colHalf μS κ r`. The verifier evaluates `eqMle xS r_S`
itself in `μS` multiplications (Lemma 3.3's structured wiring predicate) and needs only one
multilinear opening of `A` and one of `B`. -/
theorem einsum_terminal_factored
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F)
    (r : Fin (μS + κ) → F) :
    scChain (mle₃ (einsumTable A B) xL xR xS)
        (einsumHonest A B xL xR xS (chalOf r)) (chalOf r) (μS + κ)
      = eqMle xS (rowHalf μS κ r)
          * (mle₃ A xL (rowHalf μS κ r) (colHalf μS κ r)
              * mle₃ B xR (rowHalf μS κ r) (colHalf μS κ r)) := by
  rw [← einsum_claim_total A B xL xR xS, einsumTrue, einsumHonest,
    scChain_cubicHonest_final]
  exact congrFun (einsum_is_cubicForm A B xL xR xS) r

omit [Fintype F] [DecidableEq F] in
/-- **THEOREM 3d (`einsum_asymmetric_terminal_factored` — unequal summation variable counts).**
When `A₀` carries left-only + shared summation bits `κL + κM` (ignoring `κR`) and `B₀` carries
shared + right-only summation bits `κM + κR` (ignoring `κL`) over total summation cube
`κ = (κL + κM) + κR`, suffix/projection MLE invariance (`mle_extendRight` / `mle_extendLeft`)
projects the terminal oracle openings onto each operand's native variable count:

  `eqMle xS r_S * (Â₀(xL, r_S, (r_κL, r_κM)) * B̂₀(xR, r_S, (r_κM, r_κR)))`. -/
theorem einsum_asymmetric_terminal_factored {κL κM κR : ℕ}
    (A₀ : (Fin μL → Bool) → (Fin μS → Bool) → (Fin (κL + κM) → Bool) → F)
    (B₀ : (Fin μR → Bool) → (Fin μS → Bool) → (Fin (κM + κR) → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F)
    (r : Fin (μS + ((κL + κM) + κR)) → F) :
    let liftA : (Fin μL → Bool) → (Fin μS → Bool) → (Fin ((κL + κM) + κR) → Bool) → F :=
      fun aL h p => A₀ aL h (rowHalf (κL + κM) κR p)
    let liftB : (Fin μR → Bool) → (Fin μS → Bool) → (Fin ((κL + κM) + κR) → Bool) → F :=
      fun aR h p =>
        B₀ aR h (Fin.append (colHalf κL κM (rowHalf (κL + κM) κR p)) (colHalf (κL + κM) κR p))
    let rS := rowHalf μS ((κL + κM) + κR) r
    let rκ := colHalf μS ((κL + κM) + κR) r
    let rκ1 := rowHalf (κL + κM) κR rκ
    let rκ2 := Fin.append (colHalf κL κM rκ1) (colHalf (κL + κM) κR rκ)
    scChain (mle₃ (einsumTable liftA liftB) xL xR xS)
        (einsumHonest liftA liftB xL xR xS (chalOf r)) (chalOf r) (μS + ((κL + κM) + κR))
      = eqMle xS rS * (mle₃ A₀ xL rS rκ1 * mle₃ B₀ xR rS rκ2) := by
  intro liftA liftB rS rκ rκ1 rκ2
  rw [einsum_terminal_factored]
  congr 2
  · exact mle₃_extendRight_thd A₀ xL rS rκ
  · -- For `liftB`, split `(κL + κM) + κR` by peeling `κL` on the left via `mle_extendLeft`.
    rw [mle₃_as_mle_slice₃, mle₃_as_mle_slice₃]
    have hB : ∀ p : Fin ((κL + κM) + κR) → Bool,
        slice₃ liftB xR rS p
          = slice₃ B₀ xR rS
              (Fin.append (colHalf κL κM (rowHalf (κL + κM) κR p)) (colHalf (κL + κM) κR p)) :=
      fun _ => rfl
    have hEq : mle (slice₃ liftB xR rS) rκ = mle (slice₃ B₀ xR rS) rκ2 := by
      -- Re-associate `rκ : Fin ((κL + κM) + κR) → F` as `Fin.append rκL rκ2`.
      let rκL : Fin κL → F := rowHalf κL κM rκ1
      have hrκ : rκ = Fin.append (Fin.append rκL (colHalf κL κM rκ1)) (colHalf (κL + κM) κR rκ) := by
        calc rκ
            = Fin.append rκ1 (colHalf (κL + κM) κR rκ) := (append_rowHalf_colHalf rκ).symm
          _ = Fin.append (Fin.append rκL (colHalf κL κM rκ1)) (colHalf (κL + κM) κR rκ) := by
              rw [append_rowHalf_colHalf rκ1]
      -- Prove by evaluating the chi-basis sum over `(pL, pM, pR)`.
      rw [mle]
      calc
        (∑ p : Fin ((κL + κM) + κR) → Bool, slice₃ liftB xR rS p * chiEval p rκ)
            = ∑ q : (Fin (κL + κM) → Bool) × (Fin κR → Bool),
                slice₃ liftB xR rS (Fin.append q.1 q.2)
                  * chiEval (Fin.append q.1 q.2) rκ := by
              exact (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) (κL + κM) κR)
                (fun q => slice₃ liftB xR rS (Fin.append q.1 q.2)
                  * chiEval (Fin.append q.1 q.2) rκ)
                (fun p => slice₃ liftB xR rS p * chiEval p rκ)
                (fun _ => rfl)).symm
        _ = ∑ q₁ : Fin (κL + κM) → Bool, ∑ pR : Fin κR → Bool,
              slice₃ B₀ xR rS (Fin.append (colHalf κL κM q₁) pR)
                * (chiEval q₁ rκ1 * chiEval pR (colHalf (κL + κM) κR rκ)) := by
              rw [Fintype.sum_prod_type]
              refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun pR _ => ?_
              rw [hB, chiEval_split, rowHalf_append, colHalf_append]
        _ = ∑ u : (Fin κL → Bool) × (Fin κM → Bool), ∑ pR : Fin κR → Bool,
              slice₃ B₀ xR rS (Fin.append (colHalf κL κM (Fin.append u.1 u.2)) pR)
                * (chiEval (Fin.append u.1 u.2) rκ1
                    * chiEval pR (colHalf (κL + κM) κR rκ)) := by
              exact (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) κL κM)
                (fun u => ∑ pR : Fin κR → Bool,
                  slice₃ B₀ xR rS (Fin.append (colHalf κL κM (Fin.append u.1 u.2)) pR)
                    * (chiEval (Fin.append u.1 u.2) rκ1
                        * chiEval pR (colHalf (κL + κM) κR rκ)))
                (fun q₁ => ∑ pR : Fin κR → Bool,
                  slice₃ B₀ xR rS (Fin.append (colHalf κL κM q₁) pR)
                    * (chiEval q₁ rκ1 * chiEval pR (colHalf (κL + κM) κR rκ)))
                (fun _ => rfl)).symm
        _ = (∑ pL : Fin κL → Bool, chiEval pL rκL)
              * ∑ pM : Fin κM → Bool, ∑ pR : Fin κR → Bool,
                  slice₃ B₀ xR rS (Fin.append pM pR)
                    * (chiEval pM (colHalf κL κM rκ1)
                        * chiEval pR (colHalf (κL + κM) κR rκ)) := by
              rw [Fintype.sum_prod_type, Finset.sum_mul]
              refine Finset.sum_congr rfl fun pL _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun pM _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun pR _ => ?_
              rw [chiEval_split, rowHalf_append, colHalf_append]
              ring
        _ = mle (slice₃ B₀ xR rS) rκ2 := by
              rw [sum_chiEval_eq_one, one_mul, mle]
              symm
              calc
                (∑ p₂ : Fin (κM + κR) → Bool, slice₃ B₀ xR rS p₂ * chiEval p₂ rκ2)
                    = ∑ v : (Fin κM → Bool) × (Fin κR → Bool),
                        slice₃ B₀ xR rS (Fin.append v.1 v.2)
                          * chiEval (Fin.append v.1 v.2) rκ2 := by
                      exact (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) κM κR)
                        (fun v => slice₃ B₀ xR rS (Fin.append v.1 v.2)
                          * chiEval (Fin.append v.1 v.2) rκ2)
                        (fun p₂ => slice₃ B₀ xR rS p₂ * chiEval p₂ rκ2)
                        (fun _ => rfl)).symm
                _ = ∑ pM : Fin κM → Bool, ∑ pR : Fin κR → Bool,
                      slice₃ B₀ xR rS (Fin.append pM pR)
                        * (chiEval pM (colHalf κL κM rκ1)
                            * chiEval pR (colHalf (κL + κM) κR rκ)) := by
                      rw [Fintype.sum_prod_type]
                      refine Finset.sum_congr rfl fun pM _ => Finset.sum_congr rfl fun pR _ => ?_
                      rw [chiEval_split, rowHalf_append, colHalf_append,
                        rowHalf_append, colHalf_append]
    exact hEq

omit [Fintype F] [DecidableEq F] in
/-- **`zkTransformer` Appendix F Eq. (10) canonical form (`canonicalEq10_terminal_factored`).**
For `H = ∑_{x,y,z} eq(r_eq, x) · T₁(x, y) · T₂(x, y, z)` with `x : Fin ℓ → Bool`,
`y : Fin μ → Bool`, `z : Fin η → Bool`, running `cubicHonest` on `((ℓ + μ) + η)` variables
reduces directly to `eqMle r_eq r_x * (T̂₁(r_x, r_y) * T̂₂(r_x, r_y, r_z))`. -/
theorem canonicalEq10_terminal_factored {ℓ μ η : ℕ}
    (r_eq : Fin ℓ → F)
    (T₁ : (Fin (ℓ + μ) → Bool) → F)
    (T₂ : (Fin ((ℓ + μ) + η) → Bool) → F)
    (r : Fin ((ℓ + μ) + η) → F) :
    let E := extendRight (ℓ + μ) η (extendRight ℓ μ (fun x => chiEval x r_eq))
    let A := extendRight (ℓ + μ) η T₁
    let S := ∑ b : Fin ((ℓ + μ) + η) → Bool, (E b * (A b * T₂ b + 0 * 1))
    let r_xy := rowHalf (ℓ + μ) η r
    let r_x := rowHalf ℓ μ r_xy
    scChain S (cubicHonest E A T₂ (fun _ => 0) (fun _ => 1) (chalOf r))
        (chalOf r) ((ℓ + μ) + η)
      = eqMle r_eq r_x * (mle T₁ r_xy * mle T₂ r) := by
  intro E A S r_xy r_x
  rw [scChain_cubicHonest_final]
  have hE : mle E r = eqMle r_eq r_x := by
    rw [mle_extendRight, mle_extendRight, ← eqMle_eq_mle r_eq]
  have hA : mle A r = mle T₁ r_xy := mle_extendRight T₁ r
  rw [hE, hA,
    show mle (fun _ : Fin ((ℓ + μ) + η) → Bool => (0 : F)) = fun _ => 0 from mle_const 0,
    show mle (fun _ : Fin ((ℓ + μ) + η) → Bool => (1 : F)) = fun _ => 1 from mle_const 1]
  ring

/-- **The deployed verifier predicate (`EinsumRealAccepts` — no honest side).**
Following `Assurance/SpartanR1CS.lean`'s `SpartanOuterRealAccepts` discipline: a real succinct
verifier holds no tables and no `einsumHonest`; it checks the boolean sums from the claimed output
opening `vZ` and checks the final folded value against `eqMle xS r_S * (vA * vB)` computed from
its own randomness and the two claimed input openings `(vA, vB)`. -/
def EinsumRealAccepts (xS : Fin μS → F) (r : Fin (μS + κ) → F)
    (prover : ℕ → Polynomial F) (vZ vA vB : F) : Prop :=
  (∀ i, i < μS + κ → (prover i).eval 0 + (prover i).eval 1 = scChain vZ prover (chalOf r) i)
    ∧ scChain vZ prover (chalOf r) (μS + κ) = eqMle xS (rowHalf μS κ r) * (vA * vB)

omit [Fintype F] [DecidableEq F] in
/-- **Idealization discharged (`einsumReal_iff_sumcheckAccepts`).**
When the three openings `(vZ, vA, vB)` are authentic (bound by PCS evaluation claims on
`flatten₃ Z`, `flatten₃ A`, `flatten₃ B`), the deployed verifier `EinsumRealAccepts` coincides
with `SumcheckAccepts` against `einsumHonest`. -/
theorem einsumReal_iff_sumcheckAccepts
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (Z : (Fin μL → Bool) → (Fin μR → Bool) → (Fin μS → Bool) → F)
    (xL : Fin μL → F) (xR : Fin μR → F) (xS : Fin μS → F)
    (r : Fin (μS + κ) → F) (prover : ℕ → Polynomial F)
    {vZ vA vB : F}
    (hZ : vZ = mle₃ Z xL xR xS)
    (hA : vA = mle₃ A xL (rowHalf μS κ r) (colHalf μS κ r))
    (hB : vB = mle₃ B xR (rowHalf μS κ r) (colHalf μS κ r)) :
    EinsumRealAccepts xS r prover vZ vA vB ↔
      SumcheckAccepts (v := μS + κ) prover
        (einsumHonest A B xL xR xS (chalOf r))
        (mle₃ Z xL xR xS) (einsumTrue A B xL xR xS) r := by
  subst hZ; subst hA; subst hB
  unfold EinsumRealAccepts SumcheckAccepts
  rw [einsum_claim_total A B xL xR xS, einsum_terminal_factored]

end CubicReduction

/-! ## §6. Theorem 4 (`einsumcheck_soundness` — fixing `zkTransformer` Lemma 3.2) -/

section Soundness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {μL μR μS κ : ℕ}

/-- Full two-stage `EinSumcheck` acceptance event:
1. Verifier draws outer evaluation point `o = (xL, xR, xS) : OuterChal μL μR μS F`;
2. Adaptive prover (which may inspect `o` before choosing its sumcheck polynomials `prover o`)
   runs the `(μS + κ)`-round cubic sumcheck claiming `Ẑ(xL, xR, xS)` against the honest
   terminal target `einsumTrue A B xL xR xS`. -/
def EinSumcheckAccepts
    (A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F)
    (Z : (Fin μL → Bool) → (Fin μR → Bool) → (Fin μS → Bool) → F)
    (prover : OuterChal μL μR μS F → (ℕ → F) → ℕ → Polynomial F)
    (w : OuterChal μL μR μS F × (Fin (μS + κ) → F)) : Prop :=
  SumcheckAccepts (v := μS + κ)
    (prover w.1 (chalOf w.2))
    (einsumHonest A B w.1.1 w.1.2.1 w.1.2.2 (chalOf w.2))
    (mle₃ Z w.1.1 w.1.2.1 w.1.2.2)
    (einsumTrue A B w.1.1 w.1.2.1 w.1.2.2) w.2

/-- **THEOREM 4 (`einsumcheck_soundness` — fixing `zkTransformer` Lemma 3.2).**
For any claimed output table `Z ≠ einsumTable A B` and any adaptive degree-≤3 prover `prover`
(even one choosing round messages adaptively after seeing the outer challenge `(xL, xR, xS)`),

  `Pr[EinSumcheckAccepts] ≤ (μL + μR + μS) / |F| + (μS + κ) * (3 / |F|)`.

The first term `(μL + μR + μS) / |F|` is the 3-block multilinear Schwartz–Zippel probability
that `(xL, xR, xS)` fails to separate `Z` from `einsumTable A B` — omitted from `zkTransformer`
Lemma 3.2. The second term `(μS + κ) * (3 / |F|)` is the exact degree-3 sumcheck soundness
bound over the `μS + κ` summed variables. -/
theorem einsumcheck_soundness
    {A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F}
    {B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F}
    {Z : (Fin μL → Bool) → (Fin μR → Bool) → (Fin μS → Bool) → F}
    (hZ : Z ≠ einsumTable A B)
    {prover : OuterChal μL μR μS F → (ℕ → F) → ℕ → Polynomial F}
    (hpm : ∀ o, PrefixMeasurable (prover o))
    (hdeg : ∀ (o : OuterChal μL μR μS F) (χ : ℕ → F) (i : ℕ), i < μS + κ →
      (prover o χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (OuterChal μL μR μS F × (Fin (μS + κ) → F))
        (EinSumcheckAccepts A B Z prover)
      ≤ ((μL : ℝ) + μR + μS) / Fintype.card F + ((μS + κ : ℕ) : ℝ) * (3 / Fintype.card F) := by
  have hD : (fun aL aR h => Z aL aR h - einsumTable A B aL aR h) ≠ 0 := by
    intro h0
    refine hZ (funext fun aL => funext fun aR => funext fun h => ?_)
    have hab : Z aL aR h - einsumTable A B aL aR h = 0 := by
      simpa using congrFun (congrFun (congrFun h0 aL) aR) h
    exact sub_eq_zero.mp hab
  have hgap : ∀ o : OuterChal μL μR μS F,
      mle₃ Z o.1 o.2.1 o.2.2 - einsumTrue A B o.1 o.2.1 o.2.2
        = mle₃ (fun aL aR h => Z aL aR h - einsumTable A B aL aR h) o.1 o.2.1 o.2.2 := by
    intro o
    rw [mle₃_sub, einsum_claim_total]
  have hstep : ∀ w : OuterChal μL μR μS F × (Fin (μS + κ) → F),
      EinSumcheckAccepts A B Z prover w →
        (mle₃ (fun aL aR h => Z aL aR h - einsumTable A B aL aR h) w.1.1 w.1.2.1 w.1.2.2 = 0
          ∨ AdaptiveAcceptsFalse (prover w.1)
              (einsumHonest A B w.1.1 w.1.2.1 w.1.2.2)
              (mle₃ Z w.1.1 w.1.2.1 w.1.2.2)
              (einsumTrue A B w.1.1 w.1.2.1 w.1.2.2) w.2) := by
    intro w hw
    by_cases hEq : mle₃ Z w.1.1 w.1.2.1 w.1.2.2 = einsumTrue A B w.1.1 w.1.2.1 w.1.2.2
    · exact Or.inl (by rw [← hgap, hEq, sub_self])
    · exact Or.inr (acceptsFalse_iff_accepts.mpr ⟨hw, hEq⟩)
  refine le_trans (uniformProb_mono hstep) ?_
  refine le_trans (uniformProb_or_le _ _) (add_le_add ?_ ?_)
  · exact uniformProb_fst_le _
      (fun o : OuterChal μL μR μS F =>
        mle₃ (fun aL aR h => Z aL aR h - einsumTable A B aL aR h) o.1 o.2.1 o.2.2 = 0)
      (fun _ => Iff.rfl) (by positivity) (mle₃_zero_uniform_bound hD)
  · refine uniformProb_prod_le (by positivity) fun o => ?_
    show uniformProb (Fin (μS + κ) → F)
      (fun r => AdaptiveAcceptsFalse (prover o)
        (einsumHonest A B o.1 o.2.1 o.2.2)
        (mle₃ Z o.1 o.2.1 o.2.2) (einsumTrue A B o.1 o.2.1 o.2.2) r) ≤ _
    exact cubic_sumcheck_soundness
      (E := einsumEqTable κ o.2.2)
      (A := einsumLeftTable A o.1)
      (B := einsumRightTable B o.2.1)
      (C := fun _ => 0) (D := fun _ => 1)
      (hpm o) (hdeg o)

/-- Specialization of `einsumcheck_soundness` to an outer-independent prover family. -/
theorem einsumcheck_soundness_fixedOuter
    {A : (Fin μL → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F}
    {B : (Fin μR → Bool) → (Fin μS → Bool) → (Fin κ → Bool) → F}
    {Z : (Fin μL → Bool) → (Fin μR → Bool) → (Fin μS → Bool) → F}
    (hZ : Z ≠ einsumTable A B)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < μS + κ →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (OuterChal μL μR μS F × (Fin (μS + κ) → F))
        (EinSumcheckAccepts A B Z (fun _ => prover))
      ≤ ((μL : ℝ) + μR + μS) / Fintype.card F + ((μS + κ : ℕ) : ℝ) * (3 / Fintype.card F) :=
  einsumcheck_soundness hZ (fun _ => hpm) (fun _ => hdeg)

end Soundness

/-! ## §6b. Constructive soundness teeth over `ZMod 7` (`einsum_forged_survives`) -/

namespace SoundnessTeeth

open NaiveBugRefutation

/-- A forged batched-matmul output table over `ZMod 7` (`μL = 1, μR = 1, μS = 1, κ = 1`):
bumps the `(false, false, false)` entry of `einsumTable bA bB` by `1`, giving defect MLE
`(1 - xL₀)(1 - xR₀)(1 - xS₀)`. -/
def einsumForged : (Fin 1 → Bool) → (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7 :=
  fun aL aR h => einsumTable bA bB aL aR h + (if aL 0 || aR 0 || h 0 then 0 else 1)

/-- The forged output table genuinely differs from `einsumTable bA bB`. -/
theorem einsumForged_ne : einsumForged ≠ einsumTable bA bB := by
  intro h
  have := congrFun (congrFun (congrFun h (fun _ => false)) (fun _ => false)) (fun _ => false)
  revert this
  decide

/-- At `o = (![0], ![0], ![0])`, the outer random evaluation separates `einsumForged` (`1 ≠ 0`). -/
theorem einsum_forged_caught :
    mle₃ einsumForged ![0] ![0] ![0] ≠ mle₃ (einsumTable bA bB) ![0] ![0] ![0] := by
  decide

/-- **CONSTRUCTIVE TOOTH (`einsum_forged_survives` — `zkTransformer` Lemma 3.2's omitted event
is NONEMPTY).** At `xL = ![1], xR = ![3], xS = ![2]`, `einsumForged` and `einsumTable bA bB`
have the EXACT SAME 3-block MLE (`0 = 0`), even though `einsumForged ≠ einsumTable bA bB`! -/
theorem einsum_forged_survives :
    mle₃ einsumForged ![1] ![3] ![2] = mle₃ (einsumTable bA bB) ![1] ![3] ![2] := by
  decide

/-- **END-TO-END PROTOCOL SURVIVAL.** When the outer draw hits `o = (![1], ![3], ![2])`,
running the HONEST sumcheck prover `einsumHonest` causes `EinSumcheckAccepts` to accept the
FORGED table `einsumForged` for **100% of sumcheck challenges `r`**! Without the outer
`(μL + μR + μS)/|F|` term in `einsumcheck_soundness`, no sound bound on `EinSumcheckAccepts`
can hold (for instance at `μS = 0, κ = 0`, Lemma 3.2's inner sumcheck term is `0` while the
forged table still survives with positive probability). -/
theorem einsum_forged_accepts_end_to_end (r : Fin (1 + 1) → ZMod 7) :
    EinSumcheckAccepts bA bB einsumForged
      (fun o => einsumHonest bA bB o.1 o.2.1 o.2.2)
      ((![1], ![3], ![2]), r) := by
  unfold EinSumcheckAccepts
  dsimp only
  rw [einsum_forged_survives, einsum_claim_total]
  exact einsumHonest_complete bA bB ![1] ![3] ![2] r

/-- **Secondary Lemma 3.2 defect (`lemma32_v_not_upper_bound_on_rounds`).**
In `bp,bq->b` (`μL = 0, μR = 0, μS = 1, κL = 2, κM = 0, κR = 2`), operand `A(b, p)` has
`v_A = 1 + 2 = 3` variables and operand `B(b, q)` has `v_B = 1 + 2 = 3` variables, so
`v = max(v_A, v_B) = 3`. Yet `EinSumcheck` sums over `μS + (κL + κR) = 5` variables (`15/|F|`
vs Lemma 3.2's `9/|F|`), proving `v = max_t |I_t|` is not even an upper bound on the inner
sumcheck round count when operands have disjoint summation indices. -/
theorem lemma32_v_not_upper_bound_on_rounds :
    let μS := 1
    let κL := 2
    let κR := 2
    let v := max (μS + κL) (μS + κR)
    let actualRounds := μS + (κL + κR)
    v = 3 ∧ actualRounds = 5 ∧ v < actualRounds ∧ 3 * v < 3 * actualRounds := by
  decide

end SoundnessTeeth

/-! ## §7. Theorem 5 (`gqa_rounds_saved` — Grouped-Query Attention `igrc,jgc->grij`) -/

section GQA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Cube-indexed GQA attention-score table (`igrc,jgc->grij`):
* `Q` has left-only free block `Fin (μG + μI) → Bool` (packing query-in-group `r` and
  query-pos `i`), shared free KV-group `Fin μKV → Bool`, and head-dim `Fin μC → Bool`;
* `K` has right-only free key-pos `Fin μJ → Bool`, shared free KV-group `Fin μKV → Bool`,
  and head-dim `Fin μC → Bool` — **never duplicated across `2^μG`**. -/
def gqaCubeScores {μI μJ μKV μG μC : ℕ}
    (Q : (Fin (μG + μI) → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F)
    (K : (Fin μJ → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F) :
    (Fin (μG + μI) → Bool) → (Fin μJ → Bool) → (Fin μKV → Bool) → F :=
  einsumTable Q K

/-- Naive `repeat_kv` broadcast of `K` onto all `H = 2^(μKV + μG)` query heads, turning GQA
into standard `H`-head batched matmul `(g,r)ic, (g,r)jc -> (g,r)ij`. -/
def repeatKV {μJ μKV μG μC : ℕ}
    (K : (Fin μJ → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F) :
    (Fin μJ → Bool) → (Fin (μKV + μG) → Bool) → (Fin μC → Bool) → F :=
  fun j gr c => K j (rowHalf μKV μG gr) c

/-- Re-indexed `Q` for the naive `repeat_kv` batched-matmul layout. -/
def gqaBatchedQ {μI μKV μG μC : ℕ}
    (Q : (Fin (μG + μI) → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F) :
    (Fin μI → Bool) → (Fin (μKV + μG) → Bool) → (Fin μC → Bool) → F :=
  fun i gr c => Q (Fin.append (colHalf μKV μG gr) i) (rowHalf μKV μG gr) c

omit [Fintype F] [DecidableEq F] in
/-- **Semantic equivalence (`repeatKV_einsum_agrees`).** Native `EinSumcheck` GQA
(`gqaCubeScores Q K`) computes the exact same attention scores as the naive `repeat_kv`
batched matmul at every `(g, r, i, j)`. -/
theorem repeatKV_einsum_agrees {μI μJ μKV μG μC : ℕ}
    (Q : (Fin (μG + μI) → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F)
    (K : (Fin μJ → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F)
    (g : Fin μKV → Bool) (r : Fin μG → Bool) (i : Fin μI → Bool) (j : Fin μJ → Bool) :
    gqaCubeScores Q K (Fin.append r i) j g
      = einsumTable (gqaBatchedQ Q) (repeatKV K) i j (Fin.append g r) := by
  simp [gqaCubeScores, einsumTable, gqaBatchedQ, repeatKV]

/-- **GQA two-term soundness (`gqa_einsumcheck_soundness`).** Native `EinSumcheck` proves GQA
scores in `μKV + μC` rounds (independent of the group multiplier `μG`!), with `μG` appearing
ONLY in the cheap outer 1-point evaluation bound `((μG + μI) + μJ + μKV) / |F|`. -/
theorem gqa_einsumcheck_soundness {μI μJ μKV μG μC : ℕ}
    {Q : (Fin (μG + μI) → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F}
    {K : (Fin μJ → Bool) → (Fin μKV → Bool) → (Fin μC → Bool) → F}
    {Z : (Fin (μG + μI) → Bool) → (Fin μJ → Bool) → (Fin μKV → Bool) → F}
    (hZ : Z ≠ gqaCubeScores Q K)
    {prover : OuterChal (μG + μI) μJ μKV F → (ℕ → F) → ℕ → Polynomial F}
    (hpm : ∀ o, PrefixMeasurable (prover o))
    (hdeg : ∀ o χ k, k < μKV + μC →
      (prover o χ k).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (OuterChal (μG + μI) μJ μKV F × (Fin (μKV + μC) → F))
        (EinSumcheckAccepts Q K Z prover)
      ≤ (((μG + μI : ℕ) : ℝ) + μJ + μKV) / Fintype.card F
          + ((μKV + μC : ℕ) : ℝ) * (3 / Fintype.card F) :=
  einsumcheck_soundness hZ hpm hdeg

/-- Sumcheck round count of native `EinSumcheck` on GQA (`igrc,jgc->grij`). -/
def gqaNativeRounds (μKV μC : ℕ) : ℕ := μKV + μC

/-- Sumcheck round count of naive `repeat_kv` batched matmul (`(g,r)ic,(g,r)jc->(g,r)ij`). -/
def gqaRepeatKvRounds (μKV μG μC : ℕ) : ℕ := (μKV + μG) + μC

/-- **THEOREM 5 (`gqa_rounds_saved`).**
Placing the GQA query-group multiplier `G = 2^μG` (`H = KV * G`) in left-only free `μL`
rather than shared free `μS`:
1. saves exactly `μG = log₂ G` degree-3 sumcheck rounds (`gqaNativeRounds < gqaRepeatKvRounds`
   whenever `0 < μG`), and
2. shrinks the committed `K`-table hypercube domain by an exact factor of `2^μG = G`
   (`Fintype.card` of `repeatKV`'s index cube is `2^μG` times `K`'s native index cube). -/
theorem gqa_rounds_saved (μJ μKV μG μC : ℕ) :
    gqaRepeatKvRounds μKV μG μC - gqaNativeRounds μKV μC = μG
      ∧ (0 < μG → gqaNativeRounds μKV μC < gqaRepeatKvRounds μKV μG μC)
      ∧ Fintype.card ((Fin μJ → Bool) × (Fin (μKV + μG) → Bool) × (Fin μC → Bool))
          = 2 ^ μG * Fintype.card ((Fin μJ → Bool) × (Fin μKV → Bool) × (Fin μC → Bool)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gqaRepeatKvRounds gqaNativeRounds; omega
  · intro hpos; unfold gqaRepeatKvRounds gqaNativeRounds; omega
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      pow_add]
    ring

/-- **Concrete `gpt-oss-20b` GQA instantiation (`KV = 8 = 2^3`, `G = 8 = 2^3` so `H = 64 = 2^6`,
`HD = 64 = 2^6`, `S = 1024 = 2^10`).** Native `EinSumcheck` runs **9** rounds instead of **12**
per attention contraction and commits **524,288** `K` felts instead of **4,194,304** (`8×` smaller). -/
theorem gptoss_20b_gqa_savings :
    gqaNativeRounds 3 6 = 9
      ∧ gqaRepeatKvRounds 3 3 6 = 12
      ∧ Fintype.card ((Fin 10 → Bool) × (Fin 3 → Bool) × (Fin 6 → Bool)) = 524288
      ∧ Fintype.card ((Fin 10 → Bool) × (Fin (3 + 3) → Bool) × (Fin 6 → Bool)) = 4194304 := by
  refine ⟨rfl, rfl, by norm_num, by norm_num⟩

end GQA

/-! ## §8. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.mle_extendRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_extendRight
/-- info: 'Minidregg.Assurance.mle_extendLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_extendLeft
/-- info: 'Minidregg.Assurance.mle₂_ignore_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_ignore_snd
/-- info: 'Minidregg.Assurance.mle₂_ignore_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_ignore_fst
/-- info: 'Minidregg.Assurance.mle₃_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₃_agrees
/-- info: 'Minidregg.Assurance.mle_flatten₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_flatten₃
/-- info: 'Minidregg.Assurance.mle₃_zero_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₃_zero_uniform_bound
/-- info: 'Minidregg.Assurance.einsum_mle_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_mle_identity
/-- info: 'Minidregg.Assurance.einsum_zero_shared_is_matmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_zero_shared_is_matmul
/-- info: 'Minidregg.Assurance.NaiveBugRefutation.naive_batched_matmul_agrees_on_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NaiveBugRefutation.naive_batched_matmul_agrees_on_cube
/-- info: 'Minidregg.Assurance.NaiveBugRefutation.naive_batched_matmul_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NaiveBugRefutation.naive_batched_matmul_incomplete
/-- info: 'Minidregg.Assurance.NaiveBugRefutation.naive_batched_matmul_rejects_five_of_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NaiveBugRefutation.naive_batched_matmul_rejects_five_of_seven
/-- info: 'Minidregg.Assurance.einsum_is_cubicForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_is_cubicForm
/-- info: 'Minidregg.Assurance.einsum_claim_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_claim_total
/-- info: 'Minidregg.Assurance.einsumHonest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumHonest_complete
/-- info: 'Minidregg.Assurance.einsum_terminal_factored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_terminal_factored
/-- info: 'Minidregg.Assurance.einsum_asymmetric_terminal_factored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsum_asymmetric_terminal_factored
/-- info: 'Minidregg.Assurance.canonicalEq10_terminal_factored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalEq10_terminal_factored
/-- info: 'Minidregg.Assurance.einsumReal_iff_sumcheckAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumReal_iff_sumcheckAccepts
/-- info: 'Minidregg.Assurance.einsumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumcheck_soundness
/-- info: 'Minidregg.Assurance.einsumcheck_soundness_fixedOuter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms einsumcheck_soundness_fixedOuter
/-- info: 'Minidregg.Assurance.SoundnessTeeth.einsum_forged_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SoundnessTeeth.einsum_forged_survives
/-- info: 'Minidregg.Assurance.SoundnessTeeth.einsum_forged_accepts_end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SoundnessTeeth.einsum_forged_accepts_end_to_end
/-- info: 'Minidregg.Assurance.SoundnessTeeth.lemma32_v_not_upper_bound_on_rounds' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms SoundnessTeeth.lemma32_v_not_upper_bound_on_rounds
/-- info: 'Minidregg.Assurance.repeatKV_einsum_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeatKV_einsum_agrees
/-- info: 'Minidregg.Assurance.gqa_einsumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gqa_einsumcheck_soundness
/-- info: 'Minidregg.Assurance.gqa_rounds_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gqa_rounds_saved
/-- info: 'Minidregg.Assurance.gptoss_20b_gqa_savings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gptoss_20b_gqa_savings

end Minidregg.Assurance
