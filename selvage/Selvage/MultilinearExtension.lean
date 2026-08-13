/-
# Selvage.MultilinearExtension — the MLE realizer for `[SC-reshape]`.

`Selvage/SumcheckReduction.lean` closed the claim-OBJECT half of `[SC-reshape]`
(`constraint_as_hypercube_sum`) and packaged the adaptive protocol shape
(`adaptive_sumcheck_soundness`), naming ONE residual: the honest-prover
REALIZER — WHIR Def 4.5's multilinear extension `f̂`, the round polynomials
`gᵢ(X) = Σ_{b ∈ {0,1}^{m−i−1}} f̂(r₀,…,r_{i−1}, X, b)`, and the final oracle
check `f̂(r)`. This file BUILDS that realizer and plugs it in.

**What is proved here (no `sorry`, statement-first, keystones BUILT):**

* `mle` — the multilinear extension `f̂(x) = Σ_b f(b)·χ_b(x)` in the chi/eq
  basis `χ_b(x) = ∏ᵢ (if bᵢ then xᵢ else 1−xᵢ)`.
* `mle_agrees` — **agreement**: `f̂` interpolates `f` at every cube corner
  (`chiEval_cubePt`: the chi basis is the corner indicator). `mle_injective`
  follows: the extension determines the table.
* `mle_multilinear` — **multilinearity**: `f̂` is affine (degree ≤ 1) in every
  coordinate (`AffineInCoord`/`MultiAffine`, the two-point interpolation
  `g(x[i↦t]) = (1−t)·g(x[i↦0]) + t·g(x[i↦1])`). NOTE mathlib's
  `MultilinearMap` is the LINEAR notion (forces `g(x[i↦0]) = 0`), which the
  MLE does NOT satisfy — multi-AFFINE is the correct vocabulary, so nothing
  is reused there; the `Finset.sum`/`Function.update` toolkit is.
* `multiAffine_eq_mle` / `multiAffine_ext` — **uniqueness**: any multi-affine
  function IS the MLE of its cube restriction (coordinate-releasing induction
  over a `Finset`), so two multi-affine functions agreeing on the cube are
  equal. The MLE is THE multilinear interpolant.
* `mle_hypercube_sum` — the sum-claim transported: `Σ_b f(b) = Σ_b f̂(corner b)`.
* **The round-polynomial engine**: `roundSum g r i t` = challenges below `i`,
  the running variable at `i`, boolean corners above `i` — WHIR's `gᵢ`.
  `roundSum_affine` (degree ≤ 1 in `t`, from multilinearity), `roundSum_zero`
  (`g₀(0)+g₀(1)` = the full hypercube sum), `roundSum_succ` (the chain identity
  `g_{k+1}(0)+g_{k+1}(1) = g_k(r_k)` — pure sum-splitting via `suffixSplit`,
  no multilinearity needed), `roundSum_last` (the last fold IS the full
  evaluation), `roundSum_congr_prefix` (round `i` reads challenges only
  below `i`).
* **`[SC-reshape]`'s `hHonest`, DISCHARGED** — `mleHonest f` packages the
  round polynomials (`roundPoly`, an actual degree-≤1 `Polynomial F`) as the
  `(ℕ → F) → ℕ → Polynomial F` family the ADAPTIVE theorems consume:
  `mleHonest_prefixMeasurable` + `mleHonest_degree` (d = 1) +
  `mleHonest_boolean_sum` (the honest boolean-sum consistency along the truth
  chain anchored at `Σ_b f(b)`) + `scChain_mleHonest_final` (the truth chain
  ends at `f̂(r)` — the final oracle check realized). `mleHonest_complete`:
  the honest run is accepted on EVERY challenge.
* `mle_sumcheck_soundness` / `mle_retires_constraint` — the realizer CONSUMED:
  `adaptive_sumcheck_soundness` / `adaptive_sumcheck_retires_constraint`
  instantiated at `mleHonest`, closing the bound `≤ m·1/|F|` against any
  admissible prover; for a `LinearConstraint` the honest family is the MLE of
  the transported summand `b ↦ wt(e⁻¹b)·f(e⁻¹b)` — the turnkey decider
  sumcheck with a BUILT honest side (only adversary-side hypotheses remain,
  as they must).

**Keystones (ATLAS: satisfiable + teeth, BUILT over F₅, m = 2, the AND gate):**
`mle_and_agrees` (all four corners, computed); `mle_and_closed_form` — the
uniqueness theorem FIRES to produce `f̂_AND = x₀·x₁` (both sides multi-affine
+ agree on the cube, by `decide`); `mle_and_offcube` (`f̂(2,3) = 1`: a genuine
extension, not a table); teeth: `mle_and_ne_or` (different tables ⇒ different
MLEs), `mle_and_affine_fires` (the interpolation computed at an off-cube
point), `square_not_affine` (`x₀²` refutes `AffineInCoord` — multilinearity is
a constraint, not a tautology), the round chain computed
(`roundSum_and_chain0/1`, `roundSum_and_final` = the oracle check `f̂(2,3)`),
and the soundness pipeline END-TO-END: `cheat_caught` (a cheating prover
against the honest MLE family, `≤ 2/5`) with `cheat_accept_witness`
(challenges `(1,2)` DO accept the cheat — the bound constrains a nonempty
event, not a vacuum), and `zero_word_retired` (the CRS layer's own violating
zero word against `evalC`, transported along `hyperIdx`, retired with the
BUILT honest side).

**Scope and residual.** `[SC-reshape]` is discharged at the UNWEIGHTED /
single-function resolution: the honest family, its degree bound, the
boolean-sum chain, and the final check `f̂(r)` are all realized for the claim
`Σ_b f(b)`. WHIR's full Def 4.5 claim is WEIGHTED — `Σ_b â(b)·f̂(b)` with the
final check FACTORED as `â(r)·f̂(r)` (`â` evaluated by the verifier, `f̂` opened
from the committed oracle). This file's engine handles the weighted SUM
exactly (feed `f := b ↦ â(b)·w(b)` — `mle_retires_constraint` does), but its
final check then targets the PRODUCT's own MLE `(â·w)^` at `r`, which is NOT
`â(r)·f̂(r)` — the MLE of a product ≠ the product of MLEs. The factored final
check needs degree-≤2 round polynomials `Σ_b â(r,X,b)·f̂(r,X,b)`: exactly the
mul-gate face the standing `[AIR-sumcheck-quadratic]` residual names. This
file's `mle` is its foundation (both factors are now vocabulary); the
quadratic round engine and the oracle factorization stay under that tag —
no new residual is coined here.
-/
import Selvage.SumcheckReduction

namespace Minidregg.Selvage

/-! ## The boolean hypercube, the chi (eq) basis, and the MLE -/

section Cube

variable {F : Type*} [CommRing F] {m : ℕ}

/-- A boolean read as a field element: `true ↦ 1`, `false ↦ 0`. -/
def ofBool (t : Bool) : F := if t then 1 else 0

@[simp] theorem ofBool_true : (ofBool true : F) = 1 := rfl

@[simp] theorem ofBool_false : (ofBool false : F) = 0 := rfl

/-- A cube corner embedded into the field: the point the sumcheck's boolean
checks walk. -/
def cubePt (b : Fin m → Bool) : Fin m → F := fun i => ofBool (b i)

@[simp] theorem cubePt_apply (b : Fin m → Bool) (i : Fin m) :
    (cubePt b i : F) = ofBool (b i) := rfl

/-- The chi/eq basis polynomial at corner `b`, evaluated:
`χ_b(x) = ∏ᵢ (if bᵢ then xᵢ else 1 − xᵢ)` — the unique multilinear function
that is `1` at corner `b` and `0` at every other corner. -/
def chiEval (b : Fin m → Bool) (x : Fin m → F) : F :=
  ∏ i, if b i then x i else 1 - x i

/-- **The multilinear extension** (WHIR Def 4.5's `f̂`): the Lagrange
interpolant of `f` on the hypercube, `f̂(x) = Σ_b f(b)·χ_b(x)`. -/
def mle (f : (Fin m → Bool) → F) (x : Fin m → F) : F :=
  ∑ b, f b * chiEval b x

/-- The chi basis is the corner indicator: `χ_b(corner b') = δ_{b,b'}`. -/
theorem chiEval_cubePt (b b' : Fin m → Bool) :
    chiEval b (cubePt b' : Fin m → F) = if b = b' then 1 else 0 := by
  by_cases h : b = b'
  · subst h
    rw [if_pos rfl, chiEval]
    refine Finset.prod_eq_one fun i _ => ?_
    cases hb : b i <;> simp [hb]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hb : b i <;> cases hb' : b' i <;> simp [hb, hb'] at hi ⊢

/-- **Agreement (the interpolation property).** The MLE agrees with `f` at
every corner of the hypercube. -/
theorem mle_agrees (f : (Fin m → Bool) → F) (b : Fin m → Bool) :
    mle f (cubePt b) = f b := by
  rw [mle,
    Fintype.sum_eq_single b fun b' hb' => by
      rw [chiEval_cubePt, if_neg hb', mul_zero],
    chiEval_cubePt, if_pos rfl, mul_one]

/-- The extension determines the table: `mle` is injective. -/
theorem mle_injective : Function.Injective (mle (F := F) (m := m)) :=
  fun f g h => funext fun b => by rw [← mle_agrees f b, h, mle_agrees]

/-- **The sum-claim transported**: the hypercube sum of `f` is the hypercube
sum of its MLE — the object the sumcheck front walks is faithful to the
original claim. -/
theorem mle_hypercube_sum (f : (Fin m → Bool) → F) :
    ∑ b, f b = ∑ b, mle f (cubePt b) :=
  Finset.sum_congr rfl fun b _ => (mle_agrees f b).symm

/-! ## Multilinearity: affine in every coordinate

Mathlib's `MultilinearMap` is the LINEAR notion — it forces
`g(x[i ↦ 0]) = 0` — which the MLE does not satisfy (`χ_b` at `bᵢ = false`
is `1 − xᵢ`). The correct rendering of "degree ≤ 1 in each variable" for a
FUNCTION is multi-AFFINEness: on every axis-`i` line, `g` is the two-point
interpolation through its values at 0 and 1. -/

/-- `g` is affine (degree ≤ 1) in coordinate `i`. -/
def AffineInCoord (g : (Fin m → F) → F) (i : Fin m) : Prop :=
  ∀ (x : Fin m → F) (t : F),
    g (Function.update x i t)
      = (1 - t) * g (Function.update x i 0) + t * g (Function.update x i 1)

/-- Multi-affine: affine in every coordinate — "a multilinear polynomial
function". -/
def MultiAffine (g : (Fin m → F) → F) : Prop := ∀ i, AffineInCoord g i

/-- The chi basis is affine in each coordinate. -/
theorem chiEval_update (b : Fin m → Bool) (x : Fin m → F) (i : Fin m) (t : F) :
    chiEval b (Function.update x i t)
      = (1 - t) * chiEval b (Function.update x i 0)
        + t * chiEval b (Function.update x i 1) := by
  have key : ∀ s : F, chiEval b (Function.update x i s)
      = (if b i then s else 1 - s)
        * ∏ j ∈ Finset.univ.erase i, (if b j then x j else 1 - x j) := by
    intro s
    rw [chiEval, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [key t, key 0, key 1]
  by_cases hbi : b i = true
  · simp only [if_pos hbi]
    ring
  · simp only [if_neg hbi]
    ring

/-- **Multilinearity.** The MLE is affine (degree ≤ 1) in every coordinate. -/
theorem mle_multilinear (f : (Fin m → Bool) → F) : MultiAffine (mle f) := by
  intro i x t
  unfold mle
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [chiEval_update]
  ring

open Classical in
/-- **Uniqueness, constructive half**: every multi-affine function IS the MLE
of its cube restriction. Coordinate-releasing induction: `P S` says `g` matches
the MLE at every point that is boolean OUTSIDE `S`; `insert i S` releases
coordinate `i` via affineness of BOTH sides. -/
theorem multiAffine_eq_mle [Nontrivial F] {g : (Fin m → F) → F}
    (hg : MultiAffine g) : g = mle (fun b => g (cubePt b)) := by
  have key : ∀ (S : Finset (Fin m)) (x : Fin m → F),
      (∀ j, j ∉ S → x j = 0 ∨ x j = 1) →
      g x = mle (fun b => g (cubePt b)) x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      have hb : x = cubePt (fun j => decide (x j = 1)) := by
        funext j
        rcases hx j (Finset.notMem_empty j) with h0 | h1
        · have hd : decide (x j = 1) = false :=
            decide_eq_false (by rw [h0]; exact zero_ne_one)
          rw [cubePt_apply, hd, ofBool_false, h0]
        · have hd : decide (x j = 1) = true := decide_eq_true h1
          rw [cubePt_apply, hd, ofBool_true, h1]
      rw [hb, mle_agrees]
    | insert i S hiS ih =>
      intro x hx
      have hbool : ∀ c : F, c = 0 ∨ c = 1 → ∀ j, j ∉ S →
          Function.update x i c j = 0 ∨ Function.update x i c j = 1 := by
        intro c hc j hj
        rcases eq_or_ne j i with rfl | hne
        · rw [Function.update_self]; exact hc
        · rw [Function.update_of_ne hne]
          exact hx j fun hmem => (Finset.mem_insert.mp hmem).elim hne hj
      have h0 := ih _ (hbool 0 (Or.inl rfl))
      have h1 := ih _ (hbool 1 (Or.inr rfl))
      have hgx := hg i x (x i)
      rw [Function.update_eq_self] at hgx
      have hmx := mle_multilinear (fun b => g (cubePt b)) i x (x i)
      rw [Function.update_eq_self] at hmx
      rw [hgx, hmx, h0, h1]
  funext x
  exact key Finset.univ x fun j hj => absurd (Finset.mem_univ j) hj

/-- **Uniqueness.** Two multi-affine functions agreeing on the hypercube are
equal — the MLE is THE multilinear interpolant, not just one of them. -/
theorem multiAffine_ext [Nontrivial F] {g₁ g₂ : (Fin m → F) → F}
    (h₁ : MultiAffine g₁) (h₂ : MultiAffine g₂)
    (hcube : ∀ b, g₁ (cubePt b) = g₂ (cubePt b)) : g₁ = g₂ := by
  rw [multiAffine_eq_mle h₁, multiAffine_eq_mle h₂]
  exact congrArg mle (funext hcube)

/-! ## Suffix cubes and the round partial sums

Round `i` of the MLE sumcheck pins challenges below `i`, runs a variable at
`i`, and sums boolean corners above `i`. The corners above level `k` are
`SuffixCube m k`; `glue` assembles the full evaluation point; `suffixSplit`
peels the first free coordinate — the ONE combinatorial engine behind both
the round-0 total (`roundSum_zero`) and the chain identity (`roundSum_succ`),
which are pure sum-splitting (multilinearity only enters for the DEGREE of
the round polynomial). -/

/-- Boolean corners for the coordinates `≥ k` — the part of the hypercube the
sumcheck has not yet visited at level `k`. -/
abbrev SuffixCube (m k : ℕ) : Type := {j : Fin m // k ≤ j.val} → Bool

/-- Assemble a full point: coordinates `< k` from the field tuple `r`,
coordinates `≥ k` from the corner `b`. -/
def glue (r : Fin m → F) (k : ℕ) (b : SuffixCube m k) : Fin m → F :=
  fun j => if h : k ≤ j.val then ofBool (b ⟨j, h⟩) else r j

@[simp] theorem glue_apply (r : Fin m → F) (k : ℕ) (b : SuffixCube m k)
    (j : Fin m) :
    glue r k b j = if h : k ≤ j.val then ofBool (b ⟨j, h⟩) else r j := rfl

/-- Peel the first free coordinate off a suffix cube. -/
def suffixSplit {m : ℕ} (k : ℕ) (hk : k < m) :
    SuffixCube m k ≃ Bool × SuffixCube m (k + 1) where
  toFun b := (b ⟨⟨k, hk⟩, le_rfl⟩, fun j => b ⟨j.1, Nat.le_of_succ_le j.2⟩)
  invFun tb j := if h : k + 1 ≤ j.1.val then tb.2 ⟨j.1, h⟩ else tb.1
  left_inv b := by
    funext j
    dsimp only
    by_cases h : k + 1 ≤ j.1.val
    · rw [dif_pos h]
    · rw [dif_neg h]
      have h2 := j.2
      have hj : (⟨⟨k, hk⟩, le_rfl⟩ : {j : Fin m // k ≤ j.val}) = j := by
        refine Subtype.ext (Fin.ext ?_)
        show k = j.1.val
        omega
      rw [hj]
  right_inv tb := by
    refine Prod.ext ?_ (funext fun j => ?_) <;> dsimp only
    · rw [dif_neg (Nat.not_succ_le_self k)]
    · rw [dif_pos j.2]

@[simp] theorem suffixSplit_symm_apply {m k : ℕ} (hk : k < m)
    (tb : Bool × SuffixCube m (k + 1)) (j : {j : Fin m // k ≤ j.val}) :
    (suffixSplit k hk).symm tb j
      = if h : k + 1 ≤ j.1.val then tb.2 ⟨j.1, h⟩ else tb.1 := rfl

/-- Gluing through the split: peeling corner `t` at level `k` is pinning
coordinate `k` to `ofBool t`. -/
theorem glue_suffixSplit_symm {k : ℕ} (hk : k < m) (r : Fin m → F)
    (t : Bool) (b : SuffixCube m (k + 1)) :
    glue r k ((suffixSplit k hk).symm (t, b))
      = glue (Function.update r ⟨k, hk⟩ (ofBool t)) (k + 1) b := by
  funext j
  simp only [glue_apply, suffixSplit_symm_apply]
  rcases lt_trichotomy j.val k with hjk | hjk | hjk
  · rw [dif_neg (by omega), dif_neg (by omega),
      Function.update_of_ne (Fin.ne_of_val_ne (show (j : ℕ) ≠ k by omega))]
  · rw [dif_pos (by omega), dif_neg (by omega), dif_neg (by omega)]
    have hj : j = ⟨k, hk⟩ := Fin.ext hjk
    rw [hj, Function.update_self]
  · rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega)]

/-- The level-`k` suffix sum splits at its first free coordinate. -/
theorem sum_glue_fold {k : ℕ} (hk : k < m) (g : (Fin m → F) → F)
    (r : Fin m → F) :
    ∑ b : SuffixCube m k, g (glue r k b)
      = (∑ b : SuffixCube m (k + 1),
          g (glue (Function.update r ⟨k, hk⟩ 0) (k + 1) b))
        + ∑ b : SuffixCube m (k + 1),
            g (glue (Function.update r ⟨k, hk⟩ 1) (k + 1) b) := by
  rw [← Equiv.sum_comp (suffixSplit k hk).symm (fun b => g (glue r k b)),
    Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by
      rw [glue_suffixSplit_symm hk, ofBool_false]
  · exact Finset.sum_congr rfl fun b _ => by
      rw [glue_suffixSplit_symm hk, ofBool_true]

/-! ## The round partial sums -/

/-- **Round `i`'s partial sum** — WHIR Def 4.5's round polynomial as a
function: `gᵢ(t) = Σ_{b ∈ {0,1}^{m−i−1}} g(r₀,…,r_{i−1}, t, b)`. Challenges
strictly below `i`, the running variable at `i`, boolean corners above. -/
def roundSum (g : (Fin m → F) → F) (r : Fin m → F) (i : Fin m) (t : F) : F :=
  ∑ b : SuffixCube m (i.val + 1),
    g (glue (Function.update r i t) (i.val + 1) b)

/-- The fold identity: round `k`'s two boolean evaluations add up to the
previous level's full suffix sum. -/
theorem roundSum_fold {k : ℕ} (hk : k < m) (g : (Fin m → F) → F)
    (r : Fin m → F) :
    roundSum g r ⟨k, hk⟩ 0 + roundSum g r ⟨k, hk⟩ 1
      = ∑ b : SuffixCube m k, g (glue r k b) :=
  (sum_glue_fold hk g r).symm

/-- The zero-level suffix cube is the whole hypercube. -/
def suffixCubeZero (m : ℕ) : SuffixCube m 0 ≃ (Fin m → Bool) where
  toFun b j := b ⟨j, Nat.zero_le _⟩
  invFun b j := b j.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Round 0's boolean check target is the full hypercube sum**:
`g₀(0) + g₀(1) = Σ_b g(corner b)`. -/
theorem roundSum_zero (h0 : 0 < m) (g : (Fin m → F) → F) (r : Fin m → F) :
    roundSum g r ⟨0, h0⟩ 0 + roundSum g r ⟨0, h0⟩ 1
      = ∑ b : Fin m → Bool, g (cubePt b) := by
  rw [roundSum_fold h0 g r]
  exact Fintype.sum_equiv (suffixCubeZero m) _ _ fun b => rfl

/-- **The chain identity**: the next round's boolean check target is the
previous round polynomial folded at the challenge —
`g_{k+1}(0) + g_{k+1}(1) = g_k(r_k)`. Pure sum-splitting. -/
theorem roundSum_succ {k : ℕ} (hk : k + 1 < m) (g : (Fin m → F) → F)
    (r : Fin m → F) :
    roundSum g r ⟨k + 1, hk⟩ 0 + roundSum g r ⟨k + 1, hk⟩ 1
      = roundSum g r ⟨k, Nat.lt_of_succ_lt hk⟩ (r ⟨k, Nat.lt_of_succ_lt hk⟩) := by
  rw [roundSum_fold hk g r]
  simp only [roundSum, Function.update_eq_self]

/-- **The last round's fold value is the full evaluation**: with every
coordinate pinned the suffix cube is empty, so `g_{m−1}(t) = g(r₀,…,r_{m−2},t)`
— the final oracle check target. -/
theorem roundSum_last {i : Fin m} (hi : i.val + 1 = m) (g : (Fin m → F) → F)
    (r : Fin m → F) (t : F) :
    roundSum g r i t = g (Function.update r i t) := by
  haveI : IsEmpty {j : Fin m // i.val + 1 ≤ j.val} :=
    ⟨fun j => by have := j.1.isLt; have := j.2; omega⟩
  rw [roundSum,
    Fintype.sum_eq_single default fun x hx => absurd (Subsingleton.elim x _) hx]
  congr 1
  funext j
  rw [glue_apply, dif_neg (by have := j.isLt; omega)]

/-- Gluing commutes with pinning the running coordinate: the round variable
rides OUTSIDE the glue. -/
theorem glue_update {r : Fin m → F} {i : Fin m} (t : F)
    (b : SuffixCube m (i.val + 1)) :
    glue (Function.update r i t) (i.val + 1) b
      = Function.update (glue r (i.val + 1) b) i t := by
  funext j
  rcases eq_or_ne j i with rfl | hne
  · rw [Function.update_self, glue_apply, dif_neg (by omega),
      Function.update_self]
  · rw [Function.update_of_ne hne, glue_apply, glue_apply]
    by_cases h : i.val + 1 ≤ j.val
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, Function.update_of_ne hne]

/-- **The round partial sum is affine in the running variable** — the round
polynomial has degree ≤ 1. Multilinearity of `g` in coordinate `i`, summed. -/
theorem roundSum_affine {g : (Fin m → F) → F} {i : Fin m}
    (hg : AffineInCoord g i) (r : Fin m → F) (t : F) :
    roundSum g r i t = (1 - t) * roundSum g r i 0 + t * roundSum g r i 1 := by
  simp only [roundSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [glue_update t, glue_update 0, glue_update 1]
  exact hg _ t

/-- **Round `i` reads the challenge tuple only strictly below `i`** — the
prefix-measurability the adaptive sumcheck consumes. -/
theorem roundSum_congr_prefix {g : (Fin m → F) → F} {i : Fin m}
    {r r' : Fin m → F} (h : ∀ j : Fin m, j.val < i.val → r j = r' j) (t : F) :
    roundSum g r i t = roundSum g r' i t := by
  simp only [roundSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  funext j
  simp only [glue_apply]
  by_cases hj : i.val + 1 ≤ j.val
  · rw [dif_pos hj, dif_pos hj]
  · rw [dif_neg hj, dif_neg hj]
    rcases eq_or_ne j i with rfl | hne
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hne, Function.update_of_ne hne]
      have hv : j.val ≠ i.val := fun hv => hne (Fin.ext hv)
      exact h j (by omega)

end Cube

/-! ## The honest MLE prover: `[SC-reshape]`'s realizer, packaged and consumed

`Selvage/Sumcheck.lean`'s protocol theorems live over `F : Type` (the
`uniformProb` toolkit is universe-monomorphic) with `Polynomial F` round
messages; this section renders `roundSum` as an actual degree-≤1 polynomial
and inhabits every hypothesis of `adaptive_sumcheck_soundness`. -/

section Realizer

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

open Polynomial

/-- The round polynomial as a `Polynomial F`:
`C (gᵢ(1) − gᵢ(0))·X + C (gᵢ(0))` — degree ≤ 1 by construction, and (for
multilinear `g`) evaluating to `roundSum` everywhere. -/
noncomputable def roundPoly (g : (Fin m → F) → F) (r : Fin m → F) (i : Fin m) :
    Polynomial F :=
  C (roundSum g r i 1 - roundSum g r i 0) * X + C (roundSum g r i 0)

omit [Fintype F] [DecidableEq F] in
/-- For `g` affine in coordinate `i`, the round polynomial IS the round
partial sum. -/
theorem roundPoly_eval {g : (Fin m → F) → F} {i : Fin m}
    (hg : AffineInCoord g i) (r : Fin m → F) (t : F) :
    (roundPoly g r i).eval t = roundSum g r i t := by
  rw [roundSum_affine hg r t]
  simp [roundPoly]
  ring

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial has degree ≤ 1 — the `d = 1` the sumcheck bound
consumes. -/
theorem roundPoly_degree (g : (Fin m → F) → F) (r : Fin m → F) (i : Fin m) :
    (roundPoly g r i).degree < ((1 + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_linear_le (by decide)

/-- **The honest MLE prover** — the realizer `[SC-reshape]` names. Round `i`
sends the MLE partial-sum polynomial `gᵢ`; the challenge stream is read only
below `i` (constant `0` junk past the last round, never consulted). -/
noncomputable def mleHonest (f : (Fin m → Bool) → F) (χ : ℕ → F) (i : ℕ) :
    Polynomial F :=
  if h : i < m then roundPoly (mle f) (fun j : Fin m => χ j.val) ⟨i, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
/-- The honest family is prefix-measurable: round `i`'s message depends on the
challenge stream only below `i`. -/
theorem mleHonest_prefixMeasurable (f : (Fin m → Bool) → F) :
    PrefixMeasurable (mleHonest f) := by
  intro χ χ' i hpre
  unfold mleHonest
  by_cases h : i < m
  · rw [dif_pos h, dif_pos h]
    unfold roundPoly
    rw [roundSum_congr_prefix (i := ⟨i, h⟩) (fun j hj => hpre j.val hj) 0,
      roundSum_congr_prefix (i := ⟨i, h⟩) (fun j hj => hpre j.val hj) 1]
  · rw [dif_neg h, dif_neg h]

omit [Fintype F] [DecidableEq F] in
/-- The honest family's degree bound: `d = 1`, every round. -/
theorem mleHonest_degree (f : (Fin m → Bool) → F) (χ : ℕ → F) (i : ℕ)
    (hi : i < m) :
    (mleHonest f χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ) := by
  rw [mleHonest, dif_pos hi]
  exact roundPoly_degree _ _ _

omit [Fintype F] [DecidableEq F] in
/-- Restricting `chalOf r` back to `Fin m` recovers `r`. -/
theorem chalOf_restrict (r : Fin m → F) :
    (fun j : Fin m => chalOf r j.val) = r :=
  funext fun j => chalOf_coe r j

omit [Fintype F] [DecidableEq F] in
/-- **`[SC-reshape]`'s `hHonest`, DISCHARGED.** The MLE partial-sum family
satisfies the honest boolean-sum consistency along the truth chain anchored at
the full hypercube sum `Σ_b f(b)`: round 0's check target is the claimed total
(`roundSum_zero` + `mle_agrees`), and every later round's target is the
previous round polynomial folded at the challenge (`roundSum_succ`). -/
theorem mleHonest_boolean_sum (f : (Fin m → Bool) → F) (r : Fin m → F) :
    ∀ i, i < m →
      (mleHonest f (chalOf r) i).eval 0 + (mleHonest f (chalOf r) i).eval 1
        = scChain (∑ b, f b) (mleHonest f (chalOf r)) (chalOf r) i := by
  intro i hi
  rw [mleHonest, dif_pos hi, chalOf_restrict,
    roundPoly_eval (mle_multilinear f ⟨i, hi⟩) r 0,
    roundPoly_eval (mle_multilinear f ⟨i, hi⟩) r 1]
  cases i with
  | zero =>
    show _ = ∑ b, f b
    rw [roundSum_zero hi (mle f) r, ← mle_hypercube_sum]
  | succ n =>
    show _ = (mleHonest f (chalOf r) n).eval (chalOf r n)
    have hn : n < m := Nat.lt_of_succ_lt hi
    rw [mleHonest, dif_pos hn, chalOf_restrict,
      roundPoly_eval (mle_multilinear f ⟨n, hn⟩) r (chalOf r n),
      chalOf_coe r ⟨n, hn⟩]
    exact roundSum_succ hi (mle f) r

omit [Fintype F] [DecidableEq F] in
/-- **The final oracle check, realized**: after all `m` rounds the honest truth
chain's value IS the MLE at the challenge point — WHIR Def 4.5's terminal
comparison `f̂(r)` (unweighted form; the factored `â(r)·f̂(r)` is the named
residual). -/
theorem scChain_mleHonest_final (f : (Fin m → Bool) → F) (r : Fin m → F) :
    scChain (∑ b, f b) (mleHonest f (chalOf r)) (chalOf r) m = mle f r := by
  cases m with
  | zero =>
    show ∑ b, f b = mle f r
    rw [mle]
    refine Fintype.sum_congr _ _ fun b => ?_
    rw [chiEval, Fintype.prod_empty, mul_one]
  | succ n =>
    show (mleHonest f (chalOf r) n).eval (chalOf r n) = mle f r
    have hn : n < n + 1 := Nat.lt_succ_self n
    rw [mleHonest, dif_pos hn, chalOf_restrict,
      roundPoly_eval (mle_multilinear f ⟨n, hn⟩) r (chalOf r n),
      chalOf_coe r ⟨n, hn⟩, roundSum_last rfl (mle f) r,
      Function.update_eq_self]

omit [Fintype F] [DecidableEq F] in
/-- **Completeness of the realizer**: the honest MLE prover, run as both
prover and truth chain on the true total, passes every check on EVERY
challenge vector. -/
theorem mleHonest_complete (f : (Fin m → Bool) → F) (r : Fin m → F) :
    SumcheckAccepts (v := m) (mleHonest f (chalOf r)) (mleHonest f (chalOf r))
      (∑ b, f b) (∑ b, f b) r :=
  ⟨fun i hi => mleHonest_boolean_sum f r i hi, rfl⟩

/-- **Soundness against the built realizer.** With the honest side
INSTANTIATED at the MLE family (not hypothesized), any prefix-measurable
degree-≤1 prover opening with a false total `H ≠ Σ_b f(b)` is accepted with
probability at most `m/|F|` — `adaptive_sumcheck_soundness` consumed at
`d = 1`. Only adversary-side hypotheses remain, as they must. -/
theorem mle_sumcheck_soundness {f : (Fin m → Bool) → F}
    {prover : (ℕ → F) → ℕ → Polynomial F} {H : F}
    (hpm : PrefixMeasurable prover)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F)
      (AdaptiveAcceptsFalse prover (mleHonest f) H (∑ b, f b))
      ≤ (m : ℝ) * (1 / Fintype.card F) := by
  have h := adaptive_sumcheck_soundness (v := m) (d := 1) (H := H)
    hpm (mleHonest_prefixMeasurable f) hProverDeg
    (fun χ i hi => mleHonest_degree f χ i hi)
    (fun r i hi => mleHonest_boolean_sum f r i hi)
  simpa using h

/-- **The turnkey decider sumcheck**: a `LinearConstraint` transported to the
hypercube (`constraint_as_hypercube_sum`'s reshaping) with the honest side
BUILT — the MLE of the transported summand `b ↦ wt(e⁻¹b)·w(e⁻¹b)`. A word
violating the constraint survives against any admissible prover with
probability at most `v/|F|`. `[SC-reshape]`'s realizer, constructed and
consumed in one statement. -/
theorem mle_retires_constraint {ι : Type*} [Fintype ι] {v : ℕ}
    (e : ι ≃ (Fin v → Bool)) {w : ι → F} {c : LinearConstraint ι F}
    (hviol : ¬ Satisfies w c)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (prover χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin v → F)
      (fun r => SumcheckAccepts (prover (chalOf r))
        (mleHonest (fun b => constraintSummand c w (e.symm b)) (chalOf r))
        c.target (trueSum c w) r)
      ≤ (v : ℝ) * (1 / Fintype.card F) := by
  have hsum : trueSum c w = ∑ b, constraintSummand c w (e.symm b) :=
    (sum_reindex_hypercube e (constraintSummand c w)).symm
  have h := adaptive_sumcheck_retires_constraint (v := v) (d := 1)
    (prover := prover)
    (honest := mleHonest fun b => constraintSummand c w (e.symm b))
    hviol hpm
    (mleHonest_prefixMeasurable _) hProverDeg
    (fun χ i hi => mleHonest_degree _ χ i hi)
    (fun r i hi => by
      rw [hsum]
      exact mleHonest_boolean_sum _ r i hi)
  simpa using h

end Realizer

/-! ## Keystones over F₅ (ATLAS: satisfiable + teeth, BUILT)

The AND gate on two bits: its MLE, computed and audited. Uniqueness FIRES to
produce the closed form `x₀·x₁`; the sumcheck chain computes round by round;
the soundness pipeline runs end-to-end with a nonempty caught-event. -/

namespace MLEExample

open Polynomial

/-- The AND gate on two bits, valued in F₅. -/
def fAnd : (Fin 2 → Bool) → ZMod 5 := fun b => if b 0 && b 1 then 1 else 0

/-- The OR gate, for the teeth. -/
def fOr : (Fin 2 → Bool) → ZMod 5 := fun b => if b 0 || b 1 then 1 else 0

/-- **SATISFIABLE — agreement computed**: the MLE matches the AND gate on all
four cube corners. -/
theorem mle_and_agrees : ∀ b, mle fAnd (cubePt b) = fAnd b := by decide

/-- **Uniqueness FIRES — the closed form**: `f̂_AND = x₀·x₁`. Both sides are
multi-affine and agree on the cube (both checked by `decide` over the finite
point space), so `multiAffine_ext` forces equality of the FUNCTIONS. -/
theorem mle_and_closed_form : mle fAnd = fun x => x 0 * x 1 :=
  multiAffine_ext (mle_multilinear fAnd)
    (by unfold MultiAffine AffineInCoord; decide) (by decide)

/-- **A genuine extension, not a table**: off the cube, `f̂_AND(2,3) = 2·3 = 1`
— the multilinear value, computed. -/
theorem mle_and_offcube : mle fAnd ![2, 3] = 1 := by decide

/-- **TEETH — the extension determines the table**: AND and OR have different
MLEs (they differ at the corner `(1,0)`); `mle_injective` is the general
statement, this is it firing on data. -/
theorem mle_and_ne_or : mle fAnd ![1, 0] ≠ mle fOr ![1, 0] := by decide

/-- **TEETH — multilinearity computed**: the two-point interpolation fires at
an off-cube point in coordinate 0. -/
theorem mle_and_affine_fires :
    mle fAnd (Function.update ![2, 3] 0 4)
      = (1 - 4) * mle fAnd (Function.update ![2, 3] 0 0)
        + 4 * mle fAnd (Function.update ![2, 3] 0 1) := by decide

/-- **TEETH — `AffineInCoord` is not trivially true**: the SQUARE `x₀²` over F₅
refutes it, so multilinearity is a real constraint, not a tautology every
function satisfies. -/
theorem square_not_affine :
    ¬ AffineInCoord (fun x : Fin 1 → ZMod 5 => x 0 * x 0) 0 := by
  unfold AffineInCoord
  decide

/-- The round chain, link 0, computed: `g₀(0) + g₀(1) = Σ_b fAnd(b) = 1` — the
boolean check target IS the claimed total. -/
theorem roundSum_and_chain0 :
    roundSum (mle fAnd) ![2, 0] 0 0 + roundSum (mle fAnd) ![2, 0] 0 1 = 1 := by
  decide

/-- The round chain, link 1, computed: `g₁(0) + g₁(1) = g₀(r₀)` at the
challenge `r₀ = 2`. -/
theorem roundSum_and_chain1 :
    roundSum (mle fAnd) ![2, 0] 1 0 + roundSum (mle fAnd) ![2, 0] 1 1
      = roundSum (mle fAnd) ![2, 0] 0 2 := by decide

/-- The final fold IS the oracle check, computed: `g₁(r₁) = f̂_AND(2,3)`. -/
theorem roundSum_and_final :
    roundSum (mle fAnd) ![2, 3] 1 3 = mle fAnd ![2, 3] := by decide

/-- Completeness fires on data: the honest MLE prover for the AND gate is
accepted at `r = (2,3)` (and every other challenge). -/
example : SumcheckAccepts (v := 2) (mleHonest fAnd (chalOf ![2, 3]))
    (mleHonest fAnd (chalOf ![2, 3])) (∑ b, fAnd b) (∑ b, fAnd b) ![2, 3] :=
  mleHonest_complete fAnd ![2, 3]

/-- A cheating prover: passes round 0's check on the false total `H = 3`
(`4 + 4 = 3` in F₅) and round 1's check on the folded claim (`2 + 2 = 4`). -/
noncomputable def cheatProver : (ℕ → ZMod 5) → ℕ → Polynomial (ZMod 5) :=
  fun _ i => if i = 0 then C 4 else C 2

/-- **The soundness bound fires END-TO-END on the realizer**: the cheating
prover claiming `H = 3` (true total: `1`) against the honest MLE family is
accepted with probability at most `2/5`. -/
theorem cheat_caught :
    uniformProb (Fin 2 → ZMod 5)
      (AdaptiveAcceptsFalse cheatProver (mleHonest fAnd) 3 (∑ b, fAnd b))
      ≤ 2 / 5 := by
  have h := mle_sumcheck_soundness (f := fAnd) (prover := cheatProver) (H := 3)
    (fun _ _ _ _ => rfl)
    (fun χ i _ => by
      unfold cheatProver
      split <;> exact lt_of_le_of_lt (degree_C_le) (by decide))
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-- **The caught-event is NONEMPTY**: at challenges `(1,2)` the cheat IS
accepted — both round checks pass and the final fold `2` equals
`f̂_AND(1,2) = 1·2` — so the `2/5` bound constrains a real event, not a
vacuum. -/
theorem cheat_accept_witness :
    AdaptiveAcceptsFalse cheatProver (mleHonest fAnd) 3 (∑ b, fAnd b)
      ![1, 2] := by
  refine ⟨fun i hi => ?_, ?_, by decide⟩
  · have h2 : i = 0 ∨ i = 1 := by omega
    rcases h2 with rfl | rfl <;>
      simp [cheatProver, scChain, chalOf] <;> decide
  · show scChain (3 : ZMod 5) _ _ 2 = _
    rw [scChain_mleHonest_final fAnd ![1, 2]]
    simp [cheatProver, scChain]
    decide

/-- **Full circle with the CRS layer**: `CRSExample`'s constraint `f(1) = 1`
on the 4-point domain, transported to `{0,1}²` along `SCRExample.hyperIdx`,
its violating ZERO word retired by a sumcheck whose honest side is the BUILT
MLE family of the transported summand — bound `2/5`, every honest-side
hypothesis a theorem, not an assumption. -/
theorem zero_word_retired :
    uniformProb (Fin 2 → ZMod 5)
      (fun r => SumcheckAccepts (cheatProver (chalOf r))
        (mleHonest (fun b => constraintSummand CRSExample.evalC
          (0 : Fin 4 → ZMod 5) (SCRExample.hyperIdx.symm b)) (chalOf r))
        CRSExample.evalC.target
        (trueSum CRSExample.evalC (0 : Fin 4 → ZMod 5)) r)
      ≤ 2 / 5 := by
  have h := mle_retires_constraint (v := 2) SCRExample.hyperIdx
    (w := (0 : Fin 4 → ZMod 5)) (c := CRSExample.evalC)
    CRSExample.zero_not_satisfies (prover := cheatProver)
    (fun _ _ _ _ => rfl)
    (fun χ i _ => by
      unfold cheatProver
      split <;> exact lt_of_le_of_lt (degree_C_le) (by decide))
  rw [ZMod.card] at h
  norm_num at h
  exact h

end MLEExample

end Minidregg.Selvage
