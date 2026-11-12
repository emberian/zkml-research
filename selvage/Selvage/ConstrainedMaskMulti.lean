/-
# Selvage.ConstrainedMaskMulti — `[CMASK-multi]` closed: constrained-mask
surjectivity at GENERAL `r` evaluation constraints.

`Selvage/ConstrainedMask.lean` proved constrained-mask surjectivity and hiding for
ONE evaluation constraint (`r = 1`, bound `t + 1 ≤ d`) and named its own
residual `[CMASK-multi]`: general `r` — a mask vanishing at `r` constraint
points — "iterates this file's factorization … giving `t + r ≤ d`". This file
IS that iteration, and it lands at full generality: the `r`-fold vanishing
factor is `Lagrange.nodal` (the monic product `∏ⱼ (X − dom ptⱼ)`, degree
exactly `r`), so the single-factor argument reruns verbatim with the nodal
polynomial in the factor slot — no induction on the constraint list needed,
Mathlib's `degree_nodal` / `eval_nodal_at_node` / `eval_nodal_not_at_node`
carry the bookkeeping the residual predicted.

**The argument (vanishing-product factorization).** A degree-`< d` polynomial
vanishing at the `r` points `dom pt₁, …, dom ptᵣ` factors as
`p = (∏ⱼ (X − dom ptⱼ)) · p'` with `p'` of degree `< d − r`. Choosing `p'` by
Lagrange interpolation through the `t` DESIRED values, each divided by the
vanishing product's value at that query (well-defined: no query point is a
constraint point), makes `p` vanish at every `ptⱼ` AND open to exactly the
target tuple at the `t` queries — using `t + r ≤ d`: `r` of the `d` degrees
of freedom are spent paying for the constraints, `t` remain for the targets.
The `r = 1` proof is literally the special case where the nodal product has
one factor.

**What is proved here:**

* `constrainedMaskSpaceMulti` — `RS ⊓ ⨅ⱼ ker(eval at ptⱼ)`, the mask claim's
  homogeneous kernel for `r` evaluation constraints, a genuine `Submodule`.
  Coherence anchors: at `r = 0` it IS the whole code
  (`constrainedMaskSpaceMulti_zero` — the regime of `exists_codeword_open`),
  at `r = 1` it IS `constrainedMaskSpace`
  (`constrainedMaskSpaceMulti_one` — the file being generalized), and
  `coe_constrainedMaskSpaceMulti` ties it to `ConstrainedCode`'s vocabulary:
  it is `constrainedRS dom d (List.ofFn fun j => evalConstraint (pts j) 0)`.
* `exists_constrainedMaskMulti_open` — **the surjectivity theorem at general
  `r`**: for `t + r ≤ d`, distinct query points none of them a constraint
  point, every `t`-tuple is opened by some mask vanishing at ALL `r`
  constraint points. NOTE the constraint points are NOT required pairwise
  distinct: repeats only repeat a factor in the nodal product (the mask then
  vanishes to higher order), so the theorem as stated is strictly stronger
  than the residual's "r distinct points" phrasing — repeats merely waste
  constraint budget, they never break the construction.
* `constrainedMaskMulti_hiding` — the surjectivity fed through
  `maskedOpeningHiding_of_surj`: `MaskedOpeningHiding` for the `r`-constraint
  mask space at every `γ ≠ 0`, bound `t + r ≤ d`. No re-derivation of
  `ZKHiding.lean`'s fiber/simulator machinery.
* **Keystones over F₅**, `RS[F₅, {0,1,2,3}, 3]` (quadratics over the
  `RSExample` domain — `d = 3` because two constraints need `t + 2 ≤ d`),
  constrained by vanishing at BOTH `pt = 2` and `pt = 3` (`r = 2`): the
  constrained space is the F₅-multiples of `X² + 1` (word `(1, 2, 0, 0)`) —
  `quadWord_mem_multi` inhabits it; `constrainedMaskMulti_surj_F5` fires the
  surjectivity AT the tight bound `t + r = 1 + 2 = d = 3`;
  `constrainedMaskMulti_open_one_F5` is the computed end-to-end witness;
  `not_open_10_constrainedMaskMulti_F5` exhibits an UNREACHABLE tuple at
  `t = 2` (`t + r = 4 > d`) — the bound is load-bearing; and
  `not_open_1_at_constraint_F5` shows the DISJOINTNESS hypothesis is
  load-bearing too — querying a constraint point defeats surjectivity even
  inside the budget `t + r ≤ d`.

**What stays prose-residual — `[CMASK-dual-distance]`:** non-evaluation
LINEAR constraint channels. An arbitrary `LinearConstraint` weight vector not
concentrated at a domain point offers NO vanishing factor to divide out — the
factorization above needs each constraint to BE a point so `(X − dom pt)` is
available. The honest bound there is the dual distance of the constrained
code (a Singleton-type bound on an arbitrary linear code, not interpolation)
— separate, genuinely harder mathematics, named by `ZKHiding.lean`'s original
residual and NOT attempted here.
-/
import Mathlib.LinearAlgebra.Lagrange
import Selvage.ZKHiding
import Selvage.ConstrainedCode
import Selvage.ConstrainedMask
import Selvage.ReedSolomon

namespace Minidregg.Selvage

variable {F : Type*} [Field F] {ι : Type*} {t d r : ℕ}

/-! ## The multi-constrained mask space: `RS ⊓ ⨅ⱼ ker(eval at ptⱼ)` -/

/-- **The multi-constrained mask space** at `r` constraint points: codewords
of `RS[F, dom, d]` that vanish at EVERY `pts j` — the mask claim's homogeneous
kernel for the `r` evaluation constraints `evalConstraint (pts j) 0`. A
genuine `Submodule` (all targets `0`), which is what
`maskedOpeningHiding_of_surj`'s `C` argument needs. -/
noncomputable def constrainedMaskSpaceMulti (dom : ι ↪ F) (d : ℕ) (pts : Fin r → ι) :
    Submodule F (ι → F) :=
  reedSolomonCode dom d ⊓ ⨅ j, LinearMap.ker (evalAtPt (F := F) (pts j))

@[simp] theorem mem_constrainedMaskSpaceMulti {dom : ι ↪ F} {d : ℕ} {pts : Fin r → ι}
    {f : ι → F} :
    f ∈ constrainedMaskSpaceMulti dom d pts
      ↔ f ∈ reedSolomonCode dom d ∧ ∀ j, f (pts j) = 0 := by
  simp [constrainedMaskSpaceMulti, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Coherence at `r = 0`: no constraints gives back exactly the code — the
regime of `ZKHiding.lean`'s `exists_codeword_open`, bound `t + 0 ≤ d`. -/
theorem constrainedMaskSpaceMulti_zero (dom : ι ↪ F) (d : ℕ) (pts : Fin 0 → ι) :
    constrainedMaskSpaceMulti dom d pts = reedSolomonCode dom d := by
  ext f
  simp

/-- Coherence at `r = 1`: one constraint gives back exactly
`ConstrainedMask.lean`'s space — this file genuinely EXTENDS that one, it does
not sit beside it. -/
theorem constrainedMaskSpaceMulti_one (dom : ι ↪ F) (d : ℕ) (pt : ι) :
    constrainedMaskSpaceMulti dom d ![pt] = constrainedMaskSpace dom d pt := by
  ext f
  simp

/-- The multi-constrained mask space IS the constraint channel's space in
`ConstrainedCode`'s vocabulary: `constrainedRS` at the list of homogeneous
evaluation constraints — the `LinearConstraint`-shaped audit of what got
closed, mirroring `coe_constrainedMaskSpace` at `r = 1`. -/
theorem coe_constrainedMaskSpaceMulti [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (dom : ι ↪ F) (d : ℕ) (pts : Fin r → ι) :
    (constrainedMaskSpaceMulti dom d pts : Set (ι → F))
      = constrainedRS dom d (List.ofFn fun j => evalConstraint (pts j) (0 : F)) := by
  ext f
  simp [mem_constrainedRS_iff, satisfies_evalConstraint_iff]

/-! ## Constrained-mask surjectivity at general `r`: the vanishing-product argument -/

/-- **Constrained-mask surjectivity, general `r`.** For `t + r ≤ d` distinct
query points, none of them a constraint point: every `t`-tuple of symbol
values is opened by SOME mask in the `r`-constraint space — a codeword
vanishing at ALL `r` constraint points AND matching the desired values at the
`t` queries. Vanishing-product factorization:
`p = (∏ⱼ (X − dom (pts j))) · p'` — the product is `Lagrange.nodal`, monic of
degree exactly `r` — with `p'` interpolating the target values scaled by the
product's (nonzero) values at the queries, so `p` has degree
`< r + t ≤ d`, vanishes at every constraint point through the nodal factor,
and opens to `v` because the factor divides out at each query. This closes
`[CMASK-multi]` as stated: the `r = 1` proof is the one-factor special case,
and the constraint points need not even be pairwise distinct (repeated points
repeat a factor — higher-order vanishing, never failure). -/
theorem exists_constrainedMaskMulti_open (dom : ι ↪ F) (pts : Fin r → ι)
    (ht : t + r ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (hpt : ∀ i j, q i ≠ pts j)
    (v : Fin t → F) :
    ∃ mask ∈ constrainedMaskSpaceMulti dom d pts, openSymbols q mask = v := by
  classical
  set Z : Polynomial F := Lagrange.nodal Finset.univ (dom ∘ pts) with hZ_def
  have hZdeg : Z.degree = (r : WithBot ℕ) := by
    rw [hZ_def, Lagrange.degree_nodal, Finset.card_univ, Fintype.card_fin]
  have hZq : ∀ i, Z.eval (dom (q i)) ≠ 0 := fun i =>
    Lagrange.eval_nodal_not_at_node (s := Finset.univ) (v := dom ∘ pts)
      (fun j _ h => hpt i j (dom.injective h))
  have hZpt : ∀ j, Z.eval (dom (pts j)) = 0 := fun j =>
    Lagrange.eval_nodal_at_node (s := Finset.univ) (v := dom ∘ pts) (Finset.mem_univ j)
  set w : Fin t → F := fun i => v i / Z.eval (dom (q i)) with hw_def
  set p' : Polynomial F := Lagrange.interpolate Finset.univ (dom ∘ q) w with hp'_def
  have hp'deg : p'.degree < (t : WithBot ℕ) := by
    have hdeg := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := dom ∘ q) w hq.injOn
    rwa [Finset.card_univ, Fintype.card_fin] at hdeg
  have hp'eval : ∀ i, p'.eval (dom (q i)) = w i := fun i =>
    Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := dom ∘ q) w hq.injOn
      (Finset.mem_univ i)
  set p : Polynomial F := Z * p' with hp_def
  have hpdeg : p.degree < (d : WithBot ℕ) := by
    have h1 : p.degree ≤ Z.degree + p'.degree := Polynomial.degree_mul_le _ _
    rw [hZdeg] at h1
    have h3 : (r : WithBot ℕ) + p'.degree < (r : WithBot ℕ) + (t : WithBot ℕ) :=
      WithBot.add_lt_add_left (by simp) hp'deg
    have h4 : (r : WithBot ℕ) + (t : WithBot ℕ) ≤ (d : WithBot ℕ) := by
      have hcast : ((r + t : ℕ) : WithBot ℕ) ≤ (d : WithBot ℕ) := by
        exact_mod_cast (show r + t ≤ d by omega)
      rwa [Nat.cast_add] at hcast
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h3 h4)
  refine ⟨evalOnDomain dom p, ?_, ?_⟩
  · rw [mem_constrainedMaskSpaceMulti]
    refine ⟨mem_reedSolomonCode_iff.mpr ⟨p, hpdeg, fun i => rfl⟩, fun j => ?_⟩
    rw [evalOnDomain_apply, hp_def, Polynomial.eval_mul, hZpt j, zero_mul]
  · funext i
    rw [openSymbols_apply, evalOnDomain_apply, hp_def]
    simp only [Polynomial.eval_mul, hp'eval i, hw_def]
    rw [mul_comm, div_mul_cancel₀ _ (hZq i)]

/-! ## The connection: multi-constrained-mask hiding -/

/-- **Multi-constrained-mask hiding**: `[CMASK-multi]`'s hiding face —
masked-opening hiding holds when the mask is confined to the kernel of ALL
`r` evaluation constraints, at every `γ ≠ 0` and the bound `t + r ≤ d`. Fed
directly through `maskedOpeningHiding_of_surj`; only the surjectivity premise
is new, the fiber-bijection/simulator machinery is reused. -/
theorem constrainedMaskMulti_hiding (dom : ι ↪ F) (pts : Fin r → ι) (ht : t + r ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (hpt : ∀ i j, q i ≠ pts j)
    {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (constrainedMaskSpaceMulti dom d pts) q γ :=
  maskedOpeningHiding_of_surj _ q hγ (exists_constrainedMaskMulti_open dom pts ht hq hpt)

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 3]` — quadratics `a + bX + cX²` on `RSExample`'s
domain; `d = 3` because two constraints cost two degrees of freedom —
constrained by vanishing at BOTH `pt = 2` and `pt = 3` (`r = 2`): a quadratic
vanishing at `2` and `3` is `c·(X − 2)(X − 3) = c·(X² + 1)` over F₅, so the
constrained space is the F₅-multiples of the word `(1, 2, 0, 0)` — a genuine
1-dimensional subspace (5 codewords out of the 125 quadratic words). -/

namespace ConstrainedMaskMultiExample

open RSExample ConstrainedMaskExample

/-- The two constraint points: domain values `2` and `3`. -/
def pts₂₃ : Fin 2 → Fin 4 := ![2, 3]

/-- The single query point `0` is disjoint from both constraint points. -/
theorem qOne_ne_pts : ∀ i j, qOne i ≠ pts₂₃ j := by decide

/-- The word of `X² + 1`: `(1, 2, 0, 0)` over the domain `{0, 1, 2, 3}` —
`4 + 1 = 5 = 0` and `9 + 1 = 10 = 0` kill the last two coordinates. -/
def quadWord : Fin 4 → ZMod 5 := fun i => (i.val : ZMod 5) ^ 2 + 1

theorem quadWord_mem : quadWord ∈ reedSolomonCode dom₅ 3 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.X ^ 2 + Polynomial.C 1,
      by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; decide,
      fun i => by simp [quadWord, dom₅]⟩

/-- **Premise inhabitation**: the 2-constraint mask space is nontrivial — the
quadratic word `(1, 2, 0, 0)` vanishes at both constraint points and is
nonzero. -/
theorem quadWord_mem_multi : quadWord ∈ constrainedMaskSpaceMulti dom₅ 3 pts₂₃ := by
  rw [mem_constrainedMaskSpaceMulti]
  exact ⟨quadWord_mem, by decide⟩

theorem quadWord_ne_zero : quadWord ≠ 0 := by decide

/-- **Satisfiable**: the general surjectivity theorem applied at the TIGHT
bound `t + r = 1 + 2 = d = 3` — every single-symbol target is reachable from
the 2-constraint mask space. -/
theorem constrainedMaskMulti_surj_F5 (v : Fin 1 → ZMod 5) :
    ∃ mask ∈ constrainedMaskSpaceMulti dom₅ 3 pts₂₃, openSymbols qOne mask = v :=
  exists_constrainedMaskMulti_open dom₅ pts₂₃ (by norm_num) qOne_inj qOne_ne_pts v

/-- **Satisfiable, computed end-to-end**: the concrete mask `X² + 1` vanishes
at both constraint points and opens to `![1]` at the query `0` — the
surjectivity theorem's construction exhibited on real data. -/
theorem constrainedMaskMulti_open_one_F5 :
    quadWord ∈ constrainedMaskSpaceMulti dom₅ 3 pts₂₃ ∧
      openSymbols qOne quadWord = ![1] :=
  ⟨quadWord_mem_multi, by rw [openSymbols_eq_comp]; decide⟩

/-- **The hiding theorem, instantiated**: masked-opening hiding for the
2-constraint mask space fires at the tight bound, every nonzero challenge. -/
theorem constrainedMaskMulti_hiding_F5 {γ : ZMod 5} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (constrainedMaskSpaceMulti dom₅ 3 pts₂₃) qOne γ :=
  constrainedMaskMulti_hiding dom₅ pts₂₃ (by norm_num) qOne_inj qOne_ne_pts hγ

/-- The three points `{1, 2, 3}` — where the teeth witness is pinned to zero:
`1` by its opening, `2` and `3` by the constraints. -/
def qTri : Fin 3 → Fin 4 := ![1, 2, 3]

theorem qTri_inj : Function.Injective (dom₅ ∘ qTri) := by decide

/-- **Teeth (the bound)**: at `t = 2` queries `{0, 1}` the budget is blown —
`t + r = 4 > d = 3` — and surjectivity FAILS: the tuple `(1, 0)` is
unreachable. Any explaining mask would vanish at `1` (its opening), `2`, and
`3` (its constraints) — that is `d = 3` pinned symbols, so by
`open_determines` it IS the zero codeword, contradicting `f 0 = 1`. The bound
`t + r ≤ d` of `exists_constrainedMaskMulti_open` is exactly load-bearing:
one query too many defeats even the 2-constraint mask space. -/
theorem not_open_10_constrainedMaskMulti_F5 :
    ¬ ∃ mask ∈ constrainedMaskSpaceMulti dom₅ 3 pts₂₃,
        openSymbols ZkHidingExample.qLow mask = ![1, 0] := by
  rintro ⟨f, hf, hv⟩
  rw [mem_constrainedMaskSpaceMulti] at hf
  obtain ⟨hfRS, hfpts⟩ := hf
  have hzero : openSymbols qTri f = openSymbols qTri (0 : Fin 4 → ZMod 5) := by
    funext j
    fin_cases j
    · simpa [qTri, ZkHidingExample.qLow] using congrFun hv 1
    · simpa [qTri, pts₂₃] using hfpts 0
    · simpa [qTri, pts₂₃] using hfpts 1
  have hf0 : f = 0 :=
    open_determines dom₅ le_rfl qTri_inj hfRS (Submodule.zero_mem _) hzero
  have h1 : f 0 = 1 := by simpa [ZkHidingExample.qLow] using congrFun hv 0
  rw [hf0] at h1
  exact absurd h1 (by decide)

/-- The query sitting ON a constraint point. -/
def qHit : Fin 1 → Fin 4 := ![2]

/-- **Teeth (the disjointness)**: even INSIDE the budget (`t + r = 3 ≤ d`),
querying a constraint point defeats surjectivity — every mask in the space
opens to `0` there, so `![1]` is unreachable. The hypothesis
`∀ i j, q i ≠ pts j` is load-bearing, not decorative. -/
theorem not_open_1_at_constraint_F5 :
    ¬ ∃ mask ∈ constrainedMaskSpaceMulti dom₅ 3 pts₂₃,
        openSymbols qHit mask = ![1] := by
  rintro ⟨f, hf, hv⟩
  rw [mem_constrainedMaskSpaceMulti] at hf
  have h2 : f 2 = 0 := by simpa [pts₂₃] using hf.2 0
  have h1 : f 2 = 1 := by simpa [qHit] using congrFun hv 0
  rw [h2] at h1
  exact absurd h1 (by decide)

end ConstrainedMaskMultiExample

/-! ## Residual obligation — prose, not a stub

**`[CMASK-multi]` is CLOSED** — at full generality, not an `r = 2` slice:
`exists_constrainedMaskMulti_open` proves the surjectivity for EVERY `r`
(the nodal product carries the whole induction the r = 1 file predicted,
pre-packaged by Mathlib's `Lagrange.nodal` bookkeeping), the bound `t + r ≤ d`
exhibited BOTH tight (satisfiable at `t + r = d` on the F₅ keystone) and
load-bearing (refuted one query past it), the disjointness hypothesis also
exhibited load-bearing (a query AT a constraint point is refuted inside the
budget), and the surjectivity feeds through the existing reduction to genuine
`MaskedOpeningHiding` for the `r`-constraint space
(`constrainedMaskMulti_hiding`). No `[CMASK-multi-ind]` residual is needed:
nothing about general `r` was deferred.

**`[CMASK-dual-distance]`** — what genuinely remains, inherited verbatim from
the `r = 1` file and `ZKHiding.lean`: NON-EVALUATION linear constraint
channels. A general `LinearConstraint` weight vector `a` (not concentrated at
a domain point) admits no vanishing factor — there is no point `pt` with
`(X − dom pt)` to divide out, so the factorization above simply does not
start. The honest bound for the opening map's surjectivity on
`RS ⊓ ker(⟨a, ·⟩)` is the DUAL DISTANCE of the constrained code — a
Singleton-type bound on an arbitrary linear code, separate and harder
mathematics than interpolation. Open, named, not attempted, not faked.

`#print axioms` on `mem_constrainedMaskSpaceMulti`,
`constrainedMaskSpaceMulti_zero`, `constrainedMaskSpaceMulti_one`,
`coe_constrainedMaskSpaceMulti`, `exists_constrainedMaskMulti_open`,
`constrainedMaskMulti_hiding`,
`ConstrainedMaskMultiExample.quadWord_mem_multi`,
`ConstrainedMaskMultiExample.constrainedMaskMulti_surj_F5`,
`ConstrainedMaskMultiExample.constrainedMaskMulti_open_one_F5`,
`ConstrainedMaskMultiExample.constrainedMaskMulti_hiding_F5`,
`ConstrainedMaskMultiExample.not_open_10_constrainedMaskMulti_F5`,
`ConstrainedMaskMultiExample.not_open_1_at_constraint_F5`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage

