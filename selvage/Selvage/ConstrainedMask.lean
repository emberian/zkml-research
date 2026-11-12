/-
# Selvage.ConstrainedMask — gap (1) of `[OB-4-hiding-rbr]`: constrained-mask
surjectivity, `r = 1`.

`Selvage/ZKHiding.lean` proved masked-opening hiding for a mask ranging over the
WHOLE Reed–Solomon code (`rs_maskedOpeningHiding`), and named the sharper
question its own residual left open: in the accumulator the mask must ALSO
satisfy the mask claim's constraint channel (`Selvage/ZK.lean`'s `mask_bijOn`
consumes a mask from `satWords C B`), so the real mask space is an affine
subspace of the code, not the whole code. `maskedOpeningHiding_of_surj`
already reduces opening-hiding for ANY mask space to ONE property: the
opening map is surjective FROM that space. This file supplies that
surjectivity for the HOMOGENEOUS (target `0`) case of ONE evaluation-channel
constraint — the mask claim's kernel, `r = 1` of the residual's named
realizer — closing gap (1) at that instance.

**The argument (vanishing-polynomial factorization).** A degree-`< d`
polynomial `p` vanishing at a domain point `pt` factors as
`p = (X − dom pt) · p'` with `p'` of degree `< d − 1`. Choosing `p'` by
Lagrange interpolation through the `t` DESIRED values, each divided by
`(dom(qⱼ) − dom pt)` (well-defined: `pt` is never a query point), makes `p`
vanish at `pt` AND open to exactly the target tuple at the `t` queries —
using only `t ≤ d − 1`, i.e. `t + 1 ≤ d`: one query point's interpolation
budget is spent paying for the constraint. This is `exists_codeword_open`'s
proof (`Selvage/ZKHiding.lean`) run on the SCALED targets through the
vanishing factor, not a new principle.

**What is proved here:**

* `evalAtPt` / `constrainedMaskSpace` — the mask claim's homogeneous kernel
  for a single evaluation constraint, as a genuine `Submodule` (target `0`:
  no affine shift, unlike `ConstrainedCode.constrainedRS` in general).
  `coe_constrainedMaskSpace` connects it back to that file's constraint
  vocabulary: it IS `constrainedRS dom d [evalConstraint pt 0]`.
* `exists_constrainedMask_open` — **the surjectivity theorem**: for
  `t + 1 ≤ d`, distinct query points none equal to `pt`, every `t`-tuple is
  opened by some mask in the constrained space. Genuine linear algebra
  (Lagrange interpolation composed with a vanishing-factor division), not a
  restatement.
* `constrainedMask_hiding` — **the connection**: feeding the surjectivity
  into `maskedOpeningHiding_of_surj` gives `MaskedOpeningHiding` for the
  CONSTRAINED mask space, at the tightened bound `t + 1 ≤ d`. Gap (1) of
  `[OB-4-hiding-rbr]` closed for `r = 1`: the mask CAN be constraint-respecting
  and still hide.
* **Keystones over F₅**, `RS[F₅, {0,1,2,3}, 2]` (`ReedSolomon.RSExample`),
  constrained by vanishing at the domain point `pt₃ = 3`: `lineOf 2 3`
  (`= 2 + X`) witnesses the space is nontrivial; `constrainedMask_surj_F5` /
  `constrainedMask_open_one_F5` fire the surjectivity AT the tight bound
  `t + 1 = d = 2` (`t = 1`), the second one a fully computed witness
  (`lineOf 1 4`); `not_open_10_constrainedMask_F5` exhibits an UNREACHABLE
  tuple at `t = d = 2` (`t + 1 = 3 > d`) — the bound is load-bearing, one
  query too many defeats even a single-constraint mask.

**What stays prose-residual — `[CMASK-multi]`:** general `r` (several
evaluation constraints, at `r` distinct points, all distinct from the query
points and each other) iterates this file's factorization — divide by
`r` vanishing factors instead of one, spend `r` of the `d` degrees of
freedom, giving `t + r ≤ d` — and is routine but unproved here (a genuine
induction on the constraint list, not a new idea). Non-evaluation LINEAR
channels (an arbitrary `LinearConstraint` weight vector, not concentrated at
a domain point) are NOT handled by vanishing-factor division at all: the
`r = 1` proof below needs `pt` to be a domain point disjoint from the
queries so the factor `(X − dom pt)` is available; a general weight vector
`a` has no such point to divide by, and (as ZKHiding's own residual already
flagged) the general bound is the DUAL DISTANCE of the constrained code —
open, not attempted here.
-/
import Mathlib.LinearAlgebra.Lagrange
import Selvage.ZKHiding
import Selvage.ConstrainedCode
import Selvage.ReedSolomon

namespace Minidregg.Selvage

variable {F : Type*} [Field F] {ι : Type*} {t d : ℕ}

/-! ## The constrained mask space: `RS ⊓ ker(eval at a point)` -/

/-- Evaluation at a fixed index, as a linear map on words. Its kernel,
intersected with the RS code, is the mask claim's homogeneous solution space
for the single evaluation constraint `f(pt) = 0`. -/
def evalAtPt (pt : ι) : (ι → F) →ₗ[F] F where
  toFun f := f pt
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalAtPt_apply (pt : ι) (f : ι → F) : evalAtPt pt f = f pt := rfl

/-- **The constrained mask space** at a domain point `pt`: codewords of
`RS[F, dom, d]` that ALSO vanish at `pt` — the mask claim's homogeneous
kernel for the single evaluation constraint `evalConstraint pt 0`. A genuine
`Submodule` (the target is `0`, so no affine shift), which is exactly what
`maskedOpeningHiding_of_surj`'s `C` argument needs. -/
noncomputable def constrainedMaskSpace (dom : ι ↪ F) (d : ℕ) (pt : ι) : Submodule F (ι → F) :=
  reedSolomonCode dom d ⊓ LinearMap.ker (evalAtPt (F := F) pt)

@[simp] theorem mem_constrainedMaskSpace {dom : ι ↪ F} {d : ℕ} {pt : ι} {f : ι → F} :
    f ∈ constrainedMaskSpace dom d pt ↔ f ∈ reedSolomonCode dom d ∧ f pt = 0 := by
  simp [constrainedMaskSpace, LinearMap.mem_ker]

/-- The constrained mask space IS the mask claim's constraint space in
`ConstrainedCode`'s vocabulary: it coincides with `constrainedRS` at the
homogeneous evaluation constraint `evalConstraint pt 0`. The reduction
theorem needs a `Submodule` (hence the definition above); this connects it
back to the constraint channel the accumulator's mask claim actually
speaks, for a `LinearConstraint`-shaped audit of what got closed. -/
theorem coe_constrainedMaskSpace [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (dom : ι ↪ F) (d : ℕ) (pt : ι) :
    (constrainedMaskSpace dom d pt : Set (ι → F))
      = constrainedRS dom d [evalConstraint pt (0 : F)] := by
  ext f
  simp [mem_constrainedMaskSpace, mem_constrainedRS_iff, satisfies_evalConstraint_iff]

/-! ## Constrained-mask surjectivity (`r = 1`): the vanishing-factor argument -/

/-- **Constrained-mask surjectivity, `r = 1`.** For `t + 1 ≤ d` distinct
query points, none of them equal to the constraint point `pt`: every
`t`-tuple of symbol values is opened by SOME mask in the constrained space —
a codeword vanishing at `pt` AND matching the desired values at the `t`
queries. Vanishing-polynomial factorization: `p = (X − dom pt) · p'`, with
`p'` interpolating the target values scaled by `(dom(qⱼ) − dom pt)⁻¹`
through the `t` query points (degree `< t ≤ d − 1` by
`Lagrange.degree_interpolate_lt`), so `p` has degree `< d`, vanishes at `pt`
by construction, and opens to `v` at the queries because `dom(qⱼ) ≠ dom pt`
(from `pt ≠ qⱼ` and injectivity of `dom`). This is `[OB-4-hiding-rbr]`'s
named realizer at `r = 1`: a real bound, `t + 1 ≤ d`, not a restatement of
the unconstrained `exists_codeword_open`. -/
theorem exists_constrainedMask_open (dom : ι ↪ F) (pt : ι) (ht : t + 1 ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (hpt : ∀ j, q j ≠ pt)
    (v : Fin t → F) :
    ∃ mask ∈ constrainedMaskSpace dom d pt, openSymbols q mask = v := by
  classical
  set w : Fin t → F := fun j => v j / (dom (q j) - dom pt) with hw_def
  set p' : Polynomial F := Lagrange.interpolate Finset.univ (dom ∘ q) w with hp'_def
  set p : Polynomial F := (Polynomial.X - Polynomial.C (dom pt)) * p' with hp_def
  have hp'deg : p'.degree < (t : WithBot ℕ) := by
    have hdeg := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := dom ∘ q) w hq.injOn
    rwa [Finset.card_univ, Fintype.card_fin] at hdeg
  have hp'eval : ∀ j, p'.eval (dom (q j)) = w j := fun j =>
    Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := dom ∘ q) w hq.injOn
      (Finset.mem_univ j)
  have hpdeg : p.degree < (d : WithBot ℕ) := by
    have h1 : p.degree ≤ (Polynomial.X - Polynomial.C (dom pt) : Polynomial F).degree
        + p'.degree := Polynomial.degree_mul_le _ _
    have h2 : (Polynomial.X - Polynomial.C (dom pt) : Polynomial F).degree = 1 :=
      Polynomial.degree_X_sub_C _
    rw [h2] at h1
    have h3 : (1 : WithBot ℕ) + p'.degree < 1 + (t : WithBot ℕ) :=
      WithBot.add_lt_add_left (by simp) hp'deg
    have h4 : (1 : WithBot ℕ) + (t : WithBot ℕ) ≤ (d : WithBot ℕ) := by
      have hcast : ((t + 1 : ℕ) : WithBot ℕ) ≤ (d : WithBot ℕ) := by exact_mod_cast ht
      rwa [Nat.cast_add, Nat.cast_one, add_comm] at hcast
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h3 h4)
  refine ⟨evalOnDomain dom p, ?_, ?_⟩
  · rw [mem_constrainedMaskSpace]
    refine ⟨mem_reedSolomonCode_iff.mpr ⟨p, hpdeg, fun i => rfl⟩, ?_⟩
    rw [evalOnDomain_apply, hp_def]
    simp
  · funext j
    rw [openSymbols_apply, evalOnDomain_apply, hp_def]
    have hne : dom (q j) - dom pt ≠ 0 := sub_ne_zero.mpr (fun h => hpt j (dom.injective h))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      hp'eval j, hw_def]
    rw [mul_comm, div_mul_cancel₀ _ hne]

/-! ## The connection: constrained-mask hiding -/

/-- **Constrained-mask hiding, `r = 1`**: gap (1) of `[OB-4-hiding-rbr]`
closed for a single homogeneous evaluation constraint — masked-opening
hiding holds even when the mask is confined to the mask claim's kernel, at
the same `γ ≠ 0` dial and the tightened bound `t + 1 ≤ d`. Fed directly
through `maskedOpeningHiding_of_surj`; the fiber-bijection/simulator
machinery is NOT re-derived, only the surjectivity premise is supplied. -/
theorem constrainedMask_hiding (dom : ι ↪ F) (pt : ι) (ht : t + 1 ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (hpt : ∀ j, q j ≠ pt)
    {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (constrainedMaskSpace dom d pt) q γ :=
  maskedOpeningHiding_of_surj _ q hγ (exists_constrainedMask_open dom pt ht hq hpt)

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]` (`ReedSolomon.RSExample`, lines `a + bX`),
constrained by vanishing at the domain point `pt₃ = 3`: the constrained mask
space is the lines `a + bX` with `a + 3b = 0`, i.e. `a = 2b` — a genuine
1-dimensional subspace (5 codewords out of the 25 = `|F₅|²` lines). -/

namespace ConstrainedMaskExample

open RSExample

/-- The constraint point: domain value `3`. -/
def pt₃ : Fin 4 := 3

/-- The single query point `0`, at the tight bound `t = 1`, `t + 1 = d = 2`. -/
def qOne : Fin 1 → Fin 4 := ![0]

theorem qOne_inj : Function.Injective (dom₅ ∘ qOne) := by decide

theorem qOne_ne_pt₃ : ∀ j, qOne j ≠ pt₃ := by decide

/-- **Premise inhabitation**: the constrained mask space is nontrivial — the
line `2 + X` (`= ZkHidingExample.lineOf 2 3`) vanishes at `pt₃ = 3`
(`2 + 3 = 5 = 0`) and is nonzero. -/
theorem lineOf_2_3_mem : ZkHidingExample.lineOf 2 3 ∈ constrainedMaskSpace dom₅ 2 pt₃ := by
  rw [mem_constrainedMaskSpace]
  exact ⟨ZkHidingExample.lineOf_mem 2 3, by decide⟩

theorem lineOf_2_3_ne_zero : ZkHidingExample.lineOf 2 3 ≠ 0 := by decide

/-- **Satisfiable**: the general surjectivity theorem applied at the tight
bound `t + 1 = d = 2` — every single-symbol target is reachable from the
constrained mask space. -/
theorem constrainedMask_surj_F5 (v : Fin 1 → ZMod 5) :
    ∃ mask ∈ constrainedMaskSpace dom₅ 2 pt₃, openSymbols qOne mask = v :=
  exists_constrainedMask_open dom₅ pt₃ (by norm_num) qOne_inj qOne_ne_pt₃ v

/-- **Satisfiable, computed end-to-end**: the concrete mask `1 + 3X`
(`= lineOf 1 4`) vanishes at `pt₃ = 3` (`1 + 9 = 10 = 0`) and opens to `![1]`
at `qOne` — the surjectivity theorem's construction exhibited on real data,
not just asserted. -/
theorem constrainedMask_open_one_F5 :
    ZkHidingExample.lineOf 1 4 ∈ constrainedMaskSpace dom₅ 2 pt₃ ∧
      openSymbols qOne (ZkHidingExample.lineOf 1 4) = ![1] := by
  refine ⟨?_, ?_⟩
  · rw [mem_constrainedMaskSpace]
    exact ⟨ZkHidingExample.lineOf_mem 1 4, by decide⟩
  · rw [openSymbols_eq_comp]; decide

/-- **The hiding theorem, instantiated**: masked-opening hiding for the
constrained mask space fires at the tight bound, every nonzero challenge. -/
theorem constrainedMask_hiding_F5 {γ : ZMod 5} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt₃) qOne γ :=
  constrainedMask_hiding dom₅ pt₃ (by norm_num) qOne_inj qOne_ne_pt₃ hγ

/-- **Teeth**: at `t = d = 2` (one query beyond the tight bound
`t + 1 ≤ d`), the constrained mask space's openings at
`ZkHidingExample.qPair` trace out only the F₅-multiples of `(2, 4)`
(`f(0) = a = 2b`, `f(2) = a + 2b = 4b` for the constraint-solving line
`a = 2b`) — 5 of the 25 possible tuples, not all of them. The tuple
`(1, 0)` is UNREACHABLE: the unique degree-`< 2` codeword opening to
`(1, 0)` at `{0, 2}` is `lineOf 1 3` (`= 1 + 2X`, computed), which does NOT
vanish at `pt₃` (`1 + 6 = 7 = 2 ≠ 0`). The bound `t + 1 ≤ d` of
`exists_constrainedMask_open` is exactly load-bearing — one query too many
defeats surjectivity even confined to a single homogeneous constraint. -/
theorem not_open_10_constrainedMask_F5 :
    ¬ ∃ mask ∈ constrainedMaskSpace dom₅ 2 pt₃,
        openSymbols ZkHidingExample.qPair mask = ![1, 0] := by
  rintro ⟨f, hf, hv⟩
  rw [mem_constrainedMaskSpace] at hf
  obtain ⟨hfRS, hfpt⟩ := hf
  have hcand : openSymbols ZkHidingExample.qPair (ZkHidingExample.lineOf 1 3) = ![1, 0] := by
    rw [openSymbols_eq_comp]; decide
  have hfeq : f = ZkHidingExample.lineOf 1 3 :=
    open_determines dom₅ le_rfl ZkHidingExample.qPair_inj hfRS
      (ZkHidingExample.lineOf_mem 1 3) (hv.trans hcand.symm)
  have hcontra : (ZkHidingExample.lineOf 1 3) pt₃ = 0 := hfeq ▸ hfpt
  revert hcontra
  decide

end ConstrainedMaskExample

/-! ## Residual obligation — prose, not a stub

**`[CMASK-multi]`** — general `r`: a mask constrained by `r` evaluation
claims at `r` distinct domain points (all distinct from the query points and
from each other) reaches every `t`-tuple whenever `t + r ≤ d`, by iterating
this file's factorization: divide the interpolant by ALL `r` vanishing
factors `∏ₖ (X − dom ptₖ)` at once (a degree-`r` divisor), leaving a free
interpolation problem of degree `< d − r` through the `t` queries — the
`r = 1` argument's induction step, not a new idea, but genuinely unproved
here (the closed form of "value at `qⱼ` divided by the product of `r`
distinct nonzero factors" and its degree bookkeeping is more bookkeeping
than the single-factor case, not more mathematics). General LINEAR
channels (an arbitrary `LinearConstraint` weight vector not concentrated at
a domain point) are NOT reachable by vanishing-factor division at all — no
single point to divide out — and, per `ZKHiding.lean`'s original residual,
the honest bound there is the DUAL DISTANCE of the constrained code, which
is separate, harder mathematics (a Singleton-type bound on an arbitrary
linear code, not interpolation): open.

What THIS file closes: for the evaluation-constraint case, `r = 1`,
constrained-mask surjectivity is a THEOREM (`exists_constrainedMask_open`),
non-vacuously — the bound `t + 1 ≤ d` is exhibited BOTH tight (satisfiable
at `t + 1 = d`) and load-bearing (refuted one query past it), and it feeds
straight through the existing reduction to genuine `MaskedOpeningHiding` for
the constrained space (`constrainedMask_hiding`), with no re-derivation of
`ZKHiding.lean`'s fiber/simulator machinery.

`#print axioms` on `evalAtPt_apply`, `mem_constrainedMaskSpace`,
`coe_constrainedMaskSpace`, `exists_constrainedMask_open`,
`constrainedMask_hiding`, `ConstrainedMaskExample.lineOf_2_3_mem`,
`ConstrainedMaskExample.constrainedMask_surj_F5`,
`ConstrainedMaskExample.constrainedMask_open_one_F5`,
`ConstrainedMaskExample.constrainedMask_hiding_F5`,
`ConstrainedMaskExample.not_open_10_constrainedMask_F5`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
