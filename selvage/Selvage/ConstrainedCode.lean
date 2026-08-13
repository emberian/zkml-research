/-
# Selvage.ConstrainedCode — the WHIR constrained Reed–Solomon code (Def 4.5): the
claim object the accumulator folds.

WHIR (eprint 2024/1586) Definition 4.5:
`CRS[F, L, m, ŵ, σ] := { f ∈ RS[F, L, m] : Σ_{b ∈ {0,1}^m} ŵ(f̂(b), b) = σ }` —
a Reed–Solomon codeword whose multilinear extension `f̂` additionally satisfies a
weighted sum constraint. `CRS[F, L, m, 0, 0] = RS[F, L, m]` (unconstrained), the
evaluation claim `f̂(z) = σ` is the weight `ŵ(Z, X) = Z·eq(z, X)`, and the
multi-constrained code is the intersection over a list `((ŵᵢ, σᵢ))ᵢ`.

**v0 representation decision (stated, not hidden).** For the PCS instantiation
WHIR needs only the LINEAR weight class `ŵ(Z, X) = Z·â(X)`, under which the
constraint is a linear functional of the codeword: `Σ_b f̂(b)·â(b)` is linear in
`f` (the coefficient/MLE map and the weighted hypercube sum are both linear). So
minidregg's constraint channel is `LinearConstraint`: a weight vector
`wt : ι → F` on the evaluation domain plus a target, satisfaction being
`⟨f, wt⟩ = Σᵢ wt i * f i = target`. This LOSES NOTHING within the linear class:
`exists_dotWt_eq` PROVES every linear functional on `ι → F` has this form
(finite-dimensional representation along the coordinate basis), so any linear-ŵ
constraint — in particular any MLE weighted sum, once transported through the
fixed linear coefficient map — lands in this channel. What v0 does NOT model is
NONLINEAR ŵ (the general Σ-IOP weights of WHIR §5.1); that is future vocabulary,
out of scope for the PCS/accumulator floor, and this file never claims it. The
domain-point evaluation claim `f(pt) = σ` is the instance `evalConstraint`
(`satisfies_evalConstraint_iff`), the discrete `Z·eq` weight.

This is docs/LOOM-RECOMPOSITION.md §6's constraint channel: "points + targets,
γ-linear in both" — `LinearConstraint` is the channel entry, and γ-linearity in
both components is exactly what `batchConstraint` exercises.

**What is proved here (no sorry, no axioms):**

* `constrainedRS_nil`: the empty constraint list gives back exactly the RS code —
  Def 4.5's `CRS[…, 0, 0] = RS`.
* `constrainedRS_subset_code`: constraints only shrink (every constrained code
  sits inside `reedSolomonCode`); `constrainedRS_anti`: more constraints, smaller
  code.
* `constrainedRS_append`: concatenating constraint lists intersects the codes —
  multi-constraint = intersection, the closure the accumulator's claim-merging
  needs (two CRS claims on ONE word over ONE code merge to a CRS claim).
* **γ-power batching, completeness direction (WHIR Constr. 5.5)**:
  `satisfies_batch_of_forall` — a word satisfying all `t` constraints satisfies
  the single γ-batched constraint `⟨f, Σₖ γᵏ·wtₖ⟩ = Σₖ γᵏ·σₖ`, for EVERY γ. Pure
  linear algebra (`dotWt` linearity down a Horner spine). Code-level form:
  `constrainedRS_subset_batch`. Closed γ-power forms of the Horner definitions:
  `batchWt_eq_sum`, `batchTarget_eq_sum` — the paper-verbatim `Σ γ^{k}·(·)ₖ`.
* **Exact-word batching soundness (Schwartz–Zippel teeth)**:
  `card_batch_satisfying_le` — if the word VIOLATES some constraint of the list,
  then at most `t − 1` choices of `γ ∈ F` make the batched constraint pass: the
  defect polynomial `Σₖ (⟨f, wtₖ⟩ − σₖ)·Xᵏ` is nonzero of degree `< t`, root
  counting as in `ReedSolomon.card_agreeSet_lt_of_ne`. Over uniform γ this is
  error `(t−1)/|F|` for exact words.

**What stays prose-residual — `[CRS-batch-sound]`:** WHIR Constr. 5.5's full
round-by-round soundness is the PROXIMITY statement: a word δ-CLOSE to the
γ-batched code (for more than a `(t−1)·ℓ/|F|` fraction of γ, ℓ the list size at
radius δ in the mutual-correlated-agreement regime) is δ-close to the
multi-constrained code. That needs the list-decoding/mutual-CA machinery of
`Selvage/CorrelatedAgreement.lean` wired to constrained codes and is FUTURE WORK,
carried here only as prose (per the ReedSolomon.lean precedent for Thm 4.8:
naming a Prop we can't yet inhabit responsibly would be faking; the exact-word
theorem above is the machine-checked kernel of the same argument — same defect
polynomial, same root count — the residual is the lift from exact membership to
δ-proximity). No axiom, no placeholder instance.
⟲ STATUS: the lift is now a THEOREM in `Selvage/AccSound.lean`
(`accSound_batch_proximity`: `(t−1)·ℓ/|F|` with the δ-ball list size ℓ as
hypothesis, union bound over the list priced by this file's kernel;
`accSound_batch_proximity_UD`: ℓ = 1 discharged at unique decoding). What
remains of `[CRS-batch-sound]` is supplying ℓ in the beyond-UD regimes —
`[ACC-sound-list]` in that file's ledger.

**Keystone hygiene (ATLAS: satisfiable + teeth, BUILT):** over `F₅` on
`RSExample`'s 4-point domain, `CRSExample.xWord_mem_constrainedRS` exhibits a
concrete codeword IN a concretely-constrained code (an evaluation claim,
`decide`-checked); `CRSExample.zero_mem_code_not_constrained` exhibits a word in
the RS code but NOT in the constrained one (the shrink is STRICT:
`constrainedRS_ssubset_example`). The batch bound is exercised TIGHTLY: for the
violating word, exactly `1 = t − 1` of the 5 possible γ satisfy the batch
(`batch_teeth_card_eq`), so `card_batch_satisfying_le` is attained, not slack.
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.ReedSolomon

namespace Minidregg.Selvage

open Polynomial

/-- A LINEAR constraint on words `ι → F` — one entry of §6's constraint channel.
WHIR Def 4.5's weighted-sum constraint, restricted to the linear weight class
`ŵ(Z, X) = Z·â(X)` the PCS uses: the weight vector `wt` is `â` sampled on the
index set, `target` is `σ`, and satisfaction is `⟨f, wt⟩ = target`. By
`exists_dotWt_eq` this class is exactly the linear functionals on `ι → F`. -/
structure LinearConstraint (ι F : Type*) where
  /-- The weight vector `â` on the domain: the constraint reads `Σᵢ wt i * f i`. -/
  wt : ι → F
  /-- The claimed sum value `σ`. -/
  target : F

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The constraint pairing and its linearity -/

omit [DecidableEq ι] [DecidableEq F] in
/-- The pairing `⟨a, f⟩ = Σᵢ a i * f i` — the linear functional a constraint
applies to the word. -/
def dotWt (a f : ι → F) : F := ∑ i, a i * f i

omit [DecidableEq ι] [DecidableEq F] in
@[simp] theorem dotWt_zero_left (f : ι → F) : dotWt (0 : ι → F) f = 0 := by
  simp [dotWt]

omit [DecidableEq ι] [DecidableEq F] in
theorem dotWt_add_left (a b f : ι → F) :
    dotWt (a + b) f = dotWt a f + dotWt b f := by
  simp [dotWt, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] [DecidableEq F] in
theorem dotWt_smul_left (γ : F) (a f : ι → F) :
    dotWt (γ • a) f = γ * dotWt a f := by
  simp [dotWt, Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] [DecidableEq F] in
/-- **Completeness of the constraint class**: EVERY linear functional on words
is `dotWt` of some weight vector (its values on the coordinate basis). Hence the
`LinearConstraint` channel captures every linear-ŵ claim of WHIR Def 4.5 — any
MLE weighted sum included, transported through the fixed linear coefficient
map — with no loss. -/
theorem exists_dotWt_eq (φ : (ι → F) →ₗ[F] F) :
    ∃ a : ι → F, ∀ f : ι → F, dotWt a f = φ f := by
  classical
  refine ⟨fun i => φ fun j => if i = j then 1 else 0, fun f => ?_⟩
  conv_rhs => rw [pi_eq_sum_univ f, map_sum]
  simp [dotWt, mul_comm]

/-- `f` satisfies the constraint `c` when the pairing meets the target:
`⟨c.wt, f⟩ = c.target`. -/
def Satisfies (f : ι → F) (c : LinearConstraint ι F) : Prop :=
  dotWt c.wt f = c.target

omit [DecidableEq ι] in
instance {f : ι → F} {c : LinearConstraint ι F} : Decidable (Satisfies f c) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## The constrained Reed–Solomon code (WHIR Def 4.5, linear class) -/

omit [DecidableEq ι] [DecidableEq F] in
/-- **The multi-constrained Reed–Solomon code** `CRS[F, dom, d, cs]`: codewords
of `reedSolomonCode dom d` satisfying every constraint in the list `cs`. A `Set`,
not a `Submodule`: a nonzero target cuts an AFFINE slice, so linearity is not
available (and not claimed). The empty list recovers `RS` (`constrainedRS_nil` —
Def 4.5's `CRS[…,0,0] = RS`). -/
def constrainedRS (dom : ι ↪ F) (d : ℕ) (cs : List (LinearConstraint ι F)) :
    Set (ι → F) :=
  {f | f ∈ reedSolomonCode dom d ∧ ∀ c ∈ cs, Satisfies f c}

omit [DecidableEq ι] [DecidableEq F] in
theorem mem_constrainedRS_iff {dom : ι ↪ F} {d : ℕ}
    {cs : List (LinearConstraint ι F)} {f : ι → F} :
    f ∈ constrainedRS dom d cs ↔
      f ∈ reedSolomonCode dom d ∧ ∀ c ∈ cs, Satisfies f c :=
  Iff.rfl

omit [DecidableEq ι] [DecidableEq F] in
/-- The unconstrained case: `CRS[F, dom, d, []] = RS[F, dom, d]` — WHIR Def 4.5's
`CRS[…, 0, 0] = RS`. -/
@[simp] theorem constrainedRS_nil (dom : ι ↪ F) (d : ℕ) :
    constrainedRS dom d ([] : List (LinearConstraint ι F))
      = (reedSolomonCode dom d : Set (ι → F)) := by
  ext f
  simp [constrainedRS]

omit [DecidableEq ι] [DecidableEq F] in
/-- Constraints only shrink: every constrained code is a subset of the RS code. -/
theorem constrainedRS_subset_code (dom : ι ↪ F) (d : ℕ)
    (cs : List (LinearConstraint ι F)) :
    constrainedRS dom d cs ⊆ (reedSolomonCode dom d : Set (ι → F)) :=
  fun _ hf => hf.1

omit [DecidableEq ι] [DecidableEq F] in
/-- Antitone in the constraint list: a larger list cuts a smaller code. -/
theorem constrainedRS_anti (dom : ι ↪ F) (d : ℕ)
    {cs₁ cs₂ : List (LinearConstraint ι F)} (h : ∀ c ∈ cs₁, c ∈ cs₂) :
    constrainedRS dom d cs₂ ⊆ constrainedRS dom d cs₁ :=
  fun _ hf => ⟨hf.1, fun c hc => hf.2 c (h c hc)⟩

omit [DecidableEq ι] [DecidableEq F] in
/-- **Multi-constraint = intersection**: concatenating constraint lists
intersects the codes. The closure the accumulator needs — two CRS claims on one
word over one code merge (list concatenation) into a single CRS claim whose code
is exactly the intersection. -/
theorem constrainedRS_append (dom : ι ↪ F) (d : ℕ)
    (cs₁ cs₂ : List (LinearConstraint ι F)) :
    constrainedRS dom d (cs₁ ++ cs₂)
      = constrainedRS dom d cs₁ ∩ constrainedRS dom d cs₂ := by
  ext f
  simp only [Set.mem_inter_iff, mem_constrainedRS_iff, List.mem_append, or_imp,
    forall_and]
  tauto

/-! ## The evaluation claim as a constraint

WHIR Def 4.5's special weight `ŵ(Z, X) = Z·eq(z, X)` at a DOMAIN point: the
weight vector is the coordinate indicator, and satisfaction is literally
`f pt = σ`. (Out-of-domain evaluation claims of `f̂` are also linear functionals
of the word, hence in the channel by `exists_dotWt_eq`; the indicator form is
the in-domain instance, enough for the v0 keystones.) -/

/-- The evaluation claim `f(pt) = σ` as a linear constraint: indicator weight at
`pt`, target `σ`. -/
def evalConstraint (pt : ι) (σ : F) : LinearConstraint ι F where
  wt := fun i => if i = pt then 1 else 0
  target := σ

omit [DecidableEq F] in
/-- The evaluation constraint says exactly `f pt = σ`. -/
theorem satisfies_evalConstraint_iff {f : ι → F} {pt : ι} {σ : F} :
    Satisfies f (evalConstraint pt σ) ↔ f pt = σ := by
  unfold Satisfies evalConstraint dotWt
  simp [ite_mul, Finset.sum_ite_eq']

/-! ## γ-power batching (WHIR Construction 5.5)

`t` constraints on ONE word batch to ONE constraint by powers of a challenge γ:
weight `Σₖ γᵏ·wtₖ`, target `Σₖ γᵏ·σₖ` (defined in Horner form for clean
induction; the closed γ-power forms are `batchWt_eq_sum` / `batchTarget_eq_sum`).
Both channels are γ-linear — §6's "points + targets, γ-linear in both". -/

/-- Batched weight vector, Horner form: `batchWt γ [c₀, …, c_{t−1}] =
c₀.wt + γ • (c₁.wt + γ • (…))` `= Σₖ γᵏ • cₖ.wt`. -/
def batchWt (γ : F) : List (LinearConstraint ι F) → (ι → F)
  | [] => 0
  | c :: cs => c.wt + γ • batchWt γ cs

/-- Batched target, Horner form: `= Σₖ γᵏ * cₖ.target`. -/
def batchTarget (γ : F) : List (LinearConstraint ι F) → F
  | [] => 0
  | c :: cs => c.target + γ * batchTarget γ cs

/-- The γ-batched constraint of a constraint list (WHIR Constr. 5.5's single
folded claim). -/
def batchConstraint (γ : F) (cs : List (LinearConstraint ι F)) :
    LinearConstraint ι F :=
  ⟨batchWt γ cs, batchTarget γ cs⟩

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Closed form: the batched weight is the γ-power combination `Σₖ γᵏ • cₖ.wt`. -/
theorem batchWt_eq_sum (γ : F) (cs : List (LinearConstraint ι F)) :
    batchWt γ cs = ∑ k : Fin cs.length, γ ^ (k : ℕ) • (cs[(k : ℕ)]).wt := by
  induction cs with
  | nil => simp [batchWt]
  | cons c cs ih =>
      rw [batchWt, ih]
      simp [Fin.sum_univ_succ, Finset.smul_sum, smul_smul, pow_succ']

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Closed form: the batched target is the γ-power combination `Σₖ γᵏ * σₖ`. -/
theorem batchTarget_eq_sum (γ : F) (cs : List (LinearConstraint ι F)) :
    batchTarget γ cs = ∑ k : Fin cs.length, γ ^ (k : ℕ) * (cs[(k : ℕ)]).target := by
  induction cs with
  | nil => simp [batchTarget]
  | cons c cs ih =>
      rw [batchTarget, ih]
      simp [Fin.sum_univ_succ, Finset.mul_sum, pow_succ', mul_assoc]

omit [DecidableEq ι] [DecidableEq F] in
/-- **γ-power batching, completeness (WHIR Constr. 5.5, forward direction).**
A word satisfying ALL constraints of the list satisfies the γ-batched
constraint, for EVERY γ: pairing linearity down the Horner spine. This is the
direction the accumulator's fold uses to carry honest claims. -/
theorem satisfies_batch_of_forall (γ : F) {f : ι → F}
    {cs : List (LinearConstraint ι F)} (h : ∀ c ∈ cs, Satisfies f c) :
    Satisfies f (batchConstraint γ cs) := by
  induction cs with
  | nil => simp [Satisfies, batchConstraint, batchWt, batchTarget]
  | cons c cs ih =>
      have hc : Satisfies f c := h c (List.mem_cons_self ..)
      have hcs : Satisfies f (batchConstraint γ cs) :=
        ih fun c' hc' => h c' (List.mem_cons_of_mem c hc')
      simp only [Satisfies, batchConstraint, batchWt, batchTarget] at hc hcs ⊢
      rw [dotWt_add_left, dotWt_smul_left, hc, hcs]

omit [DecidableEq ι] [DecidableEq F] in
/-- Code-level completeness of the fold: the multi-constrained code sits inside
the singly-constrained code of its γ-batch, for every γ. -/
theorem constrainedRS_subset_batch (dom : ι ↪ F) (d : ℕ) (γ : F)
    (cs : List (LinearConstraint ι F)) :
    constrainedRS dom d cs ⊆ constrainedRS dom d [batchConstraint γ cs] := by
  rintro f ⟨hrs, hcs⟩
  refine ⟨hrs, fun c hc => ?_⟩
  rw [List.mem_singleton] at hc
  subst hc
  exact satisfies_batch_of_forall γ hcs

/-! ### Exact-word soundness of the batch: root counting

The defect polynomial `Σₖ (⟨f, wtₖ⟩ − σₖ)·Xᵏ` evaluates at γ to (batched pairing
− batched target). If `f` violates some constraint, it is a NONZERO polynomial
of degree `< t`, so at most `t − 1` challenges γ let the batch pass — over
uniform γ, error `(t−1)/|F|` for EXACT words. The lift from exact membership to
δ-proximity (error `(t−1)·ℓ/|F|`, ℓ the list size in the mutual-CA regime) is
the prose residual `[CRS-batch-sound]` — see the module docstring. -/

/-- The defect polynomial of a word against a constraint list: coefficient `k`
is the `k`-th constraint's violation `⟨f, wtₖ⟩ − σₖ` (Horner form). -/
noncomputable def defectPoly (f : ι → F) : List (LinearConstraint ι F) → Polynomial F
  | [] => 0
  | c :: cs => C (dotWt c.wt f - c.target) + X * defectPoly f cs

omit [DecidableEq ι] [DecidableEq F] in
/-- Evaluating the defect polynomial at γ measures the γ-batch's violation. -/
theorem defectPoly_eval (f : ι → F) (γ : F) (cs : List (LinearConstraint ι F)) :
    (defectPoly f cs).eval γ = dotWt (batchWt γ cs) f - batchTarget γ cs := by
  induction cs with
  | nil => simp [defectPoly, batchWt, batchTarget]
  | cons c cs ih =>
      simp only [defectPoly, batchWt, batchTarget, eval_add, eval_mul, eval_C,
        eval_X, dotWt_add_left, dotWt_smul_left, ih]
      ring

omit [DecidableEq ι] [DecidableEq F] in
/-- The γ-batch passes iff γ is a root of the defect polynomial. -/
theorem satisfies_batch_iff_defect_root {f : ι → F} {γ : F}
    {cs : List (LinearConstraint ι F)} :
    Satisfies f (batchConstraint γ cs) ↔ (defectPoly f cs).eval γ = 0 := by
  rw [defectPoly_eval, sub_eq_zero]
  exact Iff.rfl

omit [DecidableEq ι] [DecidableEq F] in
/-- The defect polynomial's degree is below the number of constraints. -/
theorem defectPoly_degree_lt (f : ι → F) (cs : List (LinearConstraint ι F)) :
    (defectPoly f cs).degree < (cs.length : WithBot ℕ) := by
  induction cs with
  | nil => simp [defectPoly]
  | cons c cs ih =>
      rw [defectPoly, List.length_cons]
      have hpos : (0 : WithBot ℕ) < ((cs.length + 1 : ℕ) : WithBot ℕ) := by
        exact_mod_cast Nat.succ_pos cs.length
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_C_le hpos
      · rcases eq_or_ne (defectPoly f cs) 0 with h0 | h0
        · simp only [h0, mul_zero, degree_zero]
          exact WithBot.bot_lt_coe _
        · rw [degree_mul, degree_X]
          calc 1 + (defectPoly f cs).degree
              < 1 + (cs.length : WithBot ℕ) :=
                WithBot.add_lt_add_left (by simp) ih
            _ = ((cs.length + 1 : ℕ) : WithBot ℕ) := by
                push_cast; rw [add_comm]

omit [DecidableEq ι] [DecidableEq F] in
/-- A violated constraint makes the defect polynomial nonzero. -/
theorem defectPoly_ne_zero {f : ι → F} {cs : List (LinearConstraint ι F)}
    (h : ∃ c ∈ cs, ¬ Satisfies f c) : defectPoly f cs ≠ 0 := by
  induction cs with
  | nil => obtain ⟨c, hc, -⟩ := h; exact absurd hc (List.not_mem_nil)
  | cons c cs ih =>
      obtain ⟨c', hc', hviol⟩ := h
      rcases List.mem_cons.mp hc' with rfl | htail
      · -- head violated: constant coefficient is the nonzero violation
        intro h0
        have hcoeff : (defectPoly f (c' :: cs)).coeff 0
            = dotWt c'.wt f - c'.target := by
          simp [defectPoly, coeff_add, coeff_C]
        rw [h0, coeff_zero] at hcoeff
        exact hviol (sub_eq_zero.mp hcoeff.symm)
      · -- tail violated: some higher coefficient survives
        have hp : defectPoly f cs ≠ 0 := ih ⟨c', htail, hviol⟩
        obtain ⟨k, hk⟩ : ∃ k, (defectPoly f cs).coeff k ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hp (Polynomial.ext fun n => by simp [hall n])
        intro h0
        have hcoeff : (defectPoly f (c :: cs)).coeff (k + 1)
            = (defectPoly f cs).coeff k := by
          simp [defectPoly, coeff_add, coeff_X_mul]
        rw [h0, coeff_zero] at hcoeff
        exact hk hcoeff.symm

omit [DecidableEq ι] in
/-- **Exact-word batching soundness (Schwartz–Zippel count).** If the word
violates SOME constraint of the list, then at most `t − 1` of the `|F|`
challenges γ make the γ-batched constraint pass: the satisfying challenges are
roots of the nonzero, degree-`< t` defect polynomial. Uniform-γ reading: the
probability an exactly-dishonest claim survives the batch is `≤ (t−1)/|F|` —
the exact-membership kernel of WHIR Constr. 5.5's `(t−1)·ℓ/|F|` (the δ-proximity
lift is prose residual `[CRS-batch-sound]`). -/
theorem card_batch_satisfying_le [Fintype F] {f : ι → F}
    {cs : List (LinearConstraint ι F)} (h : ∃ c ∈ cs, ¬ Satisfies f c) :
    (Finset.univ.filter fun γ : F =>
        Satisfies f (batchConstraint γ cs)).card ≤ cs.length - 1 := by
  classical
  have hne : defectPoly f cs ≠ 0 := defectPoly_ne_zero h
  have hdeg : (defectPoly f cs).natDegree < cs.length :=
    (Polynomial.natDegree_lt_iff_degree_lt hne).mpr (defectPoly_degree_lt f cs)
  have hsub : (Finset.univ.filter fun γ : F =>
      Satisfies f (batchConstraint γ cs)).val ⊆ (defectPoly f cs).roots := by
    intro γ hγ
    rw [Finset.mem_val, Finset.mem_filter] at hγ
    rw [Polynomial.mem_roots hne]
    exact satisfies_batch_iff_defect_root.mp hγ.2
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  omega

/-! ## Keystones over F₅ (ATLAS: satisfiable + teeth, BUILT)

The tiny code `RS[F₅, {0,1,2,3}, 2]` of `ReedSolomon.RSExample`, constrained by
evaluation claims. Everything below is `decide`-computed on the actual data —
witnesses, not vacuous implications. -/

namespace CRSExample

open RSExample

/-- The evaluation claim `f(1) = 1` (coordinate 1 of the domain `{0,1,2,3}`). -/
def evalC : LinearConstraint (Fin 4) (ZMod 5) := evalConstraint 1 1

/-- A second claim `f(2) = 2`, for exercising the batch. -/
def evalC₂ : LinearConstraint (Fin 4) (ZMod 5) := evalConstraint 2 2

/-- **SATISFIABLE**: the codeword `xWord = (0,1,2,3)` (evaluations of `X`,
membership from `ReedSolomon.lean`) lies in the constrained code cut by
`f(1) = 1` — the constraint check is computed by `decide`. -/
theorem xWord_mem_constrainedRS : xWord ∈ constrainedRS dom₅ 2 [evalC] := by
  refine ⟨xWord_mem, fun c hc => ?_⟩
  rw [List.mem_singleton] at hc
  subst hc
  decide

/-- The zero word is in the RS code but VIOLATES the constraint. -/
theorem zero_not_satisfies : ¬ Satisfies (0 : Fin 4 → ZMod 5) evalC := by decide

/-- **TEETH**: a word IN the RS code but NOT in the constrained code — the
constraint genuinely cuts. -/
theorem zero_mem_code_not_constrained :
    (0 : Fin 4 → ZMod 5) ∈ reedSolomonCode dom₅ 2 ∧
      (0 : Fin 4 → ZMod 5) ∉ constrainedRS dom₅ 2 [evalC] :=
  ⟨Submodule.zero_mem _,
    fun hmem => zero_not_satisfies (hmem.2 evalC (List.mem_singleton_self _))⟩

/-- The shrink is STRICT: the constrained code is a proper subset of the RS
code. -/
theorem constrainedRS_ssubset_example :
    constrainedRS dom₅ 2 [evalC] ⊂ (reedSolomonCode dom₅ 2 : Set (Fin 4 → ZMod 5)) := by
  rw [Set.ssubset_def]
  refine ⟨constrainedRS_subset_code _ _ _, fun hsub => ?_⟩
  exact zero_mem_code_not_constrained.2 (hsub zero_mem_code_not_constrained.1)

/-- The batch COMPLETENESS theorem exercised on real data: `xWord` satisfies
both claims, hence every γ-batch of them. -/
theorem xWord_satisfies_batch (γ : ZMod 5) :
    Satisfies xWord (batchConstraint γ [evalC, evalC₂]) := by
  refine satisfies_batch_of_forall γ fun c hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

/-- Concrete non-vacuity of the batch: at the specific challenge `γ = 3` the
batched constraint is verified by computation. -/
example : Satisfies xWord (batchConstraint 3 [evalC, evalC₂]) := by decide

/-- **Batch-soundness TEETH, tight**: the zero word violates `evalC`; exactly
ONE of the 5 challenges (γ = 2, where `1 + 2γ = 0`) lets the batch of
`[evalC, evalC₂]` pass — the `t − 1 = 1` bound of `card_batch_satisfying_le`
is ATTAINED, not slack. -/
theorem batch_teeth_card_eq :
    (Finset.univ.filter fun γ : ZMod 5 =>
        Satisfies (0 : Fin 4 → ZMod 5) (batchConstraint γ [evalC, evalC₂])).card
      = 1 := by decide

/-- The general soundness bound fired on the same data: `≤ t − 1 = 1`. -/
example :
    (Finset.univ.filter fun γ : ZMod 5 =>
        Satisfies (0 : Fin 4 → ZMod 5) (batchConstraint γ [evalC, evalC₂])).card
      ≤ 1 :=
  card_batch_satisfying_le ⟨evalC, List.mem_cons_self .., by decide⟩

end CRSExample

end Minidregg.Selvage
