/-
# Selvage.HashRelationInverse — the inverse S-box and the root S-box, as relation views

`HashRelation` states the relation view and carries the deployed α = 7 shape
(`pow7Witnessed`).  This module adds the two relation shapes the post-Weft hash
charting needs (`zkml-research/notes/post-weft-hash.md`):

* **The inverse S-box** `x ↦ x⁻¹` (0 ↦ 0 — Lean's `GroupWithZero` inverse IS the
  S-box convention).  This is Vision's S-box (eprint 2019/426 §7.1, the family's
  only degree-2 verification) and the S-box half of the Weft successor: F₂-degree
  n−1 — the maximum any bijection attains, the most Frobenius-opaque nonlinearity
  there is — while its *relation* is the cheapest nonlinear check that exists.
  Two presentations, both graph-sound over any field:
  - `invWitnessed` — Vision-shaped, ONE witness element `r` (honest value: the
    indicator of `x ≠ 0`), all three constraints of total degree ≤ 2:
    `x·y = r`, `x·(1−r) = 0`, `y·(1−r) = 0`.
  - `invSystem` — witness-free, TWO constraints of total degree ≤ 3:
    `x²y = x`, `xy² = y` — presented as an actual polynomial SYSTEM
    (`PolySystemRelationView`, introduced here) so the degree is a
    theorem-bearing number per constraint, inside the degree-3 rung's cap.

* **The root S-box** `x ↦ x^{1/α}` at α = 7 (XHash8/XHash12's π₁, RPO's, and — at
  the deployed BabyBear — the inverse direction of our own S-box).  The verifier
  never computes a p-scale power: it checks the FORWARD relation `y⁷ = x`,
  witnessed at degree ≤ 3 (`w = y³`, `x = w²·y`) — `pow7Witnessed` transposed.
  `powRootWitnessed` is that shape over any commutative ring; graph-soundness
  needs exactly injectivity of `(·)⁷`, carried as a hypothesis (it holds in any
  field with `gcd(7, q−1) = 1`: BabyBear, Goldilocks, and the exemplar `ZMod 13`
  where it is discharged by `decide`).

* **XHash's π₂ is not a new relation object.**  The extension-field power map
  (x⁷ over F_{p³}) is `pow7Witnessed` instantiated at the extension — stated
  here at `GaloisField 13 3`, with graph-soundness inherited from the generic
  `ring` proof.  The whole XHash8 nonlinear layer is therefore three
  instantiations of two witnessed shapes, every constraint degree ≤ 3.

## ⚠ Honest labels

* Graph-soundness of an S-box relation is the PER-GATE leg only.  Composing it
  through rounds/MDS into a permutation-level witnessed view is the same named
  next unit as for Poseidon2 (`HashRelation` §7), not smuggled in here.
* The adversary symmetry warning of `HashRelation` applies with full force: the
  inverse S-box's cheap relation is precisely what FreeLunch-style modelling
  consumes.  The `x⁻¹`-in-every-branch shape is the one FreeLunch's authors
  could not directly model (2024/347 §4.3) — evidence, not immunity.

## TEETH

* `bareInv_not_complete` — the naive relation `x·y = 1` WITHOUT the zero branch
  is not even complete: the honest evaluation at 0 is refused.  The zero branch
  of `invWitnessed`/`invSystem` is load-bearing, not decorative.
* `emptySystem_not_graphSound` — a `PolySystemRelationView` with no constraints
  inhabits the new interface perfectly and is refused the obligation: carrying
  the structure still buys nothing.
-/
import Selvage.HashRelation
import Mathlib.FieldTheory.Finite.GaloisField

namespace Minidregg.Selvage

open MvPolynomial

set_option autoImplicit false

/-! ## §1 The polynomial SYSTEM view — several constraints, each with its own degree -/

/-- **A relation presented by a polynomial system** `{Pᵢ(X₀, X₁)}` (input `X 0`,
output `X 1`): the relation is "every `Pᵢ` vanishes".  `PolyRelationView` is the
one-constraint case; real S-box checks (the deployed REG=1 shape, Vision's
inverse, the root S-box) are systems, and the rung's cap is per-constraint. -/
structure PolySystemRelationView (F : Type*) [CommRing F] (H : F → F) where
  /-- The constraint polynomials. -/
  ps : List (MvPolynomial (Fin 2) F)
  /-- Completeness through every constraint. -/
  completeEq : ∀ x, ∀ P ∈ ps, eval ![x, H x] P = 0

namespace PolySystemRelationView

variable {F : Type*} [CommRing F] {H : F → F}

/-- The checked relation: all constraints vanish. -/
def rel (V : PolySystemRelationView F H) : F → F → Prop :=
  fun x y => ∀ P ∈ V.ps, eval ![x, y] P = 0

/-- Every system view is a `RelationView`. -/
def toRelationView (V : PolySystemRelationView F H) : RelationView H where
  rel := V.rel
  complete := V.completeEq

/-- Per-constraint degree bound. -/
def DegreeLE (V : PolySystemRelationView F H) (d : ℕ) : Prop :=
  ∀ P ∈ V.ps, P.totalDegree ≤ d

/-- The rung's cap, per constraint: each polynomial fits one `cubicForm` slot. -/
def Degree3Statable (V : PolySystemRelationView F H) : Prop := V.DegreeLE 3

/-- The soundness obligation at the system layer. -/
def GraphSound (V : PolySystemRelationView F H) : Prop :=
  ∀ x y, V.rel x y → y = H x

end PolySystemRelationView

/-! ## §2 The inverse S-box, Vision-shaped: one witness, degree ≤ 2 -/

/-- **Vision's inverse S-box check** (2019/426 §7.1): witness `r` (honestly the
indicator of `x ≠ 0`), constraints `x·y = r`, `x·(1−r) = 0`, `y·(1−r) = 0` — all
of total degree ≤ 2, the lowest verification degree in the AO family.  `H` is
the field inverse with `0⁻¹ = 0`, which is exactly the S-box's 0 ↦ 0. -/
noncomputable def invWitnessed (F : Type*) [Field F] :
    WitnessedRelationView F F F (fun x => x⁻¹) where
  check := fun x r y => x * y = r ∧ x * (1 - r) = 0 ∧ y * (1 - r) = 0
  wit := fun x => letI := Classical.dec (x = 0); if x = 0 then 0 else 1
  complete := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    · simp [hx]

/-- **Graph-soundness of the Vision shape, over any field.**  The witness bit is
determined: `x ≠ 0` forces `r = 1` (so `x·y = 1` pins `y = x⁻¹`), and `x = 0`
forces `r = 0` (so the third constraint pins `y = 0 = 0⁻¹`). -/
theorem invWitnessed_graphSound (F : Type*) [Field F] :
    (invWitnessed F).GraphSound := by
  rintro x y ⟨r, hxy, hx1r, hy1r⟩
  show y = x⁻¹
  by_cases hx : x = 0
  · subst hx
    have hr : r = 0 := by simpa using hxy.symm
    subst hr
    simpa using hy1r
  · have hr : r = 1 := by
      rcases mul_eq_zero.mp hx1r with h | h
      · exact absurd h hx
      · linear_combination -h
    subst hr
    exact ((inv_eq_of_mul_eq_one_right hxy).symm)

/-! ## §3 The inverse S-box, witness-free: two constraints, degree ≤ 3 -/

/-- The two cubics presenting `x ↦ x⁻¹` with no witness: `X₀²X₁ − X₀` and
`X₀X₁² − X₁`. -/
noncomputable def invSystem (F : Type*) [Field F] :
    PolySystemRelationView F (fun x => x⁻¹) where
  ps := [X 0 ^ 2 * X 1 - X 0, X 0 * X 1 ^ 2 - X 1]
  completeEq := fun x => by
    intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · by_cases hx : x = 0
      · subst hx; simp
      · simp only [map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.head_cons]
        rw [sub_eq_zero, sq, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    · by_cases hx : x = 0
      · subst hx; simp
      · simp only [map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.head_cons]
        rw [sub_eq_zero, sq, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]

/-- Each constraint of `invSystem` is inside the degree-3 rung's cap. -/
theorem invSystem_degree3 (F : Type*) [Field F] : (invSystem F).Degree3Statable := by
  intro P hP
  simp only [invSystem, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hP
  rcases hP with rfl | rfl
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X_pow, totalDegree_X]
    · rw [totalDegree_X]; omega
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X_pow, totalDegree_X]
    · rw [totalDegree_X]; omega

/-- **Graph-soundness of the witness-free shape, over any field**: `x = 0` makes
the second constraint read `y = 0 = 0⁻¹`; `x ≠ 0` makes the first read
`x·y = 1`. -/
theorem invSystem_graphSound (F : Type*) [Field F] : (invSystem F).GraphSound := by
  intro x y hrel
  show y = x⁻¹
  have h1 := hrel (X 0 ^ 2 * X 1 - X 0) (by simp [invSystem])
  have h2 := hrel (X 0 * X 1 ^ 2 - X 1) (by simp [invSystem])
  simp only [map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.head_cons, sub_eq_zero] at h1 h2
  by_cases hx : x = 0
  · subst hx
    rw [zero_mul] at h2
    exact h2.symm.trans inv_zero.symm
  · have hxy : x * y = 1 := by
      have hc : x * (x * y) = x * 1 := by rw [mul_one]; linear_combination h1
      exact mul_left_cancel₀ hx hc
    exact (inv_eq_of_mul_eq_one_right hxy).symm

/-- ⚑ **TOOTH: the zero branch is load-bearing.**  The naive relation `x·y = 1`
(with `y = x⁻¹` intended) is NOT complete over any field: at `x = 0` the honest
evaluation is refused.  This is why Vision carries the `r` bit and `invSystem`
carries the `−X₀`/`−X₁` terms; dropping them does not "simplify" the check, it
breaks it. -/
theorem bareInv_not_complete (F : Type*) [Field F] :
    ¬ ∀ x : F, x * x⁻¹ = 1 := fun h => by
  have h0 := h 0
  rw [zero_mul] at h0
  exact zero_ne_one h0

/-! ## §4 The root S-box — XHash's π₁, the transposed α = 7 shape -/

/-- **The root S-box, witnessed forward** — XHash8/XHash12's `π₁ : x ↦ x^{1/7}`
(and RPO's; and at BabyBear the inverse direction of the deployed S-box).  The
verifier checks the forward relation `y⁷ = x` at degree ≤ 3: witness the cube of
the OUTPUT (`w = y³`) and check `x = w²·y`.  `rt` is the root function with its
section law `rt x ^ 7 = x` carried as a hypothesis. -/
def powRootWitnessed (R : Type*) [CommRing R] (rt : R → R)
    (hsec : ∀ x, rt x ^ 7 = x) :
    WitnessedRelationView R R R rt where
  check := fun x w y => w = y * y * y ∧ x = w * w * y
  wit := fun x => rt x * rt x * rt x
  complete := fun x =>
    ⟨rfl, by
      conv_lhs => rw [← hsec x]
      ring⟩

/-- **Graph-soundness of the root shape**: needs exactly injectivity of `(·)⁷` —
which any field with `gcd(7, q−1) = 1` provides (BabyBear, Goldilocks, `ZMod
13`).  The witness is determined by its own constraint, so the projection is
the graph of `rt`. -/
theorem powRootWitnessed_graphSound (R : Type*) [CommRing R] (rt : R → R)
    (hsec : ∀ x, rt x ^ 7 = x)
    (hinj : Function.Injective (fun y : R => y ^ 7)) :
    (powRootWitnessed R rt hsec).GraphSound := by
  rintro x y ⟨w, hw, hx⟩
  subst hw
  have h7 : y ^ 7 = x := by rw [hx]; ring
  exact hinj (a₁ := y) (a₂ := rt x) (show y ^ 7 = rt x ^ 7 by rw [h7, hsec x])

/-- The smallest field carrying the α = 7 root shape honestly: over `ZMod 13`,
`7·7 ≡ 1 (mod 12)`, so the septic root is `x ↦ x⁷` itself. -/
def septicRoot13 : ZMod 13 → ZMod 13 := fun x => x ^ 7

theorem septicRoot13_section : ∀ x : ZMod 13, septicRoot13 x ^ 7 = x := by decide

theorem pow7_injective13 : Function.Injective (fun y : ZMod 13 => y ^ 7) := by decide

/-- XHash's π₁ shape, instantiated and graph-sound at the exemplar field. -/
theorem xhashRoot13_graphSound :
    (powRootWitnessed (ZMod 13) septicRoot13 septicRoot13_section).GraphSound :=
  powRootWitnessed_graphSound _ _ _ pow7_injective13

/-! ## §5 π₂ is the SAME relation object at the extension field -/

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **XHash's π₂ (x⁷ over the cubic extension) is `pow7Witnessed` at another
`CommRing`** — no new relation shape, no new soundness argument: the generic
`ring` proof covers the extension field unchanged.  Stated at the smallest
honest cubic extension, `GaloisField 13 3 = GF(13³)`. -/
noncomputable example :
    WitnessedRelationView (GaloisField 13 3) (GaloisField 13 3) (GaloisField 13 3)
      (fun x => x ^ 7) :=
  pow7Witnessed (GaloisField 13 3)

theorem pi2_shape_graphSound :
    (pow7Witnessed (GaloisField 13 3)).GraphSound :=
  pow7Witnessed_graphSound _

/-! ## §6 TEETH — the new interface refuses the free lunch too -/

/-- A system view with NO constraints: inhabits `PolySystemRelationView`
perfectly and accepts everything. -/
def emptySystemView (F : Type*) [CommRing F] (H : F → F) :
    PolySystemRelationView F H where
  ps := []
  completeEq := fun _ _ hP => nomatch hP

/-- **The obligation still separates**: the empty system is a well-formed
`PolySystemRelationView` and is NOT graph-sound.  `GraphSound` cannot be
acquired by carrying the new structure either. -/
theorem emptySystem_not_graphSound :
    ¬ (emptySystemView (ZMod 11) cubeRoot).GraphSound := by
  intro h
  have h01 : (1 : ZMod 11) = cubeRoot 0 :=
    h 0 1 (fun _ hP => nomatch hP)
  simp only [cubeRoot] at h01
  exact absurd h01 (by decide)

/-! ## §7 Axiom audit -/

/-- info: 'Minidregg.Selvage.invWitnessed_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invWitnessed_graphSound
/-- info: 'Minidregg.Selvage.invSystem_degree3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invSystem_degree3
/-- info: 'Minidregg.Selvage.invSystem_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invSystem_graphSound
/-- info: 'Minidregg.Selvage.bareInv_not_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bareInv_not_complete
/-- info: 'Minidregg.Selvage.powRootWitnessed_graphSound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms powRootWitnessed_graphSound
/-- info: 'Minidregg.Selvage.xhashRoot13_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xhashRoot13_graphSound
/-- info: 'Minidregg.Selvage.pi2_shape_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pi2_shape_graphSound
/-- info: 'Minidregg.Selvage.emptySystem_not_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emptySystem_not_graphSound

end Minidregg.Selvage
