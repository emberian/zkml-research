/-
# Selvage.HashRelation — the relation view: the verifier checks R(x,y), it never runs H

`HashFamily` says what the proof system needs of a hash *as a function*.  This
module states the cheaper thing a circuit actually consumes: a RELATION.  The
in-circuit cost of a hash is never the cost of evaluating H — it is the cost of
checking a low-degree relation `R(x, y)` with `y` (and any intermediates)
supplied nondeterministically by the prover.  Anemoi's open/closed Flystel and
Griffin's `x^{1/α}` are hash designs built *from* this observation; our
degree-3 sumcheck rung (`Assurance/AirSumcheckCubic`, not importable here by
the boundary) makes "relation degree ≤ 3" a concrete design target.

Three layers, in decreasing generality and increasing teeth:

* `RelationView H` — bare relation + completeness.  Carrying one does NOT give
  soundness: `GraphSound` is the NAMED obligation, and `slack_not_graphSound`
  is the refutation of the free lunch.
* `PolyRelationView H` — the relation presented by an actual polynomial with a
  `totalDegree` bound, so "degree of the relation" is a theorem-bearing number,
  not prose.  `Degree3Statable` names the rung's cap.
* `WitnessedRelationView H` — the relation with auxiliary prover-supplied
  intermediates.  This is the shape the deployed AIR really has: BabyBear
  forces α = 7, and the REG=1 configuration commits the cube so every
  constraint is degree ≤ 3.  `pow7Witnessed` is that S-box shape over ANY
  commutative ring, with graph-soundness proved by `ring`, no `decide`, no
  field bound — it holds at the deployed BabyBear as an instantiation.

## ⚑ The asymmetry, machine-checked

The whole reason relation-designed hashes exist: the graph of a function can
have far lower degree than the function.  Exhibited here at the smallest
honest scale: over `ZMod 11` the cube-root function is `x ↦ x^7`
(functional degree 7), but its graph is `{(x,y) | y³ = x}` — a polynomial
relation of total degree 3.  `cubeRoot_asymmetry` holds both halves at once:
the relation IS degree-3 statable, and NO cubic polynomial computes the
function (checked exhaustively).  This is the Griffin/Rescue inverse-S-box
trick and the CCZ content of the Flystel, as one Lean theorem.

## ⚠ Honest labels

* `GraphSound` is an OBLIGATION.  Nothing about being a `RelationView`
  provides it (`slack_not_graphSound`), and for a real hash's full relation it
  is exactly the constraint-system soundness the AIR refinement discharges —
  not something this interface can conjure.
* ⚠ The relation-degree asymmetry is ADVERSARY-SYMMETRIC: the relation is
  public, so a low-degree `R` the verifier checks cheaply is the same
  low-degree system a Gröbner-basis attacker models cheaply.  The attack
  record (FreeLunch and its descendants; see
  `zkml-research/notes/aligned-hash-space.md`) broke exactly the designs that
  spent this asymmetry hardest.  This file prices the geometry; it does not
  bless it.
* `poseidon2NodeGraphView` fits the DEPLOYED hash to the interface via the
  trivial graph relation.  That carries no degree bound and evaluates nothing
  (one kernel-reduced permutation was measured at 47.6 GB / 68 min; nothing
  here reduces `permute`).  The witnessed degree-3 presentation of the full
  permutation — `pow7Witnessed` composed through the real round structure —
  is named as the next unit of work, not smuggled in as done.
-/
import Selvage.HashFamily
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Minidregg.Selvage

open MvPolynomial

set_option autoImplicit false

/-! ## §1 The relation view, and the named obligation -/

/-- **The relation a circuit checks in place of running `H`.**  `complete` is
the direction the honest prover needs; the converse is `GraphSound`, an
OBLIGATION carried by name, never by the structure. -/
structure RelationView {α β : Type*} (H : α → β) where
  /-- The checked relation. -/
  rel : α → β → Prop
  /-- Completeness: the honest evaluation is accepted. -/
  complete : ∀ x, rel x (H x)

namespace RelationView

variable {α β : Type*} {H : α → β}

/-- **`[HASH-relation-graph]` — the soundness obligation, NAMED.**  The
relation accepts nothing but the graph of `H`.  For the deployed hash this is
constraint-system soundness and lives with the AIR refinement; carrying a
`RelationView` does NOT discharge it (`slack_not_graphSound`). -/
def GraphSound (V : RelationView H) : Prop :=
  ∀ x y, V.rel x y → y = H x

/-- The trivial graph view.  Every function fits the interface this way — which
is exactly why the interface's content is in the DEGREE data of §3, not here. -/
def graph (H : α → β) : RelationView H where
  rel := fun x y => y = H x
  complete := fun _ => rfl

theorem graph_graphSound (H : α → β) : (graph H).GraphSound := fun _ _ h => h

end RelationView

/-! ## §2 TEETH — a relation that is the graph of NO function is refused -/

/-- `R` is the graph of `H`: complete and sound at once. -/
def IsGraphOf {α β : Type*} (R : α → β → Prop) (H : α → β) : Prop :=
  (∀ x, R x (H x)) ∧ ∀ x y, R x y → y = H x

/-- **The refusal, generically**: a relation relating one input to two distinct
outputs is the graph of no function whatsoever. -/
theorem not_graphOf_of_ambiguous {α β : Type*} (R : α → β → Prop)
    {x : α} {y₁ y₂ : β} (h₁ : R x y₁) (h₂ : R x y₂) (hne : y₁ ≠ y₂)
    (H : α → β) : ¬ IsGraphOf R H := by
  rintro ⟨_, hsound⟩
  exact hne ((hsound x y₁ h₁).trans (hsound x y₂ h₂).symm)

/-- A concrete ambiguous relation: `y² = x²` over `ZMod 11`. -/
def squareRel : ZMod 11 → ZMod 11 → Prop := fun x y => y ^ 2 = x ^ 2

/-- **The refusal, fired**: `squareRel` relates `1` to both `1` and `10`, so it
is the graph of no function `ZMod 11 → ZMod 11`. -/
theorem squareRel_refused (H : ZMod 11 → ZMod 11) : ¬ IsGraphOf squareRel H :=
  not_graphOf_of_ambiguous squareRel (x := 1) (y₁ := 1) (y₂ := 10)
    (show (1 : ZMod 11) ^ 2 = 1 ^ 2 by decide)
    (show (10 : ZMod 11) ^ 2 = 1 ^ 2 by decide) (by decide) H

/-! ## §3 The polynomial presentation — degree as a theorem-bearing number -/

/-- **A relation view presented by an actual polynomial** `P(X₀, X₁)` with the
convention `X₀` = input, `X₁` = output: the relation is `P(x, y) = 0`, and its
degree is `P.totalDegree` — a number theorems can consume, not prose. -/
structure PolyRelationView (F : Type*) [CommRing F] (H : F → F) where
  /-- The presenting polynomial: `X 0` is the input, `X 1` the output. -/
  P : MvPolynomial (Fin 2) F
  /-- Completeness through the polynomial. -/
  completeEq : ∀ x, eval ![x, H x] P = 0

namespace PolyRelationView

variable {F : Type*} [CommRing F] {H : F → F}

/-- The checked relation. -/
def rel (V : PolyRelationView F H) : F → F → Prop :=
  fun x y => eval ![x, y] V.P = 0

/-- Every polynomial presentation is a `RelationView`. -/
def toRelationView (V : PolyRelationView F H) : RelationView H where
  rel := V.rel
  complete := V.completeEq

/-- The degree bound, on the presenting polynomial itself. -/
def DegreeLE (V : PolyRelationView F H) (d : ℕ) : Prop :=
  V.P.totalDegree ≤ d

/-- **The design target our degree-3 sumcheck rung prices**: the relation is
statable at total degree ≤ 3, i.e. it fits one `cubicForm` slot without
further witnessed splitting.  (`Assurance/AirSumcheckCubic` is the consumer;
the import boundary keeps it out of `Selvage`, so the tie is by name.) -/
def Degree3Statable (V : PolyRelationView F H) : Prop := V.DegreeLE 3

/-- The soundness obligation, at the polynomial layer. -/
def GraphSound (V : PolyRelationView F H) : Prop :=
  ∀ x y, V.rel x y → y = H x

end PolyRelationView

/-! ## §4 ⚑ THE ASYMMETRY, EXHIBITED — degree-3 relation, degree-7 function

Over `ZMod 11`: `gcd(3, 10) = 1`, `3 · 7 ≡ 1 (mod 10)`, so cubing is a
bijection and the cube-root function is `x ↦ x^7`.  The RELATION `y³ = x` has
total degree 3; the FUNCTION has (minimal univariate) degree 7.  This is the
inverse-S-box / CCZ asymmetry that Rescue, Griffin and Anemoi are built from,
at the smallest scale where it is genuinely present. -/

/-- The cube-root function on `ZMod 11`. -/
def cubeRoot : ZMod 11 → ZMod 11 := fun x => x ^ 7

/-- The cube-root RELATION: `y³ − x = 0`, total degree 3. -/
noncomputable def cubeRootRel : PolyRelationView (ZMod 11) cubeRoot where
  P := X 1 ^ 3 - X 0
  completeEq := by
    intro x
    have h : ∀ x : ZMod 11, (x ^ 7) ^ 3 = x := by decide
    simp only [map_sub, map_pow, eval_X, Matrix.cons_val_one,
      Matrix.cons_val_zero, cubeRoot]
    exact sub_eq_zero.mpr (h x)

/-- The relation is inside the rung's cap. -/
theorem cubeRootRel_degree3 : cubeRootRel.Degree3Statable := by
  show (X 1 ^ 3 - X 0 : MvPolynomial (Fin 2) (ZMod 11)).totalDegree ≤ 3
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X_pow]
  · rw [totalDegree_X]; omega

/-- And it is graph-sound: cubing is injective on `ZMod 11`, so `y³ = x`
determines `y = x^7`. -/
theorem cubeRootRel_graphSound : cubeRootRel.GraphSound := by
  intro x y h
  have h' : y ^ 3 = x := by
    have := h
    simp only [cubeRootRel, PolyRelationView.rel, map_sub, map_pow, eval_X,
      Matrix.cons_val_one, Matrix.cons_val_zero] at this
    exact sub_eq_zero.mp this
  have key : ∀ a b : ZMod 11, b ^ 3 = a → b = a ^ 7 := by decide
  exact key x y h'

/-- ⚑ **No cubic computes the cube root**: there is no polynomial
`a·x³ + b·x² + c·x + d` agreeing with `cubeRoot` on all of `ZMod 11` — checked
exhaustively over all 11⁴ coefficient vectors. -/
theorem cubeRoot_not_cubic :
    ¬ ∃ a b c d : ZMod 11,
        ∀ x : ZMod 11, a * x ^ 3 + b * x ^ 2 + c * x + d = cubeRoot x := by
  decide

/-- **The asymmetry, in one statement.**  The same function admits a degree-3
graph relation while admitting NO degree-3 polynomial evaluation.  The circuit
consumes the left half; the right half is what it never has to pay for. -/
theorem cubeRoot_asymmetry :
    cubeRootRel.Degree3Statable ∧
      ¬ ∃ a b c d : ZMod 11,
          ∀ x : ZMod 11, a * x ^ 3 + b * x ^ 2 + c * x + d = cubeRoot x :=
  ⟨cubeRootRel_degree3, cubeRoot_not_cubic⟩

/-! ## §5 The witnessed relation — the shape the deployed AIR actually has -/

/-- **A relation with prover-supplied intermediates.**  `check` is what the
verifier evaluates (all polynomial constraints live there), `wit` is the honest
prover's witness map.  The projected relation `rel` existentially quantifies
the witness — which is exactly what "nondeterministic" means in-circuit. -/
structure WitnessedRelationView (α ω β : Type*) (H : α → β) where
  /-- The checked constraints, over (input, witness, output). -/
  check : α → ω → β → Prop
  /-- The honest witness. -/
  wit : α → ω
  /-- Completeness with the honest witness. -/
  complete : ∀ x, check x (wit x) (H x)

namespace WitnessedRelationView

variable {α ω β : Type*} {H : α → β}

/-- The projected relation: some witness makes the check pass. -/
def rel (V : WitnessedRelationView α ω β H) : α → β → Prop :=
  fun x y => ∃ w, V.check x w y

theorem rel_complete (V : WitnessedRelationView α ω β H) :
    ∀ x, V.rel x (H x) := fun x => ⟨V.wit x, V.complete x⟩

/-- Every witnessed view is a `RelationView` of the same function. -/
def toRelationView (V : WitnessedRelationView α ω β H) : RelationView H where
  rel := V.rel
  complete := V.rel_complete

/-- The soundness obligation: no witness certifies a wrong output. -/
def GraphSound (V : WitnessedRelationView α ω β H) : Prop :=
  ∀ x y, V.rel x y → y = H x

end WitnessedRelationView

/-- ⚑ **The deployed S-box shape, over ANY commutative ring.**  BabyBear forces
α = 7 (`gcd(α, p−1) = 1` kills 3 and 5), and the deployed REG=1 AIR commits an
intermediate so every constraint is degree ≤ 3.  This is that presentation of
`x ↦ x^7`: witness the cube, check two constraints of degree 3 each. -/
def pow7Witnessed (R : Type*) [CommRing R] :
    WitnessedRelationView R R R (fun x => x ^ 7) where
  check := fun x w y => w = x * x * x ∧ y = w * w * x
  wit := fun x => x * x * x
  complete := fun x => ⟨rfl, by ring⟩

/-- **Graph-soundness of the witnessed α=7 S-box, by `ring` alone** — no
`decide`, no finiteness, no field: the witness is determined by its own
constraint, so the projection is exactly the graph.  Holds at the deployed
BabyBear as an instantiation. -/
theorem pow7Witnessed_graphSound (R : Type*) [CommRing R] :
    (pow7Witnessed R).GraphSound := by
  rintro x y ⟨w, hw, hy⟩
  subst hw; subst hy; ring

/-- The deployed base field carries the witnessed S-box shape as-is. -/
noncomputable example :
    WitnessedRelationView BaseFoldPoseidon2.F BaseFoldPoseidon2.F
      BaseFoldPoseidon2.F (fun x => x ^ 7) :=
  pow7Witnessed BaseFoldPoseidon2.F

theorem pow7Witnessed_graphSound_deployed :
    (pow7Witnessed BaseFoldPoseidon2.F).GraphSound :=
  pow7Witnessed_graphSound _

/-! ## §6 TEETH — carrying the structure does not buy the obligation -/

/-- A witnessed view whose check is vacuous: it satisfies the INTERFACE
perfectly and accepts everything. -/
def slackWitnessed : WitnessedRelationView (ZMod 11) Unit (ZMod 11) cubeRoot where
  check := fun _ _ _ => True
  wit := fun _ => ()
  complete := fun _ => trivial

/-- **The obligation is refutable**: the slack view is a well-formed
`WitnessedRelationView` and is NOT graph-sound.  So `GraphSound` separates
inhabitants and cannot be acquired by construction. -/
theorem slack_not_graphSound : ¬ slackWitnessed.GraphSound := by
  intro h
  have h01 : (1 : ZMod 11) = cubeRoot 0 := h 0 1 ⟨(), trivial⟩
  simp only [cubeRoot] at h01
  exact absurd h01 (by decide)

/-! ## §7 The deployed hash fits the interface -/

/-- **The deployed Poseidon2 node map, as a `RelationView`.**  Via the trivial
graph relation: this shows the INTERFACE fits the shipped hash, and its honest
label is that it carries no degree bound and evaluates nothing — the
degree-bounded witnessed presentation of the full permutation (this file's
`pow7Witnessed` composed through the real round structure) is the named next
unit of work. -/
noncomputable def poseidon2NodeGraphView :
    RelationView (fun p : BaseFoldPoseidon2.Digest × BaseFoldPoseidon2.Digest =>
      HashFamily.poseidon2Family.suite.node p.1 p.2) :=
  RelationView.graph _

theorem poseidon2NodeGraphView_graphSound : poseidon2NodeGraphView.GraphSound :=
  RelationView.graph_graphSound _

/-! ## §8 Axiom audit -/

/-- info: 'Minidregg.Selvage.not_graphOf_of_ambiguous' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms not_graphOf_of_ambiguous
/-- info: 'Minidregg.Selvage.squareRel_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms squareRel_refused
/-- info: 'Minidregg.Selvage.cubeRootRel_degree3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubeRootRel_degree3
/-- info: 'Minidregg.Selvage.cubeRootRel_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubeRootRel_graphSound
/-- info: 'Minidregg.Selvage.cubeRoot_not_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubeRoot_not_cubic
/-- info: 'Minidregg.Selvage.cubeRoot_asymmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubeRoot_asymmetry
/-- info: 'Minidregg.Selvage.pow7Witnessed_graphSound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pow7Witnessed_graphSound
/-- info: 'Minidregg.Selvage.slack_not_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slack_not_graphSound
/-- info: 'Minidregg.Selvage.poseidon2NodeGraphView_graphSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms poseidon2NodeGraphView_graphSound

end Minidregg.Selvage
