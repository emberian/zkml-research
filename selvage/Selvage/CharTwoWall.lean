/-
# Selvage.CharTwoWall -- the multiplicative fold is REFUSED at characteristic two

`Selvage.Proximity`'s `FoldingData` carries `two_ne : (2 : F) ≠ 0` as a
STRUCTURE FIELD.  That is not an accident and not a strengthening that could be
relaxed: the multiplicative fold literally divides by two
(`foldEven = (f x + f (-x)) / 2`, `foldOdd = (f x - f (-x)) / (2 * x)`), and in
characteristic two `f x + f (-x) = 2 * f x = 0`, so the even/odd split at `±x`
collapses.  Squaring is the Frobenius there — a bijection — so the fibres
`{x, -x}` are singletons and there is nothing to halve.  **Multiplicative FRI
does not exist over a binary field.**  The field is a real constraint: KEEP IT.

What is dangerous is not the hypothesis, it is the SILENCE.  An uninhabitable
structure field makes `FoldingData F dom domSq` an EMPTY TYPE at characteristic
two, so every theorem quantified over it becomes VACUOUSLY TRUE there — on a
green build, passing its `#print axioms` pins, with no diagnostic anywhere.  A
complete "characteristic-two port" of the 185 declarations that take a
`FoldingData` or a `FoldingTower` could land, compile, and prove nothing.

This module makes the refusal LOUD in the three ways available:

1. `foldingData_charTwo_False` / `foldingTower_charTwo_False` — the emptiness,
   as named theorems, so a purported char-2 result over these carriers can be
   answered with one term instead of an argument.
2. `foldingData_vacuous_of_charTwo` — the CONSEQUENCE, named: at char 2 every
   predicate whatsoever holds of every `FoldingData`, including `False`.  This
   is the citation to reach for when reviewing such a port.
3. `foldingTower_charTwo_inhabited_at_height_zero` — the wall's exact
   location.  The claim is NOT "characteristic two is impossible": a height-`0`
   tower performs no folds and is perfectly inhabited at char 2.  The wall is
   at `0 < m`.  A blanket claim would be a floor that is provable rather than
   merely satisfiable, and the theorems above would be less useful for it.

⚑ AND THIS FILE IS ITSELF A TOOTH.  `foldingData_charTwo_False` is provable
*only because* `two_ne` is present, so anyone who "enables the binary port" by
deleting the field breaks this file in the same commit.  That the deletion
cannot then be papered over is CHECKED, not asserted: `strippedCharTwoWitness`
below is a machine-checked negative control building `FoldingData`-minus-
`two_ne` over `ZMod 2`, with `neg = sq = sec = id`.  Every other field is
satisfiable at characteristic two, so `two_ne` is the whole wall and there is
no second proof to fall back on.

**The honest characteristic-two path already exists and is proved.**  It is the
ADDITIVE tower, which folds along an additive coset `{x, x + β}` instead of
`{x, -x}` and never divides by two:

* `Selvage.AdditiveFriTower` — `additiveTowerFold`, `additiveTowerEmbedding`,
  `additiveTowerPivot_ne_zero`, `additiveTower_domain_eq_pairDomain`;
* `Selvage.AdditiveProximity` — `additiveProximityGap_UD` and
  `additiveFold_distance_UD`, the one-round soundness, proved unconditionally
  on the `δ < (1 - ρ)/3` band;
* `Selvage.AdditiveFriQuery` — `AdditiveFriTower` (the char-2-native structure,
  carrying `[CharP F 2]` rather than `two_ne`) and
  `additiveFriAdaptive_coherent_sampled_sound_UD`.

Binary work goes THERE.  Nothing in the binary story should ever acquire a
`FoldingData`.
-/
import Mathlib.Algebra.CharP.Two
import Selvage.Proximity

namespace Minidregg.Selvage

variable {F : Type*} [Field F] {ι κ : Type*}

/-! ## The wall -/

/-- **The multiplicative folding datum does not exist at characteristic two.**
Hand me one and I hand you `False`.  The witness is the structure's own
`two_ne` field against `CharTwo.two_eq_zero`. -/
theorem foldingData_charTwo_False [CharP F 2] {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) : False :=
  D.two_ne CharTwo.two_eq_zero

/-- The same fact as an emptiness statement, for `IsEmpty.elim`/`simp`. -/
theorem foldingData_isEmpty_charTwo [CharP F 2] (dom : ι ↪ F) (domSq : κ ↪ F) :
    IsEmpty (FoldingData F dom domSq) :=
  ⟨foldingData_charTwo_False⟩

/-- **The vacuity, named.**  At characteristic two EVERY predicate holds of
EVERY `FoldingData` — take `P := fun _ => False` to see how little that is.
Cite this when a "characteristic-two proximity result" is quantified over the
multiplicative carrier: the theorem is not weak evidence, it is no evidence. -/
theorem foldingData_vacuous_of_charTwo [CharP F 2] {dom : ι ↪ F} {domSq : κ ↪ F}
    (P : FoldingData F dom domSq → Prop) (D : FoldingData F dom domSq) : P D :=
  absurd trivial fun _ => foldingData_charTwo_False D

/-- **A tower that folds does not exist at characteristic two either.**  Any
positive height reaches level `0`'s folding datum, which is impossible. -/
theorem foldingTower_charTwo_False [CharP F 2] {ι : ℕ → Type*} {m : ℕ}
    (positive : 0 < m) (T : FoldingTower F ι m) : False :=
  foldingData_charTwo_False (T.data 0 positive)

/-- Every statement about a positive-height multiplicative tower is vacuous at
characteristic two. -/
theorem foldingTower_vacuous_of_charTwo [CharP F 2] {ι : ℕ → Type*} {m : ℕ}
    (positive : 0 < m) (P : FoldingTower F ι m → Prop) (T : FoldingTower F ι m) :
    P T :=
  absurd trivial fun _ => foldingTower_charTwo_False positive T

/-! ## Where the wall is NOT

The refusal above must be satisfiable and refutable, not blanket-provable.  It
is exactly a POSITIVE-height fact: a height-`0` tower has no folding data at
all (`∀ j, j < 0 → _` is vacuous), so it survives at characteristic two.  The
witness below is what stops `foldingTower_charTwo_False` from being stated
without its `0 < m` hypothesis, and it is the reason a reader can trust that
the hypothesis is load-bearing rather than decorative. -/

/-- The degenerate zero-fold tower over `ZMod 2`, which IS inhabited: the wall
is at `0 < m`, not at characteristic two as such. -/
def charTwoHeightZeroTower : FoldingTower (ZMod 2) (fun _ => Unit) 0 where
  dom _ := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  data j h := absurd h (Nat.not_lt_zero j)

theorem foldingTower_charTwo_inhabited_at_height_zero :
    Nonempty (FoldingTower (ZMod 2) (fun _ => Unit) 0) :=
  ⟨charTwoHeightZeroTower⟩

/-! ## ⚑ Negative control: `two_ne` is the whole wall

Nothing below is used by anything.  It exists so that the tooth in this file's
header is a MEASUREMENT rather than a claim.  `FoldingDataStripped` is
`FoldingData` with exactly one field deleted — `two_ne` — and it is INHABITED
at characteristic two.  Therefore:

* deleting `two_ne` does open the vacuity door for real, and
* `foldingData_charTwo_False` has no alternative proof from the surviving
  fields, so it cannot be quietly repaired after such a deletion.

⚠ This is a deliberate DUPLICATE of `Selvage.Proximity.FoldingData`, and the
only one allowed.  It is a refutability witness, not a second folding datum: it
has no lemmas, no `fold`, and nothing may build on it.  If `FoldingData` gains
or loses a field other than `two_ne`, update this copy in the same commit — a
control that has drifted from its subject measures nothing. -/

/-- `FoldingData` with `two_ne` DELETED and every other field verbatim. -/
structure FoldingDataStripped (F : Type*) [Field F] {ι κ : Type*}
    (dom : ι ↪ F) (domSq : κ ↪ F) where
  /-- Negation on the index set: `dom (neg i) = −dom i`. -/
  neg : ι → ι
  dom_neg : ∀ i, dom (neg i) = - dom i
  /-- The squaring projection: `domSq (sq i) = (dom i)²`. -/
  sq : ι → κ
  domSq_sq : ∀ i, domSq (sq i) = dom i ^ 2
  /-- A section of `sq`: each folded point names one of its two square roots. -/
  sec : κ → ι
  sq_sec : ∀ k, sq (sec k) = k
  dom_ne_zero : ∀ i, dom i ≠ 0

/-- The one-point domain `{1} ⊆ ZMod 2`. -/
def charTwoPoint : Unit ↪ ZMod 2 :=
  ⟨fun _ => 1, fun a b _ => Subsingleton.elim a b⟩

/-- **The control fires.**  Without `two_ne` the structure is inhabited at
characteristic two: `-1 = 1` makes `neg = id` lawful, and squaring is the
Frobenius, so `sq = sec = id` satisfies both remaining laws. -/
def strippedCharTwoWitness : FoldingDataStripped (ZMod 2) charTwoPoint charTwoPoint where
  neg := id
  dom_neg := by decide
  sq := id
  domSq_sq := by decide
  sec := id
  sq_sec := fun _ => Subsingleton.elim _ _
  dom_ne_zero := by decide

theorem foldingDataStripped_charTwo_inhabited :
    Nonempty (FoldingDataStripped (ZMod 2) charTwoPoint charTwoPoint) :=
  ⟨strippedCharTwoWitness⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.foldingData_charTwo_False' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingData_charTwo_False
/-- info: 'Minidregg.Selvage.foldingData_isEmpty_charTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingData_isEmpty_charTwo
/-- info: 'Minidregg.Selvage.foldingData_vacuous_of_charTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingData_vacuous_of_charTwo
/-- info: 'Minidregg.Selvage.foldingTower_charTwo_False' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingTower_charTwo_False
/-- info: 'Minidregg.Selvage.foldingTower_vacuous_of_charTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingTower_vacuous_of_charTwo
/-- info: 'Minidregg.Selvage.foldingTower_charTwo_inhabited_at_height_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingTower_charTwo_inhabited_at_height_zero
/-- info: 'Minidregg.Selvage.foldingDataStripped_charTwo_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldingDataStripped_charTwo_inhabited

end Minidregg.Selvage
