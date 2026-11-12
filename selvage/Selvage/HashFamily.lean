/-
# Selvage.HashFamily — what the proof system needs of a hash, as ONE interface

The proof system consumes a hash in exactly two roles:

* **the Merkle role** — an ordered 2-to-1 compression, used for commitment
  binding.  Already abstract: `BinaryMerkle.HashSuite`.
* **the transcript role** — a variable-length absorb, used for Fiat–Shamir.
  Already abstract: `SpongeIndiff.sponge` takes the permutation as an ARGUMENT.

Both halves were already hash-agnostic.  What did not exist was the **join** —
a single object saying *these two roles are played by one primitive, and here
are the assumptions it is used under* — and a **second instance** of it.  With
one instance, "swapping the hash is an instantiation, not a rewrite" is an
untested claim about code nobody has ever swapped.

This module supplies the join (`HashFamily`), the two construction ROUTES that
real hashes arrive by (`ofSponge` for a permutation-based sponge, `ofChain` for
a compression function in a chaining mode), instances on **two different
characteristics**, and the theorem that the proof system's obligation factors
through the family and never through the route.

## ⚑ The field-freedom claim, made checkable

`sponge` needs `[AddCommGroup Rate]` and nothing else: `+` on the rate is field
addition over BabyBear and XOR over `ZMod 2`, and the mode cannot tell.  That is
asserted in `docs/BINARY-POSITION.md`; here it is exhibited.  `spongeFamilyCharTwo`
is a genuine char-2 inhabitant, and `charTwo_family_nonempty` is its witness.

Read that against `Selvage.CharTwoWall`, which is the OPPOSITE result one rung
down: `FoldingData` is EMPTY at characteristic two, so every theorem over it goes
vacuously true there.  The two files together locate the binary-field wall
exactly — **it is in the FOLD, not in the HASH.**  A hash swap and a field swap
are independent moves, and only one of them hits a wall.

## The honest labels

* `MerkleObligation` is the real premise of `positionBinding_of_collisionFree`,
  restated on a family.  It is an ASSUMPTION, and `merkleObligation_not_provable`
  proves it cannot be anything else: on a finite digest type a compressing node
  map always collides, by pigeonhole.  So the obligation is **satisfiable**
  (`natChainFamily`), **refutable** (`collapsingFamily`), and **not provable** —
  the three legs a floor has to stand on.
* `TranscriptObligation` is `[HASH-transcript-indiff]`: STATED, NOT PROVED here,
  for any instance.  The sponge route can hope to discharge it from
  `SpongeIndiff.SpongeIndifferentiable`; that statement is itself unproved
  upstream (`SpongeIndiffGame`'s docstring says so).  Nothing in this file
  narrows that gap, and nothing here should be read as if it did.
* `absorb` is a plain function, so this file prices message collisions
  (`AbsorbCollision`) and NOT the full indifferentiability the challenger needs.
  Collision-freedom is strictly weaker.  It is stated as its own obligation so
  the two are not confused.

## ⚠ What is NOT in this file, and where it actually lives

A **real BLAKE3 instance**.  A complete, KAT-checked BLAKE3 exists in Lean at
`breadstuffs/metatheory/Dregg2/Crypto/Blake3Compute.lean` (`compress`, `roundFn`,
`permute`, `parentOutput`, `hash`, with `Blake3Kat.lean` beside it), and
`HashSuite` carries **no typeclass constraints at all**, so its `Array UInt32`
digests fit the interface as-is with no new mathematics.  The obstruction is a
BUILD boundary, not a mathematical one: BLAKE3 is in the `Dregg2` tree of another
repository, and `scripts/check-import-boundary.sh` restricts `Selvage/` to
Mathlib, Theory and Selvage.  `ofChain` is exactly the shape BLAKE3 arrives by;
what is missing is the artifact reaching this side of the boundary.
-/
import Selvage.BinaryMerkle
import Selvage.SpongeIndiff
import Selvage.BaseFoldPoseidon2Rom

namespace Minidregg.Selvage

open Minidregg.Selvage.BinaryMerkle

set_option autoImplicit false

/-! ## §1 The interface -/

/-- **What the proof system needs of a hash.**  One primitive in two roles:
`suite` is the Merkle 2-to-1 compression, `absorb` is the variable-length
transcript map.  No field, no characteristic, no permutation, no typeclass —
the constraints live on the ROUTES in §3, never on the interface. -/
structure HashFamily (Block Value Digest : Type*) where
  /-- The Merkle role: leaf and ordered-node digests. -/
  suite : HashSuite Value Digest
  /-- The transcript role: absorb a message, squeeze a digest. -/
  absorb : List Block → Digest

namespace HashFamily

variable {Block Value Digest : Type*}

/-! ## §2 The obligations, named

House law: a fact worth asserting is worth naming.  These are `Prop`s, not
`#guard`s and not axioms; the ones that are unproved say which. -/

/-- **Obligation 1 — the Merkle role.**  Exactly the premise
`BinaryMerkle.positionBinding_of_collisionFree` consumes.  An ASSUMPTION; see
`merkleObligation_not_provable`. -/
def MerkleObligation (H : HashFamily Block Value Digest) : Prop :=
  ¬ Collision H.suite

/-- Two distinct messages absorbing to the same digest. -/
def AbsorbCollision (H : HashFamily Block Value Digest) : Prop :=
  ∃ m₁ m₂ : List Block, m₁ ≠ m₂ ∧ H.absorb m₁ = H.absorb m₂

/-- **Obligation 2 — the transcript role, collision half.**  Strictly weaker
than what Fiat–Shamir needs; stated separately so it is not mistaken for it. -/
def TranscriptCollisionObligation (H : HashFamily Block Value Digest) : Prop :=
  ¬ AbsorbCollision H

/-- **`[HASH-transcript-indiff]` — Obligation 3, STATED, NOT PROVED for any
instance in this file.**  What Fiat–Shamir actually needs: `absorb` is
indifferentiable from a random oracle, i.e. every `q`-query distinguisher's
advantage is at most `ε q`.  Phrased here as an abstract predicate over the
error function because the family interface is mode-free; the sponge route's
concrete form of this is `SpongeIndiff.SpongeIndifferentiable`, which is itself
open upstream.  ⚠ Carrying this field does NOT discharge it. -/
def TranscriptObligation (_H : HashFamily Block Value Digest)
    (Advantage : ℕ → ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ q : ℕ, Advantage q ≤ ε q

/-! ## §3 ⚑ THE POINT — the obligation factors through the family, not the route

`positionBinding_of_family` mentions no field, no characteristic, no
permutation and no mode.  Every instance in §5 discharges the proof system's
binding requirement by *this same term*.  That is the precise content of
"swapping the hash is an instantiation, not a rewrite". -/

/-- **Merkle binding, from the family alone.**  The proof system's position-binding
requirement follows from `MerkleObligation` and nothing else — in particular not
from how the family was built. -/
theorem positionBinding_of_family (H : HashFamily Block Value Digest) (k : ℕ)
    (h : MerkleObligation H) :
    (openingScheme H.suite k).PositionBinding :=
  positionBinding_of_collisionFree H.suite k h

/-- The contrapositive the extractor uses: two accepted different values at one
position are a collision in the family's suite. -/
theorem collision_of_accepted_ne (H : HashFamily Block Value Digest)
    (k : ℕ) (root : Digest) (index : Fin (2 ^ k)) (left right : Value)
    (leftProof rightProof : List Digest)
    (hl : (openingScheme H.suite k).verifyOpen root index left leftProof)
    (hr : (openingScheme H.suite k).verifyOpen root index right rightProof)
    (hne : left ≠ right) : Collision H.suite :=
  accepted_different_values_imply_collision H.suite k root index left right
    leftProof rightProof hl hr hne

end HashFamily

/-! ## §4 The two routes real hashes arrive by -/

namespace HashFamily

/-- **Route A — SPONGE.**  A permutation on `Rate × Cap` plus an IV and a packing
of values into rate blocks.  ⚑ The ONLY structure required is
`[AddCommGroup Rate]`: field addition over BabyBear, XOR over `ZMod 2`.  This is
the route Poseidon2 and Keccak both arrive by. -/
def ofSponge {Rate Cap : Type} {Value : Type*} [AddCommGroup Rate]
    (P : Rate × Cap → Rate × Cap) (iv : Rate × Cap) (pack : Value → List Rate) :
    HashFamily Rate Value Rate where
  suite :=
    { leaf := fun v => sponge P iv (pack v)
      node := fun a b => sponge P iv [a, b] }
  absorb := sponge P iv

/-- **Route B — CHAINING COMPRESSION.**  A compression `f : Digest → Block → Digest`
in Merkle–Damgård form, with its own parent-node map.  This is the shape BLAKE3
and SHA-256 arrive by, and it requires NO algebraic structure whatsoever — not
even `AddCommGroup`.  See the header for where the real BLAKE3 artifact lives. -/
def ofChain {Block Value Digest : Type*}
    (f : Digest → Block → Digest) (iv : Digest) (node : Digest → Digest → Digest)
    (pack : Value → List Block) : HashFamily Block Value Digest where
  suite := { leaf := fun v => (pack v).foldl f iv, node := node }
  absorb := fun m => m.foldl f iv

@[simp] theorem ofSponge_absorb {Rate Cap : Type} {Value : Type*} [AddCommGroup Rate]
    (P : Rate × Cap → Rate × Cap) (iv : Rate × Cap) (pack : Value → List Rate)
    (m : List Rate) : (ofSponge P iv pack (Value := Value)).absorb m = sponge P iv m := rfl

@[simp] theorem ofChain_absorb {Block Value Digest : Type*}
    (f : Digest → Block → Digest) (iv : Digest) (node : Digest → Digest → Digest)
    (pack : Value → List Block) (m : List Block) :
    (ofChain f iv node pack).absorb m = m.foldl f iv := rfl

/-- ⚑ The routes are not the same construction: `ofChain`'s node map is a free
parameter, while `ofSponge`'s is forced to be a two-block absorb.  Recorded so
that a later "unify the routes" refactor has to confront it. -/
theorem ofSponge_node {Rate Cap : Type} {Value : Type*} [AddCommGroup Rate]
    (P : Rate × Cap → Rate × Cap) (iv : Rate × Cap) (pack : Value → List Rate)
    (a b : Rate) : (ofSponge P iv pack (Value := Value)).suite.node a b = sponge P iv [a, b] :=
  rfl

end HashFamily

/-! ## §5 Instances — on two different characteristics

⚑ The whole claim of this file is that these two live under the same theorem
(`positionBinding_of_family`) while sharing no field, no characteristic and no
route.  §6 checks that they are genuinely distinct objects. -/

namespace HashFamily

/-! ### 5a. ⚑ The DEPLOYED Poseidon2 — a real instance, not an illustration

`BaseFoldPoseidon2.hashSuite` is the suite `BinaryMerkle.openingScheme` already
consumes, at the deployed width-16 BabyBear round schedule (α = 7, 4 external /
13 internal / 4 external).  `BaseFoldPoseidon2Rom.permutePair` is that same
permutation viewed as a `Rate × Cap` map.  Joining them is the whole construction
— no new Poseidon2 anything.

⚠ **Nothing here reduces `permute`.**  One Poseidon2 permutation under kernel
reduction was measured at 47.6 GB / 68 min (`whnf` zeta-expands the `let`
helpers over field arithmetic), so this family is `noncomputable` and no theorem
below evaluates it.  An interface that needed `decide` through the permutation
would be unusable at the deployed hash, by measurement. -/

/-- **The deployed Poseidon2, as a `HashFamily`.**  Merkle role from the existing
`hashSuite`; transcript role from the existing generic `sponge` at the existing
`permutePair`.  This is the instance that makes §3's theorem a statement about
shipped code rather than about a demonstrator. -/
noncomputable def poseidon2Family :
    HashFamily BaseFoldPoseidon2Rom.Rate BaseFoldPoseidon2.E BaseFoldPoseidon2.Digest where
  suite := BaseFoldPoseidon2.hashSuite
  absorb := sponge BaseFoldPoseidon2Rom.permutePair (0, 0)

/-- The family's Merkle role IS the deployed suite, definitionally.  Recorded so a
later edit cannot silently swap in a lookalike. -/
theorem poseidon2Family_suite : poseidon2Family.suite = BaseFoldPoseidon2.hashSuite := rfl

/-- The family's collision event IS `BaseFoldPoseidon2.Collision`, definitionally —
so the pricing already written against that name applies unchanged. -/
theorem poseidon2Family_collision :
    Collision poseidon2Family.suite = BaseFoldPoseidon2.Collision := rfl

/-- ⚑ **The deployed hash's binding, discharged by §3's route-blind term.**  No
Poseidon2 fact is used: only `MerkleObligation`.  This is the swap claim, applied
to the hash we actually ship. -/
theorem poseidon2_positionBinding (k : ℕ) (h : MerkleObligation poseidon2Family) :
    (openingScheme poseidon2Family.suite k).PositionBinding :=
  positionBinding_of_family poseidon2Family k h

/-! ### 5b. Characteristic two — `+` is XOR, and the mode does not notice -/

/-- Rate for the char-2 instance: four bits. -/
abbrev CharTwoRate : Type := Fin 4 → ZMod 2

/-- Capacity for the char-2 instance: four bits. -/
abbrev CharTwoCap : Type := Fin 4 → ZMod 2

/-- A concrete invertible char-2 permutation: rotate the rate by one lane, swap
rate and capacity, and add the (rotated) rate into the capacity.  Chosen only to
be computable, non-identity and bijective — this is a MODE demonstrator, not a
cryptographic proposal, and it is deliberately NOT called a hash anywhere. -/
def charTwoPerm : CharTwoRate × CharTwoCap → CharTwoRate × CharTwoCap :=
  fun s => (fun i => s.2 i, fun i => s.1 (i + 1) + s.2 i)

/-- **A `HashFamily` at characteristic two.**  Built by `ofSponge`, whose only
requirement is `[AddCommGroup Rate]` — and at `ZMod 2` that addition IS XOR. -/
def spongeFamilyCharTwo : HashFamily CharTwoRate CharTwoRate CharTwoRate :=
  ofSponge charTwoPerm (0, 0) (fun v => [v])

/-- ⚑ **The char-2 family is INHABITED.**  Stated as a named theorem because the
sibling structure one rung down is not: `Selvage.CharTwoWall.foldingData_charTwo_False`
proves `FoldingData` is EMPTY at characteristic two.  The wall is in the FOLD,
not in the HASH. -/
theorem charTwo_family_nonempty :
    Nonempty (HashFamily CharTwoRate CharTwoRate CharTwoRate) :=
  ⟨spongeFamilyCharTwo⟩

/-- The char-2 instance computes, and its node map is not the identity on either
argument.  A guard against the identity-carrier failure mode: an interface
discharged over a carrier that throws its input away. -/
theorem charTwoPerm_ne_id : charTwoPerm ≠ id := by decide

/-! ### 5c. A chaining instance — no algebraic structure at all

`ofChain` over `ℕ` with Mathlib's pairing function.  This is the route BLAKE3
arrives by, exercised on a digest type that is not a field, not finite, and
carries no `AddCommGroup`. -/

/-- Chaining compression: pair the chaining value with the block. -/
def natChain : ℕ → ℕ → ℕ := fun cv block => Nat.pair cv block

/-- **A `HashFamily` with no algebraic structure whatsoever**, via `ofChain`. -/
def natChainFamily : HashFamily ℕ ℕ ℕ :=
  ofChain natChain 0 Nat.pair (fun v => [v])

/-! ### 5d. ⚑ The negative control — an inhabitant that FAILS the obligation -/

/-- A family whose node map collapses everything to one digest.  It is a perfectly
good `HashFamily`; it is not a good hash, and §6 proves the obligation sees the
difference. -/
def collapsingFamily : HashFamily ℕ ℕ ℕ where
  suite := { leaf := fun _ => 0, node := fun _ _ => 0 }
  absorb := fun _ => 0

end HashFamily

/-! ## §6 TEETH — satisfiable, refutable, and NOT provable

`feedback-prove-the-floor-false`: a floor must be satisfiable AND refutable but
NOT provable.  All three legs are machine-checked here. -/

namespace HashFamily

/-- **Leg 1 — REFUTABLE.**  `collapsingFamily` inhabits the interface and fails
the obligation.  So `MerkleObligation` is not vacuously true, and an instance
cannot acquire binding just by existing. -/
theorem collapsing_not_merkleObligation : ¬ MerkleObligation collapsingFamily := by
  intro h
  exact h (Or.inr ⟨0, 0, 0, 1, by decide, rfl⟩)

/-- The collapsing family also fails the transcript half. -/
theorem collapsing_not_transcriptObligation :
    ¬ TranscriptCollisionObligation collapsingFamily := by
  intro h
  exact h ⟨[], [0], by simp, rfl⟩

/-- **Leg 2 — SATISFIABLE.**  `natChainFamily` genuinely has no collision:
`Nat.pair` is injective in both arguments, so neither a leaf nor a node collision
exists.  A real, non-degenerate witness — the digest type is infinite, which §6's
third leg shows is *necessary*. -/
theorem natChain_merkleObligation : MerkleObligation natChainFamily := by
  rintro (⟨a, b, hne, hEq⟩ | ⟨a₁, b₁, a₂, b₂, hne, hEq⟩)
  · -- leaf: `fun v => [v].foldl natChain 0 = Nat.pair 0 v`
    exact hne (by simpa [natChainFamily, ofChain, natChain, Nat.pair_eq_pair] using hEq)
  · exact hne (by
      have := Nat.pair_eq_pair.mp hEq
      simp only [Prod.mk.injEq]
      exact ⟨this.1, this.2⟩)

/-- Both legs at once: the obligation separates two inhabitants of the same
interface.  This is the statement that the obligation is doing work. -/
theorem merkleObligation_separates :
    MerkleObligation natChainFamily ∧ ¬ MerkleObligation collapsingFamily :=
  ⟨natChain_merkleObligation, collapsing_not_merkleObligation⟩

/-- **Leg 3 — NOT PROVABLE.**  ⚑ On a FINITE digest type with more than one
element, an ordered node map always collides, by pigeonhole: `Digest × Digest` is
strictly larger than `Digest`, so `node` is not injective on pairs.

This is why `MerkleObligation` is a cryptographic ASSUMPTION and can never be
upgraded to a theorem for any real hash — every deployed digest type is finite.
It also says exactly what `natChainFamily` is buying with its infinite digest:
not security, only satisfiability of the statement. -/
theorem nodeCollision_of_finite_digest {Value Digest : Type*} [Fintype Digest]
    [DecidableEq Digest] (H : HashSuite Value Digest) (h : 1 < Fintype.card Digest) :
    NodeCollision H := by
  have hcard : Fintype.card Digest < Fintype.card (Digest × Digest) := by
    have hpos : 0 < Fintype.card Digest := Nat.lt_of_lt_of_le Nat.zero_lt_one h.le
    rw [Fintype.card_prod]
    nlinarith
  obtain ⟨p, q, hpq, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun p : Digest × Digest => H.node p.1 p.2) hcard
  exact ⟨p.1, p.2, q.1, q.2, hpq, hEq⟩

/-- The obligation is therefore FALSE for every family on a finite digest type
with more than one element — i.e. for every deployable one. -/
theorem merkleObligation_not_provable {Block Value Digest : Type*} [Fintype Digest]
    [DecidableEq Digest] (H : HashFamily Block Value Digest)
    (h : 1 < Fintype.card Digest) : ¬ MerkleObligation H :=
  fun hobl => hobl (Or.inr (nodeCollision_of_finite_digest H.suite h))

/-- ⚑ And it fires on our own char-2 instance, which is finite: the sponge family
of §5a provably has a node collision.  So the demonstrator is honest about being
a demonstrator — no instance in this file is claimed to be collision-resistant. -/
theorem charTwo_not_merkleObligation : ¬ MerkleObligation spongeFamilyCharTwo :=
  merkleObligation_not_provable spongeFamilyCharTwo (by decide)

end HashFamily

/-! ## §7 The instances are genuinely different objects

A guard against the failure mode where "two instances" are one instance twice. -/

namespace HashFamily

/-- The two routes produce different node maps on the same inputs. -/
theorem natChain_ne_collapsing : natChainFamily ≠ collapsingFamily := by
  intro h
  have : natChainFamily.suite.node 1 1 = collapsingFamily.suite.node 1 1 := by rw [h]
  simp [natChainFamily, ofChain, collapsingFamily, Nat.pair] at this

/-- The char-2 sponge instance and the chaining instance do not even share a
digest type — recorded as the type-level statement that the interface spans
characteristics and modes at once. -/
example : HashFamily CharTwoRate CharTwoRate CharTwoRate := spongeFamilyCharTwo
example : HashFamily ℕ ℕ ℕ := natChainFamily

end HashFamily

/-! ## §8 Axiom audit -/

/-- info: 'Minidregg.Selvage.HashFamily.positionBinding_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.positionBinding_of_family
/-- info: 'Minidregg.Selvage.HashFamily.collision_of_accepted_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.collision_of_accepted_ne
/-- info: 'Minidregg.Selvage.HashFamily.charTwo_family_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.charTwo_family_nonempty
/-- info: 'Minidregg.Selvage.HashFamily.natChain_merkleObligation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.natChain_merkleObligation
/-- info: 'Minidregg.Selvage.HashFamily.collapsing_not_merkleObligation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.collapsing_not_merkleObligation
/-- info: 'Minidregg.Selvage.HashFamily.poseidon2Family_suite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.poseidon2Family_suite
/-- info: 'Minidregg.Selvage.HashFamily.poseidon2Family_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.poseidon2Family_collision
/-- info: 'Minidregg.Selvage.HashFamily.poseidon2_positionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.poseidon2_positionBinding
/-- info: 'Minidregg.Selvage.HashFamily.charTwo_not_merkleObligation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.charTwo_not_merkleObligation
/-- info: 'Minidregg.Selvage.HashFamily.merkleObligation_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.merkleObligation_separates
/-- info: 'Minidregg.Selvage.HashFamily.nodeCollision_of_finite_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.nodeCollision_of_finite_digest
/-- info: 'Minidregg.Selvage.HashFamily.merkleObligation_not_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HashFamily.merkleObligation_not_provable

end Minidregg.Selvage
