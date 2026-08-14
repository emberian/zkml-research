/-
# Selvage.BaseFoldPoseidon2Rom — connect the BaseFold leaf to the ROM floor

`BaseFoldPoseidon2` constructs the concrete source-derived permutation and the
new fixed-width BaseFold packing.  This module identifies that leaf with the
single-block fragment of Selvage's existing sponge construction and names the
correct work-indexed indifferentiability target.

The identification is deterministic and proved.  `romConstructionTarget` is
a real quantified game proposition already defined by `SpongeIndiffWorkBudget`;
it is named here, not assumed.  Even a proof of that ideal-permutation game
would still leave the deployed Poseidon2 permutation idealization and native
codec/refinement obligations explicit.
-/

import Selvage.BaseFoldPoseidon2
import Selvage.SpongeIndiffWorkBudget

namespace Minidregg.Selvage.BaseFoldPoseidon2Rom

open BabyBearExt4
open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldPoseidon2

set_option autoImplicit false

abbrev Rate := Digest
abbrev Cap := Digest

/-- Join the rate and capacity halves in the Poseidon lane order. -/
def joinState (state : Rate × Cap) : State :=
  Fin.append state.1 state.2

/-- Split a width-16 state back into its rate and capacity halves. -/
def splitState (state : State) : Rate × Cap :=
  (truncateDigest state, fun lane => state (Fin.natAdd 8 lane))

/-- The source-derived permutation viewed at the generic sponge interface. -/
def permutePair (state : Rate × Cap) : Rate × Cap :=
  splitState (permute (joinState state))

/-- The exact fixed BaseFold rate block: four power-basis coefficients followed
by four zero lanes. -/
noncomputable def leafBlock (value : E) : Rate :=
  Fin.append (coefficients4 value) (fun _ : Fin 4 => 0)

@[simp] theorem leafState_eq_join (value : E) :
    leafState value = joinState (leafBlock value, (0 : Cap)) := rfl

/-- The same leaf expressed through Selvage's generic sponge construction. -/
noncomputable def spongeLeaf (value : E) : Rate :=
  sponge permutePair (0, 0) [leafBlock value]

/-- The new BaseFold leaf is exactly the one-block, zero-IV sponge fragment.
For this fixed one-block message, additive absorption and overwrite absorption
coincide because the initial rate is zero. -/
theorem spongeLeaf_eq_hashLeaf (value : E) :
    spongeLeaf value = hashLeaf value := by
  simp [spongeLeaf, sponge, spongeAbsorb, absorbStep, permutePair, splitState,
    hashLeaf, leafState_eq_join]

/-- Collision of the concrete leaf is literally collision of that one-block
sponge construction, with the two quartic preimages retained. -/
noncomputable def SpongeLeafCollision : Prop :=
  ∃ left right : E,
    left ≠ right ∧ spongeLeaf left = spongeLeaf right

theorem leafCollision_iff_spongeLeafCollision :
    BinaryMerkle.LeafCollision hashSuite ↔ SpongeLeafCollision := by
  constructor
  · rintro ⟨left, right, different, hashes⟩
    refine ⟨left, right, different, ?_⟩
    rw [spongeLeaf_eq_hashLeaf, spongeLeaf_eq_hashLeaf]
    exact hashes
  · rintro ⟨left, right, different, hashes⟩
    refine ⟨left, right, different, ?_⟩
    rw [← spongeLeaf_eq_hashLeaf, ← spongeLeaf_eq_hashLeaf]
    exact hashes

/-- Exact size of the eight-BabyBear-lane capacity alphabet. -/
theorem capacity_card : Fintype.card Cap = modulus ^ 8 := by
  simp [Cap, Digest, F, BabyBear, modulus]

/-- Exact size of the complete width-16 primitive state. -/
theorem state_card : Fintype.card (Rate × Cap) = modulus ^ 16 := by
  rw [Fintype.card_prod, capacity_card, capacity_card, ← pow_add]
  norm_num

/-- The correct unrestricted ROM target is indexed by primitive work, not
external construction calls.  This proposition is deliberately not asserted
as a theorem here. -/
def romConstructionTarget : Prop :=
  SpongeIndiffWorkGame Rate Cap (0, 0)

/-- The exact error expression named by that generic target after exposing the
Poseidon profile's concrete capacity and full-state cardinalities. -/
noncomputable def romError (work : Nat) : Real :=
  2 * (work : Real) ^ 2 / (modulus ^ 8 : Nat)
    + (work : Real) ^ 2 / (modulus ^ 16 : Nat)

#check @spongeLeaf_eq_hashLeaf
#check @leafCollision_iff_spongeLeafCollision
#check @romConstructionTarget

end Minidregg.Selvage.BaseFoldPoseidon2Rom
