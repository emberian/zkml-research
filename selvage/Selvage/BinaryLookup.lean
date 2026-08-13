/-
# Selvage.BinaryLookup -- sound binary lookup/read semantics

A Shout/Lasso-style binary lookup needs more than Boolean weights summing to
one.  Its equality vector must be the actual chi vector of the address bits.
This file indexes the Boolean cube LSB-first by `Fin (2^k)`, proves that the
chi vector at a Boolean address is exactly the corresponding unit vector, and
identifies its table dot product with the table's multilinear extension.

The final F₂ example shows why “Boolean entries + sum = 1” is insufficient:
a vector of Hamming weight three satisfies both constraints in characteristic
two but is not one-hot.
-/
import Selvage.MultilinearExtension

namespace Minidregg.Selvage

variable {F : Type*} [Field F]

/-! ## LSB-first addresses -/

/-- LSB-first equivalence between Boolean address words and table indices. -/
def binaryCubeIndexEquiv (k : ℕ) :
    (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Boolean address bits decoded from a table index. -/
def binaryAddressBits (k : ℕ) (i : Fin (2 ^ k)) : Fin k → Bool :=
  (binaryCubeIndexEquiv k).symm i

/-- The same decoded address embedded into the field. -/
def binaryAddressPoint (k : ℕ) (i : Fin (2 ^ k)) : Fin k → F :=
  cubePt (binaryAddressBits k i)

@[simp] theorem binaryAddressBits_encode (k : ℕ) (b : Fin k → Bool) :
    binaryAddressBits k (binaryCubeIndexEquiv k b) = b := by
  simp [binaryAddressBits]

@[simp] theorem binaryCubeIndexEquiv_decode (k : ℕ) (i : Fin (2 ^ k)) :
    binaryCubeIndexEquiv k (binaryAddressBits k i) = i := by
  simp [binaryAddressBits]

/-! ## The exact equality/one-hot vector -/

/-- Equality-vector entry for table row `i` at an arbitrary field address
`address`. -/
def binaryLookupEq (k : ℕ) (address : Fin k → F)
    (i : Fin (2 ^ k)) : F :=
  chiEval (binaryAddressBits k i) address

/-- A literal unit vector, used to state the pinning theorem as equality of
whole vectors rather than merely Booleanity and a sum constraint. -/
def binaryUnitVector {n : ℕ} (target : Fin n) : Fin n → F :=
  fun i => if i = target then 1 else 0

/-- At a Boolean address, every equality-vector coordinate is the Kronecker
delta at the encoded table index. -/
theorem binaryLookupEq_cubePt_apply (k : ℕ) (b : Fin k → Bool)
    (i : Fin (2 ^ k)) :
    binaryLookupEq (F := F) k (cubePt b) i =
      if i = binaryCubeIndexEquiv k b then 1 else 0 := by
  rw [binaryLookupEq, chiEval_cubePt]
  by_cases hi : i = binaryCubeIndexEquiv k b
  · subst i
    simp
  · have hdecode : binaryAddressBits k i ≠ b := by
      intro h
      apply hi
      rw [← binaryCubeIndexEquiv_decode k i, h]
    simp [hi, hdecode]

/-- **Exact one-hot semantics.**  At every Boolean address, the ENTIRE chi
vector is the corresponding unit vector. -/
theorem binaryLookupEq_cubePt_eq_unitVector (k : ℕ) (b : Fin k → Bool) :
    binaryLookupEq (F := F) k (cubePt b) =
      binaryUnitVector (F := F) (binaryCubeIndexEquiv k b) := by
  funext i
  exact binaryLookupEq_cubePt_apply (F := F) k b i

theorem binaryLookupEq_cubePt_at_address (k : ℕ) (b : Fin k → Bool) :
    binaryLookupEq (F := F) k (cubePt b) (binaryCubeIndexEquiv k b) = 1 := by
  simp [binaryLookupEq_cubePt_apply (F := F)]

theorem binaryLookupEq_cubePt_off_address (k : ℕ) (b : Fin k → Bool)
    {i : Fin (2 ^ k)} (hi : i ≠ binaryCubeIndexEquiv k b) :
    binaryLookupEq (F := F) k (cubePt b) i = 0 := by
  rw [binaryLookupEq_cubePt_apply (F := F)]
  simp [hi]

/-! ## Table dot product = MLE = exact Boolean read -/

/-- Reindex a flat LSB-first table as a Boolean-cube table. -/
def binaryCubeTable (k : ℕ) (table : Fin (2 ^ k) → F) :
    (Fin k → Bool) → F :=
  fun b => table (binaryCubeIndexEquiv k b)

/-- Dot product of two flat table vectors. -/
def binaryTableDot {n : ℕ} (table weights : Fin n → F) : F :=
  ∑ i, table i * weights i

/-- **Lookup/MLE bridge.**  Reading a table against its equality vector is
exactly evaluation of the reindexed table's multilinear extension. -/
theorem binaryTableDot_lookupEq_eq_mle (k : ℕ)
    (table : Fin (2 ^ k) → F) (address : Fin k → F) :
    binaryTableDot table (binaryLookupEq k address) =
      mle (binaryCubeTable k table) address := by
  unfold binaryTableDot binaryLookupEq binaryCubeTable mle binaryAddressBits
  rw [← (binaryCubeIndexEquiv k).sum_comp]
  simp

/-- At a Boolean address, the lookup dot product is the exact indexed table
read. -/
theorem binaryTableDot_lookupEq_cubePt (k : ℕ)
    (table : Fin (2 ^ k) → F) (b : Fin k → Bool) :
    binaryTableDot table (binaryLookupEq k (cubePt b)) =
      table (binaryCubeIndexEquiv k b) := by
  rw [binaryTableDot_lookupEq_eq_mle, mle_agrees]
  rfl

/-- The index-decoded spelling of exact table read. -/
theorem binaryTableDot_lookupEq_binaryAddress (k : ℕ)
    (table : Fin (2 ^ k) → F) (i : Fin (2 ^ k)) :
    binaryTableDot table (binaryLookupEq k (binaryAddressPoint (F := F) k i)) =
      table i := by
  rw [binaryAddressPoint, binaryTableDot_lookupEq_cubePt,
    binaryCubeIndexEquiv_decode]

/-! ## Characteristic-two shortcut refuter -/

namespace BinaryLookupExample

/-- Three ones and one zero over F₂: Boolean, odd-parity sum one, but not
one-hot. -/
def weightThree : Fin 4 → ZMod 2 := ![1, 1, 1, 0]

theorem weightThree_boolean : ∀ i, weightThree i = 0 ∨ weightThree i = 1 := by
  decide

theorem weightThree_sum_eq_one : ∑ i, weightThree i = 1 := by
  decide

theorem weightThree_support_card :
    (Finset.univ.filter fun i => weightThree i ≠ 0).card = 3 := by
  decide

/-- **TEETH:** Boolean entries plus sum one do not imply one-hot in
characteristic two. -/
theorem boolean_sum_one_not_oneHot_charTwo :
    (∀ i, weightThree i = 0 ∨ weightThree i = 1) ∧
      (∑ i, weightThree i) = 1 ∧
      (∀ target : Fin 4,
        weightThree ≠ binaryUnitVector (F := ZMod 2) target) := by
  refine ⟨weightThree_boolean, weightThree_sum_eq_one, ?_⟩
  decide

end BinaryLookupExample

/-- info: 'Minidregg.Selvage.binaryLookupEq_cubePt_eq_unitVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binaryLookupEq_cubePt_eq_unitVector
/-- info: 'Minidregg.Selvage.binaryTableDot_lookupEq_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binaryTableDot_lookupEq_eq_mle
/-- info: 'Minidregg.Selvage.BinaryLookupExample.boolean_sum_one_not_oneHot_charTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BinaryLookupExample.boolean_sum_one_not_oneHot_charTwo

end Minidregg.Selvage
