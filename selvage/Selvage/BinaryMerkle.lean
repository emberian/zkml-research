/-
# Selvage.BinaryMerkle — executable binary-tree semantics and binding reduction

This is the construction-level handoff that `OpeningScheme` deliberately
leaves abstract.  A suite supplies only a leaf function and an ordered binary
node function.  The module then builds the perfect-tree root, the canonical
LSB-first authentication path, the exact path-length-checking verifier, and
the corresponding `OpeningScheme` over `Fin (2^k)`.

Functional correctness is unconditional.  Security is not: two accepted,
different values at one root and position are reduced losslessly to either a
leaf collision or an ordered-node collision.  A concrete hash suite must price
that event; this file never asserts collision resistance or a random-oracle
model.
-/

import Selvage.Commitment
import Selvage.BinaryLookup

namespace Minidregg.Selvage.BinaryMerkle

open Minidregg.Selvage

set_option autoImplicit false

/-- The semantic hash interface needed by a perfect binary Merkle tree. -/
structure HashSuite (Value Digest : Type*) where
  leaf : Value → Digest
  node : Digest → Digest → Digest

/-- Two distinct semantic leaf values have the same leaf digest. -/
def LeafCollision {Value Digest : Type*} (H : HashSuite Value Digest) : Prop :=
  ∃ left right, left ≠ right ∧ H.leaf left = H.leaf right

/-- Two distinct ordered child pairs have the same parent digest. -/
def NodeCollision {Value Digest : Type*} (H : HashSuite Value Digest) : Prop :=
  ∃ left₁ right₁ left₂ right₂,
    (left₁, right₁) ≠ (left₂, right₂) ∧
      H.node left₁ right₁ = H.node left₂ right₂

/-- The exact collision event exposed by the deterministic binding reduction. -/
def Collision {Value Digest : Type*} (H : HashSuite Value Digest) : Prop :=
  LeafCollision H ∨ NodeCollision H

section Tree

variable {Value Digest : Type*} (H : HashSuite Value Digest)

/-- Root of a perfect tree on the canonical LSB-first Boolean cube. -/
def cubeRoot : {k : Nat} → ((Fin k → Bool) → Value) → Digest
  | 0, word => H.leaf (word fun i => i.elim0)
  | _ + 1, word =>
      H.node
        (cubeRoot (fun tail => word (Fin.cases false tail)))
        (cubeRoot (fun tail => word (Fin.cases true tail)))

/-- Top-down sibling roots for one Boolean-cube coordinate. -/
def cubePath : {k : Nat} →
    ((Fin k → Bool) → Value) → (Fin k → Bool) → List Digest
  | 0, _, _ => []
  | k + 1, word, address =>
      let tail : Fin k → Bool := fun i => address i.succ
      match address 0 with
      | false =>
          cubeRoot H (fun rest => word (Fin.cases true rest)) ::
            cubePath (fun rest => word (Fin.cases false rest)) tail
      | true =>
          cubeRoot H (fun rest => word (Fin.cases false rest)) ::
            cubePath (fun rest => word (Fin.cases true rest)) tail

/-- Recompute a root from a leaf digest and a top-down sibling path.  Both
under- and over-long paths fail closed. -/
def recompute : {k : Nat} →
    Digest → (Fin k → Bool) → List Digest → Option Digest
  | 0, leaf, _, [] => some leaf
  | 0, _, _, _ :: _ => none
  | _ + 1, _, _, [] => none
  | k + 1, leaf, address, sibling :: rest =>
      let tail : Fin k → Bool := fun i => address i.succ
      match recompute leaf tail rest with
      | none => none
      | some child =>
          some (match address 0 with
            | false => H.node child sibling
            | true => H.node sibling child)

/-- Honest authentication paths reconstruct the exact tree root. -/
theorem recompute_cubePath : ∀ {k : Nat}
    (word : (Fin k → Bool) → Value) (address : Fin k → Bool),
    recompute H (H.leaf (word address)) address (cubePath H word address) =
      some (cubeRoot H word) := by
  intro k
  induction k with
  | zero =>
      intro word address
      have haddress : address = (fun i => i.elim0) := Subsingleton.elim _ _
      subst address
      simp [cubePath, recompute, cubeRoot]
  | succ k ih =>
      intro word address
      cases hbit : address 0 with
      | false =>
          have haddress :
              Fin.cases false (fun i => address i.succ) = address := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using hbit.symm
            · simp
          have hrecursive := ih
            (fun rest => word (Fin.cases false rest))
            (fun i => address i.succ)
          simp only [cubePath, hbit, recompute]
          rw [show word address =
              word (Fin.cases false (fun i => address i.succ)) by rw [haddress]]
          rw [hrecursive]
          rfl
      | true =>
          have haddress :
              Fin.cases true (fun i => address i.succ) = address := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using hbit.symm
            · simp
          have hrecursive := ih
            (fun rest => word (Fin.cases true rest))
            (fun i => address i.succ)
          simp only [cubePath, hbit, recompute]
          rw [show word address =
              word (Fin.cases true (fun i => address i.succ)) by rw [haddress]]
          rw [hrecursive]
          rfl

/-- The perfect-tree construction as Selvage's raw opening interface. -/
def openingScheme (k : Nat) :
    OpeningScheme Digest Value (Fin (2 ^ k)) (List Digest) where
  commit word :=
    cubeRoot H (fun address => word (binaryCubeIndexEquiv k address))
  openAt word index :=
    cubePath H (fun address => word (binaryCubeIndexEquiv k address))
      (binaryAddressBits k index)
  verifyOpen root index value proof :=
    recompute H (H.leaf value) (binaryAddressBits k index) proof = some root
  verifyOpen_commit := by
    intro word index
    rw [show word index =
        word (binaryCubeIndexEquiv k (binaryAddressBits k index)) by
          rw [binaryCubeIndexEquiv_decode]]
    exact recompute_cubePath H
      (fun address => word (binaryCubeIndexEquiv k address))
      (binaryAddressBits k index)

/-! ## Deterministic binding reduction -/

/-- Invert one successful nonempty recomputation step without losing its
child digest. -/
theorem recompute_cons_some_iff {k : Nat}
    (leaf sibling : Digest) (address : Fin (k + 1) → Bool)
    (rest : List Digest) (root : Digest) :
    recompute H leaf address (sibling :: rest) = some root ↔
      ∃ child,
        recompute H leaf (fun i => address i.succ) rest = some child ∧
        (match address 0 with
          | false => H.node child sibling
          | true => H.node sibling child) = root := by
  cases childResult : recompute H leaf (fun i => address i.succ) rest with
  | none => simp [recompute, childResult]
  | some child =>
      cases bit : address 0 <;> simp [recompute, childResult, bit]

/-- A successful path contains exactly one sibling per address bit. -/
theorem recompute_some_path_length : ∀ {k : Nat}
    (leaf : Digest) (address : Fin k → Bool) (proof : List Digest)
    (root : Digest),
    recompute H leaf address proof = some root → proof.length = k := by
  intro k
  induction k with
  | zero =>
      intro leaf address proof root accepted
      cases proof with
      | nil => rfl
      | cons sibling rest => simp [recompute] at accepted
  | succ k ih =>
      intro leaf address proof root accepted
      cases proof with
      | nil => simp [recompute] at accepted
      | cons sibling rest =>
          obtain ⟨child, childResult, _⟩ :=
            (recompute_cons_some_iff H leaf sibling address rest root).mp accepted
          have restLength : rest.length = k :=
            ih leaf (fun i => address i.succ) rest child childResult
          simp [restLength]

/-- If two paths at one address reach one root, either the leaf digests agree
or an ordered node collision occurs along the paths. -/
theorem recompute_equal_root_implies_leaf_eq_or_node_collision :
    ∀ {k : Nat} (leftLeaf rightLeaf : Digest) (address : Fin k → Bool)
      (leftProof rightProof : List Digest) (root : Digest),
      recompute H leftLeaf address leftProof = some root →
      recompute H rightLeaf address rightProof = some root →
      leftLeaf = rightLeaf ∨ NodeCollision H := by
  intro k
  induction k with
  | zero =>
      intro leftLeaf rightLeaf address leftProof rightProof root
        leftAccepted rightAccepted
      cases leftProof with
      | cons sibling rest => simp [recompute] at leftAccepted
      | nil =>
          cases rightProof with
          | cons sibling rest => simp [recompute] at rightAccepted
          | nil =>
              left
              simpa [recompute] using leftAccepted.trans rightAccepted.symm
  | succ k ih =>
      intro leftLeaf rightLeaf address leftProof rightProof root
        leftAccepted rightAccepted
      cases leftProof with
      | nil => simp [recompute] at leftAccepted
      | cons leftSibling leftRest =>
          cases rightProof with
          | nil => simp [recompute] at rightAccepted
          | cons rightSibling rightRest =>
              let tail : Fin k → Bool := fun i => address i.succ
              obtain ⟨leftChild, leftChildResult, leftRoot⟩ :=
                (recompute_cons_some_iff H leftLeaf leftSibling address
                  leftRest root).mp leftAccepted
              obtain ⟨rightChild, rightChildResult, rightRoot⟩ :=
                (recompute_cons_some_iff H rightLeaf rightSibling address
                  rightRest root).mp rightAccepted
              cases bit : address 0 with
              | false =>
                  simp only [bit] at leftRoot rightRoot
                  by_cases pairsEqual :
                      (leftChild, leftSibling) = (rightChild, rightSibling)
                  · have childrenEqual : leftChild = rightChild :=
                      congrArg Prod.fst pairsEqual
                    subst rightChild
                    exact ih leftLeaf rightLeaf tail leftRest rightRest leftChild
                      leftChildResult rightChildResult
                  · right
                    exact ⟨leftChild, leftSibling, rightChild, rightSibling,
                      pairsEqual, leftRoot.trans rightRoot.symm⟩
              | true =>
                  simp only [bit] at leftRoot rightRoot
                  by_cases pairsEqual :
                      (leftSibling, leftChild) = (rightSibling, rightChild)
                  · have childrenEqual : leftChild = rightChild :=
                      congrArg Prod.snd pairsEqual
                    subst rightChild
                    exact ih leftLeaf rightLeaf tail leftRest rightRest leftChild
                      leftChildResult rightChildResult
                  · right
                    exact ⟨leftSibling, leftChild, rightSibling, rightChild,
                      pairsEqual, leftRoot.trans rightRoot.symm⟩

/-- The standard deterministic Merkle reduction at the exact verifier. -/
theorem accepted_different_values_imply_collision
    (k : Nat) (root : Digest) (index : Fin (2 ^ k))
    (left right : Value) (leftProof rightProof : List Digest)
    (leftAccepted : (openingScheme H k).verifyOpen
      root index left leftProof)
    (rightAccepted : (openingScheme H k).verifyOpen
      root index right rightProof)
    (different : left ≠ right) : Collision H := by
  rcases recompute_equal_root_implies_leaf_eq_or_node_collision H
      (H.leaf left) (H.leaf right) (binaryAddressBits k index)
      leftProof rightProof root leftAccepted rightAccepted with
    leafHashesEqual | nodeCollision
  · exact Or.inl ⟨left, right, different, leafHashesEqual⟩
  · exact Or.inr nodeCollision

/-- A retained `OpeningScheme.PositionEquivocation` is already an exact
leaf-or-node collision witness for this construction. -/
theorem positionEquivocation_implies_collision
    (k : Nat) (root : Digest) (index : Fin (2 ^ k))
    (value : Value) (opening : List Digest) (word : Fin (2 ^ k) → Value)
    (hequiv : (openingScheme H k).PositionEquivocation
      root index value opening word) : Collision H := by
  rcases hequiv with ⟨hvalue, hword, hne⟩
  exact accepted_different_values_imply_collision H k root index
    value (word index) opening ((openingScheme H k).openAt word index)
    hvalue hword hne

/-- Collision-freedom is exactly the premise needed to recover the universal
logical position-binding interface. -/
theorem positionBinding_of_collisionFree (k : Nat)
    (hfree : ¬ Collision H) : (openingScheme H k).PositionBinding := by
  intro root index left right leftProof rightProof leftAccepted rightAccepted
  by_cases equal : left = right
  · exact equal
  · exact False.elim <| hfree <|
      accepted_different_values_imply_collision H k root index left right
        leftProof rightProof leftAccepted rightAccepted equal

end Tree

end Minidregg.Selvage.BinaryMerkle
