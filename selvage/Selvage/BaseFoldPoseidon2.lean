/-
# Selvage.BaseFoldPoseidon2 — source-derived Poseidon2 Merkle semantics

The admitted Dregg2 artifact exports the deployed BabyBear width-16 Poseidon2
round constants and both linear maps.  `ZkmlPoseidon2Data` is mechanically
generated from that exact payload and checked by the repository trust gate.
This module gives those first-order tables their field semantics.

The IR-v2 artifact's Poseidon primitive is reused, but its MMCS leaf packing is
not silently reused.  BaseFold gets a new, explicit local profile:

* one `BabyBear[X]/(X^4-11)` symbol is represented by its four canonical
  power-basis coefficients;
* the fixed-width leaf absorbs those four lanes followed by four zero rate
  lanes into a zero-capacity state, then permutes once; and
* a node concatenates its ordered left/right eight-lane digests and permutes
  once, returning lanes zero through seven.

This closes the deterministic construction and field/basis boundary.  It does
not claim that the new BaseFold profile is the existing production IR-v2 suite,
that Poseidon2 is collision resistant/indifferentiable, or that a Rust codec
implements these functions.  Those remain named deployment obligations.
-/

import Selvage.BabyBearExt4
import Selvage.BaseFoldBinaryMerkle
import Selvage.ZkmlPoseidon2Data

namespace Minidregg.Selvage.BaseFoldPoseidon2

open scoped BigOperators
open BabyBearExt4 BinaryMerkle

set_option autoImplicit false

abbrev F := BabyBear
abbrev E := Ext4
abbrev State := Fin 16 → F
abbrev Digest := Fin 8 → F

/-- Distinct protocol identity for the local BaseFold packing.  The source
primitive suite remains recorded separately below. -/
def profileId : String :=
  "minidregg.basefold.babybear-ext4.poseidon2-w16.binary-merkle.v1"

def sourcePrimitiveSuiteId : String := ZkmlPoseidon2Data.sourceSuiteId
def sourcePrimitivePayloadSha256 : String :=
  ZkmlPoseidon2Data.sourcePayloadSha256

def leafPacking : String :=
  "one Ext4 power-basis symbol as four BabyBear lanes, then four zero rate lanes; zero capacity; exactly one permutation"

def nodePacking : String :=
  "ordered left eight-lane digest followed by right eight-lane digest; exactly one permutation"

def domainSeparationRule : String :=
  "no in-band tag; the fixed leaf arity and ordered internal-node type are external typed structure"

/-! ## Source-data-driven permutation -/

/-- Read one canonical natural from a source-derived table as BabyBear.  The
generated `sourceData_shapes` theorem proves all indices used below are in
range; `getD` keeps the evaluator total and executable. -/
def tableEntry (table : List (List Nat)) (column row : Nat) : F :=
  ((table.getD column []).getD row 0 : Nat)

def rowConstant (constants : List Nat) (lane : Fin 16) : F :=
  (constants.getD lane 0 : Nat)

/-- Apply a linear map represented by its sixteen source-derived columns. -/
def applyColumns (columns : List (List Nat)) (state : State) : State :=
  fun row => ∑ column : Fin 16,
    state column * tableEntry columns column row

def sbox (value : F) : F := value ^ 7

def externalRound (constants : List Nat) (state : State) : State :=
  applyColumns ZkmlPoseidon2Data.externalLinearColumns
    (fun lane => sbox (state lane + rowConstant constants lane))

def internalRound (constant : Nat) (state : State) : State :=
  applyColumns ZkmlPoseidon2Data.internalLinearColumns
    (fun lane =>
      if lane = (0 : Fin 16) then
        sbox (state lane + (constant : F))
      else
        state lane)

/-- The exact width-16 round schedule named by the admitted source artifact:
initial external linear layer, 4 external rounds, 13 internal rounds, and 4
final external rounds. -/
def permute (input : State) : State :=
  let initial :=
    applyColumns ZkmlPoseidon2Data.externalLinearColumns input
  let afterInitial :=
    ZkmlPoseidon2Data.externalInitialConstants.foldl
      (fun state constants => externalRound constants state) initial
  let afterInternal :=
    ZkmlPoseidon2Data.internalConstants.foldl
      (fun state constant => internalRound constant state) afterInitial
  ZkmlPoseidon2Data.externalFinalConstants.foldl
    (fun state constants => externalRound constants state) afterInternal

def truncateDigest (state : State) : Digest :=
  fun lane => state (Fin.castAdd 8 lane)

/-! ## Separately named BaseFold packing -/

/-- Canonical four-lane view of the proved quartic carrier. -/
noncomputable def coefficients4 (value : E) : Fin 4 → F :=
  fun lane => coefficients value
    (Fin.cast extensionPolynomial_natDegree.symm lane)

/-- One fixed-width BaseFold leaf: four canonical coefficients, four zero rate
lanes, then eight zero capacity lanes. -/
noncomputable def leafState (value : E) : State :=
  Fin.append
    (Fin.append (coefficients4 value) (fun _ : Fin 4 => 0))
    (fun _ : Fin 8 => 0)

noncomputable def hashLeaf (value : E) : Digest :=
  truncateDigest (permute (leafState value))

/-- The ordered binary-node compression from the admitted primitive. -/
def hashNode (left right : Digest) : Digest :=
  truncateDigest (permute (Fin.append left right))

/-- The concrete semantic hash suite consumed by `BinaryMerkle.openingScheme`. -/
noncomputable def hashSuite : HashSuite E Digest where
  leaf := hashLeaf
  node := hashNode

/-- The exact collision event that remains to be priced for this BaseFold
profile.  It is no longer an abstract commitment-failure proposition. -/
noncomputable def Collision : Prop := BinaryMerkle.Collision hashSuite

/-- The generic BaseFold reduction specialized to the real quartic carrier,
source-derived Poseidon2 primitive, and separately named leaf packing. -/
theorem friRawAdaptiveEquivocates_implies_poseidon2_collision
    {ell m qCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => openingScheme hashSuite (ell - n)))
    (r : Fin m → E)
    (Q : FriIndependentQuerySchedule (PowerTwoFriLevels ell) m qCount)
    (hequiv : FriRawAdaptiveEquivocates
      (fun n => openingScheme hashSuite (ell - n)) T st r qCount Q) :
    LocatedMerkleCollision hashSuite m :=
  friRawAdaptiveEquivocates_binaryMerkle_collision hashSuite T st r qCount Q
    hequiv

/-! ## Small executable teeth -/

theorem sbox_two : sbox 2 = 128 := by decide

theorem profile_is_not_ir2_suite : profileId ≠ sourcePrimitiveSuiteId := by
  decide

#check @friRawAdaptiveEquivocates_implies_poseidon2_collision

end Minidregg.Selvage.BaseFoldPoseidon2
