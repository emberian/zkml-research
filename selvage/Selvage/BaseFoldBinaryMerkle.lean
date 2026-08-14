/-
# Selvage.BaseFoldBinaryMerkle — discharge the raw FRI commitment event

`BaseFoldRawCommittedIor` retains a witness-bearing position equivocation at a
specific FRI level.  This module instantiates every power-of-two level with the
same semantic binary-Merkle hash suite and maps that event, without loss, to
the suite's concrete leaf-or-node collision proposition.

The hash suite is still a parameter.  Poseidon2 data, field/basis codecs,
domain separation, Fiat--Shamir framing, and collision pricing belong to the
next deployment-specific layer rather than being assumed here.
-/

import Selvage.BaseFoldRawCommittedIor
import Selvage.BinaryMerkle

namespace Minidregg.Selvage

open BinaryMerkle

set_option autoImplicit false

variable {F Digest : Type} [Field F]
variable {ell m : Nat}

/-- A collision together with the concrete bounded FRI level at which its two
preimages were exposed.  It remains a proposition because the source
equivocation event is proposition-valued. -/
def LocatedMerkleCollision (H : HashSuite F Digest) (m : Nat) : Prop :=
  ∃ level : Fin (m + 1), level.val ≤ m ∧ Collision H

/-- A raw adaptive BaseFold equivocation against the executable binary-Merkle
scheme exposes a concrete collision at one named FRI level. -/
theorem friRawAdaptiveEquivocates_binaryMerkle_collision
    (H : HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => openingScheme H (ell - n)))
    (r : Fin m → F) (qCount : Nat)
    (Q : FriIndependentQuerySchedule (PowerTwoFriLevels ell) m qCount)
    (hequiv : FriRawAdaptiveEquivocates
      (fun n => openingScheme H (ell - n)) T st r qCount Q) :
    LocatedMerkleCollision H m := by
  rcases hequiv with ⟨j, opening, a, _hopen, hquery⟩
  rcases hquery with hleft | hright | hnext
  · exact ⟨⟨j, lt_trans j.isLt (Nat.lt_succ_self m)⟩,
      Nat.le_of_lt j.isLt,
      positionEquivocation_implies_collision H (ell - j)
        (st.rootAt r j (Nat.le_of_lt j.isLt))
        ((T.data j j.isLt).sec (Q j a))
        (opening a).left (opening a).leftPath
        (st.wordAt r j (Nat.le_of_lt j.isLt)) hleft⟩
  · exact ⟨⟨j, lt_trans j.isLt (Nat.lt_succ_self m)⟩,
      Nat.le_of_lt j.isLt,
      positionEquivocation_implies_collision H (ell - j)
        (st.rootAt r j (Nat.le_of_lt j.isLt))
        ((T.data j j.isLt).neg ((T.data j j.isLt).sec (Q j a)))
        (opening a).right (opening a).rightPath
        (st.wordAt r j (Nat.le_of_lt j.isLt)) hright⟩
  · exact ⟨⟨j + 1, Nat.succ_lt_succ j.isLt⟩,
      Nat.succ_le_iff.mpr j.isLt,
      positionEquivocation_implies_collision H (ell - (j + 1))
        (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) (Q j a)
        (opening a).next (opening a).nextPath
        (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) hnext⟩

end Minidregg.Selvage
