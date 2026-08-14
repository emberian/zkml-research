/-
# Selvage.BaseFoldBcsQuerySampling — unbiased BabyBear query coordinates

The first BaseFold BCS construction used `seed.val % 2^k`. BabyBear has
order `15 * 2^27 + 1`, so that total decoder is very slightly biased: residue
zero has one extra preimage. This module supplies the strict replacement.

Reject field zero, subtract one, and split the remaining `15 * 2^27` values
into a slack coordinate and the required power-of-two FRI coordinate. The
split is an explicit equivalence, so the accepted coordinate is exactly
uniform rather than merely close to uniform. Rejection remains a named event;
no retry, beacon, or random-oracle claim is smuggled in here.

`UnbiasedAccepts` is the fail-closed construction verifier using this decoder.
It reflects into the same raw committed-IOR predicate as the original BCS
verifier, now on the exact unbiased schedule.
-/

import Selvage.BaseFoldBcsFiatShamir

namespace Minidregg.Selvage.BaseFoldBcsQuerySampling

open Minidregg.Selvage
open BabyBearExt4
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldBcsFiatShamir

set_option autoImplicit false

noncomputable section

/-! ## Exact nonzero-BabyBear factorization -/

def queryIndexBits (ell : Nat) : Nat := ell - 1

def queryIndexSize (ell : Nat) : Nat := 2 ^ queryIndexBits ell

def querySlackSize (ell : Nat) : Nat :=
  15 * 2 ^ (27 - queryIndexBits ell)

theorem queryIndexBits_le_27 {ell : Nat} (hell : ell ≤ 28) :
    queryIndexBits ell ≤ 27 := by
  simp only [queryIndexBits]
  omega

theorem babyBear_nonzero_factorization {ell : Nat} (hell : ell ≤ 28) :
    modulus - 1 = querySlackSize ell * queryIndexSize ell := by
  have hbits := queryIndexBits_le_27 hell
  have hadd : 27 - queryIndexBits ell + queryIndexBits ell = 27 := by omega
  rw [modulus]
  simp only [querySlackSize, queryIndexSize]
  rw [Nat.mul_assoc, ← pow_add, hadd]
  norm_num

theorem queryIndexSize_pos (ell : Nat) : 0 < queryIndexSize ell := by
  simp [queryIndexSize]

theorem querySlackSize_pos (ell : Nat) : 0 < querySlackSize ell := by
  simp [querySlackSize]

theorem packedQuerySeed_lt_modulus {ell : Nat} (hell : ell ≤ 28)
    (slack : Fin (querySlackSize ell))
    (coordinate : PowerTwoFriLevels ell 1) :
    slack.val * queryIndexSize ell + coordinate.val + 1 < modulus := by
  have hfactor := babyBear_nonzero_factorization hell
  have hslack : slack.val + 1 ≤ querySlackSize ell :=
    Nat.succ_le_iff.mpr slack.isLt
  have hcoordLt := coordinate.isLt
  change coordinate.val < queryIndexSize ell at hcoordLt
  have hcoord : coordinate.val + 1 ≤ queryIndexSize ell :=
    Nat.succ_le_iff.mpr hcoordLt
  have hmul := Nat.mul_le_mul_right (queryIndexSize ell) hslack
  have hleft :
      slack.val * queryIndexSize ell + coordinate.val + 1 ≤
        (slack.val + 1) * queryIndexSize ell := by
    rw [Nat.add_mul]
    omega
  have hmodulus : 0 < modulus := by norm_num [modulus]
  calc
    slack.val * queryIndexSize ell + coordinate.val + 1 ≤
        (slack.val + 1) * queryIndexSize ell := hleft
    _ ≤ querySlackSize ell * queryIndexSize ell := hmul
    _ = modulus - 1 := hfactor.symm
    _ < modulus := by omega

/-- Every nonzero BabyBear element is uniquely a slack coordinate paired with
one power-of-two BaseFold coordinate. The second projection is literally
`(x.val - 1) % 2^(ell-1)`. -/
def acceptedScalarEquiv (ell : Nat) (hell : ell ≤ 28) :
    {x : F // x ≠ 0} ≃
      Fin (querySlackSize ell) × PowerTwoFriLevels ell 1 where
  toFun x :=
    let shifted := x.1.val - 1
    (⟨shifted / queryIndexSize ell, by
        apply (Nat.div_lt_iff_lt_mul (queryIndexSize_pos ell)).2
        rw [← babyBear_nonzero_factorization hell]
        have hxlt : x.1.val < modulus := ZMod.val_lt x.1
        have hxpos : 0 < x.1.val :=
          Nat.pos_of_ne_zero ((ZMod.val_eq_zero x.1).not.mpr x.2)
        omega⟩,
      ⟨shifted % queryIndexSize ell, Nat.mod_lt _ (queryIndexSize_pos ell)⟩)
  invFun pair :=
    let raw := pair.1.val * queryIndexSize ell + pair.2.val + 1
    ⟨(raw : F), by
      have hraw : raw < modulus := by
        exact packedQuerySeed_lt_modulus hell pair.1 pair.2
      intro hzero
      have hval := congrArg ZMod.val hzero
      rw [ZMod.val_cast_of_lt hraw, ZMod.val_zero] at hval
      omega⟩
  left_inv x := by
    apply Subtype.ext
    dsimp only
    have hxpos : 0 < x.1.val :=
      Nat.pos_of_ne_zero ((ZMod.val_eq_zero x.1).not.mpr x.2)
    have hrebuild :
        (x.1.val - 1) / queryIndexSize ell * queryIndexSize ell +
            (x.1.val - 1) % queryIndexSize ell + 1 = x.1.val := by
      rw [Nat.div_add_mod']
      omega
    rw [hrebuild, ZMod.natCast_zmod_val]
  right_inv pair := by
    have hcoord := pair.2.isLt
    change pair.2.val < queryIndexSize ell at hcoord
    have hraw :
        pair.1.val * queryIndexSize ell + pair.2.val + 1 < modulus := by
      exact packedQuerySeed_lt_modulus hell pair.1 pair.2
    apply Prod.ext
    · apply Fin.ext
      dsimp only
      rw [ZMod.val_cast_of_lt hraw, Nat.add_sub_cancel,
        Nat.mul_comm pair.1.val,
        Nat.mul_add_div (queryIndexSize_pos ell), Nat.div_eq_of_lt hcoord,
        Nat.add_zero]
    · apply Fin.ext
      dsimp only
      rw [ZMod.val_cast_of_lt hraw, Nat.add_sub_cancel,
        Nat.mul_comm pair.1.val, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hcoord]

/-- The accepted decoder is the second projection of the exact factorization. -/
def unbiasedQueryCoordinate {ell : Nat} (hell : ell ≤ 28)
    (seed : Digest) (accepted : seed 0 ≠ 0) : PowerTwoFriLevels ell 1 :=
  (acceptedScalarEquiv ell hell ⟨seed 0, accepted⟩).2

@[simp] theorem unbiasedQueryCoordinate_val {ell : Nat} (hell : ell ≤ 28)
    (seed : Digest) (accepted : seed 0 ≠ 0) :
    (unbiasedQueryCoordinate hell seed accepted : Nat) =
      ((seed 0).val - 1) % (2 ^ (ell - 1)) := rfl

/-- Conditional on accepting the nonzero field lane, every BaseFold query
coordinate is exactly uniform. This is equality for every event, not a
pointwise-bias estimate. -/
set_option maxHeartbeats 800000 in
theorem acceptedScalar_coordinate_uniform {ell : Nat} (hell : ell ≤ 28)
    (event : PowerTwoFriLevels ell 1 → Prop) :
    uniformProb {x : F // x ≠ 0}
        (fun x => event (acceptedScalarEquiv ell hell x).2) =
      uniformProb (PowerTwoFriLevels ell 1) event := by
  exact (uniformProb_equiv (acceptedScalarEquiv ell hell)
    (fun pair => event pair.2)).trans (uniformProb_prod_snd event)

/-! ## Fail-closed BaseFold schedule -/

def QuerySeedsAccepted {m queryCount : Nat}
    (receipt : Receipt m queryCount) : Prop :=
  ∀ a, receipt.querySeed a 0 ≠ 0

def unbiasedQuerySchedule {ell m queryCount : Nat}
    (hell : ell ≤ 28) (hmell : m ≤ ell)
    (receipt : Receipt m queryCount) (accepted : QuerySeedsAccepted receipt) :
    FriIndependentQuerySchedule (PowerTwoFriLevels ell) m queryCount :=
  powerTwoCoherentSchedule hmell fun a =>
    unbiasedQueryCoordinate hell (receipt.querySeed a) (accepted a)

def UnbiasedSubmittedOpeningsAccept {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (hell : ell ≤ 28) (hmell : m ≤ ell)
    (receipt : Receipt m queryCount) (seeds : QuerySeedsAccepted receipt) : Prop :=
  ∀ (j : Fin m) (a : Fin queryCount),
    OpenedFriQuery
      (BinaryMerkle.openingScheme hashSuite (ell - j))
      (BinaryMerkle.openingScheme hashSuite (ell - (j + 1)))
      (T.data j j.isLt)
      (receiptLevelRoot receipt j.castSucc)
      (receiptLevelRoot receipt j.succ)
      (receipt.challenge j) ((unbiasedQuerySchedule hell hmell receipt seeds) j a)
      (receipt.opening j a).toFri

/-- Strict BCS verifier: a zero first seed lane rejects, while every accepted
query coordinate is obtained from the exact uniform factorization above. -/
def UnbiasedAccepts {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hell : ell ≤ 28) (hmell : m ≤ ell) (statement : Statement m)
    (receipt : Receipt m queryCount) : Prop :=
  ∃ seeds : QuerySeedsAccepted receipt,
    DrawsExact statement receipt ∧
    RootsExact st receipt ∧
    (∀ i, i < m →
      (submittedProver receipt (chalOf receipt.challenge) i).degree <
        ((2 + 1 : Nat) : WithBot Nat)) ∧
    (∀ i, i < m →
      (submittedProver receipt (chalOf receipt.challenge) i).eval 0 +
          (submittedProver receipt (chalOf receipt.challenge) i).eval 1 =
        scChain statement.claimedValue
          (submittedProver receipt (chalOf receipt.challenge))
          (chalOf receipt.challenge) i) ∧
    UnbiasedSubmittedOpeningsAccept T hell hmell receipt seeds ∧
    st.wordAt receipt.challenge m le_rfl ∈
      reedSolomonCode (T.dom m) (basefoldDegSched m m) ∧
    ∀ k : PowerTwoFriLevels ell m,
      scChain statement.claimedValue
          (submittedProver receipt (chalOf receipt.challenge))
          (chalOf receipt.challenge) m =
        st.wordAt receipt.challenge m le_rfl k *
          eqMle statement.evaluationPoint receipt.challenge

/-- The strict decoder changes only the coherent query schedule. All accepted
algebraic, Merkle, and terminal evidence reflects losslessly into the existing
raw committed-IOR event on that exact schedule. -/
theorem unbiasedAccepts_to_rawCommittedIor {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hell : ell ≤ 28) (hmell : m ≤ ell) (statement : Statement m)
    (receipt : Receipt m queryCount)
    (accepted : UnbiasedAccepts T st hell hmell statement receipt) :
    ∃ seeds : QuerySeedsAccepted receipt,
      BaseFoldRawCommittedIorAccepts
        (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)) T st
        statement.evaluationPoint statement.claimedValue
        (submittedProver receipt) queryCount receipt.challenge
        (unbiasedQuerySchedule hell hmell receipt seeds) := by
  obtain ⟨seeds, accepted⟩ := accepted
  refine ⟨seeds, accepted.2.2.1, accepted.2.2.2.1, ?_, accepted.2.2.2.2.2.2⟩
  refine ⟨?_, accepted.2.2.2.2.2.1⟩
  intro j
  refine ⟨fun a => (receipt.opening j a).toFri, ?_⟩
  intro a
  have hopen := accepted.2.2.2.2.1 j a
  have rootJ := accepted.2.1 j (Nat.le_of_lt j.isLt)
  have rootNext := accepted.2.1 (j + 1) (Nat.succ_le_iff.mpr j.isLt)
  simpa [show receiptLevelRoot receipt j.castSucc =
        st.rootAt receipt.challenge j (Nat.le_of_lt j.isLt) by simpa using rootJ,
    show receiptLevelRoot receipt j.succ =
        st.rootAt receipt.challenge (j + 1)
          (Nat.succ_le_iff.mpr j.isLt) by simpa using rootNext] using hopen

#check @babyBear_nonzero_factorization
#check @acceptedScalarEquiv
#check @acceptedScalar_coordinate_uniform
#check @unbiasedAccepts_to_rawCommittedIor

/-- info: 'Minidregg.Selvage.BaseFoldBcsQuerySampling.acceptedScalar_coordinate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedScalar_coordinate_uniform
/-- info: 'Minidregg.Selvage.BaseFoldBcsQuerySampling.unbiasedAccepts_to_rawCommittedIor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unbiasedAccepts_to_rawCommittedIor

end

end Minidregg.Selvage.BaseFoldBcsQuerySampling
