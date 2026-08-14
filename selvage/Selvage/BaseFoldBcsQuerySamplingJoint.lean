/-
# Selvage.BaseFoldBcsQuerySamplingJoint — joint unbiased BaseFold query batches

`BaseFoldBcsQuerySampling` proves that one accepted BabyBear seed lane has an
exact uniform query-coordinate marginal.  A BaseFold verifier consumes a whole
batch of digest seeds, however, and the other seven lanes remain in the random
oracle output.  Pointwise marginals alone do not establish that the complete
query schedule is a uniform independent batch.

This module closes that finite-sample-space seam.  An accepted digest splits
bijectively into its seven unused lanes, the exact BabyBear slack coordinate,
and one power-of-two query coordinate.  The equivalence is lifted pointwise to
the entire query family, then nuisance coordinates are marginalized by exact
counting.  Thus every event over all accepted query coordinates has exactly
the same probability as under a fresh uniform coordinate vector.

Rejection remains outside this conditional space and retains the explicit
`q / BabyBear.modulus` price proved by the imported module.  No retry or ROM
assumption is introduced here.
-/

import Selvage.BaseFoldBcsQuerySampling

namespace Minidregg.Selvage.BaseFoldBcsQuerySamplingJoint

open Minidregg.Selvage
open BabyBearExt4
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsQuerySampling

set_option autoImplicit false

noncomputable section

noncomputable instance ext4Fintype : Fintype E :=
  Fintype.ofEquiv
    (Fin extensionPolynomial.natDegree → BabyBear) coefficients.symm.toEquiv

abbrev DigestTail := {lane : Fin 8 // lane ≠ 0} → F

abbrev AcceptedDigest := {seed : Digest // seed 0 ≠ 0}

abbrev AcceptedSeedFamily (queryCount : Nat) :=
  {seeds : Fin queryCount → Digest // ∀ a, seeds a 0 ≠ 0}

noncomputable instance acceptedSeedFamilyFintype (queryCount : Nat) :
    Fintype (AcceptedSeedFamily queryCount) :=
  Fintype.ofFinite _

abbrev QueryCoordinateFamily (ell queryCount : Nat) :=
  Fin queryCount → PowerTwoFriLevels ell 1

abbrev QuerySlackFamily (ell queryCount : Nat) :=
  Fin queryCount → Fin (querySlackSize ell)

/-! ## One digest, with every lane retained -/

/-- An accepted digest is exactly its seven unused lanes, one factorization
slack coordinate, and one BaseFold query coordinate. -/
def acceptedDigestEquiv (ell : Nat) (hell : ell ≤ 28) :
    AcceptedDigest ≃
      DigestTail × (Fin (querySlackSize ell) × PowerTwoFriLevels ell 1) where
  toFun seed :=
    (fun lane => seed.1 lane.1,
      acceptedScalarEquiv ell hell ⟨seed.1 0, seed.2⟩)
  invFun split :=
    let scalar := (acceptedScalarEquiv ell hell).symm split.2
    ⟨fun lane => if h : lane = 0 then scalar.1 else split.1 ⟨lane, h⟩,
      by simpa only [if_pos rfl] using scalar.2⟩
  left_inv seed := by
    apply Subtype.ext
    funext lane
    by_cases h : lane = 0
    · subst lane
      simp
    · simp [h]
  right_inv split := by
    apply Prod.ext
    · funext lane
      dsimp only
      simp [lane.2]
    · dsimp only
      simpa only [if_pos] using
        (acceptedScalarEquiv ell hell).apply_symm_apply split.2

/-! ## Lift the equivalence to a complete seed batch -/

/-- A family satisfying the pointwise acceptance predicate is the same type
as a family of accepted digests. -/
def acceptedSeedFamilyPointwiseEquiv (queryCount : Nat) :
    AcceptedSeedFamily queryCount ≃ (Fin queryCount → AcceptedDigest) where
  toFun seeds := fun a => ⟨seeds.1 a, seeds.2 a⟩
  invFun seeds := ⟨fun a => (seeds a).1, fun a => (seeds a).2⟩
  left_inv seeds := by rfl
  right_inv seeds := by rfl

/-- Distribute a finite family over the three product coordinates. -/
def piTripleEquiv (ι A B C : Type) :
    (ι → A × (B × C)) ≃ (ι → A) × ((ι → B) × (ι → C)) where
  toFun values :=
    (fun i => (values i).1, (fun i => (values i).2.1, fun i => (values i).2.2))
  invFun values := fun i => (values.1 i, (values.2.1 i, values.2.2 i))
  left_inv values := by rfl
  right_inv values := by rfl

/-- Whole-batch accepted-seed factorization.  This is a bijection of the
complete finite sample spaces, not a statement assembled from marginals. -/
def acceptedSeedFamilyEquiv (ell queryCount : Nat) (hell : ell ≤ 28) :
    AcceptedSeedFamily queryCount ≃
      (Fin queryCount → DigestTail) ×
        (QuerySlackFamily ell queryCount × QueryCoordinateFamily ell queryCount) :=
  (acceptedSeedFamilyPointwiseEquiv queryCount).trans <|
    (Equiv.piCongrRight fun _ : Fin queryCount =>
      acceptedDigestEquiv ell hell).trans <|
        piTripleEquiv (Fin queryCount) DigestTail
          (Fin (querySlackSize ell)) (PowerTwoFriLevels ell 1)

/-- The coordinates read by the strict verifier from an accepted digest
family. -/
def acceptedSeedCoordinates {ell queryCount : Nat} (hell : ell ≤ 28)
    (seeds : AcceptedSeedFamily queryCount) : QueryCoordinateFamily ell queryCount :=
  fun a => unbiasedQueryCoordinate hell (seeds.1 a) (seeds.2 a)

theorem acceptedSeedFamilyEquiv_coordinates {ell queryCount : Nat}
    (hell : ell ≤ 28) (seeds : AcceptedSeedFamily queryCount) :
    (acceptedSeedFamilyEquiv ell queryCount hell seeds).2.2 =
      acceptedSeedCoordinates hell seeds := by
  funext a
  apply Fin.ext
  rfl

/-! ## Exact joint uniformity -/

set_option maxHeartbeats 1600000 in
/-- Conditional on fail-closed acceptance, the entire query-coordinate family
is a fresh uniform product.  The unused digest lanes and factorization slack
coordinates are marginalized exactly. -/
theorem acceptedSeedCoordinates_uniform {ell queryCount : Nat}
    (hell : ell ≤ 28) (event : QueryCoordinateFamily ell queryCount → Prop) :
    uniformProb (AcceptedSeedFamily queryCount)
        (fun seeds => event (acceptedSeedCoordinates hell seeds)) =
      uniformProb (QueryCoordinateFamily ell queryCount) event := by
  letI : Nonempty (Fin (querySlackSize ell)) :=
    ⟨⟨0, querySlackSize_pos ell⟩⟩
  letI : Nonempty DigestTail := ⟨fun _ => 0⟩
  calc
    uniformProb (AcceptedSeedFamily queryCount)
        (fun seeds => event (acceptedSeedCoordinates hell seeds)) =
      uniformProb
        ((Fin queryCount → DigestTail) ×
          (QuerySlackFamily ell queryCount × QueryCoordinateFamily ell queryCount))
        (fun split => event split.2.2) := by
          simpa [acceptedSeedFamilyEquiv_coordinates] using
            (uniformProb_equiv (acceptedSeedFamilyEquiv ell queryCount hell)
              (fun split => event split.2.2))
    _ = uniformProb
        (QuerySlackFamily ell queryCount × QueryCoordinateFamily ell queryCount)
        (fun split => event split.2) :=
      uniformProb_prod_snd
        (A := Fin queryCount → DigestTail)
        (B := QuerySlackFamily ell queryCount ×
          QueryCoordinateFamily ell queryCount)
        (fun split => event split.2)
    _ = uniformProb (QueryCoordinateFamily ell queryCount) event :=
      uniformProb_prod_snd
        (A := QuerySlackFamily ell queryCount)
        (B := QueryCoordinateFamily ell queryCount) event

/-! ## Keep an independent challenge/context coordinate -/

/-- Reassociate the accepted-seed factorization so all nuisance coordinates
sit on the left and an arbitrary independent context remains paired with the
uniform query-coordinate family. -/
def acceptedSeedContextEquiv (A : Type) (ell queryCount : Nat)
    (hell : ell ≤ 28) :
    A × AcceptedSeedFamily queryCount ≃
      ((Fin queryCount → DigestTail) × QuerySlackFamily ell queryCount) ×
        (A × QueryCoordinateFamily ell queryCount) where
  toFun value :=
    let split := acceptedSeedFamilyEquiv ell queryCount hell value.2
    ((split.1, split.2.1), (value.1, split.2.2))
  invFun value :=
    (value.2.1,
      (acceptedSeedFamilyEquiv ell queryCount hell).symm
        (value.1.1, (value.1.2, value.2.2)))
  left_inv value := by
    apply Prod.ext
    · rfl
    · exact (acceptedSeedFamilyEquiv ell queryCount hell).symm_apply_apply value.2
  right_inv value := by
    obtain ⟨nuisance, context⟩ := value
    obtain ⟨tails, slack⟩ := nuisance
    obtain ⟨a, coordinates⟩ := context
    simp only
    rw [(acceptedSeedFamilyEquiv ell queryCount hell).apply_symm_apply]

theorem acceptedSeedContextEquiv_coordinates {A : Type}
    {ell queryCount : Nat} (hell : ell ≤ 28)
    (value : A × AcceptedSeedFamily queryCount) :
    (acceptedSeedContextEquiv A ell queryCount hell value).2 =
      (value.1, acceptedSeedCoordinates hell value.2) := by
  apply Prod.ext
  · rfl
  · exact acceptedSeedFamilyEquiv_coordinates hell value.2

set_option maxHeartbeats 1600000 in
/-- Joint uniformity is stable in the presence of an arbitrary independent
finite context.  In the BaseFold application this context is the complete
algebraic challenge vector, so this theorem rules out an illicit independence
shortcut when transporting the raw soundness event. -/
theorem acceptedSeedCoordinates_uniform_with_context
    {A : Type} [Fintype A] {ell queryCount : Nat} (hell : ell ≤ 28)
    (event : A × QueryCoordinateFamily ell queryCount → Prop) :
    uniformProb (A × AcceptedSeedFamily queryCount)
        (fun value => event (value.1, acceptedSeedCoordinates hell value.2)) =
      uniformProb (A × QueryCoordinateFamily ell queryCount) event := by
  letI : Nonempty (Fin (querySlackSize ell)) :=
    ⟨⟨0, querySlackSize_pos ell⟩⟩
  letI : Nonempty DigestTail := ⟨fun _ => 0⟩
  calc
    uniformProb (A × AcceptedSeedFamily queryCount)
        (fun value => event (value.1, acceptedSeedCoordinates hell value.2)) =
      uniformProb
        (((Fin queryCount → DigestTail) × QuerySlackFamily ell queryCount) ×
          (A × QueryCoordinateFamily ell queryCount))
        (fun split => event split.2) := by
          simpa only [acceptedSeedContextEquiv_coordinates] using
            (uniformProb_equiv
              (acceptedSeedContextEquiv A ell queryCount hell)
              (fun split => event split.2))
    _ = uniformProb (A × QueryCoordinateFamily ell queryCount) event :=
      uniformProb_prod_snd
        (A := (Fin queryCount → DigestTail) ×
          QuerySlackFamily ell queryCount)
        (B := A × QueryCoordinateFamily ell queryCount) event

/-! ## The exact raw-IOR transport -/

open Polynomial

/-- The raw committed-IOR bound may consume the strict sampler's complete
accepted digest family directly.  The challenge vector and the entire query
batch have exactly the same joint law as the existing theorem's native sample
space; no coordinatewise-independence premise is added. -/
theorem acceptedSeedRawCommittedIor_coherent_exact_sound
    {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hell : ell ≤ 28) (hmell : m ≤ ell)
    (z : Fin m → E) (H : E)
    (word : PowerTwoFriLevels ell 0 → E)
    (prover : (Nat → E) → Nat → Polynomial E)
    {tau : Real} (htau1 : tau ≤ 1)
    (htau : ∀ j : Fin m,
      tau ≤ 1 /
        (Fintype.card (PowerTwoFriLevels ell (j + 1)) : Real))
    (hword0 : st.word 0 (fun i => i.elim0) = word)
    (hfalse : ¬ BaseFoldExactClaim T z H word)
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (chi : Nat → E) (i : Nat), i < m →
      (prover chi i).degree < ((2 + 1 : Nat) : WithBot Nat)) :
    uniformProb
      ((Fin m → E) × AcceptedSeedFamily queryCount)
      (fun sample =>
        BaseFoldRawCommittedIorAccepts
          (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)) T st
          z H prover queryCount sample.1
          (powerTwoCoherentSchedule hmell
            (acceptedSeedCoordinates hell sample.2)))
      ≤ (m : Real) * (3 / Fintype.card E) + (1 - tau) ^ queryCount +
        uniformProb
          ((Fin m → E) × QueryCoordinateFamily ell queryCount)
          (fun sample =>
            FriRawAdaptiveEquivocates
              (fun n => BinaryMerkle.openingScheme hashSuite (ell - n))
              T st sample.1 queryCount
              (powerTwoCoherentSchedule hmell sample.2)) := by
  let event :
      (Fin m → E) × QueryCoordinateFamily ell queryCount → Prop :=
    fun sample =>
      BaseFoldRawCommittedIorAccepts
        (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)) T st
        z H prover queryCount sample.1
        (powerTwoCoherentSchedule hmell sample.2)
  change
    uniformProb ((Fin m → E) × AcceptedSeedFamily queryCount)
        (fun sample => event
          (sample.1, acceptedSeedCoordinates hell sample.2)) ≤ _
  rw [acceptedSeedCoordinates_uniform_with_context hell event]
  exact basefoldRawCommittedIor_coherent_exact_sound
    (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)) T st hmell
    z H word prover queryCount htau1 htau hword0 hfalse hpm hdeg

#check @acceptedDigestEquiv
#check @acceptedSeedFamilyEquiv
#check @acceptedSeedCoordinates_uniform
#check @acceptedSeedCoordinates_uniform_with_context
#check @acceptedSeedRawCommittedIor_coherent_exact_sound

/-- info: 'Minidregg.Selvage.BaseFoldBcsQuerySamplingJoint.acceptedSeedCoordinates_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedSeedCoordinates_uniform
/-- info: 'Minidregg.Selvage.BaseFoldBcsQuerySamplingJoint.acceptedSeedRawCommittedIor_coherent_exact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedSeedRawCommittedIor_coherent_exact_sound

end

end Minidregg.Selvage.BaseFoldBcsQuerySamplingJoint
