/-
Actual-Q83 source-equation witnesses. Ciphertexts inhabit the mathematical
negacyclic quotient, not Rust objects. No secret-key erasure/privacy claim.
The source equations, nonzero error and selected coefficient are exercised;
full Rust/RNS/NTT, serializer and scaler refinement remain unproved.
-/
import Theory.BfvPhaseAlgebra
import Assurance.ResidentBfvWindowNoise

namespace Minidregg.Assurance.ResidentBfvSourcePhase
set_option autoImplicit false
open Minidregg.Theory.BfvPhaseAlgebra
open Minidregg.Theory.IntegerWindowNoise (Fresh Row rounded centered rowScore)
open Minidregg.Assurance.ResidentBfvWindowNoise
open scoped BigOperators

abbrev Q : Nat := 9671406214650060397780993
abbrev N : Nat := 4096
instance qLarge : Fact (1 < Q) := ⟨by decide⟩
noncomputable abbrev R := Minidregg.Theory.BfvPhaseAlgebra.Ring Q N
def delta : ZMod Q := 9653009781167034675697743

def message (j : Fin N) : Int := if j.val = 0 then 1 else 0
def row : Row width where
  message j := if j = firstCoordinate then 1 else 0
  error j := if j = firstCoordinate then 9 else 0
  phase j := q83 * (if j = firstCoordinate then 1 else 0) / t32 + (if j = firstCoordinate then 9 else 0)
noncomputable def cipher : CipherPair R := encrypt (keygen 2 3 1) 4 1 2 (encodeRing Q N t32 delta message)
def integerLift : Int := -(q83 / t32 + 9)
noncomputable def queryRing : R := AdjoinRoot.mk (modulus Q N)
  (reverseQuery Q 576 (fun j => (witnessQuery j : ZMod Q)))

def Subject : Prop :=
  ScalingPremise Q t32 delta ∧ ActualPremises [row] witnessQuery ∧
  Minidregg.Theory.BfvPhaseAlgebra.readoutPhase Q N 2 queryRing 576 cipher = (integerLift : ZMod Q) ∧
  centered t32 (rounded q83 t32 integerLift) = -1

theorem delta_inverse : ScalingPremise Q t32 delta := by
  unfold ScalingPremise
  decide

theorem source_q_mod_t : (Q : Int) % t32 = 541778926 := by decide

theorem delta_limb_remainders :
    (9653009781167034675697743 : Int) % 2199023190017 = 1144893300664 ∧
    (9653009781167034675697743 : Int) % 4398046486529 = 2396387273630 := by decide

theorem delta_limb_inverses :
    (-(t32 : ZMod 2199023190017)) * 1144893300664 = 1 ∧
    (-(t32 : ZMod 4398046486529)) * 2396387273630 = 1 := by decide

theorem source_encoding_actual (m : Int) : sourceEncoded Q t32 m delta = ((q83 * m / t32 : Int) : ZMod Q) :=
  source_encoded_floor Q t32 m delta delta_inverse

theorem noise_exact : noise (2 : R) 1 4 1 2 = 9 := by norm_num [noise]

def fullIndex (j : Fin width) : Fin N := ⟨j.val, by have hj := j.isLt; dsimp [N, width] at *; omega⟩

theorem source_coefficient (j : Fin width) :
    coefficient Q N j.val (phase (2 : R) cipher) = (row.phase j : ZMod Q) := by
  have hj : j.val = 0 ↔ j = firstCoordinate := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      exact congrArg Fin.val h
  have hm : message (fullIndex j) = row.message j := by
    simp only [message, fullIndex, row, hj]
  have hn : coefficient Q N j.val (noise (2 : R) 1 4 1 2) = (row.error j : ZMod Q) := by
    rw [noise_exact]
    have h := coefficient_intCast Q N 9 j.val
    change coefficient Q N j.val (9 : R) = _ at h
    simpa only [hj, row, Int.cast_ite, Int.cast_ofNat, Int.cast_zero] using h
  have h := encrypted_coefficient Q N (2 : R) 3 1 4 1 2 t32 delta message (fullIndex j) delta_inverse
  change coefficient Q N j.val (phase (2 : R) cipher) =
    (((Q : Int) * message (fullIndex j) / t32 : Int) : ZMod Q) +
      coefficient Q N j.val (noise (2 : R) 1 4 1 2) at h
  rw [hm, hn, ← Int.cast_add] at h
  exact h

theorem row_fresh : Fresh q83 t32 freshBound row := by
  intro j
  constructor
  · rfl
  · by_cases hj : j = firstCoordinate <;> simp [row, hj, freshBound, ringDegree, support]

theorem actual_premises : ActualPremises [row] witnessQuery := by
  refine ⟨?_, by decide, witness_premises.2.2.1, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact row_fresh
  · intro x hx j
    simp only [List.mem_singleton] at hx
    subst x
    by_cases hj : j = firstCoordinate <;> simp [row, hj, coordinateBound]

theorem row_phase : Minidregg.Theory.IntegerWindowNoise.rowPhase witnessQuery row = integerLift := by
  simp [Minidregg.Theory.IntegerWindowNoise.rowPhase, witnessQuery, row, integerLift]

theorem row_score : rowScore witnessQuery row = -1 := by
  unfold rowScore
  rw [Finset.sum_eq_single firstCoordinate]
  · simp [witnessQuery, row]
  · intro j _ hj
    simp [witnessQuery, hj]
  · simp

theorem phase_matches_integer :
    Minidregg.Theory.BfvPhaseAlgebra.readoutPhase Q N 2 queryRing 576 cipher = (integerLift : ZMod Q) := by
  have h := readout_integer_row Q N (2 : R) cipher 576 witnessQuery row
    (by decide) (by decide) source_coefficient
  change Minidregg.Theory.BfvPhaseAlgebra.readoutPhase Q N 2 queryRing 576 cipher =
    (Minidregg.Theory.IntegerWindowNoise.rowPhase witnessQuery row : ZMod Q) at h
  rw [row_phase] at h
  exact h

theorem decoded : centered t32 (rounded q83 t32 integerLift) = -1 := by
  have h := actual_signed_window [row] witnessQuery 0 actual_premises
  simpa [Minidregg.Theory.IntegerWindowNoise.readoutPhase,
    Minidregg.Theory.IntegerWindowNoise.readoutScore, row_phase, row_score] using h

theorem subject : Subject := ⟨delta_inverse, actual_premises, phase_matches_integer, decoded⟩

theorem source_nonzero :
    row.message firstCoordinate = 1 ∧ row.error firstCoordinate = 9 ∧
    cipher ≠ 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro hc
  have hp := phase_matches_integer
  rw [hc, map_zero] at hp
  have hn : (integerLift : ZMod Q) ≠ 0 := by decide
  exact hn hp.symm

/-- A plus sign in key generation fails the very noise equation that the
source's subtraction supplies. This is an arithmetic falsifier. -/
theorem wrong_key_sign : phase (2 : ZMod Q) (1 + 3 * 2, 3) = 13 ∧
    phase (2 : ZMod Q) (1 + 3 * 2, 3) ≠ 1 := by decide

/-- Dropping the minus sign in inverse(-t) changes the encoded residue. -/
theorem wrong_scaler_sign : sourceEncoded Q t32 1 (-delta) ≠ sourceEncoded Q t32 1 delta := by decide

/-- High noise coefficients do wrap, but below the selected output. Reading
coefficient zero here would substitute a different result for target576. -/
theorem wrapped_noise_wrong_slot :
    coefficient Q N 576 ((AdjoinRoot.root (modulus Q N)) ^ 4095 * AdjoinRoot.root (modulus Q N)) = 0 ∧
    coefficient Q N 0 ((AdjoinRoot.root (modulus Q N)) ^ 4095 * AdjoinRoot.root (modulus Q N)) = -1 := by
  have hw : (AdjoinRoot.root (modulus Q N)) ^ 4095 * AdjoinRoot.root (modulus Q N) = (-1 : R) := by
    rw [← pow_succ]
    exact root_power Q N
  rw [hw]
  constructor
  · have h := coefficient_intCast Q N (-1) 576
    simpa using h
  · have h := coefficient_intCast Q N (-1) 0
    simpa using h

/- Observed axiom closure pins from the successful check. -/
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.delta_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.delta_inverse
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.source_q_mod_t' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.source_q_mod_t
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.delta_limb_remainders' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.delta_limb_remainders
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.delta_limb_inverses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.delta_limb_inverses
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.source_encoding_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.source_encoding_actual
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.noise_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.noise_exact
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.source_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.source_coefficient
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.row_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.row_fresh
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.actual_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.actual_premises
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.row_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.row_phase
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.row_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.row_score
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.phase_matches_integer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.phase_matches_integer
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.decoded
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.subject
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.source_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.source_nonzero
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.wrong_key_sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.wrong_key_sign
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.wrong_scaler_sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.wrong_scaler_sign
/-- info: 'Minidregg.Assurance.ResidentBfvSourcePhase.wrapped_noise_wrong_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvSourcePhase.wrapped_noise_wrong_slot

end Minidregg.Assurance.ResidentBfvSourcePhase
