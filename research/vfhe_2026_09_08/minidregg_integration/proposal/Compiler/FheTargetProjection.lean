/- Statement first: canonical target limbs must be the residues of the already
forced source integer. Exact per-prime QR and complement rows enforce this.
The frozen source certificate is composed at a full-assignment checker boundary;
this does not authenticate ciphertext provenance or replace a proof protocol. -/
import Compiler.FheSourceCertificateVerifier
import Compiler.FheSourceCertificateWitness

namespace Minidregg.Compiler.FheTargetProjection
open Minidregg.Compiler.FheRnsScale
open scoped BigOperators
set_option autoImplicit false

def targetPrime : Fin 3 → ℕ := ![68719403009,68719230977,137438822401]

def Projection (y : ℕ) (limbs quotients slacks : Fin 3 → ℕ) : Prop :=
  ∀ i, y=targetPrime i*quotients i+limbs i ∧ limbs i+slacks i=targetPrime i-1

def ProjectionSound : Prop := ∀ y limbs quotients slacks,
  Projection y limbs quotients slacks → ∀ i, limbs i=y%targetPrime i

/-- Exact pinned target factorization; no primality premise is needed to project. -/
theorem target_factors :
    (targetPrime 0 : ℤ)*targetPrime 1*targetPrime 2=deployedQ ∧
    (∀ i, 0<targetPrime i ∧ (targetPrime i : ℤ) ∣ deployedQ) ∧
    Nat.Coprime (targetPrime 0) (targetPrime 1) ∧
    Nat.Coprime (targetPrime 0) (targetPrime 2) ∧
    Nat.Coprime (targetPrime 1) (targetPrime 2) := by decide

/-- Reduction modulo Q preserves each target residue, including negative integers. -/
theorem target_reduce (z : ℤ) (i : Fin 3) :
    z%deployedQ%(targetPrime i : ℤ)=z%(targetPrime i : ℤ) :=
  Int.emod_emod_of_dvd z (target_factors.2.1 i).2

/-- Both QR equality and canonicality come from the projection relation. -/
theorem projectionSound : ProjectionSound := by
  intro y limbs quotients slacks h i
  obtain ⟨he,hr⟩ := h i
  have hp := (target_factors.2.1 i).1
  have hl : limbs i<targetPrime i := by omega
  simp [he,Nat.add_mod,Nat.mul_mod_right,Nat.mod_eq_of_lt hl]

/-- Honest quotient/remainder and complement values inhabit the relation for every y. -/
theorem projection_honest (y : ℕ) : Projection y
    (fun i => y%targetPrime i) (fun i => y/targetPrime i)
    (fun i => targetPrime i-1-y%targetPrime i) := by
  intro i
  dsimp only
  have hp := (target_factors.2.1 i).1
  have hr := Nat.mod_lt y hp
  exact ⟨(Nat.div_add_mod y (targetPrime i)).symm,by omega⟩

/-- Composition uses a proved divisor relation, not a CRT convention assumption. -/
theorem projection_source (r : Fin 6 → ℤ) (y : ℕ) (limbs quotients slacks : Fin 3 → ℕ)
    (hy : (y : ℤ)=deployedOutput r%deployedQ)
    (h : Projection y limbs quotients slacks) :
    ∀ i, (limbs i : ℤ)=deployedOutput r%(targetPrime i : ℤ) := by
  intro i
  have hh := congrArg (fun x : ℕ => (x : ℤ)) (projectionSound y limbs quotients slacks h i)
  dsimp only at hh
  rw [Int.natCast_mod,hy,target_reduce] at hh
  exact hh

/-- The captured actual coefficient is a nonzero inhabited target projection. -/
theorem captured_projection :
    deployedOutput capturedResidues=172481 ∧
    Projection 172481 (fun _ => 172481) (fun _ => 0)
      (fun i => targetPrime i-1-172481) := by
  refine ⟨deployed_witness_inhabited.2.2.1,?_⟩
  intro i
  fin_cases i <;> norm_num [targetPrime]

/-- Changing one canonical limb cannot preserve an accepting projection. -/
theorem captured_wrong_limb (quotients slacks : Fin 3 → ℕ) :
    ¬ Projection 172481 ![172480,172481,172481] quotients slacks := by
  intro h
  have hh := projectionSound _ _ _ _ h 0
  norm_num [targetPrime] at hh

end Minidregg.Compiler.FheTargetProjection

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheTargetProjection.target_factors' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.target_factors

/-- info: 'Minidregg.Compiler.FheTargetProjection.target_reduce' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.target_reduce

/-- info: 'Minidregg.Compiler.FheTargetProjection.projectionSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.projectionSound

/-- info: 'Minidregg.Compiler.FheTargetProjection.projection_honest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.projection_honest

/-- info: 'Minidregg.Compiler.FheTargetProjection.projection_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.projection_source

/-- info: 'Minidregg.Compiler.FheTargetProjection.captured_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.captured_projection

/-- info: 'Minidregg.Compiler.FheTargetProjection.captured_wrong_limb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.captured_wrong_limb
