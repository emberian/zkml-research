/- Actual BabyBear canonical-word modulo sampling. The source distribution is
explicitly fresh uniform base elements; no Fiat--Shamir uniformity is asserted. -/
import Selvage.FiniteModuloSampling

namespace Minidregg.Selvage.BabyBearModuloSampling
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open BabyBearExt4 FiniteModuloSampling

/-- Canonical representatives of the actual existing BabyBear base field. -/
def canonicalEquiv : BabyBear ≃ Fin modulus := (ZMod.finEquiv modulus).toEquiv.symm

/-- This equivalence is exactly the field's canonical integer representation. -/
theorem canonicalEquiv_val (x : BabyBear) : (canonicalEquiv x).val = x.val := rfl

/-- The mathematical value of the vendor's canonical-value bit mask. -/
def sampleBits (ell : ℕ) (x : BabyBear) : Fin (2^ell) :=
  sampleModulo (2^ell) (by positivity) (canonicalEquiv x)

/-- Exact source-map identity for `canonical & ((1 << ell)-1)`. -/
theorem sampleBits_mask (ell : ℕ) (x : BabyBear) :
    (sampleBits ell x).val = x.val &&& (2^ell-1) := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- The source map preserves the identity between uniform base elements and canonical words. -/
theorem uniform_canonical (ell : ℕ) (E : Fin (2^ell) → Prop) :
    uniformProb BabyBear (fun x => E (sampleBits ell x)) =
      uniformProb (Fin modulus) (fun x => E (sampleModulo (2^ell) (by positivity) x)) :=
  uniformProb_equiv canonicalEquiv
    (fun x : Fin modulus => E (sampleModulo (2^ell) (by positivity) x))

/-- BabyBear has exactly this many complete cycles at every supported two-adic height. -/
def cycles (ell : ℕ) : ℕ := 15*2^(27-ell)

theorem cycles_positive (ell : ℕ) : 0 < cycles ell := by unfold cycles; positivity

/-- Exact arithmetic, including ell=0: p = cycles * 2^ell + 1. -/
theorem modulus_cycles (ell : ℕ) (hell : ell ≤ 27) : cycles ell * 2^ell + 1 = modulus := by
  unfold cycles
  rw [Nat.mul_assoc,←pow_add,Nat.sub_add_cancel hell]
  norm_num [modulus]

/-- Statement-first actual-base fresh-word sampling contract. -/
def FreshBitsLaw (ell : ℕ) : Prop := ∀ E : Fin (2^ell) → Prop,
  uniformProb BabyBear (fun x => E (sampleBits ell x)) =
    ((modulus-1:ℕ):ℝ)/modulus * uniformProb (Fin (2^ell)) E +
      (if E ⟨0,by positivity⟩ then 1/(modulus:ℝ) else 0)

/-- Exact arbitrary-predicate BabyBear law. The extra canonical representative is zero modulo 2^ell. -/
theorem fresh_bits_exact (ell : ℕ) (hell : ell ≤ 27) : FreshBitsLaw ell := by
  intro E
  rw [uniform_canonical]
  have h := pushforward_exact (cycles ell) (2^ell) (by positivity) E
  have hp := modulus_cycles ell hell
  have hn : cycles ell * 2^ell = modulus-1 := by omega
  have hp' : (cycles ell:ℝ)*(2^ell:ℝ)+1 = (modulus:ℝ) := by exact_mod_cast hp
  rw [hp,hn] at h
  simp only [Nat.cast_pow,Nat.cast_ofNat] at h
  rw [hp'] at h
  exact h

/-- q independent fresh actual base-field elements give the exact qth power. -/
theorem fresh_bits_independent_exact (ell : ℕ) (hell : ell ≤ 27) (q : ℕ)
    (E : Fin (2^ell) → Prop) :
    uniformProb (Fin q → BabyBear) (fun x => ∀ j, E (sampleBits ell (x j))) =
      (((modulus-1:ℕ):ℝ)/modulus * uniformProb (Fin (2^ell)) E +
        (if E ⟨0,by positivity⟩ then 1/(modulus:ℝ) else 0))^q := by
  rw [ArityEight.Schedule.uniformProb_all_coordinates q (fun x => E (sampleBits ell x)),
    fresh_bits_exact ell hell E]

/-- The verifier adapter can apply its uniform-index survival bound to this
exact fresh-base sampler, retaining the canonical-modulo bias. -/
theorem fresh_bits_independent_bound (ell : ℕ) (hell : ell ≤ 27) (q : ℕ)
    (E : Fin (2^ell) → Prop) (t : ℝ) (ht : uniformProb (Fin (2^ell)) E ≤ t) :
    uniformProb (Fin q → BabyBear) (fun x => ∀ j, E (sampleBits ell (x j))) ≤
      (((modulus-1:ℕ):ℝ)/modulus*t+1/(modulus:ℝ))^q := by
  rw [ArityEight.Schedule.uniformProb_all_coordinates q (fun x => E (sampleBits ell x))]
  apply pow_le_pow_left₀ (uniformProb_nonneg _)
  rw [fresh_bits_exact ell hell E]
  apply add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
  split_ifs
  · exact le_rfl
  · positivity

/-- The actual-base keystone has an inhabited, nontrivial bit-height premise. -/
theorem fresh_bits_premises_inhabited : ∃ ell : ℕ,
    0 < ell ∧ ell ≤ 27 ∧ FreshBitsLaw ell :=
  ⟨1,by decide,by decide,fresh_bits_exact 1 (by decide)⟩

/-- Actual BabyBear witness: residue zero is strictly heavier than residue one
at every positive supported bit height. This refutes exact uniformity of sample_bits. -/
theorem actual_zero_bias (ell : ℕ) (h0 : 0 < ell) (hell : ell ≤ 27) :
    uniformProb BabyBear (fun x => sampleBits ell x = ⟨1,by exact Nat.one_lt_two_pow h0.ne'⟩) <
      uniformProb BabyBear (fun x => sampleBits ell x = ⟨0,by positivity⟩) := by
  rw [uniform_canonical ell (fun i => i = ⟨1,by exact Nat.one_lt_two_pow h0.ne'⟩),
    uniform_canonical ell (fun i => i = ⟨0,by positivity⟩)]
  have h := zero_bias_witness (cycles ell) (2^ell) (Nat.one_lt_two_pow h0.ne')
  rw [modulus_cycles ell hell] at h
  exact h

end Minidregg.Selvage.BabyBearModuloSampling

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.canonicalEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.canonicalEquiv_val

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.sampleBits_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.sampleBits_mask

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.uniform_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.uniform_canonical

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.cycles_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.cycles_positive

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.modulus_cycles' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.modulus_cycles

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_exact

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_independent_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_independent_exact

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_independent_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_independent_bound

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.fresh_bits_premises_inhabited

/-- info: 'Minidregg.Selvage.BabyBearModuloSampling.actual_zero_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.BabyBearModuloSampling.actual_zero_bias

