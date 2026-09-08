/-
# Certified BabyBear roots of unity on the actual extension carrier

The current scalar prover's generator is 440564289 = 31^15 in BabyBear.
Reuse BabyBearExt4.squareN for logarithmic kernel arithmetic; no enumeration
of the base field or native_decide is used. Map the certified root through
the existing BabyBear → Ext4 algebra embedding.
-/
import Selvage.BabyBearExt4
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Minidregg.Selvage.BabyBearExt4
namespace TwoAdic

noncomputable section
set_option maxRecDepth 100000

def generator : BabyBear := 440564289

/-- Statement-first exact source-generator contract, including order. -/
def GeneratorContract : Prop :=
  generator = (31 : BabyBear)^15 ∧ IsPrimitiveRoot generator (2^27)

/-- The source's scalar multiplicative generator exponent matches exactly. -/
theorem generator_source_value : generator = (31 : BabyBear)^15 := by decide

/-- Certified 26 squarings attain -1, proving the large 2-primary order. -/
theorem generator_half_order : generator^(2^26) = -1 := by
  rw [← squareN_eq_pow_two]
  decide

/-- One more squaring is exactly the identity. -/
theorem generator_full_order : generator^(2^27) = 1 := by
  calc
    generator^(2^27) = (generator^(2^26))^2 := by rw [← pow_mul]; congr 1
    _ = 1 := by rw [generator_half_order]; norm_num

/-- Exact order from the prime-power criterion and certified squarings. -/
theorem generator_primitive : IsPrimitiveRoot generator (2^27) := by
  have hnot : ¬ generator^(2^26) = 1 := by
    rw [generator_half_order]
    decide
  have hord : orderOf generator = 2^27 :=
    orderOf_eq_prime_pow (p := 2) (n := 26) hnot generator_full_order
  rw [← hord]
  exact IsPrimitiveRoot.orderOf generator

theorem generator_contract : GeneratorContract :=
  ⟨generator_source_value, generator_primitive⟩

/-- The primitive-root contract has the exact runtime generator as witness. -/
theorem generator_premise_inhabited :
    ∃ g : BabyBear, g = 440564289 ∧ IsPrimitiveRoot g (2^27) :=
  ⟨generator, rfl, generator_primitive⟩

/-- Squaring the generator cannot preserve its advertised full order. -/
theorem squared_generator_falsifier : ¬ IsPrimitiveRoot (generator^2) (2^27) := by
  intro h
  apply h.pow_ne_one_of_pos_of_lt (l := 2^26) (by norm_num) (by norm_num)
  simpa only [← pow_mul, show 2 * 2^26 = 2^27 by norm_num] using generator_full_order

/-- The exact scalar generator viewed inside the existing X^4-11 carrier. -/
def extensionGenerator : Ext4 := algebraMap BabyBear Ext4 generator

/-- Injective field embedding preserves exact multiplicative order. -/
theorem extension_generator_primitive : IsPrimitiveRoot extensionGenerator (2^27) :=
  generator_primitive.map_of_injective (algebraMap BabyBear Ext4).injective

/-- The same repeated-squaring choice as prover/src/babybear.rs. -/
def omega (bits : ℕ) : Ext4 := extensionGenerator^(2^(27-bits))

/-- Exact match to the active p3 table's 20-bit root, 0x0ba067a3. -/
theorem omega20_source_value : omega 20 = algebraMap BabyBear Ext4 195061667 := by
  change (algebraMap BabyBear Ext4 generator)^(2^7) = _
  rw [← map_pow]
  congr 1

/-- Every supported level uses a primitive root of its exact power-of-two size. -/
theorem omega_primitive (bits : ℕ) (hbits : bits ≤ 27) :
    IsPrimitiveRoot (omega bits) (2^bits) := by
  apply IsPrimitiveRoot.pow (by norm_num : 0 < 2^27) extension_generator_primitive
  rw [← pow_add, Nat.sub_add_cancel hbits]

/-- Supported domain points and all their powers are nonzero. -/
theorem omega_ne_zero (bits : ℕ) (hbits : bits ≤ 27) : omega bits ≠ 0 :=
  (omega_primitive bits hbits).ne_zero (by positivity)

/-- The next smaller source root is exactly the square of the current root. -/
theorem omega_square (bits : ℕ) (hbits : bits < 27) :
    omega (bits+1)^2 = omega bits := by
  unfold omega
  rw [← pow_mul, ← pow_succ]
  congr 2
  omega

/-- Half a turn is negation, which makes each multiplicative FRI fibre a pair. -/
theorem omega_half_turn (bits : ℕ) (hbits : bits < 27) :
    omega (bits+1)^(2^bits) = -1 := by
  apply IsPrimitiveRoot.eq_neg_one_of_two_right
  exact IsPrimitiveRoot.pow (by positivity : 0 < 2^(bits+1))
    (omega_primitive (bits+1) (by omega)) (by rw [pow_succ])

end
end TwoAdic
end Minidregg.Selvage.BabyBearExt4

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_source_value
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_half_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_half_order
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_full_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_full_order
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_primitive
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_contract
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.generator_premise_inhabited
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.squared_generator_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.squared_generator_falsifier
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.extension_generator_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.extension_generator_primitive
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.omega20_source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.omega20_source_value
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_primitive
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_ne_zero
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_square
/-- info: 'Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_half_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.TwoAdic.omega_half_turn
