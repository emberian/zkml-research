/-
# Selvage.BabyBearExt4 — the deployed `X^4 - 11` challenge field

The zkML implementation rail serializes four BabyBear coefficients in the
power basis for `BabyBear[X]/(X^4-11)`.  Cardinality arithmetic alone does not
identify that carrier: BaseFold needs an actual field and the codec needs its
actual basis.

This module proves `X^4-11` irreducible over BabyBear.  The proof is structural:
`11` and `-11` are nonsquares by their checked Euler witnesses; `X^2-11` is
therefore irreducible; and a hypothetical square root of the quadratic root
would have a norm whose square is `-11`.  The resulting quartic is built as a
quadratic-over-quadratic Kummer polynomial.  No exhaustive enumeration of the
two-billion-element base field is used.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic.NormNum.Prime

namespace Minidregg.Selvage.BabyBearExt4

open Polynomial IntermediateField AdjoinRoot

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

def modulus : Nat := 2013265921
def halfOrder : Nat := 1006632960

abbrev BabyBear := ZMod modulus

instance modulusPrime : Fact (Nat.Prime modulus) := ⟨by
  norm_num [modulus]⟩

/-- The exact polynomial named by the Dregg2 suite's extension codec. -/
def extensionPolynomial : BabyBear[X] := X ^ 4 - C 11

/-- Repeated squaring as a small kernel computation.  This keeps the Euler
witness proof logarithmic instead of asking normalization to expand a
billionth power. -/
def squareN : Nat → BabyBear → BabyBear
  | 0, value => value
  | n + 1, value => (squareN n value) ^ 2

theorem squareN_eq_pow_two (n : Nat) (value : BabyBear) :
    squareN n value = value ^ (2 ^ n) := by
  induction n with
  | zero => simp [squareN]
  | succ n ih =>
      rw [squareN, ih, ← pow_mul]
      congr 1

theorem eleven_euler_witness :
    (11 : BabyBear) ^ halfOrder = -1 := by
  calc
    (11 : BabyBear) ^ halfOrder = ((11 : BabyBear) ^ 15) ^ (2 ^ 26) := by
      rw [← pow_mul]
      norm_num [halfOrder]
    _ = squareN 26 ((11 : BabyBear) ^ 15) := by
      rw [squareN_eq_pow_two]
    _ = -1 := by decide

theorem neg_eleven_euler_witness :
    (-11 : BabyBear) ^ halfOrder = -1 := by
  calc
    (-11 : BabyBear) ^ halfOrder = (-1) ^ halfOrder * 11 ^ halfOrder :=
      neg_pow 11 halfOrder
    _ = 11 ^ halfOrder := by norm_num [halfOrder]
    _ = -1 := eleven_euler_witness

/-- An Euler witness `a^((p-1)/2) = -1` rules out a square root in BabyBear. -/
private theorem nonsquare_of_euler_witness (a : BabyBear)
    (witness : a ^ halfOrder = -1) (b : BabyBear) : b ^ 2 ≠ a := by
  intro square
  have bne : b ≠ 0 := by
    intro bz
    subst b
    have azero : a = 0 := by simpa using square.symm
    subst a
    simp [halfOrder] at witness
  have fermat : b ^ (modulus - 1) = 1 := by
    simpa [BabyBear, modulus] using
      (FiniteField.pow_card_sub_one_eq_one b bne)
  have impossible : (1 : BabyBear) = -1 := by
    calc
      1 = b ^ (modulus - 1) := fermat.symm
      _ = (b ^ 2) ^ halfOrder := by
        rw [← pow_mul]
        norm_num [modulus, halfOrder]
      _ = a ^ halfOrder := congrArg (· ^ halfOrder) square
      _ = -1 := witness
  have one_ne_neg_one : (1 : BabyBear) ≠ -1 := by decide
  exact one_ne_neg_one impossible

theorem eleven_not_square (b : BabyBear) : b ^ 2 ≠ 11 :=
  nonsquare_of_euler_witness 11 eleven_euler_witness b

theorem neg_eleven_not_square (b : BabyBear) : b ^ 2 ≠ -11 :=
  nonsquare_of_euler_witness (-11) neg_eleven_euler_witness b

/-- The first quadratic step in the quartic construction. -/
theorem quadraticPolynomial_irreducible :
    Irreducible (X ^ 2 - C (11 : BabyBear)) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) eleven_not_square

/-- The exact deployed quartic is irreducible.  If the quadratic generator
were a square in its degree-two extension, taking its norm would make `-11` a
square in BabyBear, contradicting the second Euler witness. -/
theorem extensionPolynomial_irreducible : Irreducible extensionPolynomial := by
  have quartic := X_pow_mul_sub_C_irreducible
    (n := 2) (m := 2) quadraticPolynomial_irreducible (by
      intro E _field _algebra x minpolyExact
      apply X_pow_sub_C_irreducible_of_prime (by norm_num)
      intro b square
      have integral : IsIntegral BabyBear x := not_not.mp fun notIntegral => by
        simpa only [degree_zero, degree_X_pow_sub_C (by norm_num : 0 < 2),
          WithBot.natCast_ne_bot] using
          congrArg degree
            (minpolyExact.symm.trans (dif_neg notIntegral))
      apply neg_eleven_not_square (Algebra.norm BabyBear b)
      rw [← map_pow, square, ← IntermediateField.adjoin.powerBasis_gen integral,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
      simp [minpoly_gen, minpolyExact])
  simpa [extensionPolynomial] using quartic

instance extensionPolynomialIrreducible : Fact (Irreducible extensionPolynomial) :=
  ⟨extensionPolynomial_irreducible⟩

/-- The actual degree-four challenge carrier, with the quotient's power basis. -/
abbrev Ext4 := AdjoinRoot extensionPolynomial

/-- The deployed basis generator satisfies exactly `u^4 = 11`. -/
theorem root_pow_four :
    (AdjoinRoot.root extensionPolynomial : Ext4) ^ 4 =
      algebraMap BabyBear Ext4 11 := by
  simpa [extensionPolynomial] using
    (root_X_pow_sub_C_pow 4 (11 : BabyBear))

theorem extensionPolynomial_natDegree : extensionPolynomial.natDegree = 4 := by
  simp [extensionPolynomial]

theorem ext4_finrank : Module.finrank BabyBear Ext4 = 4 := by
  change Module.finrank BabyBear
    (BabyBear[X] ⧸ Ideal.span {extensionPolynomial}) = 4
  rw [finrank_quotient_span_eq_natDegree]
  exact extensionPolynomial_natDegree

/-- Canonical coefficient view supplied by the quotient's power basis.  Its
index has proved cardinality four; no unrelated abstract GF(p^4) basis enters
the codec boundary. -/
noncomputable def coefficients :
    Ext4 ≃ₗ[BabyBear] (Fin extensionPolynomial.natDegree → BabyBear) :=
  (AdjoinRoot.powerBasis extensionPolynomial_irreducible.ne_zero).basis.equivFun

#check @extensionPolynomial_irreducible
#check @root_pow_four
#check @ext4_finrank

/-- info: 'Minidregg.Selvage.BabyBearExt4.extensionPolynomial_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extensionPolynomial_irreducible

end

end Minidregg.Selvage.BabyBearExt4
