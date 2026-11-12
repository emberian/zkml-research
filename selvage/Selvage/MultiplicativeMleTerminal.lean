/-
# Selvage.MultiplicativeMleTerminal -- MLE terminal through multiplicative FRI folds

The runtime begins with a raw Boolean-cube value table, performs the Boolean
Möbius transform to obtain LSB-first monomial coefficients, pads those
coefficients with zeros, and then folds the resulting univariate polynomial by
`evenPart p + C r * oddPart p` for each MLE coordinate.  This file proves that
the constant left after all variables is exactly the multilinear extension of
the original raw table.
-/
import Selvage.MultilinearExtension
import Selvage.Proximity
import Mathlib.Algebra.Polynomial.Expand

namespace Minidregg.Selvage

open Polynomial

variable {F : Type*} [Field F]

/-! ## Coefficient-level parity split -/

/-- `evenPart` really selects the even-numbered coefficients. -/
theorem coeff_evenPart_terminal (p : F[X]) (k : ℕ) :
    (evenPart p).coeff k = p.coeff (2 * k) := by
  classical
  simp [evenPart]
  intro hk
  symm
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- `oddPart` really selects the odd-numbered coefficients. -/
theorem coeff_oddPart_terminal (p : F[X]) (k : ℕ) :
    (oddPart p).coeff k = p.coeff (2 * k + 1) := by
  classical
  simp [oddPart]
  intro hk
  symm
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## LSB-first coefficient packing -/

/-- Interleave two coefficient polynomials: `even` occupies indices `2k` and
`odd` occupies indices `2k+1`.  This is the coefficient-layout primitive used
by the recursive Boolean Möbius transform. -/
noncomputable def parityInterleave (even odd : F[X]) : F[X] :=
  Polynomial.expand F 2 even + X * Polynomial.expand F 2 odd

theorem coeff_parityInterleave_even (even odd : F[X]) (k : ℕ) :
    (parityInterleave even odd).coeff (2 * k) = even.coeff k := by
  classical
  cases k with
  | zero =>
      rw [parityInterleave, coeff_add,
        Polynomial.coeff_expand (by omega)]
      simp
  | succ k =>
      have hodd : ¬ 2 ∣ 2 * k + 1 := by
        rintro ⟨a, ha⟩
        omega
      rw [parityInterleave, coeff_add,
        Polynomial.coeff_expand_mul' (by omega) even (k + 1),
        show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        coeff_X_mul, Polynomial.coeff_expand (by omega)]
      simp [hodd]

theorem coeff_parityInterleave_odd (even odd : F[X]) (k : ℕ) :
    (parityInterleave even odd).coeff (2 * k + 1) = odd.coeff k := by
  classical
  have hodd : ¬ 2 ∣ 2 * k + 1 := by
    rintro ⟨a, ha⟩
    omega
  rw [parityInterleave, coeff_add, Polynomial.coeff_expand (by omega),
    if_neg hodd, coeff_X_mul,
    Polynomial.coeff_expand_mul' (by omega) odd k]
  exact zero_add _

/-- Parity splitting exactly undoes interleaving. -/
@[simp] theorem evenPart_parityInterleave (even odd : F[X]) :
    evenPart (parityInterleave even odd) = even := by
  ext k
  rw [coeff_evenPart_terminal, coeff_parityInterleave_even]

/-- Parity splitting exactly undoes interleaving. -/
@[simp] theorem oddPart_parityInterleave (even odd : F[X]) :
    oddPart (parityInterleave even odd) = odd := by
  ext k
  rw [coeff_oddPart_terminal, coeff_parityInterleave_odd]

/-! ## Boolean head/tail convention and the MLE recurrence -/

/-- Prepend the LSB coordinate. -/
def lsbCons {A : Type*} {m : ℕ} (head : A) (tail : Fin m → A) :
    Fin (m + 1) → A :=
  Fin.cons head tail

@[simp] theorem lsbCons_zero {A : Type*} {m : ℕ} (head : A)
    (tail : Fin m → A) : lsbCons head tail 0 = head := by
  simp [lsbCons]

@[simp] theorem lsbCons_succ {A : Type*} {m : ℕ} (head : A)
    (tail : Fin m → A) (i : Fin m) : lsbCons head tail i.succ = tail i := by
  simp [lsbCons]

/-- LSB-first cube words are exactly a head bit followed by the remaining
cube word. -/
def lsbCubeEquiv (m : ℕ) :
    (Fin (m + 1) → Bool) ≃ Bool × (Fin m → Bool) where
  toFun b := (b 0, fun i => b i.succ)
  invFun hb := lsbCons hb.1 hb.2
  left_inv b := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv hb := by
    rcases hb with ⟨h, b⟩
    simp

@[simp] theorem lsbCubeEquiv_symm_apply (m : ℕ)
    (hb : Bool × (Fin m → Bool)) :
    (lsbCubeEquiv m).symm hb = lsbCons hb.1 hb.2 := rfl

/-- The chi basis splits into its LSB factor and tail product. -/
theorem chiEval_lsbCons {m : ℕ} (head : Bool) (tail : Fin m → Bool)
    (x : F) (xs : Fin m → F) :
    chiEval (lsbCons head tail) (lsbCons x xs) =
      (if head then x else 1 - x) * chiEval tail xs := by
  simp [chiEval, Fin.prod_univ_succ]

/-- MLE evaluation eliminates the LSB by affine interpolation of the two
adjacent raw-table entries. -/
theorem mle_lsb_recurrence {m : ℕ} (f : (Fin (m + 1) → Bool) → F)
    (x : F) (xs : Fin m → F) :
    mle f (lsbCons x xs) =
      mle (fun b => f (lsbCons false b)) xs +
        x * (mle (fun b => f (lsbCons true b)) xs -
          mle (fun b => f (lsbCons false b)) xs) := by
  have hft : (false : Bool) ≠ true := by decide
  rw [mle]
  rw [← (lsbCubeEquiv m).symm.sum_comp
    (fun b => f b * chiEval b (lsbCons x xs))]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, lsbCubeEquiv_symm_apply,
    chiEval_lsbCons, if_true]
  rw [if_neg hft]
  simp only [mle]
  have htrue :
      (∑ b : Fin m → Bool,
        f (lsbCons true b) * (x * chiEval b xs)) =
        x * ∑ b : Fin m → Bool, f (lsbCons true b) * chiEval b xs := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hfalse :
      (∑ b : Fin m → Bool,
        f (lsbCons false b) * ((1 - x) * chiEval b xs)) =
        (1 - x) * ∑ b : Fin m → Bool,
          f (lsbCons false b) * chiEval b xs := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [htrue, hfalse]
  ring

/-! ## Recursive Boolean Möbius coefficients -/

/-- Raw-table restriction at a fixed LSB. -/
def tableLsb (head : Bool) {m : ℕ}
    (f : (Fin (m + 1) → Bool) → F) : (Fin m → Bool) → F :=
  fun tail => f (lsbCons head tail)

/-- **Boolean Möbius transform, packed LSB-first as a univariate
polynomial.**  At each level, even coefficients are the transform of the
`x₀=0` table and odd coefficients are the coefficientwise difference between
the `x₀=1` and `x₀=0` transforms.  This is the declarative counterpart of the
runtime's in-place Boolean Möbius transform. -/
noncomputable def booleanMobiusPolynomial :
    (m : ℕ) → ((Fin m → Bool) → F) → F[X]
  | 0, f => C (f fun i => Fin.elim0 i)
  | m + 1, f =>
      let p₀ := booleanMobiusPolynomial m (tableLsb false f)
      let p₁ := booleanMobiusPolynomial m (tableLsb true f)
      parityInterleave p₀ (p₁ - p₀)

/-- The Möbius transform has exactly the runtime's `2^m` coefficient window;
all coefficients at or beyond the padding boundary are zero. -/
theorem booleanMobiusPolynomial_coeff_eq_zero_of_two_pow_le (m : ℕ)
    (f : (Fin m → Bool) → F) {n : ℕ} (hn : 2 ^ m ≤ n) :
    (booleanMobiusPolynomial m f).coeff n = 0 := by
  induction m generalizing n with
  | zero =>
      have hn0 : n ≠ 0 := by omega
      simp [booleanMobiusPolynomial, coeff_C, hn0]
  | succ m ih =>
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
      · subst n
        rw [booleanMobiusPolynomial, coeff_parityInterleave_even]
        apply ih
        rw [pow_succ] at hn
        omega
      · subst n
        rw [booleanMobiusPolynomial, coeff_parityInterleave_odd, coeff_sub]
        have hkm : 2 ^ m ≤ k := by
          rw [pow_succ] at hn
          omega
        rw [ih _ hkm, ih _ hkm, sub_self]

/-- One runtime coefficient fold. -/
noncomputable def mleCoefficientFold (p : F[X]) (r : F) : F[X] :=
  evenPart p + C r * oddPart p

/-- A coefficient fold pairs adjacent LSB-first coefficients. -/
theorem coeff_mleCoefficientFold (p : F[X]) (r : F) (k : ℕ) :
    (mleCoefficientFold p r).coeff k =
      p.coeff (2 * k) + r * p.coeff (2 * k + 1) := by
  simp [mleCoefficientFold, coeff_evenPart_terminal,
    coeff_oddPart_terminal, coeff_C_mul]

@[simp] theorem mleCoefficientFold_parityInterleave
    (even odd : F[X]) (r : F) :
    mleCoefficientFold (parityInterleave even odd) r = even + C r * odd := by
  simp [mleCoefficientFold]

/-! ## Linearity of the terminal fold stack -/

theorem evenPart_add_terminal (p q : F[X]) :
    evenPart (p + q) = evenPart p + evenPart q := by
  ext k
  simp only [coeff_evenPart_terminal, coeff_add]

theorem oddPart_add_terminal (p q : F[X]) :
    oddPart (p + q) = oddPart p + oddPart q := by
  ext k
  simp only [coeff_oddPart_terminal, coeff_add]

theorem evenPart_sub_terminal (p q : F[X]) :
    evenPart (p - q) = evenPart p - evenPart q := by
  ext k
  simp only [coeff_evenPart_terminal, coeff_sub]

theorem oddPart_sub_terminal (p q : F[X]) :
    oddPart (p - q) = oddPart p - oddPart q := by
  ext k
  simp only [coeff_oddPart_terminal, coeff_sub]

theorem evenPart_C_mul_terminal (a : F) (p : F[X]) :
    evenPart (C a * p) = C a * evenPart p := by
  ext k
  simp only [coeff_evenPart_terminal, coeff_C_mul]

theorem oddPart_C_mul_terminal (a : F) (p : F[X]) :
    oddPart (C a * p) = C a * oddPart p := by
  ext k
  simp only [coeff_oddPart_terminal, coeff_C_mul]

theorem mleCoefficientFold_add (p q : F[X]) (r : F) :
    mleCoefficientFold (p + q) r =
      mleCoefficientFold p r + mleCoefficientFold q r := by
  simp only [mleCoefficientFold, evenPart_add_terminal, oddPart_add_terminal]
  ring

theorem mleCoefficientFold_sub (p q : F[X]) (r : F) :
    mleCoefficientFold (p - q) r =
      mleCoefficientFold p r - mleCoefficientFold q r := by
  simp only [mleCoefficientFold, evenPart_sub_terminal, oddPart_sub_terminal]
  ring

theorem mleCoefficientFold_C_mul (a : F) (p : F[X]) (r : F) :
    mleCoefficientFold (C a * p) r = C a * mleCoefficientFold p r := by
  simp only [mleCoefficientFold, evenPart_C_mul_terminal,
    oddPart_C_mul_terminal]
  ring

/-- Fold variables in LSB-first order, retaining the resulting polynomial. -/
noncomputable def foldMleVariables :
    (m : ℕ) → F[X] → (Fin m → F) → F[X]
  | 0, p, _ => p
  | m + 1, p, r =>
      foldMleVariables m (mleCoefficientFold p (r 0))
        (fun i => r i.succ)

theorem foldMleVariables_add (m : ℕ) (p q : F[X]) (r : Fin m → F) :
    foldMleVariables m (p + q) r =
      foldMleVariables m p r + foldMleVariables m q r := by
  induction m generalizing p q with
  | zero => rfl
  | succ m ih =>
      rw [foldMleVariables, mleCoefficientFold_add, ih]
      rfl

theorem foldMleVariables_sub (m : ℕ) (p q : F[X]) (r : Fin m → F) :
    foldMleVariables m (p - q) r =
      foldMleVariables m p r - foldMleVariables m q r := by
  induction m generalizing p q with
  | zero => rfl
  | succ m ih =>
      rw [foldMleVariables, mleCoefficientFold_sub, ih]
      rfl

theorem foldMleVariables_C_mul (m : ℕ) (a : F) (p : F[X])
    (r : Fin m → F) :
    foldMleVariables m (C a * p) r = C a * foldMleVariables m p r := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
      rw [foldMleVariables, mleCoefficientFold_C_mul, ih]
      rfl

/-! ## The terminal theorem -/

/-- **MLE-to-multiplicative-FRI terminal algebra.**  Starting from the raw
Boolean table, recursively perform its Boolean Möbius transform, pack the
monomial coefficients LSB-first (all higher polynomial coefficients are zero),
and apply `evenPart p + C (r i) * oddPart p` in LSB-first coordinate order.
After all `m` variables, the remaining polynomial is the constant whose value
is exactly the multilinear extension of the ORIGINAL raw table at `r`. -/
theorem foldMleVariables_booleanMobiusPolynomial (m : ℕ)
    (f : (Fin m → Bool) → F) (r : Fin m → F) :
    foldMleVariables m (booleanMobiusPolynomial m f) r = C (mle f r) := by
  induction m with
  | zero =>
      have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
        funext b
        congr 1
        funext i
        exact Fin.elim0 i
      have hr : r = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      rw [hf, hr]
      simp [foldMleVariables, booleanMobiusPolynomial, mle, chiEval]
  | succ m ih =>
      let f₀ : (Fin m → Bool) → F := tableLsb false f
      let f₁ : (Fin m → Bool) → F := tableLsb true f
      let p₀ : F[X] := booleanMobiusPolynomial m f₀
      let p₁ : F[X] := booleanMobiusPolynomial m f₁
      let rt : Fin m → F := fun i => r i.succ
      have hr : r = lsbCons (r 0) rt := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [rt]
      change foldMleVariables m
          (mleCoefficientFold (parityInterleave p₀ (p₁ - p₀)) (r 0)) rt =
        C (mle f r)
      rw [mleCoefficientFold_parityInterleave, foldMleVariables_add,
        foldMleVariables_C_mul, foldMleVariables_sub,
        ih f₀ rt, ih f₁ rt, hr, mle_lsb_recurrence]
      simp only [f₀, f₁, lsbCons_zero, map_add, map_sub, map_mul]
      unfold tableLsb
      ring

/-- Scalar rendering used by the terminal check: the constant coefficient is
the MLE value. -/
theorem coeff_zero_foldMleVariables_booleanMobiusPolynomial (m : ℕ)
    (f : (Fin m → Bool) → F) (r : Fin m → F) :
    (foldMleVariables m (booleanMobiusPolynomial m f) r).coeff 0 = mle f r := by
  rw [foldMleVariables_booleanMobiusPolynomial]
  simp

/-! ## F₅ two-variable tooth -/

namespace MultiplicativeMleTerminalExample

/-- LSB-first raw table `[1,2,3,4]`: `b₀` selects adjacent entries. -/
def rawTable : (Fin 2 → Bool) → ZMod 5 := fun b =>
  if b 0 then (if b 1 then 4 else 2) else (if b 1 then 3 else 1)

/-- The tempting but wrong polynomial obtained by treating raw table values as
monomial coefficients. -/
noncomputable def rawValuesAsCoefficients : Polynomial (ZMod 5) :=
  C 1 + C 2 * X + C 3 * X ^ 2 + C 4 * X ^ 3

/-- **FIRES:** after Möbius conversion, the two runtime folds at `(2,3)` end
at the correct MLE value `4`. -/
theorem mobius_terminal_f5 :
    (foldMleVariables 2 (booleanMobiusPolynomial 2 rawTable)
      ![2, 3]).coeff 0 = 4 := by
  rw [coeff_zero_foldMleVariables_booleanMobiusPolynomial]
  decide

/-- **TEETH:** skipping Möbius conversion and feeding the raw values as
coefficients ends at `3`, not the correct terminal `4`. -/
theorem raw_values_are_not_coefficients_f5 :
    (foldMleVariables 2 rawValuesAsCoefficients ![2, 3]).coeff 0 = 3 := by
  change (mleCoefficientFold
    (mleCoefficientFold rawValuesAsCoefficients 2) 3).coeff 0 = 3
  rw [coeff_mleCoefficientFold, coeff_mleCoefficientFold,
    coeff_mleCoefficientFold]
  norm_num [rawValuesAsCoefficients, Polynomial.coeff_one]
  decide

theorem raw_values_terminal_differs_f5 :
    (foldMleVariables 2 rawValuesAsCoefficients ![2, 3]).coeff 0 ≠
      (foldMleVariables 2 (booleanMobiusPolynomial 2 rawTable)
        ![2, 3]).coeff 0 := by
  rw [raw_values_are_not_coefficients_f5, mobius_terminal_f5]
  decide

end MultiplicativeMleTerminalExample

/-- info: 'Minidregg.Selvage.foldMleVariables_booleanMobiusPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldMleVariables_booleanMobiusPolynomial
/-- info: 'Minidregg.Selvage.MultiplicativeMleTerminalExample.raw_values_terminal_differs_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MultiplicativeMleTerminalExample.raw_values_terminal_differs_f5

end Minidregg.Selvage
