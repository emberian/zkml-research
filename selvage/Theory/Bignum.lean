/-
# Theory.Bignum — canonical fixed-width little-endian numerals.

Wide digests, challenges, counters, and later circuit gadgets need one positional
algebra rather than bespoke pack/unpack code at every boundary.  This file owns
that algebra at the candidate-independent `Theory` layer:

* `denoteNat` and `denoteInt` interpret little-endian limbs;
* `Ranged` and `Canonical` state the per-limb and fixed-width obligations;
* `digitsLE` is the value-to-limbs direction, padded to an exact width;
* recomposition and extraction are mutual inverses below `base ^ width`;
* ranged fixed-width limbs have an injective denotation;
* `Limbs base width` packages the canonical carrier, with a proved codec to and
  from `Fin (base ^ width)`.

This is integer/natural-number representation theory.  It does not claim that
casting a packed value into a smaller field is injective, and it emits no
circuit constraints.  Those realization obligations belong above `Theory`.
-/
import Mathlib.Tactic

namespace Minidregg.Theory.Bignum

set_option autoImplicit false

/-! ## Denotation and canonicity -/

/-- A genuine positional radix has at least the digits `0` and `1`. -/
def ValidRadix (base : Nat) : Prop := 1 < base

theorem ValidRadix.pos {base : Nat} (hbase : ValidRadix base) : 0 < base := by
  unfold ValidRadix at hbase
  omega

/-- Natural-number denotation of little-endian limbs:
`[d₀, d₁, ...]` denotes `d₀ + base*d₁ + ...`. -/
def denoteNat (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + base * denoteNat base ds

/-- Integer denotation of the same natural limbs, without field reduction. -/
def denoteInt (base : Nat) : List Nat → Int
  | [] => 0
  | d :: ds => (d : Int) + (base : Int) * denoteInt base ds

/-- Every limb is a canonical digit in `[0, base)`. -/
def Ranged (base : Nat) (limbs : List Nat) : Prop :=
  ∀ digit ∈ limbs, digit < base

/-- A canonical fixed-width representation is ranged and has exactly `width` limbs. -/
def Canonical (base width : Nat) (limbs : List Nat) : Prop :=
  Ranged base limbs ∧ limbs.length = width

instance (base : Nat) (limbs : List Nat) : Decidable (Ranged base limbs) := by
  unfold Ranged
  infer_instance

instance (base width : Nat) (limbs : List Nat) : Decidable (Canonical base width limbs) := by
  unfold Canonical
  infer_instance

@[simp] theorem denoteNat_nil (base : Nat) : denoteNat base [] = 0 := rfl

@[simp] theorem denoteNat_cons (base digit : Nat) (limbs : List Nat) :
    denoteNat base (digit :: limbs) = digit + base * denoteNat base limbs := rfl

@[simp] theorem denoteInt_nil (base : Nat) : denoteInt base [] = 0 := rfl

@[simp] theorem denoteInt_cons (base digit : Nat) (limbs : List Nat) :
    denoteInt base (digit :: limbs) =
      (digit : Int) + (base : Int) * denoteInt base limbs := rfl

/-- The natural and integer interpretations are exactly the same integer. -/
theorem denoteInt_eq_natCast (base : Nat) (limbs : List Nat) :
    denoteInt base limbs = (denoteNat base limbs : Int) := by
  induction limbs with
  | nil => simp
  | cons digit limbs ih =>
      rw [denoteInt_cons, ih, denoteNat_cons]
      norm_cast

/-- Concatenating higher limbs shifts their denotation by the lower width. -/
theorem denoteNat_append (base : Nat) (low high : List Nat) :
    denoteNat base (low ++ high) =
      denoteNat base low + base ^ low.length * denoteNat base high := by
  induction low with
  | nil => simp
  | cons digit limbs ih =>
      simp only [List.cons_append, denoteNat_cons, ih, List.length_cons, pow_succ]
      ring

/-- A ranged limb vector fits below the capacity of its width. -/
theorem denoteNat_lt_pow {base : Nat} (_hbase : 0 < base) :
    ∀ limbs : List Nat, Ranged base limbs → denoteNat base limbs < base ^ limbs.length := by
  intro limbs
  induction limbs with
  | nil => intro _; simp
  | cons digit limbs ih =>
      intro hranged
      have hdigit : digit < base := hranged digit List.mem_cons_self
      have htail : Ranged base limbs :=
        fun d hd => hranged d (List.mem_cons_of_mem digit hd)
      have ih' := ih htail
      have hsucc : denoteNat base limbs + 1 ≤ base ^ limbs.length := ih'
      calc
        denoteNat base (digit :: limbs)
            = digit + base * denoteNat base limbs := rfl
        _ < base + base * denoteNat base limbs := Nat.add_lt_add_right hdigit _
        _ = base * (denoteNat base limbs + 1) := by ring
        _ ≤ base * base ^ limbs.length := Nat.mul_le_mul_left base hsucc
        _ = base ^ (digit :: limbs).length := by simp [pow_succ, Nat.mul_comm]

/-- The integer denotation of natural limbs is nonnegative. -/
theorem denoteInt_nonneg (base : Nat) (limbs : List Nat) :
    0 ≤ denoteInt base limbs := by
  rw [denoteInt_eq_natCast]
  exact Int.natCast_nonneg _

/-- The integer denotation obeys the same fixed-width capacity bound. -/
theorem denoteInt_lt_pow {base : Nat} (hbase : 0 < base)
    (limbs : List Nat) (hranged : Ranged base limbs) :
    denoteInt base limbs < (base : Int) ^ limbs.length := by
  rw [denoteInt_eq_natCast]
  exact_mod_cast denoteNat_lt_pow hbase limbs hranged

/-! ## The value-to-limbs codec -/

/-- The first `width` base-`base` digits of `value`, least significant first. -/
def digitsLE (base : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | width + 1, value => value % base :: digitsLE base width (value / base)

@[simp] theorem digitsLE_length (base width value : Nat) :
    (digitsLE base width value).length = width := by
  induction width generalizing value with
  | zero => simp [digitsLE]
  | succ width ih => simp [digitsLE, ih]

/-- Digit extraction always produces ranged limbs. -/
theorem digitsLE_ranged {base : Nat} (hbase : 0 < base) :
    ∀ (width value : Nat), Ranged base (digitsLE base width value) := by
  intro width
  induction width with
  | zero => intro value digit hdigit; simp [digitsLE] at hdigit
  | succ width ih =>
      intro value digit hdigit
      simp only [digitsLE, List.mem_cons] at hdigit
      rcases hdigit with h | h
      · subst digit
        exact Nat.mod_lt value hbase
      · exact ih (value / base) digit h

/-- A fixed-width extraction is canonical. -/
theorem digitsLE_canonical {base : Nat} (hbase : 0 < base) (width value : Nat) :
    Canonical base width (digitsLE base width value) :=
  ⟨digitsLE_ranged hbase width value, digitsLE_length base width value⟩

/-- Recomposition: `width` limbs recover every value below `base ^ width`. -/
theorem denoteNat_digitsLE {base : Nat} (hbase : 0 < base) :
    ∀ (width value : Nat), value < base ^ width →
      denoteNat base (digitsLE base width value) = value := by
  intro width
  induction width with
  | zero =>
      intro value hvalue
      simp only [pow_zero] at hvalue
      have : value = 0 := by omega
      subst value
      rfl
  | succ width ih =>
      intro value hvalue
      have hdiv : value / base < base ^ width := by
        rw [Nat.div_lt_iff_lt_mul hbase]
        calc
          value < base ^ (width + 1) := hvalue
          _ = base ^ width * base := by rw [pow_succ]
      simp only [digitsLE, denoteNat_cons, ih (value / base) hdiv]
      exact Nat.mod_add_div value base

/-- Integer recomposition is the cast of the exact natural-number codec theorem. -/
theorem denoteInt_digitsLE {base : Nat} (hbase : 0 < base)
    (width value : Nat) (hvalue : value < base ^ width) :
    denoteInt base (digitsLE base width value) = (value : Int) := by
  rw [denoteInt_eq_natCast, denoteNat_digitsLE hbase width value hvalue]

/-- Extraction: re-encoding a ranged limb list recovers that exact list. -/
theorem digitsLE_denoteNat {base : Nat} (hbase : 0 < base) :
    ∀ limbs : List Nat, Ranged base limbs →
      digitsLE base limbs.length (denoteNat base limbs) = limbs := by
  intro limbs
  induction limbs with
  | nil => intro _; simp [digitsLE]
  | cons digit limbs ih =>
      intro hranged
      have hdigit : digit < base := hranged digit List.mem_cons_self
      have htail : Ranged base limbs :=
        fun d hd => hranged d (List.mem_cons_of_mem digit hd)
      have hmod : (digit + base * denoteNat base limbs) % base = digit := by
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hdigit
      have hdiv : (digit + base * denoteNat base limbs) / base = denoteNat base limbs := by
        rw [Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hdigit, Nat.zero_add]
      simp only [denoteNat_cons, digitsLE, hmod, hdiv, ih htail]

/-! ## Uniqueness and the canonical carrier -/

/-- Ranged equal-width little-endian representations have injective denotation. -/
theorem denoteNat_injective {base : Nat} (hbase : 0 < base)
    {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hrx : Ranged base xs) (hry : Ranged base ys)
    (hvalue : denoteNat base xs = denoteNat base ys) : xs = ys := by
  calc
    xs = digitsLE base xs.length (denoteNat base xs) :=
      (digitsLE_denoteNat hbase xs hrx).symm
    _ = digitsLE base ys.length (denoteNat base ys) := by rw [hlen, hvalue]
    _ = ys := digitsLE_denoteNat hbase ys hry

/-- The unreduced integer denotation is injective under the same obligations. -/
theorem denoteInt_injective {base : Nat} (hbase : 0 < base)
    {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hrx : Ranged base xs) (hry : Ranged base ys)
    (hvalue : denoteInt base xs = denoteInt base ys) : xs = ys := by
  apply denoteNat_injective hbase hlen hrx hry
  rw [denoteInt_eq_natCast, denoteInt_eq_natCast] at hvalue
  exact_mod_cast hvalue

/-- Fixed-width canonical representations are determined by their denotation. -/
theorem canonical_eq_of_denoteNat_eq {base width : Nat} (hbase : 0 < base)
    {xs ys : List Nat} (hx : Canonical base width xs) (hy : Canonical base width ys)
    (hvalue : denoteNat base xs = denoteNat base ys) : xs = ys :=
  denoteNat_injective hbase (hx.2.trans hy.2.symm) hx.1 hy.1 hvalue

/-- The zero value has only zero natural limbs (positivity of the radix is load-bearing). -/
theorem denoteNat_eq_zero_iff {base : Nat} (hbase : 0 < base) :
    ∀ limbs : List Nat, denoteNat base limbs = 0 ↔ ∀ digit ∈ limbs, digit = 0 := by
  intro limbs
  induction limbs with
  | nil => simp
  | cons digit limbs ih =>
      constructor
      · intro hvalue d hd
        have hparts : digit = 0 ∧ base * denoteNat base limbs = 0 :=
          Nat.add_eq_zero_iff.mp hvalue
        have htail : denoteNat base limbs = 0 :=
          (Nat.mul_eq_zero.mp hparts.2).resolve_left (Nat.ne_of_gt hbase)
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hparts.1
        · exact (ih.mp htail) d hd
      · intro hall
        have hdigit : digit = 0 := hall digit List.mem_cons_self
        have htail : ∀ d ∈ limbs, d = 0 :=
          fun d hd => hall d (List.mem_cons_of_mem digit hd)
        simp [hdigit, ih.mpr htail]

/-- Canonical fixed-width limbs as a reusable data carrier. -/
def Limbs (base width : Nat) := { limbs : List Nat // Canonical base width limbs }

namespace Limbs

/-- The underlying little-endian digit list. -/
def toList {base width : Nat} (x : Limbs base width) : List Nat := x.1

/-- Natural-number denotation of canonical fixed-width limbs. -/
def toNat {base width : Nat} (x : Limbs base width) : Nat := denoteNat base x.1

/-- Integer denotation of canonical fixed-width limbs. -/
def toInt {base width : Nat} (x : Limbs base width) : Int := denoteInt base x.1

@[simp] theorem toInt_eq_toNat {base width : Nat} (x : Limbs base width) :
    x.toInt = (x.toNat : Int) := denoteInt_eq_natCast base x.1

/-- Canonical limbs fit in the exact fixed-width capacity. -/
theorem toNat_lt_pow {base width : Nat} (hbase : 0 < base) (x : Limbs base width) :
    x.toNat < base ^ width := by
  simpa [toNat, x.2.2] using denoteNat_lt_pow hbase x.1 x.2.1

/-- Decode a canonical limb vector as its bounded natural number. -/
def toFin {base width : Nat} (hbase : 0 < base) (x : Limbs base width) :
    Fin (base ^ width) :=
  ⟨x.toNat, x.toNat_lt_pow hbase⟩

/-- Encode a bounded natural number as exactly `width` little-endian limbs. -/
def ofFin {base width : Nat} (hbase : 0 < base) (value : Fin (base ^ width)) :
    Limbs base width :=
  ⟨digitsLE base width value.1, digitsLE_canonical hbase width value.1⟩

/-- Decoding after encoding returns the original bounded natural number. -/
theorem toFin_ofFin {base width : Nat} (hbase : 0 < base)
    (value : Fin (base ^ width)) : toFin hbase (ofFin hbase value) = value := by
  apply Fin.ext
  exact denoteNat_digitsLE hbase width value.1 value.2

/-- Encoding after decoding returns the exact canonical limb vector. -/
theorem ofFin_toFin {base width : Nat} (hbase : 0 < base)
    (x : Limbs base width) : ofFin hbase (toFin hbase x) = x := by
  apply Subtype.ext
  simpa [ofFin, toFin, toNat, x.2.2] using digitsLE_denoteNat hbase x.1 x.2.1

/-- Canonical `width`-limb numerals are exactly the naturals below `base ^ width`. -/
def equivFin {base width : Nat} (hbase : 0 < base) :
    Limbs base width ≃ Fin (base ^ width) where
  toFun := toFin hbase
  invFun := ofFin hbase
  left_inv := ofFin_toFin hbase
  right_inv := toFin_ofFin hbase

/-- Encode a value from any logical range that fits inside the limb capacity.
This is the useful shape for, e.g., a `2^bits` digest range inside `base^width`. -/
def ofBounded {base width bound : Nat} (hbase : 0 < base)
    (hbound : bound ≤ base ^ width) (value : Fin bound) : Limbs base width :=
  ofFin hbase (Fin.castLE hbound value)

/-- `ofBounded` preserves the logical value exactly; the unused capacity causes no reduction. -/
theorem toNat_ofBounded {base width bound : Nat} (hbase : 0 < base)
    (hbound : bound ≤ base ^ width) (value : Fin bound) :
    (ofBounded hbase hbound value).toNat = value.1 := by
  exact denoteNat_digitsLE hbase width value.1 (lt_of_lt_of_le value.2 hbound)

/-- Canonical fixed-width denotation is injective. -/
theorem toNat_injective {base width : Nat} (hbase : 0 < base) :
    Function.Injective (@toNat base width) := by
  intro x y hvalue
  apply Subtype.ext
  exact canonical_eq_of_denoteNat_eq hbase x.2 y.2 hvalue

end Limbs

/-! ## Computed teeth -/

-- Little-endian direction: `3 + 10*2 + 10^2*1 = 123`.
#guard decide (denoteNat 10 [3, 2, 1] = 123)

-- Four bytes recover a concrete 32-bit word, least significant byte first.
#guard decide (digitsLE 256 4 305419896 = [120, 86, 52, 18])
#guard decide (denoteNat 256 [120, 86, 52, 18] = 305419896)

-- Range checks are load-bearing: without them positional notation aliases.
example : denoteNat 16 [16, 0] = denoteNat 16 [0, 1] ∧
    ([16, 0] : List Nat) ≠ [0, 1] := by decide

-- Eight limbs of this 31-bit prime do not cover 248 bits; nine do.
theorem eight_radix_2013265921_limbs_lt_248_bits :
    (2013265921 : Nat) ^ 8 < 2 ^ 248 := by norm_num

theorem bits_248_fit_nine_radix_2013265921_limbs :
    (2 : Nat) ^ 248 ≤ 2013265921 ^ 9 := by norm_num

-- Consequently every 248-bit value has a lossless canonical nine-limb encoding.
example (value : Fin ((2 : Nat) ^ 248)) :
    (Limbs.ofBounded (by norm_num : 0 < (2013265921 : Nat))
      bits_248_fit_nine_radix_2013265921_limbs value).toNat = value.1 :=
  Limbs.toNat_ofBounded _ _ _

#print axioms denoteInt_eq_natCast
#print axioms denoteNat_lt_pow
#print axioms denoteNat_digitsLE
#print axioms denoteInt_digitsLE
#print axioms digitsLE_denoteNat
#print axioms denoteNat_injective
#print axioms denoteInt_injective
#print axioms Limbs.toFin_ofFin
#print axioms Limbs.ofFin_toFin
#print axioms Limbs.toNat_ofBounded
#print axioms bits_248_fit_nine_radix_2013265921_limbs

end Minidregg.Theory.Bignum
