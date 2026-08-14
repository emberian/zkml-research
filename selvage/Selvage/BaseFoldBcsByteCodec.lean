/-
# Selvage.BaseFoldBcsByteCodec — canonical BabyBear rate-block bytes

The `.pad1` BaseFold profile is already injective at the semantic rate-block
layer.  This module pins the next deployment boundary: every BabyBear value is
four canonical little-endian bytes, and every 8-lane Poseidon2 rate block is
the lane-major concatenation of those words.

Decoding is strict.  A field word must contain exactly four bytes and denote a
natural below the BabyBear modulus; a rate block must decode exactly eight
words and leave no trailing bytes.  The resulting `LawfulCodec Rate` proves
round-trip and hence byte injectivity.  It does not identify a handwritten
native implementation with this Lean decoder, and it does not discharge the
deployed-permutation assumption.
-/

import Selvage.BaseFoldBcsPadding
import Theory.Bignum
import Theory.IndexedProgram

namespace Minidregg.Selvage.BaseFoldBcsByteCodec

open BabyBearExt4
open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsPadding
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

noncomputable section

/-! ## Four canonical little-endian bytes per BabyBear value -/

def byteOfDigit (digit : {value : Nat // value < 256}) : UInt8 :=
  UInt8.ofNatLT digit.1 (by simpa [UInt8.size] using digit.2)

def bytesOfDigits (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 256) : List UInt8 :=
  digits.attach.map fun digit =>
    byteOfDigit ⟨digit.1, ranged digit.1 digit.2⟩

@[simp] theorem bytesOfDigits_length (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 256) :
    (bytesOfDigits digits ranged).length = digits.length := by
  simp [bytesOfDigits]

@[simp] theorem bytesOfDigits_toNats (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 256) :
    (bytesOfDigits digits ranged).map UInt8.toNat = digits := by
  simp [bytesOfDigits, byteOfDigit]

/-- Exactly four little-endian base-256 digits.  Values at or above `2^32`
are truncated by this helper; every use below proves its input fits first. -/
def encodeNatLE4 (value : Nat) : List UInt8 :=
  bytesOfDigits (Bignum.digitsLE 256 4 value)
    (Bignum.digitsLE_ranged (by norm_num) 4 value)

@[simp] theorem encodeNatLE4_length (value : Nat) :
    (encodeNatLE4 value).length = 4 := by
  simp [encodeNatLE4, Bignum.digitsLE_length]

@[simp] theorem encodeNatLE4_toNats (value : Nat) :
    (encodeNatLE4 value).map UInt8.toNat =
      Bignum.digitsLE 256 4 value := by
  simp [encodeNatLE4]

def encodeField (value : F) : List UInt8 :=
  encodeNatLE4 value.val

def decodeField (bytes : List UInt8) : Option F :=
  if bytes.length = 4 then
    let value := Bignum.denoteNat 256 (bytes.map UInt8.toNat)
    if value < modulus then some (value : F) else none
  else none

@[simp] theorem encodeField_length (value : F) :
    (encodeField value).length = 4 := by
  simp [encodeField]

@[simp] theorem decodeField_encodeField (value : F) :
    decodeField (encodeField value) = some value := by
  have fits : value.val < 256 ^ 4 :=
    lt_trans (ZMod.val_lt value) (by norm_num [modulus])
  have denoted :
      Bignum.denoteNat 256 (Bignum.digitsLE 256 4 value.val) = value.val :=
    Bignum.denoteNat_digitsLE (by norm_num) 4 value.val fits
  have canonical : value.val < modulus := ZMod.val_lt value
  simp [decodeField, encodeField, denoted, canonical]

theorem decodeField_wrong_length (bytes : List UInt8)
    (wrong : bytes.length ≠ 4) :
    decodeField bytes = none := by
  simp [decodeField, wrong]

/-- The first noncanonical 32-bit word is rejected rather than reduced modulo
the field. -/
theorem decodeField_modulus_rejected :
    decodeField (encodeNatLE4 modulus) = none := by
  have fits : modulus < 256 ^ 4 := by norm_num [modulus]
  have denoted :
      Bignum.denoteNat 256 (Bignum.digitsLE 256 4 modulus) = modulus :=
    Bignum.denoteNat_digitsLE (by norm_num) 4 modulus fits
  simp [decodeField, denoted]

def fieldCodec : LawfulCodec F where
  encode := encodeField
  decode := decodeField
  decode_encode := decodeField_encodeField

/-! ## A strict parser for fixed numbers of field words -/

def encodeFields : List F → List UInt8
  | [] => []
  | value :: values => encodeField value ++ encodeFields values

def decodeFields : Nat → List UInt8 → Option (List F × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let value ← decodeField (bytes.take 4)
      let (values, rest) ← decodeFields count (bytes.drop 4)
      pure (value :: values, rest)

@[simp] theorem encodeFields_length (values : List F) :
    (encodeFields values).length = 4 * values.length := by
  induction values with
  | nil => simp [encodeFields]
  | cons value values ih =>
      simp [encodeFields, ih, Nat.mul_succ, Nat.add_comm]

/-- Parsing an encoded list consumes exactly that list and exposes the caller's
suffix unchanged.  This is the framing law used by the rate decoder. -/
theorem decodeFields_encodeFields_append (values : List F)
    (suffix : List UInt8) :
    decodeFields values.length (encodeFields values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => simp [encodeFields, decodeFields]
  | cons value values ih =>
      simp [encodeFields, decodeFields, encodeField_length,
        decodeField_encodeField, ih]

/-! ## Exact 8-lane rate blocks -/

def listToRate? (values : List F) : Option Rate :=
  if exact : values.length = 8 then
    some fun lane => values.get (Fin.cast exact.symm lane)
  else none

@[simp] theorem listToRate_ofFn (block : Rate) :
    listToRate? (List.ofFn block) = some block := by
  simp only [listToRate?, List.length_ofFn, ↓reduceDIte]
  apply congrArg some
  funext lane
  change (List.ofFn block).get lane = block lane
  exact List.get_ofFn block lane

/-- Lane-major bytes: lane zero first, four little-endian bytes per lane. -/
def encodeRate (block : Rate) : List UInt8 :=
  encodeFields (List.ofFn block)

def decodeRate (bytes : List UInt8) : Option Rate :=
  match decodeFields 8 bytes with
  | some (values, []) => listToRate? values
  | _ => none

@[simp] theorem encodeRate_length (block : Rate) :
    (encodeRate block).length = 32 := by
  simp [encodeRate]

@[simp] theorem decodeRate_encodeRate (block : Rate) :
    decodeRate (encodeRate block) = some block := by
  have parsed :
      decodeFields 8 (encodeFields (List.ofFn block)) =
        some (List.ofFn block, []) := by
    simpa using decodeFields_encodeFields_append (List.ofFn block) []
  rw [decodeRate, encodeRate, parsed]
  exact listToRate_ofFn block

theorem encodeRate_injective : Function.Injective encodeRate := by
  intro left right equal
  have decoded := congrArg decodeRate equal
  simpa using decoded

theorem decodeRate_trailing_rejected (block : Rate)
    (suffix : List UInt8) (nonempty : suffix ≠ []) :
    decodeRate (encodeRate block ++ suffix) = none := by
  have parsed :
      decodeFields 8 (encodeFields (List.ofFn block) ++ suffix) =
        some (List.ofFn block, suffix) := by
    simpa using decodeFields_encodeFields_append (List.ofFn block) suffix
  rw [decodeRate, encodeRate, parsed]
  cases suffix with
  | nil => contradiction
  | cons byte suffix => rfl

def rateCodec : LawfulCodec Rate where
  encode := encodeRate
  decode := decodeRate
  decode_encode := decodeRate_encodeRate

/-! ## The padded profile's exact byte count -/

def encodePaddedMessage (message : List Rate) : List UInt8 :=
  (padMessage message).flatMap encodeRate

@[simp] theorem encodePaddedMessage_length (message : List Rate) :
    (encodePaddedMessage message).length = 32 * (message.length + 1) := by
  rw [encodePaddedMessage, List.length_flatMap]
  simp only [encodeRate_length, List.map_const', List.sum_replicate,
    padMessage_length]
  simp [nsmul_eq_mul, Nat.mul_comm]

#check @decodeField_encodeField
#check @decodeField_modulus_rejected
#check @decodeFields_encodeFields_append
#check @decodeRate_encodeRate
#check @encodeRate_injective
#check @encodePaddedMessage_length

/-- info: 'Minidregg.Selvage.BaseFoldBcsByteCodec.decodeField_encodeField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeField_encodeField
/-- info: 'Minidregg.Selvage.BaseFoldBcsByteCodec.decodeRate_encodeRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeRate_encodeRate
/-- info: 'Minidregg.Selvage.BaseFoldBcsByteCodec.encodePaddedMessage_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodePaddedMessage_length

end

end Minidregg.Selvage.BaseFoldBcsByteCodec
