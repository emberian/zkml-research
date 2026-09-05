/-
# Selvage.BaseFoldBcsReceiptCodec — bind Ext4, root, path, and whole-receipt
# bytes to the proved field/Merkle semantics and to acceptance

`BaseFoldBcsByteCodec` fixed the deployment boundary for one BabyBear word
(four canonical little-endian bytes, strict) and one 8-lane rate block
(lane-major, strict, lawful).  The BCS verifier `Accepts`, however, consumes
a whole `Receipt`: round roots and sumcheck coefficients, challenges, the
terminal root, query seeds, and per-fibre openings with three
variable-length Merkle paths.  This module gives every one of those a codec
built ONLY from the landed word/rate codecs plus a length prefix, and binds
the bytes to acceptance:

* `FramedCodec` — an encoder/parser pair with the framing law
  `parse (encode a ++ suffix) = some (a, suffix)`; products, retractions,
  fixed-count vectors, and a strict whole-input `decode` follow, and every
  `FramedCodec` is a `LawfulCodec`.
* Ext4: the four power-basis coefficients (`coefficients4`, the proved
  quartic carrier), decoded back through `coefficients.symm`.  Bound to the
  field semantics: the Ext4 bytes are literally the head of the proved rate
  codec at the leaf block (`encodeRate_extBlock`), and decoding them is
  `rateChallenge` of that block (`ext4_decode_eq_rateChallenge`).
* Root: `Digest` IS a rate block; the root codec's strict decoder is the
  landed `decodeRate` (`digestFramed_decode_eq_decodeRate`).
* Path: a base-128 varint length prefix followed by the digests.  Bound to
  the Merkle semantics: path bytes verify under `openingScheme hashSuite k`
  exactly when the path does (`merkle_path_bytes_verify_iff`), and an extra
  sibling is refused by `recompute`'s fail-closed length check
  (`merkle_path_extra_sibling_refused`).
* Opening, round message, statement, receipt: products and vectors of the
  above; `receiptCodec m queryCount : LawfulCodec (Receipt m queryCount)`.
* **`bcs_accept_bytes_iff`**: the BCS accept predicate evaluated on the bytes
  (`AcceptsBytes`, fail-closed on undecodable bytes) holds for
  `encode receipt` exactly when `Accepts` holds for `receipt`.
  Falsifiers: a trailing byte is refused (`acceptsBytes_trailing_refused`),
  and a terminal-root tamper — different bytes, same shape — is refused by
  `RootsExact` whenever the original was accepted
  (`acceptsBytes_terminalRoot_tamper_refused`).

Not claimed: that a native implementation realizes these decoders; that the
byte layout is the production wire format; anything about hash security.
Those remain the `[NATIVE-refinement]` and `[POSEIDON2-perm-ideal]`
obligations named elsewhere.
-/

import Selvage.BaseFoldBcsByteCodec

namespace Minidregg.Selvage.BaseFoldBcsReceiptCodec

open BabyBearExt4
open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsByteCodec
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

noncomputable section

/-! ## Framed codecs -/

/-- A framed parser consumes a prefix of its input and returns the rest. -/
abbrev Parser (α : Type) := List UInt8 → Option (α × List UInt8)

/-- An encoder/parser pair with the framing law.  Framing is what lets codecs
compose sequentially without delimiters. -/
structure FramedCodec (α : Type) where
  encode : α → List UInt8
  parse : Parser α
  parse_encode_append : ∀ (value : α) (suffix : List UInt8),
    parse (encode value ++ suffix) = some (value, suffix)

namespace FramedCodec

variable {α β : Type}

/-- Strict whole-input decoding: any leftover suffix is a framing error. -/
def decode (codec : FramedCodec α) (bytes : List UInt8) : Option α :=
  match codec.parse bytes with
  | some (value, []) => some value
  | _ => none

theorem decode_encode (codec : FramedCodec α) (value : α) :
    codec.decode (codec.encode value) = some value := by
  have h := codec.parse_encode_append value []
  rw [List.append_nil] at h
  unfold decode
  rw [h]

theorem decode_encode_append_refused (codec : FramedCodec α) (value : α)
    (suffix : List UInt8) (hsuffix : suffix ≠ []) :
    codec.decode (codec.encode value ++ suffix) = none := by
  unfold decode
  rw [codec.parse_encode_append value suffix]
  cases suffix with
  | nil => exact absurd rfl hsuffix
  | cons _ _ => rfl

theorem encode_injective (codec : FramedCodec α) :
    Function.Injective codec.encode := by
  intro left right equal
  have h := congrArg codec.decode equal
  rw [decode_encode, decode_encode] at h
  exact Option.some.inj h

/-- Every framed codec is a lawful whole-input codec. -/
def toLawful (codec : FramedCodec α) : LawfulCodec α where
  encode := codec.encode
  decode := codec.decode
  decode_encode := codec.decode_encode

/-- Sequential product. -/
def prod (left : FramedCodec α) (right : FramedCodec β) :
    FramedCodec (α × β) where
  encode pair := left.encode pair.1 ++ right.encode pair.2
  parse bytes :=
    (left.parse bytes).bind fun first =>
      (right.parse first.2).bind fun second =>
        some ((first.1, second.1), second.2)
  parse_encode_append pair suffix := by
    simp only [List.append_assoc, left.parse_encode_append, Option.bind_some,
      right.parse_encode_append]

/-- Transport along a retraction `forward ∘ backward = id`. -/
def iso (codec : FramedCodec α) (forward : α → β) (backward : β → α)
    (hforward : ∀ value, forward (backward value) = value) :
    FramedCodec β where
  encode value := codec.encode (backward value)
  parse bytes :=
    (codec.parse bytes).map fun result => (forward result.1, result.2)
  parse_encode_append value suffix := by
    simp only [codec.parse_encode_append, Option.map_some, hforward]

/-- Encode a list element by element; the count is framed by the caller. -/
def encodeList (codec : FramedCodec α) : List α → List UInt8
  | [] => []
  | value :: values => codec.encode value ++ encodeList codec values

/-- Parse exactly `count` elements. -/
def parseList (codec : FramedCodec α) : Nat → Parser (List α)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes =>
      (codec.parse bytes).bind fun first =>
        (parseList codec count first.2).bind fun rest =>
          some (first.1 :: rest.1, rest.2)

theorem parseList_encodeList_append (codec : FramedCodec α) (values : List α)
    (suffix : List UInt8) :
    parseList codec values.length (encodeList codec values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [encodeList, List.append_assoc, parseList]
      rw [codec.parse_encode_append, Option.bind_some]
      dsimp only
      rw [ih, Option.bind_some]

theorem parseList_encodeList_append' (codec : FramedCodec α) (values : List α)
    (count : Nat) (hcount : values.length = count) (suffix : List UInt8) :
    parseList codec count (encodeList codec values ++ suffix) =
      some (values, suffix) := by
  subst hcount
  exact parseList_encodeList_append codec values suffix

/-- Exactly `count` parsed elements, as a vector. -/
def listToFin? (count : Nat) (values : List α) : Option (Fin count → α) :=
  if exact : values.length = count then
    some fun index => values.get (Fin.cast exact.symm index)
  else none

theorem listToFin_ofFn {count : Nat} (vector : Fin count → α) :
    listToFin? count (List.ofFn vector) = some vector := by
  simp only [listToFin?, List.length_ofFn, ↓reduceDIte]
  apply congrArg some
  funext index
  simp

/-- Fixed-count vectors. -/
def vec (codec : FramedCodec α) (count : Nat) : FramedCodec (Fin count → α) where
  encode vector := encodeList codec (List.ofFn vector)
  parse bytes :=
    (parseList codec count bytes).bind fun result =>
      (listToFin? count result.1).map fun vector => (vector, result.2)
  parse_encode_append vector suffix := by
    simp only [parseList_encodeList_append' codec (List.ofFn vector) count
      List.length_ofFn, Option.bind_some, listToFin_ofFn, Option.map_some]

end FramedCodec

/-! ## Naturals: a base-128 little-endian varint for path lengths -/

/-- Seven payload bits per byte, high bit set on every byte but the last. -/
def encodeNat : Nat → List UInt8
  | n =>
    if h : n < 128 then
      [UInt8.ofNatLT n (by simp only [UInt8.size]; omega)]
    else
      UInt8.ofNatLT (n % 128 + 128) (by simp only [UInt8.size]; omega) ::
        encodeNat (n / 128)
decreasing_by all_goals omega

def decodeNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | byte :: rest =>
      if byte.toNat < 128 then some (byte.toNat, rest)
      else (decodeNat rest).map fun result =>
        (byte.toNat - 128 + 128 * result.1, result.2)

theorem decodeNat_encodeNat_append (n : Nat) (suffix : List UInt8) :
    decodeNat (encodeNat n ++ suffix) = some (n, suffix) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [encodeNat]
    by_cases h : n < 128
    · rw [dif_pos h]
      simp [decodeNat, h]
    · rw [dif_neg h]
      simp only [List.cons_append, decodeNat, UInt8.toNat_ofNatLT]
      rw [if_neg (by omega), ih (n / 128) (by omega), Option.map_some]
      have hvalue : n % 128 + 128 - 128 + 128 * (n / 128) = n := by omega
      rw [hvalue]

def natFramed : FramedCodec Nat where
  encode := encodeNat
  parse := decodeNat
  parse_encode_append := decodeNat_encodeNat_append

/-! ## Field-word vectors, Ext4, and digests over the landed word codec -/

/-- Exactly `count` canonical BabyBear words, through the landed strict
`decodeFields` parser. -/
def fieldVecFramed (count : Nat) : FramedCodec (Fin count → F) where
  encode vector := encodeFields (List.ofFn vector)
  parse bytes :=
    (decodeFields count bytes).bind fun result =>
      (FramedCodec.listToFin? count result.1).map fun vector =>
        (vector, result.2)
  parse_encode_append vector suffix := by
    have h := decodeFields_encodeFields_append (List.ofFn vector) suffix
    rw [List.length_ofFn] at h
    simp only [h, Option.bind_some, FramedCodec.listToFin_ofFn, Option.map_some]

/-- Read four coefficients back through the proved power basis. -/
def ext4OfCoefficients4 (vector : Fin 4 → F) : E :=
  coefficients.symm fun i => vector (Fin.cast extensionPolynomial_natDegree i)

theorem ext4OfCoefficients4_coefficients4 (value : E) :
    ext4OfCoefficients4 (coefficients4 value) = value := by
  apply coefficients.injective
  unfold ext4OfCoefficients4
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp [coefficients4]

/-- Ext4: the four canonical power-basis coefficients as four field words. -/
def ext4Framed : FramedCodec E :=
  (fieldVecFramed 4).iso ext4OfCoefficients4 coefficients4
    ext4OfCoefficients4_coefficients4

/-- Roots and every other digest: a digest IS an 8-lane rate block. -/
def digestFramed : FramedCodec Digest := fieldVecFramed 8

/-- Merkle paths: varint length, then the digests. -/
def pathFramed : FramedCodec (List Digest) where
  encode path := encodeNat path.length ++ encodeRates path
  parse bytes :=
    (decodeNat bytes).bind fun header => decodeRates header.1 header.2
  parse_encode_append path suffix := by
    rw [List.append_assoc, decodeNat_encodeNat_append, Option.bind_some]
    exact decodeRates_encodeRates_append path suffix

/-! ## The receipt alphabet -/

def openingFramed : FramedCodec Opening :=
  (ext4Framed.prod (ext4Framed.prod (ext4Framed.prod
    (pathFramed.prod (pathFramed.prod pathFramed))))).iso
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩)
    (fun o => (o.left, (o.right, (o.next,
      (o.leftPath, (o.rightPath, o.nextPath))))))
    (fun _ => rfl)

def roundMessageFramed : FramedCodec RoundMessage :=
  (digestFramed.prod (ext4Framed.vec 3)).iso
    (fun t => ⟨t.1, t.2⟩)
    (fun message => (message.levelRoot, message.sumcheckCoefficients))
    (fun _ => rfl)

def statementFramed (m : Nat) : FramedCodec (Statement m) :=
  (digestFramed.prod ((ext4Framed.vec m).prod ext4Framed)).iso
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun statement =>
      (statement.statementId, (statement.evaluationPoint, statement.claimedValue)))
    (fun _ => rfl)

/-- The whole receipt: rounds, challenges, terminal root, query seeds, and
the `m × queryCount` opening table. -/
def receiptFramed (m queryCount : Nat) : FramedCodec (Receipt m queryCount) :=
  ((roundMessageFramed.vec m).prod ((ext4Framed.vec m).prod (digestFramed.prod
    ((digestFramed.vec queryCount).prod
      ((openingFramed.vec queryCount).vec m))))).iso
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun receipt => (receipt.round, (receipt.challenge, (receipt.terminalRoot,
      (receipt.querySeed, receipt.opening)))))
    (fun _ => rfl)

/-- The lawful codecs, in the tree's `LawfulCodec` interface. -/
def ext4Codec : LawfulCodec E := ext4Framed.toLawful
def rootCodec : LawfulCodec Digest := digestFramed.toLawful
def pathCodec : LawfulCodec (List Digest) := pathFramed.toLawful
def openingCodec : LawfulCodec Opening := openingFramed.toLawful
def roundMessageCodec : LawfulCodec RoundMessage := roundMessageFramed.toLawful
def statementCodec (m : Nat) : LawfulCodec (Statement m) :=
  (statementFramed m).toLawful
def receiptCodec (m queryCount : Nat) : LawfulCodec (Receipt m queryCount) :=
  (receiptFramed m queryCount).toLawful

theorem ext4_decode_encode (value : E) :
    ext4Framed.decode (ext4Framed.encode value) = some value :=
  ext4Framed.decode_encode value

theorem root_decode_encode (root : Digest) :
    digestFramed.decode (digestFramed.encode root) = some root :=
  digestFramed.decode_encode root

theorem path_decode_encode (path : List Digest) :
    pathFramed.decode (pathFramed.encode path) = some path :=
  pathFramed.decode_encode path

theorem receipt_decode_encode {m queryCount : Nat} (receipt : Receipt m queryCount) :
    (receiptFramed m queryCount).decode ((receiptFramed m queryCount).encode receipt) =
      some receipt :=
  (receiptFramed m queryCount).decode_encode receipt

theorem encodeReceipt_injective (m queryCount : Nat) :
    Function.Injective (receiptFramed m queryCount).encode :=
  (receiptFramed m queryCount).encode_injective

/-! ## Binding to the proved field semantics -/

theorem encodeFields_append (left right : List F) :
    encodeFields (left ++ right) = encodeFields left ++ encodeFields right := by
  induction left with
  | nil => rfl
  | cons value values ih => simp [encodeFields, ih]

/-- ⭐ The Ext4 bytes are the head of the proved rate codec at the BaseFold
leaf block; the tail is the four zero rate lanes.  One codec, not two. -/
theorem encodeRate_extBlock (value : E) :
    encodeRate (extBlock value) =
      ext4Framed.encode value ++ encodeFields (List.ofFn fun _ : Fin 4 => (0 : F)) := by
  unfold encodeRate extBlock BaseFoldPoseidon2Rom.leafBlock
  rw [List.ofFn_fin_append, encodeFields_append]
  rfl

/-- Decoding the Ext4 bytes is exactly reading the leaf block's first four
lanes in the power basis, the verifier's `rateChallenge`. -/
theorem ext4_decode_eq_rateChallenge (value : E) :
    ext4Framed.decode (ext4Framed.encode value) =
      some (rateChallenge (extBlock value)) := by
  rw [ext4_decode_encode, rateChallenge_extBlock]

/-- Falsifier: a noncanonical first word (the modulus itself) is refused,
not reduced. -/
theorem ext4_noncanonical_word_refused :
    ext4Framed.decode (encodeNatLE4 modulus ++ encodeFields [0, 0, 0]) = none := by
  have hparse :
      decodeFields 4 (encodeNatLE4 modulus ++ encodeFields [0, 0, 0]) = none := by
    simp [decodeFields, encodeNatLE4_length, decodeField_modulus_rejected]
  unfold FramedCodec.decode
  simp [ext4Framed, FramedCodec.iso, fieldVecFramed, hparse]

theorem listToRate_eq_listToFin (values : List F) :
    listToRate? values = FramedCodec.listToFin? 8 values := rfl

/-- ⭐ The root codec's strict decoder IS the landed lawful rate decoder. -/
theorem digestFramed_decode_eq_decodeRate (bytes : List UInt8) :
    digestFramed.decode bytes = decodeRate bytes := by
  unfold FramedCodec.decode decodeRate
  simp only [digestFramed, fieldVecFramed, listToRate_eq_listToFin]
  cases decodeFields 8 bytes with
  | none => rfl
  | some result =>
      obtain ⟨values, rest⟩ := result
      simp only [Option.bind_some]
      cases rest with
      | nil => cases h : FramedCodec.listToFin? 8 values <;> simp [h]
      | cons byte rest => cases FramedCodec.listToFin? 8 values <;> rfl

/-- Falsifier for the root codec: a trailing byte is a framing error. -/
theorem root_trailing_refused (root : Digest) (byte : UInt8) :
    digestFramed.decode (digestFramed.encode root ++ [byte]) = none :=
  digestFramed.decode_encode_append_refused root [byte] (by simp)

/-! ## Binding to the proved Merkle semantics -/

/-- ⭐ Path bytes verify under the binary-Merkle opening scheme exactly when
the path does. -/
theorem merkle_path_bytes_verify_iff {k : Nat} (root : Digest)
    (index : Fin (2 ^ k)) (value : E) (path : List Digest) :
    (∃ decoded, pathFramed.decode (pathFramed.encode path) = some decoded ∧
        (BinaryMerkle.openingScheme hashSuite k).verifyOpen root index value
          decoded) ↔
      (BinaryMerkle.openingScheme hashSuite k).verifyOpen root index value path := by
  constructor
  · rintro ⟨decoded, hdecode, hverify⟩
    rw [path_decode_encode] at hdecode
    obtain rfl := Option.some.inj hdecode
    exact hverify
  · intro hverify
    exact ⟨path, path_decode_encode path, hverify⟩

/-- Falsifier (Merkle semantics): appending one sibling to a full-length
path is refused, because `recompute` fails closed on over-long paths. -/
theorem merkle_path_extra_sibling_refused {k : Nat} (root : Digest)
    (index : Fin (2 ^ k)) (value : E) (path : List Digest) (sibling : Digest)
    (hpath : path.length = k) :
    ¬ (BinaryMerkle.openingScheme hashSuite k).verifyOpen root index value
        (path ++ [sibling]) := by
  intro hverify
  have hlength := BinaryMerkle.recompute_some_path_length hashSuite _ _ _ _ hverify
  rw [List.length_append, List.length_singleton, hpath] at hlength
  omega

theorem decodeRates_encodeRates_extra (path : List Digest) :
    decodeRates (path.length + 1) (encodeRates path) = none := by
  induction path with
  | nil => simp [decodeRates, encodeRates, decodeRate, decodeFields, decodeField]
  | cons block path ih =>
      simp only [List.length_cons, encodeRates]
      rw [decodeRates]
      simp [encodeRate_length, decodeRate_encodeRate, ih]

/-- Falsifier (framing): a length prefix one too large is refused by the
parser — no digest is invented. -/
theorem path_length_tamper_refused (path : List Digest) :
    pathFramed.decode (encodeNat (path.length + 1) ++ encodeRates path) = none := by
  unfold FramedCodec.decode
  simp [pathFramed, decodeNat_encodeNat_append, decodeRates_encodeRates_extra]

/-! ## Binding the whole receipt to acceptance -/

/-- The BCS accept predicate evaluated on bytes: decode strictly, then run the
Lean-side verifier.  Undecodable bytes are refused. -/
def AcceptsBytes {ell m : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hmell : m ≤ ell) (statement : Statement m) (queryCount : Nat)
    (bytes : List UInt8) : Prop :=
  ∃ receipt : Receipt m queryCount,
    (receiptFramed m queryCount).decode bytes = some receipt ∧
      Accepts T st hmell statement receipt

/-- ⭐ **`bcs_accept_bytes_iff`.**  The byte-level accept predicate on the
encoded receipt is the Lean-side accept predicate on the receipt. -/
theorem bcs_accept_bytes_iff {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hmell : m ≤ ell) (statement : Statement m)
    (receipt : Receipt m queryCount) :
    AcceptsBytes T st hmell statement queryCount
        ((receiptFramed m queryCount).encode receipt) ↔
      Accepts T st hmell statement receipt := by
  constructor
  · rintro ⟨decoded, hdecode, haccept⟩
    rw [receipt_decode_encode] at hdecode
    obtain rfl := Option.some.inj hdecode
    exact haccept
  · intro haccept
    exact ⟨receipt, receipt_decode_encode receipt, haccept⟩

/-- Falsifier (framing): any trailing bytes after an encoded receipt are
refused, whatever the receipt. -/
theorem acceptsBytes_trailing_refused {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hmell : m ≤ ell) (statement : Statement m)
    (receipt : Receipt m queryCount) (suffix : List UInt8)
    (hsuffix : suffix ≠ []) :
    ¬ AcceptsBytes T st hmell statement queryCount
        ((receiptFramed m queryCount).encode receipt ++ suffix) := by
  rintro ⟨decoded, hdecode, _⟩
  rw [FramedCodec.decode_encode_append_refused _ _ _ hsuffix] at hdecode
  cases hdecode

/-- A byte-level tamper: the same receipt with its terminal root replaced. -/
def tamperTerminalRoot {m queryCount : Nat} (receipt : Receipt m queryCount)
    (root : Digest) : Receipt m queryCount :=
  { receipt with terminalRoot := root }

theorem tamperTerminalRoot_bytes_ne {m queryCount : Nat}
    (receipt : Receipt m queryCount) (root : Digest)
    (hne : root ≠ receipt.terminalRoot) :
    (receiptFramed m queryCount).encode (tamperTerminalRoot receipt root) ≠
      (receiptFramed m queryCount).encode receipt := by
  intro h
  have := encodeReceipt_injective m queryCount h
  exact hne (congrArg Receipt.terminalRoot this)

/-- ⭐ Falsifier (semantics): tampering the terminal-root bytes of an accepted
receipt yields bytes the Lean predicate refuses — `RootsExact` pins the
terminal root to the adaptive statement's root at the checked challenges. -/
theorem acceptsBytes_terminalRoot_tamper_refused {ell m queryCount : Nat}
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hmell : m ≤ ell) (statement : Statement m)
    (receipt : Receipt m queryCount) (root : Digest)
    (hne : root ≠ receipt.terminalRoot)
    (haccept : Accepts T st hmell statement receipt) :
    ¬ AcceptsBytes T st hmell statement queryCount
        ((receiptFramed m queryCount).encode (tamperTerminalRoot receipt root)) := by
  rw [bcs_accept_bytes_iff]
  intro htampered
  have horig := haccept.2.1 m le_rfl
  have htamp := htampered.2.1 m le_rfl
  simp [receiptLevelRoot, tamperTerminalRoot] at horig htamp
  exact hne (htamp.trans horig.symm)

#check @FramedCodec.decode_encode
#check @decodeNat_encodeNat_append
#check @ext4Codec
#check @rootCodec
#check @pathCodec
#check @receiptCodec
#check @encodeRate_extBlock
#check @ext4_decode_eq_rateChallenge
#check @digestFramed_decode_eq_decodeRate
#check @merkle_path_bytes_verify_iff
#check @merkle_path_extra_sibling_refused
#check @bcs_accept_bytes_iff
#check @acceptsBytes_trailing_refused
#check @acceptsBytes_terminalRoot_tamper_refused

/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.decodeNat_encodeNat_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeNat_encodeNat_append
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.receipt_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms receipt_decode_encode
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.encodeRate_extBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeRate_extBlock
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.ext4_decode_eq_rateChallenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ext4_decode_eq_rateChallenge
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.ext4_noncanonical_word_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ext4_noncanonical_word_refused
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.digestFramed_decode_eq_decodeRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms digestFramed_decode_eq_decodeRate
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.merkle_path_bytes_verify_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms merkle_path_bytes_verify_iff
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.merkle_path_extra_sibling_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms merkle_path_extra_sibling_refused
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.path_length_tamper_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms path_length_tamper_refused
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.bcs_accept_bytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bcs_accept_bytes_iff
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.acceptsBytes_trailing_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptsBytes_trailing_refused
/-- info: 'Minidregg.Selvage.BaseFoldBcsReceiptCodec.acceptsBytes_terminalRoot_tamper_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptsBytes_terminalRoot_tamper_refused

end

end Minidregg.Selvage.BaseFoldBcsReceiptCodec
