/-
Source-level algebra for the two-component additive BFV path. The carrier is
an actual polynomial quotient, with its canonical remainder coefficient map.
No phase homomorphism is assumed: it is constructed from the ciphertext pair,
secret multiplication, quotient multiplication and coefficient projection.
Literal Rust/RNS/NTT and sampler refinements remain separate obligations.
-/
import Theory.IntegerWindowNoise
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic

namespace Minidregg.Theory.BfvPhaseAlgebra
set_option autoImplicit false
open scoped BigOperators
open Polynomial

section Pair
variable {R : Type} [CommRing R]
abbrev CipherPair (R : Type) := R × R

def keygen (s a e : R) : CipherPair R := (e - a * s, a)
def encrypt (pk : CipherPair R) (u e1 e2 encoded : R) : CipherPair R :=
  (u * pk.1 + e1 + encoded, u * pk.2 + e2)
def plainMul (p : R) (c : CipherPair R) : CipherPair R := (c.1 * p, c.2 * p)

def phase (s : R) : CipherPair R →+ R where
  toFun c := c.1 + c.2 * s
  map_zero' := by simp
  map_add' c d := by simp only [Prod.fst_add, Prod.snd_add]; ring

def EncryptionPhaseIdentity : Prop :=
  ∀ s a e u e1 e2 encoded : R,
    phase s (encrypt (keygen s a e) u e1 e2 encoded) = encoded + u * e + e1 + e2 * s

theorem keygen_phase (s a e : R) : phase s (keygen s a e) = e := by
  simp only [phase, AddMonoidHom.coe_mk, ZeroHom.coe_mk, keygen]
  ring

theorem encryption_phase : EncryptionPhaseIdentity (R := R) := by
  intro s a e u e1 e2 encoded
  simp only [phase, AddMonoidHom.coe_mk, ZeroHom.coe_mk, encrypt, keygen]
  ring

theorem phase_plainMul (s p : R) (c : CipherPair R) :
    phase s (plainMul p c) = phase s c * p := by
  simp only [phase, plainMul, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

def multiplyHom (p : R) : R →+ R where
  toFun a := a * p
  map_zero' := by simp
  map_add' a b := by exact add_mul a b p

def plainMulHom (p : R) : CipherPair R →+ CipherPair R where
  toFun := plainMul p
  map_zero' := by ext <;> simp [plainMul]
  map_add' a b := by ext <;> simp [plainMul, add_mul]

theorem phase_add_sub (s : R) (acc fresh expired : CipherPair R) :
    phase s (acc + fresh - expired) = phase s acc + phase s fresh - phase s expired := by
  simp only [map_sub, map_add]

theorem signed_plainMul (s positive negative : R) (c : CipherPair R) :
    phase s (plainMul positive c - plainMul negative c) = phase s c * (positive - negative) := by
  rw [map_sub, phase_plainMul, phase_plainMul]
  ring
end Pair

/-- The literal source pre-encoding: multiply by Q mod t in the plaintext
ring, then multiply by inverse(-t) in the ciphertext ring. -/
def sourceEncoded (q : Nat) (t m : Int) (delta : ZMod q) : ZMod q :=
  (((m * ((q : Int) % t)) % t : Int) : ZMod q) * delta

theorem source_encoded_canonical (q : Nat) (t m : Int) (delta : ZMod q) :
    sourceEncoded q t (m % t) delta = sourceEncoded q t m delta := by
  simp only [sourceEncoded, Int.mul_emod, Int.emod_emod]

def ScalingPremise (q : Nat) (t : Int) (delta : ZMod q) : Prop :=
  (-(t : ZMod q)) * delta = 1

theorem source_encoded_floor (q : Nat) (t m : Int) (delta : ZMod q)
    (hinv : ScalingPremise q t delta) :
    sourceEncoded q t m delta = (((q : Int) * m / t : Int) : ZMod q) := by
  have he : ((m * ((q : Int) % t)) % t : Int) = (q : Int) * m % t := by
    simp [Int.mul_emod, mul_comm]
  have hdiv := Int.mul_ediv_add_emod ((q : Int) * m) t
  have hc := congrArg (fun z : Int => (z : ZMod q)) hdiv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul] at hc
  have hrem : (((q : Int) * m % t : Int) : ZMod q) =
      -(t : ZMod q) * (((q : Int) * m / t : Int) : ZMod q) := by linear_combination hc
  unfold sourceEncoded
  rw [he, hrem]
  change -(t : ZMod q) * delta = 1 at hinv
  calc -(t : ZMod q) * ↑((q : Int) * m / t) * delta =
      (-(t : ZMod q) * delta) * ↑((q : Int) * m / t) := by ring
       _ = _ := by rw [hinv, one_mul]

section Negacyclic
variable (q N : Nat) [NeZero N]

noncomputable def modulus : Polynomial (ZMod q) := X ^ N + C 1

theorem modulus_monic : (modulus q N).Monic :=
  monic_X_pow_add_C 1 (NeZero.ne N)

abbrev Ring := AdjoinRoot (modulus q N)

/-- Canonical coefficient in the actual quotient (Z/qZ)[X]/(X^N+1). -/
noncomputable def coefficient (k : Nat) : Ring q N →+ ZMod q where
  toFun a := (AdjoinRoot.modByMonicHom (modulus_monic q N) a).coeff k
  map_zero' := by simp
  map_add' a b := by simp

/-- Constructed fixed-query phase map for the window bridge. -/
noncomputable def readoutPhase (s query : Ring q N) (k : Nat) :
    CipherPair (Ring q N) →+ ZMod q :=
  (coefficient q N k).comp ((multiplyHom query).comp (phase s))

theorem readout_is_coefficient (s query : Ring q N) (k : Nat) (c : CipherPair (Ring q N)) :
    readoutPhase q N s query k c = coefficient q N k (phase s (plainMul query c)) := by
  simp only [readoutPhase, AddMonoidHom.comp_apply, multiplyHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, phase_plainMul]

theorem readout_signed_query (s positive negative : Ring q N) (k : Nat)
    (c : CipherPair (Ring q N)) :
    readoutPhase q N s (positive - negative) k c =
      coefficient q N k (phase s (plainMul positive c - plainMul negative c)) := by
  simp only [readoutPhase, AddMonoidHom.comp_apply, multiplyHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, signed_plainMul]

theorem readout_encryption (s a e u e1 e2 encoded query : Ring q N) (k : Nat) :
    readoutPhase q N s query k (encrypt (keygen s a e) u e1 e2 encoded) =
      coefficient q N k ((encoded + u * e + e1 + e2 * s) * query) := by
  change coefficient q N k (phase s (encrypt (keygen s a e) u e1 e2 encoded) * query) = _
  rw [encryption_phase]

omit [NeZero N] in
/-- This quotient is negacyclic, not cyclic: the wrap changes sign. -/
theorem root_power : (AdjoinRoot.root (modulus q N)) ^ N = -1 := by
  have h := AdjoinRoot.mk_self (f := modulus q N)
  rw [modulus, map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Reverse query coefficients around selected output k. -/
noncomputable def reverseQuery (k : Nat) (query : Fin (k + 1) → ZMod q) : Polynomial (ZMod q) :=
  ∑ j : Fin (k + 1), C (query j) * X ^ (k - j.val)

theorem reverseQuery_degree (k : Nat) (query : Fin (k + 1) → ZMod q) :
    (reverseQuery q k query).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem reverseQuery_coefficient (p : Polynomial (ZMod q)) (k : Nat)
    (query : Fin (k + 1) → ZMod q) :
    (p * reverseQuery q k query).coeff k = ∑ j : Fin (k + 1), query j * p.coeff j.val := by
  simp only [reverseQuery, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, coeff_mul_X_pow', if_pos (Nat.sub_le _ _), coeff_mul_C]
  have hj : k - (k - j.val) = j.val := by have := j.isLt; omega
  rw [hj, mul_comm]

/-- A product can wrap at lower coefficients without affecting selected k:
if degree(p)<N+k, the quotient by X^N+1 has degree<k. -/
theorem selected_coefficient_no_alias [Nontrivial (ZMod q)]
    (p : Polynomial (ZMod q)) (k : Nat) (hk0 : 0 < k) (hkN : k < N)
    (hp : p.natDegree < N + k) :
    coefficient q N k (AdjoinRoot.mk (modulus q N) p) = p.coeff k := by
  have hd : (p /ₘ modulus q N).natDegree < k := by
    rw [natDegree_divByMonic _ (modulus_monic q N), modulus, natDegree_X_pow_add_C]
    omega
  have hz : (p /ₘ modulus q N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt hd
  change (p %ₘ modulus q N).coeff k = p.coeff k
  rw [modByMonic_eq_sub_mul_div, coeff_sub]
  simp [modulus, add_mul, coeff_X_pow_mul', Nat.not_le_of_lt hkN]
  simpa [modulus] using hz

/-- Full-degree phase noise is allowed. It need not be supported only in the
message slots; no high phase coefficient aliases the chosen output k. -/
theorem packed_readout [Nontrivial (ZMod q)]
    (p : Polynomial (ZMod q)) (k : Nat) (query : Fin (k + 1) → ZMod q)
    (hk0 : 0 < k) (hkN : k < N) (hp : p.natDegree < N) :
    coefficient q N k
      (AdjoinRoot.mk (modulus q N) p * AdjoinRoot.mk (modulus q N) (reverseQuery q k query)) =
      ∑ j : Fin (k + 1), query j * p.coeff j.val := by
  rw [← map_mul]
  rw [selected_coefficient_no_alias q N _ k hk0 hkN]
  · exact reverseQuery_coefficient q p k query
  · have hm := natDegree_mul_le (p := p) (q := reverseQuery q k query)
    have hq := reverseQuery_degree q k query
    omega

/-- Every quotient element has the actual canonical degree-bounded phase
polynomial used in the packing theorem. -/
theorem canonical_degree [Nontrivial (ZMod q)] (a : Ring q N) :
    (AdjoinRoot.modByMonicHom (modulus_monic q N) a).natDegree < N := by
  induction a using AdjoinRoot.induction_on
  rename_i p
  rw [AdjoinRoot.modByMonicHom_mk]
  have hn : modulus q N ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    simp only [modulus, natDegree_X_pow_add_C, natDegree_one] at hd
    exact NeZero.ne N hd
  have h := natDegree_modByMonic_lt p (modulus_monic q N) hn
  simpa only [modulus, natDegree_X_pow_add_C] using h

/-- No arbitrary scalar phase interpretation remains at this seam: the
constructed ciphertext-pair map equals the dot product of the quotient
phase's canonical coefficients, including all its high noise coefficients. -/
theorem readout_dot_product [Nontrivial (ZMod q)]
    (s : Ring q N) (c : CipherPair (Ring q N)) (k : Nat)
    (query : Fin (k + 1) → ZMod q) (hk0 : 0 < k) (hkN : k < N) :
    readoutPhase q N s (AdjoinRoot.mk (modulus q N) (reverseQuery q k query)) k c =
      ∑ j : Fin (k + 1), query j * coefficient q N j.val (phase s c) := by
  let p := AdjoinRoot.modByMonicHom (modulus_monic q N) (phase s c)
  have he : AdjoinRoot.mk (modulus q N) p = phase s c :=
    AdjoinRoot.mk_leftInverse (modulus_monic q N) (phase s c)
  change coefficient q N k (phase s c * _) = _
  rw [← he]
  have h := packed_readout q N p k query hk0 hkN (canonical_degree q N (phase s c))
  simpa only [coefficient, AddMonoidHom.coe_mk, ZeroHom.coe_mk, p, he] using h

/-- The existing integer-window phase premise now follows from actual
coefficient congruences, rather than an assumed fixed-query hom. -/
theorem readout_integer_row [Nontrivial (ZMod q)]
    (s : Ring q N) (c : CipherPair (Ring q N)) (k : Nat)
    (query : Fin (k + 1) → Int) (row : IntegerWindowNoise.Row (k + 1))
    (hk0 : 0 < k) (hkN : k < N)
    (hc : ∀ j : Fin (k + 1), coefficient q N j.val (phase s c) = (row.phase j : ZMod q)) :
    readoutPhase q N s (AdjoinRoot.mk (modulus q N) (reverseQuery q k (fun j => (query j : ZMod q)))) k c =
      (IntegerWindowNoise.rowPhase query row : ZMod q) := by
  rw [readout_dot_product q N s c k _ hk0 hkN]
  simp only [IntegerWindowNoise.rowPhase, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hc, Int.cast_mul]

/-- Source coefficient packing, with every coefficient (including padding)
represented in the finite vector. -/
noncomputable def pack (values : Fin N → ZMod q) : Polynomial (ZMod q) :=
  ∑ i : Fin N, C (values i) * X ^ i.val

omit [NeZero N] in
theorem pack_coefficient (values : Fin N → ZMod q) (j : Fin N) :
    (pack q N values).coeff j.val = values j := by
  unfold pack
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hij (Fin.val_injective h).symm), mul_zero]
  · simp

theorem coefficient_pack [Nontrivial (ZMod q)] (values : Fin N → ZMod q) (j : Fin N) :
    coefficient q N j.val (AdjoinRoot.mk (modulus q N) (pack q N values)) = values j := by
  change ((pack q N values) %ₘ modulus q N).coeff j.val = values j
  rw [(modByMonic_eq_self_iff (modulus_monic q N)).mpr]
  · exact pack_coefficient q N values j
  · change (∑ i : Fin N, C (values i) * X ^ i.val).degree < (X ^ N + C 1 : Polynomial (ZMod q)).degree
    rw [degree_X_pow_add_C (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact degree_sum_fin_lt values

noncomputable def encodeRing (t : Int) (delta : ZMod q) (message : Fin N → Int) : Ring q N :=
  AdjoinRoot.mk (modulus q N) (pack q N (fun j => sourceEncoded q t (message j) delta))

theorem encoding_coefficient [Nontrivial (ZMod q)] (t : Int) (delta : ZMod q)
    (message : Fin N → Int) (j : Fin N) (hinv : ScalingPremise q t delta) :
    coefficient q N j.val (encodeRing q N t delta message) =
      (((q : Int) * message j / t : Int) : ZMod q) := by
  rw [encodeRing, coefficient_pack, source_encoded_floor q t (message j) delta hinv]

/-- The public-key noise polynomial follows from the literal key/encrypt
ring equations; its coefficient range is a separate sampler/convolution fact. -/
def noise {R : Type} [CommRing R] (s e u e1 e2 : R) : R := u * e + e1 + e2 * s

theorem encrypted_coefficient [Nontrivial (ZMod q)]
    (s a e u e1 e2 : Ring q N) (t : Int) (delta : ZMod q)
    (message : Fin N → Int) (j : Fin N) (hinv : ScalingPremise q t delta) :
    coefficient q N j.val (phase s
      (encrypt (keygen s a e) u e1 e2 (encodeRing q N t delta message))) =
      (((q : Int) * message j / t : Int) : ZMod q) + coefficient q N j.val (noise s e u e1 e2) := by
  rw [encryption_phase]
  have h : encodeRing q N t delta message + u * e + e1 + e2 * s =
      encodeRing q N t delta message + noise s e u e1 e2 := by unfold noise; ring
  rw [h, map_add, encoding_coefficient q N t delta message j hinv]

theorem coefficient_constant [Nontrivial (ZMod q)] (a : ZMod q) (k : Nat) :
    coefficient q N k (AdjoinRoot.of (modulus q N) a) = if k = 0 then a else 0 := by
  rw [← AdjoinRoot.mk_C]
  change ((C a) %ₘ modulus q N).coeff k = _
  rw [(modByMonic_eq_self_iff (modulus_monic q N)).mpr]
  · exact coeff_C
  · change (C a).degree < (X ^ N + C 1 : Polynomial (ZMod q)).degree
    rw [degree_X_pow_add_C (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact degree_C_le.trans_lt (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))

theorem coefficient_intCast [Nontrivial (ZMod q)] (a : Int) (k : Nat) :
    coefficient q N k (a : Ring q N) = if k = 0 then (a : ZMod q) else 0 := by
  have h : (a : Ring q N) = AdjoinRoot.of (modulus q N) (a : ZMod q) := by simp
  rw [h, coefficient_constant]

/-- A selected message/error prefix; all other phase coefficients remain in
the ring and are handled by `readout_dot_product`, not silently discarded. -/
def prefixIndex (k : Nat) (hkN : k < N) (j : Fin (k + 1)) : Fin N :=
  ⟨j.val, by have hj := j.isLt; omega⟩

def integerRow (t : Int) (k : Nat) (hkN : k < N)
    (message error : Fin N → Int) : IntegerWindowNoise.Row (k + 1) where
  message j := message (prefixIndex N k hkN j)
  error j := error (prefixIndex N k hkN j)
  phase j := (q : Int) * message (prefixIndex N k hkN j) / t + error (prefixIndex N k hkN j)

omit [NeZero N] in
theorem integerRow_fresh (t E : Int) (k : Nat) (hkN : k < N)
    (message error : Fin N → Int) (he : ∀ j, |error j| ≤ E) :
    IntegerWindowNoise.Fresh (q : Int) t E (integerRow q N t k hkN message error) := by
  intro j
  exact ⟨rfl, he _⟩

/-- Given a bounded signed lift of the *derived noise polynomial*, the exact
source key/encrypt equations supply the existing window's coefficient and
fixed-query phase premises. The noise-lift/support refinement is explicit. -/
theorem encrypted_integer_row [Nontrivial (ZMod q)]
    (s a e u e1 e2 : Ring q N) (t : Int) (delta : ZMod q)
    (message error : Fin N → Int) (k : Nat) (query : Fin (k + 1) → Int)
    (hk0 : 0 < k) (hkN : k < N) (hinv : ScalingPremise q t delta)
    (hnoise : ∀ j : Fin N, coefficient q N j.val (noise s e u e1 e2) = (error j : ZMod q)) :
    readoutPhase q N s
      (AdjoinRoot.mk (modulus q N) (reverseQuery q k (fun j => (query j : ZMod q)))) k
      (encrypt (keygen s a e) u e1 e2 (encodeRing q N t delta message)) =
      (IntegerWindowNoise.rowPhase query (integerRow q N t k hkN message error) : ZMod q) := by
  apply readout_integer_row q N s _ k query _ hk0 hkN
  intro j
  have h := encrypted_coefficient q N s a e u e1 e2 t delta message
    (prefixIndex N k hkN j) hinv
  rw [hnoise, ← Int.cast_add] at h
  exact h

end Negacyclic
/- Observed axiom closure pins from the successful check. -/
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.keygen_phase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.keygen_phase
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.encryption_phase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.encryption_phase
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.phase_plainMul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.phase_plainMul
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.phase_add_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.phase_add_sub
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.signed_plainMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.signed_plainMul
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.source_encoded_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.source_encoded_canonical
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.source_encoded_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.source_encoded_floor
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.modulus_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.modulus_monic
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.readout_is_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.readout_is_coefficient
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.readout_signed_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.readout_signed_query
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.readout_encryption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.readout_encryption
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.root_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.root_power
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.reverseQuery_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.reverseQuery_degree
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.reverseQuery_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.reverseQuery_coefficient
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.selected_coefficient_no_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.selected_coefficient_no_alias
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.packed_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.packed_readout
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.canonical_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.canonical_degree
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.readout_dot_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.readout_dot_product
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.readout_integer_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.readout_integer_row
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.pack_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.pack_coefficient
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.coefficient_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.coefficient_pack
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.encoding_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.encoding_coefficient
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.encrypted_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.encrypted_coefficient
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.coefficient_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.coefficient_constant
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.coefficient_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.coefficient_intCast
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.integerRow_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.integerRow_fresh
/-- info: 'Minidregg.Theory.BfvPhaseAlgebra.encrypted_integer_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvPhaseAlgebra.encrypted_integer_row

end Minidregg.Theory.BfvPhaseAlgebra
