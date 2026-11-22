module
public import Obend.Vault.Mandate
public import Obend.Crypto.Transcript

public section
namespace Obend.Polis.CapTP
open Obend.Vault.Mandate Obend.Crypto

/-- Strict ordering is a representation invariant, not a cached lookup certificate. -/
def SortedBy {α : Type} (key : α → Nat) (a : Array α) : Prop :=
  ∀ i j (hi : i < a.size) (hj : j < a.size), i < j → key a[i] < key a[j]

/-- Half-open interval binary search. Fuel is only a termination bound; each recursive
call halves the interval. No array slices or linear fallback are evaluated. -/
def search {α : Type} (key : α → Nat) (a : Array α) (k : Nat) :
    Nat → Nat → Nat → Option α
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if hm : mid < a.size then
        if key a[mid] < k then search key a k fuel (mid + 1) hi
        else if k < key a[mid] then search key a k fuel lo mid
        else some a[mid]
      else none
    else none

theorem search_sound {α : Type} (key : α → Nat) (a : Array α) (k : Nat)
    (fuel lo hi : Nat) (x : α) (h : search key a k fuel lo hi = some x) :
    ∃ i, ∃ h : i < a.size, a[i] = x ∧ key x = k := by
  induction fuel generalizing lo hi with
  | zero => simp [search] at h
  | succ fuel ih =>
    simp only [search] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · exact ih _ _ h
    · split at h
      · exact ih _ _ h
      · have hx := Option.some.inj h
        refine ⟨_, ‹_ < a.size›, hx, ?_⟩
        subst x
        omega

theorem search_complete {α : Type} (key : α → Nat) (a : Array α)
    (hs : SortedBy key a) (k fuel lo hi i : Nat) (hiA : hi ≤ a.size)
    (hlen : hi - lo < fuel) (hil : lo ≤ i) (hih : i < hi)
    (hk : key (a[i]'(by omega)) = k) :
    search key a k fuel lo hi = some a[i] := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    have hmid : (lo + hi) / 2 < hi := by omega
    have hmlo : lo ≤ (lo + hi) / 2 := by omega
    have hmA : (lo + hi) / 2 < a.size := by omega
    simp only [search, show lo < hi by omega, hmA, ite_true, dite_true]
    split
    · have hmi : (lo + hi) / 2 < i := by
        apply Classical.byContradiction
        intro hn
        have he : i ≤ (lo + hi) / 2 := by omega
        rcases Nat.lt_or_eq_of_le he with he | he
        · have := hs i ((lo + hi) / 2) (by omega) hmA he
          omega
        · subst i; omega
      exact ih ((lo + hi) / 2 + 1) hi hiA (by omega) (by omega) hih hk
    · split
      · have him : i < (lo + hi) / 2 := by
          apply Classical.byContradiction
          intro hn
          have he : (lo + hi) / 2 ≤ i := by omega
          rcases Nat.lt_or_eq_of_le he with he | he
          · have := hs ((lo + hi) / 2) i hmA (by omega) he
            omega
          · subst i; omega
        exact ih lo ((lo + hi) / 2) (by omega) (by omega) hil him hk
      · have he : i = (lo + hi) / 2 := by
          rcases Nat.lt_trichotomy i ((lo + hi) / 2) with hl | he | hr
          · have := hs i _ (by omega) hmA hl; omega
          · exact he
          · have := hs _ i hmA (by omega) hr; omega
        subst i
        rfl

/-- Mathematical lookup is a linear list specification, independent of binary search. -/
def findSpec {α : Type} (key : α → Nat) (a : Array α) (k : Nat) : Option α :=
  a.toList.find? (fun x => key x == k)

theorem search_eq_spec {α : Type} (key : α → Nat) (a : Array α)
    (hs : SortedBy key a) (k : Nat) :
    search key a k (a.size + 1) 0 a.size = findSpec key a k := by
  cases hf : findSpec key a k with
  | none =>
    cases he : search key a k (a.size + 1) 0 a.size with
    | none => rfl
    | some x =>
      obtain ⟨i, hi, hx, hk⟩ := search_sound key a k _ _ _ x he
      have hn := List.find?_eq_none.mp hf x
      have hm : x ∈ a.toList := by simp [← hx, Array.mem_iff_getElem]; exact ⟨i, hi, rfl⟩
      simp [hk] at hn
      exact False.elim (hn (by simpa using hm))
  | some x =>
    have hm := List.mem_of_find?_eq_some hf
    have hk : key x = k := by simpa using List.find?_some hf
    have hm' : x ∈ a := by simpa using hm
    obtain ⟨i, hi, hx⟩ := Array.mem_iff_getElem.mp hm'
    have hc := search_complete key a hs k (a.size + 1) 0 a.size i
      (by omega) (by omega) (by omega) hi (by simpa [hx] using hk)
    simpa [hx] using hc

/-- Sorted set insertion deduplicates and preserves the order. -/
def insertKey (k : UInt64) : List UInt64 → List UInt64
  | [] => [k]
  | x :: xs => if k.toNat < x.toNat then k :: x :: xs
    else if k = x then x :: xs else x :: insertKey k xs

@[simp] theorem mem_insertKey (k x : UInt64) (xs : List UInt64) :
    x ∈ insertKey k xs ↔ x = k ∨ x ∈ xs := by
  induction xs with
  | nil => simp [insertKey]
  | cons y ys ih =>
    simp only [insertKey]
    split
    · simp only [List.mem_cons] <;> grind
    · split
      · simp_all
      · simp only [List.mem_cons, ih] <;> grind

theorem insertKey_sorted (k : UInt64) (xs : List UInt64)
    (h : xs.Pairwise (fun a b => a.toNat < b.toNat)) :
    (insertKey k xs).Pairwise (fun a b => a.toNat < b.toNat) := by
  induction xs with
  | nil => simp [insertKey]
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    simp only [insertKey]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hx, ht⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hm
      · subst y; assumption
      · have := hx y hm; omega
    · split
      · exact List.pairwise_cons.mpr ⟨hx, ht⟩
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ih ht⟩
        intro y hy
        rcases (mem_insertKey k y xs).mp hy with he | hm
        · subst y
          have hne : k.toNat ≠ x.toNat := by
            intro he; have : k = x := UInt64.toNat_inj.mp he; contradiction
          omega
        · exact hx y hm

structure SortedU64Set where
  data : Array UInt64
  sorted : data.toList.Pairwise (fun a b => a.toNat < b.toNat)

def SortedU64Set.empty : SortedU64Set := ⟨#[], by simp⟩
def SortedU64Set.spec (s : SortedU64Set) (k : UInt64) : Prop := k ∈ s.data.toList

def SortedU64Set.contains (s : SortedU64Set) (k : UInt64) : Bool :=
  (search UInt64.toNat s.data k.toNat (s.data.size + 1) 0 s.data.size).isSome

def SortedU64Set.insert (s : SortedU64Set) (k : UInt64) : SortedU64Set :=
  ⟨(insertKey k s.data.toList).toArray, by simpa using insertKey_sorted k _ s.sorted⟩

theorem SortedU64Set.contains_eq_spec (s : SortedU64Set) (k : UInt64) :
    s.contains k = true ↔ s.spec k := by
  have hs : SortedBy UInt64.toNat s.data := by
    intro i j hi hj hij
    exact (List.pairwise_iff_getElem.mp s.sorted) i j (by simpa) (by simpa) hij
  unfold contains
  rw [search_eq_spec _ _ hs]
  simp only [findSpec, List.isSome_find?, List.any_eq_true, beq_iff_eq, spec]
  constructor
  · rintro ⟨x, hx, he⟩; have : x = k := UInt64.toNat_inj.mp he; simpa [this] using hx
  · intro hk; exact ⟨k, hk, rfl⟩

@[simp] theorem SortedU64Set.spec_insert (s : SortedU64Set) (k x : UInt64) :
    (s.insert k).spec x ↔ x = k ∨ s.spec x := by simp [insert, spec]

theorem SortedU64Set.contains_list (s : SortedU64Set) (k : UInt64) :
    s.contains k = s.data.toList.contains k := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_spec]
  simp only [spec, List.contains_iff_mem]

/-! ## 256-bit keys

Bearer secrets, handoff nonces and pending ids are full 256-bit values: a 64-bit key admits a
birthday collision after about 2^32 draws. `Digest256` is the tree's fixed-width commitment
(`Obend.Core.Digest.Digest256 = BitVec 256`; its big-endian 4 x `UInt64` limb view is
`Obend.Core.Digest.DigestWords4`, a proved bijection). Its numeric literals are `BitVec.ofNat`,
and `BitVec.toNat` is the injective key, so `SortedBy`/`search`/`search_eq_spec` are reused. -/
open Obend.Core.Digest (Digest256)

theorem digest256_toNat_injective {a b : Digest256} (h : a.toNat = b.toNat) : a = b :=
  BitVec.toNat_inj.mp h

/-- Sorted digest-set insertion deduplicates and preserves the order (`insertKey` at 256 bits). -/
def insertDigest (k : Digest256) : List Digest256 → List Digest256
  | [] => [k]
  | x :: xs => if k.toNat < x.toNat then k :: x :: xs
    else if k = x then x :: xs else x :: insertDigest k xs

@[simp] theorem mem_insertDigest (k x : Digest256) (xs : List Digest256) :
    x ∈ insertDigest k xs ↔ x = k ∨ x ∈ xs := by
  induction xs with
  | nil => simp [insertDigest]
  | cons y ys ih =>
    simp only [insertDigest]
    split
    · simp only [List.mem_cons] <;> grind
    · split
      · simp_all
      · simp only [List.mem_cons, ih] <;> grind

theorem insertDigest_sorted (k : Digest256) (xs : List Digest256)
    (h : xs.Pairwise (fun a b => a.toNat < b.toNat)) :
    (insertDigest k xs).Pairwise (fun a b => a.toNat < b.toNat) := by
  induction xs with
  | nil => simp [insertDigest]
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    simp only [insertDigest]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hx, ht⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hm
      · subst y; assumption
      · have := hx y hm; omega
    · split
      · exact List.pairwise_cons.mpr ⟨hx, ht⟩
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ih ht⟩
        intro y hy
        rcases (mem_insertDigest k y xs).mp hy with he | hm
        · subst y
          have hne : k.toNat ≠ x.toNat := by
            intro he; have : k = x := digest256_toNat_injective he; contradiction
          omega
        · exact hx y hm

/-- A strictly sorted set of 256-bit keys with logarithmic membership. -/
structure SortedDigestSet where
  data : Array Digest256
  sorted : data.toList.Pairwise (fun a b => a.toNat < b.toNat)

def SortedDigestSet.empty : SortedDigestSet := ⟨#[], by simp⟩
def SortedDigestSet.spec (s : SortedDigestSet) (k : Digest256) : Prop := k ∈ s.data.toList

def SortedDigestSet.contains (s : SortedDigestSet) (k : Digest256) : Bool :=
  (search BitVec.toNat s.data k.toNat (s.data.size + 1) 0 s.data.size).isSome

def SortedDigestSet.insert (s : SortedDigestSet) (k : Digest256) : SortedDigestSet :=
  ⟨(insertDigest k s.data.toList).toArray, by simpa using insertDigest_sorted k _ s.sorted⟩

theorem SortedDigestSet.contains_eq_spec (s : SortedDigestSet) (k : Digest256) :
    s.contains k = true ↔ s.spec k := by
  have hs : SortedBy BitVec.toNat s.data := by
    intro i j hi hj hij
    exact (List.pairwise_iff_getElem.mp s.sorted) i j (by simpa) (by simpa) hij
  unfold contains
  rw [search_eq_spec _ _ hs]
  simp only [findSpec, List.isSome_find?, List.any_eq_true, beq_iff_eq, spec]
  constructor
  · rintro ⟨x, hx, he⟩; have : x = k := digest256_toNat_injective he; simpa [this] using hx
  · intro hk; exact ⟨k, hk, rfl⟩

@[simp] theorem SortedDigestSet.spec_insert (s : SortedDigestSet) (k x : Digest256) :
    (s.insert k).spec x ↔ x = k ∨ s.spec x := by simp [insert, spec]

theorem SortedDigestSet.contains_list (s : SortedDigestSet) (k : Digest256) :
    s.contains k = s.data.toList.contains k := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_spec]
  simp only [spec, List.contains_iff_mem]

/-- Removal only filters existing keys, preserving strict ordering. -/
def SortedDigestSet.erase (s : SortedDigestSet) (k : Digest256) : SortedDigestSet :=
  ⟨(s.data.toList.filter (· != k)).toArray, by
    simpa using s.sorted.filter (fun x => x != k)⟩

@[simp] theorem SortedDigestSet.spec_erase (s : SortedDigestSet) (k x : Digest256) :
    (s.erase k).spec x ↔ s.spec x ∧ x ≠ k := by
  simp [erase, spec]

/-- Sorted union by insertion; linear membership specification. The persistent arrays
are rebuilt at writes, whereas all online membership queries are logarithmic. -/
def SortedDigestSet.merge (a b : SortedDigestSet) : SortedDigestSet :=
  b.data.toList.foldl SortedDigestSet.insert a

theorem SortedDigestSet.merge_spec (a b : SortedDigestSet) (k : Digest256) :
    (a.merge b).spec k ↔ a.spec k ∨ b.spec k := by
  unfold merge
  have aux : ∀ (xs : List Digest256) (s : SortedDigestSet),
      (xs.foldl SortedDigestSet.insert s).spec k ↔ s.spec k ∨ k ∈ xs := by
    intro xs
    induction xs with
    | nil => intro s; simp
    | cons x xs ih => intro s; simp only [List.foldl_cons, ih, SortedDigestSet.spec_insert,
        List.mem_cons]; grind
  exact aux _ _

abbrev SwissNum := Digest256
structure SturdyEntry where
  swissNum : SwissNum
  mandate : Mandate
  expectedNonce : UInt64
  expiresAt : Nat
  revoked : Bool

inductive WireLookupResp where
  | granted (mandate : Mandate)
  | denied

abbrev SwissTableSpec := List SturdyEntry
structure SwissTableExec where
  entries : Array SturdyEntry
  seenNonces : SortedU64Set

def WFSwissTable (t : SwissTableExec) : Prop := SortedBy (·.swissNum.toNat) t.entries

/-- The only negative wire constructor carries no reason code. Timing is outside this
observational equality theorem; deploy behind an independently padded transport. -/
@[expose] def authorizeEntry (now : Nat) (nonce : UInt64) (replayed : Bool) :
    Option SturdyEntry → WireLookupResp
  | none => .denied
  | some e =>
    if !replayed && !e.revoked && decide (now ≤ e.expiresAt) && (nonce == e.expectedNonce)
    then .granted e.mandate else .denied

def lookupSwissSpec (t : SwissTableSpec) (seen : List UInt64) (k : SwissNum) (now : Nat)
    (nonce : UInt64) : WireLookupResp :=
  authorizeEntry now nonce (seen.contains nonce) (t.find? (fun e => e.swissNum.toNat == k.toNat))

def lookupSwissExec (t : SwissTableExec) (k : SwissNum) (now : Nat)
    (nonce : UInt64) : WireLookupResp :=
  authorizeEntry now nonce (t.seenNonces.contains nonce)
    (search (·.swissNum.toNat) t.entries k.toNat (t.entries.size + 1) 0 t.entries.size)

theorem lookupSwissExec_eq_spec (t : SwissTableExec) (hw : WFSwissTable t)
    (k : SwissNum) (now : Nat) (nonce : UInt64) :
    lookupSwissExec t k now nonce =
      lookupSwissSpec t.entries.toList t.seenNonces.data.toList k now nonce := by
  unfold lookupSwissExec lookupSwissSpec
  rw [search_eq_spec _ _ hw, SortedU64Set.contains_list]
  rfl

def InvalidLookup (now : Nat) (nonce : UInt64) (replayed : Bool) : Option SturdyEntry → Prop
  | none => True
  | some e => replayed = true ∨ e.revoked = true ∨ e.expiresAt < now ∨ nonce ≠ e.expectedNonce

theorem swissTable_no_membership_oracle (now : Nat) (nonce : UInt64) (replayed : Bool)
    (entry : Option SturdyEntry) (h : InvalidLookup now nonce replayed entry) :
    authorizeEntry now nonce replayed entry = .denied := by
  cases entry with
  | none => rfl
  | some e =>
    rcases h with h | h | h | h <;> simp [authorizeEntry, h, Nat.not_le_of_gt] <;> omega


theorem lookupSwissExec_invalid_denied (t : SwissTableExec) (hw : WFSwissTable t)
    (k : SwissNum) (now : Nat) (nonce : UInt64)
    (h : InvalidLookup now nonce (t.seenNonces.data.toList.contains nonce)
      (findSpec (·.swissNum.toNat) t.entries k.toNat)) :
    lookupSwissExec t k now nonce = .denied := by
  rw [lookupSwissExec_eq_spec t hw]
  exact swissTable_no_membership_oracle _ _ _ _ h

theorem swissTable_observational_equivalence (a b : SwissTableExec)
    (ha : WFSwissTable a) (hb : WFSwissTable b) (k : SwissNum) (now : Nat) (nonce : UInt64)
    (ia : InvalidLookup now nonce (a.seenNonces.data.toList.contains nonce)
      (findSpec (·.swissNum.toNat) a.entries k.toNat))
    (ib : InvalidLookup now nonce (b.seenNonces.data.toList.contains nonce)
      (findSpec (·.swissNum.toNat) b.entries k.toNat)) :
    lookupSwissExec a k now nonce = lookupSwissExec b k now nonce := by
  rw [lookupSwissExec_invalid_denied a ha k now nonce ia,
    lookupSwissExec_invalid_denied b hb k now nonce ib]


/-- Gift nullifiers of `Obend.Polis.GrainPowerbox` (64-bit gift ids). Promise ids and their
spends use `SortedDigestSet` (`GuardedHole`). -/
abbrev NullifierSet := SortedU64Set


structure HybridIdentity where
  classicalKey : ByteArray
  mlDsa65Key : ByteArray

def hybridIdentityDigest (id : HybridIdentity) : ByteArray :=
  cshake32ByteArray "obend.captp.hybrid-id.v1".toUTF8.data.toList
    (encodeFrame id.classicalKey id.mlDsa65Key ByteArray.empty).data.toList

structure HybridSigVerifier where
  classical : ByteArray → ByteArray → ByteArray → Bool
  mlDsa65 : ByteArray → ByteArray → ByteArray → Bool

structure HybridSignature where
  classical : ByteArray
  mlDsa65 : ByteArray

@[expose] def verifyBoth (v : HybridSigVerifier) (id : HybridIdentity)
    (msg : ByteArray) (sig : HybridSignature) : Bool :=
  v.classical id.classicalKey msg sig.classical && v.mlDsa65 id.mlDsa65Key msg sig.mlDsa65

/-- A serializable caveat language: a finite method allow-list. The inherited caveat
is conjoined by Mandate.delegate, not guessed by a Boolean attenuation oracle. -/
structure DelegationRequest where
  childId : Nat
  recipient : Principal
  rights : List Auth
  quota : Nat
  cells : List Nat
  expiresAt : Nat
  methods : List Nat

def DelegationRequest.granted (r : DelegationRequest) (held : Mandate) : Mandate :=
  (held.delegate r.childId r.recipient r.rights r.quota r.cells r.expiresAt
    ⟨fun m => r.methods.contains m⟩).2

def encodeNats (ns : List Nat) : ByteArray :=
  Obend.Digest.Cshake256.Native.bytesOfList
    (leb128 ns.length ++ ns.flatMap (fun n => encodeListField (leb128 n)))

def authCode : Auth → Nat
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7

def DelegationRequest.bytes (r : DelegationRequest) : ByteArray :=
  encodeFrame (encodeNats [r.childId, r.recipient.id, r.quota, r.expiresAt])
    (encodeStringCodepoints r.recipient.name)
    (encodeFrame (encodeNats (r.rights.map authCode)) (encodeNats r.cells) (encodeNats r.methods))

/-- `handoffNonce` is a 256-bit replay key. `msgEpoch` is the sender's message epoch; it is bound
inside both signed messages and must be nonzero (epoch 0 is the unauthenticated default). -/
structure HybridHandoffCert where
  vatId : ByteArray
  sessionId : ByteArray
  handoffNonce : Digest256
  msgEpoch : UInt64
  introducer : HybridIdentity
  recipient : HybridIdentity
  request : DelegationRequest
  giveSig : HybridSignature
  acceptSig : HybridSignature

/-- The held capability commitment is supplied by Bob's authenticated capability
store; it is not a digest asserted by the certificate. Both roles bind both identities,
the full 256-bit nonce, and the message epoch. -/
def handoffMessage (role : String) (heldCommitment : ByteArray) (c : HybridHandoffCert) : ByteArray :=
  encodeFrame role.toUTF8
    (encodeFrame c.vatId c.sessionId (encodeNats [c.handoffNonce.toNat, c.msgEpoch.toNat]))
    (encodeFrame heldCommitment c.request.bytes
      (encodeFrame (hybridIdentityDigest c.introducer) (hybridIdentityDigest c.recipient) ByteArray.empty))

theorem leb128_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

/-- The signed handoff bytes determine the full 256-bit nonce and the message epoch. -/
theorem handoffMessage_binds_nonce_epoch {role : String} {hc : ByteArray}
    {c₁ c₂ : HybridHandoffCert} (h : handoffMessage role hc c₁ = handoffMessage role hc c₂) :
    c₁.handoffNonce = c₂.handoffNonce ∧ c₁.msgEpoch = c₂.msgEpoch := by
  obtain ⟨-, h2, -⟩ := encodeFrame_injective h
  obtain ⟨-, -, h3⟩ := encodeFrame_injective h2
  have hl := congrArg (fun x : ByteArray => x.data.toList) h3
  simp only [encodeNats, Obend.Digest.Cshake256.Native.bytesOfList_toList, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] at hl
  obtain ⟨-, hl⟩ := leb128_prefix_inj hl
  obtain ⟨hn, he⟩ := encodeListField_prefix_inj hl
  obtain ⟨he, -⟩ := encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa using he)
  exact ⟨digest256_toNat_injective (leb128_injective hn), UInt64.toNat_inj.mp (leb128_injective he)⟩

def requestFits (r : DelegationRequest) (held : Mandate) : Bool :=
  r.rights.all held.rights.contains && decide (r.quota ≤ held.budget) &&
    r.cells.all held.cells.contains && decide (r.expiresAt ≤ held.expiresAt)

@[expose] def verifyHybridHandoff (v : HybridSigVerifier) (held : Mandate)
    (heldCommitment introducerDigest recipientDigest : ByteArray) (seen : SortedDigestSet)
    (c : HybridHandoffCert) : Bool :=
  decide (hybridIdentityDigest c.introducer = introducerDigest) &&
  decide (hybridIdentityDigest c.recipient = recipientDigest) &&
  verifyBoth v c.introducer (handoffMessage "HandoffGive" heldCommitment c) c.giveSig &&
  verifyBoth v c.recipient (handoffMessage "HandoffAccept" heldCommitment c) c.acceptSig &&
  !seen.contains c.handoffNonce && requestFits c.request held && c.msgEpoch != 0

def acceptHandoff (v : HybridSigVerifier) (held : Mandate)
    (hc ai ci : ByteArray) (seen : SortedDigestSet) (c : HybridHandoffCert) :
    Option (Mandate × SortedDigestSet) :=
  if verifyHybridHandoff v held hc ai ci seen c then
    some (c.request.granted held, seen.insert c.handoffNonce) else none

theorem verifyHybridHandoff_sound (v : HybridSigVerifier) (held : Mandate)
    (hc ai ci : ByteArray) (seen : SortedDigestSet) (c : HybridHandoffCert)
    (h : verifyHybridHandoff v held hc ai ci seen c = true) :
    hybridIdentityDigest c.introducer = ai ∧ hybridIdentityDigest c.recipient = ci ∧
    v.classical c.introducer.classicalKey (handoffMessage "HandoffGive" hc c) c.giveSig.classical = true ∧
    v.mlDsa65 c.introducer.mlDsa65Key (handoffMessage "HandoffGive" hc c) c.giveSig.mlDsa65 = true ∧
    v.classical c.recipient.classicalKey (handoffMessage "HandoffAccept" hc c) c.acceptSig.classical = true ∧
    v.mlDsa65 c.recipient.mlDsa65Key (handoffMessage "HandoffAccept" hc c) c.acceptSig.mlDsa65 = true ∧
    ¬ seen.spec c.handoffNonce ∧ c.msgEpoch ≠ 0 ∧ attenuates (c.request.granted held) held := by
  simp only [verifyHybridHandoff, verifyBoth, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', bne_iff_ne] at h
  refine ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2.1, h.1.1.1.1.2.2,
    h.1.1.1.2.1, h.1.1.1.2.2, ?_, h.2, ?_⟩
  · intro hm
    have := (seen.contains_eq_spec _).mpr hm
    rw [h.1.1.2] at this; cases this
  · exact delegate_child_attenuates _ _ _ _ _ _ _ _

theorem verifyHybridHandoff_complete (v : HybridSigVerifier) (held : Mandate)
    (hc : ByteArray) (seen : SortedDigestSet) (c : HybridHandoffCert)
    (hg : verifyBoth v c.introducer (handoffMessage "HandoffGive" hc c) c.giveSig = true)
    (ha : verifyBoth v c.recipient (handoffMessage "HandoffAccept" hc c) c.acceptSig = true)
    (hf : ¬seen.spec c.handoffNonce) (hr : requestFits c.request held = true)
    (he : c.msgEpoch ≠ 0) :
    verifyHybridHandoff v held hc (hybridIdentityDigest c.introducer)
      (hybridIdentityDigest c.recipient) seen c = true := by
  have hn : seen.contains c.handoffNonce = false := by
    cases h : seen.contains c.handoffNonce
    · rfl
    · exact False.elim (hf ((seen.contains_eq_spec _).mp h))
  have hb : (c.msgEpoch != 0) = true := bne_iff_ne.mpr he
  simp only [verifyHybridHandoff, decide_true, hg, ha, hn, hr, hb,
    Bool.not_false, Bool.and_true, eq_self]

/-- A certificate at the default epoch 0 is refused whatever its signatures. -/
theorem verifyHybridHandoff_rejects_epoch_zero (v : HybridSigVerifier) (held : Mandate)
    (hc ai ci : ByteArray) (seen : SortedDigestSet) (c : HybridHandoffCert)
    (h0 : c.msgEpoch = 0) : verifyHybridHandoff v held hc ai ci seen c = false := by
  simp [verifyHybridHandoff, h0]

theorem verifyHybridHandoff_no_replay (v : HybridSigVerifier) (held : Mandate)
    (hc ai ci : ByteArray) (seen : SortedDigestSet) (c : HybridHandoffCert) :
    verifyHybridHandoff v held hc ai ci (seen.insert c.handoffNonce) c = false := by
  have hm : (seen.insert c.handoffNonce).contains c.handoffNonce = true :=
    ((seen.insert c.handoffNonce).contains_eq_spec _).mpr (by simp)
  simp [verifyHybridHandoff, hm]

theorem handoff_authorizedBy_held (v : HybridSigVerifier) (held : Mandate)
    (hc ai ci : ByteArray) (seen : SortedDigestSet) (c : HybridHandoffCert) (inv : Invocation)
    (hv : verifyHybridHandoff v held hc ai ci seen c = true)
    (ha : authorizedBy (c.request.granted held) inv = true) : authorizedBy held inv = true :=
  authorizedBy_attenuates (verifyHybridHandoff_sound v held hc ai ci seen c hv).2.2.2.2.2.2.2.2 ha


theorem hybridHandoff_fails_closed_classical_or_pq (v : HybridSigVerifier)
    (id : HybridIdentity) (msg : ByteArray) (sig : HybridSignature)
    (h : v.classical id.classicalKey msg sig.classical = false ∨
      v.mlDsa65 id.mlDsa65Key msg sig.mlDsa65 = false) : verifyBoth v id msg sig = false := by
  rcases h with h | h <;> simp [verifyBoth, h]

abbrev PendingId := Digest256
/-- Promise ids and their spend nullifiers are 256-bit (`PendingId = Digest256`). -/
structure GuardedHole where
  openPromises : SortedDigestSet
  spentNullifiers : SortedDigestSet

def GuardedHole.WellFormed (s : GuardedHole) : Prop :=
  ∀ k, s.openPromises.spec k → ¬s.spentNullifiers.spec k


def allocatePromise (s : GuardedHole) (k : PendingId) : GuardedHole :=
  if s.spentNullifiers.contains k then s
  else { s with openPromises := s.openPromises.insert k }

theorem allocate_preserves_disjoint (s : GuardedHole) (k : PendingId) (h : s.WellFormed) :
    (allocatePromise s k).WellFormed := by
  unfold allocatePromise
  split
  · exact h
  · rename_i hn
    intro x hx hs
    rcases (SortedDigestSet.spec_insert _ _ _).mp hx with he | hm
    · subst x
      exact hn ((s.spentNullifiers.contains_eq_spec k).mpr hs)
    · exact h x hm hs


@[expose] def resolvePromise (s : GuardedHole) (k : PendingId) : Option GuardedHole :=
  if s.spentNullifiers.contains k || !s.openPromises.contains k then none
  else some ⟨s.openPromises.erase k, s.spentNullifiers.insert k⟩

theorem resolve_spends (s t : GuardedHole) (k : PendingId)
    (h : resolvePromise s k = some t) : t.spentNullifiers.spec k := by
  unfold resolvePromise at h
  split at h
  · cases h
  · cases Option.some.inj h
    simp

theorem resolve_preserves_disjoint (s t : GuardedHole) (k : PendingId)
    (hw : s.WellFormed) (h : resolvePromise s k = some t) : t.WellFormed := by
  unfold resolvePromise at h
  split at h
  · cases h
  · cases Option.some.inj h
    intro x hx hs
    obtain ⟨hm, hn⟩ := (SortedDigestSet.spec_erase _ _ _).mp hx
    rcases (SortedDigestSet.spec_insert _ _ _).mp hs with he | hs
    · exact hn he
    · exact hw x hm hs


theorem resolve_refuses_spent (s : GuardedHole) (k : PendingId)
    (h : s.spentNullifiers.spec k) : resolvePromise s k = none := by
  simp [resolvePromise, (s.spentNullifiers.contains_eq_spec k).mpr h]

def pushout (s : GuardedHole) (remote : SortedDigestSet) : GuardedHole :=
  let spent := s.spentNullifiers.merge remote
  ⟨⟨(s.openPromises.data.toList.filter (fun k => !spent.contains k)).toArray,
      by simpa using s.openPromises.sorted.filter (fun k => !spent.contains k)⟩, spent⟩

theorem pushout_disjoint (s : GuardedHole) (remote : SortedDigestSet) :
    (pushout s remote).WellFormed := by
  intro k hk hs
  have hc := ((s.spentNullifiers.merge remote).contains_eq_spec k).mpr hs
  simp only [pushout, SortedDigestSet.spec, List.toList_toArray, List.mem_filter] at hk
  simp [hc] at hk


theorem pushout_refuses_replay (s : GuardedHole) (remote : SortedDigestSet) (k : PendingId)
    (h : s.spentNullifiers.spec k ∨ remote.spec k) :
    resolvePromise (pushout s remote) k = none :=
  resolve_refuses_spent _ _ ((SortedDigestSet.merge_spec _ _ _).mpr h)

inductive PromiseEvent where
  | allocate (id : PendingId)
  | deliver (dependency : PendingId)
  | resolve (id : PendingId)
  | merge (spent : SortedDigestSet)

def promiseStep (s : GuardedHole) : PromiseEvent → GuardedHole × Option PendingId
  | .allocate k => (allocatePromise s k, none)
  | .deliver _ => (s, none)
  | .resolve k => match resolvePromise s k with
    | none => (s, none)
    | some t => (t, some k)
  | .merge spent => (pushout s spent, none)

/-- Counts successful deliveries on one causally serialized settlement trace. A merge
imports spends, never removes them. Concurrent speculative resolutions on two forks
are NOT globally unique until settlement; no theorem claims otherwise. -/
def countResolved (s : GuardedHole) (trace : List PromiseEvent) (k : PendingId) : Nat :=
  match trace with
  | [] => 0
  | e :: es => let (t, out) := promiseStep s e
    (if out = some k then 1 else 0) + countResolved t es k

theorem step_preserves_spent (s : GuardedHole) (e : PromiseEvent) (k : PendingId)
    (h : s.spentNullifiers.spec k) : (promiseStep s e).1.spentNullifiers.spec k := by
  cases e with
  | allocate j => simp only [promiseStep, allocatePromise]; split <;> exact h
  | deliver j => exact h
  | merge r => exact (SortedDigestSet.merge_spec _ _ _).mpr (.inl h)
  | resolve j =>
    simp only [promiseStep]
    split
    · exact h
    · rename_i t ht
      unfold resolvePromise at ht
      split at ht
      · cases ht
      · cases Option.some.inj ht
        exact (SortedDigestSet.spec_insert _ _ _).mpr (.inr h)

theorem step_resolution (s : GuardedHole) (e : PromiseEvent) (k : PendingId)
    (h : (promiseStep s e).2 = some k) :
    ¬s.spentNullifiers.spec k ∧ (promiseStep s e).1.spentNullifiers.spec k := by
  cases e <;> simp only [promiseStep] at h ⊢ <;> try contradiction
  rename_i j
  split at h
  · cases h
  · rename_i t ht
    have he := Option.some.inj h
    subst j
    simp only
    refine ⟨?_, resolve_spends s t k ht⟩
    intro hs
    rw [resolve_refuses_spent s k hs] at ht
    cases ht

theorem spent_count_zero (s : GuardedHole) (trace : List PromiseEvent) (k : PendingId)
    (h : s.spentNullifiers.spec k) : countResolved s trace k = 0 := by
  induction trace generalizing s with
  | nil => rfl
  | cons e es ih =>
    have hn : (promiseStep s e).2 ≠ some k := fun he => (step_resolution s e k he).1 h
    simp [countResolved, hn, ih _ (step_preserves_spent s e k h)]

theorem guardedHole_resolve_at_most_once (s : GuardedHole) (trace : List PromiseEvent)
    (k : PendingId) : countResolved s trace k ≤ 1 := by
  induction trace generalizing s with
  | nil => simp [countResolved]
  | cons e es ih =>
    by_cases h : (promiseStep s e).2 = some k
    · have hz := spent_count_zero (promiseStep s e).1 es k (step_resolution s e k h).2
      simp [countResolved, h, hz]
    · simpa [countResolved, h] using ih (promiseStep s e).1

end Obend.Polis.CapTP
