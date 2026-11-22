module
/-
# Obend.Polis.JointCoReceipt — joint turns across vats, and receipts that compose along promises
A turn that touches several vats leaves one local receipt in each. This module says when those
receipts are one turn, how a turn moves a `FloorBook`, and how receipts with open promise ports
compose into one.
1. Sorted tables: `tableOk (sortByKey …)` is key distinctness; lookup is CapTP's binary search.
2. `LocalTurn`, `JointTurn`: a local receipt checks its own arithmetic (`post = pre + half`, neither
   balance negative) and commits to a turn digest. A joint turn is the pullback of the receipts over
   that digest (`SharedTurnId`: every leg names one 32-byte cSHAKE256 digest, and it is the digest of
   this forest of legs), with distinct vats and half-edges summing to zero. A leg's digest bytes
   frame its vat, effects commitment, `pre`, half-edge and `post`; `coReceiptDigest_binds` and
   `sharedTurnId_binds_forest` bind every field. `tensor_not_final`: valid local receipts do not
   make a joint turn.
3. The ledger is a `Obend.Ledger.FloorBook`: a vat's balance is its user account's
   (`LedgerState.balances`). `stepJoint` refuses a replayed digest, a vat outside the ledger and a
   `pre` that is not the vat's balance, then runs `FloorBook.admitBatch` on the turn's typed postings
   through a per-turn escrow account. `stepJoint_refines_floorBook`, `stepJoint_complete`,
   `stepJoint_conserves`, `stepJoint_no_overdraft`, the three refusals, and the lifts over
   `ValidJointTrace` (`jointTrace_conserves_total_balance`, `jointTrace_no_overdraft`,
   `jointTrace_preserves_floors`, `jointTrace_no_replay`).
4. `jointTurn_committed_conservation_sound`: cSHAKE opening correspondence and natural-number
   conservation checked together; no external blinding-balance premise.
5. `CoReceipt`: a receipt with typed open ports. An `AwaitPort` is a promise hole (a CapTP pending
   id, a 32-byte commitment to the awaited payload, a `DistPred` guard, and the root grant and rights
   its resolver must show); a `FulfillPort` resolves one, carrying a delegation chain.
   `composeCoReceipts` sorts both port tables (strictly ascending ids, so no hole is allocated or
   filled twice), finds each fulfilment's hole by binary search, and checks the payload, the guard,
   the causal rank and the chain (`foldChain`: attenuation, caveats, and no revoked lineage or
   channel on any prefix). `promise_hole_no_double_fill`, `cyclic_wiring_refused`,
   `revoked_lineage_refused`, and `composeCoReceipts_closed_sound`: a composite with no open port is
   a joint turn in which every hole is filled exactly once by an authorized, unrevoked, causally
   earlier resolver.
-/
public import Obend.Consensus.SimplexProtocol
public import Obend.Polis.PrivatePredicate
public import Obend.Polis.CapTP
public import Obend.Polis.ZkBiscuit
public import Obend.Ledger.Floors
import all Obend.Polis.CapTP
public section
namespace Obend.Polis.JointCoReceipt
open Obend.Polis
open Obend.Polis.PrivatePredicate
open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Ledger (FloorBook FloorsHold AccountAddr AccountKind TypedPosting AssetId)
set_option autoImplicit false
/-! ## 1. Sorted tables -/
/-- Strictly ascending, checked on neighbours. -/
def ascending : List Nat → Bool
  | a :: b :: rest => decide (a < b) && ascending (b :: rest)
  | _ => true
theorem ascending_cons {a : Nat} : ∀ {l : List Nat}, ascending (a :: l) = true →
    (∀ x, x ∈ l → a < x) ∧ ascending l = true
  | [], _ => ⟨fun _ hx => (by cases hx), by rfl⟩
  | b :: l, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, _⟩ := ascending_cons h.2
    refine ⟨fun x hx => ?_, h.2⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (hlt x hx)
theorem ascending_pairwise : ∀ l : List Nat, ascending l = true → l.Pairwise (· < ·)
  | [], _ => .nil
  | _ :: l, h => .cons (ascending_cons h).1 (ascending_pairwise l (ascending_cons h).2)
theorem ascending_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → ascending l = true
  | [], _ => by rfl
  | [_], _ => by rfl
  | a :: b :: l, h => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨ha b (by simp), ascending_of_pairwise (b :: l) hl⟩
section Table
variable {α : Type} (key : α → Nat)
/-- A table in key order: one merge sort. -/
def sortByKey (l : List α) : Array α :=
  (l.mergeSort (fun a b => decide (key a ≤ key b))).toArray
/-- The table's keys strictly ascend: no key occurs twice. One pass. -/
def tableOk (A : Array α) : Bool := ascending (A.toList.map key)
/-- Find the entry with key `k` by CapTP's binary search. -/
def lookup (A : Array α) (k : Nat) : Option α := CapTP.search key A k (A.size + 1) 0 A.size
theorem sortByKey_perm (l : List α) : (sortByKey key l).toList.Perm l := by
  simpa only [sortByKey, List.toList_toArray] using
    List.mergeSort_perm l (fun a b => decide (key a ≤ key b))
theorem tableOk_pairwise {A : Array α} (h : tableOk key A = true) :
    A.toList.Pairwise (fun a b => key a < key b) :=
  List.pairwise_map.1 (ascending_pairwise _ h)
theorem tableOk_nodup {A : Array α} (h : tableOk key A = true) : (A.toList.map key).Nodup :=
  (ascending_pairwise _ h).imp (fun hlt => Nat.ne_of_lt hlt)
theorem pairwise_key_unique : ∀ {l : List α}, l.Pairwise (fun a b => key a < key b) →
    ∀ {x y : α}, x ∈ l → y ∈ l → key x = key y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, hp, x, y, hx, hy, hk => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · have := ha y hy'
      omega
    · have := ha x hx'
      omega
    · exact pairwise_key_unique hl hx' hy' hk
/-- On a table that passed `tableOk`, the binary search is the list search. -/
theorem lookup_eq_find {A : Array α} (h : tableOk key A = true) (k : Nat) :
    lookup key A k = A.toList.find? (fun x => key x == k) := by
  have hs : CapTP.SortedBy key A := by
    intro i j hi hj hij
    have := List.pairwise_iff_getElem.1 (tableOk_pairwise key h) i j (by simpa using hi)
      (by simpa using hj) hij
    simpa using this
  rw [lookup, CapTP.search_eq_spec key A hs k, CapTP.findSpec]
theorem lookup_some {A : Array α} (h : tableOk key A = true) {k : Nat} {x : α}
    (hx : lookup key A k = some x) : x ∈ A.toList ∧ key x = k := by
  rw [lookup_eq_find key h] at hx
  exact ⟨List.mem_of_find?_eq_some hx, by simpa using List.find?_some hx⟩
theorem lookup_of_mem {A : Array α} (h : tableOk key A = true) {x : α} (hx : x ∈ A.toList) :
    lookup key A (key x) = some x := by
  rw [lookup_eq_find key h]
  cases hf : A.toList.find? (fun y => key y == key x) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    simp at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hk : key y = key x := by simpa using List.find?_some hf
    rw [pairwise_key_unique key (tableOk_pairwise key h) hy hx hk]
/-- **The sort-and-scan check is key distinctness.** A list's sorted table strictly ascends exactly
when no key occurs twice in the list. -/
theorem tableOk_sortByKey_iff (l : List α) :
    tableOk key (sortByKey key l) = true ↔ (l.map key).Nodup := by
  constructor
  · intro h
    exact ((sortByKey_perm key l).map key).nodup_iff.1 (tableOk_nodup key h)
  · intro h
    have hnd : ((sortByKey key l).toList.map key).Nodup :=
      ((sortByKey_perm key l).map key).nodup_iff.2 h
    have hle : (sortByKey key l).toList.Pairwise (fun a b => key a ≤ key b) := by
      have hs := List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
        (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
      simpa only [sortByKey, List.toList_toArray, decide_eq_true_eq] using hs
    exact ascending_of_pairwise _ (List.pairwise_map.2
      ((hle.and (List.pairwise_map.1 hnd)).imp fun hab => Nat.lt_of_le_of_ne hab.1 hab.2))
end Table
theorem nodup_of_map_nodup {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) :
    l.Nodup :=
  (List.pairwise_map.1 h).imp (fun hne heq => hne (congrArg f heq))
/-! ## 2. Local receipts and the joint turn -/
/-- A vat. -/
abbrev VatId := Nat
/-- One vat's receipt of a turn: the turn digest it commits to, a 32-byte commitment to its local
effects, and its balance before, its half-edge, and its balance after. -/
structure LocalTurn where
  vat : VatId
  turnId : ByteArray
  body : ByteArray
  pre : Int
  half : Int
  post : Int
  asset : AssetId := 0
  epoch : Nat := 0
  nonce : Nat := 0
/-- The receipt's own arithmetic: the balance after is the balance before plus the half-edge, and
neither balance is negative. -/
def LocalTurn.valid (t : LocalTurn) : Bool :=
  decide (t.post = t.pre + t.half) && decide (0 ≤ t.pre) && decide (0 ≤ t.post)
theorem LocalTurn.valid_iff (t : LocalTurn) :
    t.valid = true ↔ t.post = t.pre + t.half ∧ 0 ≤ t.pre ∧ 0 ≤ t.post := by
  simp only [LocalTurn.valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
/-- What a leg contributes to the turn digest: the vat, its effects commitment, and its balance
before, half-edge and balance after, each length-prefixed. -/
def LocalTurn.legBytes (t : LocalTurn) : List UInt8 :=
  encodeFields [leb128 t.vat, t.body.data.toList, encodeInt t.pre, encodeInt t.half,
    encodeInt t.post, leb128 t.asset, leb128 t.epoch, leb128 t.nonce]
theorem LocalTurn.legBytes_inj {a b : LocalTurn} (h : a.legBytes = b.legBytes) :
    a.vat = b.vat ∧ a.body = b.body ∧ a.pre = b.pre ∧ a.half = b.half ∧ a.post = b.post ∧
      a.asset = b.asset ∧ a.epoch = b.epoch ∧ a.nonce = b.nonce := by
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have hint : ∀ {x y : Int}, encodeInt x = encodeInt y → x = y := fun {x y} e =>
    (encodeInt_prefix_inj (r₁ := []) (r₂ := []) (by rw [List.append_nil, List.append_nil, e])).1
  exact ⟨(leb128_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hf.1])).1,
    byteArray_eq_of_toList_eq hf.2.1, hint hf.2.2.1, hint hf.2.2.2.1, hint hf.2.2.2.2.1,
    (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hf.2.2.2.2.2.1)).1,
    (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hf.2.2.2.2.2.2.1)).1,
    (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hf.2.2.2.2.2.2.2)).1⟩
/-- Two receipts of one turn with the same leg bytes are the same receipt. -/
theorem LocalTurn.eq_of_legBytes {a b : LocalTurn} (hid : a.turnId = b.turnId)
    (h : a.legBytes = b.legBytes) : a = b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LocalTurn.legBytes_inj h
  clear h
  cases a; cases b
  simp_all
/-- Everything a receipt says: the turn digest it names, then its leg bytes. -/
def LocalTurn.receiptBytes (t : LocalTurn) : List UInt8 :=
  encodeFields [t.turnId.data.toList, t.legBytes]
theorem LocalTurn.receiptBytes_inj {a b : LocalTurn} (h : a.receiptBytes = b.receiptBytes) :
    a = b := by
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  exact LocalTurn.eq_of_legBytes (byteArray_eq_of_toList_eq hf.1) hf.2
/-- Customization string of the receipt digest. -/
def receiptCustomization : List UInt8 := "OBEND.POLIS.CORECEIPT/v1".toUTF8.data.toList
/-- The 32-byte digest of one vat's receipt. -/
def coReceiptDigest (t : LocalTurn) : ByteArray :=
  cshake32ByteArray receiptCustomization t.receiptBytes
/-- **The receipt digest binds the whole receipt**: vat, turn digest, effects commitment, balance
before, half-edge and balance after. Equal digests come from equal receipts, or the two receipts'
bytes collide. -/
def coReceiptDigest_extract {a b : LocalTurn} (h : coReceiptDigest a = coReceiptDigest b) :
    PSum (PLift (a = b)) (CollisionPair (cshake256Bytes receiptCustomization)
      (fun x => x = a.receiptBytes ∨ x = b.receiptBytes)) :=
  extractBinding _ _ _ LocalTurn.receiptBytes_inj (by
    have hl := congrArg (fun b : ByteArray => b.data.toList) h
    simp only [coReceiptDigest, cshake32ByteArray, Native.bytesOfList_toList] at hl
    exact congrArg ofBE hl)
theorem coReceiptDigest_binds {a b : LocalTurn} (h : coReceiptDigest a = coReceiptDigest b) :
    a = b ∨ CollisionAmong (cshake256Bytes receiptCustomization)
      (fun x => x = a.receiptBytes ∨ x = b.receiptBytes) :=
  bindingResult (coReceiptDigest_extract h)
/-- Customization string of the turn digest. -/
def turnCustomization : List UInt8 := "OBEND.POLIS.JOINTTURN/v1".toUTF8.data.toList
/-- The digest of a forest of legs, each length-prefixed. -/
def forestDigest (legs : List (List UInt8)) : ByteArray :=
  cshake32ByteArray turnCustomization (encodeFields legs)
/-- One digest names one forest, or the two forests collide. -/
theorem forestDigest_binds {a b : List (List UInt8)} (h : forestDigest a = forestDigest b) :
    a = b ∨ CollisionAmong (cshake256Bytes turnCustomization)
      (fun x => x = encodeFields a ∨ x = encodeFields b) := by
  rcases cshake32_binds turnCustomization h with hp | hc
  · exact .inl (encodeFields_injective _ _ hp)
  · exact .inr hc
/-- The turn digest of a list of local receipts. -/
def turnDigest (legs : List LocalTurn) : ByteArray := forestDigest (legs.map LocalTurn.legBytes)
/-- Receipts naming one turn digest, with the same leg bytes in order, are the same receipts. -/
theorem legs_eq_of_legBytes (tid : ByteArray) : ∀ (l₁ l₂ : List LocalTurn),
    (∀ t, t ∈ l₁ → t.turnId = tid) → (∀ t, t ∈ l₂ → t.turnId = tid) →
      l₁.map LocalTurn.legBytes = l₂.map LocalTurn.legBytes → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [LocalTurn.eq_of_legBytes ((h₁ a (by simp)).trans (h₂ b (by simp)).symm) h.1,
      legs_eq_of_legBytes tid l₁ l₂ (fun t ht => h₁ t (by simp [ht]))
        (fun t ht => h₂ t (by simp [ht])) h.2]
/-- **The pullback over the turn digest.** Every leg commits to `tid`, and `tid` is the digest of
exactly these legs: a receipt is a receipt of this turn and of no other. -/
structure SharedTurnId (legs : List LocalTurn) where
  tid : ByteArray
  agree : ∀ t, t ∈ legs → t.turnId = tid
  pinned : tid = turnDigest legs
/-- A joint turn: receipts that are each valid and non-negative, agree on the turn, come from
distinct vats, and conserve between them. -/
structure JointTurn where
  legs : List LocalTurn
  shared : SharedTurnId legs
  valid : ∀ t, t ∈ legs → t.post = t.pre + t.half
  nonneg : ∀ t, t ∈ legs → 0 ≤ t.pre ∧ 0 ≤ t.post
  distinct : (legs.map (·.vat)).Nodup
  balanced : (legs.map (·.half)).sum = 0
/-- No vat has two legs: one sort and one scan. -/
def vatsDistinct (legs : List LocalTurn) : Bool :=
  tableOk (fun t : LocalTurn => t.vat) (sortByKey (fun t : LocalTurn => t.vat) legs)
theorem vatsDistinct_iff (legs : List LocalTurn) :
    vatsDistinct legs = true ↔ (legs.map (·.vat)).Nodup :=
  tableOk_sortByKey_iff _ legs
/-- The checker for a joint turn. -/
def checkJoint (shared : ByteArray) (legs : List LocalTurn) : Bool :=
  legs.all (·.valid) && vatsDistinct legs && legs.all (fun t => decide (t.turnId = shared)) &&
    decide (shared = turnDigest legs) && decide ((legs.map (·.half)).sum = 0)
/-- **The checker accepts exactly the joint turns.** -/
theorem checkJoint_iff (shared : ByteArray) (legs : List LocalTurn) :
    checkJoint shared legs = true ↔ ∃ j : JointTurn, j.legs = legs ∧ j.shared.tid = shared := by
  constructor
  · intro h
    simp only [checkJoint, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      LocalTurn.valid_iff] at h
    obtain ⟨⟨⟨⟨hv, hd⟩, ha⟩, hp⟩, hb⟩ := h
    exact ⟨⟨legs, ⟨shared, ha, hp⟩, fun t ht => (hv t ht).1, fun t ht => (hv t ht).2,
      (vatsDistinct_iff legs).1 hd, hb⟩, rfl, rfl⟩
  · rintro ⟨j, rfl, rfl⟩
    simp only [checkJoint, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      LocalTurn.valid_iff]
    exact ⟨⟨⟨⟨fun t ht => ⟨j.valid t ht, j.nonneg t ht⟩, (vatsDistinct_iff _).2 j.distinct⟩,
      j.shared.agree⟩, j.shared.pinned⟩, j.balanced⟩
theorem sum_post_eq : ∀ legs : List LocalTurn, (∀ t, t ∈ legs → t.post = t.pre + t.half) →
    (legs.map (·.post)).sum = (legs.map (·.pre)).sum + (legs.map (·.half)).sum
  | [], _ => by simp
  | t :: ts, h => by
    have ht := h t (by simp)
    have ih := sum_post_eq ts (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, ih, ht]
    omega
/-- **A joint turn conserves the total balance** of the vats it touches. -/
theorem jointTurn_conserves_total_balance (j : JointTurn) :
    (j.legs.map (·.post)).sum = (j.legs.map (·.pre)).sum := by
  rw [sum_post_eq j.legs j.valid, j.balanced]
  omega
/-- What the checker establishes: conservation, distinct vats, no negative balance, and every leg
naming the digest of this forest. -/
theorem jointTurn_sound (shared : ByteArray) (legs : List LocalTurn)
    (h : checkJoint shared legs = true) :
    (legs.map (·.post)).sum = (legs.map (·.pre)).sum ∧ (legs.map (·.vat)).Nodup ∧
      (∀ t, t ∈ legs → 0 ≤ t.pre ∧ 0 ≤ t.post) ∧
      ∀ t, t ∈ legs → t.turnId = turnDigest legs := by
  obtain ⟨j, rfl, rfl⟩ := (checkJoint_iff shared legs).1 h
  exact ⟨jointTurn_conserves_total_balance j, j.distinct, j.nonneg,
    fun t ht => (j.shared.agree t ht).trans j.shared.pinned⟩
/-- **The turn digest binds the forest.** Two joint turns with one digest have the same legs (every
field of each, in order), or their forests collide. A leg cannot be moved into another turn, and
neither its `pre` nor its `post` can be restated. -/
theorem sharedTurnId_binds_forest (j₁ j₂ : JointTurn) (h : j₁.shared.tid = j₂.shared.tid) :
    j₁.legs = j₂.legs ∨
      CollisionAmong (cshake256Bytes turnCustomization)
        (fun x => x = encodeFields (j₁.legs.map LocalTurn.legBytes) ∨
          x = encodeFields (j₂.legs.map LocalTurn.legBytes)) := by
  have hd : turnDigest j₁.legs = turnDigest j₂.legs := by
    rw [← j₁.shared.pinned, ← j₂.shared.pinned, h]
  rcases forestDigest_binds hd with he | hc
  · exact .inl (legs_eq_of_legBytes j₁.shared.tid _ _ j₁.shared.agree
      (fun t ht => (j₂.shared.agree t ht).trans h.symm) he)
  · exact .inr hc
/-- **Local receipts are not enough.** Two receipts, each valid on its own and naming one turn, that
mint a unit between them; and two receipts whose half-edges cancel but which belong to different
turns. Neither pair is a joint turn under any digest: the product of the vats' own judgements is
strictly larger than the joint one, and the binding has to be checked. -/
theorem tensor_not_final :
    (∃ a b : LocalTurn, a.valid = true ∧ b.valid = true ∧ a.turnId = b.turnId ∧
        ∀ shared, checkJoint shared [a, b] = false) ∧
      (∃ a b : LocalTurn, a.valid = true ∧ b.valid = true ∧ a.half + b.half = 0 ∧
        ∀ shared, checkJoint shared [a, b] = false) := by
  refine ⟨⟨⟨0, .empty, .empty, 0, 1, 1, 0, 0, 0⟩, ⟨1, .empty, .empty, 0, 1, 1, 0, 0, 0⟩, by decide, by decide, rfl,
      fun shared => ?_⟩,
    ⟨⟨0, ⟨#[0]⟩, .empty, 0, 1, 1, 0, 0, 0⟩, ⟨1, ⟨#[1]⟩, .empty, 1, -1, 0, 0, 0, 0⟩, by decide, by decide,
      by decide, fun shared => ?_⟩⟩
  · refine Bool.eq_false_iff.2 (fun h => ?_)
    obtain ⟨j, hl, _⟩ := (checkJoint_iff _ _).1 h
    have hb := j.balanced
    rw [hl] at hb
    simp at hb
  · refine Bool.eq_false_iff.2 (fun h => ?_)
    obtain ⟨j, hl, _⟩ := (checkJoint_iff _ _).1 h
    have h12 : (⟨#[0]⟩ : ByteArray) = ⟨#[1]⟩ :=
      (j.shared.agree ⟨0, ⟨#[0]⟩, .empty, 0, 1, 1, 0, 0, 0⟩ (by rw [hl]; simp)).trans
        (j.shared.agree ⟨1, ⟨#[1]⟩, .empty, 1, -1, 0, 0, 0, 0⟩ (by rw [hl]; simp)).symm
    exact absurd h12 (by decide)
/-! ## 3. Many turns: a floor book and its spent digests -/
/-- Balances by vat: the reading of a floor book's user accounts in one asset. -/
abbrev Ledger := VatId → Int
/-- Apply one half-edge. -/
def applyLeg (L : Ledger) (t : LocalTurn) : Ledger :=
  fun v => if v = t.vat then L v + t.half else L v
/-- Apply the half-edges of a turn. -/
def applyLegs (L : Ledger) (legs : List LocalTurn) : Ledger := legs.foldl applyLeg L
/-- The total over a set of vats. -/
def total (vats : List VatId) (L : Ledger) : Int := (vats.map L).sum
theorem total_applyLeg_of_not_mem (L : Ledger) (t : LocalTurn) : ∀ vats : List VatId,
    t.vat ∉ vats → total vats (applyLeg L t) = total vats L
  | [], _ => by rfl
  | v :: vs, h => by
    have hv : v ≠ t.vat := fun e => h (by simp [e])
    have ih := total_applyLeg_of_not_mem L t vs (fun hm => h (by simp [hm]))
    have hval : applyLeg L t v = L v := by simp [applyLeg, hv]
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hval]
theorem total_applyLeg (L : Ledger) (t : LocalTurn) : ∀ vats : List VatId, vats.Nodup →
    t.vat ∈ vats → total vats (applyLeg L t) = total vats L + t.half
  | [], _, h => by cases h
  | v :: vs, hnd, hm => by
    obtain ⟨hv, hvs⟩ := List.nodup_cons.1 hnd
    by_cases he : v = t.vat
    · have ih := total_applyLeg_of_not_mem L t vs (he ▸ hv)
      have hval : applyLeg L t v = L v + t.half := by simp [applyLeg, he]
      simp only [total, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, hval]
      omega
    · have hm' : t.vat ∈ vs := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm he
        · exact h
      have ih := total_applyLeg L t vs hvs hm'
      have hval : applyLeg L t v = L v := by simp [applyLeg, he]
      simp only [total, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, hval]
      omega
theorem total_applyLegs (vats : List VatId) (hnd : vats.Nodup) :
    ∀ (legs : List LocalTurn) (L : Ledger), (∀ t, t ∈ legs → t.vat ∈ vats) →
      total vats (applyLegs L legs) = total vats L + (legs.map (·.half)).sum
  | [], L, _ => by simp [applyLegs]
  | t :: ts, L, h => by
    have ih := total_applyLegs vats hnd ts (applyLeg L t) (fun x hx => h x (by simp [hx]))
    simp only [applyLegs, List.foldl_cons] at ih ⊢
    rw [ih, total_applyLeg L t vats hnd (h t (by simp))]
    simp only [List.map_cons, List.sum_cons]
    omega
theorem applyLegs_eq_sum : ∀ (legs : List LocalTurn) (L : Ledger) (v : VatId),
    applyLegs L legs v = L v + (legs.map (fun t => if v = t.vat then t.half else 0)).sum
  | [], L, v => by simp [applyLegs]
  | t :: ts, L, v => by
    have ih := applyLegs_eq_sum ts (applyLeg L t) v
    simp only [applyLegs, List.foldl_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    by_cases hv : v = t.vat <;> simp only [applyLeg, hv, ↓reduceIte] <;> omega
theorem applyLegs_of_not_mem : ∀ (legs : List LocalTurn) (L : Ledger) (v : VatId),
    v ∉ legs.map (·.vat) → applyLegs L legs v = L v
  | [], _, _, _ => by rfl
  | t :: ts, L, v, h => by
    have hv : v ≠ t.vat := fun e => h (by simp [e])
    have ih := applyLegs_of_not_mem ts (applyLeg L t) v
      (fun hm => h (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hm))
    simp only [applyLegs, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [applyLeg, hv]
/-- With distinct vats, a turn moves each of its vats by exactly that vat's half-edge. -/
theorem applyLegs_of_mem : ∀ (legs : List LocalTurn) (L : Ledger), (legs.map (·.vat)).Nodup →
    ∀ t, t ∈ legs → applyLegs L legs t.vat = L t.vat + t.half
  | [], _, _, _, ht => by cases ht
  | a :: ts, L, hnd, t, ht => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hstep : applyLegs L (a :: ts) t.vat = applyLegs (applyLeg L a) ts t.vat := by
      simp only [applyLegs, List.foldl_cons]
    rw [hstep]
    rcases List.mem_cons.1 ht with rfl | ht'
    · rw [applyLegs_of_not_mem ts _ _ hnd.1]
      simp [applyLeg]
    · have hne : t.vat ≠ a.vat := fun e => hnd.1 (by rw [← e]; exact List.mem_map_of_mem ht')
      rw [applyLegs_of_mem ts _ hnd.2 t ht']
      simp [applyLeg, hne]
/-- A leg's outflow: a typed posting from the vat's user account into the clearing account. -/
def debitPosting (clearing : AccountAddr) (asset : AssetId) (t : LocalTurn) : TypedPosting :=
  ⟨.user t.vat, clearing, asset, (-t.half).toNat⟩
/-- A leg's inflow, as a typed posting from the clearing account to the vat's user account. -/
def creditPosting (clearing : AccountAddr) (asset : AssetId) (t : LocalTurn) : TypedPosting :=
  ⟨clearing, .user t.vat, asset, t.half.toNat⟩
/-- The typed postings of a turn: every outflow into the clearing account, then every inflow out
of it, so the clearing account never dips below where it began. -/
def turnPostings (clearing : AccountAddr) (asset : AssetId) (legs : List LocalTurn) :
    List TypedPosting :=
  legs.map (debitPosting clearing asset) ++ legs.map (creditPosting clearing asset)
/-- What one posting adds to one account. -/
def postingNet (addr : AccountAddr) (asset : AssetId) (p : TypedPosting) : Int :=
  (if addr = p.destination ∧ asset = p.asset then (p.amount : Int) else 0) -
    (if addr = p.source ∧ asset = p.asset then (p.amount : Int) else 0)
/-- An admitted batch is the raw application of its postings. -/
theorem admitBatch_eq_foldl : ∀ (ps : List TypedPosting) (fb fb' : FloorBook),
    FloorBook.admitBatch fb ps = some fb' → fb' = ps.foldl FloorBook.applyRaw fb
  | [], fb, fb', h => by cases h; rfl
  | p :: ps, fb, fb', h => by
    unfold FloorBook.admitBatch at h
    split at h
    · rename_i fb₁ hp
      have h₁ : fb₁ = fb.applyRaw p := by
        unfold FloorBook.admitPosting at hp
        split at hp
        · exact (Option.some.inj hp).symm
        · cases hp
      rw [List.foldl_cons, ← h₁]
      exact admitBatch_eq_foldl ps fb₁ fb' h
    · cases h
theorem balance_foldl_applyRaw (addr : AccountAddr) (asset : AssetId) :
    ∀ (ps : List TypedPosting) (fb : FloorBook),
      (ps.foldl FloorBook.applyRaw fb).balance addr asset =
        fb.balance addr asset + (ps.map (postingNet addr asset)).sum
  | [], fb => by simp
  | p :: ps, fb => by
    rw [List.foldl_cons, balance_foldl_applyRaw addr asset ps, FloorBook.balance_applyRaw]
    simp only [List.map_cons, List.sum_cons, postingNet]
    omega
theorem sum_map_append_map {α β : Type} (f : β → Int) (g h : α → β) : ∀ l : List α,
    ((l.map g ++ l.map h).map f).sum = (l.map (fun x => f (g x) + f (h x))).sum
  | [] => by simp
  | x :: xs => by
    have ih := sum_map_append_map f g h xs
    simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append,
      List.cons_append] at ih ⊢
    omega
/-- A leg's two postings move its own vat's account by its half-edge and no other vat's. -/
theorem legPostings_net (clearing : AccountAddr) (hc : clearing.kind ≠ .user) (asset : AssetId)
    (v : VatId) (t : LocalTurn) :
    postingNet (.user v) asset (debitPosting clearing asset t) +
      postingNet (.user v) asset (creditPosting clearing asset t) =
        if v = t.vat then t.half else 0 := by
  have hne : AccountAddr.user v ≠ clearing := fun h => hc (by rw [← h]; rfl)
  have huser : AccountAddr.user v = AccountAddr.user t.vat ↔ v = t.vat :=
    ⟨fun h => by simpa [AccountAddr.user] using h, fun h => by rw [h]⟩
  simp only [postingNet, debitPosting, creditPosting, hne, huser, and_true, ↓reduceIte]
  by_cases hv : v = t.vat <;> simp only [hv, ↓reduceIte] <;> omega
theorem turnPostings_net (clearing : AccountAddr) (hc : clearing.kind ≠ .user) (asset : AssetId)
    (v : VatId) (legs : List LocalTurn) :
    ((turnPostings clearing asset legs).map (postingNet (.user v) asset)).sum =
      (legs.map (fun t => if v = t.vat then t.half else 0)).sum := by
  rw [turnPostings, sum_map_append_map]
  exact congrArg List.sum
    (List.map_congr_left fun t _ => legPostings_net clearing hc asset v t)
theorem admitBatch_append : ∀ (ps qs : List TypedPosting) (fb : FloorBook),
    FloorBook.admitBatch fb (ps ++ qs) =
      (FloorBook.admitBatch fb ps).bind (FloorBook.admitBatch · qs)
  | [], qs, fb => by simp [FloorBook.admitBatch]
  | p :: ps, qs, fb => by
    simp only [List.cons_append, FloorBook.admitBatch]
    cases FloorBook.admitPosting fb p with
    | none => simp
    | some fb₁ => exact admitBatch_append ps qs fb₁
theorem minBalance?_foldl_applyRaw (addr : AccountAddr) (asset : AssetId) :
    ∀ (ps : List TypedPosting) (fb : FloorBook),
      (ps.foldl FloorBook.applyRaw fb).minBalance? addr asset = fb.minBalance? addr asset
  | [], _ => by rw [List.foldl_nil]
  | p :: ps, fb => by
    rw [List.foldl_cons, minBalance?_foldl_applyRaw addr asset ps, FloorBook.minBalance?_applyRaw]
/-- A posting between two accounts is admitted when its source stays at or above its floor. -/
theorem admitPosting_of_floor (fb : FloorBook) (p : TypedPosting) (hsd : p.source ≠ p.destination)
    (h : ∀ f, fb.minBalance? p.source p.asset = some f →
      f ≤ fb.balance p.source p.asset - p.amount) :
    fb.admitPosting p = some (fb.applyRaw p) := by
  have hb := FloorBook.balance_applyRaw fb p p.source p.asset
  simp only [hsd, false_and, and_self, ↓reduceIte] at hb
  unfold FloorBook.admitPosting FloorBook.accountFloorHoldsB
  rw [FloorBook.minBalance?_applyRaw]
  cases hm : fb.minBalance? p.source p.asset with
  | none => simp
  | some f =>
    have hd : decide (f ≤ (fb.applyRaw p).balance p.source p.asset) = true :=
      decide_eq_true (by have := h f hm; rw [hb]; omega)
    simp [hd]
theorem debits_admitted (c : AccountAddr) (hc : c.kind ≠ .user) (a : AssetId) :
    ∀ (legs : List LocalTurn) (fb : FloorBook), (legs.map (·.vat)).Nodup →
      (∀ t, t ∈ legs → ∀ f, fb.minBalance? (.user t.vat) a = some f →
        f ≤ fb.balance (.user t.vat) a - ((-t.half).toNat : Int)) →
      ∃ fb', FloorBook.admitBatch fb (legs.map (debitPosting c a)) = some fb'
  | [], fb, _, _ => ⟨fb, by rfl⟩
  | t :: ts, fb, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have huc : ∀ v, AccountAddr.user v ≠ c := fun v e => hc (by rw [← e]; rfl)
    have hp := admitPosting_of_floor fb (debitPosting c a t) (huc t.vat) (h t (by simp))
    obtain ⟨fb', hfb'⟩ := debits_admitted c hc a ts (fb.applyRaw (debitPosting c a t)) hnd.2
      (fun x hx f hf => by
        have hne : AccountAddr.user x.vat ≠ AccountAddr.user t.vat := fun e => hnd.1 (by
          have hxt : x.vat = t.vat := by simpa [AccountAddr.user] using e
          rw [← hxt]; exact List.mem_map_of_mem hx)
        rw [FloorBook.minBalance?_applyRaw] at hf
        have := h x (by simp [hx]) f hf
        rw [FloorBook.balance_applyRaw]
        simp only [debitPosting, hne, huc x.vat, false_and, ↓reduceIte]
        omega)
    exact ⟨fb', by rw [List.map_cons, FloorBook.admitBatch, hp]; exact hfb'⟩
theorem credits_admitted (c : AccountAddr) (hc : c.kind ≠ .user) (a : AssetId) :
    ∀ (legs : List LocalTurn) (fb : FloorBook),
      (∀ f, fb.minBalance? c a = some f →
        f ≤ fb.balance c a - ((legs.map (·.half.toNat)).sum : Nat)) →
      ∃ fb', FloorBook.admitBatch fb (legs.map (creditPosting c a)) = some fb'
  | [], fb, _ => ⟨fb, by rfl⟩
  | t :: ts, fb, h => by
    have hcu : c ≠ AccountAddr.user t.vat := fun e => hc (by rw [e]; rfl)
    have hp := admitPosting_of_floor fb (creditPosting c a t) hcu (fun f hf => by
      have := h f hf
      simp only [List.map_cons, List.sum_cons] at this
      simp only [creditPosting]
      omega)
    obtain ⟨fb', hfb'⟩ := credits_admitted c hc a ts (fb.applyRaw (creditPosting c a t))
      (fun f hf => by
        rw [FloorBook.minBalance?_applyRaw] at hf
        have := h f hf
        simp only [List.map_cons, List.sum_cons] at this
        rw [FloorBook.balance_applyRaw]
        simp only [creditPosting, hcu, false_and, and_self, ↓reduceIte]
        omega)
    exact ⟨fb', by rw [List.map_cons, FloorBook.admitBatch, hp]; exact hfb'⟩
/-- What the outflows of a turn leave in its clearing account. -/
theorem debits_net_clearing (c : AccountAddr) (hc : c.kind ≠ .user) (a : AssetId) :
    ∀ legs : List LocalTurn, ((legs.map (debitPosting c a)).map (postingNet c a)).sum =
      ((legs.map (·.half.toNat)).sum : Nat) - (legs.map (·.half)).sum
  | [] => by simp
  | t :: ts => by
    have ih := debits_net_clearing c hc a ts
    have hcu : c ≠ AccountAddr.user t.vat := fun e => hc (by rw [e]; rfl)
    simp only [List.map_cons, List.sum_cons, postingNet, debitPosting, hcu, false_and, and_self,
      ↓reduceIte]
    omega
/-- **The floors are the only reason a book refuses a turn's postings.** On a book whose floors
hold, the postings of legs with distinct vats and half-edges summing to zero are admitted, provided
no vat is taken below its configured floor. -/
theorem turnPostings_admitted (c : AccountAddr) (hc : c.kind ≠ .user) (a : AssetId)
    (fb : FloorBook) (hfl : FloorsHold fb) (legs : List LocalTurn)
    (hnd : (legs.map (·.vat)).Nodup) (hbal : (legs.map (·.half)).sum = 0)
    (hmin : ∀ t, t ∈ legs → ∀ f, fb.minBalance? (.user t.vat) a = some f →
      f ≤ fb.balance (.user t.vat) a + t.half) :
    ∃ fb', fb.admitBatch (turnPostings c a legs) = some fb' := by
  obtain ⟨fb₁, h₁⟩ := debits_admitted c hc a legs fb hnd (fun t ht f hf => by
    have h1 := hmin t ht f hf
    have h2 := hfl (.user t.vat) a
    simp only [hf] at h2
    omega)
  have hf₁ := admitBatch_eq_foldl _ _ _ h₁
  obtain ⟨fb₂, h₂⟩ := credits_admitted c hc a legs fb₁ (fun f hf => by
    rw [hf₁, minBalance?_foldl_applyRaw] at hf
    have h2 := hfl c a
    simp only [hf] at h2
    rw [hf₁, balance_foldl_applyRaw, debits_net_clearing c hc a, hbal]
    omega)
  exact ⟨fb₂, by rw [turnPostings, admitBatch_append, h₁]; exact h₂⟩
/-- The ledger: a floor book, the asset the vats' balances are held in, and the turn digests
already applied, as a sorted set of their 256-bit readings. -/
structure LedgerState where
  book : FloorBook
  asset : AssetId
  seen : RevokedSet
  epoch : Nat := 0
/-- A vat's balance is its user account's balance in the book. -/
def LedgerState.balances (s : LedgerState) : Ledger :=
  fun v => s.book.balance (.user v) s.asset
/-- The 256-bit reading of a turn digest. -/
def turnKey (shared : ByteArray) : Nat := ofBE shared.data.toList
/-- The escrow account a turn clears through, named by the turn's digest. -/
def turnClearing (shared : ByteArray) : AccountAddr := .escrow (turnKey shared)
theorem turnClearing_kind (shared : ByteArray) : (turnClearing shared).kind ≠ .user := by
  simp [turnClearing, AccountAddr.escrow]
/-- The guard of a step: the turn checks, is new, touches only vats of the ledger, and every
leg's `pre` is that vat's balance in the book. -/
def stepOk (n : Nat) (s : LedgerState) (shared : ByteArray) (legs : List LocalTurn) : Bool :=
  checkJoint shared legs && !s.seen.contains (turnKey shared) &&
    legs.all (fun t => decide (t.asset = s.asset ∧ t.epoch = s.epoch)) &&
    legs.all (fun t => decide (t.vat < n) && decide (t.pre = s.balances t.vat))
/-- Apply one joint turn: under the guard, the book admits the turn's postings floor by floor. -/
def stepJoint (n : Nat) (s : LedgerState) (shared : ByteArray) (legs : List LocalTurn) :
    Option LedgerState :=
  if stepOk n s shared legs then
    (s.book.admitBatch (turnPostings (turnClearing shared) s.asset legs)).map
      fun book => ⟨book, s.asset, s.seen.insert (turnKey shared), s.epoch⟩
  else none
/-- Accepted legs belong to this asset and epoch, not merely a matching balance. -/
theorem stepJoint_domain {n : Nat} {s f : LedgerState} {tid : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s tid legs = some f) :
    ∀ t ∈ legs, t.asset = s.asset ∧ t.epoch = s.epoch := by
  unfold stepJoint at h
  split at h
  · rename_i hc
    simp only [stepOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    exact hc.1.2
  · cases h
/-- A failed batch publishes no intermediate debit and spends no replay key. -/
def applyJoint (n : Nat) (s : LedgerState) (shared : ByteArray) (legs : List LocalTurn) : LedgerState :=
  (stepJoint n s shared legs).getD s
theorem applyJoint_rollback {n : Nat} {s : LedgerState} {shared : ByteArray} {legs : List LocalTurn}
    (h : stepJoint n s shared legs = none) : applyJoint n s shared legs = s := by
  simp [applyJoint, h]
/-- Apply a sequence of joint turns. -/
def runTrace (n : Nat) : LedgerState → List (ByteArray × List LocalTurn) → Option LedgerState
  | s, [] => some s
  | s, (shared, legs) :: rest =>
    match stepJoint n s shared legs with
    | some s' => runTrace n s' rest
    | none => none
/-- A sequence of joint turns, each applied to the ledger the last one left. -/
def ValidJointTrace (n : Nat) :
    LedgerState → List (ByteArray × List LocalTurn) → LedgerState → Prop
  | s, [], s' => s' = s
  | s, (shared, legs) :: rest, s' =>
    ∃ s₁, stepJoint n s shared legs = some s₁ ∧ ValidJointTrace n s₁ rest s'
theorem validJointTrace_cons {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} {rest : List (ByteArray × List LocalTurn)} :
    ValidJointTrace n s ((shared, legs) :: rest) s' ↔
      ∃ s₁, stepJoint n s shared legs = some s₁ ∧ ValidJointTrace n s₁ rest s' := by
  simp only [ValidJointTrace]
/-- **`runTrace` runs exactly the valid traces.** -/
theorem runTrace_eq_some_iff (n : Nat) (trace : List (ByteArray × List LocalTurn)) :
    ∀ s s' : LedgerState, runTrace n s trace = some s' ↔ ValidJointTrace n s trace s' := by
  induction trace with
  | nil =>
    intro s s'
    simp only [runTrace, ValidJointTrace, Option.some.injEq]
    exact eq_comm
  | cons e rest ih =>
    obtain ⟨shared, legs⟩ := e
    intro s s'
    simp only [runTrace, ValidJointTrace]
    cases hs : stepJoint n s shared legs with
    | none => simp
    | some s₁ => simp [ih]
theorem stepJoint_eq_some {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') :
    checkJoint shared legs = true ∧ s.seen.contains (turnKey shared) = false ∧
      (∀ t, t ∈ legs → t.vat < n ∧ t.pre = s.balances t.vat) ∧
      s.book.admitBatch (turnPostings (turnClearing shared) s.asset legs) = some s'.book ∧
      s'.asset = s.asset ∧ s'.seen = s.seen.insert (turnKey shared) := by
  unfold stepJoint at h
  split at h
  · rename_i hc
    simp only [stepOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
      decide_eq_true_eq] at hc
    cases hb : s.book.admitBatch (turnPostings (turnClearing shared) s.asset legs) with
    | none => rw [hb] at h; cases h
    | some book =>
      rw [hb] at h
      cases h
      exact ⟨hc.1.1.1, hc.1.1.2, hc.2, rfl, rfl, rfl⟩
  · cases h
/-- **A step is the turn's half-edges on the book's balances.** -/
theorem stepJoint_balances {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') (v : VatId) :
    s'.balances v = applyLegs s.balances legs v := by
  obtain ⟨_, _, _, hb, ha, _⟩ := stepJoint_eq_some h
  have hf := admitBatch_eq_foldl _ _ _ hb
  rw [applyLegs_eq_sum, ← turnPostings_net (turnClearing shared) (turnClearing_kind shared)
    s.asset v legs]
  simp only [LedgerState.balances]
  rw [ha, hf, balance_foldl_applyRaw]
/-- **Receipts and ledger agree.** After a step every touched vat holds its receipt's `post`, and
every other vat holds what it held. -/
theorem stepJoint_post_balance {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') :
    (∀ t, t ∈ legs → s'.balances t.vat = t.post) ∧
      ∀ v, v ∉ legs.map (·.vat) → s'.balances v = s.balances v := by
  obtain ⟨hc, _, hv, _⟩ := stepJoint_eq_some h
  obtain ⟨j, rfl, _⟩ := (checkJoint_iff shared legs).1 hc
  refine ⟨fun t ht => ?_, fun v hv' => ?_⟩
  · rw [stepJoint_balances h, applyLegs_of_mem _ _ j.distinct t ht, ← (hv t ht).2,
      j.valid t ht]
  · rw [stepJoint_balances h, applyLegs_of_not_mem _ _ _ hv']
/-- **A step conserves the ledger's total.** -/
theorem stepJoint_conserves {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') :
    total (List.range n) s'.balances = total (List.range n) s.balances := by
  obtain ⟨hc, _, hv, _⟩ := stepJoint_eq_some h
  obtain ⟨j, rfl, _⟩ := (checkJoint_iff shared legs).1 hc
  have hb : s'.balances = applyLegs s.balances j.legs := funext (stepJoint_balances h)
  rw [hb, total_applyLegs (List.range n) List.nodup_range j.legs s.balances
    (fun t ht => List.mem_range.2 (hv t ht).1), j.balanced]
  omega
/-- **A step conserves the total over the vats it touches**: the sum of `pre`, then of `post`. -/
theorem stepJoint_conserves_active {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') :
    total (legs.map (·.vat)) s.balances = (legs.map (·.pre)).sum ∧
      total (legs.map (·.vat)) s'.balances = (legs.map (·.post)).sum ∧
      total (legs.map (·.vat)) s'.balances = total (legs.map (·.vat)) s.balances := by
  obtain ⟨hc, _, hv, _⟩ := stepJoint_eq_some h
  obtain ⟨j, rfl, _⟩ := (checkJoint_iff shared legs).1 hc
  have hpre : total (j.legs.map (·.vat)) s.balances = (j.legs.map (·.pre)).sum := by
    simp only [total, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun t ht => (hv t ht).2.symm)
  have hpost : total (j.legs.map (·.vat)) s'.balances = (j.legs.map (·.post)).sum := by
    simp only [total, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun t ht => (stepJoint_post_balance h).1 t ht)
  exact ⟨hpre, hpost, by rw [hpost, hpre, jointTurn_conserves_total_balance j]⟩
/-- **A step overdraws no vat.** -/
theorem stepJoint_no_overdraft {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') (v : VatId)
    (hv : 0 ≤ s.balances v) : 0 ≤ s'.balances v := by
  obtain ⟨hc, _, _, _⟩ := stepJoint_eq_some h
  obtain ⟨j, rfl, _⟩ := (checkJoint_iff shared legs).1 hc
  by_cases hm : v ∈ j.legs.map (·.vat)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hm
    rw [(stepJoint_post_balance h).1 t ht]
    exact (j.nonneg t ht).2
  · rw [(stepJoint_post_balance h).2 v hm]
    exact hv
/-- **A step is an admitted batch on the floor book.** The book admits the turn's typed postings
and the new ledger holds the result; from floors that hold, the floors still hold (no user account
is negative), every asset's sum is unchanged, and the vats moved by exactly the half-edges. -/
theorem stepJoint_refines_floorBook {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (hfl : FloorsHold s.book)
    (h : stepJoint n s shared legs = some s') :
    s.book.admitBatch (turnPostings (turnClearing shared) s.asset legs) = some s'.book ∧
      FloorsHold s'.book ∧ (∀ ast, s'.book.assetSum ast = s.book.assetSum ast) ∧
      (∀ v, s'.balances v = applyLegs s.balances legs v) ∧ ∀ v, 0 ≤ s'.balances v := by
  obtain ⟨_, _, _, hb, _, _⟩ := stepJoint_eq_some h
  obtain ⟨hfl', hsum⟩ := FloorBook.admitBatch_preserves_floors _ hfl hb
  exact ⟨hb, hfl', hsum, stepJoint_balances h, fun v =>
    Obend.Ledger.nonIssuer_balance_nonneg_of_floorsHold hfl' (.user v) s'.asset
      (by simp [AccountAddr.user])⟩
/-- **The step is complete.** On a book whose floors hold, a turn that passes the guard is applied
unless it takes a vat below a floor the book configures: guard and floors are the only refusals. -/
theorem stepJoint_complete {n : Nat} {s : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (hfl : FloorsHold s.book) (hok : stepOk n s shared legs = true)
    (hmin : ∀ t, t ∈ legs → ∀ f, s.book.minBalance? (.user t.vat) s.asset = some f → f ≤ t.post) :
    ∃ s', stepJoint n s shared legs = some s' := by
  have hok' := hok
  simp only [stepOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_eq] at hok'
  obtain ⟨j, hl, _⟩ := (checkJoint_iff shared legs).1 hok'.1.1.1
  obtain ⟨fb', hfb'⟩ := turnPostings_admitted (turnClearing shared) (turnClearing_kind shared)
    s.asset s.book hfl legs (hl ▸ j.distinct) (hl ▸ j.balanced) (fun t ht f hf => by
      have h1 := hmin t ht f hf
      have h2 := (hok'.2 t ht).2
      have h3 := j.valid t (hl ▸ ht)
      simp only [LedgerState.balances] at h2
      omega)
  exact ⟨⟨fb', s.asset, s.seen.insert (turnKey shared), s.epoch⟩, by
    simp only [stepJoint, hok, ↓reduceIte, hfb', Option.map_some]⟩
/-- **A replayed turn is refused.** -/
theorem replayed_turn_refused (n : Nat) (s : LedgerState) (shared : ByteArray)
    (legs : List LocalTurn) (h : s.seen.contains (turnKey shared) = true) :
    stepJoint n s shared legs = none := by
  simp [stepJoint, stepOk, h]
/-- **A vat named twice is refused**: no leg's half-edge is counted in the sum and then
overwritten on the ledger. -/
theorem duplicate_vat_refused (n : Nat) (s : LedgerState) (shared : ByteArray)
    (legs : List LocalTurn) (h : ¬ (legs.map (·.vat)).Nodup) :
    stepJoint n s shared legs = none := by
  cases hs : stepJoint n s shared legs with
  | none => rfl
  | some s' =>
    obtain ⟨j, hl, _⟩ := (checkJoint_iff shared legs).1 (stepJoint_eq_some hs).1
    exact absurd (hl ▸ j.distinct) h
/-- **A `pre` that is not the vat's balance is refused**: a turn cannot restate what a vat held. -/
theorem unbound_pre_refused (n : Nat) (s : LedgerState) (shared : ByteArray)
    (legs : List LocalTurn) (t : LocalTurn) (ht : t ∈ legs) (h : t.pre ≠ s.balances t.vat) :
    stepJoint n s shared legs = none := by
  cases hs : stepJoint n s shared legs with
  | none => rfl
  | some s' => exact absurd ((stepJoint_eq_some hs).2.2.1 t ht).2 h
/-- **An overdraft is refused**: no leg leaves its vat below zero. -/
theorem overdraft_refused (n : Nat) (s : LedgerState) (shared : ByteArray)
    (legs : List LocalTurn) (t : LocalTurn) (ht : t ∈ legs) (h : t.post < 0) :
    stepJoint n s shared legs = none := by
  cases hs : stepJoint n s shared legs with
  | none => rfl
  | some s' =>
    obtain ⟨j, hl, _⟩ := (checkJoint_iff shared legs).1 (stepJoint_eq_some hs).1
    have := (j.nonneg t (hl ▸ ht)).2
    omega
/-- What every step preserves, every valid trace preserves. -/
theorem jointTrace_lift {n : Nat} (R : LedgerState → LedgerState → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ s shared legs s₁, stepJoint n s shared legs = some s₁ → R s s₁)
    (trace : List (ByteArray × List LocalTurn)) :
    ∀ s s', ValidJointTrace n s trace s' → R s s' := by
  induction trace with
  | nil =>
    intro s s' h
    simp only [ValidJointTrace] at h
    rw [h]
    exact hrefl s
  | cons e rest ih =>
    obtain ⟨shared, legs⟩ := e
    intro s s' h
    obtain ⟨s₁, hs, hr⟩ := validJointTrace_cons.1 h
    exact htrans _ _ _ (hstep _ _ _ _ hs) (ih _ _ hr)
/-- **Conservation over any number of turns.** A trace of joint turns leaves the ledger's total
where it was, and never forgets a digest it has applied. -/
theorem jointTrace_conserves_total_balance (n : Nat) (trace : List (ByteArray × List LocalTurn))
    (s s' : LedgerState) (h : ValidJointTrace n s trace s') :
    total (List.range n) s'.balances = total (List.range n) s.balances ∧
      ∀ k, s.seen.contains k = true → s'.seen.contains k = true :=
  jointTrace_lift
    (fun s s' => total (List.range n) s'.balances = total (List.range n) s.balances ∧
      ∀ k, s.seen.contains k = true → s'.seen.contains k = true)
    (fun _ => ⟨rfl, fun _ hk => hk⟩)
    (fun _ _ _ hab hbc => ⟨hbc.1.trans hab.1, fun k hk => hbc.2 k (hab.2 k hk)⟩)
    (fun _ _ _ _ hs => ⟨stepJoint_conserves hs, fun k hk => by
      rw [(stepJoint_eq_some hs).2.2.2.2.2]
      exact (RevokedSet.contains_insert _ _ _).2 (.inr hk)⟩) trace s s' h
/-- **No overdraft over any number of turns**: a vat not negative before is not negative after. -/
theorem jointTrace_no_overdraft (n : Nat) (trace : List (ByteArray × List LocalTurn))
    (s s' : LedgerState) (h : ValidJointTrace n s trace s') :
    ∀ v, 0 ≤ s.balances v → 0 ≤ s'.balances v :=
  jointTrace_lift (fun s s' => ∀ v, 0 ≤ s.balances v → 0 ≤ s'.balances v) (fun _ _ hv => hv)
    (fun _ _ _ hab hbc v hv => hbc v (hab v hv))
    (fun _ _ _ _ hs v hv => stepJoint_no_overdraft hs v hv) trace s s' h
/-- **A trace keeps the book's floors.** From floors that hold, any number of joint turns leaves
floors that hold, every asset's sum over all accounts unchanged, and no vat negative. -/
theorem jointTrace_preserves_floors (n : Nat) (trace : List (ByteArray × List LocalTurn))
    (s s' : LedgerState) (hfl : FloorsHold s.book) (h : ValidJointTrace n s trace s') :
    FloorsHold s'.book ∧ (∀ ast, s'.book.assetSum ast = s.book.assetSum ast) ∧
      ∀ v, 0 ≤ s'.balances v := by
  have hR := jointTrace_lift (n := n)
    (fun s s' => FloorsHold s.book →
      FloorsHold s'.book ∧ ∀ ast, s'.book.assetSum ast = s.book.assetSum ast)
    (fun _ hf => ⟨hf, fun _ => rfl⟩)
    (fun _ _ _ hab hbc hf =>
      ⟨(hbc (hab hf).1).1, fun ast => ((hbc (hab hf).1).2 ast).trans ((hab hf).2 ast)⟩)
    (fun _ _ _ _ hs hf =>
      ⟨(stepJoint_refines_floorBook hf hs).2.1, (stepJoint_refines_floorBook hf hs).2.2.1⟩)
    trace s s' h hfl
  exact ⟨hR.1, hR.2, fun v =>
    Obend.Ledger.nonIssuer_balance_nonneg_of_floorsHold hR.1 (.user v) s'.asset
      (by simp [AccountAddr.user])⟩
/-- Every turn of a valid trace was new when the trace began. -/
theorem jointTrace_fresh (n : Nat) (trace : List (ByteArray × List LocalTurn)) :
    ∀ s s' : LedgerState, ValidJointTrace n s trace s' →
      ∀ e, e ∈ trace → s.seen.contains (turnKey e.1) = false := by
  induction trace with
  | nil => intro _ _ _ _ he; cases he
  | cons e₀ rest ih =>
    obtain ⟨shared, legs⟩ := e₀
    intro s s' h e he
    obtain ⟨s₁, hs, hr⟩ := validJointTrace_cons.1 h
    obtain ⟨_, hnew, _, _, _, hseen⟩ := stepJoint_eq_some hs
    rcases List.mem_cons.1 he with rfl | he'
    · exact hnew
    · have h1 := ih s₁ s' hr e he'
      cases hc : s.seen.contains (turnKey e.1) with
      | false => rfl
      | true =>
        rw [hseen, (RevokedSet.contains_insert _ _ _).2 (.inr hc)] at h1
        cases h1
/-- **No turn digest is applied twice in a trace.** -/
theorem jointTrace_no_replay (n : Nat) (s s' : LedgerState) (shared : ByteArray)
    (legs legs' : List LocalTurn) (rest : List (ByteArray × List LocalTurn))
    (h : ValidJointTrace n s ((shared, legs) :: rest) s') : (shared, legs') ∉ rest := by
  intro hm
  obtain ⟨s₁, hs, hr⟩ := validJointTrace_cons.1 h
  have h1 : s₁.seen.contains (turnKey shared) = false :=
    jointTrace_fresh n rest s₁ s' hr (shared, legs') hm
  rw [(stepJoint_eq_some hs).2.2.2.2.2, RevokedSet.contains_insert_self] at h1
  cases h1
/-! ## 4. The joint turn over commitments -/
/-- A leg whose half-edge is hidden: its direction and a 256-bit commitment to its magnitude. -/
structure CommittedLeg where
  vat : VatId
  turnId : ByteArray
  credit : Bool
  commitment : BitVec 256

/-- What a committed leg contributes to the turn digest. -/
def CommittedLeg.legBytes (t : CommittedLeg) : List UInt8 :=
  encodeFields [leb128 t.vat, [if t.credit then 1 else 0], be 32 t.commitment.toNat]

theorem CommittedLeg.legBytes_inj {a b : CommittedLeg} (h : a.legBytes = b.legBytes) :
    a.vat = b.vat ∧ a.credit = b.credit ∧ a.commitment = b.commitment := by
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  refine ⟨(leb128_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hf.1])).1, ?_,
    BitVec.eq_of_toNat_eq (be_injective (h256 ▸ a.commitment.isLt) (h256 ▸ b.commitment.isLt)
      hf.2.2)⟩
  have hc := hf.2.1
  cases ha : a.credit <;> cases hb : b.credit <;> simp [ha, hb] at hc ⊢

/-- The commitments of the debit legs. -/
def debits (legs : List CommittedLeg) : List (BitVec 256) :=
  (legs.filter (fun t => !t.credit)).map (·.commitment)

/-- The commitments of the credit legs. -/
def credits (legs : List CommittedLeg) : List (BitVec 256) :=
  (legs.filter (·.credit)).map (·.commitment)

/-- cSHAKE commits to both the amount and the blinding at their full 256-bit widths.
The affine ring commitment is not a binding cryptographic commitment and is not used here. -/
def openingPreimage (o : Opening) : List UInt8 := encodeFields [be 32 o.value.toNat, be 32 o.blind.toNat]
def openingCommit (o : Opening) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes "OBEND.JOINT.OPENING/v1".toUTF8.toList (openingPreimage o)))

/-- An opening is bound at full width, with an explicit pair if cSHAKE collides. -/
def openingCommit_extract (a b : Opening) (h : openingCommit a = openingCommit b) :
    PSum (PLift (a = b)) (CollisionPair (cshake256Bytes "OBEND.JOINT.OPENING/v1".toUTF8.toList)
      (fun x => x = openingPreimage a ∨ x = openingPreimage b)) := by
  apply extractBinding _ (openingPreimage a) (openingPreimage b)
  · intro he
    have hf := encodeFields_injective _ _ he
    simp only [List.cons.injEq, and_true] at hf
    have bound (v : BitVec 256) : v.toNat < 256 ^ 32 := by
      simpa using v.isLt
    have hv := BitVec.eq_of_toNat_eq (be_injective (bound a.value) (bound b.value) hf.1)
    have hb := BitVec.eq_of_toNat_eq (be_injective (bound a.blind) (bound b.blind) hf.2)
    cases a; cases b; simp_all
  · have hn := congrArg BitVec.toNat h
    have hb (x : List UInt8) : ofBE (cshake256Bytes "OBEND.JOINT.OPENING/v1".toUTF8.toList x) < 2 ^ 256 := by
      have hlt := ofBE_lt (cshake256Bytes "OBEND.JOINT.OPENING/v1".toUTF8.toList x)
      rwa [cshake256Bytes_length, (by decide : (256 : Nat) ^ 32 = 2 ^ 256)] at hlt
    simpa only [openingCommit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb _)] using hn

/-- Audited openings are supplied to the verifier. This is transparent settlement, with no
zero-knowledge claim: both correspondence and integer conservation are checked, not premises. -/
def checkJointCommitted (shared : ByteArray) (legs : List CommittedLeg)
    (dOpen cOpen : List Opening) : Bool :=
  legs.all (fun t => decide (t.turnId = shared)) &&
    decide (shared = forestDigest (legs.map CommittedLeg.legBytes)) &&
    decide ((legs.map (·.vat)).Nodup) &&
    decide (debits legs = dOpen.map openingCommit) && decide (credits legs = cOpen.map openingCommit) &&
    decide (natSum (dOpen.map (·.value)) = natSum (cOpen.map (·.value)))

theorem jointTurn_committed_conservation_sound (shared : ByteArray)
    (legs : List CommittedLeg) (dOpen cOpen : List Opening)
    (hcheck : checkJointCommitted shared legs dOpen cOpen = true) :
    natSum (dOpen.map (·.value)) = natSum (cOpen.map (·.value)) ∧
      debits legs = dOpen.map openingCommit ∧ credits legs = cOpen.map openingCommit ∧
      (legs.map (·.vat)).Nodup ∧
      ∀ t, t ∈ legs → t.turnId = forestDigest (legs.map CommittedLeg.legBytes) := by
  simp only [checkJointCommitted, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨ha, hp⟩, hnd⟩, hd⟩, hc⟩, hs⟩ := hcheck
  exact ⟨hs, hd, hc, hnd, fun t ht => (ha t ht).trans hp⟩

/-- Actual cSHAKE commitments inhabit the checked path. -/
theorem jointTurn_committed_inhabited :
    ∃ shared legs, checkJointCommitted shared legs [⟨5#256, 7#256⟩] [⟨5#256, 7#256⟩] = true ∧
      legs.length = 2 := by
  let c := openingCommit ⟨5#256, 7#256⟩
  let raw : List CommittedLeg := [⟨0, .empty, false, c⟩, ⟨1, .empty, true, c⟩]
  let tid := forestDigest (raw.map CommittedLeg.legBytes)
  refine ⟨tid, [⟨0, tid, false, c⟩, ⟨1, tid, true, c⟩], ?_, rfl⟩
  simp [checkJointCommitted, debits, credits, tid, raw, CommittedLeg.legBytes, c]

/-! ## 5. Receipts with open ports -/

/-- A promise hole: the pending id, a 32-byte commitment to the awaited payload, the guard the
resolution must satisfy, and the authority its resolver must show (the lineage digest of a root
grant, and the rights needed). -/
structure AwaitPort where
  port : CapTP.PendingId
  payload : ByteArray
  guard : DistPred
  resolverRoot : ByteArray
  need : UInt64

/-- A resolution of a promise: the pending id, the payload commitment, and the delegation chain
the resolver holds. -/
structure FulfillPort where
  port : CapTP.PendingId
  payload : ByteArray
  root : Block
  chain : Array Block

/-- A receipt with open ports: the local turn, its causal rank, the holes it awaits and the
promises it resolves. -/
structure CoReceipt where
  turn : LocalTurn
  rank : Nat
  awaits : List AwaitPort
  fulfills : List FulfillPort

/-- A hole with the rank of the receipt that awaits it. -/
structure AwaitEntry where
  rank : Nat
  hole : AwaitPort

/-- A resolution with the rank of the receipt that makes it. -/
structure FulfillEntry where
  rank : Nat
  fill : FulfillPort

def AwaitEntry.key (e : AwaitEntry) : Nat := e.hole.port.toNat
def FulfillEntry.key (e : FulfillEntry) : Nat := e.fill.port.toNat

/-- Every hole of a diagram. -/
def awaitTable (rs : List CoReceipt) : List AwaitEntry :=
  rs.flatMap fun r => r.awaits.map (AwaitEntry.mk r.rank)

/-- Every resolution of a diagram. -/
def fulfillTable (rs : List CoReceipt) : List FulfillEntry :=
  rs.flatMap fun r => r.fulfills.map (FulfillEntry.mk r.rank)

theorem mem_awaitTable {rs : List CoReceipt} {e : AwaitEntry} :
    e ∈ awaitTable rs ↔ ∃ b, b ∈ rs ∧ ∃ w, w ∈ b.awaits ∧ AwaitEntry.mk b.rank w = e := by
  simp only [awaitTable, List.mem_flatMap, List.mem_map]

theorem mem_fulfillTable {rs : List CoReceipt} {e : FulfillEntry} :
    e ∈ fulfillTable rs ↔ ∃ a, a ∈ rs ∧ ∃ f, f ∈ a.fulfills ∧ FulfillEntry.mk a.rank f = e := by
  simp only [fulfillTable, List.mem_flatMap, List.mem_map]

/-- What a wire is checked against: the revoked set, the facts caveats are evaluated on, the
discharges presented for guards, and the step the guards read. -/
structure WireEnv where
  revoked : RevokedSet
  facts : Nat → KleenePred3
  discharges : List VkId
  step : Step

/-- The resolver's chain descends from the root the hole names, folds with no revoked lineage or
channel, and carries the rights the hole needs. -/
def capOk (env : WireEnv) (w : AwaitPort) (f : FulfillPort) : Bool :=
  decide (rootLineage f.root = w.resolverRoot) &&
    match foldChain env.revoked env.facts f.root f.chain with
    | some acc => authorize acc w.need
    | none => false

/-- One wire: the payload commitments agree, the guard admits, the resolver is causally earlier,
and it is authorized. -/
def wireOk (env : WireEnv) (w : AwaitEntry) (f : FulfillEntry) : Bool :=
  decide (f.fill.payload = w.hole.payload) &&
    admits (dischargeOracle env.discharges) env.step w.hole.guard &&
    decide (f.rank < w.rank) && capOk env w.hole f.fill

/-- A resolution wired to its hole, as a proposition. -/
def Wired (env : WireEnv) (a : CoReceipt) (f : FulfillPort) (b : CoReceipt) (w : AwaitPort) :
    Prop :=
  f.payload = w.payload ∧ admits (dischargeOracle env.discharges) env.step w.guard = true ∧
    a.rank < b.rank ∧ rootLineage f.root = w.resolverRoot ∧
    ∃ acc, foldChain env.revoked env.facts f.root f.chain = some acc ∧ authorize acc w.need = true

theorem wireOk_iff (env : WireEnv) (a b : CoReceipt) (f : FulfillPort) (w : AwaitPort) :
    wireOk env ⟨b.rank, w⟩ ⟨a.rank, f⟩ = true ↔ Wired env a f b w := by
  simp only [wireOk, capOk, Wired, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  cases foldChain env.revoked env.facts f.root f.chain with
  | none => simp
  | some acc => simp

/-- **A wired resolver is revocation-clean on every prefix** of its chain: no ancestor's lineage
nullifier is in the revoked set. -/
theorem wired_revocation_clean {env : WireEnv} {a b : CoReceipt} {f : FulfillPort} {w : AwaitPort}
    (h : Wired env a f b w) (pre ext : Array Block) (hsplit : f.chain = pre ++ ext) :
    env.revoked.contains (credNul (lineageOf f.root pre.toList)) = false := by
  obtain ⟨_, _, _, _, acc, hfold, _⟩ := h
  rw [hsplit] at hfold
  have hl := (foldChain_prefix_live env.revoked env.facts f.root pre ext acc hfold).1
  simpa [lineageLive] using hl

/-- The hole table in port order. -/
def sortedAwaits (rs : List CoReceipt) : Array AwaitEntry := sortByKey AwaitEntry.key (awaitTable rs)

/-- The resolution table in port order. -/
def sortedFulfills (rs : List CoReceipt) : Array FulfillEntry :=
  sortByKey FulfillEntry.key (fulfillTable rs)

/-- **Port linearity**: both tables strictly ascend, so no pending id is awaited twice and none is
resolved twice. -/
def portsLinear (rs : List CoReceipt) : Bool :=
  tableOk AwaitEntry.key (sortedAwaits rs) && tableOk FulfillEntry.key (sortedFulfills rs)

/-- Check a resolution against the hole it fills, if the diagram has that hole. -/
def wireChecks (env : WireEnv) (awaits : Array AwaitEntry) (f : FulfillEntry) : Bool :=
  match lookup AwaitEntry.key awaits f.key with
  | some w => wireOk env w f
  | none => true

/-- Every resolution that meets a hole passes its wire check. -/
def wiresOk (env : WireEnv) (rs : List CoReceipt) : Bool :=
  (sortedFulfills rs).toList.all (wireChecks env (sortedAwaits rs))

/-- The holes no resolution of the diagram fills. -/
def openAwaitsOf (rs : List CoReceipt) : List AwaitEntry :=
  (sortedAwaits rs).toList.filter fun w =>
    (lookup FulfillEntry.key (sortedFulfills rs) w.key).isNone

/-- The resolutions whose hole is not in the diagram. -/
def danglingOf (rs : List CoReceipt) : List FulfillEntry :=
  (sortedFulfills rs).toList.filter fun f =>
    (lookup AwaitEntry.key (sortedAwaits rs) f.key).isNone

/-- A diagram with no open port must be a joint turn. -/
def closureOk (shared : ByteArray) (rs : List CoReceipt) : Bool :=
  !((openAwaitsOf rs).isEmpty && (danglingOf rs).isEmpty) || checkJoint shared (rs.map (·.turn))

/-- A composed diagram: the shared turn digest, the legs, and the ports still open. -/
structure Composite where
  shared : ByteArray
  legs : List LocalTurn
  openAwaits : List AwaitEntry
  dangling : List FulfillEntry

/-- **Compose receipts along their promises.** Every receipt names the shared turn; the ports are
linear; every wire checks; and a diagram left with no open port is a joint turn. -/
def composeCoReceipts (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt) :
    Option Composite :=
  if (rs.all fun r => decide (r.turn.turnId = shared)) && portsLinear rs && wiresOk env rs &&
      closureOk shared rs then
    some ⟨shared, rs.map (·.turn), openAwaitsOf rs, danglingOf rs⟩
  else none

theorem composeCoReceipts_eq_some_iff (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) :
    composeCoReceipts env shared rs = some c ↔
      (∀ r, r ∈ rs → r.turn.turnId = shared) ∧ portsLinear rs = true ∧ wiresOk env rs = true ∧
        closureOk shared rs = true ∧
        c = ⟨shared, rs.map (·.turn), openAwaitsOf rs, danglingOf rs⟩ := by
  unfold composeCoReceipts
  split
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq]
    constructor
    · intro he
      exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, he.symm⟩
    · intro he
      exact he.2.2.2.2.symm
  · rename_i hc
    constructor
    · intro he
      cases he
    · intro he
      refine absurd ?_ hc
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨he.1, he.2.1⟩, he.2.2.1⟩, he.2.2.2.1⟩

/-- **Every wire of an accepted diagram was checked.** Whenever a resolution and a hole of the
diagram share a pending id, that resolution is wired to that hole. -/
theorem wire_checked (env : WireEnv) (rs : List CoReceipt) (hlin : portsLinear rs = true)
    (hw : wiresOk env rs = true) {a b : CoReceipt} (ha : a ∈ rs) (hb : b ∈ rs)
    {f : FulfillPort} {w : AwaitPort} (hf : f ∈ a.fulfills) (hwm : w ∈ b.awaits)
    (hport : f.port = w.port) : Wired env a f b w := by
  have hfe : (⟨a.rank, f⟩ : FulfillEntry) ∈ (sortedFulfills rs).toList :=
    (sortByKey_perm _ _).mem_iff.2 (mem_fulfillTable.2 ⟨a, ha, f, hf, rfl⟩)
  have hwe : (⟨b.rank, w⟩ : AwaitEntry) ∈ (sortedAwaits rs).toList :=
    (sortByKey_perm _ _).mem_iff.2 (mem_awaitTable.2 ⟨b, hb, w, hwm, rfl⟩)
  simp only [portsLinear, Bool.and_eq_true] at hlin
  have hchk := List.all_eq_true.1 hw _ hfe
  have hk : FulfillEntry.key ⟨a.rank, f⟩ = AwaitEntry.key ⟨b.rank, w⟩ := by
    simp only [FulfillEntry.key, AwaitEntry.key, hport]
  unfold wireChecks at hchk
  rw [hk, lookup_of_mem AwaitEntry.key hlin.1 hwe] at hchk
  exact (wireOk_iff env a b f w).1 hchk

/-- An accepted diagram has linear ports: every pending id is awaited at most once and resolved at
most once across all its receipts. -/
theorem composeCoReceipts_ports_linear (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) (h : composeCoReceipts env shared rs = some c) :
    ((awaitTable rs).map (·.hole.port)).Nodup ∧ ((fulfillTable rs).map (·.fill.port)).Nodup := by
  obtain ⟨_, hlin, _, _, _⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 h
  simp only [portsLinear, Bool.and_eq_true] at hlin
  constructor
  · have h1 := ((sortByKey_perm AwaitEntry.key (awaitTable rs)).map AwaitEntry.key).nodup_iff.1
      (tableOk_nodup AwaitEntry.key hlin.1)
    refine nodup_of_map_nodup BitVec.toNat ?_
    rw [List.map_map]
    exact h1
  · have h1 := ((sortByKey_perm FulfillEntry.key (fulfillTable rs)).map FulfillEntry.key).nodup_iff.1
      (tableOk_nodup FulfillEntry.key hlin.2)
    refine nodup_of_map_nodup BitVec.toNat ?_
    rw [List.map_map]
    exact h1

/-- **No promise hole is allocated twice or filled twice.** A diagram in which two holes, or two
resolutions, carry one pending id does not compose. -/
theorem promise_hole_no_double_fill (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (hdup : ¬ ((awaitTable rs).map (·.hole.port)).Nodup ∨
      ¬ ((fulfillTable rs).map (·.fill.port)).Nodup) :
    composeCoReceipts env shared rs = none := by
  cases hc : composeCoReceipts env shared rs with
  | none => rfl
  | some c =>
    have hl := composeCoReceipts_ports_linear env shared rs c hc
    rcases hdup with hd | hd
    · exact absurd hl.1 hd
    · exact absurd hl.2 hd

/-- `b` awaits a promise that `a` resolves. -/
def Feeds (a b : CoReceipt) : Prop :=
  ∃ f, f ∈ a.fulfills ∧ ∃ w, w ∈ b.awaits ∧ f.port = w.port

/-- Causal dependency within a diagram: the transitive closure of `Feeds`. -/
inductive Causes (rs : List CoReceipt) : CoReceipt → CoReceipt → Prop where
  | step {a b : CoReceipt} : a ∈ rs → b ∈ rs → Feeds a b → Causes rs a b
  | trans {a b c : CoReceipt} : Causes rs a b → Causes rs b c → Causes rs a c

/-- In an accepted diagram, rank strictly increases along causal dependency. -/
theorem composeCoReceipts_rank_increases (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) (h : composeCoReceipts env shared rs = some c) {a b : CoReceipt}
    (hab : Causes rs a b) : a.rank < b.rank := by
  obtain ⟨_, hlin, hw, _, _⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 h
  induction hab with
  | step ha hb hfeeds =>
    obtain ⟨f, hf, w, hwm, hport⟩ := hfeeds
    exact (wire_checked env rs hlin hw ha hb hf hwm hport).2.2.1
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-- **A causal cycle is refused.** If some receipt of the diagram transitively awaits a promise it
resolves itself, the diagram does not compose, whatever ranks it claims. -/
theorem cyclic_wiring_refused (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (hcycle : ∃ a, Causes rs a a) : composeCoReceipts env shared rs = none := by
  cases hc : composeCoReceipts env shared rs with
  | none => rfl
  | some c =>
    obtain ⟨a, ha⟩ := hcycle
    exact absurd (composeCoReceipts_rank_increases env shared rs c hc ha) (Nat.lt_irrefl _)

/-- **A revoked lineage is refused.** If a resolution meets a hole of the diagram and any prefix of
its delegation chain has a revoked lineage nullifier, the diagram does not compose. -/
theorem revoked_lineage_refused (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    {a b : CoReceipt} (ha : a ∈ rs) (hb : b ∈ rs) {f : FulfillPort} {w : AwaitPort}
    (hf : f ∈ a.fulfills) (hwm : w ∈ b.awaits) (hport : f.port = w.port) (pre ext : Array Block)
    (hsplit : f.chain = pre ++ ext)
    (hrev : env.revoked.contains (credNul (lineageOf f.root pre.toList)) = true) :
    composeCoReceipts env shared rs = none := by
  cases hc : composeCoReceipts env shared rs with
  | none => rfl
  | some c =>
    obtain ⟨_, hlin, hw, _, _⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 hc
    have hclean := wired_revocation_clean (wire_checked env rs hlin hw ha hb hf hwm hport) pre ext
      hsplit
    rw [hrev] at hclean
    cases hclean

/-- **A closed diagram is one joint turn.** If the receipts compose and no port is left open, then:
the legs are a joint turn under the shared digest (so the total balance is conserved); every
resolution is wired to a hole and every hole to a resolution, each wire with agreeing payload
commitments, an admitted guard, a causally earlier and authorized resolver; ports are linear; and
there is no causal cycle. -/
theorem composeCoReceipts_closed_sound (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) (h : composeCoReceipts env shared rs = some c)
    (hopen : c.openAwaits = []) (hdangling : c.dangling = []) :
    (∃ j : JointTurn, j.legs = rs.map (·.turn) ∧ j.shared.tid = shared) ∧
      (∀ a f, a ∈ rs → f ∈ a.fulfills →
        ∃ b w, b ∈ rs ∧ w ∈ b.awaits ∧ f.port = w.port ∧ Wired env a f b w) ∧
      (∀ b w, b ∈ rs → w ∈ b.awaits →
        ∃ a f, a ∈ rs ∧ f ∈ a.fulfills ∧ f.port = w.port ∧ Wired env a f b w) ∧
      ((awaitTable rs).map (·.hole.port)).Nodup ∧ ((fulfillTable rs).map (·.fill.port)).Nodup ∧
      ∀ a, ¬ Causes rs a a := by
  have hlinear := composeCoReceipts_ports_linear env shared rs c h
  have hrank := fun (a : CoReceipt) (ha : Causes rs a a) =>
    Nat.lt_irrefl _ (composeCoReceipts_rank_increases env shared rs c h ha)
  obtain ⟨_, hlin, hw, hclosure, rfl⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 h
  have hlin' := hlin
  simp only [portsLinear, Bool.and_eq_true] at hlin'
  simp only at hopen hdangling
  refine ⟨?_, ?_, ?_, hlinear.1, hlinear.2, hrank⟩
  · apply (checkJoint_iff shared _).1
    simpa [closureOk, hopen, hdangling] using hclosure
  · intro a f ha hf
    have hfe : (⟨a.rank, f⟩ : FulfillEntry) ∈ (sortedFulfills rs).toList :=
      (sortByKey_perm _ _).mem_iff.2 (mem_fulfillTable.2 ⟨a, ha, f, hf, rfl⟩)
    have hsome := List.filter_eq_nil_iff.1 hdangling _ hfe
    cases hl : lookup AwaitEntry.key (sortedAwaits rs) (FulfillEntry.key ⟨a.rank, f⟩) with
    | none => simp [hl] at hsome
    | some e =>
      obtain ⟨he, hk⟩ := lookup_some AwaitEntry.key hlin'.1 hl
      obtain ⟨b, hb, w, hwm, rfl⟩ := mem_awaitTable.1 ((sortByKey_perm _ _).mem_iff.1 he)
      have hport : f.port = w.port := (BitVec.toNat_inj.1 hk).symm
      exact ⟨b, w, hb, hwm, hport, wire_checked env rs hlin hw ha hb hf hwm hport⟩
  · intro b w hb hwm
    have hwe : (⟨b.rank, w⟩ : AwaitEntry) ∈ (sortedAwaits rs).toList :=
      (sortByKey_perm _ _).mem_iff.2 (mem_awaitTable.2 ⟨b, hb, w, hwm, rfl⟩)
    have hsome := List.filter_eq_nil_iff.1 hopen _ hwe
    cases hl : lookup FulfillEntry.key (sortedFulfills rs) (AwaitEntry.key ⟨b.rank, w⟩) with
    | none => simp [hl] at hsome
    | some e =>
      obtain ⟨he, hk⟩ := lookup_some FulfillEntry.key hlin'.2 hl
      obtain ⟨a, ha, f, hf, rfl⟩ := mem_fulfillTable.1 ((sortByKey_perm _ _).mem_iff.1 he)
      have hport : f.port = w.port := BitVec.toNat_inj.1 hk
      exact ⟨a, f, ha, hf, hport, wire_checked env rs hlin hw ha hb hf hwm hport⟩

/-- Promise settlement publishes a batch only after all ports close. An abort, missing leg,
invalid wire, or failed posting retains the complete ledger, including the clearing account. -/
def settleCoReceipts (env : WireEnv) (n : Nat) (s : LedgerState) (shared : ByteArray)
    (rs : List CoReceipt) : LedgerState :=
  match composeCoReceipts env shared rs with
  | none => s
  | some c => if c.openAwaits.isEmpty && c.dangling.isEmpty then applyJoint n s shared c.legs else s

theorem settleCoReceipts_open_rollback {env : WireEnv} {n : Nat} {s : LedgerState}
    {shared : ByteArray} {rs : List CoReceipt} {c : Composite}
    (h : composeCoReceipts env shared rs = some c)
    (ho : c.openAwaits ≠ [] ∨ c.dangling ≠ []) : settleCoReceipts env n s shared rs = s := by
  simp only [settleCoReceipts, h]
  rcases ho with ho | ho <;> simp [ho]

/-- Conservation includes refused attempts and selectively withheld legs. -/
theorem settleCoReceipts_preserves (env : WireEnv) (n : Nat) (s : LedgerState)
    (shared : ByteArray) (rs : List CoReceipt) (hf : FloorsHold s.book) :
    FloorsHold (settleCoReceipts env n s shared rs).book ∧
      ∀ a, (settleCoReceipts env n s shared rs).book.assetSum a = s.book.assetSum a := by
  unfold settleCoReceipts
  split
  · exact ⟨hf, fun _ => rfl⟩
  · split
    · unfold applyJoint
      cases hs : stepJoint n s shared _ with
      | none => exact ⟨hf, fun _ => rfl⟩
      | some f => exact ⟨(stepJoint_refines_floorBook hf hs).2.1,
          (stepJoint_refines_floorBook hf hs).2.2.1⟩
    · exact ⟨hf, fun _ => rfl⟩
def runSettlements (env : WireEnv) (n : Nat) :
    LedgerState → List (ByteArray × List CoReceipt) → LedgerState
  | s, [] => s
  | s, (tid, rs) :: rest => runSettlements env n (settleCoReceipts env n s tid rs) rest
theorem runSettlements_preserves (env : WireEnv) (n : Nat)
    (attempts : List (ByteArray × List CoReceipt)) (s : LedgerState) (hf : FloorsHold s.book) :
    FloorsHold (runSettlements env n s attempts).book ∧
      ∀ a, (runSettlements env n s attempts).book.assetSum a = s.book.assetSum a := by
  induction attempts generalizing s with
  | nil => exact ⟨hf, fun _ => rfl⟩
  | cons e rest ih =>
    have hs := settleCoReceipts_preserves env n s e.1 e.2 hf
    have hr := ih _ hs.1
    exact ⟨hr.1, fun a => (hr.2 a).trans (hs.2 a)⟩

/-! ## 6. A closed diagram -/

/-- A leg of the witness diagram: a vat that held ten units. -/
def demoLeg (vat : VatId) (half : Int) (tid : ByteArray) : LocalTurn :=
  ⟨vat, tid, .empty, 10, half, 10 + half, 0, 0, 0⟩

/-- The root grant the witness resolver holds: right `1`, no caveat. -/
def demoGrant : Block := ⟨1, .const true, .empty, .empty⟩

/-- The turn digest of the witness diagram. -/
def demoShared : ByteArray := turnDigest [demoLeg 0 (-1) .empty, demoLeg 1 1 .empty]

/-- Two vats of ten units each and one promise: vat `0` pays one unit and resolves pending id `5`
under its grant; vat `1` receives the unit and awaits id `5` from a holder of that grant. -/
def demoDiagram : List CoReceipt :=
  [⟨demoLeg 0 (-1) demoShared, 0, [], [⟨5, .empty, demoGrant, #[]⟩]⟩,
    ⟨demoLeg 1 1 demoShared, 1, [⟨5, .empty, .tt, rootLineage demoGrant, 1⟩], []⟩]

/-- Nothing revoked, no fact bound, no discharge, an empty step. -/
def demoEnv : WireEnv := ⟨RevokedSet.empty, fun _ => .unbound3, [], fun _ => ⟨none, none⟩⟩

/-- The premises of `composeCoReceipts_closed_sound` are met together: the two-vat diagram composes
and is closed. -/
theorem composeCoReceipts_closed_inhabited :
    ∃ c, composeCoReceipts demoEnv demoShared demoDiagram = some c ∧ c.openAwaits = [] ∧
      c.dangling = [] ∧ demoDiagram.length = 2 := by
  have hA : sortedAwaits demoDiagram = #[⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩] := by
    simp [sortedAwaits, sortByKey, awaitTable, demoDiagram]
  have hF : sortedFulfills demoDiagram = #[⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩] := by
    simp [sortedFulfills, sortByKey, fulfillTable, demoDiagram]
  have hTA : tableOk AwaitEntry.key
      #[⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩] = true := by
    simp [tableOk, ascending]
  have hTF : tableOk FulfillEntry.key #[⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩] = true := by
    simp [tableOk, ascending]
  have hLA : lookup AwaitEntry.key #[⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩]
      (FulfillEntry.key ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩) =
        some ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩ :=
    lookup_of_mem AwaitEntry.key hTA (x := ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩)
      (by simp)
  have hLF : lookup FulfillEntry.key #[⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩]
      (AwaitEntry.key ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩) =
        some ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩ :=
    lookup_of_mem FulfillEntry.key hTF (x := ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩) (by simp)
  have hfold : foldChain demoEnv.revoked demoEnv.facts demoGrant #[] =
      some ⟨1, .true3, rootLineage demoGrant⟩ := by
    simp [foldChain, foldRoot, lineageLive, channelLive, RevokedSet.contains, RevokedSet.empty,
      searchAux, demoEnv, demoGrant, Caveat.eval]
  have hwire : wireOk demoEnv ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩
      ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩ = true :=
    (wireOk_iff demoEnv ⟨demoLeg 0 (-1) demoShared, 0, [], [⟨5, .empty, demoGrant, #[]⟩]⟩
      ⟨demoLeg 1 1 demoShared, 1, [⟨5, .empty, .tt, rootLineage demoGrant, 1⟩], []⟩
      ⟨5, .empty, demoGrant, #[]⟩ ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩).2
      ⟨rfl, admits_tt _ _, by decide, rfl, _, hfold, by decide⟩
  have hjoint : checkJoint demoShared (demoDiagram.map (·.turn)) = true := by
    simp only [checkJoint, demoDiagram, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨by decide, by decide⟩, ?_⟩, rfl, rfl⟩, ?_⟩, by decide⟩
    · exact (vatsDistinct_iff _).2 (by simp [demoLeg])
    · simp only [demoShared, turnDigest, List.map_cons, List.map_nil, LocalTurn.legBytes, demoLeg]
  refine ⟨⟨demoShared, demoDiagram.map (·.turn), openAwaitsOf demoDiagram, danglingOf demoDiagram⟩,
    (composeCoReceipts_eq_some_iff _ _ _ _).2 ⟨?_, ?_, ?_, ?_, rfl⟩, ?_, ?_, rfl⟩
  · intro r hr
    simp only [demoDiagram, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · simp only [portsLinear, hA, hF, hTA, hTF, Bool.and_self]
  · simp only [wiresOk, hA, hF, List.all_cons, List.all_nil, Bool.and_true, wireChecks, hLA, hwire]
  · simp only [closureOk, hjoint, Bool.or_true]
  · simp only [openAwaitsOf, hA, hF, List.filter_cons, List.filter_nil, hLF, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte]
  · simp only [danglingOf, hA, hF, List.filter_cons, List.filter_nil, hLA, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte]

end Obend.Polis.JointCoReceipt
end
