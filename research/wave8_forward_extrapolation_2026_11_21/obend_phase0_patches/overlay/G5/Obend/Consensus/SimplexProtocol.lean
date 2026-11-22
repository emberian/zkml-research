module
/-
# Obend.Consensus.SimplexProtocol — the honest-node relation, the adversary, and chain consistency

`Obend.Consensus.Simplex` proves quorum lemmas over abstract predicates and says in its header that
it holds no protocol. This module is the protocol, as a relation (2026-11-04):

- A CHAIN has one entry per view, oldest first: the block the view notarized, or the view's dummy
  (`Entry`, `Chain`). Its height is its number of blocks.
- A MESSAGE is a sender, a view, a kind (`propose`, `vote`, `finalize`) and a target: a block,
  named by the whole chain it ends, or a view's dummy. The global state is the list of messages
  ever sent (`Sent`); an honest node's own state is read from its own messages, so "vote once per
  view" needs no other field.
- The ADVERSARY is `Step.inject`: any message whose sender the `Protocol` marks faulty. Honest
  steps are `propose` (the view's leader), `vote` (once per view; for a block only if the block
  extends a chain whose every entry is notarized) and `finalize` (only a block the node voted for
  in that view and has seen notarized). `Reach` closes the steps from the empty message list.
- `Inv` is what every reachable message list satisfies (`reach_inv`); the theorems below take
  `Inv` and the `Protocol`'s bounds (`3f+1 ≤ committee.length`, at most `f` faulty, `Nodup`).
- The QUORUM for notarizing (vote) and finalizing is `n - f` of the `n = committee.length`
  members (`Protocol.quorum`; gate G5, 2026-11-21). At `n = 3f+1` that is the familiar `2f+1`;
  for `n > 3f+1` a fixed `2f+1` would let two quorums meet only in faulty nodes (at `n = 5, f = 1`
  two 3-member quorums can share one node), while two `n - f` quorums share `n - 2f ≥ f+1`.

What is proved, all from `Simplex.honest_quorum_intersection_nf`:
- `notarized_block_unique`: one view notarizes one block.
- `finalized_no_dummy`: a view that finalized a block did not notarize its dummy.
- `finalized_prefix_of_notarized`: a finalized chain is a prefix of every notarized chain that
  reaches its view; hence `finalized_consistent` (two finalized chains, one is a prefix of the
  other) and `fin_cert_unique_per_height` (two finalized chains of one height carry the same
  blocks).
- `accountable_of_threshold`: two conflicting quorums of `q` votes in one view, with
  `n + f + 1 ≤ 2q`, name at least `f+1` signers, each with its two votes in the message list,
  which `SlashingReceipt.checks` re-reads; none of them kept the vote-once rule, and under the
  fault bound each is faulty (`signers_faulty`). `accountable_nf` and `accountable_protocol` are
  the `n - f` instances (`n ≥ 3f+1`); `accountable` is the `2f+1`-in-at-most-`3f+1` instance.

`Entry.encode` is the one wire form of an entry (tag, 8-byte view, 32-byte payload): a block's
payload is a 256-bit digest, and `Entry.encode_injective` reads every canonical entry back. The
finality digest (`Finality.chainDigest`) and the signed wire (`SimplexLiveness`) both use it.

What is not here: liveness, timers, signatures (a message's sender is taken as its signer), and
the executable node. `Obend.Consensus.SimplexTrace` decides whether a recorded run was a sequence
of these steps (`checkTrace_sound`), and `crates/obend-node/src/net.rs` records its run as that
trace; the node casts one vote per view and finalizes only after a quorum of votes.

`Obend.Consensus.Simplex.State` is not used: it is a per-node fragment of a five-kind protocol
(`candidate`, `ready`) that is not this one, and nothing there is needed once the state is the
message list.
-/

public import Obend.Consensus.Simplex
public import Obend.Digest.HashBytes

public section

/- Constructive collision evidence scoped to the actual finite transcript inputs. -/
namespace Obend.Digest.HashBytes
structure CollisionPair (H : Hash) (S : List UInt8 → Prop) where
  msgA : List UInt8
  msgB : List UInt8
  memA : S msgA
  memB : S msgB
  distinct : msgA ≠ msgB
  sameDigest : ofBE (H msgA) = ofBE (H msgB)

theorem CollisionPair.toCollisionAmong {H : Hash} {S : List UInt8 → Prop}
    (w : CollisionPair H S) : CollisionAmong H S :=
  ⟨w.msgA, w.msgB, w.memA, w.memB, w.distinct, w.sameDigest⟩

/-- Decide equality of these preimages, retaining the concrete pair on collision. -/
def extractBinding (H : Hash) (a b : List UInt8) {P : Prop}
    (inj : a = b → P) (eq : ofBE (H a) = ofBE (H b)) :
    PSum (PLift P) (CollisionPair H (fun x => x = a ∨ x = b)) :=
  if h : a = b then .inl ⟨inj h⟩
  else .inr ⟨a, b, .inl rfl, .inr rfl, h, eq⟩

theorem bindingResult {H : Hash} {a b : List UInt8} {P : Prop}
    (w : PSum (PLift P) (CollisionPair H (fun x => x = a ∨ x = b))) :
    P ∨ CollisionAmong H (fun x => x = a ∨ x = b) :=
  match w with
  | .inl h => .inl h.down
  | .inr c => .inr c.toCollisionAmong
end Obend.Digest.HashBytes

namespace Obend.Consensus.SimplexProtocol

open Obend.Consensus.Simplex (NodeId honest_quorum_intersection_nf list_filter_add_card
  list_filter_length_le nodup_filter_simplex)
open Obend.Digest

set_option autoImplicit false

/-! ## 1. Chains, targets, messages -/

/-- One view's entry in a chain: the block that view notarized (`payload` names it), or the
view's dummy. -/
inductive Entry where
  | block (view : Nat) (payload : Nat)
  | dummy (view : Nat)
  deriving Repr

@[expose] def Entry.view : Entry → Nat
  | .block v _ => v
  | .dummy v => v

@[expose] def Entry.isBlock : Entry → Bool
  | .block _ _ => true
  | .dummy _ => false

/-- A chain: one entry per view, oldest first; the entry at index `k` is view `k + 1`'s. -/
abbrev Chain := List Entry

/-- The height of a chain: its number of blocks (dummies do not count). -/
abbrev Chain.height (c : Chain) : Nat := (c.filter Entry.isBlock).length

/-- The blocks of a chain, in order. -/
abbrev Chain.blocks (c : Chain) : Chain := c.filter Entry.isBlock

/-- What a vote is for: a block, named by the whole chain it ends, or a view's dummy. -/
inductive Target where
  | block (c : Chain)
  | dummy (v : Nat)
  deriving Repr

inductive Kind where
  | propose
  | vote
  | finalize
  deriving Repr

structure Msg where
  sender : NodeId
  view : Nat
  kind : Kind
  target : Target
  deriving Repr

deriving instance @[expose] DecidableEq for Entry, Target, Kind, Msg

/-- Every message ever sent, newest first. -/
abbrev Sent := List Msg

/-! Views are `Nat` here, not `Obend.Consensus.Simplex.View`: `omega` does not see through the
imported abbreviation. -/

/-! ## 2. The committee and the adversary -/

/-- A committee of `n ≥ 3f+1` distinct nodes of which at most `f` are faulty. -/
structure Protocol where
  committee : List NodeId
  f : Nat
  faulty : NodeId → Bool
  nodup : committee.Nodup
  size : 3 * f + 1 ≤ committee.length
  faultBound : (committee.filter faulty).length ≤ f

/-- The vote and finalize quorum: `n - f` of the `n` committee members (`2f+1` when `n = 3f+1`).
Two such quorums overlap in `n - 2f ≥ f+1` members (`Simplex.quorum_overlap_nf`). -/
abbrev Protocol.quorum (P : Protocol) : Nat := P.committee.length - P.f

abbrev Protocol.honest (P : Protocol) (n : NodeId) : Prop := n ∈ P.committee ∧ P.faulty n = false

/-- The leader of a view: round-robin over the committee. -/
abbrev Protocol.leader (P : Protocol) (v : Nat) : NodeId :=
  P.committee.getD ((v - 1) % P.committee.length) 0

/-! ## 3. What the message list says -/

/-- `n` voted for `t` in view `v`. -/
abbrev voted (sent : Sent) (n : NodeId) (v : Nat) (t : Target) : Bool :=
  sent.contains ⟨n, v, .vote, t⟩

/-- `n` cast some vote in view `v`. -/
@[expose] def votedAny (sent : Sent) (n : NodeId) (v : Nat) : Bool :=
  sent.any fun m => m.sender == n && m.view == v && m.kind == .vote

/-- `n` cast a finalize vote for the block `c` in view `v`. -/
@[expose] def finalizeVoted (sent : Sent) (n : NodeId) (v : Nat) (c : Chain) : Bool :=
  sent.contains ⟨n, v, .finalize, .block c⟩

theorem voted_iff (sent : Sent) (n : NodeId) (v : Nat) (t : Target) :
    voted sent n v t = true ↔ (⟨n, v, .vote, t⟩ : Msg) ∈ sent :=
  List.contains_iff_mem

theorem finalizeVoted_iff (sent : Sent) (n : NodeId) (v : Nat) (c : Chain) :
    finalizeVoted sent n v c = true ↔ (⟨n, v, .finalize, .block c⟩ : Msg) ∈ sent :=
  List.contains_iff_mem

theorem votedAny_of_mem {sent : Sent} {m : Msg} (hm : m ∈ sent) (hk : m.kind = .vote) :
    votedAny sent m.sender m.view = true := by
  unfold votedAny
  rw [List.any_eq_true]
  exact ⟨m, hm, by simp [hk]⟩

/-- The committee members who voted for `t` in `v`. -/
abbrev voters (P : Protocol) (sent : Sent) (v : Nat) (t : Target) : List NodeId :=
  P.committee.filter fun n => voted sent n v t

abbrev votesFor (P : Protocol) (sent : Sent) (v : Nat) (t : Target) : Nat :=
  (voters P sent v t).length

/-- A block is notarized in its view by a quorum of votes for the chain it ends. -/
abbrev NotarizedBlock (P : Protocol) (sent : Sent) (v : Nat) (c : Chain) : Prop :=
  P.quorum ≤ votesFor P sent v (.block c)

/-- A view's dummy is notarized by a quorum of votes for it. -/
abbrev NotarizedDummy (P : Protocol) (sent : Sent) (v : Nat) : Prop :=
  P.quorum ≤ votesFor P sent v (.dummy v)

/-- A block is finalized in its view by a quorum of finalize votes. -/
abbrev Finalized (P : Protocol) (sent : Sent) (v : Nat) (c : Chain) : Prop :=
  P.quorum ≤ (P.committee.filter fun n => finalizeVoted sent n v c).length

/-- The entry at index `k` of a chain is notarized: a dummy by its view's dummy notarization, a
block by a notarization of the chain up to it (`upto = c.take (k+1)`); and it is view `k+1`'s. -/
@[expose] def EntryNotarized (P : Protocol) (sent : Sent) (k : Nat) (upto : Chain) : Entry → Prop
  | .dummy v => v = k + 1 ∧ NotarizedDummy P sent (k + 1)
  | .block v _ => v = k + 1 ∧ NotarizedBlock P sent (k + 1) upto

/-- Every entry of the chain is notarized in its view. -/
abbrev ChainNotarized (P : Protocol) (sent : Sent) (c : Chain) : Prop :=
  ∀ k (hk : k < c.length), EntryNotarized P sent k (c.take (k + 1)) c[k]

/-! ## 4. The honest rules and the steps -/

/-- The honest vote rule in view `v` (`1 ≤ v`): a dummy vote is for this view's dummy; a block
vote is for a chain that ends in a block of this view, extends a chain of `v-1` entries each of
which is notarized, and was proposed by the view's leader. -/
@[expose] def VoteRule (P : Protocol) (sent : Sent) (v : Nat) : Target → Prop
  | .block c => 1 ≤ v ∧ ∃ p x, c = p ++ [.block v x] ∧ p.length = v - 1 ∧ ChainNotarized P sent p ∧
      (⟨P.leader v, v, .propose, .block c⟩ : Msg) ∈ sent
  | .dummy w => 1 ≤ v ∧ w = v

/-- One step of the system: the adversary injects any message from a faulty sender; an honest
node proposes (if it leads the view), votes (once per view, by `VoteRule`) or finalizes (a block
it voted for in that view and has seen notarized). -/
inductive Step (P : Protocol) : Sent → Sent → Prop
  | inject (sent : Sent) (m : Msg) (hf : P.faulty m.sender = true) :
      Step P sent (m :: sent)
  | propose (sent : Sent) (n : NodeId) (v : Nat) (c : Chain)
      (hn : P.honest n) (hl : n = P.leader v) :
      Step P sent (⟨n, v, .propose, .block c⟩ :: sent)
  | vote (sent : Sent) (n : NodeId) (v : Nat) (t : Target)
      (hn : P.honest n) (hfresh : votedAny sent n v = false) (hrule : VoteRule P sent v t) :
      Step P sent (⟨n, v, .vote, t⟩ :: sent)
  | finalize (sent : Sent) (n : NodeId) (v : Nat) (c : Chain)
      (hn : P.honest n) (hvote : voted sent n v (.block c) = true)
      (hnot : NotarizedBlock P sent v c) :
      Step P sent (⟨n, v, .finalize, .block c⟩ :: sent)

inductive Reach (P : Protocol) : Sent → Prop
  | nil : Reach P []
  | step {s s' : Sent} (h : Reach P s) (hs : Step P s s') : Reach P s'

/-! ## 5. Monotonicity: a notarization, once seen, stays -/

theorem filter_length_mono {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x with
    | false => cases q x <;> simp <;> omega
    | true => rw [h x hp]; simp; omega

theorem voted_cons (sent : Sent) (m : Msg) (n : NodeId) (v : Nat) (t : Target)
    (h : voted sent n v t = true) : voted (m :: sent) n v t = true := by
  rw [voted_iff] at h ⊢
  exact List.mem_cons_of_mem m h

theorem finalizeVoted_cons (sent : Sent) (m : Msg) (n : NodeId) (v : Nat) (c : Chain)
    (h : finalizeVoted sent n v c = true) : finalizeVoted (m :: sent) n v c = true := by
  rw [finalizeVoted_iff] at h ⊢
  exact List.mem_cons_of_mem m h

theorem votesFor_cons (P : Protocol) (sent : Sent) (m : Msg) (v : Nat) (t : Target) :
    votesFor P sent v t ≤ votesFor P (m :: sent) v t :=
  filter_length_mono _ _ P.committee fun n h => voted_cons sent m n v t h

theorem notarizedBlock_cons {P : Protocol} {sent : Sent} (m : Msg) {v : Nat} {c : Chain}
    (h : NotarizedBlock P sent v c) : NotarizedBlock P (m :: sent) v c :=
  Nat.le_trans h (votesFor_cons P sent m v (.block c))

theorem notarizedDummy_cons {P : Protocol} {sent : Sent} (m : Msg) {v : Nat}
    (h : NotarizedDummy P sent v) : NotarizedDummy P (m :: sent) v :=
  Nat.le_trans h (votesFor_cons P sent m v (.dummy v))

theorem entryNotarized_cons {P : Protocol} {sent : Sent} (m : Msg) {k : Nat} {upto : Chain}
    {e : Entry} (h : EntryNotarized P sent k upto e) : EntryNotarized P (m :: sent) k upto e := by
  cases e with
  | dummy v => exact ⟨h.1, notarizedDummy_cons m h.2⟩
  | block v x => exact ⟨h.1, notarizedBlock_cons m h.2⟩

theorem chainNotarized_cons {P : Protocol} {sent : Sent} (m : Msg) {c : Chain}
    (h : ChainNotarized P sent c) : ChainNotarized P (m :: sent) c :=
  fun k hk => entryNotarized_cons m (h k hk)

/-! Every notion above is monotone in the message list, not only under `cons`: a node that reads
a sub-list of the messages (its own deliveries) concludes nothing the whole list does not. -/

theorem voted_mono {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) {n : NodeId} {v : Nat} {t : Target}
    (hv : voted s₁ n v t = true) : voted s₂ n v t = true :=
  (voted_iff s₂ n v t).2 (h _ ((voted_iff s₁ n v t).1 hv))

theorem votesFor_mono (P : Protocol) {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) (v : Nat) (t : Target) :
    votesFor P s₁ v t ≤ votesFor P s₂ v t :=
  filter_length_mono _ _ P.committee fun _ hn => voted_mono h hn

theorem notarizedBlock_mono {P : Protocol} {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) {v : Nat}
    {c : Chain} (hn : NotarizedBlock P s₁ v c) : NotarizedBlock P s₂ v c :=
  Nat.le_trans hn (votesFor_mono P h v (.block c))

theorem notarizedDummy_mono {P : Protocol} {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) {v : Nat}
    (hn : NotarizedDummy P s₁ v) : NotarizedDummy P s₂ v :=
  Nat.le_trans hn (votesFor_mono P h v (.dummy v))

theorem chainNotarized_mono {P : Protocol} {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) {c : Chain}
    (hc : ChainNotarized P s₁ c) : ChainNotarized P s₂ c := by
  intro k hk
  have he := hc k hk
  cases hck : c[k] with
  | dummy v => rw [hck] at he; exact ⟨he.1, notarizedDummy_mono h he.2⟩
  | block v x => rw [hck] at he; exact ⟨he.1, notarizedBlock_mono h he.2⟩

theorem voteRule_mono {P : Protocol} {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) {v : Nat} {t : Target}
    (hr : VoteRule P s₁ v t) : VoteRule P s₂ v t := by
  cases t with
  | dummy w => exact hr
  | block c =>
    obtain ⟨h1, p, x, hc, hl, hn, hp⟩ := hr
    exact ⟨h1, p, x, hc, hl, chainNotarized_mono h hn, h _ hp⟩

theorem finalized_mono {P : Protocol} {s₁ s₂ : Sent} (h : ∀ m ∈ s₁, m ∈ s₂) {v : Nat} {c : Chain}
    (hf : Finalized P s₁ v c) : Finalized P s₂ v c :=
  Nat.le_trans hf (filter_length_mono _ _ P.committee fun n hn =>
    (finalizeVoted_iff s₂ n v c).2 (h _ ((finalizeVoted_iff s₁ n v c).1 hn)))

theorem take_append_left {α : Type} :
    ∀ (l₁ l₂ : List α) (n : Nat), n ≤ l₁.length → (l₁ ++ l₂).take n = l₁.take n
  | _, _, 0, _ => by simp
  | [], _, n + 1, h => by simp at h
  | x :: xs, l₂, n + 1, h => by
    simp only [List.cons_append, List.take_succ_cons]
    rw [take_append_left xs l₂ n (by simpa using h)]

/-- Extending a notarized chain of `v-1` entries by a block of view `v` that is itself notarized
gives a notarized chain. -/
theorem chainNotarized_snoc {P : Protocol} {sent : Sent} {p : Chain} {v : Nat} {x : Nat}
    (hp : ChainNotarized P sent p) (hlen : p.length = v - 1) (hv : 1 ≤ v)
    (hn : NotarizedBlock P sent v (p ++ [.block v x])) :
    ChainNotarized P sent (p ++ [.block v x]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hkp : k < p.length
  · have hget : (p ++ [Entry.block v x])[k] = p[k] := List.getElem_append_left hkp
    have htake : (p ++ [Entry.block v x]).take (k + 1) = p.take (k + 1) :=
      take_append_left p [Entry.block v x] (k + 1) (by omega)
    rw [hget, htake]
    exact hp k hkp
  · have hkeq : k = p.length := by omega
    have hget : (p ++ [Entry.block v x])[k] = Entry.block v x := by
      rw [List.getElem_append_right (by omega)]
      simp [hkeq]
    have htake : (p ++ [Entry.block v x]).take (k + 1) = p ++ [Entry.block v x] :=
      List.take_of_length_le (by simp; omega)
    rw [hget, htake]
    have hvk : v = k + 1 := by omega
    show v = k + 1 ∧ NotarizedBlock P sent (k + 1) (p ++ [Entry.block v x])
    refine ⟨hvk, ?_⟩
    rw [← hvk]
    exact hn

/-! ## 6. The invariant of every reachable message list -/

/-- What honest senders' messages satisfy in every reachable message list. -/
structure Inv (P : Protocol) (sent : Sent) : Prop where
  /-- An honest node votes once per view: two of its votes in one view have one target. -/
  voteOnce : ∀ m ∈ sent, ∀ m' ∈ sent, P.honest m.sender → m.kind = .vote → m'.kind = .vote →
    m.sender = m'.sender → m.view = m'.view → m.target = m'.target
  /-- An honest block vote is for a chain that ends in a block of its view and extends a
  notarized chain of `view - 1` entries. -/
  voteRule : ∀ m ∈ sent, P.honest m.sender → m.kind = .vote → ∀ c, m.target = .block c →
    1 ≤ m.view ∧ ∃ p x, c = p ++ [.block m.view x] ∧ p.length = m.view - 1 ∧ ChainNotarized P sent p
  /-- An honest finalize vote is for a block the node voted for in that view and that is
  notarized. -/
  finRule : ∀ m ∈ sent, P.honest m.sender → m.kind = .finalize → ∀ c, m.target = .block c →
    voted sent m.sender m.view (.block c) = true ∧ NotarizedBlock P sent m.view c

theorem inv_nil (P : Protocol) : Inv P [] where
  voteOnce := fun _ h => absurd h (List.not_mem_nil)
  voteRule := fun _ h => absurd h (List.not_mem_nil)
  finRule := fun _ h => absurd h (List.not_mem_nil)

theorem honest_not_faulty {P : Protocol} {n : NodeId} (h : P.honest n) (hf : P.faulty n = true) : False := by
  rw [h.2] at hf; cases hf

/-- Adding a message that keeps the three rules for itself keeps the invariant: the old messages'
clauses are monotone in the message list. -/
theorem inv_cons {P : Protocol} {sent : Sent} (hI : Inv P sent) (m : Msg)
    (hOnce : ∀ m' ∈ sent, P.honest m.sender → m.kind = .vote → m'.kind = .vote →
      m.sender = m'.sender → m.view = m'.view → m.target = m'.target)
    (hVote : P.honest m.sender → m.kind = .vote → ∀ c, m.target = .block c →
      1 ≤ m.view ∧ ∃ p x, c = p ++ [.block m.view x] ∧ p.length = m.view - 1 ∧ ChainNotarized P sent p)
    (hFin : P.honest m.sender → m.kind = .finalize → ∀ c, m.target = .block c →
      voted sent m.sender m.view (.block c) = true ∧ NotarizedBlock P sent m.view c) :
    Inv P (m :: sent) where
  voteOnce := by
    intro a ha b hb hon hka hkb hs hv
    rcases List.mem_cons.1 ha with ha' | ha'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [ha', hb']
      · rw [ha'] at hon hka hs hv ⊢
        exact hOnce b hb' hon hka hkb hs hv
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [hb'] at hkb hs hv ⊢
        have hon' : P.honest m.sender := hs ▸ hon
        exact (hOnce a ha' hon' hkb hka hs.symm hv.symm).symm
      · exact hI.voteOnce a ha' b hb' hon hka hkb hs hv
  voteRule := by
    intro a ha hon hk c hc
    rcases List.mem_cons.1 ha with rfl | ha
    · obtain ⟨h1, p, x, hcp, hlen, hnot⟩ := hVote hon hk c hc
      exact ⟨h1, p, x, hcp, hlen, chainNotarized_cons a hnot⟩
    · obtain ⟨h1, p, x, hcp, hlen, hnot⟩ := hI.voteRule a ha hon hk c hc
      exact ⟨h1, p, x, hcp, hlen, chainNotarized_cons m hnot⟩
  finRule := by
    intro a ha hon hk c hc
    rcases List.mem_cons.1 ha with rfl | ha
    · obtain ⟨hv, hn⟩ := hFin hon hk c hc
      exact ⟨voted_cons sent a _ _ _ hv, notarizedBlock_cons a hn⟩
    · obtain ⟨hv, hn⟩ := hI.finRule a ha hon hk c hc
      exact ⟨voted_cons sent m _ _ _ hv, notarizedBlock_cons m hn⟩

theorem inv_step {P : Protocol} {s s' : Sent} (hI : Inv P s) (hs : Step P s s') : Inv P s' := by
  cases hs with
  | inject m hf =>
    refine inv_cons hI m ?_ ?_ ?_
    · intro m' _ hon _ _ _ _; exact absurd hf (fun h => honest_not_faulty hon h)
    · intro hon; exact absurd hf (fun h => honest_not_faulty hon h)
    · intro hon; exact absurd hf (fun h => honest_not_faulty hon h)
  | propose n v c hn hl =>
    refine inv_cons hI _ ?_ ?_ ?_
    · intro _ _ _ hk; cases hk
    · intro _ hk; cases hk
    · intro _ hk; cases hk
  | vote n v t hn hfresh hrule =>
    refine inv_cons hI _ ?_ ?_ ?_
    · intro m' hm' _ _ hk' hs hv
      have := votedAny_of_mem hm' hk'
      simp only at hs hv
      rw [← hs, ← hv] at this
      rw [this] at hfresh; cases hfresh
    · intro _ _ c hc
      simp only at hc
      subst hc
      obtain ⟨h1, p, x, hcp, hlen, hnot, _⟩ := hrule
      exact ⟨h1, p, x, hcp, hlen, hnot⟩
    · intro _ hk; cases hk
  | finalize n v c hn hvote hnot =>
    refine inv_cons hI _ ?_ ?_ ?_
    · intro _ _ _ hk; cases hk
    · intro _ hk; cases hk
    · intro _ _ c' hc'
      simp only at hc'
      cases hc'
      exact ⟨hvote, hnot⟩

/-- **Every reachable message list satisfies the invariant.** -/
theorem reach_inv {P : Protocol} {s : Sent} (h : Reach P s) : Inv P s := by
  induction h with
  | nil => exact inv_nil P
  | step _ hs ih => exact inv_step ih hs

/-! ## 7. Safety, from the quorum lemma -/

/-- A quorum of committee members with a property contains an honest one. -/
theorem honest_of_quorum (P : Protocol) (p : NodeId → Bool)
    (h : P.quorum ≤ (P.committee.filter p).length) :
    ∃ n ∈ P.committee, p n = true ∧ P.faulty n = false := by
  obtain ⟨n, hn, hp, _, hf⟩ :=
    honest_quorum_intersection_nf P.committee P.f p p P.faulty P.size h h P.faultBound
  exact ⟨n, hn, hp, hf⟩

/-- **One view notarizes one block.** Two notarizing quorums share an honest member, who voted
once. -/
theorem notarized_block_unique {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat}
    {c₁ c₂ : Chain} (h₁ : NotarizedBlock P sent v c₁) (h₂ : NotarizedBlock P sent v c₂) :
    c₁ = c₂ := by
  obtain ⟨n, hn, hv₁, hv₂, hf⟩ :=
    honest_quorum_intersection_nf P.committee P.f (fun n => voted sent n v (.block c₁))
      (fun n => voted sent n v (.block c₂)) P.faulty P.size h₁ h₂ P.faultBound
  have hm₁ := (voted_iff sent n v (.block c₁)).1 hv₁
  have hm₂ := (voted_iff sent n v (.block c₂)).1 hv₂
  have := hI.voteOnce _ hm₁ _ hm₂ ⟨hn, hf⟩ rfl rfl rfl rfl
  exact Target.block.inj this

/-- **A view that finalized a block did not notarize its dummy.** An honest member of both quorums
would have voted for the block (it finalized it) and for the dummy. -/
theorem finalized_no_dummy {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat} {c : Chain}
    (hf : Finalized P sent v c) : ¬ NotarizedDummy P sent v := by
  intro hd
  obtain ⟨n, hn, hfin, hdum, hfault⟩ :=
    honest_quorum_intersection_nf P.committee P.f (fun n => finalizeVoted sent n v c)
      (fun n => voted sent n v (.dummy v)) P.faulty P.size hf hd P.faultBound
  have hmf := (finalizeVoted_iff sent n v c).1 hfin
  have hvb := (hI.finRule _ hmf ⟨hn, hfault⟩ rfl c rfl).1
  have hmb := (voted_iff sent n v (.block c)).1 hvb
  have hmd := (voted_iff sent n v (.dummy v)).1 hdum
  have := hI.voteOnce _ hmb _ hmd ⟨hn, hfault⟩ rfl rfl rfl rfl
  cases this

/-- **A finalized block is notarized**, and its chain is a block of its view on a notarized
chain of `v - 1` entries. -/
theorem finalized_shape {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat} {c : Chain}
    (hf : Finalized P sent v c) :
    NotarizedBlock P sent v c ∧ 1 ≤ v ∧
      ∃ p x, c = p ++ [.block v x] ∧ p.length = v - 1 ∧ ChainNotarized P sent p := by
  obtain ⟨n, hn, hfin, hfault⟩ := honest_of_quorum P (fun n => finalizeVoted sent n v c) hf
  have hmf := (finalizeVoted_iff sent n v c).1 hfin
  obtain ⟨hvb, hnot⟩ := hI.finRule _ hmf ⟨hn, hfault⟩ rfl c rfl
  have hmb := (voted_iff sent n v (.block c)).1 hvb
  obtain ⟨h1, p, x, hcp, hlen, hpn⟩ := hI.voteRule _ hmb ⟨hn, hfault⟩ rfl c rfl
  simp only at h1 hcp hlen
  exact ⟨hnot, h1, p, x, hcp, hlen, hpn⟩

theorem finalized_notarized {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat} {c : Chain}
    (hf : Finalized P sent v c) : NotarizedBlock P sent v c :=
  (finalized_shape hI hf).1

theorem finalized_length {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat} {c : Chain}
    (hf : Finalized P sent v c) : c.length = v := by
  obtain ⟨_, h1, p, x, hcp, hlen, _⟩ := finalized_shape hI hf
  rw [hcp, List.length_append, List.length_singleton]
  omega

/-- A finalized chain is itself a notarized chain. -/
theorem finalized_chainNotarized {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat}
    {c : Chain} (hf : Finalized P sent v c) : ChainNotarized P sent c := by
  obtain ⟨hnot, h1, p, x, hcp, hlen, hpn⟩ := finalized_shape hI hf
  subst hcp
  exact chainNotarized_snoc hpn hlen h1 hnot

/-- **A finalized chain is a prefix of every notarized chain that reaches its view.** The notarized
chain's entry for that view is notarized: not the dummy (`finalized_no_dummy`), so a block, and
one view notarizes one block (`notarized_block_unique`). -/
theorem finalized_prefix_of_notarized {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat}
    {c c' : Chain} (hf : Finalized P sent v c) (hc' : ChainNotarized P sent c')
    (hlen : v ≤ c'.length) : c <+: c' := by
  obtain ⟨hnot, h1, _, _, _, _, _⟩ := finalized_shape hI hf
  have hk : v - 1 < c'.length := by omega
  have he := hc' (v - 1) hk
  have hv : v - 1 + 1 = v := by omega
  cases hget : c'[v - 1] with
  | dummy w =>
    rw [hget] at he
    have hd : NotarizedDummy P sent (v - 1 + 1) := he.2
    rw [hv] at hd
    exact absurd hd (finalized_no_dummy hI hf)
  | block w x =>
    rw [hget] at he
    have hb : NotarizedBlock P sent (v - 1 + 1) (c'.take (v - 1 + 1)) := he.2
    rw [hv] at hb
    have heq := notarized_block_unique hI hnot hb
    rw [heq]
    exact List.take_prefix v c'

/-- **Two finalized chains are consistent**: one is a prefix of the other. -/
theorem finalized_consistent {P : Protocol} {sent : Sent} (hI : Inv P sent) {v₁ v₂ : Nat}
    {c₁ c₂ : Chain} (h₁ : Finalized P sent v₁ c₁) (h₂ : Finalized P sent v₂ c₂) :
    c₁ <+: c₂ ∨ c₂ <+: c₁ := by
  have l₁ := finalized_length hI h₁
  have l₂ := finalized_length hI h₂
  by_cases hle : v₁ ≤ v₂
  · left
    exact finalized_prefix_of_notarized hI h₁ (finalized_chainNotarized hI h₂) (by omega)
  · right
    exact finalized_prefix_of_notarized hI h₂ (finalized_chainNotarized hI h₁) (by omega)

theorem blocks_prefix {c c' : Chain} (h : c <+: c') : c.blocks <+: c'.blocks := by
  obtain ⟨t, rfl⟩ := h
  unfold Chain.blocks
  rw [List.filter_append]
  exact List.prefix_append _ _

/-- **Finality is unique per height**: two finalized chains of one height carry the same blocks,
so a stranger holding two finalization certificates for one height holds one block. -/
theorem fin_cert_unique_per_height {P : Protocol} {sent : Sent} (hI : Inv P sent) {v₁ v₂ : Nat}
    {c₁ c₂ : Chain} (h₁ : Finalized P sent v₁ c₁) (h₂ : Finalized P sent v₂ c₂)
    (hh : c₁.height = c₂.height) : c₁.blocks = c₂.blocks := by
  have hpre : c₁.blocks <+: c₂.blocks ∨ c₂.blocks <+: c₁.blocks := by
    rcases finalized_consistent hI h₁ h₂ with h | h
    · exact .inl (blocks_prefix h)
    · exact .inr (blocks_prefix h)
  unfold Chain.height at hh
  rcases hpre with h | h
  · exact h.eq_of_length hh
  · exact (h.eq_of_length hh.symm).symm

/-- The same, for every reachable message list. -/
theorem fin_cert_unique_per_height_reach {P : Protocol} {sent : Sent} (hr : Reach P sent)
    {v₁ v₂ : Nat} {c₁ c₂ : Chain} (h₁ : Finalized P sent v₁ c₁) (h₂ : Finalized P sent v₂ c₂)
    (hh : c₁.height = c₂.height) : c₁.blocks = c₂.blocks :=
  fin_cert_unique_per_height (reach_inv hr) h₁ h₂ hh

/-! ## 8. Accountability: a receipt is two votes by one node -/

/-- Two conflicting targets in one view and the nodes that voted for both. A stranger holding the
message list checks it with `checks`; nothing is taken on the issuer's word. -/
structure SlashingReceipt where
  view : Nat
  a : Target
  b : Target
  signers : List NodeId
  deriving Repr

/-- The receipt checks against a message list: the targets differ and every signer's two votes
are in it. -/
@[expose] def SlashingReceipt.checks (r : SlashingReceipt) (sent : Sent) : Bool :=
  decide (r.a ≠ r.b) && r.signers.all fun n => voted sent n r.view r.a && voted sent n r.view r.b

/-- A node kept the vote-once rule in a view. -/
abbrev VoteOnce (sent : Sent) (n : NodeId) (v : Nat) : Prop :=
  ∀ t t', voted sent n v t = true → voted sent n v t' = true → t = t'

/-- **What a checking receipt establishes**: each signer cast both votes, so none kept the
vote-once rule in that view. -/
theorem SlashingReceipt.checks_sound {r : SlashingReceipt} {sent : Sent} (h : r.checks sent = true) :
    r.a ≠ r.b ∧ ∀ n ∈ r.signers,
      (⟨n, r.view, .vote, r.a⟩ : Msg) ∈ sent ∧ (⟨n, r.view, .vote, r.b⟩ : Msg) ∈ sent ∧
      ¬ VoteOnce sent n r.view := by
  simp only [SlashingReceipt.checks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun n hn => ?_⟩
  obtain ⟨ha, hb⟩ := h.2 n hn
  refine ⟨(voted_iff _ _ _ _).1 ha, (voted_iff _ _ _ _).1 hb, fun once => h.1 (once _ _ ha hb)⟩

/-- The receipt a committee extracts from two conflicting quorums. -/
def extractReceipt (committee : List NodeId) (sent : Sent) (v : Nat) (a b : Target) :
    SlashingReceipt :=
  ⟨v, a, b, committee.filter fun n => voted sent n v a && voted sent n v b⟩

/-- **Accountability**, at any threshold: two conflicting quorums of `q` votes in a committee of
`n` with `n + f + 1 ≤ 2q` name at least `f+1` signers, each with both votes in the message list
(`checks`), none of whom kept the vote-once rule. No fault bound is assumed: this is what a
stranger learns when the bound failed. -/
theorem accountable_of_threshold (committee : List NodeId) (f q : Nat) (sent : Sent) (v : Nat)
    (a b : Target) (hq : committee.length + f + 1 ≤ 2 * q) (hne : a ≠ b)
    (ha : q ≤ (committee.filter fun n => voted sent n v a).length)
    (hb : q ≤ (committee.filter fun n => voted sent n v b).length) :
    let r := extractReceipt committee sent v a b
    r.checks sent = true ∧ f + 1 ≤ r.signers.length ∧
      ∀ n ∈ r.signers, n ∈ committee ∧ ¬ VoteOnce sent n v := by
  intro r
  have hsum := list_filter_add_card (fun n => voted sent n v a) (fun n => voted sent n v b) committee
  have hunion := list_filter_length_le (fun n => voted sent n v a || voted sent n v b) committee
  have hbound : f + 1 ≤ (committee.filter fun n => voted sent n v a && voted sent n v b).length := by
    omega
  have hchecks : r.checks sent = true := by
    simp only [r, extractReceipt, SlashingReceipt.checks, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_filter]
    exact ⟨hne, fun n hn => hn.2⟩
  refine ⟨hchecks, hbound, fun n hn => ?_⟩
  have hmem := List.mem_filter.1 hn
  exact ⟨hmem.1, ((SlashingReceipt.checks_sound hchecks).2 n hn).2.2⟩

/-- **Accountability at `2f+1`**: two conflicting quorums of `2f+1` in a committee of at most
`3f+1` name at least `f+1` signers (the `q = 2f+1` instance of `accountable_of_threshold`). -/
theorem accountable (committee : List NodeId) (f : Nat) (sent : Sent) (v : Nat) (a b : Target)
    (hsize : committee.length ≤ 3 * f + 1) (hne : a ≠ b)
    (ha : 2 * f + 1 ≤ (committee.filter fun n => voted sent n v a).length)
    (hb : 2 * f + 1 ≤ (committee.filter fun n => voted sent n v b).length) :
    let r := extractReceipt committee sent v a b
    r.checks sent = true ∧ f + 1 ≤ r.signers.length ∧
      ∀ n ∈ r.signers, n ∈ committee ∧ ¬ VoteOnce sent n v :=
  accountable_of_threshold committee f (2 * f + 1) sent v a b (by omega) hne ha hb

/-- **Accountability at `n - f`**: two conflicting quorums of `n - f` in a committee of
`n ≥ 3f+1` name at least `f+1` signers (`2(n - f) - n = n - 2f ≥ f+1`). -/
theorem accountable_nf (committee : List NodeId) (f : Nat) (sent : Sent) (v : Nat) (a b : Target)
    (hsize : 3 * f + 1 ≤ committee.length) (hne : a ≠ b)
    (ha : committee.length - f ≤ (committee.filter fun n => voted sent n v a).length)
    (hb : committee.length - f ≤ (committee.filter fun n => voted sent n v b).length) :
    let r := extractReceipt committee sent v a b
    r.checks sent = true ∧ f + 1 ≤ r.signers.length ∧
      ∀ n ∈ r.signers, n ∈ committee ∧ ¬ VoteOnce sent n v :=
  accountable_of_threshold committee f (committee.length - f) sent v a b (by omega) hne ha hb

/-- **Accountability for a `Protocol`**: two conflicting quorums (`P.quorum = n - f`) in one view
name at least `f+1` double-signers. Only the committee size bound is used, not the fault bound. -/
theorem accountable_protocol (P : Protocol) (sent : Sent) (v : Nat) (a b : Target) (hne : a ≠ b)
    (ha : P.quorum ≤ votesFor P sent v a) (hb : P.quorum ≤ votesFor P sent v b) :
    let r := extractReceipt P.committee sent v a b
    r.checks sent = true ∧ P.f + 1 ≤ r.signers.length ∧
      ∀ n ∈ r.signers, n ∈ P.committee ∧ ¬ VoteOnce sent n v :=
  accountable_nf P.committee P.f sent v a b P.size hne ha hb

/-- Under the fault bound and the invariant, every signer of an extracted receipt is faulty: an
honest node votes once. -/
theorem signers_faulty {P : Protocol} {sent : Sent} (hI : Inv P sent) {v : Nat} {a b : Target}
    (hne : a ≠ b) : ∀ n ∈ (extractReceipt P.committee sent v a b).signers, P.faulty n = true := by
  intro n hn
  simp only [extractReceipt, List.mem_filter, Bool.and_eq_true] at hn
  obtain ⟨hmem, ha, hb⟩ := hn
  cases hf : P.faulty n with
  | true => rfl
  | false =>
    exfalso
    have hma := (voted_iff sent n v a).1 ha
    have hmb := (voted_iff sent n v b).1 hb
    exact hne (hI.voteOnce _ hma _ hmb ⟨hmem, hf⟩ rfl rfl rfl rfl)

theorem extractReceipt_nodup (P : Protocol) (sent : Sent) (v : Nat) (a b : Target) :
    (extractReceipt P.committee sent v a b).signers.Nodup :=
  nodup_filter_simplex _ P.nodup

/-! ## 9. Finalization Certificates (`FinCert`) -/

private def eraseFirstNat (a : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if a = y then ys else y :: eraseFirstNat a ys

private theorem eraseFirstNat_length {a : Nat} :
    ∀ {ys : List Nat}, a ∈ ys → (eraseFirstNat a ys).length + 1 = ys.length
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
    simp only [eraseFirstNat]
    by_cases hay : a = y
    · simp [hay]
    · simp only [hay, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.1 h with rfl | hmem
      · exact absurd rfl hay
      · have ih := eraseFirstNat_length hmem
        omega

private theorem mem_eraseFirstNat_of_ne {a x : Nat} (hne : x ≠ a) :
    ∀ {ys : List Nat}, x ∈ ys → x ∈ eraseFirstNat a ys
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
    simp only [eraseFirstNat]
    by_cases hay : a = y
    · simp only [hay, ↓reduceIte]
      rcases List.mem_cons.1 h with rfl | hmem
      · exact absurd hay.symm hne
      · exact hmem
    · simp only [hay, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.1 h with rfl | hmem
      · exact .inl rfl
      · exact .inr (mem_eraseFirstNat_of_ne hne hmem)

theorem nodup_subset_length_le :
    ∀ {xs ys : List Nat}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | a :: xs, ys, hnd, hsub => by
    cases hnd with
    | cons hnot hnd_xs =>
      have ha : a ∈ ys := hsub a (.head xs)
      have hsub' : ∀ x ∈ xs, x ∈ eraseFirstNat a ys := fun x hx =>
        mem_eraseFirstNat_of_ne (fun heq => hnot x hx heq.symm) (hsub x (.tail a hx))
      have ih := nodup_subset_length_le hnd_xs hsub'
      have hlen := eraseFirstNat_length ha
      simp only [List.length_cons]
      omega

/-- Checkable finalization certificate naming a view, a finalized chain, and the distinct
    committee members whose `finalize` votes appear in `sent`. -/
structure FinCert where
  view : Nat
  chain : Chain
  signers : List NodeId
  deriving Repr

deriving instance @[expose] DecidableEq for SlashingReceipt, FinCert

/-- Verify a `FinCert` against committee `P` and message history `sent`:
    `signers` are duplicate-free, meet `P.quorum` (`n - f`), belong to `P.committee`,
    and each cast a `finalize` vote for `chain` in `view`. -/
@[expose] def FinCert.checks (c : FinCert) (P : Protocol) (sent : Sent) : Bool :=
  decide c.signers.Nodup &&
  decide (P.quorum ≤ c.signers.length) &&
  c.signers.all (fun n => P.committee.contains n && finalizeVoted sent n c.view c.chain)

/-- Extract a canonical `FinCert` from `sent` when `Finalized P sent v c` holds. -/
def extractFinCert? (P : Protocol) (sent : Sent) (v : Nat) (c : Chain) : Option FinCert :=
  let signers := P.committee.filter (fun n => finalizeVoted sent n v c)
  if P.quorum ≤ signers.length then
    some { view := v, chain := c, signers := signers }
  else
    none

/-- Every `FinCert` that passes `checks` witnesses `Finalized P sent c.view c.chain`. -/
theorem FinCert.checks_implies_finalized {c : FinCert} {P : Protocol} {sent : Sent}
    (h : c.checks P sent = true) :
    Finalized P sent c.view c.chain := by
  simp only [FinCert.checks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨hnd, hquorum⟩, hall⟩ := h
  have hsub : ∀ n ∈ c.signers, n ∈ P.committee.filter (fun m => finalizeVoted sent m c.view c.chain) := by
    intro n hn
    exact List.mem_filter.2 (hall n hn)
  exact Nat.le_trans hquorum (nodup_subset_length_le hnd hsub)

/-- Extracting a `FinCert` from a finalized chain produces a checking certificate. -/
theorem extractFinCert_checks_of_finalized {P : Protocol} {sent : Sent} {v : Nat} {c : Chain}
    (hf : Finalized P sent v c) :
    ∃ cert : FinCert, extractFinCert? P sent v c = some cert ∧
      cert.view = v ∧ cert.chain = c ∧ cert.checks P sent = true := by
  unfold extractFinCert?
  have hq : P.quorum ≤ (P.committee.filter fun n => finalizeVoted sent n v c).length := hf
  simp only [hq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  simp only [FinCert.checks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem]
  refine ⟨⟨nodup_filter_simplex _ P.nodup, hq⟩, fun n hn => ?_⟩
  exact List.mem_filter.1 hn

/-- Two checking `FinCert`s under `Inv P sent` certify prefix-consistent chains. -/
theorem FinCert.consistent {P : Protocol} {sent : Sent} (hI : Inv P sent)
    {c₁ c₂ : FinCert} (h₁ : c₁.checks P sent = true) (h₂ : c₂.checks P sent = true) :
    c₁.chain <+: c₂.chain ∨ c₂.chain <+: c₁.chain :=
  finalized_consistent hI (FinCert.checks_implies_finalized h₁) (FinCert.checks_implies_finalized h₂)

/-- Two checking `FinCert`s of equal chain height certify the exact same block sequence. -/
theorem FinCert.unique_per_height {P : Protocol} {sent : Sent} (hI : Inv P sent)
    {c₁ c₂ : FinCert} (h₁ : c₁.checks P sent = true) (h₂ : c₂.checks P sent = true)
    (hh : c₁.chain.height = c₂.chain.height) :
    c₁.chain.blocks = c₂.chain.blocks :=
  fin_cert_unique_per_height hI
    (FinCert.checks_implies_finalized h₁)
    (FinCert.checks_implies_finalized h₂)
    hh

/-- Over any reachable message trace `Reach P sent`, checking `FinCert`s of equal height agree. -/
theorem FinCert.unique_per_height_reach {P : Protocol} {sent : Sent} (hr : Reach P sent)
    {c₁ c₂ : FinCert} (h₁ : c₁.checks P sent = true) (h₂ : c₂.checks P sent = true)
    (hh : c₁.chain.height = c₂.chain.height) :
    c₁.chain.blocks = c₂.chain.blocks :=
  FinCert.unique_per_height (reach_inv hr) h₁ h₂ hh

/-! ## 10. The wire form of an entry -/

/-- An entry fits the wire: its view in 8 bytes, and a block's payload in 32 (a 256-bit digest). -/
@[expose] def Entry.canonical : Entry → Bool
  | .block v payload => decide (v < 256 ^ 8) && decide (payload < 256 ^ 32)
  | .dummy v => decide (v < 256 ^ 8)

theorem Entry.canonical_block {v payload : Nat} :
    (Entry.block v payload).canonical = true ↔ v < 256 ^ 8 ∧ payload < 256 ^ 32 := by
  simp [Entry.canonical]

theorem Entry.canonical_dummy {v : Nat} : (Entry.dummy v).canonical = true ↔ v < 256 ^ 8 := by
  simp [Entry.canonical]

/-- The 41 bytes of an entry: a tag, the view big-endian in 8 bytes, the payload big-endian in 32
(zero for a dummy). -/
@[expose] def Entry.encode : Entry → List UInt8
  | .block v payload => (0x01 : UInt8) :: (HashBytes.be 8 v ++ HashBytes.be 32 payload)
  | .dummy v => (0x00 : UInt8) :: (HashBytes.be 8 v ++ HashBytes.be 32 0)

theorem Entry.encode_block (v payload : Nat) :
    (Entry.block v payload).encode = (0x01 : UInt8) :: (HashBytes.be 8 v ++ HashBytes.be 32 payload) := by
  simp only [Entry.encode]

theorem Entry.encode_length (e : Entry) : e.encode.length = 41 := by
  cases e <;> simp [Entry.encode, HashBytes.length_be]

/-- **The wire form loses nothing**: two canonical entries with the same 41 bytes are the same
entry, payload included at its full 256 bits. -/
theorem Entry.encode_injective {e₁ e₂ : Entry} (hc₁ : e₁.canonical = true)
    (hc₂ : e₂.canonical = true) (hEq : e₁.encode = e₂.encode) : e₁ = e₂ := by
  cases e₁ with
  | block v₁ p₁ =>
    cases e₂ with
    | dummy v₂ => simp [Entry.encode] at hEq
    | block v₂ p₂ =>
      have b₁ := Entry.canonical_block.1 hc₁
      have b₂ := Entry.canonical_block.1 hc₂
      simp only [Entry.encode, List.cons.injEq, true_and] at hEq
      obtain ⟨hv, hp⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
      rw [HashBytes.be_injective b₁.1 b₂.1 hv, HashBytes.be_injective b₁.2 b₂.2 hp]
  | dummy v₁ =>
    cases e₂ with
    | block v₂ p₂ => simp [Entry.encode] at hEq
    | dummy v₂ =>
      have b₁ := Entry.canonical_dummy.1 hc₁
      have b₂ := Entry.canonical_dummy.1 hc₂
      simp only [Entry.encode, List.cons.injEq, true_and] at hEq
      obtain ⟨hv, _⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
      rw [HashBytes.be_injective b₁ b₂ hv]

/-- The concatenated wire forms of a list of canonical entries determine the list (each entry is
41 bytes). -/
theorem encodeEntries_injective :
    ∀ {c₁ c₂ : Chain}, c₁.all Entry.canonical = true → c₂.all Entry.canonical = true →
      c₁.flatMap Entry.encode = c₂.flatMap Entry.encode → c₁ = c₂
  | [], [], _, _, _ => rfl
  | [], e :: es, _, _, h => by
    have := congrArg List.length h
    rw [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
      Entry.encode_length] at this
    omega
  | e :: es, [], _, _, h => by
    have := congrArg List.length h
    rw [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
      Entry.encode_length] at this
    omega
  | e₁ :: es₁, e₂ :: es₂, h₁, h₂, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h₁ h₂
    simp only [List.flatMap_cons] at h
    obtain ⟨he, hes⟩ := List.append_inj h (by rw [Entry.encode_length, Entry.encode_length])
    rw [Entry.encode_injective h₁.1 h₂.1 he, encodeEntries_injective h₁.2 h₂.2 hes]

end Obend.Consensus.SimplexProtocol
end
