module
/-
# Obend.Consensus.SimplexLiveness — signed senders, slot keys, and the timed network

`Obend.Consensus.SimplexProtocol` takes a message's sender as its signer and has no clock. This
module supplies both.

1. **The signed wire.** `encodeSignablePreimage` frames `(sender, view, kind, target)` under a
   domain tag, each chain entry by `Entry.encode` (8-byte view, 32-byte payload), so a block
   payload is a full 256-bit digest on the wire and `signableByteArray_injective` reads every
   canonical message back. `verifySignedSent` checks a trace against a committee roster and a
   `KeyDirectory` without reading the ghost `Protocol.faulty`.
2. **The extractor.** `extractForgedVoteSignature` turns an accepted signed trace into either a
   `SimplexProtocol.Reach` run in which only faulty senders break the honest rule, or an
   `EufCmaForgeryWitness`: an accepted signature, under an honest validator's key, on a message
   that validator never signed.
3. **Slot keys for a whole committee.** A `KeyDirectory` holds one key per validator and slot
   `(view, kind)`. `commitSlotSigScheme` is a one-time commitment scheme over a byte hash `H`: an
   honest slot key is `H` of the framed content of that slot (the one message its owner signs
   there, or the empty slot) and a salt; a signature opens it. The key does not occur in what is
   signed and no validator's key depends on another's, so `HonestSlotKeys` holds for any number of
   honest validators (`KeyDirectory.derive_honestSlotKeys`; witnessed below with four validators,
   three honest). A forgery against
   any honest validator is a second opening of its slot key:
   `forgedSignature_reduces_to_hashCollision` returns the two preimages. What the scheme asks of
   its setting: a slot key is published with knowledge of the slot's message (commit, then
   reveal), so the directory is an authenticated registry, not a long-lived key.
4. **The timed network.** `NetState` is a clock, the timestamped message log, per-node
   deliveries and view-entry times. `netStep` runs one `NetEvent`: the adversary delivers any sent
   message to any node in any order, injects any message from a faulty sender at any time, and
   decides when the clock ticks; an honest node sends by the protocol rule judged on its own
   deliveries (`honestSendOk`). The clock may tick only from a `settledB` state: every message
   whose deadline `max sendTime gst + deltaNet` has come is delivered to every honest node, and no
   honest node is sitting on a block vote or a finalize vote its deliveries enable. Every run
   projects to `SimplexProtocol.Reach` (`runNet_reach`).
   `gst_honest_leader_finalizes`: once a view with an honest leader is launched after GST
   (`ViewLaunched`), every event list whatever, once its clock has passed `2 * deltaNet`, has the
   leader's block finalized, with no honest dummy vote.

Not proved here: progress through a view whose leader is faulty. `SimplexProtocol.Step.vote` lets
a node vote once per view, for a block or for the dummy; a faulty leader that shows its proposal
to some honest nodes only can split the honest votes so that neither is notarized. The Simplex of
Chan and Pass lets a node vote for the dummy after a block vote and forbids finalizing after a
dummy vote; that rule change belongs to `SimplexProtocol`'s invariant.
-/

public import Obend.Consensus.Simplex
public import Obend.Consensus.SimplexProtocol
public import Obend.Consensus.SimplexTrace
public import Obend.Judge.Computational
public import Obend.Digest.Cshake256.Seam
public import Obend.Digest.HashBytes

public section
namespace Obend.Consensus.SimplexLiveness

open Obend.Consensus.Simplex (NodeId list_filter_sub)
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace (entryNotarizedB chainNotarizedB voteRuleB voteRuleB_sound)
open Obend.Digest
open Obend.Digest.Cshake256.Native (bytesOfList bytesOfList_toList)


set_option autoImplicit false

/-! ## 1. Domain-framed canonical preimages -/

/-- Domain separator tag for authenticated Simplex protocol messages (21 ASCII bytes). -/
def simplexAuthDomainBytes : List UInt8 :=
  [0x4F, 0x42, 0x45, 0x4E, 0x44, 0x2D, 0x53, 0x49, 0x4D, 0x50, 0x4C,
   0x45, 0x58, 0x2D, 0x41, 0x55, 0x54, 0x48, 0x2D, 0x56, 0x31]

/-- 64-bit scalar bound (`256 ^ 8`) for 8-byte big-endian framing of senders, views and lengths. -/
@[expose] def FieldBound64 : Nat := 256 ^ 8

/-- Canonical width check for a `SimplexProtocol.Target`: every entry fits `Entry.encode`. -/
def targetCanonical : Target → Bool
  | .block c => c.all Entry.canonical
  | .dummy v => decide (v < FieldBound64)

/-- Canonical width check for a `SimplexProtocol.Msg`. -/
def msgCanonical (m : Msg) : Bool :=
  decide (m.sender < FieldBound64) &&
  decide (m.view < FieldBound64) &&
  targetCanonical m.target

/-- Prefix-free recursive byte encoding of a `SimplexProtocol.Chain`, 41 bytes per entry. -/
def encodeChainBytes : Chain → List UInt8
  | []      => [0x00]
  | e :: es => (0x01 : UInt8) :: (e.encode ++ encodeChainBytes es)

theorem encodeChainBytes_append_injective :
    ∀ {c₁ c₂ : Chain} {rest₁ rest₂ : List UInt8},
      c₁.all Entry.canonical = true →
      c₂.all Entry.canonical = true →
      encodeChainBytes c₁ ++ rest₁ = encodeChainBytes c₂ ++ rest₂ →
      c₁ = c₂ ∧ rest₁ = rest₂
  | [], [], rest₁, rest₂, _, _, hEq => by
    simp [encodeChainBytes] at hEq
    exact ⟨rfl, hEq⟩
  | [], _ :: _, _, _, _, _, hEq => by
    simp [encodeChainBytes] at hEq
  | _ :: _, [], _, _, _, _, hEq => by
    simp [encodeChainBytes] at hEq
  | e₁ :: es₁, e₂ :: es₂, rest₁, rest₂, hc₁, hc₂, hEq => by
    simp only [List.all_cons, Bool.and_eq_true] at hc₁ hc₂
    simp only [encodeChainBytes, List.cons_append, List.cons.injEq, true_and,
      List.append_assoc] at hEq
    have hLen : e₁.encode.length = e₂.encode.length := by
      rw [Entry.encode_length, Entry.encode_length]
    obtain ⟨hE, hTail⟩ := List.append_inj hEq hLen
    have heEq := Entry.encode_injective hc₁.1 hc₂.1 hE
    obtain ⟨hesEq, hRestEq⟩ := encodeChainBytes_append_injective hc₁.2 hc₂.2 hTail
    exact ⟨by rw [heEq, hesEq], hRestEq⟩

/-- Prefix-free canonical byte encoding of a `SimplexProtocol.Target`. -/
def encodeTargetBytes : Target → List UInt8
  | .block c => (0x01 : UInt8) :: encodeChainBytes c
  | .dummy v => (0x00 : UInt8) :: HashBytes.be 8 v

theorem encodeTargetBytes_injective {t₁ t₂ : Target}
    (hc₁ : targetCanonical t₁ = true)
    (hc₂ : targetCanonical t₂ = true)
    (hEq : encodeTargetBytes t₁ = encodeTargetBytes t₂) :
    t₁ = t₂ := by
  cases t₁ with
  | block c₁ =>
    cases t₂ with
    | dummy v₂ => simp [encodeTargetBytes] at hEq
    | block c₂ =>
      simp only [targetCanonical] at hc₁ hc₂
      simp only [encodeTargetBytes, List.cons.injEq, true_and] at hEq
      have hApp : encodeChainBytes c₁ ++ [] = encodeChainBytes c₂ ++ [] := by simpa using hEq
      obtain ⟨hcEq, _⟩ := encodeChainBytes_append_injective hc₁ hc₂ hApp
      rw [hcEq]
  | dummy v₁ =>
    cases t₂ with
    | block c₂ => simp [encodeTargetBytes] at hEq
    | dummy v₂ =>
      simp only [targetCanonical, decide_eq_true_eq] at hc₁ hc₂
      simp only [encodeTargetBytes, List.cons.injEq, true_and] at hEq
      rw [HashBytes.be_injective hc₁ hc₂ hEq]

/-- Tag byte for `SimplexProtocol.Kind`. -/
def encodeKindByte : Kind → UInt8
  | .propose  => 0x01
  | .vote     => 0x02
  | .finalize => 0x03

theorem encodeKindByte_injective {k₁ k₂ : Kind}
    (hEq : encodeKindByte k₁ = encodeKindByte k₂) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> first | rfl | cases hEq

/-- Length-framed byte prefix helper (`be 8 bs.length ++ bs`). -/
def frameBytes64 (bs : List UInt8) : List UInt8 :=
  HashBytes.be 8 bs.length ++ bs

theorem frameBytes64_append_injective {a₁ a₂ b₁ b₂ : List UInt8}
    (ha₁ : a₁.length < FieldBound64)
    (ha₂ : a₂.length < FieldBound64)
    (hEq : frameBytes64 a₁ ++ b₁ = frameBytes64 a₂ ++ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  unfold frameBytes64 at hEq
  rw [List.append_assoc, List.append_assoc] at hEq
  obtain ⟨hLenBe, hRest⟩ := List.append_inj hEq (by simp [HashBytes.length_be])
  have hLenEq : a₁.length = a₂.length := HashBytes.be_injective ha₁ ha₂ hLenBe
  exact List.append_inj hRest hLenEq

/-- The signed bytes of a message: `(simplexAuthDomainBytes, sender, view, kind, target)`, the
    domain length-framed and every field at a fixed width or prefix-free. No key occurs in them. -/
def encodeSignablePreimage (m : Msg) : List UInt8 :=
  frameBytes64 simplexAuthDomainBytes ++
    (HashBytes.be 8 m.sender ++
      (HashBytes.be 8 m.view ++
        ([encodeKindByte m.kind] ++ encodeTargetBytes m.target)))

/-- The signed bytes as the `ByteArray` a signature verifier reads. -/
def signableByteArray (m : Msg) : ByteArray :=
  bytesOfList (encodeSignablePreimage m)

private theorem pow_256_32_eq_pow_2_256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide

/-- **The signed bytes determine the message**: sender, view, kind and target (every block payload
    at its full 256 bits) are read back, so a signature does not carry over to another view, kind
    or target. -/
theorem encodeSignablePreimage_injective {m₁ m₂ : Msg}
    (hc₁ : msgCanonical m₁ = true)
    (hc₂ : msgCanonical m₂ = true)
    (hEq : encodeSignablePreimage m₁ = encodeSignablePreimage m₂) :
    m₁ = m₂ := by
  unfold encodeSignablePreimage at hEq
  have hDomLen : simplexAuthDomainBytes.length < FieldBound64 := by decide
  obtain ⟨_, h2⟩ := frameBytes64_append_injective hDomLen hDomLen hEq
  obtain ⟨hSenderBe, h3⟩ := List.append_inj h2 (by simp [HashBytes.length_be])
  obtain ⟨hViewBe, h4⟩ := List.append_inj h3 (by simp [HashBytes.length_be])
  simp only [List.singleton_append, List.cons.injEq] at h4
  obtain ⟨hKindByte, hTargetBytes⟩ := h4
  simp only [msgCanonical, Bool.and_eq_true, decide_eq_true_eq] at hc₁ hc₂
  have hSenderEq : m₁.sender = m₂.sender := HashBytes.be_injective hc₁.1.1 hc₂.1.1 hSenderBe
  have hViewEq : m₁.view = m₂.view := HashBytes.be_injective hc₁.1.2 hc₂.1.2 hViewBe
  have hKindEq : m₁.kind = m₂.kind := encodeKindByte_injective hKindByte
  have hTargetEq : m₁.target = m₂.target := encodeTargetBytes_injective hc₁.2 hc₂.2 hTargetBytes
  cases m₁; cases m₂
  simp only at hSenderEq hViewEq hKindEq hTargetEq
  rw [hSenderEq, hViewEq, hKindEq, hTargetEq]

theorem signableByteArray_injective {m₁ m₂ : Msg}
    (hc₁ : msgCanonical m₁ = true)
    (hc₂ : msgCanonical m₂ = true)
    (hEq : signableByteArray m₁ = signableByteArray m₂) :
    m₁ = m₂ := by
  have hList : (signableByteArray m₁).data.toList = (signableByteArray m₂).data.toList :=
    congrArg (fun b => b.data.toList) hEq
  unfold signableByteArray at hList
  rw [bytesOfList_toList, bytesOfList_toList] at hList
  exact encodeSignablePreimage_injective hc₁ hc₂ hList

/-! ## 2. Signed traces and the forgery extractor -/

/-- The committee's key directory: one 256-bit verification key per validator and slot
    `(view, kind)`. -/
structure KeyDirectory where
  pubKey : NodeId → Nat → Kind → BitVec 256

/-- The key a message is verified under: its sender's key for its `(view, kind)` slot. -/
def KeyDirectory.slotKey (K : KeyDirectory) (m : Msg) : BitVec 256 :=
  K.pubKey m.sender m.view m.kind

/-- A signature verifier: key, signed bytes, signature. -/
structure SignatureScheme where
  verifySig : BitVec 256 → ByteArray → ByteArray → Bool

/-- A message on the authenticated wire, with its 32-byte signature. -/
structure SignedSimplexMsg where
  msg       : Msg
  signature : ByteArray
  deriving DecidableEq

/-- Ordered authenticated message log (oldest message first, matching `SimplexTrace`). -/
abbrev SignedSent := List SignedSimplexMsg

/-- Project an authenticated wire trace `SignedSent` to `SimplexProtocol.Sent` (newest message first). -/
def projectSignedSent (tr : SignedSent) : Sent :=
  (tr.map SignedSimplexMsg.msg).reverse

/-- Verify one signed message against the committee roster and the `KeyDirectory`: a committee
    sender, canonical widths (a block payload below `2 ^ 256`), a 32-byte signature, and the
    signature accepted under the sender's slot key. `Protocol.faulty` is not consulted. -/
def verifySignedMsg (S : SignatureScheme) (K : KeyDirectory)
    (committee : List NodeId) (sm : SignedSimplexMsg) : Bool :=
  committee.contains sm.msg.sender &&
  msgCanonical sm.msg &&
  decide (sm.signature.size = 32) &&
  S.verifySig (K.slotKey sm.msg) (signableByteArray sm.msg) sm.signature

/-- Streaming verifier over `SignedSent`: enforces non-replay (`!seen.contains sm.msg`) and
    32-byte cryptographic signature authentication on every message. -/
def verifySignedSentAux (S : SignatureScheme) (K : KeyDirectory)
    (committee : List NodeId) (seen : Sent) : SignedSent → Bool
  | [] => true
  | sm :: rest =>
    !seen.contains sm.msg &&
    verifySignedMsg S K committee sm &&
    verifySignedSentAux S K committee (sm.msg :: seen) rest

/-- Public network verifier for an authenticated `SignedSent` trace (`0` dependence on `P.faulty`). -/
def verifySignedSent (S : SignatureScheme) (K : KeyDirectory)
    (committee : List NodeId) (tr : SignedSent) : Bool :=
  verifySignedSentAux S K committee [] tr

/-- Pure honest protocol rule check for message `m` against prior history `sent`
    (independent of `P.faulty`). -/
def checkHonestProtocolRule (P : Protocol) (sent : Sent) (m : Msg) : Bool :=
  P.committee.contains m.sender &&
  match m.kind with
  | .propose =>
    match m.target with
    | .block _ => m.sender == P.leader m.view
    | .dummy _ => false
  | .vote =>
    !votedAny sent m.sender m.view && voteRuleB P sent m.view m.target
  | .finalize =>
    match m.target with
    | .block c => voted sent m.sender m.view (.block c) && decide (NotarizedBlock P sent m.view c)
    | .dummy _ => false

theorem checkHonestProtocolRule_step {P : Protocol} {sent : Sent} {m : Msg}
    (hn : P.honest m.sender)
    (hRule : checkHonestProtocolRule P sent m = true) :
    Step P sent (m :: sent) := by
  rcases m with ⟨sender, view, kind, target⟩
  unfold checkHonestProtocolRule at hRule
  simp only [Bool.and_eq_true] at hRule
  obtain ⟨_, hk⟩ := hRule
  cases kind with
  | propose =>
    cases target with
    | dummy _ => cases hk
    | block c =>
      simp only [beq_iff_eq] at hk
      exact Step.propose sent sender view c hn hk
  | vote =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    exact Step.vote sent sender view target hn hk.1 (voteRuleB_sound hk.2)
  | finalize =>
    cases target with
    | dummy _ => cases hk
    | block c =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact Step.finalize sent sender view c hn hk.1 hk.2


/-- A forgery: a signature accepted under an honest validator's slot key on a canonical message
    that validator's signing log does not contain. -/
structure EufCmaForgeryWitness (S : SignatureScheme) (K : KeyDirectory)
    (P : Protocol) (honestOracleLog : List Msg) where
  forgedMsg      : SignedSimplexMsg
  honestTarget   : P.honest forgedMsg.msg.sender
  canonical      : msgCanonical forgedMsg.msg = true
  sigWidth32     : forgedMsg.signature.size = 32
  sigAccepted    : S.verifySig (K.slotKey forgedMsg.msg)
                     (signableByteArray forgedMsg.msg) forgedMsg.signature = true
  unqueriedMsg   : forgedMsg.msg ∉ honestOracleLog

/-- A verified `SignedSent` read as a `SimplexProtocol.Reach` run: every message carries an
    accepted 32-byte signature under its sender's slot key, and a message that breaks the honest
    rule comes from a faulty sender. -/
structure AuthenticatedReachWitness (P : Protocol) (S : SignatureScheme)
    (K : KeyDirectory) (seen : Sent) (tr : SignedSent) : Prop where
  reach : Reach P ((tr.map SignedSimplexMsg.msg).reverse ++ seen)
  allAuthenticated : ∀ sm ∈ tr,
    sm.msg.sender ∈ P.committee ∧
    sm.signature.size = 32 ∧
    S.verifySig (K.slotKey sm.msg) (signableByteArray sm.msg) sm.signature = true
  faultyOnlyInject : ∀ (pre : SignedSent) (sm : SignedSimplexMsg) (suf : SignedSent),
    tr = pre ++ sm :: suf →
    checkHonestProtocolRule P ((pre.map SignedSimplexMsg.msg).reverse ++ seen) sm.msg = false →
    P.faulty sm.msg.sender = true

/-- Honest signing-oracle discipline: an honest node signs only messages that obey
    `checkHonestProtocolRule` at the point they appear in `tr`. -/
def HonestSigningOracle (P : Protocol) (seen : Sent)
    (honestOracleLog : List Msg) (tr : SignedSent) : Prop :=
  ∀ (pre : SignedSent) (sm : SignedSimplexMsg) (suf : SignedSent),
    tr = pre ++ sm :: suf →
    P.honest sm.msg.sender →
    sm.msg ∈ honestOracleLog →
    checkHonestProtocolRule P ((pre.map SignedSimplexMsg.msg).reverse ++ seen) sm.msg = true

private theorem verifySignedMsg_dest {S : SignatureScheme} {K : KeyDirectory}
    {committee : List NodeId} {sm : SignedSimplexMsg}
    (h : verifySignedMsg S K committee sm = true) :
    sm.msg.sender ∈ committee ∧
    msgCanonical sm.msg = true ∧
    sm.signature.size = 32 ∧
    S.verifySig (K.slotKey sm.msg) (signableByteArray sm.msg) sm.signature = true := by
  unfold verifySignedMsg at h
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- One verified message, classified without `Classical.choice`: a step of the protocol (one that
    breaks the honest rule only if its sender is faulty), or a forgery. -/
def classifySignedMsg (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) (seen : Sent) (sm : SignedSimplexMsg) (rest : SignedSent)
    (hVer : verifySignedMsg S K P.committee sm = true)
    (hOracle : HonestSigningOracle P seen honestOracleLog (sm :: rest)) :
    PSum (PLift (Step P seen (sm.msg :: seen) ∧
                 (checkHonestProtocolRule P seen sm.msg = false → P.faulty sm.msg.sender = true)))
         ({ w : EufCmaForgeryWitness S K P honestOracleLog // w.forgedMsg = sm }) :=
  have hMsg := verifySignedMsg_dest hVer
  if hFaulty : P.faulty sm.msg.sender = true then
    .inl ⟨⟨Step.inject seen sm.msg hFaulty, fun _ => hFaulty⟩⟩
  else
    have hHonest : P.honest sm.msg.sender := ⟨hMsg.1, Bool.eq_false_iff.2 hFaulty⟩
    if hRule : checkHonestProtocolRule P seen sm.msg = true then
      .inl ⟨⟨checkHonestProtocolRule_step hHonest hRule, fun hF => by rw [hRule] at hF; cases hF⟩⟩
    else
      .inr
        ⟨{ forgedMsg := sm
           honestTarget := hHonest
           canonical := hMsg.2.1
           sigWidth32 := hMsg.2.2.1
           sigAccepted := hMsg.2.2.2
           unqueriedMsg := fun hIn =>
            hRule (by simpa using hOracle [] sm rest rfl hHonest hIn) }, rfl⟩

/-- The extractor's walk over `SignedSent`, oldest message first (`0 Classical.choice`). -/
def extractForgedVoteSignatureAux
    (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) :
    ∀ (seen : Sent) (tr : SignedSent),
      Reach P seen →
      verifySignedSentAux S K P.committee seen tr = true →
      HonestSigningOracle P seen honestOracleLog tr →
      PSum (AuthenticatedReachWitness P S K seen tr)
           ({ w : EufCmaForgeryWitness S K P honestOracleLog // w.forgedMsg ∈ tr })
  | seen, [], hReach, _, _ =>
    .inl
      { reach := by simpa using hReach
        allAuthenticated := fun _ hMem => False.elim (List.not_mem_nil hMem)
        faultyOnlyInject := fun pre _ _ hEq => by cases pre <;> cases hEq }
  | seen, sm :: rest, hReach, hVer, hOracle =>
    have hVerParts :
        verifySignedMsg S K P.committee sm = true ∧
        verifySignedSentAux S K P.committee (sm.msg :: seen) rest = true := by
      unfold verifySignedSentAux at hVer
      simp only [Bool.and_eq_true] at hVer
      exact ⟨hVer.1.2, hVer.2⟩
    match classifySignedMsg S K P honestOracleLog seen sm rest hVerParts.1 hOracle with
    | .inr forgery => .inr ⟨forgery.val, by rw [forgery.property]; exact List.mem_cons_self⟩
    | .inl ⟨⟨hStep, hInj⟩⟩ =>
      have hOracleRest : HonestSigningOracle P (sm.msg :: seen) honestOracleLog rest := by
        intro pre sm' suf hEqRest hHon' hIn'
        have hEqFull : sm :: rest = (sm :: pre) ++ sm' :: suf := by simp [hEqRest]
        have hRes := hOracle (sm :: pre) sm' suf hEqFull hHon' hIn'
        simpa [List.reverse_cons, List.append_assoc] using hRes
      match extractForgedVoteSignatureAux S K P honestOracleLog
              (sm.msg :: seen) rest (Reach.step hReach hStep) hVerParts.2 hOracleRest with
      | .inr forgery => .inr ⟨forgery.val, List.mem_cons_of_mem sm forgery.property⟩
      | .inl wRest =>
        have hMsg := verifySignedMsg_dest hVerParts.1
        .inl
          { reach := by simpa [List.reverse_cons, List.append_assoc] using wRest.reach
            allAuthenticated := by
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hxRest
              · exact ⟨hMsg.1, hMsg.2.2.1, hMsg.2.2.2⟩
              · exact wRest.allAuthenticated x hxRest
            faultyOnlyInject := by
              intro pre x suf hSplit hRuleFalse
              cases pre with
              | nil =>
                simp only [List.nil_append, List.cons.injEq] at hSplit
                rcases hSplit with ⟨rfl, _⟩
                exact hInj (by simpa using hRuleFalse)
              | cons p ps =>
                simp only [List.cons_append, List.cons.injEq] at hSplit
                rcases hSplit with ⟨rfl, hRestSplit⟩
                exact wRest.faultyOnlyInject ps x suf hRestSplit
                  (by simpa [List.reverse_cons, List.append_assoc] using hRuleFalse) }

/-- **The forgery extractor.** A trace accepted by `verifySignedSent` is, constructively, either a
    `SimplexProtocol.Reach` run in which only faulty senders break the honest rule, or a forgery
    against an honest validator's slot key. -/
def extractForgedVoteSignature
    (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) (tr : SignedSent)
    (hVer : verifySignedSent S K P.committee tr = true)
    (hOracle : HonestSigningOracle P [] honestOracleLog tr) :
    PSum (PLift (Reach P (projectSignedSent tr) ∧
                 Inv P (projectSignedSent tr) ∧
                 AuthenticatedReachWitness P S K [] tr))
         (EufCmaForgeryWitness S K P honestOracleLog) :=
  match extractForgedVoteSignatureAux S K P honestOracleLog [] tr Reach.nil hVer hOracle with
  | .inr forgery => .inr forgery.val
  | .inl w =>
    have hReachProj : Reach P (projectSignedSent tr) := by
      simpa [projectSignedSent] using w.reach
    .inl ⟨⟨hReachProj, reach_inv hReachProj, w⟩⟩

/-- No forgery exists against the honest signing log. -/
def SignatureUnforgeable (S : SignatureScheme) (K : KeyDirectory)
    (P : Protocol) (honestOracleLog : List Msg) : Prop :=
  ¬ Nonempty (EufCmaForgeryWitness S K P honestOracleLog)

/-- Under `SignatureUnforgeable`, every trace accepted by `verifySignedSent` projects to a
    `SimplexProtocol.Reach` run satisfying `Inv`, in which only faulty senders inject. -/
theorem verifySignedSent_projects_to_reach
    (S : SignatureScheme) (K : KeyDirectory) (P : Protocol)
    (honestOracleLog : List Msg) (tr : SignedSent)
    (hVer : verifySignedSent S K P.committee tr = true)
    (hOracle : HonestSigningOracle P [] honestOracleLog tr)
    (hUnforge : SignatureUnforgeable S K P honestOracleLog) :
    Reach P (projectSignedSent tr) ∧
    Inv P (projectSignedSent tr) ∧
    AuthenticatedReachWitness P S K [] tr := by
  cases extractForgedVoteSignature S K P honestOracleLog tr hVer hOracle with
  | inl w => exact w.down
  | inr forgery => exact False.elim (hUnforge ⟨forgery⟩)

/-! ## 3. Slot keys: a one-time commitment scheme for the whole committee -/

private theorem ofBE_lt_two_pow_256_of_length_32 {bs : List UInt8} (h : bs.length = 32) :
    HashBytes.ofBE bs < 2 ^ 256 := by
  have hlt := HashBytes.ofBE_lt bs
  rw [h, pow_256_32_eq_pow_2_256] at hlt
  exact hlt

/-- What a slot key commits to: the one message its owner signs in the slot, or the empty slot.
    The tag byte keeps the two apart. -/
def slotContent : Option Msg → List UInt8
  | some m => (0x01 : UInt8) :: encodeSignablePreimage m
  | none => [0x00]

/-- The hashed preimage of a slot key: the length-framed slot content, then the salt. -/
def slotSigPreimage (content : List UInt8) (salt32 : ByteArray) : List UInt8 :=
  frameBytes64 content ++ salt32.data.toList

/-- The message an honest validator signs in slot `(n, v, k)`: the first one in its signing log. -/
def honestSlotMsg (log : List Msg) (n : NodeId) (v : Nat) (k : Kind) : Option Msg :=
  log.find? (fun q => q.sender == n && q.view == v && q.kind == k)

/-- A slot key: the 256-bit hash of the slot's framed content and a salt. -/
def deriveSlotPubKey (H : HashBytes.Hash) (content : Option Msg) (salt32 : ByteArray) : BitVec 256 :=
  BitVec.ofNat 256 (HashBytes.ofBE (H (slotSigPreimage (slotContent content) salt32)))

/-- The slot commitment scheme: a signature on `msgBytes` is a 32-byte salt that opens the slot
    key to `msgBytes` as the slot's (non-empty) content. -/
def commitSlotSigScheme (H : HashBytes.Hash) (maxPreimageBytes : Nat) : SignatureScheme where
  verifySig pk msgBytes sigSalt32 :=
    decide (msgBytes.data.toList.length + 1 < FieldBound64) &&
    decide ((slotSigPreimage ((0x01 : UInt8) :: msgBytes.data.toList) sigSalt32).length
      ≤ maxPreimageBytes) &&
    decide (sigSalt32.size = 32) &&
    decide ((H (slotSigPreimage ((0x01 : UInt8) :: msgBytes.data.toList) sigSalt32)).length = 32) &&
    decide (BitVec.ofNat 256
      (HashBytes.ofBE (H (slotSigPreimage ((0x01 : UInt8) :: msgBytes.data.toList) sigSalt32))) = pk)

/-- The honest validators' slot keys are commitments: every message in the signing log is
    canonical, and for every honest validator and every slot, used or not, the directory's key is
    the slot key of that slot's content under the validator's salt, on a preimage `H` hashes to 32
    bytes within `maxBytes`. Each validator's keys depend on its own slots only. -/
def HonestSlotKeys (H : HashBytes.Hash) (maxBytes : Nat) (K : KeyDirectory) (P : Protocol)
    (log : List Msg) (salt : NodeId → Nat → Kind → ByteArray) : Prop :=
  (∀ q ∈ log, msgCanonical q = true) ∧
  ∀ n, P.honest n → ∀ (v : Nat) (k : Kind),
    K.pubKey n v k = deriveSlotPubKey H (honestSlotMsg log n v k) (salt n v k) ∧
    (slotContent (honestSlotMsg log n v k)).length < FieldBound64 ∧
    (slotSigPreimage (slotContent (honestSlotMsg log n v k)) (salt n v k)).length ≤ maxBytes ∧
    (H (slotSigPreimage (slotContent (honestSlotMsg log n v k)) (salt n v k))).length = 32

/-- Key generation for a whole committee: every slot key derived from the signing log and the
    validators' salts. -/
def KeyDirectory.derive (H : HashBytes.Hash) (log : List Msg)
    (salt : NodeId → Nat → Kind → ByteArray) : KeyDirectory where
  pubKey n v k := deriveSlotPubKey H (honestSlotMsg log n v k) (salt n v k)

theorem slotSigPreimage_length (content : List UInt8) (salt32 : ByteArray) :
    (slotSigPreimage content salt32).length = 8 + content.length + salt32.data.toList.length := by
  simp [slotSigPreimage, frameBytes64, HashBytes.length_be]
  omega

/-- **Derived directories satisfy `HonestSlotKeys`**, for every committee and every set of honest
    validators: given a 32-byte hash, a canonical signing log whose slot contents are at most `L`
    bytes, and 32-byte salts. -/
theorem KeyDirectory.derive_honestSlotKeys (H : HashBytes.Hash) (maxBytes L : Nat) (P : Protocol)
    (log : List Msg) (salt : NodeId → Nat → Kind → ByteArray)
    (hH : ∀ bs, (H bs).length = 32)
    (hCanon : ∀ q ∈ log, msgCanonical q = true)
    (hSalt : ∀ n v k, (salt n v k).data.toList.length = 32)
    (hLen : ∀ q ∈ log, (slotContent (some q)).length ≤ L)
    (hL : 1 ≤ L ∧ L < FieldBound64 ∧ 8 + L + 32 ≤ maxBytes) :
    HonestSlotKeys H maxBytes (KeyDirectory.derive H log salt) P log salt := by
  refine ⟨hCanon, fun n _ v k => ⟨rfl, ?_⟩⟩
  have hc : (slotContent (honestSlotMsg log n v k)).length ≤ L := by
    cases hq : honestSlotMsg log n v k with
    | none => exact hL.1
    | some q => exact hLen q (List.mem_of_find?_eq_some hq)
  refine ⟨Nat.lt_of_le_of_lt hc hL.2.1, ?_, hH _⟩
  rw [slotSigPreimage_length, hSalt]
  omega

/-- The two concrete slot preimages involved in a purported signature. -/
def forgedSlotPreimage (sm : SignedSimplexMsg) : List UInt8 :=
  slotSigPreimage ((0x01 : UInt8) :: (signableByteArray sm.msg).data.toList) sm.signature
def registeredSlotPreimage (log : List Msg) (salt : NodeId → Nat → Kind → ByteArray)
    (m : Msg) : List UInt8 :=
  slotSigPreimage (slotContent (honestSlotMsg log m.sender m.view m.kind))
    (salt m.sender m.view m.kind)

/-- **A forgery against any honest validator is a hash collision.** The forged signature opens
    the validator's slot key to a message outside its signing log; the key was made from the
    slot's own content (another message, or the empty slot). The two preimages differ and hash
    alike: a scoped `CollisionPair`, computed without `Classical.choice`. -/
def forgedSignature_reduces_to_hashCollision
    (H : HashBytes.Hash) (maxBytes : Nat) (K : KeyDirectory) (P : Protocol) (log : List Msg)
    (salt : NodeId → Nat → Kind → ByteArray)
    (hKeys : HonestSlotKeys H maxBytes K P log salt)
    (w : EufCmaForgeryWitness (commitSlotSigScheme H maxBytes) K P log) :
    HashBytes.CollisionPair H (fun x => x = forgedSlotPreimage w.forgedMsg ∨
      x = registeredSlotPreimage log salt w.forgedMsg.msg) :=
  let m := w.forgedMsg.msg
  let forgedPre :=
    slotSigPreimage ((0x01 : UInt8) :: (signableByteArray m).data.toList) w.forgedMsg.signature
  let honestPre :=
    slotSigPreimage (slotContent (honestSlotMsg log m.sender m.view m.kind))
      (salt m.sender m.view m.kind)
  have hSlot := hKeys.2 m.sender w.honestTarget m.view m.kind
  have hAcc :
      (signableByteArray m).data.toList.length + 1 < FieldBound64 ∧
      forgedPre.length ≤ maxBytes ∧
      (H forgedPre).length = 32 ∧
      BitVec.ofNat 256 (HashBytes.ofBE (H forgedPre)) = K.pubKey m.sender m.view m.kind := by
    have hSig := w.sigAccepted
    unfold commitSlotSigScheme at hSig
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hSig
    exact ⟨hSig.1.1.1.1, hSig.1.1.1.2, hSig.1.2, hSig.2⟩
  have hSame : HashBytes.ofBE (H forgedPre) = HashBytes.ofBE (H honestPre) := by
    have hToNat := congrArg BitVec.toNat (hAcc.2.2.2.trans hSlot.1)
    unfold deriveSlotPubKey at hToNat
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (ofBE_lt_two_pow_256_of_length_32 hAcc.2.2.1),
        Nat.mod_eq_of_lt (ofBE_lt_two_pow_256_of_length_32 hSlot.2.2.2)] at hToNat
    exact hToNat
  have hDistinct : forgedPre ≠ honestPre := by
    intro hPreEq
    obtain ⟨hContent, _⟩ := frameBytes64_append_injective
      (a₁ := (0x01 : UInt8) :: (signableByteArray m).data.toList)
      (a₂ := slotContent (honestSlotMsg log m.sender m.view m.kind)) hAcc.1 hSlot.2.1 hPreEq
    cases hq : honestSlotMsg log m.sender m.view m.kind with
    | none =>
      rw [hq] at hContent
      simp only [slotContent] at hContent
      injection hContent with hTag _
      exact absurd hTag (by decide)
    | some q =>
      rw [hq] at hContent
      simp only [slotContent] at hContent
      injection hContent with _ hBytes
      have hBytes' : encodeSignablePreimage m = encodeSignablePreimage q := by
        rw [← hBytes]
        unfold signableByteArray
        rw [bytesOfList_toList]
      have hmq := encodeSignablePreimage_injective w.canonical
        (hKeys.1 q (List.mem_of_find?_eq_some hq)) hBytes'
      exact w.unqueriedMsg (hmq ▸ List.mem_of_find?_eq_some hq)
  ({ msgA := forgedPre
     msgB := honestPre
     memA := .inl rfl
     memB := .inr rfl
     distinct := hDistinct
     sameDigest := hSame } : HashBytes.CollisionPair H _)

/-- Statement object for `signedSimplexCompJudge`: the committee, its key directory, the honest
    validators' signing log and salts, and the signed trace under judgment. -/
structure SignedSlotTraceObj where
  proto     : Protocol
  keys      : KeyDirectory
  honestLog : List Msg
  salt      : NodeId → Nat → Kind → ByteArray
  trace     : SignedSent

/-- Finite scope: only the received openings and their registered slot preimages. -/
def slotTracePreimages (o : SignedSlotTraceObj) : List (List UInt8) :=
  o.trace.flatMap fun sm => [forgedSlotPreimage sm, registeredSlotPreimage o.honestLog o.salt sm.msg]

/-- Constructive signed-trace judgment. The generic ComputationalJudge assumption language
has no finite-transcript hash constructor; return the actual collision instead of assuming
impossible injectivity over every byte string of length at most `maxBytes`. -/
def signedSimplexCompJudge (H : HashBytes.Hash) (maxBytes : Nat) (o : SignedSlotTraceObj)
    (hVer : verifySignedSent (commitSlotSigScheme H maxBytes) o.keys o.proto.committee o.trace = true)
    (hOracle : HonestSigningOracle o.proto [] o.honestLog o.trace)
    (hKeys : HonestSlotKeys H maxBytes o.keys o.proto o.honestLog o.salt) :
    PSum (AuthenticatedReachWitness o.proto (commitSlotSigScheme H maxBytes) o.keys [] o.trace)
      (HashBytes.CollisionPair H (fun x => x ∈ slotTracePreimages o)) :=
  match extractForgedVoteSignatureAux (commitSlotSigScheme H maxBytes) o.keys o.proto
      o.honestLog [] o.trace Reach.nil hVer hOracle with
  | .inl w => .inl w
  | .inr ⟨w, hw⟩ =>
    let c := forgedSignature_reduces_to_hashCollision H maxBytes o.keys o.proto
      o.honestLog o.salt hKeys w
    have inScope : ∀ x, (x = forgedSlotPreimage w.forgedMsg ∨
        x = registeredSlotPreimage o.honestLog o.salt w.forgedMsg.msg) → x ∈ slotTracePreimages o := by
      intro x hx
      exact List.mem_flatMap.2 ⟨w.forgedMsg, hw, by simpa using hx⟩
    .inr ⟨c.msgA, c.msgB, inScope _ c.memA, inScope _ c.memB, c.distinct, c.sameDigest⟩

/-! ## 4. Honest quorum cardinality -/

/-- The duplicate-free list of honest validators in `P.committee`. -/
def honestMembers (P : Protocol) : List NodeId :=
  P.committee.filter (fun n => !P.faulty n)

theorem mem_honestMembers_iff (P : Protocol) (n : NodeId) :
    n ∈ honestMembers P ↔ P.honest n := by
  unfold honestMembers Protocol.honest
  rw [List.mem_filter]
  simp

/-- **Honest Quorum Sufficiency**: at least `n - f = P.quorum` committee members are honest. -/
theorem honestMembers_length_ge_quorum (P : Protocol) :
    P.quorum ≤ (honestMembers P).length := by
  have hSub := list_filter_sub (fun _ => true) P.faulty P.committee
  have hTrue : P.committee.filter (fun _ => true) = P.committee := by
    induction P.committee with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  have hHonEq : P.committee.filter (fun x => true && !P.faulty x) = honestMembers P := by
    simp [honestMembers]
  have hFaultEq : P.committee.filter (fun x => true && P.faulty x) = P.committee.filter P.faulty := by
    simp
  rw [hTrue, hHonEq, hFaultEq] at hSub
  have hFb := P.faultBound
  unfold Protocol.quorum
  omega

private theorem filter_length_mono_mem (p q : NodeId → Bool) :
    ∀ (xs : List NodeId),
      (∀ n ∈ xs, p n = true → q n = true) →
      (xs.filter p).length ≤ (xs.filter q).length
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    have ih := filter_length_mono_mem p q xs (fun n hn hp => h n (List.mem_cons_of_mem x hn) hp)
    simp only [List.filter_cons]
    cases hpx : p x with
    | false =>
      cases q x <;> simp <;> omega
    | true =>
      have hqx := h x List.mem_cons_self hpx
      simp [hqx]
      omega

/-- A property every honest committee member has is held by a quorum. -/
theorem quorum_of_all_honest (P : Protocol) (q : NodeId → Bool)
    (h : ∀ n, P.honest n → q n = true) : P.quorum ≤ (P.committee.filter q).length := by
  refine Nat.le_trans (honestMembers_length_ge_quorum P) ?_
  unfold honestMembers
  refine filter_length_mono_mem (fun n => !P.faulty n) q P.committee ?_
  intro n hmem hnf
  exact h n ⟨hmem, by cases hf : P.faulty n <;> simp_all⟩

theorem chainNotarizedB_of_chainNotarized {P : Protocol} {sent : Sent} {c : Chain}
    (h : ChainNotarized P sent c) :
    chainNotarizedB P sent c = true := by
  unfold chainNotarizedB
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [List.getElem?_eq_getElem hk]
  have he := h k hk
  cases hc : c[k] with
  | dummy v =>
    rw [hc] at he
    simp [entryNotarizedB, he.1, he.2]
  | block v x =>
    rw [hc] at he
    simp [entryNotarizedB, he.1, he.2]

theorem voteRuleB_of_proposal {P : Protocol} {sent : Sent} {v : Nat} {p : Chain} {x : Nat}
    (hv : 1 ≤ v) (hlen : p.length = v - 1) (hp : ChainNotarized P sent p)
    (hprop : (⟨P.leader v, v, .propose, .block (p ++ [.block v x])⟩ : Msg) ∈ sent) :
    voteRuleB P sent v (.block (p ++ [.block v x])) = true := by
  dsimp only [voteRuleB]
  have hlast : (p ++ [Entry.block v x]).getLast? = some (Entry.block v x) :=
    List.getLast?_concat
  have hdrop : (p ++ [Entry.block v x]).dropLast = p :=
    List.dropLast_concat
  rw [hlast, hdrop]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem]
  exact ⟨hv, ⟨⟨⟨trivial, hlen⟩, chainNotarizedB_of_chainNotarized hp⟩, hprop⟩⟩

/-! ## 5. The adversarial Δ-delivery timed network -/

/-- Partial-synchrony parameters: the global stabilisation time, the delivery bound that holds
    after it, and the view timer. -/
structure NetConfig where
  gst      : Nat
  deltaNet : Nat
  timeout  : Nat

/-- The network: the clock, every message ever sent with its send time (newest first), which
    node has been delivered which message, and when each node entered each view. -/
structure NetState where
  time      : Nat
  log       : List (Msg × Nat)
  delivered : NodeId → Msg → Bool
  viewEntry : NodeId → Nat → Option Nat

/-- Every message ever sent: the `SimplexProtocol.Sent` this network projects to. -/
def NetState.sent (s : NetState) : Sent := s.log.map Prod.fst

/-- What node `n` has been delivered: all it may act on. -/
def NetState.localView (s : NetState) (n : NodeId) : Sent := s.sent.filter (s.delivered n)

/-- Send `m` now. -/
def NetState.push (s : NetState) (m : Msg) : NetState := { s with log := (m, s.time) :: s.log }

theorem NetState.mem_localView {s : NetState} {n : NodeId} {m : Msg} :
    m ∈ s.localView n ↔ m ∈ s.sent ∧ s.delivered n m = true := by
  unfold NetState.localView
  exact List.mem_filter

theorem NetState.mem_sent_of_mem_log {s : NetState} {m : Msg} {t : Nat} (h : (m, t) ∈ s.log) :
    m ∈ s.sent := by
  unfold NetState.sent
  exact List.mem_map.2 ⟨(m, t), h, rfl⟩

/-- What can happen. The adversary chooses the whole event list: which sent message reaches which
    node and when (`deliver`), any message from a faulty sender (`inject`), and when the clock
    advances (`tick`); `enter` and `send` are honest nodes acting by their rules. -/
inductive NetEvent where
  | deliver (n : NodeId) (m : Msg)
  | inject (m : Msg)
  | enter (n : NodeId) (v : Nat) (p : Chain)
  | send (m : Msg)
  | tick

/-- An honest node's rule for sending `m`, judged on its own deliveries and the clock: the view's
    leader proposes once after entering; a node that entered the view and has not voted in it
    votes for a block by `voteRuleB` on its deliveries, or for the dummy once its timer
    (`viewEntry + timeout`) has expired; a node finalizes a block it voted for once its deliveries
    notarize it. -/
def honestSendOk (P : Protocol) (cfg : NetConfig) (s : NetState) (m : Msg) : Bool :=
  !P.faulty m.sender && P.committee.contains m.sender &&
  match m.kind, m.target with
  | .propose, .block _ =>
    m.sender == P.leader m.view && (s.viewEntry m.sender m.view).isSome &&
    !s.sent.any (fun q => q.sender == m.sender && q.view == m.view && q.kind == .propose)
  | .vote, .block c =>
    (s.viewEntry m.sender m.view).isSome && !votedAny s.sent m.sender m.view &&
    voteRuleB P (s.localView m.sender) m.view (.block c)
  | .vote, .dummy w =>
    w == m.view && decide (1 ≤ m.view) && !votedAny s.sent m.sender m.view &&
    (match s.viewEntry m.sender m.view with
     | some t₀ => decide (t₀ + cfg.timeout ≤ s.time)
     | none => false)
  | .finalize, .block c =>
    voted s.sent m.sender m.view (.block c) &&
    decide (NotarizedBlock P (s.localView m.sender) m.view c)
  | _, _ => false

/-- Node `n` holds a proposal `q` it could vote for and has not voted in that view. -/
def pendingVote (P : Protocol) (s : NetState) (n : NodeId) (q : Msg) : Bool :=
  q.kind == .propose && (s.viewEntry n q.view).isSome && !votedAny s.sent n q.view &&
  voteRuleB P (s.localView n) q.view q.target

/-- `q` is a block vote of node `n` whose block `n`'s deliveries notarize and `n` has not
    finalized. -/
def pendingFinalize (P : Protocol) (s : NetState) (n : NodeId) (q : Msg) : Bool :=
  q.sender == n && q.kind == .vote &&
  match q.target with
  | .block c => decide (NotarizedBlock P (s.localView n) q.view c) && !finalizeVoted s.sent n q.view c
  | .dummy _ => false

/-- The clock may advance only from a settled state: every message whose delivery deadline
    (`deltaNet` after the later of its send time and `gst`) has come is delivered to every honest
    node, and no honest node has a pending block vote or finalize vote. Before `gst` nothing is
    due; the adversary delays as it likes. -/
def settledB (P : Protocol) (cfg : NetConfig) (s : NetState) : Bool :=
  s.log.all (fun e =>
    decide (s.time < e.2 + cfg.deltaNet) || decide (s.time < cfg.gst + cfg.deltaNet) ||
      P.committee.all (fun n => P.faulty n || s.delivered n e.1)) &&
  P.committee.all (fun n => P.faulty n ||
    ((s.localView n).all (fun q => !pendingVote P s n q) &&
     s.sent.all (fun q => !pendingFinalize P s n q)))

/-- One event. A refused event (`none`) is one the model does not allow: delivering a message
    never sent, an injection by an honest sender, an honest send against the rule, a tick from an
    unsettled state. -/
def netStep (P : Protocol) (cfg : NetConfig) (s : NetState) : NetEvent → Option NetState
  | .deliver n m =>
    if s.sent.contains m then
      some { s with delivered := fun n' m' => (n' == n && m' == m) || s.delivered n' m' }
    else none
  | .inject m => if P.faulty m.sender then some (s.push m) else none
  | .enter n v p =>
    if !P.faulty n && P.committee.contains n && decide (1 ≤ v) && decide (p.length = v - 1) &&
        chainNotarizedB P (s.localView n) p && (s.viewEntry n v).isNone then
      some { s with
        viewEntry := fun n' v' => if n' = n ∧ v' = v then some s.time else s.viewEntry n' v' }
    else none
  | .send m => if honestSendOk P cfg s m then some (s.push m) else none
  | .tick => if settledB P cfg s then some { s with time := s.time + 1 } else none

/-- A timed trace: any event list, run from `s`. -/
def runNet (P : Protocol) (cfg : NetConfig) : NetState → List NetEvent → Option NetState
  | s, [] => some s
  | s, e :: es =>
    match netStep P cfg s e with
    | some s' => runNet P cfg s' es
    | none => none

theorem runNet_cons {P : Protocol} {cfg : NetConfig} {s s' : NetState} {e : NetEvent}
    {es : List NetEvent} :
    runNet P cfg s (e :: es) = some s' ↔
      ∃ s₁, netStep P cfg s e = some s₁ ∧ runNet P cfg s₁ es = some s' := by
  simp only [runNet]
  cases netStep P cfg s e <;> simp

theorem runNet_append {P : Protocol} {cfg : NetConfig} :
    ∀ (a b : List NetEvent) {s s' : NetState},
      runNet P cfg s (a ++ b) = some s' ↔
        ∃ s₁, runNet P cfg s a = some s₁ ∧ runNet P cfg s₁ b = some s'
  | [], b, s, s' =>
    ⟨fun h => ⟨s, rfl, h⟩, fun ⟨s₁, h1, h2⟩ => by
      have h1' : some s = some s₁ := h1
      injection h1' with e
      subst e
      exact h2⟩
  | e :: a, b, s, s' => by
    rw [List.cons_append, runNet_cons]
    constructor
    · rintro ⟨s₀, h0, h⟩
      obtain ⟨s₁, h1, h2⟩ := (runNet_append a b).1 h
      exact ⟨s₁, runNet_cons.2 ⟨s₀, h0, h1⟩, h2⟩
    · rintro ⟨s₁, h1, h2⟩
      obtain ⟨s₀, h0, h1'⟩ := runNet_cons.1 h1
      exact ⟨s₀, h0, (runNet_append a b).2 ⟨s₁, h1', h2⟩⟩

theorem settled_delivered {P : Protocol} {cfg : NetConfig} {s : NetState}
    (h : settledB P cfg s = true) {m : Msg} {t : Nat} (hm : (m, t) ∈ s.log)
    (hdue : t + cfg.deltaNet ≤ s.time) (hgst : cfg.gst + cfg.deltaNet ≤ s.time)
    {n : NodeId} (hn : P.honest n) : s.delivered n m = true := by
  unfold settledB at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h.1 (m, t) hm with (hlt | hlt) | hall
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · rcases hall n hn.1 with hf | hd
    · rw [hn.2] at hf; cases hf
    · exact hd

theorem settled_vote {P : Protocol} {cfg : NetConfig} {s : NetState}
    (h : settledB P cfg s = true) {n : NodeId} (hn : P.honest n) {q : Msg}
    (hq : q ∈ s.localView n) (hk : q.kind = .propose)
    (he : (s.viewEntry n q.view).isSome = true)
    (hr : voteRuleB P (s.localView n) q.view q.target = true) :
    votedAny s.sent n q.view = true := by
  unfold settledB at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  rcases h.2 n hn.1 with hf | hp
  · rw [hn.2] at hf; cases hf
  · have hpv := hp.1 q hq
    cases hva : votedAny s.sent n q.view with
    | true => rfl
    | false => simp [pendingVote, hk, he, hva, hr] at hpv

theorem settled_fin {P : Protocol} {cfg : NetConfig} {s : NetState}
    (h : settledB P cfg s = true) {n : NodeId} (hn : P.honest n) {v : Nat} {c : Chain}
    (hv : (⟨n, v, .vote, .block c⟩ : Msg) ∈ s.sent)
    (hnot : NotarizedBlock P (s.localView n) v c) : finalizeVoted s.sent n v c = true := by
  unfold settledB at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  rcases h.2 n hn.1 with hf | hp
  · rw [hn.2] at hf; cases hf
  · have hpf := hp.2 _ hv
    cases hfv : finalizeVoted s.sent n v c with
    | true => rfl
    | false => simp [pendingFinalize, hnot, hfv] at hpf

/-- An honest send is a step of `SimplexProtocol`: what a node concludes from its own deliveries
    holds of the whole message list. -/
theorem honestSendOk_step {P : Protocol} {cfg : NetConfig} {s : NetState} {m : Msg}
    (h : honestSendOk P cfg s m = true) : Step P s.sent (m :: s.sent) := by
  have hsub : ∀ n q, q ∈ s.localView n → q ∈ s.sent := fun n q hq =>
    (NetState.mem_localView.1 hq).1
  rcases m with ⟨sender, view, kind, target⟩
  unfold honestSendOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
  obtain ⟨⟨hf, hmem⟩, hk⟩ := h
  have hon : P.honest sender := ⟨hmem, hf⟩
  cases kind with
  | propose =>
    cases target with
    | block c =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      exact Step.propose s.sent sender view c hon hk.1.1
    | dummy w => simp at hk
  | vote =>
    cases target with
    | block c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
      exact Step.vote s.sent sender view (.block c) hon hk.1.2
        (voteRule_mono (hsub sender) (voteRuleB_sound hk.2))
    | dummy w =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hk
      exact Step.vote s.sent sender view (.dummy w) hon hk.1.2 ⟨hk.1.1.2, hk.1.1.1⟩
  | finalize =>
    cases target with
    | block c =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact Step.finalize s.sent sender view c hon hk.1 (notarizedBlock_mono (hsub sender) hk.2)
    | dummy w => simp at hk

/-- An honest proposer has not proposed in that view before. -/
theorem honestSendOk_propose_fresh {P : Protocol} {cfg : NetConfig} {s : NetState} {m : Msg}
    (h : honestSendOk P cfg s m = true) (hk : m.kind = .propose) :
    ∀ q ∈ s.sent, q.sender = m.sender → q.view = m.view → q.kind = .propose → False := by
  rcases m with ⟨sender, view, kind, target⟩
  simp only at hk
  subst hk
  unfold honestSendOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨_, hk⟩ := h
  cases target with
  | block c =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    intro q hq h1 h2 h3
    have hany : (s.sent.any fun q => q.sender == sender && q.view == view && q.kind == .propose)
        = true := List.any_eq_true.2 ⟨q, hq, by simp [h1, h2, h3]⟩
    rw [hk.2] at hany
    cases hany
  | dummy w => simp at hk

/-- An honest vote: its sender had not voted in the view, and either it is for a block the view's
    leader proposed, or the sender's view timer has expired. -/
theorem honestSendOk_vote {P : Protocol} {cfg : NetConfig} {s : NetState} {m : Msg}
    (h : honestSendOk P cfg s m = true) (hk : m.kind = .vote) :
    votedAny s.sent m.sender m.view = false ∧
    ((∃ c, m.target = .block c ∧ (⟨P.leader m.view, m.view, .propose, .block c⟩ : Msg) ∈ s.sent) ∨
     (∃ t₀, s.viewEntry m.sender m.view = some t₀ ∧ t₀ + cfg.timeout ≤ s.time)) := by
  rcases m with ⟨sender, view, kind, target⟩
  simp only at hk
  subst hk
  unfold honestSendOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨_, hk⟩ := h
  cases target with
  | block c =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    obtain ⟨_, p', x', _, _, _, hprop⟩ := voteRuleB_sound hk.2
    exact ⟨hk.1.2, .inl ⟨c, rfl, (NetState.mem_localView.1 hprop).1⟩⟩
  | dummy w =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    refine ⟨hk.1.2, .inr ?_⟩
    have hexp := hk.2
    cases hve : s.viewEntry sender view with
    | none => rw [hve] at hexp; cases hexp
    | some t₀ =>
      rw [hve] at hexp
      exact ⟨t₀, rfl, of_decide_eq_true hexp⟩

/-- The three shapes of an accepted event: a delivery or view entry (clock and log unchanged,
    deliveries and entries only grow), a send (by a faulty sender, or by the honest rule), or a
    tick from a settled state. -/
theorem netStep_cases {P : Protocol} {cfg : NetConfig} {s s' : NetState} {e : NetEvent}
    (h : netStep P cfg s e = some s') :
    (s'.time = s.time ∧ s'.log = s.log ∧
      (∀ n m, s.delivered n m = true → s'.delivered n m = true) ∧
      (∀ n v t, s.viewEntry n v = some t → s'.viewEntry n v = some t)) ∨
    (∃ m, s' = s.push m ∧ (P.faulty m.sender = true ∨ honestSendOk P cfg s m = true)) ∨
    (s' = { s with time := s.time + 1 } ∧ settledB P cfg s = true) := by
  cases e with
  | deliver n m =>
    simp only [netStep] at h
    split at h
    · injection h with h
      subst h
      exact .inl ⟨rfl, rfl, fun n' m' hd => by simp [hd], fun _ _ _ ht => ht⟩
    · cases h
  | inject m =>
    simp only [netStep] at h
    split at h
    · rename_i hf
      injection h with h
      exact .inr (.inl ⟨m, h.symm, .inl hf⟩)
    · cases h
  | enter n v p =>
    simp only [netStep] at h
    split at h
    · rename_i hc
      injection h with h
      subst h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      refine .inl ⟨rfl, rfl, fun _ _ hd => hd, fun n' v' t ht => ?_⟩
      by_cases hnv : n' = n ∧ v' = v
      · rw [hnv.1, hnv.2, hc.2] at ht
        cases ht
      · simp only [hnv, ↓reduceIte]
        exact ht
    · cases h
  | send m =>
    simp only [netStep] at h
    split at h
    · rename_i hc
      injection h with h
      exact .inr (.inl ⟨m, h.symm, .inr hc⟩)
    · cases h
  | tick =>
    simp only [netStep] at h
    split at h
    · rename_i hc
      injection h with h
      exact .inr (.inr ⟨h.symm, hc⟩)
    · cases h

/-- An accepted event leaves the message list alone or adds one `SimplexProtocol.Step` to it. -/
theorem netStep_sent {P : Protocol} {cfg : NetConfig} {s s' : NetState} {e : NetEvent}
    (h : netStep P cfg s e = some s') : s'.sent = s.sent ∨ Step P s.sent s'.sent := by
  rcases netStep_cases h with ⟨_, hlog, _, _⟩ | ⟨m, rfl, hm⟩ | ⟨rfl, _⟩
  · left
    unfold NetState.sent
    rw [hlog]
  · right
    rcases hm with hf | ho
    · exact Step.inject s.sent m hf
    · exact honestSendOk_step ho
  · exact .inl rfl

theorem netStep_reach {P : Protocol} {cfg : NetConfig} {s s' : NetState} {e : NetEvent}
    (h : netStep P cfg s e = some s') (hr : Reach P s.sent) : Reach P s'.sent := by
  rcases netStep_sent h with hs | hs
  · rw [hs]
    exact hr
  · exact Reach.step hr hs

/-- **Every timed trace is a `SimplexProtocol` run**: the safety theorems of `SimplexProtocol`
    hold of the message list of any `runNet`. -/
theorem runNet_reach {P : Protocol} {cfg : NetConfig} :
    ∀ (evs : List NetEvent) {s s' : NetState},
      runNet P cfg s evs = some s' → Reach P s.sent → Reach P s'.sent
  | [], s, s', h, hr => by
    have h' : some s = some s' := h
    injection h' with h'
    subst h'
    exact hr
  | e :: es, s, s', h, hr => by
    obtain ⟨s₁, h1, h2⟩ := runNet_cons.1 h
    exact runNet_reach es h2 (netStep_reach h1 hr)

/-! ## 6. Post-GST finalization over every timed trace -/

/-- View `v` is launched at `s₀`, after GST: its leader is honest and has proposed the block
    `p ++ [.block v x]` (and nothing else in the view); every honest node has entered the view
    with at least `deltaNet` left on its timer, holds the notarized parent chain `p` in its own
    deliveries, and has not voted in the view. Nothing is assumed about what happens next. -/
structure ViewLaunched (P : Protocol) (cfg : NetConfig) (s₀ : NetState) (v : Nat) (p : Chain)
    (x : Nat) : Prop where
  reach : Reach P s₀.sent
  postGst : cfg.gst ≤ s₀.time
  deltaPos : 0 < cfg.deltaNet
  stamped : ∀ e ∈ s₀.log, e.2 ≤ s₀.time
  viewPos : 1 ≤ v
  parentLen : p.length = v - 1
  leaderHonest : P.honest (P.leader v)
  proposed : (⟨P.leader v, v, .propose, .block (p ++ [.block v x])⟩ : Msg) ∈ s₀.sent
  oneProposal : ∀ m ∈ s₀.sent, m.sender = P.leader v → m.view = v → m.kind = .propose →
    m.target = .block (p ++ [.block v x])
  entered : ∀ n, P.honest n →
    ∃ t₀, s₀.viewEntry n v = some t₀ ∧ s₀.time + cfg.deltaNet < t₀ + cfg.timeout
  parentKnown : ∀ n, P.honest n → ChainNotarized P (s₀.localView n) p
  fresh : ∀ n, P.honest n → votedAny s₀.sent n v = false

/-- What holds of every state a timed trace reaches from a launch at time `T`: the proposal stays
    the leader's only one; honest votes in the view are for the block and were sent by
    `T + deltaNet`; past `T + deltaNet` every honest node has voted for it; past `T + 2 * deltaNet`
    every honest node has finalized it. -/
structure ViewProgress (P : Protocol) (cfg : NetConfig) (T : Nat) (v : Nat) (p : Chain) (x : Nat)
    (s : NetState) : Prop where
  reach : Reach P s.sent
  clock : T ≤ s.time
  stamped : ∀ e ∈ s.log, e.2 ≤ s.time
  proposed : ∃ t, t ≤ T ∧
    ((⟨P.leader v, v, .propose, .block (p ++ [.block v x])⟩ : Msg), t) ∈ s.log
  oneProposal : ∀ m ∈ s.sent, m.sender = P.leader v → m.view = v → m.kind = .propose →
    m.target = .block (p ++ [.block v x])
  entered : ∀ n, P.honest n →
    ∃ t₀, s.viewEntry n v = some t₀ ∧ T + cfg.deltaNet < t₀ + cfg.timeout
  parentKnown : ∀ n, P.honest n → ChainNotarized P (s.localView n) p
  votes : ∀ m ∈ s.sent, P.honest m.sender → m.view = v → m.kind = .vote →
    m.target = .block (p ++ [.block v x]) ∧ ∃ t, t ≤ T + cfg.deltaNet ∧ (m, t) ∈ s.log
  allVoted : T + cfg.deltaNet < s.time →
    ∀ n, P.honest n → voted s.sent n v (.block (p ++ [.block v x])) = true
  allFinal : T + 2 * cfg.deltaNet < s.time →
    ∀ n, P.honest n → finalizeVoted s.sent n v (p ++ [.block v x]) = true

theorem ViewLaunched.progress {P : Protocol} {cfg : NetConfig} {s₀ : NetState} {v : Nat}
    {p : Chain} {x : Nat} (hL : ViewLaunched P cfg s₀ v p x) :
    ViewProgress P cfg s₀.time v p x s₀ where
  reach := hL.reach
  clock := Nat.le_refl _
  stamped := hL.stamped
  proposed := by
    have hp := hL.proposed
    unfold NetState.sent at hp
    obtain ⟨e, he, heq⟩ := List.mem_map.1 hp
    refine ⟨e.2, hL.stamped e he, ?_⟩
    rw [← heq]
    exact he
  oneProposal := hL.oneProposal
  entered := hL.entered
  parentKnown := hL.parentKnown
  votes := by
    intro m hm hon hv hk
    have hany := votedAny_of_mem hm hk
    rw [hv, hL.fresh m.sender hon] at hany
    cases hany
  allVoted := fun h => absurd h (by omega)
  allFinal := fun h => absurd h (by omega)

/-- One accepted event keeps `ViewProgress`. The tick is where the model's two obligations are
    used: at the tick out of `T + deltaNet` the proposal has been delivered to every honest node,
    so none is left without a vote; at the tick out of `T + 2 * deltaNet` every honest vote has
    been delivered to every honest node, so each sees the notarization and has finalized. -/
theorem ViewProgress.step {P : Protocol} {cfg : NetConfig} {s₀ s s' : NetState} {v : Nat}
    {p : Chain} {x : Nat} {e : NetEvent} (hL : ViewLaunched P cfg s₀ v p x)
    (hI : ViewProgress P cfg s₀.time v p x s) (h : netStep P cfg s e = some s') :
    ViewProgress P cfg s₀.time v p x s' := by
  have hReach := netStep_reach h hI.reach
  rcases netStep_cases h with ⟨htime, hlog, hdel, hent⟩ | ⟨m, rfl, hm⟩ | ⟨rfl, hset⟩
  · have hsent : s'.sent = s.sent := by unfold NetState.sent; rw [hlog]
    have hlocal : ∀ n q, q ∈ s.localView n → q ∈ s'.localView n := by
      intro n q hq
      obtain ⟨h1, h2⟩ := NetState.mem_localView.1 hq
      exact NetState.mem_localView.2 ⟨by rw [hsent]; exact h1, hdel n q h2⟩
    exact
      { reach := hReach
        clock := by rw [htime]; exact hI.clock
        stamped := by rw [hlog, htime]; exact hI.stamped
        proposed := by rw [hlog]; exact hI.proposed
        oneProposal := by rw [hsent]; exact hI.oneProposal
        entered := fun n hn => by
          obtain ⟨t₀, ht, hb⟩ := hI.entered n hn
          exact ⟨t₀, hent n v t₀ ht, hb⟩
        parentKnown := fun n hn => chainNotarized_mono (hlocal n) (hI.parentKnown n hn)
        votes := by rw [hsent, hlog]; exact hI.votes
        allVoted := by rw [htime, hsent]; exact hI.allVoted
        allFinal := by rw [htime, hsent]; exact hI.allFinal }
  · have hhon : P.honest m.sender → honestSendOk P cfg s m = true := by
      intro hon
      rcases hm with hf | ho
      · rw [hon.2] at hf; cases hf
      · exact ho
    have hlocal : ∀ n q, q ∈ s.localView n → q ∈ (s.push m).localView n := by
      intro n q hq
      obtain ⟨h1, h2⟩ := NetState.mem_localView.1 hq
      exact NetState.mem_localView.2 ⟨List.mem_cons_of_mem m h1, h2⟩
    have hlate : s₀.time + cfg.deltaNet < s.time → ∀ n, P.honest n →
        votedAny s.sent n v = true := by
      intro hlt n hn
      exact votedAny_of_mem ((voted_iff _ _ _ _).1 (hI.allVoted hlt n hn)) rfl
    exact
      { reach := hReach
        clock := hI.clock
        stamped := by
          intro e he
          have he' : e ∈ (m, s.time) :: s.log := he
          rcases List.mem_cons.1 he' with rfl | he''
          · exact Nat.le_refl _
          · exact hI.stamped e he''
        proposed := by
          obtain ⟨t, ht, hmem⟩ := hI.proposed
          exact ⟨t, ht, List.mem_cons_of_mem _ hmem⟩
        oneProposal := by
          intro q hq hs hv hk
          have hq' : q ∈ m :: s.sent := hq
          rcases List.mem_cons.1 hq' with hqm | hq''
          · exfalso
            rw [hqm] at hs hv hk
            have ho := hhon (by rw [hs]; exact hL.leaderHonest)
            obtain ⟨t, _, hmem⟩ := hI.proposed
            exact honestSendOk_propose_fresh ho hk _ (NetState.mem_sent_of_mem_log hmem)
              hs.symm hv.symm rfl
          · exact hI.oneProposal q hq'' hs hv hk
        entered := hI.entered
        parentKnown := fun n hn => chainNotarized_mono (hlocal n) (hI.parentKnown n hn)
        votes := by
          intro q hq hon hv hk
          have hq' : q ∈ m :: s.sent := hq
          rcases List.mem_cons.1 hq' with hqm | hq''
          · rw [hqm] at hon hv hk ⊢
            obtain ⟨hfresh, hcase⟩ := honestSendOk_vote (hhon hon) hk
            rw [hv] at hfresh hcase
            have hle : s.time ≤ s₀.time + cfg.deltaNet := by
              rcases Nat.lt_or_ge (s₀.time + cfg.deltaNet) s.time with hlt | hge
              · have hv' := hlate hlt m.sender hon
                rw [hfresh] at hv'
                cases hv'
              · exact hge
            refine ⟨?_, s.time, hle, List.mem_cons_self⟩
            rcases hcase with ⟨c, hc, hprop⟩ | ⟨t₀, ht₀, hexp⟩
            · rw [hc]
              exact hI.oneProposal _ hprop rfl rfl rfl
            · exfalso
              obtain ⟨t₁, ht₁, hb⟩ := hI.entered m.sender hon
              rw [ht₀] at ht₁
              injection ht₁ with ht₁
              omega
          · obtain ⟨ht, t, hle, hmem⟩ := hI.votes q hq'' hon hv hk
            exact ⟨ht, t, hle, List.mem_cons_of_mem _ hmem⟩
        allVoted := fun hlt n hn => voted_cons s.sent m n v _ (hI.allVoted hlt n hn)
        allFinal := fun hlt n hn => finalizeVoted_cons s.sent m n v _ (hI.allFinal hlt n hn) }
  · have hgst := hL.postGst
    have hpos := hL.deltaPos
    exact
      { reach := hReach
        clock := Nat.le_succ_of_le hI.clock
        stamped := fun e he => Nat.le_succ_of_le (hI.stamped e he)
        proposed := hI.proposed
        oneProposal := hI.oneProposal
        entered := hI.entered
        parentKnown := hI.parentKnown
        votes := hI.votes
        allVoted := by
          intro hlt n hn
          rcases Nat.lt_or_ge (s₀.time + cfg.deltaNet) s.time with h1 | h1
          · exact hI.allVoted h1 n hn
          · have hlt' : s₀.time + cfg.deltaNet < s.time + 1 := hlt
            obtain ⟨t, ht, hmem⟩ := hI.proposed
            have hdel := settled_delivered hset hmem (by omega) (by omega) hn
            have hloc : (⟨P.leader v, v, .propose, .block (p ++ [.block v x])⟩ : Msg)
                ∈ s.localView n :=
              NetState.mem_localView.2 ⟨NetState.mem_sent_of_mem_log hmem, hdel⟩
            have hrule := voteRuleB_of_proposal hL.viewPos hL.parentLen (hI.parentKnown n hn) hloc
            obtain ⟨t₀, ht₀, _⟩ := hI.entered n hn
            have hany : votedAny s.sent n v = true :=
              settled_vote hset hn hloc rfl
                (by show (s.viewEntry n v).isSome = true; rw [ht₀]; rfl) hrule
            unfold votedAny at hany
            obtain ⟨q, hq, hqc⟩ := List.any_eq_true.1 hany
            simp only [Bool.and_eq_true, beq_iff_eq] at hqc
            obtain ⟨hb, _⟩ := hI.votes q hq (by rw [hqc.1.1]; exact hn) hqc.1.2 hqc.2
            rcases q with ⟨qs, qv, qk, qt⟩
            simp only at hqc hb
            rw [hqc.1.1, hqc.1.2, hqc.2, hb] at hq
            exact (voted_iff _ _ _ _).2 hq
        allFinal := by
          intro hlt n hn
          rcases Nat.lt_or_ge (s₀.time + 2 * cfg.deltaNet) s.time with h1 | h1
          · exact hI.allFinal h1 n hn
          · have hlt' : s₀.time + 2 * cfg.deltaNet < s.time + 1 := hlt
            have hV := hI.allVoted (by omega)
            have hnot : NotarizedBlock P (s.localView n) v (p ++ [.block v x]) := by
              refine quorum_of_all_honest P _ (fun u hu => ?_)
              have hvu := (voted_iff _ _ _ _).1 (hV u hu)
              obtain ⟨_, t, ht, hmem⟩ := hI.votes _ hvu hu rfl rfl
              have hdel := settled_delivered hset hmem (by omega) (by omega) hn
              exact (voted_iff _ _ _ _).2 (NetState.mem_localView.2 ⟨hvu, hdel⟩)
            exact settled_fin hset hn ((voted_iff _ _ _ _).1 (hV n hn)) hnot }

theorem runNet_viewProgress {P : Protocol} {cfg : NetConfig} {s₀ : NetState} {v : Nat}
    {p : Chain} {x : Nat} (hL : ViewLaunched P cfg s₀ v p x) :
    ∀ (evs : List NetEvent) {s s' : NetState},
      ViewProgress P cfg s₀.time v p x s → runNet P cfg s evs = some s' →
      ViewProgress P cfg s₀.time v p x s'
  | [], s, s', hI, h => by
    have h' : some s = some s' := h
    injection h' with h'
    subst h'
    exact hI
  | e :: es, s, s', hI, h => by
    obtain ⟨s₁, h1, h2⟩ := runNet_cons.1 h
    exact runNet_viewProgress hL es (hI.step hL h1) h2

/-- **Post-GST finalization over every adversarial timed trace.** Launch view `v` after GST with
    an honest leader (`ViewLaunched`). Then for every event list the network accepts (any delivery
    order, any delays within `deltaNet`, any messages injected by faulty senders), once the clock
    has passed `2 * deltaNet` beyond the launch: the message list is a `SimplexProtocol` run,
    every honest node voted for the leader's block and none for the dummy, the block is finalized,
    and its finalization certificate checks and is the only one at its height. -/
theorem gst_honest_leader_finalizes
    {P : Protocol} {cfg : NetConfig} {s₀ : NetState} {v : Nat} {p : Chain} {x : Nat}
    (hL : ViewLaunched P cfg s₀ v p x) {evs : List NetEvent} {s : NetState}
    (hRun : runNet P cfg s₀ evs = some s) (hTime : s₀.time + 2 * cfg.deltaNet < s.time) :
    Reach P s.sent ∧
    (∀ n, P.honest n → voted s.sent n v (.block (p ++ [.block v x])) = true ∧
      voted s.sent n v (.dummy v) = false) ∧
    Finalized P s.sent v (p ++ [.block v x]) ∧
    ∃ cert : FinCert, cert.view = v ∧ cert.chain = p ++ [.block v x] ∧
      cert.checks P s.sent = true ∧
      ∀ other : FinCert, other.checks P s.sent = true →
        other.chain.height = (p ++ [Entry.block v x]).height →
        other.chain.blocks = (p ++ [Entry.block v x]).blocks := by
  have hI := runNet_viewProgress hL evs hL.progress hRun
  have hpos := hL.deltaPos
  have hFin : Finalized P s.sent v (p ++ [.block v x]) :=
    quorum_of_all_honest P _ (hI.allFinal hTime)
  obtain ⟨cert, _, hcv, hcc, hchk⟩ := extractFinCert_checks_of_finalized hFin
  refine ⟨hI.reach, fun n hn => ⟨hI.allVoted (by omega) n hn, ?_⟩, hFin, cert, hcv, hcc, hchk, ?_⟩
  · cases hd : voted s.sent n v (.dummy v) with
    | false => rfl
    | true =>
      have ht := (hI.votes _ ((voted_iff _ _ _ _).1 hd) hn rfl rfl).1
      simp at ht
  · intro other hother hheight
    have hEq := FinCert.unique_per_height_reach hI.reach hother hchk (by rw [hcc]; exact hheight)
    rw [hcc] at hEq
    exact hEq

/-! ## 7. The premises are inhabited: four validators, three honest, a 256-bit payload -/

private def sampleProto4 : Protocol :=
  ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩

/-- One block whose payload needs more than 64 bits. -/
private def sampleBlock : Chain := [.block 1 (2 ^ 200 + 777)]

private def sampleProposal : Msg := ⟨0, 1, .propose, .block sampleBlock⟩
private def sampleVote (n : NodeId) : Msg := ⟨n, 1, .vote, .block sampleBlock⟩
private def sampleFin (n : NodeId) : Msg := ⟨n, 1, .finalize, .block sampleBlock⟩
private def sampleEquivocation : Msg := ⟨3, 1, .vote, .block [.block 1 666]⟩

private def sampleHash : HashBytes.Hash :=
  Obend.Digest.Cshake256.Fast.cshake256Fast simplexAuthDomainBytes

private def sampleSalt : NodeId → Nat → Kind → ByteArray :=
  fun n _ _ => bytesOfList (List.replicate 32 (UInt8.ofNat (n + 1)))

private def sampleLog : List Msg := [sampleProposal, sampleVote 0, sampleVote 1, sampleVote 2]

private def sampleSigned (m : Msg) : SignedSimplexMsg := ⟨m, sampleSalt m.sender m.view m.kind⟩

/-- Slot keys for a committee with three honest validators: `HonestSlotKeys` is satisfiable with
    more than one honest validator, each key made from its owner's slot alone. -/
example : HonestSlotKeys sampleHash 4096 (KeyDirectory.derive sampleHash sampleLog sampleSalt)
    sampleProto4 sampleLog sampleSalt :=
  KeyDirectory.derive_honestSlotKeys sampleHash 4096 200 sampleProto4 sampleLog sampleSalt
    (fun bs => by
      rw [sampleHash, Obend.Digest.Cshake256.Fast.cshake256Fast_eq]
      exact Obend.Digest.Cshake256.cshake256Bytes_length _ _) (by decide +kernel)
    (fun n v k => by simp [sampleSalt, bytesOfList_toList]) (by decide +kernel) (by decide)

example : msgCanonical (sampleVote 2) = true := by decide +kernel
example : checkHonestProtocolRule sampleProto4 [] sampleProposal = true := by decide +kernel
example : verifySignedSent (commitSlotSigScheme sampleHash 4096)
    (KeyDirectory.derive sampleHash sampleLog sampleSalt)
    sampleProto4.committee (sampleLog.map sampleSigned) = true := by decide +kernel

private def sampleCfg : NetConfig := ⟨0, 1, 5⟩

private def sampleNet₀ : NetState where
  time := 0
  log := [(sampleProposal, 0)]
  delivered := fun _ _ => false
  viewEntry := fun _ v => if v = 1 then some 0 else none

private def deliverAll (ms : List Msg) : List NetEvent :=
  ms.flatMap fun m => [0, 1, 2].map fun n => NetEvent.deliver n m

/-- A run the adversary could choose: the Byzantine validator equivocates, deliveries come at the
    last allowed moment. -/
private def sampleRun : List NetEvent :=
  deliverAll [sampleProposal] ++
  [.send (sampleVote 0), .send (sampleVote 1), .send (sampleVote 2), .inject sampleEquivocation,
   .tick] ++
  deliverAll [sampleVote 0, sampleVote 1, sampleVote 2, sampleEquivocation] ++
  [.send (sampleFin 0), .send (sampleFin 1), .send (sampleFin 2), .tick] ++
  deliverAll [sampleFin 0, sampleFin 1, sampleFin 2] ++ [.tick]

private theorem sampleViewLaunched : ViewLaunched sampleProto4 sampleCfg sampleNet₀ 1 [] (2 ^ 200 + 777) where
  reach := Reach.step Reach.nil
    (Step.propose [] 0 1 sampleBlock ⟨by decide, by decide⟩ (by decide))
  postGst := Nat.le_refl _
  deltaPos := by decide
  stamped := by decide
  viewPos := Nat.le_refl _
  parentLen := rfl
  leaderHonest := ⟨by decide, by decide⟩
  proposed := List.Mem.head _
  oneProposal := by
    intro m hm _ _ _
    have hm' : m ∈ [sampleProposal] := hm
    rw [List.mem_singleton] at hm'
    rw [hm']
    rfl
  entered := fun _ _ => ⟨0, rfl, by decide⟩
  parentKnown := fun _ _ k hk => absurd hk (Nat.not_lt_zero k)
  fresh := fun n _ => by simp [votedAny, sampleNet₀, NetState.sent, sampleProposal]

/-- The model is not stuck: this run is accepted and its clock passes `2 * deltaNet`. -/
example : (runNet sampleProto4 sampleCfg sampleNet₀ sampleRun).map (·.time) = some 3 := by
  decide +kernel

/-- So the liveness theorem applies to it. -/
example : ∀ s, runNet sampleProto4 sampleCfg sampleNet₀ sampleRun = some s →
    Finalized sampleProto4 s.sent 1 sampleBlock := by
  intro s h
  have ht : (runNet sampleProto4 sampleCfg sampleNet₀ sampleRun).map (·.time) = some 3 := by
    decide +kernel
  rw [h] at ht
  have ht' : s.time = 3 := by simpa using ht
  exact (gst_honest_leader_finalizes sampleViewLaunched h (by rw [ht']; decide)).2.2.1

end Obend.Consensus.SimplexLiveness
end
