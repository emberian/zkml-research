module
/-
# G3 teeth: CapTP 256-bit keys and the authenticated message epoch

Compiles against the patched `Obend.Polis.CapTP` (patch 0003-G3-captp-digest256-epoch). Every
statement is checked by the kernel; nothing here is `sorry`, `axiom` or `native_decide`.

(a) `verifyHybridHandoff` refuses every certificate whose `msgEpoch` is 0, and the same fixture
    is accepted at epoch 1 (the epoch is the only difference: premise inhabitation).
(b) A 64-bit truncation collision: two distinct 256-bit nonces with the same low `UInt64` limb.
    `SortedDigestSet` keeps them apart; a `SortedU64Set` of truncations conflates them.
(c) `#tooth` mutations showing stored proofs depend on the epoch check and on the epoch binding.
-/
public import Obend.Polis.CapTP
import all Obend.Polis.CapTP
import all Obend.Core.Digest
import Obend.Tactic.Tooth

public section
namespace Obend.Teeth.G3
open Obend.Polis.CapTP Obend.Vault.Mandate Obend.Crypto

/-! ## (a) epoch 0 is refused -/

theorem epoch_zero_refused (v : HybridSigVerifier) (held : Mandate) (hc ai ci : ByteArray)
    (seen : SortedDigestSet) (c : HybridHandoffCert) (h0 : c.msgEpoch = 0) :
    verifyHybridHandoff v held hc ai ci seen c = false := by
  simp [verifyHybridHandoff, h0]

theorem accepted_epoch_nonzero (v : HybridSigVerifier) (held : Mandate) (hc ai ci : ByteArray)
    (seen : SortedDigestSet) (c : HybridHandoffCert)
    (h : verifyHybridHandoff v held hc ai ci seen c = true) : c.msgEpoch ≠ 0 :=
  (verifyHybridHandoff_sound v held hc ai ci seen c h).2.2.2.2.2.2.2.1

@[expose] def alice : Principal := ⟨"Alice", 1⟩
@[expose] def carol : Principal := ⟨"Carol", 3⟩
@[expose] def held : Mandate :=
  ⟨1, .root alice "Bob", alice, "Bob", [.read, .call], 20, [1,2], 100, .any⟩
@[expose] def request : DelegationRequest := ⟨2, carol, [.call], 7, [1], 90, [5]⟩
@[expose] def identity : HybridIdentity := ⟨⟨#[1,2]⟩, ⟨#[3,4]⟩⟩
@[expose] def signatures : HybridSignature := ⟨⟨#[1,2]⟩, ⟨#[3,4]⟩⟩
/-- Test-only signature adapters: they exercise the composition, not Ed25519 or ML-DSA. -/
@[expose] def testSignatures : HybridSigVerifier :=
  ⟨fun key _ sig => decide (key = sig), fun key _ sig => decide (key = sig)⟩
@[expose] def certAt (epoch : UInt64) : HybridHandoffCert :=
  ⟨"Bob".toUTF8, "Alice-Carol".toUTF8, 17, epoch, identity, identity, request, signatures, signatures⟩

/-- Premise inhabitation: the fixture is accepted at epoch 1. -/
example : verifyHybridHandoff testSignatures held ByteArray.empty
    (hybridIdentityDigest identity) (hybridIdentityDigest identity) SortedDigestSet.empty
    (certAt 1) = true := by
  simp only [verifyHybridHandoff, certAt, eq_self, decide_true, Bool.true_and, verifyBoth,
    testSignatures, identity, signatures, Bool.and_true]
  rfl

/-- Falsifier: the same fixture at epoch 0, with the same (test) signatures, is refused. -/
example : verifyHybridHandoff testSignatures held ByteArray.empty
    (hybridIdentityDigest identity) (hybridIdentityDigest identity) SortedDigestSet.empty
    (certAt 0) = false :=
  epoch_zero_refused _ _ _ _ _ _ _ rfl

/-- The epoch is inside the signed bytes: messages at distinct epochs differ. -/
theorem distinct_epochs_distinct_messages (role : String) (hc : ByteArray) (c : HybridHandoffCert)
    (e : UInt64) (he : c.msgEpoch ≠ e) :
    handoffMessage role hc c ≠ handoffMessage role hc { c with msgEpoch := e } :=
  fun h => he (handoffMessage_binds_nonce_epoch h).2

/-! ## (b) a 64-bit truncation collision -/

/-- The low `UInt64` limb (bits 63–0) of a 256-bit key: what a 64-bit table would store. -/
@[expose] def lowLimb (d : SwissNum) : UInt64 := (Obend.Core.Digest.DigestWords4.ofDigest256 d).w3

@[expose] def nonceA : SwissNum := 1
@[expose] def nonceB : SwissNum := BitVec.ofNat 256 (2 ^ 64 + 1)

theorem nonces_distinct : nonceA ≠ nonceB := by decide
theorem nonces_truncate_equal : lowLimb nonceA = lowLimb nonceB := by decide

/-- 256-bit replay set: spending `nonceA` does not mark `nonceB` as seen. -/
theorem digestSet_separates : (SortedDigestSet.empty.insert nonceA).contains nonceB = false := by
  decide

theorem digestSet_holds_spent : (SortedDigestSet.empty.insert nonceA).contains nonceA = true := by
  decide

/-- The same two nonces collide in a 64-bit set of truncations. -/
theorem u64Set_conflates :
    (SortedU64Set.empty.insert (lowLimb nonceA)).contains (lowLimb nonceB) = true := by
  decide

/-- General form: inserting `a` changes membership of no other key. -/
theorem digestSet_insert_other (s : SortedDigestSet) (a b : SwissNum) (hne : b ≠ a) :
    (s.insert a).contains b = s.contains b := by
  apply Bool.eq_iff_iff.mpr
  rw [SortedDigestSet.contains_eq_spec, SortedDigestSet.contains_eq_spec,
    SortedDigestSet.spec_insert]
  exact ⟨fun h => h.resolve_left hne, Or.inr⟩

/-- At the handoff: a certificate whose nonce shares its low limb with a spent nonce is not
refused as a replay. -/
theorem handoff_not_replay_of_truncation_alias :
    (SortedDigestSet.empty.insert nonceA).contains ({ certAt 1 with handoffNonce := nonceB }).handoffNonce
      = false := digestSet_separates

/-! ## (c) teeth -/

-- Dropping the epoch check breaks the stored soundness proof (its `c.msgEpoch ≠ 0` conjunct).
#tooth verifyHybridHandoff_sound by mutation verifyHybridHandoff :=
  fun v held heldCommitment introducerDigest recipientDigest seen c =>
    decide (hybridIdentityDigest c.introducer = introducerDigest) &&
    decide (hybridIdentityDigest c.recipient = recipientDigest) &&
    verifyBoth v c.introducer (handoffMessage "HandoffGive" heldCommitment c) c.giveSig &&
    verifyBoth v c.recipient (handoffMessage "HandoffAccept" heldCommitment c) c.acceptSig &&
    !seen.contains c.handoffNonce && requestFits c.request held

#tooth verifyHybridHandoff_rejects_epoch_zero by mutation verifyHybridHandoff :=
  fun v held heldCommitment introducerDigest recipientDigest seen c =>
    decide (hybridIdentityDigest c.introducer = introducerDigest) &&
    decide (hybridIdentityDigest c.recipient = recipientDigest) &&
    verifyBoth v c.introducer (handoffMessage "HandoffGive" heldCommitment c) c.giveSig &&
    verifyBoth v c.recipient (handoffMessage "HandoffAccept" heldCommitment c) c.acceptSig &&
    !seen.contains c.handoffNonce && requestFits c.request held

-- The pre-G3 message (nonce only, no epoch) breaks the stored binding proof.
#tooth handoffMessage_binds_nonce_epoch by mutation handoffMessage :=
  fun role heldCommitment c =>
    encodeFrame role.toUTF8
      (encodeFrame c.vatId c.sessionId (encodeNats [c.handoffNonce.toNat]))
      (encodeFrame heldCommitment c.request.bytes
        (encodeFrame (hybridIdentityDigest c.introducer) (hybridIdentityDigest c.recipient)
          ByteArray.empty))

-- A 64-bit truncating key breaks the stored digest-set membership proof.
#tooth SortedDigestSet.contains_eq_spec by mutation SortedDigestSet.contains :=
  fun s k => (s.data.toList.map lowLimb).contains (lowLimb k)

#print axioms epoch_zero_refused
#print axioms digestSet_separates
#print axioms u64Set_conflates
#print axioms handoffMessage_binds_nonce_epoch

end Obend.Teeth.G3
