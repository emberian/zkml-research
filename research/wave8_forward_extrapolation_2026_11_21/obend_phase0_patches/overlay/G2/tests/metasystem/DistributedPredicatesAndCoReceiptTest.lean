module
public import Obend.Polis.PrivatePredicate
public import Obend.Polis.JointCoReceipt
public import Obend.Ledger.Floors
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Polis.PrivatePredicate
import all Obend.Polis.JointCoReceipt
meta import all Obend.Polis.PrivatePredicate
meta import all Obend.Polis.JointCoReceipt
meta import all Obend.Ledger.Floors
-- The census reads every body in the import closure.
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Fold
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Law.Syntax
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Polis.CapTP
import all Obend.Polis.EvidencedOcap
import all Obend.Polis.BlumRam
import all Obend.Polis.ZkBiscuit
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Obend.Vault.Mandate

/-!
# `tests/metasystem/DistributedPredicatesAndCoReceiptTest.lean`

Runs `Obend.Polis.PrivatePredicate` and `Obend.Polis.JointCoReceipt` on concrete data.

* `#guard` lines execute the checkers (cSHAKE256 included, which the kernel does not evaluate).
* `example`s instantiate the universal theorems, or decide hash-free facts in the kernel.
* Each `#tooth` replaces one check by a weaker one and requires the kernel to reject the stored
  proof of a universal theorem that depended on it.
* `#assert_axioms_tree` is the axiom census over every package constant this file can see.
-/

public section
namespace Obend.Tests.Metasystem.DistributedPredicatesAndCoReceiptTest

open Obend.Polis
open Obend.Polis.PrivatePredicate
open Obend.Polis.JointCoReceipt
open Obend.Ledger (FloorBook FloorsHold floorsHold_empty)

-- ============================================================================
-- 1. `DistPred`: evaluation, both polarities of `witnessed`, residuals
-- ============================================================================

def vkA : VkId := ⟨⟨#[1]⟩⟩
def vkB : VkId := ⟨⟨#[2]⟩⟩

/-- Slot 0 went 3 → 5, slot 1 was written first with 7, slot 2 kept 9. -/
def σ0 : Step := fun s =>
  match s with
  | 0 => ⟨some 3, some 5⟩
  | 1 => ⟨none, some 7⟩
  | 2 => ⟨some 9, some 9⟩
  | _ => ⟨none, none⟩

#guard evalFirstParty σ0 (.eq 0 5) == .true3
#guard evalFirstParty σ0 (.le 0 4) == .false3
#guard evalFirstParty σ0 (.memberOf 1 [6, 7]) == .true3
#guard evalFirstParty σ0 (.writeOnce 1) == .true3
#guard evalFirstParty σ0 (.writeOnce 2) == .true3
#guard evalFirstParty σ0 (.writeOnce 0) == .false3
#guard evalFirstParty σ0 (.monotone 0) == .true3
#guard evalFirstParty σ0 (.monotone 1) == .false3
#guard evalFirstParty σ0 (.eq 3 0) == .false3
#guard evalFirstParty σ0 (.hashEq 0 (slotDigest 5)) == .true3
#guard evalFirstParty σ0 (.hashEq 0 (slotDigest 6)) == .false3
#guard (slotDigest 5).size == 32

-- A third-party claim is open to the vat alone, under negation too.
#guard evalFirstParty σ0 (.witnessed vkA) == .unbound3
#guard !admits noOracle σ0 (.witnessed vkA)
#guard !admits noOracle σ0 (.not (.witnessed vkA))
#guard admits (dischargeOracle [vkA]) σ0 (.witnessed vkA)
#guard !admits (dischargeOracle [vkB]) σ0 (.witnessed vkA)
#guard !admits (dischargeOracle [vkA]) σ0 (.not (.witnessed vkA))
-- Only a refutation makes a negated claim true.
#guard admits (fun _ => .false3) σ0 (.not (.witnessed vkA))
-- Strong Kleene: a decided child decides the connective around an open one.
#guard evalFirstParty σ0 (.all (.ofList [.le 0 4, .witnessed vkA])) == .false3
#guard evalFirstParty σ0 (.any (.ofList [.eq 0 5, .witnessed vkA])) == .true3
#guard evalFirstParty σ0 (.all (.ofList [.eq 0 5, .witnessed vkA])) == .unbound3

example : evalFirstParty σ0 (.all (.ofList [.eq 0 5, .not (.le 0 4), .monotone 2])) = .true3 := by
  decide

example (σ : Step) (vk : VkId) : (evalFirstParty σ (.not (.witnessed vk))).accepts = false :=
  (negated_witnessed_refused_firstParty σ vk).1

example (o : Oracle) (σ : Step) (p : DistPred) (h : evalFirstParty σ p = .true3) :
    p.evalWith o σ = .true3 := by
  rw [evalFirstParty_sound_for_evalWith o σ p (by rw [h]; decide), h]

example (σ : Step) (p : DistPred) (h : admits (dischargeOracle [vkA]) σ p = true) :
    admits (dischargeOracle [vkB, vkA]) σ p = true :=
  discharge_monotone (fun vk hvk => by simp only [List.mem_cons] at hvk ⊢; exact .inr hvk) σ p h

-- The byte code is faithful and the syntax is comparable.
#guard (DistPred.eq 0 5).encode != (DistPred.le 0 5).encode
#guard DistPred.all (.ofList [.eq 0 5]) != DistPred.any (.ofList [.eq 0 5])
#guard (DistPred.eq 0 5).digest.size == 32

example (a b : DistPred) (h : a.encode = b.encode) : a = b := DistPred.encode_injective h

-- 256 codes cannot name the closures `Nat → Bool`; no table of any size names them all.
example (encode : (Nat → Bool) → Fin 256) :
    ∃ f g : Nat → Bool, (∃ s, f s ≠ g s) ∧ encode f = encode g :=
  opaque_closure_collapses_finite_encoding 256 (fun i s => s == i)
    (fun i j hij _ => ⟨i, by
      have hne : i ≠ j := by omega
      simp [hne]⟩) encode

example (decode : DistPred → DistPred → Bool) : ∃ f : DistPred → Bool, ∀ c, ∃ s, decode c s ≠ f s :=
  opaque_closure_escapes_descriptor_table decode

/-- The first vat holds slot 0. -/
def vat1 : View := fun s =>
  match s with
  | 0 => some ⟨some 3, some 5⟩
  | _ => none

/-- A second vat holds slot 1. -/
def vat2 : View := fun s =>
  match s with
  | 1 => some ⟨none, some 7⟩
  | _ => none

def guardP : DistPred := .all (.ofList [.eq 0 5, .le 1 10, .witnessed vkA])

-- The vat's atom is gone from the residual; the rest is left for whoever holds it.
#guard guardP.pevalVat vat1 == .all (.ofList [.le 1 10, .witnessed vkA])
#guard (guardP.pevalVat vat1).pevalVat vat2 == .all (.ofList [.witnessed vkA])
#guard !(guardP.pevalVat vat1).mentions 0
#guard (guardP.pevalVat vat1).mentions 1
#guard (DistPred.all (.ofList [.eq 0 6, .le 1 10, .witnessed vkA])).pevalVat vat1 == .ff
#guard (DistPred.not (.eq 0 6)).pevalVat vat1 == .tt
#guard (DistPred.any (.ofList [.eq 0 6, .le 1 10])).pevalVat vat1 == .any (.ofList [.le 1 10])
-- The second party evaluates the residual on a state that knows nothing of slot 0.
#guard admits (dischargeOracle [vkA]) (fun s => if s = 1 then ⟨none, some 7⟩ else ⟨none, none⟩)
  (guardP.pevalVat vat1)

example (p : DistPred) : (p.pevalVat vat1).mentions 0 = false :=
  DistPred.pevalVat_hides_known_slots (by decide) p

example (o : Oracle) (rest : Step) (p : DistPred) :
    p.evalWith o (overlay vat1 rest) = (p.pevalVat vat1).evalWith o rest :=
  eval_subst_eq_eval_pevalVat o vat1 rest p

-- ============================================================================
-- 2. Commitments over `ℤ/2²⁵⁶` and the graded ladder
-- ============================================================================

def ins0 : List Opening := [⟨30#256, 11#256⟩, ⟨12#256, 5#256⟩]
def outs0 : List Opening := [⟨40#256, 9#256⟩, ⟨2#256, 7#256⟩]
/-- One unit more than came in, under the same blinding total. -/
def outsInflated : List Opening := [⟨41#256, 9#256⟩, ⟨2#256, 7#256⟩]
/-- Two halves of `2²⁵⁶`: zero in the ring, not zero as a number. -/
def outsWrapped : List Opening :=
  [⟨BitVec.ofNat 256 (2 ^ 255), 0#256⟩, ⟨BitVec.ofNat 256 (2 ^ 255), 0#256⟩]

#guard homCheck (ins0.map (Opening.commit demoKey)) (outs0.map (Opening.commit demoKey))
#guard !homCheck (ins0.map (Opening.commit demoKey)) (outsInflated.map (Opening.commit demoKey))
-- The ring check alone accepts a wrapped total: this is what the range tier is for.
#guard homCheck ([⟨0#256, 0#256⟩].map (Opening.commit demoKey))
  (outsWrapped.map (Opening.commit demoKey))
#guard natSum (outsWrapped.map (·.value)) == 2 ^ 256

example : homCheck (ins0.map (Opening.commit demoKey)) (outs0.map (Opening.commit demoKey)) = true :=
  (private_conservation_iff_value_sum demoKey ins0 outs0 (by decide)).2 (by decide)

example :
    homCheck (ins0.map (Opening.commit demoKey)) (outsInflated.map (Opening.commit demoKey)) =
      false :=
  inflation_refused demoKey ins0 outsInflated (by decide) (by decide)

example (key : CommitKey) (ins outs : List Opening) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = true ↔
      commitVal key (valueSum ins) (blindSum ins) = commitVal key (valueSum outs) (blindSum outs) :=
  private_conservation_checks_homomorphically key ins outs

def rangeIds (os : List Opening) : List VkId := os.map fun op => rangeVk ⟨op.commit demoKey, 64⟩

-- Every range claim AND the audited blinding-conservation claim (`auditVk`) must be discharged:
-- range leaves alone (without `auditVk` / `auditedOracle`) are refused!
#guard (transferPred demoKey ins0 outs0 64 .tt).check (auditedOracle demoKey ins0 outs0 64) σ0
#guard !(transferPred demoKey ins0 outs0 64 .tt).check (dischargeOracle (rangeIds (ins0 ++ outs0))) σ0
#guard !(transferPred demoKey ins0 outs0 64 .tt).check noOracle σ0
#guard !(transferPred demoKey ins0 outs0 64 .tt).check (dischargeOracle (rangeIds ins0)) σ0
#guard !(transferPred demoKey ins0 outsInflated 64 .tt).check
  (auditedOracle demoKey ins0 outsInflated 64) σ0
#guard !(transferPred demoKey ins0 outs0 64 (.le 0 4)).check
  (auditedOracle demoKey ins0 outs0 64) σ0
-- Unblinded forgery (`[⟨0, 0⟩] → [⟨200, -120⟩]`) passes raw `homCheck` + 8-bit ranges,
-- but is REFUSED by `auditedOracle` / `transferPred` because `blindSum ins ≠ blindSum outs`!
#guard !(transferPred demoKey [⟨0#256, 0#256⟩] [⟨200#256, 0#256 - 120#256⟩] 8 .tt).check
  (auditedOracle demoKey [⟨0#256, 0#256⟩] [⟨200#256, 0#256 - 120#256⟩] 8) σ0

example (c v b : BitVec 256) :
    commitVal demoHidingKey.toCommitKey v b = c ↔ b = demoHidingKey.blindFor c v :=
  commitVal_hiding_bijection demoHidingKey c v b

example := demoKey_equivocates
example := homCheck_accepts_unblinded_forgery
example := privPred_conservation_inhabited

example (σ : Step) : (transferPred demoKey ins0 outs0 64 .tt).check noOracle σ = false :=
  privPred_ranges_refused_firstParty σ _ ⟨(⟨30#256, 11#256⟩ : Opening).commit demoKey, 64⟩
    (by simp [transferPred, ins0])

-- ============================================================================
-- 3. Third-party discharge
-- ============================================================================

def k3p : ByteArray := ⟨#[7, 7, 7]⟩
def rKey : ByteArray := ⟨(List.replicate 32 (9 : UInt8)).toArray⟩
def tailA : ByteArray := ⟨#[42]⟩
def tailB : ByteArray := ⟨#[43]⟩
def n1 : ByteArray := ⟨#[1]⟩
def n2 : ByteArray := ⟨#[2]⟩
def nD : ByteArray := ⟨#[3]⟩
def predId : VkId := ⟨(DistPred.le 1 10).digest⟩
def cavA : ThirdPartyCaveat := issueCaveat .empty k3p n1 n2 tailA rKey predId

/-- The third party's discharge, when it vouches for `predId`. -/
def served (preds : List DistPred) (createdAt : Nat) : Option Discharge :=
  serveTicket k3p cavA (fun vk => vk == predId) createdAt nD preds

def verdict (d : Option Discharge) (bind tail : ByteArray) (now : Nat) : Option Bool :=
  d.map fun d => verifyDischarge cavA (bindDischarge d bind) tail σ0 now 300

-- Sealing: the round trip, a wrong key, a flipped ciphertext byte, and `SealLedger` nonce freshness.
#guard aeadOpen k3p (aeadSeal k3p n1 [1, 2, 3]) == some [1, 2, 3]
#guard (aeadSeal k3p n1 [1, 2, 3]).body != [1, 2, 3]
#guard (aeadOpen tailA (aeadSeal k3p n1 [1, 2, 3])).isNone
#guard (aeadOpen k3p { aeadSeal k3p n1 [1, 2, 3] with body := [0, 0, 0] }).isNone
#guard (aeadOpen k3p { aeadSeal k3p n1 [1, 2, 3] with nonce := n2 }).isNone
#guard ((SealLedger.sealFresh ⟨[]⟩ k3p n1 [1, 2, 3]).bind fun (st1, _) =>
  st1.sealFresh k3p n1 [4, 5, 6]).isNone
#guard ((SealLedger.sealFresh ⟨[]⟩ k3p n1 [1, 2, 3]).bind fun (st1, _) =>
  st1.sealFresh k3p n2 [4, 5, 6]).isSome

example (len : Nat) : len ≤ (keystreamFor k3p n1 len).length := keystreamFor_covers k3p n1 len
example : xorWith (aeadSeal k3p n1 [1, 2, 3]).body (aeadSeal k3p n1 [4, 5, 6]).body =
    xorWith [1, 2, 3] [4, 5, 6] :=
  aeadSeal_nonce_reuse_leaks k3p n1 [1, 2, 3] [4, 5, 6] rfl

-- The third party recovers the key and the predicate; nobody else does.
#guard openTicket k3p cavA == some (rKey, predId)
#guard (openTicket tailA cavA).isNone
#guard recoverKey cavA tailA == some rKey
#guard (recoverKey cavA tailB).isNone
#guard (serveTicket k3p cavA (fun _ => false) 1000 nD []).isNone

-- Accepted: fresh, bound to the parent, the third party's caveat holds (slot 1 is 7 ≤ 10).
#guard verdict (served [.le 1 10] 1000) tailA tailA 1100 == some true
-- Stale, timestamp from the future, no timestamp.
#guard verdict (served [.le 1 10] 1000) tailA tailA 1301 == some false
#guard verdict (served [.le 1 10] 1000) tailA tailA 999 == some false
#guard verdict (served [.le 1 10] 0) tailA tailA 100 == some false
-- Bound to another parent; shown against another parent; not bound at all.
#guard verdict (served [.le 1 10] 1000) tailB tailA 1100 == some false
#guard verdict (served [.le 1 10] 1000) tailA tailB 1100 == some false
#guard ((served [.le 1 10] 1000).map fun d => verifyDischarge cavA d tailA σ0 1100 300) == some false
-- The third party's caveat bites, and a `witnessed` caveat is not decided by the verifier alone.
#guard verdict (served [.le 1 3] 1000) tailA tailA 1100 == some false
#guard verdict (served [.witnessed vkA] 1000) tailA tailA 1100 == some false
-- A caveat dropped after minting breaks the chain.
#guard ((served [.le 1 3] 1000).map fun d =>
  verifyDischarge cavA (bindDischarge { d with caveats := [] } tailA) tailA σ0 1100 300) == some false

example (createdAt now : Nat) (preds : List DistPred) (σ : Step)
    (hfresh : fresh createdAt now 300 = true)
    (hpreds : ∀ p, p ∈ preds → (evalFirstParty σ p).accepts = true) :
    ∃ d, serveTicket k3p cavA (fun vk => vk == predId) createdAt nD preds = some d ∧
      verifyDischarge cavA (bindDischarge d tailA) tailA σ now 300 = true :=
  honestDischarge_accepts .empty k3p n1 n2 tailA rKey nD predId _ createdAt now 300 preds σ
    (by decide) (by simp) hfresh hpreds

example (d : Discharge) (σ : Step) (now : Nat) (h : 300 < now - d.createdAt) :
    verifyDischarge cavA d tailA σ now 300 = false :=
  staleDischarge_refused cavA d tailA σ now 300 (.inr (.inr h))

example (cav : ThirdPartyCaveat) (d : Discharge) (a b : ByteArray) (σ : Step) (now maxAge : Nat)
    (hbind : ∀ x, DCaveat.bindToParent x ∈ d.caveats → x = bindingHash a)
    (hv : verifyDischarge cav d b σ now maxAge = true) :
    a = b ∨ Obend.Digest.HashBytes.CollisionAmong
      (Obend.Digest.Cshake256.cshake256Bytes bindCustomization)
      (fun x => x = a.data.toList ∨ x = b.data.toList) :=
  (unbound_or_wrong_parent_refused cav d a b σ now maxAge hbind hv).2

-- ============================================================================
-- 4. Joint turns, the ledger, and composition along promises
-- ============================================================================

example := tensor_not_final

def legs0 : List LocalTurn := demoDiagram.map (·.turn)

#guard checkJoint demoShared legs0
#guard demoShared.size == 32
-- One side minting a unit; a leg of another turn.
#guard !checkJoint demoShared [demoLeg 0 (-1) demoShared, demoLeg 1 2 demoShared]
#guard !checkJoint demoShared [demoLeg 0 (-1) demoShared, demoLeg 1 1 tailA]
-- A leg whose half-edge was changed after the digest was fixed, with the sum repaired elsewhere.
#guard !checkJoint demoShared
  [demoLeg 0 (-2) demoShared, demoLeg 1 1 demoShared, demoLeg 2 1 demoShared]

/-- Receipts over one forest: every leg names the forest's digest. -/
def sealTurn (raw : List LocalTurn) : ByteArray × List LocalTurn :=
  (turnDigest raw, raw.map fun t => { t with turnId := turnDigest raw })

/-- Vats 0 and 1 each hold ten units of asset 0, issued from its well. -/
def book0 : FloorBook :=
  (FloorBook.empty.applyRaw ⟨.issuerWell 0, .user 0, 0, 10⟩).applyRaw ⟨.issuerWell 0, .user 1, 0, 10⟩

def ledger0 : LedgerState := ⟨book0, 0, RevokedSet.empty, 0⟩

theorem floorsHold_book0 : FloorsHold book0 :=
  (FloorBook.admitBatch_preserves_floors (fb := .empty) (fb' := book0)
    [⟨.issuerWell 0, .user 0, 0, 10⟩, ⟨.issuerWell 0, .user 1, 0, 10⟩] floorsHold_empty
    (by decide)).1

/-- A second turn, on the ledger the first one leaves: vat 1 pays four back. -/
def turn2 : ByteArray × List LocalTurn :=
  sealTurn [⟨0, .empty, .empty, 9, 4, 13, 0, 0, 0⟩, ⟨1, .empty, .empty, 11, -4, 7, 0, 0, 0⟩]

#guard ((runTrace 2 ledger0 [(demoShared, legs0)]).map fun s =>
  (s.balances 0, s.balances 1, total (List.range 2) s.balances)) == some (9, 11, 20)
#guard ((runTrace 2 ledger0 [(demoShared, legs0), turn2]).map fun s =>
  (s.balances 0, s.balances 1, s.book.assetSum 0)) == some (13, 7, 0)
-- The same turn twice; a vat outside the ledger; a turn whose `pre` the ledger does not hold yet.
#guard (runTrace 2 ledger0 [(demoShared, legs0), (demoShared, legs0)]).isNone
#guard (runTrace 1 ledger0 [(demoShared, legs0)]).isNone
#guard (runTrace 2 ledger0 [turn2]).isNone
#guard (runTrace 2 ledger0 [(demoShared, legs0), turn2, turn2]).isNone

/-- Vat 0 named twice. Each leg is valid, each `pre` is the ledger's, the half-edges sum to zero. -/
def dupVatRaw : List LocalTurn :=
  [⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩, ⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 2, 12, 0, 0, 0⟩]
/-- Vat 0 says it held a thousand. A joint turn on its own; only the ledger knows better. -/
def unboundPreRaw : List LocalTurn :=
  [⟨0, .empty, .empty, 1000, -900, 100, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 900, 910, 0, 0, 0⟩]
/-- Vat 0 pays eleven of its ten. -/
def overdraftRaw : List LocalTurn :=
  [⟨0, .empty, .empty, 10, -11, -1, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 11, 21, 0, 0, 0⟩]

def stepSealed (raw : List LocalTurn) : Option LedgerState :=
  stepJoint 2 ledger0 (sealTurn raw).1 (sealTurn raw).2

-- The honest neighbour of each exploit is applied; the exploit is refused, by the check it breaks.
#guard ((stepSealed [⟨0, .empty, .empty, 10, -2, 8, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 2, 12, 0, 0, 0⟩]).map fun s =>
  (s.balances 0, s.balances 1)) == some (8, 12)
#guard (stepSealed dupVatRaw).isNone
#guard !vatsDistinct (sealTurn dupVatRaw).2
#guard (stepSealed unboundPreRaw).isNone
#guard checkJoint (sealTurn unboundPreRaw).1 (sealTurn unboundPreRaw).2
#guard !stepOk 2 ledger0 (sealTurn unboundPreRaw).1 (sealTurn unboundPreRaw).2
#guard (stepSealed overdraftRaw).isNone
#guard !(sealTurn overdraftRaw).2.all (·.valid)

-- The digests read `pre`, `post` and the turn: none can be restated under the same digest.
#guard turnDigest [⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩] != turnDigest [⟨0, .empty, .empty, 11, -1, 9, 0, 0, 0⟩]
#guard turnDigest [⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩] != turnDigest [⟨0, .empty, .empty, 10, -1, 8, 0, 0, 0⟩]
#guard coReceiptDigest ⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩ != coReceiptDigest ⟨0, .empty, .empty, 11, -1, 9, 0, 0, 0⟩
#guard coReceiptDigest ⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩ != coReceiptDigest ⟨0, .empty, .empty, 10, -1, 8, 0, 0, 0⟩
#guard coReceiptDigest ⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩ != coReceiptDigest ⟨0, tailA, .empty, 10, -1, 9, 0, 0, 0⟩
#guard (coReceiptDigest ⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩).size == 32

-- The three refusals, for every digest and every ledger.
example (n : Nat) (s : LedgerState) (shared : ByteArray) (a b : LocalTurn) (h : a.vat = b.vat) :
    stepJoint n s shared [a, b] = none :=
  duplicate_vat_refused n s shared [a, b] (by simp [h])

example (shared : ByteArray) (legs : List LocalTurn) (t : LocalTurn) (ht : t ∈ legs)
    (hv : t.vat = 0) (hp : t.pre ≠ 10) : stepJoint 2 ledger0 shared legs = none := by
  have h10 : ledger0.balances 0 = 10 := by decide
  exact unbound_pre_refused 2 ledger0 shared legs t ht (by rw [hv, h10]; exact hp)

example (n : Nat) (s : LedgerState) (shared : ByteArray) (t u : LocalTurn) (h : t.post < 0) :
    stepJoint n s shared [t, u] = none :=
  overdraft_refused n s shared [t, u] t (by simp) h

/-- The demo turn is applied to `ledger0`, in the kernel: the guard holds and the step is complete. -/
theorem demo_step_applies : ∃ s', stepJoint 2 ledger0 demoShared legs0 = some s' := by
  have hj : checkJoint demoShared legs0 = true := by
    obtain ⟨c, hc, ho, hd, _⟩ := composeCoReceipts_closed_inhabited
    exact (checkJoint_iff _ _).2
      (composeCoReceipts_closed_sound demoEnv demoShared demoDiagram c hc ho hd).1
  have hnew : ledger0.seen.contains (turnKey demoShared) = false :=
    Bool.eq_false_iff.2 fun h => by
      simpa [ledger0, RevokedSet.empty] using (RevokedSet.contains_iff _ _).1 h
  have hpre : legs0.all
      (fun t => decide (t.vat < 2) && decide (t.pre = ledger0.balances t.vat)) = true := by decide
  have hdomain : legs0.all (fun t => decide (t.asset = ledger0.asset ∧ t.epoch = ledger0.epoch)) = true := by decide
  refine stepJoint_complete (s := ledger0) floorsHold_book0
    (by simp only [stepOk, hj, hnew, hpre, hdomain, Bool.not_false, Bool.and_self]) ?_
  intro t ht f hf
  simp only [legs0, demoDiagram, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with rfl | rfl
  · have hf' : some (0 : Int) = some f := hf
    cases hf'
    decide
  · have hf' : some (0 : Int) = some f := hf
    cases hf'
    decide

-- Every trace from `ledger0`: the total, the floors, the asset's sum, and no vat below zero.
example (trace : List (ByteArray × List LocalTurn)) (s : LedgerState)
    (h : runTrace 2 ledger0 trace = some s) :
    total (List.range 2) s.balances = 20 ∧ (∀ v, 0 ≤ s.balances v) ∧ FloorsHold s.book ∧
      s.book.assetSum 0 = 0 := by
  have hv := (runTrace_eq_some_iff 2 trace ledger0 s).1 h
  obtain ⟨hf, hsum, hnn⟩ := jointTrace_preserves_floors 2 trace ledger0 s floorsHold_book0 hv
  refine ⟨?_, hnn, hf, ?_⟩
  · rw [(jointTrace_conserves_total_balance 2 trace ledger0 s hv).1]
    decide
  · rw [hsum]
    decide

example (trace : List (ByteArray × List LocalTurn)) (s s' : LedgerState)
    (h : ValidJointTrace 2 s trace s') (v : VatId) (hv : 0 ≤ s.balances v) : 0 ≤ s'.balances v :=
  jointTrace_no_overdraft 2 trace s s' h v hv

-- Commitments instead of cleartext half-edges.
def cLeg (vat : VatId) (credit : Bool) (tid : ByteArray) : CommittedLeg :=
  ⟨vat, tid, credit, openingCommit ⟨5#256, 7#256⟩⟩
def cShared : ByteArray :=
  forestDigest ([cLeg 0 false .empty, cLeg 1 true .empty].map CommittedLeg.legBytes)

#guard checkJointCommitted cShared [cLeg 0 false cShared, cLeg 1 true cShared] [⟨5#256, 7#256⟩] [⟨5#256, 7#256⟩]
#guard !checkJointCommitted cShared [cLeg 0 false cShared, cLeg 1 false cShared] [⟨5#256, 7#256⟩] [⟨5#256, 7#256⟩]
#guard !checkJointCommitted cShared [cLeg 0 false cShared] [⟨5#256, 7#256⟩] [⟨5#256, 7#256⟩]

-- The two-vat diagram closes: vat 0 resolves the promise vat 1 awaits.
def closedPorts (c : Option Composite) : Option (Nat × Nat) :=
  c.map fun c => (c.openAwaits.length, c.dangling.length)

def payer : CoReceipt := ⟨demoLeg 0 (-1) demoShared, 0, [], [⟨5, .empty, demoGrant, #[]⟩]⟩
def payee (guard : DistPred) (need : UInt64) : CoReceipt :=
  ⟨demoLeg 1 1 demoShared, 1, [⟨5, .empty, guard, rootLineage demoGrant, need⟩], []⟩

#guard closedPorts (composeCoReceipts demoEnv demoShared demoDiagram) == some (0, 0)
#guard closedPorts (composeCoReceipts demoEnv demoShared [payer, payee .tt 1]) == some (0, 0)
-- Half a diagram composes and stays open: one dangling resolution, or one open hole.
#guard closedPorts (composeCoReceipts demoEnv demoShared [payer]) == some (0, 1)
#guard closedPorts (composeCoReceipts demoEnv demoShared [payee .tt 1]) == some (1, 0)
-- Two resolutions of one hole; two holes with one id.
#guard (composeCoReceipts demoEnv demoShared [payer, payer, payee .tt 1]).isNone
#guard (composeCoReceipts demoEnv demoShared [payer, payee .tt 1, payee .tt 1]).isNone
-- The resolver is not causally earlier; and a two-receipt cycle, whatever the ranks.
#guard (composeCoReceipts demoEnv demoShared
  [{ payer with rank := 1 }, payee .tt 1]).isNone
#guard (composeCoReceipts demoEnv demoShared
  [{ payer with awaits := [⟨6, .empty, .tt, rootLineage demoGrant, 1⟩] },
    { payee .tt 1 with fulfills := [⟨6, .empty, demoGrant, #[]⟩] }]).isNone
-- The guard: false, an undischarged claim, the same claim discharged.
#guard (composeCoReceipts demoEnv demoShared [payer, payee .ff 1]).isNone
#guard (composeCoReceipts demoEnv demoShared [payer, payee (.witnessed vkA) 1]).isNone
#guard closedPorts (composeCoReceipts { demoEnv with discharges := [vkA] } demoShared
  [payer, payee (.witnessed vkA) 1]) == some (0, 0)
-- Authority: a right the grant lacks; another root; a revoked lineage; a revoked channel.
#guard (composeCoReceipts demoEnv demoShared [payer, payee .tt 2]).isNone
#guard (composeCoReceipts demoEnv demoShared
  [{ payer with fulfills := [⟨5, .empty, { demoGrant with rights := 3 }, #[]⟩] },
    payee .tt 1]).isNone
#guard (composeCoReceipts
  { demoEnv with revoked := RevokedSet.empty.insert (credNul (rootLineage demoGrant)) } demoShared
  [payer, payee .tt 1]).isNone
#guard (composeCoReceipts
  { demoEnv with revoked := RevokedSet.empty.insert (chanNul demoGrant.channel) } demoShared
  [payer, payee .tt 1]).isNone
-- A payload commitment that differs; a closed diagram that does not conserve.
#guard (composeCoReceipts demoEnv demoShared
  [{ payer with fulfills := [⟨5, tailA, demoGrant, #[]⟩] }, payee .tt 1]).isNone
#guard (composeCoReceipts demoEnv demoShared
  [{ payer with turn := demoLeg 0 (-2) demoShared }, payee .tt 1]).isNone

example : ∃ j : JointTurn, j.legs = demoDiagram.map (·.turn) ∧ j.shared.tid = demoShared := by
  obtain ⟨c, hc, ho, hd, _⟩ := composeCoReceipts_closed_inhabited
  exact (composeCoReceipts_closed_sound demoEnv demoShared demoDiagram c hc ho hd).1

example (env : WireEnv) (shared : ByteArray) (a b : CoReceipt) (f g : FulfillPort)
    (w v : AwaitPort) (hf : f ∈ a.fulfills) (hw : w ∈ b.awaits) (hfw : f.port = w.port)
    (hg : g ∈ b.fulfills) (hv : v ∈ a.awaits) (hgv : g.port = v.port) :
    composeCoReceipts env shared [a, b] = none :=
  cyclic_wiring_refused env shared [a, b]
    ⟨a, .trans (.step (by simp) (by simp) ⟨f, hf, w, hw, hfw⟩)
      (.step (by simp) (by simp) ⟨g, hg, v, hv, hgv⟩)⟩

-- A later debit fails its configured floor after an earlier debit would have succeeded.
def threeBook : FloorBook := book0.applyRaw ⟨.issuerWell 0, .user 2, 0, 10⟩
def floorLedger : LedgerState :=
  ⟨{ threeBook with policies := [((.user 1, 0), .minReserve 10)] }, 0, RevokedSet.empty, 0⟩
def lateFailure := sealTurn
  [demoLeg 0 (-1) .empty, demoLeg 1 (-1) .empty, demoLeg 2 2 .empty]
#guard checkJoint lateFailure.1 lateFailure.2
#guard stepOk 3 floorLedger lateFailure.1 lateFailure.2
#guard (stepJoint 3 floorLedger lateFailure.1 lateFailure.2).isNone
#guard (applyJoint 3 floorLedger lateFailure.1 lateFailure.2).book == floorLedger.book
#guard !(applyJoint 3 floorLedger lateFailure.1 lateFailure.2).seen.contains (turnKey lateFailure.1)

-- Selective aborts publish no debit, clearing balance, or replay key.
def settlementAttempts : List (ByteArray × List CoReceipt) :=
  [(demoShared, [payer]), (demoShared, [payee .tt 1]),
   (demoShared, [payer, payee .ff 1]), (demoShared, demoDiagram),
   (demoShared, demoDiagram)]
#guard let s := runSettlements demoEnv 2 ledger0 settlementAttempts
  (s.balances 0, s.balances 1, s.book.balance (turnClearing demoShared) 0,
    s.book.assetSum 0) == (9, 11, 0, 0)
#guard let s := settleCoReceipts demoEnv 2 ledger0 demoShared [payer]
  (s.balances 0, s.balances 1, s.seen.contains (turnKey demoShared)) == (10, 10, false)
def otherAsset : LedgerState :=
  ⟨(book0.applyRaw ⟨.issuerWell 1, .user 0, 1, 10⟩).applyRaw ⟨.issuerWell 1, .user 1, 1, 10⟩,
    1, RevokedSet.empty, 0⟩
#guard legs0.all (fun t => decide (t.vat < 2) && decide (t.pre = otherAsset.balances t.vat))
#guard !stepOk 2 otherAsset demoShared legs0
#guard !stepOk 2 { ledger0 with epoch := 1 } demoShared legs0
#guard coReceiptDigest (demoLeg 0 (-1) demoShared) !=
  coReceiptDigest { demoLeg 0 (-1) demoShared with nonce := 1 }
#guard !checkJointCommitted cShared [cLeg 0 false cShared, cLeg 1 true cShared]
  [⟨6#256, 7#256⟩] [⟨6#256, 7#256⟩]
#guard !checkJointCommitted cShared [cLeg 0 false cShared, cLeg 1 true cShared]
  [⟨5#256, 8#256⟩] [⟨5#256, 7#256⟩]
example : FloorsHold (runSettlements demoEnv 2 ledger0 settlementAttempts).book ∧
    ∀ a, (runSettlements demoEnv 2 ledger0 settlementAttempts).book.assetSum a = book0.assetSum a :=
  runSettlements_preserves demoEnv 2 settlementAttempts ledger0 floorsHold_book0

#tooth Obend.Polis.JointCoReceipt.stepJoint_domain by mutation
  Obend.Polis.JointCoReceipt.stepOk := fun _ _ _ _ => true
#tooth Obend.Polis.JointCoReceipt.runSettlements_preserves by mutation
  Obend.Polis.JointCoReceipt.settleCoReceipts := fun _ _ s _ _ =>
    { s with book := s.book.applyRaw ⟨.user 0, .user 1, s.asset, 100⟩ }
#tooth Obend.Polis.JointCoReceipt.jointTurn_committed_conservation_sound by mutation
  Obend.Polis.JointCoReceipt.checkJointCommitted := fun _ _ _ _ => true

-- ============================================================================
-- 5. Teeth
-- ============================================================================

-- With no oracle a claim reads as refuted, so its negation is admitted.
#tooth Obend.Polis.PrivatePredicate.negated_witnessed_refused_firstParty by mutation
  Obend.Polis.PrivatePredicate.noOracle := fun _ => .false3

-- The residual keeps the vat's own atoms.
#tooth Obend.Polis.PrivatePredicate.DistPred.pevalVat_hides_known_slots by mutation
  Obend.Polis.PrivatePredicate.pevalAtom := fun _ s t => .atom s t

-- Every decided atom becomes "true".
#tooth Obend.Polis.PrivatePredicate.eval_subst_eq_eval_pevalVat by mutation
  Obend.Polis.PrivatePredicate.constP := fun _ => .all .nil

-- A commitment that forgets the value.
#tooth Obend.Polis.PrivatePredicate.private_conservation_iff_value_sum by mutation
  Obend.Polis.PrivatePredicate.commitVal := fun key _ blind => key.h * blind

-- A balance check that always passes.
#tooth Obend.Polis.PrivatePredicate.inflation_refused by mutation
  Obend.Polis.PrivatePredicate.homCheck := fun _ _ => true

-- An auditor that skips the `blindSum ins = blindSum outs` check (allowing unblinded forgery!).
#tooth Obend.Polis.PrivatePredicate.privPred_conservation_sound by mutation
  Obend.Polis.PrivatePredicate.auditTransfer := fun key ins outs claim =>
    decide (claim.g = key.g) && decide (claim.h = key.h) &&
    decide (claim.inCommits = ins.map (Opening.commit key)) &&
    decide (claim.outCommits = outs.map (Opening.commit key)) &&
    decide (claim.inBinds = ins.map Opening.bind) &&
    decide (claim.outBinds = outs.map Opening.bind) &&
    (ins ++ outs).all (fun op => decide (op.value.toNat < 2 ^ claim.bits))

-- A sealing ledger that fails to refuse reused nonces.
#tooth Obend.Polis.PrivatePredicate.SealLedger.reused_nonce_refused by mutation
  Obend.Polis.PrivatePredicate.SealLedger.sealFresh := fun st key nonce msg =>
    some (⟨nonce :: st.seenNonces⟩, aeadSeal key nonce msg)

-- A verifier that does not ask for the binding to the parent.
#tooth Obend.Polis.PrivatePredicate.unbound_or_wrong_parent_refused by mutation
  Obend.Polis.PrivatePredicate.verifyDischarge := fun cav d parentTail σ now maxAge =>
    match recoverKey cav parentTail with
    | none => false
    | some r => fresh d.createdAt now maxAge && chainValid d r && caveatsHold σ d

-- A verifier that does not check freshness.
#tooth Obend.Polis.PrivatePredicate.staleDischarge_refused by mutation
  Obend.Polis.PrivatePredicate.verifyDischarge := fun cav d parentTail σ _ _ =>
    match recoverKey cav parentTail with
    | none => false
    | some r => chainValid d r && boundTo d parentTail && caveatsHold σ d

-- A joint checker without the half-edge sum.
#tooth Obend.Polis.JointCoReceipt.jointTurn_sound by mutation
  Obend.Polis.JointCoReceipt.checkJoint := fun shared legs =>
    legs.all (·.valid) && legs.all (fun t => decide (t.turnId = shared)) &&
      decide (shared = turnDigest legs)

-- A joint checker without the shared turn id.
#tooth Obend.Polis.JointCoReceipt.checkJoint_iff by mutation
  Obend.Polis.JointCoReceipt.checkJoint := fun shared legs =>
    legs.all (·.valid) && decide (shared = turnDigest legs) &&
      decide ((legs.map (·.half)).sum = 0)

-- A ledger that applies a turn it has already seen.
#tooth Obend.Polis.JointCoReceipt.jointTrace_no_replay by mutation
  Obend.Polis.JointCoReceipt.stepOk := fun n s shared legs =>
    checkJoint shared legs &&
      legs.all (fun t => decide (t.vat < n) && decide (t.pre = s.balances t.vat))

-- A joint checker that lets one vat sign twice.
#tooth Obend.Polis.JointCoReceipt.duplicate_vat_refused by mutation
  Obend.Polis.JointCoReceipt.vatsDistinct := fun _ => true

-- With one vat signing twice the ledger's total is not conserved.
#tooth Obend.Polis.JointCoReceipt.jointTrace_conserves_total_balance by mutation
  Obend.Polis.JointCoReceipt.vatsDistinct := fun _ => true

-- A step that takes a receipt's word for the balance before.
#tooth Obend.Polis.JointCoReceipt.unbound_pre_refused by mutation
  Obend.Polis.JointCoReceipt.stepOk := fun n s shared legs =>
    checkJoint shared legs && !s.seen.contains (turnKey shared) &&
      legs.all (fun t => decide (t.vat < n))

-- A receipt allowed to end below zero.
#tooth Obend.Polis.JointCoReceipt.overdraft_refused by mutation
  Obend.Polis.JointCoReceipt.LocalTurn.valid := fun t =>
    decide (t.post = t.pre + t.half) && decide (0 ≤ t.pre)

-- The same receipt, across a trace.
#tooth Obend.Polis.JointCoReceipt.jointTrace_no_overdraft by mutation
  Obend.Polis.JointCoReceipt.LocalTurn.valid := fun t =>
    decide (t.post = t.pre + t.half) && decide (0 ≤ t.pre)

-- A receipt digest that forgets which turn the receipt belongs to.
#tooth Obend.Polis.JointCoReceipt.coReceiptDigest_binds by mutation
  Obend.Polis.JointCoReceipt.LocalTurn.receiptBytes := fun t => encodeFields [t.legBytes]

-- Port tables that are never checked for a repeated id.
#tooth Obend.Polis.JointCoReceipt.promise_hole_no_double_fill by mutation
  Obend.Polis.JointCoReceipt.tableOk := fun _ _ => true

-- A wire that does not compare causal ranks.
#tooth Obend.Polis.JointCoReceipt.cyclic_wiring_refused by mutation
  Obend.Polis.JointCoReceipt.wireOk := fun env w f =>
    decide (f.fill.payload = w.hole.payload) &&
      admits (dischargeOracle env.discharges) env.step w.hole.guard && capOk env w.hole f.fill

-- A wire that checks the root but never folds the chain.
#tooth Obend.Polis.JointCoReceipt.revoked_lineage_refused by mutation
  Obend.Polis.JointCoReceipt.capOk := fun _ w f => decide (rootLineage f.root = w.resolverRoot)

-- A diagram accepted closed without being a joint turn.
#tooth Obend.Polis.JointCoReceipt.composeCoReceipts_closed_sound by mutation
  Obend.Polis.JointCoReceipt.closureOk := fun _ _ => true

#print axioms Obend.Polis.PrivatePredicate.opaque_closure_collapses_finite_encoding
#print axioms Obend.Polis.PrivatePredicate.opaque_closure_escapes_descriptor_table
#print axioms Obend.Polis.PrivatePredicate.DistPred.encode_injective
#print axioms Obend.Polis.PrivatePredicate.eval_subst_eq_eval_pevalVat
#print axioms Obend.Polis.PrivatePredicate.private_conservation_iff_value_sum
#print axioms Obend.Polis.PrivatePredicate.privPred_conservation_extract
#print axioms Obend.Polis.PrivatePredicate.privPred_conservation_sound
#print axioms Obend.Polis.PrivatePredicate.verifyDischarge_iff
#print axioms Obend.Polis.PrivatePredicate.unbound_or_wrong_parent_refused
#print axioms Obend.Polis.JointCoReceipt.tensor_not_final
#print axioms Obend.Polis.JointCoReceipt.coReceiptDigest_binds
#print axioms Obend.Polis.JointCoReceipt.stepJoint_refines_floorBook
#print axioms Obend.Polis.JointCoReceipt.stepJoint_complete
#print axioms Obend.Polis.JointCoReceipt.jointTrace_conserves_total_balance
#print axioms Obend.Polis.JointCoReceipt.jointTrace_no_overdraft
#print axioms Obend.Polis.JointCoReceipt.jointTrace_preserves_floors
#print axioms Obend.Polis.JointCoReceipt.composeCoReceipts_closed_sound

#assert_axioms_tree

end Obend.Tests.Metasystem.DistributedPredicatesAndCoReceiptTest
end
