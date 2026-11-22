import Obend.Ledger.Floors
import Obend.Ledger.Seat
import Obend.Ledger.Vault
import Obend.Run.Durable
import Obend.Teeth.RunExamplesTeeth
import Obend.Run.Shared
import Obend.Run.Fork
import Obend.Slot.Selection
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/DurableHostAndZoeSeatTest.lean` — Metasystem Regression & Verification Suite

Exercises:
1. Typed-Account Finite-Support Resource Kernel (`Obend.Ledger.Floors`):
   - `AccountKind` (`user | issuerWell | seat | escrow | feePool`), `AccountAddr`, `FloorBook`,
   - `admitBatch_preserves_floors`, `realizeBatchOnReg_sound` (`Register.Reg` + `Movement` simulation).
2. Full ZoE Offer Safety (`Obend.Ledger.Seat`):
   - One-time `Invitation` spending (`InvitationRegistry.no_double_redeem`),
   - Explicit `donate` zero-want gift guard (`donationUnmarked_refused`, `admitOffer_donationUnmarked_refused`),
   - Identity-blind `SeatView` (`seatView_identity_blind`),
   - Full-balance-support `exitSeat` sweep (`exit_sweeps_all_assets`),
   - Multi-seat atomic `BatchRealloc` (`checkBatchReallocSafe`, `batchRealloc_preserves_all_seats_offer_safe`,
     `batchRealloc_zero_sum_all_assets`, `batchRealloc_disjoint_from_ordinary_accounts`).
3. Idempotent Multi-Crash Recovery & Outbox Linearizability (`Obend.Run.Durable`) and
   Cost-Ordered Selection Policy (`Obend.Slot.Selection`).
-/

namespace Obend.Tests.DurableHostAndZoeSeatTest

open Obend.Ledger
open Obend.Slot
open Obend.Slot.World
open Obend.Slot.Protocol
open Obend.Slot.Protocol.Negotiation
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable
open Obend.Run.SharedExample
open Obend.Run.DurableExample
open Obend.Run.Negotiation (Wv host O₀ ctl au stored₀ NCand commitOp)

-- ============================================================================
-- 1. Typed-Account Finite-Support `FloorBook` & `Register.Reg` Bridge
-- ============================================================================

def assetUsdc : AssetId := 1
def assetEth  : AssetId := 2
def assetBtc  : AssetId := 3
def assetBonus : AssetId := 99

def issuerAddr : AccountAddr := AccountAddr.issuerWell assetUsdc
def aliceAddr  : AccountAddr := ⟨.user, 100⟩
def bobAddr    : AccountAddr := ⟨.user, 200⟩

def mintAndTransferBatch : List TypedPosting :=
  [ { source := issuerAddr, destination := aliceAddr, asset := assetUsdc, amount := 500 }
  , { source := aliceAddr,  destination := bobAddr,   asset := assetUsdc, amount := 125 } ]

def overdraftBatch : List TypedPosting :=
  [ { source := aliceAddr, destination := bobAddr, asset := assetUsdc, amount := 10 } ]

#guard (FloorBook.empty.admitBatch mintAndTransferBatch).isSome == true
#guard (FloorBook.empty.admitBatch overdraftBatch).isNone == true

theorem test_overdraft_refused :
    (FloorBook.empty.admitBatch overdraftBatch).isSome = false := rfl

#tooth test_overdraft_refused by mutation
  FloorBook.admitPosting := fun fb p => some (fb.applyRaw p)

example (fb' : FloorBook) (g' : Reg)
    (hrun : realizeBatchOnReg
      (mintAndTransferBatch.map (fun p => (p, "mint-xfer", "test")))
      FloorBook.empty ({ postings := [] } : Reg) = some (fb', g')) :
    (∀ (addr : AccountAddr) (ast : AssetId),
      g'.accountBalance (addr.toRegAccount ast) = fb'.balance addr ast) ∧
    FloorsHold fb' ∧
    (∀ (addr : AccountAddr) (ast : AssetId), addr.kind ≠ AccountKind.issuerWell →
      addr.kind ≠ AccountKind.member → 0 ≤ g'.accountBalance (addr.toRegAccount ast)) ∧
    (∀ ast, fb'.assetSum ast = FloorBook.empty.assetSum ast) :=
  realizeBatchOnReg_sound floorsHold_empty (fun _ _ => rfl) hrun

-- ============================================================================
-- 2. Full ZoE Offer Safety (`InvitationRegistry`, `donate`, `SeatView`, `exitSeat`, `BatchRealloc`)
-- ============================================================================

def ordinaryAlice : AccountId := 100
def ordinaryBob   : AccountId := 200

def seat1Acc : AccountId := protectedBase + 1
def seat2Acc : AccountId := protectedBase + 2
def seat3Acc : AccountId := protectedBase + 3

-- One-time invitation spending (`no_double_redeem`) & `donate` guard:
def mintedRegPair : InvitationRegistry × Invitation :=
  InvitationRegistry.empty.mint 7 "drex-swap-seat"

#guard (mintedRegPair.1.spend mintedRegPair.2.id).isSome == true
#guard (match mintedRegPair.1.spend mintedRegPair.2.id with
        | some (regAfter, _) => (regAfter.spend mintedRegPair.2.id).isNone
        | none => false) == true

def unmarkedGiftProposal : Proposal :=
  { give := [(assetUsdc, 50)], want := [], exit := .onDemand, donate := false }

def markedGiftProposal : Proposal :=
  { give := [(assetUsdc, 50)], want := [], exit := .onDemand, donate := true }

#guard (match checkDonationGuard unmarkedGiftProposal with | .error .donationUnmarked => true | _ => false)
#guard (match checkDonationGuard markedGiftProposal with | .ok () => true | _ => false)

-- Seat 1 gives 100 USDC, wants 10 ETH
def seat1 : Seat :=
  { account := seat1Acc
  , offerer := ordinaryAlice
  , payee := ordinaryAlice
  , proposal :=
      { give := [(assetUsdc, 100)]
      , want := [(assetEth, 10)]
      , exit := .onDemand
      , donate := false } }

-- Seat 1 renamed participant identities (`offerer := 999, payee := 888`) with default `disclose = {}`
def seat1Renamed : Seat :=
  { account := seat1Acc
  , offerer := 999
  , payee := 888
  , proposal := seat1.proposal }

-- Identity-blind `SeatView` check:
#guard seat1.view == seat1Renamed.view

example : seat1.view = seat1Renamed.view :=
  seatView_identity_blind seat1 seat1Renamed rfl rfl rfl rfl

-- Seat 2 gives 10 ETH, wants 2 BTC
def seat2 : Seat :=
  { account := seat2Acc
  , payee := ordinaryBob
  , proposal :=
      { give := [(assetEth, 10)]
      , want := [(assetBtc, 2)]
      , exit := .onDemand
      , donate := false } }

-- Seat 3 gives 2 BTC, wants 100 USDC
def seat3 : Seat :=
  { account := seat3Acc
  , payee := 300
  , proposal :=
      { give := [(assetBtc, 2)]
      , want := [(assetUsdc, 100)]
      , exit := .onDemand
      , donate := false } }

def activeSeats : List Seat := [seat1, seat2, seat3]

def initialEscrowBook : Book :=
  ((((({ Book.empty with accounts := [ordinaryAlice, ordinaryBob, 300, seat1Acc, seat2Acc, seat3Acc] }
      ).setBalance ordinaryAlice assetUsdc 500
      ).setBalance ordinaryBob assetEth 50
      ).setBalance seat1Acc assetUsdc 100
      ).setBalance seat1Acc assetBonus 7
      ).setBalance seat2Acc assetEth 10
      |>.setBalance seat3Acc assetBtc 2

-- Full-balance-support `exitSeat` sweep: sweeps BOTH `assetUsdc` (100) AND unsolicited `assetBonus` (7)!
def exitedBook1 : Book := exitSeat initialEscrowBook seat1

#guard exitedBook1.balance seat1Acc assetUsdc == 0
#guard exitedBook1.balance seat1Acc assetBonus == 0
#guard exitedBook1.balance ordinaryAlice assetUsdc == 600
#guard exitedBook1.balance ordinaryAlice assetBonus == 7

-- Valid 3-way circular ZoE swap satisfying every seat's `want` with zero-sum conservation
def valid3WaySwap : BatchRealloc :=
  { postings :=
      [ ⟨seat1Acc, seat3Acc, assetUsdc, 100⟩
      , ⟨seat2Acc, seat1Acc, assetEth, 10⟩
      , ⟨seat3Acc, seat2Acc, assetBtc, 2⟩ ] }

-- Invalid swap that violates Seat 1's offer safety (takes 100 USDC from Seat 1 but gives only 5 ETH < 10 ETH want)
def unsafeSwap : BatchRealloc :=
  { postings :=
      [ ⟨seat1Acc, seat3Acc, assetUsdc, 100⟩
      , ⟨seat2Acc, seat1Acc, assetEth, 5⟩
      , ⟨seat3Acc, seat2Acc, assetBtc, 2⟩ ] }

-- Invalid swap that touches an ordinary account (`ordinaryAlice < protectedBase`)
def unauthorizedOrdinaryTouchSwap : BatchRealloc :=
  { postings :=
      [ ⟨ordinaryAlice, seat1Acc, assetUsdc, 100⟩ ] }

def duplicateSeats : List Seat := [seat1, seat1, seat2, seat3]

#guard checkBatchReallocSafe initialEscrowBook activeSeats valid3WaySwap == true
#guard checkBatchReallocSafe initialEscrowBook activeSeats unsafeSwap == false
#guard checkBatchReallocSafe initialEscrowBook activeSeats unauthorizedOrdinaryTouchSwap == false
#guard checkBatchReallocSafe initialEscrowBook duplicateSeats valid3WaySwap == false

theorem test_unsafe_swap_rejected :
    checkBatchReallocSafe initialEscrowBook activeSeats unsafeSwap = false := rfl

#tooth test_unsafe_swap_rejected by mutation
  checkBatchReallocSafe := fun _ _ _ => true

example : (activeSeats.map Seat.account).Nodup :=
  batchRealloc_nodup_seats initialEscrowBook activeSeats valid3WaySwap rfl

example :
    ∀ s ∈ activeSeats,
      safeAt (applyBatchRealloc initialEscrowBook valid3WaySwap) s.account s.proposal = true :=
  batchRealloc_preserves_all_seats_offer_safe initialEscrowBook activeSeats valid3WaySwap rfl

example (ast : AssetId) :
    batchTotalCredits activeSeats valid3WaySwap ast = batchTotalDebits activeSeats valid3WaySwap ast :=
  batchRealloc_zero_sum_all_assets initialEscrowBook activeSeats valid3WaySwap rfl ast

example (ast : AssetId) :
    (applyBatchRealloc initialEscrowBook valid3WaySwap).balance ordinaryAlice ast =
      initialEscrowBook.balance ordinaryAlice ast :=
  batchRealloc_disjoint_from_ordinary_accounts
    initialEscrowBook activeSeats valid3WaySwap rfl ordinaryAlice (by decide) ast

#guard (applyBatchRealloc initialEscrowBook valid3WaySwap).balance ordinaryAlice assetUsdc == 500
#guard (applyBatchRealloc initialEscrowBook valid3WaySwap).balance ordinaryBob assetEth == 50

-- ============================================================================
-- 3. Idempotent Multi-Crash Recovery & Outbox Linearizability (`Run/Durable`)
-- ============================================================================

abbrev HostSt := DState nledger sig HoleN Res Unit Unit NCand Negotiation.Fact Ob .idle

def initHostState : HostSt := DState.init nledger J₀

def preCrashEvents : List HEv :=
  submitAll (reserve .alice ++ reserve .bob) ++
    [.submit (.dispatch .alice (commitOp .p1))]

def stateBeforeExpose : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ initHostState preCrashEvents

#guard pending nledger stateBeforeExpose == [0, 2, 4]
#guard stateBeforeExpose.outbox == []

def stateAfterExpose : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateBeforeExpose [.expose 4]

#guard pending nledger stateAfterExpose == [0, 2]
#guard stateAfterExpose.outbox == [4]
#guard (pending nledger stateAfterExpose).length < (pending nledger stateBeforeExpose).length

example (s' : HostSt)
    (h : hstep nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateBeforeExpose (.expose 4) = .ok s') :
    s'.journal = stateBeforeExpose.journal ∧
    s'.mem = stateBeforeExpose.mem ∧
    s'.outbox = stateBeforeExpose.outbox ++ [4] ∧
    4 ∈ pending nledger stateBeforeExpose ∧
    4 ∉ pending nledger s' ∧
    pending nledger s' = (pending nledger stateBeforeExpose).filter (fun m => m != 4) ∧
    (pending nledger s').length < (pending nledger stateBeforeExpose).length :=
  pending_decreases_on_expose nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateBeforeExpose s' 4 h

example (s : HostSt) (crashes : Nat) (hc : 1 ≤ crashes) :
    let trace : List HEv := List.replicate crashes .crash ++ [.recover]
    let single : List HEv := [.crash, .recover]
    runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s trace =
      runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s single ∧
    (runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s trace).journal = s.journal ∧
    (runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s trace).outbox = s.outbox :=
  crash_recover_idempotent nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s crashes hc

def stateAfter1CrashRecover : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateAfterExpose [.crash, .recover]

def stateAfter5CrashesRecover : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateAfterExpose
    (List.replicate 5 .crash ++ [.recover])

#guard stateAfter5CrashesRecover.outbox == stateAfter1CrashRecover.outbox
#guard pending nledger stateAfter5CrashesRecover == pending nledger stateAfter1CrashRecover
#guard stateAfter5CrashesRecover.mem.isSome == true

-- ============================================================================
-- 4. Cost-Ordered / Priority-Monotone Selection Policy (`Slot/Selection`)
-- ============================================================================

def memberCost : Member → Nat
  | .alice => 50
  | .bob   => 10

def testOrder : List Member := [.alice, .bob]

example : prioritySelect toySlot (holdsAt (V := Nat) 0) testOrder memberCost = .ok .bob := rfl
#guard match prioritySelect toySlot (holdsAt (V := Nat) 0) testOrder memberCost with | .ok .bob => true | _ => false

example : (priorityAdvance memberCost).advance toySlot 0 testOrder (some .alice) = .ok .bob := rfl
#guard match (priorityAdvance memberCost).advance toySlot 0 testOrder (some .alice) with | .ok .bob => true | _ => false

example : SelectionSound (priorityAdvance : Advance Nat Member Member) :=
  priorityAdvance_sound

example : SelectionSound (priorityAdvance memberCost : Advance Nat Member Member) :=
  priorityAdvance_sound

example (c : Member)
    (h : (priorityAdvance memberCost).advance toySlot 0 testOrder (some .alice) = .ok c) :
    memberCost c ≤ memberCost .alice :=
  priorityAdvance_monotone toySlot 0 testOrder .alice c rfl h

-- ============================================================================
-- 5. Axiom Audit (`0 sorryAx`)
-- ============================================================================

#print axioms FloorBook.admitBatch_preserves_floors
#print axioms realizeBatchOnReg_sound
#print axioms InvitationRegistry.no_double_redeem
#print axioms donationUnmarked_refused
#print axioms admitOffer_donationUnmarked_refused
#print axioms seatView_identity_blind
#print axioms exit_sweeps_all_assets
#print axioms batchRealloc_nodup_seats
#print axioms batchRealloc_preserves_all_seats_offer_safe
#print axioms batchRealloc_zero_sum_conservation
#print axioms batchRealloc_zero_sum_all_assets
#print axioms batchRealloc_disjoint_from_ordinary_accounts
#print axioms batchRealloc_conserves
#print axioms crash_recover_idempotent
#print axioms pending_decreases_on_expose
#print axioms prioritySelect_ok
#print axioms priorityAdvance_sound
#print axioms priorityAdvance_monotone

end Obend.Tests.DurableHostAndZoeSeatTest
