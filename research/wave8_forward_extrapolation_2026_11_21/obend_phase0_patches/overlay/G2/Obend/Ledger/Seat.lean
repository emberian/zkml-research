module
/-
# Obend.Ledger.Seat — Full ZoE Offer Safety, One-Time Invitations, Gift Guard, Identity-Blind Disclosure & Full-Support Exit Sweep

Mathlib-free port of `minidregg/Kernel/Invitation.lean` and `minidregg/Kernel/Seat.lean` over
the finite-support `Obend.Ledger.Book` resource kernel:

1. **One-Time `Invitation` Spending (`no_double_redeem`)**:
   - `InvitationRegistry` mints fresh `Invitation`s and redeems each invitation at most once
     (`no_double_redeem`, `mint_preserves_spent`).
2. **Explicit `donate : Bool` Zero-Want Gift Guard (`donationUnmarked`)**:
   - `admitOffer` refuses zero-want proposals unless `p.donate = true` (`donationUnmarked_refused`)
     and refuses `p.donate = true` when `want` is positive (`donationMarkedWithWant`), preventing
     accidental asset gifts caused by omitted `want` clauses.
3. **`Disclosure` Identity-Blind Contract View (`seatView_identity_blind`)**:
   - `Seat.view` hides `offerer`, `payee`, and `holder` identities behind `s.proposal.disclose`,
     making contract matching bit-identical across participant renamings when undisclosed.
4. **Full-Balance-Support Exit Sweep (`exitSeat`, `exit_sweeps_all_assets`)**:
   - Reads the finite support `b.heldAssets s.account` directly from `Book`'s `FinMap`, sweeping
     every asset held by the seat (including unsolicited/bonus assets outside `give` and `want`)
     to `s.payee`, leaving `0` on the seat for ALL `ast : AssetId` while conserving supply.
-/
public import Obend.Ledger.Book

public import Obend.Logic.SeparationFrame
public import Obend.Polis.CapTP
public import Obend.Consensus.SimplexProtocol
public import Obend.Digest.Cshake256.Spec
import all Obend.Polis.CapTP

public section
namespace Obend.Ledger

set_option autoImplicit false

/-! ## 1. One-Time Invitations (`no_double_redeem`) -/

/-- A linear ZoE contract invitation token bound to `instanceId` and `description`. -/
structure Invitation where
  id          : Nat
  instanceId  : Nat
  description : String
  deriving DecidableEq, Repr

/-- Registry of live unspent invitations with strictly monotone `nextId` allocator. -/
structure InvitationRegistry where
  nextId : Nat := 0
  live   : List (Nat × Invitation) := []
  deriving DecidableEq, Repr

namespace InvitationRegistry

def empty : InvitationRegistry := {}

def isLive (reg : InvitationRegistry) (invId : Nat) : Bool :=
  (reg.live.lookup invId).isSome

/-- Mint a fresh invitation with `id = reg.nextId`. -/
def mint (reg : InvitationRegistry) (instanceId : Nat) (description : String) :
    InvitationRegistry × Invitation :=
  let inv : Invitation := ⟨reg.nextId, instanceId, description⟩
  ({ nextId := reg.nextId + 1, live := (reg.nextId, inv) :: reg.live }, inv)

/-- Remove all entries keyed by `invId` from an association list. -/
def eraseAllKey (invId : Nat) : List (Nat × Invitation) → List (Nat × Invitation)
  | [] => []
  | (k, v) :: rest =>
    if k == invId then eraseAllKey invId rest
    else (k, v) :: eraseAllKey invId rest

theorem lookup_eraseAllKey_self (invId : Nat) :
    ∀ (xs : List (Nat × Invitation)), (eraseAllKey invId xs).lookup invId = none
  | [] => rfl
  | (k, v) :: rest => by
    unfold eraseAllKey
    by_cases hk : k == invId
    · simp only [hk, ↓reduceIte]
      exact lookup_eraseAllKey_self invId rest
    · have hk' : (invId == k) = false := by
        cases h : invId == k with
        | false => rfl
        | true =>
          have heq : invId = k := beq_iff_eq.mp h
          subst heq
          exact absurd (beq_self_eq_true invId) hk
      simp only [hk, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, hk']
      exact lookup_eraseAllKey_self invId rest

/-- Spend (redeem) an invitation once, removing it from `live`. -/
def spend (reg : InvitationRegistry) (invId : Nat) : Option (InvitationRegistry × Invitation) :=
  match reg.live.lookup invId with
  | some inv => some ({ reg with live := eraseAllKey invId reg.live }, inv)
  | none     => none

/-- **One-Time Invitation Redemption (`no_double_redeem`)**:
    Once `reg.spend invId = some (reg', inv)`, any second attempt `reg'.spend invId` returns `none`. -/
theorem no_double_redeem {reg reg' : InvitationRegistry} {inv : Invitation} {invId : Nat}
    (hspend : reg.spend invId = some (reg', inv)) :
    reg'.spend invId = none := by
  unfold spend at hspend ⊢
  cases hlook : reg.live.lookup invId with
  | none => rw [hlook] at hspend; cases hspend
  | some found =>
    rw [hlook] at hspend
    injection hspend with hp
    have hreg : reg' = { reg with live := eraseAllKey invId reg.live } :=
      (Prod.mk.inj hp).1.symm
    subst hreg
    simp [lookup_eraseAllKey_self]

/-- Minting new invitations at `reg.nextId` never resurrects a previously spent `invId < reg.nextId`. -/
theorem mint_preserves_spent (reg : InvitationRegistry) (inst : Nat) (desc : String)
    {invId : Nat} (hlt : invId < reg.nextId) (hspent : reg.spend invId = none) :
    (reg.mint inst desc).1.spend invId = none := by
  unfold spend at hspent ⊢
  unfold mint
  have hne : (invId == reg.nextId) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
  simp only [List.lookup_cons, hne]
  cases hlook : reg.live.lookup invId with
  | none => rfl
  | some _ => rw [hlook] at hspent; cases hspent

end InvitationRegistry

/-- Linear adjacent-key validation; unsorted and duplicate inputs retain first-match semantics. -/
def strictKeys {α : Type} (key : α → Nat) : List α → Bool
  | [] | [_] => true
  | a :: b :: rest => decide (key a < key b) && strictKeys key (b :: rest)

theorem strictKeys_pairwise {α : Type} (key : α → Nat) :
    ∀ xs, strictKeys key xs = true → xs.Pairwise (fun a b => key a < key b)
  | [], _ => .nil
  | [a], _ => by simp
  | a :: b :: rest, h => by
    simp only [strictKeys, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictKeys_pairwise key (b :: rest) h.2
    rw [List.pairwise_cons] at ih ⊢
    refine ⟨?_, List.pairwise_cons.mpr ih⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (ih.1 x hx)

theorem strictKeys_sorted {α : Type} (key : α → Nat) (xs : List α)
    (h : strictKeys key xs = true) : Obend.Polis.CapTP.SortedBy key xs.toArray := by
  intro i j hi hj hij
  simpa using (List.pairwise_iff_getElem.mp (strictKeys_pairwise key xs h)
    i j (by simpa using hi) (by simpa using hj) hij)

/-- Invitations use the same verified binary-search implementation. -/
structure InvitationTableExec where
  entries : Array (Nat × Invitation)
  sorted : Obend.Polis.CapTP.SortedBy Prod.fst entries

def InvitationTableExec.ofInvitations (invitations : List (Nat × Invitation)) :
    Option InvitationTableExec :=
  if h : strictKeys Prod.fst invitations = true then
    some ⟨invitations.toArray, strictKeys_sorted _ _ h⟩
  else none

def lookupInvitationExec (table : InvitationTableExec) (id : Nat) : Option Invitation :=
  (Obend.Polis.CapTP.search Prod.fst table.entries id
    (table.entries.size + 1) 0 table.entries.size).map Prod.snd

theorem lookupInvitationExec_eq_spec (table : InvitationTableExec) (id : Nat) :
    lookupInvitationExec table id =
      (table.entries.toList.find? (fun p => p.1 == id)).map Prod.snd := by
  unfold lookupInvitationExec
  rw [Obend.Polis.CapTP.search_eq_spec _ _ table.sorted]
  rfl

def lookupInvitationsExec (invitations : List (Nat × Invitation)) (id : Nat) : Option Invitation :=
  match InvitationTableExec.ofInvitations invitations with
  | some table => lookupInvitationExec table id
  | none => invitations.lookup id

theorem lookupInvitationsExec_eq_spec (xs : List (Nat × Invitation)) (id : Nat) :
    lookupInvitationsExec xs id = xs.lookup id := by
  unfold lookupInvitationsExec InvitationTableExec.ofInvitations
  by_cases hsorted : strictKeys Prod.fst xs = true
  · simp only [hsorted, dite_true, lookupInvitationExec_eq_spec, List.toList_toArray]
    clear hsorted
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      obtain ⟨k, v⟩ := x
      simp only [List.find?_cons, List.lookup_cons]
      by_cases h : k = id
      · simp [h]
      · simpa only [Prod.fst, beq_eq_false_iff_ne.mpr h,
          beq_eq_false_iff_ne.mpr (Ne.symm h), Bool.false_eq_true, ite_false] using ih
  · simp [hsorted]

def InvitationRegistry.spendExec (reg : InvitationRegistry) (invId : Nat) :
    Option (InvitationRegistry × Invitation) :=
  match lookupInvitationsExec reg.live invId with
  | some inv => some ({ reg with live := InvitationRegistry.eraseAllKey invId reg.live }, inv)
  | none => none

@[csimp] theorem InvitationRegistry.spend_eq_exec :
    @InvitationRegistry.spend = @InvitationRegistry.spendExec := by
  funext reg invId
  simp [InvitationRegistry.spend, InvitationRegistry.spendExec, lookupInvitationsExec_eq_spec]

/-! ## 2. Proposals, Explicit `donate` Gift Guard & `Disclosure` -/

inductive ExitRule where
  | onDemand
  | afterDeadline (due : Nat)
  deriving DecidableEq, Repr

/-- Per-role disclosure policy controlling whether contract code can inspect identities. -/
structure Disclosure where
  offerer : Bool := false
  payee   : Bool := false
  holder  : Bool := false
  deriving DecidableEq, Repr

structure Proposal where
  give     : List (AssetId × Nat)
  want     : List (AssetId × Nat)
  exit     : ExitRule
  donate   : Bool := false
  disclose : Disclosure := {}
  deriving DecidableEq, Repr

def Proposal.assets (p : Proposal) : List AssetId :=
  ((p.give ++ p.want).map Prod.fst).eraseDups

/-- True iff `p.want` requests zero positive units of every asset. -/
def Proposal.wantsNothing (p : Proposal) : Bool :=
  p.want.all (fun (_, amt) => amt == 0)

/-- Check that `p.give` and `p.want` each have duplicate-free asset keys. -/
def Proposal.assetsNodupB (p : Proposal) : Bool :=
  decide ((p.give.map Prod.fst).Nodup ∧ (p.want.map Prod.fst).Nodup)

/-- Total amount requested or offered for `ast` across all entries in `pairs`. -/
def assetAmountSum (pairs : List (AssetId × Nat)) (ast : AssetId) : Nat :=
  ((pairs.filter (fun (a, _) => a == ast)).map Prod.snd).sum

/-- Offer safety: either every `want` is met, or every `give` is refunded,
    with per-asset amounts summed across any duplicate keys. -/
def safeAt (b : Book) (account : AccountId) (p : Proposal) : Bool :=
  let wantMet :=
    p.want.all fun (ast, amt) =>
      decide ((amt : Int) ≤ b.balance account ast) &&
      decide ((assetAmountSum p.want ast : Int) ≤ b.balance account ast)
  let giveRefunded :=
    p.give.all fun (ast, amt) =>
      decide ((amt : Int) ≤ b.balance account ast) &&
      decide ((assetAmountSum p.give ast : Int) ≤ b.balance account ast)
  wantMet || giveRefunded

theorem atLeast_mono {b b' : Book} {account account' : AccountId}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (pairs fullPairs : List (AssetId × Nat))
    (hall : pairs.all (fun (ast, amt) =>
      decide ((amt : Int) ≤ b.balance account ast) &&
      decide ((assetAmountSum fullPairs ast : Int) ≤ b.balance account ast)) = true) :
    pairs.all (fun (ast, amt) =>
      decide ((amt : Int) ≤ b'.balance account' ast) &&
      decide ((assetAmountSum fullPairs ast : Int) ≤ b'.balance account' ast)) = true := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall ⊢
    refine ⟨⟨Int.le_trans hall.1.1 (hmore pair.1), Int.le_trans hall.1.2 (hmore pair.1)⟩, ih hall.2⟩

/-- Crediting an account never violates offer safety. -/
theorem safeAt_mono {b b' : Book} {account account' : AccountId} {p : Proposal}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (hsafe : safeAt b account p = true) :
    safeAt b' account' p = true := by
  unfold safeAt at hsafe ⊢
  simp only [Bool.or_eq_true] at hsafe ⊢
  rcases hsafe with hwant | hgive
  · left; exact atLeast_mono hmore p.want p.want hwant
  · right; exact atLeast_mono hmore p.give p.give hgive

/-! ## 3. Seat Structure, Identity-Blind `SeatView` & Gift-Guarded Offer Admission -/

/-- A ZoE seat carrying proof that its account coordinate is in the protected space
    (`protectedBase ≤ account`), and that its payee differs from the seat account. -/
structure Seat where
  account     : AccountId
  h_protected : protectedBase ≤ account := by decide
  inst        : Nat := 0
  offerer     : Nat := 0
  payee       : AccountId := 0
  h_payee_diff : payee ≠ account := by decide
  proposal    : Proposal
  holder      : Option Nat := none
  deriving DecidableEq, Repr

/-- Ordinary accounts below `protectedBase` cannot collide with a seat's protected account. -/
theorem ordinary_ne_seat_account {ordinary : AccountId} (s : Seat)
    (h_ord : ordinary < protectedBase) : ordinary ≠ s.account :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord s.h_protected)

/-- Contract-visible projection of a `Seat`, masking `offerer`, `payee`, and `holder`
    unless explicitly disclosed in `s.proposal.disclose`. -/
structure SeatView where
  account  : AccountId
  inst     : Nat
  give     : List (AssetId × Nat)
  want     : List (AssetId × Nat)
  exit     : ExitRule
  donate   : Bool
  offerer? : Option Nat
  payee?   : Option AccountId
  holder?  : Option Nat
  deriving DecidableEq, Repr

/-- Project a `Seat` into its contract-visible `SeatView`. -/
def Seat.view (s : Seat) : SeatView where
  account  := s.account
  inst     := s.inst
  give     := s.proposal.give
  want     := s.proposal.want
  exit     := s.proposal.exit
  donate   := s.proposal.donate
  offerer? := if s.proposal.disclose.offerer then some s.offerer else none
  payee?   := if s.proposal.disclose.payee then some s.payee else none
  holder?  := if s.proposal.disclose.holder then s.holder else none

/-- **Identity-Blind Contract View Theorem (`seatView_identity_blind`)**:
    When two seats at the same protected coordinate and contract instance carry the same
    undisclosed `Proposal` (`p.disclose = {}`), their contract-facing `SeatView`s are
    bit-identical regardless of `offerer`, `payee`, or `holder` identities! -/
theorem seatView_identity_blind (s₁ s₂ : Seat)
    (hacc : s₁.account = s₂.account)
    (hinst : s₁.inst = s₂.inst)
    (hprop : s₁.proposal = s₂.proposal)
    (hblind : s₁.proposal.disclose = {}) :
    s₁.view = s₂.view := by
  unfold Seat.view
  have hb2 : s₂.proposal.disclose = {} := hprop ▸ hblind
  simp [hacc, hinst, hprop, hb2]

/-- Structured errors refused during ZoE offer admission. -/
inductive OfferError where
  | invitationInvalid (invId : Nat)
  | donationUnmarked
  | donationMarkedWithWant
  | offerUnsafeAtAdmission
  | offererMatchesSeat
  | insufficientOffererBalance (asset : AssetId)
  deriving DecidableEq, Repr

/-- Validate the explicit `donate : Bool` zero-want gift guard on `p`. -/
def checkDonationGuard (p : Proposal) : Except OfferError Unit :=
  if p.wantsNothing then
    if p.donate then .ok ()
    else .error .donationUnmarked
  else
    if p.donate then .error .donationMarkedWithWant
    else .ok ()

/-- **Zero-Want Gift Guard (`donationUnmarked_refused`)**:
    Any proposal requesting zero `want` without `donate = true` is deterministically refused
    with `OfferError.donationUnmarked`. -/
theorem donationUnmarked_refused (p : Proposal)
    (hwant0 : p.wantsNothing = true) (hdon : p.donate = false) :
    checkDonationGuard p = .error .donationUnmarked := by
  simp [checkDonationGuard, hwant0, hdon]

/-- **Spurious Donate Flag Guard (`donationMarkedWithWant_refused`)**:
    Any proposal with positive `want` that also sets `donate = true` is refused with
    `OfferError.donationMarkedWithWant`. -/
theorem donationMarkedWithWant_refused (p : Proposal)
    (hwantPos : p.wantsNothing = false) (hdon : p.donate = true) :
    checkDonationGuard p = .error .donationMarkedWithWant := by
  simp [checkDonationGuard, hwantPos, hdon]

/-- Escrow postings locking `p.give` from `offerer` into `seatAcc`. -/
def giveEscrowPostings (offerer seatAcc : AccountId) (p : Proposal) : List ResourcePosting :=
  p.give.map fun (ast, amt) => ⟨offerer, seatAcc, ast, amt⟩

/-- Admit a ZoE offer by:
    1. Enforcing `checkDonationGuard p` (`donationUnmarked` / `donationMarkedWithWant`),
    2. Redeeming `invId` once from `reg`,
    3. Checking `offerer ≠ seatAcc` and sufficient `offerer` balances for `p.give`,
    4. Escrowing `p.give` into `seatAcc` and verifying `safeAt` on the funded seat. -/
def admitOffer (reg : InvitationRegistry) (b : Book) (invId : Nat)
    (offerer payee seatAcc : AccountId)
    (h_prot : protectedBase ≤ seatAcc) (h_diff : payee ≠ seatAcc)
    (p : Proposal) : Except OfferError (InvitationRegistry × Book × Seat) := do
  checkDonationGuard p
  match reg.spend invId with
  | none => .error (.invitationInvalid invId)
  | some (reg', inv) =>
    if offerer == seatAcc then
      .error .offererMatchesSeat
    else
      let giveAssets := (p.give.map Prod.fst).eraseDups
      match giveAssets.find? (fun ast => decide (b.balance offerer ast < (assetAmountSum p.give ast : Int))) with
      | some badAst => .error (.insufficientOffererBalance badAst)
      | none =>
        let b' := (giveEscrowPostings offerer seatAcc p).foldl Book.applyPosting b
        let s : Seat := {
          account := seatAcc
          h_protected := h_prot
          inst := inv.instanceId
          offerer := offerer
          payee := payee
          h_payee_diff := h_diff
          proposal := p
        }
        if safeAt b' seatAcc p then .ok (reg', b', s)
        else .error .offerUnsafeAtAdmission

theorem admitOffer_donationUnmarked_refused (reg : InvitationRegistry) (b : Book) (invId : Nat)
    (offerer payee seatAcc : AccountId)
    (h_prot : protectedBase ≤ seatAcc) (h_diff : payee ≠ seatAcc)
    (p : Proposal) (hwant0 : p.wantsNothing = true) (hdon : p.donate = false) :
    admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .error .donationUnmarked := by
  unfold admitOffer
  rw [donationUnmarked_refused p hwant0 hdon]
  rfl

theorem admitOffer_spends_invitation_once {reg reg' : InvitationRegistry} {b b' : Book}
    {invId : Nat} {offerer payee seatAcc : AccountId}
    {h_prot : protectedBase ≤ seatAcc} {h_diff : payee ≠ seatAcc}
    {p : Proposal} {s : Seat}
    (hadm : admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .ok (reg', b', s)) :
    reg'.spend invId = none := by
  unfold admitOffer at hadm
  cases hguard : checkDonationGuard p with
  | error e => rw [hguard] at hadm; cases hadm
  | ok _ =>
    rw [hguard] at hadm
    dsimp only [Bind.bind, Except.bind] at hadm
    cases hsp : reg.spend invId with
    | none => rw [hsp] at hadm; cases hadm
    | some pair =>
      rcases pair with ⟨r1, inv⟩
      rw [hsp] at hadm
      by_cases hoff : offerer == seatAcc
      · simp [hoff] at hadm
      · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hadm
        split at hadm
        · cases hadm
        · split at hadm
          next hsafe =>
            injection hadm with hp
            have hr : reg' = r1 := (Prod.mk.inj hp).1.symm
            subst hr
            exact InvitationRegistry.no_double_redeem hsp
          next => cases hadm

/-- Successful admission checks the actual funded account, including pre-existing debt. -/
theorem admitOffer_ensures_safeAt {reg reg' : InvitationRegistry} {b b' : Book}
    {invId offerer payee seatAcc : Nat} {hp : protectedBase ≤ seatAcc}
    {hd : payee ≠ seatAcc} {p : Proposal} {s : Seat}
    (h : admitOffer reg b invId offerer payee seatAcc hp hd p = .ok (reg', b', s)) :
    safeAt b' s.account s.proposal = true := by
  unfold admitOffer at h
  cases hg : checkDonationGuard p with
  | error e => rw [hg] at h; cases h
  | ok u =>
    simp only [hg, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h; assumption
          · cases h

/-- An unsafe funded seat cannot be returned by admission. -/
theorem admitOffer_unsafe_refused {reg reg' : InvitationRegistry} {b b' : Book}
    {invId offerer payee seatAcc : Nat} {hp : protectedBase ≤ seatAcc}
    {hd : payee ≠ seatAcc} {p : Proposal} {s : Seat}
    (hunsafe : safeAt b' s.account s.proposal = false) :
    admitOffer reg b invId offerer payee seatAcc hp hd p ≠ .ok (reg', b', s) := by
  intro h
  have := admitOffer_ensures_safeAt h
  simp_all

/-- Immutable sorted seat index; construction checks ordering once, lookup is binary search. -/
structure SeatTableExec where
  entries : Array Seat
  sorted : Obend.Polis.CapTP.SortedBy Seat.account entries

def SeatTableExec.ofSeats (seats : List Seat) : Option SeatTableExec :=
  if h : strictKeys Seat.account seats = true then
    some ⟨seats.toArray, strictKeys_sorted _ _ h⟩
  else none

def lookupSeatSpec (seats : List Seat) (account : AccountId) : Option Seat :=
  seats.find? (fun s => s.account == account)

def lookupSeatExec (table : SeatTableExec) (account : AccountId) : Option Seat :=
  Obend.Polis.CapTP.search Seat.account table.entries account
    (table.entries.size + 1) 0 table.entries.size

theorem lookupSeatExec_eq_lookupSpec (table : SeatTableExec) (account : AccountId) :
    lookupSeatExec table account = lookupSeatSpec table.entries.toList account :=
  Obend.Polis.CapTP.search_eq_spec _ _ table.sorted account

/-- Checked list entry point: sorted inputs use the index; other inputs keep the first match.
Callers making repeated queries can retain the table returned by `ofSeats`. -/
def lookupSeatsExec (seats : List Seat) (account : AccountId) : Option Seat :=
  match SeatTableExec.ofSeats seats with
  | some table => lookupSeatExec table account
  | none => seats.find? (fun s => s.account == account)

theorem lookupSeatsExec_eq_spec (seats : List Seat) (account : AccountId) :
    lookupSeatsExec seats account = lookupSeatSpec seats account := by
  unfold lookupSeatsExec SeatTableExec.ofSeats
  by_cases h : strictKeys Seat.account seats = true
  · simp [h, lookupSeatExec_eq_lookupSpec]
  · simp [h, lookupSeatSpec]

@[csimp] theorem lookupSeatSpec_eq_exec : @lookupSeatSpec = @lookupSeatsExec := by
  funext seats account
  exact (lookupSeatsExec_eq_spec seats account).symm

def checkAllSeatsSafeExec (b : Book) (table : SeatTableExec) : Bool :=
  table.entries.all (fun s => safeAt b s.account s.proposal)

theorem checkAllSeatsSafeExec_eq_spec (b : Book) (table : SeatTableExec) :
    checkAllSeatsSafeExec b table =
      table.entries.toList.all (fun s => safeAt b s.account s.proposal) := by
  exact (Array.all_toList ..).symm

/-! ## 4. World Collections & Distinct Seat Accounts -/

structure World where
  book        : Book
  seats       : List Seat
  nodup_seats : (seats.map Seat.account).Nodup := by decide
  assets      : List AssetId := []

def World.seat? (w : World) (acc : AccountId) : Option Seat :=
  lookupSeatSpec w.seats acc

theorem seats_find_mem (seats : List Seat) (hnodup : (seats.map Seat.account).Nodup) {s : Seat} (hmem : s ∈ seats) :
    seats.find? (fun x => x.account == s.account) = some s := by
  induction seats with
  | nil => cases hmem
  | cons head rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.find?_cons]
    split
    · rename_i hbeq
      have heq : head.account = s.account := beq_iff_eq.mp hbeq
      rcases List.mem_cons.mp hmem with rfl | hin
      · rfl
      · have hcontra : s.account ∈ rest.map Seat.account := List.mem_map_of_mem hin
        rw [← heq] at hcontra
        exact False.elim (hnodup.1 hcontra)
    · rename_i hbeq
      have hne : head.account ≠ s.account := by
        intro heq; rw [heq] at hbeq; simp at hbeq
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact False.elim (hne rfl)
      · exact ih hnodup.2 hin

theorem World.seat?_mem (w : World) {s : Seat} (hmem : s ∈ w.seats) :
    w.seat? s.account = some s :=
  seats_find_mem w.seats w.nodup_seats hmem

theorem seats_account_inj (w : World) {s1 s2 : Seat}
    (h1 : s1 ∈ w.seats) (h2 : s2 ∈ w.seats) (heq : s1.account = s2.account) :
    s1 = s2 := by
  have h_find1 := w.seat?_mem h1
  have h_find2 := w.seat?_mem h2
  rw [heq] at h_find1
  rw [h_find1] at h_find2
  cases h_find2
  rfl

/-! ## 5. Payout Transfers & Full-Balance-Support Exit Sweep (`exit_sweeps_all_assets`) -/

structure ExitPrecondition (b : Book) (account payee : AccountId) (assets : List AssetId) : Prop where
  h_diff         : payee ≠ account
  h_nonneg       : ∀ ast ∈ assets, 0 ≤ b.balance account ast
  h_nodup        : assets.Nodup
  h_zero_outside : ∀ ast ∉ assets, b.balance account ast = 0

def payoutPostings (b : Book) (account payee : AccountId) (assets : List AssetId) : List ResourcePosting :=
  assets.map fun ast => ⟨account, payee, ast, (b.balance account ast).toNat⟩

@[expose] def applyPostings (b : Book) (ps : List ResourcePosting) : Book :=
  ps.foldl Book.applyPosting b

@[simp] theorem applyPostings_nil (b : Book) : applyPostings b [] = b := rfl

@[simp] theorem applyPostings_cons (b : Book) (p : ResourcePosting) (ps : List ResourcePosting) :
    applyPostings b (p :: ps) = applyPostings (b.applyPosting p) ps := rfl

theorem map_congr_mem {α β : Type} (f g : α → β) (l : List α) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]

theorem applyPosting_balance_other_asset (b : Book) (p : ResourcePosting) (a : AccountId) (ast : AssetId)
    (hast : ast ≠ p.asset) : (b.applyPosting p).balance a ast = b.balance a ast := by
  rw [Book.balance_applyPosting]
  simp [hast]

theorem applyPostings_balance_other_asset (ps : List ResourcePosting) (b : Book) (a : AccountId) (ast : AssetId)
    (haway : ∀ p ∈ ps, ast ≠ p.asset) : (applyPostings b ps).balance a ast = b.balance a ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons]
    have hp : ast ≠ p.asset := haway p (List.Mem.head rest)
    have hrest : ∀ q ∈ rest, ast ≠ q.asset := fun q hq => haway q (List.Mem.tail p hq)
    rw [ih (b.applyPosting p) hrest]
    exact applyPosting_balance_other_asset b p a ast hp

theorem payoutPostings_assets_ne (b : Book) (account payee : AccountId) (assets : List AssetId) (ast : AssetId)
    (hnotmem : ast ∉ assets) :
    ∀ p ∈ payoutPostings b account payee assets, ast ≠ p.asset := by
  intro p hp
  simp only [payoutPostings, List.mem_map] at hp
  rcases hp with ⟨a, ha, rfl⟩
  intro heq
  subst heq
  exact hnotmem ha

theorem payout_single_balance (b : Book) (account payee : AccountId) (ast : AssetId)
    (hdiff : payee ≠ account) (hnonneg : 0 ≤ b.balance account ast) :
    let p : ResourcePosting := ⟨account, payee, ast, (b.balance account ast).toNat⟩
    (b.applyPosting p).balance account ast = 0 ∧
    (b.applyPosting p).balance payee ast = b.balance payee ast + b.balance account ast := by
  dsimp only
  rw [Book.balance_applyPosting, Book.balance_applyPosting]
  have htoNat : ((b.balance account ast).toNat : Int) = b.balance account ast :=
    Int.toNat_of_nonneg hnonneg
  have h_ne1 : account ≠ payee := Ne.symm hdiff
  have h_ne2 : payee ≠ account := hdiff
  simp [htoNat, h_ne1, h_ne2]

theorem payout_exact (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hdiff : payee ≠ account) (hnodup : assets.Nodup)
    (hnonneg : ∀ ast ∈ assets, 0 ≤ b.balance account ast) :
    ∀ ast ∈ assets,
      (applyPostings b (payoutPostings b account payee assets)).balance account ast = 0 ∧
      (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
        b.balance payee ast + b.balance account ast := by
  induction assets generalizing b with
  | nil =>
    intro ast hast
    cases hast
  | cons head rest ih =>
    rw [List.nodup_cons] at hnodup
    intro ast hast
    unfold payoutPostings
    simp only [List.map_cons]
    rw [applyPostings_cons]
    have hhead_nonneg : 0 ≤ b.balance account head := hnonneg head (List.Mem.head rest)
    have hrest_nonneg : ∀ a ∈ rest, 0 ≤ b.balance account a :=
      fun a ha => hnonneg a (List.Mem.tail head ha)
    let b1 := b.applyPosting ⟨account, payee, head, (b.balance account head).toNat⟩
    have hstep := payout_single_balance b account payee head hdiff hhead_nonneg
    have hrest_agree : ∀ a ∈ rest, b1.balance account a = b.balance account a := by
      intro a ha
      have hne : a ≠ head := fun h => hnodup.1 (h ▸ ha)
      exact applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ account a hne
    have hmap_eq : (rest.map fun a => (⟨account, payee, a, (b.balance account a).toNat⟩ : ResourcePosting)) =
        payoutPostings b1 account payee rest := by
      unfold payoutPostings
      apply map_congr_mem
      intro a ha
      rw [hrest_agree a ha]
    rw [hmap_eq]
    rcases List.mem_cons.mp hast with rfl | hmem
    · have haway : ∀ p ∈ payoutPostings b1 account payee rest, ast ≠ p.asset :=
        payoutPostings_assets_ne b1 account payee rest ast hnodup.1
      have hacc_rest := applyPostings_balance_other_asset (payoutPostings b1 account payee rest) b1 account ast haway
      have hpay_rest := applyPostings_balance_other_asset (payoutPostings b1 account payee rest) b1 payee ast haway
      rw [hacc_rest, hpay_rest]
      exact hstep
    · have hnew_nonneg : ∀ a ∈ rest, 0 ≤ b1.balance account a := by
        intro a ha; rw [hrest_agree a ha]; exact hrest_nonneg a ha
      have hrec := ih b1 hnodup.2 hnew_nonneg ast hmem
      refine ⟨hrec.1, ?_⟩
      rw [hrec.2]
      have hne : ast ≠ head := fun h => hnodup.1 (h ▸ hmem)
      have hpay_step := applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ payee ast hne
      have hacc_step := applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ account ast hne
      rw [hpay_step, hacc_step]

theorem exit_pays_allocation (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hdiff : payee ≠ account) (hnodup : assets.Nodup)
    (hnonneg : ∀ ast ∈ assets, 0 ≤ b.balance account ast) :
    ∀ ast ∈ assets,
      (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
        b.balance payee ast + b.balance account ast :=
  fun ast hast => (payout_exact b account payee assets hdiff hnodup hnonneg ast hast).2

theorem payout_unlisted (b : Book) (account payee : AccountId) (assets : List AssetId)
    (ast : AssetId) (hnotmem : ast ∉ assets) (a : AccountId) :
    (applyPostings b (payoutPostings b account payee assets)).balance a ast = b.balance a ast := by
  apply applyPostings_balance_other_asset
  exact payoutPostings_assets_ne b account payee assets ast hnotmem

theorem exit_recovery_all (b : Book) (account payee : AccountId) (assets : List AssetId)
    (precond : ExitPrecondition b account payee assets) :
    (∀ ast, (applyPostings b (payoutPostings b account payee assets)).balance account ast = 0) ∧
    (∀ ast ∈ assets, (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
      b.balance payee ast + b.balance account ast) := by
  have hexact := payout_exact b account payee assets precond.h_diff precond.h_nodup precond.h_nonneg
  constructor
  · intro ast
    by_cases hmem : ast ∈ assets
    · exact (hexact ast hmem).1
    · rw [payout_unlisted b account payee assets ast hmem account]
      exact precond.h_zero_outside ast hmem
  · intro ast hast
    exact (hexact ast hast).2

theorem applyPostings_accounts (b : Book) (ps : List ResourcePosting) :
    (applyPostings b ps).accounts = b.accounts := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih => rw [applyPostings_cons, ih]; rfl

theorem applyPostings_conserves (b : Book) (ps : List ResourcePosting)
    (hps : ∀ p ∈ ps, p.source ∈ b.accounts ∧ p.destination ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyPostings b ps).totalAsset ast = b.totalAsset ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons]
    have hp := hps p (List.Mem.head rest)
    have hcons := b.applyPosting_conserves p hp.1 hp.2 hnodup ast
    have hnodup' : (b.applyPosting p).accounts.Nodup := by rw [b.applyPosting_accounts]; exact hnodup
    have hrest : ∀ q ∈ rest, q.source ∈ (b.applyPosting p).accounts ∧ q.destination ∈ (b.applyPosting p).accounts := by
      intro q hq
      have hq' := hps q (List.Mem.tail p hq)
      rw [b.applyPosting_accounts]
      exact hq'
    rw [ih (b.applyPosting p) hrest hnodup', hcons]

theorem payout_conserves (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hacc : account ∈ b.accounts) (hpay : payee ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyPostings b (payoutPostings b account payee assets)).totalAsset ast = b.totalAsset ast := by
  apply applyPostings_conserves
  · intro p hp
    simp only [payoutPostings, List.mem_map] at hp
    rcases hp with ⟨_, _, rfl⟩
    exact ⟨hacc, hpay⟩
  · exact hnodup

/-- **Full-Balance-Support Seat Exit (`exitSeat`)**:
    Sweeps the seat's entire finite support `b.heldAssets s.account` directly from `Book`'s
    `FinMap` to `s.payee` — requiring NO caller-supplied asset list! -/
def exitSeat (b : Book) (s : Seat) : Book :=
  applyPostings b (payoutPostings b s.account s.payee (b.heldAssets s.account))

/-- **Full-Support Exit Sweep Theorem (`exit_sweeps_all_assets`)**:
    When a seat holds non-negative balances across all assets (`∀ ast, 0 ≤ b.balance s.account ast`),
    `exitSeat b s`:
    1. Zeroes the seat's balance on **every** asset `ast : AssetId` in the entire universe
       (including unsolicited/bonus assets outside `s.proposal.give` and `s.proposal.want`),
    2. Credits `s.payee` with the exact pre-exit seat balance on **every** asset `ast : AssetId`,
    3. Conserves global asset supply (`globalAssetSum`) unconditionally. -/
theorem exit_sweeps_all_assets (b : Book) (s : Seat)
    (hnonneg : ∀ ast : AssetId, 0 ≤ b.balance s.account ast) :
    (∀ ast : AssetId, (exitSeat b s).balance s.account ast = 0) ∧
    (∀ ast : AssetId, (exitSeat b s).balance s.payee ast =
      b.balance s.payee ast + b.balance s.account ast) ∧
    (∀ ast : AssetId, (exitSeat b s).globalAssetSum ast = b.globalAssetSum ast) := by
  have precond : ExitPrecondition b s.account s.payee (b.heldAssets s.account) := {
    h_diff := s.h_payee_diff
    h_nonneg := fun ast _ => hnonneg ast
    h_nodup := b.heldAssets_nodup s.account
    h_zero_outside := fun ast hnot => b.balance_eq_zero_of_not_mem_heldAssets s.account hnot
  }
  have ⟨hzero, hpay_in⟩ := exit_recovery_all b s.account s.payee (b.heldAssets s.account) precond
  refine ⟨hzero, ?_, ?_⟩
  · intro ast
    by_cases hmem : ast ∈ b.heldAssets s.account
    · exact hpay_in ast hmem
    · unfold exitSeat
      rw [payout_unlisted b s.account s.payee (b.heldAssets s.account) ast hmem s.payee]
      rw [b.balance_eq_zero_of_not_mem_heldAssets s.account hmem]
      omega
  · intro ast
    unfold exitSeat
    have fold_cons : ∀ (ps : List ResourcePosting) (bk : Book),
        (applyPostings bk ps).globalAssetSum ast = bk.globalAssetSum ast := by
      intro ps
      induction ps with
      | nil => intro bk; rfl
      | cons p rest ih =>
        intro bk
        rw [applyPostings_cons, ih (bk.applyPosting p), Book.applyPosting_conserves_global]
    exact fold_cons _ b

/-! ## 6. Multi-Seat Atomic Batch Reallocation (`BatchRealloc`) -/

structure BatchRealloc where
  postings : List ResourcePosting
  deriving DecidableEq, Repr

def applyBatchRealloc (b : Book) (realloc : BatchRealloc) : Book :=
  applyPostings b realloc.postings

def seatCredit (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId) : Nat :=
  ((realloc.postings.filter fun p => p.destination == acc && p.asset == ast).map ResourcePosting.amount).sum

def seatDebit (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId) : Nat :=
  ((realloc.postings.filter fun p => p.source == acc && p.asset == ast).map ResourcePosting.amount).sum

def batchTotalCredits (seats : List Seat) (realloc : BatchRealloc) (ast : AssetId) : Nat :=
  ((seats.map Seat.account).map fun acc => seatCredit realloc acc ast).sum

def batchTotalDebits (seats : List Seat) (realloc : BatchRealloc) (ast : AssetId) : Nat :=
  ((seats.map Seat.account).map fun acc => seatDebit realloc acc ast).sum

def batchAssets (seats : List Seat) (realloc : BatchRealloc) : List AssetId :=
  (seats.flatMap fun s => s.proposal.assets) ++ realloc.postings.map ResourcePosting.asset

def checkBatchReallocSafe (b : Book) (seats : List Seat) (realloc : BatchRealloc) : Bool :=
  let seatAccounts := seats.map Seat.account
  let nodupSeats := decide seatAccounts.Nodup
  let endpointsInSeats := realloc.postings.all fun p =>
    decide (p.source ∈ seatAccounts) &&
    decide (p.destination ∈ seatAccounts) &&
    decide (protectedBase ≤ p.source) &&
    decide (protectedBase ≤ p.destination)
  let assets := batchAssets seats realloc
  let zeroSumConserved := assets.all fun ast =>
    batchTotalCredits seats realloc ast == batchTotalDebits seats realloc ast
  let b' := applyBatchRealloc b realloc
  let allSeatsOfferSafe := seats.all fun s =>
    safeAt b' s.account s.proposal &&
    assets.all fun ast => decide (0 ≤ b'.balance s.account ast)
  nodupSeats && endpointsInSeats && zeroSumConserved && allSeatsOfferSafe

theorem batchRealloc_nodup_seats (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    (seats.map Seat.account).Nodup := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_safe
  exact h_safe.1.1.1

theorem batchRealloc_preserves_all_seats_offer_safe (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    ∀ s ∈ seats, safeAt (applyBatchRealloc b realloc) s.account s.proposal = true := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true] at h_safe
  intro s hs
  exact (h_safe.2 s hs).1

theorem batchRealloc_zero_sum_conservation (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    ∀ ast ∈ batchAssets seats realloc,
      batchTotalCredits seats realloc ast = batchTotalDebits seats realloc ast := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h_safe
  intro ast hast
  exact h_safe.1.2 ast hast

theorem filter_asset_nil_of_forall_ne (ps : List ResourcePosting) (pred : AccountId → ResourcePosting → Bool)
    (acc : AccountId) (ast : AssetId) (hne : ∀ p ∈ ps, p.asset ≠ ast) :
    ps.filter (fun p => pred acc p && (p.asset == ast)) = [] := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    have hp : (p.asset == ast) = false := beq_eq_false_iff_ne.mpr (hne p (List.Mem.head rest))
    simp [hp, ih (fun q hq => hne q (List.Mem.tail p hq))]

theorem seatCredit_eq_zero_of_forall_ne (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId)
    (hne : ∀ p ∈ realloc.postings, p.asset ≠ ast) :
    seatCredit realloc acc ast = 0 := by
  unfold seatCredit
  rw [filter_asset_nil_of_forall_ne realloc.postings (fun a p => p.destination == a) acc ast hne]
  rfl

theorem seatDebit_eq_zero_of_forall_ne (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId)
    (hne : ∀ p ∈ realloc.postings, p.asset ≠ ast) :
    seatDebit realloc acc ast = 0 := by
  unfold seatDebit
  rw [filter_asset_nil_of_forall_ne realloc.postings (fun a p => p.source == a) acc ast hne]
  rfl

theorem batchRealloc_zero_sum_all_assets (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) (ast : AssetId) :
    batchTotalCredits seats realloc ast = batchTotalDebits seats realloc ast := by
  by_cases hmem : ast ∈ batchAssets seats realloc
  · exact batchRealloc_zero_sum_conservation b seats realloc h_safe ast hmem
  · have hne : ∀ p ∈ realloc.postings, p.asset ≠ ast := by
      intro p hp heq
      apply hmem
      unfold batchAssets
      rw [List.mem_append]
      right
      rw [← heq]
      exact List.mem_map_of_mem hp
    unfold batchTotalCredits batchTotalDebits
    have hmap : ((seats.map Seat.account).map fun acc => seatCredit realloc acc ast) =
        ((seats.map Seat.account).map fun acc => seatDebit realloc acc ast) := by
      apply map_congr_mem
      intro acc _
      rw [seatCredit_eq_zero_of_forall_ne realloc acc ast hne,
          seatDebit_eq_zero_of_forall_ne realloc acc ast hne]
    rw [hmap]

theorem applyPosting_balance_other_account (b : Book) (p : ResourcePosting) (a : AccountId) (ast : AssetId)
    (hsrc : a ≠ p.source) (hdst : a ≠ p.destination) :
    (b.applyPosting p).balance a ast = b.balance a ast := by
  rw [Book.balance_applyPosting]
  simp [hsrc, hdst]

theorem applyPostings_balance_other_account (ps : List ResourcePosting) (b : Book) (a : AccountId) (ast : AssetId)
    (haway : ∀ p ∈ ps, a ≠ p.source ∧ a ≠ p.destination) :
    (applyPostings b ps).balance a ast = b.balance a ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons]
    have hp := haway p (List.Mem.head rest)
    have hrest : ∀ q ∈ rest, a ≠ q.source ∧ a ≠ q.destination :=
      fun q hq => haway q (List.Mem.tail p hq)
    rw [ih (b.applyPosting p) hrest]
    exact applyPosting_balance_other_account b p a ast hp.1 hp.2

theorem applyBatchRealloc_balance_ordinary_of_protected (b : Book) (realloc : BatchRealloc)
    (h_prot : ∀ p ∈ realloc.postings, protectedBase ≤ p.source ∧ protectedBase ≤ p.destination)
    (ordinary : AccountId) (h_ord : ordinary < protectedBase) (ast : AssetId) :
    (applyBatchRealloc b realloc).balance ordinary ast = b.balance ordinary ast := by
  unfold applyBatchRealloc
  apply applyPostings_balance_other_account
  intro p hp
  obtain ⟨hsrc, hdst⟩ := h_prot p hp
  exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord hsrc), Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord hdst)⟩

theorem batchRealloc_disjoint_from_ordinary_accounts (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true)
    (ordinary : AccountId) (h_ord : ordinary < protectedBase) (ast : AssetId) :
    (applyBatchRealloc b realloc).balance ordinary ast = b.balance ordinary ast := by
  apply applyBatchRealloc_balance_ordinary_of_protected b realloc _ ordinary h_ord ast
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h_safe
  intro p hp
  have hp' := h_safe.1.1.2 p hp
  exact ⟨hp'.1.2, hp'.2⟩

theorem batchRealloc_conserves (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true)
    (h_reg : ∀ s ∈ seats, s.account ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyBatchRealloc b realloc).totalAsset ast = b.totalAsset ast := by
  unfold applyBatchRealloc
  apply applyPostings_conserves _ _ _ hnodup ast
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h_safe
  intro p hp
  have hp' := h_safe.1.1.2 p hp
  rcases List.mem_map.mp hp'.1.1.1 with ⟨s1, hs1, hacc1⟩
  rcases List.mem_map.mp hp'.1.1.2 with ⟨s2, hs2, hacc2⟩
  exact ⟨hacc1 ▸ h_reg s1 hs1, hacc2 ▸ h_reg s2 hs2⟩

end Obend.Ledger

end

/-
# Obend.Polis.ZoeSeatSettlement — ZoE seat settlement on the ledger spine
Offers, seats and exits are `Obend.Ledger.Seat`'s (`Proposal`, `Seat`, `admitOffer` with its
donation guard and one-time invitations, `exitSeat`, `checkBatchReallocSafe`), run on the seat
`Book`, and every leg they move is also posted to the typed `FloorBook` through
`FloorBook.admitBatch`, which decides. `AssetBundle` is the executable form of a proposal's asset
lists. A seat's holder is a 256-bit commitment opened by its preimage. `ValidZoeTrace` and
`trace_invariant` carry the floors and every asset's total along any trace.
-/
public section
namespace Obend.Polis.ZoeSeatSettlement
/-! ## 1. `AssetBundle`: sorted, positive, 64-bit amounts with a checked linear merge -/
abbrev AssetBrand := Nat
abbrev SeatId := Nat
abbrev Entry := AssetBrand × UInt64
def Canonical (xs : List Entry) : Prop :=
  xs.Pairwise (fun a b => a.1 < b.1) ∧ ∀ p ∈ xs, 0 < p.2.toNat
structure AssetBundle where
  entries : Array Entry
  canonical : Canonical entries.toList
def amountList : List Entry → AssetBrand → Nat
  | [], _ => 0
  | (k, v) :: xs, b => (if k = b then v.toNat else 0) + amountList xs b
def AssetBundle.amountSpec (a : AssetBundle) : AssetBrand → Nat := amountList a.entries.toList
def AssetBundle.empty : AssetBundle := ⟨#[], by simp [Canonical]⟩
def AssetBundle.singleton (b : AssetBrand) (v : UInt64) (hv : 0 < v.toNat) : AssetBundle :=
  ⟨#[(b, v)], by simpa [Canonical] using hv⟩
theorem amountList_zero {xs : List Entry} {b : Nat}
    (h : ∀ p ∈ xs, p.1 ≠ b) : amountList xs b = 0 := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [amountList, h p (by simp), ↓reduceIte, Nat.zero_add]
    exact ih (fun p hp => h p (by simp [hp]))
theorem amountList_lookup {xs : List Entry} (hs : xs.Pairwise (fun a b => a.1 < b.1)) (b : Nat) :
    amountList xs b = ((xs.find? (fun p => p.1 == b)).map (fun p => p.2.toNat)).getD 0 := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨hp, ht⟩ := List.pairwise_cons.mp hs
    by_cases hb : p.1 = b
    · have hz : amountList xs b = 0 := amountList_zero (fun q hq => by have := hp q hq; simp only [AssetBrand] at *; omega)
      simp [amountList, hb, hz]
    · simp [amountList, hb, ih ht]
def AssetBundle.amountOf (a : AssetBundle) (b : AssetBrand) : Nat :=
  ((CapTP.search Prod.fst a.entries b (a.entries.size + 1) 0 a.entries.size).map
    (fun p => p.2.toNat)).getD 0
theorem AssetBundle.amountOf_eq_spec (a : AssetBundle) (b : AssetBrand) :
    a.amountOf b = a.amountSpec b := by
  have hs : CapTP.SortedBy Prod.fst a.entries := by
    intro i j hi hj hij
    exact (List.pairwise_iff_getElem.mp a.canonical.1) i j (by simpa using hi)
      (by simpa using hj) hij
  rw [amountOf, CapTP.search_eq_spec _ _ hs, amountSpec, amountList_lookup a.canonical.1]
  rfl
def AssetBundle.bundleLeq (a b : AssetBundle) : Bool :=
  a.entries.all (fun p => decide (p.2.toNat ≤ b.amountOf p.1))
theorem amountList_member {xs : List Entry} (hs : xs.Pairwise (fun a b => a.1 < b.1))
    {p : Entry} (hp : p ∈ xs) : amountList xs p.1 = p.2.toNat := by
  induction xs with
  | nil => cases hp
  | cons q xs ih =>
    obtain ⟨hq, ht⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hp with rfl | hp
    · have hz : amountList xs p.1 = 0 := amountList_zero (fun p hp => by have := hq p hp; simp only [AssetBrand] at *; omega)
      simp [amountList, hz]
    · have hne : q.1 ≠ p.1 := by have := hq p hp; simp only [AssetBrand] at *; omega
      simp [amountList, hne, ih ht hp]
theorem AssetBundle.bundleLeq_iff_forall_brand (a b : AssetBundle) :
    a.bundleLeq b = true ↔ ∀ k, a.amountSpec k ≤ b.amountSpec k := by
  simp only [bundleLeq, ← Array.all_toList, List.all_eq_true, decide_eq_true_eq, amountOf_eq_spec]
  constructor
  · intro h k
    by_cases hk : ∃ p ∈ a.entries.toList, p.1 = k
    · obtain ⟨p, hp, rfl⟩ := hk
      rw [amountSpec, amountList_member a.canonical.1 hp]
      exact h p (by simpa using hp)
    · have hz := amountList_zero (xs := a.entries.toList) (b := k) (by grind)
      simp [amountSpec, hz]
  · intro h p hp
    have hm : p ∈ a.entries.toList := by simpa using hp
    simpa [amountSpec, amountList_member a.canonical.1 hm] using h p.1
/-- Linear merge; the sum is checked in the unbounded domain before conversion. -/
def mergeAmounts : List Entry → List Entry → Option (List Entry)
  | [], ys => some ys
  | x :: xs, [] => some (x :: xs)
  | x :: xs, y :: ys =>
    if x.1 < y.1 then (mergeAmounts xs (y :: ys)).map (x :: ·)
    else if y.1 < x.1 then (mergeAmounts (x :: xs) ys).map (y :: ·)
    else if x.2.toNat + y.2.toNat < 2^64 then
      (mergeAmounts xs ys).map ((x.1, UInt64.ofNat (x.2.toNat + y.2.toNat)) :: ·)
    else none
termination_by xs ys => xs.length + ys.length
theorem mergeAmounts_sum : ∀ {xs ys zs : List Entry}, mergeAmounts xs ys = some zs →
    ∀ b, amountList zs b = amountList xs b + amountList ys b
  | [], _, _, h, b => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; simp [amountList]
  | _ :: _, [], _, h, b => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; simp [amountList]
  | x :: xs, y :: ys, _, h, b => by
    simp only [mergeAmounts] at h
    split at h
    · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [amountList, mergeAmounts_sum hz b]; simp only [AssetBrand] at *; omega
    · split at h
      · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [amountList, mergeAmounts_sum hz b]; simp only [AssetBrand] at *; omega
      · split at h
        · rename_i hx hy hbound
          obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
          have hk : x.1 = y.1 := by simp only [AssetBrand] at *; omega
          simp only [amountList, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hbound,
            mergeAmounts_sum hz b, hk]
          split <;> (simp only [AssetBrand] at *; omega)
        · cases h
termination_by xs ys _ _ _ => xs.length + ys.length
theorem mergeAmounts_keys : ∀ {xs ys zs : List Entry}, mergeAmounts xs ys = some zs →
    ∀ p ∈ zs, (∃ q ∈ xs, q.1 = p.1) ∨ (∃ q ∈ ys, q.1 = p.1)
  | [], _, _, h, p, hp => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact .inr ⟨p, hp, rfl⟩
  | _ :: _, [], _, h, p, hp => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact .inl ⟨p, hp, rfl⟩
  | x :: xs, y :: ys, _, h, p, hp => by
    simp only [mergeAmounts] at h
    split at h
    · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inl ⟨p, by simp, rfl⟩
      · rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | hy
        · exact .inl ⟨q, by simp [hq], hk⟩
        · exact .inr hy
    · split at h
      · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact .inr ⟨p, by simp, rfl⟩
        · rcases mergeAmounts_keys hz p hp with hx | ⟨q,hq,hk⟩
          · exact .inl hx
          · exact .inr ⟨q, by simp [hq], hk⟩
      · split at h
        · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
          rcases List.mem_cons.mp hp with rfl | hp
          · exact .inl ⟨x, by simp, rfl⟩
          · rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
            · exact .inl ⟨q, by simp [hq], hk⟩
            · exact .inr ⟨q, by simp [hq], hk⟩
        · cases h
termination_by xs ys _ _ _ _ => xs.length + ys.length
theorem mergeAmounts_canonical : ∀ {xs ys zs : List Entry}, Canonical xs → Canonical ys →
    mergeAmounts xs ys = some zs → Canonical zs
  | [], _, _, _, hy, h => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact hy
  | _ :: _, [], _, hx, _, h => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact hx
  | x :: xs, y :: ys, _, ⟨.cons hx sx, px⟩, ⟨.cons hy sy, py⟩, h => by
    have cx : Canonical xs := ⟨sx, fun p hp => px p (by simp [hp])⟩
    have cy : Canonical ys := ⟨sy, fun p hp => py p (by simp [hp])⟩
    simp only [mergeAmounts] at h
    split at h
    · rename_i hxy
      obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨sz, pz⟩ := mergeAmounts_canonical cx ⟨.cons hy sy, py⟩ hz
      refine ⟨.cons ?_ sz, ?_⟩
      · intro p hp
        rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
        · have := hx q hq; simp only [AssetBrand] at *; omega
        · rcases List.mem_cons.mp hq with rfl | hq
          · simp only [AssetBrand] at *; omega
          · have := hy q hq; simp only [AssetBrand] at *; omega
      · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
        · exact px p (by simp)
        · exact pz p hp
    · split at h
      · rename_i hxy hyx
        obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨sz, pz⟩ := mergeAmounts_canonical ⟨.cons hx sx, px⟩ cy hz
        refine ⟨.cons ?_ sz, ?_⟩
        · intro p hp
          rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
          · rcases List.mem_cons.mp hq with rfl | hq
            · simp only [AssetBrand] at *; omega
            · have := hx q hq; simp only [AssetBrand] at *; omega
          · have := hy q hq; simp only [AssetBrand] at *; omega
        · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · exact py p (by simp)
          · exact pz p hp
      · split at h
        · rename_i hxy hyx hb
          obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨sz, pz⟩ := mergeAmounts_canonical cx cy hz
          refine ⟨.cons ?_ sz, ?_⟩
          · intro p hp
            rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
            · have := hx q hq; dsimp; simp only [AssetBrand] at *; omega
            · have := hy q hq; dsimp; simp only [AssetBrand] at *; omega
          · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
            · simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hb]
              have := px x (by simp); simp only [AssetBrand] at *; omega
            · exact pz p hp
        · cases h
termination_by xs ys _ _ _ _ => xs.length + ys.length
def AssetBundle.addChecked (a b : AssetBundle) : Option AssetBundle :=
  match h : mergeAmounts a.entries.toList b.entries.toList with
  | none => none
  | some zs => some ⟨zs.toArray, by simpa using mergeAmounts_canonical a.canonical b.canonical h⟩
theorem AssetBundle.addChecked_sum {a b c : AssetBundle} (h : a.addChecked b = some c) :
    ∀ k, c.amountSpec k = a.amountSpec k + b.amountSpec k := by
  unfold addChecked at h
  split at h
  · cases h
  · cases h
    exact mergeAmounts_sum ‹_›
theorem amountList_tail_le (x : Entry) (xs : List Entry) (b : Nat) :
    amountList xs b ≤ amountList (x :: xs) b := by simp [amountList]
theorem mergeAmounts_complete : ∀ (xs ys : List Entry),
    (∀ k, amountList xs k + amountList ys k < 2^64) →
    ∃ zs, mergeAmounts xs ys = some zs
  | [], ys, _ => ⟨ys, by simp [mergeAmounts]⟩
  | x :: xs, [], _ => ⟨x :: xs, by simp [mergeAmounts]⟩
  | x :: xs, y :: ys, hb => by
    simp only [mergeAmounts]
    split
    · obtain ⟨zs,hz⟩ := mergeAmounts_complete xs (y :: ys) (fun k =>
        Nat.lt_of_le_of_lt (Nat.add_le_add_right (amountList_tail_le x xs k) _) (hb k))
      exact ⟨x :: zs, by simp [hz]⟩
    · split
      · obtain ⟨zs,hz⟩ := mergeAmounts_complete (x :: xs) ys (fun k =>
          Nat.lt_of_le_of_lt (Nat.add_le_add_left (amountList_tail_le y ys k) _) (hb k))
        exact ⟨y :: zs, by simp [hz]⟩
      · rename_i hx hy
        have hk : x.1 = y.1 := by simp only [AssetBrand] at *; omega
        have hv : x.2.toNat + y.2.toNat < 2^64 := by
          have := hb x.1
          simp only [amountList, ← hk, ↓reduceIte] at this
          omega
        rw [ite_eq_left hv]
        obtain ⟨zs,hz⟩ := mergeAmounts_complete xs ys (fun k =>
          Nat.lt_of_le_of_lt (Nat.add_le_add (amountList_tail_le x xs k)
            (amountList_tail_le y ys k)) (hb k))
        exact ⟨(x.1, UInt64.ofNat (x.2.toNat + y.2.toNat)) :: zs, by simp [hz]⟩
termination_by xs ys _ => xs.length + ys.length
theorem amountList_bound {xs : List Entry} (hc : Canonical xs) (k : Nat) :
    amountList xs k < 2^64 := by
  by_cases hk : ∃ p ∈ xs, p.1 = k
  · obtain ⟨p,hp,rfl⟩ := hk
    rw [amountList_member hc.1 hp]
    exact p.2.toNat_lt
  · rw [amountList_zero (by grind : ∀ p ∈ xs, p.1 ≠ k)]
    decide
theorem amountList_ext : ∀ {xs ys : List Entry}, Canonical xs → Canonical ys →
    (∀ k, amountList xs k = amountList ys k) → xs = ys
  | [], [], _, _, _ => rfl
  | x :: xs, [], hx, _, h => by
    have := h x.1
    have := hx.2 x (by simp)
    simp [amountList] at *; omega
  | [], y :: ys, _, hy, h => by
    have := h y.1
    have := hy.2 y (by simp)
    simp [amountList] at *; omega
  | x :: xs, y :: ys, ⟨.cons hx sx, px⟩, ⟨.cons hy sy, py⟩, h => by
    have hk : x.1 = y.1 := by
      by_cases hn : x.1 = y.1
      · exact hn
      exfalso
      have hxn := px x (by simp)
      have hyn := py y (by simp)
      rcases Nat.lt_or_gt_of_ne hn with hl | hl
      · have hz : amountList (y :: ys) x.1 = 0 := amountList_zero (by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · simp only [AssetBrand] at *; omega
          · have := hy p hp; simp only [AssetBrand] at *; omega)
        have := h x.1; rw [hz] at this; simp only [amountList, ↓reduceIte] at this; omega
      · have hz : amountList (x :: xs) y.1 = 0 := amountList_zero (by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · simp only [AssetBrand] at *; omega
          · have := hx p hp; simp only [AssetBrand] at *; omega)
        have := h y.1; rw [hz] at this; simp only [amountList, ↓reduceIte] at this; omega
    have hv : x.2 = y.2 := by
      apply UInt64.toNat_inj.mp
      have he := h x.1
      rw [amountList_member (.cons hx sx) (by simp), hk,
        amountList_member (.cons hy sy) (by simp)] at he
      exact he
    have ht : xs = ys := amountList_ext ⟨sx, fun p hp => px p (by simp [hp])⟩
      ⟨sy, fun p hp => py p (by simp [hp])⟩ (fun k => by
        have := h k
        simp only [amountList, hk, hv] at this
        omega)
    rw [Prod.ext hk hv, ht]
theorem AssetBundle.ext {a b : AssetBundle} (h : ∀ k, a.amountSpec k = b.amountSpec k) : a = b := by
  have he := Array.ext' (amountList_ext a.canonical b.canonical h)
  cases a; cases b; cases he; rfl
theorem AssetBundle.addChecked_eq_some_iff_no_overflow_and_sum (a b c : AssetBundle) :
    a.addChecked b = some c ↔
      (∀ k, a.amountSpec k + b.amountSpec k < 2^64) ∧
      (∀ k, c.amountSpec k = a.amountSpec k + b.amountSpec k) := by
  constructor
  · intro h
    have hs := addChecked_sum h
    exact ⟨fun k => hs k ▸ amountList_bound c.canonical k, hs⟩
  · rintro ⟨hb,hs⟩
    obtain ⟨zs,hz⟩ := mergeAmounts_complete a.entries.toList b.entries.toList hb
    unfold addChecked
    split
    · rename_i hn; rw [hz] at hn; contradiction
    · rename_i ws hw
      congr 1
      apply ext
      intro k
      exact (mergeAmounts_sum hw k).trans (hs k).symm
/-! ## 2. `AssetBundle` is the executable refinement of `Obend.Ledger.Proposal`'s asset lists -/
open Obend.Ledger
open Obend.Digest.HashBytes (be ofBE Hash CollisionAmong CollisionPair extractBinding bindingResult be_injective ofBE_lt)
/-- The ledger reading of a bundle: a `give` or `want` list of `Obend.Ledger.Proposal`. -/
def AssetBundle.toPairs (a : AssetBundle) : List (AssetId × Nat) :=
  a.entries.toList.map (fun p => (p.1, p.2.toNat))
theorem assetAmountSum_cons (a : AssetId) (n : Nat) (xs : List (AssetId × Nat)) (k : AssetId) :
    assetAmountSum ((a, n) :: xs) k = (if a = k then n else 0) + assetAmountSum xs k := by
  unfold assetAmountSum
  by_cases h : a = k
  · subst h; simp
  · simp [h]
theorem assetAmountSum_pairs (xs : List Entry) (k : AssetId) :
    assetAmountSum (xs.map (fun p => (p.1, p.2.toNat))) k = amountList xs k := by
  induction xs with
  | nil => simp [assetAmountSum, amountList]
  | cons p xs ih =>
    obtain ⟨b, v⟩ := p
    simp only [List.map_cons, assetAmountSum_cons, ih, amountList]
/-- **Refinement.** The bundle's binary search returns what the ledger's `assetAmountSum` adds up
over the proposal list the bundle stands for. -/
theorem AssetBundle.toPairs_amount (a : AssetBundle) (k : AssetId) :
    assetAmountSum a.toPairs k = a.amountOf k := by
  rw [amountOf_eq_spec]
  exact assetAmountSum_pairs a.entries.toList k
/-- A canonical bundle names each asset once, which is what `Proposal.assetsNodupB` asks. -/
theorem AssetBundle.toPairs_nodup (a : AssetBundle) : (a.toPairs.map Prod.fst).Nodup := by
  unfold AssetBundle.toPairs List.Nodup
  rw [List.map_map, List.pairwise_map]
  exact a.canonical.1.imp (fun h => Nat.ne_of_lt h)
/-- The executable bundle order is the ledger's per-asset order on the lists. -/
theorem AssetBundle.bundleLeq_iff_ledger (a b : AssetBundle) :
    a.bundleLeq b = true ↔ ∀ k, assetAmountSum a.toPairs k ≤ assetAmountSum b.toPairs k := by
  simp only [bundleLeq_iff_forall_brand, toPairs_amount, amountOf_eq_spec]
/-- The checked linear merge adds the ledger amounts asset by asset. -/
theorem AssetBundle.addChecked_ledger {a b c : AssetBundle} (h : a.addChecked b = some c)
    (k : AssetId) :
    assetAmountSum c.toPairs k = assetAmountSum a.toPairs k + assetAmountSum b.toPairs k := by
  simp only [toPairs_amount, amountOf_eq_spec]
  exact addChecked_sum h k
/-- The ledger proposal whose `give` and `want` are the two bundles. -/
def bundleProposal (give want : AssetBundle) (exit : ExitRule) (donate : Bool := false) :
    Proposal :=
  { give := give.toPairs, want := want.toPairs, exit := exit, donate := donate }
theorem bundleProposal_assetsNodup (g w : AssetBundle) (e : ExitRule) (d : Bool) :
    (bundleProposal g w e d).assetsNodupB = true := by
  unfold Proposal.assetsNodupB bundleProposal
  exact decide_eq_true ⟨g.toPairs_nodup, w.toPairs_nodup⟩
/-- A canonical bundle holds no zero entry, so the ledger's zero-want test (the one its donation
guard reads) is emptiness of the `want` bundle. -/
theorem bundleProposal_wantsNothing_iff (g w : AssetBundle) (e : ExitRule) (d : Bool) :
    (bundleProposal g w e d).wantsNothing = true ↔ w.entries.toList = [] := by
  unfold Proposal.wantsNothing bundleProposal AssetBundle.toPairs
  constructor
  · intro h
    cases hl : w.entries.toList with
    | nil => rfl
    | cons p ps =>
      have hp := w.canonical.2 p (by rw [hl]; exact List.mem_cons_self)
      rw [hl] at h
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      exact absurd h.1 (Nat.ne_of_gt hp)
  · intro h
    simp [h]
/-! ## 3. Two books, one set of legs: `FloorBook.admitBatch` gates, the seat `Book` mirrors -/
/-- The typed `FloorBook` address of a `Book` coordinate: ordinary accounts are users, the
protected band is seats, and the band above it is the issuer wells (`issuerWellAccount`). -/
def addrOf (a : AccountId) : AccountAddr :=
  if a < protectedBase then .user a
  else if a < 2 * protectedBase then .seat (a - protectedBase)
  else .issuerWell (a - 2 * protectedBase)
theorem addrOf_injective {a b : Nat} (h : addrOf a = addrOf b) : a = b := by
  unfold addrOf at h
  by_cases ha1 : a < protectedBase <;> by_cases ha2 : a < 2 * protectedBase <;>
    by_cases hb1 : b < protectedBase <;> by_cases hb2 : b < 2 * protectedBase <;>
    simp [ha1, ha2, hb1, hb2, AccountAddr.user, AccountAddr.seat, AccountAddr.issuerWell] at h <;>
    omega
theorem addrOf_inj {a b : AccountId} : addrOf a = addrOf b ↔ a = b :=
  ⟨addrOf_injective, fun h => by rw [h]⟩
theorem addrOf_seat_kind {a : AccountId} (hlo : protectedBase ≤ a) (hhi : a < 2 * protectedBase) :
    (addrOf a).kind ≠ .issuerWell := by
  unfold addrOf
  rw [ite_eq_right (Nat.not_lt.mpr hlo), ite_eq_left hhi]
  intro h; cases h
/-- No `Book` coordinate is a credit-capable `member`, so none holds a credit line
(`FloorBook.policyOf_creditLimit`). -/
theorem addrOf_not_member (a : AccountId) : (addrOf a).kind ≠ .member := by
  unfold addrOf
  split
  · intro h; cases h
  · split <;> (intro h; cases h)
theorem addrOf_user_kind {a : AccountId} (h : a < protectedBase) :
    (addrOf a).kind ≠ .issuerWell := by
  unfold addrOf
  rw [ite_eq_left h]
  intro h; cases h
/-- The same leg on the typed book. -/
def typedPosting (p : ResourcePosting) : TypedPosting :=
  ⟨addrOf p.source, addrOf p.destination, p.asset, p.amount⟩
/-- The seat `Book` and the `FloorBook` hold the same balance at every coordinate. -/
def BooksAgree (fb : FloorBook) (b : Book) : Prop :=
  ∀ (a : AccountId) (ast : AssetId), b.balance a ast = fb.balance (addrOf a) ast
/-- Post one list of legs to both books. The `FloorBook` decides: a leg that would take its
source below its floor refuses the whole batch, and then neither book moves. -/
def postBoth (fb : FloorBook) (b : Book) (ps : List ResourcePosting) : Option (FloorBook × Book) :=
  (fb.admitBatch (ps.map typedPosting)).map (fun fb' => (fb', applyPostings b ps))
theorem admitPosting_eq {fb fb' : FloorBook} {p : TypedPosting}
    (h : fb.admitPosting p = some fb') : fb' = fb.applyRaw p := by
  unfold FloorBook.admitPosting at h
  split at h
  · injection h with h; exact h.symm
  · cases h
theorem agree_applyPosting {fb : FloorBook} {b : Book} (hag : BooksAgree fb b)
    (p : ResourcePosting) : BooksAgree (fb.applyRaw (typedPosting p)) (b.applyPosting p) := by
  intro a ast
  rw [Book.balance_applyPosting, FloorBook.balance_applyRaw, hag a ast]
  simp only [typedPosting, addrOf_inj]
  by_cases hast : ast = p.asset <;> by_cases hs : a = p.source <;>
    by_cases hd : a = p.destination <;> simp [hast, hs, hd]
theorem admitBatch_agree : ∀ (ps : List ResourcePosting) {fb fb' : FloorBook} {b : Book},
    BooksAgree fb b → fb.admitBatch (ps.map typedPosting) = some fb' →
    BooksAgree fb' (applyPostings b ps)
  | [], fb, fb', b, hag, h => by
    simp only [List.map_nil, FloorBook.admitBatch, Option.some.injEq] at h
    subst h; exact hag
  | p :: ps, fb, fb', b, hag, h => by
    rw [List.map_cons] at h
    unfold FloorBook.admitBatch at h
    split at h
    · rename_i fb1 hstep
      rw [applyPostings_cons]
      refine admitBatch_agree ps ?_ h
      rw [admitPosting_eq hstep]
      exact agree_applyPosting hag p
    · cases h
theorem applyPostings_globalAssetSum (ps : List ResourcePosting) (b : Book) (ast : AssetId) :
    (applyPostings b ps).globalAssetSum ast = b.globalAssetSum ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih => rw [applyPostings_cons, ih, Book.applyPosting_conserves_global]
/-- **Posting to both books is sound.** The floors still hold, the books still agree, and every
asset's total is what it was, in the `FloorBook` (`assetSum`) and in the seat `Book`. -/
theorem postBoth_sound {fb fb' : FloorBook} {b b' : Book} {ps : List ResourcePosting}
    (hfl : FloorsHold fb) (hag : BooksAgree fb b) (h : postBoth fb b ps = some (fb', b')) :
    FloorsHold fb' ∧ BooksAgree fb' b' ∧ (∀ ast, fb'.assetSum ast = fb.assetSum ast) ∧
      (∀ ast, b'.globalAssetSum ast = b.globalAssetSum ast) ∧ b' = applyPostings b ps := by
  unfold postBoth at h
  obtain ⟨fb1, hadm, heq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  obtain ⟨hfl', hsum⟩ := FloorBook.admitBatch_preserves_floors _ hfl hadm
  exact ⟨hfl', admitBatch_agree ps hag hadm, hsum, applyPostings_globalAssetSum ps b, rfl⟩
theorem giveEscrow_endpoints {offerer seatAcc : AccountId} {p : Proposal} {q : ResourcePosting}
    (hq : q ∈ giveEscrowPostings offerer seatAcc p) :
    q.source = offerer ∧ q.destination = seatAcc := by
  unfold giveEscrowPostings at hq
  obtain ⟨⟨x, amt⟩, _, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, rfl⟩
theorem payout_endpoints {b : Book} {account payee : AccountId} {assets : List AssetId}
    {q : ResourcePosting} (hq : q ∈ payoutPostings b account payee assets) :
    q.source = account ∧ q.destination = payee := by
  unfold payoutPostings at hq
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, rfl⟩
/-- What escrowing a proposal's `give` does to the seat `Book`: the offeror loses, and the seat
gains, the ledger's per-asset sum of the list. -/
theorem escrow_balance (src dst : AccountId) (hne : src ≠ dst) (p : Proposal) (b : Book)
    (a : AccountId) (ast : AssetId) :
    (applyPostings b (giveEscrowPostings src dst p)).balance a ast =
      b.balance a ast - (if a = src then (assetAmountSum p.give ast : Int) else 0)
        + (if a = dst then (assetAmountSum p.give ast : Int) else 0) := by
  unfold giveEscrowPostings
  generalize p.give = give
  induction give generalizing b with
  | nil => simp [assetAmountSum]
  | cons q rest ih =>
    obtain ⟨x, amt⟩ := q
    simp only [List.map_cons, applyPostings_cons]
    rw [ih, Book.balance_applyPosting, assetAmountSum_cons]
    by_cases h3 : x = ast
    · subst h3
      by_cases h1 : a = src
      · simp [h1, hne] <;> omega
      · by_cases h2 : a = dst
        · simp [h2, Ne.symm hne] <;> omega
        · simp [h1, h2]
    · have h3' : ¬ ast = x := fun h => h3 h.symm
      simp [h3, h3']
/-! ## 4. Holder capabilities: a 256-bit commitment in the host, opened by its preimage -/
/-- The domain tag of holder commitments: `obend.polis.zoe.holder.v1`. -/
def zoeHolderDomain : List UInt8 :=
  [0x6f, 0x62, 0x65, 0x6e, 0x64, 0x2e, 0x70, 0x6f, 0x6c, 0x69, 0x73, 0x2e, 0x7a, 0x6f, 0x65, 0x2e,
    0x68, 0x6f, 0x6c, 0x64, 0x65, 0x72, 0x2e, 0x76, 0x31]
/-- The deployed hash: cSHAKE256 customized by the holder domain. -/
def zoeHash : Hash := Obend.Digest.Cshake256.cshake256Bytes zoeHolderDomain
theorem zoeHash_length (x : List UInt8) : (zoeHash x).length = 32 :=
  Obend.Digest.Cshake256.cshake256Bytes_length _ _
/-- The bytes a holder commits to: the domain tag, the seat id in an eight-byte frame, the
capability's length in an eight-byte frame, the capability. -/
def holderPreimage (seatId : Nat) (cap : List UInt8) : List UInt8 :=
  zoeHolderDomain ++ (be 8 seatId ++ (be 8 cap.length ++ cap))
theorem holderPreimage_injective {s₁ s₂ : Nat} {c₁ c₂ : List UInt8}
    (h₁ : s₁ < 256 ^ 8) (h₂ : s₂ < 256 ^ 8)
    (h : holderPreimage s₁ c₁ = holderPreimage s₂ c₂) : s₁ = s₂ ∧ c₁ = c₂ := by
  unfold holderPreimage at h
  obtain ⟨hs, hrest⟩ := List.append_inj (List.append_cancel_left h) (by simp)
  obtain ⟨_, hc⟩ := List.append_inj hrest (by simp)
  exact ⟨be_injective h₁ h₂ hs, hc⟩
/-- The commitment the host stores for a seat: 256 bits of `H` over the framed preimage. -/
def holderCommit (H : Hash) (seatId : Nat) (cap : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (H (holderPreimage seatId cap)))
/-- **A commitment binds its seat and capability.** Two openings of one commitment are the same
seat and the same capability, or their framed bytes are a collision of `H`. -/
def holderCommit_extract {H : Hash} (hlen : ∀ x, (H x).length = 32) {s₁ s₂ : Nat}
    {c₁ c₂ : List UInt8} (h₁ : s₁ < 256 ^ 8) (h₂ : s₂ < 256 ^ 8)
    (h : holderCommit H s₁ c₁ = holderCommit H s₂ c₂) : PSum (PLift (s₁ = s₂ ∧ c₁ = c₂))
      (CollisionPair H (fun x => x = holderPreimage s₁ c₁ ∨ x = holderPreimage s₂ c₂)) :=
  extractBinding H _ _ (holderPreimage_injective h₁ h₂) (by
    have hb : ∀ x, ofBE (H x) < 2 ^ 256 := fun x => by
      have hlt := ofBE_lt (H x)
      rwa [hlen x, (by decide : (256 : Nat) ^ 32 = 2 ^ 256)] at hlt
    have hn := congrArg BitVec.toNat h
    simp only [holderCommit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb _)] at hn
    exact hn)
theorem holderCommit_binding {H : Hash} (hlen : ∀ x, (H x).length = 32) {s₁ s₂ : Nat}
    {c₁ c₂ : List UInt8} (h₁ : s₁ < 256 ^ 8) (h₂ : s₂ < 256 ^ 8)
    (h : holderCommit H s₁ c₁ = holderCommit H s₂ c₂) : (s₁ = s₂ ∧ c₁ = c₂) ∨
      CollisionAmong H (fun x => x = holderPreimage s₁ c₁ ∨ x = holderPreimage s₂ c₂) :=
  bindingResult (holderCommit_extract hlen h₁ h₂ h)
/-! ## 5. The host over the ledger spine, and its turns -/
/-- The settlement host. `floorBook`, `seatBook`, `invReg` and `seats` are the ledger components
of `Obend.Vault.UnifiedDeosSpine`, by name and type; `seats` holds the live seats. `holders` maps
a live seat's account to the commitment of its holder capability. -/
structure ZoeHost where
  floorBook : FloorBook := {}
  seatBook  : Book := {}
  invReg    : InvitationRegistry := {}
  seats     : List Seat := []
  holders   : List (AccountId × BitVec 256) := []
  epoch     : Nat := 0
  epochKeys : List (BitVec 256) := []
  deriving DecidableEq
def initHost : ZoeHost := {}
/-- Why a turn is refused. -/
inductive ZoeRefusal where
  /-- `Ledger.admitOffer` refused: the donation guard, the invitation, or the offeror's balance -/
  | offer (e : OfferError)
  /-- the offeror or the payee is not an ordinary account -/
  | notOrdinary
  /-- the seat coordinate is out of range or held by a live seat -/
  | seatOccupied
  /-- `FloorBook.admitBatch` refused the escrow: the `give` is not in the offeror's account -/
  | unescrowed
  /-- the funded seat fails `Ledger.safeAt` -/
  | offerUnsafe
  | noSuchSeat
  /-- the presented capability does not open the seat's commitment -/
  | wrongHolder
  | epochUnauthorized
  | exitNotAllowed
  | payoutRefused
  | guestDeclined
  /-- `Ledger.checkBatchReallocSafe` refused, or a leg leaves the invoked seats -/
  | reallocUnsafe
  | reallocFloorRefused
  deriving DecidableEq, Repr
/-- A guest contract sees identity-blind `SeatView`s and proposes legs between seats. -/
abbrev GuestContract := List SeatView → Option BatchRealloc
inductive ZoeTurn where
  | mintInvitation (instanceId : Nat) (description : String)
  | enterOffer (invId : Nat) (offerer payee : AccountId) (seatId : SeatId) (proposal : Proposal)
      (holderCommit : BitVec 256)
  | invokeGuestContract (seatAccounts : List AccountId)
  | exitSeat (seatId : SeatId) (capPreimage : List UInt8)
  | advanceEpoch (capPreimage : List UInt8)
/-- **Entering an offer.** `Ledger.admitOffer` runs on the seat `Book` (donation guard, one-time
invitation, balance), and the same escrow legs must pass `FloorBook.admitBatch` out of the
offeror's typed account. Nothing reaches a seat that was not debited from an account. -/
def enterOffer (h : ZoeHost) (invId : Nat) (offerer payee : AccountId) (seatId : SeatId)
    (p : Proposal) (commit : BitVec 256) : Except ZoeRefusal ZoeHost :=
  if hord : offerer < protectedBase ∧ payee < protectedBase then
    if seatId < 256 ^ 8 ∧ h.seats.all (fun s => s.account != protectedBase + seatId) = true then
      match admitOffer h.invReg h.seatBook invId offerer payee (protectedBase + seatId)
          (Nat.le_add_right _ _)
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le hord.2 (Nat.le_add_right _ _))) p with
      | .error e => .error (.offer e)
      | .ok (reg', b', s) =>
        match h.floorBook.admitBatch
            ((giveEscrowPostings offerer (protectedBase + seatId) p).map typedPosting) with
        | none => .error .unescrowed
        | some fb' =>
          if safeAt b' s.account s.proposal = true then
            .ok { h with
              floorBook := fb', seatBook := b', invReg := reg', seats := s :: h.seats,
              holders := (s.account, commit) :: h.holders }
          else .error .offerUnsafe
    else .error .seatOccupied
  else .error .notOrdinary
def guestInput (h : ZoeHost) (accts : List AccountId) : List SeatView :=
  (h.seats.filter (fun s => accts.contains s.account)).map Seat.view
/-- **Reallocation.** The guest's legs stay among the invoked seats, pass
`Ledger.checkBatchReallocSafe` over every live seat, and pass `FloorBook.admitBatch`. -/
def reallocStep (guest : GuestContract) (h : ZoeHost) (accts : List AccountId) :
    Except ZoeRefusal ZoeHost :=
  match guest (guestInput h accts) with
  | none => .error .guestDeclined
  | some r =>
    if (r.postings.all (fun p => accts.contains p.source && accts.contains p.destination) &&
        checkBatchReallocSafe h.seatBook h.seats r) = true then
      match postBoth h.floorBook h.seatBook r.postings with
      | none => .error .reallocFloorRefused
      | some (fb', b') => .ok { h with floorBook := fb', seatBook := b' }
    else .error .reallocUnsafe
def exitAllowed : ExitRule → Nat → Bool
  | .onDemand, _ => true
  | .afterDeadline due, epoch => decide (due ≤ epoch)
/-- **Exit.** The presented capability must open the seat's stored commitment and the exit rule
must allow it; then `Ledger.exitSeat`'s sweep pays the whole seat to the payee in both books. -/
def exitSeatStep (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8) :
    Except ZoeRefusal ZoeHost :=
  match lookupSeatSpec h.seats (protectedBase + seatId) with
  | none => .error .noSuchSeat
  | some s =>
    if h.holders.lookup s.account = some (holderCommit H seatId cap) then
      if exitAllowed s.proposal.exit h.epoch = true then
        match postBoth h.floorBook h.seatBook
            (payoutPostings h.seatBook s.account s.payee (h.seatBook.heldAssets s.account)) with
        | none => .error .payoutRefused
        | some (fb', b') =>
          .ok { h with
            floorBook := fb', seatBook := b',
            seats := h.seats.filter (fun t => t.account != s.account),
            holders := h.holders.filter (fun e => e.1 != s.account) }
      else .error .exitNotAllowed
    else .error .wrongHolder
/-- Clock tokens occupy a separate domain from seat-holder capabilities. -/
def epochCommit (H : Hash) (epoch : Nat) (cap : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (H (0x45 ::
    (Obend.Crypto.encodeListField (Obend.Crypto.leb128 epoch) ++ Obend.Crypto.encodeListField cap))))

def stepZoeHost (H : Hash) (guest : GuestContract) (h : ZoeHost) :
    ZoeTurn → Except ZoeRefusal ZoeHost
  | .mintInvitation inst desc => .ok { h with invReg := (h.invReg.mint inst desc).1 }
  | .enterOffer invId offerer payee seatId p commit =>
    enterOffer h invId offerer payee seatId p commit
  | .invokeGuestContract accts => reallocStep guest h accts
  | .exitSeat seatId cap => exitSeatStep H h seatId cap
  | .advanceEpoch cap =>
    match h.epochKeys with
    | key :: rest =>
      if key = epochCommit H (h.epoch + 1) cap then
        .ok { h with epoch := h.epoch + 1, epochKeys := rest }
      else .error .epochUnauthorized
    | [] => .error .epochUnauthorized
/-- Every successful tick consumes the next epoch-specific authorization. -/
theorem advanceEpoch_authorized {H : Hash} {guest : GuestContract} {h f : ZoeHost}
    {cap : List UInt8} (he : stepZoeHost H guest h (.advanceEpoch cap) = .ok f) :
    h.epochKeys = epochCommit H (h.epoch + 1) cap :: f.epochKeys ∧ f.epoch = h.epoch + 1 := by
  simp only [stepZoeHost] at he
  split at he
  · split at he
    · rename_i hk; cases he; exact ⟨by simp_all, rfl⟩
    · cases he
  · cases he
/-- No exit rule in this host can permanently delegate recovery to a stalled guest. -/
theorem exitAllowed_eventually (rule : ExitRule) : ∃ due, ∀ epoch, due ≤ epoch →
    exitAllowed rule epoch = true := by
  cases rule with
  | onDemand => exact ⟨0, fun _ _ => rfl⟩
  | afterDeadline due => exact ⟨due, fun _ h => decide_eq_true h⟩
/-- The atomic application boundary retains the entire old state on failure. -/
def applyZoeTurn (H : Hash) (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn) : ZoeHost :=
  match stepZoeHost H guest h t with
  | .ok f => f
  | .error _ => h
def runZoe (H : Hash) (guest : GuestContract) : ZoeHost → List ZoeTurn → ZoeHost
  | h, [] => h
  | h, t :: ts => runZoe H guest (applyZoeTurn H guest h t) ts

/-- A trace: any list of turns, each applied atomically. -/
def ValidZoeTrace (H : Hash) (guest : GuestContract) : ZoeHost → List ZoeTurn → ZoeHost → Prop
  | h, [], f => f = h
  | h, t :: ts, f => ValidZoeTrace H guest (applyZoeTurn H guest h t) ts f

theorem validZoeTrace_iff_run (H : Hash) (guest : GuestContract) (ts : List ZoeTurn) :
    ∀ (h f : ZoeHost), ValidZoeTrace H guest h ts f ↔ f = runZoe H guest h ts := by
  induction ts with
  | nil => intro h f; exact Iff.rfl
  | cons t ts ih => intro h f; exact ih _ f

/-! ## 6. What an accepted turn did -/

theorem admitOffer_ok {reg reg' : InvitationRegistry} {b b' : Book} {invId : Nat}
    {offerer payee seatAcc : AccountId} {h_prot : protectedBase ≤ seatAcc}
    {h_diff : payee ≠ seatAcc} {p : Proposal} {s : Seat}
    (hadm : admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .ok (reg', b', s)) :
    checkDonationGuard p = .ok () ∧ offerer ≠ seatAcc ∧
      b' = applyPostings b (giveEscrowPostings offerer seatAcc p) ∧
      s.account = seatAcc ∧ s.payee = payee ∧ s.proposal = p := by
  unfold admitOffer at hadm
  cases hguard : checkDonationGuard p with
  | error e => rw [hguard] at hadm; cases hadm
  | ok u =>
    rw [hguard] at hadm
    dsimp only [Bind.bind, Except.bind] at hadm
    cases hsp : reg.spend invId with
    | none => rw [hsp] at hadm; cases hadm
    | some pair =>
      rcases pair with ⟨r1, inv⟩
      rw [hsp] at hadm
      by_cases hoff : offerer == seatAcc
      · simp [hoff] at hadm
      · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hadm
        split at hadm
        · cases hadm
        · split at hadm
          next =>
            injection hadm with hp
            have h1 := (Prod.mk.inj hp).2
            have hb := (Prod.mk.inj h1).1
            have hs := (Prod.mk.inj h1).2
            subst hb; subst hs
            exact ⟨rfl, fun he => hoff (by rw [he]; exact beq_self_eq_true _), rfl, rfl, rfl, rfl⟩

          next => cases hadm

/-- Why `Ledger.admitOffer` refuses an ordinary offeror: the donation guard, a spent or unknown
invitation, an uncovered `give` asset, or an unsafe funded seat. -/
theorem admitOffer_error {reg : InvitationRegistry} {b : Book} {invId : Nat}
    {offerer payee seatAcc : AccountId} {h_prot : protectedBase ≤ seatAcc}
    {h_diff : payee ≠ seatAcc} {p : Proposal} {e : OfferError}
    (hadm : admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .error e)
    (hne : offerer ≠ seatAcc) :
    checkDonationGuard p ≠ .ok () ∨ reg.spend invId = none ∨
      (∃ ast, b.balance offerer ast < (assetAmountSum p.give ast : Int)) ∨
      safeAt (applyPostings b (giveEscrowPostings offerer seatAcc p)) seatAcc p = false := by
  unfold admitOffer at hadm
  cases hguard : checkDonationGuard p with
  | error e0 => exact .inl (fun h => by cases h)
  | ok u =>
    rw [hguard] at hadm
    dsimp only [Bind.bind, Except.bind] at hadm
    cases hsp : reg.spend invId with
    | none => exact .inr (.inl rfl)
    | some pair =>
      rcases pair with ⟨r1, inv⟩
      rw [hsp] at hadm
      have hoff : (offerer == seatAcc) = false := beq_eq_false_iff_ne.mpr hne
      simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hadm
      split at hadm
      · rename_i badAst hfind
        exact .inr (.inr (.inl ⟨badAst, by simpa using List.find?_some hfind⟩))
      · split at hadm
        · cases hadm
        · exact .inr (.inr (.inr (by simpa using ‹¬ _ = true›)))

/-- **An accepted offer, taken apart.** -/
theorem enterOffer_ok {h f : ZoeHost} {invId : Nat} {offerer payee : AccountId} {seatId : SeatId}
    {p : Proposal} {commit : BitVec 256}
    (he : enterOffer h invId offerer payee seatId p commit = .ok f) :
    ∃ s : Seat, s.account = protectedBase + seatId ∧ s.payee = payee ∧ s.proposal = p ∧
      offerer < protectedBase ∧ payee < protectedBase ∧ seatId < 256 ^ 8 ∧
      (∀ t ∈ h.seats, t.account ≠ protectedBase + seatId) ∧
      checkDonationGuard p = .ok () ∧
      f.seats = s :: h.seats ∧ f.holders = (s.account, commit) :: h.holders ∧
      f.epoch = h.epoch ∧ f.invReg.spend invId = none ∧
      postBoth h.floorBook h.seatBook (giveEscrowPostings offerer (protectedBase + seatId) p) =
        some (f.floorBook, f.seatBook) ∧
      safeAt f.seatBook s.account s.proposal = true := by
  unfold enterOffer at he
  split at he
  · rename_i hord
    split at he
    · rename_i hfresh
      split at he
      · cases he
      · rename_i reg' b' s hadm
        split at he
        · cases he
        · rename_i fb' hfb
          split at he
          · rename_i hsafe
            injection he with he
            subst he
            obtain ⟨hg, _, hb, hacc, hpay, hprop⟩ := admitOffer_ok hadm
            refine ⟨s, hacc, hpay, hprop, hord.1, hord.2, hfresh.1, ?_, hg, rfl, rfl, rfl,
              admitOffer_spends_invitation_once hadm, ?_, hsafe⟩
            · intro t ht
              have := List.all_eq_true.mp hfresh.2 t ht
              simpa using this
            · rw [postBoth, hfb, hb]; rfl
          · cases he
    · cases he
  · cases he

theorem reallocStep_ok {guest : GuestContract} {h f : ZoeHost} {accts : List AccountId}
    (he : reallocStep guest h accts = .ok f) :
    ∃ r : BatchRealloc, guest (guestInput h accts) = some r ∧
      checkBatchReallocSafe h.seatBook h.seats r = true ∧
      (∀ q ∈ r.postings, q.source ∈ accts ∧ q.destination ∈ accts) ∧
      postBoth h.floorBook h.seatBook r.postings = some (f.floorBook, f.seatBook) ∧
      f.seats = h.seats ∧ f.holders = h.holders ∧ f.invReg = h.invReg ∧ f.epoch = h.epoch := by
  unfold reallocStep at he
  split at he
  · cases he
  · rename_i r hg
    split at he
    · rename_i hchk
      split at he
      · cases he
      · rename_i fb' b' hpost
        injection he with he
        subst he
        rw [Bool.and_eq_true] at hchk
        refine ⟨r, hg, hchk.2, ?_, hpost, rfl, rfl, rfl, rfl⟩
        intro q hq
        have := List.all_eq_true.mp hchk.1 q hq
        simpa using this
    · cases he

theorem exitSeatStep_ok {H : Hash} {h f : ZoeHost} {seatId : SeatId} {cap : List UInt8}
    (he : exitSeatStep H h seatId cap = .ok f) :
    ∃ s : Seat, h.seats.find? (fun s => s.account == protectedBase + seatId) = some s ∧
      h.holders.lookup s.account = some (holderCommit H seatId cap) ∧
      exitAllowed s.proposal.exit h.epoch = true ∧
      postBoth h.floorBook h.seatBook
        (payoutPostings h.seatBook s.account s.payee (h.seatBook.heldAssets s.account)) =
        some (f.floorBook, f.seatBook) ∧
      f.seats = h.seats.filter (fun t => t.account != s.account) ∧
      f.holders = h.holders.filter (fun e => e.1 != s.account) ∧
      f.invReg = h.invReg ∧ f.epoch = h.epoch := by
  unfold exitSeatStep at he
  split at he
  · cases he
  · rename_i s hfind
    split at he
    · rename_i hcap
      split at he
      · rename_i hallow
        split at he
        · cases he
        · rename_i fb' b' hpost
          injection he with he
          subst he
          exact ⟨s, hfind, hcap, hallow, hpost, rfl, rfl, rfl, rfl⟩
      · cases he
    · cases he

/-! ## 7. The invariant, and its preservation along every trace -/

/-- What every reachable host satisfies: the `FloorBook` floors, agreement of the two books,
distinct live seats in the protected band with ordinary payees, and `Ledger.safeAt` on each. -/
def ZoeInv (h : ZoeHost) : Prop :=
  FloorsHold h.floorBook ∧ BooksAgree h.floorBook h.seatBook ∧
  (h.seats.map Seat.account).Nodup ∧
  (∀ s ∈ h.seats, s.account < 2 * protectedBase ∧ s.payee < protectedBase) ∧
  (∀ s ∈ h.seats, safeAt h.seatBook s.account s.proposal = true)

theorem frameBound_lt_protectedBase : 256 ^ 8 < protectedBase := by decide

theorem initHost_invariant : ZoeInv initHost := by
  refine ⟨floorsHold_empty, fun _ _ => by rfl, List.nodup_nil, ?_, ?_⟩ <;>
    (intro s hs; cases hs)

/-- **Every accepted turn keeps the invariant and every asset's total**, in the `FloorBook`
(`assetSum`) and in the seat `Book` (`globalAssetSum`). -/
theorem step_preserves (H : Hash) (guest : GuestContract) {h f : ZoeHost} {t : ZoeTurn}
    (hi : ZoeInv h) (he : stepZoeHost H guest h t = .ok f) :
    ZoeInv f ∧ (∀ ast, f.floorBook.assetSum ast = h.floorBook.assetSum ast) ∧
      (∀ ast, f.seatBook.globalAssetSum ast = h.seatBook.globalAssetSum ast) := by
  obtain ⟨hfl, hag, hnd, hbd, hsafe⟩ := hi
  cases t with
  | mintInvitation inst desc =>
    cases he
    exact ⟨⟨hfl, hag, hnd, hbd, hsafe⟩, fun _ => rfl, fun _ => rfl⟩
  | advanceEpoch cap =>
    simp only [stepZoeHost] at he
    split at he
    · split at he
      · cases he; exact ⟨⟨hfl, hag, hnd, hbd, hsafe⟩, fun _ => rfl, fun _ => rfl⟩
      · cases he
    · cases he
  | enterOffer invId offerer payee seatId p commit =>
    obtain ⟨s, hacc, hpay, hprop, ho, hp, hsid, hfresh, _, hseats, _, _, _, hpost, hsf⟩ :=
      enterOffer_ok (show enterOffer h invId offerer payee seatId p commit = .ok f from he)
    obtain ⟨hfl', hag', hc1, hc2, hb'⟩ := postBoth_sound hfl hag hpost
    refine ⟨⟨hfl', hag', ?_, ?_, ?_⟩, hc1, hc2⟩
    · rw [hseats, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨t, ht, hta⟩ := List.mem_map.mp hm
      exact hfresh t ht (hta.trans hacc)
    · intro t ht
      rw [hseats] at ht
      rcases List.mem_cons.mp ht with heq | ht
      · rw [heq, hacc, hpay, Nat.two_mul]
        exact ⟨Nat.add_lt_add_left (Nat.lt_trans hsid frameBound_lt_protectedBase) _, hp⟩
      · exact hbd t ht
    · intro t ht
      rw [hseats] at ht
      rcases List.mem_cons.mp ht with heq | ht
      · rw [heq]; exact hsf
      · refine safeAt_mono (fun ast => Int.le_of_eq ?_) (hsafe t ht)
        rw [hb']
        refine (applyPostings_balance_other_account _ _ _ _ fun q hq => ?_).symm
        obtain ⟨hqs, hqd⟩ := giveEscrow_endpoints hq
        rw [hqs, hqd]
        exact ⟨fun e => ordinary_ne_seat_account t ho e.symm, hfresh t ht⟩
  | invokeGuestContract accts =>
    obtain ⟨r, _, hchk, _, hpost, hseats, _, _, _⟩ :=
      reallocStep_ok (show reallocStep guest h accts = .ok f from he)
    obtain ⟨hfl', hag', hc1, hc2, hb'⟩ := postBoth_sound hfl hag hpost
    refine ⟨⟨hfl', hag', hseats ▸ hnd, hseats ▸ hbd, ?_⟩, hc1, hc2⟩
    intro t ht
    rw [hseats] at ht
    rw [hb']
    exact batchRealloc_preserves_all_seats_offer_safe h.seatBook h.seats r hchk t ht
  | exitSeat seatId cap =>
    obtain ⟨s, hfind, _, _, hpost, hseats, _, _, _⟩ :=
      exitSeatStep_ok (show exitSeatStep H h seatId cap = .ok f from he)
    have hs : s ∈ h.seats := List.mem_of_find?_eq_some hfind
    obtain ⟨hfl', hag', hc1, hc2, hb'⟩ := postBoth_sound hfl hag hpost
    refine ⟨⟨hfl', hag', ?_, ?_, ?_⟩, hc1, hc2⟩
    · rw [hseats]
      exact List.Nodup.sublist (List.filter_sublist.map _) hnd
    · intro t ht
      rw [hseats] at ht
      exact hbd t (List.mem_filter.mp ht).1
    · intro t ht
      rw [hseats] at ht
      obtain ⟨htm, hne⟩ := List.mem_filter.mp ht
      refine safeAt_mono (fun ast => Int.le_of_eq ?_) (hsafe t htm)
      rw [hb']
      refine (applyPostings_balance_other_account _ _ _ _ fun q hq => ?_).symm
      obtain ⟨hqs, hqd⟩ := payout_endpoints hq
      rw [hqs, hqd]
      exact ⟨by simpa using hne, (ordinary_ne_seat_account t (hbd s hs).2).symm⟩

theorem applyZoeTurn_preserves (H : Hash) (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn)
    (hi : ZoeInv h) :
    ZoeInv (applyZoeTurn H guest h t) ∧
      (∀ ast, (applyZoeTurn H guest h t).floorBook.assetSum ast = h.floorBook.assetSum ast) ∧
      (∀ ast, (applyZoeTurn H guest h t).seatBook.globalAssetSum ast =
        h.seatBook.globalAssetSum ast) := by
  unfold applyZoeTurn
  cases he : stepZoeHost H guest h t with
  | error e => exact ⟨hi, fun _ => rfl, fun _ => rfl⟩
  | ok f => exact step_preserves H guest hi he

/-- **The trace invariant.** Along any trace, of any length, under any guest and any hash: the
invariant holds at the end, and every asset's total is what it was at the start, in the
`FloorBook` and in the seat `Book`. No turn mints and no turn burns. -/
theorem trace_invariant (H : Hash) (guest : GuestContract) (ts : List ZoeTurn) :
    ∀ (h f : ZoeHost), ZoeInv h → ValidZoeTrace H guest h ts f →
      ZoeInv f ∧ (∀ ast, f.floorBook.assetSum ast = h.floorBook.assetSum ast) ∧
        (∀ ast, f.seatBook.globalAssetSum ast = h.seatBook.globalAssetSum ast) := by
  induction ts with
  | nil =>
    intro h f hi ht
    have ht : f = h := ht
    subst ht
    exact ⟨hi, fun _ => rfl, fun _ => rfl⟩
  | cons t ts ih =>
    intro h f hi ht
    obtain ⟨hi1, hc1, hg1⟩ := applyZoeTurn_preserves H guest h t hi
    obtain ⟨hif, hc, hg⟩ := ih _ f hi1 ht
    exact ⟨hif, fun ast => (hc ast).trans (hc1 ast), fun ast => (hg ast).trans (hg1 ast)⟩

/-- The legs that fund ordinary accounts out of the issuer wells. -/
def grantPostings (grants : List (AccountId × AssetId × Nat)) : List ResourcePosting :=
  grants.map (fun g => ⟨issuerWellAccount g.2.1, g.1, g.2.1, g.2.2⟩)

/-- A genesis: both books funded by the same grants, no seat yet. -/
def fundedHost (grants : List (AccountId × AssetId × Nat)) : ZoeHost :=
  match postBoth FloorBook.empty Book.empty (grantPostings grants) with
  | some (fb, b) => { floorBook := fb, seatBook := b }
  | none => {}

theorem fundedHost_invariant (grants : List (AccountId × AssetId × Nat)) :
    ZoeInv (fundedHost grants) := by
  unfold fundedHost
  split
  · rename_i fb b hpost
    obtain ⟨hfl, hag, _, _, _⟩ :=
      postBoth_sound floorsHold_empty (fun _ _ => by rfl) hpost
    refine ⟨hfl, hag, List.nodup_nil, ?_, ?_⟩ <;> (intro s hs; cases hs)
  · exact initHost_invariant

/-- **Offer safety over the ledger, from any funded genesis.** No hypothesis constrains the
guest, the hash or the number of turns: the floors hold, every asset's `FloorBook` total is the
genesis total, every live seat passes `Ledger.safeAt`, and every live seat's escrow is a
non-negative `FloorBook` balance on every asset. -/
theorem zoe_offer_safety_unconditional (H : Hash) (guest : GuestContract)
    (grants : List (AccountId × AssetId × Nat)) (turns : List ZoeTurn) (f : ZoeHost)
    (ht : ValidZoeTrace H guest (fundedHost grants) turns f) :
    FloorsHold f.floorBook ∧
    (∀ ast, f.floorBook.assetSum ast = (fundedHost grants).floorBook.assetSum ast) ∧
    (∀ s ∈ f.seats, safeAt f.seatBook s.account s.proposal = true) ∧
    (∀ s ∈ f.seats, ∀ ast, 0 ≤ f.floorBook.balance (addrOf s.account) ast) := by
  obtain ⟨⟨hfl, _, _, hbd, hsafe⟩, hc, _⟩ :=
    trace_invariant H guest turns _ f (fundedHost_invariant grants) ht
  exact ⟨hfl, hc, hsafe, fun s hs ast =>
    nonIssuer_balance_nonneg_of_floorsHold hfl _ ast (addrOf_seat_kind s.h_protected (hbd s hs).1)
      (addrOf_not_member _)⟩

/-! ## 8. What entering, reallocating and exiting do to the `FloorBook` -/

/-- **An accepted offer is escrowed out of the offeror's `FloorBook` account.** For every asset
the offeror's typed account is debited the proposal's `give`, the seat's is credited the same,
and the offeror held at least that much: no offer is funded from thin air. The donation guard
passed and the invitation is spent. -/
theorem enterOffer_escrows {h f : ZoeHost} {invId : Nat} {offerer payee : AccountId}
    {seatId : SeatId} {p : Proposal} {commit : BitVec 256} (hi : ZoeInv h)
    (he : enterOffer h invId offerer payee seatId p commit = .ok f) (ast : AssetId) :
    f.floorBook.balance (addrOf offerer) ast =
      h.floorBook.balance (addrOf offerer) ast - (assetAmountSum p.give ast : Int) ∧
    f.floorBook.balance (addrOf (protectedBase + seatId)) ast =
      h.floorBook.balance (addrOf (protectedBase + seatId)) ast + (assetAmountSum p.give ast : Int) ∧
    (assetAmountSum p.give ast : Int) ≤ h.floorBook.balance (addrOf offerer) ast ∧
    checkDonationGuard p = .ok () ∧ f.invReg.spend invId = none := by
  obtain ⟨hfl, hag, _, _, _⟩ := hi
  obtain ⟨s, _, _, _, ho, _, _, _, hg, _, _, _, hspent, hpost, _⟩ := enterOffer_ok he
  obtain ⟨hfl', hag', _, _, hb'⟩ := postBoth_sound hfl hag hpost
  have hne : offerer ≠ protectedBase + seatId :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le ho (Nat.le_add_right _ _))
  have h1 : f.floorBook.balance (addrOf offerer) ast =
      h.floorBook.balance (addrOf offerer) ast - (assetAmountSum p.give ast : Int) := by
    rw [← hag' offerer ast, hb', escrow_balance _ _ hne, hag offerer ast]
    simp [hne]
  have h2 : f.floorBook.balance (addrOf (protectedBase + seatId)) ast =
      h.floorBook.balance (addrOf (protectedBase + seatId)) ast +
        (assetAmountSum p.give ast : Int) := by
    rw [← hag' (protectedBase + seatId) ast, hb', escrow_balance _ _ hne,
      hag (protectedBase + seatId) ast]
    simp [Ne.symm hne]
  have h0 := nonIssuer_balance_nonneg_of_floorsHold hfl' (addrOf offerer) ast (addrOf_user_kind ho)
    (addrOf_not_member offerer)
  exact ⟨h1, h2, by omega, hg, hspent⟩

/-- An unmarked donation (zero `want`, `donate = false`) is refused by name, whatever the books
hold: `Ledger.admitOffer_donationUnmarked_refused`, through the host. -/
theorem enterOffer_donationUnmarked_refused (h : ZoeHost) (invId : Nat)
    (offerer payee : AccountId) (seatId : SeatId) (p : Proposal) (commit : BitVec 256)
    (hord : offerer < protectedBase ∧ payee < protectedBase)
    (hfresh : seatId < 256 ^ 8 ∧
      h.seats.all (fun s => s.account != protectedBase + seatId) = true)
    (hwant0 : p.wantsNothing = true) (hdon : p.donate = false) :
    enterOffer h invId offerer payee seatId p commit = .error (.offer .donationUnmarked) := by
  unfold enterOffer
  rw [dite_eq_left hord, ite_eq_left hfresh,
    admitOffer_donationUnmarked_refused _ _ _ _ _ _ _ _ p hwant0 hdon]

/-- **Exit pays the whole seat to its payee in the `FloorBook`.** The seat's typed account is
left at zero on every asset, the payee's gains exactly what the seat held, and the seat is gone
from the live seats. -/
theorem exit_pays_payee {H : Hash} {h f : ZoeHost} {seatId : SeatId} {cap : List UInt8}
    (hi : ZoeInv h) (he : exitSeatStep H h seatId cap = .ok f) :
    ∃ s ∈ h.seats, s.account = protectedBase + seatId ∧
      (∀ ast, f.floorBook.balance (addrOf s.account) ast = 0) ∧
      (∀ ast, f.floorBook.balance (addrOf s.payee) ast =
        h.floorBook.balance (addrOf s.payee) ast + h.floorBook.balance (addrOf s.account) ast) ∧
      (∀ t ∈ f.seats, t.account ≠ s.account) := by
  obtain ⟨hfl, hag, _, hbd, _⟩ := hi
  obtain ⟨s, hfind, _, _, hpost, hseats, _, _, _⟩ := exitSeatStep_ok he
  have hs : s ∈ h.seats := List.mem_of_find?_eq_some hfind
  have hacc : s.account = protectedBase + seatId := by
    simpa using List.find?_some hfind
  obtain ⟨_, hag', _, _, hb'⟩ := postBoth_sound hfl hag hpost
  have hnn : ∀ ast, 0 ≤ h.seatBook.balance s.account ast := fun ast => by
    rw [hag s.account ast]
    exact nonIssuer_balance_nonneg_of_floorsHold hfl _ ast
      (addrOf_seat_kind s.h_protected (hbd s hs).1) (addrOf_not_member _)
  obtain ⟨hzero, hpaid, _⟩ := exit_sweeps_all_assets h.seatBook s hnn
  have hb'' : f.seatBook = exitSeat h.seatBook s := hb'
  refine ⟨s, hs, hacc, fun ast => ?_, fun ast => ?_, fun t ht => ?_⟩
  · rw [← hag' s.account ast, hb'']; exact hzero ast
  · rw [← hag' s.payee ast, hb'', hpaid ast, hag s.payee ast, hag s.account ast]
  · rw [hseats] at ht
    simpa using (List.mem_filter.mp ht).2

/-- **Only the holder exits.** If a seat's stored commitment was made from `cap₀`, a capability
that exits the seat is `cap₀`, or the two framed openings are a collision of `H`. -/
theorem exit_requires_holder_preimage {H : Hash} (hlen : ∀ x, (H x).length = 32)
    {h f : ZoeHost} {seatId : SeatId} {cap cap₀ : List UInt8} (hsid : seatId < 256 ^ 8)
    (hstored : h.holders.lookup (protectedBase + seatId) = some (holderCommit H seatId cap₀))
    (he : exitSeatStep H h seatId cap = .ok f) : cap = cap₀ ∨ CollisionAmong H
      (fun x => x = holderPreimage seatId cap ∨ x = holderPreimage seatId cap₀) := by
  obtain ⟨s, hfind, hcap, _, _, _, _, _, _⟩ := exitSeatStep_ok he
  have hacc : s.account = protectedBase + seatId := by
    simpa using List.find?_some hfind
  rw [hacc, hstored] at hcap
  exact (holderCommit_binding hlen hsid hsid (Option.some.inj hcap).symm).imp_left (·.2)

/-- **A guest moves nothing outside the invoked seats.** Every ordinary account's balance is
unchanged in both books, and the legs' endpoints are among the invoked accounts. -/
theorem realloc_leaves_ordinary_untouched {guest : GuestContract} {h f : ZoeHost}
    {accts : List AccountId} (hi : ZoeInv h) (he : reallocStep guest h accts = .ok f)
    (u : AccountId) (hu : u < protectedBase) (ast : AssetId) :
    f.floorBook.balance (addrOf u) ast = h.floorBook.balance (addrOf u) ast ∧
      f.seatBook.balance u ast = h.seatBook.balance u ast := by
  obtain ⟨hfl, hag, _, _, _⟩ := hi
  obtain ⟨r, _, hchk, _, hpost, _, _, _, _⟩ := reallocStep_ok he
  obtain ⟨_, hag', _, _, hb'⟩ := postBoth_sound hfl hag hpost
  have hbal : f.seatBook.balance u ast = h.seatBook.balance u ast := by
    rw [hb']
    exact batchRealloc_disjoint_from_ordinary_accounts h.seatBook h.seats r hchk u hu ast
  exact ⟨by rw [← hag' u ast, hbal, hag u ast], hbal⟩

/-! ## 9. Refusal is complete -/

def ExitViolation (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8) : Prop :=
  match lookupSeatSpec h.seats (protectedBase + seatId) with
  | none => True
  | some s =>
    h.holders.lookup s.account ≠ some (holderCommit H seatId cap) ∨
    exitAllowed s.proposal.exit h.epoch = false ∨
    h.floorBook.admitBatch ((payoutPostings h.seatBook s.account s.payee
      (h.seatBook.heldAssets s.account)).map typedPosting) = none

/-- An exit is refused exactly when there is no such live seat, the capability does not open its
commitment, its exit rule does not allow it yet, or the `FloorBook` refuses the payout. -/
theorem exitSeatStep_refused_iff (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8) :
    (∃ e, exitSeatStep H h seatId cap = .error e) ↔ ExitViolation H h seatId cap := by
  unfold exitSeatStep ExitViolation lookupSeatSpec
  cases hf : h.seats.find? (fun s => s.account == protectedBase + seatId) with
  | none => simp
  | some s =>
    by_cases hc : h.holders.lookup s.account = some (holderCommit H seatId cap)
    · cases ha : exitAllowed s.proposal.exit h.epoch with
      | false => simp [hc, ha]
      | true =>
        cases hb : h.floorBook.admitBatch ((payoutPostings h.seatBook s.account s.payee
            (h.seatBook.heldAssets s.account)).map typedPosting) with
        | none => simp [hc, ha, postBoth, hb]
        | some fb' => simp [hc, ha, postBoth, hb]
    · simp [hc]

/-- A seat whose exit rule names a deadline is not exited before it, whatever is presented. -/
theorem premature_exit_refused (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8)
    (s : Seat) (due : Nat)
    (hf : h.seats.find? (fun s => s.account == protectedBase + seatId) = some s)
    (hw : s.proposal.exit = .afterDeadline due) (he : h.epoch < due) :
    ∃ e, exitSeatStep H h seatId cap = .error e := by
  refine (exitSeatStep_refused_iff H h seatId cap).mpr ?_
  simp only [ExitViolation, lookupSeatSpec, hf]
  exact .inr (.inl (by rw [hw]; exact decide_eq_false (Nat.not_le.mpr he)))

/-- The contract a refused turn broke. Minting an invitation and advancing the epoch break none. -/
def ZoeStepViolation (H : Hash) (guest : GuestContract) (h : ZoeHost) : ZoeTurn → Prop
  | .mintInvitation _ _ => False
  | .advanceEpoch cap =>
    h.epochKeys.head? ≠ some (epochCommit H (h.epoch + 1) cap)
  | .exitSeat seatId cap => ExitViolation H h seatId cap
  | .invokeGuestContract accts =>
    match guest (guestInput h accts) with
    | none => True
    | some r =>
      (r.postings.all (fun p => accts.contains p.source && accts.contains p.destination) &&
        checkBatchReallocSafe h.seatBook h.seats r) = false ∨
      h.floorBook.admitBatch (r.postings.map typedPosting) = none
  | .enterOffer invId offerer payee seatId p _ =>
    ¬ (offerer < protectedBase ∧ payee < protectedBase) ∨
    ¬ (seatId < 256 ^ 8 ∧ h.seats.all (fun s => s.account != protectedBase + seatId) = true) ∨
    checkDonationGuard p ≠ .ok () ∨ h.invReg.spend invId = none ∨
    (∃ ast, h.seatBook.balance offerer ast < (assetAmountSum p.give ast : Int)) ∨
    h.floorBook.admitBatch
      ((giveEscrowPostings offerer (protectedBase + seatId) p).map typedPosting) = none ∨
    safeAt (applyPostings h.seatBook (giveEscrowPostings offerer (protectedBase + seatId) p))
      (protectedBase + seatId) p = false

/-- **A skipped turn broke its contract.** Every refusal is one of the named violations: the
step function declines nothing it could have run. -/
theorem zoeStep_skip_implies_violation (H : Hash) (guest : GuestContract) (h : ZoeHost)
    (t : ZoeTurn) :
    (∃ e, stepZoeHost H guest h t = .error e) → ZoeStepViolation H guest h t := by
  rintro ⟨e, he⟩
  cases t with
  | mintInvitation inst desc => cases he
  | advanceEpoch cap =>
    simp only [stepZoeHost] at he
    cases hk : h.epochKeys with
    | nil => simp [ZoeStepViolation, hk]
    | cons key rest =>
      simp only [hk] at he
      split at he
      · cases he
      · simpa [ZoeStepViolation, hk] using ‹key ≠ epochCommit H (h.epoch + 1) cap›
  | exitSeat seatId cap => exact (exitSeatStep_refused_iff H h seatId cap).mp ⟨e, he⟩
  | invokeGuestContract accts =>
    have he : reallocStep guest h accts = .error e := he
    unfold reallocStep at he
    simp only [ZoeStepViolation]
    cases hg : guest (guestInput h accts) with
    | none => trivial
    | some r =>
      rw [hg] at he
      dsimp only at he ⊢
      cases hchk : (r.postings.all (fun p => accts.contains p.source &&
          accts.contains p.destination) && checkBatchReallocSafe h.seatBook h.seats r) with
      | false => exact .inl rfl
      | true =>
        cases hb : h.floorBook.admitBatch (r.postings.map typedPosting) with
        | none => exact .inr rfl
        | some fb' =>
          rw [ite_eq_left hchk] at he
          simp [postBoth, hb] at he
  | enterOffer invId offerer payee seatId p commit =>
    have he : enterOffer h invId offerer payee seatId p commit = .error e := he
    simp only [ZoeStepViolation]
    by_cases hord : offerer < protectedBase ∧ payee < protectedBase
    · by_cases hfresh : seatId < 256 ^ 8 ∧
          h.seats.all (fun s => s.account != protectedBase + seatId) = true
      · refine .inr (.inr ?_)
        have hne : offerer ≠ protectedBase + seatId :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le hord.1 (Nat.le_add_right _ _))
        unfold enterOffer at he
        rw [dite_eq_left hord, ite_eq_left hfresh] at he
        split at he
        · rename_i e' hadm
          rcases admitOffer_error hadm hne with h1 | h1 | h1 | h1
          · exact .inl h1
          · exact .inr (.inl h1)
          · exact .inr (.inr (.inl h1))
          · exact .inr (.inr (.inr (.inr h1)))
        · rename_i reg' b' s hadm
          obtain ⟨_, _, hb, hacc, _, hprop⟩ := admitOffer_ok hadm
          refine .inr (.inr (.inr ?_))
          split at he
          · rename_i hfb
            exact .inl hfb
          · split at he
            · cases he
            · rename_i hsf
              rw [hb, hacc, hprop] at hsf
              exact .inr (by simpa using hsf)
      · exact .inr (.inl hfresh)
    · exact .inl hord

/-- Two distinct live seats are reachable from a funded genesis: the harness is not a singleton. -/
theorem two_live_seats_inhabited :
    ∃ h, ValidZoeTrace zoeHash (fun _ => none) (fundedHost [(1, 0, 5), (2, 1, 5)])
        [.mintInvitation 0 "otc", .mintInvitation 0 "otc",
          .enterOffer 0 1 1 0 ⟨[(0, 5)], [(1, 5)], .onDemand, false, {}⟩ 11#256,
          .enterOffer 1 2 2 1 ⟨[(1, 5)], [(0, 5)], .onDemand, false, {}⟩ 12#256] h ∧
      h.seats.length = 2 ∧ ZoeInv h :=
  ⟨_, (validZoeTrace_iff_run _ _ _ _ _).mpr rfl, by decide +kernel,
    (trace_invariant _ _ _ _ _ (fundedHost_invariant _)
      ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)).1⟩

example : ∀ x, (zoeHash x).length = 32 := zoeHash_length
example : BooksAgree FloorBook.empty Book.empty := fun _ _ => by rfl


/-! ## 10. A reallocation as a conserved value of `Obend.Logic.SeparationFrame` -/

namespace DeltaNormalization
open Obend.Logic

/-- Explicit decidable integer equality keeps witness construction constructive. -/
def insert (k : Nat) (d : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => if d = 0 then [] else [(k, d)]
  | (k', d') :: xs =>
    if k < k' then if d = 0 then (k', d') :: xs else (k, d) :: (k', d') :: xs
    else if k' < k then (k', d') :: insert k d xs
    else if d + d' = 0 then xs else (k', d + d') :: xs

theorem insert_keys {k : Nat} {d : Int} :
    ∀ {xs : List (Nat × Int)} {p : Nat × Int},
      p ∈ insert k d xs → p.1 = k ∨ ∃ d₀, (p.1, d₀) ∈ xs
  | [], p, hp => by
    simp only [insert] at hp; split at hp; · cases hp
    simp only [List.mem_singleton] at hp; subst hp; exact Or.inl rfl
  | (k', d') :: xs, p, hp => by
    simp only [insert] at hp
    split at hp
    · split at hp
      · exact Or.inr ⟨p.2, hp⟩
      · rcases List.mem_cons.1 hp with rfl | hm; exact Or.inl rfl; exact Or.inr ⟨p.2, hm⟩
    · split at hp
      · rcases List.mem_cons.1 hp with rfl | hm
        · exact Or.inr ⟨d', List.mem_cons_self⟩
        · exact (insert_keys hm).imp id fun ⟨d₀, h₀⟩ => ⟨d₀, List.mem_cons_of_mem _ h₀⟩
      · split at hp
        · exact Or.inr ⟨p.2, List.mem_cons_of_mem _ hp⟩
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact Or.inr ⟨d', List.mem_cons_self⟩
          · exact Or.inr ⟨p.2, List.mem_cons_of_mem _ hm⟩

theorem insert_nonZeroSorted (k : Nat) (d : Int) :
    ∀ {xs : List (Nat × Int)}, NonZeroSorted xs → NonZeroSorted (insert k d xs)
  | [], _ => by
    simp only [insert]
    by_cases hd : d = 0
    · simp [hd, NonZeroSorted]
    · simp only [hd, ↓reduceIte, NonZeroSorted]
      refine ⟨.cons (fun _ h => by cases h) .nil, fun p hp => ?_⟩
      simp only [List.mem_singleton] at hp; subst hp
      exact fun hz => absurd (hz) hd
  | (k', d') :: xs, ⟨.cons hgt hs, hnz⟩ => by
    have htail : NonZeroSorted xs := ⟨hs, fun p hp => hnz p (List.mem_cons_of_mem _ hp)⟩
    simp only [insert]
    by_cases hlt : k < k'
    · simp only [hlt, ↓reduceIte]
      by_cases hd : d = 0
      · simp [hd]; exact ⟨.cons hgt hs, hnz⟩
      · simp only [hd, ↓reduceIte]
        refine ⟨.cons (fun p hp => ?_) (.cons hgt hs), fun p hp => ?_⟩
        · rcases List.mem_cons.1 hp with rfl | hm; exact hlt; exact Nat.lt_trans hlt (hgt p hm)
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact fun hz => absurd (hz) hd
          · exact hnz p hm
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte]
        obtain ⟨hs_rec, hnz_rec⟩ := insert_nonZeroSorted k d htail
        refine ⟨.cons (fun p hp => ?_) hs_rec, fun p hp => ?_⟩
        · rcases insert_keys hp with hpk | ⟨d₀, h₀⟩
          · rw [hpk]; exact hgt'
          · exact hgt (p.1, d₀) h₀
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact hnz (k', d') List.mem_cons_self
          · exact hnz_rec p hm
      · simp only [hlt, hgt', ↓reduceIte]
        by_cases hsum : d + d' = 0
        · simp [hsum]; exact htail
        · simp only [hsum, ↓reduceIte]
          refine ⟨.cons hgt hs, fun p hp => ?_⟩
          rcases List.mem_cons.1 hp with rfl | hm
          · exact fun hz => absurd (hz) hsum
          · exact htail.2 p hm

theorem deltaAt_insert (k : Nat) (d : Int) :
    ∀ {xs : List (Nat × Int)}, NonZeroSorted xs →
      ∀ q : Nat, deltaAt (insert k d xs) q = (if q == k then d else 0) + deltaAt xs q
  | [], _, q => by
    simp only [insert]
    by_cases hd : d = 0
    · rw [hd]; simp [deltaAt]
    · simp only [hd, ↓reduceIte, deltaAt]; by_cases hqk : q == k <;> simp [hqk]
  | (k', d') :: xs, ⟨.cons hgt hs, hnz⟩, q => by
    have htail : NonZeroSorted xs := ⟨hs, fun p hp => hnz p (List.mem_cons_of_mem _ hp)⟩
    simp only [insert]
    by_cases hlt : k < k'
    · simp only [hlt, ↓reduceIte]
      by_cases hd : d = 0
      · simp [hd]
      · simp only [hd, ↓reduceIte, deltaAt]
        by_cases hqk : q == k
        · have hqeq : q = k := eq_of_beq hqk
          have hqk' : (q == k') = false := beq_false_of_ne (by omega)
          have hz : deltaAt xs q = 0 := deltaAt_zero_of_forall_gt fun p hp => by
            have := hgt p hp; omega
          simp [hqk, hqk', hz]
        · simp [hqk]
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte, deltaAt]
        by_cases hqk' : q == k'
        · have hqk_f : (q == k) = false := beq_false_of_ne (by have := eq_of_beq hqk'; omega)
          simp [hqk', hqk_f]
        · simp [hqk', deltaAt_insert k d htail q]
      · have hkeq : k = k' := by omega
        subst hkeq; simp only [hlt, ↓reduceIte]
        by_cases hsum : d + d' = 0
        · simp only [hsum, ↓reduceIte]
          have hz : d + d' = 0 := hsum
          by_cases hqk : q == k
          · have hqeq : q = k := eq_of_beq hqk; subst hqeq
            simp [deltaAt, deltaAt_zero_of_forall_gt hgt]; omega
          · simp [deltaAt, hqk]
        · simp only [hsum, ↓reduceIte, deltaAt]
          by_cases hqk : q == k <;> simp [hqk]

theorem sumDeltas_insert (k : Nat) (d : Int) :
    ∀ (xs : List (Nat × Int)), sumDeltas (insert k d xs) = d + sumDeltas xs
  | [] => by
    simp only [insert]
    by_cases hd : d = 0
    · simp [hd, sumDeltas]
    · simp [hd, sumDeltas]
  | (k', d') :: xs => by
    simp only [insert]
    by_cases hlt : k < k'
    · by_cases hd : d = 0 <;> simp [hlt, hd, sumDeltas]
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte, sumDeltas, sumDeltas_insert k d xs]; omega
      · simp only [hlt, hgt', ↓reduceIte]
        by_cases hsum : d + d' = 0
        · have := hsum; simp only [hsum, ↓reduceIte, sumDeltas]; omega
        · simp only [hsum, ↓reduceIte, sumDeltas]; omega

end DeltaNormalization

open Obend.Logic in
/-- Normalize actual signed per-seat allocation changes, removing zero entries. -/
def normalizedDeltas (ds : List (Nat × Int)) : List (Nat × Int) :=
  ds.foldr (fun p acc => DeltaNormalization.insert p.1 p.2 acc) []

open Obend.Logic in
theorem normalizedDeltas_wf (ds : List (Nat × Int)) : NonZeroSorted (normalizedDeltas ds) := by
  induction ds with
  | nil => exact ⟨.nil, by simp [normalizedDeltas]⟩
  | cons p ds ih => exact DeltaNormalization.insert_nonZeroSorted p.1 p.2 ih

open Obend.Logic in
theorem normalizedDeltas_sum (ds : List (Nat × Int)) :
    sumDeltas (normalizedDeltas ds) = (ds.map Prod.snd).sum := by
  induction ds with
  | nil => rfl
  | cons p ds ih =>
    change sumDeltas (DeltaNormalization.insert p.1 p.2 (normalizedDeltas ds)) = _
    rw [DeltaNormalization.sumDeltas_insert, ih]
    rfl

open Obend.Logic in
theorem normalizedDeltas_at (ds : List (Nat × Int)) (q : Nat) :
    deltaAt (normalizedDeltas ds) q =
      (ds.map (fun p => if q == p.1 then p.2 else 0)).sum := by
  induction ds with
  | nil => rfl
  | cons p ds ih =>
    change deltaAt (DeltaNormalization.insert p.1 p.2 (normalizedDeltas ds)) q = _
    rw [DeltaNormalization.deltaAt_insert _ _ (normalizedDeltas_wf ds), ih]
    rfl

/-- The signed account deltas of the legs in asset `ast`: each leg debits its source and credits
its destination. -/
def postingDeltas (ps : List ResourcePosting) (ast : AssetId) : List (Nat × Int) :=
  (ps.filter (fun p => p.asset == ast)).flatMap
    (fun p => [(p.source, -(p.amount : Int)), (p.destination, (p.amount : Int))])

theorem postingDeltas_sum (ps : List ResourcePosting) (ast : AssetId) :
    ((postingDeltas ps ast).map Prod.snd).sum = 0 := by
  unfold postingDeltas
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.asset = ast
    · simp only [List.filter_cons, h, beq_self_eq_true, ↓reduceIte, List.flatMap_cons,
        List.map_append, List.sum_append, ih, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    · have hb : (p.asset == ast) = false := beq_eq_false_iff_ne.mpr h
      simp only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte, ih]

/-- A reallocation's legs in one asset, normalized: a `ConservedValue` (sorted accounts, no zero
entry, deltas summing to zero). -/
def reallocConservedValue (r : BatchRealloc) (ast : AssetId) : Obend.Logic.ConservedValue where
  entries := normalizedDeltas (postingDeltas r.postings ast)
  wf := normalizedDeltas_wf _
  conserved := by rw [normalizedDeltas_sum, postingDeltas_sum]

/-- Every account delta of the conserved value is the exact sum of the legs that touch it. -/
theorem conservation_bridges_separationFrame (r : BatchRealloc) (ast : AssetId) :
    ∀ q, Obend.Logic.deltaAt (reallocConservedValue r ast).entries q =
      ((postingDeltas r.postings ast).map (fun p => if q == p.1 then p.2 else 0)).sum :=
  normalizedDeltas_at _

end Obend.Polis.ZoeSeatSettlement
