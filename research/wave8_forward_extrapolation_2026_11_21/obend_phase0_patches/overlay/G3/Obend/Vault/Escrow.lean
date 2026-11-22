module
/-
# Obend.Vault.Escrow — House Capacities as C4 Kinds: SealedEscrow and PrepaidLease

Absorbs `breadstuffs/Dregg2/Deos/SealedEscrow.lean` and `breadstuffs/Dregg2/Deos/PrepaidLease.lean`
into Obend's C4 Kind system, conserved resource Book (`Obend.Ledger.Book`), and multi-cell turns (`Obend.Vault.Hyperedge`).
-/
public import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Kind
public import Obend.Ledger.Book
public import Obend.Vault.Hyperedge
public import Obend.Law.Contract
public import Obend.Law.Proofs.Claim
public import Obend.Spec.Law
public import Obend.Spec.LawCompile

public import Obend.Vault.SurviveFirePor
import all Obend.Vault.SurviveFirePor
public import Obend.Vault.WorldTree
public import Obend.Vault.Replay
import all Obend.Vault.WorldTree
import all Obend.Vault.Replay
public import Obend.Vault.Mandate
public import Obend.Polis.CapTP
public import Obend.Codec.DetCbor
public import Obend.Polis.BlumRam
public import Obend.Polis.GrainPowerbox

public section

namespace Obend.Vault.Escrow

open Obend.Core.Data
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Kind
open Obend.Ledger
open Obend.Vault
open Obend.Law
open Obend.Spec.Law
open Obend.Spec.LawCompile (compile reqOf Fits)

set_option autoImplicit false

/-! ## 1. Coordinates and Common Types -/

inductive Side where
  | A
  | B
deriving DecidableEq, Repr

def Side.other : Side → Side
  | .A => .B
  | .B => .A

inductive LegStatus where
  | empty
  | deposited
  | consumed
deriving DecidableEq, Repr

def upd {α : Type} (f : Side → α) (s : Side) (v : α) : Side → α :=
  fun t => if t == s then v else f t

@[simp] theorem upd_same {α : Type} (f : Side → α) (s : Side) (v : α) :
    upd f s v s = v := by
  cases s <;> rfl

@[simp] theorem upd_ne {α : Type} (f : Side → α) (s : Side) (v : α) {t : Side} (h : t ≠ s) :
    upd f s v t = f t := by
  cases s <;> cases t <;> first | exact absurd rfl h | rfl

theorem upd_pair_sum (f : Side → Nat) (s : Side) (v : Nat) :
    upd f s v Side.A + upd f s v Side.B = (f Side.A + f Side.B) - f s + v := by
  cases s <;> dsimp [upd] <;> omega

/-! ## 2. SealedEscrow Value Ledger & State Machine -/

structure EscrowTerms where
  sideA_account : AccountId
  sideA_asset   : AssetId
  sideA_amount  : Nat
  sideB_account : AccountId
  sideB_asset   : AssetId
  sideB_amount  : Nat
  timeout       : Epoch
deriving DecidableEq, Repr

structure EscrowState where
  status : Side → LegStatus
  amount : Side → Nat
  recv   : Side → Nat
  paid   : Side → Nat

def openedEscrow : EscrowState where
  status := fun _ => .empty
  amount := fun _ => 0
  recv   := fun _ => 0
  paid   := fun _ => 0

def entered (st : EscrowState) (s : Side) : Nat :=
  match st.status s with
  | .empty => 0
  | _ => st.amount s

def locked (st : EscrowState) (s : Side) : Nat :=
  match st.status s with
  | .deposited => st.amount s
  | _ => 0

def enteredTotal (st : EscrowState) : Nat := entered st Side.A + entered st Side.B
def lockedTotal (st : EscrowState) : Nat := locked st Side.A + locked st Side.B
def paidTotal (st : EscrowState) : Nat := st.paid Side.A + st.paid Side.B
def recvTotal (st : EscrowState) : Nat := st.recv Side.A + st.recv Side.B

def Ready (st : EscrowState) : Prop :=
  st.status Side.A = .deposited ∧ st.status Side.B = .deposited

def ClaimOk (st : EscrowState) (own take : Side) (ownAmt claimedValue lockedAmt : Nat) : Prop :=
  st.status own = .deposited ∧
  st.amount own = ownAmt ∧
  st.status take = .deposited ∧
  st.amount take = lockedAmt ∧
  claimedValue ≤ lockedAmt

inductive EscrowOp : EscrowState → EscrowState → Prop where
  | deposit (st : EscrowState) (s : Side) (amt : Nat) (hempty : st.status s = .empty) :
      EscrowOp st { status := upd st.status s .deposited,
                    amount := upd st.amount s amt,
                    recv   := st.recv,
                    paid   := st.paid }
  | settle (st : EscrowState) (hA : st.status Side.A = .deposited) (hB : st.status Side.B = .deposited) :
      EscrowOp st { status := fun _ => .consumed,
                    amount := st.amount,
                    recv   := fun p => st.recv p + st.amount p.other,
                    paid   := fun s => st.paid s + st.amount s }
  | reclaim (st : EscrowState) (s : Side) (hdep : st.status s = .deposited) :
      EscrowOp st { status := upd st.status s .consumed,
                    amount := st.amount,
                    recv   := upd st.recv s (st.recv s + st.amount s),
                    paid   := upd st.paid s (st.paid s + st.amount s) }

inductive EscrowReachable : EscrowState → Prop where
  | genesis : EscrowReachable openedEscrow
  | step (st st' : EscrowState) (hr : EscrowReachable st) (hop : EscrowOp st st') : EscrowReachable st'

structure EscrowInv (st : EscrowState) : Prop where
  cons : ∀ s, st.paid s + locked st s = entered st s
  balance : recvTotal st = paidTotal st
  participate : ∀ s, st.status s = .empty → st.recv s = 0

theorem opened_inv : EscrowInv openedEscrow := by
  refine ⟨?_, ?_, ?_⟩
  · intro s; cases s <;> rfl
  · rfl
  · intro s _; rfl

theorem Op_preserves {st st' : EscrowState} (hop : EscrowOp st st') (ih : EscrowInv st) : EscrowInv st' := by
  cases hop with
  | deposit s amt hempty =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        cases s <;> cases t
        · have hpre := ih.cons .A
          unfold locked entered at hpre ⊢
          rw [hempty] at hpre
          dsimp [upd] at hpre ⊢
          omega
        · exact ih.cons .B
        · exact ih.cons .A
        · have hpre := ih.cons .B
          unfold locked entered at hpre ⊢
          rw [hempty] at hpre
          dsimp [upd] at hpre ⊢
          omega
      · exact ih.balance
      · intro t ht
        cases s <;> cases t
        · dsimp [upd] at ht; cases ht
        · exact ih.participate .B ht
        · exact ih.participate .A ht
        · dsimp [upd] at ht; cases ht
  | settle hA hB =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        cases t
        · have hc := ih.cons .A
          unfold locked entered at hc ⊢
          rw [hA] at hc
          dsimp at hc ⊢
          omega
        · have hc := ih.cons .B
          unfold locked entered at hc ⊢
          rw [hB] at hc
          dsimp at hc ⊢
          omega
      · unfold recvTotal paidTotal
        have hb := ih.balance
        unfold recvTotal paidTotal at hb
        dsimp [Side.other]
        omega
      · intro t ht; cases t <;> cases ht
  | reclaim s hdep =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        cases s <;> cases t
        · have hc := ih.cons .A
          unfold locked entered at hc ⊢
          rw [hdep] at hc
          dsimp [upd] at hc ⊢
          omega
        · exact ih.cons .B
        · exact ih.cons .A
        · have hc := ih.cons .B
          unfold locked entered at hc ⊢
          rw [hdep] at hc
          dsimp [upd] at hc ⊢
          omega
      · unfold recvTotal paidTotal
        have hb := ih.balance
        unfold recvTotal paidTotal at hb
        cases s <;> dsimp [upd] <;> omega
      · intro t ht
        cases s <;> cases t
        · dsimp [upd] at ht; cases ht
        · exact ih.participate .B ht
        · exact ih.participate .A ht
        · dsimp [upd] at ht; cases ht

theorem reachable_inv (st : EscrowState) (h : EscrowReachable st) : EscrowInv st := by
  induction h with
  | genesis => exact opened_inv
  | step s s' _ hop ih => exact Op_preserves hop ih

/-- **THE ECONOMIC NO-THEFT WORLD PROPERTY**:
    Per-leg conservation holds, and uncommitted parties receive nothing. -/
theorem sealedescrow_no_theft (st : EscrowState) (h : EscrowReachable st) :
    (∀ s, st.paid s + locked st s = entered st s) ∧
    (∀ s, st.status s = .empty → st.recv s = 0) :=
  ⟨(reachable_inv st h).cons, (reachable_inv st h).participate⟩

theorem no_phantom_extraction (st : EscrowState) (h : EscrowReachable st) (s : Side)
    (hempty : st.status s = .empty) : st.paid s = 0 := by
  have hc := (reachable_inv st h).cons s
  unfold locked entered at hc
  rw [hempty] at hc
  exact hc

theorem escrow_solvent (st : EscrowState) (h : EscrowReachable st) :
    recvTotal st ≤ enteredTotal st := by
  have inv := reachable_inv st h
  have hbal := inv.balance
  have hcA := inv.cons Side.A
  have hcB := inv.cons Side.B
  unfold recvTotal paidTotal enteredTotal at *
  omega

theorem halfopen_theft_unreachable (st : EscrowState) (h : EscrowReachable st)
    (hempty : st.status Side.A = .empty) (hclaim : 0 < st.recv Side.A) : False := by
  have hp := (reachable_inv st h).participate Side.A hempty
  omega

theorem phantom_extraction_unreachable (st : EscrowState) (h : EscrowReachable st)
    (hempty : st.status Side.A = .empty) (hextract : 0 < st.paid Side.A) : False := by
  have hz := no_phantom_extraction st h Side.A hempty
  omega

/-! ## 3. PrepaidLease Fused Meter-Draw Engine -/

structure LeaseTerms where
  rent    : Nat
  period  : Nat
  start   : Nat
  count   : Nat
  budget  : Nat
  lessor  : AccountId
  lessee  : AccountId
  asset   : AssetId
deriving DecidableEq, Repr

structure LeaseState where
  nextDue         : Nat
  dischargedCount : Nat
  remaining       : Nat
  drawn           : Nat
deriving DecidableEq, Repr

def LeaseTerms.wf (t : LeaseTerms) : Prop := 0 < t.rent ∧ 0 < t.period

def cursorAt (t : LeaseTerms) (k : Nat) : Nat := t.start + k * t.period
def dueBlock (t : LeaseTerms) (k : Nat) : Nat := t.start + k * t.period
def expectedPeriod (t : LeaseTerms) (nextDue : Nat) : Nat := (nextDue - t.start) / t.period

def periodsDueBy (t : LeaseTerms) (clock : Nat) : Nat :=
  if clock < t.start then 0
  else
    let due := (clock - t.start) / t.period + 1
    if 0 < t.count ∧ t.count < due then t.count else due

def openLease (t : LeaseTerms) : LeaseState where
  nextDue         := t.start
  dischargedCount := 0
  remaining       := t.budget
  drawn           := 0

/-- **THE FUSED DISCHARGE OPERATION**:
    Atomically advances the meter, bumps count, draws rent, and records drawn total. -/
@[expose] def advance (t : LeaseTerms) (st : LeaseState) : LeaseState where
  nextDue         := st.nextDue + t.period
  dischargedCount := st.dischargedCount + 1
  remaining       := st.remaining - t.rent
  drawn           := st.drawn + t.rent

def DischargeOk (t : LeaseTerms) (st : LeaseState) (clock : Nat) (amount : Nat) (periodIdx : Nat) : Prop :=
  (t.count = 0 ∨ expectedPeriod t st.nextDue < t.count) ∧
  periodIdx = expectedPeriod t st.nextDue ∧
  dueBlock t (expectedPeriod t st.nextDue) ≤ clock ∧
  amount = t.rent ∧
  t.rent ≤ st.remaining

def remainingAfter (budget rent : Nat) : Nat → Nat
  | 0 => budget
  | n + 1 => remainingAfter budget rent n - rent

def drawnAfter (rent : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => drawnAfter rent n + rent

theorem budget_never_overdrawn (budget rent n : Nat) (h : n * rent ≤ budget) :
    remainingAfter budget rent n = budget - n * rent := by
  induction n with
  | zero => simp [remainingAfter]
  | succ k ih =>
      simp only [remainingAfter]
      rw [Nat.succ_mul] at h ⊢
      have hk : k * rent ≤ budget := by omega
      rw [ih hk]
      omega

theorem drawn_eq_count_rent (rent n : Nat) :
    drawnAfter rent n = n * rent := by
  induction n with
  | zero => simp [drawnAfter]
  | succ k ih =>
      simp only [drawnAfter, ih]
      rw [Nat.succ_mul]

theorem remaining_plus_drawn_conserved (budget rent n : Nat) (h : n * rent ≤ budget) :
    remainingAfter budget rent n + drawnAfter rent n = budget := by
  rw [budget_never_overdrawn budget rent n h, drawn_eq_count_rent]
  omega

theorem cursor_strict_mono (t : LeaseTerms) (hwf : t.wf) {j k : Nat} (hjk : j < k) :
    cursorAt t j < cursorAt t k := by
  unfold cursorAt
  have hp : 0 < t.period := hwf.2
  have : j * t.period < k * t.period := Nat.mul_lt_mul_of_pos_right hjk hp
  omega

theorem advance_strictly_increases (t : LeaseTerms) (hwf : t.wf) (st : LeaseState) :
    st.nextDue < (advance t st).nextDue := by
  dsimp [advance]
  have hp := hwf.2
  omega

theorem advance_draws_exactly_rent (t : LeaseTerms) (st : LeaseState) :
    (advance t st).remaining = st.remaining - t.rent := rfl

theorem advance_meters_period (t : LeaseTerms) (st : LeaseState) :
    (advance t st).nextDue = st.nextDue + t.period := rfl

theorem expectedPeriod_open (t : LeaseTerms) : expectedPeriod t t.start = 0 := by
  unfold expectedPeriod
  simp

theorem expectedPeriod_advance (t : LeaseTerms) (hwf : t.wf) (k : Nat) :
    expectedPeriod t (t.start + (k + 1) * t.period) = expectedPeriod t (t.start + k * t.period) + 1 := by
  unfold expectedPeriod
  have hp : 0 < t.period := hwf.2
  have h1 : t.start + (k + 1) * t.period - t.start = (k + 1) * t.period := by omega
  have h0 : t.start + k * t.period - t.start = k * t.period := by omega
  rw [h1, h0]
  rw [Nat.mul_comm (k + 1) t.period, Nat.mul_div_right (k + 1) hp]
  rw [Nat.mul_comm k t.period, Nat.mul_div_right k hp]

theorem replay_rejected (t : LeaseTerms) (hwf : t.wf) (st : LeaseState) (clock : Nat)
    (k : Nat) (hcur : st.nextDue = cursorAt t k) :
    ¬ DischargeOk t (advance t st) clock t.rent (expectedPeriod t st.nextDue) := by
  intro hok
  have hexp := hok.2.1
  dsimp [advance] at hexp
  unfold cursorAt at hcur
  rw [hcur] at hexp
  have hadv : t.start + k * t.period + t.period = t.start + (k + 1) * t.period := by
    rw [Nat.succ_mul]
    omega
  rw [hadv] at hexp
  rw [expectedPeriod_advance t hwf k] at hexp
  omega

theorem insufficient_budget_rejected (t : LeaseTerms) (st : LeaseState) (clock amt pidx : Nat)
    (hshort : st.remaining < t.rent) :
    ¬ DischargeOk t st clock amt pidx := by
  intro hok
  have hcov := hok.2.2.2.2
  omega

/-! ## 4. C4 Nominal Kind Registration, Non-Trivial Laws & Verified CellContracts -/

/-- Legacy alias retained only for backward compatibility; `escrowKindCell` and
    `prepaidLeaseKindCell` now enforce `escrowLaw` and `prepaidLeaseLaw`. -/
def trivialLaw : LawExpr := .eqR .turn .turn

/-- Enforced law combinators for C4 Vault Kinds. -/
@[expose] def monotone (field : String) : LawExpr := .monotone field
@[expose] def writeOnce (field : String) : LawExpr := .writeOnce field
@[expose] def inRange (field : String) (values : List Int) : LawExpr := .inC (.field field) values
@[expose] def leField (left right : String) (offset : Int := 0) : LawExpr := .leROff (.field left) (.field right) offset

/-- Non-trivial enforced `LawExpr` for `prepaidLeaseKindCell`:
    `monotone "dischargedCount" && monotone "drawn" && leField "drawn" "budget" 0 && writeOnce "budget" && writeOnce "rent"`. -/
@[expose] def prepaidLeaseLaw : LawExpr :=
  .and (monotone "dischargedCount")
    (.and (monotone "drawn")
      (.and (leField "drawn" "budget" 0)
        (.and (writeOnce "budget") (writeOnce "rent"))))

def prepaidLeaseKindCell : KindCell LawExpr where
  name := "prepaidLease"
  version := 1
  layout := ["termsDigest", "rent", "period", "start", "count", "budget",
             "nextDue", "dischargedCount", "remaining", "drawn", "lessor", "lessee", "asset"]
  init := .record [
    ("termsDigest", .natural 0),
    ("rent", .natural 0),
    ("period", .natural 0),
    ("start", .natural 0),
    ("count", .natural 0),
    ("budget", .natural 0),
    ("nextDue", .natural 0),
    ("dischargedCount", .natural 0),
    ("remaining", .natural 0),
    ("drawn", .natural 0)
  ]
  law := prepaidLeaseLaw
  parents := ["escrow"]

/-! ### 4.1 Data Encodings & State Types for Escrow and PrepaidLease -/

def LegStatus.toNat : LegStatus → Nat
  | .empty => 0
  | .deposited => 1
  | .consumed => 2

def escrowSettledTag (st : EscrowState) : Nat :=
  if st.status .A == .consumed && st.status .B == .consumed then 1 else 0

@[expose] def escrowStateToData (st : EscrowState) : Data :=
  .record [
    ("settled", .natural (escrowSettledTag st)),
    ("statusA", .natural (st.status .A).toNat),
    ("statusB", .natural (st.status .B).toNat),
    ("sideA_amount", .natural (st.amount .A)),
    ("sideB_amount", .natural (st.amount .B)),
    ("paidA", .natural (st.paid .A)),
    ("paidB", .natural (st.paid .B)),
    ("recvA", .natural (st.recv .A)),
    ("recvB", .natural (st.recv .B))
  ]

@[expose] def escrowStateTy : Ty :=
  .field "settled" .natural
    (.field "statusA" .natural
      (.field "statusB" .natural
        (.field "sideA_amount" .natural
          (.field "sideB_amount" .natural
            (.field "paidA" .natural
              (.field "paidB" .natural
                (.field "recvA" .natural
                  (.field "recvB" .natural .emptyRow))))))))

@[expose] def leaseStateToData (t : LeaseTerms) (st : LeaseState) : Data :=
  .record [
    ("rent", .natural t.rent),
    ("period", .natural t.period),
    ("start", .natural t.start),
    ("count", .natural t.count),
    ("budget", .natural t.budget),
    ("nextDue", .natural st.nextDue),
    ("dischargedCount", .natural st.dischargedCount),
    ("remaining", .natural st.remaining),
    ("drawn", .natural st.drawn)
  ]

@[expose] def leaseStateTy : Ty :=
  .field "rent" .natural
    (.field "period" .natural
      (.field "start" .natural
        (.field "count" .natural
          (.field "budget" .natural
            (.field "nextDue" .natural
              (.field "dischargedCount" .natural
                (.field "remaining" .natural
                  (.field "drawn" .natural .emptyRow))))))))

@[simp] theorem leaseStateToData_fits (t : LeaseTerms) (st : LeaseState) :
    Fits leaseStateTy prepaidLeaseLaw (leaseStateToData t st) = true := rfl

@[simp] theorem escrowStateToData_field_settled (st : EscrowState) :
    fieldOf "settled" (escrowStateToData st) = some (Int.ofNat (escrowSettledTag st)) := rfl

@[simp] theorem escrowStateToData_field_statusA (st : EscrowState) :
    fieldOf "statusA" (escrowStateToData st) = some (Int.ofNat (st.status .A).toNat) := rfl

@[simp] theorem escrowStateToData_field_statusB (st : EscrowState) :
    fieldOf "statusB" (escrowStateToData st) = some (Int.ofNat (st.status .B).toNat) := rfl

@[simp] theorem leaseStateToData_field_rent (t : LeaseTerms) (st : LeaseState) :
    fieldOf "rent" (leaseStateToData t st) = some (Int.ofNat t.rent) := rfl

@[simp] theorem leaseStateToData_field_budget (t : LeaseTerms) (st : LeaseState) :
    fieldOf "budget" (leaseStateToData t st) = some (Int.ofNat t.budget) := rfl

@[simp] theorem leaseStateToData_field_dischargedCount (t : LeaseTerms) (st : LeaseState) :
    fieldOf "dischargedCount" (leaseStateToData t st) = some (Int.ofNat st.dischargedCount) := rfl

@[simp] theorem leaseStateToData_field_drawn (t : LeaseTerms) (st : LeaseState) :
    fieldOf "drawn" (leaseStateToData t st) = some (Int.ofNat st.drawn) := rfl

/-! ### 4.2 Inductive CellContract Construction (`escrowCellContract` & `prepaidLeaseCellContract`) -/

def cellTopInv : Term := .lam trueT

-- fixture kept (2026-11-04): cheap closed check of `closedB` on literal data
example : closedB cellTopInv = true := by decide +kernel

theorem holds_cellTopInv (d : Data) : Holds cellTopInv d := by
  unfold Holds cellTopInv
  refine evaluates_step (.beta trueT d.term) ?_
  have hinst : instantiate trueT d.term = .boolean true := by
    unfold instantiate
    exact subst_trueT _
  rw [hinst]
  exact evaluates_self (.boolean true)

def inRange012T (x : Term) : Term :=
  .ifBool (eqNat x (natT 0)) trueT
    (.ifBool (eqNat x (natT 1)) trueT
      (.ifBool (eqNat x (natT 2)) trueT falseT))

/-- A leg pays exactly its funded amount when consumed, and nothing before consumption. -/
def legPaidT (status amount paid : Term) : Term :=
  .ifBool (eqNat status (natT 2)) (eqNat paid amount) (eqNat paid (natT 0))

/-- Received value is exactly paid value; an empty leg cannot receive anything. -/
def recvBalanceT (state : Term) : Term :=
  andT (eqNat (addNat (.get state "recvA") (.get state "recvB"))
    (addNat (.get state "paidA") (.get state "paidB")))
    (andT (.ifBool (eqNat (.get state "statusA") (natT 0))
      (eqNat (.get state "recvA") (natT 0)) trueT)
      (.ifBool (eqNat (.get state "statusB") (natT 0))
        (eqNat (.get state "recvB") (natT 0)) trueT))

def escrowBalanceT (state : Term) : Term :=
  andT (legPaidT (.get state "statusA") (.get state "sideA_amount") (.get state "paidA"))
       (andT (legPaidT (.get state "statusB") (.get state "sideB_amount") (.get state "paidB"))
         (recvBalanceT state))

/-- Status validity and exact per-leg funded conservation. -/
def escrowInvariant : Term :=
  .lam (andT (inRange012T (.get (.bound 0) "statusA"))
    (andT (inRange012T (.get (.bound 0) "statusB")) (escrowBalanceT (.bound 0))))

-- fixture kept (2026-11-04): closedness of a library invariant, consumed by four proofs
theorem escrowInvariant_closed : closedB escrowInvariant = true := by decide +kernel

/-- Non-trivial single-state invariant for `PrepaidLease` enforcing `drawn ≤ budget` and `remaining ≤ budget`. -/
def prepaidLeaseInvariant : Term :=
  .lam (andT (leNat (.get (.bound 0) "drawn") (.get (.bound 0) "budget"))
             (leNat (.get (.bound 0) "remaining") (.get (.bound 0) "budget")))

-- fixture kept (2026-11-04): closedness of a library invariant, consumed by four proofs
theorem prepaidLeaseInvariant_closed : closedB prepaidLeaseInvariant = true := by decide +kernel

/-- Constructive `CellContract` builder backed by a closed `invariant` (`closedB invariant = true`)
    and a Core4 `stepBody` (`0 Classical.choice`).
    The executable `law` guards `stepBody` with `.app invariant (.bound 1)` on the post-state `new`,
    establishing both `inductive_preserves` (`Holds invariant new`) and `step_sound`
    (`Admits (law3 stepBody) old new req`). -/
def mkGuardedStepCellContract (invariant : Term) (hI : closedB invariant = true)
    (why : String) (stepBody : Term) : CellContract where
  law := law3 (guard (.app invariant (.bound 1)) why stepBody)
  invariant := invariant
  stepRel := law3 stepBody
  inductive_preserves := by
    intro old new req _ hadm
    obtain ⟨w, hw⟩ := (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).1 hadm
    unfold Obend.Law.guard at hw
    simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv] at hw
    obtain ⟨bb, hc, hr⟩ := ifBool_inv hw
    cases bb
    · simp only [Bool.false_eq_true, ↓reduceIte, refusedT, subst_inject, Term.substitute] at hr
      have hval := evaluates_value (.inject _ _) hr
      injection hval with htag _
      exact absurd htag (by decide)
    · exact hc
  step_sound := by
    intro old new req _ hadm
    obtain ⟨w, hw⟩ := (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).1 hadm
    unfold Obend.Law.guard at hw
    simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv] at hw
    obtain ⟨bb, _, hr⟩ := ifBool_inv hw
    cases bb
    · simp only [Bool.false_eq_true, ↓reduceIte, refusedT, subst_inject, Term.substitute] at hr
      have hval := evaluates_value (.inject _ _) hr
      injection hval with htag _
      exact absurd htag (by decide)
    · simp only [↓reduceIte] at hr
      exact (admits_iff stepBody old new req).2 ⟨w, hr⟩

/-- Constructive `CellContract` builder backed by a Core4 `stepBody` and `cellTopInv` (`0 Classical.choice`). -/
def mkDirectStepCellContract (stepBody : Term) : CellContract where
  law := law3 stepBody
  invariant := cellTopInv
  stepRel := law3 stepBody
  inductive_preserves := fun _ new _ _ _ => holds_cellTopInv new
  step_sound := fun _ _ _ _ hadm => hadm

/-- A funded leg cannot change amount or reset its status to empty. -/
def fundedLegT (old new : Term) (status amount : String) : Term :=
  andT (leNat (.get old status) (.get new status))
    (.ifBool (eqNat (.get old status) (natT 0))
      (leNat (.get new status) (natT 1))
      (eqNat (.get old amount) (.get new amount)))

def escrowCondT : Term :=
  andT (andT (leNat (.get (.bound 2) "recvA") (.get (.bound 1) "recvA"))
    (leNat (.get (.bound 2) "recvB") (.get (.bound 1) "recvB")))
  (andT (leNat (.get (.bound 2) "settled") (.get (.bound 1) "settled"))
    (andT (andT (leNat (.get (.bound 2) "paidA") (.get (.bound 1) "paidA"))
      (leNat (.get (.bound 2) "paidB") (.get (.bound 1) "paidB")))
      (andT (escrowBalanceT (.bound 1))
        (andT (fundedLegT (.bound 2) (.bound 1) "statusA" "sideA_amount")
          (fundedLegT (.bound 2) (.bound 1) "statusB" "sideB_amount")))))

def escrowStepBody : Term := guard escrowCondT "escrowLaw" okT

def writeOnceNatT (oldV newV : Term) : Term :=
  .ifBool (eqNat oldV (natT 0)) trueT (eqNat newV oldV)

def prepaidLeaseCondT : Term :=
  andT (leNat (.get (.bound 2) "dischargedCount") (.get (.bound 1) "dischargedCount"))
    (andT (leNat (.get (.bound 2) "drawn") (.get (.bound 1) "drawn"))
      (andT (leNat (.get (.bound 1) "drawn") (.get (.bound 1) "budget"))
        (andT (writeOnceNatT (.get (.bound 2) "budget") (.get (.bound 1) "budget"))
          (andT (writeOnceNatT (.get (.bound 2) "rent") (.get (.bound 1) "rent"))
            (andT (leNat (.get (.bound 1) "remaining") (.get (.bound 2) "remaining"))
                  (leNat (.get (.bound 1) "remaining") (.get (.bound 1) "budget")))))))

def prepaidLeaseStepBody : Term := guard prepaidLeaseCondT "prepaidLeaseLaw" okT

/-- Proof-carrying inductive `CellContract` for `SealedEscrow` with non-trivial `escrowInvariant` (`0 Classical.choice`). -/
def escrowCellContract : CellContract :=
  mkGuardedStepCellContract escrowInvariant escrowInvariant_closed "escrowLaw" escrowStepBody

/-- Registered admission uses the very same executable predicate as the proved contract. -/
def escrowLaw : Term := escrowCellContract.law

def escrowKindCell : KindCell Term where
  name := "escrow"
  version := 2
  layout := ["settled", "statusA", "statusB", "sideA_amount", "sideB_amount",
    "paidA", "paidB", "recvA", "recvB"]
  init := escrowStateToData openedEscrow
  law := escrowLaw
  parents := []

theorem escrowKindCell_admits_iff (old new req : Data) :
    Admits escrowKindCell.law old new req ↔ Admits escrowCellContract.law old new req := Iff.rfl

/-- Proof-carrying inductive `CellContract` for `PrepaidLease` with non-trivial `prepaidLeaseInvariant` (`0 Classical.choice`). -/
def prepaidLeaseCellContract : CellContract :=
  mkGuardedStepCellContract prepaidLeaseInvariant prepaidLeaseInvariant_closed "prepaidLeaseLaw" prepaidLeaseStepBody

/-! ### 4.3 Constructive Core4 Evaluation & Machine-Checked Bridge/Refusal Theorems -/

theorem guardedLaw_admits_of_holds_and_step {invariant : Term} (hI : closedB invariant = true)
    {why : String} {stepBody : Term} {old new req : Data}
    (hinv : Holds invariant new)
    (hstep : Admits (law3 stepBody) old new req) :
    Admits (law3 (guard (.app invariant (.bound 1)) why stepBody)) old new req := by
  obtain ⟨w, hw⟩ := (admits_iff stepBody old new req).1 hstep
  refine (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).2 ⟨w, ?_⟩
  unfold Obend.Law.guard
  simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv]
  refine evaluates_ifBool hinv ?_
  exact hw

theorem guardedLaw_admits_imp_stepRel {invariant : Term} (hI : closedB invariant = true)
    {why : String} {stepBody : Term} {old new req : Data}
    (hadm : Admits (law3 (guard (.app invariant (.bound 1)) why stepBody)) old new req) :
    Admits (law3 stepBody) old new req := by
  obtain ⟨w, hw⟩ := (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).1 hadm
  unfold Obend.Law.guard at hw
  simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv] at hw
  obtain ⟨bb, _, hr⟩ := ifBool_inv hw
  cases bb
  · simp only [Bool.false_eq_true, ↓reduceIte, refusedT, subst_inject, Term.substitute] at hr
    have hval := evaluates_value (.inject _ _) hr
    injection hval with htag _
    exact absurd htag (by decide)
  · simp only [↓reduceIte] at hr
    exact (admits_iff stepBody old new req).2 ⟨w, hr⟩

theorem steps_binaryLeft {p : Primitive} {l l' r : Term} (h : Steps l l') :
    Steps (.binary p l r) (.binary p l' r) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryLeft _ _ s) ih

theorem steps_binaryRight {p : Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') :
    Steps (.binary p l r) (.binary p l r') := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryRight _ _ hl s) ih

theorem ev_leNat {l r : Term} {a b : Nat} (hl : Evaluates l (.nat a)) (hr : Evaluates r (.nat b)) :
    Evaluates (leNat l r) (.boolean (decide (a ≤ b))) := by
  unfold leNat
  refine evaluates_steps (steps_binaryLeft hl.1) ?_
  refine evaluates_steps (steps_binaryRight (.natural a) hr.1) ?_
  exact evaluates_step (.primitive .lessEqual (.nat a) (.nat b) (.boolean (decide (a ≤ b))) (.natural a) (.natural b) rfl)
    (evaluates_self (.boolean _))

theorem ev_eqNat {l r : Term} {a b : Nat} (hl : Evaluates l (.nat a)) (hr : Evaluates r (.nat b)) :
    Evaluates (eqNat l r) (.boolean (a == b)) := by
  unfold eqNat
  refine evaluates_steps (steps_binaryLeft hl.1) ?_
  refine evaluates_steps (steps_binaryRight (.natural a) hr.1) ?_
  exact evaluates_step (.primitive .equal (.nat a) (.nat b) (.boolean (a == b)) (.natural a) (.natural b) rfl)
    (evaluates_self (.boolean _))

theorem ev_andT {a b : Term} {ba bb : Bool} (ha : Evaluates a (.boolean ba)) (hb : Evaluates b (.boolean bb)) :
    Evaluates (andT a b) (.boolean (ba && bb)) := by
  unfold andT
  refine evaluates_ifBool ha ?_
  cases ba
  · exact evaluates_self (.boolean false)
  · exact hb

theorem ev_orT {a b : Term} {ba bb : Bool} (ha : Evaluates a (.boolean ba)) (hb : Evaluates b (.boolean bb)) :
    Evaluates (.ifBool a trueT b) (.boolean (ba || bb)) := by
  refine evaluates_ifBool ha ?_
  cases ba
  · exact hb
  · exact evaluates_self (.boolean true)

theorem ev_get_nat {fs : List (String × Term)} {f : String} {m : Nat}
    (hf : fs.find? (fun field => field.1 == f) = some (f, .nat m)) :
    Evaluates (.get (.record fs) f) (.nat m) :=
  evaluates_step (.field fs f (.nat m) hf) (evaluates_self (.natural m))

theorem ev_inRange012T {x : Term} {m : Nat} (hx : Evaluates x (.nat m)) :
    Evaluates (inRange012T x) (.boolean ((m == 0) || ((m == 1) || (m == 2)))) := by
  unfold inRange012T
  refine ev_orT (ev_eqNat hx (evaluates_self (.natural 0))) ?_
  refine ev_orT (ev_eqNat hx (evaluates_self (.natural 1))) ?_
  refine evaluates_ifBool (ev_eqNat hx (evaluates_self (.natural 2))) ?_
  cases (m == 2) <;> exact evaluates_self (.boolean _)

theorem ev_writeOnceNatT {oldV newV : Term} {o n : Nat}
    (ho : Evaluates oldV (.nat o)) (hn : Evaluates newV (.nat n)) :
    Evaluates (writeOnceNatT oldV newV) (.boolean ((o == 0) || (n == o))) := by
  unfold writeOnceNatT
  exact ev_orT (ev_eqNat ho (evaluates_self (.natural 0))) (ev_eqNat hn ho)

def verdictOfBool (why : String) (b : Bool) : Term :=
  if b then okT else refusedT why

theorem ev_guard_okT {c : Term} {why : String} {b : Bool} (hc : Evaluates c (.boolean b)) :
    Evaluates (guard c why okT) (verdictOfBool why b) := by
  unfold Obend.Law.guard verdictOfBool
  refine evaluates_ifBool hc ?_
  cases b <;> exact evaluates_self (.inject _ _)

theorem verdictOfBool_iff {B : Term} {o n rq : Data} {why : String} {b : Bool}
    (h : Evaluates (B.substitute (lawEnv o.term n.term rq.term)) (verdictOfBool why b)) :
    (Admits (law3 B) o n rq ↔ b = true) ∧ (Refuses (law3 B) o n rq why ↔ b = false) := by
  cases b
  · refine ⟨⟨fun hadm => ?_, fun h => by cases h⟩,
            ⟨fun _ => rfl, fun _ => (refuses_iff B o n rq why).2 h⟩⟩
    obtain ⟨w, hw⟩ := (admits_iff B o n rq).1 hadm
    have heq := evaluates_unique h hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  · refine ⟨⟨fun _ => rfl, fun _ => (admits_iff B o n rq).2 ⟨_, h⟩⟩,
            ⟨fun href => ?_, fun h => by cases h⟩⟩
    have hw := (refuses_iff B o n rq why).1 href
    have heq := evaluates_unique h hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)

def legPaidB (st : EscrowState) (side : Side) : Bool :=
  if st.status side == .consumed then st.paid side == st.amount side else st.paid side == 0

def fundedLegB (st st' : EscrowState) (side : Side) : Bool :=
  decide ((st.status side).toNat ≤ (st'.status side).toNat) &&
    (if (st.status side).toNat == 0 then decide ((st'.status side).toNat ≤ 1)
      else st.amount side == st'.amount side)

def recvBalanceB (st : EscrowState) : Bool :=
  (recvTotal st == paidTotal st) &&
    ((if (st.status .A).toNat == 0 then st.recv .A == 0 else true) &&
     (if (st.status .B).toNat == 0 then st.recv .B == 0 else true))

theorem recvBalanceB_iff (st : EscrowState) : recvBalanceB st = true ↔
    recvTotal st = paidTotal st ∧ (∀ side, st.status side = .empty → st.recv side = 0) := by
  simp only [recvBalanceB, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro side hs
    cases side
    · simpa [hs, LegStatus.toNat] using h.2.1
    · simpa [hs, LegStatus.toNat] using h.2.2
  · rintro ⟨hb, hp⟩
    refine ⟨hb, ?_, ?_⟩
    · cases hs : st.status .A <;> simp [LegStatus.toNat]
      exact hp .A hs
    · cases hs : st.status .B <;> simp [LegStatus.toNat]
      exact hp .B hs

def escrowVerdictBool (st st' : EscrowState) : Bool :=
  (decide (st.recv .A ≤ st'.recv .A) && decide (st.recv .B ≤ st'.recv .B)) &&
  (decide (escrowSettledTag st ≤ escrowSettledTag st') &&
    ((decide (st.paid .A ≤ st'.paid .A) && decide (st.paid .B ≤ st'.paid .B)) &&
      ((legPaidB st' .A && (legPaidB st' .B && recvBalanceB st')) &&
        (fundedLegB st st' .A && fundedLegB st st' .B))))

theorem ev_legPaidT {status amount paid : Term} (s : LegStatus) (a p : Nat)
    (hs : Evaluates status (.nat s.toNat)) (ha : Evaluates amount (.nat a))
    (hp : Evaluates paid (.nat p)) :
    Evaluates (legPaidT status amount paid)
      (.boolean (if s == .consumed then p == a else p == 0)) := by
  unfold legPaidT
  refine evaluates_ifBool (ev_eqNat hs (evaluates_self (.natural 2))) ?_
  cases s <;> first | exact ev_eqNat hp ha | exact ev_eqNat hp (evaluates_self (.natural 0))

theorem ev_addNat {l r : Term} {a b : Nat}
    (hl : Evaluates l (.nat a)) (hr : Evaluates r (.nat b)) :
    Evaluates (addNat l r) (.nat (a + b)) := by
  unfold addNat
  refine evaluates_steps (steps_binaryLeft hl.1) ?_
  refine evaluates_steps (steps_binaryRight (.natural a) hr.1) ?_
  exact evaluates_step (.primitive .add _ _ _ (.natural a) (.natural b) rfl)
    (evaluates_self (.natural _))

theorem ev_recvBalanceT (st : EscrowState) :
    Evaluates (recvBalanceT (escrowStateToData st).term) (.boolean (recvBalanceB st)) := by
  unfold recvBalanceT recvBalanceB recvTotal paidTotal
  refine ev_andT (ev_eqNat (ev_addNat (ev_get_nat rfl) (ev_get_nat rfl))
    (ev_addNat (ev_get_nat rfl) (ev_get_nat rfl))) (ev_andT ?_ ?_)
  all_goals
    refine evaluates_ifBool (ev_eqNat (ev_get_nat rfl) (evaluates_self (.natural 0))) ?_
    split
    · exact ev_eqNat (ev_get_nat rfl) (evaluates_self (.natural 0))
    · exact evaluates_self (.boolean true)

theorem escrowStepBody_eval (st st' : EscrowState) (rq : Data) :
    Evaluates (escrowStepBody.substitute (lawEnv (escrowStateToData st).term (escrowStateToData st').term rq.term))
      (verdictOfBool "escrowLaw" (escrowVerdictBool st st')) := by
  unfold escrowStepBody escrowCondT escrowBalanceT recvBalanceT fundedLegT legPaidT
  simp only [subst_guard, subst_okT, subst_andT, subst_leNat, subst_ifBool, subst_eqNat,
    subst_natT, subst_trueT, subst_falseT, subst_get, subst_bound, subst_addNat]
  refine ev_guard_okT (ev_andT (ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
    (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))) ?_)
  refine (ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_)
  refine ev_andT (ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
    (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))) ?_
  refine ev_andT (ev_andT (ev_legPaidT _ _ _ (ev_get_nat rfl) (ev_get_nat rfl) (ev_get_nat rfl))
    (ev_andT (ev_legPaidT _ _ _ (ev_get_nat rfl) (ev_get_nat rfl) (ev_get_nat rfl))
      (ev_recvBalanceT st'))) ?_
  have leg (side : Side) (status amount : String)
      (ho : Evaluates (.get (escrowStateToData st).term status) (.nat (st.status side).toNat))
      (hn : Evaluates (.get (escrowStateToData st').term status) (.nat (st'.status side).toNat))
      (hao : Evaluates (.get (escrowStateToData st).term amount) (.nat (st.amount side)))
      (han : Evaluates (.get (escrowStateToData st').term amount) (.nat (st'.amount side))) :
      Evaluates (fundedLegT (escrowStateToData st).term (escrowStateToData st').term status amount)
        (.boolean (fundedLegB st st' side)) := by
    unfold fundedLegT fundedLegB
    refine ev_andT (ev_leNat ho hn) ?_
    refine evaluates_ifBool (ev_eqNat ho (evaluates_self (.natural 0))) ?_
    cases he : st.status side
    · exact ev_leNat hn (evaluates_self (.natural 1))
    · exact ev_eqNat hao han
    · exact ev_eqNat hao han
  exact ev_andT (leg .A "statusA" "sideA_amount" (ev_get_nat rfl) (ev_get_nat rfl)
    (ev_get_nat rfl) (ev_get_nat rfl))
    (leg .B "statusB" "sideB_amount" (ev_get_nat rfl) (ev_get_nat rfl)
      (ev_get_nat rfl) (ev_get_nat rfl))

/-- Admission conserves each funded leg and cannot mint payouts. New funding is allowed
only on a previously empty leg; deposited and consumed amounts are immutable. -/
theorem escrowCellContract_conserves_funded_value (st st' : EscrowState) (req : Data)
    (h : Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st') req) :
    (∀ side, st'.paid side + locked st' side = entered st' side) ∧
    (∀ side, st.status side ≠ .empty → st'.amount side = st.amount side) ∧
    paidTotal st' + lockedTotal st' = enteredTotal st' ∧
    recvTotal st' = paidTotal st' ∧
    (∀ side, st'.status side = .empty → st'.recv side = 0) := by
  have hs := guardedLaw_admits_imp_stepRel escrowInvariant_closed h
  have hv := (verdictOfBool_iff (escrowStepBody_eval st st' req)).1.1 hs
  simp only [escrowVerdictBool, Bool.and_eq_true] at hv
  have hv := hv.2
  have hc : ∀ side, st'.paid side + locked st' side = entered st' side := by
    intro side
    have hp : legPaidB st' side = true := by cases side <;> first | exact hv.2.2.1.1 | exact hv.2.2.1.2.1
    unfold legPaidB at hp
    unfold locked entered
    cases he : st'.status side <;> simp [he] at hp ⊢ <;> omega
  refine ⟨hc, ?_, ?_⟩
  · intro side hn
    have hf : fundedLegB st st' side = true := by cases side <;> first | exact hv.2.2.2.1 | exact hv.2.2.2.2
    simp only [fundedLegB, Bool.and_eq_true] at hf
    have hn0 : (st.status side).toNat ≠ 0 := by
      cases he : st.status side <;> simp_all [LegStatus.toNat]
    have heq := hf.2
    simp only [beq_eq_false_iff_ne.mpr hn0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at heq
    exact heq.symm
  · refine ⟨?_, (recvBalanceB_iff st').mp hv.2.2.1.2.2⟩
    have ha := hc .A
    have hb := hc .B
    unfold paidTotal lockedTotal enteredTotal
    omega

theorem escrowCellContract_preserves_EscrowInv (st st' : EscrowState) (req : Data)
    (h : Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st') req) :
    EscrowInv st' := by
  have hc := escrowCellContract_conserves_funded_value st st' req h
  exact ⟨hc.1, hc.2.2.2.1, hc.2.2.2.2⟩

/-- Admission cannot erase either participant's already received credit. -/
theorem escrowCellContract_recv_monotone (st st' : EscrowState) (req : Data)
    (h : Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st') req) :
    st.recv .A ≤ st'.recv .A ∧ st.recv .B ≤ st'.recv .B := by
  have hs := guardedLaw_admits_imp_stepRel escrowInvariant_closed h
  have hv := (verdictOfBool_iff (escrowStepBody_eval st st' req)).1.1 hs
  simp only [escrowVerdictBool, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.1

theorem escrowCellContract_refuses_phantom_recv (st st' : EscrowState) (req : Data)
    (hphantom : recvTotal st' ≠ paidTotal st') :
    ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st') req := by
  intro h
  exact hphantom (escrowCellContract_preserves_EscrowInv st st' req h).balance

/-- An empty leg must be funded before it can be consumed. -/
theorem escrowCellContract_refuses_skipped_deposit (st st' : EscrowState) (req : Data)
    (side : Side) (he : st.status side = .empty) (hc : st'.status side = .consumed) :
    ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st') req := by
  intro h
  have hs := guardedLaw_admits_imp_stepRel escrowInvariant_closed h
  have hv := (verdictOfBool_iff (escrowStepBody_eval st st' req)).1.1 hs
  simp only [escrowVerdictBool, Bool.and_eq_true] at hv
  have hv := hv.2
  have hf : fundedLegB st st' side = true := by
    cases side <;> first | exact hv.2.2.2.1 | exact hv.2.2.2.2
  simp [fundedLegB, he, hc, LegStatus.toNat] at hf

theorem escrowCellContract_refuses_unfunded_payout (st st' : EscrowState) (req : Data)
    (side : Side) (hmint : entered st' side < st'.paid side) :
    ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st') req := by
  intro h
  have hc := (escrowCellContract_conserves_funded_value st st' req h).1 side
  omega

def prepaidLeaseVerdictBool (t : LeaseTerms) (st st' : LeaseState) : Bool :=
  decide (st.dischargedCount ≤ st'.dischargedCount) &&
    (decide (st.drawn ≤ st'.drawn) &&
      (decide (st'.drawn ≤ t.budget) &&
        (((t.budget == 0) || (t.budget == t.budget)) &&
         (((t.rent == 0) || (t.rent == t.rent)) &&
          (decide (st'.remaining ≤ st.remaining) && decide (st'.remaining ≤ t.budget))))))

theorem prepaidLeaseStepBody_eval (t : LeaseTerms) (st st' : LeaseState) (rq : Data) :
    Evaluates (prepaidLeaseStepBody.substitute (lawEnv (leaseStateToData t st).term (leaseStateToData t st').term rq.term))
      (verdictOfBool "prepaidLeaseLaw" (prepaidLeaseVerdictBool t st st')) := by
  unfold prepaidLeaseStepBody prepaidLeaseCondT writeOnceNatT
  simp only [subst_guard, subst_okT, subst_andT, subst_leNat, subst_ifBool, subst_eqNat,
    subst_natT, subst_trueT, subst_get, subst_bound]
  refine ev_guard_okT ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_writeOnceNatT (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_writeOnceNatT (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  exact ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
                (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))

theorem legStatus_in_range (s : LegStatus) :
    ([0, 1, 2] : List Int).contains (Int.ofNat s.toNat) = true := by
  cases s <;> decide

theorem legStatus_inRange012 (s : LegStatus) :
    (s.toNat == 0 || (s.toNat == 1 || s.toNat == 2)) = true := by
  cases s <;> decide

theorem legPaidB_of_inv (st : EscrowState) (h : EscrowInv st) (side : Side) :
    legPaidB st side = true := by
  have hc := h.cons side
  unfold locked entered at hc
  unfold legPaidB
  cases hs : st.status side <;> simp [hs] at hc ⊢ <;> omega

theorem holds_escrowInvariant (st : EscrowState) (h : EscrowInv st) :
    Holds escrowInvariant (escrowStateToData st) := by
  unfold Holds escrowInvariant
  refine evaluates_step (.beta _ (escrowStateToData st).term) ?_
  unfold instantiate escrowBalanceT recvBalanceT legPaidT inRange012T
  simp only [subst_andT, subst_ifBool, subst_eqNat, subst_natT, subst_trueT, subst_falseT,
    subst_get, subst_bound, subst_addNat]
  have hA := legPaidB_of_inv st h .A
  have hB := legPaidB_of_inv st h .B
  have hr := (recvBalanceB_iff st).mpr ⟨h.balance, h.participate⟩
  have hev : Evaluates
      (andT (inRange012T (.get (escrowStateToData st).term "statusA"))
        (andT (inRange012T (.get (escrowStateToData st).term "statusB"))
          (escrowBalanceT (escrowStateToData st).term)))
      (.boolean (((st.status .A).toNat == 0 || ((st.status .A).toNat == 1 || (st.status .A).toNat == 2)) &&
        (((st.status .B).toNat == 0 || ((st.status .B).toNat == 1 || (st.status .B).toNat == 2)) &&
          (legPaidB st .A && (legPaidB st .B && recvBalanceB st))))) :=
    ev_andT (ev_inRange012T (ev_get_nat rfl))
      (ev_andT (ev_inRange012T (ev_get_nat rfl))
        (ev_andT (ev_legPaidT _ _ _ (ev_get_nat rfl) (ev_get_nat rfl) (ev_get_nat rfl))
          (ev_andT (ev_legPaidT _ _ _ (ev_get_nat rfl) (ev_get_nat rfl) (ev_get_nat rfl))
            (ev_recvBalanceT st))))
  simpa only [legStatus_inRange012, hA, hB, hr, Bool.and_self, inRange012T, escrowBalanceT, recvBalanceT, legPaidT] using hev

theorem holds_prepaidLeaseInvariant (t : LeaseTerms) (st : LeaseState)
    (hdrawn : st.drawn ≤ t.budget) (hrem : st.remaining ≤ t.budget) :
    Holds prepaidLeaseInvariant (leaseStateToData t st) := by
  unfold Holds prepaidLeaseInvariant
  refine evaluates_step (.beta _ (leaseStateToData t st).term) ?_
  unfold instantiate
  simp only [subst_andT, subst_leNat, subst_get, subst_bound]
  have h1 : decide (st.drawn ≤ t.budget) = true := decide_eq_true hdrawn
  have h2 : decide (st.remaining ≤ t.budget) = true := decide_eq_true hrem
  have hev : Evaluates
      (andT (leNat (.get (leaseStateToData t st).term "drawn") (.get (leaseStateToData t st).term "budget"))
            (leNat (.get (leaseStateToData t st).term "remaining") (.get (leaseStateToData t st).term "budget")))
      (.boolean (decide (st.drawn ≤ t.budget) && decide (st.remaining ≤ t.budget))) :=
    ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
  rw [h1, h2, Bool.and_self] at hev
  exact hev

theorem escrowSettledTag_eq_zero_of_not_consumed {st : EscrowState} {s : Side}
    (h : st.status s ≠ .consumed) : escrowSettledTag st = 0 := by
  unfold escrowSettledTag
  cases s
  · have hA : (st.status .A == .consumed) = false := beq_false_of_ne h
    simp [hA]
  · have hB : (st.status .B == .consumed) = false := beq_false_of_ne h
    simp [hB]

/-- Every valid `EscrowOp` transition is admitted by `escrowCellContract` (both `law` and `stepRel`)
    and preserves `escrowCellContract.invariant` (`0 Classical.choice`). -/
theorem escrowOp_admitted_by_contract (facts : Facts) {st st' : EscrowState}
    (hop : EscrowOp st st') (ag pr : String) (nb vu : Nat) (hin : EscrowInv st) :
    Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) ∧
    Admits escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) ∧
    Holds escrowCellContract.invariant (escrowStateToData st') := by
  have hzero : escrowSettledTag st = 0 := by
    cases hop with
    | deposit s amt hempty =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hempty]; decide)
    | settle hA _ =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hA]; decide)
    | reclaim s hdep =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hdep]; decide)
  have hpaidA : decide (st.paid .A ≤ st'.paid .A) = true := by
    cases hop with
    | deposit _ _ _ => exact decide_eq_true (Nat.le_refl _)
    | settle _ _ => exact decide_eq_true (Nat.le_add_right _ _)
    | reclaim s _ =>
      apply decide_eq_true
      cases s <;> dsimp [upd] <;> omega
  have hpaidB : decide (st.paid .B ≤ st'.paid .B) = true := by
    cases hop with
    | deposit _ _ _ => exact decide_eq_true (Nat.le_refl _)
    | settle _ _ => exact decide_eq_true (Nat.le_add_right _ _)
    | reclaim s _ =>
      apply decide_eq_true
      cases s <;> dsimp [upd] <;> omega
  have hle : decide (escrowSettledTag st ≤ escrowSettledTag st') = true :=
    decide_eq_true (by rw [hzero]; omega)
  have hfund : ∀ side, fundedLegB st st' side = true := by
    intro side
    cases hop with
    | deposit s amt hempty =>
      cases s <;> cases side <;> simp [fundedLegB, upd, hempty, LegStatus.toNat] <;> split <;> simp_all
    | settle hA hB =>
      cases side <;> simp [fundedLegB, hA, hB, LegStatus.toNat]
    | reclaim s hdep =>
      cases s <;> cases side <;> simp [fundedLegB, upd, hdep, LegStatus.toNat] <;> split <;> simp_all
  have hrecv : ∀ side, st.recv side ≤ st'.recv side := by
    intro side
    cases hop with
    | deposit _ _ _ => exact Nat.le_refl _
    | settle _ _ => exact Nat.le_add_right _ _
    | reclaim s _ => cases s <;> cases side <;> dsimp [upd] <;> omega
  have hr := (recvBalanceB_iff st').mpr
    ⟨(Op_preserves hop hin).balance, (Op_preserves hop hin).participate⟩
  have hv : escrowVerdictBool st st' = true := by
    simp only [escrowVerdictBool, decide_eq_true (hrecv .A), decide_eq_true (hrecv .B), hr, hle, hpaidA, hpaidB, legPaidB_of_inv st' (Op_preserves hop hin), hfund, Bool.and_self]
  have hstep : Admits escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) :=
    (verdictOfBool_iff (escrowStepBody_eval st st' _)).1.2 hv
  have hinv : Holds escrowCellContract.invariant (escrowStateToData st') :=
    holds_escrowInvariant st' (Op_preserves hop hin)
  have hlaw : Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) :=
    guardedLaw_admits_of_holds_and_step escrowInvariant_closed hinv hstep
  exact ⟨hlaw, hstep, hinv⟩

theorem escrowOp_satisfies_escrowLaw (facts : Facts) {st st' : EscrowState}
    (hop : EscrowOp st st') (ag pr : String) (nb vu : Nat) (hin : EscrowInv st) :
    Admits escrowKindCell.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) :=
  (escrowOp_admitted_by_contract facts hop ag pr nb vu hin).1

/-- A real funded deposit inhabits the strengthened executable contract. -/
theorem escrowCellContract_inhabited (facts : Facts) :
    ∃ st', Admits escrowCellContract.law (escrowStateToData openedEscrow)
      (escrowStateToData st') (reqOf "alice" "alice" 0 10 writeO facts) := by
  exact ⟨_, (escrowOp_admitted_by_contract facts
    (EscrowOp.deposit openedEscrow .A 7 rfl) "alice" "alice" 0 10 opened_inv).1⟩

/-- Every valid `PrepaidLease` `advance` transition (under `DischargeOk` and budget conservation
    `st.remaining + st.drawn ≤ t.budget`) satisfies the non-trivial `prepaidLeaseLaw`. -/
theorem lease_advance_satisfies_prepaidLeaseLaw (facts : Facts) (t : LeaseTerms) (st : LeaseState)
    (clock amt pidx : Nat) (hok : DischargeOk t st clock amt pidx)
    (hcons : st.remaining + st.drawn ≤ t.budget) :
    prepaidLeaseLaw.denote facts (some (leaseStateToData t st))
      (leaseStateToData t (advance t st)) = true := by
  have hrent : t.rent ≤ st.remaining := hok.2.2.2.2
  have h1 : decide ((Int.ofNat st.dischargedCount : Int) ≤ Int.ofNat (advance t st).dischargedCount) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h2 : decide ((Int.ofNat st.drawn : Int) ≤ Int.ofNat (advance t st).drawn) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h3 : decide ((Int.ofNat (advance t st).drawn : Int) ≤ Int.ofNat t.budget + 0) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h4 : decide (fieldOf "budget" (leaseStateToData t (advance t st)) = some (Int.ofNat t.budget)) = true :=
    decide_eq_true rfl
  have h5 : decide (fieldOf "rent" (leaseStateToData t (advance t st)) = some (Int.ofNat t.rent)) = true :=
    decide_eq_true rfl
  change ((match fieldOf "dischargedCount" (leaseStateToData t st),
                 fieldOf "dischargedCount" (leaseStateToData t (advance t st)) with
           | some v0, some v1 => decide (v0 ≤ v1) | _, _ => false) &&
          ((match fieldOf "drawn" (leaseStateToData t st),
                  fieldOf "drawn" (leaseStateToData t (advance t st)) with
            | some v0, some v1 => decide (v0 ≤ v1) | _, _ => false) &&
           ((match fieldOf "drawn" (leaseStateToData t (advance t st)),
                   fieldOf "budget" (leaseStateToData t (advance t st)) with
             | some v0, some v1 => decide (v0 ≤ v1 + 0) | _, _ => false) &&
            (((Int.ofNat t.budget == 0) ||
              decide (fieldOf "budget" (leaseStateToData t (advance t st)) = some (Int.ofNat t.budget))) &&
             ((Int.ofNat t.rent == 0) ||
              decide (fieldOf "rent" (leaseStateToData t (advance t st)) = some (Int.ofNat t.rent))))))) = true
  rw [leaseStateToData_field_dischargedCount, leaseStateToData_field_dischargedCount,
      leaseStateToData_field_drawn, leaseStateToData_field_drawn,
      h4, h5]
  rw [leaseStateToData_field_budget]
  dsimp only
  simp only [h1, h2, h3, Bool.or_true, Bool.and_self]

/-- Every valid `PrepaidLease` `advance` transition is admitted by `prepaidLeaseCellContract`
    and preserves `prepaidLeaseCellContract.invariant` (`0 Classical.choice`). -/
theorem lease_advance_admitted_by_contract (facts : Facts) (t : LeaseTerms) (st : LeaseState)
    (clock amt pidx : Nat) (hok : DischargeOk t st clock amt pidx)
    (hcons : st.remaining + st.drawn ≤ t.budget)
    (ag pr : String) (nb vu : Nat) :
    Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t (advance t st))
      (reqOf ag pr nb vu writeO facts) ∧
    Admits prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t (advance t st))
      (reqOf ag pr nb vu writeO facts) ∧
    Holds prepaidLeaseCellContract.invariant (leaseStateToData t (advance t st)) := by
  have hrent : t.rent ≤ st.remaining := hok.2.2.2.2
  have h1 : decide (st.dischargedCount ≤ (advance t st).dischargedCount) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h2 : decide (st.drawn ≤ (advance t st).drawn) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h3 : decide ((advance t st).drawn ≤ t.budget) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h4 : decide ((advance t st).remaining ≤ st.remaining) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h5 : decide ((advance t st).remaining ≤ t.budget) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have hv : prepaidLeaseVerdictBool t st (advance t st) = true := by
    simp only [prepaidLeaseVerdictBool, h1, h2, h3, h4, h5, beq_self_eq_true, Bool.or_true, Bool.and_self]
  have hstep : Admits prepaidLeaseCellContract.stepRel (leaseStateToData t st)
      (leaseStateToData t (advance t st)) (reqOf ag pr nb vu writeO facts) :=
    (verdictOfBool_iff (prepaidLeaseStepBody_eval t st (advance t st) _)).1.2 hv
  have hinv : Holds prepaidLeaseCellContract.invariant (leaseStateToData t (advance t st)) :=
    holds_prepaidLeaseInvariant t (advance t st) (by dsimp [advance]; omega) (by dsimp [advance]; omega)
  have hlaw : Admits prepaidLeaseCellContract.law (leaseStateToData t st)
      (leaseStateToData t (advance t st)) (reqOf ag pr nb vu writeO facts) :=
    guardedLaw_admits_of_holds_and_step prepaidLeaseInvariant_closed hinv hstep
  exact ⟨hlaw, hstep, hinv⟩

/-- Constructive `CellContract` refusal of overdrawing `t.budget < st'.drawn` (`0 Classical.choice`). -/
theorem lease_overdraw_contract_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hover : t.budget < st'.drawn) (ag pr : String) (nb vu : Nat) :
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotleNat : decide (st'.drawn ≤ t.budget) = false :=
    decide_eq_false (by omega)
  have hv : prepaidLeaseVerdictBool t st st' = false := by
    simp only [prepaidLeaseVerdictBool, hnotleNat, Bool.false_and, Bool.and_false]
  have href : Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" :=
    (verdictOfBool_iff (prepaidLeaseStepBody_eval t st st' _)).2.2 hv
  have hnotadm : ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
    intro hadm
    obtain ⟨w, hw⟩ := guardedLaw_admits_imp_stepRel prepaidLeaseInvariant_closed hadm
    have heq := evaluates_unique href hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  exact ⟨href, hnotadm⟩

/-- **Refusal Tooth 1 (Overdrawing `drawn > budget`)**:
    Any transition to a lease state `st'` with `t.budget < st'.drawn` is refused by `prepaidLeaseLaw`
    and rejected by `prepaidLeaseCellContract`. -/
theorem lease_overdraw_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hover : t.budget < st'.drawn) (ag pr : String) (nb vu : Nat) :
    prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false ∧
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotle : decide ((Int.ofNat st'.drawn : Int) ≤ Int.ofNat t.budget + 0) = false :=
    decide_eq_false (by simp only [Int.ofNat_eq_natCast]; omega)
  have hden : prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false := by
    simp only [prepaidLeaseLaw, monotone, leField, writeOnce, LawExpr.denote, LawRef.read,
      Option.bind_some, leaseStateToData_field_dischargedCount, leaseStateToData_field_drawn,
      leaseStateToData_field_budget, leaseStateToData_field_rent,
      hnotle, Bool.false_and, Bool.and_false]
  exact ⟨hden, lease_overdraw_contract_refused facts t st st' hover ag pr nb vu⟩

/-- Constructive `CellContract` refusal of decreasing `dischargedCount` (`0 Classical.choice`). -/
theorem lease_rollback_contract_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hdec : st'.dischargedCount < st.dischargedCount) (ag pr : String) (nb vu : Nat) :
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotleNat : decide (st.dischargedCount ≤ st'.dischargedCount) = false :=
    decide_eq_false (by omega)
  have hv : prepaidLeaseVerdictBool t st st' = false := by
    simp only [prepaidLeaseVerdictBool, hnotleNat, Bool.false_and]
  have href : Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" :=
    (verdictOfBool_iff (prepaidLeaseStepBody_eval t st st' _)).2.2 hv
  have hnotadm : ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
    intro hadm
    obtain ⟨w, hw⟩ := guardedLaw_admits_imp_stepRel prepaidLeaseInvariant_closed hadm
    have heq := evaluates_unique href hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  exact ⟨href, hnotadm⟩

/-- **Refusal Tooth 2 (Decreasing `dischargedCount` / Replay Rollback)**:
    Any transition to a lease state `st'` with `st'.dischargedCount < st.dischargedCount` is refused
    by `prepaidLeaseLaw` and rejected by `prepaidLeaseCellContract`. -/
theorem lease_rollback_dischargedCount_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hdec : st'.dischargedCount < st.dischargedCount) (ag pr : String) (nb vu : Nat) :
    prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false ∧
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotle : decide ((Int.ofNat st.dischargedCount : Int) ≤ Int.ofNat st'.dischargedCount) = false :=
    decide_eq_false (by simp only [Int.ofNat_eq_natCast]; omega)
  have hden : prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false := by
    simp only [prepaidLeaseLaw, monotone, leField, writeOnce, LawExpr.denote, LawRef.read,
      Option.bind_some, leaseStateToData_field_dischargedCount, hnotle, Bool.false_and]
  exact ⟨hden, lease_rollback_contract_refused facts t st st' hdec ag pr nb vu⟩

/-- Constructive `CellContract` refusal of rolling back `settled` from 1 to 0 (`0 Classical.choice`). -/
theorem escrow_rollback_contract_refused (facts : Facts) (st st' : EscrowState)
    (hset : escrowSettledTag st = 1) (hunset : escrowSettledTag st' = 0)
    (ag pr : String) (nb vu : Nat) :
    Refuses escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) "escrowLaw" ∧
    ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotleNat : decide (escrowSettledTag st ≤ escrowSettledTag st') = false :=
    decide_eq_false (by rw [hset, hunset]; decide)
  have hv : escrowVerdictBool st st' = false := by
    simp only [escrowVerdictBool, hnotleNat, Bool.false_and, Bool.and_false]
  have href : Refuses escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) "escrowLaw" :=
    (verdictOfBool_iff (escrowStepBody_eval st st' _)).2.2 hv
  have hnotadm : ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) := by
    intro hadm
    obtain ⟨w, hw⟩ := guardedLaw_admits_imp_stepRel escrowInvariant_closed hadm
    have heq := evaluates_unique href hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  exact ⟨href, hnotadm⟩

/-- Registered kind admission refuses rollback through the same proved contract. -/
theorem escrow_unsettled_rollback_refused (facts : Facts) (st st' : EscrowState)
    (hset : escrowSettledTag st = 1) (hunset : escrowSettledTag st' = 0)
    (ag pr : String) (nb vu : Nat) :
    ¬ Admits escrowKindCell.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) :=
  (escrow_rollback_contract_refused facts st st' hset hunset ag pr nb vu).2

/-! ## 5. Coordination with Obend.Ledger.Book & VaultTurn -/

def escrowDepositPosting (escrowAcc : AccountId) (terms : EscrowTerms) (s : Side) : ResourcePosting :=
  match s with
  | .A => ⟨terms.sideA_account, escrowAcc, terms.sideA_asset, terms.sideA_amount⟩
  | .B => ⟨terms.sideB_account, escrowAcc, terms.sideB_asset, terms.sideB_amount⟩

def escrowSettlePostings (escrowAcc : AccountId) (terms : EscrowTerms) : List ResourcePosting :=
  [ ⟨escrowAcc, terms.sideA_account, terms.sideB_asset, terms.sideB_amount⟩,
    ⟨escrowAcc, terms.sideB_account, terms.sideA_asset, terms.sideA_amount⟩ ]

def escrowReclaimPosting (escrowAcc : AccountId) (terms : EscrowTerms) (s : Side) : ResourcePosting :=
  match s with
  | .A => ⟨escrowAcc, terms.sideA_account, terms.sideA_asset, terms.sideA_amount⟩
  | .B => ⟨escrowAcc, terms.sideB_account, terms.sideB_asset, terms.sideB_amount⟩

def leaseAdvancePosting (escrowAcc : AccountId) (terms : LeaseTerms) : ResourcePosting :=
  ⟨escrowAcc, terms.lessor, terms.asset, terms.rent⟩

theorem escrow_settle_conserves_book (b : Book) (escrowAcc : AccountId) (terms : EscrowTerms)
    (hesc : escrowAcc ∈ b.accounts) (hA : terms.sideA_account ∈ b.accounts) (hB : terms.sideB_account ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    ((escrowSettlePostings escrowAcc terms).foldl Book.applyPosting b).totalAsset ast = b.totalAsset ast := by
  simp only [escrowSettlePostings, List.foldl_cons, List.foldl_nil]
  let pB : ResourcePosting := ⟨escrowAcc, terms.sideA_account, terms.sideB_asset, terms.sideB_amount⟩
  let pA : ResourcePosting := ⟨escrowAcc, terms.sideB_account, terms.sideA_asset, terms.sideA_amount⟩
  have h1 : ((b.applyPosting pB).applyPosting pA).totalAsset ast = (b.applyPosting pB).totalAsset ast := by
    exact Book.applyPosting_conserves (b.applyPosting pB) pA hesc hB hnodup ast
  have h2 : (b.applyPosting pB).totalAsset ast = b.totalAsset ast := by
    exact Book.applyPosting_conserves b pB hesc hA hnodup ast
  exact h1.trans h2

theorem lease_advance_conserves_book (b : Book) (escrowAcc : AccountId) (terms : LeaseTerms)
    (hesc : escrowAcc ∈ b.accounts) (hlessor : terms.lessor ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (b.applyPosting (leaseAdvancePosting escrowAcc terms)).totalAsset ast = b.totalAsset ast := by
  exact Book.applyPosting_conserves b (leaseAdvancePosting escrowAcc terms) hesc hlessor hnodup ast

end Obend.Vault.Escrow

end


public section
/-!
Lossless migration of the complete world and serializable capability/escrow state.
Portable mandates interpret finite method allowlists as ordinary vault mandates. The member
tag is keyed cSHAKE authentication. One-shot authority depends on the shared linearized registry;
this module proves its state machine, not a distributed consensus implementation.
CBOR's finite length range is explicit in `HomeArchiveFits`. Accepted migration histories
preserve the source home, or identify an actual collision of its archive commitment.
Bearer secrets are 256 bits wide and `cU64` refuses every wire natural `≥ 2^64`.
The migrated world is the world `Vault.Replay` serves (`Replay.World` abbreviates
`ChunkedWorld.World`); the last section connects its three representations: the portable
archive, the sharded checkpoint, and the authenticated Verkle snapshot recovered from the WAL.
-/
namespace Obend.Vault.PortableContinuation
set_option autoImplicit false
open SurviveFirePor ChunkedWorld Obend.Codec.DetCbor

/-- The portable fragment of a mandate: method filters are finite allowlists.
Its interpretation is an ordinary vault mandate, with the same allowance and authority. -/
structure PortableMandate where
  id : Nat
  grant : Mandate.Grant
  principal : Mandate.Principal
  target : String
  rights : List Mandate.Auth
  budget : Nat
  cells : List Nat
  expiresAt : Nat
  methods : List Nat
  deriving DecidableEq

def PortableMandate.toMandate (m : PortableMandate) : Mandate.Mandate :=
  ⟨m.id, m.grant, m.principal, m.target, m.rights, m.budget, m.cells, m.expiresAt,
    ⟨fun method => m.methods.contains method⟩⟩

/-- A sturdy reference carried across hosts. `swissNum` is the full 256-bit bearer secret. -/
structure SturdyMembraneEntry where
  swissNum : Digest256
  mandate : PortableMandate
  expectedNonce : UInt64
  expiresAt : Nat
  revoked : Bool
  deriving DecidableEq

/-- The leading eight bytes of the secret, a 64-bit locator. It is no longer CapTP's table key
(`swissKey` is) and it does not authenticate a bearer (`SovereignHome.lookupMembrane` compares all
32 bytes). -/
def swissLocator (d : Digest256) : UInt64 :=
  UInt64.ofNat (Obend.Digest.HashBytes.ofBE (d.val.data.toList.take 8))

/-- The key of CapTP's sorted swiss table: all 32 bytes of the secret, read big-endian. -/
def swissKey (d : Digest256) : Obend.Polis.CapTP.SwissNum :=
  BitVec.ofNat 256 (Obend.Digest.HashBytes.ofBE d.val.data.toList)

def SturdyMembraneEntry.toSturdyEntry (e : SturdyMembraneEntry) : Obend.Polis.CapTP.SturdyEntry :=
  ⟨swissKey e.swissNum, e.mandate.toMandate, e.expectedNonce, e.expiresAt, e.revoked⟩

/-- Both escrow legs are serializable; natural-valued amounts cannot be negative. -/
structure EscrowSnapshot where
  statusA : Escrow.LegStatus
  statusB : Escrow.LegStatus
  amountA : Nat
  amountB : Nat
  recvA : Nat
  recvB : Nat
  paidA : Nat
  paidB : Nat
  deriving DecidableEq

def EscrowSnapshot.toEscrowState (e : EscrowSnapshot) : Escrow.EscrowState where
  status := fun s => match s with | .A => e.statusA | .B => e.statusB
  amount := fun s => match s with | .A => e.amountA | .B => e.amountB
  recv := fun s => match s with | .A => e.recvA | .B => e.recvB
  paid := fun s => match s with | .A => e.paidA | .B => e.paidB

structure ReceiptLink where
  previous : Digest256
  payload : List UInt8
  next : Digest256
  deriving DecidableEq

structure SovereignHome where
  world : World
  membranes : List SturdyMembraneEntry
  mandates : List PortableMandate
  escrows : List EscrowSnapshot
  receiptGenesis : Digest256
  receipts : List ReceiptLink
  receiptChainHead : Digest256
  deriving DecidableEq

structure HomeArchive where
  memberId : Nat
  sourceHostId : Nat
  targetHostId : Nat
  migrationEpoch : Nat
  transferNonce : Digest256
  home : SovereignHome
  deriving DecidableEq

/-- Canonical `UInt64` codec. Decoding refuses every natural `≥ 2^64`; it never reduces one
modulo `2^64`, so `n + 2^64` is not a second encoding of `n`. -/
def cU64 : FastCodec UInt64 :=
  cMap UInt64.toNat (fun n => if n < 2 ^ 64 then some (UInt64.ofNat n) else none)
    (by intro n; simp [n.toNat_lt]) cNat

theorem cU64_dec_refuses_overflow (n : Nat) (h : 2 ^ 64 ≤ n) (rest : Log.Bytes) :
    cU64.dec (cNat.enc n ++ rest) = none := by
  have hr := cNat.roundtrip n rest
  have hn : ¬ n < 2 ^ 64 := by omega
  simp [cU64, cMap, rawMap, hr, hn]

/-- A decoded `UInt64` is exactly the natural on the wire. -/
theorem cU64_dec_exact {bs rest : Log.Bytes} {v : UInt64} (h : cU64.dec bs = some (v, rest)) :
    cNat.dec bs = some (v.toNat, rest) := by
  simp only [cU64, cMap, rawMap] at h
  cases hd : cNat.dec bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨n, r⟩ := p
    rw [hd] at h
    if hn : n < 2 ^ 64 then
      simp only [hn, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]
    else
      simp [hn] at h

/-- Wire injectivity without aliasing: two encoded naturals that decode to one `UInt64` are equal. -/
theorem cU64_wire_injective {n m : Nat} {r₁ r₂ t₁ t₂ : Log.Bytes} {v : UInt64}
    (h₁ : cU64.dec (cNat.enc n ++ r₁) = some (v, t₁))
    (h₂ : cU64.dec (cNat.enc m ++ r₂) = some (v, t₂)) : n = m := by
  have e₁ := cU64_dec_exact h₁
  have e₂ := cU64_dec_exact h₂
  rw [cNat.roundtrip] at e₁ e₂
  have a₁ := (Prod.mk.inj (Option.some.inj e₁)).1
  have a₂ := (Prod.mk.inj (Option.some.inj e₂)).1
  omega

def cPrincipal : FastCodec Mandate.Principal :=
  cMap (fun p => (p.name, p.id)) (fun (n, i) => some ⟨n, i⟩)
    (by intro p; cases p; rfl) (cPair cString cNat)

def cGrant : FastCodec Mandate.Grant :=
  cMap (fun g => match g with | .root p t => Sum.inl (p, t) | .under n => Sum.inr n)
    (fun g => some (match g with | .inl (p, t) => .root p t | .inr n => .under n))
    (by intro g; cases g <;> rfl) (cSum (cPair cPrincipal cString) cNat)

def authCode : Mandate.Auth → Nat
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7

def decodeAuth : Nat → Option Mandate.Auth
  | 0 => some .read | 1 => some .write | 2 => some .grant | 3 => some .call
  | 4 => some .reply | 5 => some .reset | 6 => some .control | 7 => some .notify | _ => none

def cMandateAuth : FastCodec Mandate.Auth :=
  cMap authCode decodeAuth (by intro a; cases a <;> rfl) cNat

def cPortableMandate : FastCodec PortableMandate :=
  cMap (fun m => (m.id, m.grant, m.principal, m.target, m.rights, m.budget,
      m.cells, m.expiresAt, m.methods))
    (fun (i, g, p, t, r, b, c, e, m) => some ⟨i, g, p, t, r, b, c, e, m⟩)
    (by intro m; cases m; rfl)
    (cPair cNat (cPair cGrant (cPair cPrincipal (cPair cString (cPair (cList cMandateAuth)
      (cPair cNat (cPair (cList cNat) (cPair cNat (cList cNat)))))))))

def cSturdyMembraneEntry : FastCodec SturdyMembraneEntry :=
  cMap (fun e => (e.swissNum, e.mandate, e.expectedNonce, e.expiresAt, e.revoked))
    (fun (s, m, n, e, r) => some ⟨s, m, n, e, r⟩) (by intro e; cases e; rfl)
    (cPair cDigest256 (cPair cPortableMandate (cPair cU64 (cPair cNat cBool))))

def cLegStatus : FastCodec Escrow.LegStatus :=
  cMap (fun s => match s with | .empty => 0 | .deposited => 1 | .consumed => 2)
    (fun n => match n with | 0 => some .empty | 1 => some .deposited | 2 => some .consumed | _ => none)
    (by intro s; cases s <;> rfl) cNat

def cEscrowSnapshot : FastCodec EscrowSnapshot :=
  cMap (fun e => (e.statusA, e.statusB, e.amountA, e.amountB, e.recvA, e.recvB, e.paidA, e.paidB))
    (fun (a, b, c, d, e, f, g, h) => some ⟨a, b, c, d, e, f, g, h⟩)
    (by intro e; cases e; rfl)
    (cPair cLegStatus (cPair cLegStatus (cPair cNat (cPair cNat (cPair cNat
      (cPair cNat (cPair cNat cNat)))))))

def cReceiptLink : FastCodec ReceiptLink :=
  cMap (fun r => (r.previous, r.payload, r.next)) (fun (p, b, n) => some ⟨p, b, n⟩)
    (by intro r; cases r; rfl) (cPair cDigest256 (cPair cBytes cDigest256))

def cHome : FastCodec SovereignHome :=
  cMap (fun h => (h.world, h.membranes, h.mandates, h.escrows, h.receiptGenesis,
      h.receipts, h.receiptChainHead))
    (fun (w, m, a, e, g, r, h) => some ⟨w, m, a, e, g, r, h⟩)
    (by intro h; cases h; rfl)
    (cPair cWorld (cPair (cList cSturdyMembraneEntry) (cPair (cList cPortableMandate)
      (cPair (cList cEscrowSnapshot) (cPair cDigest256 (cPair (cList cReceiptLink) cDigest256))))))

def cArchive : FastCodec HomeArchive :=
  cMap (fun a => (a.memberId, a.sourceHostId, a.targetHostId, a.migrationEpoch, a.transferNonce, a.home))
    (fun (m, s, t, e, n, h) => some ⟨m, s, t, e, n, h⟩) (by intro a; cases a; rfl)
    (cPair cNat (cPair cNat (cPair cNat (cPair cNat (cPair cDigest256 cHome)))))

/-- Versioned deterministic CBOR framing around the prefix-free fast world/home codec. -/
def archiveCbor (a : HomeArchive) : CborVal :=
  .array [.uint 1, .bytes (cArchive.encodeArray a)]

def encodeHomeArchiveCbor (a : HomeArchive) : ByteArray := encodeDetCbor (archiveCbor a)

def decodeHomeArchiveCbor (bytes : ByteArray) : Option HomeArchive := do
  let .array [.uint 1, .bytes payload] ← decodeDetCbor bytes | none
  let a ← cArchive.decodeExactArray payload
  if encodeHomeArchiveCbor a = bytes then some a else none

/-- CBOR's 64-bit byte-string length limit is an explicit wire-format bound. -/
def HomeArchiveFits (a : HomeArchive) : Prop := WithinWidth (archiveCbor a) = true

instance (a : HomeArchive) : Decidable (HomeArchiveFits a) :=
  inferInstanceAs (Decidable (WithinWidth (archiveCbor a) = true))

theorem archiveCbor_canonical_of_fits (a : HomeArchive) (h : HomeArchiveFits a) :
    CanonicalCbor (archiveCbor a) = true := by
  simpa [HomeArchiveFits, CanonicalCbor, WithinWidth, archiveCbor, wfVal, wfList] using h

theorem decodeHomeArchiveCbor_encode (a : HomeArchive) (h : HomeArchiveFits a) :
    decodeHomeArchiveCbor (encodeHomeArchiveCbor a) = some a := by
  have hc := decodeDetCbor_encodeDetCbor (archiveCbor a) (archiveCbor_canonical_of_fits a h)
  have hr : cArchive.decodeExactArray (cArchive.encodeArray a) = some a := by
    rw [FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc]
  unfold decodeHomeArchiveCbor
  change ((decodeDetCbor (encodeDetCbor (archiveCbor a))).bind _) = some a
  rw [hc]
  simp only [archiveCbor, hr, bind, Option.bind, ite_true]

theorem encodeHomeArchiveCbor_injective (a b : HomeArchive)
    (ha : HomeArchiveFits a) (hb : HomeArchiveFits b)
    (he : encodeHomeArchiveCbor a = encodeHomeArchiveCbor b) : a = b := by
  have hc := encodeDetCbor_injective (archiveCbor a) (archiveCbor b) ha hb he
  simp only [archiveCbor, CborVal.array.injEq, List.cons.injEq, CborVal.bytes.injEq,
    true_and, and_true] at hc
  have hd := congrArg cArchive.decodeExactArray hc
  rw [FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc,
      FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc] at hd
  exact Option.some.inj hd

def archiveDigest (a : HomeArchive) : Digest256 :=
  hash256 "obend.home.archive.v1" (encodeHomeArchiveCbor a)

/-- A shared-secret member authentication tag, not a public-key signature. -/
def memberAuthenticationTag (key : Digest256) (a : HomeArchive) : Digest256 :=
  hash256 "obend.home.member.v1" ((cPair cDigest256 cBytes).encodeArray
    (key, (encodeHomeArchiveCbor a).data.toList))

structure SignedHomeArchive where
  archive : HomeArchive
  digest : Digest256
  memberTag : Digest256
  deriving DecidableEq

def signHomeArchive (key : Digest256) (a : HomeArchive) : SignedHomeArchive :=
  ⟨a, archiveDigest a, memberAuthenticationTag key a⟩

def receiptLinkDigest (r : ReceiptLink) : Digest256 :=
  hash256 "obend.home.receipt.v1" ((cPair cDigest256 cBytes).encodeArray (r.previous, r.payload))

def checkReceiptChain : Digest256 → List ReceiptLink → Digest256 → Bool
  | head, [], expected => decide (head = expected)
  | head, r :: rs, expected => decide (r.previous = head) &&
      decide (r.next = receiptLinkDigest r) && checkReceiptChain r.next rs expected

/-- Bearer lookup by the full 256-bit secret. -/
def SovereignHome.lookupMembrane (h : SovereignHome) (secret : Digest256) :
    Option SturdyMembraneEntry :=
  h.membranes.find? fun e => decide (e.swissNum = secret)

/-- A granted lookup names a membrane of the home whose whole secret was presented: sharing the
64-bit `swissLocator` with some entry grants nothing. -/
theorem lookupMembrane_sound {h : SovereignHome} {secret : Digest256} {e : SturdyMembraneEntry}
    (hf : h.lookupMembrane secret = some e) : e ∈ h.membranes ∧ e.swissNum = secret := by
  have hf' : h.membranes.find? (fun e => decide (e.swissNum = secret)) = some e := hf
  have hd : decide (e.swissNum = secret) = true :=
    List.find?_some (p := fun (x : SturdyMembraneEntry) => decide (x.swissNum = secret)) hf'
  exact ⟨List.mem_of_find?_eq_some hf', of_decide_eq_true hd⟩

theorem lookupMembrane_refuses_unknown_secret {h : SovereignHome} {secret : Digest256}
    (hno : ∀ e ∈ h.membranes, e.swissNum ≠ secret) : h.lookupMembrane secret = none := by
  cases hf : h.lookupMembrane secret with
  | none => rfl
  | some e => exact absurd (lookupMembrane_sound hf).2 (hno e (lookupMembrane_sound hf).1)

def checkHome (h : SovereignHome) : Bool :=
  checkReceiptChain h.receiptGenesis h.receipts h.receiptChainHead &&
    h.escrows.all (fun e => decide (Escrow.enteredTotal e.toEscrowState =
      Escrow.lockedTotal e.toEscrowState + Escrow.paidTotal e.toEscrowState))

structure LiveHome where
  hostId : Nat
  genesis : Digest256
  height : Nat
  home : SovereignHome
  deriving DecidableEq

structure TransferPermit where
  source : Nat
  target : Nat
  epoch : Nat
  nonce : Digest256
  digest : Digest256
  deriving DecidableEq

/-- One member's linearized authority registry. Hosts must consult this shared state
before admission; disconnected copies do not provide one-shot authority. -/
structure MigrationRegistry where
  memberId : Nat
  latestCommittedEpoch : Nat
  active : Option LiveHome
  pending : Option TransferPermit
  consumed : List Digest256
  tombstones : List (Nat × Nat)
  deriving DecidableEq

inductive MigrationRefusal where
  | noActiveSource | transferPending | staleEpoch | nonceConsumed | sameHost
  | noPermit | wrongContext | badAuthentication | malformedHome | tombstoned
  deriving DecidableEq, Repr

def exportHomeArchive (key : Digest256) (r : MigrationRegistry) (target epoch : Nat)
    (nonce : Digest256) : Except MigrationRefusal (SignedHomeArchive × MigrationRegistry) :=
  match r.active with
  | none => .error .noActiveSource
  | some live =>
    if r.pending.isSome then .error .transferPending
    else if epoch ≤ r.latestCommittedEpoch then .error .staleEpoch
    else if nonce ∈ r.consumed then .error .nonceConsumed
    else if target = live.hostId then .error .sameHost
    else
      let a : HomeArchive := ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩
      if !decide (HomeArchiveFits a) then .error .malformedHome
      else .ok (signHomeArchive key a, { r with
        active := none
        pending := some ⟨live.hostId, target, epoch, nonce, archiveDigest a⟩
        tombstones := (live.hostId, epoch) :: r.tombstones })

def importHomeArchive (key genesis : Digest256) (host : Nat) (r : MigrationRegistry)
    (s : SignedHomeArchive) : Except MigrationRefusal MigrationRegistry :=
  if s.archive.transferNonce ∈ r.consumed then .error .nonceConsumed
  else if s.archive.migrationEpoch ≤ r.latestCommittedEpoch then .error .staleEpoch
  else match r.pending with
  | none => .error .noPermit
  | some permit =>
    if r.active.isSome || s.archive.memberId != r.memberId || s.archive.targetHostId != host ||
        s.archive.sourceHostId != permit.source || s.archive.targetHostId != permit.target ||
        s.archive.migrationEpoch != permit.epoch || s.archive.transferNonce != permit.nonce
      then .error .wrongContext
    else if s.digest != permit.digest || s.digest != archiveDigest s.archive ||
        s.memberTag != memberAuthenticationTag key s.archive then .error .badAuthentication
    else if !decide (HomeArchiveFits s.archive) || !checkHome s.archive.home then .error .malformedHome
    else .ok { r with
      latestCommittedEpoch := s.archive.migrationEpoch
      active := some ⟨host, genesis, 0, s.archive.home⟩
      pending := none
      consumed := s.archive.transferNonce :: r.consumed }

/-- A write must hold the current registry slot. An export clears that slot atomically. -/
def admitHomeMutation (host expectedEpoch : Nat) (r : MigrationRegistry) (home : SovereignHome) :
    Except MigrationRefusal MigrationRegistry :=
  match r.active with
  | none => .error .tombstoned
  | some live => if live.hostId = host ∧ r.latestCommittedEpoch = expectedEpoch then
      .ok { r with active := some { live with home := home, height := live.height + 1 } }
    else .error .tombstoned

/-- The destination installs the full decoded payload, changing only host-local wrappers. -/
theorem importHomeArchive_effect (key genesis : Digest256) (host : Nat)
    (r out : MigrationRegistry) (s : SignedHomeArchive)
    (h : importHomeArchive key genesis host r s = .ok out) :
    out.active = some ⟨host, genesis, 0, s.archive.home⟩ ∧
    out.latestCommittedEpoch = s.archive.migrationEpoch ∧
    out.pending = none ∧ out.consumed = s.archive.transferNonce :: r.consumed := by
  simp only [importHomeArchive] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem double_import_or_stale_epoch_refused (key genesis : Digest256) (host : Nat)
    (r : MigrationRegistry) (s : SignedHomeArchive)
    (h : s.archive.transferNonce ∈ r.consumed ∨
      s.archive.migrationEpoch ≤ r.latestCommittedEpoch) :
    importHomeArchive key genesis host r s = .error .nonceConsumed ∨
    importHomeArchive key genesis host r s = .error .staleEpoch := by
  if hn : s.archive.transferNonce ∈ r.consumed then
    left; simp [importHomeArchive, hn]
  else
    right
    have he := h.resolve_left hn
    simp [importHomeArchive, hn, he]

theorem import_replay_refused (key genesis : Digest256) (host otherHost : Nat)
    (r out : MigrationRegistry) (s : SignedHomeArchive)
    (h : importHomeArchive key genesis host r s = .ok out) :
    importHomeArchive key genesis otherHost out s = .error .nonceConsumed := by
  have hc := (importHomeArchive_effect key genesis host r out s h).2.2.2
  simp [importHomeArchive, hc]

theorem tombstoned_source_refused (host expectedEpoch : Nat) (r : MigrationRegistry) (home : SovereignHome)
    (h : r.active = none) : admitHomeMutation host expectedEpoch r home = .error .tombstoned := by
  simp only [admitHomeMutation, h]

/-- Digest binding returns the concrete cSHAKE preimages that collided. -/
def archiveCollision (a b : HomeArchive) (ha : HomeArchiveFits a) (hb : HomeArchiveFits b)
    (hne : a ≠ b) (he : archiveDigest a = archiveDigest b) :
    CshakePair "obend.home.archive.v1" (encodeHomeArchiveCbor a) (encodeHomeArchiveCbor b) :=
  ⟨fun h => hne (encodeHomeArchiveCbor_injective a b ha hb h), congrArg Subtype.val he⟩

/-- All fields, including nonce, epoch, destination, allowances and balances, are bound. -/
def archiveDigest_binding (a b : HomeArchive)
    (ha : HomeArchiveFits a) (hb : HomeArchiveFits b) (hne : a ≠ b) :
    PSum (archiveDigest a ≠ archiveDigest b)
      (CshakePair "obend.home.archive.v1" (encodeHomeArchiveCbor a) (encodeHomeArchiveCbor b)) :=
  if he : archiveDigest a = archiveDigest b then .inr (archiveCollision a b ha hb hne he)
  else .inl he

def totalBalance (h : SovereignHome) : Nat :=
  (h.escrows.map fun e => Escrow.lockedTotal e.toEscrowState + Escrow.paidTotal e.toEscrowState).sum

/-- Every archive component is preserved by destination installation, including the
interpreted capability and escrow states. -/
theorem migrateHome_preserves_pages_membranes_and_balances
    (key genesis : Digest256) (host : Nat) (r out : MigrationRegistry) (s : SignedHomeArchive)
    (h : importHomeArchive key genesis host r s = .ok out) :
    ∃ live, out.active = some live ∧ live.home.world = s.archive.home.world ∧
      live.home.membranes.map SturdyMembraneEntry.toSturdyEntry =
        s.archive.home.membranes.map SturdyMembraneEntry.toSturdyEntry ∧
      live.home.mandates.map PortableMandate.toMandate =
        s.archive.home.mandates.map PortableMandate.toMandate ∧
      live.home.escrows.map EscrowSnapshot.toEscrowState =
        s.archive.home.escrows.map EscrowSnapshot.toEscrowState ∧
      totalBalance live.home = totalBalance s.archive.home := by
  refine ⟨⟨host, genesis, 0, s.archive.home⟩,
    (importHomeArchive_effect key genesis host r out s h).1, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The shared registry grants write authority to at most one host. -/
def HasAuthority (r : MigrationRegistry) (host : Nat) : Prop :=
  ∃ live, r.active = some live ∧ live.hostId = host

theorem authority_unique (r : MigrationRegistry) (a b : Nat)
    (ha : HasAuthority r a) (hb : HasAuthority r b) : a = b := by
  obtain ⟨la, hla, rfl⟩ := ha
  obtain ⟨lb, hlb, rfl⟩ := hb
  have he := Option.some.inj (hla.symm.trans hlb)
  exact congrArg LiveHome.hostId he

inductive MigrationEvent where
  | export (target epoch : Nat) (nonce : Digest256)
  | importArchive (host : Nat) (genesis : Digest256) (archive : SignedHomeArchive)

/-- Histories include hostile archives: a step exists exactly when the executable admits it. -/
inductive ValidMigrationHistory (key : Digest256) :
    MigrationRegistry → List MigrationEvent → MigrationRegistry → Prop where
  | nil (r) : ValidMigrationHistory key r [] r
  | exportStep {r mid out target epoch nonce signed events}
      (step : exportHomeArchive key r target epoch nonce = .ok (signed, mid))
      (tail : ValidMigrationHistory key mid events out) :
      ValidMigrationHistory key r (.export target epoch nonce :: events) out
  | importStep {r mid out host genesis archive events}
      (step : importHomeArchive key genesis host r archive = .ok mid)
      (tail : ValidMigrationHistory key mid events out) :
      ValidMigrationHistory key r (.importArchive host genesis archive :: events) out

/-- Consumption accumulates through arbitrary exports and imports; it is never reset by a hop. -/
theorem migrationHistory_consumed_monotone (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (h : ValidMigrationHistory key r events out) : ∀ nonce ∈ r.consumed, nonce ∈ out.consumed := by
  induction h with
  | nil => exact fun _ h => h
  | @exportStep r mid out target epoch nonce signed events step tail ih =>
    have hc : mid.consumed = r.consumed := by
      simp only [exportHomeArchive] at step
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      split at step <;> try contradiction
      cases step
      rfl
    intro n hn
    exact ih n (hc.symm ▸ hn)
  | @importStep r mid out host genesis archive events step tail ih =>
    have hc := (importHomeArchive_effect key genesis host r mid archive step).2.2.2
    intro n hn
    apply ih
    rw [hc]
    exact List.mem_cons_of_mem _ hn

/-- An admitted archive must match the registry's authenticated export commitment. -/
theorem importHomeArchive_authentic (key genesis : Digest256) (host : Nat)
    (r out : MigrationRegistry) (s : SignedHomeArchive) (permit : TransferPermit)
    (hp : r.pending = some permit) (h : importHomeArchive key genesis host r s = .ok out) :
    archiveDigest s.archive = permit.digest ∧ HomeArchiveFits s.archive := by
  simp only [importHomeArchive, hp] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hauth
  split at h <;> try contradiction
  rename_i hhome
  have he : s.digest = permit.digest ∧ s.digest = archiveDigest s.archive ∧
      s.memberTag = memberAuthenticationTag key s.archive := by
    simpa only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not, and_assoc] using hauth
  refine ⟨he.2.1.symm.trans he.1, ?_⟩
  if hf : HomeArchiveFits s.archive then
    exact hf
  else
    simp only [hf, decide_false, Bool.not_false, Bool.true_or, not_true_eq_false] at hhome

/-- Mutating any archive field either prevents state admission or constructs a concrete
collision. The comparison is against the permit installed when the source was tombstoned. -/
def tampered_homeArchive_refused_or_collision (key genesis : Digest256) (host : Nat)
    (r : MigrationRegistry) (original : HomeArchive) (submitted : SignedHomeArchive)
    (permit : TransferPermit) (hp : r.pending = some permit)
    (hcommit : permit.digest = archiveDigest original) (hfit : HomeArchiveFits original)
    (hneq : submitted.archive ≠ original) :
    PSum (∃ reason, importHomeArchive key genesis host r submitted = .error reason)
      (CshakePair "obend.home.archive.v1" (encodeHomeArchiveCbor submitted.archive)
        (encodeHomeArchiveCbor original)) :=
  match he : importHomeArchive key genesis host r submitted with
  | .error reason => .inl ⟨reason, rfl⟩
  | .ok out =>
    let facts := importHomeArchive_authentic key genesis host r out submitted permit hp he
    .inr (archiveCollision submitted.archive original facts.2 hfit hneq (facts.1.trans hcommit))

/-- Export both carries the complete source home and revokes its live slot in one transition. -/
theorem exportHomeArchive_effect (key : Digest256) (r frozen : MigrationRegistry)
    (target epoch : Nat) (nonce : Digest256) (signed : SignedHomeArchive)
    (h : exportHomeArchive key r target epoch nonce = .ok (signed, frozen)) :
    ∃ source, r.active = some source ∧ signed.archive.home = source.home ∧
      frozen.active = none ∧ frozen.consumed = r.consumed ∧
      frozen.tombstones = (source.hostId, epoch) :: r.tombstones := by
  simp only [exportHomeArchive] at h
  split at h <;> try contradiction
  rename_i live hlive
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨live, hlive, rfl, rfl, rfl, rfl⟩

/-- Complete source-to-destination preservation, including wrapper re-anchoring. -/
theorem export_import_preserves_home (key genesis : Digest256) (target epoch : Nat)
    (nonce : Digest256) (before frozen after : MigrationRegistry) (signed : SignedHomeArchive)
    (he : exportHomeArchive key before target epoch nonce = .ok (signed, frozen))
    (hi : importHomeArchive key genesis target frozen signed = .ok after) :
    ∃ source destination, before.active = some source ∧ after.active = some destination ∧
      source.home = destination.home ∧ totalBalance source.home = totalBalance destination.home := by
  obtain ⟨source, hs, hh, _, _, _⟩ := exportHomeArchive_effect key before frozen target epoch nonce signed he
  have hd := (importHomeArchive_effect key genesis target frozen after signed hi).1
  refine ⟨source, ⟨target, genesis, 0, signed.archive.home⟩, hs, hd, hh.symm, ?_⟩
  exact congrArg totalBalance hh.symm

/-- An old slot token stays stale even if a later migration returns to the same physical host. -/
theorem stale_source_slot_refused (host epoch : Nat) (r : MigrationRegistry) (home : SovereignHome)
    (he : r.latestCommittedEpoch ≠ epoch) :
    admitHomeMutation host epoch r home = .error .tombstoned := by
  unfold admitHomeMutation
  cases r.active <;> simp only [he, and_false, ite_false]

/-- The archive installed by a permit; all metadata is determined by the registry and permit. -/
def originArchive (home : SovereignHome) (r : MigrationRegistry) (p : TransferPermit) : HomeArchive :=
  ⟨r.memberId, p.source, p.target, p.epoch, p.nonce, home⟩

def archivePreimage (a : HomeArchive) : List UInt8 := (encodeHomeArchiveCbor a).data.toList

def archiveHash := Obend.Digest.Cshake256.cshake256Bytes "obend.home.archive.v1".toUTF8.data.toList

/-- Exactly the submitted and provenance preimages compared at an import. -/
def importPreimages (home : SovereignHome) (r : MigrationRegistry) (s : SignedHomeArchive) :
    List (List UInt8) :=
  archivePreimage s.archive :: (r.pending.toList.map fun p => archivePreimage (originArchive home r p))

/-- Finite comparison transcript of the executable history, including hostile submissions. -/
def migrationPreimages (home : SovereignHome) (key : Digest256) :
    MigrationRegistry → List MigrationEvent → List (List UInt8)
  | _, [] => []
  | r, .export target epoch nonce :: es =>
    match exportHomeArchive key r target epoch nonce with
    | .ok (_, mid) => migrationPreimages home key mid es
    | .error _ => []
  | r, .importArchive host genesis s :: es =>
    importPreimages home r s ++ (match importHomeArchive key genesis host r s with
    | .ok mid => migrationPreimages home key mid es
    | .error _ => [])

/-- While authority is in transit, the registry keeps the commitment of the same home.
The archive witness is logical provenance, not data copied into the runtime registry. -/
structure HomeOrigin (home : SovereignHome) (r : MigrationRegistry) : Prop where
  active : ∀ live, r.active = some live → live.home = home
  pending : ∀ permit, r.pending = some permit →
    HomeArchiveFits (originArchive home r permit) ∧
      archiveDigest (originArchive home r permit) = permit.digest

theorem export_preserves_origin (home : SovereignHome) (key : Digest256)
    (r frozen : MigrationRegistry) (target epoch : Nat) (nonce : Digest256) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r)
    (h : exportHomeArchive key r target epoch nonce = .ok (signed, frozen)) : HomeOrigin home frozen := by
  simp only [exportHomeArchive] at h
  split at h <;> try contradiction
  rename_i live hlive
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hfits
  have hf : HomeArchiveFits ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩ := by
    if hf : HomeArchiveFits ⟨r.memberId, live.hostId, target, epoch, nonce, live.home⟩ then
      exact hf
    else
      simp only [hf, decide_false, Bool.not_false, not_true_eq_false] at hfits
  cases h
  constructor
  · intro other ho; cases ho
  · intro permit hp
    cases hp
    have he := origin.active live hlive
    constructor
    · simpa only [originArchive, ← he] using hf
    · simp only [originArchive, ← he]

/-- Executable collision pair, with membership in this import's finite comparison transcript. -/
structure ArchiveCollisionOn (inputs : List (List UInt8)) : Type where
  left : List UInt8
  right : List UInt8
  left_mem : left ∈ inputs
  right_mem : right ∈ inputs
  distinct : left ≠ right
  sameDigest : Obend.Digest.HashBytes.ofBE (archiveHash left) =
    Obend.Digest.HashBytes.ofBE (archiveHash right)
theorem ArchiveCollisionOn.toCollisionAmong {inputs : List (List UInt8)} (w : ArchiveCollisionOn inputs) :
    Obend.Digest.HashBytes.CollisionAmong archiveHash (fun x => x ∈ inputs) :=
  ⟨w.left, w.right, w.left_mem, w.right_mem, w.distinct, w.sameDigest⟩

def extractImportOriginBreak (home : SovereignHome) (key genesis : Digest256)
    (host : Nat) (r out : MigrationRegistry) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r)
    (h : importHomeArchive key genesis host r signed = .ok out) :
    PSum (HomeOrigin home out) (ArchiveCollisionOn (importPreimages home r signed)) := by
  cases hp : r.pending with
  | none =>
    simp only [importHomeArchive, hp] at h
    split at h <;> try contradiction
    split at h <;> contradiction
  | some permit =>
    let original := originArchive home r permit
    have hhome : original.home = home := rfl
    obtain ⟨hfit, hcommit⟩ := origin.pending permit hp
    have facts := importHomeArchive_authentic key genesis host r out signed permit hp h
    if he : signed.archive = original then
      apply PSum.inl
      have effect := importHomeArchive_effect key genesis host r out signed h
      constructor
      · intro live hlive
        rw [effect.1] at hlive
        cases hlive
        exact he ▸ hhome
      · intro other ho
        rw [effect.2.2.1] at ho
        cases ho
    else
      apply PSum.inr
      let pair := archiveCollision signed.archive original facts.2 hfit he
        (facts.1.trans hcommit.symm)
      refine ⟨archivePreimage signed.archive, archivePreimage original,
        by simp [importPreimages], by simp [importPreimages, hp, original], ?_, ?_⟩
      · intro hpre; apply pair.distinct
        exact byteArrayList_injective hpre
      · exact congrArg (fun x : ByteArray => Obend.Digest.HashBytes.ofBE x.data.toList) pair.sameDigest

theorem import_preserves_origin_or_collision (home : SovereignHome) (key genesis : Digest256)
    (host : Nat) (r out : MigrationRegistry) (signed : SignedHomeArchive)
    (origin : HomeOrigin home r) (h : importHomeArchive key genesis host r signed = .ok out) :
    HomeOrigin home out ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ importPreimages home r signed) :=
  match extractImportOriginBreak home key genesis host r out signed origin h with
  | .inl ho => .inl ho
  | .inr w => .inr w.toCollisionAmong

/-- Arbitrary accepted migration traces preserve the complete source home, including its
escrow value and mandate allowances, unless they furnish a cSHAKE collision. -/
theorem migrationHistory_preserves_home_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r) :
    HomeOrigin home out ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  induction history with
  | nil => exact Or.inl origin
  | @exportStep r mid out target epoch nonce signed events step tail ih =>
    simpa only [migrationPreimages, step] using
      ih (export_preserves_origin home key r mid target epoch nonce signed origin step)
  | @importStep r mid out host genesis archive events step tail ih =>
    rcases import_preserves_origin_or_collision home key genesis host r mid archive origin step with ho | hc
    · rcases ih ho with ho' | hc
      · exact .inl ho'
      · exact .inr (hc.mono (by
          intro x hx
          simp only [migrationPreimages, step]
          exact List.mem_append_right _ hx))
    · exact .inr (hc.mono (by
        intro x hx
        simp only [migrationPreimages, step]
        exact List.mem_append_left _ hx))

theorem migrationHistory_balance_conserved_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (live : LiveHome) (hlive : out.active = some live) :
    totalBalance live.home = totalBalance home ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · exact Or.inl (congrArg totalBalance (ho.active live hlive))
  · exact Or.inr hc

/-! ## The replayed world, its portable archive, its sharded checkpoint and its snapshot

`Vault.Replay.World` is an abbreviation of `ChunkedWorld.World`: the world a home carries is
already the type the log replays, so there is no conversion between the two to prove. What a
migration has to connect is the world's representations and the session it continues. -/

open VerkleSnapshotBridge in
/-- Project a portable archive to the sharded checkpoint form `Replay.decodeCheckpointWorld` reads. -/
def archiveToSharded (bytes : ByteArray) : Option ShardedWorld :=
  (decodeHomeArchiveCbor bytes).map fun a => encodeShardedWorld a.home.world

/-- Rehydrate the replay world of a sharded checkpoint. -/
def rehydrateWorld (s : ShardedWorld) : Option Replay.World :=
  match decodeShardedWorld s with
  | .ok w => some w
  | .error _ => none

/-- Archive → sharded checkpoint → world is lossless on every archive that fits CBOR. -/
theorem archive_sharded_rehydrate (a : HomeArchive) (h : HomeArchiveFits a) :
    (archiveToSharded (encodeHomeArchiveCbor a)).bind rehydrateWorld = some a.home.world := by
  simp [archiveToSharded, rehydrateWorld, decodeHomeArchiveCbor_encode a h,
    decodeShardedWorld_encodeShardedWorld]

/-- The checkpoint decoder of the deployed replay machine reads the migrated world back from the
manifest it commits to, given a store holding the shards of the projected archive. -/
theorem archive_checkpoint_rehydrate (a : HomeArchive) (store : String → Option Log.Bytes)
    (hstore : ∀ k sb, (k, sb) ∈ (encodeShardedWorld a.home.world).shards → store k = some sb) :
    Replay.decodeCheckpointWorld store (Replay.deployed.encW a.home.world) = some a.home.world := by
  have hm := decodeManifestWith_manifestBytes a.home.world store hstore
  change Replay.decodeCheckpointWorld store (manifestBytes a.home.world) = _
  simp [Replay.decodeCheckpointWorld, hm]

/-- **Migration continues the replay session.** If the source home carried the world of a
reachable `Replay` session, then after any accepted migration history the live home's world is the
replay of that session's log, the session over the migrated world is reachable, and it admits
every next turn exactly as the source would have; or the history exhibits a cSHAKE collision. -/
theorem migrationHistory_continues_replay_or_collision (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (S : Replay.Session) (hS : Replay.Reachable S) (hw : home.world = S.world)
    (live : LiveHome) (hlive : out.active = some live) :
    (live.home.world = Log.replay Replay.deployed Replay.genesis S.log ∧
      Replay.Reachable ⟨live.home.world, S.log⟩ ∧
      ∀ b : Log.Bytes, (⟨live.home.world, S.log⟩ : Replay.Session).admit Replay.logHash
          Replay.deployed b = S.admit Replay.logHash Replay.deployed b) ∨
    Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · left
    have hlw : live.home.world = S.world := (congrArg SovereignHome.world (ho.active live hlive)).trans hw
    have hSeq : (⟨live.home.world, S.log⟩ : Replay.Session) = S := by cases S; simp_all
    exact ⟨hlw.trans (Replay.state_eq_replay_log hS), hSeq ▸ hS, fun b => by rw [hSeq]⟩
  · exact Or.inr hc

open VerkleSnapshotBridge in
/-- Crash recovery from the session's WAL bytes (with any uncommitted tail) rebuilds exactly the
authenticated snapshot of a world equal to the one the session serves. -/
theorem walRecovery_snapshot_of_session (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (S : Replay.Session) (hS : Replay.Reachable S) (w : Replay.World) (hw : w = S.world)
    {tornTail : Log.Bytes} (htorn : UncommittedWalTail Replay.logHash
      (Log.lastHash Replay.logHash Rehydration.genesisSentinel S.log) tornTail) :
    (recoverWalSnapshot pp hCols Replay.deployed Replay.genesis
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).snapshot =
        buildAuthenticatedSnapshot pp hCols w := by
  obtain ⟨hlinked, hwf⟩ := Log.log_sound hS
  have hparse := Log.parseFrom_encodeAll Replay.logHash S.log Rehydration.genesisSentinel
    hlinked hwf tornTail
  have htail := (parseFrom_uncommittedWalTail Replay.logHash _ htorn).1
  unfold recoverWalSnapshot; dsimp only
  rw [hparse, htail, List.append_nil, hw, Replay.state_eq_replay_log hS]

open VerkleSnapshotBridge in
/-- Destination-side check: the home's world has the snapshot root of the world the WAL replays to. -/
def checkHomeAgainstWal (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) : Bool :=
  decide ((buildAuthenticatedSnapshot pp hCols home.world).snapshotRoot =
    (recoverWalSnapshot pp hCols Replay.deployed Replay.genesis wal).snapshot.snapshotRoot)

open VerkleSnapshotBridge in
/-- The snapshot WAL recovery builds is the snapshot of the replay of the parsed records. -/
theorem recoverWalSnapshot_snapshot (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (wal : Log.Bytes) :
    (recoverWalSnapshot pp hCols Replay.deployed Replay.genesis wal).snapshot =
      buildAuthenticatedSnapshot pp hCols (Log.replay Replay.deployed Replay.genesis
        (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1) := by
  unfold recoverWalSnapshot; dsimp only

open VerkleSnapshotBridge in
theorem checkHomeAgainstWal_iff (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) :
    checkHomeAgainstWal pp hCols home wal = true ↔
      (buildAuthenticatedSnapshot pp hCols home.world).snapshotRoot =
        (buildAuthenticatedSnapshot pp hCols (Log.replay Replay.deployed Replay.genesis
          (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1)).snapshotRoot := by
  unfold checkHomeAgainstWal
  rw [recoverWalSnapshot_snapshot]
  exact decide_eq_true_iff

open VerkleSnapshotBridge in
/-- **Completeness across migration.** After any accepted migration history of a home that carried
a reachable session's world, the live home passes the WAL check against that session's log, torn
tail or not; or the history exhibits a cSHAKE collision. -/
theorem migratedHome_passes_wal_check_or_collision (pp : Obend.Crypto.AjtaiParams)
    (hCols : pp.cols = 64) (home : SovereignHome) (key : Digest256)
    (r out : MigrationRegistry) (events : List MigrationEvent)
    (history : ValidMigrationHistory key r events out) (origin : HomeOrigin home r)
    (S : Replay.Session) (hS : Replay.Reachable S) (hw : home.world = S.world)
    (live : LiveHome) (hlive : out.active = some live)
    {tornTail : Log.Bytes} (htorn : UncommittedWalTail Replay.logHash
      (Log.lastHash Replay.logHash Rehydration.genesisSentinel S.log) tornTail) :
    checkHomeAgainstWal pp hCols live.home
      (Log.encodeAll Replay.logHash S.log ++ tornTail) = true ∨ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r events) := by
  rcases migrationHistory_preserves_home_or_collision home key r out events history origin with ho | hc
  · left
    have hlw : live.home.world = S.world := (congrArg SovereignHome.world (ho.active live hlive)).trans hw
    unfold checkHomeAgainstWal
    rw [walRecovery_snapshot_of_session pp hCols S hS live.home.world hlw htorn]
    exact decide_eq_true rfl
  · exact Or.inr hc

open VerkleSnapshotBridge in
/-- Two well-formed snapshots with one snapshot root have one 256-bit `VerkleUmem` root, or their
two snapshot-root headers are a named `treeHash` collision. -/
def snapshotRoot_binds_verkleRoot {pp : Obend.Crypto.AjtaiParams} {hCols : pp.cols = 64}
    {s t : AuthenticatedWorldSnapshot} (hs : SnapshotWF pp hCols s) (ht : SnapshotWF pp hCols t)
    (h : s.snapshotRoot = t.snapshotRoot) :
    PSum (s.verkleRoot = t.verkleRoot)
      (Obend.Judge.Computational.HashCollisionWitness Obend.Polis.treeHash verkleMaxPreimageBytes) :=
  have hsz : ∀ {u : AuthenticatedWorldSnapshot}, SnapshotWF pp hCols u → u.verkleRoot.size = 32 :=
    fun hwf => by rw [snapshotWF_verkleRoot_eq_fullCommit hwf]; exact fullVerkleCommitChunks_size _
  match extractSnapshotRootBreak (by rw [hs.1]; decide) (by rw [ht.1]; decide) (hsz hs) (hsz ht) h with
  | .inl heq => .inl heq.2
  | .inr col => .inr col.val

open VerkleSnapshotBridge in
/-- **Soundness of the WAL check.** A home that passes has the 256-bit `VerkleUmem` root of the
world the WAL replays to, or the two snapshot-root headers are a named `treeHash` collision. -/
def checkHomeAgainstWal_sound (pp : Obend.Crypto.AjtaiParams) (hCols : pp.cols = 64)
    (home : SovereignHome) (wal : Log.Bytes) (h : checkHomeAgainstWal pp hCols home wal = true) :
    PSum (fullVerkleCommitWorld home.world = fullVerkleCommitWorld
        (Log.replay Replay.deployed Replay.genesis
          (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1))
      (Obend.Judge.Computational.HashCollisionWitness Obend.Polis.treeHash verkleMaxPreimageBytes) :=
  match snapshotRoot_binds_verkleRoot (buildAuthenticatedSnapshot_wf pp hCols home.world)
      (buildAuthenticatedSnapshot_wf pp hCols (Log.replay Replay.deployed Replay.genesis
        (Log.parseFrom Replay.logHash Rehydration.genesisSentinel wal).1))
      ((checkHomeAgainstWal_iff pp hCols home wal).1 h) with
  | .inl heq => .inl ((buildAuthenticatedSnapshot_verkleRoot pp hCols home.world).symm.trans
      (heq.trans (buildAuthenticatedSnapshot_verkleRoot pp hCols _)))
  | .inr col => .inr col

end Obend.Vault.PortableContinuation


public section
namespace Obend.Polis.Custody
open Obend.Crypto Obend.Digest.Cshake256
set_option autoImplicit false

/-- Single `(domain, fields)` invocation of `Custody.hash` (`cSHAKE256`). -/
abbrev CshakeCall := String × List (List UInt8)

def hash (domain : String) (fields : List (List UInt8)) : ByteArray :=
  cshake32ByteArray domain.toUTF8.data.toList (encodeFields fields)

theorem hash_size (d : String) (xs : List (List UInt8)) : (hash d xs).size = 32 :=
  cshake32ByteArray_size _ _

/-- Constructive `0 Classical` full-width cSHAKE256 collision witness pinned to a finite list
    `calls` of `(domain, fields)` evaluations actually computed on the executed trace. -/
structure CshakeCallCollision (calls : List CshakeCall) where
  domain : String
  leftFields : List (List UInt8)
  rightFields : List (List UInt8)
  leftMem : (domain, leftFields) ∈ calls
  rightMem : (domain, rightFields) ∈ calls
  distinct : encodeFields leftFields ≠ encodeFields rightFields
  sameDigest : hash domain leftFields = hash domain rightFields
  deriving DecidableEq

def CshakeCallCollision.weaken {c₁ c₂ : List CshakeCall}
    (hSub : ∀ c ∈ c₁, c ∈ c₂) (w : CshakeCallCollision c₁) : CshakeCallCollision c₂ :=
  { w with leftMem := hSub _ w.leftMem, rightMem := hSub _ w.rightMem }

def CshakeCallCollision.weakenLeft {c₁ c₂ : List CshakeCall}
    (w : CshakeCallCollision c₁) : CshakeCallCollision (c₁ ++ c₂) :=
  w.weaken (fun _ hm => List.mem_append_left c₂ hm)

def CshakeCallCollision.weakenRight {c₁ c₂ : List CshakeCall}
    (w : CshakeCallCollision c₂) : CshakeCallCollision (c₁ ++ c₂) :=
  w.weaken (fun _ hm => List.mem_append_right c₁ hm)

/-- Finite-domain `CollisionAmong` proposition over an explicit executed call list `calls`. -/
def CshakeCollisionAmong (calls : List CshakeCall) : Prop :=
  Nonempty (CshakeCallCollision calls)

/-- Decidable finite-trace collision checker over `calls : List CshakeCall`. -/
def cshakeCollisionFree (calls : List CshakeCall) : Bool :=
  calls.all fun c₁ =>
    calls.all fun c₂ =>
      if decide (c₁.1 = c₂.1) then
        if decide (encodeFields c₁.2 = encodeFields c₂.2) then true
        else decide (hash c₁.1 c₁.2 ≠ hash c₂.1 c₂.2)
      else true

theorem not_cshakeCollisionAmong_of_free {calls : List CshakeCall}
    (hFree : cshakeCollisionFree calls = true) :
    ¬ CshakeCollisionAmong calls := by
  rintro ⟨w⟩
  simp only [cshakeCollisionFree, List.all_eq_true] at hFree
  have h1 := hFree (w.domain, w.leftFields) w.leftMem (w.domain, w.rightFields) w.rightMem
  have hNe : ¬ (encodeFields w.leftFields = encodeFields w.rightFields) := w.distinct
  have hDecNe : decide (encodeFields w.leftFields = encodeFields w.rightFields) = false :=
    decide_eq_false hNe
  simp only [decide_true, hDecNe, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h1
  exact h1 w.sameDigest

theorem CshakeCallCollision.toCollisionAmong {calls : List CshakeCall}
    (w : CshakeCallCollision calls) :
    Obend.Digest.HashBytes.CollisionAmong
      (cshake256Bytes w.domain.toUTF8.data.toList)
      (fun m => ∃ fs, (w.domain, fs) ∈ calls ∧ m = encodeFields fs) := by
  refine ⟨encodeFields w.leftFields, encodeFields w.rightFields,
    ⟨w.leftFields, w.leftMem, rfl⟩, ⟨w.rightFields, w.rightMem, rfl⟩, w.distinct, ?_⟩
  have hBytes :
      cshake256Bytes w.domain.toUTF8.data.toList (encodeFields w.leftFields) =
      cshake256Bytes w.domain.toUTF8.data.toList (encodeFields w.rightFields) := by
    have hEq := congrArg (fun b : ByteArray => b.data.toList) w.sameDigest
    simpa [hash, cshake32ByteArray, cshake256Bytes, Native.bytesOfList_toList] using hEq
  rw [hBytes]

/-- Constructive `0 Classical` single-call binding extractor for `Custody.hash`. -/
def hashExtract (d : String) (xs ys : List (List UInt8)) (h : hash d xs = hash d ys) :
    PSum (PLift (xs = ys)) (CshakeCallCollision [(d, xs), (d, ys)]) :=
  if hp : encodeFields xs = encodeFields ys then
    .inl ⟨encodeFields_injective _ _ hp⟩
  else
    .inr ⟨d, xs, ys, .head _, .tail _ (.head _), hp, h⟩

/-- Length-framed Merkle spine. Each node commits its payload and the complete tail root. -/
def merkle : List (List UInt8) → ByteArray
  | [] => hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" []
  | x :: xs => hash "OBEND.CUSTODY.MERKLE.NODE/v1" [[1], x, (merkle xs).data.toList]

/-- Exact finite list of `Custody.hash` evaluations performed by `merkle xs`. -/
def merkleCalls : List (List UInt8) → List CshakeCall
  | [] => [("OBEND.CUSTODY.MERKLE.EMPTY/v1", [])]
  | x :: xs => ("OBEND.CUSTODY.MERKLE.NODE/v1", [[1], x, (merkle xs).data.toList]) :: merkleCalls xs

/-- Reverse array traversal is stack-bounded; the specification remains a Merkle list. -/
def merkleExec (xs : Array (List UInt8)) : ByteArray :=
  xs.foldr (fun x tail => hash "OBEND.CUSTODY.MERKLE.NODE/v1" [[1], x, tail.data.toList])
    (hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" [])

theorem merkle_eq_foldr (xs : List (List UInt8)) :
    merkle xs = xs.foldr
      (fun x tail => hash "OBEND.CUSTODY.MERKLE.NODE/v1" [[1], x, tail.data.toList])
      (hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [merkle, List.foldr_cons, ih]

theorem merkle_exec_eq (xs : Array (List UInt8)) : merkleExec xs = merkle xs.toList := by
  rw [merkle_eq_foldr, Array.foldr_toList]
  rfl

def merkleFast (xs : List (List UInt8)) : ByteArray := merkleExec xs.toArray
@[csimp] theorem merkle_eq_fast : merkle = merkleFast := by
  funext xs
  simp only [merkleFast, merkle_exec_eq]

/-- The count is committed separately, so empty and nonempty shapes cannot alias unnoticed. -/
def merkleRoot (xs : List (List UInt8)) : ByteArray :=
  hash "OBEND.CUSTODY.MERKLE.ROOT/v1" [leb128 xs.length, (merkle xs).data.toList]

/-- Exact finite list of `Custody.hash` evaluations performed by `merkleRoot xs`. -/
def merkleRootCalls (xs : List (List UInt8)) : List CshakeCall :=
  ("OBEND.CUSTODY.MERKLE.ROOT/v1", [leb128 xs.length, (merkle xs).data.toList]) :: merkleCalls xs

theorem natBytes_inj {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

/-- Constructive `0 Classical` Merkle spine binding extractor pinned to `merkleCalls xs ++ merkleCalls ys`. -/
def merkleExtract : ∀ (xs ys : List (List UInt8)), xs.length = ys.length →
    merkle xs = merkle ys →
    PSum (PLift (xs = ys)) (CshakeCallCollision (merkleCalls xs ++ merkleCalls ys))
  | [], [], _, _ => .inl ⟨rfl⟩
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | x :: xs, y :: ys, hl, h =>
    match hashExtract "OBEND.CUSTODY.MERKLE.NODE/v1"
        [[1], x, (merkle xs).data.toList] [[1], y, (merkle ys).data.toList] h with
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact List.mem_append_left _ (.head _)
        · exact List.mem_append_right _ (.head _)))
    | .inl hp =>
      have hp' : x = y ∧ (merkle xs).data.toList = (merkle ys).data.toList := by simpa using hp.down
      match merkleExtract xs ys (Nat.succ.inj hl) (byteArray_eq_of_toList_eq hp'.2) with
      | .inl he => .inl ⟨by rw [hp'.1, he.down]⟩
      | .inr hc =>
        .inr (hc.weaken (by
          intro c hmem
          rcases List.mem_append.1 hmem with hL | hR
          · exact List.mem_append_left _ (.tail _ hL)
          · exact List.mem_append_right _ (.tail _ hR)))

/-- Constructive `0 Classical` `merkleRoot` binding extractor pinned to `merkleRootCalls xs ++ merkleRootCalls ys`. -/
def merkleRootExtract (xs ys : List (List UInt8)) (h : merkleRoot xs = merkleRoot ys) :
    PSum (PLift (xs = ys)) (CshakeCallCollision (merkleRootCalls xs ++ merkleRootCalls ys)) :=
  match hashExtract "OBEND.CUSTODY.MERKLE.ROOT/v1"
      [leb128 xs.length, (merkle xs).data.toList] [leb128 ys.length, (merkle ys).data.toList] h with
  | .inr hc =>
    .inr (hc.weaken (by
      intro c hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact List.mem_append_left _ (.head _)
      · exact List.mem_append_right _ (.head _)))
  | .inl hp =>
    have hp' : leb128 xs.length = leb128 ys.length ∧
        (merkle xs).data.toList = (merkle ys).data.toList := by simpa using hp.down
    match merkleExtract xs ys (natBytes_inj hp'.1) (byteArray_eq_of_toList_eq hp'.2) with
    | .inl he => .inl he
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        rcases List.mem_append.1 hmem with hL | hR
        · exact List.mem_append_left _ (.tail _ hL)
        · exact List.mem_append_right _ (.tail _ hR)))

structure PrepaidLease where
  leaseId : UInt64
  startPeriod : Nat
  nextDue : Nat
  rent : Nat
  initialBudget : Nat
  remaining : Nat
  drawn : Nat
  deriving DecidableEq, Repr

def openLease (id : UInt64) (start rent budget : Nat) : PrepaidLease :=
  ⟨id, start, start, rent, budget, budget, 0⟩

inductive LeaseRefusal where
  | replay | offSchedule | overDraw | insufficientBudget
  deriving DecidableEq, Repr

def advanceLease (l : PrepaidLease) : PrepaidLease :=
  { l with
    nextDue := l.nextDue + 1
    remaining := l.remaining - l.rent
    drawn := l.drawn + l.rent }

def dischargePeriod (l : PrepaidLease) (period requestedAmount : Nat) :
    Except LeaseRefusal PrepaidLease :=
  if period < l.nextDue then .error .replay
  else if period > l.nextDue then .error .offSchedule
  else if requestedAmount ≠ l.rent then .error .overDraw
  else if l.remaining < l.rent then .error .insufficientBudget
  else .ok (advanceLease l)

theorem dischargePeriod_success {l l' : PrepaidLease} {p a : Nat}
    (h : dischargePeriod l p a = .ok l') :
    p = l.nextDue ∧ a = l.rent ∧ l.rent ≤ l.remaining ∧ l' = advanceLease l := by
  unfold dischargePeriod at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all <;> omega

theorem replay_rejected (l : PrepaidLease) (p a : Nat) (h : p < l.nextDue) :
    dischargePeriod l p a = .error .replay := by simp [dischargePeriod, h]

theorem off_schedule_rejected (l : PrepaidLease) (p a : Nat) (h : p > l.nextDue) :
    dischargePeriod l p a = .error .offSchedule := by
  simp [dischargePeriod, h, show ¬ p < l.nextDue by omega]

theorem over_draw_rejected (l : PrepaidLease) (a : Nat) (h : a ≠ l.rent) :
    dischargePeriod l l.nextDue a = .error .overDraw := by simp [dischargePeriod, h]

theorem insufficient_budget_rejected (l : PrepaidLease) (h : l.remaining < l.rent) :
    dischargePeriod l l.nextDue l.rent = .error .insufficientBudget := by
  simp [dischargePeriod, h]

/-- Counts actual successful transitions, including arbitrary submitted periods and amounts. -/
inductive ReachableLease (id : UInt64) (start rent budget : Nat) : Nat → PrepaidLease → Prop
  | initial : ReachableLease id start rent budget 0 (openLease id start rent budget)
  | step {n l l' p a} : ReachableLease id start rent budget n l →
      dischargePeriod l p a = .ok l' → ReachableLease id start rent budget (n + 1) l'

theorem reachable_equations {id : UInt64} {start rent budget n : Nat} {l : PrepaidLease}
    (h : ReachableLease id start rent budget n l) :
    l.leaseId = id ∧ l.startPeriod = start ∧ l.rent = rent ∧ l.initialBudget = budget ∧
    l.nextDue = start + n ∧ l.drawn = n * rent ∧ l.remaining + l.drawn = budget := by
  induction h with
  | initial => simp [openLease]
  | @step n l l' p a _ hs ih =>
    obtain ⟨_, _, hc, rfl⟩ := dischargePeriod_success hs
    rcases ih with ⟨hi, ht, hr, hb, hn, hd, hsum⟩
    simp only [advanceLease]
    refine ⟨hi, ht, hr, hb, ?_, ?_, ?_⟩
    · omega
    · rw [hd, hr, Nat.add_mul]; simp
    · omega

theorem remainingAfter_eq {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.remaining = b - n * r := by
  have he := reachable_equations h; omega

theorem drawnAfter_eq {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.drawn = n * r :=
  (reachable_equations h).2.2.2.2.2.1

theorem budget_conserved {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.remaining + l.drawn = l.initialBudget := by
  have he := reachable_equations h; omega

theorem metered_equals_drawn {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : (l.nextDue - l.startPeriod) * l.rent = l.drawn := by
  rcases reachable_equations h with ⟨_, hs, hr, _, hn, hd, _⟩
  rw [hs, hr, hn, hd, Nat.add_sub_cancel_left]

theorem budget_never_overdrawn {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.drawn ≤ l.initialBudget := by
  have := budget_conserved h; omega

theorem no_advance_without_draw_rejected (l l' : PrepaidLease) (p a : Nat)
    (h : l'.drawn ≠ l.drawn + l.rent) : dischargePeriod l p a ≠ .ok l' := by
  intro hs; obtain ⟨_, _, _, rfl⟩ := dischargePeriod_success hs
  exact h rfl

theorem no_draw_without_advance_rejected (l l' : PrepaidLease) (p a : Nat)
    (h : l'.nextDue ≠ l.nextDue + 1) : dischargePeriod l p a ≠ .ok l' := by
  intro hs; obtain ⟨_, _, _, rfl⟩ := dischargePeriod_success hs
  exact h rfl

def leaseFields (l : PrepaidLease) : List (List UInt8) :=
  [leb128 l.leaseId.toNat, leb128 l.startPeriod, leb128 l.nextDue, leb128 l.rent,
   leb128 l.initialBudget, leb128 l.remaining, leb128 l.drawn]

theorem leaseFields_inj {a b : PrepaidLease} (h : leaseFields a = leaseFields b) : a = b := by
  simp only [leaseFields, List.cons.injEq, and_true] at h
  rcases h with ⟨hi, hs, hn, hr, hb, hm, hd⟩
  have hi' := UInt64.toNat_inj.1 (natBytes_inj hi)
  have hs' := natBytes_inj hs; have hn' := natBytes_inj hn
  have hr' := natBytes_inj hr; have hb' := natBytes_inj hb
  have hm' := natBytes_inj hm; have hd' := natBytes_inj hd
  cases a; cases b; simp_all

def leaseStateRoot (l : PrepaidLease) : ByteArray := merkleRoot (leaseFields l)

def leaseStateRootCalls (l : PrepaidLease) : List CshakeCall := merkleRootCalls (leaseFields l)

theorem leaseStateRoot_size (l : PrepaidLease) : (leaseStateRoot l).size = 32 := by
  unfold leaseStateRoot merkleRoot
  exact hash_size "OBEND.CUSTODY.MERKLE.ROOT/v1" _

def leaseStateRootExtract {a b : PrepaidLease}
    (h : leaseStateRoot a = leaseStateRoot b) :
    PSum (PLift (a = b)) (CshakeCallCollision (leaseStateRootCalls a ++ leaseStateRootCalls b)) :=
  match merkleRootExtract (leaseFields a) (leaseFields b) h with
  | .inl hp => .inl ⟨leaseFields_inj hp.down⟩
  | .inr hc => .inr hc

theorem equal_roots_bind_cursor_remaining_drawn_or_collision {a b : PrepaidLease}
    (h : leaseStateRoot a = leaseStateRoot b) :
    a = b ∨ CshakeCollisionAmong (leaseStateRootCalls a ++ leaseStateRootCalls b) := by
  cases leaseStateRootExtract h with
  | inl hp => exact .inl hp.down
  | inr hc => exact .inr ⟨hc⟩

abbrev EgressDoor := String
/-- A custody capability is the frozen powerbox reference, not its integer slot name. -/
abbrev SessionCap := GrainPowerbox.FrozenRef

structure ConfinedSession where
  sessionId : UInt64
  lease : PrepaidLease
  mindRoot : ByteArray
  egressDoors : List EgressDoor
  caps : List UInt64
  receiptHead : ByteArray
  checkpointRoot : ByteArray
  frozenGrain : GrainPowerbox.FrozenGrain
  allowedReadSlots : List UInt64 := []
  allowedEmitSlots : List UInt64 := []
  allowHashDigest : Bool := false
  issuedIds : List UInt64 := []

/-- Integer wire names resolve only inside this session's frozen c-list and allowlist. -/
def resolveSessionCap (s : ConfinedSession) (slot : UInt64) : Option SessionCap :=
  if slot ∈ s.caps then s.frozenGrain.refs[slot.toNat]? else none

theorem ungranted_slot_refused (s : ConfinedSession) (slot : UInt64) (h : slot ∉ s.caps) :
    resolveSessionCap s slot = none := by simp [resolveSessionCap, h]

structure ForkChildSpec where
  id : UInt64
  budget : Nat
  doors : List EgressDoor
  caps : List UInt64
  allowedReadSlots : List UInt64 := []
  allowedEmitSlots : List UInt64 := []
  allowHashDigest : Bool := false
  deriving DecidableEq

structure ForkTwoSpec where
  left : ForkChildSpec
  right : ForkChildSpec
  deriving DecidableEq

inductive ForkRefusal where
  | duplicateIdentity | amplifiedAuthority | budgetOverdraw | namespaceCollision
  deriving DecidableEq, Repr

@[expose] def attenuates (p : ConfinedSession) (c : ForkChildSpec) : Prop :=
  ((∀ d ∈ c.doors, d ∈ p.egressDoors) ∧ (∀ k ∈ c.caps, k ∈ p.caps)) ∧
  (∀ k ∈ c.allowedReadSlots, k ∈ p.allowedReadSlots) ∧
  (∀ k ∈ c.allowedEmitSlots, k ∈ p.allowedEmitSlots) ∧
  (c.allowHashDigest = true → p.allowHashDigest = true)
instance (p : ConfinedSession) (c : ForkChildSpec) : Decidable (attenuates p c) := by
  unfold attenuates
  infer_instance

def canonicalU64 (xs : List UInt64) : List UInt64 :=
  (xs.mergeSort (fun a b => a.toNat ≤ b.toNat)).eraseReps

def authorityRoot (doors : List EgressDoor) (caps : List UInt64)
    (reads emits : List UInt64 := []) (allowHash : Bool := false) : ByteArray :=
  hash "OBEND.CUSTODY.AUTHORITY/v1"
    [encodeFields (((doors.map fun d => d.toUTF8.data.toList).mergeSort
        (fun a b => compare a b != .gt)).eraseReps),
     encodeFields ((canonicalU64 caps).map fun c => leb128 c.toNat),
     encodeFields ((canonicalU64 reads).map fun c => leb128 c.toNat),
     encodeFields ((canonicalU64 emits).map fun c => leb128 c.toNat),
     [if allowHash then 1 else 0]]

/-- Every frozen reference binds its descriptor opening, owner, name and full digest. -/
def frozenGrainRoot (g : GrainPowerbox.FrozenGrain) : ByteArray :=
  hash "OBEND.CUSTODY.FROZEN/v1" [leb128 g.grain, encodeFields (g.refs.toList.map fun r =>
    let (tag, id) := match r.via with | .user n => (0, n) | .grain n => (1, n)
    encodeFields [r.petname.toUTF8.data.toList, [UInt8.ofNat tag], leb128 id, r.cap.root.encode,
      encodeFields (r.cap.hops.toList.map fun b => b.encode),
      encodeFields (r.cap.membranes.map leb128), Obend.Digest.HashBytes.be 32 r.commitment.toNat])]

def sessionCheckpoint (s : ConfinedSession) : ByteArray :=
  hash "OBEND.CUSTODY.SESSION/v1" [leb128 s.sessionId.toNat, (leaseStateRoot s.lease).data.toList,
    s.mindRoot.data.toList, (authorityRoot s.egressDoors s.caps s.allowedReadSlots s.allowedEmitSlots s.allowHashDigest).data.toList, s.receiptHead.data.toList, (frozenGrainRoot s.frozenGrain).data.toList]

def childMind (p : ConfinedSession) (c : ForkChildSpec) : ByteArray :=
  hash "OBEND.CUSTODY.MIND/v1" [leb128 c.id.toNat, p.mindRoot.data.toList]

def forkGenesis (parent : ByteArray) (id : UInt64) (mind leaseRoot authority : ByteArray) : ByteArray :=
  hash "OBEND.CUSTODY.FORK/v1"
    [parent.data.toList, leb128 id.toNat, mind.data.toList, leaseRoot.data.toList, authority.data.toList]

def makeChild (p : ConfinedSession) (s : ForkChildSpec) (siblings : List UInt64 := []) : ConfinedSession :=
  let l := openLease s.id p.lease.nextDue p.lease.rent s.budget
  let m := childMind p s
  let head := forkGenesis p.checkpointRoot s.id m (leaseStateRoot l) (authorityRoot s.doors s.caps s.allowedReadSlots s.allowedEmitSlots s.allowHashDigest)
  let child : ConfinedSession := ⟨s.id, l, m, s.doors, s.caps, head, head, {p.frozenGrain with grain := s.id.toNat},
    s.allowedReadSlots, s.allowedEmitSlots, s.allowHashDigest,
    s.id :: p.sessionId :: (siblings ++ p.issuedIds)⟩
  {child with checkpointRoot := sessionCheckpoint child}

/-- A fork transfers principal, not rent. The retained tranche's initial allocation is
rebased by the transfer; its rent cursor and drawn accumulator remain unchanged. -/
def retainedParent (p : ConfinedSession) (s : ForkTwoSpec) : ConfinedSession :=
  let retained := { p with issuedIds := s.left.id :: s.right.id :: p.sessionId :: p.issuedIds, lease := { p.lease with
      initialBudget := p.lease.initialBudget - (s.left.budget + s.right.budget),
      remaining := p.lease.remaining - (s.left.budget + s.right.budget) } }
  {retained with checkpointRoot := sessionCheckpoint retained}

def forkTwo (p : ConfinedSession) (s : ForkTwoSpec) :
    Except ForkRefusal (ConfinedSession × ConfinedSession × ConfinedSession) :=
  if s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId then
    .error .duplicateIdentity
  else if s.left.id ∈ p.issuedIds ∨ s.right.id ∈ p.issuedIds then .error .duplicateIdentity
  else if ¬ (attenuates p s.left ∧ attenuates p s.right) then .error .amplifiedAuthority
  else if p.lease.remaining < s.left.budget + s.right.budget then .error .budgetOverdraw
  else if childMind p s.left = childMind p s.right then .error .namespaceCollision
  else .ok (retainedParent p s, makeChild p s.left [s.right.id], makeChild p s.right [s.left.id])

theorem forkTwo_success {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    s.left.id ≠ s.right.id ∧ s.left.id ≠ p.lease.leaseId ∧ s.right.id ≠ p.lease.leaseId ∧
    attenuates p s.left ∧ attenuates p s.right ∧
    s.left.budget + s.right.budget ≤ p.lease.remaining ∧
    childMind p s.left ≠ childMind p s.right ∧
    p' = retainedParent p s ∧ a = makeChild p s.left [s.right.id] ∧ b = makeChild p s.right [s.left.id] := by
  unfold forkTwo at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all

theorem issued_identity_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : s.left.id ∈ p.issuedIds ∨ s.right.id ∈ p.issuedIds) :
    forkTwo p s = .error .duplicateIdentity := by
  unfold forkTwo
  split <;> simp_all

theorem forkTwo_inherits_ids {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    ∀ id ∈ p.issuedIds, id ∈ p'.issuedIds ∧ id ∈ a.issuedIds ∧ id ∈ b.issuedIds := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩
  intro id hi
  simp [retainedParent, makeChild, hi]

theorem forkTwo_sovereign_isolation {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    a.lease.leaseId ≠ b.lease.leaseId ∧ a.lease.leaseId ≠ p.lease.leaseId ∧
    b.lease.leaseId ≠ p.lease.leaseId ∧ a.mindRoot ≠ b.mindRoot := by
  rcases forkTwo_success h with ⟨hi, ha, hb, _, _, _, hm, _, rfl, rfl⟩
  exact ⟨hi, ha, hb, hm⟩

theorem forkTwo_attenuates_confinement {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    ((∀ d ∈ a.egressDoors, d ∈ p.egressDoors) ∧ (∀ k ∈ a.caps, k ∈ p.caps)) ∧
    ((∀ d ∈ b.egressDoors, d ∈ p.egressDoors) ∧ (∀ k ∈ b.caps, k ∈ p.caps)) := by
  rcases forkTwo_success h with ⟨_, _, _, ha, hb, _, _, _, rfl, rfl⟩
  exact ⟨ha.1, hb.1⟩

/-- The c-list is shared as a frozen value; only retained slot names can resolve. -/
theorem child_cap_resolves_in_parent (p : ConfinedSession) (c : ForkChildSpec)
    (ids : List UInt64) (slot : UInt64) (cap : SessionCap)
    (ha : attenuates p c) (h : resolveSessionCap (makeChild p c ids) slot = some cap) :
    resolveSessionCap p slot = some cap := by
  unfold resolveSessionCap at h ⊢
  simp only [makeChild] at h
  by_cases hs : slot ∈ c.caps
  · have hp := ha.1.2 slot hs
    simpa [hs, hp] using h
  · simp [hs] at h

theorem amplified_egress_or_cap_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : ¬ (attenuates p s.left ∧ attenuates p s.right)) :
    ∃ reason, forkTwo p s = .error reason := by
  unfold forkTwo
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · simp [h]

theorem duplicate_identity_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId) :
    forkTwo p s = .error .duplicateIdentity := by simp [forkTwo, h]

theorem overdrawn_split_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : p.lease.remaining < s.left.budget + s.right.budget) :
    ∃ reason, forkTwo p s = .error reason := by
  cases he : forkTwo p s with
  | error r => exact ⟨r, rfl⟩
  | ok result =>
    rcases result with ⟨p', a, b⟩
    have hs := forkTwo_success he
    exfalso
    omega

theorem forkTwo_conserves_budget {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    a.lease.initialBudget + b.lease.initialBudget + p'.lease.remaining = p.lease.remaining := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, hc, _, rfl, rfl, rfl⟩
  simp only [makeChild, openLease, retainedParent]
  omega

theorem forkTwo_preserves_lease_balance {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b))
    (hb : p.lease.remaining + p.lease.drawn = p.lease.initialBudget) :
    p'.lease.remaining + p'.lease.drawn = p'.lease.initialBudget := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, hc, _, rfl, _, _⟩
  simp only [retainedParent]; omega

/-- An independent verifier supplies an alleged fork point; equality of the genesis
receipt binds it to the actual point, with a concrete collision on any substitution. -/
def verifyForkGenesis (p : ByteArray) (c : ConfinedSession) : Bool :=
  decide (forkGenesis p c.sessionId c.mindRoot (leaseStateRoot c.lease) (authorityRoot c.egressDoors c.caps c.allowedReadSlots c.allowedEmitSlots c.allowHashDigest) = c.receiptHead)

def forkGenesisCall (parent : ByteArray) (id : UInt64) (mind leaseRoot authority : ByteArray) : CshakeCall :=
  ("OBEND.CUSTODY.FORK/v1",
   [parent.data.toList, leb128 id.toNat, mind.data.toList, leaseRoot.data.toList, authority.data.toList])

def sessionGenesisCall (p : ByteArray) (c : ConfinedSession) : CshakeCall :=
  forkGenesisCall p c.sessionId c.mindRoot (leaseStateRoot c.lease)
    (authorityRoot c.egressDoors c.caps c.allowedReadSlots c.allowedEmitSlots c.allowHashDigest)

def genesisExtract {p q : ByteArray} {id : UInt64} {m l auth : ByteArray}
    (h : forkGenesis p id m l auth = forkGenesis q id m l auth) :
    PSum (PLift (p = q)) (CshakeCallCollision [forkGenesisCall p id m l auth, forkGenesisCall q id m l auth]) :=
  match hashExtract "OBEND.CUSTODY.FORK/v1"
      [p.data.toList, leb128 id.toNat, m.data.toList, l.data.toList, auth.data.toList]
      [q.data.toList, leb128 id.toNat, m.data.toList, l.data.toList, auth.data.toList] h with
  | .inl hp =>
    have hp' : p.data.toList = q.data.toList := by simpa using hp.down
    .inl ⟨byteArray_eq_of_toList_eq hp'⟩
  | .inr hc => .inr hc

theorem genesis_binds {p q : ByteArray} {id : UInt64} {m l auth : ByteArray}
    (h : forkGenesis p id m l auth = forkGenesis q id m l auth) :
    p = q ∨ CshakeCollisionAmong [forkGenesisCall p id m l auth, forkGenesisCall q id m l auth] := by
  cases genesisExtract h with
  | inl hp => exact .inl hp.down
  | inr hc => exact .inr ⟨hc⟩

attribute [local irreducible] hash merkle merkleRoot leaseStateRoot childMind forkGenesis authorityRoot sessionCheckpoint

theorem forkTwo_anchors_receipt_chains_or_collision
    {p p' a b : ConfinedSession} {s : ForkTwoSpec} (h : forkTwo p s = .ok (p', a, b)) :
    verifyForkGenesis p.checkpointRoot a = true ∧ verifyForkGenesis p.checkpointRoot b = true ∧
    (∀ q, verifyForkGenesis q a = true →
      q = p.checkpointRoot ∨ CshakeCollisionAmong [sessionGenesisCall q a, sessionGenesisCall p.checkpointRoot a]) ∧
    (∀ q, verifyForkGenesis q b = true →
      q = p.checkpointRoot ∨ CshakeCollisionAmong [sessionGenesisCall q b, sessionGenesisCall p.checkpointRoot b]) := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩
  have accepts (c : ForkChildSpec) (ids : List UInt64) : verifyForkGenesis p.checkpointRoot (makeChild p c ids) = true := by
    unfold verifyForkGenesis
    apply decide_eq_true
    rfl
  refine ⟨accepts s.left [s.right.id], accepts s.right [s.left.id], ?_, ?_⟩
  all_goals
    intro q hq
    have he := of_decide_eq_true hq
    exact genesis_binds (id := _) (m := _) (l := _) he

/-- Every turn extends the child chain rather than overwriting the fork genesis. -/
def receiptFold (start : ByteArray) : List ByteArray → ByteArray
  | [] => start
  | event :: rest => receiptFold
      (hash "OBEND.CUSTODY.RECEIPT/v1" [start.data.toList, event.data.toList]) rest

def receiptFoldCalls (start : ByteArray) : List ByteArray → List CshakeCall
  | [] => []
  | event :: rest =>
    ("OBEND.CUSTODY.RECEIPT/v1", [start.data.toList, event.data.toList]) ::
      receiptFoldCalls (hash "OBEND.CUSTODY.RECEIPT/v1" [start.data.toList, event.data.toList]) rest

def receiptFoldExtract : ∀ (events : List ByteArray) (a b : ByteArray),
    receiptFold a events = receiptFold b events →
    PSum (PLift (a = b)) (CshakeCallCollision (receiptFoldCalls a events ++ receiptFoldCalls b events))
  | [], _, _, h => .inl ⟨h⟩
  | e :: es, a, b, h =>
    match receiptFoldExtract es
        (hash "OBEND.CUSTODY.RECEIPT/v1" [a.data.toList, e.data.toList])
        (hash "OBEND.CUSTODY.RECEIPT/v1" [b.data.toList, e.data.toList]) h with
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        rcases List.mem_append.1 hmem with hL | hR
        · exact List.mem_append_left _ (.tail _ hL)
        · exact List.mem_append_right _ (.tail _ hR)))
    | .inl he =>
      match hashExtract "OBEND.CUSTODY.RECEIPT/v1"
          [a.data.toList, e.data.toList] [b.data.toList, e.data.toList] he.down with
      | .inl hp =>
        have hh : a.data.toList = b.data.toList := by simpa using hp.down
        .inl ⟨byteArray_eq_of_toList_eq hh⟩
      | .inr hc =>
        .inr (hc.weaken (by
          intro c hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · exact List.mem_append_left _ (.head _)
          · exact List.mem_append_right _ (.head _)))

theorem receiptFold_binds_start (events : List ByteArray) (a b : ByteArray)
    (h : receiptFold a events = receiptFold b events) :
    a = b ∨ CshakeCollisionAmong (receiptFoldCalls a events ++ receiptFoldCalls b events) := by
  cases receiptFoldExtract events a b h with
  | inl hp => exact .inl hp.down
  | inr hc => exact .inr ⟨hc⟩

def forkChainCalls (events : List ByteArray) (anchor : ByteArray) (id : UInt64)
    (mind initialLeaseRoot authority : ByteArray) : List CshakeCall :=
  forkGenesisCall anchor id mind initialLeaseRoot authority ::
    receiptFoldCalls (forkGenesis anchor id mind initialLeaseRoot authority) events

def forkReceiptChainExtract (events : List ByteArray)
    (claimed actual : ByteArray) (id : UInt64) (mind initialLeaseRoot authority : ByteArray)
    (h : receiptFold (forkGenesis claimed id mind initialLeaseRoot authority) events =
      receiptFold (forkGenesis actual id mind initialLeaseRoot authority) events) :
    PSum (PLift (claimed = actual))
      (CshakeCallCollision
        (forkChainCalls events claimed id mind initialLeaseRoot authority ++
         forkChainCalls events actual id mind initialLeaseRoot authority)) :=
  match receiptFoldExtract events _ _ h with
  | .inr hc =>
    .inr (hc.weaken (by
      intro c hmem
      rcases List.mem_append.1 hmem with hL | hR
      · exact List.mem_append_left _ (.tail _ hL)
      · exact List.mem_append_right _ (.tail _ hR)))
  | .inl he =>
    match genesisExtract he.down with
    | .inl hp => .inl hp
    | .inr hc =>
      .inr (hc.weaken (by
        intro c hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact List.mem_append_left _ (.head _)
        · exact List.mem_append_right _ (.head _)))

theorem fork_receipt_chain_binds_anchor_or_collision (events : List ByteArray)
    (claimed actual : ByteArray) (id : UInt64) (mind initialLeaseRoot authority : ByteArray)
    (h : receiptFold (forkGenesis claimed id mind initialLeaseRoot authority) events =
      receiptFold (forkGenesis actual id mind initialLeaseRoot authority) events) :
    claimed = actual ∨
      CshakeCollisionAmong
        (forkChainCalls events claimed id mind initialLeaseRoot authority ++
         forkChainCalls events actual id mind initialLeaseRoot authority) := by
  cases forkReceiptChainExtract events claimed actual id mind initialLeaseRoot authority h with
  | inl hp => exact .inl hp.down
  | inr hc => exact .inr ⟨hc⟩

/-- The allocator checks every live handle, including allocations made by sibling branches.
The per-session history additionally remembers retired identities along each lineage. -/
def forkFrontier (pre post : List ConfinedSession) (p : ConfinedSession) (s : ForkTwoSpec) :
    Except ForkRefusal (ConfinedSession × ConfinedSession × ConfinedSession) :=
  if s.left.id ∈ (pre ++ post).map (·.sessionId) ∨
      s.right.id ∈ (pre ++ post).map (·.sessionId) then .error .duplicateIdentity
  else forkTwo p s

theorem forkFrontier_success {pre post : List ConfinedSession} {p p' a b : ConfinedSession}
    {s : ForkTwoSpec} (h : forkFrontier pre post p s = .ok (p', a, b)) :
    forkTwo p s = .ok (p', a, b) ∧
    s.left.id ∉ (pre ++ post).map (·.sessionId) ∧
    s.right.id ∉ (pre ++ post).map (·.sessionId) := by
  unfold forkFrontier at h
  split at h <;> simp_all

/-- Each initial live identity is distinct; subsequent allocations are checked operationally. -/
inductive ValidSessionTree : List ConfinedSession → List ConfinedSession → Prop
  | initial (ss) : (ss.map (·.sessionId)).Nodup → ValidSessionTree ss ss
  | fork {root pre post p p' a b s} : ValidSessionTree root (pre ++ p :: post) →
      forkFrontier pre post p s = .ok (p', a, b) →
      ValidSessionTree root (pre ++ p' :: a :: b :: post)

def frontierBudget (ss : List ConfinedSession) : Nat := (ss.map (·.lease.remaining)).sum

theorem multi_fork_tree_conservation {root ss : List ConfinedSession}
    (h : ValidSessionTree root ss) : frontierBudget ss = frontierBudget root := by
  induction h with
  | initial => rfl
  | @fork pre post p p' a b s _ hf ih =>
    have hf := (forkFrontier_success hf).1
    have hc := forkTwo_conserves_budget hf
    have he := forkTwo_success hf
    have ha : a.lease.remaining = a.lease.initialBudget := by rw [he.2.2.2.2.2.2.2.2.1]; rfl
    have hb : b.lease.remaining = b.lease.initialBudget := by rw [he.2.2.2.2.2.2.2.2.2]; rfl
    simp only [frontierBudget, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at *
    omega

theorem multi_fork_tree_distinct {root ss : List ConfinedSession}
    (h : ValidSessionTree root ss)
    (ids : ∀ p ∈ root, p.sessionId = p.lease.leaseId) : (ss.map (·.sessionId)).Nodup := by
  have invariant : (ss.map (·.sessionId)).Nodup ∧
      ∀ p ∈ ss, p.sessionId = p.lease.leaseId := by
    induction h with
    | initial hn => exact ⟨hn, ids⟩
    | @fork pre post p p' a b s ht hf ih =>
      obtain ⟨hf, hl, hr⟩ := forkFrontier_success hf
      obtain ⟨hne, hpl, hpr, _, _, _, _, rfl, rfl, rfl⟩ := forkTwo_success hf
      have hp := ih.2 p (by simp)
      constructor
      · simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at *
        simp only [retainedParent, makeChild]
        grind
      · intro q hq
        simp only [List.mem_append, List.mem_cons] at hq
        rcases hq with hq | rfl | rfl | rfl | hq
        · exact ih.2 q (by simp [hq])
        · exact hp
        · rfl
        · rfl
        · exact ih.2 q (by simp [hq])
  exact invariant.1

end Obend.Polis.Custody
