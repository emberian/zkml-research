module
/-
# Obend.Ledger.Floors — Finite-Support Typed-Account Resource Kernel & Register Realization

Mathlib-free port of `minidregg/Theory/CanonicalResourceKernel.lean` unified directly over
`Obend.Ledger.Register`:

1. **Typed Protected Account Namespaces (`AccountKind` & `AccountAddr`)**:
   - Distinguishes `user | issuerWell | seat | escrow | feePool | member` at the type level,
     eliminating integer collisions between `AssetId` issuer wells and user/seat `AccountId`s.
     A `member` is the one kind that may hold a credit line (minidregg's "credit limit for a
     member").
2. **Finite-Support Balance Maps (`FinMap K`)**:
   - Pure Lean 4 finite-support integer maps (`DecidableEq`, `Repr`, zero closures) with
     canonical duplicate-free `support`, `mem_support_iff` (`k ∈ m.support ↔ m.get k ≠ 0`),
     and global algebraic conservation (`totalSum`).
3. **Per-Account Floor Enforcement with Explicit Polarity (`FloorPolicy`, `FloorBook`, `FloorsHold`)**:
   - Every floor is a `FloorPolicy` whose constructor carries its sign: a member's
     `creditLimit` (down to `-limit`, `user` accounts only), a `minReserve` (at least `+reserve`),
     or the asset's own `issuerWell` (down to `-cap`, or unbounded when uncapped). Custodial
     accounts (`seat`, `escrow`, `feePool`) never go negative. Algebraic conservation and
     floor-preservation theorems hold for every policy.
4. **Direct Realization on `Obend.Ledger.Register.Reg` + `Movement`**:
   - Encodes `(AccountAddr, AssetId)` injectively into `Register` account strings, compiles
     every `TypedPosting` to balanced `Register.Movement` pairs, and proves exact per-account
     balance agreement, register debit/credit conservation, and floor preservation on `Reg`.
-/
public import Obend.Ledger.Register
import Obend.Tactic.Tooth

@[expose] public section
namespace Obend.Ledger

set_option autoImplicit false

/-! ## 1. Typed Account Namespaces & Coordinates -/

abbrev AccountId := Nat
abbrev AssetId := Nat
abbrev LeaseId := Nat
abbrev Epoch := Nat

/-- Floor of the protected numeric coordinate space (`≥ 2^256`). -/
def protectedBase : Nat := 2 ^ 256

theorem protectedBase_pos : 0 < protectedBase :=
  Nat.two_pow_pos 256

/-- Issuer-well coordinate in the `AccountId` space (`≥ 2 * protectedBase`), disjoint from
    both ordinary user accounts (`< protectedBase`) and seat/escrow accounts (`[protectedBase, 2 * protectedBase)`). -/
def issuerWellAccount (ast : AssetId) : AccountId :=
  2 * protectedBase + ast

theorem issuerWellAccount_ne_ordinary {u : AccountId} (hu : u < protectedBase) (ast : AssetId) :
    issuerWellAccount ast ≠ u :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le hu
    (Nat.le_trans (Nat.le_mul_of_pos_left protectedBase (by decide : 0 < 2))
      (Nat.le_add_right (2 * protectedBase) ast)))

/-- Protected semantic account kinds, preventing `AssetId`/`AccountId` namespace collisions. -/
inductive AccountKind where
  | user
  | issuerWell
  | seat
  | escrow
  | feePool
  /-- A credit-capable member account: the only kind whose `creditLimit` policy is honoured. -/
  | member
  deriving DecidableEq, Repr

/-- Typed account address pairing an `AccountKind` namespace with a numeric identifier. -/
structure AccountAddr where
  kind : AccountKind
  id   : Nat
  deriving DecidableEq, Repr

/-- Pure Lean 4 duplicate-free deduplication (`dedupLocal`) with constructive `mem` and `Nodup` proofs. -/
def dedupLocal {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if decide (x ∈ xs) then dedupLocal xs else x :: dedupLocal xs

theorem mem_dedupLocal {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ dedupLocal l ↔ a ∈ l
  | [] => Iff.rfl
  | x :: xs => by
    unfold dedupLocal
    by_cases hx : x ∈ xs
    · simp only [decide_eq_true hx, ↓reduceIte, mem_dedupLocal, List.mem_cons]
      exact ⟨Or.inr, fun h => by rcases h with rfl | hm; exact hx; exact hm⟩
    · simp only [decide_eq_false hx, Bool.false_eq_true, ↓reduceIte, List.mem_cons, mem_dedupLocal]

theorem nodup_dedupLocal {α : Type} [DecidableEq α] :
    ∀ (l : List α), (dedupLocal l).Nodup
  | [] => List.Pairwise.nil
  | x :: xs => by
    unfold dedupLocal
    by_cases hx : x ∈ xs
    · simp only [decide_eq_true hx, ↓reduceIte]
      exact nodup_dedupLocal xs
    · simp only [decide_eq_false hx, Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
      exact ⟨fun hm => hx (mem_dedupLocal.mp hm), nodup_dedupLocal xs⟩

/-- Pure Lean 4 `Nodup` preservation under `List.filter`. -/
theorem nodup_filter_local {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    cases hpx : p x with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact nodup_filter_local p hnd.2
    | true =>
      simp only [↓reduceIte, List.nodup_cons]
      refine ⟨?_, nodup_filter_local p hnd.2⟩
      intro hmem
      exact hnd.1 (List.mem_filter.mp hmem).1

/-- O(log n) canonical binary digit encoding of `Nat` using `'0'`/`'1'` characters (never `':'`). -/
def natBitChars : Nat → List Char
  | 0 => []
  | n + 1 =>
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
    (if (n + 1) % 2 == 0 then '0' else '1') :: natBitChars ((n + 1) / 2)

def ofNatBitChars : List Char → Nat
  | [] => 0
  | c :: cs => 2 * ofNatBitChars cs + (if c == '0' then 0 else 1)

theorem ofNatBitChars_natBitChars : ∀ (n : Nat), ofNatBitChars (natBitChars n) = n
  | 0 => by unfold natBitChars ofNatBitChars; rfl
  | n + 1 => by
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
    have ih := ofNatBitChars_natBitChars ((n + 1) / 2)
    rw [natBitChars]
    cases hpar : (n + 1) % 2 == 0 with
    | true =>
      have hm : (n + 1) % 2 = 0 := beq_iff_eq.mp hpar
      simp only [↓reduceIte, ofNatBitChars, ih]
      have hc : ('0' == '0') = true := rfl
      simp only [hc, ↓reduceIte]
      omega
    | false =>
      have hne : (n + 1) % 2 ≠ 0 := fun h => by rw [beq_iff_eq.mpr h] at hpar; cases hpar
      simp only [Bool.false_eq_true, ↓reduceIte, ofNatBitChars, ih]
      have hc : ('1' == '0') = false := rfl
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      omega

theorem natBitChars_no_colon : ∀ (n : Nat) {c : Char}, c ∈ natBitChars n → c ≠ ':'
  | 0, _, h => by rw [natBitChars] at h; cases h
  | n + 1, c, h => by
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
    rw [natBitChars] at h
    rcases List.mem_cons.mp h with rfl | htail
    · cases (n + 1) % 2 == 0 <;> simp
    · exact natBitChars_no_colon ((n + 1) / 2) htail

theorem takeWhile_append_sep : ∀ (xs ys : List Char),
    (∀ c ∈ xs, c ≠ ':') →
    List.takeWhile (· != ':') (xs ++ ':' :: ys) = xs
  | [], ys, _ => rfl
  | x :: xs, ys, hno => by
    have hx : (x != ':') = true := bne_iff_ne.mpr (hno x (List.Mem.head xs))
    simp only [List.cons_append, List.takeWhile_cons, hx, ↓reduceIte]
    rw [takeWhile_append_sep xs ys (fun c hc => hno c (List.Mem.tail x hc))]

namespace AccountAddr

def user (id : Nat) : AccountAddr := ⟨.user, id⟩
def issuerWell (ast : AssetId) : AccountAddr := ⟨.issuerWell, ast⟩
def seat (id : Nat) : AccountAddr := ⟨.seat, id⟩
def escrow (id : Nat) : AccountAddr := ⟨.escrow, id⟩
def feePool (id : Nat) : AccountAddr := ⟨.feePool, id⟩
def member (id : Nat) : AccountAddr := ⟨.member, id⟩

theorem issuerWell_ne_user (ast id : Nat) : issuerWell ast ≠ user id := by
  intro h; cases h

theorem issuerWell_ne_seat (ast id : Nat) : issuerWell ast ≠ seat id := by
  intro h; cases h

theorem issuerWell_ne_escrow (ast id : Nat) : issuerWell ast ≠ escrow id := by
  intro h; cases h

theorem issuerWell_ne_feePool (ast id : Nat) : issuerWell ast ≠ feePool id := by
  intro h; cases h

theorem seat_ne_user (sid uid : Nat) : seat sid ≠ user uid := by
  intro h; cases h

def kindChar : AccountKind → Char
  | .user       => 'U'
  | .issuerWell => 'I'
  | .seat       => 'S'
  | .escrow     => 'E'
  | .feePool    => 'F'
  | .member     => 'M'

def ofKindChar? : Char → Option AccountKind
  | 'U' => some .user
  | 'I' => some .issuerWell
  | 'S' => some .seat
  | 'E' => some .escrow
  | 'F' => some .feePool
  | 'M' => some .member
  | _   => none

@[simp] theorem ofKindChar?_kindChar (k : AccountKind) :
    ofKindChar? (kindChar k) = some k := by
  cases k <;> rfl

/-- Canonical injective `Register` account name for `(addr, asset)`. -/
def toRegAccount (addr : AccountAddr) (ast : AssetId) : String :=
  String.ofList (kindChar addr.kind :: ':' :: (natBitChars addr.id ++ ':' :: natBitChars ast))

/-- Decode a canonical `Register` account name back into `(AccountAddr, AssetId)`. -/
def ofRegAccount? (s : String) : Option (AccountAddr × AssetId) :=
  match s.toList with
  | kc :: ':' :: rest =>
    match ofKindChar? kc with
    | some k =>
      let idBits := rest.takeWhile (· != ':')
      let astBits := rest.drop (idBits.length + 1)
      some (⟨k, ofNatBitChars idBits⟩, ofNatBitChars astBits)
    | none => none
  | _ => none

@[simp] theorem ofRegAccount?_toRegAccount (addr : AccountAddr) (ast : AssetId) :
    ofRegAccount? (toRegAccount addr ast) = some (addr, ast) := by
  rcases addr with ⟨k, id⟩
  unfold toRegAccount ofRegAccount?
  simp only [String.toList_ofList, ofKindChar?_kindChar]
  have htake := takeWhile_append_sep (natBitChars id) (natBitChars ast) (fun c hc => natBitChars_no_colon id hc)
  rw [htake]
  have hdrop : ((natBitChars id ++ ':' :: natBitChars ast).drop ((natBitChars id).length + 1)) = natBitChars ast := by
    have : natBitChars id ++ ':' :: natBitChars ast = (natBitChars id ++ [':']) ++ natBitChars ast := by simp
    rw [this]
    have hlen : (natBitChars id).length + 1 = (natBitChars id ++ [':']).length := by simp
    rw [hlen, List.drop_left]
  rw [hdrop, ofNatBitChars_natBitChars, ofNatBitChars_natBitChars]

theorem toRegAccount_injective {a₁ a₂ : AccountAddr} {ast₁ ast₂ : AssetId}
    (h : toRegAccount a₁ ast₁ = toRegAccount a₂ ast₂) :
    a₁ = a₂ ∧ ast₁ = ast₂ := by
  have hdec := congrArg ofRegAccount? h
  simp only [ofRegAccount?_toRegAccount, Option.some.injEq, Prod.mk.injEq] at hdec
  exact hdec

/-- Injective numeric coordinate encoding `AccountAddr → AccountId`:
    `6 * id + tag`, injective across all `AccountKind`s and `Nat` identifiers. -/
def toTag : AccountKind → Nat
  | .user       => 0
  | .issuerWell => 1
  | .seat       => 2
  | .escrow     => 3
  | .feePool    => 4
  | .member     => 5

def ofTag? : Nat → Option AccountKind
  | 0 => some .user
  | 1 => some .issuerWell
  | 2 => some .seat
  | 3 => some .escrow
  | 4 => some .feePool
  | 5 => some .member
  | _ => none

@[simp] theorem ofTag?_toTag (k : AccountKind) : ofTag? (toTag k) = some k := by
  cases k <;> rfl

theorem toTag_lt_six (k : AccountKind) : toTag k < 6 := by
  cases k <;> decide

def toCoord (addr : AccountAddr) : AccountId :=
  6 * addr.id + toTag addr.kind

def ofCoord (c : AccountId) : AccountAddr :=
  match ofTag? (c % 6) with
  | some k => ⟨k, c / 6⟩
  | none   => ⟨.user, c / 6⟩

@[simp] theorem ofCoord_toCoord (addr : AccountAddr) :
    ofCoord (toCoord addr) = addr := by
  rcases addr with ⟨k, id⟩
  have hlt := toTag_lt_six k
  have hmod : (6 * id + toTag k) % 6 = toTag k := by omega
  have hdiv : (6 * id + toTag k) / 6 = id := by omega
  simp [ofCoord, toCoord, hmod, hdiv]

theorem toCoord_injective {a b : AccountAddr} (h : toCoord a = toCoord b) : a = b := by
  have := congrArg ofCoord h
  simpa using this

end AccountAddr

/-! ## 2. Finite-Support Signed Map (`FinMap K`) -/

/-- Pure Lean 4 finite-support map `K →₀ Int` represented as a finite delta log.
    Supports `DecidableEq` and `Repr` with zero function closures. -/
structure FinMap (K : Type) where
  entries : List (K × Int)
  deriving DecidableEq, Repr

namespace FinMap

def empty {K : Type} : FinMap K := ⟨[]⟩

def get {K : Type} [DecidableEq K] (m : FinMap K) (k : K) : Int :=
  ((m.entries.filter (fun p => p.1 == k)).map Prod.snd).sum

@[simp] theorem get_empty {K : Type} [DecidableEq K] (k : K) :
    (empty : FinMap K).get k = 0 := rfl

/-- Add signed delta `d` at key `k` (skipping zero deltas to keep logs compact). -/
def addDelta {K : Type} (m : FinMap K) (k : K) (d : Int) : FinMap K :=
  if d == 0 then m else ⟨(k, d) :: m.entries⟩

@[simp] theorem get_addDelta {K : Type} [DecidableEq K] (m : FinMap K) (k k' : K) (d : Int) :
    (m.addDelta k d).get k' = m.get k' + (if k' = k then d else 0) := by
  unfold addDelta
  cases hd : d == 0 with
  | true =>
    have hd0 : d = 0 := beq_iff_eq.mp hd
    subst hd0
    simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, get, List.filter_cons]
    by_cases hk : k = k'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · have hbeq : (k == k') = false := beq_eq_false_iff_ne.mpr hk
      have hne' : k' ≠ k := Ne.symm hk
      simp [hbeq, hne']

/-- Set key `k` to exact value `v`. -/
def set {K : Type} [DecidableEq K] (m : FinMap K) (k : K) (v : Int) : FinMap K :=
  m.addDelta k (v - m.get k)

@[simp] theorem get_set {K : Type} [DecidableEq K] (m : FinMap K) (k k' : K) (v : Int) :
    (m.set k v).get k' = if k' = k then v else m.get k' := by
  unfold set
  rw [get_addDelta]
  by_cases hk : k' = k
  · subst hk; simp; omega
  · simp [hk]

/-- Finite duplicate-free support `{ k | m.get k ≠ 0 }`. -/
def support {K : Type} [DecidableEq K] (m : FinMap K) : List K :=
  (dedupLocal (m.entries.map Prod.fst)).filter (fun k => m.get k != 0)

theorem support_nodup {K : Type} [DecidableEq K] (m : FinMap K) :
    m.support.Nodup := by
  unfold support
  exact nodup_filter_local _ (nodup_dedupLocal _)

theorem get_eq_zero_of_not_mem_fst {K : Type} [DecidableEq K] (m : FinMap K) (k : K)
    (hnot : k ∉ m.entries.map Prod.fst) : m.get k = 0 := by
  unfold get
  have hnil : m.entries.filter (fun p => p.1 == k) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp hbeq
    have hk : p.1 = k := beq_iff_eq.mp hbeq
    subst hk
    exact False.elim (hnot (List.mem_map_of_mem hp))
  simp [hnil]

theorem mem_support_iff {K : Type} [DecidableEq K] (m : FinMap K) (k : K) :
    k ∈ m.support ↔ m.get k ≠ 0 := by
  unfold support
  rw [List.mem_filter, mem_dedupLocal, bne_iff_ne]
  constructor
  · exact fun h => h.2
  · intro hne
    refine ⟨?_, hne⟩
    exact Classical.byContradiction fun hnot => hne (get_eq_zero_of_not_mem_fst m k hnot)

theorem zero_of_not_mem_support {K : Type} [DecidableEq K] (m : FinMap K) {k : K}
    (hnot : k ∉ m.support) : m.get k = 0 :=
  Classical.byContradiction fun hne => hnot ((mem_support_iff m k).mpr hne)

/-- Global algebraic sum of all entries in `m`. -/
def totalSum {K : Type} (m : FinMap K) : Int :=
  (m.entries.map Prod.snd).sum

@[simp] theorem totalSum_empty {K : Type} : (empty : FinMap K).totalSum = 0 := rfl

@[simp] theorem totalSum_addDelta {K : Type} (m : FinMap K) (k : K) (d : Int) :
    (m.addDelta k d).totalSum = m.totalSum + d := by
  unfold addDelta totalSum
  cases hd : d == 0 with
  | true =>
    have hd0 : d = 0 := beq_iff_eq.mp hd
    subst hd0; simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
    omega

end FinMap

/-! ## 3. Typed Resource Kernel with Explicit Floor Polarity (`FloorPolicy`)

`minidregg/Theory/CanonicalResourceKernel.lean:108` reads a floor as a credit line (`-floor`),
while a reserve is a `+floor`. A bare `Nat` cannot say which, so the sign lives in the
constructor of a `FloorPolicy`:

- `creditLimit limit`: a member's credit line; the balance may go down to `-limit`. Honoured
  only on `member` accounts (`FloorBook.policyOf_creditLimit`): every other non-issuer account
  (`user`, `seat`, `escrow`, `feePool`) never goes negative (`nonIssuer_floor_nonneg`).
- `minReserve reserve`: a reserve; the balance must stay at or above `+reserve`.
- `issuerWell cap`: the asset's own issuer well; `some cap` permits down to `-cap`, `none` is
  unbounded below. Granted to that well only (`FloorBook.policyOf_issuerWell`). -/

/-- A conserved typed transfer leg moving `amount` of `asset` from `source` to `destination`. -/
structure TypedPosting where
  source      : AccountAddr
  destination : AccountAddr
  asset       : AssetId
  amount      : Nat
  deriving DecidableEq, Repr

/-- A floor with its sign carried by the constructor, never inferred from a bare `Nat`. -/
inductive FloorPolicy where
  | creditLimit (limit : Nat)
  | minReserve (reserve : Nat)
  | issuerWell (cap : Option Nat)
  deriving DecidableEq, Repr

namespace FloorPolicy

/-- The least admitted balance, or `none` when unbounded below. -/
def floor? : FloorPolicy → Option Int
  | .creditLimit limit => some (-(limit : Int))
  | .minReserve reserve => some (reserve : Int)
  | .issuerWell (some cap) => some (-(cap : Int))
  | .issuerWell none => none

/-- `bal` respects the policy. -/
def admits (p : FloorPolicy) (bal : Int) : Bool :=
  match p.floor? with
  | none => true
  | some f => decide (f ≤ bal)

theorem creditLimit_admits_iff (limit : Nat) (bal : Int) :
    (creditLimit limit).admits bal = true ↔ -(limit : Int) ≤ bal := by
  simp [admits, floor?]

theorem minReserve_admits_iff (reserve : Nat) (bal : Int) :
    (minReserve reserve).admits bal = true ↔ (reserve : Int) ≤ bal := by
  simp [admits, floor?]

theorem issuerWell_capped_admits_iff (cap : Nat) (bal : Int) :
    (issuerWell (some cap)).admits bal = true ↔ -(cap : Int) ≤ bal := by
  simp [admits, floor?]

theorem issuerWell_uncapped_admits (bal : Int) : (issuerWell none).admits bal = true := rfl

/-- Polarity is observable: for `0 < n` the balance `-n` is admitted by the credit line `n` and
refused by the reserve `n`. A kernel that reads one as the other admits or refuses that balance
wrongly. -/
theorem polarity_separates (n : Nat) (hn : 0 < n) :
    (creditLimit n).admits (-(n : Int)) = true ∧ (minReserve n).admits (-(n : Int)) = false := by
  refine ⟨(creditLimit_admits_iff n _).mpr (Int.le_refl _), ?_⟩
  cases h : (minReserve n).admits (-(n : Int)) with
  | false => rfl
  | true => have := (minReserve_admits_iff n _).mp h; omega

end FloorPolicy

/-- Per-account floor configuration: an explicit `FloorPolicy` per `(account, asset)` (absent =
`minReserve 0`) and the issuance caps of issuer wells. -/
structure FloorBook where
  balances   : FinMap (AccountAddr × AssetId) := FinMap.empty
  policies   : List ((AccountAddr × AssetId) × FloorPolicy) := []
  issuerCaps : List (AssetId × Nat) := []
  deriving DecidableEq, Repr

def FloorBook.empty : FloorBook := {}

def FloorBook.balance (fb : FloorBook) (addr : AccountAddr) (ast : AssetId) : Int :=
  fb.balances.get (addr, ast)

/-- The policy in force at `(addr, ast)`:
    - the issuer well of `ast` holds `issuerWell` with its cap from `issuerCaps` (whatever the
      entries say);
    - a `creditLimit` entry is honoured on a `member` account only; on any other account, as an
      `issuerWell` entry on an account that is not that asset's well, it falls back to the
      reserve `0`;
    - a `minReserve` entry is honoured on every account but an asset's own issuer well. -/
def FloorBook.policyOf (fb : FloorBook) (addr : AccountAddr) (ast : AssetId) : FloorPolicy :=
  if addr.kind = .issuerWell ∧ addr.id = ast then .issuerWell (fb.issuerCaps.lookup ast)
  else
    match fb.policies.lookup (addr, ast) with
    | some (.creditLimit limit) => if addr.kind = .member then .creditLimit limit else .minReserve 0
    | some (.minReserve reserve) => .minReserve reserve
    | some (.issuerWell _) => .minReserve 0
    | none => .minReserve 0

/-- Minimum allowed balance for `(addr, ast)`: the floor of the policy in force. -/
def FloorBook.minBalance? (fb : FloorBook) (addr : AccountAddr) (ast : AssetId) : Option Int :=
  (fb.policyOf addr ast).floor?

/-- Only an asset's own issuer well is ever unbounded or issuer-capped. -/
theorem FloorBook.policyOf_issuerWell {fb : FloorBook} {addr : AccountAddr} {ast : AssetId}
    {cap : Option Nat} (h : fb.policyOf addr ast = .issuerWell cap) :
    addr.kind = .issuerWell ∧ addr.id = ast := by
  unfold FloorBook.policyOf at h
  split at h
  · assumption
  · split at h <;> (try split at h) <;> cases h

/-- Only a `member` account ever holds a credit line. -/
theorem FloorBook.policyOf_creditLimit {fb : FloorBook} {addr : AccountAddr} {ast : AssetId}
    {limit : Nat} (h : fb.policyOf addr ast = .creditLimit limit) : addr.kind = .member := by
  unfold FloorBook.policyOf at h
  split at h
  · cases h
  · split at h <;> (try split at h) <;> first | assumption | cases h

/-- Every account that is neither an issuer well nor a credit-capable `member` has a floor `≥ 0`. -/
theorem FloorBook.nonIssuer_floor_nonneg (fb : FloorBook) (addr : AccountAddr) (ast : AssetId)
    (hkind : addr.kind ≠ .issuerWell) (hcust : addr.kind ≠ .member) :
    ∃ (f : Int), fb.minBalance? addr ast = some f ∧ 0 ≤ f := by
  unfold FloorBook.minBalance?
  cases hp : fb.policyOf addr ast with
  | creditLimit limit => exact absurd (fb.policyOf_creditLimit hp) hcust
  | minReserve reserve => exact ⟨(reserve : Int), rfl, by omega⟩
  | issuerWell cap => exact absurd (fb.policyOf_issuerWell hp).1 hkind

/-- Predicate that a single `(addr, ast)` balance respects its floor. -/
def FloorBook.accountFloorHoldsB (fb : FloorBook) (addr : AccountAddr) (ast : AssetId) : Bool :=
  match fb.minBalance? addr ast with
  | none   => true
  | some f => decide (f ≤ fb.balance addr ast)

/-- Global floor invariant: every account and asset in the universe respects its floor. -/
def FloorsHold (fb : FloorBook) : Prop :=
  ∀ (addr : AccountAddr) (ast : AssetId),
    match fb.minBalance? addr ast with
    | none   => True
    | some f => f ≤ fb.balance addr ast

/-- `FloorsHold` is the policy reading at every account. -/
theorem floorsHold_iff_admits (fb : FloorBook) :
    FloorsHold fb ↔ ∀ addr ast, (fb.policyOf addr ast).admits (fb.balance addr ast) = true := by
  have h : ∀ addr ast, (fb.policyOf addr ast).admits (fb.balance addr ast) = true ↔
      (match fb.minBalance? addr ast with
        | none => True
        | some f => f ≤ fb.balance addr ast) := by
    intro addr ast
    unfold FloorPolicy.admits FloorBook.minBalance?
    cases (fb.policyOf addr ast).floor? <;> simp
  exact ⟨fun hf addr ast => (h addr ast).mpr (hf addr ast), fun hf addr ast => (h addr ast).mp (hf addr ast)⟩

theorem floorsHold_empty : FloorsHold FloorBook.empty := by
  intro addr ast
  have hb : FloorBook.empty.balance addr ast = 0 := rfl
  have hp : FloorBook.empty.policyOf addr ast =
      if addr.kind = .issuerWell ∧ addr.id = ast then .issuerWell none else .minReserve 0 := rfl
  unfold FloorBook.minBalance?
  rw [hp, hb]
  by_cases h : addr.kind = .issuerWell ∧ addr.id = ast
  · rw [ite_eq_left h]; exact trivial
  · rw [ite_eq_right h]; exact (by decide : ((0 : Nat) : Int) ≤ 0)

/-- Under `FloorsHold`, every account that is neither an issuer well nor a `member` (`user`,
`seat`, `escrow`, `feePool`) has balance `≥ 0` across all assets. -/
theorem nonIssuer_balance_nonneg_of_floorsHold {fb : FloorBook} (hfl : FloorsHold fb)
    (addr : AccountAddr) (ast : AssetId) (hkind : addr.kind ≠ .issuerWell) (hcust : addr.kind ≠ .member) :
    0 ≤ fb.balance addr ast := by
  obtain ⟨f, hmin, hf0⟩ := fb.nonIssuer_floor_nonneg addr ast hkind hcust
  have h := hfl addr ast
  rw [hmin] at h
  omega

/-- Under `FloorsHold`, a reserve account holds at least `+reserve`. -/
theorem reserve_le_balance_of_floorsHold {fb : FloorBook} (hfl : FloorsHold fb)
    {addr : AccountAddr} {ast : AssetId} {reserve : Nat}
    (hp : fb.policyOf addr ast = .minReserve reserve) : (reserve : Int) ≤ fb.balance addr ast :=
  (FloorPolicy.minReserve_admits_iff reserve _).mp (hp ▸ (floorsHold_iff_admits fb).mp hfl addr ast)

/-- Under `FloorsHold`, a `member` with a credit line holds at least `-limit`. -/
theorem neg_creditLimit_le_balance_of_floorsHold {fb : FloorBook} (hfl : FloorsHold fb)
    {addr : AccountAddr} {ast : AssetId} {limit : Nat}
    (hp : fb.policyOf addr ast = .creditLimit limit) : -(limit : Int) ≤ fb.balance addr ast :=
  (FloorPolicy.creditLimit_admits_iff limit _).mp (hp ▸ (floorsHold_iff_admits fb).mp hfl addr ast)

/-- Per-asset algebraic sum across all typed accounts in `fb`. -/
def FloorBook.assetSum (fb : FloorBook) (ast : AssetId) : Int :=
  ((fb.balances.entries.filter (fun p => p.1.2 == ast)).map Prod.snd).sum

@[simp] theorem FloorBook.assetSum_empty (ast : AssetId) :
    FloorBook.empty.assetSum ast = 0 := rfl

/-- Raw posting application (debiting `source` and crediting `destination`). -/
def FloorBook.applyRaw (fb : FloorBook) (p : TypedPosting) : FloorBook :=
  { fb with
    balances :=
      (fb.balances.addDelta (p.source, p.asset) (-(p.amount : Int))).addDelta
        (p.destination, p.asset) (p.amount : Int) }

theorem FloorBook.balance_applyRaw (fb : FloorBook) (p : TypedPosting)
    (addr : AccountAddr) (ast : AssetId) :
    (fb.applyRaw p).balance addr ast =
      fb.balance addr ast
        - (if addr = p.source ∧ ast = p.asset then (p.amount : Int) else 0)
        + (if addr = p.destination ∧ ast = p.asset then (p.amount : Int) else 0) := by
  unfold FloorBook.applyRaw FloorBook.balance
  simp only [FinMap.get_addDelta, Prod.mk.injEq]
  by_cases ha1 : addr = p.source <;>
    by_cases ha2 : addr = p.destination <;>
    by_cases hast : ast = p.asset
  all_goals
    simp_all
    try omega

@[simp] theorem FloorBook.minBalance?_applyRaw (fb : FloorBook) (p : TypedPosting)
    (addr : AccountAddr) (ast : AssetId) :
    (fb.applyRaw p).minBalance? addr ast = fb.minBalance? addr ast := rfl

theorem assetSum_addDelta (m : FinMap (AccountAddr × AssetId))
    (addr : AccountAddr) (pAst ast : AssetId) (d : Int) :
    (((m.addDelta (addr, pAst) d).entries.filter (fun q => q.1.2 == ast)).map Prod.snd).sum =
      ((m.entries.filter (fun q => q.1.2 == ast)).map Prod.snd).sum +
        (if pAst = ast then d else 0) := by
  unfold FinMap.addDelta
  cases hd : d == 0 with
  | true =>
    have hd0 : d = 0 := beq_iff_eq.mp hd
    subst hd0; simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons]
    by_cases ha : pAst = ast
    · subst ha
      simp only [beq_self_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · have hb : (pAst == ast) = false := beq_eq_false_iff_ne.mpr ha
      simp [hb, ha]

/-- **Algebraic Per-Asset Conservation (`applyRaw_conserves_asset`)**:
    Every `TypedPosting` preserves `assetSum` unconditionally for every asset. -/
theorem FloorBook.applyRaw_conserves_asset (fb : FloorBook) (p : TypedPosting) (ast : AssetId) :
    (fb.applyRaw p).assetSum ast = fb.assetSum ast := by
  unfold FloorBook.applyRaw FloorBook.assetSum
  rw [assetSum_addDelta, assetSum_addDelta]
  by_cases ha : p.asset = ast
  · subst ha; simp; omega
  · simp [ha]

/-- Floor-checked posting admission: verifies that after applying `p`, `p.source` still satisfies
    its floor (`accountFloorHoldsB`). -/
def FloorBook.admitPosting (fb : FloorBook) (p : TypedPosting) : Option FloorBook :=
  if (fb.applyRaw p).accountFloorHoldsB p.source p.asset then
    some (fb.applyRaw p)
  else
    none

/-- **Floor Preservation (`admitPosting_preserves_floors`)**:
    If `FloorsHold fb` and `fb.admitPosting p = some fb'`, then `FloorsHold fb'` AND
    `fb'.assetSum ast = fb.assetSum ast` for all `ast`. -/
theorem FloorBook.admitPosting_preserves_floors {fb fb' : FloorBook} (p : TypedPosting)
    (hfl : FloorsHold fb) (hadm : fb.admitPosting p = some fb') :
    FloorsHold fb' ∧ (∀ ast, fb'.assetSum ast = fb.assetSum ast) := by
  unfold FloorBook.admitPosting at hadm
  split at hadm
  · rename_i hsrc_ok
    injection hadm with heq
    subst heq
    refine ⟨?_, fun ast => fb.applyRaw_conserves_asset p ast⟩
    intro addr ast
    by_cases hs : addr = p.source ∧ ast = p.asset
    · rcases hs with ⟨rfl, rfl⟩
      unfold FloorBook.accountFloorHoldsB at hsrc_ok
      cases hmin : (fb.applyRaw p).minBalance? p.source p.asset with
      | none => trivial
      | some f =>
        rw [hmin] at hsrc_ok
        exact of_decide_eq_true hsrc_ok
    · have hprev := hfl addr ast
      rw [FloorBook.minBalance?_applyRaw]
      have hbal := FloorBook.balance_applyRaw fb p addr ast
      have hge : fb.balance addr ast ≤ (fb.applyRaw p).balance addr ast := by
        rw [hbal]
        simp only [hs, ↓reduceIte]
        by_cases hd : addr = p.destination ∧ ast = p.asset
        · simp [hd]; omega
        · simp [hd]
      cases hmin : fb.minBalance? addr ast with
      | none => trivial
      | some f =>
        rw [hmin] at hprev
        omega
  · cases hadm

/-- Batch floor-checked posting execution. -/
def FloorBook.admitBatch : FloorBook → List TypedPosting → Option FloorBook
  | fb, [] => some fb
  | fb, p :: ps =>
    match fb.admitPosting p with
    | some fb' => FloorBook.admitBatch fb' ps
    | none     => none

theorem FloorBook.admitBatch_preserves_floors {fb fb' : FloorBook} (ps : List TypedPosting)
    (hfl : FloorsHold fb) (hadm : FloorBook.admitBatch fb ps = some fb') :
    FloorsHold fb' ∧ (∀ ast, fb'.assetSum ast = fb.assetSum ast) := by
  induction ps generalizing fb with
  | nil =>
    cases hadm
    exact ⟨hfl, fun _ => rfl⟩
  | cons p rest ih =>
    unfold FloorBook.admitBatch at hadm
    split at hadm
    · rename_i fb1 hstep
      have ⟨hfl1, hcons1⟩ := FloorBook.admitPosting_preserves_floors p hfl hstep
      have ⟨hfl', hcons'⟩ := ih hfl1 hadm
      exact ⟨hfl', fun ast => (hcons' ast).trans (hcons1 ast)⟩
    · cases hadm

/-! ## 4. Direct Realization over `Obend.Ledger.Register` (`Reg` + `Movement`) -/

/-- Compile a `TypedPosting` to a balanced 2-movement `Register.Movement` list. -/
def TypedPosting.toMovements (p : TypedPosting) : List Movement :=
  transferMovements (p.source.toRegAccount p.asset) (p.destination.toRegAccount p.asset) p.amount

/-- Compile a `TypedPosting` to a `Register.Posting`. -/
def TypedPosting.toRegPosting (p : TypedPosting) (id doc origin : String) (period : Nat := 1) : Posting where
  id       := id
  doc      := doc
  period   := period
  reverses := none
  lines    := p.toMovements
  origin   := origin

theorem TypedPosting.toRegPosting_balanced (p : TypedPosting) (id doc origin : String) (period : Nat) :
    (p.toRegPosting id doc origin period).debits = (p.toRegPosting id doc origin period).credits := by
  unfold TypedPosting.toRegPosting Posting.debits Posting.credits TypedPosting.toMovements
  exact transferMovements_balanced _ _ _

/-- The `Register` account-delta of `p.toRegPosting` matches `FloorBook.applyRaw`'s balance step
    on every `(addr, ast)` pair! -/
theorem TypedPosting.toRegPosting_accountDelta (p : TypedPosting) (id doc origin : String) (period : Nat)
    (addr : AccountAddr) (ast : AssetId) :
    (p.toRegPosting id doc origin period).accountDelta (addr.toRegAccount ast) =
      (if addr = p.destination ∧ ast = p.asset then (p.amount : Int) else 0) -
        (if addr = p.source ∧ ast = p.asset then (p.amount : Int) else 0) := by
  unfold TypedPosting.toRegPosting Posting.accountDelta TypedPosting.toMovements
  rw [transferMovements_delta]
  have hd_iff : (addr.toRegAccount ast = p.destination.toRegAccount p.asset) ↔
      (addr = p.destination ∧ ast = p.asset) :=
    ⟨AccountAddr.toRegAccount_injective, fun ⟨h1, h2⟩ => by subst h1; subst h2; rfl⟩
  have hs_iff : (addr.toRegAccount ast = p.source.toRegAccount p.asset) ↔
      (addr = p.source ∧ ast = p.asset) :=
    ⟨AccountAddr.toRegAccount_injective, fun ⟨h1, h2⟩ => by subst h1; subst h2; rfl⟩
  simp [hd_iff, hs_iff]

/-- Append a `TypedPosting` onto a `Register.Reg`. -/
def Reg.appendTypedPosting (g : Reg) (p : TypedPosting) (doc origin : String) (period : Nat := 1) : Reg :=
  ⟨g.postings ++ [p.toRegPosting g.number doc origin period]⟩

/-- Fold a batch of `(TypedPosting, doc, origin)` items onto both `FloorBook` and `Register.Reg`. -/
def realizeBatchOnReg : List (TypedPosting × String × String) → FloorBook → Reg → Option (FloorBook × Reg)
  | [], fb, g => some (fb, g)
  | (p, doc, orig) :: rest, fb, g =>
    match fb.admitPosting p with
    | some fb' => realizeBatchOnReg rest fb' (g.appendTypedPosting p doc orig 1)
    | none     => none

/-- **Register-FloorBook Simulation & Non-Negative Floor Preservation Theorem (`realizeBatchOnReg_sound`)**:
    Whenever `FloorBook` and `Reg` agree on all `(addr, ast)` balances initially (`h_agree`),
    `FloorsHold fb` holds, and `realizeBatchOnReg items fb g = some (fb', g')`:
    1. `g'` and `fb'` continue to agree identically on EVERY `(addr, ast)` balance,
    2. `FloorsHold fb'` holds, so every account that is neither an issuer well nor a `member`
       (the only kind that may hold a credit line) in `g'` has `0 ≤ g'.accountBalance (addr.toRegAccount ast)`,
    3. Every asset's algebraic sum is conserved (`fb'.assetSum ast = fb.assetSum ast`). -/
theorem realizeBatchOnReg_sound {items : List (TypedPosting × String × String)}
    {fb fb' : FloorBook} {g g' : Reg}
    (hfl : FloorsHold fb)
    (h_agree : ∀ (addr : AccountAddr) (ast : AssetId),
      g.accountBalance (addr.toRegAccount ast) = fb.balance addr ast)
    (hrun : realizeBatchOnReg items fb g = some (fb', g')) :
    (∀ (addr : AccountAddr) (ast : AssetId),
      g'.accountBalance (addr.toRegAccount ast) = fb'.balance addr ast) ∧
    FloorsHold fb' ∧
    (∀ (addr : AccountAddr) (ast : AssetId),
      addr.kind ≠ AccountKind.issuerWell → addr.kind ≠ AccountKind.member →
        0 ≤ g'.accountBalance (addr.toRegAccount ast)) ∧
    (∀ (ast : AssetId), fb'.assetSum ast = fb.assetSum ast) := by
  induction items generalizing fb g with
  | nil =>
    cases hrun
    refine ⟨h_agree, hfl, ?_, fun _ => rfl⟩
    intro addr ast hk hu
    rw [h_agree addr ast]
    exact nonIssuer_balance_nonneg_of_floorsHold hfl addr ast hk hu
  | cons item rest ih =>
    rcases item with ⟨p, doc, orig⟩
    unfold realizeBatchOnReg at hrun
    split at hrun
    · rename_i fb1 hadm
      have ⟨hfl1, hcons1⟩ := FloorBook.admitPosting_preserves_floors p hfl hadm
      have hfb1_eq : fb1 = fb.applyRaw p := by
        unfold FloorBook.admitPosting at hadm
        split at hadm
        · injection hadm with heq; exact heq.symm
        · cases hadm
      have h_agree1 : ∀ (addr : AccountAddr) (ast : AssetId),
          (g.appendTypedPosting p doc orig 1).accountBalance (addr.toRegAccount ast) =
            fb1.balance addr ast := by
        intro addr ast
        unfold Reg.appendTypedPosting
        rw [Reg.accountBalance_append, h_agree addr ast, hfb1_eq,
            FloorBook.balance_applyRaw, TypedPosting.toRegPosting_accountDelta]
        omega
      obtain ⟨hag', hfl', hnonneg', hcons'⟩ := ih hfl1 h_agree1 hrun
      exact ⟨hag', hfl', hnonneg', fun ast => (hcons' ast).trans (hcons1 ast)⟩
    · cases hrun

/-! ## 5. Teeth: floor polarity (gate G2) -/

/-- The polarity is observable on concrete balances: a reserve of 5 refuses `-5`, a credit line
of 5 admits it. -/
example : (FloorPolicy.minReserve 5).admits (-5) = false := by decide
example : (FloorPolicy.creditLimit 5).admits (-5) = true := by decide

/-- A credit line is honoured on a `member` and ignored on a `user`. -/
example : ({ policies := [((.member 1, 0), .creditLimit 10)] } : FloorBook).policyOf (.member 1) 0 =
    .creditLimit 10 := by decide
example : ({ policies := [((.user 1, 0), .creditLimit 10)] } : FloorBook).policyOf (.user 1) 0 =
    .minReserve 0 := by decide
/-- An `issuerWell` entry on an account that is not that asset's well is not honoured. -/
example : ({ policies := [((.user 1, 0), .issuerWell none)] } : FloorBook).policyOf (.user 1) 0 =
    .minReserve 0 := by decide

/-- A member with a credit line of 10 may go to `-10` and no further; a user holding a reserve of
3 may not go below `+3`. -/
example : (({ policies := [((.member 1, 0), .creditLimit 10)] } : FloorBook).admitPosting
    ⟨.member 1, .user 2, 0, 10⟩).isSome = true := by decide
example : (({ policies := [((.member 1, 0), .creditLimit 10)] } : FloorBook).admitPosting
    ⟨.member 1, .user 2, 0, 11⟩).isSome = false := by decide
example : (({ policies := [((.member 1, 0), .creditLimit 10), ((.user 2, 0), .minReserve 3)] } :
    FloorBook).admitBatch [⟨.member 1, .user 2, 0, 10⟩, ⟨.user 2, .member 1, 0, 7⟩]).isSome = true := by
  decide
example : (({ policies := [((.member 1, 0), .creditLimit 10), ((.user 2, 0), .minReserve 3)] } :
    FloorBook).admitBatch [⟨.member 1, .user 2, 0, 10⟩, ⟨.user 2, .member 1, 0, 8⟩]).isSome = false := by
  decide

-- Reading a reserve as a credit line (`minReserve r ↦ -r`, the `-floor` convention) breaks
-- the stored proofs of the reserve reading and of non-negativity.
#tooth Obend.Ledger.FloorPolicy.minReserve_admits_iff by mutation Obend.Ledger.FloorPolicy.floor? :=
  fun p => match p with
    | .creditLimit limit => some (-(limit : Int))
    | .minReserve reserve => some (-(reserve : Int))
    | .issuerWell (some cap) => some (-(cap : Int))
    | .issuerWell none => none
#tooth Obend.Ledger.FloorBook.nonIssuer_floor_nonneg by mutation Obend.Ledger.FloorPolicy.floor? :=
  fun p => match p with
    | .creditLimit limit => some (-(limit : Int))
    | .minReserve reserve => some (-(reserve : Int))
    | .issuerWell (some cap) => some (-(cap : Int))
    | .issuerWell none => none

-- Honouring a credit line on every account breaks `policyOf_creditLimit`.
#tooth Obend.Ledger.FloorBook.policyOf_creditLimit by mutation Obend.Ledger.FloorBook.policyOf :=
  fun fb addr ast => match fb.policies.lookup (addr, ast) with
    | some (.creditLimit limit) => .creditLimit limit
    | _ => .minReserve 0

-- Admitting without the floor check breaks floor preservation.
#tooth Obend.Ledger.FloorBook.admitPosting_preserves_floors by mutation
  Obend.Ledger.FloorBook.admitPosting := fun fb p => some (fb.applyRaw p)

end Obend.Ledger

end
