/-
# Theory.AuthMap — an authenticated map with an incremental root and openings

DATAMODEL §3.2 / §3.9 / §5 A3.  Today a cell root is a hash of the whole encoded
cell (`CellState.Materialized.root`) and the world "root" is cSHAKE over the whole
image; nothing can be opened and every write rehashes everything.  This module is
the object that replaces that: a sparse Merkle map of fixed depth whose root is a
function of the logical map, which updates along one path, and which has
membership / non-membership openings.

## Shape

* **Parameters (`Scheme`).**  One hash `H : List UInt8 → D`, the only
  cryptographic object.  Byte renderings of digests, keys and values with the
  injectivity each needs (prefix-free for the variable-length ones), and an index
  `ix : K → List Bool` of fixed length `depth`.  Q2's index — hash the canonical
  key bytes — is `hashIndex`; the world level (§3.2) may use the id's bits.
* **Slots.**  `Map K V := List Bool → Option (K × V)`: each index path holds at
  most one occupant, which carries its own key.  `lookup` reads the occupant at
  `ix k` and answers only if the occupant's key *is* `k`; so two keys that share
  an index are never confused, only evicted (`index_collision_evicts`), and the
  eviction happens exactly where Q2's premise is stated (`hashIndex_collision`).
* **Root.**  `subRoot` is the full binary tree over the slots; empty subtrees are
  not special-cased, so §3.2's `E_i` are simply `subRoot` of an empty subtree.
  This is the specification; a cached sparse representation (Wave D) must agree
  with it, which is what `root_update` makes cheap to state.
* **Openings.**  The occupant of the slot plus `depth` siblings.  A
  non-membership opening is either an empty slot or a slot held by another key.

## Theorems

* `verify_opening` — completeness, for every map and key.
* `root_update` — the root after `write` is `rootAfter` of the *old* opening:
  the incremental-root fact.  `root_logical` — the root is a function of the
  logical map (`lookup`) on well-formed maps.
* `forgery_exhibits_collision` — unconditional reduction: a verifying opening for
  a wrong value exhibits two distinct inputs of `H`, at the same position of the
  honest and the claimed hash chains, with equal digests.
* `verify_sound` — its corollary under `PathBinding`, the pair-scoped carrier:
  `H` separates the aligned pairs of inputs this one check compares.  Poles:
  `honest_binding` (inhabited at *every* `H`, including 8-bit toy digests — not
  empty at finite digest width, unlike `BindingCommitment`, SYNTHESIS M11),
  `lengthHash_binding_fails` (refuted at a length hash where a forged opening
  verifies), `idHash_sound` (holds for every opening at an injective toy hash).
* `worldRoot_write`, `world_sound`, `two_level_sound` — Q3's two levels.
* `pathRootM_tick` — cost: `depth + 1` hash invocations per verification and per
  incremental update, measured on the same monadic code the pure path runs.
-/
import Mathlib.Data.List.Forall2

namespace Minidregg.Theory.AuthMap

set_option autoImplicit false

/-! ## Byte framing -/

/-- A rendering is prefix-free when its output can be split off the front of any
longer byte string.  Fixed width implies it; so does a length prefix. -/
def PrefixFree {α : Type} (f : α → List UInt8) : Prop :=
  ∀ (a b : α) (s t : List UInt8), f a ++ s = f b ++ t → a = b ∧ s = t

theorem PrefixFree.injective {α : Type} {f : α → List UInt8} (h : PrefixFree f) :
    Function.Injective f := by
  intro a b hab
  exact (h a b [] [] (by simpa using hab)).1

theorem prefixFree_of_fixedWidth {α : Type} (f : α → List UInt8) (w : Nat)
    (hw : ∀ a, (f a).length = w) (hinj : Function.Injective f) : PrefixFree f := by
  intro a b s t h
  have hl : (f a).length = (f b).length := by rw [hw, hw]
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨hinj h1, h2⟩

/-- A variable-length rendering made prefix-free by a unary length prefix.  Used
by the injective toy pole, whose digests are unbounded byte strings. -/
def unaryFrame (bs : List UInt8) : List UInt8 :=
  List.replicate bs.length 1 ++ 0 :: bs

theorem replicate_one_zero_inj :
    ∀ (a b : Nat) (u v : List UInt8),
      List.replicate a (1 : UInt8) ++ 0 :: u = List.replicate b 1 ++ 0 :: v →
        a = b ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, b + 1, u, v, h => by simp [List.replicate_succ] at h
  | a + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, u, v, h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := replicate_one_zero_inj a b u v h
      exact ⟨by omega, h2⟩

theorem unaryFrame_prefixFree : PrefixFree unaryFrame := by
  intro a b s t h
  simp only [unaryFrame, List.append_assoc, List.cons_append] at h
  obtain ⟨hl, h'⟩ := replicate_one_zero_inj _ _ _ _ h
  exact List.append_inj h' hl |>.imp id id

/-! ## Slots: the logical map -/

/-- Index path ↦ occupant.  The occupant carries its key. -/
abbrev Map (K V : Type) := List Bool → Option (K × V)

section Slots

variable {K V : Type} [DecidableEq K] (ix : K → List Bool)

def Map.empty : Map K V := fun _ => none

/-- What an occupant says about key `k`. -/
def readAt (k : K) : Option (K × V) → Option V
  | some (k', x) => if k' = k then some x else none
  | none => none

/-- The logical reading: the value at `k` is the occupant's value when the
occupant's key is `k`. -/
def lookup (m : Map K V) (k : K) : Option V := readAt k (m (ix k))

/-- The slot content after writing `v` at `k`, given the previous occupant.
Deleting `k` leaves another key's occupancy alone. -/
def slotAfter (occ : Option (K × V)) (k : K) : Option V → Option (K × V)
  | some x => some (k, x)
  | none =>
    match occ with
    | some (k', x') => if k' = k then none else some (k', x')
    | none => none

def write (m : Map K V) (k : K) (v : Option V) : Map K V :=
  fun p => if p = ix k then slotAfter (m p) k v else m p

/-- Every occupant sits at its own index. -/
def WF (m : Map K V) : Prop := ∀ p k x, m p = some (k, x) → ix k = p

omit [DecidableEq K] in
theorem wf_empty : WF ix (Map.empty : Map K V) := by
  intro p k x h; cases h

theorem slotAfter_eq_some {occ : Option (K × V)} {k k' : K} {v : Option V} {x : V}
    (h : slotAfter occ k v = some (k', x)) : k' = k ∨ occ = some (k', x) := by
  cases v with
  | some y =>
    simp only [slotAfter, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl h.1.symm
  | none =>
    rcases occ with _ | ⟨k'', x''⟩
    · simp [slotAfter] at h
    · simp only [slotAfter] at h
      by_cases hk : k'' = k
      · simp [hk] at h
      · simp only [hk, if_false] at h
        exact Or.inr h

theorem readAt_slotAfter_self (occ : Option (K × V)) (k : K) (v : Option V) :
    readAt k (slotAfter occ k v) = v := by
  cases v with
  | some x => simp [slotAfter, readAt]
  | none =>
    rcases occ with _ | ⟨k'', x⟩
    · rfl
    · by_cases h : k'' = k
      · simp [slotAfter, readAt, h]
      · simp [slotAfter, readAt, h]

theorem readAt_slotAfter_none {k k' : K} (hne : k' ≠ k) (occ : Option (K × V)) :
    readAt k' (slotAfter occ k none) = readAt k' occ := by
  rcases occ with _ | ⟨k'', x⟩
  · rfl
  · by_cases h : k'' = k
    · subst h; simp [slotAfter, readAt, Ne.symm hne]
    · simp [slotAfter, h]

theorem wf_write {m : Map K V} (hm : WF ix m) (k : K) (v : Option V) :
    WF ix (write ix m k v) := by
  intro p k' x h
  unfold write at h
  by_cases hp : p = ix k
  · rw [if_pos hp] at h
    rcases slotAfter_eq_some h with hk | h'
    · rw [hk, hp]
    · exact hm _ _ _ h'
  · rw [if_neg hp] at h
    exact hm _ _ _ h

theorem lookup_write_self (m : Map K V) (k : K) (v : Option V) :
    lookup ix (write ix m k v) k = v := by
  unfold lookup write
  rw [if_pos rfl]
  exact readAt_slotAfter_self _ _ _

/-- The frame: a write at `k` leaves `k'` alone unless it *inserts* at an index
`k'` shares.  The side condition is exactly Q2's premise (`hashIndex_collision`). -/
theorem lookup_write_ne (m : Map K V) {k k' : K} (hne : k' ≠ k) (v : Option V)
    (hsep : ix k' ≠ ix k ∨ v = none) :
    lookup ix (write ix m k v) k' = lookup ix m k' := by
  unfold lookup write
  by_cases hi : ix k' = ix k
  · rcases hsep with h | h
    · exact absurd hi h
    subst h
    rw [if_pos hi]
    exact readAt_slotAfter_none hne _
  · rw [if_neg hi]

/-- On well-formed maps the slots are determined by the logical map. -/
theorem map_eq_of_lookup {m m' : Map K V} (hm : WF ix m) (hm' : WF ix m')
    (h : ∀ k, lookup ix m k = lookup ix m' k) : m = m' := by
  funext p
  rcases hp : m p with _ | ⟨k, x⟩
  · rcases hp' : m' p with _ | ⟨k', x'⟩
    · rfl
    · have hi := hm' _ _ _ hp'
      have := h k'
      simp [lookup, readAt, hi, hp, hp'] at this
  · have hi := hm _ _ _ hp
    have := h k
    rcases hp' : m' p with _ | ⟨k', x'⟩
    · simp [lookup, readAt, hi, hp, hp'] at this
    · simp only [lookup, readAt, hi, hp, hp', if_true] at this
      by_cases hk : k' = k
      · subst hk
        simp only [if_true, Option.some.injEq] at this
        rw [this]
      · simp [hk] at this

end Slots

/-! ## The scheme -/

/-- All parameters of one authenticated map.  `H` is the only cryptographic
object; every other field is a rendering with a checkable injectivity property. -/
structure Scheme (K V D : Type) where
  H : List UInt8 → D
  digestBytes : D → List UInt8
  keyBytes : K → List UInt8
  valBytes : V → List UInt8
  digestBytes_prefixFree : PrefixFree digestBytes
  keyBytes_prefixFree : PrefixFree keyBytes
  valBytes_injective : Function.Injective valBytes
  depth : Nat
  ix : K → List Bool
  ix_length : ∀ k, (ix k).length = depth

/-- Q2: the index is the first `depth` bits of `H` over the tagged canonical key
bytes.  One hash invocation per index computation. -/
def hashIndex {K D : Type} (H : List UInt8 → D) (keyBytes : K → List UInt8)
    (bitsOf : D → List Bool) (k : K) : List Bool :=
  bitsOf (H (3 :: keyBytes k))

/-- Q2's premise, located: two distinct keys at one hashed index are two distinct
inputs of `H` with equal digests (when `bitsOf` keeps the whole digest), i.e. an
instance of the same carrier `Binds` that opening soundness uses. -/
theorem hashIndex_collision {K D : Type} (H : List UInt8 → D) {keyBytes : K → List UInt8}
    (hkb : Function.Injective keyBytes) {bitsOf : D → List Bool}
    (hbits : Function.Injective bitsOf) {k k' : K} (hne : k ≠ k')
    (h : hashIndex H keyBytes bitsOf k = hashIndex H keyBytes bitsOf k') :
    (3 :: keyBytes k) ≠ (3 :: keyBytes k') ∧ H (3 :: keyBytes k) = H (3 :: keyBytes k') :=
  ⟨fun e => hne (hkb (List.cons.inj e).2), hbits h⟩

namespace Scheme

variable {K V D : Type} (S : Scheme K V D)

/-! ### Hash inputs — domain-separated by the first byte -/

def leafInput : Option (K × V) → List UInt8
  | none => [2]
  | some (k, x) => 0 :: (S.keyBytes k ++ S.valBytes x)

def nodeInput (l r : D) : List UInt8 := 1 :: (S.digestBytes l ++ S.digestBytes r)

def leafDigest (o : Option (K × V)) : D := S.H (S.leafInput o)

def nodeHash (l r : D) : D := S.H (S.nodeInput l r)

theorem leafInput_injective : Function.Injective S.leafInput := by
  intro a b h
  rcases a with _ | ⟨k, x⟩ <;> rcases b with _ | ⟨k', x'⟩
  · rfl
  · simp [leafInput] at h
  · simp [leafInput] at h
  · simp only [leafInput, List.cons.injEq, true_and] at h
    obtain ⟨hk, hv⟩ := S.keyBytes_prefixFree k k' _ _ h
    subst hk
    rw [S.valBytes_injective hv]

theorem nodeInput_inj {l r l' r' : D} (h : S.nodeInput l r = S.nodeInput l' r') :
    l = l' ∧ r = r' := by
  simp only [nodeInput, List.cons.injEq, true_and] at h
  obtain ⟨hl, hr⟩ := S.digestBytes_prefixFree l l' _ _ h
  exact ⟨hl, S.digestBytes_prefixFree.injective hr⟩

/-! ### The tree (specification) -/

/-- The root of the subtree at prefix `p` with `i` levels below it. -/
def subRoot (m : Map K V) : Nat → List Bool → D
  | 0, p => S.leafDigest (m p)
  | i + 1, p => S.nodeHash (subRoot m i (p ++ [false])) (subRoot m i (p ++ [true]))

def root (m : Map K V) : D := S.subRoot m S.depth []

/-- The siblings along `bits` below prefix `pre`, top-down. -/
def openAt (m : Map K V) : List Bool → List Bool → List D
  | _, [] => []
  | pre, b :: rest => S.subRoot m rest.length (pre ++ [!b]) :: openAt m (pre ++ [b]) rest

structure Opening (K V D : Type) where
  occupant : Option (K × V)
  siblings : List D

def opening (m : Map K V) (k : K) : Opening K V D :=
  ⟨m (S.ix k), S.openAt m [] (S.ix k)⟩

/-! ### Recomputing a root from a path — one monadic definition

The verifier and the incremental update both run `climbM`.  The pure path
instantiates the hash oracle at `Id`; the cost theorem instantiates it at a
counting state monad.  There is one definition, not a counted twin. -/

def climbM {M : Type → Type} [Monad M] (hash : List UInt8 → M D) (leaf : D) :
    List Bool → List D → M D
  | [], _ => pure leaf
  | _ :: _, [] => pure leaf
  | b :: bs, s :: ss => do
      let c ← climbM hash leaf bs ss
      hash (if b then S.nodeInput s c else S.nodeInput c s)

def pathRootM {M : Type → Type} [Monad M] (hash : List UInt8 → M D) (leafIn : List UInt8)
    (bits : List Bool) (sibs : List D) : M D := do
  let l ← hash leafIn
  S.climbM hash l bits sibs

def climb (leaf : D) (bits : List Bool) (sibs : List D) : D :=
  Id.run (S.climbM (fun x => pure (S.H x)) leaf bits sibs)

def pathRoot (leafIn : List UInt8) (bits : List Bool) (sibs : List D) : D :=
  Id.run (S.pathRootM (fun x => pure (S.H x)) leafIn bits sibs)

theorem climb_nil (leaf : D) (sibs : List D) : S.climb leaf [] sibs = leaf := rfl

theorem climb_cons (leaf : D) (b : Bool) (bs : List Bool) (s : D) (ss : List D) :
    S.climb leaf (b :: bs) (s :: ss) =
      S.H (if b then S.nodeInput s (S.climb leaf bs ss)
        else S.nodeInput (S.climb leaf bs ss) s) := rfl

theorem pathRoot_eq (leafIn : List UInt8) (bits : List Bool) (sibs : List D) :
    S.pathRoot leafIn bits sibs = S.climb (S.H leafIn) bits sibs := rfl

/-! ### Verification and the incremental root -/

/-- The leaf input a claim commits to, or `none` if the claim is malformed (a
non-membership claim whose witness occupant is the key itself). -/
def claimLeaf [DecidableEq K] (k : K) (v : Option V) (occ : Option (K × V)) :
    Option (List UInt8) :=
  match v with
  | some x => some (S.leafInput (some (k, x)))
  | none =>
    match occ with
    | none => some (S.leafInput none)
    | some (k', x') => if k' = k then none else some (S.leafInput (some (k', x')))

def verify [DecidableEq K] [DecidableEq D] (r : D) (k : K) (v : Option V)
    (π : Opening K V D) : Bool :=
  match S.claimLeaf k v π.occupant with
  | none => false
  | some leafIn =>
    decide (π.siblings.length = S.depth) && decide (S.pathRoot leafIn (S.ix k) π.siblings = r)

/-- The root after writing `v` at `k`, from the old opening alone. -/
def rootAfter [DecidableEq K] (π : Opening K V D) (k : K) (v : Option V) : D :=
  S.pathRoot (S.leafInput (slotAfter π.occupant k v)) (S.ix k) π.siblings

/-! ### Completeness -/

theorem openAt_length (m : Map K V) :
    ∀ (pre bits : List Bool), (S.openAt m pre bits).length = bits.length
  | _, [] => rfl
  | pre, _ :: rest => by simp [openAt, openAt_length m (pre ++ _) rest]

/-- Climbing the honest siblings from the honest leaf reaches the subtree root. -/
theorem climb_openAt (m : Map K V) :
    ∀ (bits pre : List Bool),
      S.climb (S.leafDigest (m (pre ++ bits))) bits (S.openAt m pre bits) =
        S.subRoot m bits.length pre
  | [], pre => by simp [climb_nil, subRoot]
  | b :: rest, pre => by
      have ih := climb_openAt m rest (pre ++ [b])
      simp only [List.append_assoc, List.singleton_append] at ih
      simp only [openAt, climb_cons, ih, subRoot, nodeHash]
      cases b <;> rfl

theorem claimLeaf_lookup [DecidableEq K] (m : Map K V) (k : K) :
    S.claimLeaf k (lookup S.ix m k) (m (S.ix k)) = some (S.leafInput (m (S.ix k))) := by
  unfold lookup
  rcases m (S.ix k) with _ | ⟨k', x⟩
  · rfl
  · by_cases h : k' = k
    · subst h; simp [claimLeaf, readAt]
    · simp [claimLeaf, readAt, h]

/-- **Completeness.**  The honest opening of any key verifies against the root,
for membership and non-membership alike. -/
theorem verify_opening [DecidableEq K] [DecidableEq D] (m : Map K V) (k : K) :
    S.verify (S.root m) k (lookup S.ix m k) (S.opening m k) = true := by
  have h := S.climb_openAt m (S.ix k) []
  simp only [List.nil_append, S.ix_length] at h
  simp [verify, opening, S.claimLeaf_lookup, pathRoot_eq, openAt_length, S.ix_length,
    root, ← h, leafDigest]

/-! ### The incremental root -/

theorem subRoot_congr {m m' : Map K V} :
    ∀ (i : Nat) (p : List Bool), (∀ q, q.length = i → m (p ++ q) = m' (p ++ q)) →
      S.subRoot m i p = S.subRoot m' i p
  | 0, p, h => by simpa [subRoot] using congrArg S.leafDigest (h [] rfl)
  | i + 1, p, h => by
      simp only [subRoot]
      rw [subRoot_congr i (p ++ [false]) (fun q hq => by simpa using h (false :: q) (by simp [hq])),
        subRoot_congr i (p ++ [true]) (fun q hq => by simpa using h (true :: q) (by simp [hq]))]

theorem openAt_congr {m m' : Map K V} :
    ∀ (bits pre : List Bool), (∀ p, p ≠ pre ++ bits → m p = m' p) →
      S.openAt m pre bits = S.openAt m' pre bits
  | [], _, _ => rfl
  | b :: rest, pre, h => by
      simp only [openAt, List.cons.injEq]
      constructor
      · apply S.subRoot_congr
        intro q _
        apply h
        simp
      · apply openAt_congr rest (pre ++ [b])
        intro p hp
        exact h p (by simpa using hp)

/-- **The incremental root.**  The root of the written map is computed from the
old opening and the new value alone — `depth + 1` hashes (`pathRootM_tick`). -/
theorem root_update [DecidableEq K] (m : Map K V) (k : K) (v : Option V) :
    S.root (write S.ix m k v) = S.rootAfter (S.opening m k) k v := by
  have h := S.climb_openAt (write S.ix m k v) (S.ix k) []
  simp only [List.nil_append, S.ix_length] at h
  have hsib : S.openAt (write S.ix m k v) [] (S.ix k) = S.openAt m [] (S.ix k) := by
    apply S.openAt_congr
    intro p hp
    simp only [List.nil_append] at hp
    simp [write, hp]
  rw [root, ← h, hsib]
  simp [rootAfter, opening, pathRoot_eq, leafDigest, write]

/-- The root is a function of the logical map (on well-formed slot maps). -/
theorem root_logical [DecidableEq K] {m m' : Map K V} (hm : WF S.ix m) (hm' : WF S.ix m')
    (h : ∀ k, lookup S.ix m k = lookup S.ix m' k) : S.root m = S.root m' := by
  rw [map_eq_of_lookup S.ix hm hm' h]

/-! ### Soundness: the carrier, the reduction, the corollary -/

/-- `H` separates this pair: equal digests only for equal inputs. -/
def Binds (x y : List UInt8) : Prop := S.H x = S.H y → x = y

/-- The inputs the honest tree hashes along `bits` below `pre`, top-down. -/
def honestInputs (m : Map K V) : List Bool → List Bool → List (List UInt8)
  | pre, [] => [S.leafInput (m pre)]
  | pre, b :: rest =>
    S.nodeInput (S.subRoot m rest.length (pre ++ [false]))
        (S.subRoot m rest.length (pre ++ [true])) ::
      honestInputs m (pre ++ [b]) rest

/-- The inputs `climbM` hashes for a claimed leaf and siblings, top-down. -/
def claimInputs (leafIn : List UInt8) : List Bool → List D → List (List UInt8)
  | [], _ => [leafIn]
  | _ :: _, [] => [leafIn]
  | b :: bs, s :: ss =>
    (if b then S.nodeInput s (S.climb (S.H leafIn) bs ss)
      else S.nodeInput (S.climb (S.H leafIn) bs ss) s) :: claimInputs leafIn bs ss

/-- **The carrier.**  Collision resistance scoped to the pairs one opening check
actually compares: at each level, the honest tree's input and the claim's input.
It names finitely many concrete pairs, so it is not a global injectivity of `H`
and is not refuted by pigeonhole at finite digest width (contrast
`BindingCommitment`, SYNTHESIS M11, and `CellRegistry.RootBindingPremise`).  It
is inhabited at every `H` by the honest opening (`honest_binding`) and refuted
by a forgery at a length hash (`lengthHash_binding_fails`). -/
structure PathBinding [DecidableEq K] (m : Map K V) (k : K) (v : Option V)
    (π : Opening K V D) : Prop where
  aligned : ∀ leafIn, S.claimLeaf k v π.occupant = some leafIn →
    π.siblings.length = S.depth →
      List.Forall₂ S.Binds (S.honestInputs m [] (S.ix k))
        (S.claimInputs leafIn (S.ix k) π.siblings)

theorem honestInputs_length (m : Map K V) :
    ∀ (pre bits : List Bool), (S.honestInputs m pre bits).length = bits.length + 1
  | _, [] => rfl
  | pre, _ :: rest => by simp [honestInputs, honestInputs_length m (pre ++ _) rest]

theorem claimInputs_length (leafIn : List UInt8) :
    ∀ (bits : List Bool) (sibs : List D), sibs.length = bits.length →
      (S.claimInputs leafIn bits sibs).length = bits.length + 1
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | _ :: bs, _ :: ss, h => by
      simp only [claimInputs, List.length_cons]
      rw [claimInputs_length leafIn bs ss (by simpa using h)]

/-- Walking down a verifying path under the carrier pins the claimed leaf input
to the honest one. -/
theorem leaf_of_climb (m : Map K V) (leafIn : List UInt8) :
    ∀ (bits pre : List Bool) (sibs : List D), sibs.length = bits.length →
      S.climb (S.H leafIn) bits sibs = S.subRoot m bits.length pre →
      List.Forall₂ S.Binds (S.honestInputs m pre bits) (S.claimInputs leafIn bits sibs) →
      leafIn = S.leafInput (m (pre ++ bits))
  | [], pre, sibs, _, hr, hb => by
      simp only [honestInputs, claimInputs, List.forall₂_cons] at hb
      simp only [climb_nil, subRoot, leafDigest] at hr
      simpa using (hb.1 hr.symm).symm
  | _ :: _, _, [], hl, _, _ => by simp at hl
  | b :: bs, pre, s :: ss, hl, hr, hb => by
      simp only [honestInputs, claimInputs, List.forall₂_cons] at hb
      obtain ⟨hhead, htail⟩ := hb
      simp only [climb_cons, subRoot, nodeHash] at hr
      have hl' : ss.length = bs.length := by simpa using hl
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hhead hr
        have heq := S.nodeInput_inj (hhead hr.symm)
        have := leaf_of_climb m leafIn bs (pre ++ [false]) ss hl' heq.1.symm htail
        simpa using this
      · simp only [↓reduceIte] at hhead hr
        have heq := S.nodeInput_inj (hhead hr.symm)
        have := leaf_of_climb m leafIn bs (pre ++ [true]) ss hl' heq.2.symm htail
        simpa using this

/-- A claimed leaf equal to the honest leaf reads the logical value. -/
theorem claimLeaf_sound [DecidableEq K] (m : Map K V) (k : K) (v : Option V)
    (occ : Option (K × V)) (leafIn : List UInt8) (hc : S.claimLeaf k v occ = some leafIn)
    (hl : leafIn = S.leafInput (m (S.ix k))) : v = lookup S.ix m k := by
  unfold lookup
  cases v with
  | some x =>
    simp only [claimLeaf, Option.some.injEq] at hc
    subst hc
    have := S.leafInput_injective hl
    rw [← this]; simp [readAt]
  | none =>
    rcases occ with _ | ⟨k', x'⟩
    · simp only [claimLeaf, Option.some.injEq] at hc
      subst hc
      have := S.leafInput_injective hl
      rw [← this]; rfl
    · simp only [claimLeaf] at hc
      split_ifs at hc with hk
      simp only [Option.some.injEq] at hc
      subst hc
      have := S.leafInput_injective hl
      rw [← this]; simp [readAt, hk]

/-- **Soundness under the carrier.**  A verifying opening for `(k, v)` against
the root of `m`, whose compared pairs `H` separates, proves `lookup m k = v`. -/
theorem verify_sound [DecidableEq K] [DecidableEq D] (m : Map K V) (k : K) (v : Option V)
    (π : Opening K V D) (hbind : S.PathBinding m k v π)
    (h : S.verify (S.root m) k v π = true) : v = lookup S.ix m k := by
  unfold verify at h
  rcases hc : S.claimLeaf k v π.occupant with _ | leafIn
  · simp [hc] at h
  · simp only [hc, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, hroot⟩ := h
    have hlen' : π.siblings.length = (S.ix k).length := by rw [S.ix_length]; exact hlen
    rw [pathRoot_eq, root, ← S.ix_length k] at hroot
    have := S.leaf_of_climb m leafIn (S.ix k) [] π.siblings hlen' hroot
      (hbind.aligned leafIn hc hlen)
    exact S.claimLeaf_sound m k v π.occupant leafIn hc (by simpa using this)

/-- **The reduction, unconditionally.**  A verifying opening for a wrong value
exhibits a collision of `H`: two distinct inputs, at the same level of the honest
and the claimed hash chains, with equal digests. -/
theorem forgery_exhibits_collision [DecidableEq K] [DecidableEq D] (m : Map K V) (k : K)
    (v : Option V) (π : Opening K V D) (h : S.verify (S.root m) k v π = true)
    (hne : v ≠ lookup S.ix m k) :
    ∃ leafIn, S.claimLeaf k v π.occupant = some leafIn ∧
      ∃ x y, (x, y) ∈ (S.honestInputs m [] (S.ix k)).zip
          (S.claimInputs leafIn (S.ix k) π.siblings) ∧
        x ≠ y ∧ S.H x = S.H y := by
  have hv := h
  unfold verify at hv
  rcases hc : S.claimLeaf k v π.occupant with _ | leafIn
  · simp [hc] at hv
  simp only [hc, Bool.and_eq_true, decide_eq_true_eq] at hv
  refine ⟨leafIn, rfl, ?_⟩
  by_contra hno
  simp only [not_exists, not_and] at hno
  apply hne
  refine S.verify_sound m k v π ⟨fun leafIn' hc' hlen => ?_⟩ h
  rw [hc] at hc'
  cases hc'
  rw [List.forall₂_iff_zip]
  refine ⟨?_, fun hxy hH => ?_⟩
  · rw [S.honestInputs_length, S.claimInputs_length _ _ _ (by rw [S.ix_length]; exact hlen)]
  · by_contra hxne
    exact hno _ _ hxy hxne hH

/-- The honest opening's claimed inputs are the honest inputs. -/
theorem claimInputs_openAt (m : Map K V) :
    ∀ (bits pre : List Bool),
      S.claimInputs (S.leafInput (m (pre ++ bits))) bits (S.openAt m pre bits) =
        S.honestInputs m pre bits
  | [], pre => by simp [claimInputs, honestInputs]
  | b :: rest, pre => by
      have ih := claimInputs_openAt m rest (pre ++ [b])
      have hc := S.climb_openAt m rest (pre ++ [b])
      simp only [List.append_assoc, List.singleton_append] at ih hc
      simp only [openAt, claimInputs, honestInputs, ih, List.cons.injEq, and_true]
      simp only [leafDigest] at hc
      rw [hc]
      cases b <;> rfl

/-- **Satisfiable pole, at every `H`.**  The honest opening meets the carrier —
for any hash whatsoever, including an 8-bit toy.  So the carrier's premise type
is inhabited at every digest width. -/
theorem honest_binding [DecidableEq K] (m : Map K V) (k : K) :
    S.PathBinding m k (lookup S.ix m k) (S.opening m k) := by
  refine ⟨fun leafIn hc _ => ?_⟩
  simp only [opening] at hc
  rw [S.claimLeaf_lookup] at hc
  cases hc
  have := S.claimInputs_openAt m (S.ix k) []
  simp only [List.nil_append] at this
  simp only [opening, this]
  exact List.forall₂_same.mpr fun _ _ _ => rfl

/-- At a hash injective on all inputs every opening meets the carrier.  Only an
unbounded digest type admits such an `H`; at finite width the carrier is met
per check (`honest_binding`), never globally. -/
theorem binding_of_injective [DecidableEq K] (hH : Function.Injective S.H) (m : Map K V)
    (k : K) (v : Option V) (π : Opening K V D) : S.PathBinding m k v π := by
  refine ⟨fun leafIn _ hlen => ?_⟩
  rw [List.forall₂_iff_zip]
  refine ⟨?_, fun _ h => hH h⟩
  rw [S.honestInputs_length, S.claimInputs_length _ _ _ (by rw [S.ix_length]; exact hlen)]

/-! ### Cost -/

/-- The hash oracle that counts its invocations. -/
def tick (x : List UInt8) : StateM Nat D := fun n => (S.H x, n + 1)

theorem climbM_tick (leaf : D) :
    ∀ (bits : List Bool) (sibs : List D) (n : Nat), sibs.length = bits.length →
      (S.climbM S.tick leaf bits sibs).run n = (S.climb leaf bits sibs, n + bits.length)
  | [], _, n, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | b :: bs, s :: ss, n, h => by
      have ih := climbM_tick leaf bs ss n (by simpa using h)
      simp only [climbM, StateT.run, bind, StateT.bind] at ih ⊢
      rw [ih]
      simp only [climb_cons, List.length_cons]
      refine Prod.ext ?_ ?_
      · cases b <;> rfl
      · show n + bs.length + 1 = n + (bs.length + 1)
        omega

/-- **Cost.**  Recomputing a root from a leaf input and a path of `bits.length`
siblings invokes `H` exactly `bits.length + 1` times, and returns the pure
`pathRoot`.  `verify` and `rootAfter` are `pathRoot` along `ix k`, whose length
is `depth`: **`depth + 1` hashes per opening check and per incremental update**
(plus one for `hashIndex` when the index is Q2's hashed one).  The opening is
`depth` digests plus the occupant. -/
theorem pathRootM_tick (leafIn : List UInt8) (bits : List Bool) (sibs : List D) (n : Nat)
    (h : sibs.length = bits.length) :
    (S.pathRootM S.tick leafIn bits sibs).run n =
      (S.pathRoot leafIn bits sibs, n + (bits.length + 1)) := by
  have := S.climbM_tick (S.H leafIn) bits sibs (n + 1) h
  show (S.climbM S.tick (S.H leafIn) bits sibs).run (n + 1) = _
  rw [this, pathRoot_eq]
  refine Prod.ext rfl ?_
  show n + 1 + bits.length = n + (bits.length + 1)
  omega

theorem rootAfter_cost [DecidableEq K] (π : Opening K V D) (k : K) (v : Option V)
    (h : π.siblings.length = S.depth) :
    (S.pathRootM S.tick (S.leafInput (slotAfter π.occupant k v)) (S.ix k) π.siblings).run 0 =
      (S.rootAfter π k v, S.depth + 1) := by
  rw [S.pathRootM_tick _ _ _ _ (by rw [S.ix_length]; exact h), S.ix_length]
  simp [rootAfter]

theorem opening_siblings_length (m : Map K V) (k : K) :
    (S.opening m k).siblings.length = S.depth := by
  simp [opening, openAt_length, S.ix_length]

end Scheme

/-! ## Two levels (Q3): cell roots under a world root

A world is a slot map from cell id to cell.  The world root is the `AuthMap`
root over the map from cell id to `cellRoot cell`; `cellRoot` is a parameter, so
Wave C uses the world root without touching the cell-root implementation and
Wave D swaps the cell root for an `AuthMap` root (`two_level_sound`). -/

section TwoLevel

variable {I C V D : Type} [DecidableEq I] [DecidableEq D]
variable (W : Scheme I V D) (cellRoot : C → V)

def worldSlots (w : Map I C) : Map I V := fun p => (w p).map fun e => (e.1, cellRoot e.2)

def worldRoot (w : Map I C) : D := W.root (worldSlots cellRoot w)

omit [DecidableEq D] in
theorem lookup_worldSlots (w : Map I C) (c : I) :
    lookup W.ix (worldSlots cellRoot w) c = (lookup W.ix w c).map cellRoot := by
  unfold lookup worldSlots
  rcases w (W.ix c) with _ | ⟨c', cell⟩
  · rfl
  · by_cases h : c' = c <;> simp [readAt, h]

omit [DecidableEq D] in
theorem worldSlots_write (w : Map I C) (c : I) (v : Option C) :
    worldSlots cellRoot (write W.ix w c v) = write W.ix (worldSlots cellRoot w) c (v.map cellRoot) := by
  funext p
  unfold worldSlots write
  split_ifs
  · cases v with
    | some x => rfl
    | none =>
      simp only [slotAfter, Option.map_none]
      rcases w p with _ | ⟨c', x'⟩
      · rfl
      · by_cases h : c' = c <;> simp [h]
  · rfl

/-- Completeness at the world level: a cell's root opens at the world root. -/
theorem world_opening (w : Map I C) (c : I) :
    W.verify (worldRoot W cellRoot w) c ((lookup W.ix w c).map cellRoot)
      (W.opening (worldSlots cellRoot w) c) = true := by
  rw [← lookup_worldSlots]
  exact W.verify_opening _ c

omit [DecidableEq D] in
/-- A cell write moves the world root along one path of the world tree. -/
theorem worldRoot_write (w : Map I C) (c : I) (cell : Option C) :
    worldRoot W cellRoot (write W.ix w c cell) =
      W.rootAfter (W.opening (worldSlots cellRoot w) c) c (cell.map cellRoot) := by
  unfold worldRoot
  rw [worldSlots_write, W.root_update]

/-- Soundness at the world level: under the world carrier, a verifying opening
of `(c, r)` names a present cell whose root is `r`. -/
theorem world_sound (w : Map I C) (c : I) (r : V) (π : Scheme.Opening I V D)
    (hbind : W.PathBinding (worldSlots cellRoot w) c (some r) π)
    (h : W.verify (worldRoot W cellRoot w) c (some r) π = true) :
    ∃ cell, lookup W.ix w c = some cell ∧ cellRoot cell = r := by
  have := W.verify_sound _ c _ π hbind h
  rw [lookup_worldSlots] at this
  rcases hl : lookup W.ix w c with _ | cell
  · simp [hl] at this
  · exact ⟨cell, rfl, by simpa [hl] using this.symm⟩

/-- **Two-level composition.**  With the cell root itself an `AuthMap` root
(Wave D's cell SMT, scheme `Cs` over addresses `A`), a world opening of `(c, r)`
and a cell opening of `(a, x)` at `r`, each under its own carrier, prove that
cell `c` is present and holds `x` at `a`. -/
theorem two_level_sound {A X E : Type} [DecidableEq A] [DecidableEq E]
    (Cs : Scheme A X E) (W : Scheme I E D)
    (w : Map I (Map A X)) (c : I) (r : E) (πw : Scheme.Opening I E D)
    (a : A) (x : Option X) (πc : Scheme.Opening A X E)
    (hbw : W.PathBinding (worldSlots Cs.root w) c (some r) πw)
    (hw : W.verify (worldRoot W Cs.root w) c (some r) πw = true)
    (hbc : ∀ cell, lookup W.ix w c = some cell → Cs.PathBinding cell a x πc)
    (hc : Cs.verify r a x πc = true) :
    ∃ cell, lookup W.ix w c = some cell ∧ lookup Cs.ix cell a = x := by
  obtain ⟨cell, hl, hr⟩ := world_sound W Cs.root w c r πw hbw hw
  subst hr
  exact ⟨cell, hl, (Cs.verify_sound cell a x πc (hbc cell hl) hc).symm⟩

/-- Two-level completeness: the honest world opening and the honest cell opening
both verify. -/
theorem two_level_complete {A X E : Type} [DecidableEq A] [DecidableEq E]
    (Cs : Scheme A X E) (W : Scheme I E D)
    (w : Map I (Map A X)) (c : I) (cell : Map A X) (hl : lookup W.ix w c = some cell)
    (a : A) :
    W.verify (worldRoot W Cs.root w) c (some (Cs.root cell))
        (W.opening (worldSlots Cs.root w) c) = true ∧
      Cs.verify (Cs.root cell) a (lookup Cs.ix cell a) (Cs.opening cell a) = true := by
  refine ⟨?_, Cs.verify_opening cell a⟩
  have := world_opening W Cs.root w c
  rwa [hl] at this

end TwoLevel

/-! ## Poles -/

/-! ### The refuted pole: an 8-bit length hash

Mirrors `DurableDataIntent.Witness.lengthRoot` (which `Theory/` may not import):
the digest of a byte string is its length.  Keys, values and digests are single
bytes; depth 3, index = the low three bits of the key (so keys 1 and 9 share an
index — the Q2 eviction pole). -/

namespace LengthToy

def ix (k : UInt8) : List Bool :=
  [decide (k.toNat / 4 % 2 = 1), decide (k.toNat / 2 % 2 = 1), decide (k.toNat % 2 = 1)]

theorem single_injective : Function.Injective (fun b : UInt8 => [b]) := by
  intro a b h; simpa using h

def scheme : Scheme UInt8 UInt8 UInt8 where
  H bs := bs.length.toUInt8
  digestBytes d := [d]
  keyBytes k := [k]
  valBytes x := [x]
  digestBytes_prefixFree := prefixFree_of_fixedWidth _ 1 (fun _ => rfl) single_injective
  keyBytes_prefixFree := prefixFree_of_fixedWidth _ 1 (fun _ => rfl) single_injective
  valBytes_injective := single_injective
  depth := 3
  ix := ix
  ix_length _ := rfl

def m : Map UInt8 UInt8 := write ix Map.empty 5 (some 7)

/-- The forged opening: the honest siblings, with the claimed value 8 in place of 7. -/
def forged : Scheme.Opening UInt8 UInt8 UInt8 := scheme.opening m 5

theorem forged_verifies : scheme.verify (scheme.root m) 5 (some 8) forged = true := by
  decide

theorem lookup_m : lookup ix m 5 = some 7 := by decide

/-- The soundness conclusion fails at the length hash. -/
theorem soundness_fails :
    ¬ ∀ (m : Map UInt8 UInt8) (k : UInt8) (v : Option UInt8) (π : Scheme.Opening UInt8 UInt8 UInt8),
      scheme.verify (scheme.root m) k v π = true → v = lookup scheme.ix m k := by
  intro h
  have := h m 5 (some 8) forged forged_verifies
  rw [show scheme.ix = ix from rfl, lookup_m] at this
  cases this

/-- **Refuted pole.**  The carrier is false at this forgery: were it true,
`verify_sound` would prove `8 = 7`. -/
theorem lengthHash_binding_fails : ¬ scheme.PathBinding m 5 (some 8) forged := by
  intro hb
  have := scheme.verify_sound m 5 (some 8) forged hb forged_verifies
  rw [show scheme.ix = ix from rfl, lookup_m] at this
  cases this

/-- …and the unconditional reduction hands over the collision. -/
theorem lengthHash_collision :
    ∃ x y : List UInt8, x ≠ y ∧ scheme.H x = scheme.H y := by
  obtain ⟨_, _, x, y, _, hne, hH⟩ :=
    scheme.forgery_exhibits_collision m 5 (some 8) forged forged_verifies
      (by rw [show scheme.ix = ix from rfl, lookup_m]; decide)
  exact ⟨x, y, hne, hH⟩

/-- **Satisfiable pole at finite width.**  The same 8-bit hash meets the carrier
at the honest opening. -/
theorem lengthHash_binding_honest : scheme.PathBinding m 5 (some 7) (scheme.opening m 5) := by
  have := scheme.honest_binding m 5
  rwa [show scheme.ix = ix from rfl, lookup_m] at this

/-- **Q2 eviction pole.**  Keys 1 and 9 share an index; inserting 9 evicts 1,
which is why `lookup_write_ne` carries its side condition. -/
theorem index_collision_evicts :
    lookup ix (write ix (write ix (Map.empty : Map UInt8 UInt8) 1 (some 7)) 9 (some 8)) 1 = none ∧
      lookup ix (write ix (Map.empty : Map UInt8 UInt8) 1 (some 7)) 1 = some 7 := by
  decide

end LengthToy

/-! ### The satisfied pole: an injective toy hash over a small key space

`H = id` on byte strings — the digest is the tree, the analogue of the tree's
`identitySuite`.  Digests are variable-length, framed by `unaryFrame`.  Keys are
`Fin 4`, depth 2. -/

namespace IdToy

def ix (k : Fin 4) : List Bool := [decide (k.val / 2 % 2 = 1), decide (k.val % 2 = 1)]

def keyByte (k : Fin 4) : List UInt8 := [k.val.toUInt8]

theorem keyByte_injective : Function.Injective keyByte := by
  intro a b h; revert a b; decide

def scheme : Scheme (Fin 4) UInt8 (List UInt8) where
  H := id
  digestBytes := unaryFrame
  keyBytes := keyByte
  valBytes x := [x]
  digestBytes_prefixFree := unaryFrame_prefixFree
  keyBytes_prefixFree := prefixFree_of_fixedWidth _ 1 (fun _ => rfl) keyByte_injective
  valBytes_injective := LengthToy.single_injective
  depth := 2
  ix := ix
  ix_length _ := rfl

theorem binding (m : Map (Fin 4) UInt8) (k : Fin 4) (v : Option UInt8)
    (π : Scheme.Opening (Fin 4) UInt8 (List UInt8)) : scheme.PathBinding m k v π :=
  scheme.binding_of_injective Function.injective_id m k v π

/-- **Satisfied pole.**  At the injective toy hash, every verifying opening —
honest or not — reads the logical value. -/
theorem idHash_sound (m : Map (Fin 4) UInt8) (k : Fin 4) (v : Option UInt8)
    (π : Scheme.Opening (Fin 4) UInt8 (List UInt8))
    (h : scheme.verify (scheme.root m) k v π = true) : v = lookup scheme.ix m k :=
  scheme.verify_sound m k v π (binding m k v π) h

def m : Map (Fin 4) UInt8 := write ix (write ix Map.empty 1 (some 7)) 2 (some 9)

/-- The same forgery that passed at the length hash is refused here. -/
theorem forgery_refused : scheme.verify (scheme.root m) 1 (some 8) (scheme.opening m 1) = false := by
  decide

/-- §4.5's refutable pole: a tampered sibling yields a root that is not the
written map's. -/
theorem tampered_sibling :
    scheme.rootAfter ⟨m (ix 1), [[0], [0]]⟩ 1 (some 8) ≠
      scheme.root (write ix m 1 (some 8)) := by
  decide

/-- A world level over the same toy: cell id `Fin 4`, value = a cell root
(an `IdToy.scheme` root, framed by `unaryFrame`), `H = id`. -/
def worldScheme : Scheme (Fin 4) (List UInt8) (List UInt8) where
  H := id
  digestBytes := unaryFrame
  keyBytes := keyByte
  valBytes := unaryFrame
  digestBytes_prefixFree := unaryFrame_prefixFree
  keyBytes_prefixFree := prefixFree_of_fixedWidth _ 1 (fun _ => rfl) keyByte_injective
  valBytes_injective := unaryFrame_prefixFree.injective
  depth := 2
  ix := ix
  ix_length _ := rfl

/-- **Two-level satisfied pole.**  With both carriers discharged (injective toy
hash at each level), a world opening and a cell opening prove the cell's value
outright: the premises of `two_level_sound` are inhabited. -/
theorem two_level_sound_idToy (w : Map (Fin 4) (Map (Fin 4) UInt8)) (c : Fin 4)
    (r : List UInt8) (πw : Scheme.Opening (Fin 4) (List UInt8) (List UInt8)) (a : Fin 4)
    (x : Option UInt8) (πc : Scheme.Opening (Fin 4) UInt8 (List UInt8))
    (hw : worldScheme.verify (worldRoot worldScheme scheme.root w) c (some r) πw = true)
    (hc : scheme.verify r a x πc = true) :
    ∃ cell, lookup ix w c = some cell ∧ lookup ix cell a = x :=
  two_level_sound scheme worldScheme w c r πw a x πc
    (worldScheme.binding_of_injective Function.injective_id _ _ _ _) hw
    (fun cell _ => binding cell a x πc) hc

end IdToy

/-! ## Axiom audit -/

/-- info: 'Minidregg.Theory.AuthMap.Scheme.verify_opening' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.verify_opening

/-- info: 'Minidregg.Theory.AuthMap.Scheme.root_update' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.root_update

/-- info: 'Minidregg.Theory.AuthMap.Scheme.root_logical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.root_logical

/-- info: 'Minidregg.Theory.AuthMap.Scheme.verify_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.verify_sound

/-- info: 'Minidregg.Theory.AuthMap.Scheme.forgery_exhibits_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.forgery_exhibits_collision

/-- info: 'Minidregg.Theory.AuthMap.Scheme.honest_binding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.honest_binding

/-- info: 'Minidregg.Theory.AuthMap.Scheme.binding_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.binding_of_injective

/-- info: 'Minidregg.Theory.AuthMap.Scheme.pathRootM_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.pathRootM_tick

/-- info: 'Minidregg.Theory.AuthMap.Scheme.rootAfter_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.rootAfter_cost

/-- info: 'Minidregg.Theory.AuthMap.lookup_write_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms lookup_write_self

/-- info: 'Minidregg.Theory.AuthMap.lookup_write_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookup_write_ne

/-- info: 'Minidregg.Theory.AuthMap.hashIndex_collision' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms hashIndex_collision

/-- info: 'Minidregg.Theory.AuthMap.world_opening' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms world_opening

/-- info: 'Minidregg.Theory.AuthMap.worldRoot_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worldRoot_write

/-- info: 'Minidregg.Theory.AuthMap.world_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_sound

/-- info: 'Minidregg.Theory.AuthMap.two_level_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_level_sound

/-- info: 'Minidregg.Theory.AuthMap.two_level_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms two_level_complete

/-- info: 'Minidregg.Theory.AuthMap.LengthToy.forged_verifies' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LengthToy.forged_verifies

/-- info: 'Minidregg.Theory.AuthMap.LengthToy.soundness_fails' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LengthToy.soundness_fails

/-- info: 'Minidregg.Theory.AuthMap.LengthToy.lengthHash_binding_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LengthToy.lengthHash_binding_fails

/-- info: 'Minidregg.Theory.AuthMap.LengthToy.lengthHash_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LengthToy.lengthHash_collision

/-- info: 'Minidregg.Theory.AuthMap.LengthToy.lengthHash_binding_honest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LengthToy.lengthHash_binding_honest

/-- info: 'Minidregg.Theory.AuthMap.LengthToy.index_collision_evicts' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LengthToy.index_collision_evicts

/-- info: 'Minidregg.Theory.AuthMap.IdToy.idHash_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdToy.idHash_sound

/-- info: 'Minidregg.Theory.AuthMap.IdToy.forgery_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdToy.forgery_refused

/-- info: 'Minidregg.Theory.AuthMap.IdToy.tampered_sibling' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdToy.tampered_sibling

/-- info: 'Minidregg.Theory.AuthMap.IdToy.two_level_sound_idToy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdToy.two_level_sound_idToy

end Minidregg.Theory.AuthMap
