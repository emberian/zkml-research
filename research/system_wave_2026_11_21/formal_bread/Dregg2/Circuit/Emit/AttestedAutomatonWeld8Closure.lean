/-
# Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure — Chip-Generic 8-Lane Root Uniqueness,
Completion-Lane Pinning, and the `DescriptorIR2` `.mapOp → holdsAt8` Equivalence Bridge (`P9`).

Closes `CERTIFICATES.md` §0.3 & §5 P9 WITHOUT touching the shared `DescriptorIR2.lean` (43 legacy
consumer files stay intact):

1. **Chip-generic 8-lane root & completion-lane pinning (for ANY `S8 : Heap8Scheme`, not just
   `constChip`):**
   * `weld8_canonical_root_pins_all_8_lanes` — for a fixed heap `m`, `CommitsAutomaton8By S8 m R8₁ d`
     and `CommitsAutomaton8By S8 m R8₂ d` force `R8₁ = R8₂` on ALL 8 lanes `Fin 8`.
   * `weld8_completion_lanes_unique_at_canonical_heap` — for ANY `S8 : Heap8Scheme`, changing ANY
     of lanes `1..7` away from `autoRoot8 S8 d` either violates `Satisfied2Lanes8 S8` on a
     non-empty canonical run OR forces a distinct `2^16`-leaf sorted heap `mRow ≠ autoHeapW d`
     whose 8-felt root is `mapRoot8 S8 MAP_TREE_DEPTH mRow = R8_forged ≠ autoRoot8 S8 d`.
   * `weld8_two_runs_same_pubRoot_collides` — for ANY `S8 : Heap8Scheme`, if two Lanes8-accepted
     canonical runs publish the same 8-felt `pubRoot` while disagreeing on the output state of a
     traversed `(s, y)`, their row heaps exhibit a concrete `MapRootColl S8 MAP_TREE_DEPTH`
     collision (floor-free, no `Compress8CR`).
   * `weld8_completion_lanes_not_free_of_unattained_lane` — chip-generic falsifier: for ANY
     `S8 : Heap8Scheme` with any unattained value `v` on any completion lane `l ≠ 0`,
     `Satisfied2Lanes8 S8` refutes `weld_completion_lanes_free`.
2. **Explicit `DescriptorIR2` `.mapOp → holdsAt8` repointing bridge:**
   * `Satisfied2Repointed` — defined arm-for-arm identically to `DescriptorIR2.Satisfied2Public`,
     with ONLY `.mapOp` repointed from `MapOp.holdsAt` / `mapLog` to `MapOp.holdsAt8` / `mapLog8`.
   * `satisfied2_repointed_iff_lanes8` — `Satisfied2Repointed ↔ Satisfied2Lanes8` for EVERY
     `S8 : Heap8Scheme` and EVERY `EffectVmDescriptor2`.
   * `satisfied2_repointed_witness` — unconditional non-vacuity witness for every `S8`.
   * `satisfied2_repointed_refutes_completion_lanes_free` — proves that repointing
     `DescriptorIR2.MapOp.holdsAt` / `mapLog` to `holdsAt8` / `mapLog8` flips
     `AttestedAutomatonWeld8.weld_completion_lanes_free` from provable to refutable.

Pure. Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `#guard`.
-/
import Dregg2.Circuit.Emit.AttestedAutomatonLanes8
import Dregg2.Circuit.Emit.AttestedAutomatonBound

namespace Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv siteHoldsAll)
open Dregg2.Crypto
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Substrate
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.MapMerkleRoot
  (mapRoot8 opensToMerkle8 MapRootColl opensToMerkle8_functional_or_collides)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (CURRENT SYMBOL NEXT envAt_loc)
open Dregg2.Circuit.Emit.AttestedAutomatonEmit (ASYM ASTATES keyOf)
open Dregg2.Circuit.Emit.AttestedAutomatonWeld8
open Dregg2.Circuit.Emit.AttestedAutomatonLanes8

set_option autoImplicit false

/-! ## §1. Chip-Generic 8-Lane Root & Completion-Lane Pinning (Arbitrary `S8 : Heap8Scheme`) -/

/-- **`weld8_canonical_root_pins_all_8_lanes`**: for ANY `S8 : Heap8Scheme` and fixed heap `m`,
the 8-felt commitment root is uniquely determined on ALL 8 lanes `Fin 8`. -/
theorem weld8_canonical_root_pins_all_8_lanes (S8 : Heap8Scheme) (m : Heap.FeltHeap)
    (R8₁ R8₂ : Digest8) (d : TableDfa Nat Nat)
    (h₁ : CommitsAutomaton8By S8 m R8₁ d) (h₂ : CommitsAutomaton8By S8 m R8₂ d) :
    R8₁ = R8₂ ∧ ∀ l : Fin 8, R8₁ l = R8₂ l := by
  have heq : R8₁ = R8₂ := h₁.2.2.1.symm.trans h₂.2.2.1
  exact ⟨heq, fun l => congrFun heq l⟩

/-- **`weld8_completion_lanes_unique_at_canonical_heap`**: for ANY `S8 : Heap8Scheme`, ANY
automaton `d`, and ANY forged digest `R8_forged` differing from `autoRoot8 S8 d` on at least one
completion lane `l ≠ 0`, every non-empty canonical run `t` publishing `pubRoot t = R8_forged`
EITHER fails `Satisfied2Lanes8 S8`, OR supplies a concrete sorted `2^16`-leaf heap `mRow` whose
8-felt root is `mapRoot8 S8 MAP_TREE_DEPTH mRow = R8_forged ≠ autoRoot8 S8 d` (so
`mRow ≠ autoHeapW d`) and which opens row 0's edge. -/
theorem weld8_completion_lanes_unique_at_canonical_heap (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (d : TableDfa Nat Nat) (R8_forged : Digest8)
    (hchange : ∃ l : Fin 8, l ≠ 0 ∧ R8_forged l ≠ autoRoot8 S8 d l)
    (t : VmTrace) (hne : t.rows ≠ []) (hcan : LaneCanonical t) (hpub : pubRoot t = R8_forged) :
    ¬ Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t ∨
      ∃ mRow : Heap.FeltHeap,
        Heap.SortedKeys mRow ∧
        mRow.length = 2 ^ MAP_TREE_DEPTH ∧
        mapRoot8 S8 MAP_TREE_DEPTH mRow = R8_forged ∧
        mapRoot8 S8 MAP_TREE_DEPTH mRow ≠ autoRoot8 S8 d ∧
        mRow ≠ autoHeapW d ∧
        Heap.get mRow (2 * (envAt t 0).loc CURRENT + (envAt t 0).loc SYMBOL)
          = some ((envAt t 0).loc NEXT) := by
  by_cases hsat : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t
  · right
    have h0 : 0 < t.rows.length := List.length_pos_of_ne_nil hne
    have hopen := lanes8_row_opens_public S8 hash name minit mfin maddrs t hsat hcan 0 h0
    rw [hpub] at hopen
    obtain ⟨mRow, hsort, hlen, hroot, hget⟩ := hopen
    have hne_root : R8_forged ≠ autoRoot8 S8 d := by
      intro heq
      obtain ⟨l, _, hdiff⟩ := hchange
      exact hdiff (congrFun heq l)
    have hne_mroot : mapRoot8 S8 MAP_TREE_DEPTH mRow ≠ autoRoot8 S8 d := by
      rw [hroot]
      exact hne_root
    have hne_heap : mRow ≠ autoHeapW d := by
      intro heq
      apply hne_mroot
      rw [heq]
      exact (autoRoot8_commits S8 d).2.2.1
    exact ⟨mRow, hsort, hlen, hroot, hne_mroot, hne_heap, hget⟩
  · exact Or.inl hsat

/-- **`weld8_two_runs_same_pubRoot_collides`**: for ANY `S8 : Heap8Scheme`, if two Lanes8-accepted
canonical runs `t₁, t₂` claim the SAME 8-felt public root `pubRoot t₁ = pubRoot t₂` while
traversing the same `(s, y)` pair to DIFFERENT next states `n₁ ≠ n₂`, their opening heaps exhibit
a concrete `MapRootColl S8 MAP_TREE_DEPTH` collision (floor-free, no `Compress8CR`). -/
theorem weld8_two_runs_same_pubRoot_collides (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (name₁ name₂ : String)
    (minit₁ minit₂ : ℤ → ℤ) (mfin₁ mfin₂ : ℤ → ℤ × Nat) (maddrs₁ maddrs₂ : List ℤ)
    (t₁ t₂ : VmTrace)
    (h₁ : Satisfied2Lanes8 S8 hash (weldDesc name₁) minit₁ mfin₁ maddrs₁ t₁)
    (h₂ : Satisfied2Lanes8 S8 hash (weldDesc name₂) minit₂ mfin₂ maddrs₂ t₂)
    (hcan₁ : LaneCanonical t₁) (hcan₂ : LaneCanonical t₂)
    (hsame : pubRoot t₁ = pubRoot t₂)
    (i₁ : Nat) (hi₁ : i₁ < t₁.rows.length) (i₂ : Nat) (hi₂ : i₂ < t₂.rows.length)
    (s y : Nat)
    (hcur₁ : (envAt t₁ i₁).loc CURRENT = Int.ofNat s)
    (hsym₁ : (envAt t₁ i₁).loc SYMBOL = Int.ofNat y)
    (hcur₂ : (envAt t₂ i₂).loc CURRENT = Int.ofNat s)
    (hsym₂ : (envAt t₂ i₂).loc SYMBOL = Int.ofNat y)
    (hdiff : (envAt t₁ i₁).loc NEXT ≠ (envAt t₂ i₂).loc NEXT) :
    ∃ mRow₁ mRow₂ : Heap.FeltHeap,
      Heap.SortedKeys mRow₁ ∧ mRow₁.length = 2 ^ MAP_TREE_DEPTH ∧
      mapRoot8 S8 MAP_TREE_DEPTH mRow₁ = pubRoot t₁ ∧
      Heap.get mRow₁ ((keyOf s y : Nat) : ℤ) = some ((envAt t₁ i₁).loc NEXT) ∧
      Heap.SortedKeys mRow₂ ∧ mRow₂.length = 2 ^ MAP_TREE_DEPTH ∧
      mapRoot8 S8 MAP_TREE_DEPTH mRow₂ = pubRoot t₁ ∧
      Heap.get mRow₂ ((keyOf s y : Nat) : ℤ) = some ((envAt t₂ i₂).loc NEXT) ∧
      MapRootColl S8 MAP_TREE_DEPTH mRow₁ mRow₂ := by
  have hkey : (2 : ℤ) * Int.ofNat s + Int.ofNat y = ((keyOf s y : Nat) : ℤ) := by
    simp only [keyOf, Int.ofNat_eq_natCast]
    push_cast
    ring
  have hopen₁ := lanes8_row_opens_public S8 hash name₁ minit₁ mfin₁ maddrs₁ t₁ h₁ hcan₁ i₁ hi₁
  rw [hcur₁, hsym₁, hkey] at hopen₁
  obtain ⟨mRow₁, hsort₁, hlen₁, hroot₁, hget₁⟩ := hopen₁
  have hopen₂ := lanes8_row_opens_public S8 hash name₂ minit₂ mfin₂ maddrs₂ t₂ h₂ hcan₂ i₂ hi₂
  rw [hcur₂, hsym₂, hkey, ← hsame] at hopen₂
  obtain ⟨mRow₂, hsort₂, hlen₂, hroot₂, hget₂⟩ := hopen₂
  refine ⟨mRow₁, mRow₂, hsort₁, hlen₁, hroot₁, hget₁, hsort₂, hlen₂, hroot₂, hget₂, ?_⟩
  rcases opensToMerkle8_functional_or_collides S8 MAP_TREE_DEPTH hlen₁ hroot₁ hget₁
      hlen₂ hroot₂ hget₂ with heq | hc
  · exfalso
    exact hdiff (Option.some.inj heq)
  · exact hc

/-- **Chip-generic completion-lane non-freedom (`weld8_completion_lanes_not_free_of_unattained_lane`)**:
for ANY `S8 : Heap8Scheme` that has at least one unattained value `v` on some completion lane
`l₀ ≠ 0` (e.g. any BabyBear-range chip where `v = -1` or `2013265921` is unattained, or `constChip`
with `v = 1`), `Satisfied2Lanes8 S8` refutes arbitrary completion-lane freedom. -/
theorem weld8_completion_lanes_not_free_of_unattained_lane (S8 : Heap8Scheme)
    (l₀ : Fin 8) (hl₀ : l₀ ≠ 0) (v : ℤ)
    (hunattained : ∀ m : Heap.FeltHeap, m.length = 2 ^ MAP_TREE_DEPTH →
      mapRoot8 S8 MAP_TREE_DEPTH m l₀ ≠ v)
    (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (r0 : ℤ)
    (q : Nat) (w : List Nat) (hw : w ≠ []) (name : String) :
    ¬ ∀ hi : Fin 8 → ℤ,
      Satisfied2Lanes8 S8 hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit8 d (fun l => if l = 0 then r0 else hi l) q w) := by
  intro hall
  let R8 : Digest8 := fun l => if l = 0 then r0 else v
  have hsat := hall (fun _ => v)
  have h0 : 0 < (weldWit8 d R8 q w).rows.length := by
    show 0 < (rowsW d R8 q w).length
    rw [rowsW_length]
    exact List.length_pos_of_ne_nil hw
  obtain ⟨mRow, _, hlen, hroot, _⟩ :=
    lanes8_row_opens S8 hash name (fun _ => 0) (fun _ => (0, 0)) [] (weldWit8 d R8 q w) hsat 0 h0
  have hrow_l : rowRoot (weldWit8 d R8 q w) 0 l₀ = v := by
    show (envAt (weldWit8 d R8 q w) 0).loc (W8ROOT l₀) = v
    rw [envAt_weldWit8, envAt_loc (t := weldWit d R8 q w) h0]
    show ((rowsW d R8 q w)[0]'h0) (W8ROOT l₀) = v
    rw [rowsW_root d R8 l₀ w q 0 h0]
    simp [R8, hl₀]
  have hlane := congrFun hroot l₀
  rw [hrow_l] at hlane
  exact hunattained mRow hlen hlane

/-! ## §2. Explicit `DescriptorIR2` `.mapOp → holdsAt8` Repointing Bridge -/

/-- Per-row meaning of `VmConstraint2` written out arm-for-arm identically to
`DescriptorIR2.VmConstraint2.holdsAt`, with ONLY `.mapOp` repointed from `MapOp.holdsAt`
(lane 0) to `MapOp.holdsAt8` (all 8 lanes). -/
def VmConstraint2.holdsAtRepointed (S8 : Heap8Scheme) (_hash : List ℤ → ℤ) (tf : TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint2 → Prop
  | .base c       => c.holdsVm env isFirst isLast
  | .lookup l     => l.holdsAt tf env
  | .memOp _      => True
  | .mapOp m      => m.holdsAt8 S8 env
  | .umemOp _     => True
  | .proofBind m  => m.holdsAt env
  | .windowGate w => w.holdsAt env isLast
  | .chalGate w   => w.holdsAt env isLast

/-- Arm-by-arm identity between `holdsAtRepointed` and `VmConstraint2.holdsAt8`. -/
theorem vmConstraint2_holdsAtRepointed_iff_holdsAt8 (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint2) :
    VmConstraint2.holdsAtRepointed S8 hash tf env isFirst isLast c ↔
      c.holdsAt8 S8 hash tf env isFirst isLast := by
  cases c <;> rfl

/-- Base `DescriptorIR2.Satisfied2` with `.mapOp` repointed to `MapOp.holdsAt8` and `mapLog`
repointed to `mapLog8` (19-felt rows). -/
structure Satisfied2RepointedBase (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop where
  rowConstraints : ∀ i < t.rows.length, ∀ c ∈ d.constraints,
    VmConstraint2.holdsAtRepointed S8 hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) c
  rowHashes : ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) d.hashSites
  rowRanges : ∀ i < t.rows.length, ∀ r ∈ d.ranges, r.holds (envAt t i)
  memAddrsNodup : maddrs.Nodup
  memClosed : ∀ op ∈ memLog d t, op.addr ∈ maddrs
  memDisciplined : MemoryChecking.Disciplined (memLog d t)
  memBalanced : MemoryChecking.MemCheck minit mfin maddrs (memLog d t)
  memTableFaithful : t.tf .memory = (memLog d t).map opRow
  mapTableFaithful : t.tf .mapOps = mapLog8 d t

/-- **`Satisfied2Repointed`**: identical in structure to `DescriptorIR2.Satisfied2Public`
(`extends Satisfied2RepointedBase` + `publicTablesFaithful` + `publicLookupBalanced`), with ONLY
the `.mapOp` arm repointed to `MapOp.holdsAt8` and `mapTableFaithful` repointed to `mapLog8`. -/
structure Satisfied2Repointed (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop
    extends Satisfied2RepointedBase S8 hash d minit mfin maddrs t where
  publicTablesFaithful : PublicTablesFaithful d t
  publicLookupBalanced : PublicLookupBalanced d t

/-- **`satisfied2_repointed_iff_lanes8`**: for EVERY `S8 : Heap8Scheme` and EVERY v2 descriptor `d`,
repointing `DescriptorIR2.Satisfied2Public`'s `.mapOp` leg (`MapOp.holdsAt`/`mapLog` →
`MapOp.holdsAt8`/`mapLog8`) is LOGICALLY EQUIVALENT to `AttestedAutomatonLanes8.Satisfied2Lanes8`. -/
theorem satisfied2_repointed_iff_lanes8 (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    Satisfied2Repointed S8 hash d minit mfin maddrs t ↔
      Satisfied2Lanes8 S8 hash d minit mfin maddrs t := by
  constructor
  · intro h
    refine
      { rowConstraints := fun i hi c hc =>
          (vmConstraint2_holdsAtRepointed_iff_holdsAt8 S8 hash t.tf (envAt t i)
            (i == 0) (i + 1 == t.rows.length) c).mp (h.rowConstraints i hi c hc)
      , rowHashes := h.rowHashes
      , rowRanges := h.rowRanges
      , memAddrsNodup := h.memAddrsNodup
      , memClosed := h.memClosed
      , memDisciplined := h.memDisciplined
      , memBalanced := h.memBalanced
      , memTableFaithful := h.memTableFaithful
      , mapTableFaithful8 := h.mapTableFaithful
      , publicTablesFaithful := h.publicTablesFaithful
      , publicLookupBalanced := h.publicLookupBalanced }
  · intro h
    refine
      { rowConstraints := fun i hi c hc =>
          (vmConstraint2_holdsAtRepointed_iff_holdsAt8 S8 hash t.tf (envAt t i)
            (i == 0) (i + 1 == t.rows.length) c).mpr (h.rowConstraints i hi c hc)
      , rowHashes := h.rowHashes
      , rowRanges := h.rowRanges
      , memAddrsNodup := h.memAddrsNodup
      , memClosed := h.memClosed
      , memDisciplined := h.memDisciplined
      , memBalanced := h.memBalanced
      , memTableFaithful := h.memTableFaithful
      , mapTableFaithful := h.mapTableFaithful8
      , publicTablesFaithful := h.publicTablesFaithful
      , publicLookupBalanced := h.publicLookupBalanced }

/-- **Non-vacuity witness for `Satisfied2Repointed`**: unconditionally inhabited for EVERY
`S8 : Heap8Scheme`, automaton `d`, and non-empty in-domain run `w`. -/
theorem satisfied2_repointed_witness (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (d : TableDfa Nat Nat) (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Repointed S8 hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
      (weldWit8 d (autoRoot8 S8 d) q w) :=
  (satisfied2_repointed_iff_lanes8 S8 hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
    (weldWit8 d (autoRoot8 S8 d) q w)).mpr
    (weldWit8_satisfies_constructed S8 hash d hstep q hq w hw hsym name)

/-- **`satisfied2_repointed_refutes_completion_lanes_free`**: under `Satisfied2Repointed`
(`DescriptorIR2.Satisfied2Public` with `.mapOp` repointed to `holdsAt8`/`mapLog8`),
`AttestedAutomatonWeld8.weld_completion_lanes_free` FLIPS from provable to REFUTED — both at
`constChip` and for any `S8 : Heap8Scheme` with an unattained completion-lane value. -/
theorem satisfied2_repointed_refutes_completion_lanes_free (hash : List ℤ → ℤ)
    (d : TableDfa Nat Nat) (r0 : ℤ) (q : Nat) (w : List Nat) (hw : w ≠ []) (name : String) :
    ¬ ∀ hi : Fin 8 → ℤ,
      Satisfied2Repointed constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit8 d (fun l => if l = 0 then r0 else hi l) q w) := by
  intro hall
  exact weld_completion_lanes_not_free hash d r0 q w hw name (fun hi =>
    (satisfied2_repointed_iff_lanes8 constChip hash (weldDesc name)
      (fun _ => 0) (fun _ => (0, 0)) [] _).mp (hall hi))

/-- Chip-generic transfer of `weld8_completion_lanes_not_free_of_unattained_lane` to
`Satisfied2Repointed`. -/
theorem satisfied2_repointed_refutes_free_of_unattained_lane (S8 : Heap8Scheme)
    (l₀ : Fin 8) (hl₀ : l₀ ≠ 0) (v : ℤ)
    (hunattained : ∀ m : Heap.FeltHeap, m.length = 2 ^ MAP_TREE_DEPTH →
      mapRoot8 S8 MAP_TREE_DEPTH m l₀ ≠ v)
    (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (r0 : ℤ)
    (q : Nat) (w : List Nat) (hw : w ≠ []) (name : String) :
    ¬ ∀ hi : Fin 8 → ℤ,
      Satisfied2Repointed S8 hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit8 d (fun l => if l = 0 then r0 else hi l) q w) := by
  intro hall
  exact weld8_completion_lanes_not_free_of_unattained_lane S8 l₀ hl₀ v hunattained
    hash d r0 q w hw name (fun hi =>
      (satisfied2_repointed_iff_lanes8 S8 hash (weldDesc name)
        (fun _ => 0) (fun _ => (0, 0)) [] _).mp (hall hi))

/-! ## §3. Axiom Hygiene (`#assert_all_clean` + `#guard_msgs in #print axioms`) -/

#assert_all_clean [
  weld8_canonical_root_pins_all_8_lanes,
  weld8_completion_lanes_unique_at_canonical_heap,
  weld8_two_runs_same_pubRoot_collides,
  weld8_completion_lanes_not_free_of_unattained_lane,
  vmConstraint2_holdsAtRepointed_iff_holdsAt8,
  satisfied2_repointed_iff_lanes8,
  satisfied2_repointed_witness,
  satisfied2_repointed_refutes_completion_lanes_free,
  satisfied2_repointed_refutes_free_of_unattained_lane
]

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.weld8_canonical_root_pins_all_8_lanes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms weld8_canonical_root_pins_all_8_lanes
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.weld8_completion_lanes_unique_at_canonical_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weld8_completion_lanes_unique_at_canonical_heap
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.weld8_two_runs_same_pubRoot_collides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weld8_two_runs_same_pubRoot_collides
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.weld8_completion_lanes_not_free_of_unattained_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weld8_completion_lanes_not_free_of_unattained_lane
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.satisfied2_repointed_iff_lanes8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms satisfied2_repointed_iff_lanes8
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.satisfied2_repointed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms satisfied2_repointed_witness
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.satisfied2_repointed_refutes_completion_lanes_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms satisfied2_repointed_refutes_completion_lanes_free
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure.satisfied2_repointed_refutes_free_of_unattained_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms satisfied2_repointed_refutes_free_of_unattained_lane

end Dregg2.Circuit.Emit.AttestedAutomatonWeld8Closure
