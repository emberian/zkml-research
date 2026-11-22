module
/-
# Obend.Consensus.Simplex — Quorum Intersection, Prefix Consistency, and View Backoff Lemmas

Mathlib-free quorum combinatorics and view-timing primitives backing
`Obend.Consensus.SimplexProtocol` and `Obend.Consensus.SimplexTrace`:
- `honest_quorum_intersection`: any two `2f + 1` quorums in a `3f + 1` committee with at most
  `f` faulty members share at least one honest member.
- `honest_quorum_intersection_nf` (with `quorum_overlap_nf`): any two `n - f` quorums in a
  committee of `n ≥ 3f + 1` with at most `f` faulty members overlap in `≥ n - 2f ≥ f + 1` members
  and share an honest one. `SimplexProtocol` uses this threshold.
- `qc_same_view_unique`: two `2f + 1` quorums in the same view whose honest voters vote once
  must agree on the certified value.
- `nodup_filter_simplex`: filtering a duplicate-free committee preserves `Nodup`.
- `prefix_monotonic_of_ancestor` & `prefix_length_le`: chain prefix monotonicity.
- `exponential_backoff_timing` & `exponential_backoff_base`: bounded view timeout backoff.

The Simplex protocol state relation, invariant `Inv`, finalization certificates (`FinCert`),
and vote-carrying accountable slashing receipts (`SlashingReceipt.checks`) live in
`Obend.Consensus.SimplexProtocol`.
-/

public section

namespace Obend.Consensus.Simplex

set_option autoImplicit false

/-! ## 1. Identifiers, Configuration & View Backoff -/

abbrev NodeId := Nat
abbrev Round := Nat
abbrev View := Nat

structure Config where
  parties : Nat
  faults : Nat
  timeout : Nat
  pumpBudget : Nat := 64
  backoffCap : Nat := 0
  deriving Repr, Inhabited

deriving instance @[expose] DecidableEq, BEq for Config

@[expose] def Config.wellFormed (c : Config) : Bool :=
  c.parties == 3 * c.faults + 1 && c.timeout > 0 && c.pumpBudget > 0

@[expose] def Config.quorum (c : Config) : Nat := 2 * c.faults + 1

@[expose] def Config.leader (c : Config) (view : View) : NodeId :=
  (view - 1) % c.parties

/-- Exponential view timeout: doubles with each view entered without commit, capped by `backoffCap`. -/
@[expose] def viewTimeout (baseTimeout : Nat) (viewsSinceCommit : Nat) (backoffCap : Nat) : Nat :=
  baseTimeout * (2 ^ (min viewsSinceCommit backoffCap))

/-! ## 2. Quorum Intersection & Safety Combinatorics -/

/-- Cardinality identity for list filter sums. -/
theorem list_filter_add_card {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter q).length =
    (l.filter (fun x => p x || q x)).length + (l.filter (fun x => p x && q x)).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

theorem list_filter_length_le {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases p x <;> simp <;> omega

theorem list_filter_sub {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x && !q x)).length + (l.filter (fun x => p x && q x)).length =
    (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

theorem list_filter_and_le {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x && q x)).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

/-- Filtering a `Nodup` list preserves `Nodup`. -/
theorem nodup_filter_simplex {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    cases h with
    | cons h_not_mem h_xs =>
      simp only [List.filter_cons]
      cases p x with
      | false => exact nodup_filter_simplex p h_xs
      | true =>
        exact List.Pairwise.cons
          (fun y hy => h_not_mem y (List.mem_filter.mp hy).1)
          (nodup_filter_simplex p h_xs)

/-- Two `n - f` quorums of an `n`-element list overlap in at least `n - 2f` positions: by
inclusion–exclusion, `|p| + |q| = |p ∨ q| + |p ∧ q|` and `|p ∨ q| ≤ n`. No `Nodup` is needed, since
every count is over the same list. -/
theorem quorum_overlap_nf {α : Type} (l : List α) (f : Nat) (p q : α → Bool)
    (h_p : l.length - f ≤ (l.filter p).length)
    (h_q : l.length - f ≤ (l.filter q).length) :
    l.length - 2 * f ≤ (l.filter (fun x => p x && q x)).length := by
  have h_sum := list_filter_add_card p q l
  have h_union := list_filter_length_le (fun x => p x || q x) l
  omega

/-- **Metatheorem 1′: Quorum Intersection at `n - f`** (gate G5, 2026-11-21).
    In a committee of `n ≥ 3f + 1` with at most `f` faulty members, any two quorums of size
    `≥ n - f` overlap in `≥ n - 2f ≥ f + 1` members (`quorum_overlap_nf`), so they share an honest
    one. At `n = 3f + 1` the threshold `n - f` is `2f + 1` and this is `honest_quorum_intersection`;
    for `n > 3f + 1` a fixed `2f + 1` threshold no longer intersects honestly (`n = 5, f = 1`). -/
theorem honest_quorum_intersection_nf {α : Type} (l : List α) (f : Nat)
    (p q faulty : α → Bool)
    (h_size : 3 * f + 1 ≤ l.length)
    (h_p : l.length - f ≤ (l.filter p).length)
    (h_q : l.length - f ≤ (l.filter q).length)
    (h_faulty : (l.filter faulty).length ≤ f) :
    ∃ x ∈ l, p x = true ∧ q x = true ∧ faulty x = false := by
  have h_overlap := quorum_overlap_nf l f p q h_p h_q
  have h_sub := list_filter_sub (fun x => p x && q x) faulty l
  have h_le := list_filter_and_le (fun x => p x && q x) faulty l
  have h_honest_pos : 0 < (l.filter (fun x => (p x && q x) && !faulty x)).length := by
    omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h_honest_pos
  have ⟨h_in_l, h_cond⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h_cond
  exact ⟨x, h_in_l, h_cond.1.1, h_cond.1.2, h_cond.2⟩

/-- **Metatheorem 1: Quorum Intersection**.
    Any two quorums of size `≥ 2f + 1` in a `3f + 1` committee share an honest validator: the
    `n = 3f + 1` instance of `honest_quorum_intersection_nf`, where `n - f = 2f + 1`. -/
theorem honest_quorum_intersection {α : Type} (l : List α) (f : Nat)
    (p q faulty : α → Bool)
    (h_size : l.length = 3 * f + 1)
    (h_p : 2 * f + 1 ≤ (l.filter p).length)
    (h_q : 2 * f + 1 ≤ (l.filter q).length)
    (h_faulty : (l.filter faulty).length ≤ f) :
    ∃ x ∈ l, p x = true ∧ q x = true ∧ faulty x = false :=
  honest_quorum_intersection_nf l f p q faulty (by omega) (by omega) (by omega) h_faulty

/-- **Metatheorem 2: Same-View QC Uniqueness**.
    Two QCs formed for the same view must agree on their value. -/
theorem qc_same_view_unique {α : Type} {val1 val2 : α} (f : Nat) (committee : List Nat)
    (p1 p2 faulty : Nat → Bool)
    (h_size : committee.length = 3 * f + 1)
    (h_p1 : 2 * f + 1 ≤ (committee.filter p1).length)
    (h_p2 : 2 * f + 1 ≤ (committee.filter p2).length)
    (h_faulty : (committee.filter faulty).length ≤ f)
    (vote : Nat → Option α)
    (h_v1 : ∀ s ∈ committee, p1 s = true → faulty s = false → vote s = some val1)
    (h_v2 : ∀ s ∈ committee, p2 s = true → faulty s = false → vote s = some val2) :
    val1 = val2 := by
  have ⟨h, h_mem, hp1, hp2, h_not_faulty⟩ :=
    honest_quorum_intersection committee f p1 p2 faulty h_size h_p1 h_p2 h_faulty
  have v1_eq := h_v1 h h_mem hp1 h_not_faulty
  have v2_eq := h_v2 h h_mem hp2 h_not_faulty
  rw [v1_eq] at v2_eq
  exact Option.some.inj v2_eq

/-- **Metatheorem 3: Monotonicity of Committed Heights & Prefix Consistency**. -/
theorem prefix_monotonic_of_ancestor {α : Type} (chain : List α) (parent : List α) (payload : α)
    (h_chain : chain = parent ++ [payload]) :
    parent.IsPrefix chain := by
  rw [h_chain]
  exact List.prefix_append parent [payload]

theorem prefix_length_le {α : Type} {a b : List α} (h : a.IsPrefix b) :
    a.length ≤ b.length := by
  obtain ⟨s, rfl⟩ := h
  simp only [List.length_append]
  omega

/-- **Metatheorem 4: Exponential View Backoff Bound**. -/
theorem exponential_backoff_timing (baseTimeout : Nat) (views : Nat) (cap : Nat) :
    viewTimeout baseTimeout views cap ≤ baseTimeout * 2 ^ cap := by
  dsimp [viewTimeout]
  have h_min : min views cap ≤ cap := Nat.min_le_right ..
  have h_pow : 2 ^ (min views cap) ≤ 2 ^ cap := Nat.pow_le_pow_right (by decide) h_min
  exact Nat.mul_le_mul_left baseTimeout h_pow

theorem exponential_backoff_base (baseTimeout : Nat) (cap : Nat) :
    viewTimeout baseTimeout 0 cap = baseTimeout := by
  dsimp [viewTimeout]
  have h_min : min 0 cap = 0 := Nat.min_eq_left (Nat.zero_le cap)
  rw [h_min]
  simp

end Obend.Consensus.Simplex
end
