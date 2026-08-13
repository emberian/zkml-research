/-
# Selvage.SpongeIndiffOracleReordering — extensional lazy-sampling commutation

Construction-first prefix programming samples RO entries earlier than the
landed ideal simulator, which waits until a prefix is publicly revealed.  The
two handlers need not have definitionally equal logs: distinct responses are
appended in different orders.  What the games observe is lookup behavior.

This module proves the exact extensional algebra needed for the coupling.
Lookup-equivalent handlers return the same answer to the same response step
and remain lookup-equivalent.  In particular, responses to distinct queries
commute extensionally, and each response is unchanged by moving the other
distinct response before it.

No probability assertion appears here.  The later game equivalence must lift
this deterministic coin-reordering law to a bijection of the fixed uniform
work sample space.
-/
import Selvage.SpongeIndiffWorkStream

namespace Minidregg.Selvage

namespace Oracle

section Reordering

variable {Q C : Type}

open Classical

/-- Two finite lazy handlers denote the same partial response function.  Their
log order and proof fields may differ. -/
def LookupEquivalent (left right : Oracle Q C) : Prop :=
  ∀ query, left.lookup query = right.lookup query

theorem LookupEquivalent.refl (oracle : Oracle Q C) :
    LookupEquivalent oracle oracle := fun _ => rfl

theorem LookupEquivalent.symm {left right : Oracle Q C}
    (h : LookupEquivalent left right) : LookupEquivalent right left :=
  fun query => (h query).symm

theorem LookupEquivalent.trans {left middle right : Oracle Q C}
    (hlm : LookupEquivalent left middle)
    (hmr : LookupEquivalent middle right) : LookupEquivalent left right :=
  fun query => (hlm query).trans (hmr query)

/-- A response answer is determined only by the current lookup result. -/
theorem respond_fst_eq_of_lookup_eq (left right : Oracle Q C) (query : Q)
    (coin : C) (hlookup : left.lookup query = right.lookup query) :
    (left.respond query coin).1 = (right.respond query coin).1 := by
  cases hleft : left.lookup query with
  | some value =>
      have hright : right.lookup query = some value := hlookup ▸ hleft
      rw [respond_hit hleft, respond_hit hright]
  | none =>
      have hright : right.lookup query = none := hlookup ▸ hleft
      rw [respond_fresh_fst hleft, respond_fresh_fst hright]

/-- A response changes the queried lookup to its returned value and frames all
other queries. -/
theorem lookup_respond (oracle : Oracle Q C) (query other : Q) (coin : C) :
    (oracle.respond query coin).2.lookup other =
      if other = query then some (oracle.respond query coin).1
      else oracle.lookup other := by
  classical
  by_cases heq : other = query
  · subst other
    rw [if_pos rfl, lookup_respond_self]
  · rw [if_neg heq, lookup_respond_ne oracle heq]

/-- Responding with the same query and coin preserves lookup equivalence. -/
theorem LookupEquivalent.respond {left right : Oracle Q C}
    (h : LookupEquivalent left right) (query : Q) (coin : C) :
    LookupEquivalent (left.respond query coin).2
      (right.respond query coin).2 := by
  intro other
  classical
  by_cases heq : other = query
  · rw [lookup_respond, lookup_respond, if_pos heq, if_pos heq]
    exact congrArg some
      (respond_fst_eq_of_lookup_eq left right query coin (h query))
  · rw [lookup_respond, lookup_respond, if_neg heq, if_neg heq]
    exact h other

/-- Moving a distinct response earlier does not change this query's returned
answer. -/
theorem respond_distinct_fst (oracle : Oracle Q C) {first second : Q}
    (hne : second ≠ first) (firstCoin secondCoin : C) :
    (((oracle.respond first firstCoin).2.respond second secondCoin).1) =
      (oracle.respond second secondCoin).1 := by
  apply respond_fst_eq_of_lookup_eq
  exact lookup_respond_ne oracle hne firstCoin

/-- Two responses at distinct queries commute as partial functions, even
though their append-ordered log records are generally not equal. -/
theorem respond_distinct_commute (oracle : Oracle Q C) {first second : Q}
    (hne : first ≠ second) (firstCoin secondCoin : C) :
    LookupEquivalent
      ((oracle.respond first firstCoin).2.respond second secondCoin).2
      ((oracle.respond second secondCoin).2.respond first firstCoin).2 := by
  intro other
  classical
  by_cases hsecond : other = second
  · subst other
    rw [lookup_respond_self,
      lookup_respond_ne _ (Ne.symm hne), lookup_respond_self]
    exact congrArg some
      (respond_distinct_fst oracle (Ne.symm hne) firstCoin secondCoin)
  · by_cases hfirst : other = first
    · subst other
      rw [lookup_respond_ne _ hne, lookup_respond_self,
        lookup_respond_self]
      exact congrArg some
        (respond_distinct_fst oracle hne secondCoin firstCoin).symm
    · rw [lookup_respond_ne _ hsecond, lookup_respond_ne _ hfirst,
        lookup_respond_ne _ hfirst, lookup_respond_ne _ hsecond]

/-- Apply a finite schedule of explicit lazy-response coins. -/
noncomputable def respondAll (oracle : Oracle Q C) :
    List (Q × C) → Oracle Q C
  | [] => oracle
  | entry :: entries => respondAll (oracle.respond entry.1 entry.2).2 entries

/-- Running the same response schedule preserves lookup equivalence of the
starting handlers. -/
theorem LookupEquivalent.respondAll {left right : Oracle Q C}
    (h : LookupEquivalent left right) (entries : List (Q × C)) :
    LookupEquivalent (respondAll left entries) (respondAll right entries) := by
  induction entries generalizing left right with
  | nil => exact h
  | cons entry entries ih =>
      exact ih (h.respond entry.1 entry.2)

/-- One adjacent swap of distinct sampled queries preserves the denoted
partial function, including after any common suffix schedule. -/
theorem respondAll_swap_distinct (oracle : Oracle Q C)
    (first second : Q × C) (rest : List (Q × C))
    (hne : first.1 ≠ second.1) :
    LookupEquivalent
      (respondAll oracle (first :: second :: rest))
      (respondAll oracle (second :: first :: rest)) := by
  simpa only [respondAll] using
    (respond_distinct_commute oracle hne first.2 second.2).respondAll rest

/-- Any permutation of a schedule with pairwise-distinct query keys preserves
the final lookup semantics.  This is the deterministic core of moving eager
construction-prefix samples to later reveal points. -/
theorem respondAll_perm_of_nodup (oracle : Oracle Q C)
    {left right : List (Q × C)} (hperm : left.Perm right)
    (hnodup : (left.map Prod.fst).Nodup) :
    LookupEquivalent (respondAll oracle left) (respondAll oracle right) := by
  induction hperm generalizing oracle with
  | nil => exact LookupEquivalent.refl oracle
  | @cons entry left right hperm ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      exact ih (oracle := (oracle.respond entry.1 entry.2).2) hnodup.2
  | @swap first second entries =>
      simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnodup
      exact (respondAll_swap_distinct oracle first second entries
        (fun heq => hnodup.1 (Or.inl heq.symm))).symm
  | @trans left middle right hlm hmr ihlm ihmr =>
      have hmiddle : (middle.map Prod.fst).Nodup := by
        exact (hlm.map Prod.fst).nodup_iff.mp hnodup
      exact (ihlm (oracle := oracle) hnodup).trans
        (ihmr (oracle := oracle) hmiddle)

end Reordering

end Oracle

/-! ## Order differs, semantics agree -/

namespace SpongeOracleReorderingExample

noncomputable def leftFirst : Oracle Nat Bool :=
  ((Oracle.empty.respond 7 true).2.respond 9 false).2

noncomputable def rightFirst : Oracle Nat Bool :=
  ((Oracle.empty.respond 9 false).2.respond 7 true).2

theorem leftFirst_log : leftFirst.log = [(7, true), (9, false)] := by
  have h7 : (Oracle.empty : Oracle Nat Bool).lookup 7 = none :=
    Oracle.lookup_empty 7
  have h9 : ((Oracle.empty : Oracle Nat Bool).respond 7 true).2.lookup 9 = none := by
    rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_empty]
  simp only [leftFirst]
  rw [Oracle.respond_fresh_log h9, Oracle.respond_fresh_log h7]
  rfl

theorem rightFirst_log : rightFirst.log = [(9, false), (7, true)] := by
  have h9 : (Oracle.empty : Oracle Nat Bool).lookup 9 = none :=
    Oracle.lookup_empty 9
  have h7 : ((Oracle.empty : Oracle Nat Bool).respond 9 false).2.lookup 7 = none := by
    rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_empty]
  simp only [rightFirst]
  rw [Oracle.respond_fresh_log h7, Oracle.respond_fresh_log h9]
  rfl

theorem logs_differ : leftFirst.log ≠ rightFirst.log := by
  rw [leftFirst_log, rightFirst_log]
  decide

theorem lookups_agree : Oracle.LookupEquivalent leftFirst rightFirst := by
  exact Oracle.respond_distinct_commute Oracle.empty (by decide) true false

theorem exact_values :
    leftFirst.lookup 7 = some true ∧ leftFirst.lookup 9 = some false := by
  unfold leftFirst
  constructor
  · rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_respond_self,
      Oracle.respond_fresh_fst (Oracle.lookup_empty 7)]
  · rw [Oracle.lookup_respond_self]
    rw [Oracle.respond_fresh_fst]
    rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_empty]

def scheduleA : List (Nat × Bool) := [(7, true), (9, false), (11, true)]
def scheduleB : List (Nat × Bool) := [(11, true), (7, true), (9, false)]

theorem schedule_perm : scheduleA.Perm scheduleB := by decide

theorem schedule_keys_nodup : (scheduleA.map Prod.fst).Nodup := by decide

theorem reordered_schedule_agrees :
    Oracle.LookupEquivalent
      (Oracle.respondAll Oracle.empty scheduleA)
      (Oracle.respondAll Oracle.empty scheduleB) :=
  Oracle.respondAll_perm_of_nodup Oracle.empty schedule_perm
    schedule_keys_nodup

end SpongeOracleReorderingExample

/-- info: 'Minidregg.Selvage.Oracle.respond_distinct_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Oracle.respond_distinct_commute
/-- info: 'Minidregg.Selvage.SpongeOracleReorderingExample.lookups_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeOracleReorderingExample.lookups_agree
/-- info: 'Minidregg.Selvage.Oracle.respondAll_perm_of_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Oracle.respondAll_perm_of_nodup

end Minidregg.Selvage
