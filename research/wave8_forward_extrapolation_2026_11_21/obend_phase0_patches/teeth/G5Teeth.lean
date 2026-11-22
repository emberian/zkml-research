module
/- Gate G5 teeth (2026-11-21): the Simplex vote/finalize quorum is `n - f`, not `2f + 1`.

* (a) At `n = 5, f = 1` the old threshold `2f + 1 = 3` fails: the committee `[0, 1, 2, 3, 4]` with
  node `0` faulty has two 3-member quorums `{0, 1, 2}` and `{0, 3, 4}` whose only common member is
  faulty (`old_threshold_no_honest_overlap`, by `decide`), so the `2f + 1` intersection statement is
  false once `n > 3f + 1` (`old_threshold_lemma_false`). The same split is a *reachable* run of
  `SimplexProtocol` in which two different blocks of view 1 each collect `2f + 1` votes
  (`old_threshold_two_blocks`), and neither collects the `n - f = 4` that notarizes
  (`new_threshold_refuses_split`).
* (b) The `n - f = 4` threshold holds there: two 4-subsets of 5 share `≥ 3 ≥ f + 1` members, an
  honest one among them (`new_threshold_overlap`, `new_threshold_honest`), and the protocol theorems
  apply to the 5-node committee (`p5_notarized_block_unique`).
* (c) `#tooth`: the stored proofs of `honest_of_quorum` and `accountable_protocol` are rejected by
  the kernel when `Protocol.quorum` is mutated back to `2 * P.f + 1`.
-/
public import Obend.Consensus.SimplexProtocol
public import Obend.Tactic.Tooth
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.Simplex
@[expose] public section

namespace Obend.Teeth.Consensus.G5

open Obend.Consensus.Simplex (honest_quorum_intersection_nf quorum_overlap_nf)
open Obend.Consensus.SimplexProtocol

set_option autoImplicit false

/-! ## (a) `2f + 1` fails at `n = 5, f = 1` -/

def committee5 : List Nat := [0, 1, 2, 3, 4]
def faulty5 : Nat → Bool := (· == 0)
def quorumA : Nat → Bool := fun n => [0, 1, 2].contains n
def quorumB : Nat → Bool := fun n => [0, 3, 4].contains n

/-- Both sets are `2f + 1 = 3` quorums of a committee of `5 ≥ 3f + 1` with one faulty member, and
no member of both is honest. -/
theorem old_threshold_no_honest_overlap :
    3 * 1 + 1 ≤ committee5.length ∧
    2 * 1 + 1 ≤ (committee5.filter quorumA).length ∧
    2 * 1 + 1 ≤ (committee5.filter quorumB).length ∧
    (committee5.filter faulty5).length ≤ 1 ∧
    ¬ ∃ x ∈ committee5, quorumA x = true ∧ quorumB x = true ∧ faulty5 x = false := by
  decide

/-- Their only common member is the faulty one. -/
theorem old_threshold_overlap_is_faulty :
    committee5.filter (fun x => quorumA x && quorumB x) = [0] ∧ faulty5 0 = true := by
  decide

/-- **The `2f + 1` intersection statement is false for `n > 3f + 1`.** -/
theorem old_threshold_lemma_false :
    ¬ ∀ (l : List Nat) (f : Nat) (p q faulty : Nat → Bool),
      3 * f + 1 ≤ l.length → 2 * f + 1 ≤ (l.filter p).length → 2 * f + 1 ≤ (l.filter q).length →
      (l.filter faulty).length ≤ f → ∃ x ∈ l, p x = true ∧ q x = true ∧ faulty x = false := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := old_threshold_no_honest_overlap
  exact h5 (h committee5 1 quorumA quorumB faulty5 h1 h2 h3 h4)

/-- The 5-node protocol, node `0` faulty (and the leader of view 1). -/
def p5 : Protocol := ⟨committee5, 1, faulty5, by decide, by decide, by decide⟩

theorem p5_quorum : p5.quorum = 4 := by decide

def blockA : Chain := [.block 1 10]
def blockB : Chain := [.block 1 11]

/-- The faulty leader proposes and votes for both blocks; honest `1, 2` vote for `A`, honest `3, 4`
for `B`. Newest first. -/
def splitRun : Sent :=
  [ ⟨4, 1, .vote, .block blockB⟩, ⟨3, 1, .vote, .block blockB⟩
  , ⟨2, 1, .vote, .block blockA⟩, ⟨1, 1, .vote, .block blockA⟩
  , ⟨0, 1, .vote, .block blockB⟩, ⟨0, 1, .vote, .block blockA⟩
  , ⟨0, 1, .propose, .block blockB⟩, ⟨0, 1, .propose, .block blockA⟩ ]

private theorem voteRule_view1 (sent : Sent) (x : Nat)
    (hp : (⟨p5.leader 1, 1, .propose, .block [.block 1 x]⟩ : Msg) ∈ sent) :
    VoteRule p5 sent 1 (.block [.block 1 x]) :=
  ⟨Nat.le_refl 1, [], x, rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩

private theorem reach_vote {sent : Sent} (n x : Nat) (hn : n ∈ committee5 ∧ faulty5 n = false)
    (hfresh : votedAny sent n 1 = false)
    (hp : (⟨p5.leader 1, 1, .propose, .block [.block 1 x]⟩ : Msg) ∈ sent) (h : Reach p5 sent) :
    Reach p5 (⟨n, 1, .vote, .block [.block 1 x]⟩ :: sent) :=
  .step h (.vote sent n 1 _ hn hfresh (voteRule_view1 sent x hp))

private theorem reach_inject {sent : Sent} (m : Msg) (hf : faulty5 m.sender = true)
    (h : Reach p5 sent) : Reach p5 (m :: sent) :=
  .step h (.inject sent m hf)

/-- **`splitRun` is reachable**: every message is a step of the protocol (the faulty leader's four
by `inject`, the honest four by `vote`, each its sender's first vote of view 1). -/
theorem splitRun_reach : Reach p5 splitRun :=
  reach_vote 4 11 (by decide) (by decide) (by decide) <|
  reach_vote 3 11 (by decide) (by decide) (by decide) <|
  reach_vote 2 10 (by decide) (by decide) (by decide) <|
  reach_vote 1 10 (by decide) (by decide) (by decide) <|
  reach_inject _ (by decide) <| reach_inject _ (by decide) <|
  reach_inject _ (by decide) <| reach_inject _ (by decide) .nil

/-- **Under `2f + 1`, one reachable view would notarize two blocks**: both collect `3` votes. -/
theorem old_threshold_two_blocks :
    Reach p5 splitRun ∧ blockA ≠ blockB ∧
      2 * p5.f + 1 ≤ votesFor p5 splitRun 1 (.block blockA) ∧
      2 * p5.f + 1 ≤ votesFor p5 splitRun 1 (.block blockB) :=
  ⟨splitRun_reach, by decide, by decide, by decide⟩

/-- Under `n - f`, neither block of the split is notarized. -/
theorem new_threshold_refuses_split :
    ¬ NotarizedBlock p5 splitRun 1 blockA ∧ ¬ NotarizedBlock p5 splitRun 1 blockB := by
  decide

/-! ## (b) `n - f` holds at `n = 5, f = 1` -/

/-- Two `4`-member quorums of the five share at least `3 ≥ f + 1` members. -/
theorem new_threshold_overlap (p q : Nat → Bool)
    (hp : 4 ≤ (committee5.filter p).length) (hq : 4 ≤ (committee5.filter q).length) :
    3 ≤ (committee5.filter fun x => p x && q x).length :=
  quorum_overlap_nf committee5 1 p q hp hq

/-- ... and, with at most one faulty member, an honest one. -/
theorem new_threshold_honest (p q faulty : Nat → Bool)
    (hp : 4 ≤ (committee5.filter p).length) (hq : 4 ≤ (committee5.filter q).length)
    (hf : (committee5.filter faulty).length ≤ 1) :
    ∃ x ∈ committee5, p x = true ∧ q x = true ∧ faulty x = false :=
  honest_quorum_intersection_nf committee5 1 p q faulty (by decide) hp hq hf

/-- The protocol theorem at the 5-node committee: one view notarizes one block. -/
theorem p5_notarized_block_unique {sent : Sent} (hr : Reach p5 sent) {v : Nat} {c₁ c₂ : Chain}
    (h₁ : NotarizedBlock p5 sent v c₁) (h₂ : NotarizedBlock p5 sent v c₂) : c₁ = c₂ :=
  notarized_block_unique (reach_inv hr) h₁ h₂

/-! ## (c) Mutation teeth

`notarized_block_unique` cannot be the target: its closure reaches the structure `Inv` (and
`Step`, `Reach`), whose fields mention `NotarizedBlock`, hence `Protocol.quorum`; `#tooth`
refuses to clone affected inductives. `honest_of_quorum` and `accountable_protocol` are the
quorum-dependent steps every safety theorem goes through and reach no affected inductive. -/

#tooth Obend.Consensus.SimplexProtocol.honest_of_quorum by mutation
  Obend.Consensus.SimplexProtocol.Protocol.quorum := fun P => 2 * P.f + 1

#tooth Obend.Consensus.SimplexProtocol.accountable_protocol by mutation
  Obend.Consensus.SimplexProtocol.Protocol.quorum := fun P => 2 * P.f + 1

end Obend.Teeth.Consensus.G5
end
