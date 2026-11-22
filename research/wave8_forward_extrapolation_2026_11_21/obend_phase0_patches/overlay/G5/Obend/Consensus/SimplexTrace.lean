module
/-
# Obend.Consensus.SimplexTrace — a node's run, checked against the protocol relation

`Obend.Consensus.SimplexProtocol` is a relation. This module makes "the node is a simulator of
it" a checked sentence: a node emits its run as a TRACE, the list of messages it and its peers
sent in order, and `checkTrace P tr` decides, message by message, that each one is a `Step` of
the relation from the messages before it. `checkTrace_sound`: an accepted trace is reachable
(`Reach P tr.reverse`). A refusal is a `TraceClause` that names the message: the sender neither
in the committee nor declared faulty, a proposal not by the view's leader, a second vote in a
view (`votedTwice`), two different votes in a view (`equivocation`, carrying the
`SlashingReceipt` of those two votes, which `checks` against the trace:
`checkStep_equivocation_checks`), a block vote whose chain is not on notarized ground
(`voteRule`), or a finalize vote for a block the node did not vote for or that is not notarized
(`finalizeRule`).

The judge is `simplexTraceJudge` (object: the `Protocol`, i.e. the committee and who is declared
faulty; certificate: the trace) and the registered format is `simplex-trace@1`, decoded from JSON
(the witness wire every other format uses). `explain` renders the clause so the session's
refusal says which message, which node and, for an equivocation, which receipt.

That judge cannot refute: its claim is "some trace of `P` is reachable", and the empty trace always
is (`protocol_always_admits_empty_trace`), so no clause of it is refuting (`simplexProtocolRefutes`,
`simplexProtocolRefutes_exact`). The refusal still has content about the trace it was given:
`traceVerdict_refutes_trace` (a refused trace is not reachable). The judge whose object is the
run itself, `simplexRunJudge` over `(P, tr)`, states that as its `refuted` law: every clause
refutes, and the check is complete on every run.

Views and node ids are `Nat`. No signatures: the trace's sender field is taken as the signer,
as in the relation.
-/

public import Obend.Consensus.SimplexProtocol
public meta import Obend.Consensus.SimplexProtocol
public import Obend.Judge.Class
public import Lean.Data.Json
public import Std.Data.TreeMap.Lemmas
public import Std.Data.TreeSet.Lemmas
public import Obend.Core.Digest
public import Obend.Receipt.Merkle
public meta import Obend.Receipt.Merkle

public section

namespace Obend.Consensus.SimplexTrace

open Obend.Consensus.SimplexProtocol
open Lean (Json)

set_option autoImplicit false

/-! ## 1. The rules, decided -/

instance (P : Protocol) (sent : Sent) (v : Nat) : Decidable (NotarizedDummy P sent v) :=
  inferInstanceAs (Decidable (P.quorum ≤ votesFor P sent v (.dummy v)))

instance (P : Protocol) (sent : Sent) (v : Nat) (c : Chain) : Decidable (NotarizedBlock P sent v c) :=
  inferInstanceAs (Decidable (P.quorum ≤ votesFor P sent v (.block c)))

@[expose] def entryNotarizedB (P : Protocol) (sent : Sent) (k : Nat) (upto : Chain) : Entry → Bool
  | .dummy v => v == k + 1 && decide (NotarizedDummy P sent (k + 1))
  | .block v _ => v == k + 1 && decide (NotarizedBlock P sent (k + 1) upto)

theorem entryNotarizedB_sound {P : Protocol} {sent : Sent} {k : Nat} {upto : Chain} {e : Entry}
    (h : entryNotarizedB P sent k upto e = true) : EntryNotarized P sent k upto e := by
  cases e with
  | dummy v =>
    simp only [entryNotarizedB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h
  | block v x =>
    simp only [entryNotarizedB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h

@[expose] def chainNotarizedB (P : Protocol) (sent : Sent) (c : Chain) : Bool :=
  (List.range c.length).all fun k =>
    match c[k]? with
    | some e => entryNotarizedB P sent k (c.take (k + 1)) e
    | none => false

theorem chainNotarizedB_sound {P : Protocol} {sent : Sent} {c : Chain}
    (h : chainNotarizedB P sent c = true) : ChainNotarized P sent c := by
  intro k hk
  simp only [chainNotarizedB, List.all_eq_true, List.mem_range] at h
  have hkk := h k hk
  rw [List.getElem?_eq_getElem hk] at hkk
  exact entryNotarizedB_sound hkk

@[expose] def voteRuleB (P : Protocol) (sent : Sent) (v : Nat) : Target → Bool
  | .block c =>
    decide (1 ≤ v) &&
      (match c.getLast? with
       | some (.block w _) =>
         w == v && c.dropLast.length == v - 1 && chainNotarizedB P sent c.dropLast &&
           sent.contains ⟨P.leader v, v, .propose, .block c⟩
       | _ => false)
  | .dummy w => decide (1 ≤ v) && w == v

theorem voteRuleB_sound {P : Protocol} {sent : Sent} {v : Nat} {t : Target}
    (h : voteRuleB P sent v t = true) : VoteRule P sent v t := by
  cases t with
  | dummy w =>
    simp only [voteRuleB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h
  | block c =>
    simp only [voteRuleB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, hm⟩ := h
    cases hl : c.getLast? with
    | none => rw [hl] at hm; cases hm
    | some e =>
      rw [hl] at hm
      cases e with
      | dummy w => cases hm
      | block w x =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨⟨⟨hw, hlen⟩, hchain⟩, hprop⟩ := hm
        obtain ⟨p, hp⟩ := List.getLast?_eq_some_iff.1 hl
        have hdrop : c.dropLast = p := by rw [hp]; exact List.dropLast_concat
        rw [hdrop] at hlen hchain
        subst hw
        refine ⟨h1, p, x, hp, hlen, chainNotarizedB_sound hchain, ?_⟩
        exact List.contains_iff_mem.1 hprop

/-! ## 2. One step, checked -/

inductive TraceClause where
  | senderUnknown (n : Nat)
  | notLeader (n v : Nat)
  | proposeNotBlock (n v : Nat)
  | votedTwice (n v : Nat)
  | equivocation (r : SlashingReceipt)
  | voteRule (n v : Nat)
  | finalizeRule (n v : Nat)
  | finalizeNotBlock (n v : Nat)
  deriving DecidableEq, Repr

@[expose] def isVoteOf (n v : Nat) (m : Msg) : Bool :=
  m.sender == n && m.view == v && m.kind == .vote

/-- The step a message is, from the messages before it: an injection if its sender is declared
faulty; otherwise the honest rule of its kind. -/
@[expose] def checkStep (P : Protocol) (sent : Sent) (m : Msg) : Except TraceClause Unit :=
  if P.faulty m.sender then .ok ()
  else if !P.committee.contains m.sender then .error (.senderUnknown m.sender)
  else
    match m.kind with
    | .propose =>
      match m.target with
      | .block _ =>
        if m.sender == P.leader m.view then .ok () else .error (.notLeader m.sender m.view)
      | .dummy _ => .error (.proposeNotBlock m.sender m.view)
    | .vote =>
      match sent.find? (isVoteOf m.sender m.view) with
      | some m' =>
        match m'.target == m.target with
        | true => .error (.votedTwice m.sender m.view)
        | false => .error (.equivocation ⟨m.view, m'.target, m.target, [m.sender]⟩)
      | none =>
        match voteRuleB P sent m.view m.target with
        | true => .ok ()
        | false => .error (.voteRule m.sender m.view)
    | .finalize =>
      match m.target with
      | .block c =>
        match voted sent m.sender m.view (.block c) && decide (NotarizedBlock P sent m.view c) with
        | true => .ok ()
        | false => .error (.finalizeRule m.sender m.view)
      | .dummy _ => .error (.finalizeNotBlock m.sender m.view)

theorem votedAny_eq_false_of_find?_none {sent : Sent} {n v : Nat}
    (h : sent.find? (isVoteOf n v) = none) : votedAny sent n v = false := by
  rw [List.find?_eq_none] at h
  unfold votedAny
  rw [List.any_eq_false]
  intro m hm
  exact h m hm

/-- **An accepted step is a `Step`.** -/
theorem checkStep_sound {P : Protocol} {sent : Sent} {m : Msg}
    (h : checkStep P sent m = .ok ()) : Step P sent (m :: sent) := by
  obtain ⟨n, v, k, t⟩ := m
  unfold checkStep at h
  simp only at h
  by_cases hf : P.faulty n = true
  · exact Step.inject sent ⟨n, v, k, t⟩ hf
  · rw [ite_eq_right hf] at h
    have hf' : P.faulty n = false := by cases hpf : P.faulty n <;> simp_all
    by_cases hc : P.committee.contains n = true
    · rw [hc] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hn : P.honest n := ⟨List.contains_iff_mem.1 hc, hf'⟩
      cases k with
      | propose =>
        cases t with
        | block c =>
          simp only at h
          split at h
          · rename_i hl
            exact Step.propose sent n v c hn (beq_iff_eq.1 hl)
          · cases h
        | dummy w => cases h
      | vote =>
        simp only at h
        cases hfind : sent.find? (isVoteOf n v) with
        | some m' =>
          rw [hfind] at h
          simp only at h
          cases hq : (m'.target == t) <;> rw [hq] at h <;> cases h
        | none =>
          rw [hfind] at h
          simp only at h
          cases hrule : voteRuleB P sent v t
          · rw [hrule] at h; cases h
          · exact Step.vote sent n v t hn (votedAny_eq_false_of_find?_none hfind) (voteRuleB_sound hrule)
      | finalize =>
        cases t with
        | block c =>
          simp only at h
          cases hok : (voted sent n v (.block c) && decide (NotarizedBlock P sent v c))
          · rw [hok] at h; cases h
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
            exact Step.finalize sent n v c hn hok.1 hok.2
        | dummy w => cases h
    · have hc' : P.committee.contains n = false := by cases hpc : P.committee.contains n <;> simp_all
      rw [hc'] at h
      simp at h

/-- **An equivocation refusal names a receipt that checks against the trace up to that
message**: the two votes are both in it. -/
theorem checkStep_equivocation_checks {P : Protocol} {sent : Sent} {m : Msg} {r : SlashingReceipt}
    (h : checkStep P sent m = .error (.equivocation r)) : r.checks (m :: sent) = true := by
  obtain ⟨n, v, k, t⟩ := m
  unfold checkStep at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases k with
      | propose =>
        cases t with
        | block c => simp only at h; split at h <;> cases h
        | dummy w => cases h
      | finalize =>
        cases t with
        | block c =>
          simp only at h
          cases hok : (voted sent n v (.block c) && decide (NotarizedBlock P sent v c)) <;> rw [hok] at h <;> cases h
        | dummy w => cases h
      | vote =>
        simp only at h
        cases hfind : sent.find? (isVoteOf n v) with
        | none =>
          rw [hfind] at h
          simp only at h
          cases hrule : voteRuleB P sent v t <;> rw [hrule] at h <;> cases h
        | some m' =>
          rw [hfind] at h
          simp only at h
          cases hq : (m'.target == t)
          · rw [hq] at h
            have hne : ¬ (m'.target == t) = true := by rw [hq]; decide
            cases h
            have hmem := List.mem_of_find?_eq_some hfind
            have hp := List.find?_some hfind
            simp only [isVoteOf, Bool.and_eq_true, beq_iff_eq] at hp
            obtain ⟨⟨hs, hv⟩, hk⟩ := hp
            have hm' : m' = ⟨n, v, .vote, m'.target⟩ := by
              cases m'; simp only at hs hv hk; subst hs hv hk; rfl
            simp only [SlashingReceipt.checks, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
              List.all_nil, Bool.and_true]
            refine ⟨fun heq => hne (beq_iff_eq.2 heq), ?_, ?_⟩
            · rw [voted_iff]; rw [hm'] at hmem; exact List.mem_cons_of_mem _ hmem
            · rw [voted_iff]; exact List.mem_cons_self
          · rw [hq] at h; cases h

/-! ## 3. The trace -/

@[expose] def checkTraceAux (P : Protocol) : Sent → List Msg → Except TraceClause Unit
  | _, [] => .ok ()
  | sent, m :: rest =>
    match checkStep P sent m with
    | .ok () => checkTraceAux P (m :: sent) rest
    | .error k => .error k

theorem checkTraceAux_sound (P : Protocol) :
    ∀ (tr : List Msg) (sent : Sent), Reach P sent → checkTraceAux P sent tr = .ok () →
      Reach P (tr.reverse ++ sent)
  | [], sent, hr, _ => by simpa using hr
  | m :: rest, sent, hr, h => by
    cases hc : checkStep P sent m with
    | ok u =>
      cases u
      simp only [checkTraceAux, hc] at h
      have hs := checkStep_sound hc
      have ih := checkTraceAux_sound P rest (m :: sent) (Reach.step hr hs) h
      simpa [List.reverse_cons, List.append_assoc] using ih
    | error k => simp only [checkTraceAux, hc] at h; cases h

open Obend.Receipt.Merkle (leb128 leb128_injective encodeFields encodeFields_injective)
def encodeEntryBytes : Entry → List UInt8
  | .dummy v => encodeFields [[0],leb128 v]
  | .block v p => encodeFields [[1],leb128 v,leb128 p]
private theorem encodeEntryBytes_injective {a b : Entry} (h : encodeEntryBytes a = encodeEntryBytes b) : a = b := by
  cases a <;> cases b <;> simp only [encodeEntryBytes] at h <;>
    have hh := encodeFields_injective _ _ h <;> simp only [List.cons.injEq] at hh
  · rw [leb128_injective hh.2.1,leb128_injective hh.2.2.1]
  · exact False.elim ((show (1 : UInt8) ≠ 0 from by decide) hh.1.1)
  · exact False.elim ((show (0 : UInt8) ≠ 1 from by decide) hh.1.1)
  · exact congrArg Entry.dummy (leb128_injective hh.2.1)
private theorem encodeChainBytes_injective (a b : Chain)
    (h : a.map encodeEntryBytes = b.map encodeEntryBytes) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons e es ih =>
    cases b with
    | nil => simp at h
    | cons f fs =>
      simp only [List.map_cons,List.cons.injEq] at h
      rw [encodeEntryBytes_injective h.1,ih fs h.2]
def encodeTargetBytes : Target → List UInt8
  | .dummy v => encodeFields [[0],leb128 v]
  | .block c => encodeFields [[1],encodeFields (c.map encodeEntryBytes)]
private theorem encodeTargetBytes_injective {a b : Target} (h : encodeTargetBytes a = encodeTargetBytes b) : a = b := by
  cases a <;> cases b <;> simp only [encodeTargetBytes] at h <;>
    have h := encodeFields_injective _ _ h <;> simp only [List.cons.injEq] at h
  · congr 1
    have hh := encodeFields_injective _ _ h.2.1
    exact encodeChainBytes_injective _ _ hh
  · exact False.elim ((show (1 : UInt8) ≠ 0 from by decide) h.1.1)
  · exact False.elim ((show (0 : UInt8) ≠ 1 from by decide) h.1.1)
  · exact congrArg Target.dummy (leb128_injective h.2.1)

/-! ## Incremental voter and quorum indexing -/
attribute [local instance] lexOrd
abbrev VoteKey := Nat × Target
abbrev VoterViewKey := Nat × Nat
def cmpEntry (a b : Entry) : Ordering := compare (encodeEntryBytes a) (encodeEntryBytes b)
def cmpTarget (a b : Target) : Ordering := compare (encodeTargetBytes a) (encodeTargetBytes b)
def cmpVoteKey (a b : VoteKey) : Ordering := compare (a.1,encodeTargetBytes a.2) (b.1,encodeTargetBytes b.2)
instance : Ord Target where compare := cmpTarget
instance : Std.LawfulEqOrd Target where
  compare_self := by intro a; exact Std.ReflCmp.compare_self (a := encodeTargetBytes a)
  eq_of_compare := by
    intro a b h
    exact encodeTargetBytes_injective (Std.compare_eq_iff_eq.mp h)
instance : Std.TransOrd Target :=
  inferInstanceAs (Std.TransCmp (compareOn encodeTargetBytes))
abbrev SenderVoteKey := Nat × Nat × Target
private def voteKey (v : Nat) (t : Target) : VoteKey := (v,t)
private def senderKey (n v : Nat) (t : Target) : SenderVoteKey := (n,v,t)
private theorem voteKey_eq {v w : Nat} {t u : Target} : voteKey v t = voteKey w u ↔ v=w ∧ t=u := by simp only [voteKey,Prod.mk.injEq]
private theorem senderKey_eq {n m v w : Nat} {t u : Target} :
    senderKey n v t = senderKey m w u ↔ n=m ∧ v=w ∧ t=u := by
  simp only [senderKey,Prod.mk.injEq]
theorem cmpEntry_eq_iff (a b : Entry) : cmpEntry a b = .eq ↔ a=b := by
  constructor
  · intro h; exact encodeEntryBytes_injective (Std.compare_eq_iff_eq.mp h)
  · intro h; subst b; exact Std.ReflCmp.compare_self (a := encodeEntryBytes a)
theorem cmpTarget_eq_iff (a b : Target) : cmpTarget a b = .eq ↔ a=b := by
  change compare a b = .eq ↔ a=b
  exact Std.compare_eq_iff_eq
theorem cmpVoteKey_eq_compare (a b : VoteKey) : cmpVoteKey a b = compare a b := by unfold cmpVoteKey; rfl
instance : Std.TransCmp cmpEntry := inferInstanceAs (Std.TransCmp (compareOn encodeEntryBytes))
instance : Std.TransCmp cmpTarget := inferInstanceAs (Std.TransCmp (compareOn encodeTargetBytes))
instance : Std.TransCmp cmpVoteKey := inferInstanceAs (Std.TransCmp (compare : VoteKey → VoteKey → Ordering))
/-- Persistent balanced indexes let each trace step share its predecessor's untouched branches.
Distinct committee voters are stored in a set per vote key; duplicate votes never increase quorum. -/
structure TraceIndex where
  committee : Std.TreeSet Nat
  voters : Std.TreeMap VoteKey (Std.TreeSet Nat)
  votes : Std.TreeSet SenderVoteKey
  prior : Std.TreeMap VoterViewKey Target
  proposals : Std.TreeSet SenderVoteKey
namespace TraceIndex
def empty (P : Protocol) : TraceIndex := ⟨Std.TreeSet.ofList P.committee,∅,∅,∅,∅⟩
def lookupVoters (idx : TraceIndex) (v : Nat) (t : Target) : Std.TreeSet Nat := idx.voters.getD (voteKey v t) ∅
def lookupVotes (idx : TraceIndex) (v : Nat) (t : Target) : Nat := (idx.lookupVoters v t).size
def lookupPriorVote? (idx : TraceIndex) (n v : Nat) : Option Target := idx.prior[(n,v)]?
def add (idx : TraceIndex) (m : Msg) : TraceIndex :=
  match m.kind with
  | .propose => { idx with proposals := idx.proposals.insert (senderKey m.sender m.view m.target) }
  | .finalize => idx
  | .vote =>
    { idx with
      voters := if idx.committee.contains m.sender then
        idx.voters.insert (voteKey m.view m.target) ((idx.lookupVoters m.view m.target).insert m.sender)
        else idx.voters
      votes := idx.votes.insert (senderKey m.sender m.view m.target)
      prior := idx.prior.insert (m.sender,m.view) m.target }
def ofSent (P : Protocol) : Sent → TraceIndex
  | [] => empty P
  | m::sent => (ofSent P sent).add m
/-- Representation invariant: each query denotes exactly the corresponding historical fact. -/
def Simulates (idx : TraceIndex) (P : Protocol) (sent : Sent) : Prop :=
  (∀ n, idx.committee.contains n = P.committee.contains n) ∧
  (∀ v t n, (idx.lookupVoters v t).contains n = (P.committee.contains n && voted sent n v t)) ∧
  (∀ n v t, idx.votes.contains (senderKey n v t) = voted sent n v t) ∧
  (∀ n v, idx.lookupPriorVote? n v = (sent.find? (isVoteOf n v)).map Msg.target) ∧
  (∀ n v t, idx.proposals.contains (senderKey n v t) = sent.contains ⟨n,v,.propose,t⟩)
theorem empty_simulates (P : Protocol) : (empty P).Simulates P [] := by
  simp [Simulates,empty,lookupVoters,lookupPriorVote?,voted,Std.TreeSet.contains_ofList]
private theorem compare_eq_decide {α : Type} [Ord α] [Std.LawfulEqOrd α] [DecidableEq α] (a b : α) :
    (compare a b == .eq) = decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  simp
set_option maxRecDepth 4096 in
theorem add_simulates {idx : TraceIndex} {P : Protocol} {sent : Sent}
    (h : idx.Simulates P sent) (m : Msg) : (idx.add m).Simulates P (m::sent) := by
  rcases h with ⟨hc,hv,ha,hp,hr⟩
  rcases m with ⟨mn,mv,mk,mt⟩
  cases mk <;> simp only [Simulates,add]
  all_goals refine ⟨hc,?_,?_,?_,?_⟩
  all_goals intros
  all_goals simp only [lookupVoters,lookupPriorVote?,
    Std.TreeMap.getElem?_insert,Std.TreeSet.contains_insert,Std.compare_eq_iff_eq] at *
  all_goals simp [hc,hv,ha,hp,hr,isVoteOf,List.find?_cons,Msg.mk.injEq,
    Bool.and_assoc,compare_eq_decide,senderKey_eq]
  all_goals repeat' split <;> simp_all [Std.TreeMap.getD_insert,Std.TreeSet.contains_insert,compare_eq_decide,
    beq_iff_eq,voteKey_eq]
  all_goals grind
end TraceIndex
namespace TraceIndex
private theorem set_size_filter (xs : List Nat) (hn : xs.Nodup) (p : Nat → Bool) (set : Std.TreeSet Nat)
    (h : ∀ n, set.contains n = (xs.contains n && p n)) : set.size = (xs.filter p).length := by
  have hs : set.toList.Nodup := by simpa only [List.nodup_iff_pairwise_ne,Std.compare_eq_iff_eq] using (Std.TreeSet.distinct_toList (t := set))
  have hf : (xs.filter p).Nodup := hn.filter p
  have he : ∀ n, n ∈ set.toList ↔ n ∈ xs.filter p := by
    intro n
    rw [← List.contains_iff_mem,Std.TreeSet.contains_toList,h]
    simp [List.mem_filter]
  have hp := (List.perm_ext_iff_of_nodup hs hf).mpr he
  simpa only [Std.TreeSet.length_toList] using hp.length_eq
theorem lookupVotes_eq {idx : TraceIndex} {P : Protocol} {sent : Sent} (h : idx.Simulates P sent)
    (v : Nat) (t : Target) : idx.lookupVotes v t = votesFor P sent v t :=
  set_size_filter P.committee P.nodup (fun n => voted sent n v t) _ (h.2.1 v t)
theorem ofSent_simulates (P : Protocol) (sent : Sent) : (ofSent P sent).Simulates P sent := by
  induction sent with
  | nil => exact empty_simulates P
  | cons m sent ih => exact add_simulates ih m
end TraceIndex
def entryNotarizedExec (P : Protocol) (idx : TraceIndex) (k : Nat) (upto : Chain) : Entry → Bool
  | .dummy v => v == k + 1 && decide (P.quorum ≤ idx.lookupVotes (k+1) (.dummy (k+1)))
  | .block v _ => v == k + 1 && decide (P.quorum ≤ idx.lookupVotes (k+1) (.block upto))

def chainNotarizedExec (P : Protocol) (idx : TraceIndex) (c : Chain) : Bool :=
  (List.range c.length).all fun k =>
    match c[k]? with
    | some e => entryNotarizedExec P idx k (c.take (k + 1)) e
    | none => false

def voteRuleExec (P : Protocol) (idx : TraceIndex) (v : Nat) : Target → Bool
  | .block c =>
    decide (1 ≤ v) &&
      (match c.getLast? with
       | some (.block w _) =>
         w == v && c.dropLast.length == v - 1 && chainNotarizedExec P idx c.dropLast &&
           idx.proposals.contains (senderKey (P.leader v) v (.block c))
       | _ => false)
  | .dummy w => decide (1 ≤ v) && w == v

def checkStepExec (P : Protocol) (idx : TraceIndex) (m : Msg) : Except TraceClause Unit :=
  if P.faulty m.sender then .ok ()
  else if !idx.committee.contains m.sender then .error (.senderUnknown m.sender)
  else
    match m.kind with
    | .propose =>
      match m.target with
      | .block _ =>
        if m.sender == P.leader m.view then .ok () else .error (.notLeader m.sender m.view)
      | .dummy _ => .error (.proposeNotBlock m.sender m.view)
    | .vote =>
      match idx.lookupPriorVote? m.sender m.view with
      | some m' =>
        match m' == m.target with
        | true => .error (.votedTwice m.sender m.view)
        | false => .error (.equivocation ⟨m.view, m', m.target, [m.sender]⟩)
      | none =>
        match voteRuleExec P idx m.view m.target with
        | true => .ok ()
        | false => .error (.voteRule m.sender m.view)
    | .finalize =>
      match m.target with
      | .block c =>
        match idx.votes.contains (senderKey m.sender m.view (.block c)) && decide (P.quorum ≤ idx.lookupVotes m.view (.block c)) with
        | true => .ok ()
        | false => .error (.finalizeRule m.sender m.view)
      | .dummy _ => .error (.finalizeNotBlock m.sender m.view)

theorem entryNotarizedExec_eq_entryNotarizedB {P : Protocol} {sent : Sent} {idx : TraceIndex}
    (h : idx.Simulates P sent) (k : Nat) (c : Chain) (e : Entry) :
    entryNotarizedExec P idx k c e = entryNotarizedB P sent k c e := by
  cases e <;> simp only [entryNotarizedExec,entryNotarizedB,TraceIndex.lookupVotes_eq h]
theorem chainNotarizedExec_eq_chainNotarizedB {P : Protocol} {sent : Sent} {idx : TraceIndex}
    (h : idx.Simulates P sent) (c : Chain) : chainNotarizedExec P idx c = chainNotarizedB P sent c := by
  simp only [chainNotarizedExec,chainNotarizedB,entryNotarizedExec_eq_entryNotarizedB h]
private theorem voteRuleExec_eq {P : Protocol} {sent : Sent} {idx : TraceIndex}
    (h : idx.Simulates P sent) (v : Nat) (t : Target) : voteRuleExec P idx v t = voteRuleB P sent v t := by
  cases t <;> simp only [voteRuleExec,voteRuleB,chainNotarizedExec_eq_chainNotarizedB h,h.2.2.2.2] <;> rfl
private theorem checkStepExec_eq {P : Protocol} {sent : Sent} {idx : TraceIndex}
    (h : idx.Simulates P sent) (m : Msg) : checkStepExec P idx m = checkStep P sent m := by
  simp only [checkStepExec,checkStep,h.1,h.2.2.1,h.2.2.2.1,voteRuleExec_eq h,TraceIndex.lookupVotes_eq h]
  split <;> try rfl
  split <;> try rfl
  cases m.kind <;> try rfl
  cases sent.find? (isVoteOf m.sender m.view) <;> rfl
def checkTraceAuxExec (P : Protocol) : TraceIndex → List Msg → Except TraceClause Unit
  | _, [] => .ok ()
  | idx,m::rest => match checkStepExec P idx m with
    | .ok () => checkTraceAuxExec P (idx.add m) rest
    | .error c => .error c
def checkTraceExec (P : Protocol) (tr : List Msg) : Except TraceClause Unit :=
  checkTraceAuxExec P (TraceIndex.empty P) tr
private theorem checkTraceAuxExec_eq {P : Protocol} (tr : List Msg) {sent : Sent} {idx : TraceIndex}
    (h : idx.Simulates P sent) : checkTraceAuxExec P idx tr = checkTraceAux P sent tr := by
  induction tr generalizing sent idx with
  | nil => rfl
  | cons m rest ih =>
    simp only [checkTraceAuxExec,checkTraceAux,checkStepExec_eq h]
    split
    · exact ih (TraceIndex.add_simulates h m)
    · rfl

/-- Check a trace in send order. An empty or single-message trace needs no history
index. Longer traces use the incremental committee, voter and proposal indexes. -/
@[expose] def checkTrace (P : Protocol) : List Msg → Except TraceClause Unit
  | [] => .ok ()
  | [m] => checkStep P [] m
  | m :: n :: rest => checkTraceExec P (m :: n :: rest)

/-- All paths through the public checker return the list specification's exact verdict. -/
theorem checkTrace_eq_spec (P : Protocol) (tr : List Msg) :
    checkTrace P tr = checkTraceAux P [] tr := by
  cases tr with
  | nil => rfl
  | cons m rest =>
    cases rest with
    | nil => cases h : checkStep P [] m <;> simp [checkTrace, checkTraceAux, h]
    | cons n rest => exact checkTraceAuxExec_eq _ (TraceIndex.empty_simulates P)

theorem checkTraceExec_eq_checkTrace (P : Protocol) (tr : List Msg) :
    checkTraceExec P tr = checkTrace P tr :=
  (checkTraceAuxExec_eq tr (TraceIndex.empty_simulates P)).trans (checkTrace_eq_spec P tr).symm

/-- **An accepted trace is reachable.** -/
theorem checkTrace_sound {P : Protocol} {tr : List Msg} (h : checkTrace P tr = .ok ()) :
    Reach P tr.reverse := by
  rw [checkTrace_eq_spec] at h
  have := checkTraceAux_sound P tr [] Reach.nil h
  simpa using this

/-! ## 4. The judge and the format -/

@[expose] def TraceMeaning (P : Protocol) (tr : List Msg) : Prop := Reach P tr.reverse

@[expose] def traceVerdict (P : Protocol) (tr : List Msg) : Obend.Judge.Verdict TraceClause :=
  match checkTrace P tr with
  | .ok () => .ok
  | .error k => .refused k []

theorem traceVerdict_ok {P : Protocol} {tr : List Msg} (h : traceVerdict P tr = .ok) :
    checkTrace P tr = .ok () := by
  unfold traceVerdict at h
  cases hc : checkTrace P tr with
  | ok u => cases u; rfl
  | error k => rw [hc] at h; cases h

/-- **Every protocol admits a trace**: the empty one is reachable. So over `Protocol` objects the
claim `∃ tr, TraceMeaning P tr` is never false, and `∀ tr', ¬ TraceMeaning P tr'` never holds. -/
theorem protocol_always_admits_empty_trace (P : Protocol) : TraceMeaning P [] := Reach.nil

/-- The refuting clauses of the protocol-level judge: none. A refuting clause would certify
`∀ tr', ¬ TraceMeaning P tr'`, which `protocol_always_admits_empty_trace` contradicts for every
`P`. This determines the classification of every emitted clause (`simplexProtocolRefutes_exact`).
`traceVerdict_refutes_trace` and `simplexRunJudge` state what a refusal proves about the given trace. -/
def simplexProtocolRefutes : TraceClause → Bool
  | _ => false

theorem simplexProtocolRefutes_eq_false (k : TraceClause) : simplexProtocolRefutes k = false := by
  simp only [simplexProtocolRefutes]

/-- Any `refutes` that obeys the `refuted` law over `Protocol` objects is `false` on every clause
the checker emits, since the empty trace contradicts a refutation of the protocol. -/
theorem simplexProtocolRefutes_exact (refutes : TraceClause → Bool)
    (law : ∀ {P : Protocol} {tr : List Msg} {k : TraceClause} {p : List Nat},
      traceVerdict P tr = .refused k p → refutes k = true → ∀ tr', ¬ TraceMeaning P tr')
    {P : Protocol} {tr : List Msg} {k : TraceClause} {p : List Nat}
    (h : traceVerdict P tr = .refused k p) : refutes k = simplexProtocolRefutes k := by
  cases hk : refutes k with
  | false => exact (simplexProtocolRefutes_eq_false k).symm
  | true => exact absurd (protocol_always_admits_empty_trace P) (law h hk [])

@[expose, instance_reducible] def simplexTraceJudge : Obend.Judge Protocol (List Msg) where
  Clause := TraceClause
  Meaning := TraceMeaning
  check _ P tr := traceVerdict P tr
  sound := by intro _ P tr h; exact checkTrace_sound (traceVerdict_ok h)
  refutes := simplexProtocolRefutes
  refuted := by intro _ _ _ k _ _ href; rw [simplexProtocolRefutes_eq_false k] at href; cases href
  Fragment _ := True
  complete := by intro P _ _; exact ⟨[], 0, rfl⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- A committee of at least `3f+1` distinct nodes with the declared faulty ones bounded by `f`. -/
def mkProtocol? (committee : List Nat) (f : Nat) (faultyL : List Nat) : Option Protocol :=
  let faulty := fun n => faultyL.contains n
  if h : committee.Nodup ∧ 3 * f + 1 ≤ committee.length ∧ (committee.filter faulty).length ≤ f then
    some ⟨committee, f, faulty, h.1, h.2.1, h.2.2⟩
  else none

def decodeProtocol (s : String) : Except String Protocol := do
  let j ← Json.parse s
  let committee ← (← (← j.getObjVal? "committee").getArr?).toList.mapM (·.getNat?)
  let f ← j.getObjValAs? Nat "f"
  let faultyL ← (← (← j.getObjVal? "faulty").getArr?).toList.mapM (·.getNat?)
  match mkProtocol? committee f faultyL with
  | some P => pure P
  | none => throw "the committee must be at least 3f+1 distinct nodes with at most f declared faulty"

def decodeEntry (j : Json) : Except String Entry := do
  match j.getObjVal? "dummy" with
  | .ok d => return .dummy (← d.getNat?)
  | .error _ =>
    let b ← j.getObjVal? "block"
    return .block (← b.getObjValAs? Nat "view") (← b.getObjValAs? Nat "payload")

def decodeTarget (j : Json) : Except String Target := do
  match j.getObjVal? "dummy" with
  | .ok d => return .dummy (← d.getNat?)
  | .error _ =>
    let arr ← (← j.getObjVal? "block").getArr?
    return .block (← arr.toList.mapM decodeEntry)

def parseMsgKind (s : String) : Except String Kind :=
  if s == "propose" then .ok .propose
  else if s == "vote" then .ok .vote
  else if s == "finalize" then .ok .finalize
  else .error s!"unknown message kind {s}"

def decodeMsg (j : Json) : Except String Msg := do
  let sender ← j.getObjValAs? Nat "sender"
  let view ← j.getObjValAs? Nat "view"
  let kindS ← j.getObjValAs? String "kind"
  let kind ← parseMsgKind kindS
  let target ← decodeTarget (← j.getObjVal? "target")
  pure { sender, view, kind, target }

def decodeTrace (s : String) : Except String (List Msg) := do
  let j ← Json.parse s
  (← j.getArr?).toList.mapM decodeMsg

def TraceClause.describe : TraceClause → String
  | .senderUnknown n => s!"node {n} sent a message but is neither in the committee nor declared faulty"
  | .notLeader n v => s!"node {n} proposed in view {v} but is not its leader"
  | .proposeNotBlock n v => s!"node {n} proposed a dummy in view {v}"
  | .votedTwice n v => s!"node {n} voted twice in view {v} (the same target: a repeat, not an equivocation)"
  | .equivocation r =>
    s!"equivocation: node {r.signers} voted in view {r.view} for {toString (repr r.a)} and for {toString (repr r.b)}; slashing receipt {toString (repr r)} checks against the trace"
  | .voteRule n v => s!"node {n}'s block vote in view {v} is not on notarized ground: the chain must end in a block of view {v}, extend a chain of {v - 1} notarized entries, and have been proposed by the leader"
  | .finalizeRule n v => s!"node {n} finalize-voted in view {v} for a block it did not vote for, or that is not notarized in the trace so far"
  | .finalizeNotBlock n v => s!"node {n} finalize-voted a dummy in view {v}"

/-- Why a witness was refused, for the session's error. -/
def explainTrace (_grade : Nat) (objWire certWire : String) : String :=
  match decodeProtocol objWire, decodeTrace certWire with
  | .error e, _ => s!"protocol: {e}"
  | _, .error e => s!"trace: {e}"
  | .ok P, .ok tr =>
    match checkTrace P tr with
    | .ok () => "accepted"
    | .error k => k.describe

/-- The planted bad pair: a committee of four with none declared faulty, and a vote by a node
outside it. -/
@[expose] def badProtocol : Protocol :=
  ⟨[0, 1, 2, 3], 1, fun _ => false, by decide, by decide, by decide⟩

@[expose] def badTrace : List Msg := [⟨7, 1, .vote, .dummy 1⟩]

-- fixture kept (2026-11-05): consumed by Format.bad_refused
theorem badTrace_refused :
    simplexTraceJudge.check 0 badProtocol badTrace = .refused (.senderUnknown 7) [] := rfl

/-- **The registered format `simplex-trace@1`**: object, the committee and the declared faulty
set; certificate, a node's run as the messages sent in order. -/
def simplexTraceFormat : Obend.Judge.Format where
  name := "simplex-trace"
  version := "1"
  Obj := Protocol
  Cert := List Msg
  judge := simplexTraceJudge
  decodeObj := decodeProtocol
  decodeCert := decodeTrace
  trust := .kernel
  regime := .decidable
  bad := (badProtocol, badTrace)
  badGrade := 0
  bad_refused := ⟨.senderUnknown 7, [], badTrace_refused⟩
  explain := explainTrace

/-! ## Complete checking and authenticated transcripts -/
theorem entryNotarizedB_complete {P : Protocol} {sent : Sent} {k : Nat} {upto : Chain} {e : Entry}
    (h : EntryNotarized P sent k upto e) : entryNotarizedB P sent k upto e = true := by
  cases e <;> simpa [entryNotarizedB, EntryNotarized] using h
theorem chainNotarizedB_complete {P : Protocol} {sent : Sent} {c : Chain}
    (h : ChainNotarized P sent c) : chainNotarizedB P sent c = true := by
  simp only [chainNotarizedB, List.all_eq_true, List.mem_range]
  intro k hk; rw [List.getElem?_eq_getElem hk]; exact entryNotarizedB_complete (h k hk)
theorem voteRuleB_complete {P : Protocol} {sent : Sent} {v : Nat} {t : Target}
    (h : VoteRule P sent v t) : voteRuleB P sent v t = true := by
  cases t with
  | dummy w => simpa [voteRuleB, VoteRule] using h
  | block c =>
    obtain ⟨hv,p,x,rfl,hlen,hchain,hprop⟩ := h
    simpa [voteRuleB, hv, hlen, chainNotarizedB_complete hchain] using hprop
theorem checkStep_complete {P : Protocol} {sent : Sent} {m : Msg}
    (h : Step P sent (m::sent)) : checkStep P sent m = .ok () := by
  cases h with
  | inject _ hf => simp [checkStep, hf]
  | propose n v c hn hl =>
    have hc := List.contains_iff_mem.mpr hn.1
    unfold checkStep
    simp only [hn.2,hc,Bool.false_eq_true,↓reduceIte,Bool.not_true]
    rw [ite_eq_left (beq_iff_eq.mpr hl)]
  | finalize n v c hn hv hnot => simp only [checkStep, hn.2, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem.mpr hn.1, Bool.not_true, hv, decide_eq_true hnot, Bool.true_and]
  | vote n v t hn hfresh hrule =>
    have hnone : sent.find? (isVoteOf n v) = none := by
      apply List.find?_eq_none.mpr
      simpa only [votedAny, List.any_eq_false, isVoteOf] using hfresh
    simp only [checkStep, hn.2, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem.mpr hn.1, Bool.not_true, hnone, voteRuleB_complete hrule]
private theorem checkTraceAux_append (P : Protocol) (a b : List Msg) (sent : Sent)
    (ha : checkTraceAux P sent a = .ok ()) (hb : checkTraceAux P (a.reverse++sent) b = .ok ()) :
    checkTraceAux P sent (a++b) = .ok () := by
  induction a generalizing sent with
  | nil => simpa using hb
  | cons m a ih =>
    cases hs : checkStep P sent m with
    | error e => simp [checkTraceAux, hs] at ha
    | ok u =>
      cases u; simp only [checkTraceAux, hs] at ha
      simp only [List.cons_append, checkTraceAux, hs]
      apply ih _ ha
      simpa [List.reverse_cons, List.append_assoc] using hb
theorem checkTrace_complete {P : Protocol} {tr : List Msg} (h : Reach P tr.reverse) : checkTrace P tr = .ok () := by
  have aux {sent : Sent} (hr : Reach P sent) : checkTraceAux P [] sent.reverse = .ok () := by
    induction hr with
    | nil => rfl
    | @step s s' hr hs ih =>
      have advance (m : Msg) (hc : checkStep P s m = .ok ()) : checkTraceAux P [] (m::s).reverse = .ok () := by
        rw [List.reverse_cons]
        apply checkTraceAux_append P _ _ [] ih
        simp only [List.reverse_reverse,List.append_nil,checkTraceAux,hc]
      cases hs with
      | inject m hf => exact advance m (checkStep_complete (.inject s m hf))
      | propose n v c hn hl => exact advance _ (checkStep_complete (.propose s n v c hn hl))
      | vote n v t hn hf hr => exact advance _ (checkStep_complete (.vote s n v t hn hf hr))
      | finalize n v c hn hv hnot => exact advance _ (checkStep_complete (.finalize s n v c hn hv hnot))
  rw [checkTrace_eq_spec]
  simpa using aux h

/-! ## The run judge: a refusal refutes the run -/

theorem traceVerdict_sound {P : Protocol} {tr : List Msg} (h : traceVerdict P tr = .ok) :
    TraceMeaning P tr :=
  checkTrace_sound (traceVerdict_ok h)

theorem traceVerdict_complete {P : Protocol} {tr : List Msg} (h : TraceMeaning P tr) :
    traceVerdict P tr = .ok := by
  unfold traceVerdict
  rw [checkTrace_complete h]

/-- **A refused trace is not reachable**, whatever the clause: the check is complete, so a
reachable trace would have been accepted. -/
theorem traceVerdict_refutes_trace {P : Protocol} {tr : List Msg} {k : TraceClause}
    {path : List Nat} (h : traceVerdict P tr = .refused k path) : ¬ TraceMeaning P tr := by
  intro hm
  rw [traceVerdict_complete hm] at h
  cases h

/-- A committee is never empty: it has at least `3f+1` members. So `simplexRunJudge`'s fragment is every
run, and its completeness is unconditional. -/
theorem committee_ne_nil (P : Protocol) : P.committee ≠ [] := by
  intro h
  have hsize := P.size
  rw [h, List.length_nil] at hsize
  omega

/-- **The run judge**: the object is the run `(P, tr)` itself and the certificate is empty, so the
claim is `Reach P tr.reverse` for that trace and no other. Every clause refutes
(`traceVerdict_refutes_trace`), and the check is complete on every run (`committee_ne_nil`). -/
instance simplexRunJudge : Obend.Judge (Protocol × List Msg) Unit where
  Clause := TraceClause
  Meaning o _ := TraceMeaning o.1 o.2
  check _ o _ := traceVerdict o.1 o.2
  sound := fun h => traceVerdict_sound h
  refutes _ := true
  refuted := fun h _ _ => traceVerdict_refutes_trace h
  Fragment o := o.1.committee ≠ []
  complete := fun _ ⟨_, hm⟩ => ⟨(), 0, traceVerdict_complete hm⟩
  mono := fun _ _ => rfl

def kindByte : Kind → UInt8 | .propose => 0 | .vote => 1 | .finalize => 2
/-- Every field, including each chain entry and the domain, is length framed. -/
def encodeMsgBytes (tag : List UInt8) (m : Msg) : List UInt8 :=
  encodeFields [tag,leb128 m.sender,leb128 m.view,[kindByte m.kind],encodeTargetBytes m.target]
theorem encodeMsgBytes_injective (tag : List UInt8) {a b : Msg}
    (h : encodeMsgBytes tag a = encodeMsgBytes tag b) : a = b := by
  have h := encodeFields_injective _ _ h
  simp only [List.cons.injEq] at h
  have hs := leb128_injective h.2.1
  have hv := leb128_injective h.2.2.1
  have ht := encodeTargetBytes_injective h.2.2.2.2.1
  have hk : a.kind = b.kind := by
    have hb := h.2.2.2.1
    cases ha : a.kind <;> cases hc : b.kind <;> simp_all [kindByte]
  cases a; cases b; simp_all
def encodeMsgBytesExec (tag : ByteArray) (m : Msg) : ByteArray := ⟨(encodeMsgBytes tag.data.toList m).toArray⟩
theorem encodeMsgBytesExec_toList (tag : ByteArray) (m : Msg) :
    (encodeMsgBytesExec tag m).data.toList = encodeMsgBytes tag.data.toList m := by simp [encodeMsgBytesExec]
abbrev PubKey := Obend.Core.Digest.Digest256
abbrev Sig := Obend.Core.Digest.Digest256
structure SimplexSigScheme where
  verify : PubKey → List UInt8 → Sig → Bool
def EufCmaSecure (P : Protocol) (S : SimplexSigScheme) (keys : Nat → PubKey)
    (authentic : Nat → List UInt8 → Prop) : Prop :=
  ∀ n msg sig, P.honest n → S.verify (keys n) msg sig = true → authentic n msg
/-- A concrete allowlist scheme accepts exactly one authenticated message; the security
predicate is inhabited with both acceptance and rejection, without an empty honest set. -/
theorem eufCmaSecure_inhabited (P : Protocol) (msg : List UInt8) :
    EufCmaSecure P ⟨fun _ m _ => decide (m=msg)⟩ (fun _ => 0) (fun _ m => m=msg) ∧
    (⟨fun _ m _ => decide (m=msg)⟩ : SimplexSigScheme).verify 0 msg 0 = true := by
  exact ⟨fun _ _ _ _ h => of_decide_eq_true h, by simp⟩
structure SignedMsg where
  msg : Msg
  sig : Sig
structure SignedSimplexClaim where
  proto : Protocol
  scheme : SimplexSigScheme
  pubKeys : Nat → PubKey
  domainTag : List UInt8
  targetView : Nat
  targetChain : Chain
def SignedSimplexMeaning (c : SignedSimplexClaim) (tr : List SignedMsg) : Prop :=
  1 ≤ c.targetView ∧ c.targetChain ≠ [] ∧ c.proto.committee ≠ [] ∧
  (∀ sm ∈ tr, c.proto.honest sm.msg.sender →
    c.scheme.verify (c.pubKeys sm.msg.sender) (encodeMsgBytes c.domainTag sm.msg) sm.sig = true) ∧
  Reach c.proto (tr.map SignedMsg.msg).reverse ∧
  NotarizedBlock c.proto (tr.map SignedMsg.msg).reverse c.targetView c.targetChain
inductive SignedSimplexClause where
  | invalidTargetView | emptyTargetChain | emptyCommittee
  | badSignature (idx sender : Nat)
  | protocolViolation (clause : TraceClause)
  | targetNotNotarized
  deriving DecidableEq, Repr
def signedSimplexRefutes : SignedSimplexClause → Bool
  | .invalidTargetView | .emptyTargetChain | .emptyCommittee => true
  | _ => false
def signedSignaturesB (c : SignedSimplexClaim) (tr : List SignedMsg) : Bool :=
  tr.all fun sm => !decide (c.proto.honest sm.msg.sender) ||
    c.scheme.verify (c.pubKeys sm.msg.sender) (encodeMsgBytes c.domainTag sm.msg) sm.sig
private theorem signedSignaturesB_iff (c : SignedSimplexClaim) (tr : List SignedMsg) :
    signedSignaturesB c tr = true ↔ ∀ sm ∈ tr, c.proto.honest sm.msg.sender →
      c.scheme.verify (c.pubKeys sm.msg.sender) (encodeMsgBytes c.domainTag sm.msg) sm.sig = true := by
  simp [signedSignaturesB, List.all_eq_true, Bool.or_eq_true, Decidable.imp_iff_not_or]
def checkSignedSimplex (c : SignedSimplexClaim) (tr : List SignedMsg) : Obend.Judge.Verdict SignedSimplexClause :=
  if c.targetView < 1 then .refused .invalidTargetView []
  else if c.targetChain = [] then .refused .emptyTargetChain []
  else if c.proto.committee = [] then .refused .emptyCommittee []
  else if signedSignaturesB c tr = false then
    match tr.zipIdx |>.find? (fun (sm,_) => decide (c.proto.honest sm.msg.sender) &&
      !c.scheme.verify (c.pubKeys sm.msg.sender) (encodeMsgBytes c.domainTag sm.msg) sm.sig) with
    | some (sm,i) => .refused (.badSignature i sm.msg.sender) []
    | none => .refused (.badSignature tr.length 0) []
  else match checkTrace c.proto (tr.map SignedMsg.msg) with
    | .error k => .refused (.protocolViolation k) []
    | .ok () => if decide (NotarizedBlock c.proto (tr.map SignedMsg.msg).reverse c.targetView c.targetChain)
      then .ok else .refused .targetNotNotarized []
theorem checkSignedSimplex_sound {c : SignedSimplexClaim} {tr : List SignedMsg}
    (h : checkSignedSimplex c tr = .ok) : SignedSimplexMeaning c tr := by
  unfold checkSignedSimplex at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · split at h <;> cases h
  · rename_i hs
    split at h <;> try cases h
    rename_i hc
    split at h <;> try cases h
    rename_i hn
    exact ⟨by omega, by assumption, by assumption,
      (signedSignaturesB_iff c tr).mp (by cases hb : signedSignaturesB c tr <;> simp_all),
      checkTrace_sound hc, of_decide_eq_true hn⟩
theorem checkSignedSimplex_complete {c : SignedSimplexClaim} {tr : List SignedMsg}
    (h : SignedSimplexMeaning c tr) : checkSignedSimplex c tr = .ok := by
  obtain ⟨hv,ht,hp,hs,hr,hn⟩ := h
  simp [checkSignedSimplex, show ¬c.targetView<1 by omega, ht, hp,
    (signedSignaturesB_iff c tr).mpr hs, checkTrace_complete hr, hn]
theorem signedSimplexRefuted {c : SignedSimplexClaim} {tr : List SignedMsg}
    {k : SignedSimplexClause} {p : List Nat} (h : checkSignedSimplex c tr = .refused k p)
    (hk : signedSimplexRefutes k = true) : ∀ tr', ¬SignedSimplexMeaning c tr' := by
  intro tr' hm
  unfold checkSignedSimplex at h
  split at h
  · have hv := hm.1; cases h; omega
  · split at h
    · cases h; exact hm.2.1 (by assumption)
    · split at h
      · cases h; exact hm.2.2.1 (by assumption)
      · split at h
        · split at h <;> cases h <;> cases hk
        · split at h
          · cases h; cases hk
          · split at h <;> cases h <;> cases hk
def SignedSimplexFragment (c : SignedSimplexClaim) : Prop :=
  1 ≤ c.targetView ∧ c.targetChain ≠ [] ∧ c.proto.committee ≠ []
@[instance_reducible] def signedSimplexJudge : Obend.Judge SignedSimplexClaim (List SignedMsg) where
  Clause := SignedSimplexClause
  Meaning := SignedSimplexMeaning
  check _ := checkSignedSimplex
  sound := checkSignedSimplex_sound
  refutes := signedSimplexRefutes
  refuted := signedSimplexRefuted
  Fragment := SignedSimplexFragment
  complete := by intro c _ ⟨tr,ht⟩; exact ⟨tr,0,checkSignedSimplex_complete ht⟩
  mono := by intros; rfl
theorem checkSignedSimplex_euf_cma_authentic {c : SignedSimplexClaim} {tr : List SignedMsg}
    {authentic : Nat → List UInt8 → Prop}
    (secure : EufCmaSecure c.proto c.scheme c.pubKeys authentic) (h : checkSignedSimplex c tr = .ok) :
    ∀ sm ∈ tr, c.proto.honest sm.msg.sender → authentic sm.msg.sender (encodeMsgBytes c.domainTag sm.msg) := by
  intro sm hm hn
  exact secure _ _ _ hn ((checkSignedSimplex_sound h).2.2.2.1 sm hm hn)
theorem checkSignedSimplex_authentic_message {c : SignedSimplexClaim} {tr : List SignedMsg}
    (authentic : Nat → Msg → Prop)
    (secure : EufCmaSecure c.proto c.scheme c.pubKeys
      (fun n bytes => ∃ m, authentic n m ∧ encodeMsgBytes c.domainTag m = bytes))
    (h : checkSignedSimplex c tr = .ok) :
    ∀ sm ∈ tr, c.proto.honest sm.msg.sender → authentic sm.msg.sender sm.msg := by
  intro sm hm hn
  obtain ⟨m,ha,he⟩ := checkSignedSimplex_euf_cma_authentic secure h sm hm hn
  have he := encodeMsgBytes_injective c.domainTag he
  simpa [he] using ha
/-! Sorted array snapshots support repeated binary queries without retaining the trace. -/
def StrictRows {κ ν : Type} [Ord κ] (rows : Array (κ × ν)) : Prop :=
  ∀ i j : Fin rows.size, i.val < j.val → compare rows[i].1 rows[j].1 = .lt
private def searchRows {κ ν : Type} [Ord κ] (rows : Array (κ × ν)) (key : κ) :
    Nat → Nat → Nat → Option ν
  | 0,_,_ => none
  | fuel+1,lo,hi =>
    if h : lo < hi ∧ hi ≤ rows.size then
      let mid := (lo+hi)/2
      have hm : mid < rows.size := by omega
      match compare key rows[mid].1 with
      | .eq => some rows[mid].2
      | .lt => searchRows rows key fuel lo mid
      | .gt => searchRows rows key fuel (mid+1) hi
    else none
private theorem ordered_match_lt {κ ν : Type} [Ord κ] [Std.LawfulEqOrd κ] [Std.TransOrd κ]
    {rows : Array (κ × ν)} (sorted : StrictRows rows) (i j : Fin rows.size)
    (h : compare rows[i].1 rows[j].1 = .lt) : i.val < j.val := by
  by_cases hn : i.val < j.val
  · exact hn
  have hle : j.val ≤ i.val := by omega
  rcases Nat.eq_or_lt_of_le hle with he | hl
  · have he' : j=i := Fin.ext he
    subst j
    simp at h
  · have hh := Std.TransCmp.lt_trans h (sorted j i hl)
    simp at hh
private theorem searchRows_some_iff {κ ν : Type} [Ord κ] [Std.LawfulEqOrd κ] [Std.TransOrd κ]
    (rows : Array (κ × ν)) (sorted : StrictRows rows) (key : κ) (value : ν)
    (fuel lo hi : Nat) (hf : hi-lo ≤ fuel) (hb : hi ≤ rows.size) :
    searchRows rows key fuel lo hi = some value ↔
      ∃ i : Fin rows.size, lo ≤ i.val ∧ i.val < hi ∧ rows[i].1 = key ∧ rows[i].2 = value := by
  induction fuel generalizing lo hi with
  | zero =>
    constructor
    · intro h; cases h
    · rintro ⟨i,hil,hih,_,_⟩; omega
  | succ fuel ih =>
    by_cases hlt : lo < hi
    · let mid := (lo+hi)/2
      have hm : mid < rows.size := by dsimp [mid]; omega
      have hml : lo ≤ mid := by dsimp [mid]; omega
      have hmh : mid < hi := by dsimp [mid]; omega
      let j : Fin rows.size := ⟨mid,hm⟩
      simp only [searchRows,dite_eq_left (And.intro hlt hb)]
      change (match compare key rows[j].1 with
        | .eq => some rows[j].2
        | .lt => searchRows rows key fuel lo mid
        | .gt => searchRows rows key fuel (mid+1) hi) = some value ↔ _
      cases hc : compare key rows[j].1 with
      | eq =>
        have hk : rows[j].1=key := (Std.compare_eq_iff_eq.mp hc).symm
        simp only [Option.some.injEq]
        constructor
        · intro hv; exact ⟨j,hml,hmh,hk,hv⟩
        · rintro ⟨i,_,_,hik,hiv⟩
          have he : i=j := by
            apply Fin.ext
            by_cases hn : i.val = j.val
            · exact hn
            rcases Nat.lt_or_gt_of_ne hn with hij | hji
            · have := sorted i j hij; rw [hik,hk] at this; simp at this
            · have := sorted j i hji; rw [hik,hk] at this; simp at this
          simpa [he] using hiv
      | lt =>
        rw [ih lo mid (by omega) (by omega)]
        constructor
        · rintro ⟨i,hil,him,hik,hiv⟩; exact ⟨i,hil,by omega,hik,hiv⟩
        · rintro ⟨i,hil,hih,hik,hiv⟩
          have hij := ordered_match_lt sorted i j (by rw [hik]; exact hc)
          exact ⟨i,hil,hij,hik,hiv⟩
      | gt =>
        rw [ih (mid+1) hi (by omega) hb]
        constructor
        · rintro ⟨i,hil,him,hik,hiv⟩; exact ⟨i,by omega,him,hik,hiv⟩
        · rintro ⟨i,hil,hih,hik,hiv⟩
          have hji : compare rows[j].1 rows[i].1 = .lt := by
            rw [hik]
            exact Std.OrientedCmp.gt_iff_lt.mp hc
          have hji := ordered_match_lt sorted j i hji
          change mid < i.val at hji
          exact ⟨i,by omega,hih,hik,hiv⟩
    · rw [searchRows,dite_eq_right (by omega : ¬ (lo < hi ∧ hi ≤ rows.size))]
      constructor
      · intro h; cases h
      · rintro ⟨i,hil,hih,_,_⟩; omega
structure SortedIndex (κ ν : Type) [Ord κ] where
  rows : Array (κ × ν)
  strict : StrictRows rows
namespace SortedIndex
def ofTree {κ ν : Type} [Ord κ] [Std.TransOrd κ] (t : Std.TreeMap κ ν) : SortedIndex κ ν :=
  ⟨t.toArray,by
    intro i j hij
    have hs := Std.TreeMap.ordered_keys_toList (t := t)
    have hi : i.val < t.toList.length := by simpa [← Std.TreeMap.toArray_toList] using i.isLt
    have hj : j.val < t.toList.length := by simpa [← Std.TreeMap.toArray_toList] using j.isLt
    simpa [← Std.TreeMap.toArray_toList] using hs.rel_getElem_of_lt hi hj hij⟩
def lookup? {κ ν : Type} [Ord κ] (idx : SortedIndex κ ν) (key : κ) : Option ν :=
  searchRows idx.rows key idx.rows.size 0 idx.rows.size
theorem lookup_ofTree {κ ν : Type} [Ord κ] [Std.LawfulEqOrd κ] [Std.TransOrd κ]
    (t : Std.TreeMap κ ν) (key : κ) : (ofTree t).lookup? key = t[key]? := by
  apply Option.ext
  intro v
  rw [lookup?,searchRows_some_iff _ (ofTree t).strict _ _ _ _ _ (by omega) (by omega)]
  change (∃ i : Fin t.toArray.size, 0 ≤ i.val ∧ i.val < t.toArray.size ∧
    t.toArray[i].1 = key ∧ t.toArray[i].2 = v) ↔ t[key]? = some v
  rw [← Std.TreeMap.mem_toArray_iff_getElem?_eq_some]
  constructor
  · rintro ⟨i,_,_,hk,hv⟩
    have hm := Array.getElem_mem (xs := t.toArray) (i := i.val) i.isLt
    have he : t.toArray[i]=(key,v) := Prod.ext hk hv
    change t.toArray[i.val] = (key,v) at he
    rw [he] at hm
    exact hm
  · intro hm
    obtain ⟨i,hi,he⟩ := Array.getElem_of_mem hm
    exact ⟨⟨i,hi⟩,by omega,hi,congrArg Prod.fst he,congrArg Prod.snd he⟩
end SortedIndex
abbrev QuorumIndex := SortedIndex VoteKey Nat
abbrev VoterViewIndex := SortedIndex VoterViewKey Target
namespace QuorumIndex
def ofSent (P : Protocol) (sent : Sent) : QuorumIndex :=
  SortedIndex.ofTree ((TraceIndex.ofSent P sent).voters.map fun _ voters => voters.size)
def lookupVotes (idx : QuorumIndex) (v : Nat) (t : Target) : Nat :=
  (idx.lookup? (voteKey v t)).getD 0
theorem lookupVotes_ofSent_eq_votesFor (P : Protocol) (sent : Sent) (v : Nat) (t : Target) :
    (ofSent P sent).lookupVotes v t = votesFor P sent v t := by
  rw [← TraceIndex.lookupVotes_eq (TraceIndex.ofSent_simulates P sent) v t]
  unfold lookupVotes ofSent TraceIndex.lookupVotes TraceIndex.lookupVoters
  rw [SortedIndex.lookup_ofTree]
  simp only [Std.TreeMap.getElem?_map,Std.TreeMap.getD_eq_getD_getElem?]
  cases (TraceIndex.ofSent P sent).voters[voteKey v t]? <;> rfl
end QuorumIndex
namespace VoterViewIndex
def ofSent (P : Protocol) (sent : Sent) : VoterViewIndex :=
  SortedIndex.ofTree (TraceIndex.ofSent P sent).prior
def lookupPriorVote? (idx : VoterViewIndex) (n v : Nat) : Option Target := idx.lookup? (n,v)
theorem lookupPriorVote_ofSent (P : Protocol) (sent : Sent) (n v : Nat) :
    (ofSent P sent).lookupPriorVote? n v = (sent.find? (isVoteOf n v)).map Msg.target := by
  rw [lookupPriorVote?,ofSent,SortedIndex.lookup_ofTree]
  exact (TraceIndex.ofSent_simulates P sent).2.2.2.1 n v
end VoterViewIndex
def singleNodeProtocol : Protocol := ⟨[0],0,fun _ => false,by decide,by decide,by decide⟩
def singleNodeChain : Chain := [.block 1 7]
def singleNodeTrace : List Msg := [⟨0,1,.propose,.block singleNodeChain⟩,⟨0,1,.vote,.block singleNodeChain⟩]
example : entryNotarizedB singleNodeProtocol singleNodeTrace.reverse 0 singleNodeChain (.block 1 7) = true := by decide
example : chainNotarizedB singleNodeProtocol singleNodeTrace.reverse singleNodeChain = true := by decide
example : voteRuleB singleNodeProtocol [] 1 (.dummy 1) = true := by decide
example : checkStep singleNodeProtocol [] ⟨0,1,.vote,.dummy 1⟩ = .ok () := rfl
example : checkTraceAux singleNodeProtocol [] singleNodeTrace = .ok () := rfl
def signedSingleNodeClaim : SignedSimplexClaim :=
  ⟨singleNodeProtocol,⟨fun _ _ sig => sig == 0⟩,fun _ => 0,[83,50,67],1,singleNodeChain⟩
example : SignedSimplexFragment signedSingleNodeClaim := by
  unfold SignedSimplexFragment; decide
example : simplexRunJudge.Fragment (singleNodeProtocol, singleNodeTrace) :=
  committee_ne_nil singleNodeProtocol
example : simplexRunJudge.check 0 (singleNodeProtocol, singleNodeTrace) () = .ok := by
  change traceVerdict singleNodeProtocol singleNodeTrace = .ok
  unfold traceVerdict
  rw [checkTrace_eq_spec]
  rfl
example :
    simplexRunJudge.check 0 (badProtocol, badTrace) () = .refused (.senderUnknown 7) [] ∧
    simplexRunJudge.refutes (.senderUnknown 7) = true :=
  ⟨rfl, rfl⟩
example : ¬ TraceMeaning badProtocol badTrace :=
  traceVerdict_refutes_trace (k := .senderUnknown 7) (path := []) rfl
example : checkSignedSimplex signedSingleNodeClaim (singleNodeTrace.map fun m => ⟨m,0⟩) = .ok := by
  unfold checkSignedSimplex
  rw [checkTrace_eq_spec]
  decide
#guard (QuorumIndex.ofSent singleNodeProtocol singleNodeTrace.reverse).lookupVotes 1 (.block singleNodeChain) == 1
#guard (QuorumIndex.ofSent singleNodeProtocol (singleNodeTrace.reverse ++ singleNodeTrace.reverse)).lookupVotes 1 (.block singleNodeChain) == 1
#guard (VoterViewIndex.ofSent singleNodeProtocol singleNodeTrace.reverse).lookupPriorVote? 0 1 == some (.block singleNodeChain)
#guard match checkTraceExec singleNodeProtocol singleNodeTrace with | .ok () => true | _ => false
#guard match checkTraceExec singleNodeProtocol (singleNodeTrace ++ [⟨0,1,.vote,.block singleNodeChain⟩]) with
  | .error (.votedTwice 0 1) => true | _ => false
end Obend.Consensus.SimplexTrace
end
