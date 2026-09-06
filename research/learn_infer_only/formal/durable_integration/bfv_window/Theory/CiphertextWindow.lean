/-
[DERIVED target] Public ciphertext-window transition, independent of any
candidate encryption scheme. Ciphertexts form an additive commutative group;
canonical serialization is a lawful codec. Neither plaintexts nor secret keys
occur here. Root digests are deliberately absent from this algebra layer.

Statement-first: from the empty state, every checked transition preserves the
exact current queue sum, length bound and admission/current-id provenance.
External expiry proposals must name the current oldest entry and its exact
canonical ciphertext bytes. The codec round-trip law turns that byte equality
into the group equality actually needed by subtraction.
-/
import Theory.IndexedProgram
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace Minidregg.Theory.CiphertextWindow
open Minidregg.Theory.IndexedProgram
set_option autoImplicit false

structure Entry (Ct : Type) where
  admissionId : Nat
  ciphertext : Ct
  deriving DecidableEq
structure State (Ct : Type) where
  queue : List (Entry Ct)
  accumulator : Ct
  nextId : Nat
  deriving DecidableEq
structure Command (Ct : Type) where
  fresh : Entry Ct
  expiry : Option (Entry Ct)
  deriving DecidableEq

variable {Ct : Type} [AddCommGroup Ct]

def queueSum (q : List (Entry Ct)) : Ct := (q.map Entry.ciphertext).sum

def SumBound (W : Nat) (s : State Ct) : Prop :=
  s.accumulator=queueSum s.queue ∧ s.queue.length≤W

def Admitted (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool) (e : Entry Ct) : Prop :=
  admit e.admissionId (codec.encode e.ciphertext)=true

def Provenance (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool) (s : State Ct) : Prop :=
  (∀ e∈s.queue,Admitted codec admit e ∧ e.admissionId<s.nextId) ∧
  (s.queue.map Entry.admissionId).Nodup

def initial : State Ct := ⟨[],0,0⟩

/-- This compares canonical ciphertext bytes, never equal plaintexts or roots. -/
def sameSerialized (codec : LawfulCodec Ct) (old proposed : Entry Ct) : Bool :=
  decide (proposed.admissionId=old.admissionId ∧
    codec.encode proposed.ciphertext=codec.encode old.ciphertext)

omit [AddCommGroup Ct] in
theorem sameSerialized_eq (codec : LawfulCodec Ct) (old proposed : Entry Ct)
    (h : sameSerialized codec old proposed=true) : proposed=old := by
  simp only [sameSerialized,decide_eq_true_eq] at h
  have hc := congrArg codec.decode h.2
  rw [codec.decode_encode,codec.decode_encode] at hc
  cases old; cases proposed
  simp only [Entry.mk.injEq]
  exact ⟨h.1,Option.some.inj hc⟩

def check (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct) : Bool :=
  decide (0<W ∧ s.queue.length≤W ∧ cmd.fresh.admissionId=s.nextId) &&
  admit cmd.fresh.admissionId (codec.encode cmd.fresh.ciphertext) &&
  (if s.queue.length<W then cmd.expiry.isNone else
    match s.queue,cmd.expiry with
    | old::_,some proposed => sameSerialized codec old proposed
    | _,_ => false)

/-- The candidate expiry is what is subtracted; its equality to the stored
head is a checked semantic obligation, not an implicit trusted assertion. -/
def advance (W : Nat) (s : State Ct) (cmd : Command Ct) : State Ct :=
  if s.queue.length<W then
    ⟨s.queue++[cmd.fresh],s.accumulator+cmd.fresh.ciphertext,s.nextId+1⟩
  else match s.queue,cmd.expiry with
    | _::rest,some proposed =>
      ⟨rest++[cmd.fresh],s.accumulator+cmd.fresh.ciphertext-proposed.ciphertext,s.nextId+1⟩
    | _,_ => s

def step (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct) : Option (State Ct) :=
  if check codec admit W s cmd then some (advance W s cmd) else none

omit [AddCommGroup Ct] in
/-- A checked step has exactly one of the two intended queue layouts. -/
theorem checked_cases (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct)
    (h : check codec admit W s cmd=true) :
    0<W ∧ cmd.fresh.admissionId=s.nextId ∧ Admitted codec admit cmd.fresh ∧
    ((s.queue.length<W ∧ cmd.expiry=none) ∨
      ∃ old rest,s.queue=old::rest ∧ s.queue.length=W ∧ cmd.expiry=some old) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hw,hbound,hid⟩,ha⟩,hl⟩ := h
  refine ⟨hw,hid,ha,?_⟩
  by_cases hlen : s.queue.length<W
  · left
    refine ⟨hlen,?_⟩
    simpa only [if_pos hlen,Option.isNone_iff_eq_none] using hl
  · right
    simp only [if_neg hlen] at hl
    cases hq : s.queue with
    | nil => simp only [hq] at hl; contradiction
    | cons old rest =>
      cases he : cmd.expiry with
      | none => simp only [hq,he] at hl; contradiction
      | some proposed =>
        rw [hq,he] at hl
        have same := sameSerialized_eq codec old proposed hl
        exact ⟨old,rest,rfl,by have hlenq := congrArg List.length hq;omega,congrArg some same⟩

theorem checked_sum_bound (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct)
    (h : check codec admit W s cmd=true) (before : SumBound W s) :
    SumBound W (advance W s cmd) := by
  obtain ⟨_,_,_,cases⟩ := checked_cases codec admit W s cmd h
  rcases cases with ⟨hlen,he⟩ | ⟨old,rest,hq,hlen,he⟩
  · simp only [advance,if_pos hlen,SumBound]
    constructor
    · simp [queueSum,before.1]
    · simp only [List.length_append,List.length_singleton];omega
  · have notlt : ¬s.queue.length<W := by omega
    unfold advance
    rw [if_neg notlt]
    simp only [hq,he,SumBound]
    constructor
    · have hb := before.1
      rw [hq] at hb
      simp only [queueSum,List.map_cons,List.sum_cons] at hb
      simp only [queueSum,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
      rw [hb]
      abel
    · have size := congrArg List.length hq
      simp only [List.length_cons] at size
      simp only [List.length_append,List.length_singleton]
      omega

theorem checked_provenance (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct)
    (h : check codec admit W s cmd=true) (before : Provenance codec admit s) :
    Provenance codec admit (advance W s cmd) := by
  obtain ⟨_,hid,ha,cases⟩ := checked_cases codec admit W s cmd h
  have fresh : cmd.fresh.admissionId∉s.queue.map Entry.admissionId := by
    intro hm
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hm
    have hl := (before.1 e he).2
    omega
  rcases cases with ⟨hlen,he⟩ | ⟨old,rest,hq,hlen,he⟩
  · simp only [advance,if_pos hlen,Provenance]
    constructor
    · intro e hm
      simp only [List.mem_append,List.mem_singleton] at hm
      rcases hm with hm|rfl
      · exact ⟨(before.1 e hm).1,by have := (before.1 e hm).2;omega⟩
      · exact ⟨ha,by omega⟩
    · simp only [List.map_append,List.map_singleton]
      exact List.nodup_append.mpr ⟨before.2,by simp,by simpa using fresh⟩
  · have notlt : ¬s.queue.length<W := by omega
    unfold advance
    rw [if_neg notlt]
    simp only [hq,he,Provenance]
    have hr : (rest.map Entry.admissionId).Nodup := by
      have hn : (old.admissionId::rest.map Entry.admissionId).Nodup := by
        simpa only [hq,List.map_cons] using before.2
      exact (List.nodup_cons.mp hn).2
    constructor
    · intro e hm
      simp only [List.mem_append,List.mem_singleton] at hm
      rcases hm with hm|rfl
      · have hb := before.1 e (by simp [hq,hm])
        exact ⟨hb.1,by omega⟩
      · exact ⟨ha,by omega⟩
    · simp only [List.map_append,List.map_singleton]
      apply List.nodup_append.mpr
      refine ⟨hr,by simp,?_⟩
      have hf : cmd.fresh.admissionId∉rest.map Entry.admissionId := by
        intro hm;apply fresh;simp [hq,hm]
      simpa using hf



theorem checked_next_id (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct) (h : check codec admit W s cmd=true) :
    (advance W s cmd).nextId=s.nextId+1 := by
  obtain ⟨_,_,_,cases⟩ := checked_cases codec admit W s cmd h
  rcases cases with ⟨hlen,_⟩ | ⟨old,rest,hq,hlen,he⟩
  · simp only [advance,if_pos hlen]
  · have notlt : ¬s.queue.length<W := by omega
    unfold advance
    rw [if_neg notlt]
    simp only [hq,he]

omit [AddCommGroup Ct] in
/-- A proposal naming a different current ciphertext cannot pass, even if
its plaintext (under some separate interpretation) might be the same. -/
theorem different_serialized_expiry_refused (codec : LawfulCodec Ct)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (s : State Ct) (cmd : Command Ct)
    (old proposed : Entry Ct) (rest : List (Entry Ct))
    (hq : s.queue=old::rest) (full : s.queue.length=W) (he : cmd.expiry=some proposed)
    (different : codec.encode proposed.ciphertext≠codec.encode old.ciphertext) :
    check codec admit W s cmd=false := by
  have notlt : ¬s.queue.length<W := by omega
  unfold check
  rw [if_neg notlt,hq,he]
  simp [sameSerialized,different]

omit [AddCommGroup Ct] in
theorem stale_expiry_id_refused (codec : LawfulCodec Ct)
    (admit : Nat → List UInt8 → Bool) (W : Nat) (s : State Ct) (cmd : Command Ct)
    (old proposed : Entry Ct) (rest : List (Entry Ct))
    (hq : s.queue=old::rest) (full : s.queue.length=W) (he : cmd.expiry=some proposed)
    (stale : proposed.admissionId≠old.admissionId) : check codec admit W s cmd=false := by
  have notlt : ¬s.queue.length<W := by omega
  unfold check
  rw [if_neg notlt,hq,he]
  simp [sameSerialized,stale]

omit [AddCommGroup Ct] in
theorem stale_fresh_id_refused (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct) (stale : cmd.fresh.admissionId≠s.nextId) :
    check codec admit W s cmd=false := by simp [check,stale]

/-- The algebraic debt from bypassing exact expiry is explicit. No map from
the finite ciphertext group into the integers is assumed. -/
theorem replacement_debt (W : Nat) (s : State Ct) (cmd : Command Ct)
    (old proposed : Entry Ct) (rest : List (Entry Ct))
    (hq : s.queue=old::rest) (full : s.queue.length=W) (he : cmd.expiry=some proposed)
    (sum : s.accumulator=queueSum s.queue) :
    (advance W s cmd).accumulator=queueSum (advance W s cmd).queue+
      (old.ciphertext-proposed.ciphertext) := by
  have notlt : ¬s.queue.length<W := by omega
  unfold advance
  rw [if_neg notlt]
  simp only [hq,he]
  rw [hq] at sum
  simp only [queueSum,List.map_cons,List.sum_cons] at sum
  simp only [queueSum,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
  rw [sum]
  abel

theorem bypassed_wrong_ciphertext_breaks_sum (W : Nat) (s : State Ct) (cmd : Command Ct)
    (old proposed : Entry Ct) (rest : List (Entry Ct))
    (hq : s.queue=old::rest) (full : s.queue.length=W) (he : cmd.expiry=some proposed)
    (sum : s.accumulator=queueSum s.queue) (different : old.ciphertext≠proposed.ciphertext) :
    (advance W s cmd).accumulator≠queueSum (advance W s cmd).queue := by
  rw [replacement_debt W s cmd old proposed rest hq full he sum]
  intro heq
  apply different
  apply sub_eq_zero.mp
  exact add_left_cancel (heq.trans (add_zero _).symm)

theorem step_eq_some_iff (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (cmd : Command Ct) (after : State Ct) :
    step codec admit W s cmd=some after ↔
      check codec admit W s cmd=true ∧ advance W s cmd=after := by
  unfold step
  cases h : check codec admit W s cmd <;> simp

/-- Reachability is generated by actual checked steps, not arbitrary mutable
log/head/state fields. No finite upper bound on the number of steps occurs. -/
inductive Reachable (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool) (W : Nat) : State Ct → Prop
  | start : Reachable codec admit W initial
  | next {before : State Ct} (past : Reachable codec admit W before)
      (cmd : Command Ct) (checked : check codec admit W before cmd=true) :
      Reachable codec admit W (advance W before cmd)


/-- The executable Option-returning transition, not only its relation,
generates the same reachable-state carrier. -/
theorem reachable_after_step (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (before after : State Ct) (cmd : Command Ct)
    (past : Reachable codec admit W before) (h : step codec admit W before cmd=some after) :
    Reachable codec admit W after := by
  obtain ⟨checked,same⟩ := (step_eq_some_iff codec admit W before cmd after).mp h
  rw [←same]
  exact .next past cmd checked

def WindowInvariant (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool) (W : Nat) : Prop :=
  ∀ s,Reachable codec admit W s → SumBound W s ∧ Provenance codec admit s

theorem window_invariant (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool) (W : Nat) :
    WindowInvariant codec admit W := by
  intro s reached
  induction reached with
  | start => simp [initial,SumBound,queueSum,Provenance]
  | next past cmd checked ih =>
    exact ⟨checked_sum_bound codec admit W _ cmd checked ih.1,
      checked_provenance codec admit W _ cmd checked ih.2⟩

theorem reachable_queue_sum (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (reached : Reachable codec admit W s) :
    s.accumulator=(s.queue.map Entry.ciphertext).sum ∧ s.queue.length≤W :=
  (window_invariant codec admit W s reached).1


/-- The actual oldest entry is the canonical expiry proposal. Supplying a new
admitted ciphertext therefore leaves a usable next transition at every horizon. -/
def continuation (W : Nat) (s : State Ct) (ciphertext : Ct) : Command Ct :=
  ⟨⟨s.nextId,ciphertext⟩,if s.queue.length<W then none else s.queue.head?⟩

omit [AddCommGroup Ct] in
theorem admitted_continuation (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (s : State Ct) (ciphertext : Ct) (hw : 0<W) (hb : s.queue.length≤W)
    (ha : admit s.nextId (codec.encode ciphertext)=true) :
    check codec admit W s (continuation W s ciphertext)=true := by
  unfold check continuation
  simp only [ha,Bool.and_true]
  rw [decide_eq_true (show 0<W ∧ s.queue.length≤W ∧ True from ⟨hw,hb,True.intro⟩)]
  simp only [Bool.true_and]
  by_cases hlen : s.queue.length<W
  · simp [hlen]
  · rw [if_neg hlen,if_neg hlen]
    cases hq : s.queue with
    | nil => simp only [hq,List.length_nil] at hlen;omega
    | cons old rest => simp [sameSerialized]

/-- A supplied admitted input stream yields checked transitions for any
finite horizon. Inputs are indexed by the current monotone admission counter. -/
def run (W : Nat) (input : Nat → Ct) : Nat → State Ct
  | 0 => initial
  | n+1 =>
    let s:=run W input n
    advance W s (continuation W s (input s.nextId))

theorem run_reachable (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (input : Nat → Ct) (hw : 0<W)
    (admitted : ∀ id,admit id (codec.encode (input id))=true) (n : Nat) :
    Reachable codec admit W (run W input n) := by
  induction n with
  | zero => exact .start
  | succ n ih =>
    have hb := (window_invariant codec admit W _ ih).1.2
    exact .next ih _ (admitted_continuation codec admit W _ _ hw hb (admitted _))

theorem all_finite_horizons (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (W : Nat) (input : Nat → Ct) (hw : 0<W)
    (admitted : ∀ id,admit id (codec.encode (input id))=true) (n : Nat) :
    (run W input n).accumulator=((run W input n).queue.map Entry.ciphertext).sum ∧
    (run W input n).queue.length≤W ∧ Provenance codec admit (run W input n) := by
  have h := window_invariant codec admit W _ (run_reachable codec admit W input hw admitted n)
  exact ⟨h.1.1,h.1.2,h.2⟩

/-- info: 'Minidregg.Theory.CiphertextWindow.sameSerialized_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms sameSerialized_eq
/-- info: 'Minidregg.Theory.CiphertextWindow.checked_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_cases
/-- info: 'Minidregg.Theory.CiphertextWindow.checked_sum_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_sum_bound
/-- info: 'Minidregg.Theory.CiphertextWindow.checked_provenance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_provenance
/-- info: 'Minidregg.Theory.CiphertextWindow.checked_next_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_next_id
/-- info: 'Minidregg.Theory.CiphertextWindow.different_serialized_expiry_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms different_serialized_expiry_refused
/-- info: 'Minidregg.Theory.CiphertextWindow.stale_expiry_id_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stale_expiry_id_refused
/-- info: 'Minidregg.Theory.CiphertextWindow.stale_fresh_id_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms stale_fresh_id_refused
/-- info: 'Minidregg.Theory.CiphertextWindow.replacement_debt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replacement_debt
/-- info: 'Minidregg.Theory.CiphertextWindow.bypassed_wrong_ciphertext_breaks_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bypassed_wrong_ciphertext_breaks_sum
/-- info: 'Minidregg.Theory.CiphertextWindow.step_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms step_eq_some_iff
/-- info: 'Minidregg.Theory.CiphertextWindow.reachable_after_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms reachable_after_step
/-- info: 'Minidregg.Theory.CiphertextWindow.window_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms window_invariant
/-- info: 'Minidregg.Theory.CiphertextWindow.reachable_queue_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reachable_queue_sum
/-- info: 'Minidregg.Theory.CiphertextWindow.admitted_continuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms admitted_continuation
/-- info: 'Minidregg.Theory.CiphertextWindow.run_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_reachable
/-- info: 'Minidregg.Theory.CiphertextWindow.all_finite_horizons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms all_finite_horizons

end Minidregg.Theory.CiphertextWindow
