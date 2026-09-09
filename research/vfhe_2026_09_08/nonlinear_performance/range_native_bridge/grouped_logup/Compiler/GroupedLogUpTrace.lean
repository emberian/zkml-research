/- Source-shaped global LogUp gates: exclusive prefix, transition rows, final
row, and the final sum of cumulative values. Auxiliary traces and cumulative
values are arbitrary; they may depend on both sampled lookup challenges. -/
import Compiler.LogUpGrouping

namespace Minidregg.Compiler.GroupedLogUpTrace
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
variable {F : Type*} [Field F]

def rowSum (last : Nat) (f : Nat → F) : F := ∑ r ∈ Finset.range (last+1), f r

def Gates4 (last : Nat) (m d : Nat → Fin 4 → F) (s : Nat → F) (c : F) : Prop :=
  s 0 = 0 ∧
  (∀ r < last, LogUpGrouping.Transition (s r) (s (r+1)) (m r) (d r)) ∧
  LogUpGrouping.Transition (s last) c (m last) (d last)

def Gates1 (last : Nat) (m d s : Nat → F) (c : F) : Prop :=
  s 0 = 0 ∧
  (∀ r < last, (s (r+1)-s r)*d r=m r) ∧
  (c-s last)*d last=m last

def Nonzero4 (last : Nat) (d : Nat → Fin 4 → F) : Prop :=
  ∀ r ≤ last, ∀ i, d r i ≠ 0

def Nonzero1 (last : Nat) (d : Nat → F) : Prop := ∀ r ≤ last, d r ≠ 0

def Sound : Prop := ∀ (last : Nat) (m d : Nat → Fin 4 → F) (s : Nat → F) (c : F),
  Gates4 last m d s c → Nonzero4 last d →
  c = rowSum last (fun r => LogUpGrouping.fractions (m r) (d r))

/-- Fixed-four grouping with any source-selected number of columns, and one
negative receiver on the sixteen nibble-table rows. `recvM` is the receiver
multiplicity before the source receive operation negates it. -/
def NativeByteSoundGeneral (groups : Nat) : Prop := ∀ (last : Nat)
    (sendD : Fin groups → Nat → Fin 4 → F)
    (sendS : Fin groups → Nat → F) (sendC : Fin groups → F)
    (recvM recvD recvS : Nat → F) (recvC : F),
  (∀ g, Gates4 last (fun _ _ => 1) (sendD g) (sendS g) (sendC g)) →
  (∀ g, Nonzero4 last (sendD g)) →
  Gates1 15 (fun r => -recvM r) recvD recvS recvC → Nonzero1 15 recvD →
  (∑ g, sendC g) + recvC = 0 →
  (∑ g, rowSum last (fun r => LogUpGrouping.fractions (fun _ => 1) (sendD g r))) +
    rowSum 15 (fun r => -recvM r / recvD r) = 0

/-- The MAC specialization has 524 unit sends in 131 groups. -/
def NativeByteSound : Prop := @NativeByteSoundGeneral F _ 131

theorem telescope (n : Nat) (s f : Nat → F)
    (h : ∀ r < n, s (r+1)-s r=f r) :
    s n-s 0 = ∑ r ∈ Finset.range n, f r := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun r hr => h r (by omega))
    have hn := h n (by omega)
    rw [Finset.sum_range_succ]
    linear_combination hp + hn

theorem inclusive_sum (last : Nat) (s f : Nat → F) (c : F)
    (h0 : s 0 = 0) (ht : ∀ r < last, s (r+1)-s r=f r)
    (hf : c-s last=f last) : c=rowSum last f := by
  have hp := telescope last s f ht
  rw [h0, sub_zero] at hp
  unfold rowSum
  rw [Finset.sum_range_succ]
  linear_combination hp + hf

theorem sound : @Sound F _ := by
  intro last m d s c h hd
  apply inclusive_sum last s _ c h.1
  · intro r hr
    exact (LogUpGrouping.transition_iff _ _ _ _ (hd r (by omega))).mp (h.2.1 r hr)
  · exact (LogUpGrouping.transition_iff _ _ _ _ (hd last le_rfl)).mp h.2.2

theorem single_sound (last : Nat) (m d s : Nat → F) (c : F)
    (h : Gates1 last m d s c) (hd : Nonzero1 last d) :
    c=rowSum last (fun r => m r/d r) := by
  apply inclusive_sum last s _ c h.1
  · intro r hr
    exact (eq_div_iff (hd r (by omega))).mpr (h.2.1 r hr)
  · exact (eq_div_iff (hd last le_rfl)).mpr h.2.2

theorem native_byte_sound_general (groups : Nat) : @NativeByteSoundGeneral F _ groups := by
  intro last sendD sendS sendC recvM recvD recvS recvC hs hd hr hdr hg
  have hsend : (∑ g, sendC g) =
      ∑ g, rowSum last (fun r => LogUpGrouping.fractions (fun _ => 1) (sendD g r)) := by
    apply Finset.sum_congr rfl
    intro g _
    exact sound last _ _ _ _ (hs g) (hd g)
  rw [←hsend, ←single_sound 15 _ _ _ _ hr hdr]
  exact hg

theorem native_byte_sound : @NativeByteSound F _ := native_byte_sound_general 131

/-- This pointwise theorem quantifies over an arbitrary trace-producing function
of the sampled challenges. No pre-challenge fixation of the auxiliary trace is
used or required by telescoping. -/
theorem adaptive_trace (last : Nat) (m d : F → F → Nat → Fin 4 → F)
    (s : F → F → Nat → F) (c : F → F → F) (alpha beta : F)
    (h : Gates4 last (m alpha beta) (d alpha beta) (s alpha beta) (c alpha beta))
    (hd : Nonzero4 last (d alpha beta)) :
    c alpha beta = rowSum last (fun r =>
      LogUpGrouping.fractions (m alpha beta r) (d alpha beta r)) :=
  sound last _ _ _ _ h hd

def unitFour : Nat → Fin 4 → ℚ := fun _ i => if i=0 then 1 else 0
def positivePrefix (r : Nat) : ℚ := r
def negativePrefix (r : Nat) : ℚ := -(r : ℚ)

def SignedWitness : Prop :=
  Gates4 1 unitFour (fun _ _ => 1) positivePrefix 2 ∧
  Nonzero4 1 (fun _ _ => (1 : ℚ)) ∧
  Gates1 1 (fun _ => -1) (fun _ => 1) negativePrefix (-2) ∧
  Nonzero1 1 (fun _ => (1 : ℚ)) ∧
  (2 : ℚ)+(-2)=0 ∧ (2 : ℚ)≠0

theorem signedWitness : SignedWitness := by
  dsimp [SignedWitness,Gates4,Gates1,Nonzero4,Nonzero1,
    LogUpGrouping.Transition,LogUpGrouping.denominator,LogUpGrouping.numerator,
    unitFour,positivePrefix,negativePrefix]
  norm_num

theorem premiseInhabited : ∃ (m d : Nat → Fin 4 → ℚ) (s : Nat → ℚ) (c : ℚ),
    Gates4 1 m d s c ∧ Nonzero4 1 d ∧ c≠0 := by
  exact ⟨unitFour,fun _ _ => 1,positivePrefix,2,
    signedWitness.1,signedWitness.2.1,signedWitness.2.2.2.2.2⟩

def MissingTerminalFalsifier : Prop :=
  (positivePrefix 0=0 ∧
    ∀ r<1,LogUpGrouping.Transition (positivePrefix r) (positivePrefix (r+1))
      (unitFour r) (fun _ => 1)) ∧
  ¬Gates4 1 unitFour (fun _ _ => 1) positivePrefix 0 ∧
  ¬(0 : ℚ)=rowSum 1 (fun r => LogUpGrouping.fractions (unitFour r) (fun _ => 1))

theorem missingTerminalFalsifier : MissingTerminalFalsifier := by
  dsimp [MissingTerminalFalsifier,Gates4,positivePrefix,unitFour,
    LogUpGrouping.Transition,LogUpGrouping.denominator,LogUpGrouping.numerator,
    LogUpGrouping.fractions,rowSum]
  norm_num [Finset.sum_range_succ]

def MissingGlobalFalsifier : Prop :=
  Gates4 1 unitFour (fun _ _ => 1) positivePrefix 2 ∧
  Gates1 1 (fun _ => (0 : ℚ)) (fun _ => 1) (fun _ => 0) 0 ∧
  ¬(rowSum 1 (fun r => LogUpGrouping.fractions (unitFour r) (fun _ => 1)) +
    rowSum 1 (fun _ => (0 : ℚ)/(1 : ℚ)) = 0)

theorem missingGlobalFalsifier : MissingGlobalFalsifier := by
  refine ⟨signedWitness.1,?_,?_⟩
  · norm_num [Gates1]
  · have hs := sound 1 unitFour (fun _ _ => 1) positivePrefix 2
      signedWitness.1 signedWitness.2.1
    rw [←hs]
    norm_num [rowSum]

def nativeRecvM (r : Nat) : ℚ := if r=0 then 524 else 0
def nativeRecvS (r : Nat) : ℚ := if r=0 then 0 else -524

/-- Inhabitation of all 131 unit-send columns and the full sixteen-row signed
receiver, with nonzero cumulative values. Denominators are arbitrary resolved
field values in this trace-only theorem; tuple semantics is a later bridge. -/
def NativePremise : Prop :=
  (∀ _g : Fin 131, Gates4 0 (fun _ _ => (1 : ℚ)) (fun _ _ => 1) (fun _ => 0) 4) ∧
  (∀ _g : Fin 131, Nonzero4 0 (fun _ _ => (1 : ℚ))) ∧
  Gates1 15 (fun r => -nativeRecvM r) (fun _ => 1) nativeRecvS (-524) ∧
  Nonzero1 15 (fun _ => (1 : ℚ)) ∧
  (∑ _g : Fin 131, (4 : ℚ)) + (-524) = 0 ∧ (4 : ℚ) ≠ 0

theorem nativePremise : NativePremise := by
  refine ⟨?_,?_,?_,?_,?_,by decide⟩
  · intro g
    norm_num [Gates4,LogUpGrouping.Transition,LogUpGrouping.numerator,LogUpGrouping.denominator]
  · intro g r hr i
    norm_num
  · refine ⟨rfl,?_,by norm_num [nativeRecvM,nativeRecvS]⟩
    intro r hr
    by_cases hz : r=0
    · subst r
      norm_num [nativeRecvM,nativeRecvS]
    · simp [nativeRecvM,nativeRecvS,hz]
  · intro r hr
    norm_num
  · norm_num

end Minidregg.Compiler.GroupedLogUpTrace

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.telescope

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.inclusive_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.inclusive_sum

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.sound

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.single_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.single_sound

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.native_byte_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.native_byte_sound

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.adaptive_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.adaptive_trace

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.signedWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.signedWitness

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.premiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.premiseInhabited

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.missingTerminalFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.missingTerminalFalsifier

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.missingGlobalFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.missingGlobalFalsifier

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.nativePremise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.nativePremise

/-- info: 'Minidregg.Compiler.GroupedLogUpTrace.native_byte_sound_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedLogUpTrace.native_byte_sound_general
