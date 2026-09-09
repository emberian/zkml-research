/- The native grouped lookup gates imply field histogram conservation or a
priced fresh-coin event. Main keys and receive multiplicities are fixed here;
the existential permutation witnesses are chosen after the lookup coins. -/
import Compiler.GroupedByteFractions
import Compiler.NativeRangeKeyswitch
namespace Minidregg.Compiler.NativeByteExtraction
open Minidregg.Compiler Minidregg.Selvage
open Minidregg.Selvage.BabyBearExt4 (Ext4)
open Minidregg.Compiler.ByteLogUpDefect
open Minidregg.Compiler.GroupedLogUpTrace
open Minidregg.Compiler.GroupedByteFractions
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

def Accepted (groups last : Nat) (keys : Fin groups → Nat → Fin 4 → BabyBear)
    (m : Nat → Nat) (α : Ext4) : Prop :=
  ∃ (sendS : Fin groups → Nat → Ext4) (sendC : Fin groups → Ext4)
    (recvS : Nat → Ext4) (recvC : Ext4),
    (∀ g,Gates4 last (fun _ _ => 1)
      (fun r i => α-embed (keys g r i)) (sendS g) (sendC g)) ∧
    Gates1 15 (fun r => -(m r : Ext4)) (fun r => α-embed (r : BabyBear)) recvS recvC ∧
    (∑ g,sendC g)+recvC=0

def Sound : Prop := ∀ groups last keys m α,Accepted groups last keys m α →
  NativeNibbleBus.ExactField (sendListN groups last keys) m ∨ Bad (sendListN groups last keys) m α

theorem denom_of_nopole (sends : List BabyBear) (α : Ext4) (hp : ¬Pole sends α)
    (x : BabyBear) (hx : x∈support sends) : α-embed x≠0 := by
  intro hz
  exact hp ⟨⟨x,hx⟩,hz⟩

theorem accepted_rational (groups last : Nat) (keys : Fin groups → Nat → Fin 4 → BabyBear)
    (m : Nat → Nat) (α : Ext4) (ha : Accepted groups last keys m α)
    (hp : ¬Pole (sendListN groups last keys) α) :
    rational (sendListN groups last keys) α=rational (NativeNibbleBus.receives m) α := by
  obtain ⟨ss,sc,rs,rc,hg,hr,ht⟩ := ha
  have hd : ∀ g,Nonzero4 last (fun r i => α-embed (keys g r i)) := by
    intro g r hrl i
    exact denom_of_nopole _ α hp _
      (Finset.mem_union_left _ (List.mem_toFinset.mpr (mem_sendListN groups last keys g r hrl i)))
  have hdr : Nonzero1 15 (fun r => α-embed (r : BabyBear)) := by
    intro r hrl
    apply denom_of_nopole _ α hp
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨r,Finset.mem_range.mpr (by omega),rfl⟩
  have hbal := native_byte_sound_general groups last (fun g r i => α-embed (keys g r i)) ss sc
    (fun r => (m r : Ext4)) (fun r => α-embed (r : BabyBear)) rs rc hg hd hr hdr ht
  rw [send_rationalN,receive_rational]
  have hn : rowSum 15 (fun r => -(m r : Ext4)/(α-embed (r : BabyBear))) =
      -rowSum 15 (fun r => (m r : Ext4)/(α-embed (r : BabyBear))) := by
    simp [rowSum,neg_div]
  rw [hn] at hbal
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hbal)

theorem sound : Sound := by
  intro groups last keys m α ha
  by_cases hp : Pole (sendListN groups last keys) α
  · exact Or.inr (Or.inl hp)
  · exact ByteLogUpDefect.sound _ m α (accepted_rational groups last keys m α ha hp)

/-- Arbitrary existential permutation traces may be selected after both fresh
coins. The main keys and table multiplicities outside the event stay fixed. -/
theorem false_accept_probability (groups last : Nat) (keys : Fin groups → Nat → Fin 4 → BabyBear)
    (m : Nat → Nat) (hfalse : ¬NativeNibbleBus.ExactField (sendListN groups last keys) m) :
    uniformProb (Ext4×Ext4) (fun coins => Accepted groups last keys m coins.2) ≤
      (2*((sendListN groups last keys).length : ℝ)+31)/(2013265921 : ℝ)^4 := by
  have hprice := fresh_pair_length_bound (sendListN groups last keys) m
  have hsub : uniformProb (Ext4×Ext4) (fun coins => Accepted groups last keys m coins.2) ≤
      uniformProb (Ext4×Ext4) (fun coins =>
        TupleCollision coins.1 ∨ Bad (sendListN groups last keys) m coins.2) := by
    apply uniformProb_mono
    intro coins ha
    exact Or.inr ((sound groups last keys m coins.2 ha).resolve_left hfalse)
  exact le_trans hsub hprice

theorem exact_perm (xs ys : List BabyBear) (m : Nat → Nat) (hxy : xs.Perm ys)
    (h : NativeNibbleBus.ExactField xs m) : NativeNibbleBus.ExactField ys m := by
  intro x
  rw [←hxy.count_eq x]
  exact h x

/-- All source rows, including the terminal row, obtain their range premise
from the actual grouped gates or expose the named fresh-coin failure event.
The permutation equality is the explicit binding to compiler-declared sends;
it does not assume any histogram equality with the receiver. -/
theorem allRowsRanges_or_bad {n : Nat} (groups last : Nat)
    (keys : Fin groups → Nat → Fin 4 → BabyBear) (m : Nat → Nat) (α : Ext4)
    (trace : Fin n → RangeKeyswitchRow.Idx → BabyBear)
    (aux : Fin n → NativeRangeKeyswitch.Aux)
    (ha : Accepted groups last keys m α)
    (binding : (sendListN groups last keys).Perm (NativeRangeKeyswitch.allSends aux))
    (he : ∀ row,NativeRangeKeyswitch.Local (trace row) (aux row))
    (hn : n≤131072) :
    (∀ row,RangeKeyswitchRow.RangeHolds (trace row)) ∨ Bad (sendListN groups last keys) m α := by
  rcases sound groups last keys m α ha with hc | hb
  · left
    have hex := exact_perm _ _ m binding hc
    intro row
    apply NativeRangeKeyswitch.local_ranges (trace row) (aux row) (he row)
    intro x hx
    apply NativeNibbleBus.field_sound (NativeRangeKeyswitch.allSends aux) m hex
      (NativeRangeKeyswitch.noWrap_of_domain aux hn) x
    exact List.mem_flatMap.mpr ⟨row,List.mem_finRange row,hx⟩
  · exact Or.inr hb

theorem allRowsSound_or_bad {n : Nat} (groups last : Nat) (l : Fin 4)
    (keys : Fin groups → Nat → Fin 4 → BabyBear) (m : Nat → Nat) (α : Ext4)
    (trace : Fin n → RangeKeyswitchRow.Idx → BabyBear)
    (aux : Fin n → NativeRangeKeyswitch.Aux)
    (ha : Accepted groups last keys m α)
    (binding : (sendListN groups last keys).Perm (NativeRangeKeyswitch.allSends aux))
    (hg : ∀ row,systemAccepts (trace row) (RangeKeyswitchRow.system (BfvKeyswitchRow.primes l)))
    (he : ∀ row,NativeRangeKeyswitch.Local (trace row) (aux row))
    (hn : n≤131072) :
    (∀ row h,RangeKeyswitchRow.value (trace row) (BfvKeyswitchCore.oIndex h)=
      (RangeKeyswitchRow.value (trace row) (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
        RangeKeyswitchRow.value (trace row) (BfvKeyswitchCore.dIndex k)*
        RangeKeyswitchRow.value (trace row) (BfvKeyswitchCore.kIndex h k))%BfvKeyswitchRow.primes l) ∨
      Bad (sendListN groups last keys) m α := by
  rcases allRowsRanges_or_bad groups last keys m α trace aux ha binding he hn with hr | hb
  · exact Or.inl (fun row => (RangeKeyswitchRow.actualRowSound l (trace row) (hg row) (hr row)).2)
  · exact Or.inr hb

theorem embed_nat (n : Nat) : embed (n : BabyBear)=(n : Ext4) := map_natCast embed n

/-- A nonzero complete 131-column native byte-bus witness. All fixed source
keys are15, their source count is524, and alpha16 is outside the table. -/
theorem nonzero_native_accepted :
    Accepted 131 0 (fun _ _ _ => (15 : BabyBear))
      (fun r => if r=15 then 524 else 0) (16 : Ext4) := by
  refine ⟨fun _ _ => 0,fun _ => 4,fun _ => 0,-524,?_,?_,?_⟩
  · intro g
    norm_num [Gates4,LogUpGrouping.Transition,LogUpGrouping.denominator,
      LogUpGrouping.numerator,show embed (15 : BabyBear)=(15 : Ext4) from embed_nat 15,
      show embed (16 : BabyBear)=(16 : Ext4) from embed_nat 16]
  · refine ⟨rfl,?_,?_⟩
    · intro r hr
      have : r≠15 := by omega
      simp [this]
    · norm_num [show embed (15 : BabyBear)=(15 : Ext4) from embed_nat 15]
  · norm_num

/-- An actual bad challenge can satisfy the source-shaped gates with a wrong
histogram. Four invalid key16 sends balance eight key15 receives at alpha17.
This is a fixed committed instance, not a post-challenge choice of multiplicity. -/
theorem wrong_native_accepted :
    Accepted 1 0 (fun _ _ _ => (16 : BabyBear))
      (fun r => if r=15 then 8 else 0) (17 : Ext4) := by
  refine ⟨fun _ _ => 0,fun _ => 4,fun _ => 0,-4,?_,?_,?_⟩
  · intro g
    norm_num [Gates4,LogUpGrouping.Transition,LogUpGrouping.denominator,
      LogUpGrouping.numerator,show embed (15 : BabyBear)=(15 : Ext4) from embed_nat 15,
      show embed (16 : BabyBear)=(16 : Ext4) from embed_nat 16]
  · refine ⟨rfl,?_,?_⟩
    · intro r hr
      have : r≠15 := by omega
      simp [this]
    · norm_num [show embed (15 : BabyBear)=(15 : Ext4) from embed_nat 15]
  · norm_num

theorem wrong_native_histogram : ¬NativeNibbleBus.ExactField
    (sendListN 1 0 (fun _ _ _ => (16 : BabyBear))) (fun r => if r=15 then 8 else 0) := by
  intro h
  have hh := h 16
  norm_num [sendListN,NativeNibbleBus.receives,List.finRange_succ,List.range_succ,List.count_replicate] at hh
  rw [if_neg (by decide : (15 : BabyBear)≠16)] at hh
  exact (by decide : (4 : BabyBear)≠0) hh

theorem native_premise_inhabited : ∃ groups last keys m α,
    Accepted groups last keys m α ∧ (sendListN groups last keys).length>0 := by
  refine ⟨1,0,fun _ _ _ => (16 : BabyBear),fun r => if r=15 then 8 else 0,
    (17 : Ext4),wrong_native_accepted,?_⟩
  norm_num [sendListN,List.finRange_succ,List.range_succ]

/-- Direct producer of the frozen Infer theorem's compact-row premise. The
caller supplies the existing public operand binding for this same source row. -/
theorem checked_for_infer {n : Nat} (groups last : Nat) (l : Fin 4)
    (keys : Fin groups → Nat → Fin 4 → BabyBear) (m : Nat → Nat) (α : Ext4)
    (trace : Fin n → RangeKeyswitchRow.Idx → BabyBear)
    (aux : Fin n → NativeRangeKeyswitch.Aux) (row : Fin n)
    (operands : BfvInferComposition.Operands) (out : Fin 2 → Nat)
    (ha : Accepted groups last keys m α)
    (binding : (sendListN groups last keys).Perm (NativeRangeKeyswitch.allSends aux))
    (hg : systemAccepts (trace row) (RangeKeyswitchRow.system (BfvKeyswitchRow.primes l)))
    (he : ∀ r,NativeRangeKeyswitch.Local (trace r) (aux r))
    (hn : n≤131072)
    (hb : BfvInferComposition.Bound RangeKeyswitchRow.wires (trace row) operands out)
    (hgood : ¬Bad (sendListN groups last keys) m α) :
    NativeRangeKeyswitch.Checked l operands out := by
  have hr := (allRowsRanges_or_bad groups last keys m α trace aux ha binding he hn).resolve_right hgood
  exact ⟨trace row,hg,(NativeRangeKeyswitch.nativeRanges_iff _).mpr (hr row),hb⟩

end
end Minidregg.Compiler.NativeByteExtraction

/-- info: 'Minidregg.Compiler.NativeByteExtraction.denom_of_nopole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.denom_of_nopole
/-- info: 'Minidregg.Compiler.NativeByteExtraction.accepted_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.accepted_rational
/-- info: 'Minidregg.Compiler.NativeByteExtraction.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.sound
/-- info: 'Minidregg.Compiler.NativeByteExtraction.false_accept_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.false_accept_probability
/-- info: 'Minidregg.Compiler.NativeByteExtraction.exact_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.exact_perm
/-- info: 'Minidregg.Compiler.NativeByteExtraction.allRowsRanges_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.allRowsRanges_or_bad
/-- info: 'Minidregg.Compiler.NativeByteExtraction.allRowsSound_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.allRowsSound_or_bad
/-- info: 'Minidregg.Compiler.NativeByteExtraction.embed_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.embed_nat
/-- info: 'Minidregg.Compiler.NativeByteExtraction.nonzero_native_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.nonzero_native_accepted
/-- info: 'Minidregg.Compiler.NativeByteExtraction.wrong_native_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.wrong_native_accepted
/-- info: 'Minidregg.Compiler.NativeByteExtraction.wrong_native_histogram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.wrong_native_histogram
/-- info: 'Minidregg.Compiler.NativeByteExtraction.native_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.native_premise_inhabited
/-- info: 'Minidregg.Compiler.NativeByteExtraction.checked_for_infer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.NativeByteExtraction.checked_for_infer
