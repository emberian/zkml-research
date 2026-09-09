/- Exact list-to-native-fraction glue. No new balance or membership premise. -/
import Compiler.GroupedLogUpTrace
import Compiler.ByteLogUpDefect

namespace Minidregg.Compiler.GroupedByteFractions
open Minidregg.Compiler
open Minidregg.Compiler.ByteLogUpDefect (rational embed)
open Minidregg.Compiler.GroupedLogUpTrace (rowSum)
open Minidregg.Selvage.BabyBearExt4 (Ext4)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

def sendListN (groups last : Nat) (keys : Fin groups → Nat → Fin 4 → BabyBear) : List BabyBear :=
  (List.finRange groups).flatMap fun g =>
    (List.range (last+1)).flatMap fun r => (List.finRange 4).map (keys g r)

def sendList (last : Nat) (keys : Fin 131 → Nat → Fin 4 → BabyBear) : List BabyBear :=
  sendListN 131 last keys

def SendSoundN (groups : Nat) : Prop := ∀ last keys α,
  rational (sendListN groups last keys) α =
    ∑ g, rowSum last (fun r => LogUpGrouping.fractions (fun _ => 1)
      (fun i => α-embed (keys g r i)))

def SendSound : Prop := SendSoundN 131

def ReceiveSound : Prop := ∀ m α,
  rational (NativeNibbleBus.receives m) α =
    rowSum 15 (fun r => (m r : Ext4)/(α-embed (r : BabyBear)))

theorem rational_flatMap {ι : Type*} (xs : List ι) (f : ι → List BabyBear) (α : Ext4) :
    rational (xs.flatMap f) α = (xs.map fun i => rational (f i) α).sum := by
  induction xs with
  | nil => simp [rational]
  | cons x xs ih =>
    simpa only [rational,List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons] using congrArg (fun z => rational (f x) α+z) ih

theorem sum_map_range (n : Nat) (f : Nat → Ext4) :
    ((List.range n).map f).sum = ∑ r ∈ Finset.range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

theorem send_rationalN (groups : Nat) : SendSoundN groups := by
  intro last keys α
  unfold sendListN
  rw [rational_flatMap,←Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro g _
  rw [rational_flatMap,sum_map_range]
  unfold rowSum
  apply Finset.sum_congr rfl
  intro r _
  unfold rational
  simp only [List.map_map,Function.comp_def]
  rw [←Fin.sum_univ_def]
  simp only [Fin.sum_univ_succ,LogUpGrouping.fractions,one_div]
  change (α-embed (keys g r 0))⁻¹+((α-embed (keys g r 1))⁻¹+
    ((α-embed (keys g r 2))⁻¹+((α-embed (keys g r 3))⁻¹+0))) = _
  ring

theorem send_rational : SendSound := send_rationalN 131

theorem receive_rational : ReceiveSound := by
  intro m α
  unfold NativeNibbleBus.receives
  rw [rational_flatMap,sum_map_range]
  unfold rowSum
  apply Finset.sum_congr rfl
  intro r _
  simp [rational,List.map_replicate,List.sum_replicate,nsmul_eq_mul,div_eq_mul_inv]

theorem mem_sendListN (groups last : Nat) (keys : Fin groups → Nat → Fin 4 → BabyBear)
    (g : Fin groups) (r : Nat) (hr : r≤last) (i : Fin 4) :
    keys g r i ∈ sendListN groups last keys := by
  apply List.mem_flatMap.mpr
  refine ⟨g,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨i,by simp,rfl⟩

theorem mem_sendList (last : Nat) (keys : Fin 131 → Nat → Fin 4 → BabyBear)
    (g : Fin 131) (r : Nat) (hr : r≤last) (i : Fin 4) :
    keys g r i ∈ sendList last keys := mem_sendListN 131 last keys g r hr i

end
end Minidregg.Compiler.GroupedByteFractions

/-- info: 'Minidregg.Compiler.GroupedByteFractions.rational_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.rational_flatMap

/-- info: 'Minidregg.Compiler.GroupedByteFractions.sum_map_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.sum_map_range

/-- info: 'Minidregg.Compiler.GroupedByteFractions.send_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.send_rational

/-- info: 'Minidregg.Compiler.GroupedByteFractions.receive_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.receive_rational

/-- info: 'Minidregg.Compiler.GroupedByteFractions.mem_sendList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.mem_sendList

/-- info: 'Minidregg.Compiler.GroupedByteFractions.send_rationalN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.send_rationalN

/-- info: 'Minidregg.Compiler.GroupedByteFractions.mem_sendListN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.GroupedByteFractions.mem_sendListN
