/- Compact source with range lookup vocabulary. Data and arithmetic use the
existing paired-MAC constructors; omitted bit columns are completed in Lean. -/
import Compiler.RangeCompletedMac
import Compiler.BfvKeyswitchRow
namespace Minidregg.Compiler.RangeKeyswitchRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
local instance : Hashable BabyBear where hash x := hash x.val

def nVars : Nat := 349
abbrev Idx := Fin nVars

def group (g : Fin 16) : AirBignum.AddWires Idx 6 9 where
  x := fun i => ⟨1+6*g.val+i.val,by dsimp [nVars]; omega⟩
  y := fun i => ⟨97+13*g.val+i.val,by dsimp [nVars]; omega⟩
  z := fun i => ⟨305+i.val,by dsimp [nVars]; omega⟩
  carry := fun i => ⟨97+13*g.val+6+i.val,by dsimp [nVars]; omega⟩
  xBit := fun _ _ => ⟨0,by decide⟩
  yBit := fun _ _ => ⟨0,by decide⟩
  zBit := fun _ _ => ⟨0,by decide⟩

def wires : BfvKeyswitchCore.Wires Idx where
  canonical := group
  quotient := fun h i => ⟨311+6*h.val+i.val,by dsimp [nVars]; omega⟩
  carry := fun h i => ⟨323+13*h.val+i.val,by dsimp [nVars]; omega⟩
  quotientBit := fun _ _ _ => ⟨0,by decide⟩
  carryBit := fun _ _ _ => ⟨0,by decide⟩

structure RangeSpec where
  wire : Idx
  bits : Nat
  deriving DecidableEq,BEq,ReflBEq,LawfulBEq

def rangeFamily {n : Nat} (width : Nat) (f : Fin n → Idx) : List RangeSpec :=
  (List.finRange n).map fun i => ⟨f i,width⟩
def allRanges : List RangeSpec :=
  (List.finRange 16).flatMap (fun g => rangeFamily 9 (group g).x ++
    rangeFamily 9 (group g).y ++ rangeFamily 9 (group g).z) ++
  (List.finRange 2).flatMap (fun h => rangeFamily 9 (wires.quotient h) ++ rangeFamily 16 (wires.carry h))
def ranges := allRanges.eraseDups

def RangeHolds (a : Idx → BabyBear) : Prop :=
  ∀ r ∈ ranges,(a r.wire).val<2^r.bits

def system (q : Nat) := AirAssertionShare.optimize (RangeCompletedMac.gates q wires)
def value (a : Idx → BabyBear) (g : Fin 16) := BfvKeyswitchCore.value a wires g

/-- Public operands and both outputs satisfy the same exact integer law as the
previous bit-decomposed source, for any accepted compact assignment. -/
def RowSound (q : Nat) : Prop := ∀ a : Idx → BabyBear,
  systemAccepts a (system q) → RangeHolds a →
  (∀ g,value a g<q) ∧ ∀ h,value a (BfvKeyswitchCore.oIndex h)=
    (value a (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
      value a (BfvKeyswitchCore.dIndex k)*value a (BfvKeyswitchCore.kIndex h k))%q

theorem ranges_complete (a : Idx → BabyBear) (hr : RangeHolds a) : RangeCompletedMac.Bounds a wires := by
  have hh : ∀ r ∈ allRanges,(a r.wire).val<2^r.bits := by
    intro r hm
    exact hr r (by simpa [ranges] using hm)
  have hcan (g : Fin 16) (r : RangeSpec)
      (hm : r ∈ rangeFamily 9 (group g).x ++ rangeFamily 9 (group g).y ++ rangeFamily 9 (group g).z) :=
    hh r (List.mem_append_left _ (List.mem_flatMap.mpr ⟨g,List.mem_finRange g,hm⟩))
  have hmac (h : Fin 2) (r : RangeSpec)
      (hm : r ∈ rangeFamily 9 (wires.quotient h) ++ rangeFamily 16 (wires.carry h)) :=
    hh r (List.mem_append_right _ (List.mem_flatMap.mpr ⟨h,List.mem_finRange h,hm⟩))
  have hm {n : Nat} (b : Nat) (f : Fin n → Idx) (i : Fin n) :
      RangeSpec.mk (f i) b ∈ rangeFamily b f := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
  refine ⟨?_,?_,?_⟩
  · intro g i
    refine ⟨?_,?_,?_⟩
    · exact hcan g _ (List.mem_append_left _ (List.mem_append_left _ (hm 9 _ i)))
    · exact hcan g _ (List.mem_append_left _ (List.mem_append_right _ (hm 9 _ i)))
    · exact hcan g _ (List.mem_append_right _ (hm 9 _ i))
  · intro h i
    exact hmac h _ (List.mem_append_left _ (hm 9 _ i))
  · intro h i
    exact hmac h _ (List.mem_append_right _ (hm 16 _ i))

theorem rowSound (q : Nat) (hq : 0<q) (hcap : q<512^6) : RowSound q := by
  intro a hs hr
  exact RangeCompletedMac.sound q hq hcap wires a
    ((AirAssertionShare.optimize_preserves a _).mp hs) (ranges_complete a hr)

theorem actualRowSound (l : Fin 4) : RowSound (BfvKeyswitchRow.primes l) :=
  rowSound _ (BfvKeyswitchRow.prime_capacity l).1 (by have := (BfvKeyswitchRow.prime_capacity l).2; omega)

/-- Data-only projection from the previous generated native witness registers.
The public prefix is unchanged; existing Boolean carry data is retained. -/
def oldIndex (i : Idx) : Nat :=
  if i.val<97 then i.val
  else if i.val<305 then
    let g := (i.val-97)/13
    let j := (i.val-97)%13
    97+121*g+(if j<6 then 54+j else 114+(j-6))
  else if i.val<311 then 2033+(i.val-305)
  else if i.val<323 then 2093+281*((i.val-311)/6)+(i.val-311)%6
  else 2093+281*((i.val-323)/13)+60+(i.val-323)%13

theorem publicPrefix (i : Idx) (hi : i.val<97) : oldIndex i=i.val := by simp [oldIndex,hi]

end Minidregg.Compiler.RangeKeyswitchRow

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.ranges_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.ranges_complete

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.rowSound

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.actualRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.actualRowSound

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.publicPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.publicPrefix

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.instDecidableEqRangeSpec' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.instDecidableEqRangeSpec

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.instBEqRangeSpec' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.instBEqRangeSpec

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.instReflBEqRangeSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.instReflBEqRangeSpec

/-- info: 'Minidregg.Compiler.RangeKeyswitchRow.instLawfulBEqRangeSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchRow.instLawfulBEqRangeSpec

