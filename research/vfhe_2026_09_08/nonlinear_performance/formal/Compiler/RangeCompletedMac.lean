/- Range-native source completion. Arithmetic terms are the existing MAC and
addition constructors. Only their bit witnesses become existential. -/
import Compiler.BfvKeyswitchCore
namespace Minidregg.Compiler.RangeCompletedMac
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000

def canonicalGates {J : Type} (q : Nat) (w : AirBignum.AddWires J 6 9) : ConstraintSystem BabyBear J :=
  AirBignum.carryRangeSystem w ++ [vr (w.carry 0),vr (w.carry 6)] ++
  AirBignum.addEquationSystem w ++ AirModularView.pinWordSystem (limbBits := 9) (q-1) w.z

def rowGates {J : Type} (q : Nat) (w : BfvKeyswitchMac.RowWires J) : ConstraintSystem BabyBear J :=
  (List.finRange 10).flatMap (fun k => canonicalGates q (w.canonical k)) ++
  [add' (vr (w.carry 0)) (cst (-32768)),add' (vr (w.carry 12)) (cst (-32768))] ++
  (List.finRange 12).map (BfvKeyswitchMac.column q w)

def gates {J : Type} (q : Nat) (w : BfvKeyswitchCore.Wires J) : ConstraintSystem BabyBear J :=
  (List.finRange 2).flatMap fun h => rowGates q (BfvKeyswitchCore.macWires w h)

def Bounds {J : Type} (a : J → BabyBear) (w : BfvKeyswitchCore.Wires J) : Prop :=
  (∀ g i,(a ((w.canonical g).x i)).val<512 ∧
    (a ((w.canonical g).y i)).val<512 ∧ (a ((w.canonical g).z i)).val<512) ∧
  (∀ h i,(a (w.quotient h i)).val<512) ∧
  (∀ h i,(a (w.carry h i)).val<65536)

/-- Acceptance of unchanged arithmetic plus canonical ranges forces exactly the
previous paired-MAC public relation, for every assignment and every wire layout. -/
def Sound {J : Type} (q : Nat) (w : BfvKeyswitchCore.Wires J) : Prop :=
  ∀ a : J → BabyBear, systemAccepts a (gates q w) → Bounds a w →
  (∀ g,BfvKeyswitchCore.value a w g<q) ∧ ∀ h,
    BfvKeyswitchCore.value a w (BfvKeyswitchCore.oIndex h)=
    (BfvKeyswitchCore.value a w (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
      BfvKeyswitchCore.value a w (BfvKeyswitchCore.dIndex k)*
      BfvKeyswitchCore.value a w (BfvKeyswitchCore.kIndex h k))%q

noncomputable def bits (k : Nat) (x : BabyBear) : Fin k → BabyBear :=
  if h : x.val<2^k then Classical.choose (exists_boolDecomp (F := BabyBear) x.val h)
  else fun _ => 0

theorem bits_complete (k : Nat) (x : BabyBear) (hx : x.val<2^k) :
    systemAccepts (id : BabyBear → BabyBear) (rangeGadget x (bits k x)) := by
  apply (rangeGadget_correct id x (bits k x)).mpr
  have h := Classical.choose_spec (exists_boolDecomp (F := BabyBear) x.val hx)
  simpa [bits,hx] using h

noncomputable def completeGroup {J : Type} (a : J → BabyBear) (w : AirBignum.AddWires J 6 9) : AirBignum.AddWires BabyBear 6 9 where
  x := fun i => a (w.x i)
  y := fun i => a (w.y i)
  z := fun i => a (w.z i)
  carry := fun i => a (w.carry i)
  xBit := fun i => bits 9 (a (w.x i))
  yBit := fun i => bits 9 (a (w.y i))
  zBit := fun i => bits 9 (a (w.z i))
noncomputable def complete {J : Type} (a : J → BabyBear) (w : BfvKeyswitchCore.Wires J) : BfvKeyswitchCore.Wires BabyBear where
  canonical := fun g => completeGroup a (w.canonical g)
  quotient := fun h i => a (w.quotient h i)
  quotientBit := fun h i => bits 9 (a (w.quotient h i))
  carry := fun h i => a (w.carry h i)
  carryBit := fun h i => bits 16 (a (w.carry h i))

theorem canonical_complete {J : Type} (a : J → BabyBear) (q : Nat) (w : AirBignum.AddWires J 6 9)
    (hg : systemAccepts a (canonicalGates q w))
    (hb : ∀ i,(a (w.x i)).val<512 ∧ (a (w.y i)).val<512 ∧ (a (w.z i)).val<512) :
    systemAccepts id (BfvKeyswitchMac.canonicalSystem q (completeGroup a w)) := by
  simp only [canonicalGates,systemAccepts_append] at hg
  obtain ⟨⟨⟨hc,he⟩,ha⟩,hp⟩ := hg
  apply (systemAccepts_append id _ _).mpr
  constructor
  · apply (AirBignum.addGadget_correct id _).mpr
    refine ⟨fun i => bits_complete 9 _ (hb i).1,
      fun i => bits_complete 9 _ (hb i).2.1,
      fun i => bits_complete 9 _ (hb i).2.2,?_,?_,?_,?_⟩
    · exact (AirBignum.carryRangeSystem_correct a w).mp hc
    · simpa [systemAccepts_cons,systemAccepts_nil,accepts,eval_vr] using (he (vr (w.carry 0)) (by simp))
    · have hh := he (vr (w.carry 6)) (by simp)
      simpa [accepts,eval_vr,completeGroup] using hh
    · exact (AirBignum.addEquationSystem_correct a w).mp ha
  · apply (AirModularView.pinWordSystem_correct id _ _).mpr
    exact (AirModularView.pinWordSystem_correct a _ _).mp hp

theorem source_completion {J : Type} (q : Nat) (w : BfvKeyswitchCore.Wires J) (a : J → BabyBear)
    (hg : systemAccepts a (gates q w)) (hb : Bounds a w) :
    systemAccepts id (BfvKeyswitchCore.system q (complete a w)) := by
  intro t ht
  obtain ⟨h,_,ht⟩ := List.mem_flatMap.mp ht
  have gh : systemAccepts a (rowGates q (BfvKeyswitchCore.macWires w h)) :=
    fun t ht => hg t (List.mem_flatMap.mpr ⟨h,List.mem_finRange h,ht⟩)
  simp only [rowGates,systemAccepts_append] at gh
  obtain ⟨⟨gc,ge⟩,gm⟩ := gh
  have can (k : Fin 10) : systemAccepts id (BfvKeyswitchMac.canonicalSystem q
      ((BfvKeyswitchCore.macWires (complete a w) h).canonical k)) :=
    canonical_complete a q _ (fun t ht => gc t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩)) (hb.1 _)
  have old : systemAccepts id (BfvKeyswitchMac.rowSystem q (BfvKeyswitchCore.macWires (complete a w) h)) := by
    simp only [BfvKeyswitchMac.rowSystem,systemAccepts_append]
    refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
    · intro t ht
      obtain ⟨k,_,ht⟩ := List.mem_flatMap.mp ht
      exact can k t ht
    · apply (AirBignum.limbRangeSystem_correct id _ _).mpr
      intro i
      exact bits_complete 9 _ (hb.2.1 h i)
    · apply (AirBignum.limbRangeSystem_correct id _ _).mpr
      intro i
      exact bits_complete 16 _ (hb.2.2 h i)
    · simp only [systemAccepts_cons,systemAccepts_nil,accepts,eval_add',eval_vr,eval_cst] at ge ⊢
      exact ge
    · intro t ht
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
      apply (BfvKeyswitchMac.column_correct q (BfvKeyswitchCore.macWires (complete a w) h) id i).mpr
      have hi := (BfvKeyswitchMac.column_correct q (BfvKeyswitchCore.macWires w h) a i).mp
        (gm _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
      simpa only [BfvKeyswitchCore.macWires,complete,completeGroup,id_eq] using hi
  exact old t ht

/-- Erasing explicit bit witnesses preserves the remaining generated gates. -/
theorem source_reduction {J : Type} (q : Nat) (w : BfvKeyswitchCore.Wires J) (a : J → BabyBear)
    (hs : systemAccepts a (BfvKeyswitchCore.system q w)) :
    systemAccepts a (gates q w) := by
  intro t ht
  obtain ⟨h,_,ht⟩ := List.mem_flatMap.mp ht
  have ho : systemAccepts a (BfvKeyswitchMac.rowSystem q (BfvKeyswitchCore.macWires w h)) :=
    fun t ht => hs t (List.mem_flatMap.mpr ⟨h,List.mem_finRange h,ht⟩)
  simp only [BfvKeyswitchMac.rowSystem,systemAccepts_append] at ho
  have hn : systemAccepts a (rowGates q (BfvKeyswitchCore.macWires w h)) := by
    simp only [rowGates,systemAccepts_append]
    refine ⟨⟨?_,ho.1.2⟩,ho.2⟩
    intro t ht
    obtain ⟨g,_,ht⟩ := List.mem_flatMap.mp ht
    have hc := ho.1.1.1.1
    have hh : systemAccepts a (BfvKeyswitchMac.canonicalSystem q
        ((BfvKeyswitchCore.macWires w h).canonical g)) :=
      fun t ht => hc t (List.mem_flatMap.mpr ⟨g,List.mem_finRange g,ht⟩)
    simp only [BfvKeyswitchMac.canonicalSystem,AirBignum.addGadget,systemAccepts_append] at hh
    have hg : systemAccepts a (canonicalGates q ((BfvKeyswitchCore.macWires w h).canonical g)) := by
      simp only [canonicalGates,systemAccepts_append]
      exact ⟨⟨⟨hh.1.1.1.2,hh.1.1.2⟩,hh.1.2⟩,hh.2⟩
    exact hg t ht
  exact hn t ht

theorem sound {J : Type} (q : Nat) (hq : 0<q) (hcap : q<512^6) (w : BfvKeyswitchCore.Wires J) : Sound q w := by
  intro a hg hb
  exact BfvKeyswitchCore.sound q hq hcap (complete a w) id (source_completion q w a hg hb)
end Minidregg.Compiler.RangeCompletedMac

/-- info: 'Minidregg.Compiler.RangeCompletedMac.bits_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeCompletedMac.bits_complete

/-- info: 'Minidregg.Compiler.RangeCompletedMac.canonical_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeCompletedMac.canonical_complete

/-- info: 'Minidregg.Compiler.RangeCompletedMac.source_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeCompletedMac.source_completion

/-- info: 'Minidregg.Compiler.RangeCompletedMac.source_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeCompletedMac.source_reduction

/-- info: 'Minidregg.Compiler.RangeCompletedMac.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeCompletedMac.sound

