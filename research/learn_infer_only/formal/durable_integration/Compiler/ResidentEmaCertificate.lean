/-
[DERIVED target; EXECUTED after matching compilation]
Statement-first: the actual compiler-emitted descriptor forces mathematical
floor EMA on full signed bytes, including -128. Existing range gadgets and
source Term constructors suffice; no handwritten gates or duplicate checker.
Public certificate only: values/openings are not hidden by this module.
-/
import Compiler.DescriptorEval
import Compiler.NativeKernelPlan

namespace Minidregg.Compiler.ResidentEmaCertificate
open Minidregg.Compiler
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def ema (c u : Int) : Int := (7*c+u)/8

def SemanticSound (d : ConstraintDescriptor BabyBear) : Prop :=
  ∀ v : Nat → BabyBear, descriptorHolds d v →
    ((v 2).val : Int)-128 = ema (((v 0).val : Int)-128) (((v 1).val : Int)-128)

def scalar (i : Fin 4) : Fin 31 := ⟨i.val, by omega⟩
def byteBit (i : Fin 3) (j : Fin 8) : Fin 31 := ⟨4+8*i.val+j.val, by omega⟩
def remBit (j : Fin 3) : Fin 31 := ⟨28+j.val, by omega⟩
def relation : Term (AirSig BabyBear (Fin 31)) :=
  add' (add' (mul' (cst 7) (vr (scalar 0))) (vr (scalar 1)))
    (mul' (cst (-1)) (add' (mul' (cst 8) (vr (scalar 2))) (vr (scalar 3))))
def system : ConstraintSystem BabyBear (Fin 31) :=
  rangeGadget (scalar 0) (byteBit 0) ++
  rangeGadget (scalar 1) (byteBit 1) ++
  rangeGadget (scalar 2) (byteBit 2) ++
  rangeGadget (scalar 3) remBit ++ [relation]
def descriptor : ConstraintDescriptor BabyBear := emit Fin.val 4 31 system


/-- Compiler-derived dimensions, pinned to this actual source system. -/
theorem descriptor_shape : descriptor.nPublic=4 ∧ descriptor.nVars=31 ∧
    descriptor.nWires=153 ∧ descriptor.gates.length=122 ∧ descriptor.zeros.length=32 := by decide +kernel

/-- This small lift is deliberately independent of integer range claims; the
caller must prove BOTH natural sides below the field modulus. -/
theorem no_wrap_equal (a b : Nat) (ha : a < babyBearP) (hb : b < babyBearP)
    (h : (a : BabyBear) = (b : BabyBear)) : a = b := by
  have hv := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hv
  exact hv

theorem system_sound (v : Fin 31 → BabyBear) (h : systemAccepts v system) :
    7*(v (scalar 0)).val+(v (scalar 1)).val =
      8*(v (scalar 2)).val+(v (scalar 3)).val ∧
    (v (scalar 3)).val<8 ∧
    (v (scalar 0)).val<256 ∧ (v (scalar 1)).val<256 ∧ (v (scalar 2)).val<256 := by
  simp only [system, systemAccepts_append, systemAccepts_cons,
    systemAccepts_nil, and_true] at h
  obtain ⟨⟨⟨⟨h0,h1⟩,h2⟩,h3⟩,he⟩ := h
  have b0 := rangeGadget_val_lt (by norm_num [babyBearP] : 2^8≤babyBearP) v _ _ h0
  have b1 := rangeGadget_val_lt (by norm_num [babyBearP] : 2^8≤babyBearP) v _ _ h1
  have b2 := rangeGadget_val_lt (by norm_num [babyBearP] : 2^8≤babyBearP) v _ _ h2
  have b3 := rangeGadget_val_lt (by norm_num [babyBearP] : 2^3≤babyBearP) v _ _ h3
  have eqfield : 7*v (scalar 0)+v (scalar 1) = 8*v (scalar 2)+v (scalar 3) := by
    simp only [accepts, relation, eval_add', eval_mul', eval_cst, eval_vr] at he
    linear_combination he
  have casts : ((7*(v (scalar 0)).val+(v (scalar 1)).val : Nat) : BabyBear) =
      ((8*(v (scalar 2)).val+(v (scalar 3)).val : Nat) : BabyBear) := by
    simpa using eqfield
  refine ⟨no_wrap_equal _ _ ?_ ?_ casts, b3, b0, b1, b2⟩ <;>
    norm_num [babyBearP] at * <;> omega

theorem descriptor_qr (v : Nat → BabyBear) (h : descriptorHolds descriptor v) :
    7*(v 0).val+(v 1).val = 8*(v 2).val+(v 3).val ∧ (v 3).val<8 ∧
    (v 0).val<256 ∧ (v 1).val<256 ∧ (v 2).val<256 := by
  exact system_sound (fun i => v i.val)
    ((emit_accepts_iff_fin 31 4 (fun i => v i.val) system).mp ⟨v, fun _ => rfl,h⟩)

theorem descriptor_semantic : SemanticSound descriptor := by
  intro v h
  obtain ⟨he,hr,-,-,-⟩ := descriptor_qr v h
  have hi : 7*((v 0).val : Int)+(v 1).val = 8*(v 2).val+(v 3).val := by exact_mod_cast he
  have hir : ((v 3).val : Int)<8 := by exact_mod_cast hr
  unfold ema
  omega

theorem ema_fullbyte_closed (c u : Int) (hc : -128≤c ∧ c≤127) (hu : -128≤u ∧ u≤127) :
    -128≤ema c u ∧ ema c u≤127 := by unfold ema; omega

theorem ema_checked_subset_closed (c u : Int) (hc : -127≤c ∧ c≤127) (hu : -127≤u ∧ u≤127) :
    -127≤ema c u ∧ ema c u≤127 := by unfold ema; omega

def variableValue (C U N r : Nat) (i : Fin 31) : Nat :=
  if h : i.val<4 then (![C,U,N,r] : Fin 4 → Nat) ⟨i.val, by omega⟩
  else if h : i.val<28 then
    ((![C,U,N] : Fin 3 → Nat) ⟨(i.val-4)/8, by omega⟩ / 2^((i.val-4)%8))%2
  else (r/2^(i.val-28))%2

def assignment (C U N r : Nat) (i : Fin 31) : BabyBear := (variableValue C U N r i : BabyBear)

def candidate (C U N r : Nat) : Array BabyBear :=
  fillAux descriptor (Array.ofFn (assignment C U N r))

set_option maxHeartbeats 1000000 in
theorem honest_assignment : systemAccepts (assignment 128 248 143 0) system := by decide +kernel

theorem honest_descriptor : descriptorHolds descriptor
    (fun i => (candidate 128 248 143 0).getD i 0) :=
  fillAux_emit_holds 31 4 (by omega) _ system honest_assignment

theorem candidate_pins (C U N r : Nat) (i : Fin 4) :
    (candidate C U N r).getD i.val 0 = (![C,U,N,r] : Fin 4 → BabyBear) i := by
  have hwf : descriptor.WellFormed := emit_wellFormed Fin.val 4 31 (by omega) (fun i => i.isLt) system
  have hsize : (Array.ofFn (assignment C U N r)).size = descriptor.nVars := Array.size_ofFn
  unfold candidate
  rw [fillAux_getD_of_lt _ _ hwf hsize (by change i.val<31; omega)]
  fin_cases i <;> simp [Array.getD_eq_getD_getElem?, assignment, variableValue]

theorem changed_state_and_order :
    ema 0 120=15 ∧ ema 15 (-120)= -2 ∧
    ema 0 (-120)= -15 ∧ ema (-15) 120=1 ∧
    ema (ema 0 120) (-120) ≠ ema (ema 0 (-120)) 120 := by decide +kernel

theorem minimum_boundary : ema (-128) (-128)= -128 ∧ ema (-128) 127= -97 := by decide +kernel

theorem wrong_logical_post_refused (v : Nat → BabyBear)
    (hp : v 0=128) (hu : v 1=248) (hn : v 2=144) : ¬descriptorHolds descriptor v := by
  intro h
  have hs := descriptor_semantic v h
  rw [hp,hu,hn] at hs
  have a : (128 : BabyBear).val=128 := by decide +kernel
  have b : (248 : BabyBear).val=248 := by decide +kernel
  have c : (144 : BabyBear).val=144 := by decide +kernel
  rw [a,b,c] at hs
  norm_num [ema] at hs

end Minidregg.Compiler.ResidentEmaCertificate

/- Exact-output axiom pins, observed from the recorded matching Lean check. -/

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.no_wrap_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.no_wrap_equal

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.system_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.system_sound

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.descriptor_qr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.descriptor_qr

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.descriptor_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.descriptor_semantic

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.ema_fullbyte_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.ema_fullbyte_closed

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.ema_checked_subset_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.ema_checked_subset_closed

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.honest_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.honest_assignment

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.honest_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.honest_descriptor

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.candidate_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.candidate_pins

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.changed_state_and_order' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.changed_state_and_order

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.minimum_boundary' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.minimum_boundary

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.wrong_logical_post_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.wrong_logical_post_refused

/-- info: 'Minidregg.Compiler.ResidentEmaCertificate.descriptor_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResidentEmaCertificate.descriptor_shape
