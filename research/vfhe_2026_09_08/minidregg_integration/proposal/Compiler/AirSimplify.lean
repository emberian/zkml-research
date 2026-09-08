/-
Generic source arithmetic simplification. No emitted gate is authored here:
the pass folds the actual Air signature into smart constructors, then uses Emit.

Statement-first: `Preserves` quantifies over every assignment/expression. A
BabyBear witness below exercises constant folding and zero/one identities;
falsifiers retain a nonzero constant assertion and reject zero-as-unit rewriting.
The pass's scope is field evaluation, not integer lifting or proof-protocol soundness.
-/
import Compiler.DescriptorEval

namespace Minidregg.Compiler.AirSimplify

open Minidregg.Compiler
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan

set_option autoImplicit false
universe u
variable {F : Type u} [Field F] [DecidableEq F] {Idx : Type u}

def Preserves (rewrite : Term (AirSig F Idx) -> Term (AirSig F Idx)) : Prop :=
  forall (asg : Idx -> F) (t : Term (AirSig F Idx)), eval asg (rewrite t) = eval asg t

def constant? : Term (AirSig F Idx) -> Option F
  | .mk (.const c) _ => some c
  | _ => none

def smartAdd (a b : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  match constant? a, constant? b with
  | some c, some d => cst (c+d)
  | some c, none => if c=0 then b else add' a b
  | none, some d => if d=0 then a else add' a b
  | none, none => add' a b

def smartMul (a b : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  match constant? a, constant? b with
  | some c, some d => cst (c*d)
  | some c, none => if c=0 then cst 0 else if c=1 then b else mul' a b
  | none, some d => if d=0 then cst 0 else if d=1 then a else mul' a b
  | none, none => mul' a b

def simplifyAlg : Alg (AirSig F Idx) (Term (AirSig F Idx)) := fun s =>
  match s with
  | .const c => fun _ => cst c
  | .var i => fun _ => vr i
  | .add => fun k => smartAdd (k false) (k true)
  | .mul => fun k => smartMul (k false) (k true)

def simplify : Term (AirSig F Idx) -> Term (AirSig F Idx) := fold simplifyAlg

omit [DecidableEq F] in
theorem constant?_eval (asg : Idx -> F) (t : Term (AirSig F Idx)) (c : F)
    (h : constant? t = some c) : eval asg t = c := by
  cases t with
  | mk op k =>
    cases op with
    | const d => exact Option.some.inj h
    | var i => cases h
    | add => cases h
    | mul => cases h

theorem smartAdd_eval (asg : Idx -> F) (a b : Term (AirSig F Idx)) :
    eval asg (smartAdd a b) = eval asg a+eval asg b := by
  cases ha : constant? a with
  | none =>
    cases hb : constant? b with
    | none => simp [smartAdd,ha,hb]
    | some d =>
      have hd := constant?_eval asg b d hb
      simp only [smartAdd,ha,hb]
      split_ifs with h <;> simp_all
  | some c =>
    have hc := constant?_eval asg a c ha
    cases hb : constant? b with
    | none =>
      simp only [smartAdd,ha,hb]
      split_ifs with h <;> simp_all
    | some d =>
      have hd := constant?_eval asg b d hb
      simp [smartAdd,ha,hb,hc,hd]

theorem smartMul_eval (asg : Idx -> F) (a b : Term (AirSig F Idx)) :
    eval asg (smartMul a b) = eval asg a*eval asg b := by
  cases ha : constant? a with
  | none =>
    cases hb : constant? b with
    | none => simp [smartMul,ha,hb]
    | some d =>
      have hd := constant?_eval asg b d hb
      simp only [smartMul,ha,hb]
      split_ifs with h0 h1 <;> simp_all
  | some c =>
    have hc := constant?_eval asg a c ha
    cases hb : constant? b with
    | none =>
      simp only [smartMul,ha,hb]
      split_ifs with h0 h1 <;> simp_all
    | some d =>
      have hd := constant?_eval asg b d hb
      simp [smartMul,ha,hb,hc,hd]

/-- Evaluation of the rewrite is a homomorphism for the original field algebra. -/
theorem simplify_eval_hom (asg : Idx -> F) :
    IsFoldHom (evalAlg asg) (fun t => eval asg (simplify t)) := by
  intro op k
  cases op <;> simp [simplify,fold_mk,simplifyAlg,smartAdd_eval,smartMul_eval,evalAlg]

/-- The existing initiality theorem supplies the whole-expression proof. -/
theorem simplify_preserves : Preserves (simplify (F:=F) (Idx:=Idx)) := by
  intro asg t
  exact congrFun (fold_unique (evalAlg asg) _ (simplify_eval_hom asg)) t

def keep (t : Term (AirSig F Idx)) : Bool :=
  match constant? t with
  | some c => decide (c ≠ 0)
  | none => true

/-- Drop only assertions whose simplified field value is syntactically zero. -/
def simplifySystem (s : ConstraintSystem F Idx) : ConstraintSystem F Idx :=
  (s.map simplify).filter keep

theorem not_kept_accepts (asg : Idx -> F) (t : Term (AirSig F Idx))
    (h : keep t = false) : accepts asg t := by
  cases hc : constant? t with
  | none => simp [keep,hc] at h
  | some c =>
    have hv := constant?_eval asg t c hc
    simp [keep,hc] at h
    simp [accepts,hv,h]

theorem simplifySystem_accepts_iff (asg : Idx -> F) (s : ConstraintSystem F Idx) :
    systemAccepts asg (simplifySystem s) <-> systemAccepts asg s := by
  constructor
  · intro h t ht
    have hs : accepts asg (simplify t) := by
      by_cases hk : keep (simplify t)=true
      · exact h _ (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨t,ht,rfl⟩,hk⟩)
      · exact not_kept_accepts asg _ (by simpa using hk)
    change eval asg (simplify t)=0 at hs
    rw [simplify_preserves asg t] at hs
    exact hs
  · intro h t ht
    obtain ⟨ht,_⟩ := List.mem_filter.mp ht
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
    change eval asg (simplify original)=0
    rw [simplify_preserves asg original]
    exact h original ho

def emitSimplified (ix : Idx -> Nat) (nPublic nVars : Nat)
    (s : ConstraintSystem F Idx) : ConstraintDescriptor F :=
  emit ix nPublic nVars (simplifySystem s)

theorem emitSimplified_accepts_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i,ix i<nVars)
    (asg : Idx -> F) (s : ConstraintSystem F Idx) :
    (exists v : Nat -> F, (forall i,v (ix i)=asg i) /\
      descriptorHolds (emitSimplified ix nPublic nVars s) v) <-> systemAccepts asg s := by
  rw [emitSimplified,emit_accepts_iff ix hinj nPublic nVars hbound,
    simplifySystem_accepts_iff]

/-- Any satisfying optimized vector still satisfies the original source relation. -/
theorem emitSimplified_forces (ix : Idx -> Nat) (nPublic nVars : Nat)
    (s : ConstraintSystem F Idx) (v : Nat -> F)
    (h : descriptorHolds (emitSimplified ix nPublic nVars s) v) :
    systemAccepts (readVars ix v) s := by
  have hd := (emit_faithful ix nPublic nVars (simplifySystem s) v).mp h
  exact (simplifySystem_accepts_iff _ _).mp
    (flattenSystem_forces _ _ _ 0 hd.1 hd.2)

theorem emitSimplified_wellFormed (ix : Idx -> Nat) (nPublic nVars : Nat)
    (hpub : nPublic<=nVars) (hbound : forall i,ix i<nVars) (s : ConstraintSystem F Idx) :
    (emitSimplified ix nPublic nVars s).WellFormed :=
  emit_wellFormed ix nPublic nVars hpub hbound _

theorem checked_emitSimplified_forces {J : Type} (ix : J -> Nat) (nPublic nVars : Nat)
    (s : ConstraintSystem BabyBear J) (v : Nat -> BabyBear)
    (h : descriptorHoldsCheck (emitSimplified ix nPublic nVars s) v=true) :
    systemAccepts (readVars ix v) s :=
  emitSimplified_forces ix nPublic nVars s v
    ((descriptorHoldsCheck_eq_true_iff _ _).mp h)

theorem fillAux_emitSimplified_holds {K : Type} [Field K] [DecidableEq K]
    (m nPublic : Nat) (hpub : nPublic<=m) (asg : Fin m -> K)
    (s : ConstraintSystem K (Fin m)) (h : systemAccepts asg s) :
    descriptorHolds (emitSimplified Fin.val nPublic m s)
      (fun i => (fillAux (emitSimplified Fin.val nPublic m s) (Array.ofFn asg)).getD i 0) :=
  fillAux_emit_holds m nPublic hpub asg (simplifySystem s)
    ((simplifySystem_accepts_iff asg s).mpr h)

theorem cse_emitSimplified_accepts_iff [Hashable F]
    (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i,ix i<nVars)
    (asg : Idx -> F) (s : ConstraintSystem F Idx) :
    (exists v : Nat -> F, (forall i,v (ix i)=asg i) /\
      descriptorHolds (cse (emitSimplified ix nPublic nVars s)) v) <-> systemAccepts asg s := by
  rw [emitSimplified,cse_emit_accepts_iff ix hinj nPublic nVars hbound,
    simplifySystem_accepts_iff]

/- A nonzero public witness survives the optimized emission. -/
def witnessTerm : Term (AirSig BabyBear (Fin 1)) :=
  add' (add' (mul' (cst 0) (vr 0))
    (mul' (add' (cst 2) (cst 3)) (add' (vr 0) (cst 0)))) (cst (-15))
def witnessSystem : ConstraintSystem BabyBear (Fin 1) := [cst 0,witnessTerm]
def witnessDescriptor : ConstraintDescriptor BabyBear :=
  emitSimplified Fin.val 1 1 witnessSystem

theorem witness_accepts : systemAccepts (fun _ : Fin 1 => (3 : BabyBear)) witnessSystem := by
  simp [witnessSystem,systemAccepts_cons,systemAccepts_nil,accepts,witnessTerm]
  norm_num

theorem nonzero_premise_inhabited : exists v : Nat -> BabyBear,
    v 0=3 /\ descriptorHolds witnessDescriptor v := by
  obtain ⟨v,hpin,hd⟩ := (emitSimplified_accepts_iff Fin.val Fin.val_injective
    1 1 (fun i : Fin 1 => i.isLt) (fun _ => (3 : BabyBear)) witnessSystem).mpr witness_accepts
  exact ⟨v,hpin 0,hd⟩

theorem wrong_public_value_refused (v : Nat -> BabyBear) (hpin : v 0=4) :
    ¬ descriptorHolds witnessDescriptor v := by
  intro hd
  have hs := emitSimplified_forces Fin.val 1 1 witnessSystem v hd
  have ht := hs witnessTerm (by simp [witnessSystem])
  have hval : readVars Fin.val v (0 : Fin 1)=4 := hpin
  simp [accepts,witnessTerm,hval] at ht
  exact (show (5 : BabyBear) ≠ 0 from by decide +kernel) ht

/-- This bad sibling drops even a contradictory constant assertion. -/
def unsafeDropConstants (s : ConstraintSystem BabyBear (Fin 1)) :
    ConstraintSystem BabyBear (Fin 1) := s.filter fun t => (constant? t).isNone

theorem dropping_nonzero_constant_is_failopen (asg : Fin 1 -> BabyBear) :
    systemAccepts asg (unsafeDropConstants [cst 1]) /\
    ¬ systemAccepts asg [cst 1] := by
  constructor
  · change systemAccepts asg []
    exact systemAccepts_nil asg
  · intro h
    have hv := h (cst 1) (by simp)
    exact one_ne_zero hv

theorem nonzero_constant_still_refused (asg : Fin 1 -> BabyBear) :
    ¬ systemAccepts asg (simplifySystem [cst 1]) := by
  rw [simplifySystem_accepts_iff]
  simp [systemAccepts_cons,systemAccepts_nil,accepts]

/-- Zero is an annihilator, not a multiplicative unit; erasing it as a unit is wrong. -/
theorem zero_is_not_a_unit_rewrite :
    eval (fun _ : Fin 1 => (1 : BabyBear)) (mul' (cst 0) (vr 0)) ≠
      eval (fun _ : Fin 1 => (1 : BabyBear)) (vr 0) := by
  simp

/-- info: 'Minidregg.Compiler.AirSimplify.constant?_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.constant?_eval
/-- info: 'Minidregg.Compiler.AirSimplify.smartAdd_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.smartAdd_eval
/-- info: 'Minidregg.Compiler.AirSimplify.smartMul_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.smartMul_eval
/-- info: 'Minidregg.Compiler.AirSimplify.simplify_eval_hom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.simplify_eval_hom
/-- info: 'Minidregg.Compiler.AirSimplify.simplify_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.simplify_preserves
/-- info: 'Minidregg.Compiler.AirSimplify.not_kept_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.not_kept_accepts
/-- info: 'Minidregg.Compiler.AirSimplify.simplifySystem_accepts_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.simplifySystem_accepts_iff
/-- info: 'Minidregg.Compiler.AirSimplify.emitSimplified_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.emitSimplified_accepts_iff
/-- info: 'Minidregg.Compiler.AirSimplify.emitSimplified_forces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.emitSimplified_forces
/-- info: 'Minidregg.Compiler.AirSimplify.emitSimplified_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.emitSimplified_wellFormed
/-- info: 'Minidregg.Compiler.AirSimplify.checked_emitSimplified_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.checked_emitSimplified_forces
/-- info: 'Minidregg.Compiler.AirSimplify.fillAux_emitSimplified_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.fillAux_emitSimplified_holds
/-- info: 'Minidregg.Compiler.AirSimplify.cse_emitSimplified_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.cse_emitSimplified_accepts_iff
/-- info: 'Minidregg.Compiler.AirSimplify.witness_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.witness_accepts
/-- info: 'Minidregg.Compiler.AirSimplify.nonzero_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.nonzero_premise_inhabited
/-- info: 'Minidregg.Compiler.AirSimplify.wrong_public_value_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.wrong_public_value_refused
/-- info: 'Minidregg.Compiler.AirSimplify.dropping_nonzero_constant_is_failopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.dropping_nonzero_constant_is_failopen
/-- info: 'Minidregg.Compiler.AirSimplify.nonzero_constant_still_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.nonzero_constant_still_refused
/-- info: 'Minidregg.Compiler.AirSimplify.zero_is_not_a_unit_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.AirSimplify.zero_is_not_a_unit_rewrite

end Minidregg.Compiler.AirSimplify
