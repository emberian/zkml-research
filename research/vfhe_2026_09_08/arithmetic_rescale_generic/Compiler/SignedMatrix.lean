/- Reusable signed affine source rows. Positive/negative coefficient splitting
feeds the existing natural weighted-column compiler; values remain canonical Nats. -/
import Compiler.IntegerCertificateEmission

namespace Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler
open Minidregg.Theory.CompressedLinearEquation
open scoped BigOperators
set_option autoImplicit false

structure Row (n : Nat) where
  constant : Int
  coefficient : Fin n → Int

def eval {n : Nat} (r : Row n) (x : Fin n → Nat) : Int :=
  r.constant+∑ i,r.coefficient i*(x i : Int)
def cst {n : Nat} (c : Int) : Row n := ⟨c,fun _ => 0⟩
def var {n : Nat} (j : Fin n) : Row n := ⟨0,fun i => if i=j then 1 else 0⟩
def add {n : Nat} (a b : Row n) : Row n := ⟨a.constant+b.constant,fun i => a.coefficient i+b.coefficient i⟩
def scale {n : Nat} (c : Int) (a : Row n) : Row n := ⟨c*a.constant,fun i => c*a.coefficient i⟩
def sub {n : Nat} (a b : Row n) : Row n := add a (scale (-1) b)
def sum {n k : Nat} (f : Fin k → Row n) : Row n := ⟨∑ i,(f i).constant,fun j => ∑ i,(f i).coefficient j⟩

@[simp] theorem eval_cst {n : Nat} (c : Int) (x : Fin n → Nat) : eval (cst c) x = c := by simp [eval,cst]
@[simp] theorem eval_var {n : Nat} (j : Fin n) (x : Fin n → Nat) : eval (var j) x = x j := by simp [eval,var]
@[simp] theorem eval_add {n : Nat} (a b : Row n) (x : Fin n → Nat) : eval (add a b) x = eval a x+eval b x := by
  simp only [eval,add,add_mul,Finset.sum_add_distrib]; ring
@[simp] theorem eval_scale {n : Nat} (c : Int) (a : Row n) (x : Fin n → Nat) : eval (scale c a) x = c*eval a x := by
  simp [eval,scale,Finset.mul_sum,mul_add,mul_assoc]
@[simp] theorem eval_sub {n : Nat} (a b : Row n) (x : Fin n → Nat) : eval (sub a b) x = eval a x-eval b x := by
  simp [sub]; ring
@[simp] theorem eval_sum {n k : Nat} (f : Fin k → Row n) (x : Fin n → Nat) : eval (sum f) x = ∑ i,eval (f i) x := by
  simp only [eval,sum,Finset.sum_add_distrib,Finset.sum_mul]
  rw [Finset.sum_comm]

def leftConstant {n : Nat} (r : Row n) : Nat := Minidregg.Theory.CompressedLinearEquation.posPart r.constant
def rightConstant {n : Nat} (r : Row n) : Nat := Minidregg.Theory.CompressedLinearEquation.negPart r.constant
def leftCoefficient {n : Nat} (r : Row n) (i : Fin n) : Nat := Minidregg.Theory.CompressedLinearEquation.posPart (r.coefficient i)
def rightCoefficient {n : Nat} (r : Row n) (i : Fin n) : Nat := Minidregg.Theory.CompressedLinearEquation.negPart (r.coefficient i)
def leftMass {n : Nat} (r : Row n) (x : Fin n → Nat) : Nat := leftConstant r+∑ i,leftCoefficient r i*x i
def rightMass {n : Nat} (r : Row n) (x : Fin n → Nat) : Nat := rightConstant r+∑ i,rightCoefficient r i*x i

def SplitSound : Prop := ∀ {n : Nat} (r : Row n) (x : Fin n → Nat),
  leftMass r x = rightMass r x ↔ eval r x = 0

theorem eval_split {n : Nat} (r : Row n) (x : Fin n → Nat) :
    eval r x = (leftMass r x : Int)-(rightMass r x : Int) := by
  have hc := eq_posPart_sub_negPart r.constant
  have hs : (∑ i,r.coefficient i*(x i : Int)) =
      ∑ i,((Minidregg.Theory.CompressedLinearEquation.posPart (r.coefficient i) : Int)-(Minidregg.Theory.CompressedLinearEquation.negPart (r.coefficient i) : Int))*(x i : Int) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← eq_posPart_sub_negPart]
  rw [eval,hs,hc]
  simp only [sub_mul,Finset.sum_sub_distrib]
  simp only [leftMass,rightMass,leftConstant,rightConstant,leftCoefficient,rightCoefficient,Nat.cast_add,Nat.cast_sum,Nat.cast_mul]
  ring

theorem splitSound : SplitSound := by
  intro n r x
  rw [eval_split]
  exact_mod_cast (sub_eq_zero : ((leftMass r x : Int)-(rightMass r x : Int) = 0) ↔ _).symm

end Minidregg.Compiler.SignedMatrix

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_cst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_cst

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_var' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_var

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_add

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_scale

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_sub

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_sum

/-- info: 'Minidregg.Compiler.SignedMatrix.eval_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.eval_split

/-- info: 'Minidregg.Compiler.SignedMatrix.splitSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.SignedMatrix.splitSound
