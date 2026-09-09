/- Source for the deployed identity-scaling RNS extension. It retains the
rounded fixed-point Garner sum and does not replace it by ideal CRT centering. -/
import Compiler.ProfiledMatrix
import Compiler.FheSourceCertificate
import Compiler.FheRnsScaleDecomposition

namespace Minidregg.Compiler.ExactBasisExtension
open Minidregg.Compiler Minidregg.Compiler.SignedMatrix
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

structure Params (L K : Nat) where
  source : Fin L → Nat
  target : Fin K → Nat
  gamma : Int
  omega : Fin L → Int
  theta : Fin L → Int
  denominator : Nat
  quotientOffset : Nat

structure Valid {L K : Nat} (p : Params L K) : Prop where
  sourcePos : ∀ i,0<p.source i
  targetPos : ∀ i,0<p.target i
  denominatorPos : 0<p.denominator

def rounded {L K : Nat} (p : Params L K) (r : Fin L → Int) :=
  (2*(∑ i,r i*p.theta i)+p.denominator)/(2*p.denominator)
def output {L K : Nat} (p : Params L K) (r : Fin L → Int) (i : Fin K) :=
  ((∑ j,r j*p.omega j)-p.gamma*rounded p r)%(p.target i : Int)

def groups (L K : Nat) := 3*L+3+3*K
def residue {L K : Nat} (i : Fin L) : Fin (groups L K) := ⟨i.val,by dsimp [groups];omega⟩
def slack {L K : Nat} (i : Fin L) : Fin (groups L K) := ⟨L+i.val,by dsimp [groups];omega⟩
def extra {L K : Nat} (i : Fin 3) : Fin (groups L K) := ⟨2*L+i.val,by dsimp [groups];omega⟩
def target {L K : Nat} (i : Fin K) (j : Fin 3) : Fin (groups L K) := ⟨2*L+3+3*i.val+j.val,by dsimp [groups];omega⟩
def copied {L K : Nat} (i : Fin L) : Fin (groups L K) := ⟨2*L+3+3*K+i.val,by dsimp [groups];omega⟩
def linear {L K : Nat} (a : Fin L → Int) : Row (groups L K) :=
  sum (fun i => scale (a i) (var (residue i)))
def inputRow {L K : Nat} (p : Params L K) (i : Fin L) : Row (groups L K) :=
  sub (add (var (residue i)) (var (slack i))) (SignedMatrix.cst (p.source i-1 : Int))
def garnerRow {L K : Nat} (p : Params L K) : Row (groups L K) :=
  sub (add (scale 2 (linear p.theta)) (SignedMatrix.cst p.denominator))
    (add (scale (2*p.denominator) (var (extra 0))) (var (extra 1)))
def garnerBound {L K : Nat} (p : Params L K) : Row (groups L K) :=
  sub (add (var (extra 1)) (var (extra 2))) (SignedMatrix.cst (2*p.denominator-1 : Int))
def targetRow {L K : Nat} (p : Params L K) (i : Fin K) : Row (groups L K) :=
  sub (sub (linear p.omega) (scale p.gamma (var (extra 0))))
    (add (scale (p.target i) (sub (var (target i 1)) (SignedMatrix.cst p.quotientOffset))) (var (target i 0)))
def targetBound {L K : Nat} (p : Params L K) (i : Fin K) : Row (groups L K) :=
  sub (add (var (target i 0)) (var (target i 2))) (SignedMatrix.cst (p.target i-1 : Int))
def copyRow {L K : Nat} (i : Fin L) : Row (groups L K) := sub (var (copied i)) (var (residue i))
def forms {L K : Nat} (p : Params L K) : List (Row (groups L K)) :=
  (List.finRange L).map (inputRow p) ++ [garnerRow p,garnerBound p] ++
    (List.finRange K).flatMap (fun i => [targetRow p i,targetBound p i]) ++
    (List.finRange L).map copyRow
def Balanced {L K : Nat} (p : Params L K) (x : Fin (groups L K) → Nat) : Prop :=
  ∀ row ∈ forms p,SignedMatrix.eval row x=0
def Semantics {L K : Nat} (p : Params L K) (x : Fin (groups L K) → Nat) : Prop :=
  (∀ i,x (residue i)<p.source i) ∧
  (∀ i,x (copied i)=x (residue i)) ∧
  ∀ i,(x (target i 0) : Int)=output p (fun j => x (residue j)) i
def MatrixSound : Prop := ∀ {L K} (p : Params L K),Valid p → ∀ x,Balanced p x → Semantics p x

theorem matrixSound : MatrixSound := by
  intro L K p hp x h
  have hin (i : Fin L) := h (inputRow p i) (by simp [forms])
  have hg := h (garnerRow p) (by simp [forms])
  have hb := h (garnerBound p) (by simp [forms])
  have ht (i : Fin K) := h (targetRow p i) (by
    simp only [forms,List.mem_append,List.mem_map,List.mem_flatMap]
    exact Or.inl (Or.inr ⟨i,by simp,by simp⟩))
  have htb (i : Fin K) := h (targetBound p i) (by
    simp only [forms,List.mem_append,List.mem_map,List.mem_flatMap]
    exact Or.inl (Or.inr ⟨i,by simp,by simp⟩))
  have hc (i : Fin L) := h (copyRow i) (by simp [forms])
  simp only [inputRow,garnerRow,garnerBound,targetRow,targetBound,copyRow,linear,
    eval_sub,eval_add,eval_scale,eval_sum,eval_var,SignedMatrix.eval_cst] at hin hg hb ht htb hc
  have hrem0 : (0 : Int)≤x (extra (L:=L) (K:=K) 1) := by positivity
  have hrem1 : (x (extra (L:=L) (K:=K) 1) : Int)<2*p.denominator := by omega
  have hg' : 2*(∑ i,(x (residue i) : Int)*p.theta i)+p.denominator=
      2*p.denominator*x (extra 0)+x (extra 1) := by
    simp_rw [mul_comm (p.theta _) (x (residue _) : Int)] at hg
    linarith
  have hv := FheSourceCertificate.qr_forced _ _ _ _
    (by have := hp.denominatorPos; exact_mod_cast (show 0<2*p.denominator by omega)) hrem0 hrem1 hg'
  change (x (extra 0) : Int)=rounded p (fun j => x (residue j)) at hv
  refine ⟨?_,?_,?_⟩
  · intro i; have := hin i; have := hp.sourcePos i; omega
  · intro i; have := hc i; omega
  · intro i
    have hout0 : (0 : Int)≤x (target i 0) := by positivity
    have hout1 : (x (target i 0) : Int)<p.target i := by
      have := htb i; have := hp.targetPos i; omega
    have he := ht i
    simp_rw [mul_comm (p.omega _) (x (residue _) : Int)] at he
    rw [hv] at he
    have he' : (∑ j,(x (residue j) : Int)*p.omega j)-p.gamma*rounded p (fun j => x (residue j))=
        (p.target i : Int)*((x (target i 1) : Int)-p.quotientOffset)+x (target i 0) := by linarith
    rw [output,he',Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_eq_of_lt hout0 hout1,
      Int.emod_eq_of_lt hout0 hout1]

-- Cheap inhabited source and a universally refused wrong public residue.
def tiny : Params 1 1 := ⟨fun _ => 31,fun _ => 17,31,fun _ => 1,fun _ => 1,32,64⟩
def tinyValues : Fin (groups 1 1) → Nat := ![3,27,0,38,25,3,64,13,3]
def Inhabited : Prop := Valid tiny ∧ Balanced tiny tinyValues
theorem inhabited : Inhabited := by
  constructor
  · constructor <;> decide
  · have h : (forms tiny).all (fun row => decide (SignedMatrix.eval row tinyValues=0))=true := by decide
    intro row hm
    exact of_decide_eq_true ((List.all_eq_true.mp h) row hm)
def WrongOutputRefused : Prop := ∀ x : Fin (groups 1 1) → Nat,
  x (residue 0)=3 → x (target 0 0)=4 → ¬Balanced tiny x
theorem wrongOutputRefused : WrongOutputRefused := by
  intro x hi ho h
  have hs := (matrixSound tiny inhabited.1 x h).2.2 0
  simp [output,rounded,tiny,hi,ho] at hs

/-- info: 'Minidregg.Compiler.ExactBasisExtension.matrixSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ExactBasisExtension.matrixSound

/-- info: 'Minidregg.Compiler.ExactBasisExtension.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ExactBasisExtension.inhabited

/-- info: 'Minidregg.Compiler.ExactBasisExtension.wrongOutputRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ExactBasisExtension.wrongOutputRefused

end Minidregg.Compiler.ExactBasisExtension
