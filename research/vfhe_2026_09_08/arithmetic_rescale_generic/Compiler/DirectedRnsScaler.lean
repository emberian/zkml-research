/- Exact directed fixed-point RNS downscaling, parameterized by both basis counts
and constructor constants. This is the source algorithm, not ideal rational rounding. -/
import Compiler.SignedMatrixEmit
import Compiler.FheSourceCertificate

namespace Minidregg.Compiler.DirectedRnsScaler
open Minidregg.Compiler Minidregg.Compiler.SignedMatrix
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

structure Params (L K : Nat) where
  sourceBase : Fin L → Nat
  targetBase : Fin K → Nat
  Q : Nat
  thetaG : Fin L → Int
  thetaF : Fin L → Int
  omega : Fin L → Int
  gamma : Int
  dG : Nat
  dF : Nat
  wOffset : Nat
  uOffset : Nat

structure Valid {L K : Nat} (p : Params L K) : Prop where
  qPos : 0 < p.Q
  gPos : 0 < p.dG
  fPos : 0 < p.dF
  sourcePos : ∀ i,0 < p.sourceBase i
  targetPos : ∀ i,0 < p.targetBase i
  targetDvd : ∀ i,p.targetBase i ∣ p.Q

def roundDiv (x : Int) (d : Nat) : Int := (2*x+d)/(2*d)
def v {L K : Nat} (p : Params L K) (r : Fin L → Int) := roundDiv (∑ i,r i*p.thetaG i) p.dG
def w {L K : Nat} (p : Params L K) (r : Fin L → Int) := roundDiv (∑ i,r i*p.thetaF i) p.dF
def output {L K : Nat} (p : Params L K) (r : Fin L → Int) := (∑ i,r i*p.omega i)-p.gamma*v p r+w p r

structure Certificate (K : Nat) where
  v : Int
  w : Int
  gRem : Int
  fRem : Int
  y : Int
  u : Int
  targetQuot : Fin K → Int

def Accepts {L K : Nat} (p : Params L K) (r : Fin L → Int) (out : Fin K → Int) (c : Certificate K) : Prop :=
  (∀ i,0 ≤ r i ∧ r i < p.sourceBase i) ∧
  0 ≤ c.gRem ∧ c.gRem < 2*p.dG ∧ 0 ≤ c.fRem ∧ c.fRem < 2*p.dF ∧
  0 ≤ c.y ∧ c.y < p.Q ∧
  2*(∑ i,r i*p.thetaG i)+p.dG=2*p.dG*c.v+c.gRem ∧
  2*(∑ i,r i*p.thetaF i)+p.dF=2*p.dF*c.w+c.fRem ∧
  (∑ i,r i*p.omega i)-p.gamma*c.v+c.w=p.Q*c.u+c.y ∧
  (∀ i,0 ≤ out i ∧ out i < p.targetBase i ∧ c.y=p.targetBase i*c.targetQuot i+out i)

def CertificateSound : Prop := ∀ {L K} (p : Params L K),Valid p → ∀ r out c,
  Accepts p r out c → ∀ i,out i=output p r%(p.targetBase i : Int)

theorem certificateSound : CertificateSound := by
  intro L K p hp r out c h i
  rcases h with ⟨hr,hg0,hg1,hf0,hf1,hy0,hy1,hg,hf,hy,ht⟩
  have hv := FheSourceCertificate.qr_forced _ _ _ _ (by exact_mod_cast (show 0<2*p.dG by omega)) hg0 hg1 hg
  have hw := FheSourceCertificate.qr_forced _ _ _ _ (by exact_mod_cast (show 0<2*p.dF by omega)) hf0 hf1 hf
  change c.v=v p r at hv
  change c.w=w p r at hw
  rw [hv,hw] at hy
  change output p r=p.Q*c.u+c.y at hy
  have hy' : c.y=output p r%(p.Q : Int) := by
    rw [hy,Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_eq_of_lt hy0 hy1,Int.emod_eq_of_lt hy0 hy1]
  have hti := ht i
  have hout : out i=c.y%(p.targetBase i : Int) := by
    rw [hti.2.2,Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_eq_of_lt hti.1 hti.2.1,Int.emod_eq_of_lt hti.1 hti.2.1]
  rw [hout,hy',Int.emod_emod_of_dvd]
  exact_mod_cast hp.targetDvd i

def honest {L K : Nat} (p : Params L K) (r : Fin L → Int) : Certificate K where
  v := v p r
  w := w p r
  gRem := (2*(∑ i,r i*p.thetaG i)+p.dG)%(2*p.dG)
  fRem := (2*(∑ i,r i*p.thetaF i)+p.dF)%(2*p.dF)
  y := output p r%p.Q
  u := output p r/p.Q
  targetQuot := fun i => (output p r%p.Q)/(p.targetBase i)

theorem honest_accepts {L K : Nat} (p : Params L K) (hp : Valid p) (r : Fin L → Int)
    (hr : ∀ i,0 ≤ r i ∧ r i < p.sourceBase i) :
    Accepts p r (fun i => (output p r%p.Q)%(p.targetBase i)) (honest p r) := by
  have hg : (0 : Int)<2*p.dG := by exact_mod_cast (show 0<2*p.dG by have := hp.gPos; omega)
  have hf : (0 : Int)<2*p.dF := by exact_mod_cast (show 0<2*p.dF by have := hp.fPos; omega)
  have hq : (0 : Int)<p.Q := by exact_mod_cast hp.qPos
  refine ⟨hr,Int.emod_nonneg _ (ne_of_gt hg),Int.emod_lt_of_pos _ hg,
    Int.emod_nonneg _ (ne_of_gt hf),Int.emod_lt_of_pos _ hf,
    Int.emod_nonneg _ (ne_of_gt hq),Int.emod_lt_of_pos _ hq,?_,?_,?_,?_⟩
  · exact (Int.mul_ediv_add_emod _ _).symm
  · exact (Int.mul_ediv_add_emod _ _).symm
  · exact (Int.mul_ediv_add_emod _ _).symm
  · intro i
    have ht : (0 : Int)<p.targetBase i := by exact_mod_cast hp.targetPos i
    exact ⟨Int.emod_nonneg _ (ne_of_gt ht),Int.emod_lt_of_pos _ ht,(Int.mul_ediv_add_emod _ _).symm⟩

-- One signed affine matrix, with shared Y and per-target canonical projections.
def groups (L K : Nat) := 2*L+9+3*K
def residue {L K : Nat} (i : Fin L) : Fin (groups L K) := ⟨i.val,by dsimp [groups]; omega⟩
def inputSlack {L K : Nat} (i : Fin L) : Fin (groups L K) := ⟨L+i.val,by dsimp [groups]; omega⟩
def extra {L K : Nat} (i : Fin 9) : Fin (groups L K) := ⟨2*L+i.val,by dsimp [groups]; omega⟩
def target {L K : Nat} (i : Fin K) (j : Fin 3) : Fin (groups L K) := ⟨2*L+9+3*i.val+j.val,by dsimp [groups]; omega⟩
def linear {L K : Nat} (a : Fin L → Int) : Row (groups L K) := sum (fun i => scale (a i) (var (residue i)))
def inputRow {L K : Nat} (p : Params L K) (i : Fin L) : Row (groups L K) := sub (add (var (residue i)) (var (inputSlack i))) (SignedMatrix.cst (p.sourceBase i-1 : Int))
def gRow {L K : Nat} (p : Params L K) : Row (groups L K) := sub (add (scale 2 (linear p.thetaG)) (SignedMatrix.cst p.dG))
  (add (scale (2*p.dG) (var (extra 0))) (var (extra 1)))
def gBound {L K : Nat} (p : Params L K) : Row (groups L K) := sub (add (var (extra 1)) (var (extra 2))) (SignedMatrix.cst (2*p.dG-1 : Int))
def fRow {L K : Nat} (p : Params L K) : Row (groups L K) := sub (add (scale 2 (linear p.thetaF)) (SignedMatrix.cst p.dF))
  (add (scale (2*p.dF) (sub (var (extra 3)) (SignedMatrix.cst p.wOffset))) (var (extra 4)))
def fBound {L K : Nat} (p : Params L K) : Row (groups L K) := sub (add (var (extra 4)) (var (extra 5))) (SignedMatrix.cst (2*p.dF-1 : Int))
def yRow {L K : Nat} (p : Params L K) : Row (groups L K) := sub
  (add (sub (linear p.omega) (scale p.gamma (var (extra 0)))) (sub (var (extra 3)) (SignedMatrix.cst p.wOffset)))
  (add (scale p.Q (sub (var (extra 8)) (SignedMatrix.cst p.uOffset))) (var (extra 6)))
def yBound {L K : Nat} (p : Params L K) : Row (groups L K) := sub (add (var (extra 6)) (var (extra 7))) (SignedMatrix.cst (p.Q-1 : Int))
def targetRow {L K : Nat} (p : Params L K) (i : Fin K) : Row (groups L K) := sub (var (extra 6))
  (add (scale (p.targetBase i) (var (target i 1))) (var (target i 0)))
def targetBound {L K : Nat} (p : Params L K) (i : Fin K) : Row (groups L K) := sub
  (add (var (target i 0)) (var (target i 2))) (SignedMatrix.cst (p.targetBase i-1 : Int))
def forms {L K : Nat} (p : Params L K) : List (Row (groups L K)) :=
  (List.finRange L).map (inputRow p) ++ [gRow p,gBound p,fRow p,fBound p,yRow p,yBound p] ++
  (List.finRange K).flatMap (fun i => [targetRow p i,targetBound p i])
def Balanced {L K : Nat} (p : Params L K) (x : Fin (groups L K) → Nat) : Prop := ∀ row ∈ forms p,SignedMatrix.eval row x=0

def readCertificate {L K : Nat} (p : Params L K) (x : Fin (groups L K) → Nat) : Certificate K where
  v := x (extra 0)
  w := (x (extra 3) : Int)-p.wOffset
  gRem := x (extra 1)
  fRem := x (extra 4)
  y := x (extra 6)
  u := (x (extra 8) : Int)-p.uOffset
  targetQuot := fun i => x (target i 1)

def MatrixSound : Prop := ∀ {L K} (p : Params L K),Valid p → ∀ x,Balanced p x →
  ∀ i,(x (target i 0) : Int)=output p (fun j => x (residue j))%(p.targetBase i : Int)

theorem balanced_accepts {L K : Nat} (p : Params L K) (_hp : Valid p) (x : Fin (groups L K) → Nat)
    (h : Balanced p x) : Accepts p (fun j => x (residue j)) (fun i => x (target i 0)) (readCertificate p x) := by
  have hinput (i : Fin L) := h (inputRow p i) (by simp [forms])
  have hg := h (gRow p) (by simp [forms])
  have hgb := h (gBound p) (by simp [forms])
  have hf := h (fRow p) (by simp [forms])
  have hfb := h (fBound p) (by simp [forms])
  have hy := h (yRow p) (by simp [forms])
  have hyb := h (yBound p) (by simp [forms])
  have ht (i : Fin K) := h (targetRow p i) (by apply List.mem_append.mpr; right; exact List.mem_flatMap.mpr ⟨i,by simp,by simp⟩)
  have htb (i : Fin K) := h (targetBound p i) (by apply List.mem_append.mpr; right; exact List.mem_flatMap.mpr ⟨i,by simp,by simp⟩)
  simp only [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,linear,
    eval_sub,eval_add,eval_scale,eval_sum,eval_var,SignedMatrix.eval_cst] at hinput hg hgb hf hfb hy hyb ht htb
  have comm (a : Fin L → Int) : (∑ i,a i*(x (residue i) : Int))=∑ i,(x (residue i) : Int)*a i := by
    apply Finset.sum_congr rfl; intro i _; ring
  simp only [comm] at hg hf hy
  refine ⟨?_,by dsimp [readCertificate]; positivity,?_,by dsimp [readCertificate]; positivity,?_,
    by dsimp [readCertificate]; positivity,?_,?_,?_,?_,?_⟩
  · intro i; have := hinput i; dsimp only; constructor <;> omega
  · dsimp [readCertificate]; omega
  · dsimp [readCertificate]; omega
  · dsimp [readCertificate]; omega
  · dsimp [readCertificate]; linarith
  · dsimp [readCertificate]; linarith
  · dsimp [readCertificate]; linarith
  · intro i; have h1 := ht i; have h2 := htb i
    dsimp [readCertificate]
    exact ⟨by positivity,by omega,by linarith⟩

theorem matrixSound : MatrixSound := by
  intro L K p hp x hx
  exact certificateSound p hp _ _ _ (balanced_accepts p hp x hx)

end Minidregg.Compiler.DirectedRnsScaler

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.certificateSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.certificateSound

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.honest_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.honest_accepts

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.balanced_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.balanced_accepts

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.matrixSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.matrixSound
