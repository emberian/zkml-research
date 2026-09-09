/- Compiler-derived polynomial reading, ordered challenge batching, and quotient OOD.
The source is the existing AirSig; no parallel arithmetic syntax is introduced. -/
import Compiler.Ir2WholeRow
import Theory.PolynomialCurve
import Selvage.LogupStar
import Selvage.BabyBearExt4
import Selvage.Ir2PcsPackedSoundness

namespace Minidregg.Compiler.AirPolynomialOod
open Polynomial Minidregg.Selvage
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
variable {F E Idx : Type} [Field F] [Field E]

/-- A ring-valued reading of the existing source, with explicit constant embedding. -/
def readAlg {R : Type} [CommRing R] (φ : F →+* R) (asg : Idx → R) : Alg (AirSig F Idx) R :=
  fun op => match op with
  | .const c => fun _ => φ c
  | .var i => fun _ => asg i
  | .add => fun k => k false+k true
  | .mul => fun k => k false*k true

def read {R : Type} [CommRing R] (φ : F →+* R) (asg : Idx → R) := fold (readAlg φ asg)

/-- Naturalness follows from the source's initiality, one equation per operation. -/
theorem map_read {R S : Type} [CommRing R] [CommRing S]
    (φ : F →+* R) (ψ : R →+* S) (asg : Idx → R) (t : Term (AirSig F Idx)) :
    ψ (read φ asg t)=read (ψ.comp φ) (fun i => ψ (asg i)) t := by
  apply congrFun (fold_unique (readAlg (ψ.comp φ) (fun i => ψ (asg i)))
    (fun t => ψ (read φ asg t)) ?_) t
  intro op k
  cases op <;> simp [read,readAlg,fold_mk,map_add,map_mul]

theorem read_id (asg : Idx → F) (t : Term (AirSig F Idx)) :
    read (RingHom.id F) asg t=eval asg t := rfl

def lift (φ : F →+* E) (columns : Idx → E[X]) := read (Polynomial.C.comp φ) columns

/-- Polynomial evaluation is the original arithmetic evaluated at column evaluations. -/
theorem lift_eval (φ : F →+* E) (columns : Idx → E[X]) (z : E)
    (t : Term (AirSig F Idx)) :
    (lift φ columns t).eval z = read φ (fun i => (columns i).eval z) t := by
  have hh : (Polynomial.evalRingHom z).comp (Polynomial.C.comp φ)=φ := by
    ext c
    simp
  simpa only [lift,hh,Polynomial.coe_evalRingHom] using map_read (Polynomial.C.comp φ) (Polynomial.evalRingHom z) columns t

/-- On a base-domain row the polynomial reading is exactly the original source. -/
theorem lift_source (φ : F →+* E) (columns : Idx → E[X]) (z : E)
    (asg : Idx → F) (h : ∀ i,(columns i).eval z=φ (asg i))
    (t : Term (AirSig F Idx)) : (lift φ columns t).eval z=φ (eval asg t) := by
  rw [lift_eval]
  simp_rw [h]
  exact (map_read (RingHom.id F) φ asg t).symm

/-- Coefficients are in ascending gamma degree. For native fold-left order,
coefficient j is the constraint at reversed position M-j. -/
def batch {M : ℕ} (constraints : Fin (M+1) → E[X]) (γ : E) : E[X] :=
  ∑ j, C (γ^j.val)*constraints j

def rowCurve {M : ℕ} (constraints : Fin (M+1) → E[X]) (r : E) : E[X] :=
  PolynomialCurve.poly (fun j => (constraints j).eval r)

theorem batch_at_row {M : ℕ} (constraints : Fin (M+1) → E[X]) (γ r : E) :
    (batch constraints γ).eval r=(rowCurve constraints r).eval γ := by
  simp [batch,rowCurve,PolynomialCurve.eval_poly,Polynomial.eval_finsetSum]

/-- Finite powers are exactly Horner evaluation of the ascending coefficient list. -/
theorem sum_eq_horner {R : Type} [CommRing R] (n : ℕ) (v : Fin n → R) (γ : R) :
    (∑ j,γ^j.val*v j)=(List.ofFn v).foldr (fun c acc => c+γ*acc) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,List.ofFn_succ,List.foldr_cons,← ih]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- The batch definition equals the native left fold on reversed coefficients. -/
theorem batch_horner {M : ℕ} (constraints : Fin (M+1) → E[X]) (γ : E) :
    batch constraints γ=(List.ofFn constraints).reverse.foldl (fun acc c => C γ*acc+c) 0 := by
  rw [List.foldl_reverse]
  unfold batch
  simp_rw [Polynomial.C_pow]
  convert sum_eq_horner (M+1) constraints (C γ) using 1
  congr 1
  funext c acc
  ring

/-- A single nonzero source constraint makes the gamma polynomial nonzero. -/
theorem row_curve_nonzero {M : ℕ} (constraints : Fin (M+1) → E[X]) (r : E)
    (j : Fin (M+1)) (h : (constraints j).eval r ≠ 0) : rowCurve constraints r ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : E[X] => p.coeff j.val) hz
  change (rowCurve constraints r).coeff j.val=(0:E[X]).coeff j.val at hc
  rw [rowCurve,PolynomialCurve.coeff_poly,Polynomial.coeff_zero] at hc
  exact h hc

/-- Exact quotient residual. The quotient may depend on gamma, but precedes zeta. -/
def residual {M : ℕ} (constraints : Fin (M+1) → E[X])
    (vanishing : E[X]) (quotient : E → E[X]) (γ : E) : E[X] :=
  batch constraints γ-vanishing*quotient γ

theorem residual_nonzero {M : ℕ} (constraints : Fin (M+1) → E[X])
    (vanishing : E[X]) (quotient : E → E[X]) (r γ : E)
    (hr : vanishing.eval r=0) (hγ : (rowCurve constraints r).eval γ ≠ 0) :
    residual constraints vanishing quotient γ ≠ 0 := by
  intro h
  apply hγ
  have he := congrArg (fun p : E[X] => p.eval r) h
  simpa [residual,Polynomial.eval_sub,Polynomial.eval_mul,hr,batch_at_row] using he

/-- Statement-first two-stage AIR challenge theorem. Constraints and an erroneous
base row precede gamma; the quotient can depend on gamma, never on zeta. -/
def OodSoundness [Fintype E] : Prop :=
  ∀ (M D : ℕ) (constraints : Fin (M+1) → E[X]) (vanishing : E[X])
    (quotient : E → E[X]) (r : E),
    vanishing.eval r=0 → (∃ j,(constraints j).eval r ≠ 0) →
    (∀ γ,(residual constraints vanishing quotient γ).natDegree ≤ D) →
    uniformProb (E×E) (fun x => (residual constraints vanishing quotient x.1).eval x.2=0)
      ≤ (M:ℝ)/Fintype.card E+(D:ℝ)/Fintype.card E

theorem ood_soundness [Fintype E] : OodSoundness (E := E) := by
  intro M D constraints vanishing quotient r hr hbad hdeg
  obtain ⟨j,hj⟩ := hbad
  let bad : E → Prop := fun γ => (rowCurve constraints r).eval γ=0
  let good : E×E → Prop := fun x => ¬bad x.1 ∧ (residual constraints vanishing quotient x.1).eval x.2=0
  have hb : uniformProb (E×E) (fun x => bad x.1) ≤ (M:ℝ)/Fintype.card E := by
    have hs := uniformProb_equiv (Equiv.prodComm E E) (fun x : E×E => bad x.2)
    simp only [Equiv.prodComm_apply,Prod.swap] at hs
    rw [hs,uniformProb_prod_snd]
    exact uniformProb_poly_eval_eq_zero_le _ (row_curve_nonzero constraints r j hj)
      (PolynomialCurve.natDegree_poly _)
  have hg : uniformProb (E×E) good ≤ (D:ℝ)/Fintype.card E := by
    apply uniformProb_prod_le (by positivity)
    intro γ
    by_cases h : bad γ
    · rw [uniformProb_false (fun _ hh => hh.1 h)]
      positivity
    · exact (uniformProb_mono fun _ hh => hh.2).trans
        (uniformProb_poly_eval_eq_zero_le _ (residual_nonzero constraints vanishing quotient r γ hr h) (hdeg γ))
  have hc : ∀ x : E×E,(residual constraints vanishing quotient x.1).eval x.2=0 → bad x.1 ∨ good x := by
    intro x hx
    by_cases h : bad x.1
    · exact Or.inl h
    · exact Or.inr ⟨h,hx⟩
  exact ((uniformProb_mono hc).trans (uniformProb_or_le _ _)).trans (add_le_add hb hg)

end
end Minidregg.Compiler.AirPolynomialOod

/-- info: 'Minidregg.Compiler.AirPolynomialOod.map_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.map_read

/-- info: 'Minidregg.Compiler.AirPolynomialOod.read_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.read_id

/-- info: 'Minidregg.Compiler.AirPolynomialOod.lift_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.lift_eval

/-- info: 'Minidregg.Compiler.AirPolynomialOod.lift_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.lift_source

/-- info: 'Minidregg.Compiler.AirPolynomialOod.batch_at_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.batch_at_row

/-- info: 'Minidregg.Compiler.AirPolynomialOod.sum_eq_horner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.sum_eq_horner

/-- info: 'Minidregg.Compiler.AirPolynomialOod.batch_horner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.batch_horner

/-- info: 'Minidregg.Compiler.AirPolynomialOod.row_curve_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.row_curve_nonzero

/-- info: 'Minidregg.Compiler.AirPolynomialOod.residual_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.residual_nonzero

/-- info: 'Minidregg.Compiler.AirPolynomialOod.ood_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.AirPolynomialOod.ood_soundness

