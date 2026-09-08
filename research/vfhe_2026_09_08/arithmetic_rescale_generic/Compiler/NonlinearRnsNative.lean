import Compiler.NonlinearRnsInstance
import Mathlib.Algebra.BigOperators.ModEq

namespace Minidregg.Compiler.NonlinearRnsInstance
open Minidregg.Compiler.DirectedRnsScaler
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The actual nine-source constructor selects shift125. -/
theorem wordV125_correct (T : Int) (h0 : 0 ≤ T) (h1 : T < 2^191) :
    FheRnsScale.wordV T 125=DirectedRnsScaler.roundDiv T (2^125) := by
  norm_num [FheRnsScale.wordV,DirectedRnsScaler.roundDiv] at *
  omega

theorem fixed_ranges :
    (∀ i,0 ≤ params.thetaG i ∧ params.thetaG i ≤ (2^125 : Int)) ∧
    (∀ i,|params.thetaF i| ≤ (2^126 : Int)) ∧
    (∑ i,(params.sourceBase i : Int)) < (2^65 : Int) := by
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · decide

theorem accumulator_ranges (r : Fin 9 → Int) (hr : ∀ i,0 ≤ r i ∧ r i < params.sourceBase i) :
    (0 ≤ (∑ i,r i*params.thetaG i) ∧ (∑ i,r i*params.thetaG i) < (2^191 : Int)) ∧
    |∑ i,r i*params.thetaF i| < (2^191 : Int) := by
  have mass : (∑ i,r i)<(2^65 : Int) := lt_of_le_of_lt (Finset.sum_le_sum fun i _ => (hr i).2.le) fixed_ranges.2.2
  have hn : 0 ≤ ∑ i,r i*params.thetaG i := Finset.sum_nonneg fun i _ => mul_nonneg (hr i).1 (fixed_ranges.1 i).1
  have hg := FheRnsScale.weighted_accumulator_bound r params.thetaG (2^65) (2^125)
    (fun i => (hr i).1) (fun i => by rw [abs_of_nonneg (fixed_ranges.1 i).1]; exact (fixed_ranges.1 i).2) mass (by positivity)
  have hf := FheRnsScale.weighted_accumulator_bound r params.thetaF (2^65) (2^126)
    (fun i => (hr i).1) fixed_ranges.2.1 mass (by positivity)
  rw [abs_of_nonneg hn] at hg
  constructor
  · exact ⟨hn,lt_trans hg (by norm_num)⟩
  · convert hf using 1

def wordOutput (r : Fin 9 → Int) := (∑ i,r i*params.omega i)-params.gamma*FheRnsScale.wordV (∑ i,r i*params.thetaG i) 125+
  FheRnsScale.wordCorrection (∑ i,r i*params.thetaF i)

def NativeWordRefinement : Prop := ∀ r : Fin 9 → Int,(∀ i,0 ≤ r i ∧ r i < params.sourceBase i) → wordOutput r=output params r

theorem nativeWordRefinement : NativeWordRefinement := by
  intro r hr
  have hg := (accumulator_ranges r hr).1
  have hf := abs_lt.mp (accumulator_ranges r hr).2
  rw [wordOutput,wordV125_correct _ hg.1 hg.2,FheRnsScale.wordCorrection_correct _ hf.1 hf.2]
  rfl

-- Exact target projections captured from the native constructor's public Debug fields.
def nativeGamma : Fin 4 → Int := ![189256259174533,269185146936170,309110484995418,1099828484501922]
def nativeOmega : Fin 4 → Fin 9 → Int := ![![919266481151328,614432041883277,220805836114720,1061633369902838,516694701508972,174554922464147,671366408792485,665877208589722,415993693595608],![731239734295067,978931059018830,637801756007939,851448501272091,914153916222315,216634305729285,721480138310162,866146896791901,788403813245256],![656173524129678,1017057792752850,796474426644298,1066395811428167,583750121662032,242120638803145,107688184756408,35840751676568,108640405363218],![379754679710728,172030311190824,80525252502281,547526791021708,833730950704209,90219970297635,563844343593948,650832680694208,1080848958292148]]

def ProjectionAgreement : Prop := ∀ i,
  Int.ModEq (params.targetBase i) params.gamma (nativeGamma i) ∧
  ∀ j,Int.ModEq (params.targetBase i) (params.omega j) (nativeOmega i j)

theorem projectionAgreement : ProjectionAgreement := by
  intro i
  constructor
  · fin_cases i <;> decide
  · intro j; fin_cases i <;> fin_cases j <;> decide

def nativeProjectedOutput (r : Fin 9 → Int) (i : Fin 4) : Int :=
  ((∑ j,r j*nativeOmega i j)-nativeGamma i*FheRnsScale.wordV (∑ j,r j*params.thetaG j) 125+
    FheRnsScale.wordCorrection (∑ j,r j*params.thetaF j))%(params.targetBase i : Int)

theorem canonical_lift_preserves_native (r : Fin 9 → Int) (i : Fin 4) :
    wordOutput r%(params.targetBase i : Int)=nativeProjectedOutput r i := by
  have hs := Int.ModEq.sum (s:=Finset.univ) (fun j _ => (projectionAgreement i).2 j |>.mul_left (r j))
  have hg := (projectionAgreement i).1.mul_right (FheRnsScale.wordV (∑ j,r j*params.thetaG j) 125)
  exact ((hs.sub hg).add_right (FheRnsScale.wordCorrection (∑ j,r j*params.thetaF j))).eq

end Minidregg.Compiler.NonlinearRnsInstance

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.wordV125_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.wordV125_correct

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.fixed_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.fixed_ranges

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.accumulator_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.accumulator_ranges

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.nativeWordRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.nativeWordRefinement

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.projectionAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.projectionAgreement

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.canonical_lift_preserves_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.canonical_lift_preserves_native
