import Compiler.BasisExtensionLayout

namespace Minidregg.Compiler.ActualBasisExtension
open Minidregg.Compiler Minidregg.Compiler.ExactBasisExtension
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

theorem fixed_ranges : (∀ i,0≤params.theta i ∧ params.theta i≤(2^127 : Int)) ∧
    (∑ i,(params.source i : Int))<(2^52 : Int) := by
  constructor
  · intro i; fin_cases i <;> decide
  · decide

theorem garner_range (r : Fin 4 → Int) (hr : ∀ i,0≤r i ∧ r i<params.source i) :
    0≤(∑ i,r i*params.theta i) ∧ (∑ i,r i*params.theta i)<(2^191 : Int) := by
  have mass : (∑ i,r i)<(2^52 : Int) :=
    lt_of_le_of_lt (Finset.sum_le_sum fun i _ => (hr i).2.le) fixed_ranges.2
  have hn : 0≤∑ i,r i*params.theta i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hr i).1 (fixed_ranges.1 i).1
  have h := FheRnsScale.weighted_accumulator_bound r params.theta (2^52) (2^127)
    (fun i => (hr i).1) (fun i => by rw [abs_of_nonneg (fixed_ranges.1 i).1];exact (fixed_ranges.1 i).2)
    mass (by positivity)
  rw [abs_of_nonneg hn] at h
  exact ⟨hn,lt_trans h (by norm_num)⟩

def ProjectionAgreement : Prop := ∀ i,
  Int.ModEq (params.target i) params.gamma (nativeGamma i) ∧
    ∀ j,Int.ModEq (params.target i) (params.omega j) (nativeOmega i j)
theorem projectionAgreement : ProjectionAgreement := by
  intro i
  constructor
  · fin_cases i <;> decide
  · intro j; fin_cases i <;> fin_cases j <;> decide

def nativeOutput (r : Fin 4 → Int) (i : Fin 5) : Int :=
  ((∑ j,r j*nativeOmega i j)-nativeGamma i*FheRnsScale.wordV (∑ j,r j*params.theta j) 127)%
    (params.target i : Int)
def NativeAgreement : Prop := ∀ r : Fin 4 → Int,(∀ i,0≤r i ∧ r i<params.source i) →
  ∀ i,ExactBasisExtension.output params r i=nativeOutput r i
theorem nativeAgreement : NativeAgreement := by
  intro r hr i
  have ht := garner_range r hr
  have hv : FheRnsScale.wordV (∑ j,r j*params.theta j) 127=rounded params r := by
    simpa only [rounded,FheRnsScale.roundDiv] using FheRnsScale.wordV127_correct _ ht.1 ht.2
  have hs := Int.ModEq.sum (s:=Finset.univ) (fun j _ => (projectionAgreement i).2 j |>.mul_left (r j))
  have hg := (projectionAgreement i).1.mul_right (rounded params r)
  unfold output nativeOutput
  rw [hv]
  exact (hs.sub hg).eq

/-- info: 'Minidregg.Compiler.ActualBasisExtension.fixed_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.fixed_ranges

/-- info: 'Minidregg.Compiler.ActualBasisExtension.garner_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.garner_range

/-- info: 'Minidregg.Compiler.ActualBasisExtension.projectionAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.projectionAgreement

/-- info: 'Minidregg.Compiler.ActualBasisExtension.nativeAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.nativeAgreement

end Minidregg.Compiler.ActualBasisExtension
