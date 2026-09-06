/- Statement first: RnsScaler's per-target lazy residues, 2p negations and signed
correction compose to its exact integer source representative modulo p. This
models scaler.rs:321-340 and does not assume canonical intermediate residues.
Primitive reduction correctness is explicit; Shoup is discharged by its separate
literal-word theorem. Rust arrays/unsafe access/compiler semantics remain outside. -/
import Compiler.FheShoupWord
import Mathlib.Data.Int.ModEq

namespace Minidregg.Compiler.FheRnsModularAccumulation
open Minidregg.Compiler.FheRnsScale
open Minidregg.Compiler.FheShoupWord
open scoped BigOperators
set_option autoImplicit false

def signed (negative : Bool) (w : ℤ) : ℤ := if negative then -w else w
def correctionTerm (p : ℤ) (negative : Bool) (lazyW : ℤ) : ℤ :=
  if negative then 2*p-lazyW else lazyW
def accumulation {L : ℕ} (p lazyGamma lazyW : ℤ) (negative : Bool)
    (lazyTerms : Fin L → ℤ) : ℤ :=
  2*p-lazyGamma+correctionTerm p negative lazyW+∑ i,lazyTerms i

def ModularAccumulationSound : Prop := ∀ {L : ℕ} (p : ℤ)
  (r omega lazyTerms : Fin L → ℤ) (v gamma w lazyGamma lazyW : ℤ) (negative : Bool),
  lazyGamma%p=v*gamma%p → lazyW%p=w%p →
  (∀ i,lazyTerms i%p=r i*omega i%p) →
  accumulation p lazyGamma lazyW negative lazyTerms%p=
    (integerPart r omega v gamma+signed negative w)%p

/-- Pointwise congruence is preserved by the actual finite coefficient sum. -/
theorem sum_congruent {L : ℕ} (p : ℤ) (a b : Fin L → ℤ)
    (h : ∀ i,Int.ModEq p (a i) (b i)) :
    Int.ModEq p (∑ i,a i) (∑ i,b i) := by
  have hs (s : Finset (Fin L)) : Int.ModEq p (∑ i∈s,a i) (∑ i∈s,b i) := by
    induction s using Finset.induction_on with
    | empty => simp [Int.ModEq]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i).add ih
  simpa using hs Finset.univ

/-- Exact source accumulation equation; lazy representatives may differ by p. -/
theorem modularAccumulationSound : ModularAccumulationSound := by
  intro L p r omega lazyTerms v gamma w lazyGamma lazyW negative hg hw ht
  have hp : Int.ModEq p (2*p) 0 := by simp [Int.ModEq]
  have hstart := hp.sub (show Int.ModEq p lazyGamma (v*gamma) from hg)
  have hcorr : Int.ModEq p (correctionTerm p negative lazyW) (signed negative w) := by
    cases negative with
    | false => exact hw
    | true => simpa [correctionTerm,signed] using hp.sub (show Int.ModEq p lazyW w from hw)
  have hs := sum_congruent p lazyTerms (fun i => r i*omega i) ht
  have hh := (hstart.add hcorr).add hs
  change (2*p-lazyGamma+correctionTerm p negative lazyW+∑ i,lazyTerms i)%p=
    (0-v*gamma+signed negative w+∑ i,r i*omega i)%p at hh
  rw [show 0-v*gamma+signed negative w+∑ i,r i*omega i=
    integerPart r omega v gamma+signed negative w by dsimp [integerPart];ring] at hh
  exact hh

/-- Lazy ranges make both source 2p-subtractions nonnegative and bound the u128 sum. -/
theorem accumulation_range {L : ℕ} (p lazyGamma lazyW : ℤ) (negative : Bool)
    (lazyTerms : Fin L → ℤ) (_hp : 0<p)
    (hg : 0≤lazyGamma ∧ lazyGamma<2*p) (hw : 0≤lazyW ∧ lazyW<2*p)
    (ht : ∀ i,0≤lazyTerms i ∧ lazyTerms i<2*p) :
    0≤2*p-lazyGamma ∧ 2*p-lazyGamma≤2*p ∧
    0≤correctionTerm p negative lazyW ∧ correctionTerm p negative lazyW≤2*p ∧
    0≤accumulation p lazyGamma lazyW negative lazyTerms ∧
    accumulation p lazyGamma lazyW negative lazyTerms≤((L : ℤ)+2)*(2*p) := by
  have hc : 0≤correctionTerm p negative lazyW ∧ correctionTerm p negative lazyW≤2*p := by
    cases negative <;> simp only [correctionTerm] <;> omega
  have hs0 : 0≤∑ i,lazyTerms i := Finset.sum_nonneg (fun i _ => (ht i).1)
  have hs1 : (∑ i,lazyTerms i)≤(L : ℤ)*(2*p) := by
    calc
      _ ≤ ∑ _i : Fin L,2*p := Finset.sum_le_sum (fun i _ => (ht i).2.le)
      _ = _ := by simp
  dsimp [accumulation]
  exact ⟨by omega,by omega,hc.1,hc.2,by omega,by nlinarith⟩

/-- Six source limbs and a legal 62-bit modulus cannot overflow the target u128 accumulator. -/
theorem six_limb_accumulator_fits (p : ℤ) (hp : 2≤p ∧ p<2^62)
    (lazyGamma lazyW : ℤ) (negative : Bool) (lazyTerms : Fin 6 → ℤ)
    (hg : 0≤lazyGamma ∧ lazyGamma<2*p) (hw : 0≤lazyW ∧ lazyW<2*p)
    (ht : ∀ i,0≤lazyTerms i ∧ lazyTerms i<2*p) :
    0≤accumulation p lazyGamma lazyW negative lazyTerms ∧
    accumulation p lazyGamma lazyW negative lazyTerms<(2^128 : ℤ) := by
  have h := accumulation_range p lazyGamma lazyW negative lazyTerms (by omega) hg hw ht
  norm_num at h
  exact ⟨h.2.2.2.2.1,by omega⟩

/-- Projection of the huge omega coefficient before multiplication preserves its product. -/
theorem projected_product (p a b : ℤ) : a*(b%p)%p=a*b%p := by
  simp [Int.mul_emod]

/-- The first argument is reduced for gamma, but the six rest operands need not be. -/
theorem shoup_projected {L : ℕ} (p : ℤ) (r omega : Fin L → ℤ)
    (hp : 2≤p ∧ p<2^62) (hr : ∀ i,0≤r i ∧ r i<2^64) :
    ∀ i, 0≤wordLazyShoup (2^64) p (r i) (omega i%p) ∧
      wordLazyShoup (2^64) p (r i) (omega i%p)<2*p ∧
      wordLazyShoup (2^64) p (r i) (omega i%p)%p=r i*omega i%p := by
  intro i
  have hpp := source_u64_bounds p hp.1 hp.2
  have hb0 := Int.emod_nonneg (omega i) (ne_of_gt hpp.1)
  have hb1 := Int.emod_lt_of_pos (omega i) hpp.1
  rw [wordLazyShoup_correct _ _ _ _ (by norm_num) hpp.1 hpp.2 (hr i).1 (hr i).2 hb0 hb1]
  have hs := shoupRefinement _ _ _ _ (by norm_num) hpp.1 (hr i).1 (hr i).2 hb0 hb1
  exact ⟨hs.1,hs.2.1,hs.2.2.trans (projected_product _ _ _)⟩

/-- A nontrivial signed source example uses lazy gamma, correction, and term representatives. -/
theorem lazy_signed_premises_inhabited :
    (33 : ℤ)%31=34*11%31 ∧ (35 : ℤ)%31=4%31 ∧
    (32 : ℤ)%31=1*1%31 ∧
    accumulation 31 33 35 true ![32]%31=(integerPart ![1] ![1] 34 11-4)%31 := by decide

/-- Flipping the source correction sign changes an otherwise valid modular result. -/
theorem correction_sign_falsifier :
    accumulation 31 33 35 false ![32]%31 ≠
      (integerPart ![1] ![1] 34 11-4)%31 := by decide

end Minidregg.Compiler.FheRnsModularAccumulation

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.sum_congruent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.sum_congruent

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.modularAccumulationSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.modularAccumulationSound

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.accumulation_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.accumulation_range

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.six_limb_accumulator_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.six_limb_accumulator_fits

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.projected_product' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.projected_product

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.shoup_projected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.shoup_projected

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.lazy_signed_premises_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.lazy_signed_premises_inhabited

/-- info: 'Minidregg.Compiler.FheRnsModularAccumulation.correction_sign_falsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsModularAccumulation.correction_sign_falsifier
