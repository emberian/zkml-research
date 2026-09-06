/- Closed handwritten source-equation model for the deployed six-to-three BFV
downscaler: actual correction branches, Barrett calls, Shoup products, lazy 2p
negations, u128 accumulation, and canonical output. This is not a Rust semantics,
constructor, pointer/array, NTT, or ciphertext provenance theorem. -/
import Compiler.FheBarrettWord
import Compiler.FheRnsModularAccumulation

namespace Minidregg.Compiler.FheRnsSourceWord
open Minidregg.Compiler.FheRnsScale
open Minidregg.Compiler.FheShoupWord
open Minidregg.Compiler.FheBarrettWord
open Minidregg.Compiler.FheRnsModularAccumulation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def target (i : Fin 3) : ℤ := FheTargetProjection.targetPrime i

def sourceNegative (T : ℤ) : Bool := decide (0<(T%(2^256))/(2^191))
def sourceMagnitude (T : ℤ) : ℤ :=
  if sourceNegative T then
    (((((2^256-1-T%(2^256))/(2^126))%(2^128))+1)/2)
  else
    (((((T%(2^256))/(2^126))%(2^128))+1)/2)

/-- The scalar sign/magnitude pair is exactly the existing source word branch. -/
theorem signed_magnitude (T : ℤ) : signed (sourceNegative T) (sourceMagnitude T)=wordCorrection T := by
  simp [signed,sourceNegative,sourceMagnitude,wordCorrection]
  split_ifs <;> rfl

/-- Legal signed accumulators make the magnitude fit u128, including the branch +1. -/
theorem magnitude_range (T : ℤ) (hlo : -(2^191)<T) (hhi : T<2^191) :
    0≤sourceMagnitude T ∧ sourceMagnitude T<(2^128 : ℤ) := by
  norm_num [sourceMagnitude,sourceNegative] at *
  split_ifs <;> omega

/-- The negative branch's literal u128 +1 cannot overflow under the established sign range. -/
theorem negative_increment_fits (T : ℤ) (hlo : -(2^191)<T) (hhi : T<2^191)
    (hnegative : sourceNegative T=true) :
    ((((2^256-1-T%(2^256))/(2^126))%(2^128))+1)<(2^128 : ℤ) := by
  norm_num [sourceNegative] at *
  omega

/-- Actual target moduli and split Barrett reciprocals satisfy every word-bound premise. -/
theorem target_word_bounds : ∀ i : Fin 3,
    2≤target i ∧ target i<2^62 ∧
    ((2^64 : ℤ)^2/target i)%(2^64)+((2^64 : ℤ)^2/target i)/(2^64)<2^64 := by decide

/-- Every canonical source residue is a valid full-word first operand to Shoup. -/
theorem source_rest_bounds (r : Fin 6 → ℤ) (hr : ∀ i,0≤r i ∧ r i<deployedBase i) :
    ∀ i,0≤r i ∧ r i<2^64 := by
  have hb : ∀ i : Fin 6,deployedBase i<(2^64 : ℤ) := by decide
  exact fun i => ⟨(hr i).1,lt_trans (hr i).2 (hb i)⟩

/-- The selected Garner index fits the source's u128 reduction input. -/
theorem source_v_range (r : Fin 6 → ℤ) (hr : ∀ i,0≤r i ∧ r i<deployedBase i) :
    0≤deployedV r ∧ deployedV r<(2^128 : ℤ) := by
  have h := deployed_garner_range r hr
  rw [deployedV_correct r hr]
  norm_num [roundDiv] at *
  omega

def sourceWordTarget (r : Fin 6 → ℤ) (i : Fin 3) : ℤ :=
  let p := target i
  let T := ∑ j,r j*deployedThetaF j
  let v := deployedV r
  let lg := wordLazyShoup (2^64) p (wordReduce (2^64) p v) (deployedGamma%p)
  let lw := wordLazyBarrett (2^64) p (sourceMagnitude T)
  let terms := fun j => wordLazyShoup (2^64) p (r j) (deployedOmega j%p)
  wordReduce (2^64) p (accumulation p lg lw (sourceNegative T) terms%(2^128))

def SourceWordRefinement : Prop := ∀ (r : Fin 6 → ℤ),
  (∀ j,0≤r j ∧ r j<deployedBase j) →
  ∀ i, sourceWordTarget r i=deployedOutput r%target i

/-- Every modular reduction call is exact at a deployed target, for all u128 inputs. -/
theorem target_reduce_correct (i : Fin 3) (a : ℤ) (ha0 : 0≤a) (ha : a<2^128) :
    wordReduce (2^64) (target i) a=a%target i := by
  obtain ⟨hp0,hp,hparts⟩ := target_word_bounds i
  exact wordReduce_correct _ _ _ (by norm_num) (by omega)
    (source_u64_bounds _ hp0 hp).2 ha0 (by norm_num;exact ha) hparts

/-- Closed source-equation refinement. All Shoup, Barrett, projection, lazy range,
sign and u128 accumulation premises are discharged for canonical six-limb inputs. -/
theorem sourceWordRefinement : SourceWordRefinement := by
  intro r hr i
  let p := target i
  let T := ∑ j,r j*deployedThetaF j
  let mag := sourceMagnitude T
  let vr := deployedV r
  let lg := wordLazyShoup (2^64) p (wordReduce (2^64) p vr) (deployedGamma%p)
  let lw := wordLazyBarrett (2^64) p mag
  let terms := fun j => wordLazyShoup (2^64) p (r j) (deployedOmega j%p)
  obtain ⟨hp0,hp,hparts⟩ := target_word_bounds i
  have hp' : 0<p := by dsimp [p];omega
  have hpB : 2*p<(2^64 : ℤ) := (source_u64_bounds _ hp0 hp).2
  have vBounds := source_v_range r hr
  have vReduce : wordReduce (2^64) p vr=vr%p := target_reduce_correct i vr vBounds.1 vBounds.2
  have vg0 := Int.emod_nonneg vr (ne_of_gt hp')
  have vg1 := Int.emod_lt_of_pos vr hp'
  have gg0 := Int.emod_nonneg deployedGamma (ne_of_gt hp')
  have gg1 := Int.emod_lt_of_pos deployedGamma hp'
  have glazy : 0≤lg ∧ lg<2*p ∧ lg%p=vr*deployedGamma%p := by
    have hlg : lg=remainder (2^64) p (vr%p) (deployedGamma%p) := by
      change wordLazyShoup (2^64) p (wordReduce (2^64) p vr) (deployedGamma%p)=_
      rw [vReduce,wordLazyShoup_correct _ _ _ _ (by norm_num) hp' hpB vg0 (by omega) gg0 gg1]
    rw [hlg]
    have h := shoupRefinement (2^64) p (vr%p) (deployedGamma%p) (by norm_num) hp' vg0 (by omega) gg0 gg1
    refine ⟨h.1,h.2.1,?_⟩
    rw [h.2.2]
    simp [Int.mul_emod]
  have tr := abs_lt.mp (deployed_correction_range r hr)
  have magBounds := magnitude_range T tr.1 tr.2
  have wlazy : 0≤lw ∧ lw<2*p ∧ lw%p=mag%p := by
    have hlw : lw=mag-(mag*((2^64 : ℤ)^2/p)/((2^64 : ℤ)^2))*p := by
      exact wordLazyBarrett_correct (2^64) p mag (by norm_num) (by dsimp [p];omega) hpB magBounds.1
        (by norm_num;exact magBounds.2) hparts
    rw [hlw]
    exact barrett_reference _ _ _ (by norm_num) (by dsimp [p];omega) magBounds.1 (by norm_num;exact magBounds.2)
  have tlazy := shoup_projected p r deployedOmega ⟨hp0,hp⟩ (source_rest_bounds r hr)
  have arange := six_limb_accumulator_fits p ⟨hp0,hp⟩ lg lw (sourceNegative T) terms
    ⟨glazy.1,glazy.2.1⟩ ⟨wlazy.1,wlazy.2.1⟩ (fun j => ⟨(tlazy j).1,(tlazy j).2.1⟩)
  change wordReduce (2^64) p (accumulation p lg lw (sourceNegative T) terms%(2^128)) = _
  rw [Int.emod_eq_of_lt arange.1 arange.2,
    target_reduce_correct i _ arange.1 arange.2]
  have h := modularAccumulationSound p r deployedOmega terms vr deployedGamma mag lg lw
    (sourceNegative T) glazy.2.2 wlazy.2.2 (fun j => (tlazy j).2.2)
  rw [h]
  change (integerPart r deployedOmega (deployedV r) deployedGamma+
    signed (sourceNegative T) (sourceMagnitude T))%p=deployedOutput r%p
  rw [signed_magnitude]
  rfl

/-- The actual captured nearest+1 coefficient inhabits the complete source-word model. -/
theorem captured_source_word_inhabited :
    (∀ i,0≤capturedResidues i ∧ capturedResidues i<deployedBase i) ∧
    (∀ i,sourceWordTarget capturedResidues i=172481) := by
  refine ⟨deployed_witness_inhabited.1,?_⟩
  intro i
  rw [sourceWordRefinement capturedResidues deployed_witness_inhabited.1 i,
    deployed_witness_inhabited.2.2.1]
  fin_cases i <;> norm_num [target,FheTargetProjection.targetPrime]

/-- The complete word model refuses the exact-nearest neighbor on the actual +1 row. -/
theorem captured_wrong_neighbor : sourceWordTarget capturedResidues 0 ≠ 172480 := by
  rw [captured_source_word_inhabited.2 0]
  norm_num

/-- The frozen source descriptor already enforces canonicality; callers need not
assert it again to apply the source-word refinement. -/
theorem source_check_canonical (r : Fin 6 → ℤ) (y : ℤ)
    (v : ℕ → Minidregg.Compiler.BabyBear)
    (h : FheSourceCertificate.pinnedSourceCheck r y v=true) :
    ∀ i,0≤r i ∧ r i<deployedBase i := by
  open Minidregg.Compiler Minidregg.Compiler.FheSourceCertificate
    Minidregg.Compiler.AirSimplify Minidregg.Compiler.DescriptorEval
    Minidregg.Compiler.NativeKernelPlan in
  have hc : FheSourceCertificate.accepts r y
      (FheSourceCertificate.readCertificate (FheSourceCertificate.decoded v)) := by
    simp only [pinnedSourceCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨hr,hy⟩,hd⟩ := h
    let asg : Fin 30294 → BabyBear := fun i => v i.val
    have hs := (cse_emitSimplified_accepts_iff Fin.val Fin.val_injective 0 30294
      (fun i : Fin 30294 => i.isLt) asg sourceSystem).mp
      ⟨v,fun _ => rfl,(descriptorHoldsCheck_eq_true_iff _ _).mp hd⟩
    obtain ⟨v',hp,hd'⟩ := (emit_accepts_iff_fin 30294 0 asg sourceSystem).mpr hs
    have he : decoded v'=decoded v := by
      funext g
      apply Finset.sum_congr rfl
      intro d _
      rw [hp (scalarWire (groupDigit (g,d)))]
    have hcert := balanced_source_accepts (decoded v') (sourceDescriptor_balanced v' hd')
    rw [he,hr,hy] at hcert
    exact hcert
  exact hc.1

/-- Canonical target limbs accepted by the frozen extended boundary equal the
entire handwritten source-word output, not merely an independent integer reference. -/
theorem accepted_target_matches_source (r : Fin 6 → ℤ) (y : ℕ) (limbs : Fin 3 → ℕ)
    (sv tv : ℕ → Minidregg.Compiler.BabyBear)
    (h : FheTargetProjection.pinnedTargetCheck r y limbs sv tv=true) :
    ∀ i,(limbs i : ℤ)=sourceWordTarget r i := by
  have hs := h
  simp only [FheTargetProjection.pinnedTargetCheck,Bool.and_eq_true] at hs
  have hr := source_check_canonical r y sv hs.1.1.1
  intro i
  rw [sourceWordRefinement r hr i]
  exact (FheTargetProjection.pinnedTargetCheck_sound r y limbs sv tv h i).2

end Minidregg.Compiler.FheRnsSourceWord

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.signed_magnitude' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.signed_magnitude

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.magnitude_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.magnitude_range

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.negative_increment_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.negative_increment_fits

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.target_word_bounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.target_word_bounds

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.source_rest_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.source_rest_bounds

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.source_v_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.source_v_range

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.target_reduce_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.target_reduce_correct

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.sourceWordRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.sourceWordRefinement

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.captured_source_word_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.captured_source_word_inhabited

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.captured_wrong_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.captured_wrong_neighbor

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.source_check_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.source_check_canonical

/-- info: 'Minidregg.Compiler.FheRnsSourceWord.accepted_target_matches_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheRnsSourceWord.accepted_target_matches_source
