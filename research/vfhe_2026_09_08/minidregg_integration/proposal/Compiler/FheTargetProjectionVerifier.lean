/- A composition of two existing emitted checks with an explicit shared integer
claim. Both arrays are full assignments; proof-protocol authentication remains
separate. No change to the frozen source descriptor is needed. -/
import Compiler.FheTargetProjectionEmit
import Compiler.AirSimplify

namespace Minidregg.Compiler.FheTargetProjection
open Minidregg.Compiler
open Minidregg.Compiler.AirSimplify
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

def optimizedTargetDescriptor : ConstraintDescriptor BabyBear :=
  cse (emitSimplified Fin.val 0 7282 sourceSystem)

/-- Generic simplification and CSE preserve the full target balance relation. -/
theorem optimizedTargetDescriptor_balanced (v : ℕ → BabyBear)
    (hd : descriptorHolds optimizedTargetDescriptor v) : Balanced (decoded v) := by
  let asg : Fin 7282 → BabyBear := fun i => v i.val
  have hs := (cse_emitSimplified_accepts_iff Fin.val Fin.val_injective 0 7282
    (fun i : Fin 7282 => i.isLt) asg sourceSystem).mp ⟨v,fun _ => rfl,hd⟩
  obtain ⟨v',hp,hd'⟩ := (emit_accepts_iff_fin 7282 0 asg sourceSystem).mpr hs
  have hc := sourceDescriptor_balanced v' hd'
  have he : decoded v'=decoded v := by
    funext g
    apply Finset.sum_congr rfl
    intro d _
    rw [hp (scalarWire (groupDigit (g,d)))]
  simpa only [he] using hc

def pinnedTargetCheck (r : Fin 6 → ℤ) (y : ℕ) (limbs : Fin 3 → ℕ)
    (sourceAssignment targetAssignment : ℕ → BabyBear) : Bool :=
  FheSourceCertificate.pinnedSourceCheck r y sourceAssignment &&
  decide (decoded targetAssignment 0=y) &&
  decide (readLimbs (decoded targetAssignment)=limbs) &&
  descriptorHoldsCheck optimizedTargetDescriptor targetAssignment

/-- A passing extended boundary pins every canonical target limb to the exact
source result reduced modulo that target prime, including negative representatives. -/
theorem pinnedTargetCheck_sound (r : Fin 6 → ℤ) (y : ℕ) (limbs : Fin 3 → ℕ)
    (sv tv : ℕ → BabyBear) (h : pinnedTargetCheck r y limbs sv tv=true) :
    ∀ i, limbs i<targetPrime i ∧
      (limbs i : ℤ)=FheRnsScale.deployedOutput r%(targetPrime i : ℤ) := by
  simp only [pinnedTargetCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs,hy⟩,hl⟩,hd⟩ := h
  have hsource := FheSourceCertificate.pinnedSourceCheck_sound r y sv hs
  have hb := optimizedTargetDescriptor_balanced tv
    ((descriptorHoldsCheck_eq_true_iff _ _).mp hd)
  have hp := balanced_projection (decoded tv) hb
  rw [hy,hl] at hp
  intro i
  have he := projectionSound _ _ _ _ hp i
  refine ⟨?_,projection_source r y _ _ _ hsource hp i⟩
  rw [he]
  exact Nat.mod_lt _ (target_factors.2.1 i).1

/-- No choice of internal source or target assignments admits a changed first limb. -/
theorem pinned_wrong_target_refused (sv tv : ℕ → BabyBear) :
    pinnedTargetCheck FheRnsScale.capturedResidues 172481 ![172480,172481,172481] sv tv=false := by
  cases hh : pinnedTargetCheck FheRnsScale.capturedResidues 172481 ![172480,172481,172481] sv tv with
  | false => rfl
  | true =>
    have h := (pinnedTargetCheck_sound _ _ _ _ _ hh 0).2
    rw [FheRnsScale.deployed_witness_inhabited.2.2.1] at h
    norm_num [targetPrime] at h

/-- The first certificate remains inhabited when an external target claim is
changed; the new projection boundary is the constraint that refuses it. -/
theorem coherent_boundary_falsifier :
    FheSourceCertificate.accepts FheRnsScale.capturedResidues 172481
      (FheSourceCertificate.honestCertificate FheRnsScale.capturedResidues) ∧
    (∀ quotients slacks,¬ Projection 172481 ![172480,172481,172481] quotients slacks) :=
  ⟨FheSourceCertificate.actual_plus_one_inhabited,captured_wrong_limb⟩

end Minidregg.Compiler.FheTargetProjection

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheTargetProjection.optimizedTargetDescriptor_balanced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.optimizedTargetDescriptor_balanced

/-- info: 'Minidregg.Compiler.FheTargetProjection.pinnedTargetCheck_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.pinnedTargetCheck_sound

/-- info: 'Minidregg.Compiler.FheTargetProjection.pinned_wrong_target_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.pinned_wrong_target_refused

/-- info: 'Minidregg.Compiler.FheTargetProjection.coherent_boundary_falsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.coherent_boundary_falsifier
