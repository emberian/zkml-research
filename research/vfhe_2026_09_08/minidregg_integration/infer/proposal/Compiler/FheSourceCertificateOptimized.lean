import Compiler.FheSourceCertificateEmit
import Compiler.AirSimplify

namespace Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler
open Minidregg.Compiler.AirSimplify
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

/-- Generic source simplification and existing CSE, with the pinned source equations intact. -/
def optimizedSourceDescriptor : ConstraintDescriptor BabyBear :=
  cse (emitSimplified Fin.val 0 30294 sourceSystem)

/-- Neither compiler optimization gives the prover a rounding choice. -/
theorem optimizedSourceDescriptor_sound : EmittedSourceSound optimizedSourceDescriptor := by
  intro v hd
  let asg : Fin 30294 → BabyBear := fun i => v i.val
  have hs := (cse_emitSimplified_accepts_iff Fin.val Fin.val_injective 0 30294
    (fun i : Fin 30294 => i.isLt) asg sourceSystem).mp ⟨v,fun _ => rfl,hd⟩
  obtain ⟨v',hp,hd'⟩ := (emit_accepts_iff_fin 30294 0 asg sourceSystem).mpr hs
  have hc := sourceDescriptor_sound v' hd'
  have he : decoded v'=decoded v := by
    funext g
    apply Finset.sum_congr rfl
    intro d _
    rw [hp (scalarWire (groupDigit (g,d)))]
  simpa only [he] using hc

theorem optimizedSourceDescriptor_wrong_neighbor (v : ℕ → BabyBear)
    (hr : readResidues (decoded v)=FheRnsScale.capturedResidues)
    (hy : decoded v 18=172480) : ¬ descriptorHolds optimizedSourceDescriptor v := by
  intro h
  have hc := optimizedSourceDescriptor_sound v h
  rw [hr,hy,FheRnsScale.deployed_witness_inhabited.2.2.1] at hc
  norm_num [FheRnsScale.deployedQ] at hc

end Minidregg.Compiler.FheSourceCertificate

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheSourceCertificate.optimizedSourceDescriptor_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.optimizedSourceDescriptor_sound

/-- info: 'Minidregg.Compiler.FheSourceCertificate.optimizedSourceDescriptor_wrong_neighbor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.optimizedSourceDescriptor_wrong_neighbor
