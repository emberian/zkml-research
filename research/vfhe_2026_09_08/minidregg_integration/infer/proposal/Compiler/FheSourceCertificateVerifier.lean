/- Explicit statement pins for the local full-assignment checker. This is not a
succinct proof verifier: a proof protocol must authenticate these same pins and
bind the source residue vector to the committed ciphertext computation. -/
import Compiler.FheSourceCertificateOptimized

namespace Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

/-- The named claim includes the precise external residue and output values. -/
def pinnedSourceCheck (r : Fin 6 → ℤ) (output : ℤ) (v : ℕ → BabyBear) : Bool :=
  decide (readResidues (decoded v)=r) &&
  decide ((decoded v 18 : ℤ)=output) &&
  descriptorHoldsCheck optimizedSourceDescriptor v

/-- A passing real descriptor check plus explicit claim pins forces the source output. -/
theorem pinnedSourceCheck_sound (r : Fin 6 → ℤ) (output : ℤ) (v : ℕ → BabyBear)
    (h : pinnedSourceCheck r output v=true) : output=FheRnsScale.deployedOutput r % FheRnsScale.deployedQ := by
  have hh := h
  simp only [pinnedSourceCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
  obtain ⟨⟨hr,ho⟩,hc⟩ := hh
  have hd := (descriptorHoldsCheck_eq_true_iff _ _).mp hc
  have hs := optimizedSourceDescriptor_sound v hd
  rw [hr,ho] at hs
  exact hs

/-- Every assignment fails for the wrong exact-nearest claim on the captured source row. -/
theorem pinned_wrong_neighbor_refused (v : ℕ → BabyBear) :
    pinnedSourceCheck FheRnsScale.capturedResidues 172480 v=false := by
  cases hh : pinnedSourceCheck FheRnsScale.capturedResidues 172480 v with
  | false => rfl
  | true =>
    have h := pinnedSourceCheck_sound _ _ _ hh
    rw [FheRnsScale.deployed_witness_inhabited.2.2.1] at h
    norm_num [FheRnsScale.deployedQ] at h

end Minidregg.Compiler.FheSourceCertificate

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheSourceCertificate.pinnedSourceCheck_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.pinnedSourceCheck_sound

/-- info: 'Minidregg.Compiler.FheSourceCertificate.pinned_wrong_neighbor_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.pinned_wrong_neighbor_refused
