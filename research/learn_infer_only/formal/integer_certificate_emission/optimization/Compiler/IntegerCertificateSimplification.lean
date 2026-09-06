/- Instantiate the generic source pass at the previously checked signed QR systems.
The original modules stay unchanged. These are compiler-path composition theorems,
not an alternate arithmetic relation or checker. -/
import Compiler.AirSimplify
import Compiler.LargeIntegerCertificateEmission

namespace Minidregg.Compiler.IntegerCertificateSimplification
open Minidregg.Compiler
open Minidregg.Compiler.AirSimplify
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan

namespace Small
open Minidregg.Compiler.IntegerCertificateEmission

def descriptor := emitSimplified Fin.val 3 115 certificateSystem
def sharedDescriptor := cse descriptor

theorem source_forces (v : Nat -> BabyBear)
    (h : systemAccepts (readVars Fin.val v) certificateSystem) :
    4 * ((v 0).val : Int) + 263 =
      31 * ((v 1).val : Int) + ((v 2).val : Int) + 128 /\ (v 2).val<31 := by
  have hc := certificateSystem_sound (readVars Fin.val v) h
  change 4*(v 0).val+263=31*(v 1).val+(v 2).val+128 /\ (v 2).val<31 at hc
  exact ⟨by exact_mod_cast hc.1,hc.2⟩

theorem descriptor_sound : CertificateSound descriptor := by
  intro v hd
  exact source_forces v (emitSimplified_forces Fin.val 3 115 certificateSystem v hd)

theorem sharedDescriptor_sound : CertificateSound sharedDescriptor := by
  intro v hd
  have hs := (cse_emitSimplified_accepts_iff Fin.val Fin.val_injective 3 115
    (fun i : Fin 115 => i.isLt) (readVars Fin.val v) certificateSystem).mp
    ⟨v,fun _ => rfl,hd⟩
  exact source_forces v hs

theorem premise_inhabited : exists v : Nat -> BabyBear, descriptorHolds descriptor v := by
  obtain ⟨v,_,hd⟩ := (emitSimplified_accepts_iff Fin.val Fin.val_injective 3 115
    (fun i : Fin 115 => i.isLt) (assignment 24 7 14) certificateSystem).mpr
    honest_assignment_accepts
  exact ⟨v,hd⟩

theorem forged_quotient_refused (v : Nat -> BabyBear) (hz : v 0=24) (hy : v 1=8) :
    ¬ descriptorHolds descriptor v := by
  intro hd
  obtain ⟨heq,hr⟩ := descriptor_sound v hd
  rw [hz,hy] at heq
  have h24 : (24 : BabyBear).val=24 := by decide +kernel
  have h8 : (8 : BabyBear).val=8 := by decide +kernel
  rw [h24,h8] at heq
  omega

end Small

namespace Large
open Minidregg.Compiler.LargeIntegerCertificateEmission

def descriptor := emitSimplified Fin.val 0 3773 system
def sharedDescriptor := cse descriptor

theorem source_forces (v : Nat -> BabyBear)
    (h : systemAccepts (readVars Fin.val v) system) :
    (t : Int)*((encoded zCoefficient v : Int)-zOffset)+(Q/2 : Nat) =
      (Q : Int)*((encoded yCoefficient v : Int)-yOffset)+encoded rCoefficient v /\
    encoded rCoefficient v<Q := by
  obtain ⟨v',hpin,hd⟩ := (emit_accepts_iff_fin 3773 0 (readVars Fin.val v) system).mpr h
  have hc := LargeIntegerCertificateEmission.descriptor_sound v' hd
  have he (cf : Fin 101 -> Nat) : encoded cf v'=encoded cf v := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hpin (scalar i)]
    rfl
  simpa only [he] using hc

theorem descriptor_sound : CertificateSound descriptor := by
  intro v hd
  exact source_forces v (emitSimplified_forces Fin.val 0 3773 system v hd)

theorem sharedDescriptor_sound : CertificateSound sharedDescriptor := by
  intro v hd
  have hs := (cse_emitSimplified_accepts_iff Fin.val Fin.val_injective 0 3773
    (fun i : Fin 3773 => i.isLt) (readVars Fin.val v) system).mp
    ⟨v,fun _ => rfl,hd⟩
  exact source_forces v hs

end Large
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Small.source_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Small.source_forces
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Small.descriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Small.descriptor_sound
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Small.sharedDescriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Small.sharedDescriptor_sound
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Small.premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Small.premise_inhabited
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Small.forged_quotient_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Small.forged_quotient_refused
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Large.source_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Large.source_forces
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Large.descriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Large.descriptor_sound
/-- info: 'Minidregg.Compiler.IntegerCertificateSimplification.Large.sharedDescriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.IntegerCertificateSimplification.Large.sharedDescriptor_sound

end Minidregg.Compiler.IntegerCertificateSimplification
