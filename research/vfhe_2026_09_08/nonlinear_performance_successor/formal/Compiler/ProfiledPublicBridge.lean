/- The original public output argument on an arbitrary old assignment;
no compact source, index enumeration, or range profile is imported. -/
import Compiler.ProfiledRowCoverage
import Compiler.BasisExtensionPublic
import Compiler.NonlinearRnsProfiled
namespace Minidregg.Compiler.ProfiledPublicBridge
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000

theorem extensionMatrixPublic (old : Nat → BabyBear) (hz : old 84=0)
    (hm : ∀ i : Fin ActualBasisExtension.profile.rows,SignedMatrix.eval (ActualBasisExtension.rows i)
      (decoded ActualBasisExtension.profile (old ∘ ActualBasisExtension.wireMap))=0) :
    (∀ i,ActualBasisExtension.publicInput old i<ActualBasisExtension.params.source i) ∧
    (∀ i,ActualBasisExtension.publicCopy old i=ActualBasisExtension.publicInput old i) ∧
    ∀ i,(ActualBasisExtension.publicNew old i : Int)=ActualBasisExtension.nativeOutput
      (fun j => ActualBasisExtension.publicInput old j) i := by
  have hb := ProfiledRowCoverage.extensionBalanced _ hm
  obtain ⟨hin,hcopy,hout⟩ := ExactBasisExtension.matrixSound ActualBasisExtension.params
    ActualBasisExtension.paramsValid _ hb
  have hi := ActualBasisExtension.input_public old hz
  have hc := ActualBasisExtension.copy_public old hz
  have hn := ActualBasisExtension.new_public old hz
  have hin' : ∀ i,ActualBasisExtension.publicInput old i<ActualBasisExtension.params.source i := by
    intro i;rw [← congrFun hi i];exact hin i
  refine ⟨hin',?_,?_⟩
  · intro i;rw [← congrFun hc i,← congrFun hi i];exact hcopy i
  · intro i
    have h := hout i
    have hzinput := congrArg (fun f : Fin 4 → Nat => fun j => (f j : Int)) hi
    dsimp only at hzinput
    rw [congrFun hn i,hzinput] at h
    exact h.trans (ActualBasisExtension.nativeAgreement _
      (fun j => ⟨by positivity,by exact_mod_cast hin' j⟩) i)


theorem rescaleMatrixPublic (old : Nat → BabyBear) (hz : old 88=0)
    (hm : ∀ i : Fin NonlinearRnsInstance.profile.rows,SignedMatrix.eval (NonlinearRnsInstance.rows i)
      (decoded NonlinearRnsInstance.profile (old ∘ NonlinearRnsPublic.wireMap))=0) :
    ∀ i,(NonlinearRnsPublic.publicOutput old i : Int)=NonlinearRnsInstance.nativeProjectedOutput
      (NonlinearRnsPublic.publicResidues old) i := by
  intro i
  have hb := ProfiledRowCoverage.rescaleBalanced _ hm
  have hc := DirectedRnsScaler.balanced_accepts NonlinearRnsInstance.params NonlinearRnsInstance.paramsValid _ hb
  have hw := NonlinearRnsInstance.nativeWordRefinement _ hc.1
  have hout := DirectedRnsScaler.matrixSound NonlinearRnsInstance.params NonlinearRnsInstance.paramsValid _ hb i
  rw [← hw,NonlinearRnsPublic.input_public old hz,congrFun (NonlinearRnsPublic.output_public old hz) i,
    NonlinearRnsInstance.canonical_lift_preserves_native] at hout
  exact hout


end Minidregg.Compiler.ProfiledPublicBridge
/-- info: 'Minidregg.Compiler.ProfiledPublicBridge.extensionMatrixPublic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledPublicBridge.extensionMatrixPublic
/-- info: 'Minidregg.Compiler.ProfiledPublicBridge.rescaleMatrixPublic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledPublicBridge.rescaleMatrixPublic
