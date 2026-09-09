import Compiler.RangeProfiledProfiles
import Compiler.RangeProfiledTransport
import Compiler.ProfiledPublicBridge
namespace Minidregg.Compiler.RangeProfiledActual
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.RangeProfiledCompact
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

attribute [local irreducible] RangeProfiledCompact.indexMap RangeProfiledCompact.privateData SignedMatrix.eval SignedMatrix.decoded
  ActualBasisExtension.rows NonlinearRnsInstance.rows ActualBasisExtension.nativeOutput NonlinearRnsInstance.nativeProjectedOutput

def ExtensionResult (input copy : Fin 4 → Nat) (new : Fin 5 → Nat) : Prop :=
  (∀ i,input i<ActualBasisExtension.params.source i) ∧ (∀ i,copy i=input i) ∧
  ∀ i,(new i : Int)=ActualBasisExtension.nativeOutput (fun j => (input j : Int)) i
def RescaleResult (input : Fin 9 → Int) (output : Fin 4 → Nat) : Prop :=
  ∀ i,(output i : Int)=NonlinearRnsInstance.nativeProjectedOutput input i

def ExtensionSound : Prop := ∀ a : Nat → BabyBear,systemAccepts a (system extension) → RangeHolds extension a →
  (∀ i,ActualBasisExtension.publicInput a i<ActualBasisExtension.params.source i) ∧
  (∀ i,ActualBasisExtension.publicCopy a i=ActualBasisExtension.publicInput a i) ∧
  ∀ i,(ActualBasisExtension.publicNew a i : Int)=ActualBasisExtension.nativeOutput
    (fun j => ActualBasisExtension.publicInput a j) i
def RescaleSound : Prop := ∀ a : Nat → BabyBear,systemAccepts a (system rescale) → RangeHolds rescale a →
  ∀ i,(NonlinearRnsPublic.publicOutput a i : Int)=NonlinearRnsInstance.nativeProjectedOutput
    (NonlinearRnsPublic.publicResidues a) i

theorem extension_input (a : Nat → BabyBear) :
    ActualBasisExtension.publicInput (a ∘ indexMap extension)=ActualBasisExtension.publicInput a := by
  funext i
  apply Finset.sum_congr rfl
  intro d _
  simp only [Function.comp_apply,publicPrefix extension _ (show 1+6*i.val+d.val<extension.publicArity by
    change _<84;have := i.isLt;have := d.isLt;omega)]
theorem extension_copy (a : Nat → BabyBear) :
    ActualBasisExtension.publicCopy (a ∘ indexMap extension)=ActualBasisExtension.publicCopy a := by
  funext i
  apply Finset.sum_congr rfl
  intro d _
  simp only [Function.comp_apply,publicPrefix extension _ (show 25+6*i.val+d.val<extension.publicArity by
    change _<84;have := i.isLt;have := d.isLt;omega)]
theorem extension_new (a : Nat → BabyBear) :
    ActualBasisExtension.publicNew (a ∘ indexMap extension)=ActualBasisExtension.publicNew a := by
  funext i
  apply Finset.sum_congr rfl
  intro d _
  simp only [Function.comp_apply,publicPrefix extension _ (show 49+7*i.val+d.val<extension.publicArity by
    change _<84;have := i.isLt;have := d.isLt;omega)]

theorem extensionSound : ExtensionSound := by
  intro a hs hr
  obtain ⟨hz,hm⟩ := RangeProfiledTransport.soundLeft extension ActualBasisExtension.capacity a hs hr
  have h := ProfiledPublicBridge.extensionMatrixPublic (a ∘ indexMap extension) hz hm
  have heq := congrArg₂ Prod.mk (extension_input a)
    (congrArg₂ Prod.mk (extension_copy a) (extension_new a))
  exact Eq.mp (congrArg (fun v : (Fin 4 → Nat) × (Fin 4 → Nat) × (Fin 5 → Nat) =>
    ExtensionResult v.1 v.2.1 v.2.2) heq) h

theorem rescale_input (a : Nat → BabyBear) :
    NonlinearRnsPublic.publicResidues (a ∘ indexMap rescale)=NonlinearRnsPublic.publicResidues a := by
  funext i
  apply congrArg (fun x : Nat => (x : Int))
  apply Finset.sum_congr rfl
  intro d _
  simp only [Function.comp_apply,publicPrefix rescale _ (show 1+7*i.val+d.val<rescale.publicArity by
    change _<88;have := i.isLt;have := d.isLt;omega)]
theorem rescale_output (a : Nat → BabyBear) :
    NonlinearRnsPublic.publicOutput (a ∘ indexMap rescale)=NonlinearRnsPublic.publicOutput a := by
  funext i
  apply Finset.sum_congr rfl
  intro d _
  simp only [Function.comp_apply,publicPrefix rescale _ (show 64+6*i.val+d.val<rescale.publicArity by
    change _<88;have := i.isLt;have := d.isLt;omega)]

theorem rescaleSound : RescaleSound := by
  intro a hs hr
  obtain ⟨hz,hm⟩ := RangeProfiledTransport.soundLeft rescale NonlinearRnsProfiled.capacity a hs hr
  have h := ProfiledPublicBridge.rescaleMatrixPublic (a ∘ indexMap rescale) hz hm
  exact Eq.mp (congrArg₂ RescaleResult (rescale_input a) (rescale_output a)) h

end Minidregg.Compiler.RangeProfiledActual

/-- info: 'Minidregg.Compiler.RangeProfiledActual.extension_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.extension_input

/-- info: 'Minidregg.Compiler.RangeProfiledActual.extension_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.extension_copy

/-- info: 'Minidregg.Compiler.RangeProfiledActual.extension_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.extension_new

/-- info: 'Minidregg.Compiler.RangeProfiledActual.extensionSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.extensionSound

/-- info: 'Minidregg.Compiler.RangeProfiledActual.rescale_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.rescale_input

/-- info: 'Minidregg.Compiler.RangeProfiledActual.rescale_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.rescale_output

/-- info: 'Minidregg.Compiler.RangeProfiledActual.rescaleSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledActual.rescaleSound
