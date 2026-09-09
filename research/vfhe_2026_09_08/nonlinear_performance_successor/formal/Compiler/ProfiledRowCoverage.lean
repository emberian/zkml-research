/- The list/index bridge is proved with an opaque row predicate. It never
normalizes the large concrete signed rows or their evaluation functions. -/
import Compiler.ActualBasisExtension
import Compiler.NonlinearRnsInstance
namespace Minidregg.Compiler.ProfiledRowCoverage
open Minidregg.Compiler.SignedMatrix
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000

def Covers {A : Type} {n : Nat} (rows : Fin n → A) (forms : List A) : Prop :=
  ∀ P : A → Prop, (∀ i,P (rows i)) → ∀ row ∈ forms,P row

theorem of_get {A : Type} (forms : List A) : Covers forms.get forms := by
  intro P h row hr
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
  exact hi ▸ h i

theorem extensionCover : Covers ActualBasisExtension.rows
    (ExactBasisExtension.forms ActualBasisExtension.params) := by
  intro P h
  apply of_get
  intro i
  exact h ⟨i.val,by change i.val<20 at *;exact i.isLt⟩

theorem rescaleCover : Covers NonlinearRnsInstance.rows
    (DirectedRnsScaler.forms NonlinearRnsInstance.params) := by
  intro P h
  apply of_get
  intro i
  exact h ⟨i.val,by change i.val<23 at *;exact i.isLt⟩

theorem extensionBalanced (x : Fin ActualBasisExtension.profile.groups → Nat)
    (h : ∀ i,SignedMatrix.eval (ActualBasisExtension.rows i) x=0) :
    ExactBasisExtension.Balanced ActualBasisExtension.params x :=
  extensionCover (fun row => SignedMatrix.eval row x=0) h

theorem rescaleBalanced (x : Fin NonlinearRnsInstance.profile.groups → Nat)
    (h : ∀ i,SignedMatrix.eval (NonlinearRnsInstance.rows i) x=0) :
    DirectedRnsScaler.Balanced NonlinearRnsInstance.params x :=
  rescaleCover (fun row => SignedMatrix.eval row x=0) h

end Minidregg.Compiler.ProfiledRowCoverage

/-- info: 'Minidregg.Compiler.ProfiledRowCoverage.of_get' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledRowCoverage.of_get
/-- info: 'Minidregg.Compiler.ProfiledRowCoverage.extensionCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledRowCoverage.extensionCover
/-- info: 'Minidregg.Compiler.ProfiledRowCoverage.rescaleCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledRowCoverage.rescaleCover
/-- info: 'Minidregg.Compiler.ProfiledRowCoverage.extensionBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledRowCoverage.extensionBalanced
/-- info: 'Minidregg.Compiler.ProfiledRowCoverage.rescaleBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledRowCoverage.rescaleBalanced
