import Compiler.RangeProfiledCompact
namespace Minidregg.Compiler.RangeProfiledTransport
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.RangeProfiledCompact
set_option autoImplicit false

/-- Reassociate the pulled-back assignment at abstract parameters before
specializing a concrete matrix. No concrete matrix is normalized for this join. -/
theorem soundLeft (s : Profile) (cap : ProfiledMatrix.Capacity s.layout s.rowsLayout s.rows)
    (a : Nat → BabyBear) (hs : systemAccepts a (system s)) (hr : RangeHolds s a) :
    (a (indexMap s s.publicArity)=0) ∧ ∀ i,
      SignedMatrix.eval (s.rows i) (decoded s.layout ((a ∘ indexMap s) ∘ s.oldMap))=0 := by
  obtain ⟨hz,hm⟩ := sound s cap a hs hr
  refine ⟨hz,?_⟩
  have heq : (a ∘ indexMap s ∘ s.oldMap)=((a ∘ indexMap s) ∘ s.oldMap) := rfl
  intro i
  exact Eq.mp (congrArg (fun f => SignedMatrix.eval (s.rows i) (decoded s.layout f)=0) heq) (hm i)
end Minidregg.Compiler.RangeProfiledTransport

/-- info: 'Minidregg.Compiler.RangeProfiledTransport.soundLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledTransport.soundLeft
