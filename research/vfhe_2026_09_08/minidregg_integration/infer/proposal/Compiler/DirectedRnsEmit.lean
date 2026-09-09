/- Reusable source/projection compiler entrypoint for arbitrary modulus counts. -/
import Compiler.DirectedRnsScaler
namespace Minidregg.Compiler.DirectedRnsScaler
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

def layout {L K : Nat} (p : Params L K) (digits bits width carry : Nat) : Layout :=
  ⟨groups L K,digits,(forms p).length,bits,width,carry⟩
def matrixRows {L K : Nat} (p : Params L K) (digits bits width carry : Nat) :
    Fin (layout p digits bits width carry).rows → Row (layout p digits bits width carry).groups :=
  fun i => (forms p).get i

def CompiledSound : Prop := ∀ {L K : Nat} (p : Params L K) digits bits width carry,
  Valid p → Capacity (layout p digits bits width carry) (matrixRows p digits bits width carry) →
  ∀ asg,systemAccepts asg (SignedMatrix.system (layout p digits bits width carry) (matrixRows p digits bits width carry)) →
  ∀ i,(decoded (layout p digits bits width carry) asg (target i 0) : Int)=
    output p (fun j => decoded (layout p digits bits width carry) asg (residue j))%(p.targetBase i : Int)

theorem compiledSound : CompiledSound := by
  intro L K p digits bits width carry hp cap asg hs
  apply matrixSound p hp
  intro row hm
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  have h := SignedMatrix.sourceSound _ _ cap asg hs i
  simpa only [matrixRows,hi] using h

end Minidregg.Compiler.DirectedRnsScaler

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.compiledSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.compiledSound
