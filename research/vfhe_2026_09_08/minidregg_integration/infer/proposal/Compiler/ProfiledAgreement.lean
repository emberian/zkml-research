import Compiler.NonlinearRnsProfiled

namespace Minidregg.Compiler.NonlinearRnsProfiled
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

/-- Both compiler layouts force the same complete target tuple on the same input.
This is output agreement, not an unproved total auxiliary-witness bijection. -/
def LayoutAgreement : Prop := ∀ old new : Nat → BabyBear,
  systemAccepts old NonlinearRnsPublic.system → systemAccepts new system →
  NonlinearRnsPublic.publicResidues old=NonlinearRnsPublic.publicResidues new →
  NonlinearRnsPublic.publicOutput old=NonlinearRnsPublic.publicOutput new

theorem layoutAgreement : LayoutAgreement := by
  intro old new ho hn hi
  funext i
  have h1 := NonlinearRnsPublic.nativeProjectedRow_sound old ho i
  have h2 := rowSound new hn i
  rw [hi] at h1
  exact_mod_cast h1.trans h2.symm

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.layoutAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.layoutAgreement

end Minidregg.Compiler.NonlinearRnsProfiled
