/- Independent bounded reviewer fixture. Native census/checks below are executed
evidence, not additional universal arithmetic or proof-protocol theorems. -/
import Compiler.IntegerCertificateSimplification

open Minidregg.Compiler
open Minidregg.Compiler.AirSimplify
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan

namespace SimplificationReview

/-- The actual constructors retain the original input layout, including unused inputs. -/
theorem input_headers_unchanged (p n : Nat)
    (s : ConstraintSystem BabyBear (Fin n)) :
    (cse (emitSimplified Fin.val p n s)).nPublic=p ∧
    (cse (emitSimplified Fin.val p n s)).nVars=n := by
  exact ⟨rfl,rfl⟩

/-- An identically-zero source legitimately imposes no condition on its public input. -/
theorem vanished_dependency_is_originally_unconstrained (asg : Fin 1 → BabyBear) :
    systemAccepts asg [mul' (cst 0) (vr 0)] := by
  simp [systemAccepts_cons,systemAccepts_nil,accepts]

/-- info: 'SimplificationReview.input_headers_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SimplificationReview.input_headers_unchanged
/-- info: 'SimplificationReview.vanished_dependency_is_originally_unconstrained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SimplificationReview.vanished_dependency_is_originally_unconstrained

def check (d : ConstraintDescriptor BabyBear) (a : Array BabyBear) : Bool :=
  descriptorHoldsCheck d (fun i => a.getD i 0)

#eval show IO Unit from do
  let raw := LargeIntegerCertificateEmission.descriptor
  let opt := IntegerCertificateSimplification.Large.descriptor
  let shared := IntegerCertificateSimplification.Large.sharedDescriptor
  unless raw.gates.length == 52378 && opt.gates.length == 17344 &&
      shared.gates.length == 15208 && shared.zeros.length == 4555 &&
      shared.nWires == 21117 && shared.nVars == 3773 && shared.nPublic == 0 do
    throw (IO.userError "Large emitted census changed")
  IO.println s!"LARGE_CENSUS raw={raw.gates.length} simplified={opt.gates.length} simplified_CSE={shared.gates.length} adds={shared.gates.countP (fun g => g.op == .add)} muls={shared.gates.countP (fun g => g.op == .mul)} zeros={shared.zeros.length} public={shared.nPublic} vars={shared.nVars} wires={shared.nWires}"
  IO.println s!"REFERENCE_PARAMETERS Q={LargeIntegerCertificateEmission.Q} t={LargeIntegerCertificateEmission.t}"
  let smalls := [IntegerCertificateEmission.certificateDescriptor,
    cse IntegerCertificateEmission.certificateDescriptor,
    IntegerCertificateSimplification.Small.descriptor,
    IntegerCertificateSimplification.Small.sharedDescriptor]
  let mut count := 0
  for zEnc in [:64] do
    let z : Int := (zEnc : Int)-32
    let y := (4*z+15)/31
    let rem := ((4*z+15)%31).toNat
    for d in smalls do
      let a := Array.ofFn (IntegerCertificateEmission.assignment zEnc (y+8).toNat rem)
      let b := Array.ofFn (IntegerCertificateEmission.assignment zEnc (y+9).toNat rem)
      unless check d (fillAux d a) && !(check d (fillAux d b)) do
        throw (IO.userError s!"Small honest/forged discrepancy {zEnc}")
      count := count+1
  let dropped := emit Fin.val 1 1 (unsafeDropConstants [cst 1])
  let safe := emitSimplified Fin.val 1 1 ([cst 1] : ConstraintSystem BabyBear (Fin 1))
  unless check dropped (fillAux dropped #[7]) && !(check safe (fillAux safe #[7])) do
    throw (IO.userError "Contradictory constant control failed")
  let zero := emitSimplified Fin.val 1 1 ([mul' (cst 0) (vr 0)] : ConstraintSystem BabyBear (Fin 1))
  unless zero.nPublic == 1 && zero.nVars == 1 && zero.zeros.length == 0 &&
      check zero (fillAux zero #[7]) && check zero (fillAux zero #[9]) do
    throw (IO.userError "Vanished dependency changed input header or semantics")
  IO.println s!"SMALL_PIPELINES honest_and_wrong_pairs={count} nonzero_constant_retained=true zero_public_dependency_originally_unconstrained=true"

end SimplificationReview
