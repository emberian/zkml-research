/- Executed checks through the existing emitted-descriptor checker. These checks
are logged execution evidence, not axioms or a claim about a Rust compiler. -/
import Compiler.FheTargetProjectionWitness

namespace Minidregg.Compiler.FheTargetProjection
open Minidregg.Compiler
open Minidregg.Compiler.FheRnsScale
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Lean (Json toJson)
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000


def certificateDigits (x : Fin 10 → ℕ) (i : Fin 190) : ℕ :=
  digit 64 (x (groupDigit.symm i).1) (groupDigit.symm i).2.val

def sourceCarry (c : ℕ) (coeff : Fin 190 → ℕ) (x : Fin 190 → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => (digit 64 c i+∑ j, digit 64 (coeff j) i*x j+sourceCarry c coeff x i)/64

def installGroup (a : Array BabyBear) (offset bits : ℕ) (values : Array ℕ) : Array BabyBear := Id.run do
  let mut a := a
  for i in [:values.size] do
    a := a.set! (offset+i) (values[i]! : BabyBear)
    for j in [:bits] do
      a := a.set! (offset+values.size+bits*i+j) (digit 2 values[i]! j : BabyBear)
  return a

def cachedCarries (c : ℕ) (coeff ds : Array ℕ) : Array ℕ := Id.run do
  let mut carry := 0
  let mut result := #[0]
  for column in [:26] do
    let mut mass := digit 64 c column+carry
    for j in [:190] do
      mass := mass+digit 64 coeff[j]! column*ds[j]!
    carry := mass/64
    result := result.push carry
  return result

def sourceVariableArray (x : Fin 10 → ℕ) : Array BabyBear := Id.run do
  let xv := Array.ofFn x
  let ds := Array.ofFn (certificateDigits (fun i => xv[i.val]!))
  let mut a := installGroup (Array.replicate 7282 0) 0 6 ds
  for row in List.finRange 6 do
    let c := leftConstant row
    let l := Array.ofFn (digitCoefficient (leftMatrix row))
    let r := Array.ofFn (digitCoefficient (rightMatrix row))
    let mut total := c
    for j in [:190] do total := total+l[j]!*ds[j]!
    a := installGroup a (resultStart row) 6 ((List.range 26).toArray.map (digit 64 total))
    a := installGroup a (resultStart row+182) 14 (cachedCarries c l ds)
    a := installGroup a (resultStart row+587) 14 (cachedCarries (rightConstant row) r ds)
  return a

def sourceCheck (d : ConstraintDescriptor BabyBear) (x : Fin 10 → ℕ) : Bool :=
  let a := fillAux d (sourceVariableArray x)
  descriptorHoldsCheck d (fun i => a.getD i 0)

def readJson (name : String) : IO Json := do
  let txt ← IO.FS.readFile ("../../../experiments/bfv_lift_refinement/target_projection/"++name)
  IO.ofExcept (Json.parse txt)

def targetFilled (x : Fin 10 → ℕ) : Array BabyBear :=
  fillAux optimizedTargetDescriptor (sourceVariableArray x)

def runTargetChecks : IO Unit := do
  let sourceJson ← readJson "captured-source-variables.json"
  let sourceNats ← IO.ofExcept (Lean.fromJson? sourceJson : Except String (Array Nat))
  let sourceInitial := sourceNats.map (fun n : Nat => (n : BabyBear))
  let sf := fillAux FheSourceCertificate.optimizedSourceDescriptor sourceInitial
  let sv := fun i => sf.getD i 0
  unless FheSourceCertificate.pinnedSourceCheck capturedResidues 172481 sv do
    throw <| IO.userError "frozen source fixture refused"
  let d := optimizedTargetDescriptor
  let cap := targetValues 172481
  let tf := targetFilled cap
  let tv := fun i => tf.getD i 0
  unless pinnedTargetCheck capturedResidues 172481 (fun _ => 172481) sv tv do
    throw <| IO.userError "actual captured target array refused"
  unless sourceCheck sourceDescriptor cap do throw <| IO.userError "raw projection refused"
  if pinnedTargetCheck capturedResidues 172481 ![172480,172481,172481] sv tv then
    throw <| IO.userError "changed external limb accepted"
  let wrong := Function.update (Function.update cap 1 172480) 3 (cap 3+1)
  let wf := targetFilled wrong
  if pinnedTargetCheck capturedResidues 172481 ![172480,172481,172481] sv (fun i => wf.getD i 0) then
    throw <| IO.userError "coherent changed internal target accepted"
  let disconnected := targetValues 172480
  unless sourceCheck d disconnected do throw <| IO.userError "disconnected projection control refused"
  let df := targetFilled disconnected
  if pinnedTargetCheck capturedResidues 172481 (fun _ => 172480) sv (fun i => df.getD i 0) then
    throw <| IO.userError "shared integer claim was not pinned"
  let max := targetValues (deployedQ.toNat-1)
  unless sourceCheck d max do throw <| IO.userError "maximum canonical output refused"
  let noncanonical := Function.update (Function.update max 1 (max 1+targetPrime 0)) 2 (max 2-1)
  if sourceCheck d noncanonical then throw <| IO.userError "coherent noncanonical target accepted"
  let badDigit := (sourceVariableArray cap).set! 0 64
  let bf := fillAux d badDigit
  if descriptorHoldsCheck d (fun i => bf.getD i 0) then throw <| IO.userError "radix digit64 accepted"
  let actual ← readJson "actual-coefficients.json"
  let cases ← IO.ofExcept (actual.getObjValAs? (Array Json) "cases")
  let mut checked : Array Json := #[]
  for c in cases do
    let y ← IO.ofExcept (c.getObjValAs? Nat "canonical_output")
    let limbs ← IO.ofExcept (c.getObjValAs? (Array Nat) "actual_target_limbs")
    let x := targetValues y
    unless sourceCheck d x do throw <| IO.userError "actual retained coefficient projection refused"
    unless Array.ofFn (readLimbs x)==limbs do throw <| IO.userError "actual engine target limbs differ"
    checked := checked.push c
  let serialize := fun label expected (a : Array BabyBear) => Json.mkObj [
    ("label",toJson label),("expected",toJson expected),("initial_variables",toJson (a.map fun x => x.val))]
  let fixtures := #[serialize "captured_projection" true (sourceVariableArray cap),
    serialize "coherent_wrong_limb" false (sourceVariableArray wrong),
    serialize "disconnected_valid_projection" true (sourceVariableArray disconnected),
    serialize "maximum_projection" true (sourceVariableArray max),
    serialize "coherent_noncanonical_limb" false (sourceVariableArray noncanonical),
    serialize "out_of_range_digit" false badDigit]
  let result := Json.mkObj [("label",toJson "EXECUTED existing emitted target projection plus frozen source checker"),
    ("variables",toJson d.nVars),("raw_gates",toJson sourceDescriptor.gates.length),
    ("optimized_gates",toJson d.gates.length),("optimized_add_gates",toJson (d.gates.filter fun g => g.op==.add).length),
    ("optimized_mul_gates",toJson (d.gates.filter fun g => g.op==.mul).length),
    ("zero_checks",toJson d.zeros.length),("wires",toJson d.nWires),
    ("frozen_source_check_accepts",toJson true),("captured_full_boundary_accepts",toJson true),
    ("changed_external_target_refused",toJson true),("coherent_wrong_internal_target_refused",toJson true),
    ("valid_disconnected_projection_refused_by_shared_y_pin",toJson true),
    ("coherent_noncanonical_target_refused",toJson true),("radix_digit64_refused",toJson true),
    ("actual_projection_cases",Json.arr checked)]
  IO.FS.writeFile "../../../experiments/bfv_lift_refinement/target_projection/check-results.json" (result.pretty++"\n")
  IO.FS.writeFile "../../../experiments/bfv_lift_refinement/target_projection/retained-inputs.json"
    ((Json.mkObj [("cases",Json.arr fixtures)]).pretty++"\n")
  writeDescriptorJson "../../../experiments/bfv_lift_refinement/target_projection/optimized-descriptor.json" d
  IO.println result.pretty

#eval runTargetChecks
end Minidregg.Compiler.FheTargetProjection
