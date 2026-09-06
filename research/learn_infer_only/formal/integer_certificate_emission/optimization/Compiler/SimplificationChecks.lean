import Compiler.IntegerCertificateSimplification

namespace Minidregg.Compiler.SimplificationChecks
open Minidregg.Compiler
open Minidregg.Compiler.AirSimplify
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Lean (Json toJson)

def outputDir : System.FilePath := "../../../experiments/integer_certificate_emission/optimization"
def check (d : ConstraintDescriptor BabyBear) (a : Array BabyBear) : Bool :=
  descriptorHoldsCheck d (fun i => a.getD i 0)
def count (name : String) (d : ConstraintDescriptor BabyBear) : Json :=
  let isZero : DWire BabyBear -> Bool := fun | .cnst c => c==0 | _ => false
  let isConstant : DWire BabyBear -> Bool := fun | .cnst _ => true | _ => false
  Json.mkObj [("variant",toJson name),("gates",toJson d.gates.length),
    ("add_gates",toJson (d.gates.filter fun g => g.op == .add).length),
    ("mul_gates",toJson (d.gates.filter fun g => g.op == .mul).length),
    ("zero_checks",toJson d.zeros.length),("variables",toJson d.nVars),
    ("public_variables",toJson d.nPublic),("wires",toJson d.nWires),
    ("zero_product_gates",toJson (d.gates.filter fun g =>
      g.op == .mul && (isZero g.a || isZero g.b)).length),
    ("constant_product_gates",toJson (d.gates.filter fun g =>
      g.op == .mul && (isConstant g.a || isConstant g.b)).length)]

def run : IO Unit := do
  let smallRaw := IntegerCertificateEmission.certificateDescriptor
  let smallCSE := cse smallRaw
  let smallOpt := IntegerCertificateSimplification.Small.descriptor
  let smallOptCSE := IntegerCertificateSimplification.Small.sharedDescriptor
  let largeRaw := LargeIntegerCertificateEmission.descriptor
  let largeCSE := LargeIntegerCertificateEmission.sharedDescriptor
  let largeOpt := IntegerCertificateSimplification.Large.descriptor
  let largeOptCSE := IntegerCertificateSimplification.Large.sharedDescriptor
  let variants := [("small_raw",smallRaw),("small_CSE",smallCSE),
    ("small_simplified",smallOpt),("small_simplified_CSE",smallOptCSE),
    ("large_raw",largeRaw),("large_CSE",largeCSE),
    ("large_simplified",largeOpt),("large_simplified_CSE",largeOptCSE)]
  let mut smallCases := 0
  for zEnc in List.range 64 do
    let z : Int := (zEnc : Nat)-32
    let y := (4*z+15)/31
    let r := ((4*z+15)%31).toNat
    for (_,d) in variants.take 4 do
      let honest := fillAux d (Array.ofFn (IntegerCertificateEmission.assignment zEnc (y+8).toNat r))
      unless check d honest do throw <| IO.userError s!"small honest z={z} refused"
      let bad := fillAux d (Array.ofFn (IntegerCertificateEmission.assignment zEnc (y+9).toNat r))
      if check d bad then throw <| IO.userError s!"small wrong quotient z={z} accepted"
      smallCases := smallCases+1
  let smallHonest := fillAux smallOpt (Array.ofFn (IntegerCertificateEmission.assignment 24 7 14))
  for i in List.range smallOpt.nWires do
    if check smallOpt (smallHonest.set! i (smallHonest.getD i 0+1)) then
      throw <| IO.userError s!"optimized small single-wire mutation {i} accepted"
  let Q := LargeIntegerCertificateEmission.Q
  let t := LargeIntegerCertificateEmission.t
  let zMax : Int := 8192*(Q-1)^2
  let zs : List Int := [-zMax,-zMax+1,-1,0,1,zMax-1,zMax]
  let mut largeCases := 0
  for z in zs do
    let num := (t : Int)*z+(Q/2 : Nat)
    let y := num/(Q : Int)
    let r := (num%(Q : Int)).toNat
    for (_,d) in variants.drop 4 do
      let honest := fillAux d (LargeIntegerCertificateEmission.variableArray z y r)
      unless check d honest do throw <| IO.userError s!"large honest z={z} refused"
      let badY := fillAux d (LargeIntegerCertificateEmission.variableArray z (y+1) r)
      if check d badY then throw <| IO.userError s!"large wrong quotient z={z} accepted"
      let badR := fillAux d (LargeIntegerCertificateEmission.variableArray z (y-1) (r+Q))
      if check d badR then throw <| IO.userError s!"large remainder shift z={z} accepted"
      largeCases := largeCases+1
  let falseSource : ConstraintSystem BabyBear (Fin 1) := [cst 1]
  let falseRaw := emit Fin.val 1 1 falseSource
  let falseOpt := emitSimplified Fin.val 1 1 falseSource
  let falseUnsafe := emit Fin.val 1 1 (unsafeDropConstants falseSource)
  let emptyVars : Array BabyBear := #[0]
  if check falseRaw (fillAux falseRaw emptyVars) then throw <| IO.userError "raw false constant accepted"
  if check falseOpt (fillAux falseOpt emptyVars) then throw <| IO.userError "simplified false constant accepted"
  unless check falseUnsafe (fillAux falseUnsafe emptyVars) do
    throw <| IO.userError "unsafe-drop-constant falsifier disappeared"
  let zeroSource : ConstraintSystem BabyBear (Fin 1) := [cst 0]
  let zeroOpt := emitSimplified Fin.val 1 1 zeroSource
  unless zeroOpt.zeros.length=0 && check zeroOpt (fillAux zeroOpt emptyVars) do
    throw <| IO.userError "true zero assertion was not safely removed"
  let result := Json.mkObj [("counts",toJson (variants.map fun (n,d) => count n d)),
    ("small_honest_and_forged_pairs",toJson smallCases),
    ("small_simplified_all_wire_mutations_refused",toJson smallOpt.nWires),
    ("large_honest_and_two_forged_triples",toJson largeCases),
    ("unsafe_constant_drop_falsifier",toJson true),
    ("nonzero_constant_retained",toJson true),("zero_constant_removed",toJson true)]
  IO.FS.writeFile (outputDir/"results.json") (result.pretty++"\n")
  for (name,d) in variants do
    if name.endsWith "simplified" || name.endsWith "simplified_CSE" then
      writeDescriptorJson (outputDir/(name++"_descriptor.json")) d
  IO.println result.pretty

#eval run
end Minidregg.Compiler.SimplificationChecks
