import Compiler.LargeIntegerCertificateEmission

namespace Minidregg.Compiler.LargeIntegerCertificateEmissionChecks
open Minidregg.Compiler
open Minidregg.Compiler.LargeIntegerCertificateEmission
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Lean (Json toJson)

def run : IO Unit := do
  let d := descriptor
  let sd := sharedDescriptor
  let sharedCheck := fun a : Array BabyBear => descriptorHoldsCheck sd (fun i => a.getD i 0)
  let zMax : Int := 8192*(Q-1)^2
  let zs : List Int := [-zMax, -zMax+1, -1, 0, 1, zMax-1, zMax]
  let mut rows : Array Json := #[]
  for z in zs do
    let numerator := (t : Int)*z+(Q/2 : Nat)
    let y := numerator/(Q : Int)
    let r := (numerator%(Q : Int)).toNat
    let c := candidate z y r
    unless check c do throw <| IO.userError s!"large honest z={z} refused"
    let bad := candidate z (y+1) r
    if check bad then throw <| IO.userError s!"large wrong quotient z={z} accepted"
    let badR := candidate z (y-1) (r+Q)
    if check badR then throw <| IO.userError s!"large out-of-range remainder z={z} accepted"
    unless sharedCheck (fillAux sd (variableArray z y r)) do
      throw <| IO.userError s!"CSE honest z={z} refused"
    if sharedCheck (fillAux sd (variableArray z (y+1) r)) then
      throw <| IO.userError s!"CSE wrong quotient z={z} accepted"
    if sharedCheck (fillAux sd (variableArray z (y-1) (r+Q))) then
      throw <| IO.userError s!"CSE out-of-range remainder z={z} accepted"
    rows := rows.push <| Json.mkObj [("z",toJson (toString z)),
      ("y",toJson (toString y)),("r",toJson (toString r)),
      ("accepted",toJson true),("wrong_quotient_refused",toJson true),
      ("out_of_range_remainder_refused",toJson true),
      ("CSE_same_three_verdicts",toJson true)]
  let summary := Json.mkObj [("field",toJson babyBearP),("Q",toJson (toString Q)),
    ("t",toJson t),("radix",toJson (64:Nat)),("columns",toJson (43:Nat)),
    ("scalar_digits",toJson (101:Nat)),("carry_bits",toJson (13:Nat)),
    ("left_column_bound",toJson (63+101*63*63+(2^13-1):Nat)),
    ("right_column_bound",toJson (63+64*(2^13-1):Nat)),
    ("gates",toJson d.gates.length),
    ("add_gates",toJson (d.gates.filter fun g => g.op == .add).length),
    ("mul_gates",toJson (d.gates.filter fun g => g.op == .mul).length),
    ("zero_checks",toJson d.zeros.length),("variables",toJson d.nVars),
    ("wires",toJson d.nWires),("cases",Json.arr rows)]
  let isZero : DWire BabyBear -> Bool := fun | .cnst c => c == 0 | _ => false
  let isConstant : DWire BabyBear -> Bool := fun | .cnst _ => true | _ => false
  let cost := Json.mkObj [
    ("raw_gates",toJson d.gates.length),("shared_gates",toJson sd.gates.length),
    ("shared_add_gates",toJson (sd.gates.filter fun g => g.op == .add).length),
    ("shared_mul_gates",toJson (sd.gates.filter fun g => g.op == .mul).length),
    ("raw_zero_product_gates",toJson (d.gates.filter fun g =>
      g.op == .mul && (isZero g.a || isZero g.b)).length),
    ("raw_constant_product_gates",toJson (d.gates.filter fun g =>
      g.op == .mul && (isConstant g.a || isConstant g.b)).length),
    ("shared_zero_checks",toJson sd.zeros.length),("shared_wires",toJson sd.nWires),
    ("header_compacted",toJson false)]
  IO.FS.writeFile "../../experiments/integer_certificate_emission/large_results.json"
    (summary.pretty++"\n")
  writeDescriptorJson "../../experiments/integer_certificate_emission/large_descriptor.json" d
  writeDescriptorJson "../../experiments/integer_certificate_emission/large_shared_descriptor.json" sd
  IO.FS.writeFile "../../experiments/integer_certificate_emission/large_CSE_costs.json"
    (cost.pretty++"\n")
  IO.println summary.pretty
  IO.println cost.pretty


#eval run
end Minidregg.Compiler.LargeIntegerCertificateEmissionChecks
