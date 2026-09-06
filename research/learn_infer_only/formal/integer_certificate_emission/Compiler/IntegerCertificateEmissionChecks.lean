import Compiler.IntegerCertificateEmission

namespace Minidregg.Compiler.IntegerCertificateEmissionChecks
open Minidregg.Compiler
open Minidregg.Compiler.IntegerCertificateEmission
open Minidregg.Compiler.DescriptorEval
open Lean (Json toJson)

def outputDir : System.FilePath :=
  "../../experiments/integer_certificate_emission"

def row (name : String) (c : Array BabyBear) (expected : Bool) : IO Json := do
  let accepted := check c
  unless accepted = expected do throw <| IO.userError s!"{name}: unexpected verdict {accepted}"
  pure <| Json.mkObj [("name", toJson name), ("accepted", toJson accepted),
    ("wires", Json.arr (c.map fun x => toJson x.val))]

def run : IO Unit := do
  let d := certificateDescriptor
  let honest := candidate 24 7 14
  let forged := candidate 24 8 14
  let r31 := candidate 4 3 31
  let carryMut := honest.set! 20 (honest.getD 20 0 + 1)
  let auxMut := honest.set! d.nVars (honest.getD d.nVars 0 + 1)
  let mutRows ← [row "negative_z_-8_y_-1" honest true,
    row "forged_quotient_fresh_aux" forged false,
    row "remainder_31" r31 false,
    row "carry_mutation" carryMut false,
    row "aux_mutation" auxMut false].mapM id
  let mutJson := Json.arr mutRows.toArray
  IO.FS.writeFile (outputDir / "checker_vectors.json") (mutJson.pretty ++ "\n")
  writeDescriptorJson (outputDir / "descriptor.json") d
  let mutCount ← (List.range d.nWires).foldlM (fun count i => do
    let tampered := honest.set! i (honest.getD i 0 + 1)
    if check tampered then throw <| IO.userError s!"single wire {i} mutation accepted"
    pure (count+1)) 0
  let acceptsCount ← (List.range 64).foldlM (fun count zEnc => do
    let z : Int := (zEnc : Nat) - 32
    let y := (4*z+15)/31
    let r := ((4*z+15)%31).toNat
    unless check (candidate zEnc (y+8).toNat r) do
      throw <| IO.userError s!"honest z={z} refused"
    pure (count+1)) 0
  let summary := Json.mkObj [("field", toJson babyBearP),
    ("gates", toJson d.gates.length),
    ("add_gates", toJson (d.gates.filter fun g => g.op == .add).length),
    ("mul_gates", toJson (d.gates.filter fun g => g.op == .mul).length),
    ("zero_checks", toJson d.zeros.length),
    ("variables", toJson d.nVars), ("wires", toJson d.nWires),
    ("public_variables", toJson d.nPublic),
    ("honest_signed_coefficients", toJson acceptsCount),
    ("single_wire_mutations_refused", toJson mutCount)]
  IO.FS.writeFile (outputDir / "checker_results.json") (summary.pretty ++ "\n")
  IO.println summary.pretty

#eval run
end Minidregg.Compiler.IntegerCertificateEmissionChecks
