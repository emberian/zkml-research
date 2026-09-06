import Compiler.FheSourceCertificateChecks

namespace Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler
open Minidregg.Compiler.FheRnsScale
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Lean (Json toJson)

def retainSourceFixtures : IO Unit := do
  let cap := sourceValues capturedResidues
  let d := optimizedSourceDescriptor
  let initial := sourceVariableArray cap
  let filled := fillAux d initial
  unless pinnedSourceCheck capturedResidues 172481 (fun i => filled.getD i 0) do
    throw <| IO.userError "explicit pinned positive source claim refused"
  if pinnedSourceCheck capturedResidues 172480 (fun i => filled.getD i 0) then
    throw <| IO.userError "wrong explicit source output claim accepted"
  let serialize := fun label expected (a : Array BabyBear) => Json.mkObj [
    ("label",toJson label),("expected",toJson expected),("initial_variables",toJson (a.map fun x => x.val))]
  let cases := #[serialize "captured_source_plus_one" true initial,
    serialize "wrong_nearest_neighbor" false (sourceVariableArray (wrongOutput cap 172480)),
    serialize "correction_range_attack" false (sourceVariableArray
      (withValue (withValue (wrongOutput cap 172480) 15 (cap 15-1)) 16 (cap 16+2*(2^127)))),
    serialize "Garner_range_attack" false (sourceVariableArray
      (withValue (withValue cap 12 (cap 12-1)) 13 (cap 13+2*(2^126)))),
    serialize "noncanonical_residue" false (sourceVariableArray
      (withValue (withValue cap 0 (deployedBase 0).toNat) 6 0)),
    serialize "out_of_range_digit" false (initial.set! 0 64)]
  let obj := Json.mkObj [("label",toJson "EXECUTED retained inputs to existing emitted descriptor"),
    ("source_residues",toJson ((Array.ofFn capturedResidues).map toString)),
    ("pinned_output",toJson (172481:Nat)),("wrong_pinned_output_refused",toJson true),("cases",Json.arr cases)]
  IO.FS.writeFile "../../../experiments/bfv_lift_refinement/source_certificate/retained-inputs.json" (obj.pretty++"\n")
  IO.println "retained six emitted-checker fixtures; exact external source/output pins pass"

#eval retainSourceFixtures
end Minidregg.Compiler.FheSourceCertificate
