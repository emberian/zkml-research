import Compiler.BfvRescaleWitness
import Compiler.AirAssertionShare
import Lean.Data.Json

open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.BfvRescaleRow
open Minidregg.Compiler.AirSimplify Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def ir2Alg : Alg (AirSig BabyBear (Fin nVars)) String := fun op => match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString c.val++"}"
  | .var i => fun _ => ir2Var i.val
  | .add => fun child => "{\"t\":\"add\",\"l\":"++child false++",\"r\":"++child true++"}"
  | .mul => fun child => "{\"t\":\"mul\",\"l\":"++child false++",\"r\":"++child true++"}"

def ir2Template (terms : ConstraintSystem BabyBear (Fin nVars)) : String :=
  let arithmetic := terms.map fun t => "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++String.intercalate "," ((List.range 88).map ir2Var)++"]}"
  "{\"name\":\"bfv_complete_six_to_three_integer_rescale\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"bfv_public_rows\",\"arity\":88,"++
    "\"sem\":\"exact_public_rows\",\"rows\":[]}],\"constraints\":["++String.intercalate "," (lookup::arithmetic)++
    "],\"hash_sites\":[],\"ranges\":[]}"

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.headD "artifacts"
  IO.FS.createDirAll outDir
  let before := simplifySystem system
  let after := Minidregg.Compiler.AirAssertionShare.share before
  IO.FS.writeFile (outDir/"template_before_ir2.json") (ir2Template before++"\n")
  IO.FS.writeFile (outDir/"template_ir2.json") (ir2Template after++"\n")
  let summary := Json.mkObj [("trace_width",toJson nVars),("public_arity",toJson (88:Nat)),
    ("before_arithmetic_constraints",toJson before.length),
    ("after_arithmetic_constraints",toJson after.length),
    ("removed_repeated_assertions",toJson (before.length-after.length)),
    ("trace_projection_changed",toJson false)]
  IO.FS.writeFile (outDir/"emission.json") (summary.pretty++"\n")
  IO.println summary.compress
  return 0
