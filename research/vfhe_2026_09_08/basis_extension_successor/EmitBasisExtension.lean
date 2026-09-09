import Compiler.BasisExtensionWitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.ActualBasisExtension
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def ir2Alg : Alg (AirSig BabyBear Nat) String := fun op => match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString c.val++"}"
  | .var i => fun _ => ir2Var i
  | .add => fun c => "{\"t\":\"add\",\"l\":"++c false++",\"r\":"++c true++"}"
  | .mul => fun c => "{\"t\":\"mul\",\"l\":"++c false++",\"r\":"++c true++"}"
def ir2Template (terms : ConstraintSystem BabyBear Nat) : String :=
  let gates := terms.map fun t => "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++String.intercalate "," ((List.range 84).map ir2Var)++"]}"
  "{\"name\":\"actual_identity_rns_basis_extension\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"bfv_public_rows\",\"arity\":84,"++
    "\"sem\":\"exact_public_rows\",\"rows\":[]}],\"constraints\":["++String.intercalate "," (lookup::gates)++"],\"hash_sites\":[],\"ranges\":[]}"
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath := args.headD "program"
  IO.FS.createDirAll out
  let terms := AirSimplify.simplifySystem system
  IO.FS.writeFile (out/"template_ir2.json") (ir2Template terms++"\n")
  let b ← IO.ofExcept BasisExtensionWitnessPlan.generated
  IO.FS.writeFile (out/"witness_plan.json") ((BasisExtensionWitnessPlan.programJson b).compress++"\n")
  let emissionSummary := Json.mkObj [("trace_width",toJson nVars),("arithmetic_constraints",toJson terms.length),
    ("public_arity",toJson (84 : Nat)),("instructions",toJson b.code.size),("registers",toJson b.next),
    ("public_tuple",toJson "rowID,input4x6_radix512,copied4x6_radix512,new5x7_radix512")]
  IO.FS.writeFile (out/"emission.json") (emissionSummary.pretty++"\n")
  IO.println emissionSummary.compress
  return 0
