/- Each emitted equation is folded from the proved source relation. -/
import Compiler.BfvTensorWitnessPlan
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.BfvTensorRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def ir2Alg : Alg (AirSig BabyBear (Fin nVars)) String := fun op => match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString c.val++"}"
  | .var i => fun _ => ir2Var i.val
  | .add => fun c => "{\"t\":\"add\",\"l\":"++c false++",\"r\":"++c true++"}"
  | .mul => fun c => "{\"t\":\"mul\",\"l\":"++c false++",\"r\":"++c true++"}"
def ir2Template (q : Nat) : String :=
  let arithmetic := (emittedSystem q).map fun t => "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++String.intercalate "," ((List.range 56).map ir2Var)++"]}"
  "{\"name\":\"bfv_actual_extended_tensor_square_q"++toString q++"\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"bfv_public_tensor_rows\",\"arity\":56,\"sem\":\"exact_public_rows\",\"rows\":[]}],\"constraints\":["++
    String.intercalate "," (lookup::arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "artifacts"
  IO.FS.createDirAll root
  let mut rows : Array Json := #[]
  for l in List.finRange 9 do
    let q := primes l
    let folder := root / ("prime"++toString l.val)
    IO.FS.createDirAll folder
    IO.FS.writeFile (folder / "template_ir2.json") (ir2Template q++"\n")
    IO.FS.writeFile (folder / "witness_plan.json") ((WitnessPlan.programJson q).compress++"\n")
    IO.FS.writeFile (folder / "sample_rows.json") ((toJson (WitnessPlan.sampleRows q)).compress++"\n")
    let prog := WitnessPlan.program q
    let row := Json.mkObj [("prime_index",toJson l.val),("q",toJson q),
      ("trace_width",toJson nVars),("public_arity",toJson (56 : Nat)),
      ("radix",toJson (64 : Nat)),("limbs",toJson (11 : Nat)),
      ("arithmetic_constraints",toJson (emittedSystem q).length),
      ("instructions",toJson prog.code.size),("register_count",toJson prog.next)]
    rows := rows.push row
    IO.println row.compress
  IO.FS.writeFile (root / "emission.json") (Json.arr rows |>.pretty)
  return 0
