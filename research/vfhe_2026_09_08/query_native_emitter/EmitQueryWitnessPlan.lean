/- Ordered IR2 emission folds the proved source. No constraint expressions are
written by the Rust public reader. -/
import Compiler.BfvQueryWitnessPlan
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.BfvQueryRow Minidregg.Theory
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def ir2Alg : Alg (AirSig BabyBear (Fin nVars)) String := fun op => match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString c.val++"}"
  | .var i => fun _ => ir2Var i.val
  | .add => fun c => "{\"t\":\"add\",\"l\":"++c false++",\"r\":"++c true++"}"
  | .mul => fun c => "{\"t\":\"mul\",\"l\":"++c false++",\"r\":"++c true++"}"
def ir2Template : String :=
  let arithmetic := emittedSystem.map fun t => "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++String.intercalate "," ((List.range 57).map ir2Var)++"]}"
  "{\"name\":\"bfv_actual_query_two_products_subtraction\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"bfv_public_rows\",\"arity\":57,\"sem\":\"exact_public_rows\",\"rows\":[]}],\"constraints\":["++
    String.intercalate "," (lookup::arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"
def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    for shift in [0,8,16,24] do b := b.push ((value.val >>> shift).toUInt8)
  return b

def sampleRows : Array (Array Nat) := #[
  rowOfValues 0 (fun _=>0) (fun _=>0) (fun _=>0) (fun _=>0),
  rowOfValues 1 (fun _=>17) (fun _=>23) (fun _=>9) (fun _=>238),
  rowOfValues 2 (fun l=>primes l-1) (fun l=>primes l-1) (fun _=>0) (fun _=>1),
  rowOfValues 3 (fun _=>3) (fun _=>0) (fun _=>5) (fun l=>primes l-15)]

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.headD "program"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "witness_plan.json") (Minidregg.Compiler.BfvQueryRow.WitnessPlan.programJson.compress++"\n")
  IO.FS.writeFile (outDir / "template_ir2.json") (ir2Template++"\n")
  IO.FS.writeFile (outDir / "sample_rows.json") ((toJson sampleRows).compress++"\n")
  IO.FS.withFile (outDir / "sample_baseline.leu32") .write fun h => do
    for row in sampleRows do
      unless sourceCheck row do throw (IO.userError "frozen constructed witness refused")
      h.write (u32Bytes (variableArray row))
  IO.println s!"generated {Minidregg.Compiler.BfvQueryRow.WitnessPlan.program.code.size} instructions, {Minidregg.Compiler.BfvQueryRow.WitnessPlan.program.next} registers; source template unchanged"
  return 0
