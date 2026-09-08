/- Ordered IR2 emission folds the proved source. No constraint expressions are
written by the Rust public reader. -/
import Compiler.BfvQueryWitness
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
  let outDir : System.FilePath := args.headD "artifacts"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "template_ir2.json") (ir2Template++"\n")
  IO.FS.writeBinFile (outDir / "sample0.leu32") (u32Bytes (variableArray sampleRows[0]!))
  for row in sampleRows do
    unless sourceCheck row do
      let a := variableArray row
      let failures := emittedSystem.zipIdx |>.filterMap fun (t,i) =>
        let value := eval (fun j => a[j.val]!) t
        if value==0 then none else some (i,value.val)
      throw (IO.userError s!"sample {row[0]!} refused: {failures}")
  if sourceCheck (sampleRows[1]!.set! 43 47) then throw (IO.userError "wrong output accepted")
  if sourceCheck (sampleRows[1]!.set! 1 64) then throw (IO.userError "bad radix digit accepted")
  let mut rows := sampleRows
  if let some inputPath := args[1]? then
    let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile (System.FilePath.mk inputPath)))
    rows ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array (Array Nat)))
  IO.FS.withFile (outDir / "trace.leu32") .write fun handle => do
    for i in [:rows.size] do
      let row := rows[i]!
      unless row.size == 57 && row[0]! == i do throw (IO.userError s!"bad public rowshape or index at{i}")
      for j in [1:57] do unless row[j]!<64 do throw (IO.userError s!"bad public digit at{i}/{j}")
      handle.write (u32Bytes (variableArray row))
      if i%1024==0 then IO.println s!"produced{i}/{rows.size} rows"
  let summary := Json.mkObj [("rows",toJson rows.size),("trace_width",toJson nVars),
    ("trace_bytes",toJson (rows.size*nVars*4)),("source_constraints",toJson system.length),
    ("ir2_arithmetic_constraints",toJson emittedSystem.length),("constructed_cases_checked",toJson sampleRows.size),
    ("changed_output_refused",toJson true),("radix64_refused",toJson true),
    ("actual_row_constraint_check",toJson "unchanged native prover; emitter checks four constructed rows"),
    ("public_tuple_order",toJson "rowID,acc2x7,positivePT2x7,negativePT2x7,out2x7")]
  IO.FS.writeFile (outDir / "emission.json") (summary.pretty++"\n")
  IO.println summary.compress
  return 0
