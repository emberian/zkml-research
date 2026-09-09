/- Ordered IR2 emission folds the proved source. No constraint expressions are
written by the Rust public reader. -/
import Compiler.TfheSparseWitness
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.TfheSparseRow Minidregg.Theory
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
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++String.intercalate "," ((List.range 46).map ir2Var)++"]}"
  "{\"name\":\"tfhe_selected_sparse_first_external_product\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"tfhe_sparse_public_rows\",\"arity\":46,\"sem\":\"exact_public_rows\",\"rows\":[]}],\"constraints\":["++
    String.intercalate "," (lookup::arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"
def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    for shift in [0,8,16,24] do b := b.push ((value.val >>> shift).toUInt8)
  return b

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.headD "artifacts"
  let inputPath := args[1]?.getD "../fixtures/normal_001/public_rows46.json"
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile (System.FilePath.mk inputPath)))
  let rows ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array (Array Nat)))
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "template_ir2.json") (ir2Template++"\n")
  for i in [0,1,44,162,511,512,1024,1536,2047] do
    unless sourceCheck rows[i]! do
      let a := variableArray rows[i]!
      let failures := emittedSystem.zipIdx |>.filterMap fun (t,j) =>
        let value := eval (fun k => a[k.val]!) t
        if value==0 then none else some (j,value.val)
      throw (IO.userError s!"sample {i} refused: {failures}")
  if sourceCheck (rows[1]!.set! 20 (((rows[1]!)[20]!+1)%64)) then
    throw (IO.userError "changed output accepted")
  if sourceCheck (rows[1]!.set! 40 (((rows[1]!)[40]!+1)%64)) then
    throw (IO.userError "changed raw low bits accepted")
  if sourceCheck (rows[0]!.set! 36 (((rows[0]!)[36]!+1)%64)) then
    throw (IO.userError "changed anchor accepted")
  IO.FS.withFile (outDir / "trace.leu32") .write fun handle => do
    for i in [:rows.size] do
      let row := rows[i]!
      unless row.size==46 && row[0]! == i do throw (IO.userError s!"bad rowshape/id at{i}")
      for j in [8:46] do unless row[j]!<64 do throw (IO.userError s!"bad digit at{i}/{j}")
      for j in [3:8] do unless row[j]!≤1 do throw (IO.userError s!"bad flag at{i}/{j}")
      handle.write (u32Bytes (variableArray row))
  let summary := Json.mkObj [("rows",toJson rows.size),("trace_width",toJson nVars),
    ("public_arity",toJson (46 : Nat)),("trace_bytes",toJson (rows.size*nVars*4)),
    ("source_constraints",toJson system.length),("arithmetic_constraints",toJson emittedSystem.length),
    ("selected_actual_rows_checked",toJson (9 : Nat)),("changed_output_refused",toJson true),
    ("raw_scale_refused",toJson true),("anchor_refused",toJson true),
    ("full_row_check",toJson "unchanged native proof backend")]
  IO.FS.writeFile (outDir / "emission.json") (summary.pretty++"\n")
  IO.println summary.compress
  return 0
