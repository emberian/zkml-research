import Compiler.BfvRescaleWitness
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

def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    for shift in [0,8,16,24] do bytes := bytes.push ((value.val >>> shift).toUInt8)
  return bytes

def capturedRow : Array Nat := #[0] ++
  ((List.finRange 6).flatMap fun i => (List.range 11).map
    (digit 64 (Minidregg.Compiler.FheRnsScale.capturedResidues i).toNat)).toArray ++
  ((List.range 3).flatMap fun _ => (List.range 7).map (digit 64 172481)).toArray

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.headD "artifacts"
  IO.FS.createDirAll outDir
  IO.println "constructing shared exact rescale source"
  let terms := simplifySystem system
  IO.FS.writeFile (outDir/"template_ir2.json") (ir2Template terms++"\n")
  IO.println s!"emitted {terms.length} arithmetic constraints"
  let check := fun a : Array BabyBear => terms.all (fun t => eval (fun i => a[i.val]!) t == 0)
  let cap ← IO.ofExcept (variableArray capturedRow)
  unless check cap do throw (IO.userError "captured actual nearest+1 witness refused")
  let wrong := capturedRow.set! 67 (digit 64 172480 0)
  if let .ok a := variableArray wrong then
    if check a then throw (IO.userError "wrong nearest output accepted")
  let bad := capturedRow.set! 1 64
  if let .ok _ := variableArray bad then throw (IO.userError "radix64 admitted")
  let some input := args[1]? | throw (IO.userError "expected public rows path")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile (System.FilePath.mk input)))
  let rows ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array (Array Nat)))
  IO.FS.withFile (outDir/"trace.leu32") .write fun handle => do
    for i in [:rows.size] do
      let row := rows[i]!
      unless row[0]! == i do throw (IO.userError s!"wrong row ID {i}")
      let a ← IO.ofExcept (variableArray row)
      unless check a do throw (IO.userError s!"generated relation refused actual row {i}")
      handle.write (u32Bytes a)
      IO.println s!"produced {i+1}/{rows.size} rows"
  let summary := Json.mkObj [("rows",toJson rows.size),("trace_width",toJson nVars),
    ("trace_bytes",toJson (rows.size*nVars*4)),("ir2_arithmetic_constraints",toJson terms.length),
    ("public_arity",toJson (88:Nat)),("captured_nearest_plus_one_accepted",toJson true),
    ("wrong_nearest_refused",toJson true),("radix64_refused",toJson true),
    ("all_actual_source_rows_checked",toJson true),
    ("public_tuple_order",toJson "rowID,product_extended6x11,output3x7")]
  IO.FS.writeFile (outDir/"emission.json") (summary.pretty++"\n")
  IO.println summary.compress
  return 0
