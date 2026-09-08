import Compiler.TfheCmuxDecomposition
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.TfheCmuxDecomposition
open Minidregg.Compiler.NativeKernelPlan Minidregg.Compiler.AirSimplify
open Minidregg.Theory
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def ir2Alg : Alg (AirSig BabyBear W) String := fun op =>
  match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString c.val++"}"
  | .var i => fun _ => ir2Var i.val
  | .add => fun c => "{\"t\":\"add\",\"l\":"++c false++",\"r\":"++c true++"}"
  | .mul => fun c => "{\"t\":\"mul\",\"l\":"++c false++",\"r\":"++c true++"}"
def lookup (id : Nat) (cols : List Nat) : String :=
  "{\"t\":\"lookup\",\"table\":"++toString id++",\"tuple\":["++
    String.intercalate "," (cols.map ir2Var)++"]}"
def table (id arity : Nat) : String :=
  "{\"id\":"++toString id++",\"name\":\"cmux_decomposition_public_"++toString id++
    "\",\"arity\":"++toString arity++",\"sem\":\"exact_public_rows\",\"rows\":[]}"
def ir2Template : String :=
  let arithmetic := (simplifySystem system).map fun t =>
    "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  "{\"name\":\"tfhe_u32_first_cmux_input_and_signed_decomposition\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":["++table 11 10++","++table 12 4++","++table 13 4++
    "],\"constraints\":["++String.intercalate "," (lookup 11 [0,1,2,250,111,112,113,114,115,116]::lookup 12 [1,6,7,8]::lookup 13 [1,2,251,252]::arithmetic)++
    "],\"hash_sites\":[],\"ranges\":[]}"
def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    for shift in [0,8,16,24] do bytes := bytes.push ((value.val >>> shift).toUInt8)
  return bytes
def main (args : List String) : IO UInt32 := do
  let sourcePath := System.FilePath.mk (args.headD "fixtures/normal_001/tables.json")
  let outputPath := System.FilePath.mk (args[1]?.getD "artifacts")
  IO.FS.createDirAll outputPath
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile sourcePath))
  let inputJson ← IO.ofExcept (parsed.getObjVal? "input_rows")
  let outputJson ← IO.ofExcept (parsed.getObjVal? "output_rows")
  let inputs ← IO.ofExcept (Lean.fromJson? inputJson : Except String (Array (Array Nat)))
  let outputs ← IO.ofExcept (Lean.fromJson? outputJson : Except String (Array (Array Nat)))
  unless inputs.size == 2048 && outputs.size == 2048 do throw (IO.userError "wrong complete accumulator size")
  for i in [:inputs.size] do
    let row := inputs[i]!
    unless row.size == 4 && row[0]! == i/512 && row[1]! == i%512 && row[2]! < 65536 && row[3]! < 65536 do
      throw (IO.userError "wrong canonical indexed input table")
  let cachedSystem := system.toArray
  let check := fun a : Array BabyBear => cachedSystem.all (fun t => eval (asgOf a) t == 0)
  let changed := outputs[1536]!.set! 4 (((outputs[1536]!)[4]!+1)%65536)
  if check (variableArray changed inputs) then throw (IO.userError "changed output accepted by generated source")
  let changedDigit := outputs[1536]!.set! 8 ((outputs[1536]!)[8]!+1)
  if check (variableArray changedDigit inputs) then throw (IO.userError "changed signed digit accepted")
  let badDigit := outputs[1536]!.set! 4 65536
  if check (variableArray badDigit inputs) then throw (IO.userError "out-of-range output limb accepted")
  let boundaryInputs := #[0,1,2047,2048,2049,2095103,2095104,2097152,2147481599,2147481600,
    2147481601,2147483648,2147485696,2149580800,4294965247,4294965248,4294967295]
  for x in boundaryInputs do
    unless TfheSignedDecomposition.sourceCheck (TfheSignedDecomposition.canonical x) do
      throw (IO.userError s!"signed decomposition boundary {x} refused")
  IO.FS.writeFile (outputPath/"template_ir2.json") (ir2Template++"\n")
  IO.FS.withFile (outputPath/"trace.leu32") .write fun h => do
    for i in [:outputs.size] do
      let row := outputs[i]!
      unless row.size == 10 && row[0]! == i && row[1]! == i/512 && row[2]! == i%512 do
        throw (IO.userError "wrong public output coverage")
      let a := variableArray row inputs
      unless check a do throw (IO.userError s!"native CMUX/decomposition row {i} refused")
      h.write (u32Bytes a)
  let report := Json.mkObj [("claim",toJson "EXECUTED compiler-generated complete native CMUX input and exact signed decomposition"),
    ("rounding_tie_boundaries",toJson boundaryInputs.size),("rows",toJson outputs.size),("trace_width",toJson nVars),("source_constraints",toJson system.length),
    ("ir2_arithmetic_constraints",toJson (simplifySystem system).length),
    ("exact_public_tables",toJson 3),("changed_output_refused",toJson true),("changed_signed_digit_refused",toJson true),("out_of_range_limb_refused",toJson true),
    ("all_native_rows_exported",toJson true),("all_native_rows_source_checked",toJson true),("complete_relation_checked_by_actual_proof",toJson "pending"),("trace_bytes",toJson (outputs.size*nVars*4))]
  IO.FS.writeFile (outputPath/"emission.json") (report.pretty++"\n")
  IO.println report.compress
  return 0
