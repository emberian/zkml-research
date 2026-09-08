import Compiler.TfheModulusSwitch
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.TfheModulusSwitch
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
def ir2Template : String :=
  let arithmetic := (simplifySystem system).map fun t =>
    "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++
    String.intercalate "," ((List.range 4).map ir2Var)++"]}"
  "{\"name\":\"tfhe_u32_modulus_switch_10\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"pbs_entry_public_rows\","++
    "\"arity\":4,\"sem\":\"exact_public_rows\",\"rows\":[]}],\"constraints\":["++
    String.intercalate "," (lookup::arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"
def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    for shift in [0,8,16,24] do bytes := bytes.push ((value.val >>> shift).toUInt8)
  return bytes
def main (args : List String) : IO UInt32 := do
  let inputPath := System.FilePath.mk (args.headD "fixtures/normal_001/public_rows.json")
  let outputPath := System.FilePath.mk (args[1]?.getD "artifacts")
  IO.FS.createDirAll outputPath
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile inputPath))
  let rows ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array (Array Nat)))
  let mut positive : Nat := 0
  for x in #[0,2097151,2097152,2097153,2147483648,4292870143,4292870144,4294967295] do
    let row := #[0,x%65536,x/65536,((x+2097152)/4194304)%1024]
    unless sourceCheck row do throw (IO.userError s!"boundary witness refused: {x}")
    if sourceCheck (row.set! 3 ((row[3]!+1)%1024)) then
      throw (IO.userError "changed exponent accepted")
    positive := positive+1
  IO.FS.writeFile (outputPath/"template_ir2.json") (ir2Template++"\n")
  IO.FS.withFile (outputPath/"trace.leu32") .write fun h => do
    for i in [:rows.size] do
      let row := rows[i]!
      unless row.size == 4 && row[0]! == i do throw (IO.userError "bad public row shape/id")
      unless sourceCheck row do throw (IO.userError s!"native modulus-switch row {i} refused")
      h.write (u32Bytes (variableArray row))
  let report := Json.mkObj [("claim",toJson "EXECUTED compiler-generated native PBS modulus-switch relation"),
    ("rows",toJson rows.size),("trace_width",toJson nVars),("source_constraints",toJson system.length),
    ("ir2_arithmetic_constraints",toJson (simplifySystem system).length),
    ("boundary_cases",toJson positive),("changed_exponents_refused",toJson positive),
    ("all_native_rows_checked",toJson true),("trace_bytes",toJson (rows.size*nVars*4))]
  IO.FS.writeFile (outputPath/"emission.json") (report.pretty++"\n")
  IO.println report.compress
  return 0
