/- Executable compiler boundary: the IR2 arithmetic is a Signature.fold of the
proved source terms. Rust supplies public table rows, not constraint expressions. -/
import Compiler.BfvLinearCombinationLayout
import Lean.Data.Json

open Lean (Json toJson)
open Minidregg.Compiler
open Minidregg.Compiler.BfvLinearCombination
open Minidregg.Compiler.AirSimplify
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"

def ir2Alg : Alg (AirSig BabyBear (Fin nVars)) String := fun op =>
  match op with
  | .const c => fun _ => "{\"t\":\"const\",\"v\":"++toString c.val++"}"
  | .var i => fun _ => ir2Var i.val
  | .add => fun child => "{\"t\":\"add\",\"l\":"++child false++",\"r\":"++child true++"}"
  | .mul => fun child => "{\"t\":\"mul\",\"l\":"++child false++",\"r\":"++child true++"}"

/-- The backend's tagged-node parser requires the discriminator first. This
ordered serialization folds the same source terms; it introduces no equations. -/
def ir2Template : String :=
  let terms := simplifySystem system
  let arithmetic := terms.map fun t => "{\"t\":\"gate\",\"body\":"++fold ir2Alg t++"}"
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++
    String.intercalate "," ((List.range 64).map ir2Var)++"]}"
  "{\"name\":\"bfv_three_moduli_linear_combination_3a_5b\",\"ir\":2,\"trace_width\":"++
    toString nVars++",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,"++
    "\"name\":\"bfv_public_rows\",\"arity\":64,\"sem\":\"exact_public_rows\",\"rows\":[]}],"++
    "\"constraints\":["++String.intercalate "," (lookup::arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"

def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    let v := value.val
    for shift in [0,8,16,24] do bytes := bytes.push ((v >>> shift).toUInt8)
  return bytes

def sampleRows : Array (Array Nat) := #[
  rowOfValues 0 (fun _ => 0) (fun _ => 0) (fun _ => 0),
  rowOfValues 1 (fun _ => 17) (fun _ => 23) (fun _ => 166),
  rowOfValues 2 (fun i => primes i-1) (fun i => primes i-1) (fun i => primes i-8),
  rowOfValues 3 (fun i => primes i-4) (fun _ => 11) (fun _ => 43)]

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.headD "artifacts"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "template_ir2.json") (ir2Template++"\n")
  let d := descriptor
  IO.FS.writeFile (outDir / "minidregg_descriptor.json") ((descriptorToJson d).compress++"\n")
  for row in sampleRows do
    unless sourceCheck row do
      let a := variableArray row
      let failures := system.zipIdx |>.filterMap fun (term,i) =>
        let value := eval (fun j => a[j.val]!) term
        if value == 0 then none else some (i,value.val)
      throw (IO.userError s!"constructed row {row[0]!} refused: {failures}")
    let full := fillAux d (variableArray row)
    unless descriptorHoldsCheck d (fun i => full.getD i 0) do
      throw (IO.userError "existing emitted descriptor refused constructed witness")
  let wrong := sampleRows[1]!.set! 43 39
  if sourceCheck wrong then throw (IO.userError "changed output accepted")
  let badDigit := sampleRows[1]!.set! 1 64
  if sourceCheck badDigit then throw (IO.userError "out-of-range radix digit accepted")
  let mut rows := sampleRows
  if let some inputPath := args[1]? then
    let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile (System.FilePath.mk inputPath)))
    rows ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array (Array Nat)))
  IO.FS.withFile (outDir / "trace.leu32") .write fun handle => do
    for i in [:rows.size] do
      let row := rows[i]!
      unless row.size == 64 do throw (IO.userError s!"row {i}: wrong public arity")
      unless row[0]! == i do throw (IO.userError s!"row {i}: wrong row ID")
      unless sourceCheck row do throw (IO.userError s!"row {i}: actual operation does not satisfy generated relation")
      handle.write (u32Bytes (variableArray row))
      if i % 1024 == 0 then IO.println s!"produced {i}/{rows.size} rows"
  let summary := Json.mkObj [("rows",toJson rows.size),("trace_width",toJson nVars),
    ("trace_bytes",toJson (rows.size*nVars*4)),
    ("source_constraints",toJson system.length),
    ("ir2_arithmetic_constraints",toJson (simplifySystem system).length),
    ("standard_descriptor_gates",toJson d.gates.length),
    ("standard_descriptor_nWires",toJson d.nWires),
    ("constructed_cases_checked",toJson sampleRows.size),
    ("changed_output_refused",toJson true),("radix64_refused",toJson true),
    ("all_actual_source_rows_checked",toJson true),
    ("public_tuple_order",toJson "rowID,A3x7,B3x7,O3x7")]
  IO.FS.writeFile (outDir / "emission.json") (summary.pretty++"\n")
  IO.println summary.compress
  return 0
