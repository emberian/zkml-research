/- Executable compiler boundary: the IR2 arithmetic is a Signature.fold of the
proved source terms. Rust supplies public table rows, not constraint expressions. -/
import Compiler.BfvExpiryWitnessPlan
import Lean.Data.Json

open Lean (Json toJson)
open Minidregg.Compiler
open Minidregg.Compiler.BfvExpiry
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
    String.intercalate "," ((List.range 57).map ir2Var)++"]}"
  "{\"name\":\"bfv_two_moduli_expiry_acc_plus_fresh_minus_old\",\"ir\":2,\"trace_width\":"++
    toString nVars++",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,"++
    "\"name\":\"bfv_public_rows\",\"arity\":57,\"sem\":\"exact_public_rows\",\"rows\":[]}],"++
    "\"constraints\":["++String.intercalate "," (lookup::arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"

def u32Bytes (a : Array BabyBear) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (4*a.size)
  for value in a do
    let v := value.val
    for shift in [0,8,16,24] do bytes := bytes.push ((v >>> shift).toUInt8)
  return bytes

def sampleRows : Array (Array Nat) := #[
  rowOfValues 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0),
  rowOfValues 1 (fun _ => 17) (fun _ => 23) (fun _ => 9) (fun _ => 31),
  rowOfValues 2 (fun i => primes i-1) (fun i => primes i-1) (fun _ => 0) (fun i => primes i-2),
  rowOfValues 3 (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun i => primes i-1)]

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.headD "program"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "witness_plan.json") (Minidregg.Compiler.BfvExpiry.WitnessPlan.programJson.compress++"\n")
  IO.FS.writeFile (outDir / "template_ir2.json") (ir2Template++"\n")
  IO.FS.writeFile (outDir / "sample_rows.json") ((toJson sampleRows).compress++"\n")
  IO.FS.withFile (outDir / "sample_baseline.leu32") .write fun h => do
    for row in sampleRows do
      unless sourceCheck row do throw (IO.userError "frozen constructed witness refused")
      h.write (u32Bytes (variableArray row))
  IO.println s!"generated {Minidregg.Compiler.BfvExpiry.WitnessPlan.program.code.size} instructions, {Minidregg.Compiler.BfvExpiry.WitnessPlan.program.next} registers; expiry source template unchanged"
  return 0
