/- Derived all-row arithmetic, native range declarations, and a data-only
projection appended to the existing untrusted BigInt witness plans. -/
import Compiler.RangeProfiledProfiles
import Compiler.BasisExtensionWitnessPlan
import Compiler.RescaleWitnessPlan
import Compiler.Ir2WholeRow
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.RangeProfiledCompact Minidregg.Compiler.RangeProfiledActual
open Minidregg.Compiler.BfvQueryRow.WitnessPlan (Operand Builder Build put)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def rangeLookup (r : Nat × Nat) : String :=
  "{\"t\":\"lookup\",\"table\":"++toString (69+r.2)++",\"tuple\":["++ir2Var r.1++"]}"
def rangeTable (b : Nat) : String :=
  "{\"id\":"++toString (69+b)++",\"name\":\"range"++toString b++
    "\",\"arity\":1,\"sem\":\"range\",\"bits\":"++toString b++"}"
def template (name : String) (s : Profile) (terms : ConstraintSystem BabyBear Nat)
    (rs : List (Nat × Nat)) : String :=
  let arithmetic := terms.map (Ir2WholeRow.gateJson (fun c : BabyBear => c.val) id)
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++
    String.intercalate "," ((List.range s.publicArity).map ir2Var)++"]}"
  let tables := ((rs.map Prod.snd).eraseDups).map rangeTable
  "{\"name\":\"bfv_range_profiled_"++name++"\",\"ir\":2,\"trace_width\":"++toString (nVars s)++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"bfv_public_rows\",\"arity\":"++
    toString s.publicArity++",\"sem\":\"exact_public_rows\",\"rows\":[]},"++String.intercalate "," tables++
    "],\"constraints\":["++String.intercalate "," (lookup::(rs.map rangeLookup)++arithmetic)++
    "],\"hash_sites\":[],\"ranges\":[]}"

def projection (s : Profile) : Build Unit := do
  let data := privateData s
  for j in [:s.publicArity+data.length] do
    put j (.reg (if j<s.publicArity then j else data[j-s.publicArity]?.getD 0))
def programJson (s : Profile) (b : Builder) : Json := Json.mkObj [
  ("schema",toJson "lean-bigint-witness-plan-v1"),("trace_width",toJson (nVars s)),
  ("input_arity",toJson s.publicArity),("input_digit_radix",toJson (512 : Nat)),
  ("field_modulus",toJson babyBearP),("register_count",toJson b.next),
  ("instructions",Json.arr (b.code.map RescaleWitnessPlan.instructionJson))]

def emitOne (root : System.FilePath) (name : String) (s : Profile) (old : Except String Builder) : IO Json := do
  let folder := root/name
  IO.FS.createDirAll folder
  -- Capture the data list once; reducing `indexMap s` at every term leaf would
  -- repeatedly reconstruct the profile. This is the same defining expression.
  let data := privateData s
  let mapping := fun j => if j<s.publicArity then j else s.publicArity+data.idxOf j
  let terms := renameS mapping (AirSimplify.simplifySystem (source s))
  let rs := ((oldRanges s).map fun r => (mapping r.1,r.2)).eraseDups
  IO.FS.writeFile (folder/"template_ir2.json") (template name s terms rs++"\n")
  let old ← IO.ofExcept old
  let b := (projection s |>.run old).2
  IO.FS.writeFile (folder/"witness_plan.json") ((programJson s b).compress++"\n")
  let project := fun j => if j<s.publicArity then j else data[j-s.publicArity]?.getD 0
  IO.FS.writeFile (folder/"projection.json") ((toJson ((List.range (nVars s)).map project)).compress++"\n")
  let counts := ((rs.map Prod.snd).eraseDups).map fun bits =>
    Json.mkObj [("bits",toJson bits),("count",toJson (rs.filter (fun r => r.2==bits)).length)]
  let summary := Json.mkObj [("name",toJson name),("width",toJson (nVars s)),
    ("public_arity",toJson s.publicArity),("arithmetic_constraints",toJson terms.length),
    ("range_counts",toJson counts),("instructions",toJson b.code.size),("register_count",toJson b.next)]
  IO.FS.writeFile (folder/"emission.json") (summary.pretty++"\n")
  IO.println summary.compress
  return summary
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "artifacts"
  let e ← emitOne root "extension" extension BasisExtensionWitnessPlan.generated
  let r ← emitOne root "rescale" rescale RescaleWitnessPlan.generated
  IO.FS.writeFile (root/"emission.json") ((toJson [e,r]).pretty++"\n")
  return 0
