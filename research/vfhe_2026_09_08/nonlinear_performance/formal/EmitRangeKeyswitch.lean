/- The existing source term fold, now using whole-row gates and declared native
range relations. Only a projection is appended to the old untrusted witness plan. -/
import Compiler.RangeKeyswitchRow
import Compiler.BfvKeyswitchWitnessPlan
import Compiler.Ir2WholeRow
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.RangeKeyswitchRow
open Minidregg.Compiler.BfvQueryRow.WitnessPlan (Operand Builder Build put)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ir2Var (i : Nat) : String := "{\"t\":\"var\",\"v\":"++toString i++"}"
def rangeLookup (r : RangeSpec) : String :=
  "{\"t\":\"lookup\",\"table\":"++toString (69+r.bits)++",\"tuple\":["++ir2Var r.wire.val++"]}"
def ir2Template (q : Nat) : String :=
  let arithmetic := (system q).map (Ir2WholeRow.gateJson (fun c : BabyBear => c.val) Fin.val)
  let lookup := "{\"t\":\"lookup\",\"table\":11,\"tuple\":["++String.intercalate "," ((List.range 97).map ir2Var)++"]}"
  "{\"name\":\"bfv_range_paired_keyswitch_mac_q"++toString q++"\",\"ir\":2,\"trace_width\":"++toString nVars++
    ",\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":11,\"name\":\"bfv_public_keyswitch_rows\",\"arity\":97,\"sem\":\"exact_public_rows\",\"rows\":[]},"++
    "{\"id\":78,\"name\":\"range9\",\"arity\":1,\"sem\":\"range\",\"bits\":9},"++
    "{\"id\":85,\"name\":\"range16\",\"arity\":1,\"sem\":\"range\",\"bits\":16}],\"constraints\":["++
    String.intercalate "," (lookup::(ranges.map rangeLookup)++arithmetic)++"],\"hash_sites\":[],\"ranges\":[]}"

def projection : Build Unit := do
  for i in List.finRange nVars do put i.val (.reg (oldIndex i))
def program (q : Nat) : Builder :=
  (projection.run (BfvKeyswitchRow.WitnessPlan.program q)).2

def programJson (q : Nat) : Json :=
  let p := program q
  Json.mkObj [("schema",toJson "lean-bigint-witness-plan-v1"),
    ("trace_width",toJson nVars),("input_arity",toJson (97 : Nat)),
    ("input_digit_radix",toJson (512 : Nat)),("field_modulus",toJson babyBearP),
    ("register_count",toJson p.next),
    ("instructions",Json.arr (p.code.map BfvKeyswitchRow.WitnessPlan.instructionJson))]

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "artifacts"
  IO.FS.createDirAll root
  let mut rows : Array Json := #[]
  for l in List.finRange 4 do
    let q := BfvKeyswitchRow.primes l
    let folder := root / ("prime"++toString l.val)
    IO.FS.createDirAll folder
    IO.FS.writeFile (folder / "template_ir2.json") (ir2Template q++"\n")
    IO.FS.writeFile (folder / "witness_plan.json") ((programJson q).compress++"\n")
    let p := program q
    let row := Json.mkObj [("prime_index",toJson l.val),("prime",toJson q),
      ("width",toJson nVars),("public_arity",toJson (97 : Nat)),
      ("range9",toJson (ranges.filter (fun r => r.bits==9)).length),
      ("range16",toJson (ranges.filter (fun r => r.bits==16)).length),
      ("arithmetic_constraints",toJson (system q).length),
      ("instructions",toJson p.code.size),("register_count",toJson p.next)]
    rows := rows.push row
    IO.println row.compress
  IO.FS.writeFile (root / "emission.json") (Json.arr rows |>.pretty)
  return 0
