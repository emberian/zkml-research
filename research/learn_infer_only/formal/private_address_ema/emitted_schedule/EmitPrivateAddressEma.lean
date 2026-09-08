/- IO runner only. Gate author is the existing Lean compiler, through the
checked source module. This file is not a rooted theorem module. -/
import Compiler.PrivateAddressEmaSchedule
import Lean.Data.Json

open Lean (Json toJson)
open Minidregg.Compiler
open Minidregg.Compiler.PrivateAddressEmaSchedule

def wireJson : DWire F2 → Json
  | .cnst c => Json.mkObj [("c", toJson (c.val == 1))]
  | .wire n => Json.mkObj [("w", toJson n)]

def gateJson (g : DGate F2) : Json := Json.mkObj
  [("op", toJson (match g.op with | .add => "xor" | .mul => "and")),
   ("a", wireJson g.a), ("b", wireJson g.b), ("out", toJson g.out)]

def scheduleJson (operation : String) (d : ConstraintDescriptor F2) : Json := Json.mkObj
  [("schema", toJson "private-address-ema-bool-schedule-v1"),
   ("operation", toJson operation), ("nInputs", toJson d.nVars),
   ("nWires", toJson d.nWires), ("gates", toJson (d.gates.map gateJson)),
   ("outputs", toJson (d.zeros.map wireJson))]

def main : IO Unit := do
  IO.FS.createDirAll "artifacts"
  let ld := learnSchedule
  let id := inferSchedule
  IO.FS.writeFile "artifacts/learn.json" ((scheduleJson "learn" ld).compress ++ "\n")
  IO.FS.writeFile "artifacts/infer.json" ((scheduleJson "infer" id).compress ++ "\n")
  IO.println ((Json.mkObj [
    ("learn", Json.mkObj [("nInputs",toJson ld.nVars),("nWires",toJson ld.nWires),
      ("gates",toJson ld.gates.length),("outputs",toJson ld.zeros.length)]),
    ("infer", Json.mkObj [("nInputs",toJson id.nVars),("nWires",toJson id.nWires),
      ("gates",toJson id.gates.length),("outputs",toJson id.zeros.length)])]).compress)
