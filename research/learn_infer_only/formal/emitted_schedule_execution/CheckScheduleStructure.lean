/- Compiled structural evidence only. This IO runner is not a theorem module. -/
import Compiler.EmittedScheduleExecution
import Lean.Data.Json

open Lean (Json toJson)
open Minidregg.Compiler
open Minidregg.Compiler.PrivateAddressEmaSchedule
open Minidregg.Compiler.EmittedScheduleExecution

def report (operation : String) (d : ConstraintDescriptor F2) : Json := Json.mkObj
  [("operation", toJson operation), ("structurallyValid", toJson (validCheck d)),
   ("nInputs", toJson d.nVars), ("nWires", toJson d.nWires),
   ("gates", toJson d.gates.length), ("outputs", toJson d.zeros.length)]

def main : IO Unit := do
  let l := learnSchedule
  let i := inferSchedule
  IO.println ((Json.arr #[report "learn" l, report "infer" i]).compress)
  if !(validCheck l && validCheck i) then
    throw (IO.userError "computed structural check failed")
