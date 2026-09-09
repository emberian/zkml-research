import Compiler.RescaleWitnessPlan
open Minidregg.Compiler.RescaleWitnessPlan
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath := args.headD "program/witness_plan.json"
  let b ← IO.ofExcept generated
  IO.FS.writeFile out ((programJson b).compress++"\n")
  IO.println s!"emitted {b.code.size} instructions, {b.next} registers; frozen AIR unchanged"
  return 0
