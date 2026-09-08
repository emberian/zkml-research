import Compiler.ProfiledMatrix
import Compiler.NonlinearRnsInstance
import Lean.Data.Json
open Minidregg.Compiler Minidregg.Compiler.NonlinearRnsInstance Minidregg.Compiler.ProfiledMatrix
open Lean (Json toJson)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO UInt32 := do
  let p := autoLayout profile rows
  let r := Json.mkObj [("widths",toJson (Array.ofFn p.width)),("carry_bits",toJson (Array.ofFn p.carryBits)),
    ("nVars",toJson (89+nVars profile p)),("row_vars",toJson (Array.ofFn (rowVars p))),
    ("scalar_vars",toJson (profile.scalars*(1+profile.limbBits)))]
  IO.FS.writeFile "results/profile.json" (r.pretty++"\n")
  IO.println r.compress
  return 0
