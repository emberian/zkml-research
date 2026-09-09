import Compiler.ActualBasisExtension
import Lean.Data.Json
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.ActualBasisExtension
def main : IO UInt32 := do
  let q := ProfiledMatrix.autoLayout profile rows
  IO.println ((Json.mkObj [("width",toJson (Array.ofFn q.width)),
    ("carry_bits",toJson (Array.ofFn q.carryBits)),
    ("nVars",toJson (85+ProfiledMatrix.nVars profile q))]).compress)
  return 0
