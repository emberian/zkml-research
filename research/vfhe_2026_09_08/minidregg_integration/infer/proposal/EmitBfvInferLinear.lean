import Compiler.BfvInferLinear
open Lean Minidregg.Compiler.BfvInferLinear

def main (args : List String) : IO Unit := do
  let out := args.headD "artifacts/linear_plan.json"
  let stages := (List.finRange 10).map fun i => Json.mkObj [
    ("index",toJson (i.val+1)),("exponent",toJson (exponents i)),
    ("permutation",toJson ((List.finRange degree).map fun j => (permutation (exponents i) j).val))]
  let plan := Json.mkObj [("schema",toJson "lean-bfv-infer-linear-plan-v1"),
    ("degree",toJson degree),("primes",toJson (List.ofFn primes)),("stages",toJson stages)]
  IO.FS.writeFile out (plan.compress++"\n")
