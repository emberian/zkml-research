/- The native producer remains untrusted. All equations come from the basis
extension source and all carry data from the existing signed-matrix compiler. -/
import Compiler.BasisExtensionPublic
import Compiler.RescaleWitnessPlan

namespace Minidregg.Compiler.BasisExtensionWitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler.ExactBasisExtension Minidregg.Compiler.ActualBasisExtension
open Minidregg.Compiler.BfvQueryRow.WitnessPlan
open Minidregg.Compiler.RescaleWitnessPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def scalars : CheckedBuild (Array Operand) := do
  let mut xs : Array (Option Operand) := Array.replicate 30 none
  for i in List.finRange 4 do
    let mut r := Operand.lit 0
    for d in [:6] do r ← compute 1 r (← compute 2 (.lit (512^d : Nat)) (.reg (1+6*i.val+d)))
    xs := xs.set! (residue (K:=5) i).val (some r)
  for i in List.finRange 4 do xs ← solveSingle (inputRow params i) (slack i) xs
  xs ← solveQR (garnerRow params) (extra 0) (extra 1) xs
  xs ← solveSingle (garnerBound params) (extra 2) xs
  for i in List.finRange 5 do
    xs ← solveQR (targetRow params i) (target i 1) (target i 0) xs
    xs ← solveSingle (targetBound params i) (target i 2) xs
  for i in List.finRange 4 do xs ← solveSingle (copyRow (K:=5) i) (copied (K:=5) i) xs
  let mut out := #[]
  for x in xs do
    let some v := x | throw "extension scalar remains unassigned"
    out := out.push v
  return out

def putMapped (mapping : Nat → Nat) (reserved : Nat) (j : Nat) (a : Operand) : Build Unit := do
  let k := mapping j
  if k<reserved then modify fun s => {s with code:=s.code.push ⟨k,9,.reg k,a⟩}
  else put k a
def installMapped (mapping : Nat → Nat) (reserved offset bits : Nat) (ds : Array Operand) : Build Unit := do
  for i in [:ds.size] do
    putMapped mapping reserved (offset+i) ds[i]!
    for j in [:bits] do
      putMapped mapping reserved (offset+ds.size+bits*i+j) (← digitOperand 2 ds[i]! j)

def producer : CheckedBuild Unit := do
  for i in [:84] do input i i
  let xs ← scalars
  let mut ds := #[]
  for i in List.finRange profile.scalars do
    let gd := (groupDigit profile).symm i
    ds := ds.push (← digitOperand profile.base xs[gd.1.val]! gd.2.val)
  installMapped wireMap 85 0 profile.limbBits ds
  let cache := ProfiledWitness.caches profile rowLayout rows
  for row in List.finRange profile.rows do
    let (l,r) := cache[row.val]!
    let mut total := Operand.lit l.constant
    for i in [:ds.size] do
      if l.coefficients[i]! != 0 then total ← compute 1 total (← compute 2 (.lit l.coefficients[i]!) ds[i]!)
    let mut rd := #[]
    for i in [:rowLayout.width row] do rd := rd.push (← digitOperand profile.base total i)
    let start := ProfiledMatrix.resultStart profile rowLayout row
    let width := rowLayout.width row
    let bits := rowLayout.carryBits row
    installMapped wireMap 85 start profile.limbBits rd
    installMapped wireMap 85 (start+width*(1+profile.limbBits)) bits (← carryPlan profile.base l ds)
    installMapped wireMap 85 (start+width*(1+profile.limbBits)+(width+1)*(1+bits)) bits
      (← carryPlan profile.base r ds)

def generated : Except String Builder :=
  let (r,b) := producer.run.run {next:=nVars}
  r.map fun _ => b
def programJson (b : Builder) : Json := Json.mkObj [
  ("schema",toJson "lean-bigint-witness-plan-v1"),("trace_width",toJson nVars),
  ("input_arity",toJson (84 : Nat)),("input_digit_radix",toJson (512 : Nat)),
  ("field_modulus",toJson babyBearP),("register_count",toJson b.next),
  ("instructions",Json.arr (b.code.map RescaleWitnessPlan.instructionJson))]

end Minidregg.Compiler.BasisExtensionWitnessPlan
