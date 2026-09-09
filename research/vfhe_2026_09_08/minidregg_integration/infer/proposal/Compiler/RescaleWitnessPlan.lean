/- Untrusted witness compilation from the actual signed source rows. The AIR and
its accepted-assignment theorem are the frozen ProfiledMatrix compiler. -/
import Compiler.ProfiledWitness
import Compiler.BfvQueryWitnessPlan

namespace Minidregg.Compiler.RescaleWitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler.DirectedRnsScaler Minidregg.Compiler.DirectedRnsWitness
open Minidregg.Compiler.BfvQueryRow.WitnessPlan
open Minidregg.Compiler.NonlinearRnsInstance Minidregg.Compiler.NonlinearRnsProfiled
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev CheckedBuild := ExceptT String Build

/-- Evaluate the known part of the source row; unknown non-pivot terms fail. -/
def knownPart {n : Nat} (row : Row n) (skip : Array Nat)
    (xs : Array (Option Operand)) : CheckedBuild Operand := do
  let mut total := Operand.lit row.constant
  for g in List.finRange n do
    let c := row.coefficient g
    if c != 0 && !skip.contains g.val then
      let some x := xs[g.val]! | throw s!"unknown source variable {g.val}"
      total ← compute 1 total (← compute 2 (.lit c) x)
  return total

/-- One-variable elimination uses the row's coefficient, never a copied formula. -/
def solveSingle {n : Nat} (row : Row n) (pivot : Fin n)
    (xs : Array (Option Operand)) : CheckedBuild (Array (Option Operand)) := do
  unless (xs[pivot.val]!).isNone do throw "single pivot already assigned"
  let c := row.coefficient pivot
  unless c == 1 || c == -1 do throw "single pivot must have unit coefficient"
  let a ← knownPart row #[pivot.val] xs
  let value ← if c == 1 then compute 4 (.lit 0) a else pure a
  return xs.set! pivot.val (some (← compute 7 value (.lit 0)))

/-- Extract quotient/remainder from a source row with negative divisor and unit
remainder coefficients. Existing Int Euclidean division supplies the witness. -/
def solveQR {n : Nat} (row : Row n) (quot rem : Fin n)
    (xs : Array (Option Operand)) : CheckedBuild (Array (Option Operand)) := do
  unless quot != rem && (xs[quot.val]!).isNone && (xs[rem.val]!).isNone do
    throw "QR pivots must be distinct and unassigned"
  let d := -row.coefficient quot
  unless d > 0 && row.coefficient rem == -1 do throw "invalid QR source coefficients"
  let a ← knownPart row #[quot.val,rem.val] xs
  let q ← compute 7 (← compute 5 a (.lit d)) (.lit 0)
  let r ← compute 7 (← compute 6 a (.lit d)) (.lit 0)
  return (xs.set! quot.val (some q)).set! rem.val (some r)

def scalarValues {L K : Nat} (p : Params L K) (inputValues : Array Operand) : CheckedBuild (Array Operand) := do
  unless inputValues.size == L do throw "source residue count mismatch"
  let mut xs : Array (Option Operand) := Array.replicate (groups L K) none
  for i in List.finRange L do xs := xs.set! (residue (K:=K) i).val (some inputValues[i.val]!)
  for i in List.finRange L do xs ← solveSingle (inputRow p i) (inputSlack i) xs
  xs ← solveQR (gRow p) (extra 0) (extra 1) xs
  xs ← solveSingle (gBound p) (extra 2) xs
  xs ← solveQR (fRow p) (extra 3) (extra 4) xs
  xs ← solveSingle (fBound p) (extra 5) xs
  xs ← solveQR (yRow p) (extra 8) (extra 6) xs
  xs ← solveSingle (yBound p) (extra 7) xs
  for i in List.finRange K do
    xs ← solveQR (targetRow p i) (target i 1) (target i 0) xs
    xs ← solveSingle (targetBound p i) (target i 2) xs
  let mut out := #[]
  for x in xs do
    let some v := x | throw "source variable remains unassigned"
    out := out.push v
  return out

def digitOperand (base : Nat) (x : Operand) (i : Nat) : Build Operand := do
  compute 6 (← compute 5 x (.lit (base^i : Nat))) (.lit base)

/-- Public aliases are equality assertions, so caller input columns are retained. -/
def putInner (j : Nat) (a : Operand) : Build Unit := do
  let k := NonlinearRnsPublic.wireMap j
  if k<89 then
    modify fun s => {s with code := s.code.push ⟨k,9,.reg k,a⟩}
  else put k a

def installPlan (offset bits : Nat) (ds : Array Operand) : Build Unit := do
  for i in [:ds.size] do
    putInner (offset+i) ds[i]!
    for j in [:bits] do
      putInner (offset+ds.size+bits*i+j) (← digitOperand 2 ds[i]! j)

def carryPlan (base : Nat) (c : SideCache) (ds : Array Operand) : Build (Array Operand) := do
  let mut carry := Operand.lit 0
  let mut out := #[carry]
  for col in [:c.columnCoefficients.size] do
    let mut mass ← compute 1 (.lit c.constantDigits[col]!) carry
    for (i,d) in c.columnCoefficients[col]! do
      mass ← compute 1 mass (← compute 2 (.lit d) ds[i]!)
    carry ← compute 5 mass (.lit base)
    out := out.push carry
  return out

def producer : CheckedBuild Unit := do
  for i in [:88] do input i i
  let mut rs := #[]
  for i in [:9] do
    let mut r := Operand.lit 0
    for d in [:7] do
      r ← compute 1 r (← compute 2 (.lit (512^d : Nat)) (.reg (1+7*i+d)))
    rs := rs.push r
  let xs ← scalarValues params rs
  let mut ds := #[]
  for i in List.finRange profile.scalars do
    let gd := (groupDigit profile).symm i
    ds := ds.push (← digitOperand profile.base xs[gd.1.val]! gd.2.val)
  installPlan 0 profile.limbBits ds
  let cache := ProfiledWitness.caches profile rowLayout rows
  for row in List.finRange profile.rows do
    let (l,r) := cache[row.val]!
    let mut total := Operand.lit l.constant
    for i in [:ds.size] do
      if l.coefficients[i]! != 0 then
        total ← compute 1 total (← compute 2 (.lit l.coefficients[i]!) ds[i]!)
    let mut rd := #[]
    for i in [:rowLayout.width row] do rd := rd.push (← digitOperand profile.base total i)
    let start := ProfiledMatrix.resultStart profile rowLayout row
    installPlan start profile.limbBits rd
    let width := rowLayout.width row
    let bits := rowLayout.carryBits row
    installPlan (start+width*(1+profile.limbBits)) bits (← carryPlan profile.base l ds)
    installPlan (start+width*(1+profile.limbBits)+(width+1)*(1+bits)) bits (← carryPlan profile.base r ds)

def operandJson (a : Operand) : Array Json := match a with
  | .lit n => #[toJson (0 : Nat),toJson (toString n)]
  | .reg n => #[toJson (1 : Nat),toJson n]
def instructionJson (i : Instruction) : Json :=
  Json.arr (#[toJson i.dst,toJson i.op] ++ operandJson i.a ++ operandJson i.b)
def generated : Except String Builder :=
  let (result,b) := producer.run.run {next:=nVars}
  result.map fun _ => b
def programJson (b : Builder) : Json := Json.mkObj [
  ("schema",toJson "lean-bigint-witness-plan-v1"),
  ("trace_width",toJson nVars),("input_arity",toJson (88 : Nat)),
  ("input_digit_radix",toJson (512 : Nat)),("field_modulus",toJson babyBearP),
  ("register_count",toJson b.next),("instructions",Json.arr (b.code.map instructionJson))]
end Minidregg.Compiler.RescaleWitnessPlan
