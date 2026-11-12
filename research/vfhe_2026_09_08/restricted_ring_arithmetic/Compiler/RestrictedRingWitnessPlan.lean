/- Reusable untrusted witness instructions, produced in Lean from the actual
layout. The verifier consumes only the unchanged proved source relation. -/
import Compiler.RestrictedRingWindow
import Compiler.BfvQueryWitnessPlan

namespace Minidregg.Compiler.RestrictedRingWitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Compiler.RestrictedRingWindow
open Minidregg.Compiler.BfvQueryRow.WitnessPlan (Operand Instruction Builder Build compute put input)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def digitOperand (value : Operand) (i : Nat) : Build Operand :=
  compute 6 (← compute 5 value (.lit (radix^i : Nat))) (.lit radix)

def putBits {bits : Nat} (w : Fin bits → Fin nVars) (value : Operand) : Build Unit := do
  for j in List.finRange bits do
    put (w j).val (← compute 6 (← compute 5 value (.lit (2^j.val : Nat))) (.lit 2))

def readWord (digits : Array Operand) : Build Operand := do
  let mut value := Operand.lit 0
  for i in [:11] do value ← compute 1 digits[10-i]! (← compute 2 (.lit radix) value)
  return value

def producer : Build Unit := do
  for i in [:45] do input i i
  let mut words : Array Operand := #[]
  let mut ds : Array (Array Operand) := #[]
  for kind in List.finRange 4 do
    let w := layout.canonical kind
    let digits := ((List.finRange 11).map fun i => Operand.reg (w.x i).val).toArray
    let value ← readWord digits
    ds := ds.push digits
    words := words.push value
    let slack ← compute 3 (.lit (modulus-1 : Nat)) value
    let mut carry := Operand.lit 0
    for i in List.finRange 11 do
      let yd ← digitOperand slack i.val
      putBits (w.xBit i) digits[i.val]!
      put (w.y i).val yd
      putBits (w.yBit i) yd
      put (w.carry i.castSucc).val carry
      carry ← compute 5 (← compute 1 (← compute 1 digits[i.val]! yd) carry) (.lit radix)
    put (w.carry 11).val carry
  for i in List.finRange 11 do
    let d := Operand.lit (digit (modulus-1) i.val : Nat)
    put ((layout.canonical 0).z i).val d
    putBits ((layout.canonical 0).zBit i) d
  let k ← compute 5 (← compute 3 (← compute 1 (← compute 1 words[0]! words[1]!) (.lit modulus)) words[2]!) (.lit modulus)
  put layout.quotient.val k
  putBits layout.quotientBit k
  let mut carry := Operand.lit 0
  for i in List.finRange 12 do
    let encoded ← compute 7 (← compute 1 carry (.lit 4)) (.lit 0)
    put (layout.carry i).val encoded
    putBits (layout.carryBit i) encoded
    if i.val < 11 then
      let qd := Operand.lit (digit modulus i.val : Nat)
      let left ← compute 1 (← compute 1 (← compute 1 (ds[0]!)[i.val]! (ds[1]!)[i.val]!) qd) carry
      let right ← compute 1 (← compute 1 (ds[2]!)[i.val]! (ds[3]!)[i.val]!) (← compute 2 qd k)
      carry ← compute 5 (← compute 4 left right) (.lit radix)

def operandJson (a : Operand) : Array Json := match a with
  | .lit n => #[toJson (0 : Nat),toJson (toString n)]
  | .reg n => #[toJson (1 : Nat),toJson n]
def instructionJson (i : Instruction) : Json :=
  Json.arr (#[toJson i.dst,toJson i.op] ++ operandJson i.a ++ operandJson i.b)
def program : Builder := (producer.run {next := nVars}).2
def programJson : Json := Json.mkObj [
  ("schema",toJson "lean-bigint-witness-plan-v1"),
  ("trace_width",toJson nVars),("input_arity",toJson publicWidth),
  ("input_digit_radix",toJson radix),("field_modulus",toJson babyBearP),
  ("register_count",toJson program.next),("instructions",Json.arr (program.code.map instructionJson))]
end Minidregg.Compiler.RestrictedRingWitnessPlan
