/- Reuse the frozen witness instruction machinery with the actual expiry layout.
The source relation remains BfvExpiry.system, with no native-authored AIR. -/
import Compiler.BfvQueryWitnessPlan
namespace Minidregg.Compiler.BfvExpiry.WitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler.BfvQueryRow.WitnessPlan
  (Operand Builder Build compute put input instructionJson)
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def planDigits := Minidregg.Compiler.BfvQueryRow.WitnessPlan.digits
def planWord := Minidregg.Compiler.BfvQueryRow.WitnessPlan.readWord

def putBits {bits : Nat} (w : Fin bits → Fin nVars) (value : Operand) : Build Unit := do
  for j in List.finRange bits do
    put (w j).val (← compute 6 (← compute 5 value (.lit (2^j.val : Nat))) (.lit 2))

def producer : Build Unit := do
  for i in [:57] do input i i
  for l in List.finRange 2 do
    let q := primes l
    let w := layout l
    let qd := (List.range 7).map (fun i => Operand.lit (BfvExpiry.digit q i : Nat)) |>.toArray
    let bd := (List.range 7).map (fun i => Operand.lit (BfvExpiry.digit (q-1) i : Nat)) |>.toArray
    let mut ds : Array (Array Operand) := #[]
    let mut values : Array Operand := #[]
    for g in List.finRange 4 do
      let cw := w.canonical g
      let d := (List.finRange 7).map (fun i => Operand.reg (cw.x i).val) |>.toArray
      let value ← planWord d
      values := values.push value
      ds := ds.push d
      let slack ← planDigits (← compute 3 (.lit (q-1 : Nat)) value)
      let mut carry := Operand.lit 0
      for i in List.finRange 7 do
        putBits (cw.xBit i) d[i.val]!
        put (cw.y i).val slack[i.val]!
        putBits (cw.yBit i) slack[i.val]!
        put (cw.carry i.castSucc).val carry
        carry ← compute 5 (← compute 1 (← compute 1 d[i.val]! slack[i.val]!) carry) (.lit 64)
      put (cw.carry 7).val carry
    let cw := w.canonical 0
    for i in List.finRange 7 do
      put (cw.z i).val bd[i.val]!
      putBits (cw.zBit i) bd[i.val]!
    let quotient ← compute 5 (← compute 3 (← compute 1
      (← compute 1 values[0]! values[1]!) (.lit q)) values[2]!) (.lit q)
    put w.quotient.val quotient
    putBits w.quotientBit quotient
    let mut carry := Operand.lit 0
    for i in List.finRange 8 do
      let encoded ← compute 7 (← compute 1 carry (.lit 4)) (.lit 0)
      put (w.carry i).val encoded
      putBits (w.carryBit i) encoded
      if i.val<7 then
        carry ← compute 5 (← compute 4 (← compute 4 (← compute 4
          (← compute 1 (← compute 1 (← compute 1 (ds[0]!)[i.val]! (ds[1]!)[i.val]!) qd[i.val]!) carry)
          (ds[2]!)[i.val]!) (ds[3]!)[i.val]!) (← compute 2 qd[i.val]! quotient)) (.lit 64)

def program : Builder := (producer.run {next := nVars}).2

def programJson : Json := Json.mkObj [
  ("schema",toJson "lean-bfv-query-witness-plan-v1"),
  ("operation",toJson "bfv-expiry-acc-plus-fresh-minus-old"),
  ("trace_width",toJson nVars),("input_arity",toJson (57 : Nat)),
  ("field_modulus",toJson Minidregg.Compiler.babyBearP),
  ("register_count",toJson program.next),("instructions",Json.arr (program.code.map instructionJson))]
end Minidregg.Compiler.BfvExpiry.WitnessPlan
