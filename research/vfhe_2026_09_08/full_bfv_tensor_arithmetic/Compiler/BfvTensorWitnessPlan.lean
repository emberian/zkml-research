/- Compiler-emitted untrusted witness schedule, consumed by the existing generic
BigInt executor. No AIR or field constraints are authored by that executor. -/
import Compiler.BfvTensorRow
import Compiler.BfvQueryWitnessPlan
namespace Minidregg.Compiler.BfvTensorRow.WitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler.BfvQueryRow.WitnessPlan (Operand Instruction Builder Build compute put input)
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def digit (v i : Nat) : Nat := v/64^i%64

def digits (a : Operand) : Build (Array Operand) := do
  let mut ds := #[]
  let mut rest := a
  for _ in [:11] do
    ds := ds.push (← compute 6 rest (.lit 64))
    rest ← compute 5 rest (.lit 64)
  return ds

def readWord (ds : Array Operand) : Build Operand := do
  let mut value := Operand.lit 0
  for i in [:11] do value ← compute 1 ds[10-i]! (← compute 2 (.lit 64) value)
  return value

def putBits {bits : Nat} (w : Fin bits → Fin nVars) (value : Operand) : Build Unit := do
  let mut rest := value
  for j in List.finRange bits do
    put (w j).val (← compute 6 rest (.lit 2))
    rest ← compute 5 rest (.lit 2)

def convolution (a b : Array Operand) : Build (Array Operand) := do
  let mut cs := Array.replicate 22 (Operand.lit 0)
  for i in [:11] do
    for j in [:11] do
      cs := cs.set! (i+j) (← compute 1 cs[i+j]! (← compute 2 a[i]! b[j]!))
  return cs

/-- All five caller words are copied unchanged. Only internal quotient/range/
carry witnesses are generated from them, with the quotient derived from inputs. -/
def producer (q : Nat) : Build Unit := do
  for i in [:56] do input i i
  let qd := ((List.range 11).map (fun i => Operand.lit (digit q i : Nat))).toArray
  let bd := ((List.range 11).map (fun i => Operand.lit (digit (q-1) i : Nat))).toArray
  let mut ds : Array (Array Operand) := #[]
  let mut values : Array Operand := #[]
  for g in List.finRange 5 do
    let d := ((List.finRange 11).map fun i => Operand.reg ((group g).x i).val).toArray
    ds := ds.push d
    values := values.push (← readWord d)
  for g in List.finRange 5 do
    let w := group g
    let vd := ds[g.val]!
    let sd ← digits (← compute 3 (.lit (q-1 : Nat)) values[g.val]!)
    let mut carry := Operand.lit 0
    for i in List.finRange 11 do
      putBits (w.xBit i) vd[i.val]!
      put (w.y i).val sd[i.val]!
      putBits (w.yBit i) sd[i.val]!
      put (w.carry i.castSucc).val carry
      carry ← compute 5 (← compute 1 (← compute 1 vd[i.val]! sd[i.val]!) carry) (.lit 64)
    put (w.carry 11).val carry
  let gw := group 0
  for i in List.finRange 11 do
    put (gw.z i).val bd[i.val]!
    putBits (gw.zBit i) bd[i.val]!
  for k in List.finRange 3 do
    let w := mulWires k
    let numerator ← compute 2 (.lit (factor k : Nat)) (← compute 2 values[(lhs k).val]! values[(rhs k).val]!)
    let quotient ← compute 5 numerator (.lit q)
    let kd ← digits quotient
    let ab ← convolution ds[(lhs k).val]! ds[(rhs k).val]!
    let qk ← convolution qd kd
    let pd := ds[(out k).val]!
    for i in List.finRange 11 do
      put (w.quotient i).val kd[i.val]!
      putBits (w.quotientBit i) kd[i.val]!
    let mut carry := Operand.lit 0
    for i in List.finRange 23 do
      let encoded ← compute 7 (← compute 1 carry (.lit 2048)) (.lit 0)
      put (w.carry i).val encoded
      putBits (w.carryBit i) encoded
      if i.val<22 then
        carry ← compute 5 (← compute 4 (← compute 4
          (← compute 1 (← compute 2 (.lit (factor k : Nat)) ab[i.val]!) carry) qk[i.val]!)
          (pd.getD i.val (.lit 0))) (.lit 64)

def operandJson (a : Operand) : Array Json := match a with
  | .lit n => #[toJson (0 : Nat),toJson (toString n)]
  | .reg n => #[toJson (1 : Nat),toJson n]
def instructionJson (i : Instruction) : Json :=
  Json.arr (#[toJson i.dst,toJson i.op] ++ operandJson i.a ++ operandJson i.b)
def program (q : Nat) : Builder := (producer q |>.run {next := nVars}).2

def programJson (q : Nat) : Json :=
  let p := program q
  Json.mkObj [("schema",toJson "lean-bigint-witness-plan-v1"),
    ("trace_width",toJson nVars),("input_arity",toJson (56 : Nat)),
    ("input_digit_radix",toJson (64 : Nat)),
    ("field_modulus",toJson Minidregg.Compiler.babyBearP),
    ("register_count",toJson p.next),("instructions",Json.arr (p.code.map instructionJson))]

def rowOfValues (rowID a0 a1 p0 p1 p2 : Nat) : Array Nat :=
  #[rowID] ++ (([a0,a1,p0,p1,p2]).flatMap fun x =>
    (List.range 11).map fun i => digit x i).toArray

def sampleRows (q : Nat) : Array (Array Nat) := #[
  rowOfValues 0 0 0 0 0 0,
  rowOfValues 1 3 5 9 30 25,
  rowOfValues 2 (q-1) (q-1) 1 2 1,
  rowOfValues 3 (q-2) (q-3) 4 12 9]
end Minidregg.Compiler.BfvTensorRow.WitnessPlan
