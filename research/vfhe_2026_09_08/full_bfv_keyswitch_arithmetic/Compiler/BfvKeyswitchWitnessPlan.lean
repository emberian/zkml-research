/- Compiler-emitted untrusted witness schedule, consumed by the existing generic
BigInt executor. No AIR or field constraints are authored by that executor. -/
import Compiler.BfvKeyswitchRow
import Compiler.BfvQueryWitnessPlan
namespace Minidregg.Compiler.BfvKeyswitchRow.WitnessPlan
open Lean (Json toJson)
open Minidregg.Compiler.BfvQueryRow.WitnessPlan (Operand Instruction Builder Build compute put input)
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def digit (v i : Nat) : Nat := v/512^i%512

def digits (a : Operand) : Build (Array Operand) := do
  let mut ds := #[]
  let mut rest := a
  for _ in [:6] do
    ds := ds.push (← compute 6 rest (.lit 512))
    rest ← compute 5 rest (.lit 512)
  return ds

def readWord (ds : Array Operand) : Build Operand := do
  let mut value := Operand.lit 0
  for i in [:6] do value ← compute 1 ds[5-i]! (← compute 2 (.lit 512) value)
  return value

def putBits {bits : Nat} (w : Fin bits → Fin nVars) (value : Operand) : Build Unit := do
  let mut rest := value
  for j in List.finRange bits do
    put (w j).val (← compute 6 rest (.lit 2))
    rest ← compute 5 rest (.lit 2)

def convolution (a b : Array Operand) : Build (Array Operand) := do
  let mut cs := Array.replicate 12 (Operand.lit 0)
  for i in [:6] do
    for j in [:6] do
      cs := cs.set! (i+j) (← compute 1 cs[i+j]! (← compute 2 a[i]! b[j]!))
  return cs

/-- All sixteen public words are copied unchanged; only source auxiliaries are generated. -/
def producer (q : Nat) : Build Unit := do
  for i in [:97] do input i i
  let qd := ((List.range 6).map (fun i => Operand.lit (digit q i : Nat))).toArray
  let bd := ((List.range 6).map (fun i => Operand.lit (digit (q-1) i : Nat))).toArray
  let mut ds : Array (Array Operand) := #[]
  let mut values : Array Operand := #[]
  for g in List.finRange 16 do
    let d := ((List.finRange 6).map fun i => Operand.reg ((group g).x i).val).toArray
    ds := ds.push d
    values := values.push (← readWord d)
  for g in List.finRange 16 do
    let w := group g
    let vd := ds[g.val]!
    let sd ← digits (← compute 3 (.lit (q-1 : Nat)) values[g.val]!)
    let mut carry := Operand.lit 0
    for i in List.finRange 6 do
      putBits (w.xBit i) vd[i.val]!
      put (w.y i).val sd[i.val]!
      putBits (w.yBit i) sd[i.val]!
      put (w.carry i.castSucc).val carry
      carry ← compute 5 (← compute 1 (← compute 1 vd[i.val]! sd[i.val]!) carry) (.lit 512)
    put (w.carry 6).val carry
  let gw := group 0
  for i in List.finRange 6 do
    put (gw.z i).val bd[i.val]!
    putBits (gw.zBit i) bd[i.val]!
  for h in List.finRange 2 do
    let w := macWires h
    let mut numerator := values[12+h.val]!
    let mut ab := Array.replicate 12 (Operand.lit 0)
    for k in [:4] do
      numerator ← compute 1 numerator (← compute 2 values[k]! values[4+4*h.val+k]!)
      let prod ← convolution ds[k]! ds[4+4*h.val+k]!
      for i in [:12] do ab := ab.set! i (← compute 1 ab[i]! prod[i]!)
    let quotient ← compute 5 numerator (.lit q)
    let kd ← digits quotient
    let qk ← convolution qd kd
    let ad := ds[12+h.val]!
    let pd := ds[14+h.val]!
    for i in List.finRange 6 do
      put (w.quotient i).val kd[i.val]!
      putBits (w.quotientBit i) kd[i.val]!
    let mut carry := Operand.lit 0
    for i in List.finRange 13 do
      let encoded ← compute 7 (← compute 1 carry (.lit 32768)) (.lit 0)
      put (w.carry i).val encoded
      putBits (w.carryBit i) encoded
      if i.val<12 then
        carry ← compute 5 (← compute 4 (← compute 4
          (← compute 1 (← compute 1 ab[i.val]! (ad.getD i.val (.lit 0))) carry) qk[i.val]!)
          (pd.getD i.val (.lit 0))) (.lit 512)

def operandJson (a : Operand) : Array Json := match a with
  | .lit n => #[toJson (0 : Nat),toJson (toString n)]
  | .reg n => #[toJson (1 : Nat),toJson n]
def instructionJson (i : Instruction) : Json :=
  Json.arr (#[toJson i.dst,toJson i.op] ++ operandJson i.a ++ operandJson i.b)
def program (q : Nat) : Builder := (producer q |>.run {next := nVars}).2

def programJson (q : Nat) : Json :=
  let p := program q
  Json.mkObj [("schema",toJson "lean-bigint-witness-plan-v1"),
    ("trace_width",toJson nVars),("input_arity",toJson (97 : Nat)),
    ("input_digit_radix",toJson (512 : Nat)),
    ("field_modulus",toJson Minidregg.Compiler.babyBearP),
    ("register_count",toJson p.next),("instructions",Json.arr (p.code.map instructionJson))]

def rowOfValues (rowID : Nat) (xs : List Nat) : Array Nat :=
  #[rowID] ++ (xs.flatMap fun x => (List.range 6).map fun i => digit x i).toArray

def sampleRows : Array (Array Nat) := #[
  rowOfValues 0 (List.replicate 16 0),
  rowOfValues 1 [1,2,3,4,2,2,2,2,3,3,3,3,7,5,27,35]]
end Minidregg.Compiler.BfvKeyswitchRow.WitnessPlan
