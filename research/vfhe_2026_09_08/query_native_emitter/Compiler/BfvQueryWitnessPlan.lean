/- Executable producer compilation only: the verifier relation remains the frozen
BfvQueryRow.emittedSystem. This plan is untrusted witness-generation data. -/
import Compiler.BfvQueryWitness
import Lean.Data.Json
namespace Minidregg.Compiler.BfvQueryRow.WitnessPlan
open Lean (Json toJson)
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

inductive Operand where
  | lit : Int → Operand
  | reg : Nat → Operand
  deriving Inhabited
structure Instruction where
  dst : Nat
  op : Nat
  a : Operand
  b : Operand
structure Builder where
  next : Nat := nVars
  code : Array Instruction := #[]
abbrev Build := StateM Builder

def compute (op : Nat) (a b : Operand) : Build Operand := do
  if let .lit x := a then
    if let .lit y := b then
      return .lit (match op with
        | 1 => x+y | 2 => x*y | 3 => max (x-y) 0 | 4 => x-y
        | 5 => x/y | 6 => x%y | 7 => max x 0 | _ => x)
  let s : Builder ← get
  set ({next := s.next+1,code := s.code.push ⟨s.next,op,a,b⟩} : Builder)
  return .reg s.next

def put (dst : Nat) (a : Operand) : Build Unit :=
  modify fun s => {s with code := s.code.push ⟨dst,0,a,.lit 0⟩}

def input (dst index : Nat) : Build Unit :=
  modify fun s => {s with code := s.code.push ⟨dst,8,.lit index,.lit 0⟩}

def digits (a : Operand) : Build (Array Operand) := do
  let mut ds := #[]
  for i in [:7] do ds := ds.push (← compute 6 (← compute 5 a (.lit (64^i : Nat))) (.lit 64))
  return ds

def readWord (ds : Array Operand) : Build Operand := do
  let mut value := Operand.lit 0
  for i in [:7] do value ← compute 1 ds[6-i]! (← compute 2 (.lit 64) value)
  return value

def putBits {bits : Nat} (w : Fin bits → Fin nVars) (value : Operand) : Build Unit := do
  for j in List.finRange bits do
    put (w j).val (← compute 6 (← compute 5 value (.lit (2^j.val : Nat))) (.lit 2))

def convolution (a b : Array Operand) : Build (Array Operand) := do
  let mut cs := Array.replicate 14 (Operand.lit 0)
  for i in [:7] do
    for j in [:7] do cs := cs.set! (i+j) (← compute 1 cs[i+j]! (← compute 2 a[i]! b[j]!))
  return cs

def producer : Build Unit := do
  for i in [:57] do input i i
  for l in List.finRange 2 do
    let q := primes l
    let qd := (List.range 7).map (fun i => Operand.lit (BfvQueryRow.digit q i : Nat)) |>.toArray
    let bd := (List.range 7).map (fun i => Operand.lit (BfvQueryRow.digit (q-1) i : Nat)) |>.toArray
    let mut ds : Array (Array Operand) := #[]
    let mut values : Array Operand := #[]
    for g in List.finRange 4 do
      let d := (List.finRange 7).map (fun i => Operand.reg ((group l (g.castLE (by decide))).x i).val) |>.toArray
      ds := ds.push d
      values := values.push (← readWord d)
    let mut numerators : Array Operand := #[]
    let mut quotients : Array Operand := #[]
    for sign in [:2] do
      let product ← compute 2 values[0]! values[1+sign]!
      numerators := numerators.push product
      quotients := quotients.push (← compute 5 product (.lit q))
      let reduced ← compute 6 product (.lit q)
      values := values.push reduced
      ds := ds.push (← digits reduced)
    values := values.push (.lit 0)
    ds := ds.push (Array.replicate 7 (.lit 0))
    for g in List.finRange 7 do
      let w := group l g
      let vd := ds[g.val]!
      let sd ← digits (← compute 3 (.lit (q-1 : Nat)) values[g.val]!)
      let mut carry := Operand.lit 0
      for i in List.finRange 7 do
        if 4 ≤ g.val then put (w.x i).val vd[i.val]!
        putBits (w.xBit i) vd[i.val]!
        put (w.y i).val sd[i.val]!
        putBits (w.yBit i) sd[i.val]!
        put (w.carry i.castSucc).val carry
        carry ← compute 5 (← compute 1 (← compute 1 vd[i.val]! sd[i.val]!) carry) (.lit 64)
      put (w.carry 7).val carry
    let gw := group l 0
    for i in List.finRange 7 do
      put (gw.z i).val bd[i.val]!
      putBits (gw.zBit i) bd[i.val]!
    for sign in List.finRange 2 do
      let w := mulWires l sign
      let kd ← digits quotients[sign.val]!
      let ab ← convolution ds[0]! ds[1+sign.val]!
      let qk ← convolution qd kd
      let pd := ds[4+sign.val]!
      for i in List.finRange 7 do
        put (w.quotient i).val kd[i.val]!
        putBits (w.quotientBit i) kd[i.val]!
      let mut carry := Operand.lit 0
      for i in List.finRange 15 do
        let encoded ← compute 7 (← compute 1 carry (.lit 512)) (.lit 0)
        put (w.carry i).val encoded
        putBits (w.carryBit i) encoded
        if i.val<14 then
          carry ← compute 5 (← compute 4 (← compute 4 (← compute 1 ab[i.val]! carry) qk[i.val]!)
            (pd.getD i.val (.lit 0))) (.lit 64)
    let w := subWires l
    let quotient ← compute 5 (← compute 3 (← compute 1 values[4]! (.lit q)) values[5]!) (.lit q)
    put w.quotient.val quotient
    putBits w.quotientBit quotient
    let mut carry := Operand.lit 0
    for i in List.finRange 8 do
      let encoded ← compute 7 (← compute 1 carry (.lit 4)) (.lit 0)
      put (w.carry i).val encoded
      putBits (w.carryBit i) encoded
      if i.val<7 then
        carry ← compute 5 (← compute 4 (← compute 4 (← compute 4
          (← compute 1 (← compute 1 (ds[4]!)[i.val]! qd[i.val]!) carry)
          (ds[5]!)[i.val]!) (ds[3]!)[i.val]!) (← compute 2 qd[i.val]! quotient)) (.lit 64)

def operandJson (a : Operand) : Array Json := match a with
  | .lit n => #[toJson (0 : Nat),toJson n]
  | .reg n => #[toJson (1 : Nat),toJson n]
def instructionJson (i : Instruction) : Json :=
  Json.arr (#[toJson i.dst,toJson i.op] ++ operandJson i.a ++ operandJson i.b)
def program : Builder := (producer.run {}).2

def programJson : Json := Json.mkObj [
  ("schema",toJson "lean-bfv-query-witness-plan-v1"),
  ("trace_width",toJson nVars),("input_arity",toJson (57 : Nat)),
  ("field_modulus",toJson Minidregg.Compiler.babyBearP),
  ("register_count",toJson program.next),("instructions",Json.arr (program.code.map instructionJson))]
end Minidregg.Compiler.BfvQueryRow.WitnessPlan
