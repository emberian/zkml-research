import Compiler.DirectedRnsScaler
import Compiler.AirSimplify
import Compiler.PredCompile

namespace Minidregg.Compiler.DirectedRnsWitness
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DirectedRnsScaler
open Minidregg.Compiler.SignedMatrix
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def digit (base value index : Nat) := value/base^index%base

def values {L K : Nat} (p : Params L K) (r : Fin L → Int) (g : Fin (groups L K)) : Nat :=
  let c := honest p r
  if hr : g.val<L then (r ⟨g.val,hr⟩).toNat
  else if hs : g.val<2*L then p.sourceBase ⟨g.val-L,by omega⟩-1-(r ⟨g.val-L,by omega⟩).toNat
  else if hx : g.val<2*L+9 then
    (![c.v,c.gRem,2*p.dG-1-c.gRem,c.w+p.wOffset,c.fRem,2*p.dF-1-c.fRem,c.y,p.Q-1-c.y,c.u+p.uOffset]
      ⟨g.val-2*L,by omega⟩).toNat
  else
    let i : Fin K := ⟨(g.val-(2*L+9))/3,by have := g.isLt; dsimp [groups] at this; omega⟩
    let o := c.y%(p.targetBase i)
    (![o,c.targetQuot i,p.targetBase i-1-o] ⟨(g.val-(2*L+9))%3,by omega⟩).toNat

def install (a : Array BabyBear) (offset bits : Nat) (values : Array Nat) : Array BabyBear := Id.run do
  let mut a := a
  for i in [:values.size] do
    a := a.set! (offset+i) (values[i]! : BabyBear)
    for j in [:bits] do a := a.set! (offset+values.size+bits*i+j) (digit 2 values[i]! j : BabyBear)
  return a

structure SideCache where
  constant : Nat
  coefficients : Array Nat
  constantDigits : Array Nat
  columnCoefficients : Array (Array (Nat × Nat))
  deriving Inhabited

def sideCache (p : Layout) (c : Nat) (matrix : Fin p.groups → Nat) : SideCache := Id.run do
  let cs := Array.ofFn (digitCoefficient p matrix)
  let columns := (List.range p.width).toArray.map fun column => Id.run do
    let mut sparse := #[]
    for i in [:cs.size] do
      let d := digit p.base cs[i]! column
      if d != 0 then sparse := sparse.push (i,d)
    return sparse
  return ⟨c,cs,(List.range p.width).toArray.map (digit p.base c),columns⟩

def caches (p : Layout) (rows : Fin p.rows → Row p.groups) : Array (SideCache × SideCache) :=
  Array.ofFn fun i => (sideCache p (leftConstant (rows i)) (leftCoefficient (rows i)),
    sideCache p (rightConstant (rows i)) (rightCoefficient (rows i)))

def carries (base : Nat) (c : SideCache) (ds : Array Nat) : Array Nat := Id.run do
  let mut carry := 0
  let mut out := #[0]
  for col in [:c.columnCoefficients.size] do
    let mut mass := c.constantDigits[col]!+carry
    for (i,d) in c.columnCoefficients[col]! do mass := mass+d*ds[i]!
    carry := mass/base
    out := out.push carry
  return out

def matrixWitness (p : Layout) (cache : Array (SideCache × SideCache)) (x : Fin p.groups → Nat) : Array BabyBear := Id.run do
  let ds := Array.ofFn fun i : Fin p.scalars => digit p.base (x (groupDigit p|>.symm i).1) (groupDigit p|>.symm i).2.val
  let mut a := install (Array.replicate p.nVars 0) 0 p.limbBits ds
  for row in List.finRange p.rows do
    let (l,r) := cache[row.val]!
    let mut total := l.constant
    for i in [:ds.size] do total := total+l.coefficients[i]!*ds[i]!
    a := install a (resultStart p row) p.limbBits ((List.range p.width).toArray.map (digit p.base total))
    a := install a (resultStart p row+p.width*(1+p.limbBits)) p.carryBits (carries p.base l ds)
    a := install a (resultStart p row+p.width*(1+p.limbBits)+(p.width+1)*(1+p.carryBits)) p.carryBits (carries p.base r ds)
  return a

end Minidregg.Compiler.DirectedRnsWitness
