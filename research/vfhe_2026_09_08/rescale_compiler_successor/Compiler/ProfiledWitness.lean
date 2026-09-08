/- The successor changes allocation only. Values, sparse coefficient caches,
radix installation, and carry evaluation are the frozen generic producer. -/
import Compiler.NonlinearRnsProfiled
import Compiler.DirectedRnsWitness

namespace Minidregg.Compiler.ProfiledWitness
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.DirectedRnsWitness
open Minidregg.Compiler.ProfiledMatrix
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def caches (p : Layout) (q : RowLayout p.rows) (rows : Fin p.rows → Row p.groups) : Array (SideCache × SideCache) :=
  Array.ofFn fun i => (sideCache {p with width:=q.width i} (leftConstant (rows i)) (leftCoefficient (rows i)),
    sideCache {p with width:=q.width i} (rightConstant (rows i)) (rightCoefficient (rows i)))

def matrixWitness (p : Layout) (q : RowLayout p.rows) (cache : Array (SideCache × SideCache)) (x : Fin p.groups → Nat) : Array BabyBear := Id.run do
  let ds := Array.ofFn fun i : Fin p.scalars => digit p.base (x (groupDigit p|>.symm i).1) (groupDigit p|>.symm i).2.val
  let mut a := install (Array.replicate (nVars p q) 0) 0 p.limbBits ds
  for row in List.finRange p.rows do
    let (l,r) := cache[row.val]!
    let mut total := l.constant
    for i in [:ds.size] do total := total+l.coefficients[i]!*ds[i]!
    a := install a (resultStart p q row) p.limbBits ((List.range (q.width row)).toArray.map (digit p.base total))
    a := install a (resultStart p q row+q.width row*(1+p.limbBits)) (q.carryBits row) (carries p.base l ds)
    a := install a (resultStart p q row+q.width row*(1+p.limbBits)+(q.width row+1)*(1+q.carryBits row)) (q.carryBits row) (carries p.base r ds)
  return a

open Minidregg.Compiler.NonlinearRnsInstance Minidregg.Compiler.NonlinearRnsProfiled

def variableArray (cache : Array (SideCache × SideCache)) (row : Array Nat) : Except String (Array BabyBear) := do
  unless row.size == 88 do throw "wrong public arity"
  unless row[0]! < babyBearP do throw "row ID outside field"
  for i in [1:88] do unless row[i]!<512 do throw "noncanonical radix512 digit"
  let r := NonlinearRnsPublic.readResidues row
  let x := values params r
  for i in List.finRange 9 do
    unless r i < params.sourceBase i do throw "noncanonical source residue"
  for g in List.finRange 39 do
    unless x g < profile.base^profile.digits do throw "scalar capacity exceeded"
  let inner := matrixWitness profile rowLayout cache x
  let mut a := Array.replicate NonlinearRnsProfiled.nVars (0 : BabyBear)
  for i in [:88] do a := a.set! i (row[i]! : BabyBear)
  for j in [:inner.size] do
    let k := NonlinearRnsPublic.wireMap j
    if k<89 then
      unless a[k]! == inner[j]! do throw s!"public/shared alias mismatch {k}"
    else a := a.set! k inner[j]!
  return a

end Minidregg.Compiler.ProfiledWitness
