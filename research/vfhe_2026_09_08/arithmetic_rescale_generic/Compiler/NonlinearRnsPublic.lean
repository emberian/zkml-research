import Compiler.DirectedRnsWitness
import Compiler.NonlinearRnsInstance

namespace Minidregg.Compiler.NonlinearRnsPublic
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DirectedRnsScaler Minidregg.Compiler.DirectedRnsWitness
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.NonlinearRnsInstance
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def nVars := 89+profile.nVars

def wireMap (j : Nat) : Nat :=
  if j < profile.scalars then
    let g := j/23
    let d := j%23
    if g<9 then if d<7 then 1+7*g+d else 88
    else if 27 ≤ g ∧ g<39 ∧ (g-27)%3=0 then
      if d<6 then 64+6*((g-27)/3)+d else 88
    else 89+j
  else 89+j

def system : ConstraintSystem BabyBear Nat := [vr 88] ++ renameS wireMap source

def readResidues (row : Array Nat) (i : Fin 9) : Int :=
  ((List.range 7).foldr (fun d acc => row[1+7*i.val+d]!+512*acc) 0 : Nat)

def variableArray (cache : Array (SideCache × SideCache)) (row : Array Nat) : Except String (Array BabyBear) := do
  unless row.size == 88 do throw "wrong public arity"
  unless row[0]! < babyBearP do throw "row ID outside field"
  for i in [1:88] do unless row[i]!<512 do throw "noncanonical radix512 digit"
  let r := readResidues row
  let x := values params r
  for i in List.finRange 9 do
    unless r i < params.sourceBase i do throw "noncanonical source residue"
  for g in List.finRange 39 do
    unless x g < profile.base^profile.digits do throw "scalar capacity exceeded"
  let inner := matrixWitness profile cache x
  let mut a := Array.replicate nVars (0 : BabyBear)
  for i in [:88] do a := a.set! i (row[i]! : BabyBear)
  for j in [:inner.size] do
    let k := wireMap j
    if k<89 then
      unless a[k]! == inner[j]! do throw s!"public/shared alias mismatch {k}"
    else a := a.set! k inner[j]!
  return a

end Minidregg.Compiler.NonlinearRnsPublic
