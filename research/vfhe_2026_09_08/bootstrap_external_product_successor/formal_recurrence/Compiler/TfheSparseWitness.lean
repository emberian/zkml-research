import Compiler.TfheSparseRow
namespace Minidregg.Compiler.TfheSparseRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
set_option autoImplicit false

def variableArray (row : Array Nat) : Array BabyBear := Id.run do
  let mut a := Array.replicate nVars (0 : BabyBear)
  for i in [:46] do a := a.set! i (row[i]! : BabyBear)
  for g in [:8] do
    for i in [:4] do
      for j in [:6] do a := a.set! (46+24*g+6*i+j) ((row[8+4*g+i]!/2^j%2 : Nat) : BabyBear)
  for k in [:2] do
    let mut c : Int := 0
    for i in [:5] do
      let enc := (c+4).toNat
      a := a.set! (238+20*k+i) (enc : BabyBear)
      for j in [:3] do a := a.set! (243+20*k+3*i+j) ((enc/2^j%2 : Nat) : BabyBear)
      if i<4 then
        let lhs := if k=0 then row[28+i]!+row[6]!*row[8+i]!
          else row[24+i]!+2*row[4]!*row[12+i]!+2*row[5]!*row[16+i]!
        let rhs := if k=0 then row[32+i]!+row[7]!*row[8+i]!
          else row[20+i]!+row[12+i]!+row[16+i]!
        c := ((lhs : Int)+c-(rhs : Int))/64
  return a

def sourceCheck (row : Array Nat) : Bool :=
  let a := variableArray row
  emittedSystem.all (fun t => eval (fun i => a[i.val]!) t==0)
end Minidregg.Compiler.TfheSparseRow
