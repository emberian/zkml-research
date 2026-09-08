/- Public-input-only witness synthesis for the compiler's joined query relation. -/
import Compiler.BfvQueryRow
namespace Minidregg.Compiler.BfvQueryRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def digit (v i : Nat) : Nat := v/64^i%64
def bit (v i : Nat) : Nat := v/2^i%2
def readWord (row : Array Nat) (g l : Nat) : Nat :=
  (List.range 7).foldr (fun i acc => row[1+14*g+7*l+i]!+64*acc) 0

def setBits (a : Array BabyBear) (offset bits value : Nat) : Array BabyBear := Id.run do
  let mut a := a
  for j in [:bits] do a := a.set! (offset+j) (bit value j : BabyBear)
  return a

def productColumn (a b t : Nat) : Nat :=
  ((List.range 7).flatMap fun i => (List.range 7).map fun j =>
    if i+j=t then digit a i*digit b j else 0).sum

/-- The producer computes internal products and quotients from A and the public
encoded plaintexts. It copies the supplied answer unchanged. Thus an incorrect
answer cannot be repaired by choosing private product intermediates. -/
def variableArray (row : Array Nat) : Array BabyBear := Id.run do
  let mut a := Array.replicate nVars (0 : BabyBear)
  for i in [:57] do a := a.set! i (row[i]! : BabyBear)
  for l in List.finRange 2 do
    let q := primes l
    let s := start l
    let av := readWord row 0 l.val
    let pp := readWord row 1 l.val
    let pm := readWord row 2 l.val
    let out := readWord row 3 l.val
    let u := av*pp%q
    let v := av*pm%q
    let values := #[av,pp,pm,out,u,v,0]
    for g in [:7] do
      let value := values[g]!
      let slack := q-1-value
      let t := s+21+99*g
      let mut c : Nat := 0
      for i in [:7] do
        if 4 ≤ g then a := a.set! (s+7*(g-4)+i) (digit value i : BabyBear)
        a := setBits a (t+6*i) 6 (digit value i)
        a := a.set! (t+42+i) (digit slack i : BabyBear)
        a := setBits a (t+49+6*i) 6 (digit slack i)
        a := a.set! (t+91+i) (c : BabyBear)
        c := (digit value i+digit slack i+c)/64
      a := a.set! (t+98) (c : BabyBear)
    for i in [:7] do
      a := a.set! (s+714+i) (digit (q-1) i : BabyBear)
      a := setBits a (s+721+6*i) 6 (digit (q-1) i)
    for sign in [:2] do
      let b := values[1+sign]!
      let prod := values[4+sign]!
      let quotient := av*b/q
      let t := s+763+214*sign
      for i in [:7] do
        a := a.set! (t+i) (digit quotient i : BabyBear)
        a := setBits a (t+7+6*i) 6 (digit quotient i)
      let mut c : Int := 0
      for i in [:15] do
        let encoded := (c+512).toNat
        a := a.set! (t+49+i) (encoded : BabyBear)
        a := setBits a (t+64+10*i) 10 encoded
        if i<14 then c := ((productColumn av b i : Int)+c-
          (productColumn q quotient i : Int)-(digit prod i : Int))/64
    let quotient := (u+q-v)/q
    a := a.set! (s+1191) (quotient : BabyBear)
    a := setBits a (s+1192) 2 quotient
    let mut c : Int := 0
    for i in [:8] do
      let encoded := (c+4).toNat
      a := a.set! (s+1194+i) (encoded : BabyBear)
      a := setBits a (s+1202+3*i) 3 encoded
      if i<7 then c := ((digit u i : Int)+(digit q i : Int)+c-
        (digit v i : Int)-(digit out i : Int)-(digit q i : Int)*quotient)/64
  return a

def rowOfValues (rowID : Nat) (a plus minus out : Fin 2 → Nat) : Array Nat :=
  #[rowID] ++ ((List.finRange 4).flatMap fun g => (List.finRange 2).flatMap fun l =>
    (List.range 7).map fun i => digit ((![a,plus,minus,out] : Fin 4 → Fin 2 → Nat) g l) i).toArray

def sourceCheck (row : Array Nat) : Bool :=
  let a := variableArray row
  emittedSystem.all (fun t => eval (fun i => a[i.val]!) t==0)
end Minidregg.Compiler.BfvQueryRow
