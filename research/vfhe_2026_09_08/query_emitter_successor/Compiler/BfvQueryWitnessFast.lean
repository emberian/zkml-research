/- Faster public-input witness scheduling. The proved source relation and layout
are imported byte-identically from the frozen query package. -/
import Compiler.BfvQueryWitness
namespace Minidregg.Compiler.BfvQueryRow.Fast
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

/-- Decompose once by repeated division, instead of recomputing powers and
repeating the same quotient for every consumer. -/
def digits (v : Nat) : Array Nat := Id.run do
  let mut rest := v
  let mut ds := Array.emptyWithCapacity 7
  for _ in [:7] do
    ds := ds.push (rest%64)
    rest := rest/64
  return ds

/-- Accumulate all fourteen columns in one 7×7 pass. The last column remains
zero; the original productColumn recomputed every digit in fourteen scans. -/
def columns (a b : Array Nat) : Array Nat := Id.run do
  let mut cs := Array.replicate 14 0
  for i in [:7] do
    for j in [:7] do
      cs := cs.set! (i+j) (cs[i+j]!+a[i]!*b[j]!)
  return cs

def setBitsFast (a : Array BabyBear) (offset bits value : Nat) : Array BabyBear := Id.run do
  let mut a := a
  let mut rest := value
  for j in [:bits] do
    a := a.set! (offset+j) ((rest%2 : Nat) : BabyBear)
    rest := rest/2
  return a

/-- Same positions and values as the frozen producer, with row-local digit and
convolution caches. The supplied output is still copied unchanged. -/
def variableArrayFast (row : Array Nat) : Array BabyBear := Id.run do
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
    let ds := values.map digits
    let qd := digits q
    let bound := digits (q-1)
    for g in [:7] do
      let value := ds[g]!
      let slack := digits (q-1-values[g]!)
      let t := s+21+99*g
      let mut c : Nat := 0
      for i in [:7] do
        let vd := value[i]!
        let sd := slack[i]!
        if 4 ≤ g then a := a.set! (s+7*(g-4)+i) (vd : BabyBear)
        a := setBitsFast a (t+6*i) 6 vd
        a := a.set! (t+42+i) (sd : BabyBear)
        a := setBitsFast a (t+49+6*i) 6 sd
        a := a.set! (t+91+i) (c : BabyBear)
        c := (vd+sd+c)/64
      a := a.set! (t+98) (c : BabyBear)
    for i in [:7] do
      a := a.set! (s+714+i) (bound[i]! : BabyBear)
      a := setBitsFast a (s+721+6*i) 6 bound[i]!
    for sign in [:2] do
      let quotient := av*values[1+sign]!/q
      let kd := digits quotient
      let ab := columns ds[0]! ds[1+sign]!
      let qk := columns qd kd
      let prod := ds[4+sign]!
      let t := s+763+214*sign
      for i in [:7] do
        a := a.set! (t+i) (kd[i]! : BabyBear)
        a := setBitsFast a (t+7+6*i) 6 kd[i]!
      let mut c : Int := 0
      for i in [:15] do
        let encoded := (c+512).toNat
        a := a.set! (t+49+i) (encoded : BabyBear)
        a := setBitsFast a (t+64+10*i) 10 encoded
        if i<14 then c := ((ab[i]! : Int)+c-(qk[i]! : Int)-(prod.getD i 0 : Int))/64
    let quotient := (u+q-v)/q
    a := a.set! (s+1191) (quotient : BabyBear)
    a := setBitsFast a (s+1192) 2 quotient
    let mut c : Int := 0
    for i in [:8] do
      let encoded := (c+4).toNat
      a := a.set! (s+1194+i) (encoded : BabyBear)
      a := setBitsFast a (s+1202+3*i) 3 encoded
      if i<7 then c := (((ds[4]!)[i]! : Int)+(qd[i]! : Int)+c-
        ((ds[5]!)[i]! : Int)-((ds[3]!)[i]! : Int)-(qd[i]! : Int)*quotient)/64
  return a
end Minidregg.Compiler.BfvQueryRow.Fast
