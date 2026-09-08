/- Witness generation reuses the existing nonnegative matrices. A single
parameterized producer installs their radix digits and computes their two carry
chains; it does not contain the downscaler's arithmetic formula or constraints. -/
import Compiler.BfvRescaleRow
import Compiler.FheSourceCertificateWitness

namespace Minidregg.Compiler.BfvRescaleRow
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def digit (base value index : Nat) : Nat := value/base^index%base

def installGroup (a : Array BabyBear) (offset bits : Nat) (values : Array Nat) : Array BabyBear := Id.run do
  let mut a := a
  for i in [:values.size] do
    a := a.set! (offset+i) (values[i]! : BabyBear)
    for j in [:bits] do
      a := a.set! (offset+values.size+bits*i+j) (digit 2 values[i]! j : BabyBear)
  return a

def cachedCarries (width c : Nat) (coeff ds : Array Nat) : Array Nat := Id.run do
  let mut carry : Nat := 0
  let mut result := #[0]
  for column in [:width] do
    let mut mass : Nat := digit 64 c column+carry
    for j in [:ds.size] do mass := mass+digit 64 coeff[j]! column*ds[j]!
    carry := mass/64
    result := result.push carry
  return result

/-- The source matrices and their layout determine both emitted equations and
this witness traversal. Source/target use the same producer with different dimensions. -/
def matrixWitness (groups digits rows width carryBits variableCount : Nat)
    (leftConstant rightConstant : Fin rows → Nat)
    (leftMatrix rightMatrix : Fin rows → Fin groups → Nat)
    (resultStart : Fin rows → Nat) (values : Fin groups → Nat) : Array BabyBear := Id.run do
  let gd : Fin groups × Fin digits ≃ Fin (groups*digits) := finProdFinEquiv
  let ds := Array.ofFn fun i : Fin (groups*digits) =>
    digit 64 (values (gd.symm i).1) (gd.symm i).2.val
  let mut a := installGroup (Array.replicate variableCount 0) 0 6 ds
  for row in List.finRange rows do
    let l := Array.ofFn fun i : Fin (groups*digits) => leftMatrix row (gd.symm i).1*64^(gd.symm i).2.val
    let r := Array.ofFn fun i : Fin (groups*digits) => rightMatrix row (gd.symm i).1*64^(gd.symm i).2.val
    let mut total : Nat := leftConstant row
    for j in [:ds.size] do total := total+l[j]!*ds[j]!
    a := installGroup a (resultStart row) 6 ((List.range width).toArray.map (digit 64 total))
    a := installGroup a (resultStart row+7*width) carryBits (cachedCarries width (leftConstant row) l ds)
    a := installGroup a (resultStart row+7*width+(width+1)*(carryBits+1)) carryBits
      (cachedCarries width (rightConstant row) r ds)
  return a

def sourceWitness (r : Fin 6 → Int) : Array BabyBear := matrixWitness 21 22 12 57 15 30294
  FheSourceCertificate.leftConstant FheSourceCertificate.rightConstant FheSourceCertificate.leftMatrix FheSourceCertificate.rightMatrix FheSourceCertificate.resultStart (FheSourceCertificate.sourceValues r)

def targetWitness (y : Nat) : Array BabyBear := matrixWitness 10 19 6 26 14 7282
  FheTargetProjection.leftConstant FheTargetProjection.rightConstant FheTargetProjection.leftMatrix FheTargetProjection.rightMatrix FheTargetProjection.resultStart (FheTargetProjection.targetValues y)

def readResidues (row : Array Nat) (i : Fin 6) : Int :=
  ((List.range 11).foldr (fun d acc => row[1+11*i.val+d]!+64*acc) 0 : Nat)

/-- Public columns and shared Y are checked before installing aliases: the
producer cannot overwrite the externally supplied actual downscaler outputs. -/
def variableArray (row : Array Nat) : Except String (Array BabyBear) := do
  unless row.size == 88 do throw "wrong public row arity"
  unless row[0]! < babyBearP do throw "row ID exceeds field"
  for j in [1:88] do unless row[j]! < 64 do throw "noncanonical public radix digit"
  let r := readResidues row
  let sa := sourceWitness r
  let y := (FheRnsScale.deployedOutput r%FheRnsScale.deployedQ).toNat
  let ta := targetWitness y
  let mut a : Array BabyBear := Array.replicate nVars 0
  for j in [:88] do a := a.set! j (row[j]! : BabyBear)
  for j in List.finRange 30294 do
    let target := (sourceIx j).val
    let value := sa[j.val]!
    if target < 89 then
      unless a[target]! == value do throw s!"source/public alias mismatch at{target}"
    else a := a.set! target value
  for j in List.finRange 7282 do
    let target := (targetIx j).val
    let value := ta[j.val]!
    if target < 30383 then
      unless a[target]! == value do throw s!"target/public/shared-Y alias mismatch at{target}"
    else a := a.set! target value
  return a

end Minidregg.Compiler.BfvRescaleRow
