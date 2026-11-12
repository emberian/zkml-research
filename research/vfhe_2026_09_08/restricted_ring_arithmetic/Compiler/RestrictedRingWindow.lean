import Compiler.AirWindowUpdate
import Compiler.AirAssertionShare

namespace Minidregg.Compiler.RestrictedRingWindow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

local instance : Hashable BabyBear where hash x := hash x.val

def modulus : Nat := 497323290947860672931310292648754779192460749687510494957169639477681564739617435942913
def radix : Nat := 134217728
def limbCount : Nat := 11
def publicWidth : Nat := 45
def nVars : Nat := 2872

/-- One complete 297-bit coefficient per row; all four words are public.
The q−1 word and its bits are shared between the four canonicality gadgets. -/
def layout : AirWindowUpdate.RowWires (Fin nVars) 11 where
  canonical := fun kind => {
    x := fun i => ⟨1+11*kind.val+i.val,by dsimp [nVars]; omega⟩
    y := fun i => ⟨1233+11*kind.val+i.val,by dsimp [nVars]; omega⟩
    z := fun i => ⟨2465+i.val,by dsimp [nVars]; omega⟩
    xBit := fun i j => ⟨45+297*kind.val+27*i.val+j.val,by dsimp [nVars]; omega⟩
    yBit := fun i j => ⟨1277+297*kind.val+27*i.val+j.val,by dsimp [nVars]; omega⟩
    zBit := fun i j => ⟨2476+27*i.val+j.val,by dsimp [nVars]; omega⟩
    carry := fun i => ⟨2773+12*kind.val+i.val,by dsimp [nVars]; omega⟩ }
  quotient := ⟨2821,by decide⟩
  quotientBit := fun j => ⟨2822+j.val,by dsimp [nVars]; omega⟩
  carry := fun i => ⟨2824+i.val,by dsimp [nVars]; omega⟩
  carryBit := fun i j => ⟨2836+3*i.val+j.val,by dsimp [nVars]; omega⟩

def system : ConstraintSystem BabyBear (Fin nVars) := AirWindowUpdate.rowSystem modulus layout
def emittedSystem : ConstraintSystem BabyBear (Fin nVars) := AirAssertionShare.optimize system
def word (asg : Fin nVars → BabyBear) (kind : Fin 4) : Nat := AirWindowUpdate.word asg layout kind

/-- The public words are canonical and the result is the exact modular update.
No carry, range, canonicality or arithmetic identity is a caller premise. -/
def WholeRowSound : Prop := ∀ asg : Fin nVars → BabyBear,
  systemAccepts asg emittedSystem → (∀ kind,word asg kind < modulus) ∧
    word asg 3 = (word asg 0+word asg 1+modulus-word asg 2)%modulus

theorem modulus_capacity : 0 < modulus ∧ modulus < 134217728^11 := by norm_num [modulus]

theorem capacity_and_public_width : 2^289 ≤ 134217728^11 ∧ publicWidth ≤ 64 := by
  decide +kernel

theorem no_field_wrap : 12*radix+4 < babyBearP := by norm_num [radix,babyBearP]

theorem wholeRowSound : WholeRowSound := by
  intro asg hs
  exact AirWindowUpdate.rowSystem_sound modulus modulus_capacity.1 modulus_capacity.2 layout asg
    ((AirAssertionShare.optimize_preserves asg system).mp hs)

theorem all_public_limbs (asg : Fin nVars → BabyBear) (kind : Fin 4) :
    word asg kind = Bignum.denoteNat radix
      (List.ofFn fun i : Fin 11 => (asg ⟨1+11*kind.val+i.val,by dsimp [nVars]; omega⟩).val) := rfl

/-- The ordinary compiler descriptor forces the same relation as the ordered IR2 fold. -/
theorem descriptor_sound (v : Nat → BabyBear)
    (h : descriptorHolds (AirAssertionShare.emitShared Fin.val publicWidth nVars system) v) :
    (∀ kind,word (fun i => v i.val) kind < modulus) ∧
      word (fun i => v i.val) 3 =
        (word (fun i => v i.val) 0+word (fun i => v i.val) 1+modulus-
          word (fun i => v i.val) 2)%modulus := by
  exact AirWindowUpdate.rowSystem_sound modulus modulus_capacity.1 modulus_capacity.2 layout _
    (AirAssertionShare.emitShared_forces Fin.val publicWidth nVars system v h)

def digit (value index : Nat) : Nat := value / radix^index % radix
def bit (value index : Nat) : Nat := value / 2^index % 2
def readWord (row : Array Nat) (kind : Nat) : Nat :=
  (List.range 11).foldr (fun i acc => row[1+11*kind+i]!+radix*acc) 0
def setBits (a : Array BabyBear) (offset bits value : Nat) : Array BabyBear := Id.run do
  let mut a := a
  for j in [:bits] do a := a.set! (offset+j) (bit value j : BabyBear)
  return a

/-- Untrusted witness synthesis retains every supplied public output digit. -/
def variableArray (row : Array Nat) : Array BabyBear := Id.run do
  let mut a : Array BabyBear := Array.replicate nVars 0
  for i in [:45] do a := a.set! i (row[i]! : BabyBear)
  for kind in [:4] do
    let value := readWord row kind
    let slack := modulus-1-value
    let mut carry : Nat := 0
    for i in [:11] do
      a := setBits a (45+297*kind+27*i) 27 (digit value i)
      a := a.set! (1233+11*kind+i) (digit slack i : BabyBear)
      a := setBits a (1277+297*kind+27*i) 27 (digit slack i)
      a := a.set! (2773+12*kind+i) (carry : BabyBear)
      carry := (digit value i+digit slack i+carry)/radix
    a := a.set! (2773+12*kind+11) (carry : BabyBear)
  for i in [:11] do
    a := a.set! (2465+i) (digit (modulus-1) i : BabyBear)
    a := setBits a (2476+27*i) 27 (digit (modulus-1) i)
  let av := readWord row 0
  let fresh := readWord row 1
  let old := readWord row 2
  let out := readWord row 3
  let k := (av+fresh+modulus-old)/modulus
  a := a.set! 2821 (k : BabyBear)
  a := setBits a 2822 2 k
  let mut carry : Int := 0
  for i in [:12] do
    let encoded := (carry+4).toNat
    a := a.set! (2824+i) (encoded : BabyBear)
    a := setBits a (2836+3*i) 3 encoded
    if i < 11 then
      carry := ((digit av i : Int)+(digit fresh i : Int)+(digit modulus i : Int)+carry-
        (digit old i : Int)-(digit out i : Int)-(digit modulus i : Int)*k)/radix
  return a

def rowOfValues (rowId av fresh old out : Nat) : Array Nat :=
  #[rowId] ++ (([av,fresh,old,out].flatMap fun v => (List.range 11).map (digit v))).toArray

def sourceCheck (row : Array Nat) : Bool :=
  let a := variableArray row
  system.all (fun term => eval (fun i => a[i.val]!) term == 0)

/-- info: 'Minidregg.Compiler.RestrictedRingWindow.modulus_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modulus_capacity
/-- info: 'Minidregg.Compiler.RestrictedRingWindow.capacity_and_public_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms capacity_and_public_width
/-- info: 'Minidregg.Compiler.RestrictedRingWindow.no_field_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_field_wrap
/-- info: 'Minidregg.Compiler.RestrictedRingWindow.wholeRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wholeRowSound
/-- info: 'Minidregg.Compiler.RestrictedRingWindow.all_public_limbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms all_public_limbs
/-- info: 'Minidregg.Compiler.RestrictedRingWindow.descriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descriptor_sound

end Minidregg.Compiler.RestrictedRingWindow
