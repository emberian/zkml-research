import Compiler.BfvLinearCombination
import Compiler.AirSimplify

namespace Minidregg.Compiler.BfvLinearCombination
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.AirSimplify
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

local instance : Hashable BabyBear where hash x := hash x.val

def primes : Fin 3 → Nat := ![68719403009,68719230977,137438822401]
def nVars : Nat := 1234
def start (limb : Fin 3) : Nat := 64+390*limb.val

def layout (limb : Fin 3) : RowWires (Fin nVars) where
  canonical := fun kind => {
    x := fun i => ⟨1+21*kind.val+7*limb.val+i.val,by dsimp [nVars]; omega⟩
    y := fun i => ⟨start limb+126+7*kind.val+i.val,by dsimp [start,nVars]; omega⟩
    z := fun i => ⟨start limb+273+i.val,by dsimp [start,nVars]; omega⟩
    xBit := fun i j => ⟨start limb+42*kind.val+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
    yBit := fun i j => ⟨start limb+147+42*kind.val+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
    zBit := fun i j => ⟨start limb+280+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
    carry := fun i => ⟨start limb+322+8*kind.val+i.val,by dsimp [start,nVars]; omega⟩ }
  quotient := ⟨start limb+346,by dsimp [start,nVars]; omega⟩
  quotientBit := fun j => ⟨start limb+347+j.val,by dsimp [start,nVars]; omega⟩
  carry := fun i => ⟨start limb+350+i.val,by dsimp [start,nVars]; omega⟩
  carryBit := fun i j => ⟨start limb+358+4*i.val+j.val,by dsimp [start,nVars]; omega⟩

def system : ConstraintSystem BabyBear (Fin nVars) :=
  (List.finRange 3).flatMap fun limb => rowSystem (primes limb) (layout limb)

def descriptor : ConstraintDescriptor BabyBear := cse (emitSimplified Fin.val 64 nVars system)

/-- One shared row contains A, B and O for all three limbs. -/
def WholeRowSound : Prop := ∀ asg : Fin nVars → BabyBear, systemAccepts asg system →
  ∀ limb, (∀ kind,word asg (layout limb) kind < primes limb) ∧
    word asg (layout limb) 2 =
      (3*word asg (layout limb) 0+5*word asg (layout limb) 1)%primes limb

theorem prime_capacity (limb : Fin 3) : 0 < primes limb ∧ primes limb < 64^7 := by
  fin_cases limb <;> norm_num [primes]

theorem wholeRowSound : WholeRowSound := by
  intro asg hs limb
  apply rowSystem_sound (primes limb) (prime_capacity limb).1 (prime_capacity limb).2
  intro term ht
  exact hs term (List.mem_flatMap.mpr ⟨limb,List.mem_finRange limb,ht⟩)

theorem descriptor_sound (v : Nat → BabyBear) (h : descriptorHolds descriptor v) :
    ∀ limb, (∀ kind,word (fun i => v i.val) (layout limb) kind < primes limb) ∧
      word (fun i => v i.val) (layout limb) 2 =
        (3*word (fun i => v i.val) (layout limb) 0+
          5*word (fun i => v i.val) (layout limb) 1)%primes limb := by
  have hs := (cse_emitSimplified_accepts_iff Fin.val Fin.val_injective 64 nVars
    (fun i : Fin nVars => i.isLt) (fun i => v i.val) system).mp ⟨v,fun _ => rfl,h⟩
  exact wholeRowSound _ hs

/-- The IR2 serializer folds exactly this simplified source system. -/
theorem simplifiedSource_sound (asg : Fin nVars → BabyBear)
    (h : systemAccepts asg (simplifySystem system)) :
    ∀ limb, (∀ kind,word asg (layout limb) kind < primes limb) ∧
      word asg (layout limb) 2 =
      (3*word asg (layout limb) 0+5*word asg (layout limb) 1)%primes limb := by
  exact wholeRowSound asg ((simplifySystem_accepts_iff asg system).mp h)

def digit (value index : Nat) : Nat := value / 64^index % 64
def bit (value index : Nat) : Nat := value / 2^index % 2

def readWord (row : Array Nat) (kind limb : Nat) : Nat :=
  (List.range 7).foldr (fun i acc => row[1+21*kind+7*limb+i]!+64*acc) 0

def setBits (a : Array BabyBear) (offset bits value : Nat) : Array BabyBear := Id.run do
  let mut a := a
  for j in [:bits] do a := a.set! (offset+j) (bit value j : BabyBear)
  return a

/-- Witness synthesis is in the same Lean package as the generated relation.
The caller supplies actual public A/B/O digits; the producer does not choose O. -/
def variableArray (row : Array Nat) : Array BabyBear := Id.run do
  let mut a : Array BabyBear := Array.replicate nVars 0
  for i in [:64] do a := a.set! i (row[i]! : BabyBear)
  for limb in List.finRange 3 do
    let q := primes limb
    let s := start limb
    for kind in [:3] do
      let value := readWord row kind limb.val
      let slack := q-1-value
      let mut carry : Nat := 0
      for i in [:7] do
        a := setBits a (s+42*kind+6*i) 6 (digit value i)
        a := a.set! (s+126+7*kind+i) (digit slack i : BabyBear)
        a := setBits a (s+147+42*kind+6*i) 6 (digit slack i)
        a := a.set! (s+322+8*kind+i) (carry : BabyBear)
        carry := (digit value i+digit slack i+carry)/64
      a := a.set! (s+322+8*kind+7) (carry : BabyBear)
    for i in [:7] do
      a := a.set! (s+273+i) (digit (q-1) i : BabyBear)
      a := setBits a (s+280+6*i) 6 (digit (q-1) i)
    let av := readWord row 0 limb.val
    let bv := readWord row 1 limb.val
    let ov := readWord row 2 limb.val
    let k := (3*av+5*bv)/q
    a := a.set! (s+346) (k : BabyBear)
    a := setBits a (s+347) 3 k
    let mut carry : Int := 0
    for i in [:8] do
      let encoded := (carry+8).toNat
      a := a.set! (s+350+i) (encoded : BabyBear)
      a := setBits a (s+358+4*i) 4 encoded
      if i < 7 then
        carry := (3*(digit av i : Int)+5*(digit bv i : Int)+carry-
          (digit ov i : Int)-(digit q i : Int)*k)/64
  return a

def rowOfValues (rowId : Nat) (av bv ov : Fin 3 → Nat) : Array Nat :=
  #[rowId] ++ ((List.finRange 3).flatMap fun kind =>
    (List.finRange 3).flatMap fun limb =>
      (List.range 7).map fun i => digit ((![av,bv,ov] : Fin 3 → Fin 3 → Nat) kind limb) i).toArray

def sourceCheck (row : Array Nat) : Bool :=
  let a := variableArray row
  system.all (fun term => eval (fun i => a[i.val]!) term == 0)


/-- info: 'Minidregg.Compiler.BfvLinearCombination.prime_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_capacity

/-- info: 'Minidregg.Compiler.BfvLinearCombination.wholeRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wholeRowSound

/-- info: 'Minidregg.Compiler.BfvLinearCombination.descriptor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descriptor_sound

/-- info: 'Minidregg.Compiler.BfvLinearCombination.simplifiedSource_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms simplifiedSource_sound

end Minidregg.Compiler.BfvLinearCombination
