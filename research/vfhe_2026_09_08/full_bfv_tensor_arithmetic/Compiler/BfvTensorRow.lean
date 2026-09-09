/- One canonical input pair shared by three weighted modular products. -/
import Compiler.BfvTensorCore
import Compiler.AirAssertionShare
namespace Minidregg.Compiler.BfvTensorRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
local instance : Hashable BabyBear where hash x := hash x.val

def primes : Fin 9 → Nat := ![1125899906826241,1125899906629633,1125899905744897,
  1125899905351681,4611686018427322369,4611686018427289601,
  4611686018426454017,4611686018426257409,4611686018425815041]
def nVars : Nat := 2036

def group (g : Fin 5) : AirBignum.AddWires (Fin nVars) 11 6 where
  x := fun i => ⟨1+11*g.val+i.val,by dsimp [nVars]; omega⟩
  xBit := fun i j => ⟨56+155*g.val+6*i.val+j.val,by dsimp [nVars]; omega⟩
  y := fun i => ⟨56+155*g.val+66+i.val,by dsimp [nVars]; omega⟩
  yBit := fun i j => ⟨56+155*g.val+77+6*i.val+j.val,by dsimp [nVars]; omega⟩
  carry := fun i => ⟨56+155*g.val+143+i.val,by dsimp [nVars]; omega⟩
  z := fun i => ⟨831+i.val,by dsimp [nVars]; omega⟩
  zBit := fun i j => ⟨842+6*i.val+j.val,by dsimp [nVars]; omega⟩

def lhs := BfvTensorCore.lhs
def rhs := BfvTensorCore.rhs
def out := BfvTensorCore.out
def factor := BfvTensorCore.factor

def wires : BfvTensorCore.Wires (Fin nVars) where
  canonical := group
  quotient := fun k i => ⟨908+376*k.val+i.val,by dsimp [nVars]; omega⟩
  quotientBit := fun k i j => ⟨908+376*k.val+11+6*i.val+j.val,by dsimp [nVars]; omega⟩
  carry := fun k i => ⟨908+376*k.val+77+i.val,by dsimp [nVars]; omega⟩
  carryBit := fun k i j => ⟨908+376*k.val+100+12*i.val+j.val,by dsimp [nVars]; omega⟩
def mulWires (k : Fin 3) := BfvTensorCore.weightedWires wires k

def system (q : Nat) : ConstraintSystem BabyBear (Fin nVars) :=
  BfvTensorCore.system q wires
def value (asg : Fin nVars → BabyBear) (g : Fin 5) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (group g).x)

/-- Source theorem: every complete public component word is canonical and all
three pointwise tensor products are forced from the same public input pair. -/
def WholeRowSound (q : Nat) : Prop := ∀ asg : Fin nVars → BabyBear,
  systemAccepts asg (system q) →
    (∀ g,value asg g<q) ∧
    value asg 2=(value asg 0*value asg 0)%q ∧
    value asg 3=(2*value asg 0*value asg 1)%q ∧
    value asg 4=(value asg 1*value asg 1)%q

theorem prime_capacity (l : Fin 9) : 0<primes l ∧ 2*primes l<64^11 := by
  fin_cases l <;> norm_num [primes]

theorem wholeRowSound (q : Nat) (hq : 0<q) (hcap : q<64^11) : WholeRowSound q := by
  exact BfvTensorCore.sound q hq hcap wires

def emittedSystem (q : Nat) : ConstraintSystem BabyBear (Fin nVars) :=
  AirAssertionShare.optimize (system q)

theorem emittedSystem_sound (l : Fin 9) (asg : Fin nVars → BabyBear)
    (h : systemAccepts asg (emittedSystem (primes l))) :
    (∀ g,value asg g<primes l) ∧
    value asg 2=(value asg 0*value asg 0)%primes l ∧
    value asg 3=(2*value asg 0*value asg 1)%primes l ∧
    value asg 4=(value asg 1*value asg 1)%primes l := by
  apply wholeRowSound (primes l) (prime_capacity l).1 (by have := (prime_capacity l).2; omega) asg
  exact (AirAssertionShare.optimize_preserves asg (system (primes l))).mp h
end Minidregg.Compiler.BfvTensorRow
