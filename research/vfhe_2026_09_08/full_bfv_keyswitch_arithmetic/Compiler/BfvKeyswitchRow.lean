import Compiler.BfvKeyswitchCore
import Compiler.AirAssertionShare
namespace Minidregg.Compiler.BfvKeyswitchRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
local instance : Hashable BabyBear where hash x := hash x.val

def primes : Fin 4 → Nat := ![1125899906826241,1125899906629633,1125899905744897,1125899905351681]
def nVars : Nat := 2655

def group (g : Fin 16) : AirBignum.AddWires (Fin nVars) 6 9 where
  x := fun i => ⟨1+6*g.val+i.val,by dsimp [nVars]; omega⟩
  xBit := fun i j => ⟨97+121*g.val+9*i.val+j.val,by dsimp [nVars]; omega⟩
  y := fun i => ⟨97+121*g.val+54+i.val,by dsimp [nVars]; omega⟩
  yBit := fun i j => ⟨97+121*g.val+60+9*i.val+j.val,by dsimp [nVars]; omega⟩
  carry := fun i => ⟨97+121*g.val+114+i.val,by dsimp [nVars]; omega⟩
  z := fun i => ⟨2033+i.val,by dsimp [nVars]; omega⟩
  zBit := fun i j => ⟨2039+9*i.val+j.val,by dsimp [nVars]; omega⟩
def wires : BfvKeyswitchCore.Wires (Fin nVars) where
  canonical := group
  quotient := fun h i => ⟨2093+281*h.val+i.val,by dsimp [nVars]; omega⟩
  quotientBit := fun h i j => ⟨2093+281*h.val+6+9*i.val+j.val,by dsimp [nVars]; omega⟩
  carry := fun h i => ⟨2093+281*h.val+60+i.val,by dsimp [nVars]; omega⟩
  carryBit := fun h i j => ⟨2093+281*h.val+73+16*i.val+j.val,by dsimp [nVars]; omega⟩
def macWires (h : Fin 2) := BfvKeyswitchCore.macWires wires h
def system (q : Nat) := BfvKeyswitchCore.system q wires
def value (asg : Fin nVars → BabyBear) (g : Fin 16) := BfvKeyswitchCore.value asg wires g

def WholeRowSound (q : Nat) : Prop := BfvKeyswitchCore.Sound q wires

theorem prime_capacity (l : Fin 4) : 0<primes l ∧ 5*primes l<512^6 := by
  fin_cases l <;> norm_num [primes]
theorem wholeRowSound (q : Nat) (hq : 0<q) (hcap : q<512^6) : WholeRowSound q :=
  BfvKeyswitchCore.sound q hq hcap wires

def emittedSystem (q : Nat) := AirAssertionShare.optimize (system q)
theorem emittedSystem_sound (l : Fin 4) (asg : Fin nVars → BabyBear)
    (h : systemAccepts asg (emittedSystem (primes l))) :
    (∀ g,value asg g<primes l) ∧ ∀ h,value asg (BfvKeyswitchCore.oIndex h)=
      (value asg (BfvKeyswitchCore.aIndex h)+∑ k : Fin 4,
        value asg (BfvKeyswitchCore.dIndex k)*value asg (BfvKeyswitchCore.kIndex h k))%primes l := by
  apply wholeRowSound (primes l) (prime_capacity l).1 (by have := (prime_capacity l).2; omega) asg
  exact (AirAssertionShare.optimize_preserves asg (system (primes l))).mp h
end Minidregg.Compiler.BfvKeyswitchRow
