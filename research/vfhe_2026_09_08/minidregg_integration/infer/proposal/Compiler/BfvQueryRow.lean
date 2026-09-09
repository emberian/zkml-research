/- Exact source composition for host-infer's two products and final subtraction.
Intermediate products are shared wires, not externally supplied arithmetic premises. -/
import Compiler.BfvQueryMul
import Compiler.BfvExpiryLayout
import Compiler.AirAssertionShare
namespace Minidregg.Compiler.BfvQueryRow
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.AirSimplify Minidregg.Compiler.DescriptorEval
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
local instance : Hashable BabyBear where hash x := hash x.val

def primes : Fin 2 → Nat := ![2199023190017,4398046486529]
def nVars : Nat := 2509
def start (l : Fin 2) : Nat := 57+1226*l.val

def group (l : Fin 2) (g : Fin 7) : AirBignum.AddWires (Fin nVars) 7 6 where
  x := fun i => if h : g.val<4 then
    ⟨1+14*g.val+7*l.val+i.val,by dsimp [nVars]; omega⟩
    else ⟨start l+7*(g.val-4)+i.val,by dsimp [start,nVars]; omega⟩
  y := fun i => ⟨start l+21+99*g.val+42+i.val,by dsimp [start,nVars]; omega⟩
  z := fun i => ⟨start l+714+i.val,by dsimp [start,nVars]; omega⟩
  xBit := fun i j => ⟨start l+21+99*g.val+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
  yBit := fun i j => ⟨start l+21+99*g.val+49+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
  zBit := fun i j => ⟨start l+721+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
  carry := fun i => ⟨start l+21+99*g.val+91+i.val,by dsimp [start,nVars]; omega⟩

def mulWires (l : Fin 2) (sign : Fin 2) : BfvQueryMul.RowWires (Fin nVars) where
  canonical := ![group l 0,group l ⟨1+sign.val,by omega⟩,group l ⟨4+sign.val,by omega⟩]
  quotient := fun i => ⟨start l+763+214*sign.val+i.val,by dsimp [start,nVars]; omega⟩
  quotientBit := fun i j => ⟨start l+763+214*sign.val+7+6*i.val+j.val,by dsimp [start,nVars]; omega⟩
  carry := fun i => ⟨start l+763+214*sign.val+49+i.val,by dsimp [start,nVars]; omega⟩
  carryBit := fun i j => ⟨start l+763+214*sign.val+64+10*i.val+j.val,by dsimp [start,nVars]; omega⟩

def subWires (l : Fin 2) : BfvExpiry.RowWires (Fin nVars) where
  canonical := ![group l 4,group l 6,group l 5,group l 3]
  quotient := ⟨start l+1191,by dsimp [start,nVars]; omega⟩
  quotientBit := fun j => ⟨start l+1192+j.val,by dsimp [start,nVars]; omega⟩
  carry := fun i => ⟨start l+1194+i.val,by dsimp [start,nVars]; omega⟩
  carryBit := fun i j => ⟨start l+1202+3*i.val+j.val,by dsimp [start,nVars]; omega⟩

def limbSystem (l : Fin 2) : ConstraintSystem BabyBear (Fin nVars) :=
  BfvQueryMul.rowSystem (primes l) (mulWires l 0) ++
  BfvQueryMul.rowSystem (primes l) (mulWires l 1) ++
  BfvExpiry.rowSystem (primes l) (subWires l) ++
  (List.finRange 7).map (fun i => vr ((group l 6).x i))
def system : ConstraintSystem BabyBear (Fin nVars) :=
  (List.finRange 2).flatMap limbSystem

def value (asg : Fin nVars → BabyBear) (l : Fin 2) (g : Fin 7) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (group l g).x)

/-- Exactly the serialized NTT arithmetic performed by host-infer. Query parsing,
plaintext encoding and the correspondence of this row to a committed ciphertext
are public reader obligations; no decryption, NTT theorem or key assertion is hidden here. -/
def WholeRowSound : Prop := ∀ asg : Fin nVars → BabyBear, systemAccepts asg system →
  ∀ l, (∀ g : Fin 4,value asg l (g.castLE (by decide)) < primes l) ∧
    value asg l 3 = ((value asg l 0*value asg l 1)%primes l+primes l-
      (value asg l 0*value asg l 2)%primes l)%primes l

theorem prime_capacity (l : Fin 2) : 0<primes l ∧ primes l<64^7 := by
  fin_cases l <;> norm_num [primes]

theorem wholeRowSound : WholeRowSound := by
  intro asg hs l
  have hl : systemAccepts asg (limbSystem l) := by
    intro t ht
    exact hs t (List.mem_flatMap.mpr ⟨l,List.mem_finRange l,ht⟩)
  simp only [limbSystem,systemAccepts_append] at hl
  obtain ⟨⟨⟨hplus,hminus⟩,hsub⟩,hz⟩ := hl
  have hp := BfvQueryMul.rowSystem_sound (primes l) (prime_capacity l).1 (prime_capacity l).2 (mulWires l 0) asg hplus
  have hm := BfvQueryMul.rowSystem_sound (primes l) (prime_capacity l).1 (prime_capacity l).2 (mulWires l 1) asg hminus
  have hsub := BfvExpiry.rowSystem_sound (primes l) (prime_capacity l).1 (prime_capacity l).2 (subWires l) asg hsub
  have hz' : ∀ i,asg ((group l 6).x i)=0 := by
    intro i
    exact hz _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
  have hzval : value asg l 6=0 := by simp [value,AirBignum.limbVals,hz']
  have hpe : value asg l 4=(value asg l 0*value asg l 1)%primes l := hp.2
  have hme : value asg l 5=(value asg l 0*value asg l 2)%primes l := hm.2
  have hse : value asg l 3=(value asg l 4+value asg l 6+primes l-value asg l 5)%primes l := hsub.2
  refine ⟨?_,?_⟩
  · intro g
    fin_cases g
    · exact hp.1 0
    · exact hp.1 1
    · exact hm.1 1
    · exact hsub.1 3
  · simpa [hzval,hpe,hme] using hse

/-- The same generic assertion-sharing pass removes repeated canonical ranges
introduced by the source composition. It does not add or replace equations. -/
def emittedSystem : ConstraintSystem BabyBear (Fin nVars) :=
  AirAssertionShare.optimize system

theorem emittedSystem_sound (asg : Fin nVars → BabyBear)
    (h : systemAccepts asg emittedSystem) :
    ∀ l, (∀ g : Fin 4,value asg l (g.castLE (by decide)) < primes l) ∧
    value asg l 3=((value asg l 0*value asg l 1)%primes l+primes l-
      (value asg l 0*value asg l 2)%primes l)%primes l := by
  apply wholeRowSound asg
  exact (AirAssertionShare.optimize_preserves asg system).mp h
end Minidregg.Compiler.BfvQueryRow

/-- info: 'Minidregg.Compiler.BfvQueryRow.prime_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryRow.prime_capacity

/-- info: 'Minidregg.Compiler.BfvQueryRow.wholeRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryRow.wholeRowSound

/-- info: 'Minidregg.Compiler.BfvQueryRow.emittedSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvQueryRow.emittedSystem_sound
