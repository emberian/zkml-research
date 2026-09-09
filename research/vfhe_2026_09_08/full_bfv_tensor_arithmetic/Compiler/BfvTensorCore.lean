/- Generic source composition shares two canonical inputs across all products. -/
import Compiler.BfvTensorMul
namespace Minidregg.Compiler.BfvTensorCore
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def lhs : Fin 3 → Fin 5 := ![0,0,1]
def rhs : Fin 3 → Fin 5 := ![0,1,1]
def out : Fin 3 → Fin 5 := ![2,3,4]
def factor : Fin 3 → Nat := ![1,2,1]

structure Wires (J : Type) where
  canonical : Fin 5 → AirBignum.AddWires J 11 6
  quotient : Fin 3 → Fin 11 → J
  quotientBit : Fin 3 → Fin 11 → Fin 6 → J
  carry : Fin 3 → Fin 23 → J
  carryBit : Fin 3 → Fin 23 → Fin 12 → J

def weightedWires {J : Type} (w : Wires J) (k : Fin 3) : BfvTensorMul.RowWires J where
  canonical := ![w.canonical (lhs k),w.canonical (rhs k),w.canonical (out k)]
  quotient := w.quotient k
  quotientBit := w.quotientBit k
  carry := w.carry k
  carryBit := w.carryBit k

def system {J : Type} (q : Nat) (w : Wires J) : ConstraintSystem BabyBear J :=
  (List.finRange 3).flatMap fun k => BfvTensorMul.rowSystem q (factor k) (weightedWires w k)
def value {J : Type} (asg : J → BabyBear) (w : Wires J) (g : Fin 5) : Nat :=
  Bignum.denoteNat 64 (AirBignum.limbVals asg (w.canonical g).x)

/-- Every output is forced from one shared canonical pair, including the cross
term's factor2. No multiplication or output-range premise is supplied externally. -/
def Sound {J : Type} (q : Nat) (w : Wires J) : Prop := ∀ asg : J → BabyBear,
  systemAccepts asg (system q w) →
    (∀ g,value asg w g<q) ∧
    value asg w 2=(value asg w 0*value asg w 0)%q ∧
    value asg w 3=(2*value asg w 0*value asg w 1)%q ∧
    value asg w 4=(value asg w 1*value asg w 1)%q

theorem factor_bound (k : Fin 3) : factor k≤2 := by fin_cases k <;> decide

theorem sound {J : Type} (q : Nat) (hq : 0<q) (hcap : q<64^11) (w : Wires J) : Sound q w := by
  intro asg hs
  have hc (k : Fin 3) := BfvTensorMul.rowSystem_sound q (factor k) hq hcap
    (factor_bound k) (weightedWires w k) asg
    (show systemAccepts asg (BfvTensorMul.rowSystem q (factor k) (weightedWires w k)) from
      fun t ht => hs t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩))
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have hp0 : value asg w 2=(value asg w 0*value asg w 0)%q := by
    simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,factor,value] using h0.2
  have hp1 : value asg w 3=(2*value asg w 0*value asg w 1)%q := by
    simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,factor,value] using h1.2
  have hp2 : value asg w 4=(value asg w 1*value asg w 1)%q := by
    simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,factor,value] using h2.2
  refine ⟨?_,hp0,hp1,hp2⟩
  intro g
  fin_cases g
  · simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,value] using h0.1 0
  · simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,value] using h2.1 0
  · simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,value] using h0.1 2
  · simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,value] using h1.1 2
  · simpa [BfvTensorMul.word,weightedWires,lhs,rhs,out,value] using h2.1 2
end Minidregg.Compiler.BfvTensorCore
