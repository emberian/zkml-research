/- Paired RNS switching MAC, sharing four canonical lifted inputs. -/
import Compiler.BfvKeyswitchMac
namespace Minidregg.Compiler.BfvKeyswitchCore
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
structure Wires (J : Type) where
  canonical : Fin 16 → AirBignum.AddWires J 6 9
  quotient : Fin 2 → Fin 6 → J
  quotientBit : Fin 2 → Fin 6 → Fin 9 → J
  carry : Fin 2 → Fin 13 → J
  carryBit : Fin 2 → Fin 13 → Fin 16 → J

def kindMap (h : Fin 2) (k : Fin 10) : Fin 16 :=
  if k.val<4 then ⟨k.val,by omega⟩
  else if k.val<8 then ⟨4*h.val+k.val,by omega⟩
  else if k.val=8 then ⟨12+h.val,by omega⟩
  else ⟨14+h.val,by omega⟩
def macWires {J : Type} (w : Wires J) (h : Fin 2) : BfvKeyswitchMac.RowWires J where
  canonical := fun k => w.canonical (kindMap h k)
  quotient := w.quotient h
  quotientBit := w.quotientBit h
  carry := w.carry h
  carryBit := w.carryBit h

def system {J : Type} (q : Nat) (w : Wires J) : ConstraintSystem BabyBear J :=
  (List.finRange 2).flatMap fun h => BfvKeyswitchMac.rowSystem q (macWires w h)
def value {J : Type} (asg : J → BabyBear) (w : Wires J) (g : Fin 16) : Nat :=
  Bignum.denoteNat 512 (AirBignum.limbVals asg (w.canonical g).x)
def dIndex (k : Fin 4) : Fin 16 := ⟨k.val,by omega⟩
def kIndex (h : Fin 2) (k : Fin 4) : Fin 16 := ⟨4+4*h.val+k.val,by omega⟩
def aIndex (h : Fin 2) : Fin 16 := ⟨12+h.val,by omega⟩
def oIndex (h : Fin 2) : Fin 16 := ⟨14+h.val,by omega⟩
/-- Every operand/output is canonical; both accumulated outputs are forced from
one shared D[4]. All sixteen public word bounds are part of acceptance. -/
def Sound {J : Type} (q : Nat) (w : Wires J) : Prop := ∀ asg : J → BabyBear,
  systemAccepts asg (system q w) → (∀ g,value asg w g<q) ∧
    ∀ h,value asg w (oIndex h)=(value asg w (aIndex h)+
      ∑ k : Fin 4,value asg w (dIndex k)*value asg w (kIndex h k))%q

theorem sound {J : Type} (q : Nat) (hq : 0<q) (hcap : q<512^6) (w : Wires J) : Sound q w := by
  intro asg hs
  have hc (h : Fin 2) := BfvKeyswitchMac.rowSystem_sound q hq hcap (macWires w h) asg
    (show systemAccepts asg (BfvKeyswitchMac.rowSystem q (macWires w h)) from
      fun t ht => hs t (List.mem_flatMap.mpr ⟨h,List.mem_finRange h,ht⟩))
  constructor
  · intro g
    have h0 := hc 0
    have h1 := hc 1
    fin_cases g
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 0
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 1
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 2
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 3
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 4
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 5
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 6
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 7
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h1.1 4
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h1.1 5
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h1.1 6
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h1.1 7
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 8
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h1.1 8
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h0.1 9
    · simpa [BfvKeyswitchMac.word,macWires,kindMap,value] using h1.1 9
  · intro h
    have hh := (hc h).2
    fin_cases h <;>
      simpa [BfvKeyswitchMac.word,macWires,kindMap,value,BfvKeyswitchMac.lhs,
        BfvKeyswitchMac.rhs,dIndex,kIndex,aIndex,oIndex,Fin.sum_univ_succ] using hh
end Minidregg.Compiler.BfvKeyswitchCore
