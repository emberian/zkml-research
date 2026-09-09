/- Direct semantics of matched_field/native/src/proof.rs, MacAir::eval:
sixteen public preprocessed residues, two whole-row quadratic equations, and
one zero main column. No BabyBear carry or range witnesses enter this proof. -/
import Compiler.BfvInferComposition
namespace Minidregg.Compiler.MatchedFieldMac
open Minidregg.Compiler Minidregg.Compiler.BfvInferComposition
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000

abbrev Row := Fin 16 → Nat
def dIndex (i : Fin 4) : Fin 16 := ⟨i.val,by omega⟩
def keyIndex (h : Fin 2) (i : Fin 4) : Fin 16 := ⟨4+4*h.val+i.val,by omega⟩
def addIndex (h : Fin 2) : Fin 16 := ⟨12+h.val,by omega⟩
def outIndex (h : Fin 2) : Fin 16 := ⟨14+h.val,by omega⟩

def operands (r : Row) : Operands where
  d i := r (dIndex i)
  key h i := r (keyIndex h i)
  addend h := r (addIndex h)
def outputs (r : Row) (h : Fin 2) : Nat := r (outIndex h)
def Canonical (q : Nat) (r : Row) : Prop := ∀ i,r i<q
def Equations (q : Nat) (r : Row) : Prop := ∀ h : Fin 2,
  (r (addIndex h) : ZMod q)+∑ i : Fin 4,
    (r (dIndex i) : ZMod q)*(r (keyIndex h i) : ZMod q)=(r (outIndex h) : ZMod q)
def WholeRow (q : Nat) (r : Row) (main : ZMod q) : Prop := main=0 ∧ Equations q r

def Sound : Prop := ∀ q,0<q → ∀ r,Canonical q r → Equations q r →
  ∀ h,outputs r h=output q (operands r) h

def pack (a : Operands) (out : Fin 2 → Nat) : Row :=
  ![a.d 0,a.d 1,a.d 2,a.d 3,
    a.key 0 0,a.key 0 1,a.key 0 2,a.key 0 3,
    a.key 1 0,a.key 1 1,a.key 1 2,a.key 1 3,
    a.addend 0,a.addend 1,out 0,out 1]

theorem field_eq_iff (q n o : Nat) (_hq : 0<q) (ho : o<q) :
    (n : ZMod q)=(o : ZMod q) ↔ o=n%q := by
  letI : NeZero q := ⟨Nat.ne_of_gt _hq⟩
  constructor
  · intro h
    have hh := congrArg ZMod.val h
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt ho] using hh.symm
  · intro h
    rw [h]
    simp

theorem sound : Sound := by
  intro q hq r hc he h
  apply (field_eq_iff q _ _ hq (hc (outIndex h))).mp
  simpa only [operands,Nat.cast_add,Nat.cast_sum,Nat.cast_mul] using he h

/-- Exact equivalence to the same integer MAC law, at canonical public outputs.
No bound on an unreduced integer sum is needed: reduction is in the target ring. -/
theorem equations_iff (q : Nat) (hq : 0<q) (r : Row) (hc : Canonical q r) :
    Equations q r ↔ ∀ h,outputs r h=output q (operands r) h := by
  constructor
  · exact sound q hq r hc
  · intro h c
    have hh := (field_eq_iff q _ _ hq (hc (outIndex c))).mpr (h c)
    simpa only [operands,Nat.cast_add,Nat.cast_sum,Nat.cast_mul] using hh

theorem pack_operands (a : Operands) (out : Fin 2 → Nat) : operands (pack a out)=a := by
  cases a with
  | mk d key addend =>
    dsimp only [operands]
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext h i; fin_cases h <;> fin_cases i <;> rfl
    · funext h; fin_cases h <;> rfl

theorem pack_outputs (a : Operands) (out : Fin 2 → Nat) : outputs (pack a out)=out := by
  funext h; fin_cases h <;> rfl

theorem pack_canonical (q : Nat) (a : Operands) (out : Fin 2 → Nat)
    (hd : ∀ i,a.d i<q) (hk : ∀ h i,a.key h i<q)
    (ha : ∀ h,a.addend h<q) (ho : ∀ h,out h<q) : Canonical q (pack a out) := by
  intro i
  fin_cases i <;> first | exact hd _ | exact hk _ _ | exact ha _ | exact ho _

theorem complete (q : Nat) (hq : 0<q) (a : Operands)
    (hd : ∀ i,a.d i<q) (hk : ∀ h i,a.key h i<q) (ha : ∀ h,a.addend h<q) :
    Canonical q (pack a (output q a)) ∧ WholeRow q (pack a (output q a)) 0 := by
  have hc := pack_canonical q a (output q a) hd hk ha
    (fun h => Nat.mod_lt _ hq)
  refine ⟨hc,rfl,(equations_iff q hq _ hc).mpr ?_⟩
  intro h
  rw [pack_operands,pack_outputs]

theorem allRowsSound {n : Nat} (q : Nat) (hq : 0<q) (rows : Fin n → Row)
    (main : Fin n → ZMod q) (hc : ∀ j,Canonical q (rows j))
    (he : ∀ j,WholeRow q (rows j) (main j)) :
    ∀ j h,outputs (rows j) h=output q (operands (rows j)) h :=
  fun j => sound q hq (rows j) (hc j) (he j).2

def primes := BfvInferLinear.primes
theorem primes_exact : primes=![1125899906826241,1125899906629633,1125899905744897,1125899905351681] := rfl
theorem prime_positive (l : Fin 4) : 0<primes l := (BfvKeyswitchRow.prime_capacity l).1

def witnessOperands : Operands where
  d := ![1,2,3,4]
  key := ![![2,3,4,5],![3,4,5,6]]
  addend := ![7,8]

theorem nonzeroWitness (l : Fin 4) :
    Canonical (primes l) (pack witnessOperands ![47,58]) ∧
    WholeRow (primes l) (pack witnessOperands ![47,58]) 0 := by
  have hd : ∀ i,witnessOperands.d i<primes l := by
    intro i; fin_cases l <;> fin_cases i <;> decide
  have hk : ∀ h i,witnessOperands.key h i<primes l := by
    intro h i; fin_cases l <;> fin_cases h <;> fin_cases i <;> decide
  have ha : ∀ h,witnessOperands.addend h<primes l := by
    intro h; fin_cases l <;> fin_cases h <;> decide
  have ho : output (primes l) witnessOperands=![47,58] := by
    funext h; fin_cases l <;> fin_cases h <;> decide
  simpa only [ho] using complete (primes l) (prime_positive l) witnessOperands hd hk ha

theorem wrongOutputRefused (l : Fin 4) :
    ¬WholeRow (primes l) (pack witnessOperands ![48,58]) 0 := by
  intro h
  have hc : Canonical (primes l) (pack witnessOperands ![48,58]) := by
    intro i; fin_cases l <;> fin_cases i <;> decide
  have hh := sound (primes l) (prime_positive l) _ hc h.2 0
  fin_cases l <;> norm_num [pack_outputs,pack_operands,output,witnessOperands,primes,
    BfvInferLinear.primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ] at hh

theorem premiseInhabited (l : Fin 4) : ∃ r : Row,
    Canonical (primes l) r ∧ WholeRow (primes l) r 0 ∧ outputs r 0≠0 := by
  exact ⟨pack witnessOperands ![47,58],(nonzeroWitness l).1,(nonzeroWitness l).2,by decide⟩

/-- info: 'Minidregg.Compiler.MatchedFieldMac.field_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms field_eq_iff
/-- info: 'Minidregg.Compiler.MatchedFieldMac.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sound
/-- info: 'Minidregg.Compiler.MatchedFieldMac.equations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equations_iff
/-- info: 'Minidregg.Compiler.MatchedFieldMac.pack_operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_operands
/-- info: 'Minidregg.Compiler.MatchedFieldMac.pack_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_outputs
/-- info: 'Minidregg.Compiler.MatchedFieldMac.pack_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_canonical
/-- info: 'Minidregg.Compiler.MatchedFieldMac.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complete
/-- info: 'Minidregg.Compiler.MatchedFieldMac.allRowsSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allRowsSound
/-- info: 'Minidregg.Compiler.MatchedFieldMac.primes_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms primes_exact
/-- info: 'Minidregg.Compiler.MatchedFieldMac.prime_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prime_positive
/-- info: 'Minidregg.Compiler.MatchedFieldMac.nonzeroWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonzeroWitness
/-- info: 'Minidregg.Compiler.MatchedFieldMac.wrongOutputRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrongOutputRefused
/-- info: 'Minidregg.Compiler.MatchedFieldMac.premiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms premiseInhabited

end Minidregg.Compiler.MatchedFieldMac
