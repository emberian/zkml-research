/- Exact public linear boundary for the actual multi-prime, level-zero Infer. -/
import Compiler.BfvKeyswitchRow
namespace Minidregg.Compiler.BfvInferLinear
open Minidregg.Compiler
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

def degree : Nat := 8192
abbrev Slot := Fin degree
def primes := BfvKeyswitchRow.primes
/-- The actual prime constructor's optimized-reduction test after substituting
its fourteen leading zero bits. All inputs here are public constants. -/
def supportsOptimized (q : Nat) : Prop :=
  (2^(3*14)+1)*2^64 < 2^(3*14)*(2^14+1)*q
/-- Natural-word model of zq::lazy_reduce_opt at fifty-bit moduli. -/
def lazyLiftWord (q x : Nat) : Nat := x-(x/2^50)*q
/-- Canonical target-prime input to the public NTT callback. -/
def canonicalLift (q x : Nat) : Nat := x%q

def LiftCorrect : Prop := ∀ s t : Fin 4, ∀ x : Nat, x<primes s →
  supportsOptimized (primes t) ∧ lazyLiftWord (primes t) x=x ∧
  x<2*primes t ∧ lazyLiftWord (primes t) x%primes t=canonicalLift (primes t) x

theorem actual_prime_bounds (i : Fin 4) :
    2^49<primes i ∧ primes i<2^50 ∧ supportsOptimized (primes i) := by
  fin_cases i <;> norm_num [primes,BfvKeyswitchRow.primes,supportsOptimized]

theorem liftCorrect : LiftCorrect := by
  intro s t x hx
  have hs := actual_prime_bounds s
  have ht := actual_prime_bounds t
  have hx50 : x<2^50 := lt_trans hx hs.2.1
  have hz : x/2^50=0 := Nat.div_eq_of_lt hx50
  have heq : lazyLiftWord (primes t) x=x := by unfold lazyLiftWord; rw [hz]; simp
  exact ⟨ht.2.2,heq,by omega,by simp [heq,canonicalLift]⟩

/-- Bit-reversed NTT storage coordinate, exactly thirteen low bits. -/
def reverseIndex (j : Slot) : Slot := (BitVec.ofFin (show Fin (2^13) from j)).reverse.toFin
/-- Odd-root enumeration map, before converting to bit-reversed storage. -/
def rootIndex (e : Nat) (j : Slot) : Slot :=
  ⟨((e-1)/2+e*j.val)%degree,Nat.mod_lt _ (by decide)⟩
/-- Direct input index for each output storage index. -/
def permutation (e : Nat) (j : Slot) : Slot :=
  reverseIndex (rootIndex e (reverseIndex j))
def substitute {A : Type} (e : Nat) (p : Slot → A) (j : Slot) : A := p (permutation e j)

def PermutationCorrect : Prop := ∀ (A : Type) (e : Nat) (p : Slot → A) (j : Slot),
  substitute e p (reverseIndex j)=p (reverseIndex (rootIndex e j))

theorem reverseIndex_involutive (j : Slot) : reverseIndex (reverseIndex j)=j := by
  simp only [reverseIndex,BitVec.ofFin_toFin,BitVec.reverse_reverse_eq,BitVec.toFin_ofFin]

theorem permutationCorrect : PermutationCorrect := by
  intro A e p j
  simp [substitute,permutation,reverseIndex_involutive]

/-- Fixed exponents used by the saved evaluation key: nine column rotations
by 8..2048 followed by the row automorphism. -/
def exponents : Fin 10 → Nat := ![6561,5953,16001,15617,14849,13313,10241,4097,8193,16383]
def shifts : Fin 9 → Nat := ![8,16,32,64,128,256,512,1024,2048]
def StageExponents : Prop :=
  (∀ i : Fin 9, exponents i.castSucc=3^(shifts i)%(2*degree)) ∧
  exponents 9=2*degree-1 ∧ (∀ i, exponents i%2=1 ∧ exponents i<2*degree)

theorem stageExponents : StageExponents := by
  constructor
  · intro i; fin_cases i <;> decide
  constructor
  · decide
  · intro i; fin_cases i <;> decide

/-- Nonzero source residue above one target prime: lift must not be mistaken
for canonical equality across all moduli. -/
def LiftInhabited : Prop := ∃ x, x<primes 0 ∧ lazyLiftWord (primes 3) x=x ∧
  canonicalLift (primes 3) x=1

theorem liftInhabited : LiftInhabited := by
  exact ⟨primes 3+1,by decide,by decide,by decide⟩

def RawCanonicalEqualityFalse : Prop :=
  ¬ ∀ x, x<primes 0 → canonicalLift (primes 3) x=x

theorem rawCanonicalEqualityFalse : RawCanonicalEqualityFalse := by
  intro h
  have heq := h (primes 3+1) (by decide)
  have hne : canonicalLift (primes 3) (primes 3+1)≠primes 3+1 := by decide
  exact hne heq
end Minidregg.Compiler.BfvInferLinear

/-- info: 'Minidregg.Compiler.BfvInferLinear.actual_prime_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.actual_prime_bounds

/-- info: 'Minidregg.Compiler.BfvInferLinear.liftCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.liftCorrect

/-- info: 'Minidregg.Compiler.BfvInferLinear.reverseIndex_involutive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.reverseIndex_involutive

/-- info: 'Minidregg.Compiler.BfvInferLinear.permutationCorrect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.permutationCorrect

/-- info: 'Minidregg.Compiler.BfvInferLinear.stageExponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.stageExponents

/-- info: 'Minidregg.Compiler.BfvInferLinear.liftInhabited' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.liftInhabited

/-- info: 'Minidregg.Compiler.BfvInferLinear.rawCanonicalEqualityFalse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferLinear.rawCanonicalEqualityFalse
