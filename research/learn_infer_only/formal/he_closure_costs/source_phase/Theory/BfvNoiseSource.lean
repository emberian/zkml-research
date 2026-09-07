/-
Integer noise lifts for the actual modular negacyclic ring. Mathematical
anchor adapted/generalized from the read-only Bfv.Ring proof (toPoly, negaMul,
negaX_dvd and expansion), not a new encryption implementation. The source
reference and hash are recorded in the report. The range theorem reuses
Theory.IntegerWindowNoise's existing finite-product bound.
-/
import Theory.BfvPhaseAlgebra
import Mathlib.Algebra.Group.Fin.Basic

namespace Minidregg.Theory.BfvNoiseSource
set_option autoImplicit false
open Polynomial
open scoped BigOperators
open Minidregg.Theory.BfvPhaseAlgebra
open Minidregg.Theory.IntegerWindowNoise (signedProductSum signedProductSum_bound)

def convolution {R : Type} [CommRing R] {N : Nat} (a b : Fin N → R) : Fin N → R :=
  fun k => ∑ i : Fin N, if i.val ≤ k.val then a i * b (k - i) else -(a i * b (k - i))

noncomputable def ringVector (q N : Nat) (a : Fin N → Int) : Ring q N :=
  AdjoinRoot.mk (modulus q N) (pack q N (fun j => (a j : ZMod q)))

def integerNoise {N : Nat} (s e u e1 e2 : Fin N → Int) : Fin N → Int :=
  fun k => convolution u e k + e1 k + convolution e2 s k

/-- Statement-first target: an explicit signed integer lift of the source
noise polynomial, together with its deterministic coefficient bound. -/
def NoiseLiftContract (q N : Nat) [NeZero N]
    (s e u e1 e2 : Fin N → Int) (S : Int) : Prop :=
  (∀ k, coefficient q N k.val (noise (ringVector q N s) (ringVector q N e)
    (ringVector q N u) (ringVector q N e1) (ringVector q N e2)) = (integerNoise s e u e1 e2 k : ZMod q)) ∧
  (∀ k, |integerNoise s e u e1 e2 k| ≤ 2 * (N : Int) * S ^ 2 + S)

noncomputable def reducePower (q N s : Nat) : Polynomial (ZMod q) :=
  if s < N then X ^ s else -(X ^ (s - N))

theorem reducePower_dvd (q N s : ℕ) :
    (Polynomial.X ^ N + 1 : Polynomial (ZMod q)) ∣ (Polynomial.X ^ s - reducePower q N s) := by
  unfold reducePower
  split
  · simp
  · refine ⟨Polynomial.X ^ (s - N), ?_⟩
    have hs : s - N + N = s := by omega
    rw [sub_neg_eq_add, add_mul, one_mul, ← pow_add, Nat.add_comm N (s - N), hs]

/-- The product of two `pack q N`s, expanded over index PAIRS. -/
theorem pack_mul_expand (q N : ℕ) (a b : Fin N → ZMod q) :
    pack q N a * pack q N b
      = ∑ i : Fin N, ∑ j : Fin N,
          Polynomial.C (a i * b j) * Polynomial.X ^ ((i : ℕ) + (j : ℕ)) := by
  unfold pack
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.C_mul, pow_add]
  ring

/-- `convolution`, expanded over the SAME index pairs as `pack_mul_expand`, with each `X^(i+j)`
replaced by its negacyclic reduction. This is the reindexing step: `k := j + i` in `Fin N`. -/
theorem pack_convolution_expand (q N : ℕ) [NeZero N] (a b : Fin N → ZMod q) :
    pack q N (convolution a b)
      = ∑ i : Fin N, ∑ j : Fin N,
          Polynomial.C (a i * b j) * reducePower q N ((i : ℕ) + (j : ℕ)) := by
  unfold pack convolution
  -- push `C` through the inner sum, then swap the `k` and `i` sums
  have h1 : ∀ k : Fin N,
      Polynomial.C (∑ i : Fin N, (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i)
        else -(a i * b (k - i)))) * Polynomial.X ^ (k : ℕ)
        = ∑ i : Fin N, Polynomial.C (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i)
            else -(a i * b (k - i))) * Polynomial.X ^ (k : ℕ) := by
    intro k
    rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- reindex `k ↦ j` by `k = j + i`
  rw [← Equiv.sum_comp (Equiv.addRight i) (fun k : Fin N =>
    Polynomial.C (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))
      * Polynomial.X ^ (k : ℕ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi : (i : ℕ) < N := i.isLt
  have hj : (j : ℕ) < N := j.isLt
  have hcancel : (j + i : Fin N) - i = j := add_sub_cancel_right j i
  have hval : ((j + i : Fin N) : ℕ) = ((j : ℕ) + (i : ℕ)) % N := Fin.val_add j i
  simp only [Equiv.coe_addRight, hcancel, hval, reducePower]
  by_cases hlt : (i : ℕ) + (j : ℕ) < N
  · have hmod : ((j : ℕ) + (i : ℕ)) % N = (i : ℕ) + (j : ℕ) := by
      rw [Nat.add_comm]; exact Nat.mod_eq_of_lt hlt
    rw [hmod, if_pos (by omega), if_pos hlt]
  · have hmod : ((j : ℕ) + (i : ℕ)) % N = (i : ℕ) + (j : ℕ) - N := by
      have : (j : ℕ) + (i : ℕ) - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt this]
      omega
    rw [hmod, if_neg (by omega), if_neg hlt]
    simp


theorem pack_convolution_dvd (q N : Nat) [NeZero N] (a b : Fin N → ZMod q) :
    modulus q N ∣ pack q N a * pack q N b - pack q N (convolution a b) := by
  rw [pack_mul_expand, pack_convolution_expand, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j _
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (reducePower_dvd q N _) _

theorem pack_convolution_quotient (q N : Nat) [NeZero N] (a b : Fin N → ZMod q) :
    AdjoinRoot.mk (modulus q N) (pack q N a) * AdjoinRoot.mk (modulus q N) (pack q N b) =
      AdjoinRoot.mk (modulus q N) (pack q N (convolution a b)) := by
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  exact pack_convolution_dvd q N a b

theorem convolution_cast (q N : Nat) (a b : Fin N → Int) (k : Fin N) :
    ((convolution a b k : Int) : ZMod q) =
      convolution (fun j => (a j : ZMod q)) (fun j => (b j : ZMod q)) k := by
  simp only [convolution, Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_neg]


theorem product_coefficient_lift (q N : Nat) [NeZero N] [Nontrivial (ZMod q)]
    (a b : Fin N → Int) (k : Fin N) :
    coefficient q N k.val (ringVector q N a * ringVector q N b) = ((convolution a b k : Int) : ZMod q) := by
  rw [ringVector, ringVector, pack_convolution_quotient, coefficient_pack]
  exact (convolution_cast q N a b k).symm

theorem vector_coefficient_lift (q N : Nat) [NeZero N] [Nontrivial (ZMod q)]
    (a : Fin N → Int) (k : Fin N) :
    coefficient q N k.val (ringVector q N a) = (a k : ZMod q) := by
  exact coefficient_pack q N _ k


theorem noise_coefficient_lift (q N : Nat) [NeZero N] [Nontrivial (ZMod q)]
    (s e u e1 e2 : Fin N → Int) (k : Fin N) :
    coefficient q N k.val (noise (ringVector q N s) (ringVector q N e)
      (ringVector q N u) (ringVector q N e1) (ringVector q N e2)) = (integerNoise s e u e1 e2 k : ZMod q) := by
  simp only [noise, map_add, product_coefficient_lift, vector_coefficient_lift,
    integerNoise, Int.cast_add]

theorem convolution_as_signed_sum {N : Nat} (a b : Fin N → Int) (k : Fin N) :
    convolution a b k = signedProductSum a (fun i => b (k - i)) (fun i => decide (k.val < i.val)) := by
  unfold convolution signedProductSum
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

theorem convolution_bound {N : Nat} (a b : Fin N → Int) (S : Int)
    (hS : 0 ≤ S) (ha : ∀ i, |a i| ≤ S) (hb : ∀ i, |b i| ≤ S) (k : Fin N) :
    |convolution a b k| ≤ (N : Int) * S ^ 2 := by
  rw [convolution_as_signed_sum]
  exact signedProductSum_bound a (fun i => b (k - i)) _ S hS ha (fun i => hb _)

theorem integerNoise_bound {N : Nat} (s e u e1 e2 : Fin N → Int) (S : Int)
    (hS : 0 ≤ S) (hs : ∀ i, |s i| ≤ S) (he : ∀ i, |e i| ≤ S)
    (hu : ∀ i, |u i| ≤ S) (he1 : ∀ i, |e1 i| ≤ S) (he2 : ∀ i, |e2 i| ≤ S) (k : Fin N) :
    |integerNoise s e u e1 e2 k| ≤ 2 * (N : Int) * S ^ 2 + S := by
  have h1 := convolution_bound u e S hS hu he k
  have h2 := convolution_bound e2 s S hS he2 hs k
  have h3 := abs_add_le (convolution u e k) (e1 k)
  have h4 := abs_add_le (convolution u e k + e1 k) (convolution e2 s k)
  have h5 := he1 k
  unfold integerNoise
  nlinarith

/-- This packages precisely the two premises needed by the phase and noise
modules, derived from coefficient-supported source factors. -/
theorem supported_noise_lift (q N : Nat) [NeZero N] [Nontrivial (ZMod q)]
    (s e u e1 e2 : Fin N → Int) (S : Int) (hS : 0 ≤ S)
    (hs : ∀ i, |s i| ≤ S) (he : ∀ i, |e i| ≤ S) (hu : ∀ i, |u i| ≤ S)
    (he1 : ∀ i, |e1 i| ≤ S) (he2 : ∀ i, |e2 i| ≤ S) :
    NoiseLiftContract q N s e u e1 e2 S :=
  ⟨noise_coefficient_lift q N s e u e1 e2,
    integerNoise_bound s e u e1 e2 S hS hs he hu he1 he2⟩

/-- info: 'Minidregg.Theory.BfvNoiseSource.reducePower_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.reducePower_dvd
/-- info: 'Minidregg.Theory.BfvNoiseSource.pack_mul_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.pack_mul_expand
/-- info: 'Minidregg.Theory.BfvNoiseSource.pack_convolution_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.pack_convolution_expand
/-- info: 'Minidregg.Theory.BfvNoiseSource.pack_convolution_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.pack_convolution_dvd
/-- info: 'Minidregg.Theory.BfvNoiseSource.pack_convolution_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.pack_convolution_quotient
/-- info: 'Minidregg.Theory.BfvNoiseSource.convolution_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.convolution_cast
/-- info: 'Minidregg.Theory.BfvNoiseSource.product_coefficient_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.product_coefficient_lift
/-- info: 'Minidregg.Theory.BfvNoiseSource.vector_coefficient_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.vector_coefficient_lift
/-- info: 'Minidregg.Theory.BfvNoiseSource.noise_coefficient_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.noise_coefficient_lift
/-- info: 'Minidregg.Theory.BfvNoiseSource.convolution_as_signed_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.convolution_as_signed_sum
/-- info: 'Minidregg.Theory.BfvNoiseSource.convolution_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.convolution_bound
/-- info: 'Minidregg.Theory.BfvNoiseSource.integerNoise_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.integerNoise_bound
/-- info: 'Minidregg.Theory.BfvNoiseSource.supported_noise_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.BfvNoiseSource.supported_noise_lift

end Minidregg.Theory.BfvNoiseSource
