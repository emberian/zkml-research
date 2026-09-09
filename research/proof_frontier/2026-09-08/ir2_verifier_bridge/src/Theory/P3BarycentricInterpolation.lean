/- Mathematical semantics of the deployed P3 coset-row interpolation kernel.
The formula follows plonky3-fri-82cfad73/src/two_adic_pcs.rs:464–508;
the inspected P3 source is dual MIT/Apache-2.0 licensed. This Lean proof
is newly derived here from Mathlib interpolation identities.
The theorem derives its equality with interpolation from the actual distinct
coset-node equations, including the challenge-at-node branch. -/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace P3Barycentric
open Polynomial
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

/-- The nonempty, distinct coset-node interface checked by the fold construction. -/
structure CosetNodes (F : Type*) [Field F] (n : ℕ) where
  pos : 0 < n
  nodes : Fin n ↪ F
  power : F
  power_ne_zero : power ≠ 0
  powers : ∀ i, nodes i ^ n = power
  cardinal_ne_zero : (n : F) ≠ 0

/-- Source-independent constructor from the actual coset root and shift. -/
def fromPrimitive (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (s : F) (hs : s ≠ 0) (hcast : (n:F) ≠ 0) : CosetNodes F n where
  pos := hn
  nodes := ⟨fun i => s*ω^i.val, fun i j h => Fin.ext (hω.pow_inj i.isLt j.isLt (mul_left_cancel₀ hs h))⟩
  power := s^n
  power_ne_zero := pow_ne_zero _ hs
  powers i := by
    change (s*ω^i.val)^n = s^n
    rw [mul_pow]
    rw [←pow_mul,Nat.mul_comm i.val n,pow_mul,hω.pow_eq_one,one_pow,mul_one]
  cardinal_ne_zero := hcast

/-- Ordering may be the runtime's bit reversal; coset equations are preserved. -/
def reindex (xs : CosetNodes F n) (e : Fin n ≃ Fin n) : CosetNodes F n where
  pos := xs.pos
  nodes := e.toEmbedding.trans xs.nodes
  power := xs.power
  power_ne_zero := xs.power_ne_zero
  powers i := xs.powers (e i)
  cardinal_ne_zero := xs.cardinal_ne_zero

/-- Exact early-return/barycentric branch structure of the native row kernel.
The inverse factor is native `weight_scale`; products and sums preserve order
semantically because the carrier is a field. -/
def native (xs : CosetNodes F n) (ys : Fin n → F) (z : F) : F :=
  if h : ∃ i, z = xs.nodes i then ys (Classical.choose h)
  else (∑ i, ys i * (xs.nodes i * ((n:F)*xs.power)⁻¹) * (z-xs.nodes i)⁻¹) *
    ∏ i, (z-xs.nodes i)

/-- Statement first: native evaluation is the unique degree-bounded interpolant. -/
def Correctness (xs : CosetNodes F n) : Prop :=
  ∀ ys z, native xs ys z = (Lagrange.interpolate Finset.univ xs.nodes ys).eval z

lemma nodes_ne_zero (xs : CosetNodes F n) (i : Fin n) : xs.nodes i ≠ 0 := by
  intro h
  apply xs.power_ne_zero
  rw [←xs.powers i,h,zero_pow (Nat.ne_of_gt xs.pos)]

lemma nodal_shape (xs : CosetNodes F n) :
    Lagrange.nodal Finset.univ xs.nodes = X^n-C xs.power := by
  have hd : (Lagrange.nodal Finset.univ xs.nodes).degree = (X^n-C xs.power : F[X]).degree := by
    simp [degree_X_pow_sub_C xs.pos]
  have hl : (Lagrange.nodal Finset.univ xs.nodes).leadingCoeff =
      (X^n-C xs.power : F[X]).leadingCoeff := by
    rw [Lagrange.nodal_monic.leadingCoeff,(monic_X_pow_sub_C _ (Nat.ne_of_gt xs.pos)).leadingCoeff]
  have hb := Polynomial.degree_sub_lt hd Lagrange.nodal_ne_zero hl
  rw [Lagrange.degree_nodal] at hb
  have hz : Lagrange.nodal Finset.univ xs.nodes - (X^n-C xs.power) = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ xs.nodes.injective.injOn hb
    intro i hi
    simp [Lagrange.eval_nodal_at_node hi,xs.powers i]
  exact sub_eq_zero.mp hz

lemma native_weight (xs : CosetNodes F n) (i : Fin n) :
    Lagrange.nodalWeight Finset.univ xs.nodes i = xs.nodes i * ((n:F)*xs.power)⁻¹ := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i),nodal_shape]
  simp only [derivative_sub,derivative_X_pow,derivative_C,sub_zero,eval_mul,eval_C,eval_pow,eval_X]
  have he : (xs.nodes i)^(n-1)*xs.nodes i = xs.power := by
    rw [←pow_succ,Nat.sub_add_cancel xs.pos,xs.powers]
  have hx := nodes_ne_zero xs i
  have hn := xs.cardinal_ne_zero
  have hc := xs.power_ne_zero
  field_simp [hx,hn,hc]
  exact he.symm

/-- The exact deployed barycentric formula, including the node hit, equals
ordinary polynomial interpolation. No claimed fold equality is a premise. -/
theorem correctness (xs : CosetNodes F n) : Correctness xs := by
  intro ys z
  by_cases h : ∃ i, z = xs.nodes i
  · rw [native,dif_pos h]
    have hv := Lagrange.eval_interpolate_at_node ys xs.nodes.injective.injOn (Finset.mem_univ (Classical.choose h))
    exact hv.symm.trans (congrArg (fun x => (Lagrange.interpolate Finset.univ xs.nodes ys).eval x) (Classical.choose_spec h).symm)
  · rw [native,dif_neg h]
    have hi := Lagrange.eval_interpolate_not_at_node (s := Finset.univ) ys (fun i _ hz => h ⟨i,hz⟩)
    rw [Lagrange.eval_nodal] at hi
    simp only [native_weight] at hi
    rw [hi,mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Every genuine low-degree row polynomial is evaluated at the same scalar. -/
theorem native_of_polynomial (xs : CosetNodes F n) (p : F[X]) (hp : p.degree < n) (z : F) :
    native xs (fun i => p.eval (xs.nodes i)) z = p.eval z := by
  rw [correctness]
  congr 1
  symm
  exact Lagrange.eq_interpolate xs.nodes.injective.injOn (by simpa using hp)

end
end P3Barycentric

/-- info: 'P3Barycentric.nodes_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms P3Barycentric.nodes_ne_zero

/-- info: 'P3Barycentric.nodal_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms P3Barycentric.nodal_shape

/-- info: 'P3Barycentric.native_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms P3Barycentric.native_weight

/-- info: 'P3Barycentric.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms P3Barycentric.correctness

/-- info: 'P3Barycentric.native_of_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms P3Barycentric.native_of_polynomial

