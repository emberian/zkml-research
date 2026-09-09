/- Exact modulo pushforward for fresh uniform finite words. This is a
finite sampling statement, without a pseudorandomness claim about a transcript. -/
import Selvage.AuditSampling
import Selvage.ConsistencyCoherentTransport

namespace Minidregg.Selvage.FiniteModuloSampling
open scoped BigOperators Classical

/-- The residue map applied to the canonical representative. -/
def sampleModulo {p : ℕ} (k : ℕ) (hk : 0 < k) (x : Fin p) : Fin k :=
  ⟨x.val % k,Nat.mod_lt _ hk⟩

/-- Statement-first exact law: a complete number of residue cycles plus one
additional zero representative. -/
def PushforwardLaw (a k : ℕ) (hk : 0 < k) : Prop :=
  ∀ E : Fin k → Prop,
    uniformProb (Fin (a*k+1)) (fun x => E (sampleModulo k hk x)) =
      ((a*k:ℕ):ℝ)/(a*k+1) * uniformProb (Fin k) E +
        (if E ⟨0,hk⟩ then 1/(a*k+1:ℝ) else 0)

/-- Every full residue cycle contributes the same arbitrary-predicate mass. -/
theorem full_cycles_sum (a k : ℕ) (hk : 0 < k) (E : Fin k → Prop) :
    (∑ x : Fin (a*k), if E (sampleModulo k hk x) then (1:ℝ) else 0) =
      (a:ℝ) * ∑ i : Fin k, if E i then (1:ℝ) else 0 := by
  rw [←Equiv.sum_comp (finProdFinEquiv : Fin a × Fin k ≃ Fin (a*k))]
  rw [Fintype.sum_prod_type]
  have hmod (x : Fin a) (i : Fin k) :
      sampleModulo k hk (finProdFinEquiv (x,i)) = i := by
    apply Fin.ext
    simp [sampleModulo,finProdFinEquiv,Nat.mod_eq_of_lt i.isLt]
  simp_rw [hmod]
  simp

/-- The extra canonical representative a*k contributes exactly at residue zero. -/
theorem cycles_plus_zero_sum (a k : ℕ) (hk : 0 < k) (E : Fin k → Prop) :
    (∑ x : Fin (a*k+1), if E (sampleModulo k hk x) then (1:ℝ) else 0) =
      (a:ℝ) * (∑ i : Fin k, if E i then (1:ℝ) else 0) +
        (if E ⟨0,hk⟩ then 1 else 0) := by
  rw [Fin.sum_univ_castSucc]
  have hlast : sampleModulo k hk (Fin.last (a*k)) = ⟨0,hk⟩ := by
    apply Fin.ext
    simp [sampleModulo]
  rw [hlast]
  change (∑ x : Fin (a*k), if E (sampleModulo k hk x) then (1:ℝ) else 0) + _ = _
  rw [full_cycles_sum]

/-- Exact arbitrary-event distribution under one fresh uniform canonical word. -/
theorem pushforward_exact (a k : ℕ) (hk : 0 < k) : PushforwardLaw a k hk := by
  intro E
  rw [uniformProb_eq_avg_indicator,cycles_plus_zero_sum,
    uniformProb_eq_avg_indicator,Fintype.card_fin,Fintype.card_fin]
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp' : (a*k+1:ℝ) ≠ 0 := by positivity
  push_cast
  split_ifs <;> field_simp
  all_goals ring

/-- Independent fresh base words preserve the exact biased one-word law to power q. -/
theorem independent_exact (a k : ℕ) (hk : 0 < k) (q : ℕ) (E : Fin k → Prop) :
    uniformProb (Fin q → Fin (a*k+1)) (fun x => ∀ j, E (sampleModulo k hk (x j))) =
      (((a*k:ℕ):ℝ)/(a*k+1) * uniformProb (Fin k) E +
        (if E ⟨0,hk⟩ then 1/(a*k+1:ℝ) else 0))^q := by
  rw [ArityEight.Schedule.uniformProb_all_coordinates q
    (fun x : Fin (a*k+1) => E (sampleModulo k hk x))]
  rw [pushforward_exact a k hk E]

/-- Uniform-index survival controls the actual fresh-base modulo sampler,
including its extra mass at zero, without assuming a uniform residue distribution. -/
theorem independent_bound (a k : ℕ) (hk : 0 < k) (q : ℕ) (E : Fin k → Prop)
    (t : ℝ) (ht : uniformProb (Fin k) E ≤ t) :
    uniformProb (Fin q → Fin (a*k+1)) (fun x => ∀ j, E (sampleModulo k hk (x j))) ≤
      (((a*k:ℕ):ℝ)/(a*k+1) * t + 1/(a*k+1:ℝ))^q := by
  rw [ArityEight.Schedule.uniformProb_all_coordinates q
    (fun x : Fin (a*k+1) => E (sampleModulo k hk x))]
  apply pow_le_pow_left₀ (uniformProb_nonneg _)
  rw [pushforward_exact a k hk E]
  apply add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
  split_ifs
  · exact le_rfl
  · positivity

/-- One residue has uniform mass exactly 1/k before applying the biased map. -/
theorem uniform_singleton (k : ℕ) (b : Fin k) :
    uniformProb (Fin k) (fun i => i = b) = 1/(k:ℝ) := by
  unfold uniformProb
  simp [Nat.card_eq_fintype_card]

/-- Zero receives the additional canonical representative. -/
theorem zero_probability (a k : ℕ) (hk : 0 < k) :
    uniformProb (Fin (a*k+1)) (fun x => sampleModulo k hk x = ⟨0,hk⟩) =
      (a+1:ℝ)/(a*k+1) := by
  rw [pushforward_exact a k hk (fun i => i = ⟨0,hk⟩),uniform_singleton]
  simp only [ite_true]
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-- Every nonzero residue has only the complete-cycle representatives. -/
theorem nonzero_probability (a k : ℕ) (hk : 0 < k) (b : Fin k) (hb : b.val ≠ 0) :
    uniformProb (Fin (a*k+1)) (fun x => sampleModulo k hk x = b) =
      (a:ℝ)/(a*k+1) := by
  rw [pushforward_exact a k hk (fun i => i = b),uniform_singleton]
  have hb' : (⟨0,hk⟩ : Fin k) ≠ b := by
    intro h
    exact hb (congrArg Fin.val h).symm
  simp only [hb',ite_false,add_zero]
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-- Falsifier to a uniform-residue claim: zero is strictly heavier than one. -/
theorem zero_bias_witness (a k : ℕ) (hk : 1 < k) :
    uniformProb (Fin (a*k+1)) (fun x => sampleModulo k (by omega) x = ⟨1,hk⟩) <
      uniformProb (Fin (a*k+1)) (fun x => sampleModulo k (by omega) x = ⟨0,by omega⟩) := by
  rw [nonzero_probability a k (by omega) ⟨1,hk⟩ (by simp),zero_probability]
  apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < a*k+1)).mpr
  linarith

/-- The keystone premises are inhabited at positive cycle count and nontrivial residue size. -/
theorem pushforward_premises_inhabited : ∃ (a k : ℕ) (hk : 0 < k),
    0 < a ∧ 1 < k ∧ PushforwardLaw a k hk :=
  ⟨1,2,by decide,by decide,by decide,pushforward_exact 1 2 (by decide)⟩

end Minidregg.Selvage.FiniteModuloSampling

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.full_cycles_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.full_cycles_sum

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.cycles_plus_zero_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.cycles_plus_zero_sum

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.pushforward_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.pushforward_exact

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.independent_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.independent_exact

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.independent_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.independent_bound

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.uniform_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.uniform_singleton

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.zero_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.zero_probability

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.nonzero_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.nonzero_probability

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.zero_bias_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.zero_bias_witness

/-- info: 'Minidregg.Selvage.FiniteModuloSampling.pushforward_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.FiniteModuloSampling.pushforward_premises_inhabited

