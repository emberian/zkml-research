/- PCS divided differences on a multiplicative coset. The source degree
convention is explicit: quotient degree < d gives original degree ≤ d.
No commitment, sampler, transcript or Fiat--Shamir assumption is hidden here. -/
import Selvage.CurveProximityGapFullUD
import Mathlib.Tactic

namespace Minidregg.Selvage.PcsBatching
open Polynomial
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {F ι κ : Type*} [Field F] [DecidableEq F] [Fintype ι]

/-- Terms are in the fixed coefficient order of the alpha polynomial. Repeated
column identifiers share the same source word but may have different claims. -/
structure Data (F ι κ : Type*) (M : ℕ) where
  column : Fin (M+1) → κ
  source : κ → ι → F
  point : Fin (M+1) → F
  claim : Fin (M+1) → F

def Data.quotientWord {M : ℕ} (a : Data F ι κ M) (dom : ι ↪ F) (s : F)
    (j : Fin (M+1)) (i : ι) : F :=
  (a.claim j-a.source (a.column j) i)/(a.point j-s*dom i)

def Data.OffDomain {M : ℕ} (a : Data F ι κ M) (dom : ι ↪ F) (s : F) : Prop :=
  ∀ j i, a.point j ≠ s*dom i

/-- Physical-variable polynomials: evaluated at the original coset point s*t,
and at the supplied opening point z, rather than silently at z/s. -/
def Data.JointOn {M : ℕ} (a : Data F ι κ M) (dom : ι ↪ F) (s : F)
    (d : ℕ) (S : Finset ι) : Prop :=
  ∃ p : Fin (M+1) → F[X],
    (∀ j, (p j).natDegree ≤ d ∧ (p j).eval (a.point j)=a.claim j ∧
      ∀ i ∈ S, (p j).eval (s*dom i)=a.source (a.column j) i) ∧
    ∀ j k, a.column j=a.column k → p j=p k

def Data.JointNear {M : ℕ} (a : Data F ι κ M) (dom : ι ↪ F) (s : F)
    (d : ℕ) (δ : ℝ) : Prop :=
  ∃ S : Finset ι, (1-δ)*(Fintype.card ι : ℝ) ≤ S.card ∧ a.JointOn dom s d S

def liftQuotient (s z claim : F) (q : F[X]) : F[X] :=
  C claim-(C z-X)*(q.comp (C s⁻¹*X))

def cosetDomain (dom : ι ↪ F) (s : F) (hs : s ≠ 0) : ι ↪ F where
  toFun i := s*dom i
  inj' := by intro i j h; exact dom.injective (mul_left_cancel₀ hs h)

omit [DecidableEq F] in
theorem liftQuotient_eval_point (s z claim : F) (q : F[X]) :
    (liftQuotient s z claim q).eval z=claim := by
  simp [liftQuotient]

omit [DecidableEq F] in
theorem liftQuotient_eval_coset (s z claim t : F) (hs : s ≠ 0) (q : F[X]) :
    (liftQuotient s z claim q).eval (s*t)=claim-(z-s*t)*q.eval t := by
  simp [liftQuotient,hs]

omit [DecidableEq F] in
theorem liftQuotient_natDegree (s z claim : F) (q : F[X]) {d : ℕ}
    (hq : q.natDegree < d) : (liftQuotient s z claim q).natDegree ≤ d := by
  have hc : (q.comp (C s⁻¹*X)).natDegree ≤ q.natDegree := by
    calc
      _ ≤ q.natDegree*(C s⁻¹*X : F[X]).natDegree := Polynomial.natDegree_comp_le
      _ ≤ q.natDegree*1 := Nat.mul_le_mul_left _ (Polynomial.natDegree_le_of_degree_le (Polynomial.degree_C_mul_X_le _))
      _ = _ := Nat.mul_one _
  have hz : (C z-X : F[X]).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by omega)

/-- Polynomial identity uses strictly more than d shared positions. This is
why the one-degree reconstruction loss cannot be suppressed. -/
theorem eq_of_common_set (dom : ι ↪ F) {d : ℕ} {p q : F[X]}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (S : Finset ι)
    (hsize : d < S.card) (heq : ∀ i ∈ S, p.eval (dom i)=q.eval (dom i)) : p=q := by
  by_contra hne
  have hp' : p.degree < ((d+1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast (Nat.lt_succ_of_le hp))
  have hq' : q.degree < ((d+1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast (Nat.lt_succ_of_le hq))
  have hcard := card_agreeSet_lt_of_ne dom hp' hq' hne
  have hsub : S ⊆ Finset.univ.filter (fun i => p.eval (dom i)=q.eval (dom i)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,heq i hi⟩
  have := Finset.card_le_card hsub
  omega

/-- All quotient codewords agreeing on S reconstruct one physical polynomial
per source column, with every supplied opening claim satisfied. -/
theorem jointOn_of_quotient_agreement {M d : ℕ} (a : Data F ι κ M)
    (dom : ι ↪ F) (s : F) (hs : s ≠ 0) (hd : 1 ≤ d)
    (hoff : a.OffDomain dom s) (S : Finset ι) (hsize : d < S.card)
    (hjoint : ∀ j, ∃ w ∈ reedSolomonCode dom d, AgreesOn S (a.quotientWord dom s j) w) :
    a.JointOn dom s d S := by
  have hpoly : ∀ j, ∃ q : F[X], q.natDegree < d ∧
      ∀ i ∈ S, a.quotientWord dom s j i=q.eval (dom i) := by
    intro j
    obtain ⟨w,hw,hagree⟩ := hjoint j
    obtain ⟨q,hq,hval⟩ := mem_reedSolomonCode_iff.mp hw
    refine ⟨q,?_,fun i hi => (hagree i hi).trans (hval i)⟩
    by_cases hq0 : q=0
    · simpa [hq0] using hd
    · exact (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hq
  choose q hdegree heval using hpoly
  let p := fun j => liftQuotient s (a.point j) (a.claim j) (q j)
  have hp : ∀ j, (p j).natDegree ≤ d := fun j => liftQuotient_natDegree _ _ _ _ (hdegree j)
  have hagree : ∀ j i, i ∈ S → (p j).eval (s*dom i)=a.source (a.column j) i := by
    intro j i hi
    have hh := heval j i hi
    have hn : a.point j-s*dom i ≠ 0 := sub_ne_zero.mpr (hoff j i)
    have hm := (div_eq_iff hn).mp hh
    change (liftQuotient s (a.point j) (a.claim j) (q j)).eval (s*dom i)=_
    rw [liftQuotient_eval_coset _ _ _ _ hs]
    linear_combination hm
  refine ⟨p,fun j => ⟨hp j,liftQuotient_eval_point _ _ _ _,hagree j⟩,?_⟩
  intro j k hcol
  apply eq_of_common_set (cosetDomain dom s hs) (hp j) (hp k) S hsize
  intro i hi
  change (p j).eval (s*dom i)=(p k).eval (s*dom i)
  rw [hagree j i hi,hagree k i hi,hcol]

/- Exact dependencies of every theorem in this module. -/

/-- info: 'Minidregg.Selvage.PcsBatching.liftQuotient_eval_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.liftQuotient_eval_point

/-- info: 'Minidregg.Selvage.PcsBatching.liftQuotient_eval_coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.liftQuotient_eval_coset

/-- info: 'Minidregg.Selvage.PcsBatching.liftQuotient_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.liftQuotient_natDegree

/-- info: 'Minidregg.Selvage.PcsBatching.eq_of_common_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.eq_of_common_set

/-- info: 'Minidregg.Selvage.PcsBatching.jointOn_of_quotient_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.jointOn_of_quotient_agreement

end
end Minidregg.Selvage.PcsBatching
