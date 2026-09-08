/-
# Full UD on the actual BabyBear X^4-11 carrier

Statement-first concrete carrier/cardinality bridge. The field and basis
come from BabyBearExt4; the full-UD realizer is imported unchanged. No new
field or RS semantics are introduced.
-/
import Selvage.BabyBearExt4
import Selvage.ProximityGapFullUD

namespace Minidregg.Selvage.BabyBearExt4

noncomputable section

/-- Finite enumeration transported through the existing coefficient equivalence. -/
instance ext4Fintype : Fintype Ext4 :=
  Fintype.ofEquiv (Fin extensionPolynomial.natDegree → BabyBear) coefficients.toEquiv.symm

instance ext4DecidableEq : DecidableEq Ext4 := Classical.decEq _

/-- Exact cardinality obligation for the existing deployed quotient carrier. -/
def CarrierCardinality : Prop := Fintype.card Ext4 = modulus^4

/-- Full-UD interface on the actual carrier, with its exact cardinality in
the denominator. Domain, positive dimension and rate remain explicit. -/
def FullUDRealizer (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] : Prop :=
  ∀ (dom : ι ↪ Ext4) (d : ℕ), 1 ≤ d →
    IsProximityGenerator (affineGenerator Ext4) (reedSolomonCode dom d)
      ((1+(d : ℝ)/(Fintype.card ι : ℝ))/2)
      (fun _ => (Fintype.card ι : ℝ)/(modulus : ℝ)^4)

/-- The existing power basis has four BabyBear coefficients, hence exactly p^4 values. -/
theorem ext4_card : CarrierCardinality := by
  change Fintype.card Ext4 = modulus^4
  rw [Fintype.card_congr coefficients.toEquiv, Fintype.card_fun, Fintype.card_fin]
  rw [extensionPolynomial_natDegree, ZMod.card]

/-- A base-field carrier cannot satisfy the quartic carrier cardinality contract. -/
theorem base_field_cardinality_falsifier : Fintype.card BabyBear ≠ modulus^4 := by
  rw [ZMod.card]
  norm_num [modulus]

namespace FullUDInstantiation

/-- A concrete n=2^20 evaluation embedding through the actual base subfield.
This is an RS witness domain; no multiplicative folding tower is asserted. -/
def domain : Fin (2^20) ↪ Ext4 where
  toFun i := algebraMap BabyBear Ext4 (i.val : BabyBear)
  inj' := by
    intro a b hab
    have heq : (a.val : BabyBear) = (b.val : BabyBear) :=
      (algebraMap BabyBear Ext4).injective hab
    have ha : a.val < modulus := lt_trans a.isLt (by norm_num [modulus])
    have hb : b.val < modulus := lt_trans b.isLt (by norm_num [modulus])
    apply Fin.ext
    have h := congrArg ZMod.val heq
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h

def xWord : Fin (2^20) → Ext4 := domain
def oneWord : Fin (2^20) → Ext4 := fun _ => 1
def pair : Fin 2 → Fin (2^20) → Ext4 := ![xWord,oneWord]

/-- Exact nonvacuity obligation at the parameter lane's rate-half direct-tail radius. -/
def FiringPremise (f : Fin 2 → Fin (2^20) → Ext4) : Prop :=
  (0 : ℝ) < 1/5 ∧
  (1/5 : ℝ) < 1-(1+(2^19 : ℝ)/(Fintype.card (Fin (2^20)) : ℝ))/2 ∧
  (Fintype.card (Fin (2^20)) : ℝ)/(modulus : ℝ)^4 <
    (affineGenerator Ext4).pr (fun r =>
      close (1/5 : ℝ) (reedSolomonCode domain (2^19)) (comb r f))

/-- Polynomial witness for the nonconstant member of the actual-carrier line. -/
theorem x_mem : xWord ∈ reedSolomonCode domain (2^19) := by
  apply mem_reedSolomonCode_iff.mpr
  exact ⟨Polynomial.X, by norm_num, fun _ => by simp [xWord]⟩

theorem one_mem : oneWord ∈ reedSolomonCode domain (2^19) := by
  apply mem_reedSolomonCode_iff.mpr
  exact ⟨1,by norm_num,fun _ => by simp [oneWord]⟩

/-- The chosen line has exact probability one, without enumerating Ext4. -/
theorem line_pr_one :
    (affineGenerator Ext4).pr (fun r =>
      close (1/5 : ℝ) (reedSolomonCode domain (2^19)) (comb r pair)) = 1 := by
  classical
  have hall : ∀ z : Ext4,
      close (1/5 : ℝ) (reedSolomonCode domain (2^19))
        (comb ((affineGenerator Ext4).gen z) pair) := by
    intro z
    have heq : comb ((affineGenerator Ext4).gen z) pair = xWord + z • oneWord :=
      funext fun i => by rw [comb_affineGenerator]; rfl
    rw [heq]
    exact close_of_mem ((reedSolomonCode domain (2^19)).add_mem x_mem
      ((reedSolomonCode domain (2^19)).smul_mem z one_mem)) (by norm_num)
  unfold ProximityGenerator.pr
  simp only [hall, Finset.filter_true]
  exact (affineGenerator Ext4).weight_sum_one

/-- All probability-source premises hold together on the real carrier. -/
theorem premise_inhabited : ∃ f, FiringPremise f := by
  refine ⟨pair,by norm_num,by norm_num,?_⟩
  rw [line_pr_one]
  norm_num [modulus]

/-- The exact witness radius is outside the older one-third-UD band. -/
theorem former_band_falsifier :
    ¬ (1/5 : ℝ) < 1-(2+(2^19 : ℝ)/(Fintype.card (Fin (2^20)) : ℝ))/3 := by
  norm_num

end FullUDInstantiation

/-- Universe-polymorphic immediately usable full-UD probability interface. -/
theorem isProximityGenerator_fullUD {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : FullUDRealizer ι := by
  intro dom d hd
  have h := reedSolomonCode_isProximityGenerator_fullUD dom d hd
  have hcard : (Fintype.card Ext4 : ℝ) = (modulus : ℝ)^4 := by
    exact_mod_cast ext4_card
  simpa only [hcard] using h

/-- Immediately usable probability bound at n=2^20, d=2^19, delta=1/5.
The substantive failure-of-common-agreement premise remains explicit. -/
theorem rateHalf_probability_bound (dom : Fin (2^20) ↪ Ext4)
    (f : Fin 2 → Fin (2^20) → Ext4)
    (hnot : ¬ CorrelatedAgreement (reedSolomonCode dom (2^19)) (1/5 : ℝ) f) :
    (affineGenerator Ext4).pr (fun r =>
      close (1/5 : ℝ) (reedSolomonCode dom (2^19)) (comb r f)) ≤
      (2^20 : ℝ)/(modulus : ℝ)^4 := by
  apply le_of_not_gt
  intro hpr
  exact hnot (isProximityGenerator_fullUD dom (2^19) (by norm_num)
    f (1/5 : ℝ) (by norm_num) (by norm_num) (by norm_num at hpr ⊢; exact hpr))

namespace FullUDInstantiation

/-- The concrete realizer fires on the actual carrier at the new radius. -/
theorem good_line_correlatedAgreement :
    CorrelatedAgreement (reedSolomonCode domain (2^19)) (1/5 : ℝ) pair := by
  apply isProximityGenerator_fullUD domain (2^19) (by norm_num)
    pair (1/5 : ℝ) (by norm_num) (by norm_num)
  rw [line_pr_one]
  norm_num [modulus]

def badWord : Fin (2^20) → Ext4 := fun i => (domain i)^(2^19)
def badPair : Fin 2 → Fin (2^20) → Ext4 := ![badWord,0]

/-- The probability-bound premise is inhabited by a degree-exactly-d word:
no degree-below-d codeword explains enough common positions. -/
theorem bad_pair_not_correlatedAgreement :
    ¬ CorrelatedAgreement (reedSolomonCode domain (2^19)) (1/5 : ℝ) badPair := by
  classical
  rintro ⟨S,hScard,hjoint⟩
  obtain ⟨w,hw,hAg⟩ := hjoint 0
  obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hpow_ne : (Polynomial.X^(2^19) : Polynomial Ext4) ≠ p := by
    intro heq
    rw [← heq] at hp
    norm_num at hp
  have hcard := card_agreeSet_lt_of_ne domain (d := 2^19+1)
    (p := (Polynomial.X^(2^19) : Polynomial Ext4))
    (by norm_num) (q := p) (hp.trans (by norm_num)) hpow_ne
  have hsub : S ⊆ Finset.univ.filter (fun i =>
      (Polynomial.X^(2^19) : Polynomial Ext4).eval (domain i) = p.eval (domain i)) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    have h := (hAg i hi).trans (heval i)
    simpa [badPair,badWord] using h
  have hSle : S.card ≤ 2^19 := by
    have h := (Finset.card_le_card hsub).trans_lt hcard
    omega
  have hSle' : (S.card : ℝ) ≤ (2^19 : ℝ) := by exact_mod_cast hSle
  norm_num at hScard
  rw [show (2 : ℝ)^19 = 524288 by norm_num] at hSle'
  linarith only [hScard,hSle']

/-- The actual-carrier probability theorem applies to the explicit bad pair. -/
theorem bad_pair_probability_bound :
    (affineGenerator Ext4).pr (fun r =>
      close (1/5 : ℝ) (reedSolomonCode domain (2^19)) (comb r badPair)) ≤
      (2^20 : ℝ)/(modulus : ℝ)^4 :=
  rateHalf_probability_bound domain badPair bad_pair_not_correlatedAgreement

end FullUDInstantiation

/-- info: 'Minidregg.Selvage.BabyBearExt4.ext4_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ext4_card

/-- info: 'Minidregg.Selvage.BabyBearExt4.base_field_cardinality_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms base_field_cardinality_falsifier

/-- info: 'Minidregg.Selvage.BabyBearExt4.isProximityGenerator_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isProximityGenerator_fullUD

/-- info: 'Minidregg.Selvage.BabyBearExt4.rateHalf_probability_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rateHalf_probability_bound

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.x_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.x_mem

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.one_mem

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.line_pr_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.line_pr_one

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.premise_inhabited

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.former_band_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.former_band_falsifier

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.good_line_correlatedAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.good_line_correlatedAgreement

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.bad_pair_not_correlatedAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.bad_pair_not_correlatedAgreement

/-- info: 'Minidregg.Selvage.BabyBearExt4.FullUDInstantiation.bad_pair_probability_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDInstantiation.bad_pair_probability_bound

end
end Minidregg.Selvage.BabyBearExt4
