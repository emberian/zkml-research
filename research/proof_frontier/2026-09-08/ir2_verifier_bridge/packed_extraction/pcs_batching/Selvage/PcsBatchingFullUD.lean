/- Full unique decoding applied to the actual kind of PCS alpha batching.
Inputs, points and claims are fixed before the one uniform alpha challenge.
This file proves the algebraic bad-alpha count, not a Fiat--Shamir reduction. -/
import Selvage.PcsQuotientAgreement

namespace Minidregg.Selvage.PcsBatching
open Polynomial
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {F ι κ : Type*} [Field F] [DecidableEq F] [Fintype ι]

def Data.JointCard {M : ℕ} (a : Data F ι κ M) (dom : ι ↪ F) (s : F)
    (d e : ℕ) : Prop :=
  ∃ S : Finset ι, Fintype.card ι-e ≤ S.card ∧ a.JointOn dom s d S

/-- More than M*n nearby alpha reductions force a shared set of nearby original
polynomials and consistent opening claims, including all repetitions of a column. -/
theorem jointCard_of_many_close {M d e : ℕ} (a : Data F ι κ M)
    (dom : ι ↪ F) (s : F) (hs : s ≠ 0) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (hradius : 2*e+d ≤ Fintype.card ι) (hstrict : d < Fintype.card ι-e)
    (hoff : a.OffDomain dom s) (A : Finset F)
    (hclose : ∀ α ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (curveWord (a.quotientWord dom s) α) w ≤ e)
    (hcard : M*Fintype.card ι < A.card) : a.JointCard dom s d e := by
  obtain ⟨S,hS,hjoint⟩ := curveFullUDCardCore M dom d e hM hd hradius
    (a.quotientWord dom s) A hclose hcard
  exact ⟨S,hS,jointOn_of_quotient_agreement a dom s hs hd hoff S (hstrict.trans_le hS) hjoint⟩

omit [DecidableEq F] in
theorem shared_set_strict {d : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (S : Finset ι) (hS : (1-δ)*(Fintype.card ι : ℝ) ≤ S.card) : d < S.card := by
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have h : (d : ℝ) < S.card := by nlinarith
  exact_mod_cast h

theorem jointNear_of_many_close [Nonempty ι] {M d : ℕ} {δ : ℝ}
    (a : Data F ι κ M) (dom : ι ↪ F) (s : F) (hs : s ≠ 0) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (hoff : a.OffDomain dom s) (A : Finset F)
    (hclose : ∀ α ∈ A, close δ (reedSolomonCode dom d) (curveWord (a.quotientWord dom s) α))
    (hcard : M*Fintype.card ι < A.card) : a.JointNear dom s d δ := by
  obtain ⟨S,hS,hjoint⟩ := curve_correlatedAgreement_of_many_close M hM dom hd hδ0 hδ2
    (a.quotientWord dom s) A hclose hcard
  exact ⟨S,hS,jointOn_of_quotient_agreement a dom s hs hd hoff S
    (shared_set_strict hδ0 hδ2 S hS) hjoint⟩

/-- The bad-alpha event is closeness of the actual single-scalar polynomial
curve. The coefficient words are fixed independently of alpha. -/
theorem bad_alpha_card_le [Nonempty ι] [Fintype F] {M d : ℕ} {δ : ℝ}
    (a : Data F ι κ M) (dom : ι ↪ F) (s : F) (hs : s ≠ 0) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (hoff : a.OffDomain dom s) (hfar : ¬a.JointNear dom s d δ) :
    (Finset.univ.filter (fun α => close δ (reedSolomonCode dom d)
      (curveWord (a.quotientWord dom s) α))).card ≤ M*Fintype.card ι := by
  by_contra h
  exact hfar (jointNear_of_many_close a dom s hs hM hd hδ0 hδ2 hoff _
    (fun α hα => (Finset.mem_filter.mp hα).2) (Nat.lt_of_not_ge h))

/-- Exact low-degree inputs identify the reconstructed polynomials. Thus the
joint agreement conclusion forces every claim to equal its original evaluation. -/
theorem claims_of_jointOn {M d : ℕ} (a : Data F ι κ M) (dom : ι ↪ F)
    (s : F) (hs : s ≠ 0) (original : κ → F[X])
    (hdegree : ∀ k, (original k).natDegree ≤ d)
    (hsource : ∀ k i, (original k).eval (s*dom i)=a.source k i)
    (S : Finset ι) (hS : d < S.card) (hjoint : a.JointOn dom s d S) :
    ∀ j, a.claim j=(original (a.column j)).eval (a.point j) := by
  obtain ⟨p,hp,_⟩ := hjoint
  intro j
  have heq : p j=original (a.column j) := by
    apply eq_of_common_set (cosetDomain dom s hs) (hp j).1 (hdegree _) S hS
    intro i hi
    exact ((hp j).2.2 i hi).trans (hsource _ i).symm
  rw [←heq]
  exact (hp j).2.1.symm

/-- A false claim for an already exact input gives the needed batching-farness
failure predicate; no polynomial-agreement premise is smuggled into this step. -/
theorem not_jointNear_of_wrong_claim {M d : ℕ} {δ : ℝ}
    (a : Data F ι κ M) (dom : ι ↪ F) (s : F) (hs : s ≠ 0)
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (original : κ → F[X]) (hdegree : ∀ k, (original k).natDegree ≤ d)
    (hsource : ∀ k i, (original k).eval (s*dom i)=a.source k i)
    (j : Fin (M+1)) (hwrong : a.claim j ≠ (original (a.column j)).eval (a.point j)) :
    ¬a.JointNear dom s d δ := by
  rintro ⟨S,hS,hjoint⟩
  exact hwrong (claims_of_jointOn a dom s hs original hdegree hsource S
    (shared_set_strict hδ0 hδ2 S hS) hjoint j)

theorem bad_alpha_card_of_wrong_claim [Nonempty ι] [Fintype F] {M d : ℕ} {δ : ℝ}
    (a : Data F ι κ M) (dom : ι ↪ F) (s : F) (hs : s ≠ 0) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (hδ0 : 0 < δ) (hδ2 : (d : ℝ) < (1-2*δ)*(Fintype.card ι : ℝ))
    (hoff : a.OffDomain dom s) (original : κ → F[X])
    (hdegree : ∀ k, (original k).natDegree ≤ d)
    (hsource : ∀ k i, (original k).eval (s*dom i)=a.source k i)
    (j : Fin (M+1)) (hwrong : a.claim j ≠ (original (a.column j)).eval (a.point j)) :
    (Finset.univ.filter (fun α => close δ (reedSolomonCode dom d)
      (curveWord (a.quotientWord dom s) α))).card ≤ M*Fintype.card ι :=
  bad_alpha_card_le a dom s hs hM hd hδ0 hδ2 hoff
    (not_jointNear_of_wrong_claim a dom s hs hδ0 hδ2 original hdegree hsource j hwrong)

/- Exact dependencies of every theorem in this module. -/

/-- info: 'Minidregg.Selvage.PcsBatching.jointCard_of_many_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.jointCard_of_many_close

/-- info: 'Minidregg.Selvage.PcsBatching.shared_set_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.shared_set_strict

/-- info: 'Minidregg.Selvage.PcsBatching.jointNear_of_many_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.jointNear_of_many_close

/-- info: 'Minidregg.Selvage.PcsBatching.bad_alpha_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.bad_alpha_card_le

/-- info: 'Minidregg.Selvage.PcsBatching.claims_of_jointOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.claims_of_jointOn

/-- info: 'Minidregg.Selvage.PcsBatching.not_jointNear_of_wrong_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.not_jointNear_of_wrong_claim

/-- info: 'Minidregg.Selvage.PcsBatching.bad_alpha_card_of_wrong_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.bad_alpha_card_of_wrong_claim

end
end Minidregg.Selvage.PcsBatching
