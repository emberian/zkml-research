/- Selected nearby columns before zeta: source exact-codeword membership is absent. -/
import Compiler.Ir2NearbyColumns

namespace Minidregg.Compiler.Ir2NearbyColumns
open Polynomial Minidregg.Selvage BabyBearExt4 Ir2Fri Ir2FriSchedule Packed Pcs AirPolynomialOod Ir2AirPcsOod
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Commitment-time rows may depend on gamma (the quotient commit does), but
not on zeta. The mathematical selected polynomial reads only these fixed rows. -/
structure SelectedPlan where
  rows : Ext4 → Index 0 → AllInputRows
  scale : Pcs.Term → Ext4
  expression : Ext4 → Expr

def SelectedPlan.equation (a : SelectedPlan) : EquationPlan where
  physical γ := selected (a.rows γ)
  scale := a.scale
  expression := a.expression

variable {Digest : Type} [DecidableEq Digest]

/-- Statement-first application bound from arbitrary fixed commitment words.
No assertion says the LDE word is exactly the selected polynomial. The application
row is a value of that polynomial, not an unproved decoding of every LDE cell. -/
def SelectedAirPcsSoundness : Prop :=
  ∀ (H : BinaryMerkle.HashSuite Leaf Digest) (M D : ℕ)
    (constraints : Fin (M+1) → Ext4[X]) (vanishing : Ext4[X])
    (quotient : Ext4 → Ext4[X]) (r : Ext4) (a : SelectedPlan)
    (s : AirCoins → CommitmentPlan Digest)
    (o : AllCoins → Openings Digest 38) (P : AllCoins → Packed.Log Digest),
    vanishing.eval r=0 → (∃ j,(constraints j).eval r ≠ 0) →
    (∀ γ,(residual constraints vanishing quotient γ).natDegree ≤ D) →
    (∀ γ,equationPoly (a.equation.physical γ) a.equation.scale (a.equation.expression γ)=residual constraints vanishing quotient γ) →
    (∀ x t,(s x).points t.batch t.matrix t.point=a.equation.scale t*x.2) →
    (∀ x,(s x).rows=a.rows x.1) →
    (∀ x,CheckpointsLogged ((s x.1).atAlpha x.2.1) x.2.2.1 (P x)) →
    uniformProb AllCoins (fun x => AirAccepted a.equation s x.1 ∧ Accepted H (s x.1) (fun y => o (x.1,y)) x.2) ≤
      (M:ℝ)/Fintype.card Ext4+(D:ℝ)/Fintype.card Ext4+pcsError+
      uniformProb AllCoins (BoundaryFailure H s o P)

theorem selected_air_pcs_soundness : SelectedAirPcsSoundness (Digest := Digest) := by
  intro H M D constraints vanishing quotient r a s o P hr hbad hdeg heq hpoints hrows hP
  let rz : AirCoins → Prop := fun x => (residual constraints vanishing quotient x.1).eval x.2=0
  let failure : AllCoins → Prop := BoundaryFailure H s o P
  let good : AllCoins → Prop := fun x => ¬rz x.1 ∧ AirAccepted a.equation s x.1 ∧
    Accepted H (s x.1) (fun y => o (x.1,y)) x.2 ∧ ¬failure x
  have hz : uniformProb AllCoins (fun x => rz x.1) ≤
      (M:ℝ)/Fintype.card Ext4+(D:ℝ)/Fintype.card Ext4 := by
    have hs := uniformProb_equiv (Equiv.prodComm AirCoins ChallengeSpace) (fun x => rz x.2)
    simp only [Equiv.prodComm_apply,Prod.swap] at hs
    rw [hs,uniformProb_prod_snd]
    exact ood_soundness M D constraints vanishing quotient r hr hbad hdeg
  have hg : uniformProb AllCoins good ≤ pcsError := by
    apply uniformProb_prod_le (by unfold pcsError; positivity)
    intro x
    by_cases ha : AirAccepted a.equation s x
    · by_cases hz : rz x
      · rw [uniformProb_false (fun _ h => h.1 hz)]
        unfold pcsError; positivity
      · have hp : (equationPoly (a.equation.physical x.1) a.equation.scale (a.equation.expression x.1)).eval x.2 ≠ 0 := by
          rwa [heq]
        obtain ⟨t,ht⟩ := wrong_opening_of_expression (a.equation.physical x.1) a.equation.scale (s x).points (s x).claims x.2
          (a.equation.expression x.1) (hpoints x) ha hp
        have hb : ¬JointColumnsNear (s x).rows (s x).points (s x).claims (degree 0) (2/5) := by
          rw [hrows]
          exact not_joint_of_wrong_selected_claim (a.rows x.1) (s x).points (s x).claims t ht
        by_cases hoff : (data (s x).rows (s x).points (s x).claims).OffDomain (domain 0) 31
        · exact (uniformProb_mono fun _ h => ⟨h.2.2.1,fun hf => h.2.2.2 (Or.inl hf)⟩).trans
            (pcs_without_failure H (s x) (fun y => o (x,y)) (fun y => P (x,y)) (fun y => hP (x,y)) hoff hb)
        · rw [uniformProb_false (fun _ h => h.2.2.2 (Or.inr hoff))]
          unfold pcsError; positivity
    · rw [uniformProb_false (fun _ h => ha h.2.1)]
      unfold pcsError; positivity
  have hc : ∀ x : AllCoins,AirAccepted a.equation s x.1 ∧ Accepted H (s x.1) (fun y => o (x.1,y)) x.2 →
      rz x.1 ∨ (good x ∨ failure x) := by
    intro x hx
    by_cases hz : rz x.1
    · exact Or.inl hz
    · by_cases hf : failure x
      · exact Or.inr (Or.inr hf)
      · exact Or.inr (Or.inl ⟨hz,hx.1,hx.2,hf⟩)
  have h := ((uniformProb_mono hc).trans (uniformProb_or_le _ _)).trans
    (add_le_add hz ((uniformProb_or_le good failure).trans (add_le_add hg le_rfl)))
  simpa only [add_assoc] using h


end
end Minidregg.Compiler.Ir2NearbyColumns

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.selected_air_pcs_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.selected_air_pcs_soundness

