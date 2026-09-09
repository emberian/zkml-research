/- AIR polynomial/OOD check joined to the actual packed PCS, with exact source
polynomial membership still explicit. Opening points, claims and logs precede
PCS alpha. The AIR quotient family is fixed before zeta. -/
import Compiler.AirPolynomialOod

namespace Minidregg.Compiler.Ir2AirPcsOod
open Polynomial Minidregg.Selvage BabyBearExt4 Ir2Fri Ir2FriSchedule Packed Pcs AirPolynomialOod
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Expr := Compiler.Term (AirSig Ext4 (Option Pcs.Term))

def opened (claims : Claims) (ζ : Ext4) : Option Pcs.Term → Ext4
  | none => ζ
  | some t => claims t.batch t.matrix t.point t.column

def columnPolys (p : Column → Ext4[X]) (scale : Pcs.Term → Ext4) : Option Pcs.Term → Ext4[X]
  | none => X
  | some t => (p t.key).comp (C (scale t)*X)

/-- Exact opening-expression polynomial produced by the existing arithmetic fold. -/
def equationPoly (p : Column → Ext4[X]) (scale : Pcs.Term → Ext4) (e : Expr) : Ext4[X] :=
  lift (RingHom.id Ext4) (columnPolys p scale) e

/-- The claimed expression can differ from its polynomial reading only at a false opening. -/
theorem wrong_opening_of_expression (p : Column → Ext4[X]) (scale : Pcs.Term → Ext4)
    (points : Points) (claims : Claims) (ζ : Ext4) (e : Expr)
    (hpoints : ∀ t : Pcs.Term,points t.batch t.matrix t.point=scale t*ζ)
    (haccept : eval (opened claims ζ) e=0)
    (hpoly : (equationPoly p scale e).eval ζ ≠ 0) :
    ∃ t : Pcs.Term,claims t.batch t.matrix t.point t.column ≠
      (p t.key).eval (points t.batch t.matrix t.point) := by
  by_contra h
  push Not at h
  apply hpoly
  rw [equationPoly,lift_eval]
  have he : (fun i => (columnPolys p scale i).eval ζ)=opened claims ζ := by
    funext i
    cases i with
    | none => simp [columnPolys,opened]
    | some t => simpa [columnPolys,opened,hpoints t] using (h t).symm
  rw [he,read_id]
  exact haccept

variable {Digest : Type} [DecidableEq Digest]

def pcsError : ℝ := (690880504:ℝ)/(modulus^4:ℕ)+
  ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38

/-- The frozen PCS event with observed extraction failure excluded has the
same numerical PCS/FRI bound. No probability for the deployed hash is inserted. -/
theorem pcs_without_failure (H : BinaryMerkle.HashSuite Leaf Digest)
    (s : CommitmentPlan Digest) (o : ChallengeSpace → Openings Digest 38)
    (P : ChallengeSpace → Packed.Log Digest)
    (hP : ∀ x,CheckpointsLogged (s.atAlpha x.1) x.2.1 (P x))
    (hoff : (data s.rows s.points s.claims).OffDomain (domain 0) 31)
    (hbad : ¬JointColumnsNear s.rows s.points s.claims (degree 0) (2/5)) :
    uniformProb ChallengeSpace (fun x => Accepted H s o x ∧ ¬ObservedFailure H s o P x) ≤ pcsError := by
  let near : Ext4 → Prop := fun α =>
    close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) (extracted (s.atAlpha α)).input
  let ideal : ChallengeSpace → Prop := fun x => ¬near x.1 ∧
    NativeFreshAccepts (extracted (s.atAlpha x.1)) 38 x.2.1 x.2.2
  have hn : uniformProb ChallengeSpace (fun x => near x.1) ≤ (690749440:ℝ)/(modulus^4:ℕ) := by
    have hs := uniformProb_equiv (Equiv.prodComm Ext4 (Packed.External 38)) (fun x => near x.2)
    simp only [Equiv.prodComm_apply,Prod.swap] at hs
    rw [hs,uniformProb_prod_snd]
    simpa only [near,extracted_input_reduction] using actual_bad_alpha_probability s.rows s.points s.claims hoff hbad
  have hi : uniformProb ChallengeSpace ideal ≤ (131064:ℝ)/(modulus^4:ℕ)+
      ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38 := by
    apply uniformProb_prod_le (by positivity)
    intro α
    by_cases hf : near α
    · rw [uniformProb_false (fun _ h => h.1 hf)]; positivity
    · exact (uniformProb_mono fun _ h => h.2).trans (native_fresh_38 (extracted (s.atAlpha α)) hf)
  have hc : ∀ x,Accepted H s o x ∧ ¬ObservedFailure H s o P x → near x.1 ∨ ideal x := by
    intro x hx
    by_cases hn : near x.1
    · exact Or.inl hn
    · have h := supplied_cover H (s.atAlpha x.1) 38 x.2.1 (rawQueries x.2) (o x) (P x) (hP x) hx.1
      exact Or.inr ⟨hn,h.resolve_right hx.2⟩
  have h := ((uniformProb_mono hc).trans (uniformProb_or_le _ _)).trans (add_le_add hn hi)
  calc
    _ ≤ (690749440:ℝ)/(modulus^4:ℕ)+((131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38) := h
    _ = pcsError := by unfold pcsError; ring

abbrev AirCoins := Ext4×Ext4
abbrev AllCoins := AirCoins×ChallengeSpace

/-- Exact source columns and quotient-derived expression are indexed by gamma
only. In particular neither can be selected after the OOD point is sampled. -/
structure EquationPlan where
  physical : Ext4 → Column → Ext4[X]
  scale : Pcs.Term → Ext4
  expression : Ext4 → Expr

def AirAccepted (a : EquationPlan) (s : AirCoins → CommitmentPlan Digest)
    (x : AirCoins) : Prop := eval (opened (s x).claims x.2) (a.expression x.1)=0

/-- Two distinct boundary failures: shaped hash extraction, or a PCS opening
point on its committed LDE coset. The latter is retained as an event, not the
impossible requirement that every uniform zeta avoid the coset. -/
def BoundaryFailure (H : BinaryMerkle.HashSuite Leaf Digest)
    (s : AirCoins → CommitmentPlan Digest) (o : AllCoins → Openings Digest 38)
    (P : AllCoins → Packed.Log Digest) (x : AllCoins) : Prop :=
  ObservedFailure H (s x.1) (fun y => o (x.1,y)) (fun y => P (x.1,y)) x.2 ∨
    ¬(data (s x.1).rows (s x.1).points (s x.1).claims).OffDomain (domain 0) 31

/-- Statement-first composed application-equation bound. This proves a concrete
AIR-expression-to-false-PCS-opening reduction, not native AIR serialization,
lookup extraction, or exact codeword membership of arbitrary commitment logs. -/
def AirPcsSoundness : Prop :=
  ∀ (H : BinaryMerkle.HashSuite Leaf Digest) (M D : ℕ)
    (constraints : Fin (M+1) → Ext4[X]) (vanishing : Ext4[X])
    (quotient : Ext4 → Ext4[X]) (r : Ext4) (a : EquationPlan)
    (s : AirCoins → CommitmentPlan Digest)
    (o : AllCoins → Openings Digest 38) (P : AllCoins → Packed.Log Digest),
    vanishing.eval r=0 → (∃ j,(constraints j).eval r ≠ 0) →
    (∀ γ,(residual constraints vanishing quotient γ).natDegree ≤ D) →
    (∀ γ,equationPoly (a.physical γ) a.scale (a.expression γ)=residual constraints vanishing quotient γ) →
    (∀ x t,(s x).points t.batch t.matrix t.point=a.scale t*x.2) →
    (∀ γ k,(a.physical γ k).natDegree ≤ degree 0) →
    (∀ x k i,(a.physical x.1 k).eval (31*domain 0 i)=
      algebraMap BabyBear Ext4 ((s x).rows i k.1 k.2.1 k.2.2)) →
    (∀ x,CheckpointsLogged ((s x.1).atAlpha x.2.1) x.2.2.1 (P x)) →
    uniformProb AllCoins (fun x => AirAccepted a s x.1 ∧ Accepted H (s x.1) (fun y => o (x.1,y)) x.2) ≤
      (M:ℝ)/Fintype.card Ext4+(D:ℝ)/Fintype.card Ext4+pcsError+
      uniformProb AllCoins (BoundaryFailure H s o P)

theorem air_pcs_soundness : AirPcsSoundness (Digest := Digest) := by
  intro H M D constraints vanishing quotient r a s o P hr hbad hdeg heq hpoints hpdeg hsource hP
  let rz : AirCoins → Prop := fun x => (residual constraints vanishing quotient x.1).eval x.2=0
  let failure : AllCoins → Prop := BoundaryFailure H s o P
  let good : AllCoins → Prop := fun x => ¬rz x.1 ∧ AirAccepted a s x.1 ∧
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
    by_cases ha : AirAccepted a s x
    · by_cases hz : rz x
      · rw [uniformProb_false (fun _ h => h.1 hz)]
        unfold pcsError; positivity
      · have hp : (equationPoly (a.physical x.1) a.scale (a.expression x.1)).eval x.2 ≠ 0 := by
          rwa [heq]
        obtain ⟨t,ht⟩ := wrong_opening_of_expression (a.physical x.1) a.scale (s x).points (s x).claims x.2
          (a.expression x.1) (hpoints x) ha hp
        have hb := not_joint_columns_of_wrong_claim (s x).rows (s x).points (s x).claims
          (a.physical x.1) (hpdeg x.1) (hsource x) t ht
        by_cases hoff : (data (s x).rows (s x).points (s x).claims).OffDomain (domain 0) 31
        · exact (uniformProb_mono fun _ h => ⟨h.2.2.1,fun hf => h.2.2.2 (Or.inl hf)⟩).trans
            (pcs_without_failure H (s x) (fun y => o (x,y)) (fun y => P (x,y)) (fun y => hP (x,y)) hoff hb)
        · rw [uniformProb_false (fun _ h => h.2.2.2 (Or.inr hoff))]
          unfold pcsError; positivity
    · rw [uniformProb_false (fun _ h => ha h.2.1)]
      unfold pcsError; positivity
  have hc : ∀ x : AllCoins,AirAccepted a s x.1 ∧ Accepted H (s x.1) (fun y => o (x.1,y)) x.2 →
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
end Minidregg.Compiler.Ir2AirPcsOod

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.wrong_opening_of_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.wrong_opening_of_expression

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.pcs_without_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.pcs_without_failure

/-- info: 'Minidregg.Compiler.Ir2AirPcsOod.air_pcs_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2AirPcsOod.air_pcs_soundness

