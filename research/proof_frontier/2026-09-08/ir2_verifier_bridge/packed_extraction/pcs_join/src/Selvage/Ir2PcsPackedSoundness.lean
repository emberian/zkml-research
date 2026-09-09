/- Actual one-height PCS alpha reduction composed with arbitrary canonical
packed supplied openings. Input commitment checkpoints, points and claims precede
alpha; FRI checkpoints follow alpha and their own beta prefix. Fresh challenges,
observed hash extraction failure and native-code correspondence remain separate. -/
import Selvage.Ir2PcsBatching
import Selvage.Ir2PackedSoundness

namespace Minidregg.Selvage.Ir2Fri.Pcs
open BabyBearExt4 Ir2FriSchedule Packed Polynomial
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Only the FRI checkpoints may depend on alpha. Actual input roots, point
claims and input checkpoint logs are fixed first. -/
structure CommitmentPlan (Digest : Type) where
  input : Fin 5 → Packed.Checkpoint Digest
  points : Points
  claims : Claims
  fri : Ext4 → (j : Fin 5) → (Fin j.val → Ext4) → Packed.Checkpoint Digest
  final : Ext4 → (Fin 5 → Ext4) → Ext4

variable {Digest : Type} [DecidableEq Digest]

def CommitmentPlan.atAlpha (s : CommitmentPlan Digest) (α : Ext4) : Packed.Checkpoints Digest where
  input := s.input
  fri := s.fri α
  final := s.final α
  reduction := reduction s.points s.claims α

/-- The base-field rows are extracted once, before alpha, from fixed input logs. -/
def CommitmentPlan.rows (s : CommitmentPlan Digest) : Index 0 → AllInputRows :=
  fun i => inputRowsAt (s.atAlpha 0) (sourceEquiv.symm i)

theorem inputRows_alpha_independent (s : CommitmentPlan Digest) (α : Ext4) (i : Index 0) :
    inputRowsAt (s.atAlpha α) (sourceEquiv.symm i)=s.rows i := rfl

theorem extracted_input_reduction (s : CommitmentPlan Digest) (α : Ext4) :
    (extracted (s.atAlpha α)).input = fun i => reduction s.points s.claims α i (s.rows i) := rfl

abbrev ChallengeSpace := Ext4 × Packed.External 38

def Accepted (H : BinaryMerkle.HashSuite Leaf Digest) (s : CommitmentPlan Digest)
    (o : ChallengeSpace → Openings Digest 38) (x : ChallengeSpace) : Prop :=
  Packed.FreshAccepts H (s.atAlpha x.1) 38 x.2 (o x)

def ObservedFailure (H : BinaryMerkle.HashSuite Leaf Digest) (s : CommitmentPlan Digest)
    (o : ChallengeSpace → Openings Digest 38) (P : ChallengeSpace → Packed.Log Digest)
    (x : ChallengeSpace) : Prop :=
  Packed.observedFailure H (s.atAlpha x.1) 38 x.2 (o x) (P x)

/-- Statement-first actual PCS/packed theorem. The arbitrary reduction and
reduced-input farness premises have been replaced by fixed actual points/claims
and failure of their common nearby physical-polynomial explanation. -/
def PackedPcsSoundness : Prop :=
  ∀ (H : BinaryMerkle.HashSuite Leaf Digest) (s : CommitmentPlan Digest)
    (o : ChallengeSpace → Openings Digest 38) (P : ChallengeSpace → Packed.Log Digest),
    (∀ x,CheckpointsLogged (s.atAlpha x.1) x.2.1 (P x)) →
    (data s.rows s.points s.claims).OffDomain (domain 0) 31 →
    ¬JointColumnsNear s.rows s.points s.claims (degree 0) (2/5) →
    uniformProb ChallengeSpace (Accepted H s o) ≤
      (690880504:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38+
      uniformProb ChallengeSpace (ObservedFailure H s o P)

/-- Arbitrary canonically typed supplied proofs under fresh alpha, five fresh
Ext4 betas, and the actual38 base-word query distribution. -/
theorem packed_pcs_soundness : PackedPcsSoundness (Digest := Digest) := by
  intro H s o P hP hoff hbad
  let near : Ext4 → Prop := fun α =>
    close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) (extracted (s.atAlpha α)).input
  let ideal : ChallengeSpace → Prop := fun x => ¬near x.1 ∧
    NativeFreshAccepts (extracted (s.atAlpha x.1)) 38 x.2.1 x.2.2
  let bad := ObservedFailure H s o P
  have hn : uniformProb ChallengeSpace (fun x => near x.1) ≤
      (690749440:ℝ)/(modulus^4:ℕ) := by
    have hs := uniformProb_equiv (Equiv.prodComm Ext4 (Packed.External 38))
      (fun x => near x.2)
    simp only [Equiv.prodComm_apply,Prod.swap] at hs
    rw [hs,uniformProb_prod_snd]
    simpa only [near,extracted_input_reduction] using
      actual_bad_alpha_probability s.rows s.points s.claims hoff hbad
  have hi : uniformProb ChallengeSpace ideal ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38 := by
    apply uniformProb_prod_le (by positivity)
    intro α
    by_cases hf : near α
    · rw [uniformProb_false (fun _ h => h.1 hf)]
      positivity
    · exact (uniformProb_mono fun _ h => h.2).trans (native_fresh_38 (extracted (s.atAlpha α)) hf)
  have hc : ∀ x, Accepted H s o x → near x.1 ∨ (ideal x ∨ bad x) := by
    intro x hx
    by_cases hn : near x.1
    · exact Or.inl hn
    · have h := supplied_cover H (s.atAlpha x.1) 38 x.2.1 (rawQueries x.2)
        (o x) (P x) (hP x) hx
      exact Or.inr (h.elim (fun h => Or.inl ⟨hn,h⟩) Or.inr)
  have h := ((uniformProb_mono hc).trans (uniformProb_or_le _ _)).trans
    (add_le_add hn (uniformProb_or_le ideal bad))
  have h' := h.trans (add_le_add le_rfl (add_le_add hi le_rfl))
  calc
    _ ≤ (690749440:ℝ)/(modulus^4:ℕ)+
        ((131064:ℝ)/(modulus^4:ℕ)+
          ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38+
          uniformProb ChallengeSpace bad) := h'
    _ = _ := by dsimp only [bad]; ring

/-- The common-column conclusion is also the generic quotient theorem's
joint conclusion; this direction allows exact source polynomials to identify it. -/
theorem joint_data_of_columns (rows : Index 0 → AllInputRows) (points : Points)
    (claims : Claims) {d : ℕ} {δ : ℝ}
    (h : JointColumnsNear rows points claims d δ) :
    (data rows points claims).JointNear (domain 0) 31 d δ := by
  obtain ⟨S,hS,p,hp,hclaims⟩ := h
  refine ⟨S,hS,(fun j => p (termAt j).key),?_,?_⟩
  · intro j
    exact ⟨(hp _).1,hclaims _,(hp _).2⟩
  · intro j k hkey
    exact congrArg p hkey

/-- A false claimed opening of already exact low-degree extracted columns
rules out the joint nearby explanation. The degree cap is ≤16384, explicitly. -/
theorem not_joint_columns_of_wrong_claim (rows : Index 0 → AllInputRows)
    (points : Points) (claims : Claims) (original : Column → Ext4[X])
    (hdegree : ∀ k, (original k).natDegree ≤ degree 0)
    (hsource : ∀ k i, (original k).eval (31*domain 0 i)=
      algebraMap BabyBear Ext4 (rows i k.1 k.2.1 k.2.2))
    (t : Term) (hwrong : claims t.batch t.matrix t.point t.column ≠
      (original t.key).eval (points t.batch t.matrix t.point)) :
    ¬JointColumnsNear rows points claims (degree 0) (2/5) := by
  obtain ⟨j,rfl⟩ := term_covered t
  exact fun h => PcsBatching.not_jointNear_of_wrong_claim (data rows points claims)
    (domain 0) 31 coset31_ne_zero batching_parameters.2.2.1 batching_parameters.2.2.2.1
    original hdegree hsource j hwrong (joint_data_of_columns rows points claims h)

/-- Concrete false-opening corollary for exact extracted source polynomials.
Exact source membership remains stated here; the general head above needs only
the absence of a common nearby explanation and does not assume source membership. -/
theorem packed_pcs_false_claim_sound (H : BinaryMerkle.HashSuite Leaf Digest)
    (s : CommitmentPlan Digest) (o : ChallengeSpace → Openings Digest 38)
    (P : ChallengeSpace → Packed.Log Digest)
    (hP : ∀ x,CheckpointsLogged (s.atAlpha x.1) x.2.1 (P x))
    (hoff : (data s.rows s.points s.claims).OffDomain (domain 0) 31)
    (original : Column → Ext4[X])
    (hdegree : ∀ k, (original k).natDegree ≤ degree 0)
    (hsource : ∀ k i, (original k).eval (31*domain 0 i)=
      algebraMap BabyBear Ext4 (s.rows i k.1 k.2.1 k.2.2))
    (t : Term) (hwrong : s.claims t.batch t.matrix t.point t.column ≠
      (original t.key).eval (s.points t.batch t.matrix t.point)) :
    uniformProb ChallengeSpace (Accepted H s o) ≤
      (690880504:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38+
      uniformProb ChallengeSpace (ObservedFailure H s o P) :=
  packed_pcs_soundness H s o P hP hoff
    (not_joint_columns_of_wrong_claim s.rows s.points s.claims original hdegree hsource t hwrong)

end
end Minidregg.Selvage.Ir2Fri.Pcs

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.inputRows_alpha_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.inputRows_alpha_independent

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.extracted_input_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.extracted_input_reduction

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.packed_pcs_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.packed_pcs_soundness

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.joint_data_of_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.joint_data_of_columns

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.not_joint_columns_of_wrong_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.not_joint_columns_of_wrong_claim

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.packed_pcs_false_claim_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.packed_pcs_false_claim_sound

