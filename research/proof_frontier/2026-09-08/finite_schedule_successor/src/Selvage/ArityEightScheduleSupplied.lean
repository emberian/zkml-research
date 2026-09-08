/- Finite prefix-adaptive checkpoint extraction and actual supplied-row reduction.
The execution log may depend on all challenges and queries. Each checkpoint
root/log and input word depends only on the permitted challenge prefix. -/
import Selvage.ArityEightSchedule
import Selvage.ArityEightSupplied

namespace Minidregg.Selvage.ArityEight.Schedule
open scoped Classical

structure Checkpoints (F Digest : Type) where
  word : ∀ n, (Fin n → F) → (EfficientRootOpening.Log F Digest × Digest)
  input : ∀ n, (Fin n → F) → (EfficientRootOpening.Log F Digest × Digest)

section Extraction
variable {F Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest] {ell m : ℕ}

def extracted (st : Checkpoints F Digest) (default : F) : Words F (PowerTwoFriLevels ell) where
  word n p := EfficientRootOpening.word (st.word n p).1 default (ell-3*n) (st.word n p).2
  input n p := EfficientRootOpening.word (st.input n p).1 default (ell-3*(n+1)) (st.input n p).2

def CheckpointsLogged (st : Checkpoints F Digest) (L : EfficientRootOpening.Log F Digest)
    (r : Fin m → F) : Prop :=
  (∀ n (hn : n ≤ m), ∀ e ∈ (st.word n (friPrefix r n hn)).1, e ∈ L) ∧
  (∀ j : Fin m, ∀ e ∈ (st.input j (friPrefix r j (by omega))).1, e ∈ L)

def Failure (st : Checkpoints F Digest) (L : EfficientRootOpening.Log F Digest) (r : Fin m → F) : Prop :=
  ∃ j : Fin m,
    let src := st.word j (friPrefix r j (by omega))
    let inp := st.input j (friPrefix r j (by omega))
    let dst := st.word (j+1) (friPrefix r (j+1) (by omega))
    RoundBad src.1 inp.1 dst.1 L src.2 inp.2 dst.2

abbrev Openings (F Digest : Type) (m q : ℕ) := Fin m → Fin q → RowOpening F Digest

def SuppliedAccepts (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (default : F) (deg : ℕ → ℕ) (q : ℕ) (hell : 3*m ≤ ell)
    (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1) (o : Openings F Digest m q) : Prop :=
  (extracted st default).wordAt r m le_rfl ∈ reedSolomonCode (T.dom (3*m)) (deg m) ∧
  ∀ j : Fin m, ∀ a,
    RowVerified H (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
      (T.data (3*j.val+2) (by omega))
      (st.word j (friPrefix r j (by omega))).2
      (st.input j (friPrefix r j (by omega))).2
      (st.word (j+1) (friPrefix r (j+1) (by omega))).2
      (r j) (roundQueries hell j seed a) (o j a)

def OpeningsLogged (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (L : EfficientRootOpening.Log F Digest)
    (q : ℕ) (hell : 3*m ≤ ell) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest m q) : Prop :=
  ∀ j : Fin m, ∀ a,
    RowLogged H L (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
      (T.data (3*j.val+2) (by omega)) (roundQueries hell j seed a) (o j a)

/-- Every shared intermediate checkpoint is extracted once at its prefix.
All accepted supplied transitions pin off the observed finite-log failure. -/
theorem supplied_cover (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (default : F) (deg : ℕ → ℕ) (q : ℕ) (hell : 3*m ≤ ell)
    (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1) (o : Openings F Digest m q)
    (L : EfficientRootOpening.Log F Digest)
    (hsub : CheckpointsLogged st L r) (hlog : OpeningsLogged H T L q hell seed o)
    (ha : SuppliedAccepts H T st default deg q hell r seed o) :
    Accepts T (extracted st default) deg q hell r seed ∨ Failure st L r := by
  by_cases hb : Failure st L r
  · exact Or.inr hb
  · refine Or.inl ⟨ha.1,?_⟩
    intro j a
    exact supplied_row_pins H (T.data (3*j.val) (by omega))
      (T.data (3*j.val+1) (by omega)) (T.data (3*j.val+2) (by omega))
      (st.word j (friPrefix r j (by omega))).1 (st.input j (friPrefix r j (by omega))).1
      (st.word (j+1) (friPrefix r (j+1) (by omega))).1 L default
      (st.word j (friPrefix r j (by omega))).2 (st.input j (friPrefix r j (by omega))).2
      (st.word (j+1) (friPrefix r (j+1) (by omega))).2
      (hsub.1 j (by omega)) (hsub.2 j) (hsub.1 (j+1) (by omega))
      (fun h => hb ⟨j,h⟩) (r j) (roundQueries hell j seed a) (o j a) (hlog j a) (ha.2 j a)

set_option maxHeartbeats 800000 in
/-- Finite prefix-adaptive supplied-row soundness: the actual challenge sum,
one coherent-query tail, and the retained observed-log failure event. -/
theorem supplied_sound [Fintype F] (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (default : F) (deg : ℕ → ℕ) (radius : ℕ → ℝ) (q : ℕ) (hell : 3*m ≤ ell) {τ : ℝ}
    (hd : ∀ j : Fin m, 1 ≤ deg (j+1)) (hdeg : ∀ j : Fin m, deg j = 8*deg (j+1))
    (hρ : ∀ j : Fin m, 0 < radius j) (hτ : τ ≤ 1) (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j+1)+τ ≤ radius j)
    (hrate : ∀ j : Fin m, (deg (j+1):ℝ) < (1-2*radius j)*
      (Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℝ))
    (openings : (Fin m → F) × (Fin q → PowerTwoFriLevels ell 1) → Openings F Digest m q)
    (logs : (Fin m → F) × (Fin q → PowerTwoFriLevels ell 1) → EfficientRootOpening.Log F Digest)
    (hsub : ∀ x, CheckpointsLogged st (logs x) x.1)
    (hlog : ∀ x, OpeningsLogged H T (logs x) q hell x.2 (openings x))
    (hfar : EfficientRootOpening.Far_E (radius 0) ell (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0)).1 default (st.word 0 (fun i => i.elim0)).2) :
    uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1))
      (fun x => SuppliedAccepts H T st default deg q hell x.1 x.2 (openings x)) ≤
      (∑ j : Fin m, ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F) +
      (1-τ)^q + uniformProb ((Fin m → F) × (Fin q → PowerTwoFriLevels ell 1))
        (fun x => Failure st (logs x) x.1) := by
  let Ω := (Fin m → F) × (Fin q → PowerTwoFriLevels ell 1)
  let ideal : Ω → Prop := fun x => Accepts T (extracted st default) deg q hell x.1 x.2
  let raw : Ω → Prop := fun x => SuppliedAccepts H T st default deg q hell x.1 x.2 (openings x)
  let bad : Ω → Prop := fun x => Failure st (logs x) x.1
  have hf : ¬close (radius 0) (reedSolomonCode (T.dom 0) (deg 0))
      ((extracted st default).word 0 (fun i => i.elim0)) := hfar
  have h : uniformProb Ω ideal ≤
      (∑ j : Fin m, ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F)+(1-τ)^q :=
    sound T (extracted st default) deg radius q hell hd hdeg hρ hτ hfinal hgap hrate hf
  have hcover : ∀ x : Ω, raw x → ideal x ∨ bad x := by
    intro x hx
    exact supplied_cover H T st default deg q hell x.1 x.2 (openings x) (logs x) (hsub x) (hlog x) hx
  have hsplit : uniformProb Ω raw ≤ uniformProb Ω ideal + uniformProb Ω bad :=
    le_trans (uniformProb_mono hcover) (uniformProb_or_le ideal bad)
  change uniformProb Ω raw ≤ _
  linarith

end Extraction
end Minidregg.Selvage.ArityEight.Schedule

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.supplied_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.supplied_cover

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.supplied_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.supplied_sound
