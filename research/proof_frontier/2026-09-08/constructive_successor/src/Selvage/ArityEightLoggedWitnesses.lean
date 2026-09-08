/- End-to-end finite supplied-path witness. The tree-valued digest is an
explicit injective toy hash, not a cryptographic assumption or runtime hash. -/
import Selvage.ArityEightSupplied
import Selvage.ArityEightWitnesses

namespace Minidregg.Selvage.ArityEight.Witnesses.Logged
open scoped Classical

inductive Digest where
  | leaf : F → Digest
  | node : Digest → Digest → Digest
  deriving DecidableEq

def H : BinaryMerkle.HashSuite F Digest := ⟨Digest.leaf,Digest.node⟩

def honestPoint (k : ℕ) (f : Fin (2^k) → F) (i : Fin (2^k)) : PointOpening F Digest :=
  ⟨f i,(BinaryMerkle.openingScheme H k).openAt f i⟩

def completeLog (k : ℕ) (f : Fin (2^k) → F) : EfficientRootOpening.Log F Digest :=
  (List.ofFn fun i : Fin (2^k) => EfficientRootOpening.openingLog H (f i)
    (binaryAddressBits k i) ((honestPoint k f i).path)).flatten

def sourceRoot := (BinaryMerkle.openingScheme H 4).commit farWord
def inputRoot := (BinaryMerkle.openingScheme H 1).commit (fun _ => (0:F))
def nextRoot := (BinaryMerkle.openingScheme H 1).commit (fun _ => (1:F))

def checkpoint : EfficientRootOpening.Log F Digest :=
  completeLog 4 farWord ++ completeLog 1 (fun _ => 0) ++ completeLog 1 (fun _ => 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- All three honest roots and all queried entries already occur at the checkpoint. -/
theorem no_bad (root : Digest) : ¬EfficientRootOpening.Bad checkpoint checkpoint root := by
  rintro (hc | ⟨e,he,hnot,_⟩)
  · have hb : EfficientRootOpening.badCheck checkpoint checkpoint sourceRoot = false := by decide
    exact (EfficientRootOpening.no_bad_of_check_false checkpoint checkpoint sourceRoot hb) (Or.inl hc)
  · exact hnot he

/-- Each honest path is retained in its complete finite log. -/
theorem completeLog_contains (k : ℕ) (f : Fin (2^k) → F) (i : Fin (2^k)) :
    PointLogged H (completeLog k f) i (honestPoint k f i) := by
  intro e he
  apply List.mem_flatten.mpr
  refine ⟨_,?_,he⟩
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

/-- The checkpoint's actual extracted source is the far source, coordinate by coordinate. -/
theorem extracted_source : EfficientRootOpening.word checkpoint 0 4 sourceRoot = farWord := by
  funext i
  symm
  apply supplied_point_pins H checkpoint checkpoint 0 sourceRoot i (honestPoint 4 farWord i)
    (fun _ h => h) (no_bad sourceRoot)
  · intro e he
    have hm := completeLog_contains 4 farWord i e he
    simp [checkpoint,hm]
  · exact (BinaryMerkle.openingScheme H 4).verifyOpen_commit farWord i

def row (i : Fin 2) : RowOpening F Digest where
  source c b a := honestPoint 4 farWord (rowPoint D₀ D₁ D₂ i c b a)
  injected := honestPoint 1 (fun _ => 0) i
  next := honestPoint 1 (fun _ => 1) i

/-- Every supplied path really is logged at the fixed checkpoint. -/
theorem row_logged (i : Fin 2) : RowLogged H checkpoint D₀ D₁ D₂ i (row i) := by
  refine ⟨?_,?_,?_⟩
  · intro c b a e he
    have hm := completeLog_contains 4 farWord (rowPoint D₀ D₁ D₂ i c b a) e he
    simp [checkpoint,hm]
  · intro e he
    have hm := completeLog_contains 1 (fun _ => (0:F)) i e he
    simpa only [checkpoint,List.mem_append,or_assoc] using (Or.inr (Or.inl hm) :
      e ∈ completeLog 4 farWord ∨ e ∈ completeLog 1 (fun _ => (0:F)) ∨
        e ∈ completeLog 1 (fun _ => (1:F)))
  · intro e he
    have hm := completeLog_contains 1 (fun _ => (1:F)) i e he
    simpa only [checkpoint,List.mem_append,or_assoc] using (Or.inr (Or.inr hm) :
      e ∈ completeLog 4 farWord ∨ e ∈ completeLog 1 (fun _ => (0:F)) ∨
        e ∈ completeLog 1 (fun _ => (1:F)))

/-- All supplied honest paths pass; at row zero their literal equation passes too. -/
theorem row_zero_verified (β : F) :
    RowVerified H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 0 (row 0) := by
  refine ⟨fun c b a => ?_,?_,?_,?_⟩
  · exact (BinaryMerkle.openingScheme H 4).verifyOpen_commit farWord _
  · exact (BinaryMerkle.openingScheme H 1).verifyOpen_commit (fun _ => (0:F)) _
  · exact (BinaryMerkle.openingScheme H 1).verifyOpen_commit (fun _ => (1:F)) _
  · change (1:F) = foldRow8 D₀ D₁ D₂ 0
      (fun c b a => farWord (rowPoint D₀ D₁ D₂ 0 c b a)) β + β^8*0
    rw [foldRow8_eq_fold8,fold_zero]
    simp

/-- Actual extracted farness and a no-Bad accepted supplied row coexist. -/
theorem supplied_premises_inhabited (β : F) :
    EfficientRootOpening.Far_E (1/5:ℝ) 4 (reedSolomonCode (dom 0) 8) checkpoint 0 sourceRoot ∧
    ¬RoundBad checkpoint checkpoint checkpoint checkpoint sourceRoot inputRoot nextRoot ∧
    RowLogged H checkpoint D₀ D₁ D₂ 0 (row 0) ∧
    RowVerified H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 0 (row 0) := by
  refine ⟨?_,?_,row_logged 0,row_zero_verified β⟩
  · simpa [EfficientRootOpening.Far_E,extracted_source] using farWord_far
  · rintro (h | h | h)
    · exact no_bad _ h
    · exact no_bad _ h
    · exact no_bad _ h

/-- The executable checker accepts the supplied witness for every scalar. -/
theorem row_zero_check (β : F) :
    rowCheck H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 0 (row 0) = true :=
  (rowCheck_eq_true_iff _ _ _ _ _ _ _ _ _ _).mpr (row_zero_verified β)

/-- Honest paths at row one still fail the false fold equation. -/
theorem row_one_check (β : F) :
    rowCheck H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 1 (row 1) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have h := (rowCheck_eq_true_iff _ _ _ _ _ _ _ _ _ _).mp ht
  have heq := h.2.2.2
  change (1:F) = foldRow8 D₀ D₁ D₂ 1
    (fun c b a => farWord (rowPoint D₀ D₁ D₂ 1 c b a)) β + β^8*0 at heq
  rw [foldRow8_eq_fold8,fold_one] at heq
  simp only [mul_zero,add_zero] at heq
  exact (by decide : (1:F) ≠ -1) heq

/-- The next checkpoint extracts the claimed constant codeword. -/
theorem extracted_next : EfficientRootOpening.word checkpoint 0 1 nextRoot = fun _ => (1:F) := by
  funext i
  symm
  apply supplied_point_pins H checkpoint checkpoint 0 nextRoot i
    (honestPoint 1 (fun _ => 1) i) (fun _ h => h) (no_bad nextRoot)
  · intro e he
    have hm := completeLog_contains 1 (fun _ => (1:F)) i e he
    simpa only [checkpoint,List.mem_append] using
      (Or.inr hm : e ∈ completeLog 4 farWord ++ completeLog 1 (fun _ => (0:F)) ∨
        e ∈ completeLog 1 (fun _ => (1:F)))
  · exact (BinaryMerkle.openingScheme H 1).verifyOpen_commit (fun _ => (1:F)) i

/-- The complete raw event is inhabited for any query count. -/
theorem supplied_event_accepts (β : F) (q : ℕ) :
    SuppliedCrossing H D₀ D₁ D₂ 1 (1/10:ℝ) q (fun _ => checkpoint) 0
      sourceRoot inputRoot (fun _ => nextRoot)
      (fun x a => row (x.2 a)) (β,fun _ => 0) := by
  refine ⟨?_,fun _ => row_zero_verified β⟩
  change close (1/10:ℝ) (reedSolomonCode (dom 3) 1)
    (EfficientRootOpening.word checkpoint 0 1 nextRoot)
  rw [extracted_next]
  exact ⟨fun _ => 1,mem_reedSolomonCode_one_iff.mpr (fun _ _ => rfl),by norm_num [relDist,hammingDist]⟩

/-- The supplied-opening probability head fires with genuine extracted
farness, full path-log completeness and zero observed failure probability. -/
theorem supplied_bound_fires (q : ℕ) :
    uniformProb (F × (Fin q → Fin 2))
      (SuppliedCrossing H D₀ D₁ D₂ 1 (1/10:ℝ) q (fun _ => checkpoint) 0
        sourceRoot inputRoot (fun _ => nextRoot) (fun x a => row (x.2 a))) ≤
      16/17+(9/10:ℝ)^q := by
  have hf : EfficientRootOpening.Far_E (1/5:ℝ) 4 (reedSolomonCode (dom 0) 8)
      checkpoint 0 sourceRoot := (supplied_premises_inhabited 0).1
  have h := supplied_injected_crossing_sound H D₀ D₁ D₂ (d := 1) (by decide)
    (θ := (1/5:ℝ)) (δ := (1/10:ℝ)) (τ := (1/10:ℝ)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) q checkpoint checkpoint
    (fun _ => checkpoint) 0 sourceRoot inputRoot (fun _ => nextRoot)
    (fun x a => row (x.2 a)) (fun _ => checkpoint)
    (fun _ => ⟨fun _ h => h,fun _ h => h,fun _ h => h⟩)
    (fun x a => row_logged (x.2 a)) hf
  have hz : uniformProb (F × (Fin q → Fin (2^(4-(2+1)))))
      (fun _ => RoundBad checkpoint checkpoint checkpoint checkpoint sourceRoot inputRoot nextRoot) = 0 := by
    apply uniformProb_false
    intro _ hb
    exact (supplied_premises_inhabited 0).2.1 hb
  dsimp only at h
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.reducePow] at h
  rw [hz] at h
  norm_num [ZMod.card] at h ⊢
  exact h

end Minidregg.Selvage.ArityEight.Witnesses.Logged

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.no_bad

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.completeLog_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.completeLog_contains

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.extracted_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.extracted_source

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.row_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.row_logged

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.row_zero_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.row_zero_verified

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.supplied_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.supplied_premises_inhabited

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.row_zero_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.row_zero_check

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.row_one_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.row_one_check

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.extracted_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.extracted_next

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.supplied_event_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.supplied_event_accepts

/-- info: 'Minidregg.Selvage.ArityEight.Witnesses.Logged.supplied_bound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Witnesses.Logged.supplied_bound_fires

