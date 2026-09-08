/- A structural supplied-log witness for the five-round actual BabyBear
schedule. The toy tree-valued hash and generic honest log lemmas are reused
unchanged from the frozen two-round witness. No field/domain enumeration. -/
import Selvage.ArityEightScheduleWitnesses
import Selvage.ArityEightTwoRoundLogged

namespace Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged
open BabyBearExt4
open scoped Classical
noncomputable section

abbrev Digest := TwoRound.Witnesses.Logged.Digest
abbrev H := TwoRound.Witnesses.Logged.H
open TwoRound.Witnesses.Logged (honestPoint completeLog completeLog_contains completeLog_valid evaluate_injective)

def value (n : ℕ) : PowerTwoFriLevels 20 (3*n) → Ext4 :=
  if n < 5 then monomial n else fun _ => 1

@[irreducible] def checkpoint : EfficientRootOpening.Log Ext4 Digest :=
  (List.ofFn fun n : Fin 6 => completeLog (20-3*n.val) (value n)).flatten ++
  (List.ofFn fun j : Fin 5 => completeLog (20-3*(j.val+1)) (fun _ => (0:Ext4))).flatten

theorem word_log_subset (n : ℕ) (hn : n ≤ 5) (e : EfficientRootOpening.Query Ext4 Digest × Digest)
    (he : e ∈ completeLog (20-3*n) (value n)) : e ∈ checkpoint := by
  unfold checkpoint
  apply List.mem_append.mpr
  left
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨⟨n,by omega⟩,rfl⟩,he⟩

theorem input_log_subset (j : Fin 5) (e : EfficientRootOpening.Query Ext4 Digest × Digest)
    (he : e ∈ completeLog (20-3*(j.val+1)) (fun _ => (0:Ext4))) : e ∈ checkpoint := by
  unfold checkpoint
  apply List.mem_append.mpr
  right
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,he⟩

theorem checkpoint_valid (e : EfficientRootOpening.Query Ext4 Digest × Digest)
    (he : e ∈ checkpoint) : e.2 = EfficientRootOpening.evaluate H e.1 := by
  unfold checkpoint at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨l,hl,he⟩ := List.mem_flatten.mp he
    obtain ⟨n,hn⟩ := List.mem_ofFn.mp hl
    subst l
    exact completeLog_valid _ (value n) e he
  · obtain ⟨l,hl,he⟩ := List.mem_flatten.mp he
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hl
    subst l
    exact completeLog_valid _ (fun _ => (0:Ext4)) e he

/-- Truthful constructor-hash records cannot collide; the checkpoint is complete. -/
theorem no_bad (root : Digest) : ¬EfficientRootOpening.Bad checkpoint checkpoint root := by
  rintro (⟨e,he,e',he',hresp,hne⟩ | ⟨e,he,hnot,_⟩)
  · apply hne
    apply evaluate_injective
    rw [←checkpoint_valid e he,←checkpoint_valid e' he']
    exact hresp
  · exact hnot he

theorem extracted_word (k : ℕ) (f : Fin (2^k) → Ext4)
    (hsub : ∀ e ∈ completeLog k f, e ∈ checkpoint) :
    EfficientRootOpening.word checkpoint 0 k ((BinaryMerkle.openingScheme H k).commit f) = f := by
  funext i
  symm
  apply supplied_point_pins H checkpoint checkpoint 0 _ i (honestPoint k f i)
    (fun _ h => h) (no_bad _)
  · exact fun e he => hsub e (completeLog_contains k f i e he)
  · exact (BinaryMerkle.openingScheme H k).verifyOpen_commit f i

/-- The whole finite honest checkpoint is fixed before all five fresh scalars. -/
def checkpoints : Checkpoints Ext4 Digest where
  word n _ := (checkpoint,(BinaryMerkle.openingScheme H (20-3*n)).commit (value n))
  input n _ := (checkpoint,(BinaryMerkle.openingScheme H (20-3*(n+1))).commit (fun _ => 0))

theorem word_extract (n : ℕ) (hn : n ≤ 5) (p : Fin n → Ext4) :
    (extracted checkpoints 0).word n p = value n :=
  extracted_word _ (value n) (word_log_subset n hn)

theorem input_extract (j : Fin 5) (p : Fin j.val → Ext4) :
    (extracted (ell := 20) checkpoints 0).input j p = fun _ => 0 :=
  extracted_word _ (fun _ => 0) (input_log_subset j)

theorem no_failure (r : Fin 5 → Ext4) : ¬Failure checkpoints checkpoint r := by
  rintro ⟨j,h | h | h⟩ <;> exact no_bad _ h

def row (j : Fin 5) (i : PowerTwoFriLevels 20 (3*(j.val+1))) : RowOpening Ext4 Digest where
  source c b a := honestPoint (20-3*j.val) (value j)
    (rowPoint (firstFifteen.data (3*j.val) (by omega))
      (firstFifteen.data (3*j.val+1) (by omega)) (firstFifteen.data (3*j.val+2) (by omega)) i c b a)
  injected := honestPoint (20-3*(j.val+1)) (fun _ => 0) i
  next := honestPoint (20-3*(j.val+1)) (value (j+1)) i

theorem row_logged (j : Fin 5) (i : PowerTwoFriLevels 20 (3*(j.val+1))) :
    RowLogged H checkpoint (firstFifteen.data (3*j.val) (by omega))
      (firstFifteen.data (3*j.val+1) (by omega)) (firstFifteen.data (3*j.val+2) (by omega)) i (row j i) := by
  refine ⟨?_,?_,?_⟩
  · intro c b a e he
    exact word_log_subset j (by omega) e (completeLog_contains _ (value j) _ e he)
  · intro e he
    exact input_log_subset j e (completeLog_contains _ (fun _ => (0:Ext4)) i e he)
  · intro e he
    exact word_log_subset (j+1) (by omega) e (completeLog_contains _ (value (j+1)) i e he)

/-- Every round at zero has actual honest paths and a true arity-eight equation. -/
theorem row_zero_verified (j : Fin 5) (p : Fin j.val → Ext4) (p' : Fin (j.val+1) → Ext4) (β : Ext4) :
    RowVerified H (firstFifteen.data (3*j.val) (by omega))
      (firstFifteen.data (3*j.val+1) (by omega)) (firstFifteen.data (3*j.val+2) (by omega))
      (checkpoints.word j p).2 (checkpoints.input j p).2 (checkpoints.word (j+1) p').2 β 0 (row j 0) := by
  refine ⟨fun _ _ _ => ?_,?_,?_,?_⟩
  · exact (BinaryMerkle.openingScheme H (20-3*j.val)).verifyOpen_commit (value j) _
  · exact (BinaryMerkle.openingScheme H (20-3*(j.val+1))).verifyOpen_commit (fun _ => (0:Ext4)) _
  · exact (BinaryMerkle.openingScheme H (20-3*(j.val+1))).verifyOpen_commit (value (j+1)) _
  · change value (j+1) 0 = foldRow8 _ _ _ 0
      (fun c b a => value j (rowPoint _ _ _ 0 c b a)) β + β^8*0
    rw [foldRow8_eq_fold8]
    have h := congrFun (literal_exact j p β) 0
    have hz : value (j+1) 0 = monomial (j+1) 0 := by
      unfold value
      split_ifs
      · rfl
      · simp [monomial,domain_zero]
    rw [hz]
    exact h.symm

def openings (q : ℕ) (x : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1)) :
    Openings Ext4 Digest 5 q := fun j a => row j (roundQueries (by decide) j x.2 a)

theorem checkpoints_logged (r : Fin 5 → Ext4) : CheckpointsLogged checkpoints checkpoint r :=
  ⟨fun _ _ _ h => h,fun _ _ h => h⟩

theorem openings_logged (q : ℕ) (x : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1)) :
    OpeningsLogged H firstFifteen checkpoint q (by decide) x.2 (openings q x) :=
  fun j _ => row_logged j _

theorem extracted_far : EfficientRootOpening.Far_E (2/5:ℝ) 20
    (reedSolomonCode (firstFifteen.dom 0) (2^19))
    (checkpoints.word 0 (fun i => i.elim0)).1 0 (checkpoints.word 0 (fun i => i.elim0)).2 := by
  change ¬close (2/5:ℝ) (reedSolomonCode (firstFifteen.dom 0) (2^19))
    ((extracted checkpoints 0).word 0 (fun i => i.elim0))
  rw [word_extract 0 (by decide)]
  exact source_far

/-- All five supplied rows and the extracted terminal membership accept. -/
theorem supplied_zero_accepts (r : Fin 5 → Ext4) (q : ℕ) :
    SuppliedAccepts H firstFifteen checkpoints 0 degree q (by decide) r (fun _ => 0)
      (openings q (r,fun _ => 0)) := by
  constructor
  · change (extracted checkpoints 0).word 5 (friPrefix r 5 le_rfl) ∈ _
    rw [word_extract 5 le_rfl]
    exact terminal_mem r
  · intro j a
    change RowVerified H _ _ _ _ _ _ _ (roundQueries (show 3*5 ≤ 20 by decide) j
      (fun _ : Fin q => (0 : PowerTwoFriLevels 20 1)) a) (row j _)
    have hz : roundQueries (show 3*5 ≤ 20 by decide) j
        (fun _ : Fin q => (0 : PowerTwoFriLevels 20 1)) a = 0 := by
      apply Fin.ext
      simp [roundQueries,powerTwoCoherentRound,powerTwoRoundIndex]
    rw [hz]
    exact row_zero_verified j _ _ _

/-- The full supplied theorem fires with actual far extraction, complete
path logs and zero observed failure, for the entire five-round schedule. -/
theorem supplied_bound_fires (q : ℕ) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => SuppliedAccepts H firstFifteen checkpoints 0 degree q (by decide) x.1 x.2 (openings q x)) ≤
      ((2^20+2^17+2^14+2^11+2^8:ℕ):ℝ)/(modulus^4:ℕ)+(24/25:ℝ)^q := by
  have h := supplied_terminal_sound H checkpoints 0 q (openings q) (fun _ => checkpoint)
    (fun x => checkpoints_logged x.1) (openings_logged q) extracted_far
  have hn : uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Failure checkpoints checkpoint x.1) = 0 :=
    uniformProb_false (fun x hx => no_failure x.1 hx)
  simpa only [hn,add_zero] using h

end
end Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.word_log_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.word_log_subset

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.input_log_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.input_log_subset

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.checkpoint_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.checkpoint_valid

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.no_bad

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.extracted_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.extracted_word

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.word_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.word_extract

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.input_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.input_extract

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.no_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.no_failure

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.row_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.row_logged

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.row_zero_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.row_zero_verified

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.checkpoints_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.checkpoints_logged

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.openings_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.openings_logged

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.extracted_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.extracted_far

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.supplied_zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.supplied_zero_accepts

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.supplied_bound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.Logged.supplied_bound_fires
