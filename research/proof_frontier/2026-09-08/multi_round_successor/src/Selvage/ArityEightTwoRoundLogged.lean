/- A finite honest checkpoint witness for both supplied-opening rounds.
The digest is an explicit tree-valued toy hash. No cryptographic pricing or
huge finite-field enumeration is used: log consistency is proved structurally. -/
import Selvage.ArityEightTwoRoundSupplied
import Selvage.ArityEightTwoRoundWitnesses

namespace Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged
open BabyBearExt4
open scoped Classical
noncomputable section

inductive Digest where
  | leaf : Ext4 → Digest
  | node : Digest → Digest → Digest
  deriving DecidableEq

def H : BinaryMerkle.HashSuite Ext4 Digest := ⟨Digest.leaf,Digest.node⟩

/-- Constructor separation gives this explicit toy hash injective typed queries. -/
theorem evaluate_injective : Function.Injective (EfficientRootOpening.evaluate H) := by
  intro q q' h
  cases q <;> cases q' <;> simp_all [EfficientRootOpening.evaluate,H]

/-- Every recursively recorded node response is its actual hash evaluation. -/
theorem pathLog_valid (leaf : Digest) : ∀ (k : ℕ) (address : Fin k → Bool)
    (path : List Digest) (e : EfficientRootOpening.Query Ext4 Digest × Digest),
    e ∈ EfficientRootOpening.pathLog H leaf address path →
      e.2 = EfficientRootOpening.evaluate H e.1 := by
  intro k
  induction k with
  | zero => intro address path e he; simp [EfficientRootOpening.pathLog] at he
  | succ k ih =>
    intro address path e he
    cases path with
    | nil => simp [EfficientRootOpening.pathLog] at he
    | cons sibling rest =>
      cases hr : BinaryMerkle.recompute H leaf (fun i => address i.succ) rest with
      | none => simp [EfficientRootOpening.pathLog,hr] at he
      | some child =>
        simp only [EfficientRootOpening.pathLog,hr] at he
        rcases List.mem_append.mp he with he | he
        · exact ih _ _ _ he
        · have heq := List.mem_singleton.mp he
          rw [heq]

/-- Supplied opening logs are truthful hash-call records. -/
theorem openingLog_valid (k : ℕ) (v : Ext4) (address : Fin k → Bool) (path : List Digest)
    (e : EfficientRootOpening.Query Ext4 Digest × Digest)
    (he : e ∈ EfficientRootOpening.openingLog H v address path) :
    e.2 = EfficientRootOpening.evaluate H e.1 := by
  rcases List.mem_cons.mp he with he | he
  · rw [he]; rfl
  · exact pathLog_valid (H.leaf v) k address path e he

def honestPoint (k : ℕ) (f : Fin (2^k) → Ext4) (i : Fin (2^k)) : PointOpening Ext4 Digest :=
  ⟨f i,(BinaryMerkle.openingScheme H k).openAt f i⟩

@[irreducible] def completeLog (k : ℕ) (f : Fin (2^k) → Ext4) : EfficientRootOpening.Log Ext4 Digest :=
  (List.ofFn fun i : Fin (2^k) => EfficientRootOpening.openingLog H (f i)
    (binaryAddressBits k i) (honestPoint k f i).path).flatten

theorem completeLog_valid (k : ℕ) (f : Fin (2^k) → Ext4)
    (e : EfficientRootOpening.Query Ext4 Digest × Digest) (he : e ∈ completeLog k f) :
    e.2 = EfficientRootOpening.evaluate H e.1 := by
  unfold completeLog at he
  obtain ⟨l,hl,he⟩ := List.mem_flatten.mp he
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hl
  subst l
  exact openingLog_valid k (f i) (binaryAddressBits k i) _ e he

theorem completeLog_contains (k : ℕ) (f : Fin (2^k) → Ext4) (i : Fin (2^k)) :
    PointLogged H (completeLog k f) i (honestPoint k f i) := by
  intro e he
  unfold completeLog
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,he⟩

/-- A fixed honest middle word; the adaptive-input witness is separate. -/
def middleWord : PowerTwoFriLevels 7 3 → Ext4 := fun i => (smallTower.dom 3 i)^8

def checkpoint : EfficientRootOpening.Log Ext4 Digest :=
  completeLog 7 farWord ++ completeLog 4 middleWord ++
    completeLog 4 (fun _ => 0) ++ completeLog 1 (fun _ => 0) ++ completeLog 1 (fun _ => 1)

theorem checkpoint_valid (e : EfficientRootOpening.Query Ext4 Digest × Digest)
    (he : e ∈ checkpoint) : e.2 = EfficientRootOpening.evaluate H e.1 := by
  simp only [checkpoint,List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · exact completeLog_valid 7 farWord e he
  · exact completeLog_valid 4 middleWord e he
  · exact completeLog_valid 4 (fun _ => 0) e he
  · exact completeLog_valid 1 (fun _ => 0) e he
  · exact completeLog_valid 1 (fun _ => 1) e he

/-- A structural proof of no observed collision or late checkpoint entry. -/
theorem no_bad (root : Digest) : ¬EfficientRootOpening.Bad checkpoint checkpoint root := by
  rintro (⟨e,he,e',he',hresp,hne⟩ | ⟨e,he,hnot,_⟩)
  · apply hne
    apply evaluate_injective
    rw [←checkpoint_valid e he,←checkpoint_valid e' he']
    exact hresp
  · exact hnot he

/-- Retained honest openings determine the existing checkpoint extractor exactly. -/
theorem extracted_word (k : ℕ) (f : Fin (2^k) → Ext4)
    (hsub : ∀ e ∈ completeLog k f, e ∈ checkpoint) :
    EfficientRootOpening.word checkpoint 0 k ((BinaryMerkle.openingScheme H k).commit f) = f := by
  funext i
  symm
  apply supplied_point_pins H checkpoint checkpoint 0 _ i (honestPoint k f i)
    (fun _ h => h) (no_bad _)
  · exact fun e he => hsub e (completeLog_contains k f i e he)
  · exact (BinaryMerkle.openingScheme H k).verifyOpen_commit f i

def checkpoints : Checkpoints Ext4 Digest where
  source := (checkpoint,(BinaryMerkle.openingScheme H 7).commit farWord)
  input0 := (checkpoint,(BinaryMerkle.openingScheme H 4).commit (fun _ => 0))
  middle _ := (checkpoint,(BinaryMerkle.openingScheme H 4).commit middleWord)
  input1 _ := (checkpoint,(BinaryMerkle.openingScheme H 1).commit (fun _ => 0))
  final _ _ := (checkpoint,(BinaryMerkle.openingScheme H 1).commit (fun _ => 1))

def fixedWords : Words Ext4 (PowerTwoFriLevels 7) where
  source := farWord
  input0 := fun _ => 0
  middle _ := middleWord
  input1 _ _ := 0
  final _ _ _ := 1

/-- All five extracted words coincide with their concrete honest commitments. -/
theorem extracted_checkpoints : extracted checkpoints 0 = fixedWords := by
  have hs := extracted_word 7 farWord (by intros e he; simp only [checkpoint,List.mem_append]; tauto)
  have hm := extracted_word 4 middleWord (by intros e he; simp only [checkpoint,List.mem_append]; tauto)
  have hg := extracted_word 4 (fun _ => (0:Ext4)) (by intros e he; simp only [checkpoint,List.mem_append]; tauto)
  have hi := extracted_word 1 (fun _ => (0:Ext4)) (by intros e he; simp only [checkpoint,List.mem_append]; tauto)
  have hn := extracted_word 1 (fun _ => (1:Ext4)) (by intros e he; simp only [checkpoint,List.mem_append]; tauto)
  change Words.mk _ _ _ _ _ = Words.mk _ _ _ _ _
  simp only [checkpoints,hs,hm,hg,hi,hn]

/-- Both round failure events are absent at this actual fixed checkpoint. -/
theorem no_failure (r : Ext4 × Ext4) : ¬Failure checkpoints checkpoint r := by
  rintro ((h | h | h) | (h | h | h)) <;> exact no_bad _ h

def firstRow (i : PowerTwoFriLevels 7 3) : RowOpening Ext4 Digest where
  source c b a := honestPoint 7 farWord
    (rowPoint (smallTower.data 0 (by decide)) (smallTower.data 1 (by decide))
      (smallTower.data 2 (by decide)) i c b a)
  injected := honestPoint 4 (fun _ => 0) i
  next := honestPoint 4 middleWord i

def secondRow (i : PowerTwoFriLevels 7 6) : RowOpening Ext4 Digest where
  source c b a := honestPoint 4 middleWord
    (rowPoint (smallTower.data 3 (by decide)) (smallTower.data 4 (by decide))
      (smallTower.data 5 (by decide)) i c b a)
  injected := honestPoint 1 (fun _ => 0) i
  next := honestPoint 1 (fun _ => 1) i

/-- Every supplied path in either round is already logged before the challenge pair. -/
theorem first_logged (i : PowerTwoFriLevels 7 3) :
    RowLogged H checkpoint (smallTower.data 0 (by decide)) (smallTower.data 1 (by decide))
      (smallTower.data 2 (by decide)) i (firstRow i) := by
  refine ⟨?_,?_,?_⟩
  · intro c b a e he
    have hm := completeLog_contains 7 farWord _ e he
    simp only [checkpoint,List.mem_append]; tauto
  · intro e he
    have hm := completeLog_contains 4 (fun _ => (0:Ext4)) i e he
    simp only [checkpoint,List.mem_append]; tauto
  · intro e he
    have hm := completeLog_contains 4 middleWord i e he
    simp only [checkpoint,List.mem_append]; tauto

theorem second_logged (i : PowerTwoFriLevels 7 6) :
    RowLogged H checkpoint (smallTower.data 3 (by decide)) (smallTower.data 4 (by decide))
      (smallTower.data 5 (by decide)) i (secondRow i) := by
  refine ⟨?_,?_,?_⟩
  · intro c b a e he
    have hm := completeLog_contains 4 middleWord _ e he
    simp only [checkpoint,List.mem_append]; tauto
  · intro e he
    have hm := completeLog_contains 1 (fun _ => (0:Ext4)) i e he
    simp only [checkpoint,List.mem_append]; tauto
  · intro e he
    have hm := completeLog_contains 1 (fun _ => (1:Ext4)) i e he
    simp only [checkpoint,List.mem_append]; tauto

/-- Every first-round row is the exact honest fold. -/
theorem first_verified (β : Ext4) (i : PowerTwoFriLevels 7 3) :
    RowVerified H (smallTower.data 0 (by decide)) (smallTower.data 1 (by decide))
      (smallTower.data 2 (by decide)) checkpoints.source.2 checkpoints.input0.2
      (checkpoints.middle β).2 β i (firstRow i) := by
  refine ⟨fun _ _ _ => ?_,?_,?_,?_⟩
  · exact (BinaryMerkle.openingScheme H 7).verifyOpen_commit farWord _
  · exact (BinaryMerkle.openingScheme H 4).verifyOpen_commit (fun _ => (0:Ext4)) _
  · exact (BinaryMerkle.openingScheme H 4).verifyOpen_commit middleWord _
  · change middleWord i = foldRow8 _ _ _ i (fun c b a => farWord (rowPoint _ _ _ i c b a)) β + β^8*0
    rw [foldRow8_eq_fold8]
    have h := congrFun (first_block_exact β) i
    simpa [block0,words,middleWord] using h.symm

/-- A genuine accepted second-round row on the same shared middle root. -/
theorem second_zero_verified (a b : Ext4) :
    RowVerified H (smallTower.data 3 (by decide)) (smallTower.data 4 (by decide))
      (smallTower.data 5 (by decide)) (checkpoints.middle a).2 (checkpoints.input1 a).2
      (checkpoints.final a b).2 b 0 (secondRow 0) := by
  refine ⟨fun _ _ _ => ?_,?_,?_,?_⟩
  · exact (BinaryMerkle.openingScheme H 4).verifyOpen_commit middleWord _
  · exact (BinaryMerkle.openingScheme H 1).verifyOpen_commit (fun _ => (0:Ext4)) _
  · exact (BinaryMerkle.openingScheme H 1).verifyOpen_commit (fun _ => (1:Ext4)) _
  · change (1:Ext4) = foldRow8 _ _ _ 0
      (fun c b a => middleWord (rowPoint _ _ _ 0 c b a)) b + b^8*0
    rw [foldRow8_eq_fold8]
    have h := congrFun (second_block_exact 0 b) 0
    simpa [block1,words,middleWord,terminal_domain_zero] using h.symm

def openings (q : ℕ) (x : (Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 7 1)) : Openings Ext4 Digest q where
  first a := firstRow (powerTwoCoherentRound (show 6 ≤ 7 by decide) (⟨2,by decide⟩ : Fin 6) x.2 a)
  second a := secondRow (powerTwoCoherentRound (show 6 ≤ 7 by decide) (⟨5,by decide⟩ : Fin 6) x.2 a)

theorem checkpoints_logged (r : Ext4 × Ext4) : CheckpointsLogged checkpoints checkpoint r :=
  ⟨fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h⟩

theorem openings_logged (q : ℕ) (x : (Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 7 1)) :
    OpeningsLogged H smallTower checkpoint q (by decide) x.2 (openings q x) :=
  ⟨fun _ => first_logged _,fun _ => second_logged _⟩

/-- The initial extracted farness premise is actually inhabited. -/
theorem extracted_far : EfficientRootOpening.Far_E (1/5:ℝ) 7
    (reedSolomonCode (smallTower.dom 0) 64) checkpoints.source.1 0 checkpoints.source.2 := by
  have h := congrArg Words.source extracted_checkpoints
  change (extracted checkpoints 0).source = farWord at h
  change ¬close (1/5:ℝ) (reedSolomonCode (smallTower.dom 0) 64) (extracted checkpoints 0).source
  rw [h]
  exact farWord_far

/-- Both supplied rounds, terminal membership and no observed failure hold together. -/
theorem supplied_zero_accepts (r : Ext4 × Ext4) (q : ℕ) :
    SuppliedAccepts H smallTower checkpoints 0 1 q (by decide) r (fun _ => 0)
      (openings q (r,fun _ => 0)) := by
  refine ⟨?_,?_,?_⟩
  · rw [extracted_checkpoints]
    exact mem_reedSolomonCode_one_iff.mpr (fun _ _ => rfl)
  · intro a
    exact first_verified r.1 _
  · intro a
    have hz : powerTwoCoherentRound (show 6 ≤ 7 by decide) (⟨5,by decide⟩ : Fin 6)
        (fun _ : Fin q => (0 : PowerTwoFriLevels 7 1)) a = 0 := by
      apply Fin.ext
      simp [powerTwoCoherentRound,powerTwoRoundIndex]
    change RowVerified _ _ _ _ _ _ _ _ _ (secondRow _)
    rw [hz]
    exact second_zero_verified r.1 r.2

/-- The complete supplied two-round theorem fires with zero observed failure
and inhabited positive query acceptance, not just an ideal-word hypothesis. -/
theorem supplied_bound_fires (q : ℕ) :
    uniformProb ((Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 7 1))
      (fun x => SuppliedAccepts H smallTower checkpoints 0 1 q (by decide) x.1 x.2 (openings q x)) ≤
      (144:ℝ)/(modulus^4:ℕ)+(9/10:ℝ)^q := by
  have h := supplied_sound H smallTower checkpoints 0 (d := 1) (by decide) q (by decide)
    (ρ₀ := (1/5:ℝ)) (ρ₁ := (1/10:ℝ)) (τ := (1/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [PowerTwoFriLevels]) (by norm_num [PowerTwoFriLevels])
    (openings q) (fun _ => checkpoint) (fun x => checkpoints_logged x.1) (openings_logged q) extracted_far
  have hz : uniformProb ((Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 7 1))
      (fun x => Failure checkpoints checkpoint x.1) = 0 :=
    uniformProb_false (fun x => no_failure x.1)
  dsimp only at h
  rw [hz] at h
  have hc : Fintype.card Ext4 = modulus^4 := ext4_card
  rw [hc] at h
  norm_num [PowerTwoFriLevels] at h ⊢
  convert h using 1
  ring

end
end Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged


/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.evaluate_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.evaluate_injective

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.pathLog_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.pathLog_valid

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.openingLog_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.openingLog_valid

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.completeLog_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.completeLog_valid

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.completeLog_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.completeLog_contains

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.checkpoint_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.checkpoint_valid

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.no_bad

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.extracted_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.extracted_word

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.extracted_checkpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.extracted_checkpoints

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.no_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.no_failure

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.first_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.first_logged

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.second_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.second_logged

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.first_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.first_verified

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.second_zero_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.second_zero_verified

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.checkpoints_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.checkpoints_logged

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.openings_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.openings_logged

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.extracted_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.extracted_far

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.supplied_zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.supplied_zero_accepts

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.supplied_bound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.Witnesses.Logged.supplied_bound_fires
