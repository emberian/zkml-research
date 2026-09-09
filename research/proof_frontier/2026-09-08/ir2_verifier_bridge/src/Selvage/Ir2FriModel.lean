/- The exact canonical query-template FRI schedule: four width-eight folds,
then width-four, rate1/8, no lower-height injections and a constant terminal.
This is the mathematical event targeted by the fresh native admission adapter. -/
import Selvage.Ir2FriCosetRows
import Selvage.Ir2FriSchedule
import Selvage.ConsistencyMask
import Selvage.ArityEightConsistencySchedule

namespace Minidregg.Selvage.Ir2Fri
open BabyBearExt4 ArityEight Ir2FriSchedule
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Existing root/tower machinery at the actual LDE size and total reduction. -/
def tower : FoldingTower Ext4 (PowerTwoFriLevels 17) 14 :=
  PowerTwoRootFolding.tower (TwoAdic.omega_primitive 17 (by decide))
    MultiplicativeTower.two_ne_zero (by decide)

def domain (n : ℕ) : Index n ↪ Ext4 := tower.dom (stage n)
def degree (n : ℕ) : ℕ := 2^(14-stage n)

/-- This adapter profile has no lower-height injected words. The base input
is the alpha-reduced opening function on subgroup t (original coset point31t).
Each committed FRI word is fixed by the prior beta prefix. -/
structure Words where
  input : Index 0 → Ext4
  word : ∀ n, (Fin n → Ext4) → Index n → Ext4

def Words.wordAt (s : Words) (r : Fin 5 → Ext4) (n : ℕ) (hn : n ≤ 5) : Index n → Ext4 :=
  s.word n (friPrefix r n hn)

/-- Native [3,3,3,3,2] correlated-power folding using existing FoldingData. -/
def foldStep : (j : Fin 5) → (Index j → Ext4) → Ext4 → Index (j+1) → Ext4
  | ⟨0,_⟩ => fun f β => fold8 (tower.data 0 (by decide)) (tower.data 1 (by decide)) (tower.data 2 (by decide)) f β
  | ⟨1,_⟩ => fun f β => fold8 (tower.data 3 (by decide)) (tower.data 4 (by decide)) (tower.data 5 (by decide)) f β
  | ⟨2,_⟩ => fun f β => fold8 (tower.data 6 (by decide)) (tower.data 7 (by decide)) (tower.data 8 (by decide)) f β
  | ⟨3,_⟩ => fun f β => fold8 (tower.data 9 (by decide)) (tower.data 10 (by decide)) (tower.data 11 (by decide)) f β
  | ⟨4,_⟩ => fun f β => fold4 (tower.data 12 (by decide)) (tower.data 13 (by decide)) f β
  | ⟨n+5,h⟩ => False.elim (by omega)

/-- The weight projection follows those same actual square fibres. -/
def projectStep : (j : Fin 5) → (Index j → ℝ) → Index (j+1) → ℝ
  | ⟨0,_⟩ => projectConsistency8 (tower.data 0 (by decide)) (tower.data 1 (by decide)) (tower.data 2 (by decide))
  | ⟨1,_⟩ => projectConsistency8 (tower.data 3 (by decide)) (tower.data 4 (by decide)) (tower.data 5 (by decide))
  | ⟨2,_⟩ => projectConsistency8 (tower.data 6 (by decide)) (tower.data 7 (by decide)) (tower.data 8 (by decide))
  | ⟨3,_⟩ => projectConsistency8 (tower.data 9 (by decide)) (tower.data 10 (by decide)) (tower.data 11 (by decide))
  | ⟨4,_⟩ => fun w => projectConsistency (tower.data 13 (by decide)) (projectConsistency (tower.data 12 (by decide)) w)
  | ⟨n+5,h⟩ => False.elim (by omega)

/-- Exact native polynomial-curve degree:7 for each width8,3 for width4. -/
def curveDegree (j : Fin 5) : ℕ := if j.val < 4 then 7 else 3

theorem degrees : [degree 0,degree 1,degree 2,degree 3,degree 4,degree 5] =
    [16384,2048,256,32,4,1] := by decide

theorem projectStep_le_one (j : Fin 5) (w : Index j → ℝ) (h : ∀ i, w i ≤ 1) :
    ∀ i, projectStep j w i ≤ 1 := by
  fin_cases j
  · exact projectConsistency8_le_one _ _ _ _ h
  · exact projectConsistency8_le_one _ _ _ _ h
  · exact projectConsistency8_le_one _ _ _ _ h
  · exact projectConsistency8_le_one _ _ _ _ h
  · exact projectConsistency_le_one _ _ (projectConsistency_le_one _ _ h)

/-- Every actual transition satisfies the weighted full-UD bound. All field,
domain, arity and degree premises are discharged by the fixed native profile. -/
theorem step_weighted_bound (j : Fin 5) {θ : ℝ} (hθ : 0 < θ) (hθmax : θ < 7/16)
    (w : Index j → ℝ) (hw : ∀ i, w i ≤ 1) (f : Index j → Ext4)
    (hfar : ¬WeightedClose (reedSolomonCode (domain j) (degree j)) θ w f) :
    uniformProb Ext4 (fun β => WeightedClose (reedSolomonCode (domain (j+1)) (degree (j+1))) θ
      (projectStep j w) (foldStep j f β)) ≤
      ((curveDegree j*Fintype.card (Index (j+1)):ℕ):ℝ)/Fintype.card Ext4 := by
  have hr : ∀ j : Fin 5, (degree (j+1):ℝ) < (1-2*θ)*(Fintype.card (Index (j+1)):ℝ) := by
    intro j
    fin_cases j <;> norm_num [degree,Index,stage] <;> linarith
  fin_cases j
  · exact fold8_weighted_sound (tower.data 0 (by decide)) (tower.data 1 (by decide)) (tower.data 2 (by decide)) (by decide) hθ (hr 0) w hw f hfar
  · exact fold8_weighted_sound (tower.data 3 (by decide)) (tower.data 4 (by decide)) (tower.data 5 (by decide)) (by decide) hθ (hr 1) w hw f hfar
  · exact fold8_weighted_sound (tower.data 6 (by decide)) (tower.data 7 (by decide)) (tower.data 8 (by decide)) (by decide) hθ (hr 2) w hw f hfar
  · exact fold8_weighted_sound (tower.data 9 (by decide)) (tower.data 10 (by decide)) (tower.data 11 (by decide)) (by decide) hθ (hr 3) w hw f hfar
  · exact fold4_weighted_sound (tower.data 12 (by decide)) (tower.data 13 (by decide)) (by decide) hθ (hr 4) w hw f hfar

/-- The initial mask is required by the native carried-input equality, even
before the first folding challenge. -/
def initialMask (s : Words) (i : Index 0) : Prop := s.word 0 (fun i => i.elim0) i = s.input i

def prefixWeight (s : Words) : (n : ℕ) → n ≤ 5 → (Fin n → Ext4) → Index n → ℝ
  | 0, _, p => maskConsistency (fun _ => 1) (s.word 0 p) s.input
  | n+1, hn, p =>
    let j : Fin 5 := ⟨n,by omega⟩
    let prior : Fin n → Ext4 := fun i => p i.castSucc
    maskConsistency (projectStep j (prefixWeight s n (by omega) prior))
      (s.word (n+1) p) (foldStep j (s.word n prior) (p (Fin.last n)))

def weightAt (s : Words) (r : Fin 5 → Ext4) (n : ℕ) (hn : n ≤ 5) :=
  prefixWeight s n hn (friPrefix r n hn)

def blockAt (s : Words) (j : Fin 5) (r : Fin 5 → Ext4) :=
  foldStep j (s.wordAt r j (by omega)) (r j)

def BadRound (s : Words) (θ : ℝ) (j : Fin 5) (r : Fin 5 → Ext4) : Prop :=
  ¬WeightedClose (reedSolomonCode (domain j) (degree j)) θ (weightAt s r j (by omega))
      (s.wordAt r j (by omega)) ∧
    WeightedClose (reedSolomonCode (domain (j+1)) (degree (j+1))) θ
      (projectStep j (weightAt s r j (by omega))) (blockAt s j r)


theorem prefixWeight_le_one (s : Words) (n : ℕ) (hn : n ≤ 5) (p : Fin n → Ext4) :
    ∀ i, prefixWeight s n hn p i ≤ 1 := by
  induction n with
  | zero => exact maskConsistency_le_one _ (fun _ => le_rfl) _ _
  | succ n ih =>
    let j : Fin 5 := ⟨n,by omega⟩
    exact maskConsistency_le_one _ (projectStep_le_one j _ (ih (by omega) (fun i => p i.castSucc))) _ _

theorem weightAt_succ (s : Words) (r : Fin 5 → Ext4) (j : Fin 5) :
    weightAt s r (j+1) (by omega) =
      maskConsistency (projectStep j (weightAt s r j (by omega)))
        (s.wordAt r (j+1) (by omega)) (blockAt s j r) := rfl

/-- The round event is controlled by one fresh scalar conditioned on its prefix. -/
theorem bad_round_bound (s : Words) {θ : ℝ} (hθ : 0 < θ) (hθmax : θ < 7/16) (j : Fin 5) :
    uniformProb (Fin 5 → Ext4) (BadRound s θ j) ≤
      ((curveDegree j*Fintype.card (Index (j+1)):ℕ):ℝ)/Fintype.card Ext4 := by
  apply ArityEight.Schedule.prefix_challenge_bound j (fun p β =>
    ¬WeightedClose (reedSolomonCode (domain j) (degree j)) θ
      (prefixWeight s j (by omega) p) (s.word j p) ∧
    WeightedClose (reedSolomonCode (domain (j+1)) (degree (j+1))) θ
      (projectStep j (prefixWeight s j (by omega) p)) (foldStep j (s.word j p) β)) (by positivity)
  intro p
  by_cases hf : WeightedClose (reedSolomonCode (domain j) (degree j)) θ
      (prefixWeight s j (by omega) p) (s.word j p)
  · rw [uniformProb_false (fun _ h => h.1 hf)]
    positivity
  · exact le_trans (uniformProb_mono fun _ h => h.2)
      (step_weighted_bound j hθ hθmax _ (prefixWeight_le_one s j (by omega) p) _ hf)

/-- All five actual challenge errors are derived and summed; there is no
injected coefficient in this single-height deployed profile. -/
theorem bad_schedule_bound (s : Words) {θ : ℝ} (hθ : 0 < θ) (hθmax : θ < 7/16) :
    uniformProb (Fin 5 → Ext4) (fun r => ∃ j, BadRound s θ j r) ≤
      (131064:ℝ)/(modulus^4:ℕ) := by
  have h := le_trans (uniformProb_exists_le (fun (j : Fin 5) r => BadRound s θ j r))
    (Finset.sum_le_sum fun j _ => bad_round_bound s hθ hθmax j)
  rw [ext4_card] at h
  norm_num [curveDegree,Index,stage,Fin.sum_univ_succ] at h ⊢
  convert h using 1
  ring

/-- The initial native input-equality mask transfers closeness back to the
actual alpha-reduced input, so first-root farness is not an assumption. -/
theorem weighted_invariant (s : Words) (θ : ℝ)
    (hfar : ¬close θ (reedSolomonCode (domain 0) (degree 0)) s.input)
    (r : Fin 5 → Ext4) (hgood : ¬∃ j, BadRound s θ j r) (n : ℕ) (hn : n ≤ 5) :
    ¬WeightedClose (reedSolomonCode (domain n) (degree n)) θ
      (weightAt s r n hn) (s.wordAt r n hn) := by
  induction n with
  | zero =>
    intro h
    apply hfar
    exact weightedClose_one_to_close _ θ _ (weightedClose_mask_transfer _ θ _ _ _ h)
  | succ n ih =>
    intro h
    let j : Fin 5 := ⟨n,by omega⟩
    apply hgood
    refine ⟨j,ih (by omega),?_⟩
    rw [weightAt_succ s r j] at h
    exact weightedClose_mask_transfer _ θ _ _ _ h

/-- A one-coefficient native final polynomial supplies this exact condition. -/
def Terminal (s : Words) (r : Fin 5 → Ext4) : Prop := ∃ c, ∀ i, s.wordAt r 5 le_rfl i = c

theorem terminal_codeword (s : Words) (r : Fin 5 → Ext4) (h : Terminal s r) :
    s.wordAt r 5 le_rfl ∈ reedSolomonCode (domain 5) (degree 5) := by
  obtain ⟨c,hc⟩ := h
  exact mem_reedSolomonCode_iff.mpr ⟨Polynomial.C c,by
    have hd : (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
    exact hd.trans_lt (by norm_num [degree,stage]),by simpa using hc⟩

/-- The whole remaining query survival mass is small, including its required
initial equality mask, whenever no derived challenge failure occurred. -/
theorem terminal_mass (s : Words) (θ : ℝ)
    (hfar : ¬close θ (reedSolomonCode (domain 0) (degree 0)) s.input)
    (r : Fin 5 → Ext4) (hgood : ¬∃ j, BadRound s θ j r) (ht : Terminal s r) :
    consistencyMass (weightAt s r 5 le_rfl) Finset.univ <
      (1-θ)*(Fintype.card (Index 5):ℝ) := by
  by_contra hn
  exact weighted_invariant s θ hfar r hgood 5 le_rfl
    (weightedClose_self_of_mass _ θ _ _ (terminal_codeword s r ht) (le_of_not_gt hn))

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.degrees' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.degrees

/-- info: 'Minidregg.Selvage.Ir2Fri.projectStep_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.projectStep_le_one

/-- info: 'Minidregg.Selvage.Ir2Fri.step_weighted_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.step_weighted_bound

/-- info: 'Minidregg.Selvage.Ir2Fri.prefixWeight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.prefixWeight_le_one

/-- info: 'Minidregg.Selvage.Ir2Fri.weightAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.weightAt_succ

/-- info: 'Minidregg.Selvage.Ir2Fri.bad_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.bad_round_bound

/-- info: 'Minidregg.Selvage.Ir2Fri.bad_schedule_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.bad_schedule_bound

/-- info: 'Minidregg.Selvage.Ir2Fri.weighted_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.weighted_invariant

/-- info: 'Minidregg.Selvage.Ir2Fri.terminal_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.terminal_codeword

/-- info: 'Minidregg.Selvage.Ir2Fri.terminal_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.terminal_mass

