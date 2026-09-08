/- Small finite adaptive trace controls and actual instrumented row witnesses. -/
import Selvage.SuppliedScheduleTrace
import Selvage.ArityEightLoggedWitnesses

namespace Minidregg.Selvage.CommitmentFreshTrace.Witnesses
open scoped Classical

/-- The second query contains the first answer; leaf/node tags ensure freshness. -/
def adaptive : Strategy Bool 2 17 1 where
  query t p := if h : t.val = 0 then .leaf false else .node (p ⟨0,by omega⟩) 2
  roots _ _ := [4]
  roots_le _ _ := by decide

def good : Fin 2 → Fin 17 := ![1,3]
def late : Fin 2 → Fin 17 := ![1,4]
def collision : Fin 2 → Fin 17 := ![1,1]

theorem adaptive_fresh : Fresh adaptive := by
  intro c i j h
  fin_cases i <;> fin_cases j <;> simp_all [entry,adaptive]

theorem adaptive_really_uses_answer :
    adaptive.query 1 (fun _ => 1) ≠ adaptive.query 1 (fun _ => 2) := by decide

theorem good_no_bad : ¬Bad adaptive good := by
  unfold Bad Collides
  decide

theorem late_observed : EfficientRootOpening.LateTarget [] (entries adaptive late) 4 := by
  exact Classical.not_not.mp ((lateWitness_none_iff [] (entries adaptive late) 4).mpr.mt (by decide))

theorem collision_observed : EfficientRootOpening.ResponseCollision (entries adaptive collision) := by
  exact Classical.not_not.mp ((collisionWitness_none_iff (entries adaptive collision)).mpr.mt (by decide))

theorem empty_origin (c : Fin 2 → Fin 17) : CheckpointOrigin adaptive c [] 4 := by
  refine ⟨0,by decide,?_,?_⟩
  · intro e
    simp [prefixLog]
  · intro t ht
    simp [adaptive]

theorem late_extracted : lateWitness [] (entries adaptive late) 4 =
    some (.node 1 2,4) := by decide

theorem collision_extracted : collisionWitness (entries adaptive collision) =
    some ((.leaf false,1),(.node 1 2,1)) := by decide

/-- A concrete typed leaf/node collision exists in the canonically completed suite. -/
theorem collision_typed :
    EfficientRootOpening.evaluate (cachedSuite adaptive collision 0) (.leaf false) =
      EfficientRootOpening.evaluate (cachedSuite adaptive collision 0) (.node 1 2) := by
  have h0 := cachedSuite_entry adaptive adaptive_fresh collision 0 0
  have h1 := cachedSuite_entry adaptive adaptive_fresh collision 0 1
  simpa [entry,adaptive,collision] using h0.trans h1.symm

/-- The derived probability bound is nontrivial on an inhabited adaptive strategy. -/
theorem adaptive_probability : uniformProb (Fin 2 → Fin 17) (Bad adaptive) ≤ 9/17 := by
  have h := bad_probability adaptive
  norm_num at h ⊢
  exact h

/-- No roots are declared by this one-query strategy. -/
def undeclared : Strategy Bool 1 17 0 where
  query _ _ := .leaf false
  roots _ _ := []
  roots_le _ _ := by decide

/-- Choosing root equal to the new response creates a late hit on every tape. -/
theorem future_root_hit (c : Fin 1 → Fin 17) :
    EfficientRootOpening.LateTarget [] (entries undeclared c) (c 0) := by
  refine ⟨(.leaf false,c 0),?_,by simp,Or.inl rfl⟩
  exact List.mem_ofFn.mpr ⟨0,rfl⟩

/-- The causal origin requirement excludes that future-root attack. -/
theorem future_root_origin_false (c : Fin 1 → Fin 17) :
    ¬CheckpointOrigin undeclared c [] (c 0) := by
  rintro ⟨k,hk,hmem,hroot⟩
  have hzero : k = 0 := by
    by_contra hn
    have he : entry undeclared c 0 ∈ prefixLog undeclared k hk (friPrefix c k hk) :=
      (mem_prefixLog_iff undeclared c k hk _).mpr ⟨0,by omega,rfl⟩
    simpa using (hmem _).mpr he
  have h := hroot 0 (by omega)
  simp [undeclared] at h

end Minidregg.Selvage.CommitmentFreshTrace.Witnesses

namespace Minidregg.Selvage.SuppliedOpeningTrace.Witnesses
open ArityEight ArityEight.Witnesses ArityEight.Witnesses.Logged

/-- The new instrumented checker accepts the existing far-source supplied witness. -/
theorem instrumented_accepts (β : F) :
    (rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 0 (row 0)).1 = true := by
  rw [rowRun_check]
  exact row_zero_check β

/-- Honest paths cannot rescue the wrong row's fold equation. -/
theorem instrumented_rejects (β : F) :
    (rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 1 (row 1)).1 = false := by
  rw [rowRun_check]
  exact row_one_check β

/-- Farness, genuine supplied acceptance and generated path logs coexist. -/
theorem instrumented_inhabited (β : F) :
    EfficientRootOpening.Far_E (1/5:ℝ) 4 (reedSolomonCode (dom 0) 8) checkpoint 0 sourceRoot ∧
    (rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 0 (row 0)).1 = true ∧
    RowLogged H (rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot β 0 (row 0)).2
      D₀ D₁ D₂ 0 (row 0) :=
  ⟨(supplied_premises_inhabited β).1,instrumented_accepts β,rowRun_logged _ _ _ _ _ _ _ _ _ _⟩

theorem instrumented_record_count :
    (rowRun H D₀ D₁ D₂ sourceRoot inputRoot nextRoot 0 0 (row 0)).2.length = 44 := by decide

end Minidregg.Selvage.SuppliedOpeningTrace.Witnesses

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.adaptive_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.adaptive_fresh

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.adaptive_really_uses_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.adaptive_really_uses_answer

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.good_no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.good_no_bad

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.late_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.late_observed

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.collision_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.collision_observed

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.empty_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.empty_origin

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.late_extracted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.late_extracted

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.collision_extracted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.collision_extracted

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.collision_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.collision_typed

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.adaptive_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.adaptive_probability

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.future_root_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.future_root_hit

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.Witnesses.future_root_origin_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.Witnesses.future_root_origin_false

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_accepts

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_rejects

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_inhabited

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_record_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.Witnesses.instrumented_record_count
