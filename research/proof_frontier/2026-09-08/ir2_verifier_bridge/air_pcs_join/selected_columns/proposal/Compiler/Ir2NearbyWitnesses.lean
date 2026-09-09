/- The selected application bridge handles words that are not exact codewords. -/
import Compiler.Ir2SelectedAirPcs
import Compiler.Ir2AirPcsOodWitnesses

namespace Minidregg.Compiler.Ir2NearbyColumns.Witnesses
open Polynomial Minidregg.Selvage BabyBearExt4 Ir2Fri Ir2FriSchedule Packed Pcs AirPolynomialOod Ir2AirPcsOod
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- A public word with one corrupted LDE position, in each supplied column. -/
def bumped (i : Index 0) : AllInputRows := fun _ _ _ => if i=0 then 1 else 0

/-- Zero is still within the actual3/5 agreement threshold. -/
theorem bumped_zero_near (k : Column) : NearColumn bumped k 0 := by
  refine ⟨by simp,Finset.univ.erase 0,?_,?_⟩
  · norm_num [Index,stage]
  · intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    simp [bumped,hi0]

theorem bumped_selects_zero (k : Column) : selected bumped k=0 :=
  selected_eq bumped k 0 (bumped_zero_near k)

/-- No degree≤16384 polynomial represents every position of this word.
Thus the new selected-column theorem covers a condition forbidden by the
previous exact-source premise, rather than merely renaming that premise. -/
theorem bumped_not_exact (k : Column) :
    ¬∃ p : Ext4[X],p.natDegree ≤ degree 0 ∧
      ∀ i,p.eval (31*domain 0 i)=algebraMap BabyBear Ext4 (bumped i k.1 k.2.1 k.2.2) := by
  rintro ⟨p,hp,hsource⟩
  have hn : NearColumn bumped k p := by
    refine ⟨hp,Finset.univ,?_,fun i _ => hsource i⟩
    norm_num [Index,stage]
  have heq : p=0 := (selected_eq bumped k p hn).symm.trans (bumped_selects_zero k)
  have h := hsource 0
  rw [heq] at h
  simp [bumped] at h

/-- A wrong1 claim is still ruled out despite the source's corrupted position. -/
theorem bumped_wrong_claim (t : Pcs.Term) :
    ¬JointColumnsNear bumped (fun _ _ _ => 0) (fun _ _ _ _ => 1) (degree 0) (2/5) := by
  apply not_joint_of_wrong_selected_claim bumped (fun _ _ _ => 0) (fun _ _ _ _ => 1) t
  rw [bumped_selects_zero]
  simp

abbrev W := Pcs.PackedWitnesses.plan

/-- The already retained actual-shaped zero commitments have selected polynomial zero. -/
theorem actual_selected_zero (k : Column) : selected W.rows k=0 := by
  apply selected_eq W.rows k 0
  refine ⟨by simp,Finset.univ,?_,fun i _ => Pcs.PackedWitnesses.originals_exact k i⟩
  norm_num [Index,stage]

def plan : SelectedPlan where
  rows _ := W.rows
  scale _ := 0
  expression _ := Ir2AirPcsOod.Witnesses.equation

theorem plan_equation : plan.equation=Ir2AirPcsOod.Witnesses.eqPlan := by
  have h : (fun γ => selected W.rows)=(fun _ : Ext4 => fun _ : Column => (0:Ext4[X])) := by
    funext γ k
    exact actual_selected_zero k
  unfold SelectedPlan.equation plan Ir2AirPcsOod.Witnesses.eqPlan
  congr

/-- The entire stronger head fires on the actual commitment/log carrier,
without supplying an exact source-polynomial membership premise. -/
theorem selected_head_fires :
    uniformProb AllCoins (fun x => AirAccepted plan.equation (fun _ => W) x.1 ∧
      Accepted Packed.Witnesses.hash W (fun _ => Packed.Witnesses.openings 38) x.2) ≤
      ((0:ℕ):ℝ)/Fintype.card Ext4+((0:ℕ):ℝ)/Fintype.card Ext4+pcsError+
      uniformProb AllCoins (BoundaryFailure Packed.Witnesses.hash (fun _ => W)
        (fun _ => Packed.Witnesses.openings 38) (fun _ => Packed.Witnesses.checkpointLog)) := by
  apply selected_air_pcs_soundness Packed.Witnesses.hash 0 0 Ir2AirPcsOod.Witnesses.badConstraint X
    (fun _ => 0) 0 plan (fun _ => W) (fun _ => Packed.Witnesses.openings 38)
    (fun _ => Packed.Witnesses.checkpointLog) Ir2AirPcsOod.Witnesses.bad_row.1
    Ir2AirPcsOod.Witnesses.bad_row.2 Ir2AirPcsOod.Witnesses.residual_degree
  · intro γ
    rw [plan_equation]
    exact Ir2AirPcsOod.Witnesses.exact_residual γ
  · intro x t
    simp [SelectedPlan.equation,plan,W,Pcs.PackedWitnesses.plan]
  · intro x
    rfl
  · intro x
    exact Pcs.PackedWitnesses.checkpoints_logged x.2

end
end Minidregg.Compiler.Ir2NearbyColumns.Witnesses

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_zero_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_zero_near

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_selects_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_selects_zero

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_not_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_not_exact

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_wrong_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.bumped_wrong_claim

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.actual_selected_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.actual_selected_zero

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.plan_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.plan_equation

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.Witnesses.selected_head_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.Witnesses.selected_head_fires

