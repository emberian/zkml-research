/- Exact identification of the actual folding tower's consistency projection
with the replay's counted coherent-query maps. -/
import Selvage.Ir2FriModel
import Selvage.Ir2FriConsistency

namespace Minidregg.Selvage.Ir2Fri
open BabyBearExt4 ArityEight Ir2FriSchedule
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 100000

/-- Existing certified FoldingData has the runtime's exact modulus. -/
theorem square_val (n : ℕ) (hn : n < 14) (i : PowerTwoFriLevels 17 n) :
    ((tower.data n hn).sq i).val = i.val % 2^(17-(n+1)) := rfl

def squareStep : (j : Fin 5) → Index j → Index (j+1)
  | ⟨0,_⟩ => fun i => (tower.data 2 (by decide)).sq ((tower.data 1 (by decide)).sq ((tower.data 0 (by decide)).sq i))
  | ⟨1,_⟩ => fun i => (tower.data 5 (by decide)).sq ((tower.data 4 (by decide)).sq ((tower.data 3 (by decide)).sq i))
  | ⟨2,_⟩ => fun i => (tower.data 8 (by decide)).sq ((tower.data 7 (by decide)).sq ((tower.data 6 (by decide)).sq i))
  | ⟨3,_⟩ => fun i => (tower.data 11 (by decide)).sq ((tower.data 10 (by decide)).sq ((tower.data 9 (by decide)).sq i))
  | ⟨4,_⟩ => fun i => (tower.data 13 (by decide)).sq ((tower.data 12 (by decide)).sq i)
  | ⟨n+5,h⟩ => False.elim (by omega)

/-- All actual square maps identify the same parent as the native coherent map. -/
theorem squareStep_project (j : Fin 5) : squareStep j = project j := by
  funext i
  apply Fin.ext
  fin_cases j
  · change i.val % 65536 % 32768 % 16384 = i.val % 16384
    rw [Nat.mod_mod_of_dvd _ (by decide : 32768 ∣ 65536),Nat.mod_mod_of_dvd _ (by decide : 16384 ∣ 32768)]
  · change i.val % 8192 % 4096 % 2048 = i.val % 2048
    rw [Nat.mod_mod_of_dvd _ (by decide : 4096 ∣ 8192),Nat.mod_mod_of_dvd _ (by decide : 2048 ∣ 4096)]
  · change i.val % 1024 % 512 % 256 = i.val % 256
    rw [Nat.mod_mod_of_dvd _ (by decide : 512 ∣ 1024),Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 512)]
  · change i.val % 128 % 64 % 32 = i.val % 32
    rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 128),Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 64)]
  · change i.val % 16 % 8 = i.val % 8
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 16)]

/-- Projection mass is exactly the actual parent preimage mass divided by radix. -/
theorem projectStep_mass (j : Fin 5) (w : Index j → ℝ) (S : Finset (Index (j+1))) :
    consistencyMass (projectStep j w) S =
      consistencyMass w (Finset.univ.filter fun i => squareStep j i ∈ S)/(radix j:ℝ) := by
  fin_cases j <;> unfold projectStep
  all_goals simp only [projectConsistency8]
  all_goals repeat rw [projectConsistency_mass]
  all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  all_goals dsimp [squareStep,radix,stage]
  all_goals norm_num
  all_goals ring_nf
  all_goals rfl

/-- The two retained constructions are the same function, not merely similar
cardinality bounds. This lets the weighted invariant feed the actual sampler. -/
theorem projectStep_eq_projectWeight (j : Fin 5) (w : Index j → ℝ) :
    projectStep j w = projectWeight j w := by
  funext k
  have h := projectStep_mass j w {k}
  rw [squareStep_project] at h
  simpa [consistencyMass,projectWeight] using h

/-- Exact native transition equalities, with the same initial reduced-input mask. -/
def stepMasks (s : Words) (r : Fin 5 → Ext4) : Mask :=
  fun j k => s.wordAt r (j+1) (by omega) k = blockAt s j r k

/-- The mathematical prefix recurrence equals the exact counted mask recurrence. -/
theorem weightAt_eq_counted (s : Words) (r : Fin 5 → Ext4) (n : ℕ) (hn : n ≤ 5) :
    weightAt s r n hn = weight (initialMask s) (stepMasks s r) n hn := by
  induction n with
  | zero =>
    have hp : friPrefix r 0 hn = (fun i => i.elim0) := Subsingleton.elim _ _
    funext i
    simp only [weightAt,prefixWeight,hp,weight,initialMask]
    rfl
  | succ n ih =>
    let j : Fin 5 := ⟨n,by omega⟩
    rw [weightAt_succ s r j,weight_succ (initialMask s) (stepMasks s r) j,ih (by omega),projectStep_eq_projectWeight]
    rfl

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.square_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.square_val

/-- info: 'Minidregg.Selvage.Ir2Fri.squareStep_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.squareStep_project

/-- info: 'Minidregg.Selvage.Ir2Fri.projectStep_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.projectStep_mass

/-- info: 'Minidregg.Selvage.Ir2Fri.projectStep_eq_projectWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.projectStep_eq_projectWeight

/-- info: 'Minidregg.Selvage.Ir2Fri.weightAt_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.weightAt_eq_counted

