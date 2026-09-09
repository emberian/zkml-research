/- Exact counting transport for the existing recursive consistency weights. -/
import Selvage.ArityEightConsistencySchedule

namespace Minidregg.Selvage.ArityEight.Schedule
open scoped BigOperators Classical
variable {F : Type} [Field F] [DecidableEq F] {ell m : ℕ}

/-- Actual three successive squaring maps, without a replacement domain. -/
def blockSquare (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (n : ℕ) (hn : n < m) (i : PowerTwoFriLevels ell (3*n)) :
    PowerTwoFriLevels ell (3*(n+1)) :=
  (T.data (3*n+2) (by omega)).sq ((T.data (3*n+1) (by omega)).sq
    ((T.data (3*n) (by omega)).sq i))

/-- Transport an initial source index through the actual folding maps. -/
def sourcePoint (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) :
    (n : ℕ) → n ≤ m → PowerTwoFriLevels ell 0 → PowerTwoFriLevels ell (3*n)
  | 0, _, i => i
  | n+1, hn, i => blockSquare T n (by omega) (sourcePoint T n (by omega) i)

/-- The prefix of the existing literal fold checks, pulled back to one source index. -/
def sourceChecks (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F) :
    (n : ℕ) → n ≤ m → PowerTwoFriLevels ell 0 → Prop
  | 0, _, _ => True
  | n+1, hn, i => sourceChecks T s r n (by omega) i ∧
    s.wordAt r (n+1) hn (sourcePoint T (n+1) hn i) =
      blockAt T s ⟨n,by omega⟩ r (sourcePoint T (n+1) hn i)

/-- Statement-first counting contract: recursive weights count exactly the
source indices passing those same checks, with eightfold normalization. -/
def SourceMassContract (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F) : Prop :=
  ∀ n (hn : n ≤ m) (S : Finset (PowerTwoFriLevels ell (3*n))),
    consistencyMass (consistencyAt T s r n hn) S * (8:ℝ)^n =
      ((Finset.univ.filter fun i => sourceChecks T s r n hn i ∧
        sourcePoint T n hn i ∈ S).card : ℝ)

omit [DecidableEq F] in
theorem block_project_mass (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (n : ℕ) (hn : n < m) (w : PowerTwoFriLevels ell (3*n) → ℝ)
    (S : Finset (PowerTwoFriLevels ell (3*(n+1)))) :
    consistencyMass (projectConsistency8 (T.data (3*n) (by omega))
      (T.data (3*n+1) (by omega)) (T.data (3*n+2) (by omega)) w) S =
      consistencyMass w (Finset.univ.filter fun i => blockSquare T n hn i ∈ S)/8 := by
  unfold projectConsistency8
  rw [projectConsistency_mass,projectConsistency_mass,projectConsistency_mass]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  dsimp [blockSquare]
  ring_nf
  congr 2

theorem consistency_mass_source (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F) : SourceMassContract T s r := by
  intro n
  induction n with
  | zero =>
    intro hn S
    simp [consistencyAt,prefixConsistency,consistencyMass,sourceChecks,sourcePoint]
  | succ n ih =>
    intro hn S
    let j : Fin m := ⟨n,by omega⟩
    rw [consistencyAt_succ T s r j,maskConsistency_mass,block_project_mass T n (by omega)]
    have h := ih (by omega) (Finset.univ.filter fun i =>
      blockSquare T n (by omega) i ∈ S.filter fun k =>
        s.wordAt r (n+1) hn k = blockAt T s j r k)
    have hset : (Finset.univ.filter fun i => sourceChecks T s r n (by omega) i ∧
        sourcePoint T n (by omega) i ∈ (Finset.univ.filter fun k =>
          blockSquare T n (by omega) k ∈ S.filter fun a =>
            s.wordAt r (n+1) hn a = blockAt T s j r a)) =
        (Finset.univ.filter fun i => sourceChecks T s r (n+1) hn i ∧
          sourcePoint T (n+1) hn i ∈ S) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,sourceChecks,sourcePoint]
      dsimp [j]
      tauto
    rw [hset] at h
    rw [pow_succ]
    convert h using 1
    ring

/-- The source endpoint cardinality is the target cardinality times eight per block. -/
theorem source_card_factor (hell : 3*m ≤ ell) (n : ℕ) (hn : n ≤ m) :
    (Fintype.card (PowerTwoFriLevels ell 0):ℝ) =
      (8:ℝ)^n * Fintype.card (PowerTwoFriLevels ell (3*n)) := by
  simp only [PowerTwoFriLevels,Fintype.card_fin,Nat.sub_zero,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (8:ℝ) = 2^3 by norm_num,←pow_mul,←pow_add]
  congr 1
  omega

/-- Uniform single-source acceptance is exactly the final normalized consistency mass. -/
theorem source_probability_mass (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F) (hell : 3*m ≤ ell)
    (n : ℕ) (hn : n ≤ m) :
    uniformProb (PowerTwoFriLevels ell 0) (sourceChecks T s r n hn) =
      consistencyMass (consistencyAt T s r n hn) Finset.univ /
        Fintype.card (PowerTwoFriLevels ell (3*n)) := by
  have h := consistency_mass_source T s r n hn Finset.univ
  simp only [Finset.mem_univ,and_true] at h
  unfold uniformProb
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←h,source_card_factor hell n hn]
  have h8 : (8:ℝ)^n ≠ 0 := by positivity
  field_simp

omit [DecidableEq F] in
/-- The recursive pullback is exactly the conjunction of existing round equations. -/
theorem sourceChecks_iff_all (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) (i : PowerTwoFriLevels ell 0) :
    sourceChecks T s r n hn i ↔ ∀ j : Fin n,
      s.wordAt r (j+1) (by omega) (sourcePoint T (j+1) (by omega) i) =
        blockAt T s ⟨j,by omega⟩ r (sourcePoint T (j+1) (by omega) i) := by
  induction n with
  | zero => simp [sourceChecks]
  | succ n ih =>
    rw [sourceChecks,Fin.forall_fin_succ',ih (by omega)]
    rfl

end Minidregg.Selvage.ArityEight.Schedule

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.block_project_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.block_project_mass

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.consistency_mass_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.consistency_mass_source

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.source_card_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.source_card_factor

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.source_probability_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.source_probability_mass

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.sourceChecks_iff_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.sourceChecks_iff_all

