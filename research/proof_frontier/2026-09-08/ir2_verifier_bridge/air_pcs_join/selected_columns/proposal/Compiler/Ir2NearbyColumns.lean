/- Commitment-time unique nearby columns, without exact codeword membership. -/
import Compiler.Ir2AirPcsOod

namespace Minidregg.Compiler.Ir2NearbyColumns
open Polynomial Minidregg.Selvage BabyBearExt4 Ir2Fri Ir2FriSchedule Packed Pcs
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- A single column polynomial agrees with a fixed commitment-time word on
at least3/5 of the actual131072-position domain; agreement need not be exact. -/
def NearColumn (rows : Index 0 → AllInputRows) (k : Column) (p : Ext4[X]) : Prop :=
  p.natDegree ≤ degree 0 ∧ ∃ S : Finset (Index 0),
    (3/5:ℝ)*(Fintype.card (Index 0):ℝ) ≤ S.card ∧
    ∀ i ∈ S,p.eval (31*domain 0 i)=algebraMap BabyBear Ext4 (rows i k.1 k.2.1 k.2.2)

/-- The actual agreement threshold forces an overlap larger than the inclusive
degree cap. This integer inequality is strict:16384 < intersection.card. -/
theorem overlap_large (S T : Finset (Index 0))
    (hS : (3/5:ℝ)*(Fintype.card (Index 0):ℝ) ≤ S.card)
    (hT : (3/5:ℝ)*(Fintype.card (Index 0):ℝ) ≤ T.card) : degree 0 < (S∩T).card := by
  have hn : Fintype.card (Index 0)=131072 := by norm_num [Index,stage]
  have hU := Finset.card_le_univ (S∪T)
  have hI := Finset.card_inter_add_card_union S T
  have hUr : ((S∪T).card:ℝ) ≤ 131072 := by exact_mod_cast hU.trans_eq hn
  have hIr : ((S∩T).card:ℝ)+((S∪T).card:ℝ)=(S.card:ℝ)+(T.card:ℝ) := by exact_mod_cast hI
  rw [hn] at hS hT
  have hl : (16384:ℝ)<((S∩T).card:ℝ) := by norm_num at hS hT; linarith
  have hd : degree 0=16384 := by norm_num [Ir2Fri.degree,stage]
  rw [hd]
  exact_mod_cast hl

/-- Any two sufficiently near candidate polynomials are literally equal. -/
theorem unique (rows : Index 0 → AllInputRows) (k : Column) {p q : Ext4[X]}
    (hp : NearColumn rows k p) (hq : NearColumn rows k q) : p=q := by
  obtain ⟨hpd,S,hS,hps⟩ := hp
  obtain ⟨hqd,T,hT,hqt⟩ := hq
  apply PcsBatching.eq_of_common_set (PcsBatching.cosetDomain (domain 0) 31 coset31_ne_zero)
    hpd hqd (S∩T) (overlap_large S T hS hT)
  intro i hi
  exact (hps i (Finset.mem_inter.mp hi).1).trans (hqt i (Finset.mem_inter.mp hi).2).symm

/-- Deterministic mathematical selection from the fixed word alone. A default
zero is used when no sufficiently near polynomial exists; no existence premise
or proof of efficient decoding is hidden in this definition. -/
def selected (rows : Index 0 → AllInputRows) (k : Column) : Ext4[X] :=
  if h : ∃ p,NearColumn rows k p then Classical.choose h else 0

theorem selected_eq (rows : Index 0 → AllInputRows) (k : Column) (p : Ext4[X])
    (hp : NearColumn rows k p) : selected rows k=p := by
  unfold selected
  split
  · rename_i h
    exact unique rows k (Classical.choose_spec h) hp
  · rename_i h
    exact False.elim (h ⟨p,hp⟩)

theorem selected_degree (rows : Index 0 → AllInputRows) (k : Column) :
    (selected rows k).natDegree ≤ degree 0 := by
  unfold selected
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · simp

/-- Every common-nearby PCS explanation must use these pre-opening selected
columns, so all its claims refer to polynomials fixed by commitment-time rows. -/
theorem claims_of_joint (rows : Index 0 → AllInputRows) (points : Points) (claims : Claims)
    (h : JointColumnsNear rows points claims (degree 0) (2/5)) :
    ∀ t : Pcs.Term,claims t.batch t.matrix t.point t.column=
      (selected rows t.key).eval (points t.batch t.matrix t.point) := by
  obtain ⟨S,hS,p,hp,hclaims⟩ := h
  have heq : ∀ k,selected rows k=p k := by
    intro k
    apply selected_eq rows k (p k)
    refine ⟨(hp k).1,S,?_,(hp k).2⟩
    convert hS using 1
    norm_num
  intro t
  rw [heq]
  exact (hclaims t).symm

theorem not_joint_of_wrong_selected_claim (rows : Index 0 → AllInputRows)
    (points : Points) (claims : Claims) (t : Pcs.Term)
    (hwrong : claims t.batch t.matrix t.point t.column ≠
      (selected rows t.key).eval (points t.batch t.matrix t.point)) :
    ¬JointColumnsNear rows points claims (degree 0) (2/5) :=
  fun h => hwrong (claims_of_joint rows points claims h t)

end
end Minidregg.Compiler.Ir2NearbyColumns

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.overlap_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.overlap_large

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.unique

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.selected_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.selected_eq

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.selected_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.selected_degree

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.claims_of_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.claims_of_joint

/-- info: 'Minidregg.Compiler.Ir2NearbyColumns.not_joint_of_wrong_selected_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2NearbyColumns.not_joint_of_wrong_selected_claim

