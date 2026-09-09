/- Canonical IR2 PCS batching. Runtime source: Plonky3 82cfad7,
fri/src/verifier.rs:524-655; breadstuffs/vendor/plonky3-fri-82cfad73/
src/two_adic_pcs.rs:841-928. All 23 matrices have LDE logheight17;
alpha advances through batch, matrix, point, column without a height reset.
This is the arithmetic reduction on canonically typed inputs, not Rust parsing. -/
import Selvage.Ir2PackedCommitments
import Selvage.PcsBatchingFullUD

namespace Minidregg.Selvage.Ir2Fri.Pcs
open BabyBearExt4 Ir2FriSchedule Packed PcsBatching Polynomial
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def pointCount (b : Fin 5) : ℕ := if b.val=1 ∨ b.val=4 then 2 else 1

structure Term where
  batch : Fin 5
  matrix : Fin (widths batch).length
  point : Fin (pointCount batch)
  column : Fin (width batch matrix)

abbrev Column := (b : Fin 5) × (m : Fin (widths b).length) × Fin (width b m)
abbrev Points := (b : Fin 5) → (m : Fin (widths b).length) → Fin (pointCount b) → Ext4
abbrev Claims := (b : Fin 5) → (m : Fin (widths b).length) →
  Fin (pointCount b) → Fin (width b m) → Ext4

/-- Literal nesting order of the native verifier, including point before column. -/
def termList : List Term :=
  (List.ofFn fun b : Fin 5 =>
    (List.ofFn fun m : Fin (widths b).length =>
      (List.ofFn fun p : Fin (pointCount b) =>
        List.ofFn fun c : Fin (width b m) => (⟨b,m,p,c⟩ : Term)).flatten).flatten).flatten

theorem termList_length : termList.length=5271 := by
  simp only [termList,List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn]
  norm_num [pointCount,width,widths,PackedLeafEncoding.widthsOfList,List.ofFn_succ]

def termAt (j : Fin 5271) : Term := termList[j.val]'(by rw [termList_length]; exact j.isLt)

def Term.key (t : Term) : Column := ⟨t.batch,t.matrix,t.column⟩

/-- Every supplied column/point pair appears in the coefficient order. -/
theorem term_covered (t : Term) : ∃ j : Fin 5271, termAt j=t := by
  have hm : t ∈ termList := by
    unfold termList
    apply List.mem_flatten.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨t.batch,rfl⟩,?_⟩
    apply List.mem_flatten.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨t.matrix,rfl⟩,?_⟩
    apply List.mem_flatten.mpr
    exact ⟨_,List.mem_ofFn.mpr ⟨t.point,rfl⟩,List.mem_ofFn.mpr ⟨t.column,rfl⟩⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
  refine ⟨⟨j.val,by simpa [termList_length] using j.isLt⟩,?_⟩
  exact hj

theorem pointCount_pos (b : Fin 5) : 0 < pointCount b := by
  unfold pointCount
  split <;> decide

def representative (k : Column) : Term := ⟨k.1,k.2.1,⟨0,pointCount_pos k.1⟩,k.2.2⟩
def columnIndex (k : Column) : Fin 5271 := Classical.choose (term_covered (representative k))

theorem columnIndex_key (k : Column) : (termAt (columnIndex k)).key=k := by
  unfold columnIndex
  rw [Classical.choose_spec (term_covered (representative k))]
  rfl

def data (rows : Index 0 → AllInputRows) (points : Points) (claims : Claims) :
    PcsBatching.Data Ext4 (Index 0) Column 5270 where
  column j := (termAt j).key
  source k i := algebraMap BabyBear Ext4 (rows i k.1 k.2.1 k.2.2)
  point j := let t := termAt j; points t.batch t.matrix t.point
  claim j := let t := termAt j; claims t.batch t.matrix t.point t.column

/-- One physical polynomial per actual input column, shared across all its
supplied opening points, agreeing with the extracted base rows on the same S. -/
def JointColumnsNear (rows : Index 0 → AllInputRows) (points : Points) (claims : Claims)
    (d : ℕ) (δ : ℝ) : Prop :=
  ∃ S : Finset (Index 0), (1-δ)*(Fintype.card (Index 0) : ℝ) ≤ S.card ∧
    ∃ p : Column → Ext4[X],
      (∀ k, (p k).natDegree ≤ d ∧ ∀ i ∈ S,
        (p k).eval (31*domain 0 i)=algebraMap BabyBear Ext4 (rows i k.1 k.2.1 k.2.2)) ∧
      ∀ t : Term, (p t.key).eval (points t.batch t.matrix t.point)=
        claims t.batch t.matrix t.point t.column

theorem jointColumnsNear_of_data (rows : Index 0 → AllInputRows) (points : Points) (claims : Claims)
    {d : ℕ} {δ : ℝ} (h : (data rows points claims).JointNear (domain 0) 31 d δ) :
    JointColumnsNear rows points claims d δ := by
  obtain ⟨S,hS,p,hp,hshared⟩ := h
  refine ⟨S,hS,(fun k => p (columnIndex k)),?_,?_⟩
  · intro k
    refine ⟨(hp (columnIndex k)).1,?_⟩
    intro i hi
    have hki := (hp (columnIndex k)).2.2 i hi
    change (p (columnIndex k)).eval (31*domain 0 i)=
      algebraMap BabyBear Ext4 (rows i ((termAt (columnIndex k)).key).1
        ((termAt (columnIndex k)).key).2.1 ((termAt (columnIndex k)).key).2.2) at hki
    exact hki.trans (congrArg (fun key : Column =>
      algebraMap BabyBear Ext4 (rows i key.1 key.2.1 key.2.2)) (columnIndex_key k))
  · intro t
    obtain ⟨j,rfl⟩ := term_covered t
    have hkey : (data rows points claims).column (columnIndex (termAt j).key)=
        (data rows points claims).column j := by
      change (termAt (columnIndex (termAt j).key)).key=(termAt j).key
      exact columnIndex_key _
    dsimp only
    rw [hshared _ _ hkey]
    exact (hp j).2.1

def termQuotient (points : Points) (claims : Claims) (i : Index 0)
    (rows : AllInputRows) (t : Term) : Ext4 :=
  (claims t.batch t.matrix t.point t.column-
    algebraMap BabyBear Ext4 (rows t.batch t.matrix t.column))/
      (points t.batch t.matrix t.point-31*domain 0 i)

/-- The actual one-height Reduction supplied to packed extraction. -/
def reduction (points : Points) (claims : Claims) (α : Ext4) : Packed.Reduction :=
  fun i rows => ∑ j : Fin 5271, α^j.val*termQuotient points claims i rows (termAt j)

theorem reduction_eq_curve (rows : Index 0 → AllInputRows) (points : Points)
    (claims : Claims) (α : Ext4) :
    (fun i => reduction points claims α i (rows i))=
      curveWord ((data rows points claims).quotientWord (domain 0) 31) α := by
  rfl

/-- The loop state retains alpha's power across all matrices and batches. -/
def alphaLoop {F : Type*} [Field F] (α : F) (values : List F) (power total : F) : F × F :=
  values.foldl (fun st v => (st.1*α,st.2+st.1*v)) (power,total)

theorem alphaLoop_ofFn {F : Type*} [Field F] (α : F) {n : ℕ}
    (values : Fin n → F) (power total : F) :
    alphaLoop α (List.ofFn values) power total=
      (power*α^n,total+power*∑ j : Fin n, α^j.val*values j) := by
  induction n generalizing power total with
  | zero => simp [alphaLoop]
  | succ n ih =>
    have hsum : (∑ j : Fin (n+1), α^j.val*values j)=
        values 0+α*(∑ j : Fin n, α^j.val*values j.succ) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    change alphaLoop α ((List.ofFn values)) power total=_
    rw [List.ofFn_succ]
    change alphaLoop α (List.ofFn (fun i => values i.succ)) (power*α) (total+power*values 0)=_
    rw [ih,hsum]
    apply Prod.ext <;> simp only [pow_succ] <;> ring

/-- The literal sequential power/accumulator loop equals the reduced word. -/
theorem native_loop_eq_reduction (points : Points) (claims : Claims) (α : Ext4)
    (i : Index 0) (rows : AllInputRows) :
    alphaLoop α (List.ofFn (fun j : Fin 5271 => termQuotient points claims i rows (termAt j))) 1 0=
      (α^5271,reduction points claims α i rows) := by
  rw [alphaLoop_ofFn]
  simp only [one_mul,zero_add,reduction]

theorem coset31_ne_zero : (31 : Ext4) ≠ 0 := by
  have h : (31 : BabyBear) ≠ 0 := by decide
  intro hx
  apply h
  apply (algebraMap BabyBear Ext4).injective
  simpa only [map_natCast,map_zero] using hx

/-- Full-UD parameter arithmetic for the actual rate1/8 and radius2/5. -/
theorem batching_parameters :
    (1 : ℕ) ≤ 5270 ∧ (1 : ℕ) ≤ degree 0 ∧
    (0 : ℝ) < 2/5 ∧
    (degree 0 : ℝ) < (1-2*(2/5:ℝ))*(Fintype.card (Index 0) : ℝ) ∧
    5270*Fintype.card (Index 0)=690749440 := by
  norm_num [degree,Index,stage]

/-- If fixed input rows and claims lack a joint nearby physical-polynomial
explanation of degree≤16384, at most5270*131072 alpha values can make the actual
PCS-reduced word close to the FRI code of degree<16384. -/
theorem actual_bad_alpha_card (rows : Index 0 → AllInputRows) (points : Points) (claims : Claims)
    (hoff : (data rows points claims).OffDomain (domain 0) 31)
    (hfar : ¬JointColumnsNear rows points claims (degree 0) (2/5)) :
    (Finset.univ.filter (fun α => close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0))
      (fun i => reduction points claims α i (rows i)))).card ≤ 690749440 := by
  simp_rw [reduction_eq_curve]
  have h := bad_alpha_card_le (data rows points claims) (domain 0) 31 coset31_ne_zero
    batching_parameters.1 batching_parameters.2.1 batching_parameters.2.2.1
    batching_parameters.2.2.2.1 hoff (fun hj => hfar (jointColumnsNear_of_data rows points claims hj))
  simpa only [batching_parameters.2.2.2.2] using h

/-- Fresh uniform alpha only. No identification with the deployed sponge is
made; rows, points and claims precede this challenge in the statement. -/
theorem actual_bad_alpha_probability (rows : Index 0 → AllInputRows) (points : Points) (claims : Claims)
    (hoff : (data rows points claims).OffDomain (domain 0) 31)
    (hfar : ¬JointColumnsNear rows points claims (degree 0) (2/5)) :
    uniformProb Ext4 (fun α => close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0))
      (fun i => reduction points claims α i (rows i))) ≤
      (690749440:ℝ)/(modulus^4:ℕ) := by
  have h := actual_bad_alpha_card rows points claims hoff hfar
  unfold uniformProb
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hF : (0 : ℝ) < Fintype.card Ext4 := by exact_mod_cast Fintype.card_pos
  have hb := (div_le_div_iff_of_pos_right hF).mpr (show
      ((Finset.univ.filter (fun α => close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0))
        (fun i => reduction points claims α i (rows i)))).card : ℝ) ≤ 690749440 by exact_mod_cast h)
  have hcard : Fintype.card Ext4=modulus^4 := ext4_card
  simpa only [hcard] using hb

/- Exact dependencies of every theorem in this module. -/

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.termList_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.termList_length

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.term_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.term_covered

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.pointCount_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.pointCount_pos

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.columnIndex_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.columnIndex_key

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.jointColumnsNear_of_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.jointColumnsNear_of_data

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.reduction_eq_curve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.reduction_eq_curve

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.alphaLoop_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.alphaLoop_ofFn

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.native_loop_eq_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.native_loop_eq_reduction

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.coset31_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.coset31_ne_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.batching_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.batching_parameters

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.actual_bad_alpha_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.actual_bad_alpha_card

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.actual_bad_alpha_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.actual_bad_alpha_probability

end
end Minidregg.Selvage.Ir2Fri.Pcs
