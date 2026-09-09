/- Actual packed native rows equal the IR2 mathematical folding steps.
Node and fibre premises are derived from the certified tower and actual row maps. -/
import Selvage.Ir2FriProjection

namespace Minidregg.Selvage.Ir2Fri
open BabyBearExt4 ArityEight Ir2FriSchedule
open Minidregg.Theory.BitReverseFriTransport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Every current domain has the native repeated-squaring root convention. -/
theorem native_domain_source (n : ℕ) (i : Index n) :
    domain n i = TwoAdic.omega (17-stage n)^i.val := by
  have hs : stage n + (17-stage n) = 17 := by
    have h := stage_le n
    omega
  have h := omega_power_drop (stage n) (17-stage n) (by omega)
  rw [hs] at h
  change (TwoAdic.omega 17^(2^(stage n)))^i.val = _
  rw [h]

/-- Parent-row logheight in the actual packed native matrix. -/
def nativeRowHeight (j : Fin 5) : ℕ := 17-stage (j+1)

/-- The observed row logarity, including the final arity-four round. -/
def nativeLogArity (j : Fin 5) : ℕ := stage (j+1)-stage j

theorem native_height_add (j : Fin 5) : nativeRowHeight j + nativeLogArity j = 17-stage j := by
  unfold nativeRowHeight nativeLogArity
  have h := stage_monotone (show j.val ≤ j.val+1 by omega)
  have h' := stage_le (j+1)
  omega

/-- The rowNodes constructor's root-height premise is discharged for all five actual rounds. -/
theorem native_height_supported (j : Fin 5) : nativeRowHeight j + nativeLogArity j ≤ 27 := by
  rw [native_height_add]
  omega

/-- The existing native coset-node construction at this actual stage and parent row. -/
def nativeRowNodes (j : Fin 5) (row : Index (j+1)) :
    P3Barycentric.CosetNodes Ext4 (radix j) :=
  rowNodes (nativeRowHeight j) (nativeLogArity j) (native_height_supported j) row

/-- The existing packed-row source indices, transported only by the proved height identity. -/
def nativeRowSourceIndex (j : Fin 5) (row : Index (j+1)) (c : Fin (radix j)) : Index j :=
  Fin.cast (congrArg (fun n : ℕ => 2^n) (native_height_add j))
    (rowSourceIndex (nativeRowHeight j) (nativeLogArity j) row c)

/-- Native parent row number in natural exponent order. -/
def nativeParentIndex (j : Fin 5) (row : Index (j+1)) : Index (j+1) :=
  ⟨reverseIndex (nativeRowHeight j) row.val,reverseIndex_lt _ _⟩

/-- Source indexing is exactly the existing bit-reversed row-column construction. -/
theorem nativeRowSourceIndex_value (j : Fin 5) (row : Index (j+1)) (c : Fin (radix j)) :
    (nativeRowSourceIndex j row c).val =
      (rowSourceIndex (nativeRowHeight j) (nativeLogArity j) row c).val := rfl

/-- Actual native row nodes are actual source-domain points, not a desired fold-equality premise. -/
theorem nativeRowNodes_domain (j : Fin 5) (row : Index (j+1)) (c : Fin (radix j)) :
    (nativeRowNodes j row).nodes c = domain j (nativeRowSourceIndex j row c) := by
  rw [native_domain_source,nativeRowSourceIndex_value]
  change (rowNodes (nativeRowHeight j) (nativeLogArity j) (native_height_supported j) row).nodes c = _
  rw [rowNodes_sourceIndex]
  exact congrArg (fun x : Ext4 => x^(rowSourceIndex (nativeRowHeight j)
    (nativeLogArity j) row c).val) (congrArg TwoAdic.omega (native_height_add j))

/-- Every actual row source position has the same concrete projected parent. -/
theorem nativeRowSourceIndex_project (j : Fin 5) (row : Index (j+1)) (c : Fin (radix j)) :
    project j (nativeRowSourceIndex j row c) = nativeParentIndex j row := by
  apply Fin.ext
  exact rowSourceIndex_parent (nativeRowHeight j) (nativeLogArity j) row c

/-- Statement-first native interpolation/fold-step interface on every actual row. -/
def NativeFoldContract : Prop := ∀ (j : Fin 5) (row : Index (j+1))
    (f : Index j → Ext4) (β : Ext4),
  P3Barycentric.native (nativeRowNodes j row) (fun c => f (nativeRowSourceIndex j row c)) β =
    foldStep j f β (nativeParentIndex j row)

/-- The actual binary folding composition has the native row's exact parent exponent. -/
theorem nativeRowSourceIndex_squareStep (j : Fin 5) (row : Index (j+1)) (c : Fin (radix j)) :
    squareStep j (nativeRowSourceIndex j row c) = nativeParentIndex j row := by
  rw [squareStep_project]
  exact nativeRowSourceIndex_project j row c

/-- Native interpolation is the existing foldStep at every actual parent row.
The node and fibre hypotheses of native_eq_fold8/4 are discharged above. -/
theorem native_eq_foldStep : NativeFoldContract := by
  intro j row f β
  fin_cases j
  · exact native_eq_fold8 (tower.data 0 (by decide)) (tower.data 1 (by decide))
      (tower.data 2 (by decide)) (nativeRowNodes 0 row) (nativeRowSourceIndex 0 row)
      (nativeParentIndex 0 row) (nativeRowNodes_domain 0 row)
      (nativeRowSourceIndex_squareStep 0 row) f β
  · exact native_eq_fold8 (tower.data 3 (by decide)) (tower.data 4 (by decide))
      (tower.data 5 (by decide)) (nativeRowNodes 1 row) (nativeRowSourceIndex 1 row)
      (nativeParentIndex 1 row) (nativeRowNodes_domain 1 row)
      (nativeRowSourceIndex_squareStep 1 row) f β
  · exact native_eq_fold8 (tower.data 6 (by decide)) (tower.data 7 (by decide))
      (tower.data 8 (by decide)) (nativeRowNodes 2 row) (nativeRowSourceIndex 2 row)
      (nativeParentIndex 2 row) (nativeRowNodes_domain 2 row)
      (nativeRowSourceIndex_squareStep 2 row) f β
  · exact native_eq_fold8 (tower.data 9 (by decide)) (tower.data 10 (by decide))
      (tower.data 11 (by decide)) (nativeRowNodes 3 row) (nativeRowSourceIndex 3 row)
      (nativeParentIndex 3 row) (nativeRowNodes_domain 3 row)
      (nativeRowSourceIndex_squareStep 3 row) f β
  · exact native_eq_fold4 (tower.data 12 (by decide)) (tower.data 13 (by decide))
      (nativeRowNodes 4 row) (nativeRowSourceIndex 4 row) (nativeParentIndex 4 row)
      (nativeRowNodes_domain 4 row) (nativeRowSourceIndex_squareStep 4 row) f β

/-- The actual row node/fibre premises and the resulting equality contract are inhabited together. -/
theorem native_premises_inhabited : ∃ (j : Fin 5) (row : Index (j+1)),
    (∀ c, (nativeRowNodes j row).nodes c = domain j (nativeRowSourceIndex j row c)) ∧
    (∀ c, squareStep j (nativeRowSourceIndex j row c) = nativeParentIndex j row) ∧
    NativeFoldContract :=
  ⟨4,0,nativeRowNodes_domain 4 0,nativeRowSourceIndex_squareStep 4 0,native_eq_foldStep⟩

/-- A nonconstant actual-domain word is evaluated as X on every native row. -/
theorem native_linear_value (j : Fin 5) (row : Index (j+1)) (β : Ext4) :
    P3Barycentric.native (nativeRowNodes j row)
      (fun c => domain j (nativeRowSourceIndex j row c)) β = β := by
  have hr : 1 < radix j := by
    rw [radix_exact]
    split_ifs <;> decide
  have hp : (Polynomial.X : Polynomial Ext4).degree < radix j := by
    rw [Polynomial.degree_X]
    exact_mod_cast hr
  have hword : (fun c => domain j (nativeRowSourceIndex j row c)) =
      (fun c => (Polynomial.X : Polynomial Ext4).eval ((nativeRowNodes j row).nodes c)) := by
    funext c
    simpa only [Polynomial.eval_X] using (nativeRowNodes_domain j row c).symm
  rw [hword,P3Barycentric.native_of_polynomial _ _ hp]
  simp

/-- The equality contract fires on the same nonconstant word at every scalar. -/
theorem foldStep_linear_value (j : Fin 5) (row : Index (j+1)) (β : Ext4) :
    foldStep j (domain j) β (nativeParentIndex j row) = β := by
  rw [←native_eq_foldStep j row (domain j) β,native_linear_value]

/-- Teeth: a scalar-ignoring native row cannot satisfy the proved actual-row contract. -/
theorem native_scalar_falsifier (j : Fin 5) (row : Index (j+1)) :
    P3Barycentric.native (nativeRowNodes j row)
        (fun c => domain j (nativeRowSourceIndex j row c)) 0 ≠
      P3Barycentric.native (nativeRowNodes j row)
        (fun c => domain j (nativeRowSourceIndex j row c)) 1 := by
  rw [native_linear_value,native_linear_value]
  exact zero_ne_one

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.native_domain_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_domain_source

/-- info: 'Minidregg.Selvage.Ir2Fri.native_height_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_height_add

/-- info: 'Minidregg.Selvage.Ir2Fri.native_height_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_height_supported

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_value

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeRowNodes_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeRowNodes_domain

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_project

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_squareStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_squareStep

/-- info: 'Minidregg.Selvage.Ir2Fri.native_eq_foldStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_eq_foldStep

/-- info: 'Minidregg.Selvage.Ir2Fri.native_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_premises_inhabited

/-- info: 'Minidregg.Selvage.Ir2Fri.native_linear_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_linear_value

/-- info: 'Minidregg.Selvage.Ir2Fri.foldStep_linear_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.foldStep_linear_value

/-- info: 'Minidregg.Selvage.Ir2Fri.native_scalar_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_scalar_falsifier

