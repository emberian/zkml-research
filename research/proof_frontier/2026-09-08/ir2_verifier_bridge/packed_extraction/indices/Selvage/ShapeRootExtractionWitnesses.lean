/- Concrete mixed-role and mixed-length logs test the public leaf-shape filter. -/
import Selvage.ShapeRootExtractionFresh

namespace Minidregg.Selvage.ShapeRootExtraction
open EfficientRootOpening CommitmentFreshTrace
open scoped Classical
noncomputable section

/-- The two public leaf widths retained in the counterexample. -/
def shortLeaf : List ℕ := List.replicate 20 0
def longLeaf : List ℕ := List.replicate 24 0
def valid20 (v : List ℕ) : Prop := v.length = 20

/-- A wrong-width leaf and a node precede the admissible leaf, all with digest seven. -/
def mixedShapeLog : Log (List ℕ) ℕ :=
  [(.leaf longLeaf,7),(.node 1 2,7),(.leaf shortLeaf,7)]

/-- Filtering really separates both public leaf width and expected node/leaf role. -/
theorem mixed_shape_matching :
    matchingLog valid20 false mixedShapeLog = [(.leaf shortLeaf,7)] ∧
      matchingLog valid20 true mixedShapeLog = [(.node 1 2,7)] := by
  simp [matchingLog,mixedShapeLog,admits,valid20,shortLeaf,longLeaf]

/-- Different-width leaves collide under the old unfiltered event. -/
theorem mixed_shape_old_collision : ResponseCollision mixedShapeLog := by
  refine ⟨(.leaf longLeaf,7),by simp [mixedShapeLog],
    (.leaf shortLeaf,7),by simp [mixedShapeLog],rfl,?_⟩
  intro h
  have hl : longLeaf.length = shortLeaf.length := congrArg List.length (Query.leaf.inj h)
  norm_num [longLeaf,shortLeaf] at hl

/-- Neither expected role has an internal response collision, and P=P has no late entry. -/
theorem mixed_shape_good : ¬Bad valid20 mixedShapeLog mixedShapeLog 7 := by
  have hc : ¬Collision valid20 mixedShapeLog := by
    simp only [Collision,mixed_shape_matching.1,mixed_shape_matching.2,ResponseCollision,
      List.mem_singleton]
    simp
  rintro (h|⟨e,he,hnot,_⟩)
  · exact hc h
  · exact hnot he

/-- The first two same-digest records cannot divert the depth-zero leaf extractor. -/
theorem mixed_shape_extracts_short :
    extractedAt valid20 mixedShapeLog [] 7 (fun i : Fin 0 => i.elim0) = shortLeaf := by
  simp [extractedAt,preimage,mixed_shape_matching.1,EfficientRootOpening.preimage]

/-- Teeth: the old global collision event is strictly stronger on this retained checkpoint. -/
theorem mixed_shape_filter_falsifier :
    EfficientRootOpening.Bad mixedShapeLog mixedShapeLog 7 ∧
      ¬Bad valid20 mixedShapeLog mixedShapeLog 7 ∧
      extractedAt valid20 mixedShapeLog [] 7 (fun i : Fin 0 => i.elim0) = shortLeaf :=
  ⟨Or.inl mixed_shape_old_collision,mixed_shape_good,mixed_shape_extracts_short⟩

/-- One positive-query ideal strategy fixes its only root before receiving any response. -/
def witnessStrategy : Strategy (List ℕ) 1 17 1 where
  query _ _ := .leaf shortLeaf
  roots _ _ := [0]
  roots_le _ _ := by simp

/-- Freshness, actual checkpoint origin and oracle coverage are inhabited together. -/
theorem family_probability_premises_inhabited :
    Fresh witnessStrategy ∧
      (∀ c : Fin 1 → Fin 17, CheckpointOrigin witnessStrategy c [] 0) ∧
      (∀ (c : Fin 1 → Fin 17) e, e ∈ entries witnessStrategy c → e ∈ oracleLog witnessStrategy c) := by
  have hf : Fresh witnessStrategy := by
    intro c i j _
    exact Subsingleton.elim i j
  refine ⟨hf,?_,?_⟩
  · intro c
    refine ⟨0,by omega,?_,?_⟩
    · intro e
      simp [prefixLog]
    · intro t _
      simp [witnessStrategy]
  · intro c e he
    simpa only [oracleLog_eq_entries witnessStrategy hf c] using he

end
end Minidregg.Selvage.ShapeRootExtraction

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.mixed_shape_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.mixed_shape_matching

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.mixed_shape_old_collision' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.mixed_shape_old_collision

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.mixed_shape_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.mixed_shape_good

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.mixed_shape_extracts_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.mixed_shape_extracts_short

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.mixed_shape_filter_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.mixed_shape_filter_falsifier

/-- info: 'Minidregg.Selvage.ShapeRootExtraction.family_probability_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ShapeRootExtraction.family_probability_premises_inhabited
