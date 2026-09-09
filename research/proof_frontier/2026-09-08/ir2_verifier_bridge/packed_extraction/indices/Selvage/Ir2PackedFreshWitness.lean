/- Structural inhabitation of the ideal execution interface at Q7/N1/q38.
A singleton digest alphabet has no cryptographic security meaning. -/
import Selvage.Ir2PackedFresh
import Selvage.Ir2PackedWitnesses

namespace Minidregg.Selvage.Ir2Fri.Packed.FreshWitness
open BabyBearExt4 Ir2FriSchedule PackedLeafEncoding EfficientRootOpening CommitmentFreshTrace
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Seven distinct actual packed macro-query keys. -/
def keys : Fin 7 → Query Leaf (Fin 1) :=
  ![.leaf (Witnesses.inputOpening 0).leaf,.leaf (Witnesses.inputOpening 1).leaf,
    .leaf (Witnesses.inputOpening 2).leaf,.leaf (Witnesses.inputOpening 3).leaf,
    .leaf (Witnesses.friOpening 0).leaf,.leaf (Witnesses.friOpening 4).leaf,.node 0 0]

def keyTag : Query Leaf (Fin 1) → ℕ
  | .leaf leaf => leaf.length
  | .node _ _ => 0

theorem key_tags (i : Fin 7) : keyTag (keys i) = (![24,2526,192,63,36,20,0] : Fin 7 → ℕ) i := by
  fin_cases i
  · change (Witnesses.inputOpening 0).leaf.length=24
    rw [Witnesses.input_leaf_length]; rfl
  · change (Witnesses.inputOpening 1).leaf.length=2526
    rw [Witnesses.input_leaf_length]; rfl
  · change (Witnesses.inputOpening 2).leaf.length=192
    rw [Witnesses.input_leaf_length]; rfl
  · change (Witnesses.inputOpening 3).leaf.length=63
    rw [Witnesses.input_leaf_length]; rfl
  · change (Witnesses.friOpening 0).leaf.length=36
    rw [Witnesses.fri_leaf_length]; rfl
  · change (Witnesses.friOpening 4).leaf.length=20
    rw [Witnesses.fri_leaf_length]; rfl
  · rfl

theorem keys_injective : Function.Injective keys := by
  intro i j h
  have ht := congrArg keyTag h
  rw [key_tags,key_tags] at ht
  fin_cases i <;> fin_cases j <;> simp_all

/-- All fresh keys are fixed before any response; the complete-cut checkpoints need no later roots. -/
def strategy : Strategy Leaf 7 1 10 where
  query t _ := keys t
  roots _ _ := []
  roots_le _ _ := by simp

def log : Packed.Log (Fin 1) := List.ofFn fun i => (keys i,0)

theorem strategy_fresh : CommitmentFreshTrace.Fresh strategy := by
  intro c i j h
  exact keys_injective h

theorem entries_eq (c : Coins 7 1) : entries strategy c = log := by
  apply congrArg List.ofFn
  funext t
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

theorem prefix_eq (c : Coins 7 1) : prefixLog strategy 7 le_rfl (friPrefix c 7 le_rfl) = log := by
  apply congrArg List.ofFn
  funext t
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

def hash : BinaryMerkle.HashSuite Leaf (Fin 1) where
  leaf _ := 0
  node _ _ := 0

theorem cached_eq (c : Coins 7 1) : cachedSuite strategy c 0 = hash := by
  cases cachedSuite strategy c 0
  unfold hash
  congr <;> exact Subsingleton.elim _ _

def inputOpening (b : Fin 5) : InputOpening (Fin 1) b where
  rows := (Witnesses.inputOpening b).rows
  salts := (Witnesses.inputOpening b).salts
  siblings := List.replicate 17 0

def friOpening (j : Fin 5) : FriOpening (Fin 1) j where
  values := (Witnesses.friOpening j).values
  salts := (Witnesses.friOpening j).salts
  siblings := List.replicate (nativeRowHeight j) 0

def queryOpening : QueryOpening (Fin 1) where
  input := inputOpening
  fri := friOpening

def checkpoints : Checkpoints (Fin 1) where
  input _ := ⟨log,0⟩
  fri _ _ := ⟨log,0⟩
  final _ := 1
  reduction i _ := Ir2Fri.Witnesses.farWord i

/-- The causal origin is the full seven-entry cut, with no later fresh responses. -/
theorem checkpoint_origin (c : Coins 7 1) : CheckpointOrigin strategy c log 0 := by
  refine ⟨7,le_rfl,?_,?_⟩
  · intro e
    rw [prefix_eq]
  · intro t ht
    omega

theorem family_origin (c : Coins 7 1) (x : External 38) (i : Fin 10) :
    CheckpointOrigin strategy c (rootFamily checkpoints x.1 i).log (rootFamily checkpoints x.1 i).root := by
  unfold rootFamily
  cases (finSumFinEquiv.symm i : Fin 5 ⊕ Fin 5) <;> exact checkpoint_origin c

theorem node_mem : (.node 0 0,0) ∈ log := List.mem_ofFn.mpr ⟨6,rfl⟩

theorem input_mem (b : Fin 5) : (.leaf (inputOpening b).leaf,0) ∈ log := by
  fin_cases b
  · exact List.mem_ofFn.mpr ⟨0,rfl⟩
  · exact List.mem_ofFn.mpr ⟨1,rfl⟩
  · exact List.mem_ofFn.mpr ⟨2,rfl⟩
  · exact List.mem_ofFn.mpr ⟨3,rfl⟩
  · exact List.mem_ofFn.mpr ⟨0,rfl⟩

theorem fri_mem (j : Fin 5) : (.leaf (friOpening j).leaf,0) ∈ log := by
  fin_cases j
  · exact List.mem_ofFn.mpr ⟨4,rfl⟩
  · exact List.mem_ofFn.mpr ⟨4,rfl⟩
  · exact List.mem_ofFn.mpr ⟨4,rfl⟩
  · exact List.mem_ofFn.mpr ⟨4,rfl⟩
  · exact List.mem_ofFn.mpr ⟨5,rfl⟩

theorem recompute_zero (k : ℕ) (bits : Fin k → Bool) :
    BinaryMerkle.recompute hash 0 bits (List.replicate k 0) = some 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,BinaryMerkle.recompute,ih]
    cases bits 0 <;> rfl

theorem node_log_zero (k : ℕ) (bits : Fin k → Bool) :
    EfficientRootOpening.pathLog hash 0 bits (List.replicate k 0) =
      List.replicate k (.node 0 0,0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,EfficientRootOpening.pathLog,recompute_zero,ih]
    cases bits 0 <;> simp [evaluate,hash,List.replicate_succ']

theorem path_mem (k : ℕ) (raw : Fin (2^k)) (leaf : Leaf)
    (hl : (.leaf leaf,0) ∈ log) (e : Query Leaf (Fin 1) × Fin 1)
    (he : e ∈ Packed.pathLog hash k raw leaf (List.replicate k 0)) : e ∈ log := by
  change e ∈ (.leaf leaf,0)::EfficientRootOpening.pathLog hash 0
    (fun i => binaryAddressBits k raw i.rev) (List.replicate k 0).reverse at he
  rw [List.reverse_replicate,node_log_zero] at he
  rcases List.mem_cons.mp he with h|h
  · exact h ▸ hl
  · exact (List.eq_of_mem_replicate h) ▸ node_mem

theorem verification_covered (raw : Fin 38 → Fin (2^17)) (e : Query Leaf (Fin 1) × Fin 1)
    (he : e ∈ verificationLog hash 38 raw (fun _ => queryOpening)) : e ∈ log := by
  obtain ⟨L,hL,he⟩ := List.mem_flatten.mp he
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hL
  rcases List.mem_append.mp he with hi|hf
  · obtain ⟨L,hL,he⟩ := List.mem_flatten.mp hi
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hL
    exact path_mem 17 (raw a) _ (input_mem b) e he
  · obtain ⟨L,hL,he⟩ := List.mem_flatten.mp hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hL
    exact path_mem (nativeRowHeight j) (rawParentRow j (raw a)) _ (fri_mem j) e he

/-- An actual-shaped, positive-query execution inhabits the ideal interface over one digest. -/
def execution : Execution 7 1 38 where
  strategy _ := strategy
  fresh _ := strategy_fresh
  checkpoints _ := checkpoints
  proverLog _ _ := log
  openings _ _ _ := queryOpening
  origins c x i := family_origin c x i
  checkpoints_logged _ _ := ⟨fun _ _ h => h,fun _ _ h => h⟩
  covered c x e he := by
    rw [cached_eq] at he
    rw [oracleLog_eq_entries strategy strategy_fresh c,entries_eq]
    rcases List.mem_append.mp he with h|h
    · exact h
    · exact verification_covered (rawQueries x) e h

/-- The source is the frozen monomial witness; this is not an implementation of PCS batching. -/
theorem initially_far (c : Coins 7 1) : InitiallyFar execution c := Ir2Fri.Witnesses.farWord_far

/-- The singleton-digest execution accepts the actual all-zero 38-query base-word sample. -/
theorem zero_accepts (c : Coins 7 1) (r : Fin 5 → Ext4) :
    ExecutionAccepts execution c (r,fun _ => 0) := by
  change Accepts (cachedSuite strategy c 0) checkpoints 38 r
    (rawQueries (r,fun _ => 0)) (fun _ => queryOpening)
  rw [cached_eq]
  have hr : rawQueries (r,fun _ : Fin 38 => 0) = fun _ => 0 := by
    funext a
    apply Fin.ext
    change (BabyBearModuloSampling.sampleBits 17 (0:BabyBear)).val = 0
    decide
  rw [hr]
  have hp (k : ℕ) (raw : Fin (2^k)) (leaf : Leaf) :
      PathAccepts hash 0 k raw leaf (List.replicate k 0) := by
    rw [PathAccepts,bottomUpRecompute_raw,List.reverse_replicate]
    exact recompute_zero k _
  have hs (n : ℕ) : suppliedAt checkpoints r 0 queryOpening n = 1 := by
    unfold suppliedAt
    split_ifs <;> rfl
  intro a
  change QueryAccepts hash checkpoints r 0 queryOpening
  refine ⟨⟨fun _ => hp 17 0 _,fun j => hp (nativeRowHeight j) (rawParentRow j 0) _⟩,?_,?_⟩
  · rw [hs]
    have hz : sourceIndex (0 : Fin (2^17)) = 0 := by apply Fin.ext; decide
    change 1 = Ir2Fri.Witnesses.farWord (sourceIndex 0)
    rw [hz]
    exact Ir2Fri.Witnesses.input_zero.symm
  · intro j
    rw [hs]
    exact (Witnesses.native_one j 0 (r j)).symm

/-- Explicit structural inhabitation, with actual source farness and a positive-query accepting sample. -/
theorem execution_inhabited : ∃ E : Execution 7 1 38,
    (∀ c, InitiallyFar E c) ∧ ∀ c r, ExecutionAccepts E c (r,fun _ => 0) :=
  ⟨execution,initially_far,zero_accepts⟩

end
end Minidregg.Selvage.Ir2Fri.Packed.FreshWitness

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.key_tags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.key_tags

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.keys_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.keys_injective

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.strategy_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.strategy_fresh

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.entries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.entries_eq

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.prefix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.prefix_eq

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.cached_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.cached_eq

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.checkpoint_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.checkpoint_origin

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.family_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.family_origin

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.node_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.node_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.input_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.input_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.fri_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.fri_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.recompute_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.recompute_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.node_log_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.node_log_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.path_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.path_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.verification_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.verification_covered

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.initially_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.initially_far

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.zero_accepts

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.execution_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.FreshWitness.execution_inhabited
