/- Actual packed-profile nonvacuity, using finite shape-filtered checkpoints.
The reduction is an explicit mathematical far-word witness, not a PCS batching claim. -/
import Selvage.Ir2PackedExtraction
import Selvage.Ir2FriWitnesses

namespace Minidregg.Selvage.Ir2Fri.Packed.Witnesses
open BabyBearExt4 Ir2FriSchedule PackedLeafEncoding EfficientRootOpening
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A deliberately collision-rich suite tests the narrower actual-shape extractor. -/
def hash : BinaryMerkle.HashSuite Leaf ℕ where
  leaf _ := 0
  node _ _ := 0

def inputOpening (b : Fin 5) : InputOpening ℕ b where
  rows _ _ := 0
  salts _ _ := 0
  siblings := List.replicate 17 0

def friOpening (j : Fin 5) : FriOpening ℕ j where
  values _ := 1
  salts _ := 0
  siblings := List.replicate (nativeRowHeight j) 0

def queryOpening : QueryOpening ℕ where
  input := inputOpening
  fri := friOpening

def openings (q : ℕ) : Openings ℕ q := fun _ => queryOpening

/-- Six distinct actual leaf shapes plus the one node query suffice at every native depth. -/
def checkpointLog : Packed.Log ℕ :=
  [(.leaf (inputOpening 0).leaf,0),(.leaf (inputOpening 1).leaf,0),
   (.leaf (inputOpening 2).leaf,0),(.leaf (inputOpening 3).leaf,0),
   (.leaf (friOpening 0).leaf,0),(.leaf (friOpening 4).leaf,0),(.node 0 0,0)]

/-- The reduction ignores the concrete zero input rows; its separate PCS interpretation is not claimed. -/
def checkpoints : Checkpoints ℕ where
  input _ := ⟨checkpointLog,0⟩
  fri _ _ := ⟨checkpointLog,0⟩
  final _ := 1
  reduction i _ := Ir2Fri.Witnesses.farWord i

/-- Statement-first actual 38-query witness target, including source farness and rejection. -/
def ActualProfileContract : Prop :=
  ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) (extracted checkpoints).input ∧
  ∀ r : Fin 5 → Ext4,
    CheckpointsLogged checkpoints r checkpointLog ∧
    ¬Failure checkpoints r (checkpointLog++verificationLog hash 38 (fun _ => 0) (openings 38)) ∧
    Accepts hash checkpoints 38 r (fun _ => 0) (openings 38) ∧
    ¬Accepts hash checkpoints 38 r (fun _ => ⟨65536,by decide⟩) (openings 38)

theorem input_leaf_length (b : Fin 5) : (inputOpening b).leaf.length = inputLeafLength b :=
  rowsEncode_length _ _ _

theorem fri_leaf_length (j : Fin 5) : (friOpening j).leaf.length = friLeafLength j :=
  friLeafEncode_length _ _

/-- The finite checkpoint contains the supplied canonical input leaf for every batch. -/
theorem input_leaf_mem (b : Fin 5) : (.leaf (inputOpening b).leaf,0) ∈ checkpointLog := by
  fin_cases b <;> simp [checkpointLog]
  exact Or.inl rfl

/-- The four arity-eight encodings coincide; the last arity-four encoding has its own entry. -/
theorem fri_leaf_mem (j : Fin 5) : (.leaf (friOpening j).leaf,0) ∈ checkpointLog := by
  fin_cases j <;> simp [checkpointLog]
  all_goals exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- Each expected public shape has one leaf query, and only node00 occupies the node role. -/
theorem checkpoint_no_collision (len : ℕ) :
    ¬ShapeRootExtraction.Collision (fun leaf : Leaf => leaf.length=len) checkpointLog := by
  have h0 : (inputOpening 0).leaf.length=24 := by rw [input_leaf_length]; rfl
  have h1 : (inputOpening 1).leaf.length=2526 := by rw [input_leaf_length]; rfl
  have h2 : (inputOpening 2).leaf.length=192 := by rw [input_leaf_length]; rfl
  have h3 : (inputOpening 3).leaf.length=63 := by rw [input_leaf_length]; rfl
  have h4 : (friOpening 0).leaf.length=36 := by rw [fri_leaf_length]; rfl
  have h5 : (friOpening 4).leaf.length=20 := by rw [fri_leaf_length]; rfl
  simp only [ShapeRootExtraction.Collision,ResponseCollision,
    ShapeRootExtraction.mem_matching,checkpointLog,List.mem_cons,
    ShapeRootExtraction.admits]
  simp_all
  constructor <;> intro x d hx hshape x' hx' hshape'
  all_goals
    rcases hx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases hx' with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;>
    simp_all

/-- The root-first kernel recomputes zero at any exact native path height. -/
theorem recompute_zero (k : ℕ) (bits : Fin k → Bool) :
    BinaryMerkle.recompute hash 0 bits (List.replicate k 0) = some 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,BinaryMerkle.recompute,ih]
    cases bits 0 <;> rfl

/-- The actual low-bit-first MMCS path accepts at every selected row. -/
theorem path_accepts_zero (k : ℕ) (raw : Fin (2^k)) (leaf : Leaf) :
    PathAccepts hash 0 k raw leaf (List.replicate k 0) := by
  rw [PathAccepts,bottomUpRecompute_raw,List.reverse_replicate]
  exact recompute_zero k _

/-- Every internal call along such a path is the retained node00 call. -/
theorem node_log_zero (k : ℕ) (bits : Fin k → Bool) :
    EfficientRootOpening.pathLog hash 0 bits (List.replicate k 0) =
      List.replicate k (.node 0 0,0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,EfficientRootOpening.pathLog,recompute_zero,ih]
    cases bits 0 <;> simp [evaluate,hash,List.replicate_succ']

/-- All supplied path records belong to the finite commitment checkpoint. -/
theorem path_log_mem (k : ℕ) (raw : Fin (2^k)) (leaf : Leaf)
    (hl : (.leaf leaf,0) ∈ checkpointLog) (e : Query Leaf ℕ × ℕ)
    (he : e ∈ Packed.pathLog hash k raw leaf (List.replicate k 0)) : e ∈ checkpointLog := by
  have hn : (.node 0 0,0) ∈ checkpointLog := by simp [checkpointLog]
  change e ∈ (.leaf leaf,0)::EfficientRootOpening.pathLog hash 0
    (fun i => binaryAddressBits k raw i.rev) (List.replicate k 0).reverse at he
  rw [List.reverse_replicate,node_log_zero] at he
  rcases List.mem_cons.mp he with h|h
  · exact h ▸ hl
  · exact (List.eq_of_mem_replicate h) ▸ hn

/-- The complete 38-query verifier log reuses only the checkpoint's seven records. -/
theorem verification_log_covered (q : ℕ) (raw : Fin q → Fin (2^17))
    (e : Query Leaf ℕ × ℕ) (he : e ∈ verificationLog hash q raw (openings q)) : e ∈ checkpointLog := by
  obtain ⟨L,hL,he⟩ := List.mem_flatten.mp he
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hL
  rcases List.mem_append.mp he with hi|hf
  · obtain ⟨L,hL,he⟩ := List.mem_flatten.mp hi
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hL
    exact path_log_mem 17 (raw a) _ (input_leaf_mem b) e he
  · obtain ⟨L,hL,he⟩ := List.mem_flatten.mp hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hL
    exact path_log_mem (nativeRowHeight j) (rawParentRow j (raw a)) _ (fri_leaf_mem j) e he

/-- No verifier record is late, and every public expected shape retains unique role queries. -/
theorem no_failure (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → Fin (2^17)) :
    ¬Failure checkpoints r (checkpointLog++verificationLog hash q raw (openings q)) := by
  let L := checkpointLog++verificationLog hash q raw (openings q)
  have hsub : ∀ e ∈ L,e ∈ checkpointLog := by
    intro e he
    rcases List.mem_append.mp he with h|h
    · exact h
    · exact verification_log_covered q raw e h
  have hgood (len : ℕ) : ¬ShapeRootExtraction.Bad
      (fun leaf : Leaf => leaf.length=len) checkpointLog L 0 := by
    have hm (role : Bool) : ∀ e ∈ ShapeRootExtraction.matchingLog
        (fun leaf : Leaf => leaf.length=len) role L,
        e ∈ ShapeRootExtraction.matchingLog (fun leaf : Leaf => leaf.length=len) role checkpointLog := by
      intro e he
      have hh := (ShapeRootExtraction.mem_matching _ _ _ e).mp he
      exact (ShapeRootExtraction.mem_matching _ _ _ e).mpr ⟨hsub e hh.1,hh.2⟩
    rintro ((h|h)|⟨e,he,hnot,_⟩)
    · obtain ⟨e,he,e',he',hr,hn⟩ := h
      exact checkpoint_no_collision len (Or.inl ⟨e,hm false e he,e',hm false e' he',hr,hn⟩)
    · obtain ⟨e,he,e',he',hr,hn⟩ := h
      exact checkpoint_no_collision len (Or.inr ⟨e,hm true e he,e',hm true e' he',hr,hn⟩)
    · exact hnot (hsub e he)
  rintro (⟨b,hb⟩|⟨j,hj⟩)
  · exact hgood (inputLeafLength b) hb
  · exact hgood (friLeafLength j) hj

/-- The declared commitment-time checkpoints are actually retained. -/
theorem checkpoints_logged (r : Fin 5 → Ext4) : CheckpointsLogged checkpoints r checkpointLog :=
  ⟨fun _ _ h => h,fun _ _ h => h⟩

/-- All actual input and FRI paths verify for every raw query, not only the accepting sample. -/
theorem paths_accept (r : Fin 5 → Ext4) (raw : Fin (2^17)) :
    PathsAccept hash checkpoints r raw queryOpening :=
  ⟨fun _b => path_accepts_zero 17 raw _,fun j => path_accepts_zero (nativeRowHeight j) (rawParentRow j raw) _⟩

/-- Every supplied carried FRI value, including the transparent final constant, is one. -/
theorem supplied_one (r : Fin 5 → Ext4) (raw : Fin (2^17)) (n : ℕ) :
    suppliedAt checkpoints r raw queryOpening n = 1 := by
  unfold suppliedAt
  split_ifs <;> rfl

/-- Constant-one native interpolation fires at every scalar, including node hits. -/
theorem native_one (j : Fin 5) (raw : Fin (2^17)) (β : Ext4) :
    P3Barycentric.native (nativeRowNodes j (rawParentRow j raw)) (friOpening j).values β = 1 := by
  simpa using P3Barycentric.native_of_polynomial (nativeRowNodes j (rawParentRow j raw))
    (Polynomial.C (1:Ext4)) (by simpa using (show (0:WithBot ℕ) < (radix j:WithBot ℕ) from
      WithBot.coe_lt_coe.mpr (radix_positive j))) β

/-- The full actual-shape 38-query supplied proof accepts the all-zero raw query vector. -/
theorem zero_accepts (r : Fin 5 → Ext4) :
    Accepts hash checkpoints 38 r (fun _ => 0) (openings 38) := by
  intro a
  change QueryAccepts hash checkpoints r 0 queryOpening
  refine ⟨paths_accept r 0,?_,?_⟩
  · rw [supplied_one]
    have hz : sourceIndex (0 : Fin (2^17)) = 0 := by apply Fin.ext; decide
    change 1 = Ir2Fri.Witnesses.farWord (sourceIndex 0)
    rw [hz]
    exact Ir2Fri.Witnesses.input_zero.symm
  · intro j
    rw [supplied_one]
    exact (native_one j 0 (r j)).symm

/-- Raw bit16 selects natural coordinate one and makes the initial carried equality fail. -/
theorem initial_rejects (r : Fin 5 → Ext4) :
    ¬Accepts hash checkpoints 38 r (fun _ => ⟨65536,by decide⟩) (openings 38) := by
  intro h
  have he := (h 0).2.1
  change suppliedAt checkpoints r ⟨65536,by decide⟩ queryOpening 0 =
    Ir2Fri.Witnesses.farWord (sourceIndex ⟨65536,by decide⟩) at he
  rw [supplied_one] at he
  have ho : sourceIndex (⟨65536,by decide⟩ : Fin (2^17)) = 1 := by apply Fin.ext; decide
  change 1 = Ir2Fri.Witnesses.farWord (sourceIndex ⟨65536,by decide⟩) at he
  rw [ho] at he
  exact Ir2Fri.Witnesses.input_one he.symm

/-- The extracted source inherits the frozen positive-farness witness by construction. -/
theorem extracted_source_far :
    ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) (extracted checkpoints).input :=
  Ir2Fri.Witnesses.farWord_far

/-- All actual-profile premises hold together, with accepting and rejecting query vectors. -/
theorem actual_profile_inhabited : ActualProfileContract :=
  ⟨extracted_source_far,fun r => ⟨checkpoints_logged r,no_failure 38 r _,zero_accepts r,initial_rejects r⟩⟩

end
end Minidregg.Selvage.Ir2Fri.Packed.Witnesses

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.input_leaf_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.input_leaf_length

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.fri_leaf_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.fri_leaf_length

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.input_leaf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.input_leaf_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.fri_leaf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.fri_leaf_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.checkpoint_no_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.checkpoint_no_collision

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.recompute_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.recompute_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.path_accepts_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.path_accepts_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.node_log_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.node_log_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.path_log_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.path_log_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.verification_log_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.verification_log_covered

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.no_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.no_failure

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.checkpoints_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.checkpoints_logged

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.paths_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.paths_accept

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.supplied_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.supplied_one

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.native_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.native_one

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.zero_accepts

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.initial_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.initial_rejects

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.extracted_source_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.extracted_source_far

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.Witnesses.actual_profile_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.Witnesses.actual_profile_inhabited
