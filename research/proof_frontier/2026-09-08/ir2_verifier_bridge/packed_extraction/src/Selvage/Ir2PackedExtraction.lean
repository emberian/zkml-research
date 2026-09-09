/- Arbitrary canonically shaped supplied openings reduce to the extracted
native IR2 event or an observed same-shape collision / checkpoint late hit. -/
import Selvage.Ir2PackedCommitments

namespace Minidregg.Selvage.Ir2Fri.Packed
open BabyBearExt4 Ir2FriSchedule PackedLeafEncoding EfficientRootOpening
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {Digest : Type} [DecidableEq Digest]

/-- The raw native path pins its complete salted leaf at the fixed checkpoint. -/
theorem leaf_pins (H : BinaryMerkle.HashSuite Leaf Digest) (cp : Checkpoint Digest)
    (L : Log Digest) (len k : ℕ) (raw : Fin (2^k)) (v : Leaf) (siblings : List Digest)
    (hsub : ∀ e ∈ cp.log,e ∈ L)
    (hgood : ¬ShapeRootExtraction.Bad (fun leaf : Leaf => leaf.length=len) cp.log L cp.root)
    (hv : v.length=len) (hlog : ∀ e ∈ pathLog H k raw v siblings,e ∈ L)
    (ha : PathAccepts H cp.root k raw v siblings) : v=leafAt cp len k raw := by
  have hh : BinaryMerkle.recompute H (H.leaf v)
      (fun i => binaryAddressBits k raw i.rev) siblings.reverse = some cp.root := by
    simpa only [PathAccepts,bottomUpRecompute_raw] using ha
  exact (ShapeRootExtraction.extractedAt_eq_of_logged (fun leaf : Leaf => leaf.length=len)
    H cp.log L [] cp.root hsub hgood v hv
    (hlog _ (by simp [pathLog,openingLog])) k cp.root _ siblings.reverse (Or.inl rfl)
    (fun e he => hlog e (by simp [pathLog,openingLog,he])) hh).symm

omit [DecidableEq Digest] in
/-- Every actual supplied input path contributes to the constructed verifier log. -/
theorem input_log_mem (H : BinaryMerkle.HashSuite Leaf Digest) (q : ℕ)
    (raw : Fin q → Fin (2^17)) (o : Openings Digest q) (a : Fin q) (b : Fin 5)
    (e : EfficientRootOpening.Query Leaf Digest × Digest)
    (he : e ∈ pathLog H 17 (raw a) (o a |>.input b).leaf (o a |>.input b).siblings) :
    e ∈ verificationLog H q raw o := by
  apply List.mem_flatten.mpr
  refine ⟨queryLog H (raw a) (o a),List.mem_ofFn.mpr ⟨a,rfl⟩,?_⟩
  apply List.mem_append_left
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨b,rfl⟩,he⟩

omit [DecidableEq Digest] in
/-- Every actual supplied packed FRI path contributes to the same verifier log. -/
theorem fri_log_mem (H : BinaryMerkle.HashSuite Leaf Digest) (q : ℕ)
    (raw : Fin q → Fin (2^17)) (o : Openings Digest q) (a : Fin q) (j : Fin 5)
    (e : EfficientRootOpening.Query Leaf Digest × Digest)
    (he : e ∈ pathLog H (nativeRowHeight j) (rawParentRow j (raw a))
      (o a |>.fri j).leaf (o a |>.fri j).siblings) :
    e ∈ verificationLog H q raw o := by
  apply List.mem_flatten.mpr
  refine ⟨queryLog H (raw a) (o a),List.mem_ofFn.mpr ⟨a,rfl⟩,?_⟩
  apply List.mem_append_right
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,he⟩

/-- Fixed-width matrix/salt decoding recovers every supplied base input row. -/
theorem input_rows_pin (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (L : Log Digest) (r : Fin 5 → Ext4) (raw : Fin (2^17)) (o : QueryOpening Digest)
    (hsub : CheckpointsLogged st r L) (hgood : ¬Failure st r L)
    (hlog : ∀ b e,e ∈ pathLog H 17 raw (o.input b).leaf (o.input b).siblings → e ∈ L)
    (ha : PathsAccept H st r raw o) : inputRowsAt st raw = fun b => (o.input b).rows := by
  funext b i
  have hv := leaf_pins H (st.input b) L (inputLeafLength b) 17 raw
    (o.input b).leaf (o.input b).siblings (hsub.1 b)
    (fun h => hgood (Or.inl ⟨b,h⟩))
    (rowsEncode_length (width b) (o.input b).rows (o.input b).salts) (hlog b) (ha.1 b)
  unfold inputRowsAt
  rw [←hv]
  exact rowsRoundTrip _ _ _ _ i

/-- One leaf lookup recovers every extension value in the packed source row. -/
theorem fri_values_pin (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (L : Log Digest) (r : Fin 5 → Ext4) (raw : Fin (2^17)) (o : QueryOpening Digest)
    (hsub : CheckpointsLogged st r L) (hgood : ¬Failure st r L)
    (hlog : ∀ j e,e ∈ pathLog H (nativeRowHeight j) (rawParentRow j raw)
      (o.fri j).leaf (o.fri j).siblings → e ∈ L)
    (ha : PathsAccept H st r raw o) (j : Fin 5) (c : Fin (radix j)) :
    (o.fri j).values c =
      (extracted st).wordAt r j (by omega) (nativeRowSourceIndex j (rawParentRow j raw) c) := by
  have hv := leaf_pins H (st.fri j (friPrefix r j (by omega))) L (friLeafLength j)
    (nativeRowHeight j) (rawParentRow j raw) (o.fri j).leaf (o.fri j).siblings (hsub.2 j)
    (fun h => hgood (Or.inr ⟨j,h⟩))
    (friLeafEncode_length (o.fri j).values (o.fri j).salts) (hlog j) (ha.2 j)
  rw [extracted_fri]
  unfold packedWord
  rw [packedIndexEquiv_nativeRowSourceIndex]
  dsimp only
  rw [←hv]
  exact (friRoundTrip _ _ _ c).symm

/-- The carried next coordinate is pinned to the extracted next global word;
this includes the transparent constant terminal, without a nonexistent final root. -/
theorem suppliedAt_pin (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (L : Log Digest) (r : Fin 5 → Ext4) (raw : Fin (2^17)) (o : QueryOpening Digest)
    (hsub : CheckpointsLogged st r L) (hgood : ¬Failure st r L)
    (hlog : ∀ j e,e ∈ pathLog H (nativeRowHeight j) (rawParentRow j raw)
      (o.fri j).leaf (o.fri j).siblings → e ∈ L)
    (ha : PathsAccept H st r raw o) (n : ℕ) (hn : n ≤ 5) :
    suppliedAt st r raw o n = (extracted st).wordAt r n hn (runtimeIndex n raw) := by
  by_cases hlt : n < 5
  · let j : Fin 5 := ⟨n,hlt⟩
    have hp := fri_values_pin H st L r raw o hsub hgood hlog ha j (rawColumn j raw)
    rw [nativeRowSourceIndex_raw] at hp
    simpa only [suppliedAt,dif_pos hlt] using hp
  · have he : n=5 := by omega
    subst n
    rfl

/-- Every accepted query becomes the literal native query event on derived
prefix-fixed words, provided no required shape/role collision or late hit was observed. -/
theorem query_pins (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (L : Log Digest) (r : Fin 5 → Ext4) (raw : Fin (2^17)) (o : QueryOpening Digest)
    (hsub : CheckpointsLogged st r L) (hgood : ¬Failure st r L)
    (hi : ∀ b e,e ∈ pathLog H 17 raw (o.input b).leaf (o.input b).siblings → e ∈ L)
    (hf : ∀ j e,e ∈ pathLog H (nativeRowHeight j) (rawParentRow j raw)
      (o.fri j).leaf (o.fri j).siblings → e ∈ L)
    (ha : QueryAccepts H st r raw o) :
    initialMask (extracted st) (sourceIndex raw) ∧
    ∀ j : Fin 5,
      (extracted st).wordAt r (j+1) (by omega) (nativeParentIndex j (rawParentRow j raw)) =
        P3Barycentric.native (nativeRowNodes j (rawParentRow j raw))
          (fun c => (extracted st).wordAt r j (by omega)
            (nativeRowSourceIndex j (rawParentRow j raw) c)) (r j) := by
  constructor
  · have hp := suppliedAt_pin H st L r raw o hsub hgood hf ha.1 0 (by decide)
    rw [runtimeIndex_zero] at hp
    have hin : (extracted st).input (sourceIndex raw) =
        st.reduction (sourceIndex raw) (fun b => (o.input b).rows) := by
      change st.reduction (sourceIndex raw) (inputRowsAt st (sourceEquiv.symm (sourceEquiv raw))) = _
      rw [Equiv.symm_apply_apply,input_rows_pin H st L r raw o hsub hgood hi ha.1]
    have he : friPrefix r 0 (by decide) = (fun i => i.elim0) := Subsingleton.elim _ _
    simpa only [initialMask,Words.wordAt,he] using hp.symm.trans (ha.2.1.trans hin.symm)
  · intro j
    have hp := suppliedAt_pin H st L r raw o hsub hgood hf ha.1 (j+1) (by omega)
    rw [nativeParentIndex_rawParentRow]
    rw [←hp,ha.2.2 j]
    congr 1
    funext c
    exact fri_values_pin H st L r raw o hsub hgood hf ha.1 j c

/-- Arbitrary canonical packed supplied-proof reduction. The verifier's own
hash-call log is constructed here; only the prover checkpoints must be logged. -/
theorem supplied_cover (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → Fin (2^17)) (o : Openings Digest q)
    (P : Log Digest) (hP : CheckpointsLogged st r P)
    (ha : Accepts H st q r raw o) :
    (Terminal (extracted st) r ∧ NativeQueryAccepts (extracted st) r q raw) ∨
      Failure st r (P++verificationLog H q raw o) := by
  let L := P++verificationLog H q raw o
  by_cases hb : Failure st r L
  · exact Or.inr hb
  · have hsub : CheckpointsLogged st r L := by
      constructor
      · intro b e he; exact List.mem_append_left _ (hP.1 b e he)
      · intro j e he; exact List.mem_append_left _ (hP.2 j e he)
    have hq (a : Fin q) := query_pins H st L r (raw a) (o a) hsub hb
      (fun b e he => List.mem_append_right _ (input_log_mem H q raw o a b e he))
      (fun j e he => List.mem_append_right _ (fri_log_mem H q raw o a j e he)) (ha a)
    exact Or.inl ⟨extracted_terminal st r,fun a => (hq a).1,fun j a => (hq a).2 j⟩

end
end Minidregg.Selvage.Ir2Fri.Packed

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.leaf_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.leaf_pins

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.input_log_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.input_log_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.fri_log_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.fri_log_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.input_rows_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.input_rows_pin

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.fri_values_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.fri_values_pin

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.suppliedAt_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.suppliedAt_pin

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.query_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.query_pins

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.supplied_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.supplied_cover

