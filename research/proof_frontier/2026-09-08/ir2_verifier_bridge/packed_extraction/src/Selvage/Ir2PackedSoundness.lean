/- Actual-profile packed supplied-opening soundness with its observed extraction
failure explicit. PCS batching/farness and Fiat--Shamir remain separate. -/
import Selvage.Ir2PackedExtraction

namespace Minidregg.Selvage.Ir2Fri.Packed
open BabyBearExt4 Ir2FriSchedule
open scoped Classical
noncomputable section
variable {Digest : Type} [DecidableEq Digest]

abbrev External (q : ℕ) := (Fin 5 → Ext4) × (Fin q → BabyBear)

def rawQueries {q : ℕ} (x : External q) : Fin q → Fin (2^17) :=
  fun a => BabyBearModuloSampling.sampleBits 17 (x.2 a)

def FreshAccepts (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (q : ℕ) (x : External q) (o : Openings Digest q) : Prop :=
  Accepts H st q x.1 (rawQueries x) o

/-- This residual is computed on the supplied prover log plus this verifier's
constructed packed leaf/node call log. No desired extraction implication is assumed. -/
def observedFailure (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (q : ℕ) (x : External q) (o : Openings Digest q) (P : Log Digest) : Prop :=
  Failure st x.1 (P++verificationLog H q (rawQueries x) o)

/-- Arbitrary packed supplied proofs, actual q38/native folds/base query law.
The initial farness premise is about the input derived from packed checkpoints
and the fixed reduction, not an assumed global FRI word. -/
theorem supplied_fresh_38 (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (o : External 38 → Openings Digest 38) (P : External 38 → Log Digest)
    (hP : ∀ x,CheckpointsLogged st x.1 (P x))
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) (extracted st).input) :
    uniformProb (External 38) (fun x => FreshAccepts H st 38 x (o x)) ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38+
      uniformProb (External 38) (fun x => observedFailure H st 38 x (o x) (P x)) := by
  have hc : ∀ x : External 38,FreshAccepts H st 38 x (o x) →
      NativeFreshAccepts (extracted st) 38 x.1 x.2 ∨ observedFailure H st 38 x (o x) (P x) := by
    intro x hx
    exact supplied_cover H st 38 x.1 (rawQueries x) (o x) (P x) (hP x) hx
  exact ((uniformProb_mono hc).trans (uniformProb_or_le _ _)).trans
    (add_le_add (native_fresh_38 (extracted st) hfar) le_rfl)

omit [DecidableEq Digest] in
/-- Each native leaf/path verifier emits at most one leaf macro-call plus one
node macro-call per actual level, including malformed supplied paths. -/
theorem pathLog_length_le (H : BinaryMerkle.HashSuite Leaf Digest) (k : ℕ)
    (raw : Fin (2^k)) (v : Leaf) (siblings : List Digest) :
    (pathLog H k raw v siblings).length ≤ k+1 := by
  have h := SuppliedOpeningTrace.openingRun_length_le H v k
    (fun i => binaryAddressBits k raw i.rev) siblings.reverse
  rw [SuppliedOpeningTrace.openingRun_eq] at h
  exact h

omit [DecidableEq Digest] in
/-- The five input roots cost90 and the five packed FRI roots46 macro-call
records per query. This is not a count of underlying Poseidon permutations. -/
theorem queryLog_length_le (H : BinaryMerkle.HashSuite Leaf Digest)
    (raw : Fin (2^17)) (o : QueryOpening Digest) : (queryLog H raw o).length ≤ 136 := by
  have hi := Finset.sum_le_sum (fun (b : Fin 5) (_ : b ∈ Finset.univ) =>
    pathLog_length_le H 17 raw (o.input b).leaf (o.input b).siblings)
  have hf := Finset.sum_le_sum (fun (j : Fin 5) (_ : j ∈ Finset.univ) =>
    pathLog_length_le H (nativeRowHeight j) (rawParentRow j raw) (o.fri j).leaf (o.fri j).siblings)
  have h := Nat.add_le_add hi hf
  norm_num [nativeRowHeight,stage,Fin.sum_univ_succ] at h
  simpa only [queryLog,List.length_append,List.length_flatten,List.map_ofFn,Function.comp_def,List.sum_ofFn] using h

omit [DecidableEq Digest] in
/-- Actual packed verifier accounting is136q records, hence5168 at38 queries.
Repeated calls may share one fresh cache entry. Prover and transcript work are additional. -/
theorem verificationLog_length_le (H : BinaryMerkle.HashSuite Leaf Digest) (q : ℕ)
    (raw : Fin q → Fin (2^17)) (o : Openings Digest q) :
    (verificationLog H q raw o).length ≤ 136*q := by
  have h := Finset.sum_le_sum (fun (a : Fin q) (_ : a ∈ Finset.univ) => queryLog_length_le H (raw a) (o a))
  simpa [verificationLog,List.length_flatten,List.map_ofFn,Function.comp_def,List.sum_ofFn,Nat.mul_comm] using h

end
end Minidregg.Selvage.Ir2Fri.Packed

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.supplied_fresh_38' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.supplied_fresh_38

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.pathLog_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.pathLog_length_le

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.queryLog_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.queryLog_length_le

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.verificationLog_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.verificationLog_length_le

