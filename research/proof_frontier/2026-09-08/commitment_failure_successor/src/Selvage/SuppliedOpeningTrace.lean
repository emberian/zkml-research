/- One-pass instrumented BinaryMerkle recomputation and concrete supplied-row
hash-call logs. The result is proved equal to the existing verifier; accounting
counts emitted hash-call records, not implementation time or packed MMCS work. -/
import Selvage.CommitmentFailureReduction
import Selvage.ArityEightScheduleBabyBear

namespace Minidregg.Selvage.SuppliedOpeningTrace
open scoped Classical
variable {Value Digest : Type}

/-- One recursive verifier pass returns its result together with the exact
node calls. Every successful level evaluates its node hash once. -/
def recomputeLogged (H : BinaryMerkle.HashSuite Value Digest) (leaf : Digest) :
    {k : ℕ} → (Fin k → Bool) → List Digest → Option Digest × EfficientRootOpening.Log Value Digest
  | 0, _, [] => (some leaf,[])
  | 0, _, _::_ => (none,[])
  | _+1, _, [] => (none,[])
  | k+1, address, sibling::rest =>
      let r := recomputeLogged H leaf (fun i : Fin k => address i.succ) rest
      match r.1 with
      | none => (none,[])
      | some child =>
          let query := if address 0 then EfficientRootOpening.Query.node sibling child
            else EfficientRootOpening.Query.node child sibling
          let answer := EfficientRootOpening.evaluate H query
          (some answer,r.2++[(query,answer)])

/-- Exact source-verifier and source-log equality, including malformed paths. -/
theorem recomputeLogged_eq (H : BinaryMerkle.HashSuite Value Digest) (leaf : Digest) :
    ∀ (k : ℕ) (address : Fin k → Bool) (path : List Digest),
    recomputeLogged H leaf address path =
      (BinaryMerkle.recompute H leaf address path,EfficientRootOpening.pathLog H leaf address path) := by
  intro k
  induction k with
  | zero => intro address path; cases path <;> rfl
  | succ k ih =>
    intro address path
    cases path with
    | nil => rfl
    | cons sibling rest =>
      simp only [recomputeLogged,ih]
      cases h : BinaryMerkle.recompute H leaf (fun i => address i.succ) rest with
      | none => simp [BinaryMerkle.recompute,EfficientRootOpening.pathLog,h]
      | some child =>
        cases hb : address 0 <;>
          simp [BinaryMerkle.recompute,EfficientRootOpening.pathLog,h,hb,EfficientRootOpening.evaluate]

/-- The leaf is hashed once, then the existing path is traversed once. -/
def openingRun (H : BinaryMerkle.HashSuite Value Digest) (v : Value)
    {k : ℕ} (address : Fin k → Bool) (path : List Digest) :
    Option Digest × EfficientRootOpening.Log Value Digest :=
  let d := H.leaf v
  let r := recomputeLogged H d address path
  (r.1,(.leaf v,d)::r.2)

theorem openingRun_eq (H : BinaryMerkle.HashSuite Value Digest) (v : Value)
    (k : ℕ) (address : Fin k → Bool) (path : List Digest) :
    openingRun H v address path =
      (BinaryMerkle.recompute H (H.leaf v) address path,EfficientRootOpening.openingLog H v address path) := by
  simp [openingRun,recomputeLogged_eq,EfficientRootOpening.openingLog]

/-- Even a malformed supplied path emits no more than k node records. -/
theorem pathLog_length_le (H : BinaryMerkle.HashSuite Value Digest) (leaf : Digest) :
    ∀ (k : ℕ) (address : Fin k → Bool) (path : List Digest),
      (EfficientRootOpening.pathLog H leaf address path).length ≤ k := by
  intro k
  induction k with
  | zero => intro address path; simp [EfficientRootOpening.pathLog]
  | succ k ih =>
    intro address path
    cases path with
    | nil => simp [EfficientRootOpening.pathLog]
    | cons sibling rest =>
      cases h : BinaryMerkle.recompute H leaf (fun i => address i.succ) rest with
      | none => simp [EfficientRootOpening.pathLog,h]
      | some child =>
        have ht := ih (fun i => address i.succ) rest
        simpa only [EfficientRootOpening.pathLog,h,List.length_append,List.length_singleton,Nat.succ_eq_add_one,
          Nat.add_le_add_iff_right] using Nat.add_le_add_right ht 1

theorem openingRun_length_le (H : BinaryMerkle.HashSuite Value Digest) (v : Value)
    (k : ℕ) (address : Fin k → Bool) (path : List Digest) :
    (openingRun H v address path).2.length ≤ k+1 := by
  rw [openingRun_eq]
  simpa only [EfficientRootOpening.openingLog,List.length_cons,Nat.succ_eq_add_one]
    using Nat.add_le_add_right (pathLog_length_le H (H.leaf v) k address path) 1

section Row
open ArityEight
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
variable {k₀ k₁ k₂ k₃ : ℕ}
variable {dom₀ : Fin (2^k₀) ↪ F} {dom₁ : Fin (2^k₁) ↪ F}
variable {dom₂ : Fin (2^k₂) ↪ F} {dom₃ : Fin (2^k₃) ↪ F}

def pointRun (H : BinaryMerkle.HashSuite F Digest) {k : ℕ} (i : Fin (2^k)) (o : PointOpening F Digest) :=
  openingRun H o.value (binaryAddressBits k i) o.path

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
theorem pointRun_result (H : BinaryMerkle.HashSuite F Digest) {k : ℕ} (i : Fin (2^k)) (o : PointOpening F Digest) :
    (pointRun H i o).1 = BinaryMerkle.recompute H (H.leaf o.value) (binaryAddressBits k i) o.path := by
  rw [pointRun,openingRun_eq]

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
theorem pointRun_log (H : BinaryMerkle.HashSuite F Digest) {k : ℕ} (i : Fin (2^k)) (o : PointOpening F Digest) :
    (pointRun H i o).2 = EfficientRootOpening.openingLog H o.value (binaryAddressBits k i) o.path := by
  rw [pointRun,openingRun_eq]

def sourceRuns (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (i : Fin (2^k₃)) (o : RowOpening F Digest) :
    List (Option Digest × EfficientRootOpening.Log F Digest) :=
  [false,true].flatMap fun c => [false,true].flatMap fun b => [false,true].map fun a =>
    pointRun H (rowPoint D₀ D₁ D₂ i c b a) (o.source c b a)

/-- Actual row verifier plus retained records, sharing the ten evaluated runs. -/
def rowRun (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (rs rg rn : Digest) (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) :
    Bool × EfficientRootOpening.Log F Digest :=
  let src := sourceRuns H D₀ D₁ D₂ i o
  let inp := pointRun H i o.injected
  let dst := pointRun H i o.next
  (src.all (fun r => decide (r.1 = some rs)) && decide (inp.1 = some rg) && decide (dst.1 = some rn) &&
      decide (o.next.value = foldRow8 D₀ D₁ D₂ i (fun c b a => (o.source c b a).value) β + β^8*o.injected.value),
    (src.flatMap Prod.snd)++inp.2++dst.2)

/-- The instrumented Boolean result is exactly the frozen supplied-row checker. -/
theorem rowRun_check (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (rs rg rn : Digest) (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) :
    (rowRun H D₀ D₁ D₂ rs rg rn β i o).1 = rowCheck H D₀ D₁ D₂ rs rg rn β i o := by
  simp [rowRun,sourceRuns,rowCheck,pointCheck,pointRun_result,Bool.and_assoc]

/-- All hash calls needed by the supplied-path reduction occur in the produced log. -/
theorem rowRun_logged (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (rs rg rn : Digest) (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) :
    RowLogged H (rowRun H D₀ D₁ D₂ rs rg rn β i o).2 D₀ D₁ D₂ i o := by
  refine ⟨?_,?_,?_⟩
  · intro c b a e he
    cases c <;> cases b <;> cases a <;>
      simp only [rowRun,sourceRuns,List.flatMap_cons,List.flatMap_nil,List.flatMap_append,List.map_cons,List.map_nil,
        List.append_nil,List.mem_append,pointRun_log] <;> tauto
  · intro e he
    simp only [rowRun,List.mem_append,pointRun_log]
    exact Or.inl (Or.inr he)
  · intro e he
    simp only [rowRun,List.mem_append,pointRun_log]
    exact Or.inr he

/-- Eight depth-k0 paths and two depth-k3 paths: exact scalar interface accounting. -/
theorem rowRun_length_le (H : BinaryMerkle.HashSuite F Digest)
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (rs rg rn : Digest) (β : F) (i : Fin (2^k₃)) (o : RowOpening F Digest) :
    (rowRun H D₀ D₁ D₂ rs rg rn β i o).2.length ≤ 8*(k₀+1)+2*(k₃+1) := by
  have hs (c b a : Bool) := openingRun_length_le H (o.source c b a).value k₀
    (binaryAddressBits k₀ (rowPoint D₀ D₁ D₂ i c b a)) (o.source c b a).path
  have hg := openingRun_length_le H o.injected.value k₃ (binaryAddressBits k₃ i) o.injected.path
  have hn := openingRun_length_le H o.next.value k₃ (binaryAddressBits k₃ i) o.next.path
  have h000 := hs false false false
  have h001 := hs false false true
  have h010 := hs false true false
  have h011 := hs false true true
  have h100 := hs true false false
  have h101 := hs true false true
  have h110 := hs true true false
  have h111 := hs true true true
  simp only [rowRun,sourceRuns,List.flatMap_cons,List.flatMap_nil,List.flatMap_append,List.map_cons,List.map_nil,
    List.append_nil,List.length_append,pointRun]
  omega

end Row
end Minidregg.Selvage.SuppliedOpeningTrace

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.recomputeLogged_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.recomputeLogged_eq

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.openingRun_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.openingRun_eq

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.pathLog_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.pathLog_length_le

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.openingRun_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.openingRun_length_le

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.pointRun_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.pointRun_result

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.pointRun_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.pointRun_log

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.rowRun_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.rowRun_check

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.rowRun_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.rowRun_logged

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.rowRun_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.rowRun_length_le
