/- Canonical IR2 packed commitments, actual raw path order and causal extraction.
No global source or FRI word is supplied as a premise: both are constructed
from commitment-time logs and the fixed pre-FRI reduction data. -/
import Selvage.ShapeRootExtraction
import Selvage.Ir2FriPackedIndices
import Selvage.Ir2FriNativeMerklePath
import Selvage.PackedLeafEncoding
import Selvage.Ir2FriSoundness
import Selvage.SuppliedOpeningTrace

namespace Minidregg.Selvage.Ir2Fri.Packed
open BabyBearExt4 Ir2FriSchedule PackedLeafEncoding EfficientRootOpening
open scoped Classical
noncomputable section
set_option maxRecDepth 100000

abbrev Leaf := List BabyBear
abbrev Log (Digest : Type) := EfficientRootOpening.Log Leaf Digest

def widths (b : Fin 5) : List ℕ :=
  match b.val with
  | 0 => [8,8]
  | 1 => [2513,5]
  | 2 => List.replicate 16 8
  | 3 => [59]
  | _ => [8,8]

def width (b : Fin 5) := widthsOfList (widths b)
abbrev InputRows (b : Fin 5) := (i : Fin (widths b).length) → Fin (width b i) → BabyBear
abbrev AllInputRows := (b : Fin 5) → InputRows b
abbrev InputSalts (b : Fin 5) := Fin (widths b).length → Fin 4 → BabyBear

def inputLeafLength (b : Fin 5) : ℕ := (List.ofFn (fun i => width b i+4)).sum

def friLeafLength (j : Fin 5) : ℕ := 4*radix j+4

/-- Exact same-height salted leaf lengths enforced by canonical admission. -/
theorem leaf_lengths :
    (List.ofFn inputLeafLength) = [24,2526,192,63,24] ∧
    (List.ofFn friLeafLength) = [36,36,36,36,20] := by
  norm_num [inputLeafLength,width,widths,widthsOfList,friLeafLength,radix,stage,List.ofFn_succ]

/-- Fixed before the FRI challenges: alpha, claims and reduction points may be
captured here. The same function reduces supplied rows and extracted rows.
Its PCS algebra and false-claim-to-farness theorem are separate obligations. -/
abbrev Reduction := Index 0 → AllInputRows → Ext4

structure Checkpoint (Digest : Type) where
  log : Log Digest
  root : Digest

structure Checkpoints (Digest : Type) where
  input : Fin 5 → Checkpoint Digest
  fri : (j : Fin 5) → (Fin j.val → Ext4) → Checkpoint Digest
  final : (Fin 5 → Ext4) → Ext4
  reduction : Reduction

variable {Digest : Type} [DecidableEq Digest]

/-- The role/shape-directed extractor uses the native row's MSB-first address
in the existing root-first lookup. It never consults future query openings. -/
def leafAt (cp : Checkpoint Digest) (len k : ℕ) (raw : Fin (2^k)) : Leaf :=
  ShapeRootExtraction.extractedAt (fun leaf => leaf.length=len) cp.log [] cp.root
    (fun i => binaryAddressBits k raw i.rev)

def inputRowsAt (st : Checkpoints Digest) (raw : Fin (2^17)) : AllInputRows :=
  fun b i => rowProject (width b) i (leafAt (st.input b) (inputLeafLength b) 17 raw)

def packedWord (st : Checkpoints Digest) (j : Fin 5) (p : Fin j.val → Ext4) (i : Index j) : Ext4 :=
  let packed := packedIndexEquiv j i
  friProject packed.2 (leafAt (st.fri j p) (friLeafLength j) (nativeRowHeight j) packed.1)

/-- Prefix-fixed global words are derived from logs, packing and coefficient
decoding. The transparent final constant has no fictitious Merkle root. -/
def extracted (st : Checkpoints Digest) : Words where
  input i := st.reduction i (inputRowsAt st (sourceEquiv.symm i))
  word n p := if hn : n < 5 then packedWord st ⟨n,hn⟩ p else
    fun _ => st.final (fun i => p ⟨i.val,by omega⟩)

theorem extracted_fri (st : Checkpoints Digest) (r : Fin 5 → Ext4) (j : Fin 5) :
    (extracted st).wordAt r j (by omega) = packedWord st j (friPrefix r j (by omega)) := by
  simp only [Words.wordAt,extracted,dif_pos j.isLt]

theorem extracted_final (st : Checkpoints Digest) (r : Fin 5 → Ext4) :
    (extracted st).wordAt r 5 le_rfl = fun _ => st.final r := by
  rfl

theorem extracted_terminal (st : Checkpoints Digest) (r : Fin 5 → Ext4) : Terminal (extracted st) r :=
  ⟨st.final r,fun i => congrFun (extracted_final st r) i⟩

/-- Raw supplied input values have fixed canonical row/salt types. -/
structure InputOpening (Digest : Type) (b : Fin 5) where
  rows : InputRows b
  salts : InputSalts b
  siblings : List Digest

structure FriOpening (Digest : Type) (j : Fin 5) where
  values : Fin (radix j) → Ext4
  salts : Fin 4 → BabyBear
  siblings : List Digest

structure QueryOpening (Digest : Type) where
  input : (b : Fin 5) → InputOpening Digest b
  fri : (j : Fin 5) → FriOpening Digest j

abbrev Openings (Digest : Type) (q : ℕ) := Fin q → QueryOpening Digest

def InputOpening.leaf {b : Fin 5} (o : InputOpening Digest b) : Leaf :=
  rowsEncode (width b) o.rows o.salts

def FriOpening.leaf {j : Fin 5} (o : FriOpening Digest j) : Leaf := friLeafEncode o.values o.salts

/-- Literal native binary MMCS path verification on the supplied raw integer. -/
def PathAccepts (H : BinaryMerkle.HashSuite Leaf Digest) (root : Digest)
    (k : ℕ) (raw : Fin (2^k)) (leaf : Leaf) (siblings : List Digest) : Prop :=
  bottomUpRecompute H (H.leaf leaf) (fun i : Fin k => Nat.testBit raw.val i.val) siblings = some root

/-- Exact actual hash calls of the supplied path, represented in the existing
finite log after the proved reversal adapter. -/
def pathLog (H : BinaryMerkle.HashSuite Leaf Digest) (k : ℕ) (raw : Fin (2^k))
    (leaf : Leaf) (siblings : List Digest) : Log Digest :=
  openingLog H leaf (fun i => binaryAddressBits k raw i.rev) siblings.reverse

def PathsAccept (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (r : Fin 5 → Ext4) (raw : Fin (2^17)) (o : QueryOpening Digest) : Prop :=
  (∀ b, PathAccepts H (st.input b).root 17 raw (o.input b).leaf (o.input b).siblings) ∧
  ∀ j, PathAccepts H (st.fri j (friPrefix r j (by omega))).root (nativeRowHeight j)
    (rawParentRow j raw) (o.fri j).leaf (o.fri j).siblings

/-- The carried next coordinate is taken from the next supplied packed row;
at the last round it is the transparent final polynomial coefficient. -/
def suppliedAt (st : Checkpoints Digest) (r : Fin 5 → Ext4) (raw : Fin (2^17))
    (o : QueryOpening Digest) (n : ℕ) : Ext4 :=
  if hn : n < 5 then (o.fri ⟨n,hn⟩).values (rawColumn ⟨n,hn⟩ raw) else st.final r

def QueryAccepts (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (r : Fin 5 → Ext4) (raw : Fin (2^17)) (o : QueryOpening Digest) : Prop :=
  PathsAccept H st r raw o ∧
  suppliedAt st r raw o 0 = st.reduction (sourceIndex raw) (fun b => (o.input b).rows) ∧
  ∀ j : Fin 5,
    suppliedAt st r raw o (j+1) =
      P3Barycentric.native (nativeRowNodes j (rawParentRow j raw)) (o.fri j).values (r j)

def Accepts (H : BinaryMerkle.HashSuite Leaf Digest) (st : Checkpoints Digest)
    (q : ℕ) (r : Fin 5 → Ext4) (raw : Fin q → Fin (2^17)) (o : Openings Digest q) : Prop :=
  ∀ a, QueryAccepts H st r (raw a) (o a)

def CheckpointsLogged (st : Checkpoints Digest) (r : Fin 5 → Ext4) (L : Log Digest) : Prop :=
  (∀ b e,e ∈ (st.input b).log → e ∈ L) ∧
  ∀ j e,e ∈ (st.fri j (friPrefix r j (by omega))).log → e ∈ L

/-- Only each actual checkpoint's own fixed shape and role is compared. -/
def Failure (st : Checkpoints Digest) (r : Fin 5 → Ext4) (L : Log Digest) : Prop :=
  (∃ b, ShapeRootExtraction.Bad (fun leaf : Leaf => leaf.length=inputLeafLength b)
    (st.input b).log L (st.input b).root) ∨
  ∃ j, ShapeRootExtraction.Bad (fun leaf : Leaf => leaf.length=friLeafLength j)
    (st.fri j (friPrefix r j (by omega))).log L (st.fri j (friPrefix r j (by omega))).root

def queryLog (H : BinaryMerkle.HashSuite Leaf Digest) (raw : Fin (2^17)) (o : QueryOpening Digest) : Log Digest :=
  (List.ofFn fun b : Fin 5 => pathLog H 17 raw (o.input b).leaf (o.input b).siblings).flatten ++
  (List.ofFn fun j : Fin 5 => pathLog H (nativeRowHeight j) (rawParentRow j raw)
    (o.fri j).leaf (o.fri j).siblings).flatten

def verificationLog (H : BinaryMerkle.HashSuite Leaf Digest) (q : ℕ)
    (raw : Fin q → Fin (2^17)) (o : Openings Digest q) : Log Digest :=
  (List.ofFn fun a => queryLog H (raw a) (o a)).flatten

end
end Minidregg.Selvage.Ir2Fri.Packed

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.leaf_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.leaf_lengths

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.extracted_fri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.extracted_fri

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.extracted_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.extracted_final

/-- info: 'Minidregg.Selvage.Ir2Fri.Packed.extracted_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Packed.extracted_terminal

