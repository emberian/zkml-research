/-
# Selvage.LogupIndexLink — canonical binary addresses into LogUp*

This is the formal semantic counterpart of the runtime Tower256 index bundle.
An indexed lookup does not receive arbitrary field-valued address columns:
each column is the decoded Boolean bit of one fixed `I : rows → Fin (2^k)`.
The resulting incidence vector is the literal unit vector at `I(row)`, and its
weighted table pushforward is definitionally the `logupPushforward` consumed by
`LogupStar`.

Cryptographic root equality is not modeled as a theorem about hashes.  The
runtime `SemanticLookupClause` exposes the canonical ordered root bundle and
checks it against the receipt-supplied root; `[COMMIT-CR]` remains the concrete
binding assumption.
-/
import Selvage.BinaryLookup
import Selvage.LogupStar

namespace Minidregg.Selvage

variable {F : Type*} [Field F]
variable {κ : Type*} [Fintype κ]

/-- LSB-first Boolean address column for one fixed indexed-lookup map. -/
def canonicalIndexColumn (k : Nat) (I : κ → Fin (2 ^ k))
    (bit : Fin k) (row : κ) : F :=
  cubePt (binaryAddressBits k (I row)) bit

theorem canonicalIndexColumn_boolean (k : Nat) (I : κ → Fin (2 ^ k))
    (bit : Fin k) (row : κ) :
    canonicalIndexColumn (F := F) k I bit row = 0 ∨
      canonicalIndexColumn (F := F) k I bit row = 1 := by
  cases h : binaryAddressBits k (I row) bit <;>
    simp [canonicalIndexColumn, cubePt, h]

/-- The one-hot incidence entry reconstructed from all canonical bit columns. -/
def canonicalIncidence (k : Nat) (I : κ → Fin (2 ^ k))
    (row : κ) (tableIndex : Fin (2 ^ k)) : F :=
  binaryLookupEq k (fun bit => canonicalIndexColumn k I bit row) tableIndex

theorem canonicalIndexPoint_eq (k : Nat) (I : κ → Fin (2 ^ k)) (row : κ) :
    (fun bit => canonicalIndexColumn (F := F) k I bit row) =
      binaryAddressPoint k (I row) := by
  rfl

/-- The entire reconstructed incidence row is a literal unit vector, not just
a Boolean vector whose sum happens to be one in characteristic two. -/
theorem canonicalIncidence_eq_unitVector (k : Nat)
    (I : κ → Fin (2 ^ k)) (row : κ) :
    canonicalIncidence (F := F) k I row = binaryUnitVector (I row) := by
  simpa [canonicalIncidence, canonicalIndexColumn, binaryAddressPoint] using
    (binaryLookupEq_cubePt_eq_unitVector (F := F) k
      (binaryAddressBits k (I row)))

@[simp] theorem canonicalIncidence_apply (k : Nat)
    (I : κ → Fin (2 ^ k)) (row : κ) (tableIndex : Fin (2 ^ k)) :
    canonicalIncidence (F := F) k I row tableIndex =
      if tableIndex = I row then 1 else 0 := by
  rw [canonicalIncidence_eq_unitVector]
  rfl

/-- Scatter equality weights through the committed incidence table. -/
noncomputable def canonicalIncidencePushforward (k : Nat)
    (I : κ → Fin (2 ^ k)) (X : κ → F) : Fin (2 ^ k) → F :=
  fun tableIndex => ∑ row, canonicalIncidence k I row tableIndex * X row

/-- **The address-link theorem.**  The incidence-MLE scatter used by the
runtime is exactly LogUp*'s semantic pushforward of the fixed indexed map. -/
theorem canonicalIncidencePushforward_eq_logupPushforward (k : Nat)
    (I : κ → Fin (2 ^ k)) (X : κ → F) :
    canonicalIncidencePushforward k I X = logupPushforward I X := by
  classical
  funext tableIndex
  simp only [canonicalIncidencePushforward, canonicalIncidence_apply,
    logupPushforward]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  by_cases h : I row = tableIndex
  · simp [h]
  · have h' : tableIndex ≠ I row := Ne.symm h
    simp [h, h']

/-- Consequently the linked incidence table preserves the exact lookup
evaluation used by the native LogUp* claim. -/
theorem canonical_indexed_lookup_pullback (k : Nat)
    (I : κ → Fin (2 ^ k)) (X : κ → F)
    (table : Fin (2 ^ k) → F) :
    logupDot (fun row => table (I row)) X =
      logupDot table (canonicalIncidencePushforward k I X) := by
  rw [canonicalIncidencePushforward_eq_logupPushforward]
  exact logup_pullback_pushforward I X table

/-- info: 'Minidregg.Selvage.canonicalIncidence_eq_unitVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalIncidence_eq_unitVector
/-- info: 'Minidregg.Selvage.canonicalIncidencePushforward_eq_logupPushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalIncidencePushforward_eq_logupPushforward
/-- info: 'Minidregg.Selvage.canonical_indexed_lookup_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_indexed_lookup_pullback

end Minidregg.Selvage
