/-
# Canonical opening resolution for arbitrary roots

A root need not lie in `commit`'s image. Resolve each position from any accepted
opening, with an explicit default if no opening exists. Resolution is semantic
(Classical.choose), not an efficient extraction algorithm. A mismatch retains
two actual accepted openings, so no collision/security price is hidden.
-/
import Selvage.BinaryMerkle

namespace Minidregg.Selvage
namespace OpeningResolution

variable {Root F ι Op : Type*}

/-- An arbitrary root admits two different accepted values at one position. -/
def DoubleOpening (S : OpeningScheme Root F ι Op) (rt : Root) : Prop :=
  ∃ i v v' o o', S.verifyOpen rt i v o ∧ S.verifyOpen rt i v' o' ∧ v ≠ v'

/-- Resolve from the root alone, including roots outside the honest image. -/
noncomputable def word (S : OpeningScheme Root F ι Op) (default : F)
    (rt : Root) (i : ι) : F := by
  classical
  exact if h : ∃ v, ∃ o, S.verifyOpen rt i v o then Classical.choose h else default

/-- Statement-first contract. Every accepted value either agrees with the
root's canonical word or retains a concrete double-opening witness. -/
def Correctness (S : OpeningScheme Root F ι Op) (default : F) : Prop :=
  ∀ rt i v o, S.verifyOpen rt i v o →
    v = word S default rt i ∨ DoubleOpening S rt

/-- A canonical value at an openable position comes with an accepted path. -/
theorem word_openable (S : OpeningScheme Root F ι Op) (default : F)
    {rt : Root} {i : ι} (h : ∃ v, ∃ o, S.verifyOpen rt i v o) :
    ∃ o, S.verifyOpen rt i (word S default rt i) o := by
  unfold word
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The statement-first resolver contract, without a binding assumption. -/
theorem correctness (S : OpeningScheme Root F ι Op) (default : F) :
    Correctness S default := by
  intro rt i v o hv
  by_cases heq : v = word S default rt i
  · exact Or.inl heq
  · obtain ⟨o', ho'⟩ := word_openable S default ⟨v, o, hv⟩
    exact Or.inr ⟨i, v, word S default rt i, o, o', hv, ho', heq⟩

/-- Local absence of double openings pins every accepted value. -/
theorem eq_word_of_no_double (S : OpeningScheme Root F ι Op) (default : F)
    {rt : Root} {i : ι} {v : F} {o : Op}
    (hfree : ¬ DoubleOpening S rt) (hv : S.verifyOpen rt i v o) :
    v = word S default rt i :=
  (correctness S default rt i v o hv).resolve_right hfree

/-- Perfect position binding is sufficient for the local condition. -/
theorem no_double_of_binding (S : OpeningScheme Root F ι Op)
    (hb : S.PositionBinding) (rt : Root) : ¬ DoubleOpening S rt := by
  rintro ⟨i, v, v', o, o', hv, hv', hne⟩
  exact hne (hb rt i v v' o o' hv hv')

/-- On honest roots, canonical resolution recovers the original word. -/
theorem word_commit (S : BindingCommitment Root F ι Op) (default : F)
    (w : ι → F) : word S.toOpeningScheme default (S.commit w) = w := by
  funext i
  exact (eq_word_of_no_double S.toOpeningScheme default
    (no_double_of_binding S.toOpeningScheme S.binding _) (S.verifyOpen_commit w i)).symm

/-- Adjoin transparent word roots to a raw opening scheme. A transparent
root is the final polynomial's evaluation word; its opening is equality.
Ordinary roots and paths keep the original verifier unchanged. -/
def transparent (S : OpeningScheme Root F ι Op) :
    OpeningScheme (Root ⊕ (ι → F)) F ι (Option Op) where
  commit w := Sum.inl (S.commit w)
  openAt w i := some (S.openAt w i)
  verifyOpen rt i v op := match rt, op with
    | Sum.inl rt, some op => S.verifyOpen rt i v op
    | Sum.inl _, none => False
    | Sum.inr w, _ => w i = v
  verifyOpen_commit := S.verifyOpen_commit

/-- Transparent roots cannot equivocate, independently of the raw scheme. -/
theorem transparent_no_double (S : OpeningScheme Root F ι Op) (w : ι → F) :
    ¬ DoubleOpening (transparent S) (Sum.inr w) := by
  rintro ⟨i, v, v', o, o', hv, hv', hne⟩
  exact hne (hv.symm.trans hv')

/-- Canonical resolution of a transparent terminal word is exact. -/
theorem word_transparent (S : OpeningScheme Root F ι Op) (default : F)
    (w : ι → F) : word (transparent S) default (Sum.inr w) = w := by
  funext i
  exact (eq_word_of_no_double (transparent S) default
    (transparent_no_double S w) (o := none) rfl).symm

/-- An ordinary-root double opening in the extension retains two paths
accepted by the original scheme. -/
theorem transparent_double_original (S : OpeningScheme Root F ι Op)
    {rt : Root} (h : DoubleOpening (transparent S) (Sum.inl rt)) :
    DoubleOpening S rt := by
  obtain ⟨i, v, v', o, o', hv, hv', hne⟩ := h
  cases o with
  | none => exact False.elim hv
  | some o =>
    cases o' with
    | none => exact False.elim hv'
    | some o' => exact ⟨i, v, v', o, o', hv, hv', hne⟩

/-- Transparent terminal roots preserve a proved binding property of the raw scheme. -/
theorem transparent_binding (S : OpeningScheme Root F ι Op)
    (hb : S.PositionBinding) : (transparent S).PositionBinding := by
  intro rt i v v' o o' hv hv'
  by_contra hne
  have hd : DoubleOpening (transparent S) rt := ⟨i, v, v', o, o', hv, hv', hne⟩
  cases rt with
  | inl rt => exact no_double_of_binding S hb rt (transparent_double_original S hd)
  | inr w => exact transparent_no_double S w hd

/-- The retained resolver obstruction reduces to the existing exact binary
Merkle leaf-or-ordered-node collision event. No collision probability is set. -/
theorem binaryMerkle_double_implies_collision {Value Digest : Type*}
    (H : BinaryMerkle.HashSuite Value Digest) (k : ℕ) {rt : Digest}
    (h : DoubleOpening (BinaryMerkle.openingScheme H k) rt) :
    BinaryMerkle.Collision H := by
  obtain ⟨i, v, v', o, o', hv, hv', hne⟩ := h
  exact BinaryMerkle.accepted_different_values_imply_collision
    H k rt i v v' o o' hv hv' hne

/-! ## Witnesses, teeth, and premise inhabitation -/

/-- A binding scheme with duplicate root tags. Its `true` roots all lie
outside the honest commit image but admit complete, unique openings. -/
def tagged (F ι : Type*) : BindingCommitment ((ι → F) × Bool) F ι Unit where
  commit w := (w, false)
  openAt _ _ := ()
  verifyOpen rt i v _ := rt.1 i = v
  verifyOpen_commit _ _ := rfl
  binding _ _ _ _ _ _ h h' := h.symm.trans h'

/-- False: binding plus full openability implies an honest root preimage. -/
theorem honest_image_falsifier :
    let S := tagged Bool Unit
    let rt := ((fun _ : Unit => true), true)
    (∀ i, ∃ v o, S.verifyOpen rt i v o) ∧
      ¬ ∃ w, rt = S.commit w := by
  refine ⟨fun _ => ⟨true, (), rfl⟩, ?_⟩
  rintro ⟨w, h⟩
  have htag := congrArg Prod.snd h
  cases htag

/-- The resolver contract is inhabited on an actually off-image root. -/
theorem off_image_resolution_witness (F ι : Type*) (default : F) (w : ι → F) :
    word (tagged F ι).toOpeningScheme default (w, true) = w := by
  funext i
  exact (eq_word_of_no_double (tagged F ι).toOpeningScheme default
    (no_double_of_binding (tagged F ι).toOpeningScheme (tagged F ι).binding _) (o := ()) rfl).symm

/-- A complete but nonbinding scheme for the binding-removal falsifier. -/
def permissive : OpeningScheme Unit Bool Unit Unit where
  commit _ := ()
  openAt _ _ := ()
  verifyOpen _ _ _ _ := True
  verifyOpen_commit _ _ := trivial

/-- Dropping binding cannot force every accepted value to one word. -/
theorem binding_removal_falsifier :
    ¬ ∀ v : Bool, permissive.verifyOpen () () v () →
      v = word permissive false () () := by
  intro h
  have hfalse := h false trivial
  have htrue := h true trivial
  have := hfalse.trans htrue.symm
  cases this

/-- A concrete conflicting-opening witness inhabits the retained bad event. -/
theorem double_opening_inhabited : DoubleOpening permissive () := by
  exact ⟨(), false, true, (), (), trivial, trivial, by decide⟩

end OpeningResolution
end Minidregg.Selvage

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.OpeningResolution.word_openable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.word_openable
/-- info: 'Minidregg.Selvage.OpeningResolution.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.correctness
/-- info: 'Minidregg.Selvage.OpeningResolution.eq_word_of_no_double' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.eq_word_of_no_double
/-- info: 'Minidregg.Selvage.OpeningResolution.no_double_of_binding' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.no_double_of_binding
/-- info: 'Minidregg.Selvage.OpeningResolution.word_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.word_commit
/-- info: 'Minidregg.Selvage.OpeningResolution.transparent_no_double' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.transparent_no_double
/-- info: 'Minidregg.Selvage.OpeningResolution.word_transparent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.word_transparent
/-- info: 'Minidregg.Selvage.OpeningResolution.transparent_double_original' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.transparent_double_original
/-- info: 'Minidregg.Selvage.OpeningResolution.transparent_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.transparent_binding
/-- info: 'Minidregg.Selvage.OpeningResolution.binaryMerkle_double_implies_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.binaryMerkle_double_implies_collision
/-- info: 'Minidregg.Selvage.OpeningResolution.honest_image_falsifier' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.honest_image_falsifier
/-- info: 'Minidregg.Selvage.OpeningResolution.off_image_resolution_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.off_image_resolution_witness
/-- info: 'Minidregg.Selvage.OpeningResolution.binding_removal_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.binding_removal_falsifier
/-- info: 'Minidregg.Selvage.OpeningResolution.double_opening_inhabited' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.OpeningResolution.double_opening_inhabited
