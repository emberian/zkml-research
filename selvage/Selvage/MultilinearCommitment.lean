/-
# Selvage.MultilinearCommitment — the claim object for hash-based multilinear openings

`OpeningScheme.openAt` is positional because the commitment is a Merkle/vector
commitment to a codeword.  A multilinear evaluation is not another kind of leaf
opening and must not be represented by changing that field to accept a field point.
BaseFold/WHIR prove an evaluation by an interactive reduction over the SAME committed
word, later compiled by Selvage's RBR/Fiat--Shamir/BCS cone.

This file installs the claim-level seam that was missing between
`BaseFoldCompleteness` and consumers such as the zkML contraction:

* `MleEvalClaim` is `(root, point, value)`;
* `basefoldWord` is the ordinary Reed--Solomon evaluation word of the Boolean
  Möbius packing;
* `MleEvalClaim.Holds` says that the root commits such a word and that the encoded
  table evaluates to the claimed value;
* `holds_iff_of_committed` proves that, inside the BaseFold degree window, a binding
  root fixes the value.  It uses commitment binding to fix the word, RS interpolation
  uniqueness to fix the polynomial, and the already-proved Möbius injectivity to fix
  the table.

This is not the opening protocol.  The remaining object is exactly the braided
BaseFold `Reduction`/`RbrKnowledgeSoundness` instance.  Positional Merkle openings
remain the BCS query layer of that reduction; `[COMMIT-CR]` remains the deployed
binding floor.

Teeth over the landed F5 tower show both directions: the honest claim is inhabited,
and changing only its value is refused at the claim predicate.  The refusal consumes
binding and the domain-size/degree-window condition rather than computation on the
particular table.
-/
import Selvage.BaseFoldCompleteness
import Selvage.Commitment
import Selvage.OutOfDomain

namespace Minidregg.Selvage

open Polynomial

variable {Root F ι Op : Type*} {m : ℕ}

/-- A multilinear evaluation claim over a vector-commitment root.  The proof is an
interactive reduction/transcript, not an `OpeningScheme.openAt` value. -/
structure MleEvalClaim (Root F : Type*) (m : ℕ) where
  rt : Root
  pt : Fin m → F
  val : F

/-- The ordinary RS word committed by BaseFold: evaluate the Boolean Möbius packing
of `table` on the commitment domain. -/
noncomputable def basefoldWord [Field F] (dom : ι ↪ F)
    (table : (Fin m → Bool) → F) : ι → F :=
  fun i => (booleanMobiusPolynomial m table).eval (dom i)

/-- Truth of a BaseFold-shaped multilinear claim.  The root is the SAME vector root
used by `OpeningScheme`; only the statement interpreted above it is new. -/
def MleEvalClaim.Holds [Field F] (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (c : MleEvalClaim Root F m) : Prop :=
  ∃ table : (Fin m → Bool) → F,
    c.rt = S.commit (basefoldWord dom table) ∧ mle table c.pt = c.val

section Binding

variable [Field F] [DecidableEq F] [Fintype ι]

omit [DecidableEq F] [Fintype ι] in
/-- The honest claim is true by construction. -/
theorem MleEvalClaim.holds_of_commit (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (table : (Fin m → Bool) → F) (pt : Fin m → F) :
    MleEvalClaim.Holds S dom
      ⟨S.commit (basefoldWord dom table), pt, mle table pt⟩ :=
  ⟨table, rfl, rfl⟩

/-- Binding of the vector commitment fixes the encoded Boolean table, provided the
commitment domain is large enough for the BaseFold degree window.  This is the exact
place where vector-root binding becomes multilinear-value binding. -/
theorem basefoldWord_injective (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (hcard : 2 ^ m ≤ Fintype.card ι) :
    Function.Injective (fun table : (Fin m → Bool) → F =>
      S.commit (basefoldWord dom table)) := by
  intro f g hroot
  have hword : basefoldWord dom f = basefoldWord dom g :=
    S.commit_injective hroot
  have hpoly : booleanMobiusPolynomial m f = booleanMobiusPolynomial m g := by
    refine eq_of_degreeLT_of_agree dom hcard
      (degree_booleanMobiusPolynomial_lt m f)
      (degree_booleanMobiusPolynomial_lt m g) ?_
    intro i
    exact congrFun hword i
  exact booleanMobiusPolynomial_injective m hpoly

/-- At a known honest root, the claim predicate is equivalent to equality with the
one value fixed by the committed table.  No evaluation-point-shaped opening primitive
is assumed or needed. -/
theorem MleEvalClaim.holds_iff_of_committed
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (hcard : 2 ^ m ≤ Fintype.card ι) (table : (Fin m → Bool) → F)
    (c : MleEvalClaim Root F m)
    (hrt : c.rt = S.commit (basefoldWord dom table)) :
    c.Holds S dom ↔ mle table c.pt = c.val := by
  constructor
  · rintro ⟨table', hrt', hval⟩
    have ht : table' = table := basefoldWord_injective S dom hcard
      (hrt'.symm.trans hrt)
    simpa [ht] using hval
  · intro hval
    exact ⟨table, hrt, hval⟩

/-- Two true claims at the same root and point have the same value.  This is the
consumer-facing binding theorem: a contraction verifier cannot obtain two different
terminal values from one binding BaseFold commitment. -/
theorem MleEvalClaim.value_unique
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (hcard : 2 ^ m ≤ Fintype.card ι)
    {c d : MleEvalClaim Root F m} (hrt : c.rt = d.rt) (hpt : c.pt = d.pt)
    (hc : c.Holds S dom) (hd : d.Holds S dom) : c.val = d.val := by
  obtain ⟨f, hfrt, hfval⟩ := hc
  obtain ⟨g, hgrt, hgval⟩ := hd
  have hfg : f = g := basefoldWord_injective S dom hcard
    (hfrt.symm.trans (hrt.trans hgrt))
  rw [hfg, hpt] at hfval
  exact hfval.symm.trans hgval

/-- **Refusal tooth:** at a binding root, changing only the claimed value makes the
claim false. -/
theorem MleEvalClaim.wrong_value_refused
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (hcard : 2 ^ m ≤ Fintype.card ι) (table : (Fin m → Bool) → F)
    (pt : Fin m → F) {bad : F} (hbad : bad ≠ mle table pt) :
    ¬ MleEvalClaim.Holds S dom
      ⟨S.commit (basefoldWord dom table), pt, bad⟩ := by
  intro h
  have hv := (MleEvalClaim.holds_iff_of_committed S dom hcard table _ rfl).mp h
  exact hbad hv.symm

end Binding

/-! ## F5 premise firing and teeth -/

namespace MleEvalClaimExample

open ProximityExample BaseFoldExample

/-- The honest one-variable F5 claim over the landed BaseFold table and domain. -/
noncomputable def honestClaim :
    MleEvalClaim (Fin 4 → ZMod 5) (ZMod 5) 1 :=
  ⟨(idealCommitment (ZMod 5) (Fin 4)).commit
      (basefoldWord (ldtTower.dom 0) table), ![3], mle table ![3]⟩

/-- The claim predicate is inhabited on the real BaseFold example. -/
theorem honestClaim_holds :
    honestClaim.Holds (idealCommitment (ZMod 5) (Fin 4)) (ldtTower.dom 0) :=
  MleEvalClaim.holds_of_commit _ _ table ![3]

/-- Changing only `4` to `0` is refused through binding and RS-window uniqueness. -/
theorem wrong_value_refused_f5 :
    ¬ MleEvalClaim.Holds (idealCommitment (ZMod 5) (Fin 4)) (ldtTower.dom 0)
      ⟨(idealCommitment (ZMod 5) (Fin 4)).commit
          (basefoldWord (ldtTower.dom 0) table), ![3], 0⟩ := by
  refine MleEvalClaim.wrong_value_refused _ _ (by norm_num) table ![3] ?_
  have hv : mle table ![3] = 4 := by
    have h := mobius_descent_terminal
      (⟨0, by norm_num [levels]⟩ : levels 1)
    rw [basefold_terminal_is_mle] at h
    exact h
  rw [hv]
  decide

end MleEvalClaimExample

/-- info: 'Minidregg.Selvage.basefoldWord_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldWord_injective
/-- info: 'Minidregg.Selvage.MleEvalClaim.holds_iff_of_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MleEvalClaim.holds_iff_of_committed
/-- info: 'Minidregg.Selvage.MleEvalClaim.value_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MleEvalClaim.value_unique
/-- info: 'Minidregg.Selvage.MleEvalClaimExample.honestClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MleEvalClaimExample.honestClaim_holds
/-- info: 'Minidregg.Selvage.MleEvalClaimExample.wrong_value_refused_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MleEvalClaimExample.wrong_value_refused_f5

end Minidregg.Selvage
