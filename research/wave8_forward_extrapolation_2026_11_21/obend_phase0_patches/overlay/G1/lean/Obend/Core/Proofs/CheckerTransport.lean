module
/- The checker's transport theorems, stated of `Bidirectional.checkAgainst`: substitution
(`checkAgainst_msubst`) and template instantiation (`Discharges.checkAgainst_instantiate`). Each is
the relation-level theorem (`TypedSubstitution.checked_msubst`, `Templates.Discharges.partialTyping_instantiate`)
followed by annotated completeness (`BidirectionalCompleteness.annotated_complete`): the transported
term is accepted by the checker under prepared annotations, at the transported type, with the
transported uses.

Why prepared annotations and not the original ones carried along. The fuel checker's
`infer_instantiate` kept the template's annotations, instantiated: `infer` only asks `agree` yes or
no and keeps its own synthesized type. The bidirectional checker does not: an elimination form's
ascription (`Bidirectional.ascribe`) takes the annotation's type when it agrees with the synthesized
one and keeps the synthesized one otherwise, and the two then drive different weak-head forms and
row lookups downstream. A rigid `Self` makes that branch move under instantiation: `variable Self`
and its bound row disagree in the template (rigid, never an alias) and the instance row and the
instantiated bound may agree, so the instance's run takes a branch the template's never took. No
statement of the form "the instantiated annotations are accepted" follows from the template's run;
acceptance under re-prepared annotations does, for every instance. The substitution theorem is in
the same position: the filled term's annotations are the template's around the fillings' own, and a
filling's ascriptions meet a context they were not checked in. -/
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Proofs.TypedSubstitution
public import Obend.Core.Proofs.Templates
import all Obend.Core.Check

namespace Obend.Core.Proofs.CheckerTransport
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional Obend.Core.Invariant
open Obend.Core.Proofs.Substitution Obend.Core.Proofs.Templates
open Obend.Core.Proofs.BidirectionalCompleteness (annotated_complete)
set_option autoImplicit false

/-- **The substitution lemma for the checker.** A term the checker accepts in `Ψ` at `A`, with every
filling `σ` names closed, sharing the term's assumptions, and accepted in `Ψ` at exactly the type `Ψ`
declares for its hypothesis, gives `msubst σ t` accepted in `Ψ` at `A` under prepared annotations, with
pointwise no more uses of any hypothesis than `t` had. -/
public theorem checkAgainst_msubst {t : AnnotatedTerm} {Ψ : Context} {A : Ty} {c : Checked t Ψ}
    (σ : Nat → Option AnnotatedTerm) (accepted : checkAgainst t Ψ A = .ok c)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ b : Binding, Ψ[x]? = some b ∧ ∃ d, checkAgainst f Ψ b.type = .ok d) :
    ∃ annotations, ∃ c' : Checked { msubst σ t with annotations := annotations } Ψ,
      checkAgainst { msubst σ t with annotations := annotations } Ψ A = .ok c' ∧ UsesLE c'.uses c.uses := by
  have typedσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ b : Binding, Ψ[x]? = some b ∧ ∃ d : Checked f Ψ, d.type = b.type := by
    intro x f found
    obtain ⟨closed, same, b, hb, d, hd⟩ := hσ x f found
    exact ⟨closed, same, b, hb, d, (checkAgainst_sound hd).1⟩
  obtain ⟨c', type', le⟩ := TypedSubstitution.checked_msubst c σ typedσ
  have type : c'.type = A := type'.trans (checkAgainst_sound accepted).1
  obtain ⟨annotations, checked, accepted', uses⟩ :=
    annotated_complete (source := { msubst σ t with annotations := (msubst σ t).annotations })
      c'.derivation c'.safe c'.contextValid c'.assumptionsValid
  refine ⟨annotations, checked, ?_, ?_⟩
  · rw [← type]; exact accepted'
  · rw [uses]; exact le

/-- **The template theorem for a certificate.** A term typed under rigid bounds (any `Checked`, in
particular the front end's template check, `Spec.FrontEnd.checkTemplate`) is accepted by the checker
at every instance that discharges the bounds (the instance's assumptions valid, as for any program):
in the instantiated context, at the instantiated type, with the same uses, under prepared annotations. -/
public theorem Discharges.checked_instantiate {σ : Nat → Ty} {instance_ : Assumptions} {extra : Nat}
    {source : AnnotatedTerm} {context : Context} (D : Discharges σ source.assumptions instance_ extra)
    (checked : Checked source context) (valid : instance_.valid = true) :
    ∃ annotations, ∃ checked' : Checked ⟨source.term, annotations, instance_⟩ (instantiateContext σ context),
      checkAgainst ⟨source.term, annotations, instance_⟩ (instantiateContext σ context)
          (checked.type.instantiate σ) = .ok checked' ∧
        checked'.uses = checked.uses := by
  have typed := D.partialTyping_instantiate valid checked.derivation
  have safe : safeUses (instantiateContext σ context) checked.uses = true :=
    (safeUses_instantiate (σ := σ) context checked.uses).trans checked.safe
  have contextValid : validContext instance_.shareableVariables (instantiateContext σ context) = true :=
    (validContext_instantiate D.shareable D.custody context).trans checked.contextValid
  exact annotated_complete (source := ⟨source.term, fun _ => none, instance_⟩) typed safe contextValid valid

/-- **The template theorem for the checker** (`check_instantiate` restated over `checkAgainst`): a
template the checker accepts at `expected` under rigid bounds is accepted at every discharging
instance, at `expected` instantiated, with the same uses, under prepared annotations. -/
public theorem Discharges.checkAgainst_instantiate {σ : Nat → Ty} {instance_ : Assumptions} {extra : Nat}
    {source : AnnotatedTerm} {context : Context} {expected : Ty} {checked : Checked source context}
    (D : Discharges σ source.assumptions instance_ extra)
    (accepted : checkAgainst source context expected = .ok checked) (valid : instance_.valid = true) :
    ∃ annotations, ∃ checked' : Checked ⟨source.term, annotations, instance_⟩ (instantiateContext σ context),
      checkAgainst ⟨source.term, annotations, instance_⟩ (instantiateContext σ context)
          (expected.instantiate σ) = .ok checked' ∧
        checked'.uses = checked.uses := by
  have type := (checkAgainst_sound accepted).1
  rw [← type]
  exact Discharges.checked_instantiate D checked valid

/-! ### The template fixtures (`Templates.weightTemplate`, `selfAsBoundRow`) on the checker -/

/-- The one-method template over a rigid `Self` bounded by `{weight: Nat}` is accepted at
`Self → Nat`. -/
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem weight_template_checks :
    (checkAgainst weightTemplate [] (.arrow .reusable .unrestricted (.variable 5) .natural)).toBool = true := by
  decide +kernel

/-- Its instance at the wider row `{colour: Label, weight: Nat}` is accepted BY THE THEOREM, at the
instantiated type, with no re-check of the template. -/
theorem coloured_instance_checks :
    ∃ annotations, ∃ checked : Checked ⟨weightTemplate.term, annotations, {}⟩ [],
      checkAgainst ⟨weightTemplate.term, annotations, {}⟩ [] (.arrow .reusable .unrestricted colouredRow .natural) =
        .ok checked := by
  cases h : checkAgainst weightTemplate [] (.arrow .reusable .unrestricted (.variable 5) .natural) with
  | error e => have w := weight_template_checks; rw [h] at w; cases w
  | ok checked =>
    obtain ⟨annotations, checked', accepted, _⟩ :=
      Discharges.checkAgainst_instantiate (σ := colouredSelf) (instance_ := {}) (context := []) coloured_discharges h (by decide)
    exact ⟨annotations, checked', accepted⟩

/-- D2's tooth on the checker: `self` returned where the bound row is declared. With `Self` an alias
of its bound the checker accepts it; with `Self` rigid it refuses it. -/
-- fixture kept (2026-11-04): cheap closed check of `checkAgainst` on literal data
example :
    (checkAgainst (selfAsBoundRow []) [] (.arrow .reusable .unrestricted (.variable 5) weightBound)).toBool = true := by
  decide +kernel

-- fixture kept (2026-11-04): refusal witness: `checkAgainst` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    (checkAgainst (selfAsBoundRow [5]) [] (.arrow .reusable .unrestricted (.variable 5) weightBound)).toBool = false := by
  decide +kernel

end Obend.Core.Proofs.CheckerTransport
