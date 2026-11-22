module
/- Templates over rigid Self/Super (OB-LTUO LT2, MODULAR-TYPING.md §6).

The canonicalization lemmas remain useful compatibility laws for finite syntax.
Public agreement is now structural equi-recursive bisimulation. Its hereditary
substitution theorem lives in EquiRecursiveSubstitutionTransport; this module
lifts it through the typing relation (`Discharges.partialTyping_instantiate`). Discharges retains its original
fields. Agreement and checker transport require validated instance assumptions,
which connect declared nominal shareability to semantic resource safety. -/
public import Obend.Core.Ty
public import Obend.Core.EquiRecursiveSubstitution
public import Obend.Core.Check
public import Obend.Tactic.Cases
import all Obend.Core.Check
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty
set_option autoImplicit false

theorem lt_of_not_lt_ne {a b : String} (h1 : ¬ a < b) (h2 : a ≠ b) : b < a :=
  Decidable.byContradiction fun h3 => h2 (String.le_antisymm (String.not_lt.mp h3) (String.not_lt.mp h1))

theorem tri {a b : String} (h : a ≠ b) : (a < b ∧ ¬ b < a) ∨ (b < a ∧ ¬ a < b) := by
  by_cases l : a < b
  · exact .inl ⟨l, String.lt_asymm l⟩
  · have g := lt_of_not_lt_ne l h
    exact .inr ⟨g, l⟩

/-- Inserting a name twice keeps the second insertion when the first is shareable
(a non-shareable first insertion stays behind the second). -/
theorem insertCanonical_same (row : Ty) (name : String) (first second : Ty) (shareable : first.shareable = true) :
    (row.insertCanonical name first).insertCanonical name second = row.insertCanonical name second := by
  induction row with
  | field prior old tail _ ih =>
    by_cases he : name = prior
    · subst he
      by_cases ho : old.shareable = true <;> simp [Ty.insertCanonical, ho, shareable]
    · by_cases hl : name < prior
      · simp [Ty.insertCanonical, he, hl, shareable]
      · simp [Ty.insertCanonical, he, hl, ih]
  | _ => simp [Ty.insertCanonical, shareable]

/-- Inserting two different names commutes. -/
theorem insertCanonical_comm (row : Ty) (n p : String) (a b : Ty) (ne : n ≠ p) :
    (row.insertCanonical n a).insertCanonical p b = (row.insertCanonical p b).insertCanonical n a := by
  have ne' : p ≠ n := fun h => ne h.symm
  induction row with
  | field q o t _ ih =>
    by_cases ho : o.shareable = true
    · by_cases hn : n = q
      · subst hn
        by_cases hp : p < n
        · simp [Ty.insertCanonical, ne, ne', hp, String.lt_asymm hp, ho]
        · have : n < p := lt_of_not_lt_ne hp ne'
          simp [Ty.insertCanonical, ne', hp, ho, this, String.lt_asymm this]
      · by_cases hp : p = q
        · subst hp
          by_cases hl : n < p
          · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl, ho]
          · have : p < n := lt_of_not_lt_ne hl ne
            simp [Ty.insertCanonical, ne, hl, ho, this]
        · have hp' : q ≠ p := fun h => hp h.symm
          rcases tri hn with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases tri hp with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
            rcases tri ne with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
            simp [Ty.insertCanonical, a1, a2, b1, b2, c1, c2, hn, hp, hp', ne, ne', ih] <;>
            first
            | exact absurd (String.lt_trans (String.lt_trans ‹_› ‹_›) ‹_›) (String.lt_irrefl _)
            | skip
    · by_cases hn : n = q
      · subst hn
        by_cases hp : p < n
        · simp [Ty.insertCanonical, ne, ne', hp, String.lt_asymm hp, ho]
        · have : n < p := lt_of_not_lt_ne hp ne'
          simp [Ty.insertCanonical, ne', hp, ho, this, String.lt_asymm this]
      · by_cases hp : p = q
        · subst hp
          by_cases hl : n < p
          · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl, ho]
          · have : p < n := lt_of_not_lt_ne hl ne
            simp [Ty.insertCanonical, ne, hl, ho, this]
        · have hp' : q ≠ p := fun h => hp h.symm
          rcases tri hn with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases tri hp with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
            rcases tri ne with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
            simp [Ty.insertCanonical, a1, a2, b1, b2, c1, c2, hn, hp, hp', ne, ne', ih] <;>
            first
            | exact absurd (String.lt_trans (String.lt_trans ‹_› ‹_›) ‹_›) (String.lt_irrefl _)
            | skip
  | _ =>
    by_cases hl : n < p
    · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl]
    · have hl' : p < n := lt_of_not_lt_ne hl ne
      simp [Ty.insertCanonical, ne, ne', hl, hl']

/-- A shareable type stays shareable at every instance: it mentions no variable where
shareability looks. -/
theorem shareable_instantiate (σ : Nat → Ty) : ∀ {type : Ty}, type.shareable = true →
    (type.instantiate σ).shareable = true
  | .field _ member tail, h => by
    simp only [Ty.shareable, Bool.and_eq_true] at h
    simp [Ty.instantiate, Ty.shareable, shareable_instantiate σ h.1, shareable_instantiate σ h.2]
  | .specification m e, h => by
    simp only [Ty.shareable, Bool.and_eq_true] at h
    simp [Ty.instantiate, Ty.shareable, shareable_instantiate σ h.1, shareable_instantiate σ h.2]
  | .prototype s t, h => by
    simp only [Ty.shareable, Bool.and_eq_true] at h
    simp [Ty.instantiate, Ty.shareable, shareable_instantiate σ h.1, shareable_instantiate σ h.2]
  | .variant r, h => by
    simp only [Ty.shareable] at h
    simp [Ty.instantiate, Ty.shareable, shareable_instantiate σ h]
  | .variable _, h => by simp [Ty.shareable] at h
  | .natural, _ | .label, _ | .boolean, _ | .emptyRow, _ | .custody _, _ | .arrow _ _ _ _, _
  | .computation _ _ _, _ => by simp_all [Ty.instantiate, Ty.shareable]

theorem canonical_instantiate_insert (σ : Nat → Ty) (row : Ty) (name : String) (member : Ty) :
    ((row.insertCanonical name member).instantiate σ).canonical =
      ((row.instantiate σ).canonical).insertCanonical name ((member.instantiate σ).canonical) := by
  induction row with
  | field prior old tail _ ih =>
    by_cases he : name = prior
    · subst he
      by_cases ho : old.shareable = true
      · have sh : ((old.instantiate σ).canonical).shareable = true := by
          rw [Ty.shareable_canonical]; exact shareable_instantiate σ ho
        simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical, ho, insertCanonical_same _ _ _ _ sh]
      · simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical, ho]
    · by_cases hl : name < prior
      · simp [Ty.insertCanonical, he, hl, Ty.instantiate, Ty.canonical]
      · simp only [Ty.insertCanonical, he, hl, if_false, Ty.instantiate, Ty.canonical]
        rw [ih, insertCanonical_comm _ _ _ _ _ he]
  | _ => simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical]

/-- Canonical form commutes with instantiation, up to a final `canonical`. -/
theorem canonical_instantiate (σ : Nat → Ty) (type : Ty) :
    (type.instantiate σ).canonical = (type.canonical.instantiate σ).canonical := by
  induction type with
  | field name member tail ihm iht =>
    simp only [Ty.instantiate, Ty.canonical]
    rw [canonical_instantiate_insert, ← iht, ← ihm]
  | arrow reuse q d c ihd ihc => simp [Ty.instantiate, Ty.canonical, ihd, ihc]
  | specification m e ihm ihe => simp [Ty.instantiate, Ty.canonical, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.instantiate, Ty.canonical, ihs, iht]
  | variant r ih => simp [Ty.instantiate, Ty.canonical, ih]
  | computation p r a ihp ihr iha => simp [Ty.instantiate, Ty.canonical, ihp, ihr, iha]
  | _ => simp [Ty.instantiate, Ty.canonical]

/-- So a conversion the template's checker accepted survives every instantiation. -/
theorem canonical_eq_instantiate (σ : Nat → Ty) {a b : Ty} (h : a.canonical = b.canonical) :
    (a.instantiate σ).canonical = (b.instantiate σ).canonical := by
  rw [canonical_instantiate σ a, canonical_instantiate σ b, h]

/-! ## Step 4: a template typed against its rigid bounds is typed at every discharge

`Discharges.partialTyping_instantiate` (MODULAR-TYPING §6). A template is typed under assumptions
whose `rigid` variables are its `Self` (a lower bound, never an alias). An instance is the SAME
term in the context instantiated by `σ`, under the instance's assumptions. If `σ` discharges the
bounds (`Discharges`), the instance is typed at the template's type instantiated, with the same
uses. `extra` is the instance's additional lookup depth (a wider row may hide a member deeper than
the bound did); the relation's lookups are at any depth, so it is absorbed. The checker-level
statement is `CheckerTransport.Discharges.checkAgainst_instantiate`. -/

open Obend.Core.Check Obend.Core.Term

@[expose] public def instantiateAnnotation (σ : Nat → Ty) (annotation : LambdaAnnotation) : LambdaAnnotation :=
  { annotation with domain := annotation.domain.instantiate σ, codomain := annotation.codomain.instantiate σ }

@[expose] public def instantiateAnnotations (σ : Nat → Ty) (annotations : Annotations) : Annotations :=
  fun position => (annotations position).map (instantiateAnnotation σ)

theorem instantiate_parameter (σ : Nat → Ty) (annotations : Annotations) (position : List Nat) :
    ((instantiateAnnotations σ annotations position).map (·.parameter)) = (annotations position).map (·.parameter) := by
  simp only [instantiateAnnotations, Option.map_map]; rfl

@[expose] public def instantiateContext (σ : Nat → Ty) (context : Context) : Context :=
  context.map fun binding => ⟨binding.type.instantiate σ, binding.quantity⟩

/- Lean v4.35 checks implicit arguments at `.implicit` transparency
(`backward.isDefEq.respectTransparency`): the checker transport below rewrites `infer` results
whose context index is `instantiateContext σ (b :: Γ)` into goals indexed by
`⟨b.type.instantiate σ, b.quantity⟩ :: instantiateContext σ Γ`. Those agree by unfolding these
three definitions, so they are implicit-reducible in this module. -/
attribute [local implicit_reducible] Ty.instantiate instantiateAnnotation instantiateContext


section
variable {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}

theorem alias_not_rigid {assumptions : Assumptions} {j : Nat} {bound : Ty}
    (found : assumptions.alias j = some bound) : j ∉ assumptions.rigid := by
  intro member
  have : assumptions.rigid.contains j = true := by simpa using member
  rw [Assumptions.alias_rigid this] at found
  cases found

theorem instantiate_isComputation (pure : ∀ j, (σ j).isComputation = false) (type : Ty) :
    (type.instantiate σ).isComputation = type.isComputation := by
  cases type with
  | «variable» j => exact pure j
  | _ => simp [Ty.instantiate, Ty.isComputation]

theorem shareableUnder_instantiate {vars vars' : List Nat}
    (shareable : ∀ j, (σ j).shareableUnder vars' = vars.contains j) (type : Ty) :
    (type.instantiate σ).shareableUnder vars' = type.shareableUnder vars := by
  induction type with
  | «variable» j => simp [Ty.instantiate, Ty.shareableUnder, shareable]
  | field _ m t ihm iht => simp [Ty.instantiate, Ty.shareableUnder, ihm, iht]
  | specification m e ihm ihe => simp [Ty.instantiate, Ty.shareableUnder, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.instantiate, Ty.shareableUnder, ihs, iht]
  | variant r ih => simp [Ty.instantiate, Ty.shareableUnder, ih]
  | _ => simp [Ty.instantiate, Ty.shareableUnder, Ty.shareable]

theorem bearsCustody_instantiate (custody : ∀ j, (σ j).bearsCustody = false) (type : Ty) :
    (type.instantiate σ).bearsCustody = type.bearsCustody := by
  induction type with
  | «variable» j => simpa [Ty.instantiate] using custody j
  | field _ m t ihm iht => simp [Ty.instantiate, Ty.bearsCustody, ihm, iht]
  | specification m e ihm ihe => simp [Ty.instantiate, Ty.bearsCustody, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.instantiate, Ty.bearsCustody, ihs, iht]
  | variant r ih => simp [Ty.instantiate, Ty.bearsCustody, ih]
  | _ => simp [Ty.instantiate, Ty.bearsCustody]

theorem instantiate_of_isData {type : Ty} (data : type.isData = true) : type.instantiate σ = type := by
  induction type with
  | field _ m t ihm iht =>
    simp only [Ty.isData, Bool.and_eq_true] at data
    simp [Ty.instantiate, ihm data.1, iht data.2]
  | variant r ih => simp only [Ty.isData] at data; simp [Ty.instantiate, ih data]
  | «variable» _ => simp [Ty.isData] at data
  | arrow => simp [Ty.isData] at data
  | specification => simp [Ty.isData] at data
  | prototype => simp [Ty.isData] at data
  | computation => simp [Ty.isData] at data
  | _ => rfl

theorem isPlan_instantiate {type : Ty} (plan : type.isPlan = true) : type.instantiate σ = type := by
  cases type <;> simp [Ty.isPlan] at plan
  exact instantiate_of_isData (type := .variant _) (by simpa [Ty.isData] using plan)

theorem callable_instantiate {type : Ty} {reuse : Reuse} {quantity : Quantity} {domain codomain : Ty}
    (shape : callable type = .arrow reuse quantity domain codomain) :
    callable (type.instantiate σ) = .arrow reuse quantity (domain.instantiate σ) (codomain.instantiate σ) := by
  induction type with
  | arrow r q d c =>
    simp only [callable] at shape; cases shape; rfl
  | specification m e _ ihe => simp only [callable] at shape; simpa [Ty.instantiate, callable] using ihe shape
  | _ => simp [callable] at shape

theorem instantiateContext_length (context : Context) :
    (instantiateContext σ context).length = context.length := by simp [instantiateContext]

theorem zeroUses_instantiate (context : Context) : zeroUses (instantiateContext σ context) = zeroUses context := by
  simp [zeroUses, instantiateContext_length]

theorem variableUses_instantiate (context : Context) (index : Nat) :
    variableUses (instantiateContext σ context) index = variableUses context index := by
  simp [variableUses, instantiateContext_length]

public theorem safeUses_instantiate (context : Context) (uses : Uses) :
    safeUses (instantiateContext σ context) uses = safeUses context uses := by
  simp only [safeUses, instantiateContext, List.length_map, List.zip_map_left, List.all_map]
  rfl

theorem branchesAgree_instantiate : ∀ (context : Context) (first second : Uses),
    branchesAgree (instantiateContext σ context) first second = branchesAgree context first second
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: context, _ :: first, _ :: second => by
    simp only [instantiateContext, List.map_cons, branchesAgree] at *
    rw [← branchesAgree_instantiate context first second]; rfl

theorem linearFree_instantiate (context : Context) (uses : Uses) :
    linearFree (instantiateContext σ context) uses = linearFree context uses := by
  simp only [linearFree, instantiateContext, List.zip_map_left, List.all_map]
  rfl

theorem reusableCaptures_instantiate {vars vars' : List Nat}
    (shareable : ∀ j, (σ j).shareableUnder vars' = vars.contains j) (context : Context) (uses : Uses) :
    reusableCaptures vars' (instantiateContext σ context) uses = reusableCaptures vars context uses := by
  simp only [reusableCaptures, instantiateContext, List.length_map, List.zip_map_left, List.all_map]
  congr 2
  funext pair
  simp [shareableUnder_instantiate shareable]

public theorem validContext_instantiate {vars vars' : List Nat}
    (shareable : ∀ j, (σ j).shareableUnder vars' = vars.contains j)
    (custody : ∀ j, (σ j).bearsCustody = false) (context : Context) :
    validContext vars' (instantiateContext σ context) = validContext vars context := by
  simp only [validContext, instantiateContext, List.all_map]
  congr 1
  funext binding
  simp [shareableUnder_instantiate shareable, bearsCustody_instantiate custody]

theorem getElem?_instantiateContext (context : Context) (index : Nat) :
    (instantiateContext σ context)[index]? =
      context[index]?.map (fun binding => ⟨binding.type.instantiate σ, binding.quantity⟩) := by
  simp [instantiateContext]

theorem instantiateContext_cons (type : Ty) (quantity : Quantity) (context : Context) :
    instantiateContext σ (⟨type, quantity⟩ :: context) = ⟨type.instantiate σ, quantity⟩ :: instantiateContext σ context := rfl


theorem primitiveTypes_instantiate (primitive : Primitive) :
    (primitiveTypes primitive).1.instantiate σ = (primitiveTypes primitive).1 ∧
      (primitiveTypes primitive).2.instantiate σ = (primitiveTypes primitive).2 := by
  cases primitive <;> exact ⟨rfl, rfl⟩

theorem overlay_instantiate {row : Ty} (closed : row.tail = .emptyRow) (inherited : Ty) :
    (overlay row inherited).instantiate σ = overlay (row.instantiate σ) (inherited.instantiate σ) := by
  induction row with
  | field n m t _ iht => simp only [Ty.tail] at closed; simp [overlay, Ty.instantiate, iht closed]
  | emptyRow => rfl
  | _ => simp [Ty.tail] at closed

/-- A record's row is closed: fields typed in order build a row ending in `{}`. -/
theorem fieldsTyping_tail {assumptions : Assumptions} : ∀ {context : Context} {fields : List (String × Term)}
    {row : Ty} {uses : Uses}, FieldsTyping assumptions context fields row uses → row.tail = .emptyRow
  | _, [], _, _, typed => by cases typed; rfl
  | _, _ :: _, _, _, typed => by
    cases typed with
    | cons _ rest _ => simpa [Ty.tail] using fieldsTyping_tail rest

theorem tail_instantiate : ∀ {row : Ty}, row.tail = .emptyRow → (row.instantiate σ).tail = .emptyRow
  | .field _ _ rest, h => by simpa [Ty.instantiate, Ty.tail] using tail_instantiate (row := rest) (by simpa [Ty.tail] using h)
  | .emptyRow, _ => rfl
  | .natural, h | .label, h | .boolean, h | .variable _, h | .arrow _ _ _ _, h | .specification _ _, h
  | .prototype _ _, h | .custody _, h | .variant _, h | .computation _ _ _, h => by simp [Ty.tail] at h

theorem spineLabels_instantiate : ∀ (row : Ty), row.tail = .emptyRow →
    spineLabels (row.instantiate σ) = spineLabels row
  | .field _ _ rest, h => by simp [Ty.instantiate, spineLabels, spineLabels_instantiate rest (by simpa [Ty.tail] using h)]
  | .emptyRow, _ => rfl
  | .natural, h | .label, h | .boolean, h | .variable _, h | .arrow _ _ _ _, h | .specification _ _, h
  | .prototype _ _, h | .custody _, h | .variant _, h | .computation _ _ _, h => by simp [Ty.tail] at h

theorem splitCovers_instantiate' {row : Ty} {names : List String} (covers : SplitCovers row names = true) :
    SplitCovers (row.instantiate σ) names = true := by
  simp only [SplitCovers, Bool.and_eq_true, beq_iff_eq] at covers ⊢
  exact ⟨tail_instantiate (σ := σ) covers.1, by rw [spineLabels_instantiate (σ := σ) _ covers.1]; exact covers.2⟩

variable (D : Discharges σ template instance_ extra)
include D

theorem Discharges.lookup_instantiate : ∀ (fuel : Nat) (type : Ty) (name : String) (member : Ty),
    type.lookup template.bounds fuel name = some member →
    (type.instantiate σ).lookup instance_.bounds (fuel + extra) name = some (member.instantiate σ)
  | 0, _, _, _, h => by simp [Ty.lookup] at h
  | fuel + 1, type, name, member, h => by
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    cases type with
    | field prior m tail =>
      simp only [Ty.lookup, Ty.instantiate] at h ⊢
      split at h
      · cases h; rw [if_pos ‹_›]
      · rw [if_neg ‹_›]; exact Discharges.lookup_instantiate fuel tail name member h
    | «variable» j =>
      simp only [Ty.lookup, Option.bind_eq_bind] at h
      cases found : template.bounds.lookup j with
      | none => simp [found] at h
      | some bound =>
        simp only [found, Option.bind_some] at h
        by_cases rigid : j ∈ template.rigid
        · exact Ty.lookup_mono (D.lookup j bound rigid found fuel name member h) (by omega)
        · simp only [Ty.instantiate, D.fixed j rigid, Ty.lookup, Option.bind_eq_bind, D.bounds j rigid, found,
            Option.bind_some]
          have := Discharges.lookup_instantiate fuel bound name member h
          rwa [D.closed j bound rigid found] at this
    | _ => simp [Ty.lookup] at h

theorem Discharges.isRow_instantiate : ∀ (fuel : Nat) (type : Ty),
    type.isRow template.bounds fuel = true → (type.instantiate σ).isRow instance_.bounds (fuel + extra) = true
  | 0, _, h => by simp [Ty.isRow] at h
  | fuel + 1, type, h => by
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    cases type with
    | emptyRow => rfl
    | field _ _ tail =>
      simp only [Ty.isRow, Ty.instantiate] at h ⊢
      exact Discharges.isRow_instantiate fuel tail h
    | «variable» j =>
      simp only [Ty.isRow] at h
      cases found : template.bounds.lookup j with
      | none => simp [found] at h
      | some bound =>
        simp only [found] at h
        by_cases rigid : j ∈ template.rigid
        · exact Ty.isRow_mono (D.row j bound rigid found fuel h) (by omega)
        · simp only [Ty.instantiate, D.fixed j rigid, Ty.isRow, D.bounds j rigid, found]
          have := Discharges.isRow_instantiate fuel bound h
          rwa [D.closed j bound rigid found] at this
    | _ => simp [Ty.isRow] at h

/-- Recursive equality is stable at valid discharging instances. Validity
supplies the instance's declared resource premises during substitution. -/
theorem Discharges.sameType_instantiate {actual expected : Ty}
    (instanceValid : instance_.valid = true)
    (agreement : sameType template actual expected = true) :
    sameType instance_ (actual.instantiate σ) (expected.instantiate σ) = true :=
  (sameType_iff instance_ _ _).mpr
    (D.equivalent_instantiate instanceValid ((sameType_iff template actual expected).mp agreement))

theorem Discharges.argumentAllowed_instantiate (quantity : Quantity) (context : Context) (type : Ty) (uses : Uses) :
    argumentAllowed instance_ quantity (instantiateContext σ context) (type.instantiate σ) uses =
      argumentAllowed template quantity context type uses := by
  simp [argumentAllowed, instantiate_isComputation D.pure, shareableUnder_instantiate D.shareable,
    reusableCaptures_instantiate D.shareable, linearFree_instantiate]

theorem Discharges.caseAllowed_instantiate (quantity : Quantity) (context : Context) (uses : Uses) :
    caseAllowed instance_ quantity (instantiateContext σ context) uses = caseAllowed template quantity context uses := by
  simp [caseAllowed, reusableCaptures_instantiate D.shareable, linearFree_instantiate]

theorem Discharges.validBinder_instantiate (payload : Ty) (quantity : Quantity) :
    validContext instance_.shareableVariables [⟨payload.instantiate σ, quantity⟩] =
      validContext template.shareableVariables [⟨payload, quantity⟩] := by
  simp [validContext, shareableUnder_instantiate D.shareable, bearsCustody_instantiate D.custody]

theorem Discharges.reusableAllowed_instantiate (reuse : Reuse) (context : Context) (uses : Uses) :
    reusableAllowed instance_ reuse (instantiateContext σ context) uses = reusableAllowed template reuse context uses := by
  simp [reusableAllowed, reusableCaptures_instantiate D.shareable]

theorem Discharges.splitCovers_instantiate {row : Ty} {names : List String} (covers : SplitCovers row names = true) :
    SplitCovers (row.instantiate σ) names = true := splitCovers_instantiate' (σ := σ) covers

theorem Discharges.splitSpine_instantiate (instanceValid : instance_.valid = true) {context : Context} {uses : Uses}
    {row : Ty} : ∀ {names : List String} {functionType result : Ty},
      SplitSpine template context uses row names functionType result →
      SplitSpine instance_ (instantiateContext σ context) uses (row.instantiate σ) names
        (functionType.instantiate σ) (result.instantiate σ)
  | [], _, _, h => by cases h; rfl
  | _ :: _, _, _, ⟨r, q, m, c, shape, ⟨fuel, found, l, same⟩, pure, allowed, share, rest⟩ =>
    ⟨r, q, m.instantiate σ, c.instantiate σ, callable_instantiate shape,
      ⟨fuel + extra, found.instantiate σ, D.lookup_instantiate fuel row _ found l,
        D.sameType_instantiate instanceValid same⟩,
      by rw [instantiate_isComputation D.pure]; exact pure,
      by rw [D.caseAllowed_instantiate]; exact allowed,
      by rw [D.validBinder_instantiate]; exact share,
      Discharges.splitSpine_instantiate instanceValid rest⟩

/-- **The template theorem on the typing relation** (MODULAR-TYPING §6): a derivation under rigid
bounds is a derivation at every instance that discharges them, in the instantiated context, at the
instantiated type, with the same usage. Every lambda's annotation is instantiated with it (the
relation names each binder's annotation; `instantiateAnnotation`). By induction on the derivation. -/
public theorem Discharges.partialTyping_instantiate (instanceValid : instance_.valid = true)
    {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping template context term type uses) :
    PartialTyping instance_ (instantiateContext σ context) term (type.instantiate σ) uses := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ =>
      PartialTyping instance_ (instantiateContext σ context) term (type.instantiate σ) uses)
    (motive_2 := fun context fields row uses _ =>
      FieldsTyping instance_ (instantiateContext σ context) fields (row.instantiate σ) uses)
    (motive_3 := fun context q arms row result uses _ =>
      ArmsTyping instance_ (instantiateContext σ context) q arms (row.instantiate σ) (result.instantiate σ) uses)
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend ?specification
    ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject ?case ?ifBool ?perform ?done
    ?effectCase ?split ?hole ?fieldsNil ?fieldsCons ?armsNil ?armsCons typed
  case bound =>
    intro Γ index binding found
    rw [← variableUses_instantiate (σ := σ)]
    exact .bound (binding := ⟨binding.type.instantiate σ, binding.quantity⟩)
      (by rw [getElem?_instantiateContext, found]; rfl)
  case natural =>
    intro Γ value; rw [← zeroUses_instantiate (σ := σ)]; exact .natural _ value
  case boolean =>
    intro Γ value; rw [← zeroUses_instantiate (σ := σ)]; exact .boolean _ value
  case label =>
    intro Γ value; rw [← zeroUses_instantiate (σ := σ)]; exact .label _ value
  case lambda =>
    intro Γ body annotation bodyUses _ safe valid captures fits ih
    exact .lambda (annotation := instantiateAnnotation σ annotation) ih
      ((safeUses_instantiate (σ := σ) (⟨annotation.domain, annotation.parameter⟩ :: Γ) bodyUses).trans safe)
      ((validContext_instantiate D.shareable D.custody (⟨annotation.domain, annotation.parameter⟩ :: Γ)).trans valid)
      (by rw [D.reusableAllowed_instantiate]; exact captures) fits
  case conversion =>
    intro Γ term actual expected uses _ agreement ih
    exact .conversion ih (D.sameType_instantiate instanceValid agreement)
  case application =>
    intro Γ function argument functionType argumentType domain codomain fu au reuse quantity
      _ _ shape argumentEq allowed ihF ihA
    subst argumentType
    exact .application ihF ihA (callable_instantiate shape) rfl
      (by rw [D.argumentAllowed_instantiate]; exact allowed)
  case record => intro Γ fields row uses _ distinct ih; exact .record ih distinct
  case get =>
    intro Γ target targetType member uses name fuel _ found free ih
    exact .get ih (D.lookup_instantiate fuel targetType name member found)
      (by rw [linearFree_instantiate]; exact free)
  case extend =>
    intro Γ target fields targetType row tu fu fuel _ fieldsTyped distinct isRow free ihT ihF
    rw [overlay_instantiate (fieldsTyping_tail fieldsTyped)]
    exact .extend ihT ihF distinct (D.isRow_instantiate fuel targetType isRow)
      (by rw [linearFree_instantiate]; exact free)
  case specification =>
    intro Γ metadata extension metadataType extensionType mu eu _ _ pureM pureE free ihM ihE
    exact .specification ihM ihE (by rw [instantiate_isComputation D.pure]; exact pureM)
      (by rw [instantiate_isComputation D.pure]; exact pureE) (by rw [linearFree_instantiate]; exact free)
  case prototype =>
    intro Γ spec target specType targetType su tu _ _ pureS pureT ihS ihT
    exact .prototype ihS ihT (by rw [instantiate_isComputation D.pure]; exact pureS)
      (by rw [instantiate_isComputation D.pure]; exact pureT)
  case reflect =>
    intro Γ target specType targetType uses _ free ih
    exact .reflect ih (by rw [linearFree_instantiate]; exact free)
  case metadata =>
    intro Γ target metadataType extensionType uses _ free ih
    exact .metadata ih (by rw [linearFree_instantiate]; exact free)
  case project =>
    intro Γ target specType targetType uses _ free ih
    exact .project ih (by rw [linearFree_instantiate]; exact free)
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu _ _
      shapeL shapeU captures shareSelf shareInherited shareMiddle ihL ihU
    exact .mix ihL ihU (callable_instantiate shapeL) (callable_instantiate shapeU)
      (by rw [reusableCaptures_instantiate D.shareable]; exact captures)
      (by rw [shareableUnder_instantiate D.shareable]; exact shareSelf)
      (by rw [shareableUnder_instantiate D.shareable]; exact shareInherited)
      (by rw [shareableUnder_instantiate D.shareable]; exact shareMiddle)
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu _ shape _ share allowed captures ihS ihI
    exact .fix ihS (callable_instantiate shape) ihI
      (by rw [shareableUnder_instantiate D.shareable]; exact share)
      (by rw [D.argumentAllowed_instantiate]; exact allowed)
      (by rw [reusableCaptures_instantiate D.shareable]; exact captures)
  case binary =>
    intro Γ primitive left right input output lu ru shape _ _ ihL ihR
    have fixed := primitiveTypes_instantiate (σ := σ) primitive
    rw [shape] at fixed
    rw [fixed.2]; rw [fixed.1] at ihL ihR
    exact .binary shape ihL ihR
  case ifZero =>
    intro Γ value zero successor result vu zu su _ _ _ safe agreeing ihV ihZ ihS
    exact .ifZero ihV ihZ ihS ((safeUses_instantiate (σ := σ) (⟨.natural, .unrestricted⟩ :: Γ) su).trans safe)
      (by rw [branchesAgree_instantiate]; exact agreeing)
  case inject =>
    intro Γ tag payload payloadType row uses fuel _ found nonComputation ih
    exact .inject ih (D.lookup_instantiate fuel row tag payloadType found)
      (by rw [instantiate_isComputation D.pure]; exact nonComputation)
  case case =>
    intro Γ scrutinee arms row result su au q _ _ distinct allowed ihS ihA
    exact .case ihS ihA distinct (by rw [D.caseAllowed_instantiate]; exact allowed)
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu _ _ _ agreeing ihC ihT ihF
    exact .ifBool ihC ihT ihF (by rw [branchesAgree_instantiate]; exact agreeing)
  case perform =>
    intro Γ plan planType response uses _ isPlan data ih
    have planFixed : planType.instantiate σ = planType := isPlan_instantiate isPlan
    have responseFixed : response.instantiate σ = response := instantiate_of_isData data
    show PartialTyping _ _ _ (.computation (planType.instantiate σ) (response.instantiate σ)
      (response.instantiate σ)) _
    rw [planFixed, responseFixed]; rw [planFixed] at ih
    exact .perform ih isPlan data
  case done =>
    intro Γ value plan response result uses _ nonComputation ih
    exact .done ih (by rw [instantiate_isComputation D.pure]; exact nonComputation)
  case effectCase =>
    intro Γ scrutinee arms plan response row result su au q _ _ nonComputation distinct allowed ihS ihA
    exact .effectCase ihS ihA (by rw [instantiate_isComputation D.pure]; exact nonComputation) distinct
      (by rw [D.caseAllowed_instantiate]; exact allowed)
  case split =>
    intro Γ target function names row functionType result tu fu _ _ nodup covers spine ihT ihF
    exact .split ihT ihF nodup (D.splitCovers_instantiate covers) (D.splitSpine_instantiate instanceValid spine)
  case hole =>
    intro Γ n σ' decl args found hσ hctx _ allowed ih
    subst hσ
    have typed := PartialTyping.hole (assumptions := instance_) (context := instantiateContext σ Γ)
      (σ := args.map (·.1)) (args := args.map fun a => (a.1, (⟨a.2.1.type.instantiate σ, a.2.1.quantity⟩ : Binding), a.2.2))
      (D.holes n decl found) (by simp [Function.comp_def]) (by rw [← hctx]; simp [Function.comp_def])
      (fun a ha => by obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact ih b hb)
      (fun a ha => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        rw [D.argumentAllowed_instantiate]; exact allowed b hb)
    simpa [zeroUses_instantiate, Function.comp_def] using typed
  case fieldsNil =>
    intro Γ; rw [← zeroUses_instantiate (σ := σ)]; exact .nil _
  case fieldsCons =>
    intro Γ name body rest type row bu ru _ _ nonComputation ihB ihR
    exact .cons ihB ihR (by rw [instantiate_isComputation D.pure]; exact nonComputation)
  case armsNil =>
    intro Γ q result; rw [← zeroUses_instantiate (σ := σ)]; exact .nil _ q _
  case armsCons =>
    intro Γ q name body rest payload row result bu ru _ safe share fits _ agreeing ihB ihR
    exact .cons ihB ((safeUses_instantiate (σ := σ) (⟨payload, q⟩ :: Γ) bu).trans safe)
      (by rw [D.validBinder_instantiate]; exact share) fits ihR
      (by rw [branchesAgree_instantiate]; exact agreeing)

end

/-! ### Inhabitants

A one-method template over a rigid `Self` (index 5) bounded by `{weight: Nat}`: it reads
`self.weight`. Its instance at `{colour: Label, weight: Nat}` (wider, and `weight` one field
deeper than in the bound, so `extra = 1`) discharges the bounds (`coloured_discharges`), so the
checker accepts it by the theorem (`CheckerTransport.coloured_instance_checks`). `selfAsBoundRow`
returns `self` where the bound ROW is declared: accepted with `Self` an alias, refused with it
rigid (`CheckerTransport.self_as_bound_row_*`). -/

@[expose] public def weightBound : Ty := .field "weight" .natural .emptyRow
@[expose] public def colouredRow : Ty := .field "colour" .label (.field "weight" .natural .emptyRow)
@[expose] public def templateAssumptions : Assumptions := ⟨[(5, weightBound)], [5], [5], []⟩
@[expose] public def colouredSelf : Nat → Ty := fun j => if j = 5 then colouredRow else .variable j

@[expose] public def weightTemplate : AnnotatedTerm :=
  ⟨.lam (.get (.bound 0) "weight"),
    fun position => if position = [] then some ⟨.variable 5, .natural, .unrestricted, .reusable⟩ else none,
    templateAssumptions⟩

public theorem coloured_discharges : Discharges colouredSelf templateAssumptions {} 1 where
  fixed j rigid := by
    have : j ≠ 5 := fun e => rigid (by simp [templateAssumptions, e])
    simp [colouredSelf, this]
  bounds j rigid := by
    have : (j == 5) = false := by simpa using fun e => rigid (by simp [templateAssumptions, e])
    simp [templateAssumptions, List.lookup, this]
  aliases j rigid := by
    have hb : (j == 5) = false := by simpa using fun e => rigid (by simp [templateAssumptions, e])
    have hn : j ≠ 5 := by simpa using hb
    simp [Assumptions.alias, templateAssumptions, List.lookup, hb, hn]
  closed j bound rigid found := by
    have : (j == 5) = false := by simpa using fun e => rigid (by simp [templateAssumptions, e])
    simp [templateAssumptions, List.lookup, this] at found
  lookup k bound rigid found fuel name member h := by
    have hk : k = 5 := by simpa [templateAssumptions] using rigid
    subst hk
    simp [templateAssumptions, List.lookup] at found
    subst found
    cases fuel with
    | zero => simp [Ty.lookup] at h
    | succ f =>
      simp only [weightBound, Ty.lookup] at h
      split at h
      · rename_i e; subst e; cases h
        simp [colouredSelf, colouredRow, Ty.lookup, Ty.instantiate]
      · cases f <;> simp [Ty.lookup] at h
  row k bound rigid found fuel h := by
    have hk : k = 5 := by simpa [templateAssumptions] using rigid
    subst hk
    simp [templateAssumptions, List.lookup] at found
    subst found
    cases fuel with
    | zero => simp [Ty.isRow] at h
    | succ f =>
      cases f with
      | zero => simp [weightBound, Ty.isRow] at h
      | succ f => simp [colouredSelf, colouredRow, Ty.isRow]
  shareable j := by
    by_cases e : j = 5
    · subst e; simp [colouredSelf, colouredRow, Ty.shareableUnder, Ty.shareable, templateAssumptions]
    · simp [colouredSelf, e, Ty.shareableUnder, Ty.shareable, templateAssumptions]
  custody j := by
    by_cases e : j = 5
    · subst e; simp [colouredSelf, colouredRow]
    · simp [colouredSelf, e]
  pure j := by
    by_cases e : j = 5
    · subst e; simp [colouredSelf, colouredRow, Ty.isComputation]
    · simp [colouredSelf, e, Ty.isComputation]
  holes n decl found := by simp [templateAssumptions] at found

/-- D2's fixture: `self` returned where the bound row is declared, with `Self` rigid when `rigid`
names it. -/
@[expose] public def selfAsBoundRow (rigid : List Nat) : AnnotatedTerm :=
  ⟨.lam (.bound 0),
    fun position => if position = [] then some ⟨.variable 5, weightBound, .unrestricted, .reusable⟩ else none,
    ⟨[(5, weightBound)], [5], rigid, []⟩⟩

end Obend.Core.Proofs.Templates

