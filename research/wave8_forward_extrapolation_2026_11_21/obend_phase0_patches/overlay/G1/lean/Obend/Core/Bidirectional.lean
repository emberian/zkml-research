module
/- The checker of Core4: bidirectional, over the specification in `Obend.Core.Check`
(`PartialTyping`, `Checked`, the quantity rules, `sameType`, the row machinery).

`synthAt` infers a type for a term; `checkAt` checks a term against an expected type.
Both recurse on the term (no fuel), return `Except CheckRefusal`, and carry the
declarative derivation (`PartialTyping`), so soundness is by construction. Conversion happens only where synthesis meets an expected type: the
mode switch (`checkAt` of an elimination form), an expected type's head unfolded to
weak-head form (`whnf`), and a join (`ifBool`, `ifZero`, `case` in synthesis, which
synthesize one branch and check the rest against it). Usage vectors are synthesized
bottom-up exactly as the relation computes them.

Representative annotations are used in both modes. In synthesis: a lambda's (`LambdaAnnotation`), an
injection's (its codomain is the sum, or an alias of it, `injectionHead`), a `perform`'s (plan and response), a `done`'s
(plan and response), and, anywhere else, an ascription (its codomain): an
introduction form checks against it, an elimination form takes it when it agrees
with what was synthesized and otherwise keeps its own type. An `extend` takes its
target's representative from the annotation's domain and its fields' row from the
codomain. Checking prefers a present representative annotation and then converts
to the requested type. Missing annotations retain expected-directed behavior.
Eliminations may use annotation.domain as their operand representative; mix uses
domain for the lower operand and codomain for the upper operand. -/
public import Obend.Core.Check
import all Obend.Core.Check

@[expose] public section
namespace Obend.Core.Bidirectional
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
set_option autoImplicit false

/-- Why a term was refused, and where: `path` is the source position (the same
addressing as `Annotations`). Each names the rule that failed and, where it is a
missing piece, what to add. -/
inductive CheckRefusal where
  | unboundVariable (path : List Nat) (index : Nat)
  | missingLambdaAnnotation (path : List Nat)
  /-- An injection, `perform` or `done` in synthesis position needs its annotation. -/
  | missingAnnotation (path : List Nat)
  | emptyCaseInSynthMode (path : List Nat)
  | typeMismatch (path : List Nat) (expected actual : Ty)
  /-- The type's weak-head form is not the shape the rule eliminates or introduces. -/
  | shapeMismatch (path : List Nat) (wanted : String) (actual : Ty)
  | unknownLabel (path : List Nat) (name : String) (row : Ty)
  | duplicateLabels (path : List Nat)
  /-- Hypothesis `index` is used `count` times, more than its quantity `quantity` allows (`erased`:
  never; `affine`, `linear`: at most once). -/
  | binderOverused (path : List Nat) (index : Nat) (quantity : Quantity) (count : Nat)
  /-- The `linear` parameter of the lambda at `path` is not used: exact discharge fails at its binder. -/
  | linearBinderUnused (path : List Nat)
  /-- The argument at `path` uses the `linear` hypothesis `index`, and the parameter it is passed to is
  `quantity`, which may drop or share it. -/
  | linearArgumentDropped (path : List Nat) (index : Nat) (quantity : Quantity)
  /-- The branches of the join at `path` use the `linear` hypothesis `index` unequally: one path
  drops it, or uses it more often than another. -/
  | linearBranchesDisagree (path : List Nat) (index : Nat)
  /-- The projection at `path` drops the siblings of what it keeps, and its target uses the `linear`
  hypothesis `index`. -/
  | linearProjected (path : List Nat) (index : Nat)
  /-- The metadata of the specification at `path` uses the `linear` hypothesis `index`; applying the
  specification calls its extension and discards the metadata. -/
  | linearMetadata (path : List Nat) (index : Nat)
  /-- The target of the extension at `path` uses the `linear` hypothesis `index`; the extension may
  overwrite the field that holds it. -/
  | linearOverwritten (path : List Nat) (index : Nat)
  /-- The arm at `path` binds a `linear` payload (its scrutinee uses a `linear` hypothesis, or the
  case's annotation says `linear`) and does not use it. -/
  | linearScrutinee (path : List Nat)
  | capturesNotShareable (path : List Nat)
  /-- The destructor at `path` does not name the field `name` of its target: it would drop it. -/
  | fieldDropped (path : List Nat) (name : String)
  | notShareable (path : List Nat) (type : Ty)
  | activityMisplaced (path : List Nat) (type : Ty)
  | invalidContext (path : List Nat)
  | invalidAssumptions
  /-- The hole `hole` at `path` is not declared (`Assumptions.holes`). -/
  | undeclaredHole (path : List Nat) (hole : Nat)
  /-- The hole `hole` at `path` is declared over `declared` variables and given `supplied` arguments. -/
  | holeArity (path : List Nat) (hole : Nat) (declared supplied : Nat)
  deriving Repr, DecidableEq

/-- A Boolean premise as evidence, or the named refusal. -/
def need (premise : Bool) (refusal : CheckRefusal) : Except CheckRefusal (PLift (premise = true)) :=
  if h : premise = true then .ok ⟨h⟩ else .error refusal

theorem need_ok {premise : Bool} {refusal : CheckRefusal} (h : premise = true) :
    need premise refusal = .ok ⟨h⟩ := by simp [need, h]

/-- The first binder a usage vector uses more often than its quantity allows, with that quantity. -/
def firstOveruse (context : Context) (uses : Uses) : Option (Nat × Quantity × Nat) :=
  ((context.zip uses).zipIdx.find? (fun entry => !safeQuantity entry.1.1.quantity entry.1.2)).map
    (fun entry => (entry.2, entry.1.1.quantity, entry.1.2))

/-- Why `safeUses` failed: the first overused binder, named with its own quantity. -/
def overuse (path : List Nat) (context : Context) (uses : Uses) : CheckRefusal :=
  match firstOveruse context uses with
  | some (index, quantity, count) => .binderOverused path index quantity count
  | none => .invalidContext path

/-- The first `linear` hypothesis a usage vector uses. -/
def firstLinearUse (context : Context) (uses : Uses) : Option Nat :=
  ((context.zip uses).zipIdx.find? (fun entry => entry.1.2 != 0 && entry.1.1.quantity == .linear)).map
    (fun entry => entry.2)

/-- The first `linear` hypothesis two branches use unequally (`branchesAgree` fails there). -/
def firstDisagreement : Context → Uses → Uses → Nat → Option Nat
  | binding :: context, first :: firsts, second :: seconds, index =>
      if binding.quantity.agrees first second then firstDisagreement context firsts seconds (index + 1)
      else some index
  | _, _, _, _ => none

def disagreement (path : List Nat) (context : Context) (first second : Uses) : CheckRefusal :=
  .linearBranchesDisagree path ((firstDisagreement context first second 0).getD 0)

def projected (path : List Nat) (context : Context) (uses : Uses) : CheckRefusal :=
  .linearProjected path ((firstLinearUse context uses).getD 0)

/-- A refusal naming the first `linear` hypothesis `uses` uses (where `linearFree` failed). -/
def linearRefusal (refusal : List Nat → Nat → CheckRefusal) (path : List Nat) (context : Context)
    (uses : Uses) : CheckRefusal :=
  refusal path ((firstLinearUse context uses).getD 0)

/-- Why `argumentAllowed` failed, clause by clause in its own order: an activity passed as an argument
(`activityMisplaced`); a `linear` hypothesis passed to a non-`linear` parameter
(`linearArgumentDropped`); for an `unrestricted` parameter, a type that is not shareable
(`notShareable`) or captures that are not reusable (`capturesNotShareable`). -/
def argumentRefusal (assumptions : Assumptions) (path : List Nat) (quantity : Quantity) (context : Context)
    (type : Ty) (uses : Uses) : CheckRefusal :=
  if type.isComputation then .activityMisplaced path type
  else match quantity, firstLinearUse context uses with
    | .linear, _ | _, none =>
      if type.shareableUnder assumptions.shareableVariables then .capturesNotShareable path
      else .notShareable path type
    | _, some index => .linearArgumentDropped path index quantity

/-- A type with its declared alias head unfolded as far as it goes: the canonical
point of its orbit after as many steps as there are bounds. -/
def whnf (assumptions : Assumptions) (type : Ty) : Ty :=
  assumptions.chase assumptions.bounds.length type.canonical

theorem unfoldHead_isCanonical (assumptions : Assumptions) {type : Ty} (canonical : type.isCanonical) :
    (assumptions.unfoldHead type).isCanonical := by
  cases type with
  | «variable» index =>
    simp only [Assumptions.unfoldHead]
    split
    · split
      · trivial
      · exact Ty.canonical_isCanonical _
    · trivial
  | _ => exact canonical

theorem chase_isCanonical (assumptions : Assumptions) : ∀ (k : Nat) {type : Ty}, type.isCanonical →
    (assumptions.chase k type).isCanonical
  | 0, _, h => h
  | k + 1, _, h => chase_isCanonical assumptions k (unfoldHead_isCanonical assumptions h)

theorem whnf_canonical (assumptions : Assumptions) (type : Ty) :
    (whnf assumptions type).canonical = whnf assumptions type :=
  Ty.canonical_of_isCanonical (chase_isCanonical assumptions _ (Ty.canonical_isCanonical type))

/-- Every type agrees with its weak-head form. -/
theorem sameType_whnf (assumptions : Assumptions) (type : Ty) :
    sameType assumptions type (whnf assumptions type) = true :=
  sameType_trans (sameType_canonical assumptions type)
    (EquiRecursiveAgreement.agrees_chase assumptions assumptions.bounds.length type.canonical)

theorem whnf_sameType (assumptions : Assumptions) (type : Ty) :
    sameType assumptions (whnf assumptions type) type = true :=
  sameType_symm (sameType_whnf assumptions type)

/-- With a local annotation, the parent selected an exact raw rule
representative. Do not canonicalize its payloads or binder contexts. Unannotated
calls retain the original weak-head fallback. -/
def representativeHead (assumptions : Assumptions) (annotations : Annotations)
    (path : List Nat) (type : Ty) : Ty :=
  if (annotations path).isSome then type else whnf assumptions type

theorem sameType_representativeHead (assumptions : Assumptions) (annotations : Annotations)
    (path : List Nat) (type : Ty) :
    sameType assumptions type (representativeHead assumptions annotations path type) = true := by
  unfold representativeHead
  split
  · exact sameType_refl assumptions type
  · exact sameType_whnf assumptions type

theorem representativeHead_sameType (assumptions : Assumptions) (annotations : Annotations)
    (path : List Nat) (type : Ty) :
    sameType assumptions (representativeHead assumptions annotations path type) type = true :=
  sameType_symm (sameType_representativeHead assumptions annotations path type)

/-- The sum an injection is typed at. A local annotation selects its raw representative
when that is a sum; an annotation naming the sum through an alias (the front end's
convention for a recursive sum) is unfolded to its weak head, and the injection is then
converted back to the alias, so the synthesized type stays the name the annotation gave. -/
def injectionHead (assumptions : Assumptions) (annotations : Annotations)
    (path : List Nat) (type : Ty) : Ty :=
  match representativeHead assumptions annotations path type with
  | .variant row => .variant row
  | other => whnf assumptions other

theorem injectionHead_sameType (assumptions : Assumptions) (annotations : Annotations)
    (path : List Nat) (type : Ty) :
    sameType assumptions (injectionHead assumptions annotations path type) type = true := by
  unfold injectionHead
  split
  · rename_i row shape
    rw [← shape]; exact representativeHead_sameType assumptions annotations path type
  · exact sameType_trans (whnf_sameType assumptions _) (representativeHead_sameType assumptions annotations path type)

/-- The first entry of a label in a row's explicit fields. -/
def rowMember : Ty → String → Option Ty
  | .field prior member tail, name => if prior = name then some member else rowMember tail name
  | _, _ => none

/-- Every arm's payload, as `rowMember` finds it, is shareable: what an `unrestricted` payload needs. -/
def armsShareable (assumptions : Assumptions) (row : Ty) (arms : List (String × Term)) : Bool :=
  arms.all fun arm => match rowMember row arm.1 with
    | some payload => payload.shareableUnder assumptions.shareableVariables
    | none => true

/-- Any arm whose resolved payload bears custody forces a `linear` payload binding (`mustBeLinear`). -/
def armsCustody (row : Ty) (arms : List (String × Term)) : Bool :=
  arms.any fun arm => match rowMember row arm.1 with
    | some payload => payload.bearsCustody
    | none => false

/-- The case's payload quantity: its annotation's, else `caseQuantity`. -/
def caseQuantityAt (assumptions : Assumptions) (annotations : Annotations) (path : List Nat) (context : Context)
    (uses : Uses) (row : Ty) (arms : List (String × Term)) : Quantity :=
  match annotations path with
  | some annotation => annotation.parameter
  | none => caseQuantity assumptions context uses (armsShareable assumptions row arms) (armsCustody row arms)

theorem caseQuantityAt_some {assumptions : Assumptions} {annotations : Annotations} {path : List Nat}
    {annotation : LambdaAnnotation} (h : annotations path = some annotation) (context : Context) (uses : Uses)
    (row : Ty) (arms : List (String × Term)) :
    caseQuantityAt assumptions annotations path context uses row arms = annotation.parameter := by
  simp [caseQuantityAt, h]

/-- Why `caseAllowed` failed for an annotated quantity: the scrutinee's `linear` hypothesis would be
bound at `quantity`, or its captures are not reusable for an `unrestricted` payload. -/
def caseRefusal (path : List Nat) (quantity : Quantity) (context : Context) (uses : Uses) : CheckRefusal :=
  match quantity, firstLinearUse context uses with
  | .linear, _ | _, none => .capturesNotShareable path
  | _, some index => .linearArgumentDropped path index quantity

/-- A destructor's parameters checked against its target's row, name by name (`SplitSpine`): the
function's type is read as given (its annotation is the parent's codomain), so the walk is exact. -/
def checkSpine (assumptions : Assumptions) (context : Context) (path : List Nat) (uses : Uses) (row : Ty) :
    (names : List String) → (functionType : Ty) →
      Except CheckRefusal ((result : Ty) ×' SplitSpine assumptions context uses row names functionType result)
  | [], functionType => pure ⟨functionType, rfl⟩
  | name :: names, functionType =>
    match shape : callable functionType with
    | .arrow reuse quantity member codomain =>
      match found : lookupV assumptions.bounds [] row name with
      | some actual =>
        if agrees : sameType assumptions actual member = true then do
          let ⟨hc⟩ ← need (!member.isComputation) (.activityMisplaced (path ++ [1]) member)
          let ⟨ha⟩ ← need (caseAllowed assumptions quantity context uses) (caseRefusal path quantity context uses)
          let ⟨hu⟩ ← need (validContext assumptions.shareableVariables [⟨member, quantity⟩])
            (.notShareable (path ++ [1]) member)
          let rest ← checkSpine assumptions context path uses row names codomain
          pure ⟨rest.1, reuse, quantity, member, codomain, shape,
            (by obtain ⟨fuel, l⟩ := (lookupV_iff _ _ _ _).1 found; exact ⟨fuel, actual, l, agrees⟩),
            by simpa using hc, ha, hu, rest.2⟩
        else throw (.typeMismatch (path ++ [1]) member actual)
      | none => throw (.unknownLabel (path ++ [0]) name row)
    | _ => throw (.shapeMismatch (path ++ [1]) "function" functionType)

/-- The first label on the row's spine a destructor does not name (`""` if the spine is not closed). -/
def uncoveredLabel (row : Ty) (names : List String) : String :=
  ((spineLabels row).find? fun name => !names.contains name).getD ""

/-- A synthesized type. -/
abbrev Synth (assumptions : Assumptions) (context : Context) (term : Term) := Inferred assumptions context term

/-- A term checked against a given type. -/
structure Against (assumptions : Assumptions) (context : Context) (term : Term) (expected : Ty) where
  uses : Uses
  derivation : PartialTyping assumptions context term expected uses

/-- Arms checked against one result type, with the closed row they build, at one payload quantity,
which the answer records (`quantity`): the case then checks that its scrutinee allows it. -/
structure ArmsAgainst (assumptions : Assumptions) (context : Context) (arms : List (String × Term)) (result : Ty) where
  row : Ty
  uses : Uses
  quantity : Quantity
  derivation : ArmsTyping assumptions context quantity arms row result uses

/-- Fields checked against a given row, entry by entry. -/
structure FieldsAgainst (assumptions : Assumptions) (context : Context) (fields : List (String × Term)) (row : Ty) where
  uses : Uses
  derivation : FieldsTyping assumptions context fields row uses

/-- A hole's arguments checked against its declared context, entry by entry: what
`PartialTyping.hole` asks of them. -/
structure ArgsAgainst (assumptions : Assumptions) (context : Context) (σ : List Term) (Δ : Context) where
  args : List (Term × Binding × Uses)
  terms : σ = args.map (·.1)
  bindings : args.map (·.2.1) = Δ
  typed : ∀ arg ∈ args, PartialTyping assumptions context arg.1 arg.2.1.type arg.2.2
  allowed : ∀ arg ∈ args, argumentAllowed assumptions arg.2.1.quantity context arg.2.1.type arg.2.2 = true

/-- What a call is asked: synthesize, or check against a type. -/
inductive Mode where
  | synth
  | check (expected : Ty)

/-- The result a mode asks for. -/
abbrev Result (assumptions : Assumptions) (context : Context) (term : Term) : Mode → Type
  | .synth => Synth assumptions context term
  | .check expected => Against assumptions context term expected

/-- Package a checked operand at the exact representative selected by its
parent's annotation. This prevents nominal resource tests from observing an
arbitrary equivalent type chosen by synthesis. -/
def checkedSynth {assumptions : Assumptions} {context : Context} {term : Term} {expected : Ty}
    (checked : Against assumptions context term expected) : Synth assumptions context term :=
  ⟨expected, checked.uses, checked.derivation⟩

/-- An elimination form's synthesized type, or its ascription when the two agree. -/
def ascribe (assumptions : Assumptions) (annotations : Annotations) (path : List Nat) {context : Context}
    {term : Term} (synthesized : Synth assumptions context term) : Synth assumptions context term :=
  match annotations path with
  | some annotation =>
    if agrees : sameType assumptions synthesized.type annotation.codomain = true then
      ⟨annotation.codomain, synthesized.uses, .conversion synthesized.derivation agrees⟩
    else synthesized
  | none => synthesized

/-- An elimination form finishes: ascription in synthesis, the mode switch in checking. -/
def finish (assumptions : Assumptions) (annotations : Annotations) (path : List Nat) {context : Context}
    {term : Term} (synthesized : Synth assumptions context term) :
    (mode : Mode) → Except CheckRefusal (Result assumptions context term mode)
  | .synth => .ok (ascribe assumptions annotations path synthesized)
  | .check expected =>
    if agrees : sameType assumptions synthesized.type expected = true then
      .ok ⟨synthesized.uses, .conversion synthesized.derivation agrees⟩
    else .error (.typeMismatch path expected synthesized.type)

/-- An introduction form finishes: checking as given; in synthesis, its ascription
(the annotation's codomain) is checked, and without one `unannotated` is tried. -/
def introduce (annotations : Annotations) (path : List Nat) {assumptions : Assumptions} {context : Context}
    {term : Term} (against : (expected : Ty) → Except CheckRefusal (Against assumptions context term expected))
    (unannotated : Except CheckRefusal (Synth assumptions context term)) :
    (mode : Mode) → Except CheckRefusal (Result assumptions context term mode)
  | .check expected =>
    match annotations path with
    | none => against expected
    | some annotation => do
      let checked ← against annotation.codomain
      finish assumptions annotations path (checkedSynth checked) (.check expected)
  | .synth =>
    match annotations path with
    | some annotation => (against annotation.codomain).map fun checked =>
        (⟨annotation.codomain, checked.uses, checked.derivation⟩ : Synth assumptions context term)
    | none => unannotated

mutual
/-- Synthesis and checking, by the term's shape. -/
def elaborate (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat) :
    (term : Term) → (mode : Mode) → Except CheckRefusal (Result assumptions context term mode)
  | .hole n σ, mode =>
    match found : assumptions.holes.lookup n with
    | none => throw (.undeclaredHole path n)
    | some decl => do
      let checked ← checkArgs assumptions annotations context path n 0 σ decl.context
      finish assumptions annotations path ⟨decl.type, (checked.args.map (·.2.2)).foldr addUses (zeroUses context),
        .hole found checked.terms checked.bindings checked.typed checked.allowed⟩ mode
  | .bound index, mode =>
    match found : context[index]? with
    | some binding => finish assumptions annotations path ⟨binding.type, variableUses context index, .bound found⟩ mode
    | none => throw (.unboundVariable path index)
  | .nat value, mode => finish assumptions annotations path ⟨.natural, zeroUses context, .natural context value⟩ mode
  | .boolean value, mode =>
    finish assumptions annotations path ⟨.boolean, zeroUses context, .boolean context value⟩ mode
  | .label value, mode =>
    finish assumptions annotations path ⟨literalType value, zeroUses context, .label context value⟩ mode
  | .lam body, mode =>
    let withAnnotation (annotation : LambdaAnnotation) : Except CheckRefusal (Against assumptions context (.lam body)
        (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain)) := do
      let binder : Binding := ⟨annotation.domain, annotation.parameter⟩
      let checked ← elaborate assumptions annotations (binder :: context) (path ++ [0]) body (.check annotation.codomain)
      let ⟨hs⟩ ← need (safeUses (binder :: context) checked.uses) (overuse path (binder :: context) checked.uses)
      let ⟨hv⟩ ← need (validContext assumptions.shareableVariables (binder :: context)) (.invalidContext path)
      let ⟨hc⟩ ← need (reusableAllowed assumptions annotation.reuse context checked.uses.tail)
        (.capturesNotShareable path)
      let ⟨hf⟩ ← need (annotation.parameter.fits (checked.uses.headD 0)) (.linearBinderUnused path)
      pure ⟨checked.uses.tail, .lambda checked.derivation hs hv hc hf⟩
    match mode with
    | .synth =>
      match annotations path with
      | none => throw (.missingLambdaAnnotation path)
      | some annotation => (withAnnotation annotation).map fun checked =>
          (⟨_, checked.uses, checked.derivation⟩ : Synth assumptions context _)
    | .check expected =>
      match annotations path with
      | some annotation => do
        let typed ← withAnnotation annotation
        finish assumptions annotations path (checkedSynth typed) (.check expected)
      | none =>
        match shape : representativeHead assumptions annotations path expected with
        | .arrow reuse parameter domain codomain => do
          let typed ← withAnnotation ⟨domain, codomain, parameter, reuse⟩
          pure ⟨typed.uses, .conversion typed.derivation (shape ▸ representativeHead_sameType assumptions annotations path expected)⟩
        | _ => throw (.shapeMismatch path "function" expected)
  | .app function argument, mode => do
    let fn ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) function .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) function (.check annotation.domain)).map checkedSynth
    match shape : callable (representativeHead assumptions annotations path fn.type) with
    | .arrow reuse quantity domain codomain =>
      let arg ← elaborate assumptions annotations context (path ++ [1]) argument (.check domain)
      let ⟨ha⟩ ← need (argumentAllowed assumptions quantity context domain arg.uses)
        (argumentRefusal assumptions (path ++ [1]) quantity context domain arg.uses)
      finish assumptions annotations path ⟨codomain, addUses fn.uses arg.uses,
        .application (.conversion fn.derivation (sameType_representativeHead _ annotations path _)) arg.derivation shape rfl ha⟩ mode
    | _ => throw (.shapeMismatch (path ++ [0]) "function" fn.type)
  | .get target name, mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) target .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) target (.check annotation.domain)).map checkedSynth
    match found : lookupV assumptions.bounds [] value.type name with
    | some member => do
      let ⟨hl⟩ ← need (linearFree context value.uses) (projected path context value.uses)
      finish assumptions annotations path ⟨member, value.uses,
        (by obtain ⟨fuel, h⟩ := (lookupV_iff _ _ _ _).1 found; exact .get value.derivation h hl)⟩ mode
    | none => throw (.unknownLabel (path ++ [0]) name value.type)
  | .split target names function, mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) target .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) target (.check annotation.domain)).map checkedSynth
    let fn ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [1]) function .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [1]) function (.check annotation.codomain)).map checkedSynth
    let row := representativeHead assumptions annotations path value.type
    let ⟨hn⟩ ← need (decide names.Nodup) (.duplicateLabels path)
    let ⟨hc⟩ ← need (SplitCovers row names) (.fieldDropped path (uncoveredLabel row names))
    let spine ← checkSpine assumptions context path value.uses row names fn.type
    finish assumptions annotations path ⟨spine.1, addUses value.uses fn.uses,
      .split (.conversion value.derivation (sameType_representativeHead assumptions annotations path value.type))
        fn.derivation (of_decide_eq_true hn) hc spine.2⟩ mode
  | .reflect target, mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) target .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) target (.check annotation.domain)).map checkedSynth
    match shape : representativeHead assumptions annotations path value.type with
    | .prototype specType targetType => do
      let ⟨hl⟩ ← need (linearFree context value.uses) (projected path context value.uses)
      finish assumptions annotations path ⟨specType, value.uses,
        .reflect (PartialTyping.conversion (expected := .prototype specType targetType) value.derivation
          (shape ▸ sameType_representativeHead assumptions annotations path value.type)) hl⟩ mode
    | _ => throw (.shapeMismatch (path ++ [0]) "prototype" value.type)
  | .metadata target, mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) target .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) target (.check annotation.domain)).map checkedSynth
    match shape : representativeHead assumptions annotations path value.type with
    | .specification metadataType extensionType => do
      let ⟨hl⟩ ← need (linearFree context value.uses) (projected path context value.uses)
      finish assumptions annotations path ⟨metadataType, value.uses,
        .metadata (PartialTyping.conversion (expected := .specification metadataType extensionType) value.derivation
          (shape ▸ sameType_representativeHead assumptions annotations path value.type)) hl⟩ mode
    | _ => throw (.shapeMismatch (path ++ [0]) "specification" value.type)
  | .project target, mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) target .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) target (.check annotation.domain)).map checkedSynth
    match shape : representativeHead assumptions annotations path value.type with
    | .prototype specType targetType => do
      let ⟨hl⟩ ← need (linearFree context value.uses) (projected path context value.uses)
      finish assumptions annotations path ⟨targetType, value.uses,
        .project (PartialTyping.conversion (expected := .prototype specType targetType) value.derivation
          (shape ▸ sameType_representativeHead assumptions annotations path value.type)) hl⟩ mode
    | _ => throw (.shapeMismatch (path ++ [0]) "prototype" value.type)
  | .binary primitive left right, mode => do
    let l ← elaborate assumptions annotations context (path ++ [0]) left (.check (primitiveTypes primitive).1)
    let r ← elaborate assumptions annotations context (path ++ [1]) right (.check (primitiveTypes primitive).1)
    finish assumptions annotations path ⟨(primitiveTypes primitive).2, addUses l.uses r.uses,
      .binary (Prod.eta _) l.derivation r.derivation⟩ mode
  | .mix lower upper, mode => do
    let first ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) lower .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) lower (.check annotation.domain)).map checkedSynth
    let second ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [1]) upper .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [1]) upper (.check annotation.codomain)).map checkedSynth
    match hl : callable (representativeHead assumptions annotations path first.type), hu : callable (representativeHead assumptions annotations path second.type) with
    | .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle),
      .arrow .reusable .unrestricted self' (.arrow .reusable .unrestricted middle' provided) =>
      if hs : self' = self then
        if hm : middle' = middle then do
          let ⟨captures⟩ ← need (reusableCaptures assumptions.shareableVariables context (addUses first.uses second.uses))
            (.capturesNotShareable path)
          let ⟨shareSelf⟩ ← need (self.shareableUnder assumptions.shareableVariables) (.notShareable path self)
          let ⟨shareInherited⟩ ← need (inherited.shareableUnder assumptions.shareableVariables)
            (.notShareable path inherited)
          let ⟨shareMiddle⟩ ← need (middle.shareableUnder assumptions.shareableVariables) (.notShareable path middle)
          finish assumptions annotations path
            ⟨.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided),
              addUses first.uses second.uses,
              .mix (.conversion first.derivation (sameType_representativeHead _ annotations path _)) (.conversion second.derivation (sameType_representativeHead _ annotations path _))
                hl (by rw [hu, hs, hm]) captures shareSelf shareInherited shareMiddle⟩ mode
        else throw (.typeMismatch (path ++ [1]) middle middle')
      else throw (.typeMismatch (path ++ [1]) self self')
    | _, _ => throw (.shapeMismatch path "mixable pair" first.type)
  | .fix spec inheritedTerm, mode => do
    let code ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) spec .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) spec (.check annotation.domain)).map checkedSynth
    match shape : callable (representativeHead assumptions annotations path code.type) with
    | .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited output) =>
      if ho : output = target then do
        let base ← elaborate assumptions annotations context (path ++ [1]) inheritedTerm (.check inherited)
        let ⟨hs⟩ ← need (target.shareableUnder assumptions.shareableVariables) (.notShareable path target)
        let ⟨ha⟩ ← need (argumentAllowed assumptions .unrestricted context inherited base.uses)
          (.notShareable (path ++ [1]) inherited)
        let ⟨hc⟩ ← need (reusableCaptures assumptions.shareableVariables context code.uses)
          (.capturesNotShareable (path ++ [0]))
        finish assumptions annotations path ⟨target, addUses code.uses base.uses,
          .fix (.conversion code.derivation (sameType_representativeHead _ annotations path _)) (by rw [shape, ho]) base.derivation hs ha hc⟩ mode
      else throw (.typeMismatch (path ++ [0]) target output)
    | _ => throw (.shapeMismatch (path ++ [0]) "fixable specification" code.type)
  | .inject tag payload, mode =>
    introduce annotations path (fun expected =>
      match shape : injectionHead assumptions annotations path expected with
      | .variant row =>
        match found : lookupV assumptions.bounds [] row tag with
        | some payloadType => do
          let value ← elaborate assumptions annotations context (path ++ [0]) payload (.check payloadType)
          let ⟨hp⟩ ← need (!payloadType.isComputation) (.activityMisplaced (path ++ [0]) payloadType)
          pure ⟨value.uses, .conversion
            (by obtain ⟨fuel, h⟩ := (lookupV_iff _ _ _ _).1 found
                exact .inject value.derivation h (by simpa using hp))
            (shape ▸ injectionHead_sameType assumptions annotations path expected)⟩
        | none => throw (.unknownLabel path tag row)
      | _ => throw (.shapeMismatch path "sum" expected))
      (throw (.missingAnnotation path)) mode
  | .perform plan, mode =>
    let against (expected : Ty) : Except CheckRefusal (Against assumptions context (.perform plan) expected) :=
      match shape : representativeHead assumptions annotations path expected with
      | .computation planType response result =>
        if same : result = response then do
          let value ← elaborate assumptions annotations context (path ++ [0]) plan (.check planType)
          let ⟨hp⟩ ← need planType.isPlan (.shapeMismatch path "plan" planType)
          let ⟨hr⟩ ← need response.isData (.shapeMismatch path "data" response)
          pure ⟨value.uses, .conversion (.perform value.derivation hp hr)
            (by have h := representativeHead_sameType assumptions annotations path expected; rw [shape, same] at h; exact h)⟩
        else throw (.typeMismatch path response result)
      | _ => throw (.shapeMismatch path "activity" expected)
    match mode with
    | .check expected =>
      match annotations path with
      | none => against expected
      | some annotation => do
        let typed ← against (.computation annotation.domain annotation.codomain annotation.codomain)
        finish assumptions annotations path (checkedSynth typed) (.check expected)
    | .synth =>
      match annotations path with
      | some annotation => (against (.computation annotation.domain annotation.codomain annotation.codomain)).map
          fun checked => ⟨_, checked.uses, checked.derivation⟩
      | none => throw (.missingAnnotation path)
  | .done value, mode =>
    let synthesized : Except CheckRefusal (Synth assumptions context (.done value)) :=
      match annotations path with
      | some annotation =>
        match annotation.codomain with
        | .computation planType response result => do
          let inner ← elaborate assumptions annotations context (path ++ [0]) value (.check result)
          let ⟨hn⟩ ← need (!result.isComputation) (.activityMisplaced (path ++ [0]) result)
          pure ⟨.computation planType response result, inner.uses, .done inner.derivation (by simpa using hn)⟩
        | _ => do
          let inner ← elaborate assumptions annotations context (path ++ [0]) value .synth
          let ⟨hn⟩ ← need (!inner.type.isComputation) (.activityMisplaced (path ++ [0]) inner.type)
          pure ⟨.computation annotation.domain annotation.codomain inner.type, inner.uses,
            .done inner.derivation (by simpa using hn)⟩
      | none => throw (.missingAnnotation path)
    match mode with
    | .synth => synthesized
    | .check expected =>
      match annotations path with
      | some _ => do
        let typed ← synthesized
        finish assumptions annotations path typed (.check expected)
      | none =>
        match shape : representativeHead assumptions annotations path expected with
        | .computation planType response result => do
          let inner ← elaborate assumptions annotations context (path ++ [0]) value (.check result)
          let ⟨hn⟩ ← need (!result.isComputation) (.activityMisplaced (path ++ [0]) result)
          pure ⟨inner.uses, .conversion (.done inner.derivation (by simpa using hn))
            (shape ▸ representativeHead_sameType assumptions annotations path expected)⟩
        | _ => throw (.shapeMismatch path "activity" expected)
  | .record fields, mode =>
    introduce annotations path (fun expected => do
      -- a record names each field once (`PartialTyping.record`)
      let ⟨hd⟩ ← need (labelsDistinct fields) (.duplicateLabels path)
      if (annotations path).isSome then do
        let members ← checkFields assumptions annotations context path 0 fields expected
        pure ⟨members.uses, .record members.derivation hd⟩
      else do
        let members ← checkFieldsByLabel assumptions annotations context path 0 (representativeHead assumptions annotations path expected) fields
        let ⟨hc⟩ ← need (sameType assumptions members.type expected) (.typeMismatch path expected members.type)
        pure ⟨members.uses, .conversion (.record members.derivation hd) hc⟩)
      (do
        let ⟨hd⟩ ← need (labelsDistinct fields) (.duplicateLabels path)
        let row ← synthFields assumptions annotations context path 0 fields
        pure ⟨row.type, row.uses, .record row.derivation hd⟩) mode
  | .specification metadata extension, mode =>
    introduce annotations path (fun expected =>
      match shape : representativeHead assumptions annotations path expected with
      | .specification metadataType extensionType => do
        let m ← elaborate assumptions annotations context (path ++ [0]) metadata (.check metadataType)
        let e ← elaborate assumptions annotations context (path ++ [1]) extension (.check extensionType)
        let ⟨hm⟩ ← need (!metadataType.isComputation) (.activityMisplaced (path ++ [0]) metadataType)
        let ⟨he⟩ ← need (!extensionType.isComputation) (.activityMisplaced (path ++ [1]) extensionType)
        let ⟨hl⟩ ← need (linearFree context m.uses) (linearRefusal .linearMetadata path context m.uses)
        pure ⟨addUses m.uses e.uses, .conversion
          (.specification m.derivation e.derivation (by simpa using hm) (by simpa using he) hl)
          (shape ▸ representativeHead_sameType assumptions annotations path expected)⟩
      | _ => throw (.shapeMismatch path "specification" expected))
      (do
        let m ← elaborate assumptions annotations context (path ++ [0]) metadata .synth
        let e ← elaborate assumptions annotations context (path ++ [1]) extension .synth
        let ⟨hm⟩ ← need (!m.type.isComputation) (.activityMisplaced (path ++ [0]) m.type)
        let ⟨he⟩ ← need (!e.type.isComputation) (.activityMisplaced (path ++ [1]) e.type)
        let ⟨hl⟩ ← need (linearFree context m.uses) (linearRefusal .linearMetadata path context m.uses)
        pure ⟨.specification m.type e.type, addUses m.uses e.uses,
          .specification m.derivation e.derivation (by simpa using hm) (by simpa using he) hl⟩) mode
  | .prototype spec target, mode =>
    introduce annotations path (fun expected =>
      match shape : representativeHead assumptions annotations path expected with
      | .prototype specType targetType => do
        let s ← elaborate assumptions annotations context (path ++ [0]) spec (.check specType)
        let t ← elaborate assumptions annotations context (path ++ [1]) target (.check targetType)
        let ⟨hs⟩ ← need (!specType.isComputation) (.activityMisplaced (path ++ [0]) specType)
        let ⟨ht⟩ ← need (!targetType.isComputation) (.activityMisplaced (path ++ [1]) targetType)
        pure ⟨addUses s.uses t.uses, .conversion
          (.prototype s.derivation t.derivation (by simpa using hs) (by simpa using ht))
          (shape ▸ representativeHead_sameType assumptions annotations path expected)⟩
      | _ => throw (.shapeMismatch path "prototype" expected))
      (do
        let s ← elaborate assumptions annotations context (path ++ [0]) spec .synth
        let t ← elaborate assumptions annotations context (path ++ [1]) target .synth
        let ⟨hs⟩ ← need (!s.type.isComputation) (.activityMisplaced (path ++ [0]) s.type)
        let ⟨ht⟩ ← need (!t.type.isComputation) (.activityMisplaced (path ++ [1]) t.type)
        pure ⟨.prototype s.type t.type, addUses s.uses t.uses,
          .prototype s.derivation t.derivation (by simpa using hs) (by simpa using ht)⟩) mode
  | .extend target fields, mode => do
    let prior ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) target .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) target (.check annotation.domain)).map checkedSynth
    let synthesized : Except CheckRefusal (Synth assumptions context (.extend target fields)) :=
      match annotations path with
      | some annotation => do
        let ⟨agrees⟩ ← need (sameType assumptions prior.type annotation.domain)
          (.typeMismatch (path ++ [0]) annotation.domain prior.type)
        let ⟨isRow⟩ ← need (isRowV assumptions.bounds [] annotation.domain)
          (.shapeMismatch (path ++ [0]) "row" annotation.domain)
        let members ← checkFields assumptions annotations context (path ++ [1]) 0 fields annotation.codomain
        let ⟨hd⟩ ← need (labelsDistinct fields) (.duplicateLabels (path ++ [1]))
        let ⟨hl⟩ ← need (linearFree context prior.uses) (linearRefusal .linearOverwritten path context prior.uses)
        pure ⟨overlay annotation.codomain annotation.domain, addUses prior.uses members.uses,
          (by obtain ⟨fuel, h⟩ := (isRowV_iff _ _).1 isRow
              exact .extend (.conversion prior.derivation agrees) members.derivation hd h hl)⟩
      | none => do
        let ⟨isRow⟩ ← need (isRowV assumptions.bounds [] prior.type) (.shapeMismatch (path ++ [0]) "row" prior.type)
        let members ← synthFields assumptions annotations context (path ++ [1]) 0 fields
        let ⟨hd⟩ ← need (labelsDistinct fields) (.duplicateLabels (path ++ [1]))
        let ⟨hl⟩ ← need (linearFree context prior.uses) (linearRefusal .linearOverwritten path context prior.uses)
        pure ⟨overlay members.type prior.type, addUses prior.uses members.uses,
          (by obtain ⟨fuel, h⟩ := (isRowV_iff _ _).1 isRow
              exact .extend prior.derivation members.derivation hd h hl)⟩
    let typed ← synthesized
    match (dependent := true) mode with
    | .synth => pure typed
    | .check expected =>
      if agrees : sameType assumptions typed.type expected = true then
        pure ⟨typed.uses, .conversion typed.derivation agrees⟩
      else throw (.typeMismatch path expected typed.type)
  | .ifBool condition whenTrue whenFalse, mode =>
    introduce annotations path (fun expected => do
      let c ← elaborate assumptions annotations context (path ++ [0]) condition (.check .boolean)
      let t ← elaborate assumptions annotations context (path ++ [1]) whenTrue (.check expected)
      let f ← elaborate assumptions annotations context (path ++ [2]) whenFalse (.check expected)
      let ⟨hj⟩ ← need (branchesAgree context t.uses f.uses) (disagreement path context t.uses f.uses)
      pure ⟨addUses c.uses (joinUses t.uses f.uses), .ifBool c.derivation t.derivation f.derivation hj⟩)
      (do
        let c ← elaborate assumptions annotations context (path ++ [0]) condition (.check .boolean)
        let t ← elaborate assumptions annotations context (path ++ [1]) whenTrue .synth
        let f ← elaborate assumptions annotations context (path ++ [2]) whenFalse (.check t.type)
        let ⟨hj⟩ ← need (branchesAgree context t.uses f.uses) (disagreement path context t.uses f.uses)
        pure ⟨t.type, addUses c.uses (joinUses t.uses f.uses), .ifBool c.derivation t.derivation f.derivation hj⟩) mode
  | .ifZero value zero successor, mode =>
    let successorContext : Context := ⟨.natural, .unrestricted⟩ :: context
    introduce annotations path (fun expected => do
      let v ← elaborate assumptions annotations context (path ++ [0]) value (.check .natural)
      let z ← elaborate assumptions annotations context (path ++ [1]) zero (.check expected)
      let s ← elaborate assumptions annotations successorContext (path ++ [2]) successor (.check expected)
      let ⟨hu⟩ ← need (safeUses successorContext s.uses) (overuse (path ++ [2]) successorContext s.uses)
      let ⟨hj⟩ ← need (branchesAgree context z.uses s.uses.tail) (disagreement path context z.uses s.uses.tail)
      pure ⟨addUses v.uses (joinUses z.uses s.uses.tail), .ifZero v.derivation z.derivation s.derivation hu hj⟩)
      (do
        let v ← elaborate assumptions annotations context (path ++ [0]) value (.check .natural)
        let z ← elaborate assumptions annotations context (path ++ [1]) zero .synth
        let s ← elaborate assumptions annotations successorContext (path ++ [2]) successor (.check z.type)
        let ⟨hu⟩ ← need (safeUses successorContext s.uses) (overuse (path ++ [2]) successorContext s.uses)
        let ⟨hj⟩ ← need (branchesAgree context z.uses s.uses.tail) (disagreement path context z.uses s.uses.tail)
        pure ⟨z.type, addUses v.uses (joinUses z.uses s.uses.tail), .ifZero v.derivation z.derivation s.derivation hu hj⟩)
      mode
  | .case scrutinee [], mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) scrutinee .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) scrutinee (.check annotation.domain)).map checkedSynth
    let against (expected : Ty) : Except CheckRefusal (Against assumptions context (.case scrutinee []) expected) :=
      match representativeHead assumptions annotations path value.type with
      | .variant row => do
        let typed ← checkArms assumptions annotations context
          (caseQuantityAt assumptions annotations path context value.uses row []) (path ++ [1]) 0 row expected []
        let ⟨hq⟩ ← need (caseAllowed assumptions typed.quantity context value.uses)
          (caseRefusal path typed.quantity context value.uses)
        let ⟨hc⟩ ← need (sameType assumptions value.type (.variant typed.row))
          (.typeMismatch (path ++ [0]) (.variant typed.row) value.type)
        pure ⟨addUses value.uses typed.uses, .case (.conversion value.derivation hc) typed.derivation rfl hq⟩
      | .computation planType response (.variant row) =>
        match representativeHead assumptions annotations path expected with
        | .computation _ _ result => do
          let typed ← checkArms assumptions annotations context
            (caseQuantityAt assumptions annotations path context value.uses row []) (path ++ [1]) 0 row
            (.computation planType response result) []
          let ⟨hq⟩ ← need (caseAllowed assumptions typed.quantity context value.uses)
            (caseRefusal path typed.quantity context value.uses)
          let ⟨hc⟩ ← need (sameType assumptions value.type (.computation planType response (.variant typed.row)))
            (.typeMismatch (path ++ [0]) (.computation planType response (.variant typed.row)) value.type)
          let ⟨hn⟩ ← need (!result.isComputation) (.activityMisplaced path result)
          let ⟨he⟩ ← need (sameType assumptions (.computation planType response result) expected)
            (.typeMismatch path expected (.computation planType response result))
          pure ⟨addUses value.uses typed.uses, .conversion
            (.effectCase (.conversion value.derivation hc) typed.derivation (by simpa using hn) rfl hq) he⟩
        | _ => throw (.shapeMismatch path "activity" expected)
      | _ => throw (.shapeMismatch (path ++ [0]) "sum or activity" value.type)
    match (dependent := true) mode with
    | .check expected =>
      match annotations path with
      | none => against expected
      | some annotation => do
        let typed ← against annotation.codomain
        finish assumptions annotations path (checkedSynth typed) (.check expected)
    | .synth =>
      match annotations path with
      | some annotation => (against annotation.codomain).map fun checked =>
          (⟨annotation.codomain, checked.uses, checked.derivation⟩ : Synth assumptions context _)
      | none => throw (.emptyCaseInSynthMode path)
  | .case scrutinee ((name, body) :: rest), mode => do
    let value ← match annotations path with
      | none => elaborate assumptions annotations context (path ++ [0]) scrutinee .synth
      | some annotation =>
        (elaborate assumptions annotations context (path ++ [0]) scrutinee (.check annotation.domain)).map checkedSynth
    let ⟨hd⟩ ← need (labelsDistinct ((name, body) :: rest)) (.duplicateLabels path)
    let against (expected : Ty) :
        Except CheckRefusal (Against assumptions context (.case scrutinee ((name, body) :: rest)) expected) :=
      match representativeHead assumptions annotations path value.type with
      | .variant row => do
        let typed ← checkArms assumptions annotations context
          (caseQuantityAt assumptions annotations path context value.uses row ((name, body) :: rest)) (path ++ [1]) 0 row
          expected ((name, body) :: rest)
        let ⟨hq⟩ ← need (caseAllowed assumptions typed.quantity context value.uses)
          (caseRefusal path typed.quantity context value.uses)
        let ⟨hc⟩ ← need (sameType assumptions value.type (.variant typed.row))
          (.typeMismatch (path ++ [0]) (.variant typed.row) value.type)
        pure ⟨addUses value.uses typed.uses, .case (.conversion value.derivation hc) typed.derivation hd hq⟩
      | .computation planType response (.variant row) =>
        match representativeHead assumptions annotations path expected with
        | .computation _ _ result => do
          let typed ← checkArms assumptions annotations context
            (caseQuantityAt assumptions annotations path context value.uses row ((name, body) :: rest)) (path ++ [1]) 0 row
            (.computation planType response result) ((name, body) :: rest)
          let ⟨hq⟩ ← need (caseAllowed assumptions typed.quantity context value.uses)
            (caseRefusal path typed.quantity context value.uses)
          let ⟨hc⟩ ← need (sameType assumptions value.type (.computation planType response (.variant typed.row)))
            (.typeMismatch (path ++ [0]) (.computation planType response (.variant typed.row)) value.type)
          let ⟨hn⟩ ← need (!result.isComputation) (.activityMisplaced path result)
          let ⟨he⟩ ← need (sameType assumptions (.computation planType response result) expected)
            (.typeMismatch path expected (.computation planType response result))
          pure ⟨addUses value.uses typed.uses, .conversion
            (.effectCase (.conversion value.derivation hc) typed.derivation (by simpa using hn) hd hq) he⟩
        | _ => throw (.shapeMismatch path "activity" expected)
      | _ => throw (.shapeMismatch (path ++ [0]) "sum or activity" value.type)
    match (dependent := true) mode with
    | .check expected =>
      match annotations path with
      | none => against expected
      | some annotation => do
        let typed ← against annotation.codomain
        finish assumptions annotations path (checkedSynth typed) (.check expected)
    | .synth =>
      match annotations path with
      | some annotation => (against annotation.codomain).map fun checked =>
          (⟨annotation.codomain, checked.uses, checked.derivation⟩ : Synth assumptions context _)
      | none =>
        -- without an ascription, the first arm's synthesized type is the result
        let row? : Option Ty := match representativeHead assumptions annotations path value.type with
          | .variant row => some row
          | .computation _ _ (.variant row) => some row
          | _ => none
        match row? with
        | some row =>
          match rowMember row name with
          | some payload => do
            let first ← elaborate assumptions annotations
              (⟨payload, caseQuantityAt assumptions annotations path context value.uses row ((name, body) :: rest)⟩ :: context)
              (path ++ [1] ++ [0]) body .synth
            let checked ← against first.type
            pure ⟨first.type, checked.uses, checked.derivation⟩
          | none => throw (.unknownLabel (path ++ [1]) name row)
        | none => throw (.shapeMismatch (path ++ [0]) "sum or activity" value.type)

/-- Record fields, synthesized; positions `path ++ [index]`, `path ++ [index + 1]`, …. -/
def synthFields (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (index : Nat) : (fields : List (String × Term)) → Except CheckRefusal (InferredFields assumptions context fields)
  | [] => pure ⟨.emptyRow, zeroUses context, .nil context⟩
  | (name, body) :: rest => do
    let first ← elaborate assumptions annotations context (path ++ [index]) body .synth
    let later ← synthFields assumptions annotations context path (index + 1) rest
    let ⟨hc⟩ ← need (!first.type.isComputation) (.activityMisplaced (path ++ [index]) first.type)
    pure ⟨.field name first.type later.type, addUses first.uses later.uses,
      .cons first.derivation later.derivation (by simpa using hc)⟩

/-- Record fields checked against a row in field order. -/
def checkFields (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (index : Nat) : (fields : List (String × Term)) → (row : Ty) → Except CheckRefusal (FieldsAgainst assumptions context fields row)
  | [], .emptyRow => pure ⟨zeroUses context, .nil context⟩
  | [], row => throw (.typeMismatch path row .emptyRow)
  | (name, body) :: rest, .field name' member tail =>
    if hn : name' = name then do
      let first ← elaborate assumptions annotations context (path ++ [index]) body (.check member)
      let later ← checkFields assumptions annotations context path (index + 1) rest tail
      let ⟨hc⟩ ← need (!member.isComputation) (.activityMisplaced (path ++ [index]) member)
      pure ⟨addUses first.uses later.uses, hn ▸ .cons first.derivation later.derivation (by simpa using hc)⟩
    else throw (.unknownLabel (path ++ [index]) name (.field name' member tail))
  | (name, _) :: _, row => throw (.unknownLabel (path ++ [index]) name row)

/-- Record fields checked against a row's members by label (labels distinct). -/
def checkFieldsByLabel (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (index : Nat) (row : Ty) : (fields : List (String × Term)) → Except CheckRefusal (InferredFields assumptions context fields)
  | [] => pure ⟨.emptyRow, zeroUses context, .nil context⟩
  | (name, body) :: rest =>
    match rowMember row name with
    | some member => do
      let first ← elaborate assumptions annotations context (path ++ [index]) body (.check member)
      let later ← checkFieldsByLabel assumptions annotations context path (index + 1) row rest
      let ⟨hc⟩ ← need (!member.isComputation) (.activityMisplaced (path ++ [index]) member)
      pure ⟨.field name member later.type, addUses first.uses later.uses,
        .cons first.derivation later.derivation (by simpa using hc)⟩
    | none => throw (.unknownLabel (path ++ [index]) name row)

/-- A hole's arguments, each checked at its parameter's type and passed as `argumentAllowed`
allows; positions `path ++ [index]`, `path ++ [index + 1]`, …. -/
def checkArgs (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (hole index : Nat) : (σ : List Term) → (Δ : Context) → Except CheckRefusal (ArgsAgainst assumptions context σ Δ)
  | [], [] => pure ⟨[], rfl, rfl, by simp, by simp⟩
  | t :: σ, b :: Δ => do
    let first ← elaborate assumptions annotations context (path ++ [index]) t (.check b.type)
    let ⟨ha⟩ ← need (argumentAllowed assumptions b.quantity context b.type first.uses)
      (argumentRefusal assumptions (path ++ [index]) b.quantity context b.type first.uses)
    let later ← checkArgs assumptions annotations context path hole (index + 1) σ Δ
    pure ⟨(t, b, first.uses) :: later.args, by simp [later.terms], by simp [later.bindings],
      by
        intro arg h; rcases List.mem_cons.mp h with rfl | h
        · exact first.derivation
        · exact later.typed arg h,
      by
        intro arg h; rcases List.mem_cons.mp h with rfl | h
        · exact ha
        · exact later.allowed arg h⟩
  | σ, Δ => throw (.holeArity path hole (index + Δ.length) (index + σ.length))

/-- Arms checked against one result type, each under its label's payload in `row`. -/
def checkArms (assumptions : Assumptions) (annotations : Annotations) (context : Context) (q : Quantity)
    (path : List Nat) (index : Nat) (row result : Ty) :
    (arms : List (String × Term)) → Except CheckRefusal (ArmsAgainst assumptions context arms result)
  | [] => pure ⟨.emptyRow, zeroUses context, q, .nil context q result⟩
  | (name, body) :: rest =>
    match rowMember row name with
    | some payload => do
      let ⟨hs⟩ ← need (validContext assumptions.shareableVariables [⟨payload, q⟩]) (.notShareable (path ++ [index]) payload)
      let first ← elaborate assumptions annotations (⟨payload, q⟩ :: context) (path ++ [index]) body
        (.check result)
      let ⟨hu⟩ ← need (safeUses (⟨payload, q⟩ :: context) first.uses)
        (overuse (path ++ [index]) (⟨payload, q⟩ :: context) first.uses)
      let ⟨hf⟩ ← need (q.fits (first.uses.headD 0)) (.linearScrutinee (path ++ [index]))
      let later ← checkArms assumptions annotations context q path (index + 1) row result rest
      let ⟨hj⟩ ← need (rest.isEmpty || branchesAgree context first.uses.tail later.uses)
        (disagreement (path ++ [index]) context first.uses.tail later.uses)
      if hq : later.quantity = q then
        pure ⟨.field name payload later.row, joinUses first.uses.tail later.uses, q,
          .cons first.derivation hu hs hf (hq ▸ later.derivation) hj⟩
      else throw (.invalidContext (path ++ [index]))
    | none => throw (.unknownLabel (path ++ [index]) name row)
end

/-- Synthesis at a position. -/
abbrev synthAt (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (term : Term) : Except CheckRefusal (Synth assumptions context term) :=
  elaborate assumptions annotations context path term .synth

/-- Checking at a position. -/
abbrev checkAt (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (term : Term) (expected : Ty) : Except CheckRefusal (Against assumptions context term expected) :=
  elaborate assumptions annotations context path term (.check expected)

/-- The top-level check: the term at the expected type, with every top-level premise
`Checked` carries. -/
def checkAgainst (source : AnnotatedTerm) (context : Context) (expected : Ty) :
    Except CheckRefusal (Checked source context) := do
  let result ← checkAt source.assumptions source.annotations context [] source.term expected
  let ⟨hs⟩ ← need (safeUses context result.uses) (overuse [] context result.uses)
  let ⟨hv⟩ ← need (validContext source.assumptions.shareableVariables context) (.invalidContext [])
  let ⟨ha⟩ ← need source.assumptions.valid .invalidAssumptions
  pure ⟨expected, result.uses, result.derivation, hs, hv, ha⟩

/-- The top-level synthesis. -/
def infer (source : AnnotatedTerm) (context : Context) : Except CheckRefusal (Checked source context) := do
  let result ← synthAt source.assumptions source.annotations context [] source.term
  let ⟨hs⟩ ← need (safeUses context result.uses) (overuse [] context result.uses)
  let ⟨hv⟩ ← need (validContext source.assumptions.shareableVariables context) (.invalidContext [])
  let ⟨ha⟩ ← need source.assumptions.valid .invalidAssumptions
  pure ⟨result.type, result.uses, result.derivation, hs, hv, ha⟩

/-- Soundness is the certificate: whatever `checkAgainst` accepts has a derivation at
exactly the expected type. -/
theorem checkAgainst_sound {source : AnnotatedTerm} {context : Context} {expected : Ty}
    {checked : Checked source context} (accepted : checkAgainst source context expected = .ok checked) :
    checked.type = expected ∧
      PartialTyping source.assumptions context source.erase checked.type checked.uses := by
  refine ⟨?_, checked.derivation⟩
  unfold checkAgainst at accepted
  cases hr : checkAt source.assumptions source.annotations context [] source.term expected with
  | error e => simp [hr, bind, Except.bind] at accepted
  | ok r =>
    simp only [hr, bind, Except.bind, need] at accepted
    by_cases h1 : safeUses context r.uses = true <;>
      by_cases h2 : validContext source.assumptions.shareableVariables context = true <;>
      by_cases h3 : source.assumptions.valid = true <;>
      simp [h1, h2, h3, pure, Except.pure] at accepted
    cases accepted; rfl

/-- The checker refuses an undeclared hole in any mode. Proved through `elaborate.eq_def`, so the
unfolding equation is generated here once, not again in each of the modules that unfold `elaborate`. -/
theorem elaborate_refuses_hole (assumptions : Assumptions) (annotations : Annotations)
    (context : Context) (path : List Nat) (n : Nat) (payload : List Term) (mode : Mode)
    (undeclared : assumptions.holes.lookup n = none) :
    elaborate assumptions annotations context path (.hole n payload) mode =
      throw (.undeclaredHole path n) := by
  rw [elaborate.eq_def]
  simp only
  split
  · rfl
  · rename_i h; rw [undeclared] at h; cases h

end Obend.Core.Bidirectional

end
