module
/- Executable annotation preparation for `Bidirectional.checkAgainst`.

`prepare` walks an erased term in the checker's own modes and produces an
`AnnotationTree` for exactly the positions the checker cannot fill from its
expected type: a lambda in function position (a let-redex), an introduction form
in synthesis position, a `fix` whose specification is a bare lambda, a record
checked against a row whose members sit behind an alias or a row tail, an
application whose function type is a specification over an alias. Everything it
annotates it infers locally, from the expected type, the context and the types it
predicts for the subterms; it predicts exactly the type the checker will
synthesize, because each branch below computes it the same way `elaborate` does.

A caller may pass `hints`, an annotation map in the checker's own convention (the
front end's packet annotations). A hint at a lambda, injection, `perform` or
`done` is kept; preparation adds annotations only where there is none.

Preparation is not trusted: `prepareChecked` runs `checkAgainst` on the result,
so a wrong prediction is a refusal, never an acceptance. `prepare_checks`
(`Obend.Elab.PrepareChecks`) proves that on the fragment `Checkable` with
alias-free assumptions, every `Typed` term is prepared and accepted. Where local
inference is silent (a lambda, injection, `perform`, `done` or empty `case` in
synthesis position with no hint), `prepareSearch` tries a bounded set of
candidate annotations at the named path and rechecks; exhaustion is a refusal
that names the path and the number of candidates tried, never "untypable".
Search is not covered by `prepare_checks`; it is the fallback, and every answer
it returns is still the checker's. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Elab.Work

public section
namespace Obend.Elab.Prepare
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Elab.Work (tyNodes)
set_option autoImplicit false

/-- Why preparation stopped, and where (`path` is the checker's source position). -/
inductive PrepareRefusal where
  /-- Local inference has nothing to go on: a form in synthesis position whose type no
  subterm, context entry or expected type determines. `what` names the form. -/
  | silent (path : List Nat) (what : String)
  | unbound (path : List Nat) (index : Nat)
  | shape (path : List Nat) (wanted : String) (actual : Ty)
  | unknownLabel (path : List Nat) (name : String) (row : Ty)
  | hole (path : List Nat)
  /-- The bounded search at `path` tried `tried` candidates and none checked. -/
  | searchExhausted (path : List Nat) (tried : Nat)
  /-- Preparation finished; the checker refused its output. -/
  | checker (refusal : CheckRefusal)
  deriving Repr, DecidableEq

/-- The path of a refusal. -/
def PrepareRefusal.path : PrepareRefusal → List Nat
  | .silent p _ | .unbound p _ | .shape p _ _ | .unknownLabel p _ _ | .hole p | .searchExhausted p _ => p
  | .checker _ => []

abbrev Prepared := Except PrepareRefusal (AnnotationTree × Ty)

/-- A leaf. -/
def leaf : AnnotationTree := .node none []

/-- The sum the checker types an injection at (`Bidirectional.injectionHead`): the raw
annotated sum, or the weak head of the expected type or of an annotation naming the sum by
an alias. -/
def injectionSum (assumptions : Assumptions) (annotated : Bool) (type : Ty) : Ty :=
  match (if annotated then type else whnf assumptions type) with
  | .variant row => .variant row
  | other => whnf assumptions other

/-- Expose a function type for `callable`: unfold the head, and keep unfolding through
specification extensions, at most `fuel` times. The result agrees with the input. -/
def exposeCallable (assumptions : Assumptions) : Nat → Ty → Ty
  | 0, type => type
  | fuel + 1, type =>
    match whnf assumptions type with
    | .specification metadata extension => .specification metadata (exposeCallable assumptions fuel extension)
    | other => other

/-- Replace the underlying target of a `callable` specification spine with `arrow`, keeping its
metadata wrappers intact. -/
def retargetCallable : Ty → Ty → Ty
  | .specification metadata extension, arrow => .specification metadata (retargetCallable extension arrow)
  | _, arrow => arrow

/-- The quantity a let-bound parameter gets: unrestricted when the argument may be
shared (its type is shareable and every capture it uses is), affine when it uses no `linear`
hypothesis, and otherwise `linear`: a `linear` hypothesis is passed only to a `linear` parameter
(`argumentAllowed`), which the body must then use exactly once. -/
def letQuantity (assumptions : Assumptions) (context : Context) (argumentType : Ty) (argument : Term) : Quantity :=
  if argumentType.shareableUnder assumptions.shareableVariables &&
      reusableCaptures assumptions.shareableVariables context (occurrences context.length argument)
  then .unrestricted
  else if !argumentType.bearsCustody && linearFree context (occurrences context.length argument) then .affine else .linear

/-- The lambda annotation that makes an introduction form in synthesis position
check against its own predicted type in both modes. -/
def selfHint (type : Ty) : LambdaAnnotation := hint .emptyRow type

/-- The row a distinct-label record is checked against: its labels, in its order, at
the members the expected type's lookup finds. -/
def lookupRow (assumptions : Assumptions) (expected : Ty) : List (String × Term) → Option Ty
  | [] => some .emptyRow
  | (name, _) :: rest => do
    let member ← lookupV assumptions.bounds [] expected name
    let tail ← lookupRow assumptions expected rest
    pure (.field name member tail)

/-- An application once its function is prepared. When the function's predicted type is
already callable as written, the application is annotated with it, so the checker reads that
representative and ascribes the written codomain (the type the historical checker reported);
otherwise its weak head is used, and deeper through specification extensions (annotated)
only when that is not yet an arrow. Then the argument is prepared against the domain. -/
def applyPrepared (assumptions : Assumptions) (_hints : Annotations) (_context : Context) (path : List Nat)
    (_argument : Term) (mode : Mode) (functionTree : AnnotationTree) (functionType : Ty)
    (prepareArgument : Ty → Except PrepareRefusal AnnotationTree) : Prepared := do
  let exposed := callable (whnf assumptions functionType)
  let deeper := exposeCallable assumptions
    (tyNodes functionType + (assumptions.bounds.map (tyNodes ·.2)).sum + 1) functionType
  let (here, shape) : Option LambdaAnnotation × Ty := match callable functionType with
    | .arrow _ _ _ codomain =>
      -- the function's own representative: the result keeps the codomain as written
      (some (hint functionType codomain), callable functionType)
    | _ => match exposed with
      | .arrow .. => (none, exposed)
      | _ => match callable deeper with
        | .arrow _ _ _ codomain => (some (hint deeper codomain), callable deeper)
        | other => (none, other)
  match shape with
  | .arrow _ _ domain codomain => do
    let argumentTree ← prepareArgument domain
    pure (.node here [functionTree, argumentTree], match mode with | .synth => codomain | .check expected => expected)
  | _ => throw (.shape (path ++ [0]) "function" functionType)

/-- The row a case's arms are typed against, from the scrutinee type's weak head. -/
def caseRow (assumptions : Assumptions) : Ty → Option Ty
  | .variant row => some row
  | .computation _ _ inner => match whnf assumptions inner with
    | .variant row => some row
    | _ => none
  | _ => none

/-- The type every arm is checked against: the expected type, or for an activity scrutinee
the activity over the scrutinee's plan and response with the expected result. -/
def armResult (path : List Nat) (head expected expectedHead : Ty) : Except PrepareRefusal Ty :=
  match head with
  | .computation planType response _ =>
    match expectedHead with
    | .computation _ _ result => pure (.computation planType response result)
    | _ => throw (.shape path "activity" expected)
  | _ => pure expected

/-- What remains of a destructor's function type after its named parameters (`checkSpine`'s result). -/
def spineResult : List String → Ty → Ty
  | [], functionType => functionType
  | _ :: names, functionType => match callable functionType with
    | .arrow _ _ _ codomain => spineResult names codomain
    | _ => functionType

mutual
/-- Prepare a term in a mode. In synthesis the type returned is the type `synthAt`
will produce under the returned tree; in checking it is the expected type. -/
def prepare (assumptions : Assumptions) (hints : Annotations) (context : Context) (path : List Nat) :
    (term : Term) → (mode : Mode) → Prepared
  | .hole _ _, _ => throw (.hole path)
  | .bound index, mode =>
    match context[index]? with
    | some binding => pure (leaf, match mode with | .synth => binding.type | .check expected => expected)
    | none => throw (.unbound path index)
  | .nat _, mode => pure (leaf, match mode with | .synth => .natural | .check expected => expected)
  | .boolean _, mode => pure (leaf, match mode with | .synth => .boolean | .check expected => expected)
  | .label value, mode => pure (leaf, match mode with | .synth => literalType value | .check expected => expected)
  | .lam body, mode =>
    match hints path with
    | some annotation => do
      let (bodyTree, _) ← prepare assumptions hints (⟨annotation.domain, annotation.parameter⟩ :: context)
        (path ++ [0]) body (.check annotation.codomain)
      pure (.node (some annotation) [bodyTree], match mode with
        | .synth => .arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain
        | .check expected => expected)
    | none =>
      match mode with
      | .check expected =>
        match whnf assumptions expected with
        | .arrow _ parameter domain codomain => do
          let (bodyTree, _) ← prepare assumptions hints (⟨domain, parameter⟩ :: context) (path ++ [0]) body
            (.check codomain)
          pure (.node none [bodyTree], expected)
        | _ => throw (.shape path "function" expected)
      | .synth => throw (.silent path "lambda")
  | .app (.lam body) argument, mode =>
    match hints (path ++ [0]) with
    | some annotation => do
      let (bodyTree, _) ← prepare assumptions hints (⟨annotation.domain, annotation.parameter⟩ :: context)
        (path ++ [0, 0]) body (.check annotation.codomain)
      applyPrepared assumptions hints context path argument mode (.node (some annotation) [bodyTree])
        (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain)
        (fun domain => do
          let (tree, _) ← prepare assumptions hints context (path ++ [1]) argument (.check domain)
          pure tree)
    | none => do
      -- a let-redex: the argument's type is the parameter's
      let (argumentTree, argumentType) ← prepare assumptions hints context (path ++ [1]) argument .synth
      let quantity := letQuantity assumptions context argumentType argument
      let binder : Binding := ⟨argumentType, quantity⟩
      let (bodyTree, codomain) ← match mode with
        | .synth => prepare assumptions hints (binder :: context) (path ++ [0, 0]) body .synth
        | .check expected => do
          let (tree, _) ← prepare assumptions hints (binder :: context) (path ++ [0, 0]) body (.check expected)
          pure (tree, expected)
      let annotation : LambdaAnnotation := ⟨argumentType, codomain, quantity, .once⟩
      applyPrepared assumptions hints context path argument mode (.node (some annotation) [bodyTree])
        (.arrow .once quantity argumentType codomain) (fun _ => pure argumentTree)
  | .app function argument, mode => do
    let (functionTree, functionType) ← prepare assumptions hints context (path ++ [0]) function .synth
    applyPrepared assumptions hints context path argument mode functionTree functionType
      (fun domain => do
        let (tree, _) ← prepare assumptions hints context (path ++ [1]) argument (.check domain)
        pure tree)
  | .split target names function, mode => do
    let (targetTree, _) ← prepare assumptions hints context (path ++ [0]) target .synth
    let (functionTree, functionType) ← prepare assumptions hints context (path ++ [1]) function .synth
    pure (.node none [targetTree, functionTree], match mode with
      | .synth => spineResult names functionType | .check expected => expected)
  | .get target name, mode => do
    let (targetTree, targetType) ← prepare assumptions hints context (path ++ [0]) target .synth
    match lookupV assumptions.bounds [] targetType name with
    | some member => pure (.node none [targetTree], match mode with | .synth => member | .check expected => expected)
    | none => throw (.unknownLabel (path ++ [0]) name targetType)
  | .reflect target, mode => do
    let (targetTree, targetType) ← prepare assumptions hints context (path ++ [0]) target .synth
    match whnf assumptions targetType with
    | .prototype specType _ => pure (.node none [targetTree], match mode with | .synth => specType | .check expected => expected)
    | _ => throw (.shape (path ++ [0]) "prototype" targetType)
  | .metadata target, mode => do
    let (targetTree, targetType) ← prepare assumptions hints context (path ++ [0]) target .synth
    match whnf assumptions targetType with
    | .specification metadataType _ =>
      pure (.node none [targetTree], match mode with | .synth => metadataType | .check expected => expected)
    | _ => throw (.shape (path ++ [0]) "specification" targetType)
  | .project target, mode => do
    let (targetTree, targetType) ← prepare assumptions hints context (path ++ [0]) target .synth
    match whnf assumptions targetType with
    | .prototype _ targetType' => pure (.node none [targetTree], match mode with | .synth => targetType' | .check expected => expected)
    | _ => throw (.shape (path ++ [0]) "prototype" targetType)
  | .binary primitive left right, mode => do
    let (leftTree, _) ← prepare assumptions hints context (path ++ [0]) left (.check (primitiveTypes primitive).1)
    let (rightTree, _) ← prepare assumptions hints context (path ++ [1]) right (.check (primitiveTypes primitive).1)
    pure (.node none [leftTree, rightTree], match mode with | .synth => (primitiveTypes primitive).2 | .check expected => expected)
  | .mix lower upper, mode => do
    let (lowerTree, lowerType) ← prepare assumptions hints context (path ++ [0]) lower .synth
    let (upperTree, upperType) ← prepare assumptions hints context (path ++ [1]) upper .synth
    let lowerDeeper := exposeCallable assumptions
      (tyNodes lowerType + (assumptions.bounds.map (tyNodes ·.2)).sum + 1) lowerType
    let upperDeeper := exposeCallable assumptions
      (tyNodes upperType + (assumptions.bounds.map (tyNodes ·.2)).sum + 1) upperType
    match callable lowerDeeper, callable upperDeeper with
    | .arrow .reusable .unrestricted self lowerInner,
      .arrow .reusable .unrestricted _ upperInner =>
      match whnf assumptions lowerInner, whnf assumptions upperInner with
      | .arrow .reusable .unrestricted inherited middle,
        .arrow .reusable .unrestricted _ provided =>
        let lowerRep := retargetCallable lowerDeeper
          (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle))
        let upperRep := retargetCallable upperDeeper
          (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided))
        let mixType := Ty.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)
        let predicted := if sameType assumptions mixType upperRep then upperRep else mixType
        pure (.node (some (hint lowerRep upperRep)) [lowerTree, upperTree], match mode with
          | .synth => predicted
          | .check expected => expected)
      | _, _ => throw (.shape path "mixable pair" lowerType)
    | _, _ => throw (.shape path "mixable pair" lowerType)
  | .fix spec inheritedTerm, mode =>
    match spec, hints (path ++ [0]), mode with
    | .lam _, none, .check expected => do
      -- the specification is a bare lambda: its type is `target → inherited → target`
      let (inheritedTree, inheritedType) ← prepare assumptions hints context (path ++ [1]) inheritedTerm .synth
      let specType := Ty.arrow .reusable .unrestricted expected (.arrow .reusable .unrestricted inheritedType expected)
      let (specTree, _) ← prepare assumptions hints context (path ++ [0]) spec (.check specType)
      pure (.node (some (hint specType expected)) [specTree, inheritedTree], expected)
    | _, _, _ => do
      let (specTree, specType) ← prepare assumptions hints context (path ++ [0]) spec .synth
      let deeper := exposeCallable assumptions
        (tyNodes specType + (assumptions.bounds.map (tyNodes ·.2)).sum + 1) specType
      match callable deeper with
      | .arrow .reusable .unrestricted target inner =>
        match whnf assumptions inner with
        | .arrow .reusable .unrestricted inherited _ =>
          let fixedSpec := retargetCallable deeper
            (.arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target))
          let (inheritedTree, _) ← prepare assumptions hints context (path ++ [1]) inheritedTerm (.check inherited)
          pure (.node (some (hint fixedSpec target)) [specTree, inheritedTree],
            match mode with | .synth => target | .check expected => expected)
        | _ => throw (.shape (path ++ [0]) "fixable specification" specType)
      | _ => throw (.shape (path ++ [0]) "fixable specification" specType)
  | .inject tag payload, mode =>
    let body (annotation? : Option LambdaAnnotation) (sum : Ty) : Prepared :=
      match injectionSum assumptions annotation?.isSome sum with
      | .variant row =>
        match lookupV assumptions.bounds [] row tag with
        | some payloadType => do
          let (payloadTree, _) ← prepare assumptions hints context (path ++ [0]) payload (.check payloadType)
          pure (.node annotation? [payloadTree], sum)
        | none => throw (.unknownLabel path tag row)
      | _ => throw (.shape path "sum" sum)
    match hints path, mode with
    | some annotation, .synth => body (some annotation) annotation.codomain
    | some annotation, .check expected =>
      (body (some annotation) annotation.codomain).map fun (tree, _) => (tree, expected)
    | none, .check expected => body none expected
    | none, .synth => throw (.silent path "injection")
  | .perform plan, mode =>
    let body (annotation? : Option LambdaAnnotation) (activity : Ty) : Prepared :=
      match (match annotation? with | some a => Ty.computation a.domain a.codomain a.codomain | none => whnf assumptions activity) with
      | .computation planType _ _ => do
        let (planTree, _) ← prepare assumptions hints context (path ++ [0]) plan (.check planType)
        pure (.node annotation? [planTree], activity)
      | _ => throw (PrepareRefusal.shape path "activity" activity)
    match hints path, mode with
    | some annotation, .synth => body (some annotation) (.computation annotation.domain annotation.codomain annotation.codomain)
    | some annotation, .check expected => (body (some annotation) expected).map fun (tree, _) => (tree, expected)
    | none, .check expected => body none expected
    | none, .synth => throw (.silent path "perform")
  | .done value, mode =>
    match hints path, mode with
    | some annotation, mode =>
      match annotation.codomain with
      | .computation planType response result => do
        let (valueTree, _) ← prepare assumptions hints context (path ++ [0]) value (.check result)
        pure (.node (some annotation) [valueTree], match mode with
          | .synth => .computation planType response result | .check expected => expected)
      | _ => do
        let (valueTree, valueType) ← prepare assumptions hints context (path ++ [0]) value .synth
        pure (.node (some annotation) [valueTree], match mode with
          | .synth => .computation annotation.domain annotation.codomain valueType | .check expected => expected)
    | none, .check expected =>
      match whnf assumptions expected with
      | .computation _ _ result => do
        let (valueTree, _) ← prepare assumptions hints context (path ++ [0]) value (.check result)
        pure (.node none [valueTree], expected)
      | _ => throw (.shape path "activity" expected)
    | none, .synth => throw (.silent path "done")
  | .record fields, mode =>
    match mode with
    | .synth => do
      let (trees, row) ← prepareFieldsSynth assumptions hints context path 0 fields
      pure (.node (some (selfHint row)) trees, row)
    | .check expected =>
      if labelsDistinct fields then
        match lookupRow assumptions expected fields with
        | some row => do
          let trees ← prepareFieldsCheck assumptions hints context path 0 fields row
          pure (.node (some (selfHint row)) trees, expected)
        | none => do
          -- a label the expected type does not have: the checker names it
          let (trees, row) ← prepareFieldsSynth assumptions hints context path 0 fields
          pure (.node (some (selfHint row)) trees, expected)
      else do
        let (trees, row) ← prepareFieldsSynth assumptions hints context path 0 fields
        pure (.node (some (selfHint row)) trees, expected)
  | .specification metadata extension, mode =>
    match mode with
    | .check expected =>
      match whnf assumptions expected with
      | .specification metadataType extensionType => do
        let (m, _) ← prepare assumptions hints context (path ++ [0]) metadata (.check metadataType)
        let (e, _) ← prepare assumptions hints context (path ++ [1]) extension (.check extensionType)
        pure (.node none [m, e], expected)
      | _ => throw (.shape path "specification" expected)
    | .synth => do
      let (m, metadataType) ← prepare assumptions hints context (path ++ [0]) metadata .synth
      let (e, extensionType) ← prepare assumptions hints context (path ++ [1]) extension .synth
      let type := Ty.specification metadataType extensionType
      pure (.node (some (selfHint type)) [m, e], type)
  | .prototype spec target, mode =>
    match mode with
    | .check expected =>
      match whnf assumptions expected with
      | .prototype specType targetType => do
        let (s, _) ← prepare assumptions hints context (path ++ [0]) spec (.check specType)
        let (t, _) ← prepare assumptions hints context (path ++ [1]) target (.check targetType)
        pure (.node none [s, t], expected)
      | _ => throw (.shape path "prototype" expected)
    | .synth => do
      let (s, specType) ← prepare assumptions hints context (path ++ [0]) spec .synth
      let (t, targetType) ← prepare assumptions hints context (path ++ [1]) target .synth
      let type := Ty.prototype specType targetType
      pure (.node (some (selfHint type)) [s, t], type)
  | .extend target fields, mode => do
    let (targetTree, targetType) ← prepare assumptions hints context (path ++ [0]) target .synth
    let (trees, row) ← prepareFieldsSynth assumptions hints context (path ++ [1]) 0 fields
    pure (.node none [targetTree, .node none trees], match mode with
      | .synth => overlay row targetType | .check expected => expected)
  | .ifBool condition whenTrue whenFalse, mode => do
    let (c, _) ← prepare assumptions hints context (path ++ [0]) condition (.check .boolean)
    match mode with
    | .check expected => do
      let (t, _) ← prepare assumptions hints context (path ++ [1]) whenTrue (.check expected)
      let (f, _) ← prepare assumptions hints context (path ++ [2]) whenFalse (.check expected)
      pure (.node none [c, t, f], expected)
    | .synth => do
      let (t, result) ← prepare assumptions hints context (path ++ [1]) whenTrue .synth
      let (f, _) ← prepare assumptions hints context (path ++ [2]) whenFalse (.check result)
      pure (.node (some (selfHint result)) [c, t, f], result)
  | .ifZero value zero successor, mode => do
    let successorContext : Context := ⟨.natural, .unrestricted⟩ :: context
    let (v, _) ← prepare assumptions hints context (path ++ [0]) value (.check .natural)
    match mode with
    | .check expected => do
      let (z, _) ← prepare assumptions hints context (path ++ [1]) zero (.check expected)
      let (s, _) ← prepare assumptions hints successorContext (path ++ [2]) successor (.check expected)
      pure (.node none [v, z, s], expected)
    | .synth => do
      let (z, result) ← prepare assumptions hints context (path ++ [1]) zero .synth
      let (s, _) ← prepare assumptions hints successorContext (path ++ [2]) successor (.check result)
      pure (.node (some (selfHint result)) [v, z, s], result)
  | .case scrutinee [], mode => do
    let (scrutineeTree, scrutineeType) ← prepare assumptions hints context (path ++ [0]) scrutinee .synth
    let head := whnf assumptions scrutineeType
    match caseRow assumptions head with
    | none => throw (.shape (path ++ [0]) "sum or activity" scrutineeType)
    | some _ =>
      match mode with
      | .check expected => do
        let expectedHead := whnf assumptions expected
        let _ ← armResult path head expected expectedHead
        let scrutineeRep := match head with
          | .computation planType response _ => .computation planType response (.variant .emptyRow)
          | _ => .variant .emptyRow
        let q := caseQuantity assumptions context (occurrences context.length scrutinee) true
        pure (.node (some ⟨scrutineeRep, expectedHead, q, .reusable⟩) [scrutineeTree, .node none []], expected)
      | .synth => throw (.silent path "empty case")
  | .case scrutinee ((name, body) :: rest), mode => do
    let (scrutineeTree, scrutineeType) ← prepare assumptions hints context (path ++ [0]) scrutinee .synth
    let head := whnf assumptions scrutineeType
    match caseRow assumptions head with
    | none => throw (.shape (path ++ [0]) "sum or activity" scrutineeType)
    | some rawRow =>
      let row := (lookupRow assumptions rawRow ((name, body) :: rest)).getD rawRow
      let scrutineeRep := match head with
        | .computation planType response _ => .computation planType response (.variant row)
        | _ => .variant row
      -- the payload quantity the checker computes for the resolved arm row (`caseQuantityAt`)
      let q := caseQuantity assumptions context (occurrences context.length scrutinee)
        (armsShareable assumptions row ((name, body) :: rest))
        (armsCustody row ((name, body) :: rest))
      match mode with
      | .check expected => do
        let expectedHead := whnf assumptions expected
        let result ← armResult path head expectedHead expectedHead
        let trees ← prepareArms assumptions hints context q (path ++ [1]) 0 row result ((name, body) :: rest)
        pure (.node (some ⟨scrutineeRep, expectedHead, q, .reusable⟩) [scrutineeTree, .node none trees], expected)
      | .synth =>
        match rowMember row name with
        | none => throw (.unknownLabel (path ++ [1]) name rawRow)
        | some payload => do
          -- the first arm's synthesis tree also checks at its own type; the case is annotated
          -- with its scrutinee's resolved row representative and that type's weak head
          let (firstTree, first) ← prepare assumptions hints (⟨payload, q⟩ :: context) (path ++ [1, 0]) body .synth
          let firstHead := whnf assumptions first
          let result ← armResult path head firstHead firstHead
          let trees ← prepareArms assumptions hints context q (path ++ [1]) 1 row result rest
          pure (.node (some ⟨scrutineeRep, firstHead, q, .reusable⟩) [scrutineeTree, .node none (firstTree :: trees)], firstHead)

def prepareFieldsSynth (assumptions : Assumptions) (hints : Annotations) (context : Context) (path : List Nat)
    (index : Nat) : List (String × Term) → Except PrepareRefusal (List AnnotationTree × Ty)
  | [] => pure ([], .emptyRow)
  | (name, body) :: rest => do
    let (tree, type) ← prepare assumptions hints context (path ++ [index]) body .synth
    let (trees, row) ← prepareFieldsSynth assumptions hints context path (index + 1) rest
    pure (tree :: trees, .field name type row)

def prepareFieldsCheck (assumptions : Assumptions) (hints : Annotations) (context : Context) (path : List Nat)
    (index : Nat) : List (String × Term) → Ty → Except PrepareRefusal (List AnnotationTree)
  | [], _ => pure []
  | (_name, body) :: rest, .field _ member tail => do
    let (tree, _) ← prepare assumptions hints context (path ++ [index]) body (.check member)
    let trees ← prepareFieldsCheck assumptions hints context path (index + 1) rest tail
    pure (tree :: trees)
  | (name, _) :: _, row => throw (.unknownLabel (path ++ [index]) name row)

def prepareArms (assumptions : Assumptions) (hints : Annotations) (context : Context) (q : Quantity) (path : List Nat)
    (index : Nat) (row result : Ty) : List (String × Term) → Except PrepareRefusal (List AnnotationTree)
  | [] => pure []
  | (name, body) :: rest =>
    match rowMember row name with
    | some payload => do
      let (tree, _) ← prepare assumptions hints (⟨payload, q⟩ :: context) (path ++ [index]) body
        (.check result)
      let trees ← prepareArms assumptions hints context q path (index + 1) row result rest
      pure (tree :: trees)
    | none => throw (.unknownLabel (path ++ [index]) name row)
end

/-- No hints: the erased program. -/
def noHints : Annotations := fun _ => none

/-- Prepare the erased term `source.term` (its annotations are hints) against `expected`. -/
def prepareAnnotations (source : AnnotatedTerm) (context : Context) (expected : Ty) :
    Except PrepareRefusal Annotations := do
  let (tree, _) ← prepare source.assumptions source.annotations context [] source.term (.check expected)
  pure (treeAnnotations tree)

/-- Prepare, then run the checker: what it accepts is what the gate accepts. -/
def prepareChecked (source : AnnotatedTerm) (context : Context) (expected : Ty) :
    Except PrepareRefusal (Σ annotations : Annotations, Checked { source with annotations := annotations } context) := do
  let annotations ← prepareAnnotations source context expected
  match checkAgainst { source with annotations := annotations } context expected with
  | .ok checked => pure ⟨annotations, checked⟩
  | .error refusal => throw (.checker refusal)

/-- Prepare in synthesis: the predicted type, then the checker at it. -/
def prepareInferred (source : AnnotatedTerm) (context : Context) :
    Except PrepareRefusal (Σ annotations : Annotations, Checked { source with annotations := annotations } context) := do
  let (tree, type) ← prepare source.assumptions source.annotations context [] source.term .synth
  let annotations := treeAnnotations tree
  match checkAgainst { source with annotations := annotations } context type with
  | .ok checked => pure ⟨annotations, checked⟩
  | .error refusal => throw (.checker refusal)

/-! ## Bounded search where local inference is silent -/

/-- The candidate types at a silent position: the scalars and the context's binder types. -/
def candidateTypes (context : Context) : List Ty :=
  [.natural, .boolean, .label] ++ context.map (·.type)

/-- Candidate annotations: for a lambda every scalar or context domain and codomain at every
quantity and reuse (72 for an empty context, the set Astra searched); for the other silent forms
the same pairs as unrestricted reusable hints. -/
def candidates (context : Context) (what : String) : List LambdaAnnotation :=
  let types := candidateTypes context
  let pairs := types.flatMap fun d => types.map fun c => (d, c)
  if what == "lambda" then
    pairs.flatMap fun (d, c) =>
      [Quantity.erased, .affine, .linear, .unrestricted].flatMap fun q =>
        [Reuse.once, .reusable].map fun r => (⟨d, c, q, r⟩ : LambdaAnnotation)
  else pairs.map fun (d, c) => hint d c

/-- One more hint at one path. -/
def withHint (hints : Annotations) (path : List Nat) (annotation : LambdaAnnotation) : Annotations :=
  fun p => if p = path then some annotation else hints p

mutual
/-- Prepare and check; where preparation is silent at a path, try each candidate there, with at
most `depth` silent positions filled. Every result is the checker's acceptance. -/
def prepareSearch (depth : Nat) (source : AnnotatedTerm) (context : Context) (expected : Ty) :
    Except PrepareRefusal (Σ annotations : Annotations, Checked { source with annotations := annotations } context) :=
  match prepareChecked source context expected with
  | .ok result => .ok result
  | .error (.silent path what) =>
    match depth with
    | 0 => .error (.silent path what)
    | depth + 1 => tryCandidates depth source context expected path (candidates context what) 0
  | .error refusal => .error refusal

def tryCandidates (depth : Nat) (source : AnnotatedTerm) (context : Context) (expected : Ty) (path : List Nat) :
    List LambdaAnnotation → Nat →
      Except PrepareRefusal (Σ annotations : Annotations, Checked { source with annotations := annotations } context)
  | [], tried => .error (.searchExhausted path tried)
  | candidate :: rest, tried =>
    match prepareSearch depth { source with annotations := withHint source.annotations path candidate } context expected with
    | .ok ⟨annotations, checked⟩ => .ok ⟨annotations, checked⟩
    | .error _ => tryCandidates depth source context expected path rest (tried + 1)
end

end Obend.Elab.Prepare
end
