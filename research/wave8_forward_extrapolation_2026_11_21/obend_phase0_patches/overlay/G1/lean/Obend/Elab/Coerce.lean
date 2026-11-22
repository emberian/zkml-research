module
/- Type-directed coercions (review/ALGEBRAIC-SUBTYPING-20261031.md §3.5, narrowed as
astra/ASTRA-EVAL-20261031.md lines 55–67 propose).

`emit a A B` builds a closed annotated lambda from `A` to `B`, or names the obstruction:

* identity, when `A` and `B` agree;
* records: `B` an explicit closed row of distinct labels, each found in `A` by lookup and
  coerced (identity or a nested coercion applied to the projection). The parameter is used
  once per kept field, so two or more kept fields need an `unrestricted` parameter, which needs
  `A` shareable: otherwise `needsSharing` (the §5.3 obstruction, measured at line 57);
* sums: `A` an explicit closed sum whose every label `B` has, each payload coerced inside its
  arm and re-injected. Arm payloads are bound unrestricted, so they must be shareable;
* functions: the η-wrapper `λf. λy. c (f (d y))`, with the reuse fixed and the parameter
  quantities gated by `wrapperAllowed`, the matrix the actual checker admits
  (`Obend.Elab.Proofs.CoerceProbes` re-measures every cell). Since `linear` separates from
  `affine` in the kernel (`PartialTyping.lambda` requires `Quantity.fits`, `argumentAllowed`
  requires `linearFree` for a non-`linear` parameter), a wrapper whose parameter is `linear`
  must hand it to a `linear` parameter: relabelling a `linear` hypothesis as `affine` (or
  `erased`) is refused by name (`launders`). When the wrapper's parameter is `linear`, its
  domain and codomain components are emitted at `linear` too (`Emitted.once`);
* nothing else: activities, custody, scalars of different heads, and recursive coercions
  between aliases whose unfoldings differ are refused by name.

`coerce` emits and then runs `Bidirectional.checkAgainst` at `arrow reusable q A B`, so
`coerce_checks` holds for every coercion it returns. `emit_identity_checks` and
`emit_width_checks` prove, without running the checker, that emission of the identity and of
a width/representative record coercion (agreeing kept members) always checks. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Check

@[expose] public section
namespace Obend.Elab.Coerce
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Core.Term (Term)
set_option autoImplicit false

inductive CoercionRefusal where
  /-- A label the target row or sum needs that the source lacks. -/
  | missingLabel (name : String) (source : Ty)
  /-- Two or more kept fields read the parameter twice; the source is not shareable. -/
  | needsSharing (source : Ty)
  /-- A sum's payload is bound unrestricted in its arm; this one is not shareable. -/
  | payloadNotShareable (name : String) (payload : Ty)
  | activityField (name : String) (member : Ty)
  /-- A quantity pair outside the measured η-wrapper matrix, or a change of reuse. -/
  | quantityNotWrappable (source target : Quantity)
  /-- The wrapper's `linear` parameter would be handed to a `source` parameter that may drop it:
  a once-resource laundered through a coercion. -/
  | launders (source target : Quantity)
  | reuseChanged (source target : Reuse)
  /-- Two aliases, or an alias and a constructor, that agree on no finite unfolding here. -/
  | recursive (source target : Ty)
  | notCoercible (source target : Ty)
  | checker (refusal : CheckRefusal)
  | fuel (source target : Ty)
  deriving Repr

/-- A wrapper with a `linear` parameter around a callee that may drop its argument. -/
def launders : Quantity → Quantity → Bool
  | .erased, .linear | .affine, .linear => true
  | _, _ => false

/-- The η-wrapper matrix: `λy. f y` wraps `f : q → C` as a `q' → C` (rows `q`, columns `q'`,
order erased, affine, linear, unrestricted). Measured in `CoerceProbes`: `erased` is never a
wrapper's parameter (it is used), `unrestricted` only wraps `unrestricted`, and a `linear`
parameter only wraps a `linear` one (`launders` names the two cells that changed when `linear`
separated from `affine`). -/
def wrapperAllowed : Quantity → Quantity → Bool
  | _, .erased => false
  | .unrestricted, .unrestricted => true
  | .unrestricted, _ => false
  | .linear, _ => true
  | _, .linear => false
  | _, _ => true

/-- An emitted coercion: a closed lambda, its annotations, and its parameter's quantity. -/
structure Emitted where
  term : Term
  tree : AnnotationTree
  quantity : Quantity

/-- Its type. -/
def Emitted.type (e : Emitted) (source target : Ty) : Ty := .arrow .reusable e.quantity source target

/-- The same coercion with an `affine` parameter declared `linear`: it is applied to an expression
that uses a `linear` hypothesis, so its parameter must be `linear` too. The kernel then demands
exact discharge of it (a coercion that drops it is refused at its binder); an `unrestricted`
parameter is left as is and refused by the kernel at the application. -/
def Emitted.once (e : Emitted) : Emitted :=
  match e.quantity, e.tree with
  | .affine, .node (some annotation) children =>
    ⟨e.term, .node (some { annotation with parameter := .linear }) children, .linear⟩
  | _, _ => e

/-- The explicit fields of a closed row, or nothing. -/
def closedFields : Ty → Option (List (String × Ty))
  | .emptyRow => some []
  | .field name member tail => (closedFields tail).map ((name, member) :: ·)
  | _ => none

def distinctNames : List (String × Ty) → Bool
  | [] => true
  | (name, _) :: rest => !(rest.any (·.1 == name)) && distinctNames rest

/-- One component: the source expression itself, or a nested coercion applied to it. -/
structure Component where
  term : Term
  tree : AnnotationTree
  /-- The nested coercion's parameter is unrestricted: the source expression must be shareable
  and its captures reusable. -/
  shared : Bool

def identityQuantity (source : Ty) : Quantity :=
  if source.bearsCustody then .linear else .affine

def identityEmitted (source target : Ty) : Emitted :=
  let q := identityQuantity source
  ⟨.lam (.bound 0), .node (some ⟨source, target, q, .reusable⟩) [.node none []], q⟩

mutual
def emit (a : Assumptions) : Nat → Ty → Ty → Except CoercionRefusal Emitted
  | 0, source, target => .error (.fuel source target)
  | fuel + 1, source, target =>
    if sameType a source target then .ok (identityEmitted source target)
    else match source, target with
    | _, .emptyRow | _, .field .. =>
      match closedFields target with
      | none => .error (.notCoercible source target)
      | some fields =>
        if !distinctNames fields then .error (.notCoercible source target) else do
        let parts ← emitFields a fuel source fields 0
        let shared := parts.any (·.2.shared)
        let quantity : Quantity := if fields.length ≤ 1 && !shared then .affine else .unrestricted
        if quantity == .unrestricted && !source.shareableUnder a.shareableVariables then
          throw (.needsSharing source)
        pure ⟨.lam (.record (parts.map fun (name, c) => (name, c.term))),
          .node (some ⟨source, target, quantity, .reusable⟩)
            [.node (some (hint .emptyRow target)) (parts.map (·.2.tree))], quantity⟩
    | .variant sourceRow, .variant targetRow =>
      match closedFields sourceRow with
      | none => .error (.notCoercible source target)
      | some arms => do
        let parts ← emitArms a fuel targetRow arms
        pure ⟨.lam (.case (.bound 0) (parts.map fun (name, c) => (name, .inject name c.term))),
          .node (some ⟨source, target, .affine, .reusable⟩)
            [.node none [.node none [], .node none (parts.map fun (_, c) => .node none [c.tree])]], .affine⟩
    | .arrow r q d c, .arrow r' q' d' c' =>
      if r ≠ r' then .error (.reuseChanged r r')
      else if launders q q' then .error (.launders q q')
      else if !wrapperAllowed q q' then .error (.quantityNotWrappable q q')
      else do
        let domainPart ← component a fuel d' d (.bound 0) (.node none []) (q' == .linear)
        let codomainPart ← component a fuel c c'
          (.app (.bound 1) domainPart.term)
          (.node (some (hint source c)) [.node none [], domainPart.tree]) (q' == .linear)
        let outer : Quantity := if r == .reusable then .unrestricted else .affine
        pure ⟨.lam (.lam codomainPart.term),
          .node (some ⟨source, target, outer, .reusable⟩)
            [.node (some ⟨d', c', q', r'⟩) [codomainPart.tree]], outer⟩
    | .variable _, _ | _, .variable _ => .error (.recursive source target)
    | _, _ => .error (.notCoercible source target)

/-- A component `source → target` applied to `expression` (with its tree); `once` when the
expression uses a `linear` hypothesis. -/
def component (a : Assumptions) (fuel : Nat) (source target : Ty) (expression : Term)
    (expressionTree : AnnotationTree) (once : Bool := false) : Except CoercionRefusal Component :=
  if sameType a source target then .ok ⟨expression, expressionTree, false⟩
  else do
    let emitted ← emit a fuel source target
    let nested := if once then emitted.once else emitted
    pure ⟨.app nested.term expression,
      .node (some (hint (nested.type source target) target)) [nested.tree, expressionTree],
      nested.quantity == .unrestricted⟩

def emitFields (a : Assumptions) (fuel : Nat) (source : Ty) :
    List (String × Ty) → Nat → Except CoercionRefusal (List (String × Component))
  | [], _ => pure []
  | (name, member) :: rest, index => do
    let found ← match lookupV a.bounds [] source name with
      | some found => pure found
      | none => throw (.missingLabel name source)
    if member.isComputation then throw (.activityField name member)
    let part ← component a fuel found member (.get (.bound 0) name) (.node none [.node none []])
    let parts ← emitFields a fuel source rest (index + 1)
    pure ((name, part) :: parts)

def emitArms (a : Assumptions) (fuel : Nat) (targetRow : Ty) :
    List (String × Ty) → Except CoercionRefusal (List (String × Component))
  | [] => pure []
  | (name, payload) :: rest => do
    let wanted ← match lookupV a.bounds [] targetRow name with
      | some wanted => pure wanted
      | none => throw (.missingLabel name targetRow)
    if !payload.shareableUnder a.shareableVariables then throw (.payloadNotShareable name payload)
    let part ← component a fuel payload wanted (.bound 0) (.node none [])
    let parts ← emitArms a fuel targetRow rest
    pure ((name, part) :: parts)
end

/-- The fuel `coerce` grants: the two types' sizes bound the recursion. -/
def tyNodes : Ty → Nat
  | .arrow _ _ a b | .field _ a b | .specification a b | .prototype a b => tyNodes a + tyNodes b + 1
  | .variant a => tyNodes a + 1
  | .computation a b c => tyNodes a + tyNodes b + tyNodes c + 1
  | _ => 1

/-- A coercion the checker has accepted at its type. -/
structure Coercion (a : Assumptions) (source target : Ty) where
  emitted : Emitted
  checked : Checked ⟨emitted.term, treeAnnotations emitted.tree, a⟩ []
  accepted : checkAgainst ⟨emitted.term, treeAnnotations emitted.tree, a⟩ [] (emitted.type source target) = .ok checked

def coerce (a : Assumptions) (source target : Ty) : Except CoercionRefusal (Coercion a source target) := do
  let emitted ← emit a (tyNodes source + tyNodes target) source target
  match h : checkAgainst ⟨emitted.term, treeAnnotations emitted.tree, a⟩ [] (emitted.type source target) with
  | .ok checked => pure ⟨emitted, checked, h⟩
  | .error refusal => throw (.checker refusal)

/-- Every coercion `coerce` returns is a closed term the checker accepts at `source ⇒ target`. -/
theorem coerce_checks {a : Assumptions} {source target : Ty} {c : Coercion a source target}
    (_ : coerce a source target = .ok c) :
    ∃ checked, checkAgainst ⟨c.emitted.term, treeAnnotations c.emitted.tree, a⟩ []
      (.arrow .reusable c.emitted.quantity source target) = .ok checked :=
  ⟨c.checked, c.accepted⟩

/-- Emission of the identity always checks, without running the checker. -/
theorem emit_identity_checks {a : Assumptions} {source target : Ty} (valid : a.valid = true)
    (agrees : sameType a source target = true) :
    ∃ checked, checkAgainst ⟨(identityEmitted source target).term,
      treeAnnotations (identityEmitted source target).tree, a⟩ []
      ((identityEmitted source target).type source target) = .ok checked := by
  have safe : safeUses [⟨source, identityQuantity source⟩] [1] = true := by
    unfold identityQuantity; split <;> rfl
  have validCtx : validContext a.shareableVariables [⟨source, identityQuantity source⟩] = true := by
    unfold identityQuantity; split <;> simp_all [validContext]
  have captures : reusableAllowed a .reusable [] [] = true := rfl
  have fits : (identityQuantity source).fits 1 = true := by
    unfold identityQuantity; split <;> rfl
  have validNil : validContext a.shareableVariables [] = true := rfl
  have safeNil : safeUses [] [] = true := rfl
  simp [checkAgainst, checkAt, elaborate, identityEmitted, Emitted.type, treeAnnotations,
    AnnotationTree.lookup, finish, agrees, sameType_refl,
    variableUses, List.getElem?_cons_zero, List.range_succ, List.tail_cons, checkedSynth,
    need_ok safe, need_ok validCtx, need_ok captures, need_ok fits, need_ok safeNil, need_ok validNil,
    need_ok valid, bind, Except.bind, pure, Except.pure]

/-! ### Width and representative record coercions check, by proof -/

/-- The record of projections a width coercion emits, and its annotations. -/
def widthTerm (fields : List (String × Ty)) : Term :=
  .lam (.record (fields.map fun (name, _) => (name, .get (.bound 0) name)))

def widthQuantity (fields : List (String × Ty)) : Quantity :=
  if fields.length ≤ 1 then .affine else .unrestricted

def widthTree (source target : Ty) (fields : List (String × Ty)) : AnnotationTree :=
  .node (some ⟨source, target, widthQuantity fields, .reusable⟩)
    [.node (some (hint .emptyRow target)) (fields.map fun _ => .node none [.node none []])]

def rowOf : List (String × Ty) → Ty
  | [] => .emptyRow
  | (name, member) :: rest => .field name member (rowOf rest)

/-- Each kept member is found in the source at an agreeing, non-activity type. -/
def KeptAgree (a : Assumptions) (source : Ty) (fields : List (String × Ty)) : Prop :=
  ∀ name member, (name, member) ∈ fields → member.isComputation = false ∧
    ∃ found, lookupV a.bounds [] source name = some found ∧ sameType a found member = true

theorem emptyTree_lookup : ∀ path : List Nat, emptyTree.lookup path = none
  | [] => rfl
  | _ :: path => by
    simp only [AnnotationTree.lookup, AnnotationTree.child, emptyTree, List.getElem?_nil, Option.getD_none]
    exact emptyTree_lookup path

theorem plain_lookup : ∀ path : List Nat, (AnnotationTree.node none [.node none []]).lookup path = none
  | [] => rfl
  | 0 :: path => by simpa [AnnotationTree.lookup, AnnotationTree.child, emptyTree] using emptyTree_lookup path
  | (_ + 1) :: path => by simpa [AnnotationTree.lookup, AnnotationTree.child] using emptyTree_lookup path

theorem width_field_annotations (source target : Ty) (fields : List (String × Ty)) (index : Nat)
    (rest : List Nat) :
    treeAnnotations (widthTree source target fields) ([0, index] ++ rest) = none := by
  simp only [treeAnnotations, widthTree, List.cons_append, List.nil_append, AnnotationTree.lookup,
    AnnotationTree.child, List.getElem?_cons_zero, Option.getD_some, List.getElem?_map]
  cases h : fields[index]? with
  | none => simpa using emptyTree_lookup rest
  | some _ => simpa using plain_lookup rest

theorem get_bound_checks {a : Assumptions} {annotations : Annotations} {path : List Nat} {source found member : Ty}
    {q : Quantity} {name : String} (notLinear : q ≠ .linear)
    (here : annotations path = none) (below : annotations (path ++ [0]) = none)
    (lookup : lookupV a.bounds [] source name = some found) (agrees : sameType a found member = true) :
    ∃ r, elaborate a annotations [⟨source, q⟩] path (.get (.bound 0) name) (.check member) = .ok r ∧
      r.uses = [1] := by
  rw [elaborate]
  simp only [here, elaborate, below, finish, ascribe, bind, Except.bind, List.getElem?_cons_zero]
  split
  · rename_i m h
    rw [lookup] at h; cases h
    have free : linearFree [⟨source, q⟩] (List.map (fun position => if position = 0 then 1 else 0) [0]) = true := by
      simp [linearFree, notLinear]
    simp [agrees, variableUses, need_ok free]
  · rename_i h; rw [lookup] at h; contradiction

theorem width_fields_check {a : Assumptions} {source : Ty} {q : Quantity} (notLinear : q ≠ .linear)
    (annotations : Annotations)
    (plain : ∀ index rest, annotations ([0, index] ++ rest) = none) :
    ∀ (fields : List (String × Ty)) (index : Nat), KeptAgree a source fields →
    ∃ result, checkFields a annotations [⟨source, q⟩] [0] index
        (fields.map fun (name, _) => (name, .get (.bound 0) name)) (rowOf fields) = .ok result ∧
      result.uses = [fields.length]
  | [], _, _ => ⟨⟨[0], .nil _⟩, rfl, rfl⟩
  | (name, member) :: rest, index, kept => by
    obtain ⟨nonComputation, found, lookup, agrees⟩ := kept name member (by simp)
    obtain ⟨later, laterOk, laterUses⟩ := width_fields_check (q := q) notLinear annotations plain rest (index + 1)
      (fun n m h => kept n m (by simp [h]))
    have atField : annotations [0, index] = none := by simpa using plain index []
    have atBound : annotations [0, index, 0] = none := by simpa using plain index [0]
    have nonActivity : (!member.isComputation) = true := by simp [nonComputation]
    obtain ⟨field, fieldOk, fieldUses⟩ := get_bound_checks (q := q) notLinear atField atBound lookup agrees
    rw [List.map_cons, rowOf, checkFields]
    simp [fieldOk, laterOk, need_ok nonActivity, bind, Except.bind, pure, Except.pure, fieldUses, laterUses,
      addUses, Nat.add_comm]

/-- **A width/representative record coercion checks, by proof.** Each kept member agrees with
the source's, two or more kept fields have a shareable source, and the kept labels are distinct (a record
names each field once): then the emitted record of
projections is accepted at `source ⇒ target` without running the checker. -/
theorem width_checks {a : Assumptions} {source : Ty} {fields : List (String × Ty)} (valid : a.valid = true)
    (kept : KeptAgree a source fields)
    (sharing : (fields.length ≤ 1 ∧ source.bearsCustody = false) ∨ source.shareableUnder a.shareableVariables = true)
    (distinct : labelsDistinct (fields.map fun (name, _) => (name, Term.get (.bound 0) name)) = true) :
    ∃ checked, checkAgainst ⟨widthTerm fields, treeAnnotations (widthTree source (rowOf fields) fields), a⟩ []
      (.arrow .reusable (widthQuantity fields) source (rowOf fields)) = .ok checked := by
  let annotations := treeAnnotations (widthTree source (rowOf fields) fields)
  obtain ⟨members, membersOk, membersUses⟩ := width_fields_check (q := widthQuantity fields) (by unfold widthQuantity; split <;> decide) annotations
    (width_field_annotations source (rowOf fields) fields) fields 0 kept
  have root : annotations [] = some ⟨source, rowOf fields, widthQuantity fields, .reusable⟩ := rfl
  have recordRoot : annotations [0] = some (hint .emptyRow (rowOf fields)) := rfl
  have safe : safeUses [⟨source, widthQuantity fields⟩] members.uses = true := by
    rw [membersUses]; unfold widthQuantity; split <;> simp_all [safeUses, safeQuantity]
  have validCtx : validContext a.shareableVariables [⟨source, widthQuantity fields⟩] = true := by
    have noCustody : source.bearsCustody = false := by
      rcases sharing with ⟨_, hc⟩ | hs
      · exact hc
      · exact Ty.bearsCustody_of_shareableUnder hs
    unfold widthQuantity; split
    · simp [validContext, noCustody]
    · rename_i long
      have hs : source.shareableUnder a.shareableVariables = true := by
        rcases sharing with ⟨hle, _⟩ | hs
        · exact False.elim (long hle)
        · exact hs
      simp [validContext, hs, noCustody]
  have captures : reusableAllowed a .reusable [] members.uses.tail = true := by
    rw [membersUses]; rfl
  have fits : (widthQuantity fields).fits (members.uses.headD 0) = true := by
    rw [membersUses]; unfold widthQuantity; split <;> simp_all [Quantity.fits]
  have top : safeUses [] members.uses.tail = true := by rw [membersUses]; rfl
  have topValid : validContext a.shareableVariables [] = true := rfl
  simp [checkAgainst, checkAt, elaborate, widthTerm, root, recordRoot, introduce, membersOk, finish,
    checkedSynth, sameType_refl, need_ok safe, need_ok validCtx, need_ok captures, need_ok fits, need_ok valid, hint,
    need_ok top, need_ok topValid, need_ok distinct, bind, Except.bind, pure, Except.pure, annotations]

end Obend.Elab.Coerce