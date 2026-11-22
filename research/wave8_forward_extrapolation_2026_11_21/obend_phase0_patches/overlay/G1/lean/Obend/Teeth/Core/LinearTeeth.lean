module
/- `linear` separates from `affine` in the kernel (decided 2026-11-01; `lean/docs/REPORT-LINEAR-20261101.md`).

Four premises carry it. `PartialTyping.lambda` requires `Quantity.fits` of the parameter's own
count, so a `linear` binder is used exactly once; `argumentAllowed` requires `linearFree` of an
argument passed to a non-`linear` parameter, so a `linear` hypothesis is never handed to a callee
that may drop it (`erased`, `affine`) or share it (`unrestricted`); the joins (`ifBool`, `ifZero`,
`case` arms) require `branchesAgree`, so every branch uses it equally, and join by `joinUses`; the
projections (`get`, `reflect`, `metadata`, `project`) require `linearFree` of their target, so no
dropped sibling holds one. The checker names the refusal: `linearBinderUnused`,
`linearArgumentDropped`, `linearBranchesDisagree`, `linearProjected`.

The examples check concrete refusal paths. The mutation checks exercise the quantity rules
for arbitrary counts, contexts and usage vectors. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Tactic.Tooth
import all Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.Bidirectional

public section
namespace Obend.Teeth.Core.LinearTeeth
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences)
set_option autoImplicit false

/-- A linear binder must be used exactly once, at every possible usage count. -/
theorem linear_fits_iff (uses : Nat) : Quantity.linear.fits uses = true ↔ uses = 1 := by
  simp [Quantity.fits]

#tooth linear_fits_iff by mutation Quantity.fits := safeQuantity

/-- `λ(h : Custody). 0`: the custody is dropped. -/
def droppedCustody (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.nat 0), fun path => if path = [] then some ⟨.custody 0, .natural, q, .once⟩ else none, {}⟩

def droppedCustodyType (q : Quantity) : Ty := .arrow .once q (.custody 0) .natural

/-- TOOTH (a dropped `linear` custody is refused, by name, at its binder). -/
example :
    (match checkAgainst (droppedCustody .linear) [] (droppedCustodyType .linear) with
      | .error (.linearBinderUnused []) => true
      | _ => false) = true := by decide

/-- Under Gate G1 (`mustBeLinear`), binding custody at `affine` is refused (`invalidContext`),
whereas a custody-free `affine` binder may still be dropped. -/
example :
    (match checkAgainst (droppedCustody .affine) [] (droppedCustodyType .affine) with
      | .error (.invalidContext []) => true
      | _ => false) = true := by decide

example :
    (checkAgainst ⟨.lam (.nat 0), fun path => if path = [] then some ⟨.natural, .natural, .affine, .once⟩ else none, {}⟩
      [] (.arrow .once .affine .natural .natural)).toBool = true := by decide

/-- `λ(h : Custody). (λ(z : Custody). 0) h`: the custody is passed to a callee whose parameter has
quantity `q`. At `affine`, G1 already refuses the callee's `affine` custody binder at `[0, 0]`;
for a custody-free `linear` binder (`handedLinearNat`), the checker reaches `[0, 1]` and refuses
`linearArgumentDropped`. -/
def handedCustody (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.app (.lam (.nat 0)) (.bound 0)), fun path =>
    if path = [] then some ⟨.custody 0, .natural, .linear, .once⟩
    else if path = [0] then some ⟨.arrow .once q (.custody 0) .natural, .natural, .affine, .once⟩
    else if path = [0, 0] then some ⟨.custody 0, .natural, q, .once⟩
    else none, {}⟩

def handedLinearNat (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.app (.lam (.nat 0)) (.bound 0)), fun path =>
    if path = [] then some ⟨.natural, .natural, .linear, .once⟩
    else if path = [0] then some ⟨.arrow .once q .natural .natural, .natural, .affine, .once⟩
    else if path = [0, 0] then some ⟨.natural, .natural, q, .once⟩
    else none, {}⟩

example :
    (match checkAgainst (handedCustody .affine) [] (droppedCustodyType .linear) with
      | .error (.invalidContext [0, 0]) => true
      | _ => false) = true := by decide

/-- TOOTH (a `linear` hypothesis handed to an `affine` callee, which drops it, is refused by name:
the argument at `[0, 1]` uses hypothesis `0`). The binder count is one, so exact discharge at the
binder alone would have accepted it. -/
example :
    (match checkAgainst (handedLinearNat .affine) [] (.arrow .once .linear .natural .natural) with
      | .error (.linearArgumentDropped [0, 1] 0 .affine) => true
      | _ => false) = true := by decide

theorem linear_argument_needs_linear_slot (a : Assumptions) (q : Quantity) (ctx : Context)
    (t : Ty) (uses : Uses) (h : linearFree ctx uses = false)
    (ok : argumentAllowed a q ctx t uses = true) : q = .linear := by
  have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).2
  simpa [h] using allowed

#tooth linear_argument_needs_linear_slot by mutation argumentAllowed := fun _ _ _ _ _ => true

/-- With a `linear` callee the obligation moves to it, and it is refused at the callee's own binder,
which drops it: the drop is found wherever the custody goes. -/
example :
    (match checkAgainst (handedCustody .linear) [] (droppedCustodyType .linear) with
      | .error (.linearBinderUnused [0, 0]) => true
      | _ => false) = true := by decide

/-- A `linear` custody that flows into a `linear` slot which uses it is accepted:
`λ(h : Custody). (λ(z : Custody). z) h`. -/
def passedCustody : AnnotatedTerm :=
  ⟨.lam (.app (.lam (.bound 0)) (.bound 0)), fun path =>
    if path = [] then some ⟨.custody 0, .custody 0, .linear, .once⟩
    else if path = [0] then some ⟨.arrow .once .linear (.custody 0) (.custody 0), .custody 0, .affine, .once⟩
    else if path = [0, 0] then some ⟨.custody 0, .custody 0, .linear, .once⟩
    else none, {}⟩

example :
    (checkAgainst passedCustody [] (.arrow .once .linear (.custody 0) (.custody 0))).toBool = true := by decide

/-! ### The two gaps exact discharge left at the binder, closed

A branch that drops a `linear` hypothesis the other branch uses (`branchesAgree`), and a projection
that drops a sibling holding one (`linearFree` at `get`, `reflect`, `metadata`, `project`). -/

/-- `λ(h : Nat). if c then h else e`, with `h` of quantity `q`. -/
def branching (q : Quantity) (whenFalse : Term) : AnnotatedTerm :=
  ⟨.lam (.ifBool (.boolean true) (.bound 0) whenFalse), fun path =>
    if path = [] then some ⟨.natural, .natural, q, .once⟩ else none, {}⟩

/-- TOOTH (a branch drops a `linear` hypothesis the other uses: refused by name at the join, naming
hypothesis `0`). Counting by sum this was one use and accepted. -/
example :
    (match checkAgainst (branching .linear (.nat 0)) [] (.arrow .once .linear .natural .natural) with
      | .error (.linearBranchesDisagree [0] 0) => true
      | _ => false) = true := by decide

theorem linear_join_agrees (t : Ty) (ctx : Context) (x y : Nat) (xs ys : Uses)
    (h : branchesAgree (⟨t, .linear⟩ :: ctx) (x :: xs) (y :: ys) = true) : x = y := by
  simpa [Quantity.agrees] using (Bool.and_eq_true_iff.mp h).1

#tooth linear_join_agrees by mutation branchesAgree := fun _ _ _ => true

/-- A mismatch at the current binder is reported at its actual index. -/
theorem disagreement_at_linear (t : Ty) (ctx : Context) (x y index : Nat) (xs ys : Uses)
    (h : x ≠ y) :
    firstDisagreement (⟨t, .linear⟩ :: ctx) (x :: xs) (y :: ys) index = some index := by
  simp [firstDisagreement, Quantity.agrees, h]

#tooth disagreement_at_linear by mutation firstDisagreement := fun _ _ _ _ => none

/-- Both branches use it once: one use on every path, accepted (by sum it was two, refused). -/
example :
    (checkAgainst (branching .linear (.bound 0)) [] (.arrow .once .linear .natural .natural)).toBool = true := by
  decide

/-- An `affine` hypothesis joins by maximum: used on one branch, or on both, it is used at most once. -/
example :
    (checkAgainst (branching .affine (.nat 0)) [] (.arrow .once .affine .natural .natural)).toBool = true ∧
    (checkAgainst (branching .affine (.bound 0)) [] (.arrow .once .affine .natural .natural)).toBool = true := by
  decide

/-- `λ(h : Nat). {kept = 1, held = h}.kept`: the projection keeps `kept` and drops `held`. -/
def siblingDropped (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.get (.record [("kept", .nat 1), ("held", .bound 0)]) "kept"), fun path =>
    if path = [] then some ⟨.natural, .natural, q, .once⟩ else none, {}⟩

/-- TOOTH (a projection drops a sibling holding a `linear` hypothesis: refused by name at the
projection, naming hypothesis `0`). The binder count is one, so the binder rule alone accepted it. -/
example :
    (match checkAgainst (siblingDropped .linear) [] (.arrow .once .linear .natural .natural) with
      | .error (.linearProjected [0] 0) => true
      | _ => false) = true := by decide

/-- A projection, metadata discard, or overwrite may discard only unused linear bindings. -/
theorem discarded_linear_unused (ctx : Context) (uses : Uses) (t : Ty) (n : Nat)
    (free : linearFree ctx uses = true) (member : (⟨t, .linear⟩, n) ∈ ctx.zip uses) : n = 0 := by
  simpa using List.all_eq_true.mp free _ member

#tooth discarded_linear_unused by mutation linearFree := fun _ _ => true

theorem projected_at_linear_use (path : List Nat) (ctx : Context) (uses : Uses) (i : Nat)
    (h : firstLinearUse ctx uses = some i) : projected path ctx uses = .linearProjected path i := by
  simp [projected, h]

#tooth projected_at_linear_use by mutation projected := fun path _ _ => .linearProjected path 0

/-- At `affine` the same projection is accepted: the dropped sibling may be dropped. -/
example :
    (checkAgainst (siblingDropped .affine) [] (.arrow .once .affine .natural .natural)).toBool = true := by decide


/-! ### Four rules that let a `Step` discard what a subterm held (lane Sound, 11-01)

Gemini's checkpoint review, item 1. Each fixture below is `λ(h : Nat). body` with `h` of quantity `q`;
at `linear`, `body` was accepted by both checkers before 11-01 (measured on the tree at `9d75d59`), and
one or two `Step`s from `body` (open in `h`) lose the use of `h`. Each is now refused by name at
`linear` and accepted at `affine`. -/

/-- `λh. {meta = h; λx. x} 3`: applying a specification calls its extension and discards the
metadata (`Step.applySpecification`). -/
def specificationBody : Term := .app (.specification (.bound 0) (.lam (.bound 0))) (.nat 3)
def specificationDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam specificationBody, fun p => if p = [] then some ⟨.natural, .natural, q, .once⟩
    else if p = [0, 0, 1] then some ⟨.natural, .natural, .unrestricted, .reusable⟩ else none, {}⟩

example :
    Step specificationBody (.app (.lam (.bound 0)) (.nat 3)) ∧
      occurrences 1 specificationBody = [1] ∧ occurrences 1 (.app (.lam (.bound 0)) (.nat 3)) = [0] :=
  ⟨.applySpecification _ _ _, by decide, by decide⟩

/-- TOOTH: the metadata of the specification at `[0, 0]` uses `h`. -/
example :
    (match checkAgainst (specificationDrop .linear) [] (.arrow .once .linear .natural .natural) with
      | .error (.linearMetadata [0, 0] 0) => true
      | _ => false) = true := by decide

/-- Discarding metadata and overwriting a field both report the binding that was used. -/
theorem discard_reports_binding (path : List Nat) (ctx : Context) (uses : Uses) (i : Nat)
    (h : firstLinearUse ctx uses = some i) :
    linearRefusal .linearMetadata path ctx uses = .linearMetadata path i ∧
    linearRefusal .linearOverwritten path ctx uses = .linearOverwritten path i := by
  simp [linearRefusal, h]

#tooth discard_reports_binding by mutation linearRefusal := fun refusal path _ _ => refusal path 0

/-- `λh. {a = h} with {a = 0}`: the extension overwrites the field holding `h` (`Step.extendRecord`). -/
def oneField : Ty := .field "a" .natural .emptyRow
def extendBody : Term := .extend (.record [("a", .bound 0)]) [("a", .nat 0)]
def extendDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam extendBody, fun p => if p = [] then some ⟨.natural, overlay oneField oneField, q, .once⟩ else none, {}⟩

example :
    Step extendBody (.record [("a", .nat 0)]) ∧
      occurrences 1 extendBody = [1] ∧ occurrences 1 (.record [("a", .nat 0)]) = [0] :=
  ⟨.extendRecord _ _, by decide, by decide⟩

/-- TOOTH: the target of the extension at `[0]` uses `h`. -/
example :
    (match checkAgainst (extendDrop .linear) [] (.arrow .once .linear .natural (overlay oneField oneField)) with
      | .error (.linearOverwritten [0] 0) => true
      | _ => false) = true := by decide

/-- `λh. case l h of l x. 0`: the arm drops the payload (`Step.caseInject`). Before 11-01 the arm
bound it `unrestricted`; the arm now binds it at the case's quantity (here `q`, the hypothesis's),
and a `linear` payload is used exactly once. -/
def oneLabel : Ty := .variant (.field "l" .natural .emptyRow)
def caseBody : Term := .case (.inject "l" (.bound 0)) [("l", .nat 0)]
def caseDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam caseBody, fun p => if p = [] then some ⟨.natural, .natural, q, .once⟩
    else if p = [0] then some ⟨oneLabel, .natural, q, .reusable⟩ else none, {}⟩

example :
    Step caseBody (.nat 0) ∧ occurrences 1 caseBody = [1] ∧ occurrences 1 (.nat 0) = [0] :=
  ⟨by simpa [caseBody, instantiate, Term.substitute] using Step.caseInject "l" (.bound 0) [("l", .nat 0)] (.nat 0) rfl,
    by decide, by decide⟩

/-- TOOTH: the arm at `[0, 1, 0]` binds the `linear` payload and does not use it. -/
example :
    (match checkAgainst (caseDrop .linear) [] (.arrow .once .linear .natural .natural) with
      | .error (.linearScrutinee [0, 1, 0]) => true
      | _ => false) = true := by decide

/-- The same scrutinee with no case annotation: the checker binds the payload `linear` itself
(`caseQuantity`), and refuses the same arm. -/
example :
    (match checkAgainst ⟨.lam (.case (.inject "l" (.bound 0)) [("l", .nat 0)]), fun p =>
        if p = [] then some ⟨.natural, .natural, .linear, .once⟩
        else if p = [0, 0] then some ⟨.natural, oneLabel, .unrestricted, .reusable⟩ else none, {}⟩
        [] (.arrow .once .linear .natural .natural) with
      | .error (.linearScrutinee [0, 1, 0]) => true
      | _ => false) = true := by decide

/-- A `linear` sum is matched: the arm uses its `linear` payload once, `λh. case l h of l x. x`. -/
example :
    (checkAgainst ⟨.lam (.case (.inject "l" (.bound 0)) [("l", .bound 0)]), fun p =>
        if p = [] then some ⟨.natural, .natural, .linear, .once⟩
        else if p = [0] then some ⟨oneLabel, .natural, .linear, .reusable⟩ else none, {}⟩
        [] (.arrow .once .linear .natural .natural)).toBool = true := by decide

/-- An annotation that binds a `linear` scrutinee's payload `unrestricted` is refused at the case. -/
example :
    (match checkAgainst ⟨.lam (.case (.inject "l" (.bound 0)) [("l", .bound 0)]), fun p =>
        if p = [] then some ⟨.natural, .natural, .linear, .once⟩
        else if p = [0] then some ⟨oneLabel, .natural, .unrestricted, .reusable⟩ else none, {}⟩
        [] (.arrow .once .linear .natural .natural) with
      | .error (.linearArgumentDropped [0] 0 .unrestricted) => true
      | _ => false) = true := by decide

/-- Inferred case binders preserve a linear scrutinee, including through sequencing. -/
theorem case_quantity_of_linear_use (a : Assumptions) (ctx : Context) (uses : Uses)
    (shareable : Bool) (h : linearFree ctx uses = false) :
    caseQuantity a ctx uses shareable = .linear := by simp [caseQuantity, h]

#tooth case_quantity_of_linear_use by mutation caseQuantity := fun _ _ _ _ _ => .affine

/-- The same arm duplicating the payload, `case l h of l x. x + x`, is a copy of `h` in one step. -/
example :
    Step (.case (.inject "l" (.bound 0)) [("l", .binary .add (.bound 0) (.bound 0))])
        (.binary .add (.bound 0) (.bound 0)) ∧
      occurrences 1 (.binary .add (.bound 0) (.bound 0)) = [2] :=
  ⟨by simpa [instantiate, Term.substitute] using
      Step.caseInject "l" (.bound 0) [("l", .binary .add (.bound 0) (.bound 0))] (.binary .add (.bound 0) (.bound 0)) rfl,
    by decide⟩

/-- `λh. case (done (l h)) of l x. done 0`, a sequencing `case`: `done` steps to its value, and the
plain `case` then drops it. Two steps; the same arm rule closes it (a `done` premise did, before the
arm rule). -/
def activity (result : Ty) : Ty := .computation (.variant .emptyRow) .natural result
def doneBody : Term := .case (.done (.inject "l" (.bound 0))) [("l", .done (.nat 0))]
def doneDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam doneBody, fun p => if p = [] then some ⟨.natural, activity .natural, q, .once⟩
    else if p = [0] then some ⟨activity oneLabel, activity .natural, q, .reusable⟩ else none, {}⟩

example :
    Steps doneBody (.done (.nat 0)) ∧ occurrences 1 doneBody = [1] ∧ occurrences 1 (.done (.nat 0)) = [0] :=
  ⟨.next (.caseTarget _ (.done _)) (.next (by
      simpa [instantiate, Term.substitute] using
        Step.caseInject "l" (.bound 0) [("l", .done (.nat 0))] (.done (.nat 0)) rfl) (.refl _)),
    by decide, by decide⟩

/-- TOOTH: the sequencing arm at `[0, 1, 0]` binds the `linear` payload and does not use it. -/
example :
    (match checkAgainst (doneDrop .linear) [] (.arrow .once .linear .natural (activity .natural)) with
      | .error (.linearScrutinee [0, 1, 0]) => true
      | _ => false) = true := by decide

/-- NOT A HOLE: `ifZero` and `ifBool` eliminate their scrutinee. `λh. ifZero h 0 (p. p + p)` is
accepted at `linear`: the test is the one use of `h`. `Step.successor` fires only at a literal, which
holds no hypothesis, and binds the predecessor, a fresh literal; `step_conserves_linear` covers both
rules with no new premise. -/
def ifZeroBody : Term := .ifZero (.bound 0) (.nat 0) (.binary .add (.bound 0) (.bound 0))
example :
    (checkAgainst ⟨.lam ifZeroBody, fun p => if p = [] then some ⟨.natural, .natural, .linear, .once⟩ else none, {}⟩
      [] (.arrow .once .linear .natural .natural)).toBool = true := by decide

/-! ### Refusals that name their own clause (Kimi's review A) -/

/-- `λ(h : linear Nat). h + h`: overuse names the binder's quantity (it said `affine` for every one). -/
example :
    (match checkAgainst ⟨.lam (.binary .add (.bound 0) (.bound 0)),
        fun p => if p = [] then some ⟨.natural, .natural, .linear, .once⟩ else none, {}⟩
        [] (.arrow .once .linear .natural .natural) with
      | .error (.binderOverused [] 0 .linear 2) => true
      | _ => false) = true := by decide

example :
    (match checkAgainst ⟨.lam (.bound 0),
        fun p => if p = [] then some ⟨.natural, .natural, .erased, .once⟩ else none, {}⟩
        [] (.arrow .once .erased .natural .natural) with
      | .error (.binderOverused [] 0 .erased 1) => true
      | _ => false) = true := by decide

/-- An `affine` hypothesis passed to an `unrestricted` parameter of shareable type: the captures, not
the type, are what is not shareable (it said `notShareable` of the type). -/
example :
    (match checkAgainst ⟨.lam (.app (.lam (.bound 0)) (.bound 0)), fun p =>
        if p = [] then some ⟨.natural, .natural, .affine, .once⟩
        else if p = [0, 0] then some ⟨.natural, .natural, .unrestricted, .reusable⟩ else none, {}⟩
        [] (.arrow .once .affine .natural .natural) with
      | .error (.capturesNotShareable [0, 1]) => true
      | _ => false) = true := by decide

/-- An activity passed as an argument is `activityMisplaced` (it said `notShareable`). -/
example :
    (match checkAgainst ⟨.app (.lam (.nat 0)) (.done (.nat 0)), fun p =>
        if p = [0] then some ⟨activity .natural, .natural, .affine, .reusable⟩ else none, {}⟩
        [] .natural with
      | .error (.activityMisplaced [1] _) => true
      | _ => false) = true := by decide

/-- An empty record against a row with a field: expected the row, actual the empty row (the two were
reversed). -/
example :
    (match checkAgainst ⟨.record [], fun p => if p = [] then some ⟨.emptyRow, oneField, .unrestricted, .reusable⟩
        else none, {}⟩ [] oneField with
      | .error (.typeMismatch [] expected actual) => expected == oneField && actual == .emptyRow
      | _ => false) = true := by decide

/-! ## Custody is bound `linear` (`mustBeLinear`, gate G1)

`validContext` requires `mustBeLinear` of every binding: a custody-bearing binder is `linear`, so
custody is never dropped (`erased`, `affine`) or shared (`unrestricted`). The lambda rule, the arms
of a `case`/`effectCase` (`ArmsTyping.cons`), `SplitSpine` and `Checked` all require `validContext`. -/

example : validContext [] [⟨.custody 7, .affine⟩] = false := by decide
example : validContext [] [⟨.custody 7, .erased⟩] = false := by decide
example : validContext [] [⟨.custody 7, .unrestricted⟩] = false := by decide
example : validContext [] [⟨.custody 7, .linear⟩] = true := by decide
/-- Custody under a record field or a sum is still custody. -/
example : validContext [] [⟨.field "c" (.custody 7) .emptyRow, .affine⟩] = false := by decide
example : validContext [] [⟨.variant (.field "c" (.custody 7) .emptyRow), .affine⟩] = false := by decide
/-- A custody-free record may still be `affine`. -/
example : validContext [] [⟨.field "n" .natural .emptyRow, .affine⟩] = true := by decide

/-- The checker refuses a top-level context with an `affine` custody binding... -/
example :
    (match checkAgainst ⟨.nat 0, fun _ => none, {}⟩ [⟨.custody 7, .affine⟩] .natural with
      | .error (.invalidContext []) => true
      | _ => false) = true := by decide
/-- ...and accepts the same term over a `linear` one. -/
example :
    (match checkAgainst ⟨.nat 0, fun _ => none, {}⟩ [⟨.custody 7, .linear⟩] .natural with
      | .ok _ => true
      | _ => false) = true := by decide

/-- A lambda that takes custody at `affine` is refused; at `linear` it checks. -/
example :
    (match checkAgainst ⟨.lam (.bound 0), fun p =>
        if p = [] then some ⟨.custody 7, .custody 7, .affine, .once⟩ else none, {}⟩
        [] (.arrow .once .affine (.custody 7) (.custody 7)) with
      | .error (.invalidContext _) => true
      | _ => false) = true := by decide
example :
    (match checkAgainst ⟨.lam (.bound 0), fun p =>
        if p = [] then some ⟨.custody 7, .custody 7, .linear, .once⟩ else none, {}⟩
        [] (.arrow .once .linear (.custody 7) (.custody 7)) with
      | .ok _ => true
      | _ => false) = true := by decide

theorem caseQuantity_custody_linear (a : Assumptions) (ctx : Context) (uses : Uses) (sh : Bool) :
    caseQuantity a ctx uses sh true = .linear := by
  simp [caseQuantity]

-- Without `mustBeLinear` (and `custody` in `caseQuantity`) the stored proofs fail: an `affine`
-- custody context would be valid, and an unannotated `case` could bind a custody payload `affine`.
#tooth Obend.Core.Ty.validContext_refuses_affine_custody by mutation Obend.Core.Ty.mustBeLinear :=
  fun _ => true
#tooth Obend.Core.Ty.validContext_custody_linear by mutation Obend.Core.Ty.mustBeLinear :=
  fun _ => true
#tooth Obend.Core.Check.lambda_custody_linear by mutation Obend.Core.Ty.mustBeLinear :=
  fun _ => true
#tooth caseQuantity_custody_linear by mutation caseQuantity := fun a ctx uses sh _ =>
  if !linearFree ctx uses then .linear
  else if reusableCaptures a.shareableVariables ctx uses && sh then .unrestricted
  else .affine

end Obend.Teeth.Core.LinearTeeth
end
