module
public import Lean
public section
namespace Obend.Core.Ty
set_option autoImplicit false

/-- Quantities are obligations of this edition. -/
inductive Quantity where
  | erased | affine | linear | unrestricted
  deriving Repr, DecidableEq
inductive Reuse where
  | once | reusable
  deriving Repr, DecidableEq

/-- Rigid variables stand for future self/super types. A row tail is retained,
not flattened to the currently known methods. Ordinary arrows and scalar targets
are first-class. This is an annotated equality/row fragment, not general F-sub. -/
inductive Ty where
  | natural | label | boolean
  | variable (index : Nat)
  | arrow (reuse : Reuse) (parameter : Quantity) (domain codomain : Ty)
  | emptyRow
  | field (name : String) (member tail : Ty)
  | specification (metadata extension : Ty)
  | prototype (specification target : Ty)
  | custody (identity : Nat)
  /-- A sum over the labels of an ordinary field row. A `.emptyRow` tail is a
  closed (exhaustively eliminable) sum; a variable tail is an open sum. -/
  | variant (row : Ty)
  /-- An activity: a computation that may yield Plans of type `plan`, is resumed
  with responses of type `response`, and finishes with `result`. Only a direct
  (never suspended) position may hold it: it is not shareable, and every
  cell-allocating typing rule refuses it. Surface: `Activity<Plan, Response, Result>`. -/
  | computation (plan response result : Ty)
  deriving Repr, @[expose] DecidableEq

/-- A reusable closure is shareable only after its captures have been checked.
Custody is never hidden by a record/prototype/specification wrapper. -/
@[expose] def Ty.shareable : Ty → Bool
  | .natural | .label | .boolean | .emptyRow => true
  | .variable _ | .custody _ => false
  | .arrow reuse _ _ _ => reuse == .reusable
  | .field _ member tail => member.shareable && tail.shareable
  | .specification metadata extension => metadata.shareable && extension.shareable
  | .prototype spec target => spec.shareable && target.shareable
  | .variant row => row.shareable
  | .computation _ _ _ => false

/-- Rigid variables may be quantified over shareable future types explicitly.
Every instantiation must discharge this finite premise; an unknown row is never
implicitly pure merely because its currently visible fields are immutable. -/
@[expose] def Ty.shareableUnder (variables : List Nat) : Ty → Bool
  | .variable index => variables.contains index
  | .field _ member tail => member.shareableUnder variables && tail.shareableUnder variables
  | .specification metadata extension => metadata.shareableUnder variables && extension.shareableUnder variables
  | .prototype spec target => spec.shareableUnder variables && target.shareableUnder variables
  | .variant row => row.shareableUnder variables
  | other => other.shareable

@[simp] theorem Ty.shareableUnder_empty (type : Ty) : type.shareableUnder [] = type.shareable := by
  induction type <;> simp_all [Ty.shareableUnder, Ty.shareable]

/-- The head of an activity type. Only the head is inspected: canonical row
equality preserves it, and bounds never name an activity (`Assumptions.valid`),
so this is invariant under every checked type agreement. -/
@[expose] def Ty.isComputation : Ty → Bool
  | .computation _ _ _ => true
  | _ => false

/-- First-order data: what a Plan, a response and a checkpointed reply can be.
No closures, specifications, prototypes, custody, rigid variables (so no
recursive sums yet) and no activities. -/
@[expose] def Ty.isData : Ty → Bool
  | .natural | .label | .boolean | .emptyRow => true
  | .field _ member tail => member.isData && tail.isData
  | .variant row => row.isData
  | _ => false

/-- A Plan is a sum of typed actions over first-order data. -/
@[expose] def Ty.isPlan : Ty → Bool
  | .variant row => row.isData
  | _ => false

theorem Ty.shareable_not_computation (type : Ty) (shareable : type.shareable = true) :
    type.isComputation = false := by
  cases type <;> simp_all [Ty.shareable, Ty.isComputation]

theorem Ty.shareableUnder_not_computation (variables : List Nat) (type : Ty)
    (shareable : type.shareableUnder variables = true) : type.isComputation = false := by
  cases type <;> simp_all [Ty.shareableUnder, Ty.shareable, Ty.isComputation]


/-- Shadowing changes this field only; unknown future tail stays present. -/
def Ty.put (row : Ty) (name : String) (member : Ty) : Ty :=
  match row with
  | .field prior old tail =>
      if prior = name then .field name member tail else .field prior old (tail.put name member)
  | tail => .field name member tail

@[expose] def Ty.tail : Ty → Ty
  | .field _ _ rest => rest.tail
  | other => other

theorem put_preserves_future_tail (row : Ty) (name : String) (member : Ty) :
    (row.put name member).tail = row.tail := by
  induction row with
  | field prior old rest ih₁ ih₂ =>
    simp only [Ty.put]
    split <;> simp_all [Ty.tail]
  | _ => rfl

/-- Canonical finite named-row equality preserves a rigid unknown tail and
first-field shadowing. It is equality, not width/depth subtyping or a solver.
A shadowed member is forgotten only when it is `shareable`: a custody, a once
closure or any other non-shareable member stays in the canonical row behind the
member that shadows it, so canonical equality never hides what shareability
sees (`Ty.shareableUnder_canonical`). -/
@[expose] def Ty.insertCanonical (row : Ty) (name : String) (member : Ty) : Ty :=
  match row with
  | .field prior old tail =>
      if name = prior then (if old.shareable then .field name member tail else .field name member row)
      else if name < prior then .field name member row
      else .field prior old (tail.insertCanonical name member)
  | tail => .field name member tail

@[expose] def Ty.canonical : Ty → Ty
  | .arrow reuse quantity domain codomain => .arrow reuse quantity domain.canonical codomain.canonical
  | .field name member tail => tail.canonical.insertCanonical name member.canonical
  | .specification metadata extension => .specification metadata.canonical extension.canonical
  | .prototype spec target => .prototype spec.canonical target.canonical
  | .variant row => .variant row.canonical
  | .computation plan response result =>
      .computation plan.canonical response.canonical result.canonical
  | other => other

theorem Ty.insertCanonical_not_computation (row : Ty) (name : String) (member : Ty) :
    (row.insertCanonical name member).isComputation = false := by
  cases row <;> simp only [Ty.insertCanonical]
  all_goals repeat' first | split
  all_goals rfl

theorem Ty.canonical_isComputation (type : Ty) : type.canonical.isComputation = type.isComputation := by
  cases type <;> try rfl
  exact Ty.insertCanonical_not_computation _ _ _

/-- A shareable type is shareable under any shareability premises. -/
theorem Ty.shareableUnder_of_shareable (variables : List Nat) : ∀ {type : Ty},
    type.shareable = true → type.shareableUnder variables = true
  | .field _ member tail, h => by
    simp only [Ty.shareable, Bool.and_eq_true] at h
    simp [Ty.shareableUnder, Ty.shareableUnder_of_shareable variables h.1, Ty.shareableUnder_of_shareable variables h.2]
  | .specification metadata extension, h => by
    simp only [Ty.shareable, Bool.and_eq_true] at h
    simp [Ty.shareableUnder, Ty.shareableUnder_of_shareable variables h.1, Ty.shareableUnder_of_shareable variables h.2]
  | .prototype spec target, h => by
    simp only [Ty.shareable, Bool.and_eq_true] at h
    simp [Ty.shareableUnder, Ty.shareableUnder_of_shareable variables h.1, Ty.shareableUnder_of_shareable variables h.2]
  | .variant row, h => by
    simp only [Ty.shareable] at h
    simp [Ty.shareableUnder, Ty.shareableUnder_of_shareable variables h]
  | .variable _, h => by simp [Ty.shareable] at h
  | .natural, _ | .label, _ | .boolean, _ | .emptyRow, _ | .custody _, _ | .arrow _ _ _ _, _
  | .computation _ _ _, _ => by simp_all [Ty.shareableUnder]

theorem Ty.shareableUnder_insertCanonical (variables : List Nat) (row : Ty) (name : String) (member : Ty) :
    (row.insertCanonical name member).shareableUnder variables =
      (member.shareableUnder variables && row.shareableUnder variables) := by
  induction row with
  | field prior old tail _ ih =>
    simp only [Ty.insertCanonical]
    by_cases he : name = prior
    · by_cases hs : old.shareable = true
      · simp [he, hs, Ty.shareableUnder, Ty.shareableUnder_of_shareable variables hs]
      · simp [he, hs, Ty.shareableUnder]
    · by_cases hl : name < prior
      · simp [he, hl, Ty.shareableUnder]
      · simp only [he, hl, if_false, Ty.shareableUnder, ih]
        cases member.shareableUnder variables <;> cases old.shareableUnder variables <;> rfl
  | _ => simp [Ty.insertCanonical, Ty.shareableUnder]

/-- Canonical form never changes shareability: no member it forgets was needed
to refuse it (`Ty.insertCanonical` forgets only shareable shadowed members). -/
theorem Ty.shareableUnder_canonical (variables : List Nat) (type : Ty) :
    type.canonical.shareableUnder variables = type.shareableUnder variables := by
  induction type with
  | field name member tail ihm iht =>
    simp only [Ty.canonical, Ty.shareableUnder_insertCanonical, ihm, iht, Ty.shareableUnder]
  | specification m e ihm ihe => simp [Ty.canonical, Ty.shareableUnder, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.canonical, Ty.shareableUnder, ihs, iht]
  | variant r ih => simp [Ty.canonical, Ty.shareableUnder, ih]
  | arrow => simp [Ty.canonical, Ty.shareableUnder, Ty.shareable]
  | computation => simp [Ty.canonical, Ty.shareableUnder, Ty.shareable]
  | _ => rfl

theorem Ty.shareable_canonical (type : Ty) : type.canonical.shareable = type.shareable := by
  simpa using Ty.shareableUnder_canonical [] type

/-! ### Canonical form is idempotent -/

/-- The label relation between a row entry and the row after it in canonical form:
labels ascend, and a label repeats only before a non-shareable shadowed member. -/
@[expose] def Ty.headOk (name : String) : Ty → Prop
  | .field next member _ => name < next ∨ (name = next ∧ member.shareable = false)
  | _ => True

/-- The shape `Ty.canonical` produces. -/
@[expose] def Ty.isCanonical : Ty → Prop
  | .arrow _ _ domain codomain => domain.isCanonical ∧ codomain.isCanonical
  | .field name member tail => member.isCanonical ∧ tail.isCanonical ∧ Ty.headOk name tail
  | .specification metadata extension => metadata.isCanonical ∧ extension.isCanonical
  | .prototype spec target => spec.isCanonical ∧ target.isCanonical
  | .variant row => row.isCanonical
  | .computation plan response result => plan.isCanonical ∧ response.isCanonical ∧ result.isCanonical
  | _ => True

theorem String.gt_of_not_lt_ne {a b : String} (h1 : ¬ a < b) (h2 : a ≠ b) : b < a :=
  Decidable.byContradiction fun h3 => h2 (String.le_antisymm (String.not_lt.mp h3) (String.not_lt.mp h1))

theorem Ty.isCanonical_insert (name : String) (member : Ty) (canonicalMember : member.isCanonical) :
    ∀ (row : Ty), row.isCanonical → (row.insertCanonical name member).isCanonical
  | .field prior old tail, ⟨co, ct, ho⟩ => by
    simp only [Ty.insertCanonical]
    by_cases he : name = prior
    · subst he
      by_cases hs : old.shareable = true
      · simp only [if_true, hs]; exact ⟨canonicalMember, ct, ho⟩
      · simp only [if_true, hs, Bool.false_eq_true, if_false]
        exact ⟨canonicalMember, ⟨co, ct, ho⟩, .inr ⟨rfl, by simpa using hs⟩⟩
    · by_cases hl : name < prior
      · simp only [he, hl, if_true, if_false]; exact ⟨canonicalMember, ⟨co, ct, ho⟩, .inl hl⟩
      · have gt : prior < name := String.gt_of_not_lt_ne hl he
        simp only [he, hl, if_false]
        refine ⟨co, Ty.isCanonical_insert name member canonicalMember tail ct, ?_⟩
        cases tail with
        | field next m rest =>
          simp only [Ty.insertCanonical]
          by_cases he' : name = next
          · subst he'
            by_cases hs : m.shareable = true <;> simp [hs, Ty.headOk, gt]
          · by_cases hl' : name < next
            · simp only [he', hl', if_true, if_false, Ty.headOk]; exact .inl gt
            · simp only [he', hl', if_false]; exact ho
        | _ => simp only [Ty.insertCanonical, Ty.headOk]; exact .inl gt
  | .natural, _ | .label, _ | .boolean, _ | .variable _, _ | .arrow .., _ | .emptyRow, _
  | .specification .., _ | .prototype .., _ | .custody _, _ | .variant _, _ | .computation .., _ => by
    simp only [Ty.insertCanonical]; exact ⟨canonicalMember, by assumption, trivial⟩

theorem Ty.canonical_isCanonical : ∀ (type : Ty), type.canonical.isCanonical
  | .field name member tail =>
    Ty.isCanonical_insert name _ (Ty.canonical_isCanonical member) _ (Ty.canonical_isCanonical tail)
  | .arrow _ _ d c => ⟨Ty.canonical_isCanonical d, Ty.canonical_isCanonical c⟩
  | .specification m e => ⟨Ty.canonical_isCanonical m, Ty.canonical_isCanonical e⟩
  | .prototype s t => ⟨Ty.canonical_isCanonical s, Ty.canonical_isCanonical t⟩
  | .variant r => Ty.canonical_isCanonical r
  | .computation p r a => ⟨Ty.canonical_isCanonical p, Ty.canonical_isCanonical r, Ty.canonical_isCanonical a⟩
  | .natural | .label | .boolean | .variable _ | .emptyRow | .custody _ => trivial

theorem Ty.canonical_of_isCanonical : ∀ {type : Ty}, type.isCanonical → type.canonical = type
  | .field name member tail, ⟨cm, ct, ho⟩ => by
    simp only [Ty.canonical, Ty.canonical_of_isCanonical cm, Ty.canonical_of_isCanonical ct]
    cases tail with
    | field next m rest =>
      simp only [Ty.insertCanonical]
      rcases ho with lt | ⟨rfl, hs⟩
      · simp [String.ne_of_lt lt, lt]
      · simp [hs]
    | _ => rfl
  | .arrow _ _ d c, ⟨cd, cc⟩ => by simp [Ty.canonical, Ty.canonical_of_isCanonical cd, Ty.canonical_of_isCanonical cc]
  | .specification m e, ⟨cm, ce⟩ => by simp [Ty.canonical, Ty.canonical_of_isCanonical cm, Ty.canonical_of_isCanonical ce]
  | .prototype s t, ⟨cs, ct⟩ => by simp [Ty.canonical, Ty.canonical_of_isCanonical cs, Ty.canonical_of_isCanonical ct]
  | .variant r, cr => by simp [Ty.canonical, Ty.canonical_of_isCanonical (type := r) cr]
  | .computation p r a, ⟨cp, cr, ca⟩ => by
    simp [Ty.canonical, Ty.canonical_of_isCanonical cp, Ty.canonical_of_isCanonical cr, Ty.canonical_of_isCanonical ca]
  | .natural, _ | .label, _ | .boolean, _ | .variable _, _ | .emptyRow, _ | .custody _, _ => rfl

/-- Canonical form is idempotent. -/
@[simp] theorem Ty.canonical_canonical (type : Ty) : type.canonical.canonical = type.canonical :=
  Ty.canonical_of_isCanonical (Ty.canonical_isCanonical type)

/-- Explicit finite bounds disclose the members available on a rigid self/super
variable. Recursive bounds are explored only to the requested finite depth. -/
abbrev Bounds := List (Nat × Ty)
@[expose] def Ty.lookup (bounds : Bounds) : Nat → Ty → String → Option Ty
  | 0, _, _ => none
  | fuel + 1, .field prior member tail, name =>
      if prior = name then some member else tail.lookup bounds fuel name
  | fuel + 1, .variable index, name => do
      let bound ← bounds.lookup index
      bound.lookup bounds fuel name
  | _, _, _ => none

@[expose] def Ty.isRow (bounds : Bounds) : Nat → Ty → Bool
  | 0, _ => false
  | _ + 1, .emptyRow => true
  | fuel + 1, .field _ _ tail => tail.isRow bounds fuel
  | fuel + 1, .variable index =>
      match bounds.lookup index with
      | some type => type.isRow bounds fuel
      | none => false
  | _, _ => false

/-- A decidable annotated structural interface check. Fields are looked up in
the actual row/bounds and checked by exact type equality; arbitrary subtyping,
variance, associated-type search and unbounded recursive conversion are absent. -/
def Ty.supports (bounds : Bounds) : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, actual, .emptyRow => actual.isRow bounds (fuel + 1)
  | fuel + 1, actual, .field name member tail =>
      actual.lookup bounds (fuel + 1) name == some member && actual.supports bounds fuel tail
  | _ + 1, actual, required => actual == required

/-- What a binder of this quantity promises about its own uses: `linear` exactly once. The lambda
rule (`PartialTyping.lambda`) requires it of the parameter's count. -/
@[expose] def Quantity.fits : Quantity → Nat → Bool
  | .erased, count => count == 0
  | .affine, count => count <= 1
  | .linear, count => count == 1
  | .unrestricted, _ => true

structure Binding where
  type : Ty
  quantity : Quantity
  deriving Repr, DecidableEq
abbrev Context := List Binding
abbrev Uses := List Nat

@[expose] def zeroUses (context : Context) : Uses := List.replicate context.length 0
@[expose] def variableUses (context : Context) (index : Nat) : Uses :=
  (List.range context.length).map (fun position => if position = index then 1 else 0)
@[expose] def addUses (first second : Uses) : Uses := List.zipWith (· + ·) first second

/-- At most once for `affine` and `linear`, never for `erased`. A partial computation may still
retain a linear obligation forever (a divergent body never reaches its use); the checker's part of
exact discharge is syntactic and lives at the binder (`Quantity.fits`, required by
`PartialTyping.lambda`), at the argument (`linearFree`, required by `argumentAllowed`), at the joins
(`branchesAgree`, required by `ifBool`, `ifZero` and the arms of a `case`), wherever a step may
discard what a subterm holds (`linearFree`: the target of `get`, `reflect`, `metadata`, `project` and
`extend`, a specification's metadata), and at a `case`, whose arms bind the payload at a quantity the
scrutinee allows (`caseAllowed`: `linear` for a scrutinee that uses a `linear` hypothesis). -/
@[expose] def safeQuantity : Quantity → Nat → Bool
  | .erased, count => count == 0
  | .affine, count | .linear, count => count <= 1
  | .unrestricted, _ => true

@[expose] def safeUses (context : Context) (uses : Uses) : Bool :=
  uses.length == context.length &&
    (context.zip uses).all (fun pair => safeQuantity pair.1.quantity pair.2)

/-- No `linear` hypothesis is used: what an argument must satisfy unless the parameter it is
passed to is itself `linear`. A `linear` hypothesis flows only into a `linear` slot, so a callee
that may drop its argument (`erased`, `affine`) or share it (`unrestricted`) never receives one. -/
@[expose] def linearFree (context : Context) (uses : Uses) : Bool :=
  (context.zip uses).all (fun pair => pair.2 == 0 || pair.1.quantity != .linear)

/-- The uses of two branches of which exactly one runs (`ifBool`, `ifZero`, the arms of a `case`):
pointwise maximum. With `branchesAgree` this is the additive rule: a `linear` hypothesis is used
equally often on every branch and the join is that common count; an `affine` one at most once on
each branch, so at most once; an `unrestricted` one any number of times. The join is the same `max`
at every quantity, so the uses of a term stay a function of the term alone (`uses_determined`). -/
@[expose] def joinUses (first second : Uses) : Uses := List.zipWith max first second

/-- What a binder of this quantity demands of two branches: a `linear` one the same count on both. -/
@[expose] def Quantity.agrees : Quantity → Nat → Nat → Bool
  | .linear, first, second => first == second
  | _, _, _ => true

/-- The branches agree on every `linear` hypothesis: the premise `joinUses` needs at a join. -/
@[expose] def branchesAgree : Context → Uses → Uses → Bool
  | binding :: context, first :: firsts, second :: seconds =>
      binding.quantity.agrees first second && branchesAgree context firsts seconds
  | _, _, _ => true

@[expose] def reusableCaptures (variables : List Nat) (context : Context) (uses : Uses) : Bool :=
  uses.length == context.length && (context.zip uses).all (fun pair =>
    pair.2 == 0 || (pair.1.quantity == .unrestricted && pair.1.type.shareableUnder variables))

/-- The type holds custody where a value of it can carry it: `custody` itself, or a record,
specification, prototype or sum with a custody-bearing member. An arrow is not inspected (what a
closure captures is checked at its own binder), and an activity is never bound (`Ty.computation`
is not shareable and no cell-allocating rule admits it). A rigid variable is custody-free here
and discharged custody-free by `Templates.Discharges.custody`. -/
@[expose, simp] def Ty.bearsCustody : Ty → Bool
  | .custody _ => true
  | .field _ member tail => member.bearsCustody || tail.bearsCustody
  | .specification metadata extension => metadata.bearsCustody || extension.bearsCustody
  | .prototype spec target => spec.bearsCustody || target.bearsCustody
  | .variant row => row.bearsCustody
  | .natural | .label | .boolean | .variable _ | .arrow _ _ _ _ | .emptyRow | .computation _ _ _ => false

/-- A shareable type bears no custody (`Ty.shareable` refuses `custody` under every wrapper). -/
theorem Ty.bearsCustody_of_shareableUnder {variables : List Nat} :
    ∀ {type : Ty}, type.shareableUnder variables = true → type.bearsCustody = false
  | .field _ member tail, h => by
    simp only [Ty.shareableUnder, Bool.and_eq_true] at h
    simp [Ty.bearsCustody_of_shareableUnder h.1, Ty.bearsCustody_of_shareableUnder h.2]
  | .specification m e, h => by
    simp only [Ty.shareableUnder, Bool.and_eq_true] at h
    simp [Ty.bearsCustody_of_shareableUnder h.1, Ty.bearsCustody_of_shareableUnder h.2]
  | .prototype s t, h => by
    simp only [Ty.shareableUnder, Bool.and_eq_true] at h
    simp [Ty.bearsCustody_of_shareableUnder h.1, Ty.bearsCustody_of_shareableUnder h.2]
  | .variant row, h => by
    simp only [Ty.shareableUnder] at h
    simp [Ty.bearsCustody_of_shareableUnder h]
  | .custody _, h => by simp [Ty.shareableUnder, Ty.shareable] at h
  | .natural, _ | .label, _ | .boolean, _ | .variable _, _ | .arrow _ _ _ _, _ | .emptyRow, _
  | .computation _ _ _, _ => rfl

@[simp] theorem Ty.bearsCustody_of_shareable {type : Ty} (h : type.shareable = true) :
    type.bearsCustody = false :=
  Ty.bearsCustody_of_shareableUnder (variables := []) (by simpa using h)

/-- First-order data never bears custody: a response (`Ty.isData`) is custody-free. -/
@[simp] theorem Ty.bearsCustody_of_isData : ∀ {type : Ty}, type.isData = true → type.bearsCustody = false
  | .natural, _ | .label, _ | .boolean, _ | .emptyRow, _ => rfl
  | .field _ member tail, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp [Ty.bearsCustody_of_isData h.1, Ty.bearsCustody_of_isData h.2]
  | .variant row, h => by
    simp only [Ty.isData] at h
    simp [Ty.bearsCustody_of_isData h]
  | .variable _, h | .arrow _ _ _ _, h | .specification _ _, h | .prototype _ _, h | .custody _, h
  | .computation _ _ _, h => by simp [Ty.isData] at h

/-- Custody is held `linear`: a binder of a custody-bearing type is neither droppable (`erased`,
`affine`) nor shareable (`unrestricted`). -/
@[expose, simp] def mustBeLinear (binding : Binding) : Bool :=
  !binding.type.bearsCustody || binding.quantity == .linear

/-- A context is valid when every `unrestricted` binding is shareable and every custody-bearing
binding is `linear` (`mustBeLinear`). -/
@[expose] def validContext (variables : List Nat) (context : Context) : Bool :=
  context.all (fun binding =>
    (binding.quantity != .unrestricted || binding.type.shareableUnder variables) &&
      mustBeLinear binding)

/-- A valid context binds custody `linear`. -/
theorem validContext_custody_linear {variables : List Nat} {context : Context} {binding : Binding}
    (valid : validContext variables context = true) (member : binding ∈ context)
    (custody : binding.type.bearsCustody = true) : binding.quantity = .linear := by
  unfold validContext at valid
  have h := (List.all_eq_true.mp valid) binding member
  simp only [Bool.and_eq_true, mustBeLinear, custody, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact h.2

/-- An `affine` custody binding is refused. -/
theorem validContext_refuses_affine_custody (variables : List Nat) (identity : Nat) (context : Context) :
    validContext variables (⟨.custody identity, .affine⟩ :: context) = false := by
  simp [validContext]

/-- No affine/linear binding can occur twice in a checked computation. This
is syntactic safety; machine conservation and terminal discharge are separate. -/
theorem safe_use_bound (context : Context) (uses : Uses) (binding : Binding) (count : Nat)
    (safe : safeUses context uses = true) (member : (binding,count) ∈ context.zip uses)
    (quantity : binding.quantity = .affine ∨ binding.quantity = .linear) : count ≤ 1 := by
  have all := (Bool.and_eq_true_iff.mp safe).2
  have checked := (List.all_eq_true.mp all) (binding,count) member
  rcases quantity with affine | linear
  · simpa [safeQuantity, affine] using checked
  · simpa [safeQuantity, linear] using checked

/-- Every USED reusable capture is both quantity-unrestricted and transitively
shareable under the explicitly checked future-type premises. -/
theorem reusable_capture_member (variables : List Nat) (context : Context) (uses : Uses)
    (binding : Binding) (count : Nat)
    (qualified : reusableCaptures variables context uses = true)
    (member : (binding,count) ∈ context.zip uses) (used : count ≠ 0) :
    binding.quantity = .unrestricted ∧ binding.type.shareableUnder variables = true := by
  have all := (Bool.and_eq_true_iff.mp qualified).2
  have checked := (List.all_eq_true.mp all) (binding,count) member
  simpa [used] using checked

/-- Reusable captures use only `unrestricted` hypotheses, so no `linear` one. -/
theorem linearFree_of_reusableCaptures {variables : List Nat} {context : Context} {uses : Uses}
    (captures : reusableCaptures variables context uses = true) : linearFree context uses = true := by
  have all := (Bool.and_eq_true_iff.mp captures).2
  unfold linearFree
  rw [List.all_eq_true] at all ⊢
  intro pair member
  have := all pair member
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this ⊢
  rcases this with zero | ⟨unrestricted, _⟩
  · exact .inl zero
  · exact .inr (by simp [unrestricted])

/-- A variable that is not `linear` uses no `linear` hypothesis. -/
theorem linearFree_variableUses {context : Context} {index : Nat} {binding : Binding}
    (found : context[index]? = some binding) (notLinear : binding.quantity ≠ .linear) :
    linearFree context (variableUses context index) = true := by
  unfold linearFree
  rw [List.all_eq_true]
  intro pair member
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem member
  simp only [List.length_zip, variableUses, List.length_map, List.length_range, Nat.min_self] at hj
  simp only [variableUses, List.getElem_zip, List.getElem_map, List.getElem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  by_cases e : j = index
  · subst e
    rename_i hj'
    rw [List.getElem?_eq_getElem hj', Option.some.injEq] at found
    exact .inr (found ▸ notLinear)
  · exact .inl (by simp [e])

/-- An annotation connects source binders to actual checking. `default` must be
resolved by the source frontend using the type/capture discipline. -/
structure LambdaAnnotation where
  domain : Ty
  codomain : Ty
  parameter : Quantity
  reuse : Reuse
  deriving Repr, DecidableEq

/-- Type substitution instantiates future row/type parameters, including their
negative occurrences in binary methods. No variance/subtype oracle is hidden. -/
@[expose] def Ty.instantiate (arguments : Nat → Ty) : Ty → Ty
  | .variable index => arguments index
  | .arrow reuse quantity domain codomain =>
      .arrow reuse quantity (domain.instantiate arguments) (codomain.instantiate arguments)
  | .field name member tail => .field name (member.instantiate arguments) (tail.instantiate arguments)
  | .specification metadata extension =>
      .specification (metadata.instantiate arguments) (extension.instantiate arguments)
  | .prototype spec target => .prototype (spec.instantiate arguments) (target.instantiate arguments)
  | .variant row => .variant (row.instantiate arguments)
  | .computation plan response result =>
      .computation (plan.instantiate arguments) (response.instantiate arguments)
        (result.instantiate arguments)
  | other => other

/-- Families are independently authored expressions over future type variables.
`required` is a bound/interface of future Self, not the final closed Self type. -/
structure ExtensionFamilies where
  inherited : Ty
  required : Ty
  provided : Ty
  deriving Repr, DecidableEq

def ExtensionFamilies.functionType (family : ExtensionFamilies) (futureSelf : Ty) : Ty :=
  .arrow .reusable .unrestricted futureSelf
    (.arrow .reusable .unrestricted family.inherited family.provided)

/-- Heterogeneous composition: inherited→middle→provided. Requirements from
both independently authored extensions remain explicit obligations. -/
structure FamilyMix where
  earlier : ExtensionFamilies
  later : ExtensionFamilies
  intermediate : earlier.provided = later.inherited
  required : List Ty := [earlier.required, later.required]

/-- A recursively constrained binary method keeps the future Self parameter in
both argument and result; a future row remains in the provided target. -/
def binaryMethodFamily : ExtensionFamilies :=
  ⟨.variable 1,
    .field "combine" (.arrow .reusable .unrestricted (.variable 0) (.variable 0)) (.variable 2),
    .field "combine" (.arrow .reusable .unrestricted (.variable 0) (.variable 0)) (.variable 1)⟩

theorem binary_method_changes_with_future_self (first second : Ty) :
    (Ty.arrow .reusable .unrestricted (.variable 0) (.variable 0)).instantiate
      (fun _ => first) = Ty.arrow .reusable .unrestricted first first ∧
    (Ty.arrow .reusable .unrestricted (.variable 0) (.variable 0)).instantiate
      (fun _ => second) = Ty.arrow .reusable .unrestricted second second := ⟨rfl, rfl⟩

end Obend.Core.Ty

end