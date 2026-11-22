module
public import Obend.Core.RecursiveAgreement
public import Obend.Core.Term
public section
namespace Obend.Core.Check
open Obend.Core.Ty Obend.Core.Term
set_option autoImplicit false

/-- More fuel never turns an accepted row into a refused one. -/
theorem Ty.isRow_mono {bounds : Bounds} : ∀ {fuel fuel' : Nat} {type : Ty},
    type.isRow bounds fuel = true → fuel ≤ fuel' → type.isRow bounds fuel' = true
  | 0, _, _, h, _ => by simp [Ty.isRow] at h
  | fuel + 1, fuel', type, h, le => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    cases type with
    | emptyRow => rfl
    | field _ _ tail => simp only [Ty.isRow] at h ⊢; exact Ty.isRow_mono h (by omega)
    | «variable» index =>
      simp only [Ty.isRow] at h ⊢
      split at h
      · exact Ty.isRow_mono h (by omega)
      · cases h
    | _ => simp [Ty.isRow] at h

/-- More fuel never changes a successful lookup. -/
theorem Ty.lookup_mono {bounds : Bounds} : ∀ {fuel fuel' : Nat} {type : Ty} {name : String} {member : Ty},
    type.lookup bounds fuel name = some member → fuel ≤ fuel' → type.lookup bounds fuel' name = some member
  | 0, _, _, _, _, h, _ => by simp [Ty.lookup] at h
  | fuel + 1, fuel', type, name, member, h, le => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    cases type with
    | field prior m tail =>
      simp only [Ty.lookup] at h ⊢
      split at h
      · rw [if_pos ‹_›]; exact h
      · rw [if_neg ‹_›]; exact Ty.lookup_mono h (by omega)
    | «variable» index =>
      simp only [Ty.lookup, Option.bind_eq_bind] at h ⊢
      cases found : bounds.lookup index with
      | none => simp [found] at h
      | some bound => simp only [found, Option.bind_some] at h ⊢; exact Ty.lookup_mono h (by omega)
    | _ => simp [Ty.lookup] at h

/-! ### Row lookup bounded by a visited set instead of fuel

The relation keeps `∃ fuel` (`PartialTyping.get`, `.extend`, `.inject`); a successful
lookup never passes the same bounded variable twice (it would loop), so a walk that
refuses a revisited variable finds exactly what some fuel finds
(`lookupV_iff`, `isRowV_iff`). The bidirectional checker uses these. -/

/-- How many declared bounds a walk has not yet entered. -/
def unvisited (bounds : Bounds) (visited : List Nat) : Nat :=
  (bounds.filter (fun entry => !visited.contains entry.1)).length

theorem filter_length_lt {α : Type} (p q : α → Bool) (sub : ∀ x, q x = true → p x = true) :
    ∀ (l : List α) (x : α), x ∈ l → p x = true → q x = false →
      (l.filter q).length < (l.filter p).length
  | [], _, mem, _, _ => by simp at mem
  | y :: ys, x, mem, px, qx => by
    have le : ∀ (l : List α), (l.filter q).length ≤ (l.filter p).length := by
      intro l
      induction l with
      | nil => simp
      | cons z zs ih =>
        by_cases hq : q z = true
        · simp [List.filter_cons, hq, sub z hq]; omega
        · by_cases hp : p z = true
          · simp [List.filter_cons, hq, hp]; omega
          · simp [List.filter_cons, hq, hp]; omega
    rcases List.mem_cons.mp mem with rfl | mem
    · simp [List.filter_cons, px, qx]
      exact Nat.lt_succ_of_le (le ys)
    · have := filter_length_lt p q sub ys x mem px qx
      by_cases hq : q y = true
      · simp [List.filter_cons, hq, sub y hq]; omega
      · by_cases hp : p y = true
        · simp [List.filter_cons, hq, hp]; omega
        · simp [List.filter_cons, hq, hp]; omega

theorem unvisited_lt {bounds : Bounds} {visited : List Nat} {index : Nat} {bound : Ty}
    (found : bounds.lookup index = some bound) (fresh : visited.contains index = false) :
    unvisited bounds (index :: visited) < unvisited bounds visited := by
  have mem : ∃ entry ∈ bounds, entry.1 = index := by
    clear fresh
    induction bounds with
    | nil => simp at found
    | cons entry rest ih =>
      by_cases h : index = entry.1
      · exact ⟨entry, List.mem_cons_self .., h.symm⟩
      · have : rest.lookup index = some bound := by
          simpa [List.lookup, show (index == entry.1) = false from by simpa using h] using found
        obtain ⟨e, he, hk⟩ := ih this
        exact ⟨e, List.mem_cons_of_mem _ he, hk⟩
  obtain ⟨entry, member, key⟩ := mem
  unfold unvisited
  exact filter_length_lt _ _ (fun x h => by simp_all [List.contains_cons]) bounds entry member
    (by simp only [key]; simpa using fresh) (by simp [key])

/-- Walk a row's explicit fields; at a variable tail, ask `onVariable`. -/
def walkRow {α : Type} (onVariable : Nat → Option α) (onField : String → Ty → Option α)
    (onEnd : Ty → Option α) : Ty → Option α
  | .field prior member tail => (onField prior member).or (walkRow onVariable onField onEnd tail)
  | .variable index => onVariable index
  | other => onEnd other

/-- Field lookup through bounds with a budget of variable entries, refusing to enter a
bounded variable twice. Structural, so the kernel evaluates it. -/
def lookupW (bounds : Bounds) (name : String) : Nat → List Nat → Ty → Option Ty
  | 0, _, type => walkRow (fun _ => none) (fun prior member => if prior = name then some member else none)
      (fun _ => none) type
  | budget + 1, visited, type =>
      walkRow (fun index => if visited.contains index then none else
          (bounds.lookup index).bind (lookupW bounds name budget (index :: visited)))
        (fun prior member => if prior = name then some member else none) (fun _ => none) type

/-- Row-ness through bounds with a budget of variable entries, refusing re-entry. -/
def isRowW (bounds : Bounds) : Nat → List Nat → Ty → Bool
  | 0, _, type => (walkRow (fun _ => none) (fun _ _ => none)
      (fun end_ => if end_ = .emptyRow then some true else none) type).getD false
  | budget + 1, visited, type =>
      (walkRow (fun index => if visited.contains index then none else
          (bounds.lookup index).bind (fun bound => if isRowW bounds budget (index :: visited) bound then some true else none))
        (fun _ _ => none) (fun end_ => if end_ = .emptyRow then some true else none) type).getD false

/-- Field lookup through bounds: each bounded variable is entered at most once, and a
budget of one entry per bound not yet visited is exactly enough. -/
def lookupV (bounds : Bounds) (visited : List Nat) (type : Ty) (name : String) : Option Ty :=
  lookupW bounds name (unvisited bounds visited) visited type

def isRowV (bounds : Bounds) (visited : List Nat) (type : Ty) : Bool :=
  isRowW bounds (unvisited bounds visited) visited type

theorem walkRow_field {α : Type} (onVariable : Nat → Option α) (onField : String → Ty → Option α)
    (onEnd : Ty → Option α) (prior : String) (member tail : Ty) :
    walkRow onVariable onField onEnd (.field prior member tail) =
      (onField prior member).or (walkRow onVariable onField onEnd tail) := by rfl

theorem lookupW_sound {bounds : Bounds} {name : String} {member : Ty} :
    ∀ (budget : Nat) (visited : List Nat) (type : Ty), lookupW bounds name budget visited type = some member →
      ∃ fuel, type.lookup bounds fuel name = some member := by
  intro budget
  induction budget with
  | zero =>
    intro visited type h
    induction type with
    | field prior m tail _ ih =>
      by_cases hit : prior = name
      · simp [lookupW, walkRow_field, hit] at h; exact ⟨1, by simp [Ty.lookup, hit, h]⟩
      · obtain ⟨fuel, l⟩ := ih (by simpa [lookupW, walkRow_field, hit] using h)
        exact ⟨fuel + 1, by simp [Ty.lookup, hit, l]⟩
    | _ => simp [lookupW, walkRow] at h
  | succ budget outer =>
    intro visited type h
    induction type with
    | field prior m tail _ ih =>
      by_cases hit : prior = name
      · simp [lookupW, walkRow_field, hit] at h; exact ⟨1, by simp [Ty.lookup, hit, h]⟩
      · obtain ⟨fuel, l⟩ := ih (by simpa [lookupW, walkRow_field, hit] using h)
        exact ⟨fuel + 1, by simp [Ty.lookup, hit, l]⟩
    | «variable» index =>
      simp only [lookupW, walkRow] at h
      split at h
      · cases h
      · cases found : bounds.lookup index with
        | none => simp [found] at h
        | some bound =>
          simp only [found, Option.bind_some] at h
          obtain ⟨fuel, l⟩ := outer _ _ h
          exact ⟨fuel + 1, by simp [Ty.lookup, found, l]⟩
    | _ => simp [lookupW, walkRow] at h

/-- A successful fuelled lookup is either found by the budgeted walk, or explained by a
variable the walk had already entered, reached again with strictly less fuel. -/
theorem lookupW_complete_aux {bounds : Bounds} {name : String} {member : Ty} :
    ∀ (fuel : Nat) (type : Ty) (visited : List Nat) (budget : Nat), unvisited bounds visited ≤ budget →
      type.lookup bounds fuel name = some member →
      lookupW bounds name budget visited type = some member ∨
        ∃ index ∈ visited, ∃ bound, bounds.lookup index = some bound ∧
          ∃ less, less < fuel ∧ bound.lookup bounds less name = some member := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel outer =>
    intro type visited budget enough h
    cases fuel with
    | zero => simp [Ty.lookup] at h
    | succ fuel =>
      cases type with
      | field prior m tail =>
        by_cases hit : prior = name
        · left; simp [Ty.lookup, hit] at h
          cases budget <;> simp [lookupW, walkRow_field, hit, h]
        · simp only [Ty.lookup, hit, if_false] at h
          rcases outer fuel (Nat.lt_succ_self _) tail visited budget enough h with
            found | ⟨i, hi, b, hb, less, hl, hlook⟩
          · left
            cases budget <;> simp_all [lookupW, walkRow_field]
          · right; exact ⟨i, hi, b, hb, less, by omega, hlook⟩
      | «variable» index =>
        simp only [Ty.lookup, Option.bind_eq_bind] at h
        cases found : bounds.lookup index with
        | none => simp [found] at h
        | some bound =>
          simp only [found, Option.bind_some] at h
          by_cases fresh : visited.contains index = false
          · have shrink := unvisited_lt found fresh
            obtain ⟨budget', rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by omega⟩
            have enough' : unvisited bounds (index :: visited) ≤ budget' := by omega
            have inner : ∀ g, g ≤ fuel → bound.lookup bounds g name = some member →
                lookupW bounds name budget' (index :: visited) bound = some member ∨
                  ∃ i ∈ visited, ∃ b, bounds.lookup i = some b ∧
                    ∃ less, less < fuel + 1 ∧ b.lookup bounds less name = some member := by
              intro g
              induction g using Nat.strongRecOn with
              | ind g innerIH =>
                intro hg hlook
                rcases outer g (by omega) bound (index :: visited) budget' enough' hlook with
                  done | ⟨i, hi, b, hb, less, hl, hlook'⟩
                · exact .inl done
                · rcases List.mem_cons.mp hi with rfl | hi
                  · rw [found] at hb; cases hb
                    exact innerIH less hl (by omega) hlook'
                  · exact .inr ⟨i, hi, b, hb, less, by omega, hlook'⟩
            rcases inner fuel (Nat.le_refl _) h with done | other
            · left
              simp only [lookupW, walkRow, fresh, found, Option.bind_some, Bool.false_eq_true, if_false]
              exact done
            · exact .inr other
          · right
            exact ⟨index, by simpa using fresh, bound, found, fuel, Nat.lt_succ_self _, h⟩
      | _ => simp [Ty.lookup] at h

theorem lookupV_iff (bounds : Bounds) (type : Ty) (name : String) (member : Ty) :
    lookupV bounds [] type name = some member ↔ ∃ fuel, type.lookup bounds fuel name = some member := by
  constructor
  · exact lookupW_sound _ [] type
  · rintro ⟨fuel, h⟩
    rcases lookupW_complete_aux fuel type [] _ (Nat.le_refl _) h with done | ⟨_, hi, _⟩
    · exact done
    · simp at hi

theorem isRowW_sound {bounds : Bounds} :
    ∀ (budget : Nat) (visited : List Nat) (type : Ty), isRowW bounds budget visited type = true →
      ∃ fuel, type.isRow bounds fuel = true := by
  intro budget
  induction budget with
  | zero =>
    intro visited type h
    induction type with
    | emptyRow => exact ⟨1, rfl⟩
    | field n m tail _ ih =>
      obtain ⟨fuel, l⟩ := ih (by simpa [isRowW, walkRow_field] using h)
      exact ⟨fuel + 1, by simp [Ty.isRow, l]⟩
    | _ => simp [isRowW, walkRow] at h
  | succ budget outer =>
    intro visited type h
    induction type with
    | emptyRow => exact ⟨1, rfl⟩
    | field n m tail _ ih =>
      obtain ⟨fuel, l⟩ := ih (by simpa [isRowW, walkRow_field] using h)
      exact ⟨fuel + 1, by simp [Ty.isRow, l]⟩
    | «variable» index =>
      simp only [isRowW, walkRow] at h
      split at h
      · cases h
      · cases found : bounds.lookup index with
        | none => simp [found] at h
        | some bound =>
          simp only [found, Option.bind_some] at h
          split at h
          · rename_i inner
            obtain ⟨fuel, l⟩ := outer _ _ inner
            exact ⟨fuel + 1, by simp [Ty.isRow, found, l]⟩
          · cases h
    | _ => simp [isRowW, walkRow] at h

theorem isRowW_complete_aux {bounds : Bounds} :
    ∀ (fuel : Nat) (type : Ty) (visited : List Nat) (budget : Nat), unvisited bounds visited ≤ budget →
      type.isRow bounds fuel = true →
      isRowW bounds budget visited type = true ∨
        ∃ index ∈ visited, ∃ bound, bounds.lookup index = some bound ∧
          ∃ less, less < fuel ∧ bound.isRow bounds less = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel outer =>
    intro type visited budget enough h
    cases fuel with
    | zero => simp [Ty.isRow] at h
    | succ fuel =>
      cases type with
      | emptyRow => left; cases budget <;> simp [isRowW, walkRow]
      | field n m tail =>
        simp only [Ty.isRow] at h
        rcases outer fuel (Nat.lt_succ_self _) tail visited budget enough h with
          found | ⟨i, hi, b, hb, less, hl, hlook⟩
        · left; cases budget <;> simp_all [isRowW, walkRow_field]
        · right; exact ⟨i, hi, b, hb, less, by omega, hlook⟩
      | «variable» index =>
        simp only [Ty.isRow] at h
        cases found : bounds.lookup index with
        | none => simp [found] at h
        | some bound =>
          simp only [found] at h
          by_cases fresh : visited.contains index = false
          · have shrink := unvisited_lt found fresh
            obtain ⟨budget', rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by omega⟩
            have enough' : unvisited bounds (index :: visited) ≤ budget' := by omega
            have inner : ∀ g, g ≤ fuel → bound.isRow bounds g = true →
                isRowW bounds budget' (index :: visited) bound = true ∨
                  ∃ i ∈ visited, ∃ b, bounds.lookup i = some b ∧
                    ∃ less, less < fuel + 1 ∧ b.isRow bounds less = true := by
              intro g
              induction g using Nat.strongRecOn with
              | ind g innerIH =>
                intro hg hlook
                rcases outer g (by omega) bound (index :: visited) budget' enough' hlook with
                  done | ⟨i, hi, b, hb, less, hl, hlook'⟩
                · exact .inl done
                · rcases List.mem_cons.mp hi with rfl | hi
                  · rw [found] at hb; cases hb
                    exact innerIH less hl (by omega) hlook'
                  · exact .inr ⟨i, hi, b, hb, less, by omega, hlook'⟩
            rcases inner fuel (Nat.le_refl _) h with done | other
            · left
              simp only [isRowW, walkRow, fresh, found, Option.bind_some, Bool.false_eq_true, if_false, done,
                if_true, Option.getD_some]
            · exact .inr other
          · right
            exact ⟨index, by simpa using fresh, bound, found, fuel, Nat.lt_succ_self _, h⟩
      | _ => simp [Ty.isRow] at h

theorem isRowV_iff (bounds : Bounds) (type : Ty) :
    isRowV bounds [] type = true ↔ ∃ fuel, type.isRow bounds fuel = true := by
  constructor
  · exact isRowW_sound _ [] type
  · rintro ⟨fuel, h⟩
    rcases isRowW_complete_aux fuel type [] _ (Nat.le_refl _) h with done | ⟨_, hi, _⟩
    · exact done
    · simp at hi

/-- Finite guarded shareability premises are checked from the declared bounds.
A recursive immutable row may refer to itself; a custody/once member rejects
its shareability even when hidden under that recursive row. -/
@[expose] def Assumptions.valid (assumptions : Assumptions) : Bool :=
  assumptions.shareableVariables.all (fun index =>
    match assumptions.bounds.lookup index with
    | none => false
    | some bound => bound.shareableUnder assumptions.shareableVariables) &&
  -- No rigid variable names an activity, so a type agreement never turns an
  -- activity into a suspendable type or back (`Ty.isComputation` is invariant).
  (assumptions.bounds.all (fun bound => !bound.2.isComputation) &&
  -- A program runs with no hole open: holes are declared only to check a term before its fills
  -- (`PartialTyping.hole`), and the machine has no step for one.
  assumptions.holes.isEmpty)

theorem Assumptions.valid_holes {assumptions : Assumptions} (valid : assumptions.valid = true) :
    assumptions.holes = [] := by
  simp only [Assumptions.valid, Bool.and_eq_true, List.isEmpty_iff] at valid
  exact valid.2.2

/-- Source positions address the annotation of each actual lambda. Missing
annotations are refused, not guessed or silently replaced by Data types. An
injection's position carries the type of its constructor function: domain is
the declared payload type, codomain the declared variant; a sum type is never
guessed from one label. -/
abbrev Annotations := List Nat → Option LambdaAnnotation
structure AnnotatedTerm where
  term : Term
  annotations : Annotations
  assumptions : Assumptions := {}
@[expose] def AnnotatedTerm.erase (source : AnnotatedTerm) : Term := source.term

@[expose] def callable : Ty → Ty
  | .specification _ extension => callable extension
  | other => other

@[expose] def reusableAllowed (assumptions : Assumptions) (reuse : Reuse)
    (context : Context) (uses : Uses) : Bool :=
  reuse != .reusable || reusableCaptures assumptions.shareableVariables context uses

/-- An argument becomes a shared heap thunk, so it is never an activity (rule
`effect-as-argument`); an unrestricted one must also be shareable; one that uses a `linear`
hypothesis goes only to a `linear` parameter (`linearFree`). -/
def argumentAllowed (assumptions : Assumptions) (quantity : Quantity)
    (context : Context) (type : Ty) (uses : Uses) : Bool :=
  !type.isComputation && (quantity == .linear || linearFree context uses) && (quantity != .unrestricted ||
    (type.shareableUnder assumptions.shareableVariables &&
      reusableCaptures assumptions.shareableVariables context uses))

/-- The quantity `q` at which a `case`'s arms bind the payload is allowed for a scrutinee of uses
`uses`: matching passes the payload to the selected arm as an argument (`caseInject` substitutes
it), so this is `argumentAllowed`'s quantity clauses. A scrutinee that uses a `linear` hypothesis
binds a `linear` payload, which the arm uses exactly once; one whose captures are not all reusable
binds at most `affine`; an `unrestricted` payload needs reusable captures (and, per arm, a
shareable payload type: `validContext`). A custody-bearing payload is bound `linear` whatever the
scrutinee: `validContext` includes `mustBeLinear` (`ArmsTyping.custody_linear`). -/
def caseAllowed (assumptions : Assumptions) (quantity : Quantity) (context : Context) (uses : Uses) : Bool :=
  (quantity == .linear || linearFree context uses) &&
    (quantity != .unrestricted || reusableCaptures assumptions.shareableVariables context uses)

/-- The quantity a `case` binds its payload at when no annotation names one: `linear` when an arm
payload bears custody or the scrutinee uses a `linear` hypothesis, `unrestricted` for one whose
captures are reusable when every payload is shareable, `affine` otherwise. -/
def caseQuantity (assumptions : Assumptions) (context : Context) (uses : Uses)
    (shareable : Bool) (custody : Bool := false) : Quantity :=
  if custody || !linearFree context uses then .linear
  else if reusableCaptures assumptions.shareableVariables context uses && shareable then .unrestricted
  else .affine

theorem caseQuantity_allowed (assumptions : Assumptions) (context : Context) (uses : Uses)
    (shareable : Bool) (custody : Bool := false) :
    caseAllowed assumptions (caseQuantity assumptions context uses shareable custody) context uses = true := by
  unfold caseQuantity caseAllowed
  by_cases hc : (custody || !linearFree context uses) = true
  · simp [hc]
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hc
    by_cases hr : (reusableCaptures assumptions.shareableVariables context uses && shareable) = true
    · simp only [hc.1, hc.2, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr]
      simpa using (Bool.and_eq_true_iff.mp hr).1
    · simp [hc.1, hc.2, hr]

def overlay : Ty → Ty → Ty
  | .field name member rest, inherited => .field name member (overlay rest inherited)
  | _, inherited => inherited

@[expose] def primitiveTypes : Primitive → Ty × Ty
  | .add | .multiply | .subtract | .divide | .modulo
  | .bitAnd | .bitOr | .bitXor | .shl | .lshr | .ashr | .qmul32 => (.natural, .natural)
  | .equal | .less | .lessEqual | .slt => (.natural, .boolean)
  | .conjunction => (.boolean, .boolean)
  | .labelEqual => (.label, .boolean)

@[expose] def literalType (_value : String) : Ty := .label

/-- No label names two arms. The machine selects the first arm of a label, so a later
one is dead code, and the relation (which types each arm at its own row entry) would
give it a payload type no scrutinee determines; both judgments refuse it instead. -/
@[expose] def labelsDistinct : List (String × Term) → Bool
  | [] => true
  | (name, _) :: rest => !(rest.any (fun arm => arm.1 == name)) && labelsDistinct rest

/-- Distinctness reads labels only: rewriting the arm bodies keeps it. -/
@[simp] theorem labelsDistinct_map (f : Term → Term) : ∀ arms : List (String × Term),
    labelsDistinct (arms.map fun field => (field.1, f field.2)) = labelsDistinct arms
  | [] => rfl
  | (name, body) :: rest => by
    simp only [List.map_cons, labelsDistinct, List.any_map, labelsDistinct_map f rest]
    rfl

/-- The labels on a row's spine of explicit fields. -/
@[expose] def spineLabels : Ty → List String
  | .field name _ tail => name :: spineLabels tail
  | _ => []

/-- The parameters a destructor's `function` takes, one per name, against the target's row `row` and
uses `uses`: each parameter's domain is the row's member of that name (up to `sameType`) and is not an
activity, its quantity is one the target allows (`caseAllowed`, as a `case` binds its payload: a target
that uses a `linear` hypothesis gives every field to a `linear` parameter), and an `unrestricted`
parameter takes a shareable member. What remains after the last name is `result`. -/
@[expose] def SplitSpine (assumptions : Assumptions) (context : Context) (uses : Uses) (row : Ty) :
    List String → Ty → Ty → Prop
  | [], functionType, result => functionType = result
  | name :: names, functionType, result => ∃ reuse quantity member codomain,
      callable functionType = .arrow reuse quantity member codomain ∧
      (∃ fuel found, row.lookup assumptions.bounds fuel name = some found ∧
        sameType assumptions found member = true) ∧
      member.isComputation = false ∧
      caseAllowed assumptions quantity context uses = true ∧
      validContext assumptions.shareableVariables [⟨member, quantity⟩] = true ∧
      SplitSpine assumptions context uses row names codomain result

/-- `SplitSpine` without the target's uses, its members listed: what the machine's destructor frame
needs of its function. -/
@[expose] def SplitShape (assumptions : Assumptions) (row : Ty) : List String → List Ty → Ty → Ty → Prop
  | [], [], functionType, result => functionType = result
  | name :: names, member :: members, functionType, result => ∃ reuse quantity codomain,
      callable functionType = .arrow reuse quantity member codomain ∧
      (∃ fuel found, row.lookup assumptions.bounds fuel name = some found ∧
        sameType assumptions found member = true) ∧
      member.isComputation = false ∧
      validContext assumptions.shareableVariables [⟨member, quantity⟩] = true ∧
      SplitShape assumptions row names members codomain result
  | _, _, _, _ => False

theorem SplitShape.length {assumptions : Assumptions} {row : Ty} :
    ∀ {names : List String} {members : List Ty} {functionType result : Ty},
      SplitShape assumptions row names members functionType result → members.length = names.length
  | [], [], _, _, _ => rfl
  | _ :: _, _ :: _, _, _, ⟨_, _, _, _, _, _, _, rest⟩ => by simp [SplitShape.length rest]
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- A spine depends on the target's uses only through `caseAllowed`. -/
theorem SplitSpine.transport {assumptions : Assumptions} {context context' : Context} {uses uses' : Uses} {row : Ty}
    (allowed : ∀ q, caseAllowed assumptions q context uses = true → caseAllowed assumptions q context' uses' = true) :
    ∀ {names : List String} {functionType result : Ty},
      SplitSpine assumptions context uses row names functionType result →
      SplitSpine assumptions context' uses' row names functionType result
  | [], _, _, h => h
  | _ :: _, _, _, ⟨r, q, m, c, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨r, q, m, c, h1, h2, h3, allowed q h4, h5, SplitSpine.transport allowed h6⟩

/-- A spine to its machine shape, with the members it names. -/
theorem SplitSpine.shape {assumptions : Assumptions} {context : Context} {uses : Uses} {row : Ty} :
    ∀ {names : List String} {functionType result : Ty},
      SplitSpine assumptions context uses row names functionType result →
      ∃ members, SplitShape assumptions row names members functionType result
  | [], _, _, h => ⟨[], h⟩
  | _ :: _, _, _, ⟨r, q, m, c, h1, h2, h3, _, h5, h6⟩ =>
    let ⟨members, rest⟩ := SplitSpine.shape h6
    ⟨m :: members, r, q, c, h1, h2, h3, h5, rest⟩

/-- A destructor's target row is closed and explicit (its spine of fields ends in `{}`, so no rigid
`Self` can widen it at instantiation), and `names` names every label on it: no field is dropped. -/
@[expose] def SplitCovers (row : Ty) (names : List String) : Bool :=
  row.tail == .emptyRow && (spineLabels row).all names.contains

mutual
/-- A derivation over the independent runtime syntax. This judges partial
computations only: Fix is not evaluated by Lean's definitional conversion. -/
inductive PartialTyping (assumptions : Assumptions) : Context → Term → Ty → Uses → Prop where
  | bound {context : Context} {index : Nat} {binding : Binding} :
      context[index]? = some binding →
      PartialTyping assumptions context (.bound index) binding.type (variableUses context index)
  | natural (context : Context) (value : Nat) :
      PartialTyping assumptions context (.nat value) .natural (zeroUses context)
  | boolean (context : Context) (value : Bool) :
      PartialTyping assumptions context (.boolean value) .boolean (zeroUses context)
  | label (context : Context) (value : String) :
      PartialTyping assumptions context (.label value) (literalType value) (zeroUses context)
  | lambda {context : Context} {body : Term} {annotation : LambdaAnnotation} {uses : Uses} :
      PartialTyping assumptions (⟨annotation.domain, annotation.parameter⟩ :: context)
        body annotation.codomain uses →
      safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) uses = true →
      validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true →
      reusableAllowed assumptions annotation.reuse context uses.tail = true →
      annotation.parameter.fits (uses.headD 0) = true →
      PartialTyping assumptions context (.lam body)
        (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain) uses.tail
  | conversion {context : Context} {term : Term} {actual expected : Ty} {uses : Uses} :
      PartialTyping assumptions context term actual uses → sameType assumptions actual expected = true →
      PartialTyping assumptions context term expected uses
  | application {context : Context} {function argument : Term} {functionType argumentType domain codomain : Ty}
      {functionUses argumentUses : Uses} {reuse : Reuse} {quantity : Quantity} :
      PartialTyping assumptions context function functionType functionUses →
      PartialTyping assumptions context argument argumentType argumentUses →
      callable functionType = .arrow reuse quantity domain codomain → argumentType = domain →
      argumentAllowed assumptions quantity context argumentType argumentUses = true →
      PartialTyping assumptions context (.app function argument) codomain (addUses functionUses argumentUses)
  /-- A record names each field once: a repeated label would be a field no `get` reaches and no
  destructor passes, so it would drop what it holds. -/
  | record {context : Context} {fields : List (String × Term)} {row : Ty} {uses : Uses} :
      FieldsTyping assumptions context fields row uses →
      labelsDistinct fields = true →
      PartialTyping assumptions context (.record fields) row uses
  /-- A projection keeps one component and drops the rest, so (like `reflect`, `metadata` and
  `project`) its target uses no `linear` hypothesis: records and pairs are multiplicative, and a
  sibling holding a `linear` obligation would be dropped. -/
  | get {context : Context} {target : Term} {targetType member : Ty} {uses : Uses} {name : String} {fuel : Nat} :
      PartialTyping assumptions context target targetType uses →
      targetType.lookup assumptions.bounds fuel name = some member →
      linearFree context uses = true →
      PartialTyping assumptions context (.get target name) member uses
  /-- An extension may overwrite a field of its target (`extendRecord` keeps the new one), so the
  target uses no `linear` hypothesis: an overwritten field holding one would be dropped. -/
  | extend {context : Context} {target : Term} {fields : List (String × Term)}
      {targetType row : Ty} {targetUses fieldUses : Uses} {fuel : Nat} :
      PartialTyping assumptions context target targetType targetUses →
      FieldsTyping assumptions context fields row fieldUses →
      labelsDistinct fields = true →
      targetType.isRow assumptions.bounds fuel = true →
      linearFree context targetUses = true →
      PartialTyping assumptions context (.extend target fields) (overlay row targetType) (addUses targetUses fieldUses)
  /-- Applying a specification calls its extension and discards its metadata
  (`applySpecification`), so the metadata uses no `linear` hypothesis. -/
  | specification {context : Context} {metadata extension : Term} {metadataType extensionType : Ty} {mu eu : Uses} :
      PartialTyping assumptions context metadata metadataType mu →
      PartialTyping assumptions context extension extensionType eu →
      metadataType.isComputation = false → extensionType.isComputation = false →
      linearFree context mu = true →
      PartialTyping assumptions context (.specification metadata extension)
        (.specification metadataType extensionType) (addUses mu eu)
  | prototype {context : Context} {spec target : Term} {specType targetType : Ty} {su tu : Uses} :
      PartialTyping assumptions context spec specType su → PartialTyping assumptions context target targetType tu →
      specType.isComputation = false → targetType.isComputation = false →
      PartialTyping assumptions context (.prototype spec target) (.prototype specType targetType) (addUses su tu)
  | reflect {context : Context} {target : Term} {specType targetType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.prototype specType targetType) uses →
      linearFree context uses = true →
      PartialTyping assumptions context (.reflect target) specType uses
  | metadata {context : Context} {target : Term} {metadataType extensionType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.specification metadataType extensionType) uses →
      linearFree context uses = true →
      PartialTyping assumptions context (.metadata target) metadataType uses
  | project {context : Context} {target : Term} {specType targetType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.prototype specType targetType) uses →
      linearFree context uses = true →
      PartialTyping assumptions context (.project target) targetType uses
  | mix {context : Context} {lower upper : Term} {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses} :
      PartialTyping assumptions context lower lowerType lu →
      PartialTyping assumptions context upper upperType uu →
      callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle) →
      callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided) →
      reusableCaptures assumptions.shareableVariables context (addUses lu uu) = true →
      self.shareableUnder assumptions.shareableVariables = true →
      inherited.shareableUnder assumptions.shareableVariables = true →
      middle.shareableUnder assumptions.shareableVariables = true →
      PartialTyping assumptions context (.mix lower upper)
        (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) (addUses lu uu)
  | fix {context : Context} {spec inheritedTerm : Term} {specType inherited target : Ty} {su iu : Uses} :
      PartialTyping assumptions context spec specType su →
      callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target) →
      PartialTyping assumptions context inheritedTerm inherited iu →
      target.shareableUnder assumptions.shareableVariables = true →
      argumentAllowed assumptions .unrestricted context inherited iu = true →
      reusableCaptures assumptions.shareableVariables context su = true →
      PartialTyping assumptions context (.fix spec inheritedTerm) target (addUses su iu)
  | binary {context : Context} {primitive : Primitive} {left right : Term} {input output : Ty} {lu ru : Uses} :
      primitiveTypes primitive = (input, output) →
      PartialTyping assumptions context left input lu → PartialTyping assumptions context right input ru →
      PartialTyping assumptions context (.binary primitive left right) output (addUses lu ru)
  | ifZero {context : Context} {value zero successor : Term} {result : Ty} {vu zu su : Uses} :
      PartialTyping assumptions context value .natural vu → PartialTyping assumptions context zero result zu →
      PartialTyping assumptions (⟨.natural,.unrestricted⟩ :: context) successor result su →
      safeUses (⟨.natural,.unrestricted⟩ :: context) su = true →
      branchesAgree context zu su.tail = true →
      PartialTyping assumptions context (.ifZero value zero successor) result (addUses vu (joinUses zu su.tail))
  | inject {context : Context} {tag : String} {payload : Term} {payloadType row : Ty} {uses : Uses} {fuel : Nat} :
      PartialTyping assumptions context payload payloadType uses →
      row.lookup assumptions.bounds fuel tag = some payloadType →
      payloadType.isComputation = false →
      PartialTyping assumptions context (.inject tag payload) (.variant row) uses
  /-- The arms bind the payload at a quantity `q` the scrutinee allows (`caseAllowed`): a `linear`
  scrutinee's payload is bound `linear` and used exactly once by the selected arm. -/
  | case {context : Context} {scrutinee : Term} {arms : List (String × Term)} {row result : Ty} {su au : Uses}
      {q : Quantity} :
      PartialTyping assumptions context scrutinee (.variant row) su →
      ArmsTyping assumptions context q arms row result au →
      labelsDistinct arms = true →
      caseAllowed assumptions q context su = true →
      PartialTyping assumptions context (.case scrutinee arms) result (addUses su au)
  /-- Exactly one branch runs: uses join (`joinUses`) under `branchesAgree`, so a `linear`
  hypothesis is used equally on both. -/
  | ifBool {context : Context} {condition whenTrue whenFalse : Term} {result : Ty} {cu tu fu : Uses} :
      PartialTyping assumptions context condition .boolean cu →
      PartialTyping assumptions context whenTrue result tu →
      PartialTyping assumptions context whenFalse result fu →
      branchesAgree context tu fu = true →
      PartialTyping assumptions context (.ifBool condition whenTrue whenFalse) result (addUses cu (joinUses tu fu))
  /-- Yield a Plan (a sum of first-order actions); the response is data. -/
  | perform {context : Context} {plan : Term} {planType response : Ty} {uses : Uses} :
      PartialTyping assumptions context plan planType uses →
      planType.isPlan = true → response.isData = true →
      PartialTyping assumptions context (.perform plan) (.computation planType response response) uses
  /-- A pure value where an activity is expected. -/
  | done {context : Context} {value : Term} {planType response result : Ty} {uses : Uses} :
      PartialTyping assumptions context value result uses → result.isComputation = false →
      PartialTyping assumptions context (.done value) (.computation planType response result) uses
  /-- Sequencing: the activity's result selects an arm; every arm is an activity
  over the same plan/response types. This is the only `bind`. -/
  | effectCase {context : Context} {scrutinee : Term} {arms : List (String × Term)}
      {planType response row result : Ty} {su au : Uses} {q : Quantity} :
      PartialTyping assumptions context scrutinee (.computation planType response (.variant row)) su →
      ArmsTyping assumptions context q arms row (.computation planType response result) au →
      result.isComputation = false →
      labelsDistinct arms = true →
      caseAllowed assumptions q context su = true →
      PartialTyping assumptions context (.case scrutinee arms) (.computation planType response result) (addUses su au)
  /-- The consuming record destructor: the target is consumed once, whole, and each field named goes
  to its own parameter of `function` (`SplitSpine`), so a `linear` target's fields are each used
  exactly once; the names are distinct and cover the target's closed row (`SplitCovers`), so no
  field is dropped. The positive counterpart to the projection refusal (`get`'s `linearFree`). -/
  | split {context : Context} {target function : Term} {names : List String}
      {row functionType result : Ty} {tu fu : Uses} :
      PartialTyping assumptions context target row tu →
      PartialTyping assumptions context function functionType fu →
      names.Nodup →
      SplitCovers row names = true →
      SplitSpine assumptions context tu row names functionType result →
      PartialTyping assumptions context (.split target names function) result (addUses tu fu)
  /-- A declared hole `n : ⟨Δ, A⟩` is a term of type `A` over `Δ`, and `.hole n σ` is that term with
`σ[i]` put for variable `i`: it checks as a call of an `n`-ary function whose parameters are the
bindings of `Δ`. Each argument checks at its parameter's type and is passed as `argumentAllowed` lets
an argument reach a parameter of that quantity; the uses are the arguments' uses summed. The filler,
when it comes, discharges the rest (`Obend.Core.Proofs.FillTyping`). -/
  | hole {context : Context} {n : Nat} {σ : List Term} {decl : HoleDecl} {args : List (Term × Binding × Uses)} :
      assumptions.holes.lookup n = some decl →
      σ = args.map (·.1) →
      args.map (·.2.1) = decl.context →
      (∀ arg ∈ args, PartialTyping assumptions context arg.1 arg.2.1.type arg.2.2) →
      (∀ arg ∈ args, argumentAllowed assumptions arg.2.1.quantity context arg.2.1.type arg.2.2 = true) →
      PartialTyping assumptions context (.hole n σ) decl.type
        ((args.map (·.2.2)).foldr addUses (zeroUses context))
inductive FieldsTyping (assumptions : Assumptions) : Context → List (String × Term) → Ty → Uses → Prop where
  | nil (context : Context) : FieldsTyping assumptions context [] .emptyRow (zeroUses context)
  | cons {context : Context} {name : String} {body : Term} {rest : List (String × Term)} {type row : Ty} {bu ru : Uses} :
      PartialTyping assumptions context body type bu → FieldsTyping assumptions context rest row ru →
      type.isComputation = false →
      FieldsTyping assumptions context ((name,body) :: rest) (.field name type row) (addUses bu ru)
/-- Arms in source order build a CLOSED row: with the scrutinee at that variant
row, every label has exactly the arm the machine's first-match lookup selects.
Each body binds the payload at the case's quantity `q`: used as `q` allows (`Quantity.fits`:
exactly once when `linear`), and at a shareable type when `unrestricted` (`validContext`). -/
inductive ArmsTyping (assumptions : Assumptions) : Context → Quantity → List (String × Term) → Ty → Ty → Uses → Prop where
  | nil (context : Context) (q : Quantity) (result : Ty) : ArmsTyping assumptions context q [] .emptyRow result (zeroUses context)
  | cons {context : Context} {q : Quantity} {name : String} {body : Term} {rest : List (String × Term)} {payload row result : Ty} {bu ru : Uses} :
      PartialTyping assumptions (⟨payload,q⟩ :: context) body result bu →
      safeUses (⟨payload,q⟩ :: context) bu = true →
      validContext assumptions.shareableVariables [⟨payload,q⟩] = true →
      q.fits (bu.headD 0) = true →
      ArmsTyping assumptions context q rest row result ru →
      (rest.isEmpty || branchesAgree context bu.tail ru) = true →
      ArmsTyping assumptions context q ((name,body) :: rest) (.field name payload row) result (joinUses bu.tail ru)
end

/-- A choice for every member of a list, as a list of pairs (how a hole's arguments are rebuilt). -/
theorem exists_list_choice {α β : Type} {P : α → β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, P a b) → ∃ m : List (α × β), m.map Prod.fst = l ∧ ∀ p ∈ m, P p.1 p.2
  | [], _ => ⟨[], rfl, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨m, hm, hp⟩ := exists_list_choice l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨(a, b) :: m, by simp [hm], fun p hp' => ?_⟩
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact hb
    · exact hp p hp'

/-- A relation between uses that addition and the zero vector respect holds of two hole sums
(`PartialTyping.hole`) whose arguments it relates. -/
theorem foldr_addUses_rel {R : Uses → Uses → Prop}
    (hadd : ∀ {a a' b b' : Uses}, R a' a → R b' b → R (addUses a' b') (addUses a b))
    {z z' : Uses} (hz : R z' z) {β : Type} (f g : β → Uses) :
    ∀ (l : List β), (∀ x ∈ l, R (g x) (f x)) → R ((l.map g).foldr addUses z') ((l.map f).foldr addUses z)
  | [], _ => hz
  | x :: l, h => by
    simp only [List.map_cons, List.foldr_cons]
    exact hadd (h x List.mem_cons_self) (foldr_addUses_rel hadd hz f g l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- The arguments' uses summed (`PartialTyping.hole`) account for every slot when each does. -/
theorem length_foldr_addUses {n : Nat} : ∀ (us : List Uses) (z : Uses), z.length = n →
    (∀ u ∈ us, u.length = n) → (us.foldr addUses z).length = n
  | [], _, hz, _ => hz
  | u :: us, z, hz, h => by
    simp only [List.foldr_cons, addUses, List.length_zipWith, h u List.mem_cons_self,
      length_foldr_addUses us z hz (fun v hv => h v (List.mem_cons_of_mem _ hv)), Nat.min_self]

structure Inferred (assumptions : Assumptions) (context : Context) (term : Term) where
  type : Ty
  uses : Uses
  derivation : PartialTyping assumptions context term type uses
structure InferredFields (assumptions : Assumptions) (context : Context) (fields : List (String × Term)) where
  type : Ty
  uses : Uses
  derivation : FieldsTyping assumptions context fields type uses
structure Checked (source : AnnotatedTerm) (context : Context) where
  type : Ty
  uses : Uses
  derivation : PartialTyping source.assumptions context source.erase type uses
  safe : safeUses context uses = true
  contextValid : validContext source.assumptions.shareableVariables context = true
  assumptionsValid : source.assumptions.valid = true

/-- Successful checking constructs a derivation for exactly the consumed runtime
term, together with capture/usage premises. This is not preservation/adequacy. -/
theorem checked_erasure (source : AnnotatedTerm) (context : Context)
    (result : Checked source context) :
    PartialTyping source.assumptions context source.erase result.type result.uses := result.derivation

theorem partial_beta_law (body argument : Term) :
    Step (.app (.lam body) argument) (instantiate body argument) := .beta body argument

/-- Reusability is justified by a checked capture premise, not by the immutable
shape of a closure/record wrapper. This holds for every lambda derivation. -/
theorem reusable_lambda_capture_rule {assumptions : Assumptions} {context : Context}
    {body : Term} {annotation : LambdaAnnotation} {uses : Uses}
    (_bodyTyped : PartialTyping assumptions (⟨annotation.domain,annotation.parameter⟩ :: context)
      body annotation.codomain uses)
    (_safe : safeUses (⟨annotation.domain,annotation.parameter⟩ :: context) uses = true)
    (_valid : validContext assumptions.shareableVariables (⟨annotation.domain,annotation.parameter⟩ :: context) = true)
    (captures : reusableAllowed assumptions annotation.reuse context uses.tail = true)
    (reusable : annotation.reuse = .reusable) :
    reusableCaptures assumptions.shareableVariables context uses.tail = true := by
  simpa [reusableAllowed, reusable] using captures

/-- Total logic proves a contextual reduction law despite the discarded
argument being any partial computation, including a divergent Fix. -/
theorem ignores_any_partial_argument (argument : Term) :
    Evaluates (.app (.lam (.nat 7)) argument) (.nat 7) :=
  by
    refine ⟨.next (.beta _ _) ?_, .natural 7⟩
    simpa [instantiate, Term.substitute] using (Steps.refl (.nat 7))

/-! ## Activities: the plan and response types the activity teeth and proofs share -/
def planRow : Ty := .field "write" (.field "after" .natural .emptyRow) .emptyRow
def planType : Ty := .variant planRow
def responseType : Ty := .variant (.field "written" .emptyRow (.field "refused" .emptyRow .emptyRow))

/-- An activity is never shareable, so it is never a fix target, mix operand or
unrestricted binder either. -/
theorem computation_not_shareable (plan response result : Ty) (variables : List Nat) :
    (Ty.computation plan response result).shareableUnder variables = false := rfl

/-! ## Custody is bound `linear` (`mustBeLinear`, gate G1) -/

/-- Every arm of a `case` binds a custody-bearing payload `linear`: `ArmsTyping.cons` requires
`validContext` of the payload binding, which includes `mustBeLinear`. -/
theorem ArmsTyping.custody_linear {assumptions : Assumptions} {context : Context} {q : Quantity} :
    ∀ {arms : List (String × Term)} {row result : Ty} {uses : Uses},
      ArmsTyping assumptions context q arms row result uses → row.bearsCustody = true → q = .linear
  | _, _, _, _, .nil _ _ _, h => by simp at h
  | _, _, _, _, @ArmsTyping.cons _ _ _ _ _ _ payload _ _ _ _ _ _ valid _ rest _, h => by
    simp only [Ty.bearsCustody, Bool.or_eq_true] at h
    rcases h with h | h
    · exact validContext_custody_linear (binding := ⟨payload, q⟩) valid List.mem_cons_self h
    · exact ArmsTyping.custody_linear rest h

/-- `effectCase` binds a custody-bearing result payload `linear`: its arms are an `ArmsTyping`
at the case's quantity (`PartialTyping.effectCase`, second premise). -/
theorem effectCase_custody_linear {assumptions : Assumptions} {context : Context}
    {arms : List (String × Term)} {planType response row result : Ty} {au : Uses} {q : Quantity}
    (armsTyped : ArmsTyping assumptions context q arms row (.computation planType response result) au)
    (custody : row.bearsCustody = true) : q = .linear :=
  ArmsTyping.custody_linear armsTyped custody

/-- A response is first-order data, so `perform` never hands a custody-bearing response to an
`effectCase` arm (before `.perform` is widened beyond `Ty.isData`). -/
theorem perform_response_custody_free {response : Ty} (data : response.isData = true) :
    response.bearsCustody = false :=
  Ty.bearsCustody_of_isData data

/-- A `Checked` term's context binds custody `linear`. -/
theorem Checked.custody_linear {source : AnnotatedTerm} {context : Context} (checked : Checked source context)
    {binding : Binding} (member : binding ∈ context) (custody : binding.type.bearsCustody = true) :
    binding.quantity = .linear :=
  validContext_custody_linear checked.contextValid member custody

/-- A lambda whose parameter is custody-bearing takes it `linear`. -/
theorem lambda_custody_linear {assumptions : Assumptions} {context : Context} {annotation : LambdaAnnotation}
    (valid : validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true)
    (custody : annotation.domain.bearsCustody = true) : annotation.parameter = .linear :=
  validContext_custody_linear (binding := ⟨annotation.domain, annotation.parameter⟩) valid List.mem_cons_self custody

end Obend.Core.Check

end