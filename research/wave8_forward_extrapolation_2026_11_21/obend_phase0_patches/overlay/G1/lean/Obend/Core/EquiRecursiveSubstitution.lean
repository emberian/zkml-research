module
/- Equi-recursive row search, filtered streams, weighted resource safety, nominal residual paths,
   and hereditary substitution bisimulation transport (`Wave C2-Core`, `21 → 1` consolidation).
   LAW-M1 encapsulated (`0` `@[expose] public section`, `0` `@[expose]` attributes). -/
public import Obend.Core.AliasExposure
public import Obend.Core.Assumptions
public import Obend.Core.Check
public import Obend.Core.FieldCongruence
public import Obend.Core.FiniteRowLaws
public import Obend.Core.ResourceSemantics
public import Obend.Core.RowHit
public import Obend.Core.TypeGraph
public import Obend.Core.TypeGraphAlias
import all Obend.Core.Check

public section

/-! ## Consolidated from `lean/Obend/Core/RelationalRowSearch.lean` -/
namespace Obend.Core.RowSearch
set_option autoImplicit false

inductive StepLift {α β γ δ : Type} (R : α → γ → Prop) (S : β → δ → Prop) :
    Step α β → Step γ δ → Prop where
  | stop : StepLift R S .stop .stop
  | emit {p q} : S p q → StepLift R S (.emit p) (.emit q)
  | skip {x y} : R x y → StepLift R S (.skip x) (.skip y)

theorem StepLift.symm {α β γ δ : Type} {R : α → γ → Prop} {S : β → δ → Prop}
    {left : Step α β} {right : Step γ δ} (related : StepLift R S left right) :
    StepLift (fun y x => R x y) (fun q p => S p q) right left := by
  cases related with
  | stop => exact .stop
  | emit h => exact .emit h
  | skip h => exact .skip h

/-- A finite deterministic emission path transports through a relational
scanner simulation, preserving the emission's payload relation. -/
theorem Hit.related {α β γ δ : Type} {left : α → Step α β} {right : γ → Step γ δ}
    {R : α → γ → Prop} {S : β → δ → Prop}
    (closed : ∀ x y, R x y → StepLift R S (left x) (right y))
    {x : α} {p : β} {n : Nat} (hit : Hit left x p n)
    {y : γ} (root : R x y) : ∃ q, Hit right y q n ∧ S p q := by
  induction hit generalizing y with
  | emit x p observed =>
    have next := closed x y root
    rw [observed] at next
    cases observedRight : right y with
    | stop => rw [observedRight] at next; cases next
    | skip other => rw [observedRight] at next; cases next
    | emit q =>
      rw [observedRight] at next
      cases next with
      | emit related => exact ⟨q,.emit y q observedRight,related⟩
  | skip x next p n observed nested ih =>
    have step := closed x y root
    rw [observed] at step
    cases observedRight : right y with
    | stop => rw [observedRight] at step; cases step
    | emit q => rw [observedRight] at step; cases step
    | skip other =>
      rw [observedRight] at step
      cases step with
      | skip related =>
        obtain ⟨q,emitted,payload⟩ := ih related
        exact ⟨q,.skip y other q n observedRight emitted,payload⟩

inductive OptionLift {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop where
  | none : OptionLift R none none
  | some {x y} : R x y → OptionLift R (some x) (some y)

/-- Finite support selection does not interfere with relational scanner
equivalence: both visited searches realize exactly their finite hit paths. -/
theorem find_related {α β γ δ : Type} [DecidableEq α] [DecidableEq γ]
    (left : α → Step α β) (right : γ → Step γ δ)
    (R : α → γ → Prop) (S : β → δ → Prop)
    (closed : ∀ x y, R x y → StepLift R S (left x) (right y))
    (leftNodes : List α) (rightNodes : List γ)
    (leftClosed : ∀ x y, x ∈ leftNodes → left x = .skip y → y ∈ leftNodes)
    (rightClosed : ∀ x y, x ∈ rightNodes → right x = .skip y → y ∈ rightNodes)
    {x : α} {y : γ} (leftRoot : x ∈ leftNodes) (rightRoot : y ∈ rightNodes) (root : R x y) :
    OptionLift S (find left leftNodes x) (find right rightNodes y) := by
  cases one : find left leftNodes x with
  | some p =>
    obtain ⟨n,hit⟩ := find_sound left leftNodes x p one
    obtain ⟨q,other,related⟩ := hit.related closed root
    have found := (find_iff_hit right rightNodes rightClosed rightRoot).mpr ⟨n,other⟩
    rw [found]
    exact .some related
  | none =>
    cases two : find right rightNodes y with
    | none => exact .none
    | some q =>
      obtain ⟨n,hit⟩ := find_sound right rightNodes y q two
      have reversed : ∀ y x, R x y →
          StepLift (fun y x => R x y) (fun q p => S p q) (right y) (left x) := by
        intro y x link
        exact (closed x y link).symm
      obtain ⟨p,other,_⟩ := hit.related reversed root
      have found := (find_iff_hit left leftNodes leftClosed leftRoot).mpr ⟨n,other⟩
      rw [one] at found
      contradiction

end Obend.Core.RowSearch

/-! ## Consolidated from `lean/Obend/Core/ResourceValidity.lean` -/
/- Syntactic validity implies greatest semantic resource safety, with alias-only
cycles safe. This proof is staged for the opaque-safe ResourceSemantics head. -/
namespace Obend.Core.ResourceValidity
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace FS
export Obend.Core.FiniteSafety (Closed Safe)
end FS
set_option autoImplicit false

def observationHead (a : Assumptions) : Head → Bool × List Ty
  | .nominal index => (a.shareableVariables.contains index,[])
  | .unproductive _ => (true,[])
  | .constructor observation =>
    match observation.tag with
    | .natural | .label | .boolean | .emptyRow => (true,[])
    | .arrow reuse _ => (reuse == .reusable,[])
    | .custody _ | .computation => (false,[])
    | .field _ | .specification | .prototype | .variant => (true,observation.children)

/-- The exact finite premise used from `Assumptions.valid`. Keeping this helper
independent of `valid` lets it live below the checker in the eventual graph. -/
def BoundShareable (a : Assumptions) : Prop :=
  ∀ index body, a.shareableVariables.contains index = true →
    a.alias index = some body → body.shareableUnder a.shareableVariables = true

theorem valid_boundShareable {a : Assumptions} (valid : a.valid = true) : BoundShareable a := by
  intro index body listed found
  have checked := (Bool.and_eq_true_iff.mp valid).1
  have entry := (List.all_eq_true.mp checked) index (by simpa using listed)
  simpa [Assumptions.alias_bound found] using entry

private theorem constructor_head_safe (a : Assumptions) (t : Ty)
    (share : t.shareableUnder a.shareableVariables = true) :
    (observationHead a (constructorHead t)).1 = true ∧
      ∀ child ∈ (observationHead a (constructorHead t)).2,
        child.shareableUnder a.shareableVariables = true := by
  cases t <;> simp_all [observationHead,constructorHead,Ty.shareableUnder,Ty.shareable]

theorem walk_head_safe (a : Assumptions) (valid : BoundShareable a)
    (remaining visited : List Nat) (covers : Covers a visited remaining) (t : Ty)
    (share : t.shareableUnder a.shareableVariables = true) :
    (observationHead a (exposeWalk a remaining visited covers t)).1 = true ∧
      ∀ child ∈ (observationHead a (exposeWalk a remaining visited covers t)).2,
        child.shareableUnder a.shareableVariables = true := by
  cases t with
  | «variable» index =>
    simp only [Ty.shareableUnder] at share
    rw [exposeWalk]
    split
    · simp [observationHead]
    · rename_i seen
      split
      · simpa [observationHead] using share
      · rename_i body found
        split
        · simpa [observationHead] using share
        · exact walk_head_safe a valid (remaining.erase index) (index :: visited)
            (covers_step covers index) body (valid index body share found)
  | _ => simpa only [exposeWalk] using constructor_head_safe a _ share
termination_by remaining.length
decreasing_by
  have fresh : index ∈ remaining := (covers index _ (by assumption)).resolve_left (by assumption)
  rw [List.length_erase_of_mem fresh]
  have positive := List.length_pos_of_mem fresh
  omega

/-- A validated syntactic shareability premise supplies a closed greatest-safe
predicate. Alias-only cycles now close safely instead of contradicting it. -/
theorem shareableUnder_safe {a : Assumptions} (valid : BoundShareable a)
    (t : Ty) (share : t.shareableUnder a.shareableVariables = true) : FS.Safe (Obend.Core.ResourceSemantics.graph a) t := by
  refine ⟨fun child => child.shareableUnder a.shareableVariables = true,?_,share⟩
  intro child checked
  exact walk_head_safe a valid _ _ (initial_covers a) child checked

theorem valid_shareableUnder_safe {a : Assumptions} (valid : a.valid = true)
    (t : Ty) (share : t.shareableUnder a.shareableVariables = true) : FS.Safe (Obend.Core.ResourceSemantics.graph a) t :=
  shareableUnder_safe (valid_boundShareable valid) t share

theorem valid_shareableUnder_shareable {a : Assumptions} (valid : a.valid = true)
    (t : Ty) (share : t.shareableUnder a.shareableVariables = true) :
    Obend.Core.ResourceSemantics.shareable a t = true :=
  (Obend.Core.ResourceSemantics.shareable_iff a t).mpr
    (valid_shareableUnder_safe valid t share)

end Obend.Core.ResourceValidity

/-! ## Consolidated from `lean/Obend/Core/RowAlphabet.lean` -/
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Every label collected by the finite alphabet scanner has a visible first
emission, using exactly the same finite visitation budget. -/
public theorem scanLabels_mem_true_emits (a : Assumptions) (remaining : List Ty)
    (row : Ty) (label : String) (presentLabel : label ∈ scanLabels a remaining row) :
    ∃ member tail, scanStream a remaining label true row = .emit member tail := by
  rw [scanLabels] at presentLabel
  split at presentLabel
  · rename_i observation exposed
    split at presentLabel
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at presentLabel
      · rename_i present
        rcases (mem_insertLabel name label _).mp presentLabel with same | nested
        · subst label
          refine ⟨member, tail, ?_⟩
          rw [scanStream, exposed]
          simp [present]
        · by_cases same : name = label
          · subst label
            refine ⟨member, tail, ?_⟩
            rw [scanStream, exposed]
            simp [present]
          · obtain ⟨found, rest, emitted⟩ :=
              scanLabels_mem_true_emits a (remaining.erase row) tail label nested
            refine ⟨found, rest, ?_⟩
            rw [scanStream, exposed]
            simpa [present, same] using emitted
      · simp_all
    · simp_all
  · simp_all
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- The row alphabet is precisely the set of labels with a visible emission. -/
public theorem labels_iff_true_emits (a : Assumptions) (row : Ty) (label : String) :
    label ∈ labels a row ↔ ∃ member tail, streamStep a row label true = .emit member tail := by
  constructor
  · exact scanLabels_mem_true_emits a (support a row row) row label
  · rintro ⟨member, tail, emitted⟩
    exact Obend.Core.TypeGraph.scan_emission_label a (support a row row) label true
      row member tail emitted

end Obend.Core.RecursiveRows

/-! ## Consolidated from `lean/Obend/Core/SubstitutionExposure.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- What an instance must discharge. Non-rigid variables are left alone and keep their
bounds (which mention no rigid variable); each rigid variable's image supports its bound
(every member the bound discloses, at the bound's member type instantiated, and row-ness),
is shareable exactly when the template assumed it shareable, and is never an activity. -/
public structure Discharges (σ : Nat → Ty) (template instance_ : Assumptions) (extra : Nat) : Prop where
  fixed : ∀ j, j ∉ template.rigid → σ j = .variable j
  bounds : ∀ j, j ∉ template.rigid → instance_.bounds.lookup j = template.bounds.lookup j
  aliases : ∀ j, j ∉ template.rigid → instance_.alias j = template.alias j
  closed : ∀ j bound, j ∉ template.rigid → template.bounds.lookup j = some bound → bound.instantiate σ = bound
  lookup : ∀ k bound, k ∈ template.rigid → template.bounds.lookup k = some bound →
    ∀ fuel name member, bound.lookup template.bounds fuel name = some member →
      (σ k).lookup instance_.bounds (fuel + extra) name = some (member.instantiate σ)
  row : ∀ k bound, k ∈ template.rigid → template.bounds.lookup k = some bound →
    ∀ fuel, bound.isRow template.bounds fuel = true → (σ k).isRow instance_.bounds (fuel + extra) = true
  shareable : ∀ j, (σ j).shareableUnder instance_.shareableVariables = template.shareableVariables.contains j
  custody : ∀ j, (σ j).bearsCustody = false
  pure : ∀ j, (σ j).isComputation = false
  /-- A hole the template declares, the instance declares at the instantiated types. -/
  holes : ∀ n decl, template.holes.lookup n = some decl →
    instance_.holes.lookup n = some ⟨decl.context.map fun b => ⟨b.type.instantiate σ, b.quantity⟩,
      decl.type.instantiate σ⟩

variable {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}

public theorem exposure_alias_not_rigid {assumptions : Assumptions} {index : Nat} {body : Ty}
    (found : assumptions.alias index = some body) : index ∉ assumptions.rigid := by
  intro member
  have rigid : assumptions.rigid.contains index = true := by simpa using member
  rw [Assumptions.alias_rigid rigid] at found
  cases found

public theorem Discharges.aliasChain_instantiate
    (D : Discharges σ template instance_ extra) {start finish : Ty} {path : List Nat}
    (chain : AliasChain template start path finish) :
    AliasChain instance_ (start.instantiate σ) path (finish.instantiate σ) := by
  induction chain with
  | nil t => exact .nil _
  | @cons index body finish path found pure chain ih =>
    have nonrigid := exposure_alias_not_rigid found
    have closed := D.closed index body nonrigid (Assumptions.alias_bound found)
    have target : instance_.alias index = some body := (D.aliases index nonrigid).trans found
    simpa only [Ty.instantiate, D.fixed index nonrigid, closed] using
      (AliasChain.cons target pure (by simpa only [closed] using ih))

public theorem aliasChain_expose {assumptions : Assumptions} {start finish : Ty}
    {path : List Nat} (chain : AliasChain assumptions start path finish) :
    expose assumptions start = expose assumptions finish := by
  induction chain with
  | nil => rfl
  | cons found pure chain ih => exact (expose_alias _ _ _ found pure).trans ih

public theorem aliasChain_path_nonrigid {start finish : Ty} {path : List Nat}
    (chain : AliasChain template start path finish) :
    ∀ index ∈ path, index ∉ template.rigid := by
  induction chain with
  | nil => simp
  | @cons index body finish path found pure chain ih =>
    intro other present
    rcases List.mem_cons.mp present with same | inside
    · subst other; exact exposure_alias_not_rigid found
    · exact ih other inside

/-- Exposure commutes with a discharging substitution. Nominal observations
are re-exposed because the image of a rigid variable can be an arbitrary row.
Transparent cycles retain their original representative. -/
public theorem Discharges.expose_instantiate
    (D : Discharges σ template instance_ extra) (t : Ty) :
    expose instance_ (t.instantiate σ) =
      match expose template t with
      | .constructor c => .constructor ⟨c.tag, c.children.map (Ty.instantiate σ)⟩
      | .nominal index => expose instance_ (σ index)
      | .unproductive representative => .unproductive representative := by
  obtain ⟨path, finish, chain, distinct, fresh, stopped⟩ :=
    exposeWalk_trace template (template.bounds.map Prod.fst) [] (initial_covers template) t
  change Stopped template (visitPath [] path) finish (expose template t) at stopped
  have mapped := D.aliasChain_instantiate chain
  have endpoint := aliasChain_expose mapped
  generalize sourceResult : expose template t = result at stopped ⊢
  cases stopped with
  | productive terminal nonvariable =>
    rw [endpoint]
    cases finish <;> simp_all [Ty.instantiate, expose, exposeWalk, constructorHead]
  | @unbound index notVisited absent =>
    simpa only [Ty.instantiate] using endpoint
  | @activity index body notVisited found blocked =>
    simpa only [Ty.instantiate] using endpoint
  | @cycle index repeated =>
    have inPath : index ∈ path := by simpa only [visitPath_reverse, List.append_nil,
      List.mem_reverse] using repeated
    have fixed : σ index = .variable index := D.fixed index (aliasChain_path_nonrigid chain index inPath)
    have replay := exposeWalk_replay mapped distinct (instance_.bounds.map Prod.fst) []
      (initial_covers instance_) (by simp)
    change expose instance_ (t.instantiate σ) =
      exposeWalk instance_ _ (visitPath [] path) _ ((Ty.variable index).instantiate σ) at replay
    rw [replay]
    simp only [Ty.instantiate, fixed]
    rw [exposeWalk]
    simp only [repeated, ↓reduceDIte]

public theorem Discharges.expose_instantiate_constructor
    (D : Discharges σ template instance_ extra) {t : Ty} {c : Constructor}
    (observed : expose template t = .constructor c) :
    expose instance_ (t.instantiate σ) =
      .constructor ⟨c.tag, c.children.map (Ty.instantiate σ)⟩ := by
  rw [D.expose_instantiate t, observed]

public theorem Discharges.expose_instantiate_nominal
    (D : Discharges σ template instance_ extra) {t : Ty} {index : Nat}
    (observed : expose template t = .nominal index) :
    expose instance_ (t.instantiate σ) = expose instance_ (σ index) := by
  rw [D.expose_instantiate t, observed]

public theorem Discharges.expose_instantiate_unproductive
    (D : Discharges σ template instance_ extra) {t : Ty} {representative : Nat}
    (observed : expose template t = .unproductive representative) :
    expose instance_ (t.instantiate σ) = .unproductive representative := by
  rw [D.expose_instantiate t, observed]

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/WeightedResource.lean` -/
namespace Obend.Core.FiniteSafety
open Obend.Core.FinitePresentation (Graph Bisimilar)
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

theorem children_right_member {α : Type} {R : α → α → Prop} {xs ys : List α}
    (related : Children R xs ys) {y : α} (present : y ∈ ys) :
    ∃ x ∈ xs, R x y := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Children]
  | cons x xs ih =>
    cases ys with
    | nil => simp at present
    | cons z zs =>
      rcases List.mem_cons.mp present with rfl | nested
      · exact ⟨x,by simp,related.1⟩
      · obtain ⟨original,inside,link⟩ := ih related.2 nested
        exact ⟨original,List.mem_cons_of_mem _ inside,link⟩

/-- Greatest resource safety is invariant under ordinary graph bisimulation. -/
theorem safe_of_bisimilar {α : Type} (g : Graph α Bool) {x y : α}
    (related : Bisimilar g x y) (safe : Safe g x) : Safe g y := by
  let P : α → Prop := fun target => ∃ source, Safe g source ∧ Bisimilar g source target
  refine ⟨P,?_,⟨x,safe,related⟩⟩
  intro target h
  obtain ⟨source,sourceSafe,link⟩ := h
  obtain ⟨good,children⟩ := safe_closed g source sourceSafe
  obtain ⟨labels,nested⟩ := Obend.Core.FinitePresentation.bisimilar_closed g _ _ link
  refine ⟨labels.symm.trans good,?_⟩
  intro child inside
  obtain ⟨original,present,related⟩ := children_right_member nested inside
  exact ⟨original,children original present,related⟩

theorem safe_bisimilar_iff {α : Type} (g : Graph α Bool) {x y : α}
    (related : Bisimilar g x y) : Safe g x ↔ Safe g y :=
  ⟨safe_of_bisimilar g related,
    safe_of_bisimilar g ((Obend.Core.FinitePresentation.bisimilar_equivalence g).symm related)⟩

end Obend.Core.FiniteSafety

namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

/-- Interpret nominal leaves with arbitrary resource values. Rows account for
their nominal residual in addition to their visible and retained member streams.
The source shareability annotation is deliberately not read by this interpretation. -/
def weightedResourceLabel (nominal : Nat → Bool) : Label → Bool
  | .nominal index => nominal index
  | .unproductive _ => true
  | .ordinary (.arrow reuse _) _ => reuse == .reusable
  | .ordinary (.custody _) _ | .ordinary .computation _ => false
  | .row _ (.nominal index) _ => nominal index
  | _ => true

def weightedResourceDependencies : Label → Bool
  | .ordinary .specification _ | .ordinary .prototype _ | .ordinary .variant _ => true
  | .ordinary _ _ => false
  | _ => true

def weightedResourceGraph (a : Assumptions) (nominal : Nat → Bool) :
    Obend.Core.FinitePresentation.Graph Node Bool where
  label := fun node => weightedResourceLabel nominal ((graph a).label node)
  successors := fun node => if weightedResourceDependencies ((graph a).label node)
    then (graph a).successors node else []

/-- Source equivalence transports to every weighted resource interpretation.
This separates the coinductive resource argument from scanner substitution. -/
theorem weightedResource_bisimilar (a : Assumptions) (nominal : Nat → Bool)
    {x y : Node} (related : FP.Bisimilar (graph a) x y) :
    FP.Bisimilar (weightedResourceGraph a nominal) x y := by
  refine ⟨FP.Bisimilar (graph a),?_,related⟩
  intro left right link
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ link
  refine ⟨congrArg (weightedResourceLabel nominal) labels,?_⟩
  change Obend.Core.FiniteBisimulation.Children _
    (if weightedResourceDependencies ((graph a).label left) then (graph a).successors left else [])
    (if weightedResourceDependencies ((graph a).label right) then (graph a).successors right else [])
  rw [← labels]
  cases weightedResourceDependencies ((graph a).label left) <;>
    simp only [Bool.false_eq_true,↓reduceIte]
  · trivial
  · exact children

theorem equivalent_weighted_resource {a : Assumptions} {left right : Ty}
    (nominal : Nat → Bool) (related : Equivalent a left right) :
    Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type left) ↔
      Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type right) :=
  Obend.Core.FiniteSafety.safe_bisimilar_iff _ (weightedResource_bisimilar a nominal related)

end Obend.Core.TypeGraph

/-! ## Consolidated from `lean/Obend/Core/ResourcePredicate.lean` -/
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Raw resource dependencies of a productive type constructor. -/
def resourceObservation (c : Constructor) : Bool × List Ty :=
  match c.tag with
  | .natural | .label | .boolean | .emptyRow => (true,[])
  | .arrow reuse _ => (reuse == .reusable,[])
  | .custody _ | .computation => (false,[])
  | .field _ | .specification | .prototype | .variant => (true,c.children)

/-- A local resource invariant, independent of the scanner's finite support.
This interface covers both source safety and safety after substitution. -/
structure ResourcePredicate (a : Assumptions) (nominal : Nat → Bool) (Q : Ty → Prop) : Prop where
  productive : ∀ {t c}, expose a t = .constructor c → Q t →
    (resourceObservation c).1 = true ∧ ∀ child ∈ (resourceObservation c).2, Q child
  nominal : ∀ {t j}, expose a t = .nominal j → Q t → nominal j = true

theorem ResourcePredicate.field {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) {row member tail : Ty} {name : String}
    (observed : expose a row = .constructor ⟨.field name,[member,tail]⟩) (safe : Q row) :
    Q member ∧ Q tail := by
  simpa [resourceObservation] using P.productive observed safe

theorem ResourcePredicate.scanStream {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) (remaining : List Ty)
    (label : String) (first : Bool) (row member tail : Ty) (safe : Q row)
    (emitted : Obend.Core.RecursiveRows.scanStream a remaining label first row = .emit member tail) :
    Q member ∧ Q tail := by
  rw [Obend.Core.RecursiveRows.scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name,[fieldMember,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have childrenSafe := P.field exposed safe
      split at emitted
      · split at emitted
        · cases emitted; exact childrenSafe
        · exact P.scanStream (remaining.erase row) label first fieldTail member tail childrenSafe.2 emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

def ResourceTailPredicate (nominal : Nat → Bool) (Q : Ty → Prop) : RR.Tail → Prop
  | .nominal index => nominal index = true
  | .nonRow t => Q t
  | _ => True

theorem ResourcePredicate.scanResidual {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) (remaining : List Ty) (row : Ty) (safe : Q row) :
    ResourceTailPredicate nominal Q (Obend.Core.RecursiveRows.scanResidual a remaining row) := by
  rw [Obend.Core.RecursiveRows.scanResidual]
  split
  · rename_i index exposed
    exact P.nominal exposed safe
  · trivial
  · rename_i observation exposed
    split
    · trivial
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name,[member,tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have childrenSafe := P.field exposed safe
      split
      · exact P.scanResidual (remaining.erase row) tail childrenSafe.2
      · trivial
    · exact safe
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- A resource invariant closes over the quotient row graph. This is the shared
coinductive bridge used for ordinary safety and substitution-image safety. -/
theorem ResourcePredicate.weighted_safe {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) {t : Ty} (safe : Q t) :
    Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type t) := by
  let Nodes : Node → Prop := fun node => match node with
    | .type row | .stream row _ _ => Q row
  refine ⟨Nodes,?_,safe⟩
  intro node good
  cases node with
  | stream row label first =>
    cases emitted : RR.streamStep a row label first with
    | «end» ending => simp [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies]
    | emit member tail =>
      have children := P.scanStream _ label first row member tail good emitted
      simpa [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies,Nodes] using children
  | type row =>
    have good : Q row := good
    cases exposed : expose a row with
    | nominal index =>
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies,P.nominal exposed good]
    | unproductive representative =>
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies]
    | constructor observation =>
      have closed := P.productive exposed good
      by_cases isRow : rowTag observation.tag = true
      · have residualSafe : ResourceTailPredicate nominal Q (RR.residual a row) :=
          P.scanResidual (support a row row) row good
        have root : weightedResourceLabel nominal
            (.row (RR.labels a row) (tailKind (RR.residual a row)) (RR.shareable a row)) = true := by
          cases ending : RR.residual a row with
          | nominal index =>
            simpa [ending,ResourceTailPredicate,weightedResourceLabel,tailKind] using residualSafe
          | _ => rfl
        refine ⟨?_,?_⟩
        · simpa [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation] using root
        · intro child inside
          change child ∈ (weightedResourceGraph a nominal).successors (.type row) at inside
          simp only [weightedResourceGraph,graph,observe,exposed,isRow,↓reduceIte,
            rowObservation,weightedResourceDependencies] at inside
          change child ∈ rowChildren a row at inside
          rcases List.mem_append.mp inside with stream | ending
          · obtain ⟨label,_,rfl⟩ := List.mem_map.mp stream
            exact good
          · cases result : RR.residual a row <;> simp [tailChildren,result] at ending
            subst child
            simpa [result,ResourceTailPredicate,Nodes] using residualSafe
      · cases tag : observation.tag <;>
          simp_all [weightedResourceGraph,graph,observe,weightedResourceLabel,
            weightedResourceDependencies,resourceObservation,rowTag,Nodes]

end Obend.Core.TypeGraph

/-! ## Consolidated from `lean/Obend/Core/ResourceSubstitution.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace RS
export Obend.Core.ResourceSemantics (head graph shareable shareable_iff shareable_eq_of_expose_eq)
end RS
namespace FS
export Obend.Core.FiniteSafety (Safe Closed safe_closed)
end FS
set_option autoImplicit false

/-- Productive observations commute with substitution, including their resource
dependencies. Arrow children are type-equality dependencies, not resource ones. -/
theorem Discharges.resource_head_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) {t : Ty} {c : Constructor}
    (observed : expose a t = .constructor c) :
    RS.head b (t.instantiate σ) =
      ((RS.head a t).1,(RS.head a t).2.map (Ty.instantiate σ)) := by
  have mapped := D.expose_instantiate t
  rw [observed] at mapped
  cases tag : c.tag <;> simp [RS.head,observed,mapped,tag]

/-- Source safety is preserved, rather than reflected: substituting a safe
type for an unconstrained nominal variable can legitimately gain shareability.
The proof closes a greatest-safe predicate over mapped source states. -/
theorem Discharges.resource_safe_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {t : Ty} (sourceSafe : FS.Safe (RS.graph a) t) :
    FS.Safe (RS.graph b) (t.instantiate σ) := by
  let P : Ty → Prop := fun image => FS.Safe (RS.graph b) image ∨
    ∃ source, FS.Safe (RS.graph a) source ∧ image = source.instantiate σ
  have prior (image : Ty) (safe : FS.Safe (RS.graph b) image) :
      (RS.graph b).label image = true ∧
        ∀ child ∈ (RS.graph b).successors image, P child := by
    obtain ⟨good,children⟩ := FS.safe_closed (RS.graph b) image safe
    exact ⟨good,fun child inside => Or.inl (children child inside)⟩
  refine ⟨P,?_,Or.inr ⟨t,sourceSafe,rfl⟩⟩
  intro image related
  rcases related with safe | ⟨source,safe,rfl⟩
  · exact prior image safe
  · obtain ⟨good,children⟩ := FS.safe_closed (RS.graph a) source safe
    have mapped := D.expose_instantiate source
    cases observed : expose a source with
    | nominal index =>
      have listed : a.shareableVariables.contains index = true := by
        simpa [RS.graph,RS.head,observed] using good
      have imageShare : (σ index).shareableUnder b.shareableVariables = true :=
        (D.shareable index).trans listed
      have imageSafe := Obend.Core.ResourceValidity.valid_shareableUnder_shareable valid (σ index) imageShare
      have sameHead : expose b (source.instantiate σ) = expose b (σ index) := by
        simpa only [observed] using mapped
      have transported : RS.shareable b (source.instantiate σ) = true :=
        (RS.shareable_eq_of_expose_eq sameHead).trans imageSafe
      exact prior _ ((RS.shareable_iff _ _).mp transported)
    | unproductive representative =>
      have sameHead : expose b (source.instantiate σ) = .unproductive representative := by
        simpa only [observed] using mapped
      simp [RS.graph,RS.head,sameHead]
    | constructor c =>
      have heads := D.resource_head_instantiate observed
      refine ⟨?_,?_⟩
      · change (RS.head b (source.instantiate σ)).1 = true
        rw [heads]
        exact good
      · intro child inside
        change child ∈ (RS.head b (source.instantiate σ)).2 at inside
        rw [heads] at inside
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp inside
        exact Or.inr ⟨original,children original present,rfl⟩

theorem Discharges.semantic_shareable_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {t : Ty} (share : RS.shareable a t = true) :
    RS.shareable b (t.instantiate σ) = true :=
  (RS.shareable_iff _ _).mpr
    (D.resource_safe_instantiate valid ((RS.shareable_iff _ _).mp share))

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/RowResourceSafety.lean` -/
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

theorem exposed_field_shareable {a : Assumptions} {row member tail : Ty} {name : String}
    (observed : expose a row = .constructor ⟨.field name,[member,tail]⟩)
    (share : shareable a row = true) : shareable a member = true ∧ shareable a tail = true := by
  have closed := (shareable_unfold a row).mp share
  simpa [Obend.Core.ResourceSemantics.head,observed] using closed

theorem scanStream_emit_shareable (a : Assumptions) (remaining : List Ty)
    (label : String) (first : Bool) (row member tail : Ty)
    (share : shareable a row = true)
    (emitted : scanStream a remaining label first row = .emit member tail) :
    shareable a member = true ∧ shareable a tail = true := by
  rw [scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name,[fieldMember,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have safe := exposed_field_shareable exposed share
      split at emitted
      · split at emitted
        · cases emitted; exact safe
        · exact scanStream_emit_shareable a (remaining.erase row) label first
            fieldTail member tail safe.2 emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem streamStep_emit_shareable {a : Assumptions} {row member tail : Ty}
    {label : String} {first : Bool} (share : shareable a row = true)
    (emitted : streamStep a row label first = .emit member tail) :
    shareable a member = true ∧ shareable a tail = true :=
  scanStream_emit_shareable a _ label first row member tail share emitted

def TailShareable (a : Assumptions) : Tail → Prop
  | .nominal index => a.shareableVariables.contains index = true
  | .nonRow t => shareable a t = true
  | _ => True

theorem scanResidual_shareable (a : Assumptions) (remaining : List Ty) (row : Ty)
    (share : shareable a row = true) : TailShareable a (scanResidual a remaining row) := by
  rw [scanResidual]
  split
  · rename_i index exposed
    have good := (shareable_unfold a row).mp share
    simpa [TailShareable,Obend.Core.ResourceSemantics.head,exposed] using good
  · trivial
  · rename_i observation exposed
    split
    · trivial
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name,[member,tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have safe := exposed_field_shareable exposed share
      split
      · exact scanResidual_shareable a (remaining.erase row) tail safe.2
      · trivial
    · exact share
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem residual_shareable {a : Assumptions} {row : Ty} (share : shareable a row = true) :
    TailShareable a (residual a row) := scanResidual_shareable a _ row share

end Obend.Core.RecursiveRows

namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Raising the interpretation of nominal resource leaves preserves safety.
This justifies omitting source-shareable entries after substitution. -/
theorem weighted_safe_of_shareable (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    {t : Ty} (share : RR.shareable a t = true) :
    Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type t) := by
  let P : Node → Prop := fun node => match node with
    | .type row | .stream row _ _ => RR.shareable a row = true
  refine ⟨P,?_,share⟩
  intro node safe
  cases node with
  | stream row label first =>
    cases emitted : RR.streamStep a row label first with
    | «end» ending => simp [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies]
    | emit member tail =>
      have children := Obend.Core.RecursiveRows.streamStep_emit_shareable safe emitted
      simpa [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies,P] using children
  | type row =>
    have safe : RR.shareable a row = true := safe
    have closed := (Obend.Core.RecursiveRows.shareable_unfold a row).mp safe
    cases exposed : expose a row with
    | nominal index =>
      have listed : a.shareableVariables.contains index = true := by
        simpa [Obend.Core.ResourceSemantics.head,exposed] using closed
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies,raised index listed]
    | unproductive representative =>
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies]
    | constructor observation =>
      by_cases isRow : rowTag observation.tag = true
      · have residualSafe := Obend.Core.RecursiveRows.residual_shareable safe
        have root : weightedResourceLabel nominal
            (.row (RR.labels a row) (tailKind (RR.residual a row)) (RR.shareable a row)) = true := by
          cases ending : RR.residual a row with
          | nominal index =>
            have listed : a.shareableVariables.contains index = true := by
              simpa [ending,Obend.Core.RecursiveRows.TailShareable] using residualSafe
            exact raised index listed
          | _ => rfl
        refine ⟨?_,?_⟩
        · simpa [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation] using root
        · intro child inside
          change child ∈ (weightedResourceGraph a nominal).successors (.type row) at inside
          simp only [weightedResourceGraph,graph,observe,exposed,isRow,↓reduceIte,
            rowObservation,weightedResourceDependencies] at inside
          change child ∈ rowChildren a row at inside
          rcases List.mem_append.mp inside with stream | ending
          · obtain ⟨label,_,rfl⟩ := List.mem_map.mp stream
            exact safe
          · cases result : RR.residual a row <;> simp [tailChildren,result] at ending
            subst child
            simpa [result,Obend.Core.RecursiveRows.TailShareable] using residualSafe
      · cases tag : observation.tag <;>
          simp_all [weightedResourceGraph,graph,observe,weightedResourceLabel,
            weightedResourceDependencies,Obend.Core.ResourceSemantics.head,rowTag,P]

end Obend.Core.TypeGraph

/-! ## Consolidated from `lean/Obend/Core/SubstitutionResidual.lean` -/
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

public theorem residual_exposed_field {a : Assumptions} {row member tail : Ty} {name : String}
    (observed : expose a row = .constructor ⟨.field name, [member, tail]⟩) :
    residual a row = residual a tail := by
  have heads : expose a row = expose a (.field name member tail) :=
    observed.trans (raw_field_observation a name member tail).symm
  exact (residual_expose_eq a row (.field name member tail) _ observed heads rfl).trans
    (residual_field a name member tail)

public theorem scanStream_residual_emit
    (a : Assumptions) (remaining : List Ty) (row : Ty) (label : String) (first : Bool)
    (member tail : Ty) (emitted : scanStream a remaining label first row = .emit member tail) :
    residual a row = residual a tail := by
  rw [scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i name current fieldTail tag children
      have shape : observation = ⟨.field name, [current, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have step := residual_exposed_field exposed
      split at emitted
      · rename_i present
        split at emitted
        · cases emitted
          exact step
        · exact step.trans (scanStream_residual_emit a (remaining.erase row)
            fieldTail label first member tail emitted)
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

public theorem residual_emit {a : Assumptions} {row : Ty} {label : String} {first : Bool}
    {member tail : Ty} (emitted : streamStep a row label first = .emit member tail) :
    residual a row = residual a tail :=
  scanStream_residual_emit a _ row label first member tail emitted

public theorem residual_skip {a : Assumptions} {row tail : Ty} {label : String} {first : Bool}
    (skipped : Obend.Core.TypeGraph.RowHit.step a label first row = .skip tail) :
    residual a row = residual a tail := by
  rw [Obend.Core.TypeGraph.RowHit.step] at skipped
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at skipped
      · contradiction
      · cases skipped
        exact residual_exposed_field exposed
    · contradiction
  · contradiction

/-- Residuals retain raw syntax only for non-row terminals. Those payloads
are compared by the type graph rather than by syntactic equality. -/
public inductive ResidualRelated (a : Assumptions) : Tail → Tail → Prop where
  | closed : ResidualRelated a .closed .closed
  | productiveCycle : ResidualRelated a .productiveCycle .productiveCycle
  | nominal (index : Nat) : ResidualRelated a (.nominal index) (.nominal index)
  | unproductive (index : Nat) : ResidualRelated a (.unproductive index) (.unproductive index)
  | nonRow {left right : Ty} : Obend.Core.TypeGraph.Equivalent a left right →
      ResidualRelated a (.nonRow left) (.nonRow right)

public theorem ResidualRelated.refl (a : Assumptions) (tail : Tail) :
    ResidualRelated a tail tail := by
  cases tail with
  | closed => exact .closed
  | productiveCycle => exact .productiveCycle
  | nominal index => exact .nominal index
  | unproductive index => exact .unproductive index
  | nonRow t => exact .nonRow (Obend.Core.TypeGraph.equivalent_of_expose_eq rfl)

public theorem residual_nonrow {a : Assumptions} {row : Ty} {c : Constructor}
    (observed : expose a row = .constructor c)
    (nonrow : Obend.Core.TypeGraph.rowTag c.tag = false) :
    residual a row = .nonRow row := by
  rw [residual, scanResidual, observed]
  cases c with
  | mk tag children => cases tag <;> simp_all [Obend.Core.TypeGraph.rowTag]

public theorem residual_related_of_expose_eq {a : Assumptions} {left right : Ty}
    (heads : expose a left = expose a right) :
    ResidualRelated a (residual a left) (residual a right) := by
  cases exposed : expose a left with
  | nominal index =>
    have other : expose a right = .nominal index := heads.symm.trans exposed
    simp only [residual, scanResidual, exposed, other]
    exact .nominal index
  | unproductive index =>
    have other : expose a right = .unproductive index := heads.symm.trans exposed
    simp only [residual, scanResidual, exposed, other]
    exact .unproductive index
  | constructor c =>
    have other : expose a right = .constructor c := heads.symm.trans exposed
    by_cases row : Obend.Core.TypeGraph.rowTag c.tag = true
    · rw [residual_expose_eq a left right c exposed heads row]
      exact .refl _ _
    · have nonrow : Obend.Core.TypeGraph.rowTag c.tag = false := by
        cases h : Obend.Core.TypeGraph.rowTag c.tag <;> simp_all
      rw [residual_nonrow exposed nonrow, residual_nonrow other nonrow]
      exact .nonRow (Obend.Core.TypeGraph.equivalent_of_expose_eq heads)

end Obend.Core.RecursiveRows

/-! ## Consolidated from `lean/Obend/Core/SubstitutionResidualTransport.lean` -/
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.Proofs.Templates
namespace Search
export Obend.Core.RowSearch (find_iff_hit)
end Search
set_option autoImplicit false

public theorem ResidualRelated.tailKind {a : Assumptions} {left right : Tail}
    (related : ResidualRelated a left right) :
    Obend.Core.TypeGraph.tailKind left = Obend.Core.TypeGraph.tailKind right := by
  cases related <;> rfl

public theorem residualStep_skip_exposed {a : Assumptions} {row tail : Ty}
    (skipped : residualStep a row = .skip tail) :
    ∃ name member, expose a row = .constructor ⟨.field name, [member, tail]⟩ := by
  rw [residualStep] at skipped
  split at skipped
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at skipped
    · contradiction
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      cases skipped
      exact ⟨name, member, shape ▸ exposed⟩
    · contradiction

public theorem residualStep_skip {a : Assumptions} {row tail : Ty}
    (skipped : residualStep a row = .skip tail) : residual a row = residual a tail := by
  obtain ⟨name, member, observed⟩ := residualStep_skip_exposed skipped
  exact residual_exposed_field observed

public theorem residualStep_no_stop (a : Assumptions) (row : Ty) :
    residualStep a row ≠ .stop := by
  rw [residualStep]
  split <;> simp_all
  split <;> simp_all

public theorem residualStep_no_cycle (a : Assumptions) (row : Ty) :
    residualStep a row ≠ .emit .productiveCycle := by
  rw [residualStep]
  split <;> simp_all
  split <;> simp_all

public theorem residual_hit_payload_not_cycle {a : Assumptions} {row : Ty} {payload : Tail} {n : Nat}
    (hit : Search.Hit (residualStep a) row payload n) : payload ≠ .productiveCycle := by
  induction hit with
  | emit row p observed =>
    intro same
    subst p
    exact residualStep_no_cycle a row observed
  | skip row next p n observed nested ih => exact ih

public theorem residual_hit_no_cycle {a : Assumptions} {row : Ty} {n : Nat}
    (hit : Search.Hit (residualStep a) row .productiveCycle n) : False :=
  residual_hit_payload_not_cycle hit rfl

public theorem residual_cycle_iff_no_hit (a : Assumptions) (row : Ty) :
    residual a row = .productiveCycle ↔
      ∀ payload n, ¬ Search.Hit (residualStep a) row payload n := by
  have finds := fun payload => Search.find_iff_hit (residualStep a) (support a row row)
    (fun x y inside skipped => residualStep_skip_support a row row x y inside skipped)
    (p := payload) (left_mem_support a row row)
  constructor
  · intro cycle payload n hit
    have found := (finds payload).mpr ⟨n, hit⟩
    rw [residual_projection, found] at cycle
    simp only [Option.getD_some] at cycle
    subst payload
    exact residual_hit_no_cycle hit
  · intro nohit
    rw [residual_projection]
    cases found : Search.find (residualStep a) (support a row row) row with
    | none => rfl
    | some payload =>
      obtain ⟨n, hit⟩ := (finds payload).mp found
      exact False.elim (nohit payload n hit)

variable {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}

public theorem discharge_residualStep_skip
    (D : Discharges σ template instance_ extra) {row tail : Ty}
    (skipped : residualStep template row = .skip tail) :
    residualStep instance_ (row.instantiate σ) = .skip (tail.instantiate σ) := by
  obtain ⟨name, member, observed⟩ := residualStep_skip_exposed skipped
  have mapped := D.expose_instantiate_constructor observed
  simp only [residualStep, mapped, List.map_cons, List.map_nil]


public theorem discharge_residual_no_hit
    (D : Discharges σ template instance_ extra) {row : Ty}
    (nohit : ∀ payload n, ¬ Search.Hit (residualStep template) row payload n) :
    ∀ payload n, ¬ Search.Hit (residualStep instance_) (row.instantiate σ) payload n := by
  intro payload n
  induction n generalizing row with
  | zero =>
    intro hit
    cases source : residualStep template row with
    | stop => exact residualStep_no_stop template row source
    | emit p => exact nohit p 0 (.emit row p source)
    | skip tail =>
      have target := discharge_residualStep_skip D source
      cases hit with
      | emit _ _ observed => rw [target] at observed; contradiction
  | succ n ih =>
    intro hit
    cases source : residualStep template row with
    | stop => exact residualStep_no_stop template row source
    | emit p => exact nohit p 0 (.emit row p source)
    | skip tail =>
      have target := discharge_residualStep_skip D source
      have tailNoHit : ∀ p k, ¬ Search.Hit (residualStep template) tail p k := by
        intro p k nested
        exact nohit p (k + 1) (.skip row tail p k source nested)
      cases hit with
      | skip _ next _ k observed nested =>
        rw [target] at observed
        cases observed
        exact ih tailNoHit nested

public def instantiateResidual (σ : Nat → Ty) (a : Assumptions) : Tail → Tail
  | .closed => .closed
  | .productiveCycle => .productiveCycle
  | .nominal index => residual a (σ index)
  | .unproductive index => .unproductive index
  | .nonRow t => .nonRow (t.instantiate σ)

public theorem discharge_residual_emit
    (D : Discharges σ template instance_ extra) {row : Ty} {payload : Tail}
    (emitted : residualStep template row = .emit payload) :
    ResidualRelated instance_ (residual instance_ (row.instantiate σ))
      (instantiateResidual σ instance_ payload) := by
  cases exposed : expose template row with
  | nominal index =>
    simp only [residualStep, exposed] at emitted
    cases emitted
    exact residual_related_of_expose_eq (D.expose_instantiate_nominal exposed)
  | unproductive index =>
    simp only [residualStep, exposed] at emitted
    cases emitted
    have mapped := D.expose_instantiate_unproductive exposed
    simp only [residual, scanResidual, mapped, instantiateResidual]
    exact .unproductive index
  | constructor observation =>
    obtain ⟨source, present, raw⟩ := expose_origin (left_mem_support template row row) exposed
    cases source <;> simp only [constructorHead, Head.constructor.injEq] at raw
    all_goals try contradiction
    all_goals subst observation
    all_goals simp only [residualStep, exposed] at emitted
    all_goals try contradiction
    all_goals cases emitted
    all_goals have mapped := D.expose_instantiate_constructor exposed
    all_goals simp only [residual, scanResidual, mapped, List.map_cons, List.map_nil,
      instantiateResidual]
    all_goals first
      | exact .closed
      | exact .nonRow (Obend.Core.TypeGraph.equivalent_of_expose_eq rfl)

public theorem discharge_residual_hit
    (D : Discharges σ template instance_ extra) {row : Ty} {payload : Tail} {n : Nat}
    (hit : Search.Hit (residualStep template) row payload n) :
    ResidualRelated instance_ (residual instance_ (row.instantiate σ))
      (instantiateResidual σ instance_ payload) := by
  induction hit with
  | emit row payload observed => exact discharge_residual_emit D observed
  | skip row next payload n observed nested ih =>
    rw [residualStep_skip (discharge_residualStep_skip D observed)]
    exact ih

public theorem discharge_residual_instantiate
    (D : Discharges σ template instance_ extra) (row : Ty) :
    ResidualRelated instance_ (residual instance_ (row.instantiate σ))
      (instantiateResidual σ instance_ (residual template row)) := by
  by_cases cycle : residual template row = .productiveCycle
  · rw [cycle]
    have nohit := discharge_residual_no_hit D ((residual_cycle_iff_no_hit template row).mp cycle)
    rw [(residual_cycle_iff_no_hit instance_ (row.instantiate σ)).mpr nohit]
    exact .productiveCycle
  · have found : ∃ n, Search.Hit (residualStep template) row (residual template row) n := by
      have projection := residual_projection template row
      cases searched : Search.find (residualStep template) (support template row row) row with
      | none => simp only [searched, Option.getD_none] at projection; exact False.elim (cycle projection)
      | some payload =>
        simp only [searched, Option.getD_some] at projection
        rw [projection]
        exact (Search.find_iff_hit (residualStep template) (support template row row)
          (fun x y inside skipped => residualStep_skip_support template row row x y inside skipped)
          (left_mem_support template row row)).mp searched
    obtain ⟨n, hit⟩ := found
    exact discharge_residual_hit D hit

end Obend.Core.RecursiveRows

/-! ## Consolidated from `lean/Obend/Core/SubstitutionStreamSteps.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
namespace Search
export Obend.Core.RowSearch (Step Hit SkipPath)
end Search
set_option autoImplicit false

/-- Every source epsilon field remains an epsilon field. The only resource
premise needed is preservation of source-true shareability. -/
theorem Discharges.stream_step_skip_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row tail : Ty} {label : String} {first : Bool}
    (skipped : RowHit.step a label first row = .skip tail) :
    RowHit.step b label first (row.instantiate σ) = .skip (tail.instantiate σ) := by
  rw [RowHit.step] at skipped
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name,[member,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at skipped
      · contradiction
      · rename_i notmatched
        have sameTail : fieldTail = tail := Obend.Core.RowSearch.Step.skip.inj skipped
        subst tail
        have targetSkip : (name == label && (first || !RR.shareable b (member.instantiate σ))) = false := by
          cases named : (name == label) with
          | false => simp [named]
          | true =>
            have invisible : first = false := by cases first <;> simp_all
            have sourceSafe : RR.shareable a member = true := by
              cases resource : RR.shareable a member <;> simp_all
            have imageSafe : RR.shareable b (member.instantiate σ) = true :=
              D.semantic_shareable_instantiate valid sourceSafe
            simp [invisible,imageSafe]
        have mapped := D.expose_instantiate_constructor exposed
        simp [RowHit.step,mapped,targetSkip]
    · contradiction
  · contradiction

/-- A source emission determines the exact mapped field observation, before
choosing whether the instantiated hidden member is emitted or skipped. -/
theorem Discharges.stream_step_emit_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) {row member tail : Ty} {label : String} {first : Bool}
    (emitted : RowHit.step a label first row = .emit (member,tail)) :
    RowHit.step b label first (row.instantiate σ) =
      if first || !RR.shareable b (member.instantiate σ) then
        .emit (member.instantiate σ,tail.instantiate σ) else .skip (tail.instantiate σ) := by
  rw [RowHit.step] at emitted
  split at emitted
  · rename_i observation exposed
    split at emitted
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name,[fieldMember,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at emitted
      · rename_i matched
        have named : (name == label) = true := (Bool.and_eq_true_iff.mp matched).1
        have same := Obend.Core.RowSearch.Step.emit.inj emitted
        have memberSame : fieldMember = member := congrArg Prod.fst same
        have tailSame : fieldTail = tail := congrArg Prod.snd same
        subst fieldMember
        subst fieldTail
        have mapped := D.expose_instantiate_constructor exposed
        simp [RowHit.step,mapped,named]
      · contradiction
    · contradiction
  · contradiction

theorem Discharges.stream_path_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row tail : Ty} {label : String} {first : Bool}
    (path : Search.SkipPath (RowHit.step a label first) row tail) :
    Search.SkipPath (RowHit.step b label first) (row.instantiate σ) (tail.instantiate σ) := by
  induction path with
  | refl row => exact .refl _
  | cons row next tail observed nested ih =>
    exact .cons _ _ _ (D.stream_step_skip_instantiate valid observed) ih

theorem Discharges.stream_hit_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row : Ty} {payload : Ty × Ty} {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step a label first) row payload n)
    (retained : (first || !RR.shareable b (payload.1.instantiate σ)) = true) :
    Search.Hit (RowHit.step b label first) (row.instantiate σ)
      (payload.1.instantiate σ,payload.2.instantiate σ) n := by
  revert retained
  induction hit with
  | emit row payload observed =>
    intro retained
    cases payload with
    | mk member tail =>
      apply Obend.Core.RowSearch.Hit.emit
      simpa only [retained,↓reduceIte] using D.stream_step_emit_instantiate observed
  | skip row next payload n observed nested ih =>
    intro retained
    exact .skip _ _ _ n (D.stream_step_skip_instantiate valid observed) (ih retained)

/-- A newly safe source emission becomes one more target epsilon step, after
all already invisible fields in its finite source hit path. -/
theorem Discharges.stream_hit_hidden_path
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {row : Ty} {payload : Ty × Ty} {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step a label first) row payload n)
    (hidden : (first || !RR.shareable b (payload.1.instantiate σ)) = false) :
    Search.SkipPath (RowHit.step b label first) (row.instantiate σ) (payload.2.instantiate σ) := by
  revert hidden
  induction hit with
  | emit row payload observed =>
    intro hidden
    cases payload with
    | mk member tail =>
      apply Obend.Core.RowSearch.SkipPath.cons _ _ _ _ (.refl _)
      simpa only [hidden,Bool.false_eq_true,↓reduceIte] using D.stream_step_emit_instantiate observed
  | skip row next payload n observed nested ih =>
    intro hidden
    exact .cons _ _ _ (D.stream_step_skip_instantiate valid observed) (ih hidden)

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/WeightedRowSafety.lean` -/
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

abbrev WeightedSafe (a : Assumptions) (nominal : Nat → Bool) (node : Node) : Prop :=
  Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) node

theorem weighted_safe_of_related (a : Assumptions) (nominal : Nat → Bool)
    {x y : Node} (related : FP.Bisimilar (graph a) x y) :
    WeightedSafe a nominal x ↔ WeightedSafe a nominal y :=
  Obend.Core.FiniteSafety.safe_bisimilar_iff _ (weightedResource_bisimilar a nominal related)

theorem weighted_end_safe (a : Assumptions) (nominal : Nat → Bool) {node : Node}
    (observed : observe a node = (.streamEnd,[])) : WeightedSafe a nominal node := by
  apply Obend.Core.FiniteSafety.safe_of_children
  · simp [weightedResourceGraph,graph,observed,weightedResourceLabel]
  · simp [weightedResourceGraph,graph,observed,weightedResourceDependencies]

theorem weighted_emit_safe (a : Assumptions) (nominal : Nat → Bool)
    {node : Node} {member tail : Ty} {label : String}
    (observed : observe a node = (.streamEmit,[.type member,.stream tail label false])) :
    WeightedSafe a nominal node ↔
      WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.stream tail label false) := by
  simp only [WeightedSafe]
  rw [Obend.Core.FiniteSafety.safe_iff]
  have labelEq : (weightedResourceGraph a nominal).label node = true := by
    simp [weightedResourceGraph,graph,observed,weightedResourceLabel]
  have childrenEq : (weightedResourceGraph a nominal).successors node =
      [.type member,.stream tail label false] := by
    simp [weightedResourceGraph,graph,observed,weightedResourceDependencies]
  rw [labelEq,childrenEq]
  simp

theorem weighted_hide_safe (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    (row : Ty) (label : String) :
    WeightedSafe a nominal (.stream row label true) ↔
      WeightedSafe a nominal (.stream row label false) := by
  cases emitted : RR.streamStep a row label true with
  | «end» ending =>
    exact (weighted_safe_of_related a nominal (hide_end a row label ending emitted)).symm
  | emit member tail =>
    cases resource : RR.shareable a member with
    | false =>
      exact (weighted_safe_of_related a nominal
        (hide_emit_resourceful a row member tail label resource emitted)).symm
    | true =>
      have hidden := weighted_safe_of_related a nominal
        (RowHit.hide_emit_shareable a label row member tail emitted resource)
      have visible := weighted_emit_safe a nominal
        (show observe a (.stream row label true) =
          (.streamEmit,[.type member,.stream tail label false]) by simp [observe,emitted])
      have goodMember := weighted_safe_of_shareable a nominal raised resource
      rw [visible]
      exact ⟨fun h => hidden.mpr h.2,fun h => ⟨goodMember,hidden.mp h⟩⟩

theorem weighted_field_stream_safe (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    (name label : String) (member tail : Ty) :
    WeightedSafe a nominal (.stream (.field name member tail) label true) ↔
      if name = label then
        WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.stream tail label true)
      else WeightedSafe a nominal (.stream tail label true) := by
  by_cases same : name = label
  · rw [if_pos same]
    have observed := field_stream_emit a name label true member tail (by simp [same])
    exact (weighted_emit_safe a nominal observed).trans
      (and_congr_right (fun _ => (weighted_hide_safe a nominal raised tail label).symm))
  · rw [if_neg same]
    exact weighted_safe_of_related a nominal
      (field_stream_skip a name label true member tail (by simp [same]))

def weightedTailLabel (nominal : Nat → Bool) : RR.Tail → Bool
  | .nominal index => nominal index
  | _ => true

def WeightedInterfaceSafe (a : Assumptions) (nominal : Nat → Bool) (row : Ty) : Prop :=
  weightedTailLabel nominal (RR.residual a row) = true ∧
    (∀ label, WeightedSafe a nominal (.stream row label true)) ∧
    ∀ child ∈ tailChildren (RR.residual a row), WeightedSafe a nominal child

private theorem weighted_row_label (nominal : Nat → Bool) (names : List String)
    (ending : RR.Tail) (share : Bool) :
    weightedResourceLabel nominal (.row names (tailKind ending) share) = weightedTailLabel nominal ending := by
  cases ending <;> rfl

theorem weighted_absent_stream_safe (a : Assumptions) (nominal : Nat → Bool)
    (row : Ty) (label : String) (absent : label ∉ RR.labels a row) :
    WeightedSafe a nominal (.stream row label true) :=
  weighted_end_safe a nominal (absent_stream a row label true absent)

/-- This interface characterization also covers nominal and ordinary non-row
tails. For the latter the residual retains the whole original type state. -/
theorem weighted_interface_safe (a : Assumptions) (nominal : Nat → Bool) (row : Ty) :
    WeightedSafe a nominal (.type row) ↔ WeightedInterfaceSafe a nominal row := by
  cases exposed : expose a row with
  | nominal index =>
    rw [WeightedSafe,Obend.Core.FiniteSafety.safe_iff]
    have streams (label : String) : WeightedSafe a nominal (.stream row label true) := by
      apply weighted_end_safe
      simp [observe,RR.streamStep,Rows.scanStream,exposed]
    simp [WeightedInterfaceSafe,weightedResourceGraph,graph,observe,exposed,
      weightedResourceLabel,weightedResourceDependencies,RR.labels,Rows.scanLabels,
      RR.residual,Rows.scanResidual,weightedTailLabel,tailChildren,streams]
  | unproductive representative =>
    rw [WeightedSafe,Obend.Core.FiniteSafety.safe_iff]
    have streams (label : String) : WeightedSafe a nominal (.stream row label true) := by
      apply weighted_end_safe
      simp [observe,RR.streamStep,Rows.scanStream,exposed]
    simp [WeightedInterfaceSafe,weightedResourceGraph,graph,observe,exposed,
      weightedResourceLabel,weightedResourceDependencies,RR.labels,Rows.scanLabels,
      RR.residual,Rows.scanResidual,weightedTailLabel,tailChildren,streams]
  | constructor observation =>
    by_cases isRow : rowTag observation.tag = true
    · have finite : WeightedSafe a nominal (.type row) ↔
          weightedTailLabel nominal (RR.residual a row) = true ∧
          (∀ label ∈ RR.labels a row, WeightedSafe a nominal (.stream row label true)) ∧
          ∀ child ∈ tailChildren (RR.residual a row), WeightedSafe a nominal child := by
        simp only [WeightedSafe]
        rw [Obend.Core.FiniteSafety.safe_iff]
        have labelEq : (weightedResourceGraph a nominal).label (.type row) =
            weightedTailLabel nominal (RR.residual a row) := by
          simp [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation,weighted_row_label]
        have childrenEq : (weightedResourceGraph a nominal).successors (.type row) =
            (RR.labels a row).map (fun label => Node.stream row label true) ++
              tailChildren (RR.residual a row) := by
          simp [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation,rowChildren,
            weightedResourceDependencies]
        rw [labelEq,childrenEq,List.forall_mem_append,List.forall_mem_map]
      constructor
      · intro safe
        obtain ⟨tail,streams,children⟩ := finite.mp safe
        refine ⟨tail,?_,children⟩
        intro label
        by_cases present : label ∈ RR.labels a row
        · exact streams label present
        · exact weighted_absent_stream_safe a nominal row label present
      · intro safe
        exact finite.mpr ⟨safe.1,fun label _ => safe.2.1 label,safe.2.2⟩
    · obtain ⟨labels,residual⟩ := nonrow_scans a row observation exposed isRow
      have streams (label : String) : WeightedSafe a nominal (.stream row label true) :=
        weighted_absent_stream_safe a nominal row label (by simp [labels])
      simp [WeightedInterfaceSafe,residual,weightedTailLabel,tailChildren,streams]

/-- Weighted row safety recovers the ordinary resource constructor equation.
The source scanner may omit entries only when their weighted safety is known. -/
theorem weighted_field_safe (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    (name : String) (member tail : Ty) :
    WeightedSafe a nominal (.type (.field name member tail)) ↔
      WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.type tail) := by
  have residual : RR.residual a (.field name member tail) = RR.residual a tail := Rows.residual_field a name member tail
  constructor
  · intro safe
    have field := (weighted_interface_safe a nominal _).mp safe
    have named := (weighted_field_stream_safe a nominal raised name name member tail).mp (field.2.1 name)
    simp only [if_pos rfl] at named
    refine ⟨named.1,(weighted_interface_safe a nominal tail).mpr ?_⟩
    refine ⟨by simpa only [residual] using field.1,?_,by simpa only [residual] using field.2.2⟩
    intro label
    have stream := (weighted_field_stream_safe a nominal raised name label member tail).mp (field.2.1 label)
    by_cases same : name = label
    · have both : WeightedSafe a nominal (.type member) ∧ WeightedSafe a nominal (.stream tail label true) := by
        simpa only [if_pos same] using stream
      exact both.2
    · simpa only [if_neg same] using stream
  · rintro ⟨memberSafe,tailSafe⟩
    have tail := (weighted_interface_safe a nominal _).mp tailSafe
    apply (weighted_interface_safe a nominal _).mpr
    refine ⟨by simpa only [residual] using tail.1,?_,by simpa only [residual] using tail.2.2⟩
    intro label
    apply (weighted_field_stream_safe a nominal raised name label member _).mpr
    by_cases same : name = label
    · simpa only [if_pos same] using And.intro memberSafe (tail.2.1 label)
    · simpa only [if_neg same] using tail.2.1 label

end Obend.Core.TypeGraph

/-! ## Consolidated from `lean/Obend/Core/ResidualNominalPath.lean` -/
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false
namespace RH
export Obend.Core.TypeGraph.RowHit (step emission scan_projection step_skip_support)
end RH

public theorem noemit_step_not_emit {a : Assumptions} {row : Ty} {label : String} {first : Bool}
    (noemit : RH.emission (streamStep a row label first) = none) (member tail : Ty) :
    RH.step a label first row ≠ .emit (member, tail) := by
  intro emitted
  have projected : RH.emission (streamStep a row label first) = some (member, tail) := by
    change RH.emission (scanStream a (support a row row) label first row) = _
    rw [RH.scan_projection, Obend.Core.RowSearch.find, emitted]
    simp only [left_mem_support, ↓reduceIte]
  rw [noemit] at projected
  contradiction

public theorem stream_skip_emission_eq {a : Assumptions} {row tail : Ty}
    {label : String} {first : Bool} (skipped : RH.step a label first row = .skip tail) :
    RH.emission (streamStep a row label first) =
      RH.emission (streamStep a tail label first) := by
  have path : Obend.Core.RowSearch.SkipPath (RH.step a label first) row tail :=
    .cons row tail tail skipped (.refl tail)
  have found := Obend.Core.RowSearch.find_path_eq (support a row row) (support a tail tail)
    (fun x y present skipped => RH.step_skip_support a row row x y label first present skipped)
    (fun x y present skipped => RH.step_skip_support a tail tail x y label first present skipped)
    (left_mem_support a row row) (left_mem_support a tail tail) path
  simpa only [streamStep, RH.scan_projection] using found

public theorem residual_hit_nominal_noemit_path {a : Assumptions} {row : Ty}
    {payload : Tail} {n : Nat} {label : String} {first : Bool}
    (hit : Obend.Core.RowSearch.Hit (residualStep a) row payload n) :
    ∀ index, payload = .nominal index → RH.emission (streamStep a row label first) = none →
    ∃ endpoint, Obend.Core.RowSearch.SkipPath (RH.step a label first) row endpoint ∧
      expose a endpoint = .nominal index := by
  induction hit with
  | emit row payload observed =>
    intro index nominal noemit
    rw [residualStep] at observed
    split at observed
    · rename_i terminal exposed
      cases observed
      cases nominal
      exact ⟨row, .refl row, exposed⟩
    · cases observed
      cases nominal
    · split at observed
      · cases observed
        cases nominal
      · contradiction
      · cases observed
        cases nominal
  | skip row next payload n observed nested ih =>
    intro index nominal noemit
    obtain ⟨name, member, exposed⟩ := residualStep_skip_exposed observed
    have skipped : RH.step a label first row = .skip next := by
      by_cases matched : (name == label && (first || !shareable a member)) = true
      · have emitted : RH.step a label first row = .emit (member, next) := by
          simp only [RH.step, exposed, matched, ↓reduceIte]
        exact False.elim (noemit_step_not_emit noemit member next emitted)
      · simp [RH.step, exposed, matched]
    have tailNoemit : RH.emission (streamStep a next label first) = none :=
      (stream_skip_emission_eq skipped).symm.trans noemit
    obtain ⟨endpoint, path, terminal⟩ := ih index nominal tailNoemit
    exact ⟨endpoint, .cons row next endpoint skipped path, terminal⟩

public theorem noemit_nominal_skipPath (a : Assumptions) (row : Ty) (label : String)
    (first : Bool) (index : Nat) (nominal : residual a row = .nominal index)
    (noemit : RH.emission (streamStep a row label first) = none) :
    ∃ endpoint, Obend.Core.RowSearch.SkipPath (RH.step a label first) row endpoint ∧
      expose a endpoint = .nominal index := by
  have found : Obend.Core.RowSearch.find (residualStep a) (support a row row) row =
      some (.nominal index) := by
    rw [residual_projection] at nominal
    cases searched : Obend.Core.RowSearch.find (residualStep a) (support a row row) row with
    | none => simp only [searched, Option.getD_none] at nominal; contradiction
    | some payload =>
      simp only [searched, Option.getD_some] at nominal
      simpa only [nominal] using searched
  obtain ⟨n, hit⟩ := Obend.Core.RowSearch.find_sound _ _ _ _ found
  exact residual_hit_nominal_noemit_path hit index rfl noemit

end Obend.Core.RecursiveRows

/-! ## Consolidated from `lean/Obend/Core/SubstitutionResourceCongruence.lean` -/
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Once omitted source-shareable entries are safe, the weighted quotient
interpretation satisfies precisely the raw resource equations. -/
theorem weighted_resource_predicate (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true) :
    ResourcePredicate a nominal (fun t => WeightedSafe a nominal (.type t)) where
  nominal := by
    intro t j exposed safe
    obtain ⟨good,_⟩ := Obend.Core.FiniteSafety.safe_closed (weightedResourceGraph a nominal) _ safe
    simpa [weightedResourceGraph,graph,observe,exposed,weightedResourceLabel] using good
  productive := by
    intro t c exposed safe
    obtain ⟨raw,_,head⟩ := expose_origin (left_mem_support a t t) exposed
    have nonvariable : ∀ index, raw ≠ .variable index := by
      intro index equal
      subst raw
      simp [constructorHead] at head
    have rawExposure : expose a raw = .constructor c :=
      (expose_nonvariable a raw nonvariable).trans head
    have rawSafe := (weighted_safe_of_related a nominal
      (equivalent_of_expose_eq (exposed.trans rawExposure.symm))).mp safe
    cases raw with
    | «variable» index => exact False.elim (nonvariable index rfl)
    | field name member tail =>
      have shape : c = ⟨.field name,[member,tail]⟩ := by simpa [constructorHead] using head.symm
      subst c
      simpa [resourceObservation] using (weighted_field_safe a nominal raised name member tail).mp rawSafe
    | _ =>
      simp only [constructorHead,Head.constructor.injEq] at head
      subst c
      simp only [WeightedSafe] at rawSafe ⊢
      rw [Obend.Core.FiniteSafety.safe_iff] at rawSafe
      simpa [resourceObservation,weightedResourceGraph,graph,observe,expose,exposeWalk,
        constructorHead,rowTag,weightedResourceLabel,weightedResourceDependencies] using rawSafe

end Obend.Core.TypeGraph

namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

theorem Discharges.image_resource_predicate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat} (D : Discharges σ a b extra) :
    ResourcePredicate a (fun j => RS.shareable b (σ j))
      (fun t => RS.shareable b (t.instantiate σ) = true) where
  nominal := by
    intro t j observed safe
    have mapped := D.expose_instantiate_nominal observed
    exact (RS.shareable_eq_of_expose_eq mapped).symm.trans safe
  productive := by
    intro t c observed safe
    have mapped := D.expose_instantiate_constructor observed
    have closed := (Obend.Core.ResourceSemantics.shareable_unfold b (t.instantiate σ)).mp safe
    cases tag : c.tag <;>
      simp_all [RS.head,resourceObservation]

/-- Exact bridge between actual substitution-image safety and the weighted
source quotient. It uses local syntactic validity, not a new discharge field. -/
theorem Discharges.weighted_resource_iff_image
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) (t : Ty) :
    WeightedSafe a (fun j => RS.shareable b (σ j)) (.type t) ↔
      RS.shareable b (t.instantiate σ) = true := by
  have raised : ∀ j, a.shareableVariables.contains j = true → RS.shareable b (σ j) = true := by
    intro j listed
    exact Obend.Core.ResourceValidity.valid_shareableUnder_shareable valid (σ j)
      ((D.shareable j).trans listed)
  have source := weighted_resource_predicate a (fun j => RS.shareable b (σ j)) raised
  constructor
  · intro safe
    let P : Ty → Prop := fun image => Obend.Core.FiniteSafety.Safe (RS.graph b) image ∨
      ∃ original, WeightedSafe a (fun j => RS.shareable b (σ j)) (.type original) ∧
        image = original.instantiate σ
    have prior (image : Ty) (safe : Obend.Core.FiniteSafety.Safe (RS.graph b) image) :
        (RS.graph b).label image = true ∧ ∀ child ∈ (RS.graph b).successors image, P child := by
      obtain ⟨good,children⟩ := Obend.Core.FiniteSafety.safe_closed (RS.graph b) _ safe
      exact ⟨good,fun child inside => Or.inl (children child inside)⟩
    apply (RS.shareable_iff _ _).mpr
    refine ⟨P,?_,Or.inr ⟨t,safe,rfl⟩⟩
    intro image related
    rcases related with existing | ⟨original,safe,rfl⟩
    · exact prior image existing
    · cases observed : expose a original with
      | nominal index =>
        have imageSafe := source.nominal observed safe
        have mapped := D.expose_instantiate_nominal observed
        have transferred : RS.shareable b (original.instantiate σ) = true :=
          (RS.shareable_eq_of_expose_eq mapped).trans imageSafe
        exact prior _ ((RS.shareable_iff _ _).mp transferred)
      | unproductive representative =>
        have mapped := D.expose_instantiate_unproductive observed
        simp [RS.graph,RS.head,mapped]
      | constructor c =>
        obtain ⟨good,children⟩ := source.productive observed safe
        have mapped := D.expose_instantiate_constructor observed
        have heads : RS.head b (original.instantiate σ) =
            ((resourceObservation c).1,(resourceObservation c).2.map (Ty.instantiate σ)) := by
          cases tag : c.tag <;> simp [RS.head,mapped,resourceObservation,tag]
        refine ⟨?_,?_⟩
        · change (RS.head b (original.instantiate σ)).1 = true
          simpa only [heads] using good
        · intro child inside
          change child ∈ (RS.head b (original.instantiate σ)).2 at inside
          rw [heads] at inside
          obtain ⟨originalChild,present,rfl⟩ := List.mem_map.mp inside
          exact Or.inr ⟨originalChild,children originalChild present,rfl⟩
  · intro safe
    exact D.image_resource_predicate.weighted_safe safe

/-- Source-equivalent types have exactly equal resource flags after
instantiation, even when an unconstrained nominal image becomes shareable. -/
theorem Discharges.semantic_shareable_congr
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) {left right : Ty}
    (related : Equivalent a left right) :
    RS.shareable b (left.instantiate σ) = RS.shareable b (right.instantiate σ) := by
  apply Obend.Core.FiniteSafety.bool_ext
  exact (D.weighted_resource_iff_image valid left).symm.trans
    ((equivalent_weighted_resource _ related).trans (D.weighted_resource_iff_image valid right))

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/FilteredStream.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
namespace Search
export Obend.Core.RowSearch (Step StepLift Hit find OptionLift find_related)
end Search
set_option autoImplicit false

/-- Source streams retain their original row quotient until a nominal residual
is reached. Expanded states then execute the actual instantiated nominal image. -/
inductive FilteredState where
  | source (row : Ty) (first : Bool)
  | expanded (row : Ty) (first : Bool)
  deriving DecidableEq

def nominalResidual : TailKind → Option Nat
  | .nominal j => some j
  | _ => none

def filteredStep (σ : Nat → Ty) (a b : Assumptions) (label : String) :
    FilteredState → Search.Step FilteredState (Ty × FilteredState)
  | .source row first =>
    match RR.streamStep a row label first with
    | .emit member tail =>
      if first || !RR.shareable b (member.instantiate σ) then
        .emit (member.instantiate σ,.source tail false)
      else .skip (.source tail false)
    | .end _ =>
      match nominalResidual (tailKind (RR.residual a row)) with
      | some j => .skip (.expanded (σ j) first)
      | none => .stop
  | .expanded row first =>
    match RowHit.step b label first row with
    | .emit (member,tail) => .emit (member,.expanded tail false)
    | .skip tail => .skip (.expanded tail first)
    | .stop => .stop

/-- Residual kind is required: source end-stream observations alone discard
the nominal tail which may expand to new fields after instantiation. -/
inductive FilteredRelated (a : Assumptions) (label : String) :
    FilteredState → FilteredState → Prop where
  | source {left right : Ty} {first : Bool} :
      StreamEquivalent a left right label first →
      tailKind (RR.residual a left) = tailKind (RR.residual a right) →
      FilteredRelated a label (.source left first) (.source right first)
  | expanded (row : Ty) (first : Bool) :
      FilteredRelated a label (.expanded row first) (.expanded row first)

def FilteredPayloadRelated (σ : Nat → Ty) (a : Assumptions) (label : String)
    (left right : Ty × FilteredState) : Prop :=
  left = right ∨ ∃ l r, Equivalent a l r ∧ left.1 = l.instantiate σ ∧
    right.1 = r.instantiate σ ∧ FilteredRelated a label left.2 right.2

theorem FilteredRelated.symm {a : Assumptions} {label : String} {left right : FilteredState}
    (related : FilteredRelated a label left right) : FilteredRelated a label right left := by
  cases related with
  | source streams kinds =>
    exact .source ((FP.bisimilar_equivalence (graph a)).symm streams) kinds.symm
  | expanded row first => exact .expanded row first

/-- Newly shareable hidden emissions are skipped in lockstep because source
equivalence preserves their exact instantiated resource flags. -/
theorem Discharges.filteredStep_related
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) (label : String)
    {left right : FilteredState} (related : FilteredRelated a label left right) :
    Search.StepLift (FilteredRelated a label) (FilteredPayloadRelated σ a label)
      (filteredStep σ a b label left) (filteredStep σ a b label right) := by
  cases related with
  | expanded row first =>
    cases observed : RowHit.step b label first row with
    | stop => simp only [filteredStep,observed]; exact .stop
    | skip tail => simp only [filteredStep,observed]; exact .skip (.expanded tail first)
    | emit payload =>
      cases payload with
      | mk member tail =>
        simp only [filteredStep,observed]
        exact .emit (Or.inl rfl)
  | @source left right first streams kinds =>
    obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ streams
    cases one : RR.streamStep a left label first with
    | «end» ending =>
      cases two : RR.streamStep a right label first with
      | emit member tail => simp [graph,observe,one,two] at labels
      | «end» ending' =>
        simp only [filteredStep,one,two,kinds]
        cases nominalResidual (tailKind (RR.residual a right)) with
        | none => exact .stop
        | some j => exact .skip (.expanded (σ j) first)
    | emit member tail =>
      cases two : RR.streamStep a right label first with
      | «end» ending => simp [graph,observe,one,two] at labels
      | emit member' tail' =>
        have nested : Equivalent a member member' ∧ StreamEquivalent a tail tail' label false := by
          simpa [graph,observe,one,two,Obend.Core.FiniteBisimulation.Children,
            Equivalent,StreamEquivalent] using children
        have tails : FilteredRelated a label (.source tail false) (.source tail' false) := by
          apply FilteredRelated.source nested.2
          rw [← Obend.Core.RecursiveRows.residual_emit one,
            ← Obend.Core.RecursiveRows.residual_emit two]
          exact kinds
        have resources : RR.shareable b (member.instantiate σ) = RR.shareable b (member'.instantiate σ) :=
          D.semantic_shareable_congr valid nested.1
        simp only [filteredStep,one,two,← resources]
        split
        · apply Obend.Core.RowSearch.StepLift.emit
          unfold FilteredPayloadRelated
          right
          exact ⟨member,member',nested.1,rfl,rfl,tails⟩
        · exact .skip tails

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/FilteredStreamSteps.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

def filteredRow (σ : Nat → Ty) : FilteredState → Ty
  | .source row _ => row.instantiate σ
  | .expanded row _ => row

def filteredFirst : FilteredState → Bool
  | .source _ first | .expanded _ first => first

theorem source_stream_hit (a : Assumptions) {row member tail : Ty}
    {label : String} {first : Bool}
    (emitted : RR.streamStep a row label first = .emit member tail) :
    ∃ n, Search.Hit (RowHit.step a label first) row (member,tail) n := by
  have projected : Obend.Core.RowSearch.find (RowHit.step a label first) (support a row row) row =
      some (member,tail) := by
    rw [← RowHit.scan_projection]
    exact congrArg RowHit.emission emitted
  exact Obend.Core.RowSearch.find_sound _ _ _ _ projected

/-- Source epsilon prefixes are already compressed by the source stream
scanner, and therefore do not consume a filtered-machine transition. -/
theorem filteredStep_source_skip (σ : Nat → Ty) (a b : Assumptions)
    {row tail : Ty} {label : String} {first : Bool}
    (skipped : RowHit.step a label first row = .skip tail) :
    filteredStep σ a b label (.source row first) =
      filteredStep σ a b label (.source tail first) := by
  have streams := RowHit.stream_skip_observe_eq a label first row tail skipped
  have residual := Obend.Core.RecursiveRows.residual_skip skipped
  cases one : RR.streamStep a row label first with
  | «end» ending =>
    cases two : RR.streamStep a tail label first with
    | emit member next => simp [observe,one,two] at streams
    | «end» ending' => simp only [filteredStep,one,two,residual]
  | emit member next =>
    cases two : RR.streamStep a tail label first with
    | «end» ending => simp [observe,one,two] at streams
    | emit member' next' =>
      have payload : member = member' ∧ next = next' := by
        simpa [observe,one,two] using streams
      simp only [filteredStep,one,two,payload.1,payload.2]

theorem filteredStep_source_emit (σ : Nat → Ty) (a b : Assumptions)
    {row member tail : Ty} {label : String} {first : Bool}
    (emitted : RowHit.step a label first row = .emit (member,tail)) :
    filteredStep σ a b label (.source row first) =
      if first || !RR.shareable b (member.instantiate σ) then
        .emit (member.instantiate σ,.source tail false) else .skip (.source tail false) := by
  have observation := RowHit.stream_emit_observe_eq a label first row member tail emitted
  cases result : RR.streamStep a row label first with
  | «end» ending => simp [observe,result] at observation
  | emit member' tail' =>
    have payload : member' = member ∧ tail' = tail := by
      simpa [observe,result] using observation
    simp only [filteredStep,result,payload.1,payload.2]

theorem filteredStep_source_nominal (σ : Nat → Ty) (a b : Assumptions)
    {row : Ty} {label : String} {first : Bool} {index : Nat}
    (observed : expose a row = .nominal index) :
    filteredStep σ a b label (.source row first) = .skip (.expanded (σ index) first) := by
  simp [filteredStep,RR.streamStep,Obend.Core.RecursiveRows.scanStream,observed,
    RR.residual,Obend.Core.RecursiveRows.scanResidual,tailKind,nominalResidual]

/-- Expanded nominal images run the ordinary target epsilon machine exactly. -/
theorem expanded_hit (σ : Nat → Ty) (a b : Assumptions) {row : Ty}
    {label : String} {first : Bool} {payload : Ty × Ty} {n : Nat}
    (hit : Search.Hit (RowHit.step b label first) row payload n) :
    Search.Hit (filteredStep σ a b label) (.expanded row first)
      (payload.1,.expanded payload.2 false) n := by
  induction hit with
  | emit row payload observed =>
    cases payload with
    | mk member tail =>
      apply Obend.Core.RowSearch.Hit.emit
      simp only [filteredStep,observed]
  | skip row next payload n observed nested ih =>
    apply Obend.Core.RowSearch.Hit.skip _ (.expanded next first) _ n _ ih
    simp only [filteredStep,observed]

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/FilteredStreamCompleteness.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

private theorem stream_stop_after_constructor_map
    {a b : Assumptions} {σ : Nat → Ty} {row : Ty} {c : Constructor}
    {label : String} {first : Bool}
    (source : expose a row = .constructor c)
    (target : expose b (row.instantiate σ) = .constructor ⟨c.tag,c.children.map (Ty.instantiate σ)⟩)
    (stopped : RowHit.step a label first row = .stop) :
    RowHit.step b label first (row.instantiate σ) = .stop := by
  cases tag : c.tag <;> try simp [RowHit.step,target,tag]
  case field name =>
    cases children : c.children with
    | nil => simp [RowHit.step,target,tag,children]
    | cons member rest =>
      cases rest with
      | nil => simp [RowHit.step,target,tag,children]
      | cons tail rest =>
        cases rest with
        | cons x xs => simp [RowHit.step,target,tag,children]
        | nil =>
          simp only [RowHit.step,source,tag,children] at stopped
          split at stopped <;> contradiction

/-- Every finite actual emission has a finite path in the filtered source
machine. The induction consumes actual epsilon steps; old source epsilons
are compressed, and newly safe emissions become explicit filtered skips. -/
theorem Discharges.image_hit_filtered
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {source member tail : Ty} {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step b label first) (source.instantiate σ) (member,tail) n) :
    ∃ next k, Search.Hit (filteredStep σ a b label) (.source source first) (member,next) k ∧
      filteredRow σ next = tail ∧ filteredFirst next = false := by
  cases sourceStep : RowHit.step a label first source with
  | skip sourceTail =>
    have targetStep := D.stream_step_skip_instantiate valid sourceStep
    cases hit with
    | emit _ _ observed => rw [targetStep] at observed; contradiction
    | skip _ actualTail _ count observed nested =>
      have same : actualTail = sourceTail.instantiate σ := by
        exact Obend.Core.RowSearch.Step.skip.inj (observed.symm.trans targetStep)
      subst actualTail
      obtain ⟨next,k,filtered,row,mode⟩ := D.image_hit_filtered valid nested
      have compressed := filteredStep_source_skip σ a b sourceStep
      exact ⟨next,k,Obend.Core.RowSearch.hit_of_step_eq compressed.symm filtered,row,mode⟩
  | emit payload =>
    cases payload with
    | mk sourceMember sourceTail =>
      have targetStep := D.stream_step_emit_instantiate sourceStep
      have macroStep := filteredStep_source_emit σ a b sourceStep
      cases retained : (first || !RR.shareable b (sourceMember.instantiate σ)) with
      | true =>
        simp only [retained,↓reduceIte] at targetStep macroStep
        cases hit with
        | skip _ actualTail _ count observed nested => rw [targetStep] at observed; contradiction
        | emit _ _ observed =>
          have same := Obend.Core.RowSearch.Step.emit.inj (targetStep.symm.trans observed)
          have sameMember : sourceMember.instantiate σ = member := congrArg Prod.fst same
          have sameTail : sourceTail.instantiate σ = tail := congrArg Prod.snd same
          subst member
          subst tail
          exact ⟨.source sourceTail false,0,.emit _ _ macroStep,rfl,rfl⟩
      | false =>
        have hidden : first = false := by cases first <;> simp_all
        subst first
        simp only [retained,Bool.false_eq_true,↓reduceIte] at targetStep macroStep
        cases hit with
        | emit _ _ observed => rw [targetStep] at observed; contradiction
        | skip _ actualTail _ count observed nested =>
          have same : actualTail = sourceTail.instantiate σ :=
            Obend.Core.RowSearch.Step.skip.inj (observed.symm.trans targetStep)
          subst actualTail
          obtain ⟨next,k,filtered,row,mode⟩ := D.image_hit_filtered valid nested
          exact ⟨next,k + 1,.skip _ _ _ k macroStep filtered,row,mode⟩
  | stop =>
    cases sourceHead : expose a source with
    | nominal index =>
      have mapped := D.expose_instantiate_nominal sourceHead
      have same : RowHit.step b label first (source.instantiate σ) = RowHit.step b label first (σ index) := by
        unfold RowHit.step
        rw [mapped]
      have imageHit := Obend.Core.RowSearch.hit_of_step_eq same hit
      have expanded := expanded_hit σ a b imageHit
      have macroStep := filteredStep_source_nominal σ a b (label := label) (first := first) sourceHead
      exact ⟨.expanded tail false,n + 1,.skip _ _ _ n macroStep expanded,rfl,rfl⟩
    | unproductive representative =>
      have mapped := D.expose_instantiate_unproductive sourceHead
      have stopped : RowHit.step b label first (source.instantiate σ) = .stop := by
        simp [RowHit.step,mapped]
      cases hit with
      | emit _ _ observed => rw [stopped] at observed; contradiction
      | skip _ _ _ _ observed _ => rw [stopped] at observed; contradiction
    | constructor c =>
      have stopped := stream_stop_after_constructor_map sourceHead
        (D.expose_instantiate_constructor sourceHead) sourceStep
      cases hit with
      | emit _ _ observed => rw [stopped] at observed; contradiction
      | skip _ _ _ _ observed _ => rw [stopped] at observed; contradiction
termination_by n
decreasing_by
  all_goals
    have current : n = count + 1 := by assumption
    omega

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/FilteredStreamSoundness.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

/-- A finite filtered emission is realized by the actual substituted row.
Compressed source skips and newly safe hidden fields form finite target
prefixes; nominal dispatch shares the exposed target head with its image. -/
public theorem Discharges.filtered_hit_image
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {label : String} {state : FilteredState} {payload : Ty × FilteredState} {n : Nat}
    (hit : Search.Hit (filteredStep σ a b label) state payload n) :
    filteredFirst payload.2 = false ∧
      ∃ k, Search.Hit (RowHit.step b label (filteredFirst state))
        (filteredRow σ state) (payload.1, filteredRow σ payload.2) k := by
  induction hit with
  | emit state payload observed =>
    cases state with
    | source row first =>
      cases sourceStream : RR.streamStep a row label first with
      | «end» ending =>
        simp only [filteredStep,sourceStream] at observed
        cases dispatched : nominalResidual (tailKind (RR.residual a row)) <;>
          simp only [dispatched] at observed <;> contradiction
      | emit member tail =>
        simp only [filteredStep,sourceStream] at observed
        split at observed
        · rename_i retained
          cases observed
          obtain ⟨count,sourceHit⟩ := source_stream_hit a sourceStream
          refine ⟨rfl,count,?_⟩
          simpa only [filteredRow,filteredFirst] using D.stream_hit_instantiate valid sourceHit retained
        · contradiction
    | expanded row first =>
      cases targetStep : RowHit.step b label first row with
      | stop => simp only [filteredStep,targetStep] at observed; contradiction
      | skip next => simp only [filteredStep,targetStep] at observed; contradiction
      | emit targetPayload =>
        cases targetPayload with
        | mk member tail =>
          simp only [filteredStep,targetStep] at observed
          cases observed
          exact ⟨rfl,0,.emit row (member,tail) targetStep⟩
  | skip state next payload n observed nested ih =>
    cases state with
    | expanded row first =>
      cases targetStep : RowHit.step b label first row with
      | stop => simp only [filteredStep,targetStep] at observed; contradiction
      | emit targetPayload =>
        cases targetPayload with
        | mk member tail => simp only [filteredStep,targetStep] at observed; contradiction
      | skip tail =>
        simp only [filteredStep,targetStep] at observed
        cases observed
        obtain ⟨mode,count,imageHit⟩ := ih
        exact ⟨mode,count + 1,.skip row tail _ count targetStep imageHit⟩
    | source row first =>
      cases sourceStream : RR.streamStep a row label first with
      | emit member tail =>
        cases retained : (first || !RR.shareable b (member.instantiate σ)) with
        | true =>
          simp only [filteredStep,sourceStream,retained,↓reduceIte] at observed
          contradiction
        | false =>
          simp only [filteredStep,sourceStream,retained,Bool.false_eq_true,↓reduceIte] at observed
          cases observed
          have hiddenMode : first = false := by cases first <;> simp_all
          subst first
          obtain ⟨mode,count,imageHit⟩ := ih
          obtain ⟨sourceCount,sourceHit⟩ := source_stream_hit a sourceStream
          have path := D.stream_hit_hidden_path valid sourceHit retained
          refine ⟨mode,?_⟩
          exact (Obend.Core.RowSearch.hit_path_iff path).mpr ⟨count,imageHit⟩
      | «end» ending =>
        cases sourceResidual : RR.residual a row with
        | closed =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | productiveCycle =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | unproductive representative =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | nonRow terminal =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          contradiction
        | nominal index =>
          simp only [filteredStep,sourceStream,sourceResidual,tailKind,nominalResidual] at observed
          cases observed
          obtain ⟨mode,count,imageHit⟩ := ih
          have noemit : RowHit.emission (RR.streamStep a row label first) = none := by
            rw [sourceStream]
            rfl
          obtain ⟨endpoint,sourcePath,nominal⟩ :=
            Obend.Core.RecursiveRows.noemit_nominal_skipPath a row label first index sourceResidual noemit
          have targetPath := D.stream_path_instantiate valid sourcePath
          have sameHead := D.expose_instantiate_nominal nominal
          have sameStep : RowHit.step b label first (endpoint.instantiate σ) =
              RowHit.step b label first (σ index) := by
            unfold RowHit.step
            rw [sameHead]
          have endpointHit := Obend.Core.RowSearch.hit_of_step_eq sameStep.symm imageHit
          refine ⟨mode,?_⟩
          exact (Obend.Core.RowSearch.hit_path_iff targetPath).mpr ⟨count,endpointHit⟩

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/SubstitutionBisimulation.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

/-- Coinductive substitution seeds, closed under actual target equivalence
and composition. Composition absorbs raw alias wrappers in residual payloads. -/
inductive InstantiationRelated (σ : Nat → Ty) (a b : Assumptions) : Node → Node → Prop where
  | existing {x y} : FP.Bisimilar (graph b) x y → InstantiationRelated σ a b x y
  | types {left right} : Equivalent a left right →
      InstantiationRelated σ a b (.type (left.instantiate σ)) (.type (right.instantiate σ))
  | streams {left right label} : FilteredRelated a label left right →
      InstantiationRelated σ a b
        (.stream (filteredRow σ left) label (filteredFirst left))
        (.stream (filteredRow σ right) label (filteredFirst right))
  | trans {x y z} : InstantiationRelated σ a b x y → InstantiationRelated σ a b y z →
      InstantiationRelated σ a b x z

theorem streamStep_of_hit (b : Assumptions) {row member tail : Ty}
    {label : String} {first : Bool} {n : Nat}
    (hit : Search.Hit (RowHit.step b label first) row (member,tail) n) :
    RR.streamStep b row label first = .emit member tail := by
  have found := (Obend.Core.RowSearch.find_iff_hit (RowHit.step b label first) (support b row row)
    (fun x y present skipped => RowHit.step_skip_support b row row x y label first present skipped)
    (left_mem_support b row row)).mpr ⟨n,hit⟩
  have projected : RowHit.emission (RR.streamStep b row label first) = some (member,tail) := by
    simpa only [RR.streamStep,RowHit.scan_projection] using found
  cases emitted : RR.streamStep b row label first with
  | «end» ending => simp [emitted,RowHit.emission] at projected
  | emit m t =>
    have same : m = member ∧ t = tail := by simpa [emitted,RowHit.emission] using projected
    simp only [same.1,same.2]

theorem Discharges.realized_hit_filtered
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {state : FilteredState} {member tail : Ty} {label : String} {n : Nat}
    (hit : Search.Hit (RowHit.step b label (filteredFirst state)) (filteredRow σ state) (member,tail) n) :
    ∃ next k, Search.Hit (filteredStep σ a b label) state (member,next) k ∧
      filteredRow σ next = tail ∧ filteredFirst next = false := by
  cases state with
  | source row first => exact D.image_hit_filtered valid hit
  | expanded row first => exact ⟨.expanded tail false,n,expanded_hit σ a b hit,rfl,rfl⟩

theorem filtered_payload_nodes {σ : Nat → Ty} {a b : Assumptions} {label : String}
    {left right : Ty × FilteredState}
    (related : FilteredPayloadRelated σ a label left right)
    (leftMode : filteredFirst left.2 = false) (rightMode : filteredFirst right.2 = false) :
    InstantiationRelated σ a b (.type left.1) (.type right.1) ∧
      InstantiationRelated σ a b (.stream (filteredRow σ left.2) label false)
        (.stream (filteredRow σ right.2) label false) := by
  rcases related with equal | ⟨l,r,types,leftMember,rightMember,tails⟩
  · subst right
    exact ⟨.existing ((FP.bisimilar_equivalence (graph b)).refl _),
      .existing ((FP.bisimilar_equivalence (graph b)).refl _)⟩
  · constructor
    · rw [leftMember,rightMember]
      exact .types types
    · simpa only [leftMode,rightMode] using
        (InstantiationRelated.streams (σ := σ) (b := b) tails)

/-- Finite actual emissions transport through the filtered source bisimulation;
their member and continuation pairs are seeds of the final type coinduction. -/
theorem Discharges.related_stream_emits
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {left right : FilteredState} {label : String}
    (related : FilteredRelated a label left right) {member tail : Ty}
    (emitted : RR.streamStep b (filteredRow σ left) label (filteredFirst left) = .emit member tail) :
    ∃ member' tail', RR.streamStep b (filteredRow σ right) label (filteredFirst right) = .emit member' tail' ∧
      InstantiationRelated σ a b (.type member) (.type member') ∧
      InstantiationRelated σ a b (.stream tail label false) (.stream tail' label false) := by
  obtain ⟨n,hit⟩ := source_stream_hit b emitted
  obtain ⟨next,k,filtered,row,mode⟩ := D.realized_hit_filtered valid hit
  obtain ⟨payload,other,payloadRelated⟩ := filtered.related
    (fun x y link => D.filteredStep_related valid label link) related
  obtain ⟨otherMode,count,imageHit⟩ := D.filtered_hit_image valid other
  have nodes := filtered_payload_nodes (b := b) payloadRelated mode otherMode
  refine ⟨payload.1,filteredRow σ payload.2,streamStep_of_hit b imageHit,nodes.1,?_⟩
  simpa only [row] using nodes.2

theorem Discharges.related_stream_closed
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {left right : FilteredState} {label : String}
    (related : FilteredRelated a label left right) :
    (graph b).label (.stream (filteredRow σ left) label (filteredFirst left)) =
      (graph b).label (.stream (filteredRow σ right) label (filteredFirst right)) ∧
    Children (InstantiationRelated σ a b)
      ((graph b).successors (.stream (filteredRow σ left) label (filteredFirst left)))
      ((graph b).successors (.stream (filteredRow σ right) label (filteredFirst right))) := by
  cases one : RR.streamStep b (filteredRow σ left) label (filteredFirst left) with
  | emit member tail =>
    obtain ⟨member',tail',two,members,tails⟩ := D.related_stream_emits valid related one
    constructor
    · simp [graph,observe,one,two]
    · simp only [graph,observe,one,two]
      exact ⟨members,tails,True.intro⟩
  | «end» ending =>
    cases two : RR.streamStep b (filteredRow σ right) label (filteredFirst right) with
    | «end» ending' => simp [graph,observe,one,two,Children]
    | emit member tail =>
      obtain ⟨_,_,impossible,_⟩ := D.related_stream_emits valid related.symm two
      rw [one] at impossible
      contradiction

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/SubstitutionRows.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.FiniteBisimulation (Children children_mono children_refl children_symm children_comp)
set_option autoImplicit false

theorem instantiation_children_trans {σ : Nat → Ty} {a b : Assumptions} {xs ys zs : List Node}
    (one : Children (InstantiationRelated σ a b) xs ys)
    (two : Children (InstantiationRelated σ a b) ys zs) :
    Children (InstantiationRelated σ a b) xs zs :=
  children_mono (fun _ _ ⟨_,h,k⟩ => InstantiationRelated.trans h k) (children_comp one two)

theorem residual_existing_children {b : Assumptions} {left right : RR.Tail}
    (related : Obend.Core.RecursiveRows.ResidualRelated b left right) :
    Children (FP.Bisimilar (graph b)) (tailChildren left) (tailChildren right) := by
  cases related with
  | nonRow h => exact ⟨h,True.intro⟩
  | _ => trivial

theorem mapped_residual_interface (σ : Nat → Ty) (a b : Assumptions)
    (left right : RR.Tail) (kinds : tailKind left = tailKind right)
    (children : Children (FP.Bisimilar (graph a)) (tailChildren left) (tailChildren right)) :
    tailKind (Obend.Core.RecursiveRows.instantiateResidual σ b left) =
      tailKind (Obend.Core.RecursiveRows.instantiateResidual σ b right) ∧
    Children (InstantiationRelated σ a b)
      (tailChildren (Obend.Core.RecursiveRows.instantiateResidual σ b left))
      (tailChildren (Obend.Core.RecursiveRows.instantiateResidual σ b right)) := by
  cases left with
  | closed => cases right <;> simp_all [tailKind,Obend.Core.RecursiveRows.instantiateResidual,tailChildren,Children]
  | productiveCycle => cases right <;> simp_all [tailKind,Obend.Core.RecursiveRows.instantiateResidual,tailChildren,Children]
  | unproductive index => cases right <;> simp_all [tailKind,Obend.Core.RecursiveRows.instantiateResidual,tailChildren,Children]
  | nominal index =>
    cases right with
    | nominal other =>
      have same : index = other := TailKind.nominal.inj kinds
      subst other
      exact ⟨rfl,children_mono (fun x y equal => by
        subst y
        exact InstantiationRelated.existing ((FP.bisimilar_equivalence (graph b)).refl x)) (children_refl _)⟩
    | _ => simp [tailKind] at kinds
  | nonRow left =>
    cases right with
    | nonRow right => exact ⟨rfl,InstantiationRelated.types children.1,True.intro⟩
    | _ => simp [tailKind] at kinds

theorem Discharges.row_residual_interface
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) {left right : Ty} (view : RowInterface a left right) :
    tailKind (RR.residual b (left.instantiate σ)) = tailKind (RR.residual b (right.instantiate σ)) ∧
    Children (InstantiationRelated σ a b)
      (tailChildren (RR.residual b (left.instantiate σ)))
      (tailChildren (RR.residual b (right.instantiate σ))) := by
  have one := Obend.Core.RecursiveRows.discharge_residual_instantiate D left
  have two := Obend.Core.RecursiveRows.discharge_residual_instantiate D right
  have middle := mapped_residual_interface σ a b (RR.residual a left) (RR.residual a right)
    view.residualKind view.residualChildren
  refine ⟨one.tailKind.trans (middle.1.trans two.tailKind.symm),?_⟩
  have front := children_mono (fun _ _ h => InstantiationRelated.existing (σ := σ) (a := a) h)
    (residual_existing_children one)
  have back := children_mono (fun _ _ h => InstantiationRelated.existing (σ := σ) (a := a)
    ((FP.bisimilar_equivalence (graph b)).symm h)) (children_symm (residual_existing_children two))
  exact instantiation_children_trans front (instantiation_children_trans middle.2 back)

theorem Discharges.row_alphabet_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {left right : Ty} (view : RowInterface a left right) :
    RR.labels b (left.instantiate σ) = RR.labels b (right.instantiate σ) := by
  apply Obend.Core.RecursiveRows.sorted_ext _ _
    (Obend.Core.RecursiveRows.scanLabels_sorted b _ (left.instantiate σ))
    (Obend.Core.RecursiveRows.scanLabels_sorted b _ (right.instantiate σ))
  intro label
  change label ∈ RR.labels b (left.instantiate σ) ↔ label ∈ RR.labels b (right.instantiate σ)
  rw [Obend.Core.RecursiveRows.labels_iff_true_emits,Obend.Core.RecursiveRows.labels_iff_true_emits]
  have related : FilteredRelated a label (.source left true) (.source right true) :=
    .source (view.streams label) view.residualKind
  constructor
  · rintro ⟨member,tail,emitted⟩
    obtain ⟨member',tail',found,_⟩ := D.related_stream_emits valid related emitted
    exact ⟨member',tail',found⟩
  · rintro ⟨member,tail,emitted⟩
    obtain ⟨member',tail',found,_⟩ := D.related_stream_emits valid related.symm emitted
    exact ⟨member',tail',found⟩

theorem instantiation_type_children (σ : Nat → Ty) (a b : Assumptions) (xs ys : List Ty)
    (children : Children (FP.Bisimilar (graph a)) (xs.map Node.type) (ys.map Node.type)) :
    Children (InstantiationRelated σ a b)
      (xs.map (fun t => Node.type (t.instantiate σ))) (ys.map (fun t => Node.type (t.instantiate σ))) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Children]
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys => exact ⟨.types children.1,ih ys children.2⟩

end Obend.Core.Proofs.Templates

/-! ## Consolidated from `lean/Obend/Core/EquiRecursiveSubstitutionTransport.lean` -/
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.FiniteBisimulation (Children children_mono)
set_option autoImplicit false

theorem existing_instantiation_closed {σ : Nat → Ty} {a b : Assumptions} {x y : Node}
    (related : FP.Bisimilar (graph b) x y) :
    (graph b).label x = (graph b).label y ∧
      Children (InstantiationRelated σ a b) ((graph b).successors x) ((graph b).successors y) := by
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph b) _ _ related
  exact ⟨labels,children_mono (fun _ _ h => InstantiationRelated.existing h) children⟩

theorem Discharges.type_seed_closed
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) {left right : Ty}
    (related : Equivalent a left right) :
    (graph b).label (.type (left.instantiate σ)) = (graph b).label (.type (right.instantiate σ)) ∧
      Children (InstantiationRelated σ a b) ((graph b).successors (.type (left.instantiate σ)))
        ((graph b).successors (.type (right.instantiate σ))) := by
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ related
  cases sourceL : expose a left with
  | nominal index =>
    cases sourceR : expose a right with
    | nominal other =>
      have same : index = other := by simpa [graph,observe,sourceL,sourceR] using labels
      subst other
      exact existing_instantiation_closed (equivalent_of_expose_eq
        ((D.expose_instantiate_nominal sourceL).trans (D.expose_instantiate_nominal sourceR).symm))
    | unproductive other => simp [graph,observe,sourceL,sourceR] at labels
    | constructor c =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
  | unproductive representative =>
    cases sourceR : expose a right with
    | unproductive other =>
      have same : representative = other := by simpa [graph,observe,sourceL,sourceR] using labels
      subst other
      exact existing_instantiation_closed (equivalent_of_expose_eq
        ((D.expose_instantiate_unproductive sourceL).trans (D.expose_instantiate_unproductive sourceR).symm))
    | nominal other => simp [graph,observe,sourceL,sourceR] at labels
    | constructor c =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
  | constructor c =>
    cases sourceR : expose a right with
    | nominal other =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
    | unproductive other =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
    | constructor d =>
      have mappedL := D.expose_instantiate_constructor sourceL
      have mappedR := D.expose_instantiate_constructor sourceR
      have resources : RR.shareable b (left.instantiate σ) = RR.shareable b (right.instantiate σ) :=
        D.semantic_shareable_congr valid related
      by_cases lrow : rowTag c.tag = true
      · have rrow : rowTag d.tag = true := by
          by_cases isRow : rowTag d.tag = true
          · exact isRow
          · simp [graph,observe,sourceL,sourceR,lrow,isRow,rowObservation] at labels
        have view := equivalent_row_interface related
        have alphabet := D.row_alphabet_instantiate valid view
        have residual := D.row_residual_interface view
        constructor
        · simp [graph,observe,mappedL,mappedR,lrow,rrow,rowObservation,
            alphabet,residual.1,resources]
        · simp only [graph,observe,mappedL,mappedR,lrow,rrow,↓reduceIte,rowObservation]
          unfold rowChildren
          rw [← alphabet]
          apply children_append
          · apply children_mapped
            intro label _
            exact InstantiationRelated.streams (.source (view.streams label) view.residualKind)
          · exact residual.2
      · have rrow : rowTag d.tag ≠ true := by
          intro isRow
          simp [graph,observe,sourceL,sourceR,lrow,isRow,rowObservation] at labels
        have tags : c.tag = d.tag := by
          have ordinary : Label.ordinary c.tag (RR.shareable a left) =
              Label.ordinary d.tag (RR.shareable a right) := by
            simpa [graph,observe,sourceL,sourceR,lrow,rrow] using labels
          exact (Label.ordinary.inj ordinary).1
        have sourceChildren : Children (FP.Bisimilar (graph a))
            (c.children.map Node.type) (d.children.map Node.type) := by
          simpa [graph,observe,sourceL,sourceR,lrow,rrow] using children
        constructor
        · simp [graph,observe,mappedL,mappedR,lrow,rrow,tags,resources]
        · simpa [graph,observe,mappedL,mappedR,lrow,rrow,List.map_map,Function.comp_def] using
            instantiation_type_children σ a b c.children d.children sourceChildren

/-- Full hereditary recursive equality transport. The original discharge
contract is retained; the actual instance's premise validation is essential. -/
theorem Discharges.equivalent_instantiate
    {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}
    (D : Discharges σ template instance_ extra) (valid : instance_.valid = true)
    {actual expected : Ty} (agreement : Equivalent template actual expected) :
    Equivalent instance_ (actual.instantiate σ) (expected.instantiate σ) := by
  refine ⟨InstantiationRelated σ template instance_,?_,InstantiationRelated.types agreement⟩
  intro left right related
  induction related with
  | existing h => exact existing_instantiation_closed h
  | types h => exact D.type_seed_closed valid h
  | streams h => exact D.related_stream_closed valid h
  | trans h k ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,instantiation_children_trans ih₁.2 ih₂.2⟩

end Obend.Core.Proofs.Templates

end
