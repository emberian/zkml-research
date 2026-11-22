module
/- `prepare_checks`: on the expanded syntactic fragment `Checkable` (including `.extend`, `.mix`,
`.fix`, and `.case` / `.effectCase`), over any `Assumptions` (including non-empty equi-recursive
alias bounds) satisfying `ShareableComplete`, every typed erased term is prepared and accepted by
`Bidirectional.checkAgainst` with its exact usage vector.

Consolidates and upgrades `Obend.Elab.Proofs.{AliasFree, Refines, PrepareChecks}` (Wave C2 Core). -/
public import Obend.Elab.Prepare
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
import all Obend.Core.Check
import all Obend.Elab.Prepare

namespace Obend.Elab.Proofs.PrepareChecks
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.Term (Term Primitive)
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Elab.Prepare Obend.Elab.Work
set_option autoImplicit false

/-! ## 1. Equi-Recursive Weak-Head Inversion & `ShareableComplete` -/

/-- Decidable alignment between nominal `shareableVariables` declarations and semantic
greatest-fixed-point shareability over `a.bounds`. Evaluates to `true` by `rfl` on empty bounds
(`{}`) and holds on non-empty equi-recursive sum, function, prototype, and row bounds. -/
@[expose] public def ShareableComplete (a : Assumptions) : Bool :=
  (a.bounds.all fun (index, _) =>
    a.shareableVariables.contains index == Obend.Core.RecursiveRows.shareable a (.variable index)) &&
  (a.bounds.all fun (index, _) =>
    match a.bounds.lookup index with
    | some bound => !bound.bearsCustody
    | none => true)

public theorem shareableComplete_empty : ShareableComplete {} = true := rfl

public theorem shareableComplete_of_bounds_nil {a : Assumptions} (h : a.bounds = []) :
    ShareableComplete a = true := by
  simp [ShareableComplete, h]

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {xs : List (α × β)} {k : α} {v : β}
    (found : xs.lookup k = some v) : (k, v) ∈ xs := by
  induction xs with
  | nil => simp [List.lookup] at found
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [List.lookup] at found
    by_cases h : (k == k') = true
    · simp only [h, Option.some.injEq] at found
      have hk : k = k' := eq_of_beq h
      subst hk; subst found; exact List.mem_cons_self
    · simp only [h] at found
      exact List.mem_cons_of_mem _ (ih found)

theorem valid_lookup_shareable {a : Assumptions} (valid : a.valid = true) {index : Nat}
    (mem : a.shareableVariables.contains index = true) :
    ∃ bound, a.bounds.lookup index = some bound ∧
      bound.shareableUnder a.shareableVariables = true := by
  simp only [Assumptions.valid, Bool.and_eq_true, List.all_eq_true] at valid
  have hex := valid.1 index (List.contains_iff_mem.mp mem)
  cases h : a.bounds.lookup index with
  | none => simp [h] at hex
  | some bound => exact ⟨bound, rfl, by simpa [h] using hex⟩

theorem aliasChain_preserves_shareableUnder {a : Assumptions} (valid : a.valid = true)
    {start finish : Ty} {path : List Nat} (chain : AliasChain a start path finish)
    (hs : start.shareableUnder a.shareableVariables = true) :
    finish.shareableUnder a.shareableVariables = true := by
  induction chain with
  | nil => exact hs
  | @cons index body finish path aliased _ tail ih =>
    simp only [Ty.shareableUnder] at hs
    obtain ⟨bound, hlook, hshare⟩ := valid_lookup_shareable valid hs
    have hbound := Assumptions.alias_bound aliased
    rw [hlook] at hbound
    cases hbound
    exact ih hshare

/-- On any `Assumptions.valid` environment, syntactic `shareableUnder` implies semantic
greatest-fixed-point `RecursiveRows.shareable`. -/
public theorem valid_shareableUnder_semantic {a : Assumptions} (valid : a.valid = true)
    {t : Ty} (hs : t.shareableUnder a.shareableVariables = true) :
    Obend.Core.RecursiveRows.shareable a t = true := by
  rw [Obend.Core.RecursiveRows.shareable_iff]
  refine ⟨fun u => u.shareableUnder a.shareableVariables = true, ?_, hs⟩
  intro u hu
  obtain ⟨path, finish, chain, _, _, stopped⟩ :=
    exposeWalk_trace a (a.bounds.map Prod.fst) [] (initial_covers a) u
  have hfin := aliasChain_preserves_shareableUnder valid chain hu
  change Stopped a (visitPath [] path) finish (expose a u) at stopped
  generalize hExp : expose a u = hd at stopped
  cases stopped with
  | productive _ nonvar =>
    cases finish with
    | «variable» idx => exact False.elim (nonvar idx rfl)
    | natural | label | boolean | emptyRow =>
      simp [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp, constructorHead]
    | custody _ =>
      simp [Ty.shareableUnder, Ty.shareable] at hfin
    | computation _ _ _ =>
      simp [Ty.shareableUnder, Ty.shareable] at hfin
    | arrow reuse _ _ _ =>
      simp only [Ty.shareableUnder, Ty.shareable] at hfin
      simp [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp, constructorHead, hfin]
    | field _ m tl =>
      simp only [Ty.shareableUnder, Bool.and_eq_true] at hfin
      simpa [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp, constructorHead] using hfin
    | specification m e =>
      simp only [Ty.shareableUnder, Bool.and_eq_true] at hfin
      simpa [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp, constructorHead] using hfin
    | prototype sp tg =>
      simp only [Ty.shareableUnder, Bool.and_eq_true] at hfin
      simpa [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp, constructorHead] using hfin
    | variant r =>
      simp only [Ty.shareableUnder] at hfin
      simpa [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp, constructorHead] using hfin
  | @unbound idx _ _ =>
    simp only [Ty.shareableUnder] at hfin
    simp [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp,
      List.contains_iff_mem.mp hfin]
  | @activity idx body _ aliased blocked =>
    have hbound := mem_of_lookup (Assumptions.alias_bound aliased)
    simp only [Assumptions.valid, Bool.and_eq_true, List.all_eq_true] at valid
    have hpure := valid.2.1 (idx, body) hbound
    simp [blocked] at hpure
  | @cycle idx _ =>
    simp [Obend.Core.ResourceSemantics.graph, Obend.Core.ResourceSemantics.head, hExp]

/-- Every valid assumption environment whose declared bounds are all marked shareable
(such as mutually recursive algebraic datatypes and shareable row aliases) satisfies
`ShareableComplete`. -/
public theorem shareableComplete_of_all_shareable {a : Assumptions} (valid : a.valid = true)
    (allDeclared : ∀ p ∈ a.bounds, a.shareableVariables.contains p.1 = true) :
    ShareableComplete a = true := by
  simp only [ShareableComplete, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨fun ⟨index, bound⟩ hmem => ?_, fun ⟨index, _⟩ hmem => ?_⟩
  · have hc : a.shareableVariables.contains index = true := allDeclared (index, bound) hmem
    have hsem : Obend.Core.RecursiveRows.shareable a (.variable index) = true :=
      valid_shareableUnder_semantic valid (by simpa [Ty.shareableUnder] using hc)
    rw [hc, hsem]
  · have hc : a.shareableVariables.contains index = true := allDeclared _ hmem
    obtain ⟨bound, hlook, hsh⟩ := valid_lookup_shareable valid hc
    simp [hlook, Ty.bearsCustody_of_shareableUnder hsh]

theorem semantic_variable {a : Assumptions} (sc : ShareableComplete a = true) (index : Nat) :
    Obend.Core.RecursiveRows.shareable a (.variable index) = a.shareableVariables.contains index := by
  cases h : a.bounds.lookup index with
  | some bound =>
    have hmem := mem_of_lookup h
    simp only [ShareableComplete, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at sc
    exact (sc.1 (index, bound) hmem).symm
  | none =>
    have hAlias : a.alias index = none := by
      cases ha : a.alias index with
      | none => rfl
      | some b =>
        have hb := Assumptions.alias_bound ha
        rw [h] at hb; cases hb
    apply Obend.Core.RecursiveRows.shareable_terminal
    simp [Obend.Core.ResourceSemantics.head, expose_without_alias a index hAlias]

public theorem shareable_semantic {a : Assumptions} (sc : ShareableComplete a = true) :
    ∀ t : Ty, t.shareableUnder a.shareableVariables = Obend.Core.RecursiveRows.shareable a t
  | .variable index => by simp [Ty.shareableUnder, semantic_variable sc]
  | .natural => by simp [Ty.shareableUnder, Ty.shareable]
  | .label => by simp [Ty.shareableUnder, Ty.shareable]
  | .boolean => by simp [Ty.shareableUnder, Ty.shareable]
  | .emptyRow => by simp [Ty.shareableUnder, Ty.shareable]
  | .custody _ => by simp [Ty.shareableUnder, Ty.shareable]
  | .arrow .. => by simp [Ty.shareableUnder, Ty.shareable]
  | .computation .. => by simp [Ty.shareableUnder, Ty.shareable]
  | .field _ member tail => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_field,
      shareable_semantic sc member, shareable_semantic sc tail]
  | .specification m e => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_specification,
      shareable_semantic sc m, shareable_semantic sc e]
  | .prototype s t => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_prototype,
      shareable_semantic sc s, shareable_semantic sc t]
  | .variant row => by
    simp [Ty.shareableUnder, Obend.Core.RecursiveRows.shareable_variant, shareable_semantic sc row]

/-- Under `ShareableComplete`, syntactic `shareableUnder` is invariant under equi-recursive
agreement `sameType`. -/
public theorem shareable_congr {a : Assumptions} (sc : ShareableComplete a = true) {t u : Ty}
    (agrees : sameType a t u = true) :
    t.shareableUnder a.shareableVariables = u.shareableUnder a.shareableVariables := by
  rw [shareable_semantic sc, shareable_semantic sc]
  exact equivalent_shareable ((sameType_iff _ _ _).mp agrees)

/-! ### Custody-Freedom Invariance (`bearsCustody_congr`) Under `ShareableComplete` -/

theorem bound_custodyFree {a : Assumptions} (sc : ShareableComplete a = true) {index : Nat} {bound : Ty}
    (hlook : a.bounds.lookup index = some bound) : bound.bearsCustody = false := by
  have hmem := mem_of_lookup hlook
  simp only [ShareableComplete, Bool.and_eq_true, List.all_eq_true] at sc
  have hb := sc.2 (index, bound) hmem
  simpa [hlook] using hb

theorem aliasChain_bearsCustody {a : Assumptions} (sc : ShareableComplete a = true)
    {start finish : Ty} {path : List Nat} (chain : AliasChain a start path finish) :
    start.bearsCustody = finish.bearsCustody := by
  induction chain with
  | nil => rfl
  | @cons index body _ _ aliased _ _ ih =>
    have hb := bound_custodyFree sc (Assumptions.alias_bound aliased)
    rw [← ih, hb]; rfl

def labelCustodyFree : Label → Bool
  | .ordinary (.custody _) _ => false
  | _ => true

def labelStopsCustody : Label → Bool
  | .ordinary (.arrow _ _) _ | .ordinary .computation _ => true
  | _ => false

def custodyFreeGraph (a : Assumptions) : Obend.Core.FinitePresentation.Graph Node Bool where
  label := fun n => labelCustodyFree ((graph a).label n)
  successors := fun n => if labelStopsCustody ((graph a).label n) then [] else (graph a).successors n

theorem children_mem_right {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, Obend.Core.FiniteBisimulation.Children R xs ys →
      ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | [], [], _, _, hy => by cases hy
  | _ :: _, [], h, _, _ => False.elim h
  | [], _ :: _, h, _, _ => False.elim h
  | x :: xs, _ :: ys, ⟨hxy, hrest⟩, z, hz => by
    rcases List.mem_cons.mp hz with rfl | hmem
    · exact ⟨x, List.mem_cons_self, hxy⟩
    · obtain ⟨w, hw, hr⟩ := children_mem_right hrest z hmem
      exact ⟨w, List.mem_cons_of_mem _ hw, hr⟩

theorem bisimilar_custodyFree {a : Assumptions} {n₁ n₂ : Node}
    (hbisim : FP.Bisimilar (graph a) n₁ n₂)
    (hsafe : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) n₁) :
    Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) n₂ := by
  refine ⟨fun m => ∃ n, FP.Bisimilar (graph a) n m ∧ Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) n,
    ?_, ⟨n₁, hbisim, hsafe⟩⟩
  rintro m ⟨n, hrel, hnSafe⟩
  obtain ⟨hlab, hsucc⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) n m hrel
  obtain ⟨hnLab, hnChildren⟩ := Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) n hnSafe
  refine ⟨by simpa [custodyFreeGraph, hlab] using hnLab, ?_⟩
  intro child' hmem'
  simp only [custodyFreeGraph, ← hlab] at hmem'
  split at hmem'
  · cases hmem'
  · rename_i hnotStop
    obtain ⟨child, hmem, hcRel⟩ := children_mem_right hsucc child' hmem'
    have hcMem : child ∈ (custodyFreeGraph a).successors n := by
      simp [custodyFreeGraph, hnotStop, hmem]
    exact ⟨child, hcRel, hnChildren child hcMem⟩

theorem scanStream_bearsCustody_false {a : Assumptions} (sc : ShareableComplete a = true)
    (remaining : List Ty) (label : String) (first : Bool) {row m tl : Ty}
    (hrow : row.bearsCustody = false)
    (hemit : Obend.Core.RecursiveRows.scanStream a remaining label first row = .emit m tl) :
    m.bearsCustody = false ∧ tl.bearsCustody = false := by
  rw [Obend.Core.RecursiveRows.scanStream] at hemit
  split at hemit
  · cases hemit
  · cases hemit
  · rename_i obs hexp
    split at hemit
    · cases hemit
    · rename_i fname fmem ftail htag hch
      have hshape : obs = ⟨.field fname, [fmem, ftail]⟩ := by cases obs; simp_all
      rw [hshape] at hexp
      obtain ⟨src, path, chain, raw⟩ := Obend.Core.TypeGraph.expose_constructor_chain a row _ hexp
      have hsrc : src = .field fname fmem ftail := by cases src <;> simp_all [constructorHead]
      subst hsrc
      have hbc := (aliasChain_bearsCustody sc chain).symm.trans hrow
      simp only [Ty.bearsCustody, Bool.or_eq_false_iff] at hbc
      split at hemit
      · split at hemit
        · cases hemit; exact hbc
        · exact scanStream_bearsCustody_false sc (remaining.erase row) label first hbc.2 hemit
      · cases hemit
    · cases hemit
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem scanResidual_bearsCustody_false {a : Assumptions} (sc : ShareableComplete a = true)
    (remaining : List Ty) {row res : Ty} (hrow : row.bearsCustody = false)
    (hres : Obend.Core.RecursiveRows.scanResidual a remaining row = .nonRow res) :
    res.bearsCustody = false := by
  rw [Obend.Core.RecursiveRows.scanResidual] at hres
  split at hres
  · cases hres
  · cases hres
  · rename_i obs hexp
    split at hres
    · cases hres
    · rename_i fname fmem ftail htag hch
      have hshape : obs = ⟨.field fname, [fmem, ftail]⟩ := by cases obs; simp_all
      rw [hshape] at hexp
      obtain ⟨src, path, chain, raw⟩ := Obend.Core.TypeGraph.expose_constructor_chain a row _ hexp
      have hsrc : src = .field fname fmem ftail := by cases src <;> simp_all [constructorHead]
      subst hsrc
      have hbc := (aliasChain_bearsCustody sc chain).symm.trans hrow
      simp only [Ty.bearsCustody, Bool.or_eq_false_iff] at hbc
      split at hres
      · exact scanResidual_bearsCustody_false sc (remaining.erase row) hbc.2 hres
      · cases hres
    · cases hres; exact hrow
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem safe_of_bearsCustody_false {a : Assumptions} (sc : ShareableComplete a = true)
    {t : Ty} (ht : t.bearsCustody = false) :
    Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type t) := by
  let P : Node → Prop := fun
    | .type u => u.bearsCustody = false
    | .stream row _ _ => row.bearsCustody = false
  have hRow {u : Ty} {obs : Constructor} (hu : u.bearsCustody = false)
      (hexp : expose a u = .constructor obs) (hrowTag : rowTag obs.tag = true) :
      (custodyFreeGraph a).label (.type u) = true ∧
        ∀ child ∈ (custodyFreeGraph a).successors (.type u), P child := by
    refine ⟨by simp [custodyFreeGraph, graph, observe, hexp, hrowTag, rowObservation, labelCustodyFree], ?_⟩
    intro child hmem
    simp only [custodyFreeGraph, graph, observe, hexp, hrowTag, ↓reduceIte, rowObservation,
      labelStopsCustody, Bool.false_eq_true, rowChildren, List.mem_append, List.mem_map] at hmem
    rcases hmem with ⟨lbl, _, rfl⟩ | htail
    · exact hu
    · cases hres : RR.residual a u with
      | nonRow res =>
        simp only [hres, tailChildren, List.mem_cons, List.not_mem_nil, or_false] at htail
        subst child
        exact scanResidual_bearsCustody_false sc _ hu hres
      | _ => simp [hres, tailChildren] at htail
  refine ⟨P, ?_, ht⟩
  intro n hn
  cases n with
  | stream row label first =>
    change row.bearsCustody = false at hn
    cases hstep : RR.streamStep a row label first with
    | «end» _ => simp [custodyFreeGraph, graph, observe, hstep, labelCustodyFree, labelStopsCustody]
    | emit m tl =>
      obtain ⟨hm, htl⟩ := scanStream_bearsCustody_false sc _ label first hn hstep
      refine ⟨by simp [custodyFreeGraph, graph, observe, hstep, labelCustodyFree], ?_⟩
      intro child hmem
      simp only [custodyFreeGraph, graph, observe, hstep, labelStopsCustody,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> assumption
  | type u =>
    change u.bearsCustody = false at hn
    cases hexp : expose a u with
    | nominal idx => simp [custodyFreeGraph, graph, observe, hexp, labelCustodyFree, labelStopsCustody]
    | unproductive idx => simp [custodyFreeGraph, graph, observe, hexp, labelCustodyFree, labelStopsCustody]
    | constructor obs =>
      obtain ⟨src, path, chain, hhead⟩ := Obend.Core.TypeGraph.expose_constructor_chain a u _ hexp
      have hsrc : src.bearsCustody = false := (aliasChain_bearsCustody sc chain).symm.trans hn
      cases src with
      | «variable» _ => simp [constructorHead] at hhead
      | custody _ => simp [Ty.bearsCustody] at hsrc
      | natural | label | boolean =>
        cases hhead; simp [custodyFreeGraph, graph, observe, hexp, rowTag, labelCustodyFree, labelStopsCustody]
      | arrow _ _ _ _ =>
        cases hhead; simp [custodyFreeGraph, graph, observe, hexp, rowTag, labelCustodyFree, labelStopsCustody]
      | computation _ _ _ =>
        cases hhead; simp [custodyFreeGraph, graph, observe, hexp, rowTag, labelCustodyFree, labelStopsCustody]
      | specification m e =>
        cases hhead
        simp only [Ty.bearsCustody, Bool.or_eq_false_iff] at hsrc
        refine ⟨by simp [custodyFreeGraph, graph, observe, hexp, rowTag, labelCustodyFree], ?_⟩
        intro child hmem
        simp only [custodyFreeGraph, graph, observe, hexp, rowTag, Bool.false_eq_true, ↓reduceIte,
          labelStopsCustody, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact hsrc.1
        · exact hsrc.2
      | prototype s g =>
        cases hhead
        simp only [Ty.bearsCustody, Bool.or_eq_false_iff] at hsrc
        refine ⟨by simp [custodyFreeGraph, graph, observe, hexp, rowTag, labelCustodyFree], ?_⟩
        intro child hmem
        simp only [custodyFreeGraph, graph, observe, hexp, rowTag, Bool.false_eq_true, ↓reduceIte,
          labelStopsCustody, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact hsrc.1
        · exact hsrc.2
      | variant row =>
        cases hhead
        simp only [Ty.bearsCustody] at hsrc
        refine ⟨by simp [custodyFreeGraph, graph, observe, hexp, rowTag, labelCustodyFree], ?_⟩
        intro child hmem
        simp only [custodyFreeGraph, graph, observe, hexp, rowTag, Bool.false_eq_true, ↓reduceIte,
          labelStopsCustody, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        subst child; exact hsrc
      | emptyRow =>
        cases hhead; exact hRow hn hexp rfl
      | field _ _ _ =>
        cases hhead; exact hRow hn hexp rfl

theorem safe_stream_false_to_true {a : Assumptions} (sc : ShareableComplete a = true)
    {row : Ty} {name : String}
    (h : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream row name false)) :
    Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream row name true) := by
  cases hemit : RR.streamStep a row name true with
  | «end» _ =>
    exact Obend.Core.FiniteSafety.safe_of_children
      (by simp [custodyFreeGraph, graph, observe, hemit, labelCustodyFree])
      (by simp [custodyFreeGraph, graph, observe, hemit, labelStopsCustody])
  | emit m tl =>
    cases hsh : RR.shareable a m with
    | false =>
      exact bisimilar_custodyFree (hide_emit_resourceful a row m tl name hsh hemit) h
    | true =>
      have hmSh : m.shareableUnder a.shareableVariables = true := by
        rw [shareable_semantic sc]; exact hsh
      have hmSafe : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type m) :=
        safe_of_bearsCustody_false sc (Ty.bearsCustody_of_shareableUnder hmSh)
      have htlSafe : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream tl name false) :=
        bisimilar_custodyFree (RowHit.hide_emit_shareable a name row m tl hemit hsh) h
      refine Obend.Core.FiniteSafety.safe_of_children
        (by simp [custodyFreeGraph, graph, observe, hemit, labelCustodyFree]) ?_
      intro child hmem
      simp only [custodyFreeGraph, graph, observe, hemit, labelStopsCustody,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hmSafe
      · exact htlSafe

theorem safe_field_components {a : Assumptions} (sc : ShareableComplete a = true)
    {name : String} {member tail : Ty}
    (h : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type (.field name member tail))) :
    Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type member) ∧
      Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type tail) := by
  let r := Ty.field name member tail
  have hObsR : observe a (.type r) = rowObservation a r := by
    simp [r, observe, raw_field_observation, rowTag]
  have hClosedR := (Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) (.type r) h).2
  have hSuccR : ∀ c ∈ (RR.labels a r).map (fun l => Node.stream r l true) ++ tailChildren (RR.residual a r),
      Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) c := by
    intro c hc
    apply hClosedR
    simpa [custodyFreeGraph, graph, hObsR, rowObservation, labelStopsCustody, rowChildren] using hc
  have hNameIn : name ∈ RR.labels a r := by
    dsimp only [r]; rw [Obend.Core.RecursiveRows.labels_field]
    exact (Obend.Core.RecursiveRows.mem_insertLabel name name _).mpr (.inl rfl)
  have hStreamR : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream r name true) :=
    hSuccR _ (List.mem_append_left _ (List.mem_map.mpr ⟨name, hNameIn, rfl⟩))
  have hEmitR : observe a (.stream r name true) = (.streamEmit, [.type member, .stream tail name false]) :=
    RowHit.stream_emit_observe_eq a name true r member tail (by simp [r, RowHit.step, raw_field_observation])
  have hEmitChildren := (Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) (.stream r name true) hStreamR).2
  have hmSafe : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type member) :=
    hEmitChildren _ (by simp [custodyFreeGraph, graph, hEmitR, labelStopsCustody])
  have htlFalse : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream tail name false) :=
    hEmitChildren _ (by simp [custodyFreeGraph, graph, hEmitR, labelStopsCustody])
  have htlName : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream tail name true) :=
    safe_stream_false_to_true sc htlFalse
  refine ⟨hmSafe, ?_⟩
  cases hexp : expose a tail with
  | nominal _ =>
    exact Obend.Core.FiniteSafety.safe_of_children
      (by simp [custodyFreeGraph, graph, observe, hexp, labelCustodyFree])
      (by simp [custodyFreeGraph, graph, observe, hexp, labelStopsCustody])
  | unproductive _ =>
    exact Obend.Core.FiniteSafety.safe_of_children
      (by simp [custodyFreeGraph, graph, observe, hexp, labelCustodyFree])
      (by simp [custodyFreeGraph, graph, observe, hexp, labelStopsCustody])
  | constructor obs =>
    by_cases hrow : rowTag obs.tag = true
    · refine Obend.Core.FiniteSafety.safe_of_children
        (by simp [custodyFreeGraph, graph, observe, hexp, hrow, rowObservation, labelCustodyFree]) ?_
      intro child hmem
      simp only [custodyFreeGraph, graph, observe, hexp, hrow, ↓reduceIte, rowObservation,
        labelStopsCustody, Bool.false_eq_true, rowChildren, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨lbl, hlbl, rfl⟩ | htail
      · by_cases hsame : lbl = name
        · subst hsame; exact htlName
        · have hLblInR : lbl ∈ RR.labels a r := by
            dsimp only [r]; rw [Obend.Core.RecursiveRows.labels_field]
            exact (Obend.Core.RecursiveRows.mem_insertLabel name lbl _).mpr (.inr hlbl)
          have hStreamRL : Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.stream r lbl true) :=
            hSuccR _ (List.mem_append_left _ (List.mem_map.mpr ⟨lbl, hLblInR, rfl⟩))
          have hSkip : observe a (.stream r lbl true) = observe a (.stream tail lbl true) :=
            RowHit.stream_skip_observe_eq a lbl true r tail
              (by simp [r, RowHit.step, raw_field_observation, Ne.symm hsame])
          obtain ⟨hLabL, hChL⟩ := Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) _ hStreamRL
          have hLEq : (custodyFreeGraph a).label (.stream tail lbl true) =
              (custodyFreeGraph a).label (.stream r lbl true) := by
            change labelCustodyFree (observe a (.stream tail lbl true)).1 =
              labelCustodyFree (observe a (.stream r lbl true)).1
            rw [hSkip]
          have hCEq : ∀ c, c ∈ (custodyFreeGraph a).successors (.stream tail lbl true) →
              c ∈ (custodyFreeGraph a).successors (.stream r lbl true) := by
            intro c hc
            change c ∈ (if labelStopsCustody (observe a (.stream tail lbl true)).1 = true then []
              else (observe a (.stream tail lbl true)).2) at hc
            change c ∈ (if labelStopsCustody (observe a (.stream r lbl true)).1 = true then []
              else (observe a (.stream r lbl true)).2)
            rwa [hSkip]
          exact Obend.Core.FiniteSafety.safe_of_children
            (hLEq.trans hLabL)
            (fun c hc => hChL c (hCEq c hc))
      · rw [← Obend.Core.RecursiveRows.residual_field a name member tail] at htail
        exact hSuccR child (List.mem_append_right _ htail)
    · have hresTail : RR.residual a tail = .nonRow tail :=
        (nonrow_scans a tail obs hexp hrow).2
      have hresR : RR.residual a r = .nonRow tail := by
        dsimp only [r]; rw [Obend.Core.RecursiveRows.residual_field, hresTail]
      exact hSuccR (.type tail) (List.mem_append_right _ (by simp [hresR, tailChildren]))

theorem bearsCustody_false_of_safe {a : Assumptions} (sc : ShareableComplete a = true) :
    ∀ {t : Ty}, Obend.Core.FiniteSafety.Safe (custodyFreeGraph a) (.type t) → t.bearsCustody = false
  | .natural, _ | .label, _ | .boolean, _ | .variable _, _ | .arrow .., _ | .emptyRow, _
  | .computation .., _ => rfl
  | .custody id, h => by
    have hlab := (Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) _ h).1
    simp [custodyFreeGraph, graph, observe, expose, exposeWalk, constructorHead, rowTag, labelCustodyFree] at hlab
  | .specification m e, h => by
    have hch := (Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) _ h).2
    have hm := bearsCustody_false_of_safe sc (hch (.type m)
      (by simp [custodyFreeGraph, graph, observe_specification, labelStopsCustody]))
    have he := bearsCustody_false_of_safe sc (hch (.type e)
      (by simp [custodyFreeGraph, graph, observe_specification, labelStopsCustody]))
    simp [Ty.bearsCustody, hm, he]
  | .prototype s g, h => by
    have hch := (Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) _ h).2
    have hs := bearsCustody_false_of_safe sc (hch (.type s)
      (by simp [custodyFreeGraph, graph, observe_prototype, labelStopsCustody]))
    have hg := bearsCustody_false_of_safe sc (hch (.type g)
      (by simp [custodyFreeGraph, graph, observe_prototype, labelStopsCustody]))
    simp [Ty.bearsCustody, hs, hg]
  | .variant row, h => by
    have hch := (Obend.Core.FiniteSafety.safe_closed (custodyFreeGraph a) _ h).2
    have hr := bearsCustody_false_of_safe sc (hch (.type row)
      (by simp [custodyFreeGraph, graph, observe_variant, labelStopsCustody]))
    simp [Ty.bearsCustody, hr]
  | .field _ _ _, h => by
    obtain ⟨hm, htl⟩ := safe_field_components sc h
    simp [Ty.bearsCustody, bearsCustody_false_of_safe sc hm, bearsCustody_false_of_safe sc htl]

/-- Under `ShareableComplete`, `bearsCustody` is invariant under equi-recursive agreement `sameType`. -/
public theorem bearsCustody_congr {a : Assumptions} (sc : ShareableComplete a = true) {t u : Ty}
    (agrees : sameType a t u = true) :
    t.bearsCustody = u.bearsCustody := by
  have hEqv := (sameType_iff _ _ _).mp agrees
  cases ht : t.bearsCustody <;> cases hu : u.bearsCustody
  · rfl
  · have hSafeU := bisimilar_custodyFree hEqv (safe_of_bearsCustody_false sc ht)
    rw [bearsCustody_false_of_safe sc hSafeU] at hu; cases hu
  · have hSafeT := bisimilar_custodyFree ((FP.bisimilar_equivalence (graph a)).symm hEqv)
      (safe_of_bearsCustody_false sc hu)
    rw [bearsCustody_false_of_safe sc hSafeT] at ht; cases ht
  · rfl

/-! ### Unconditional Weak-Head (`whnf`) Inversion Over Arbitrary `Assumptions` -/

theorem insertCanonical_not_variable (row : Ty) (name : String) (member : Ty) (idx : Nat) :
    row.insertCanonical name member ≠ .variable idx := by
  cases row with
  | field prior old tail =>
    simp only [Ty.insertCanonical]
    split
    · split <;> simp
    · split <;> simp
  | _ => simp [Ty.insertCanonical]

theorem canonical_not_variable {t : Ty} (nonvar : ∀ idx, t ≠ .variable idx) (idx : Nat) :
    t.canonical ≠ .variable idx := by
  cases t with
  | «variable» i => exact False.elim (nonvar i rfl)
  | field name member tail => exact insertCanonical_not_variable tail.canonical name member.canonical idx
  | _ => simp [Ty.canonical]

theorem unfoldHead_nonvariable {a : Assumptions} {t : Ty} (nonvar : ∀ idx, t ≠ .variable idx) :
    a.unfoldHead t = t := by
  cases t with
  | «variable» idx => exact False.elim (nonvar idx rfl)
  | _ => rfl

theorem chase_nonvariable {a : Assumptions} {t : Ty} (nonvar : ∀ idx, t ≠ .variable idx) :
    ∀ k : Nat, a.chase k t = t
  | 0 => rfl
  | k + 1 => by rw [Assumptions.chase, unfoldHead_nonvariable nonvar, chase_nonvariable nonvar k]

theorem chase_of_aliasChain {a : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain a start path finish) (nonvar : ∀ idx, finish ≠ .variable idx) :
    ∀ k : Nat, path.length ≤ k → a.chase k start.canonical = finish.canonical := by
  induction chain with
  | nil t =>
    intro k _
    exact chase_nonvariable (canonical_not_variable nonvar) k
  | @cons index body finish path aliased pure tail ih =>
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      have hk' : path.length ≤ k := by simpa using hk
      have hStep : a.unfoldHead (.variable index) = body.canonical := by
        simp [Assumptions.unfoldHead, aliased, pure]
      change a.chase k (a.unfoldHead (.variable index)) = finish.canonical
      rw [hStep]
      exact ih nonvar k hk'

theorem aliasChain_subset_bounds {a : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain a start path finish) :
    ∀ idx ∈ path, idx ∈ a.bounds.map Prod.fst := by
  induction chain with
  | nil _ => intro _ h; cases h
  | @cons index body _ path aliased _ tail ih =>
    intro idx hmem
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact List.mem_map.mpr ⟨(idx, body), mem_of_lookup (Assumptions.alias_bound aliased), rfl⟩
    · exact ih idx hrest

theorem length_erase_lt {x : Nat} {l : List Nat} (hx : x ∈ l) : (l.erase x).length < l.length := by
  have heq := List.length_erase_of_mem hx
  have hpos := List.length_pos_of_mem hx
  omega

theorem mem_erase_of_ne {x y : Nat} (hne : x ≠ y) : ∀ {l : List Nat}, x ∈ l → x ∈ l.erase y
  | [], h => h
  | z :: zs, h => by
    simp only [List.erase_cons]
    by_cases hzy : (z == y) = true
    · have hz : z = y := eq_of_beq hzy
      subst hz
      rcases List.mem_cons.mp h with rfl | hm
      · exact False.elim (hne rfl)
      · simpa [hzy] using hm
    · simp only [hzy]
      rcases List.mem_cons.mp h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_erase_of_ne hne hm)

theorem nodup_length_le : ∀ {l₁ l₂ : List Nat}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l₂, hnd, hsub => by
    obtain ⟨hx_not_mem, hnd_xs⟩ := List.nodup_cons.mp hnd
    have hx_mem : x ∈ l₂ := hsub x List.mem_cons_self
    have hsub_xs : ∀ y ∈ xs, y ∈ l₂.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => by subst h; exact hx_not_mem hy
      exact mem_erase_of_ne hne (hsub y (List.mem_cons_of_mem _ hy))
    have ih := nodup_length_le hnd_xs hsub_xs
    have hlt := length_erase_lt hx_mem
    simp only [List.length_cons]
    omega

theorem expose_constructor_chain {a : Assumptions} {t : Ty} {obs : Constructor}
    (hexp : expose a t = .constructor obs) :
    ∃ source path, AliasChain a t path source ∧
      path.Nodup ∧
      (∀ idx, source ≠ .variable idx) ∧
      constructorHead source = .constructor obs := by
  obtain ⟨path, finish, chain, distinct, _, stopped⟩ :=
    exposeWalk_trace a (a.bounds.map Prod.fst) [] (initial_covers a) t
  change Stopped a (visitPath [] path) finish (expose a t) at stopped
  generalize hOut : expose a t = hd at stopped
  cases stopped with
  | productive _ nonvar =>
    rw [hexp] at hOut
    exact ⟨finish, path, chain, distinct, nonvar, hOut.symm⟩
  | unbound _ _ => rw [hexp] at hOut; cases hOut
  | activity _ _ _ => rw [hexp] at hOut; cases hOut
  | cycle _ => rw [hexp] at hOut; cases hOut

theorem whnf_of_expose_constructor {a : Assumptions} {t : Ty} {obs : Constructor}
    (hexp : expose a t = .constructor obs) :
    ∃ source, constructorHead source = .constructor obs ∧ whnf a t = source.canonical := by
  obtain ⟨source, path, chain, distinct, nonvar, hHead⟩ := expose_constructor_chain hexp
  have hlen : path.length ≤ a.bounds.length := by
    have h := nodup_length_le distinct (aliasChain_subset_bounds chain)
    simpa using h
  exact ⟨source, hHead, chase_of_aliasChain chain nonvar a.bounds.length hlen⟩

theorem expose_ordinary_of_head {a : Assumptions} {t : Ty} {tag : Tag}
    (hHead : labelHead ((graph a).label (.type t)) = .ordinary tag) :
    ∃ obs, expose a t = .constructor obs ∧ obs.tag = tag := by
  cases hexp : expose a t with
  | nominal idx => simp [graph, observe, hexp, labelHead] at hHead
  | unproductive idx => simp [graph, observe, hexp, labelHead] at hHead
  | constructor obs =>
    cases hr : rowTag obs.tag with
    | true => simp [graph, observe, hexp, hr, rowObservation, labelHead] at hHead
    | false =>
      simp only [graph, observe, hexp, hr, Bool.false_eq_true, ↓reduceIte, labelHead, HeadShape.ordinary.injEq] at hHead
      exact ⟨obs, rfl, hHead⟩

public theorem whnf_arrow_inv {a : Assumptions} {t : Ty} {r : Reuse} {q : Quantity} {d c : Ty}
    (agrees : sameType a t (.arrow r q d c) = true) :
    ∃ d' c', whnf a t = .arrow r q d' c' ∧ sameType a d' d = true ∧ sameType a c' c = true := by
  have hEqv := (sameType_iff _ _ _).mp agrees
  have hHead := equivalent_head hEqv
  simp only [graph, observe, expose, exposeWalk, constructorHead, rowTag, Bool.false_eq_true,
    ↓reduceIte, labelHead] at hHead
  obtain ⟨obs, hexp, htag⟩ := expose_ordinary_of_head hHead
  obtain ⟨source, hsrc, hwhnf⟩ := whnf_of_expose_constructor hexp
  cases source with
  | arrow r' q' d₀ c₀ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc
    simp only [Tag.arrow.injEq] at htag
    obtain ⟨hrEq, hqEq⟩ := htag
    subst r'; subst q'
    have hWhnfAgrees : sameType a (.arrow r q (Ty.canonical d₀) (Ty.canonical c₀)) (.arrow r q d c) = true := by
      simpa [hwhnf, Ty.canonical] using sameType_trans (whnf_sameType a t) agrees
    obtain ⟨_, _, hd, hc⟩ := arrow_components ((sameType_iff _ _ _).mp hWhnfAgrees)
    exact ⟨Ty.canonical d₀, Ty.canonical c₀, by simpa [Ty.canonical] using hwhnf,
      (sameType_iff _ _ _).mpr hd, (sameType_iff _ _ _).mpr hc⟩
  | «variable» _ => simp [constructorHead] at hsrc
  | _ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc; simp at htag

public theorem whnf_variant_inv {a : Assumptions} {t row : Ty}
    (agrees : sameType a t (.variant row) = true) :
    ∃ row', whnf a t = .variant row' ∧ sameType a row' row = true := by
  have hEqv := (sameType_iff _ _ _).mp agrees
  have hHead := equivalent_head hEqv
  simp only [graph, observe_variant, labelHead] at hHead
  obtain ⟨obs, hexp, htag⟩ := expose_ordinary_of_head hHead
  obtain ⟨source, hsrc, hwhnf⟩ := whnf_of_expose_constructor hexp
  cases source with
  | variant row₀ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc
    have hWhnfAgrees : sameType a (.variant (Ty.canonical row₀)) (.variant row) = true := by
      simpa [hwhnf, Ty.canonical] using sameType_trans (whnf_sameType a t) agrees
    have hrow := variant_components ((sameType_iff _ _ _).mp hWhnfAgrees)
    exact ⟨Ty.canonical row₀, by simpa [Ty.canonical] using hwhnf, (sameType_iff _ _ _).mpr hrow⟩
  | «variable» _ => simp [constructorHead] at hsrc
  | _ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc; simp at htag

public theorem whnf_specification_inv {a : Assumptions} {t m e : Ty}
    (agrees : sameType a t (.specification m e) = true) :
    ∃ m' e', whnf a t = .specification m' e' ∧ sameType a m' m = true ∧ sameType a e' e = true := by
  have hEqv := (sameType_iff _ _ _).mp agrees
  have hHead := equivalent_head hEqv
  simp only [graph, observe_specification, labelHead] at hHead
  obtain ⟨obs, hexp, htag⟩ := expose_ordinary_of_head hHead
  obtain ⟨source, hsrc, hwhnf⟩ := whnf_of_expose_constructor hexp
  cases source with
  | specification m₀ e₀ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc
    have hWhnfAgrees : sameType a (.specification (Ty.canonical m₀) (Ty.canonical e₀)) (.specification m e) = true := by
      simpa [hwhnf, Ty.canonical] using sameType_trans (whnf_sameType a t) agrees
    obtain ⟨hm, he⟩ := specification_components ((sameType_iff _ _ _).mp hWhnfAgrees)
    exact ⟨Ty.canonical m₀, Ty.canonical e₀, by simpa [Ty.canonical] using hwhnf,
      (sameType_iff _ _ _).mpr hm, (sameType_iff _ _ _).mpr he⟩
  | «variable» _ => simp [constructorHead] at hsrc
  | _ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc; simp at htag

public theorem whnf_prototype_inv {a : Assumptions} {t s g : Ty}
    (agrees : sameType a t (.prototype s g) = true) :
    ∃ s' g', whnf a t = .prototype s' g' ∧ sameType a s' s = true ∧ sameType a g' g = true := by
  have hEqv := (sameType_iff _ _ _).mp agrees
  have hHead := equivalent_head hEqv
  simp only [graph, observe_prototype, labelHead] at hHead
  obtain ⟨obs, hexp, htag⟩ := expose_ordinary_of_head hHead
  obtain ⟨source, hsrc, hwhnf⟩ := whnf_of_expose_constructor hexp
  cases source with
  | prototype s₀ g₀ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc
    have hWhnfAgrees : sameType a (.prototype (Ty.canonical s₀) (Ty.canonical g₀)) (.prototype s g) = true := by
      simpa [hwhnf, Ty.canonical] using sameType_trans (whnf_sameType a t) agrees
    obtain ⟨hs, hg⟩ := prototype_components ((sameType_iff _ _ _).mp hWhnfAgrees)
    exact ⟨Ty.canonical s₀, Ty.canonical g₀, by simpa [Ty.canonical] using hwhnf,
      (sameType_iff _ _ _).mpr hs, (sameType_iff _ _ _).mpr hg⟩
  | «variable» _ => simp [constructorHead] at hsrc
  | _ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc; simp at htag

public theorem whnf_computation_inv {a : Assumptions} {t p r x : Ty}
    (agrees : sameType a t (.computation p r x) = true) :
    ∃ p' r' x', whnf a t = .computation p' r' x' ∧
      sameType a p' p = true ∧ sameType a r' r = true ∧ sameType a x' x = true := by
  have hEqv := (sameType_iff _ _ _).mp agrees
  have hHead := equivalent_head hEqv
  simp only [graph, observe_computation, labelHead] at hHead
  obtain ⟨obs, hexp, htag⟩ := expose_ordinary_of_head hHead
  obtain ⟨source, hsrc, hwhnf⟩ := whnf_of_expose_constructor hexp
  cases source with
  | computation p₀ r₀ x₀ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc
    have hWhnfAgrees : sameType a (.computation (Ty.canonical p₀) (Ty.canonical r₀) (Ty.canonical x₀)) (.computation p r x) = true := by
      simpa [hwhnf, Ty.canonical] using sameType_trans (whnf_sameType a t) agrees
    obtain ⟨hp, hr, hx⟩ := computation_components ((sameType_iff _ _ _).mp hWhnfAgrees)
    exact ⟨Ty.canonical p₀, Ty.canonical r₀, Ty.canonical x₀, by simpa [Ty.canonical] using hwhnf,
      (sameType_iff _ _ _).mpr hp, (sameType_iff _ _ _).mpr hr, (sameType_iff _ _ _).mpr hx⟩
  | «variable» _ => simp [constructorHead] at hsrc
  | _ =>
    simp only [constructorHead, Head.constructor.injEq] at hsrc
    subst hsrc; simp at htag

/-- Lookup transports along equi-recursive agreement, in the checker's visited form. -/
public theorem lookupV_transport {a : Assumptions} {t row : Ty} (agrees : sameType a t row = true)
    {name : String} {member : Ty} (found : lookupV a.bounds [] row name = some member) :
    ∃ member', lookupV a.bounds [] t name = some member' ∧ sameType a member' member = true := by
  obtain ⟨fuel, h⟩ := (lookupV_iff _ _ _ _).1 found
  obtain ⟨depth, member', h', related⟩ :=
    Obend.Core.TypeGraph.equivalent_lookup_transport ((sameType_iff _ _ _).mp agrees) fuel name member h
  exact ⟨member', (lookupV_iff _ _ _ _).2 ⟨depth, h'⟩, (sameType_iff _ _ _).mpr related⟩

/-! ## 2. `exposeCallable` & `retargetCallable` Completeness Over Arbitrary `Assumptions` -/

theorem exposeCallable_sameType (a : Assumptions) :
    ∀ (fuel : Nat) (t : Ty), sameType a t (exposeCallable a fuel t) = true
  | 0, t => sameType_refl a t
  | fuel + 1, t => by
    simp only [exposeCallable]
    have hw := sameType_whnf a t
    split
    · rename_i m ext heq
      rw [heq] at hw
      exact sameType_trans hw (sameType_specification (sameType_refl a m) (exposeCallable_sameType a fuel ext))
    · exact hw

theorem retargetCallable_callable (t : Ty) (r : Reuse) (q : Quantity) (d c : Ty) :
    callable (retargetCallable t (.arrow r q d c)) = .arrow r q d c := by
  induction t with
  | specification m ext _ ih => simpa [retargetCallable, callable] using ih
  | _ => rfl

theorem sameType_retargetCallable {a : Assumptions} :
    ∀ {t : Ty} {r : Reuse} {q : Quantity} {d₀ c₀ d c : Ty},
      callable t = .arrow r q d₀ c₀ →
      sameType a d₀ d = true →
      sameType a c₀ c = true →
      sameType a t (retargetCallable t (.arrow r q d c)) = true
  | .arrow r' q' d' c', r, q, d₀, c₀, d, c, hcall, hd, hc => by
    simp only [callable, Ty.arrow.injEq] at hcall
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcall
    exact sameType_arrow hd hc
  | .specification m ext, r, q, d₀, c₀, d, c, hcall, hd, hc => by
    simp only [callable] at hcall
    exact sameType_specification (sameType_refl a m) (sameType_retargetCallable hcall hd hc)
  | .natural, _, _, _, _, _, _, h, _, _ | .label, _, _, _, _, _, _, h, _, _
  | .boolean, _, _, _, _, _, _, h, _, _ | .variable _, _, _, _, _, _, _, h, _, _
  | .emptyRow, _, _, _, _, _, _, h, _, _ | .field .., _, _, _, _, _, _, h, _, _
  | .prototype .., _, _, _, _, _, _, h, _, _ | .custody _, _, _, _, _, _, _, h, _, _
  | .variant _, _, _, _, _, _, _, h, _, _ | .computation .., _, _, _, _, _, _, h, _, _ => by
    simp [callable] at h

def specDepth : Ty → Nat
  | .specification _ ext => specDepth ext + 1
  | _ => 0

theorem arrow_not_sameType_specification {a : Assumptions} {r : Reuse} {q : Quantity} {d c m e : Ty}
    (agrees : sameType a (.arrow r q d c) (.specification m e) = true) : False := by
  have h := equivalent_head ((sameType_iff _ _ _).mp agrees)
  simp [graph, observe, expose, exposeWalk, constructorHead, rowTag, labelHead] at h

theorem callable_arrow_agrees {a : Assumptions} :
    ∀ {t₁ t₂ : Ty} {r₁ r₂ : Reuse} {q₁ q₂ : Quantity} {d₁ c₁ d₂ c₂ : Ty},
      callable t₁ = .arrow r₁ q₁ d₁ c₁ →
      callable t₂ = .arrow r₂ q₂ d₂ c₂ →
      sameType a t₁ t₂ = true →
      specDepth t₁ = specDepth t₂ ∧ r₁ = r₂ ∧ q₁ = q₂ ∧
        sameType a d₁ d₂ = true ∧ sameType a c₁ c₂ = true
  | .arrow r₁' q₁' d₁' c₁', .arrow r₂' q₂' d₂' c₂', r₁, r₂, q₁, q₂, d₁, c₁, d₂, c₂, hc₁, hc₂, agrees => by
    simp only [callable, Ty.arrow.injEq] at hc₁ hc₂
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc₁
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc₂
    obtain ⟨hr, hq, hd, hc⟩ := arrow_components ((sameType_iff _ _ _).mp agrees)
    exact ⟨rfl, hr, hq, (sameType_iff _ _ _).mpr hd, (sameType_iff _ _ _).mpr hc⟩
  | .arrow r₁' q₁' d₁' c₁', .specification m₂ e₂, _, _, _, _, _, _, _, _, hc₁, _, agrees =>
    False.elim (arrow_not_sameType_specification agrees)
  | .specification m₁ e₁, .arrow r₂' q₂' d₂' c₂', _, _, _, _, _, _, _, _, _, hc₂, agrees =>
    False.elim (arrow_not_sameType_specification (sameType_symm agrees))
  | .specification m₁ e₁, .specification m₂ e₂, r₁, r₂, q₁, q₂, d₁, c₁, d₂, c₂, hc₁, hc₂, agrees => by
    simp only [callable] at hc₁ hc₂
    obtain ⟨_, he⟩ := specification_components ((sameType_iff _ _ _).mp agrees)
    obtain ⟨hdepth, hr, hq, hd, hc⟩ := callable_arrow_agrees hc₁ hc₂ ((sameType_iff _ _ _).mpr he)
    exact ⟨by simp [specDepth, hdepth], hr, hq, hd, hc⟩
  | .natural, _, _, _, _, _, _, _, _, _, h, _, _ | .label, _, _, _, _, _, _, _, _, _, h, _, _
  | .boolean, _, _, _, _, _, _, _, _, _, h, _, _ | .variable _, _, _, _, _, _, _, _, _, _, h, _, _
  | .emptyRow, _, _, _, _, _, _, _, _, _, h, _, _ | .field .., _, _, _, _, _, _, _, _, _, h, _, _
  | .prototype .., _, _, _, _, _, _, _, _, _, h, _, _ | .custody _, _, _, _, _, _, _, _, _, _, h, _, _
  | .variant _, _, _, _, _, _, _, _, _, _, h, _, _ | .computation .., _, _, _, _, _, _, _, _, _, h, _, _ => by
    simp [callable] at h
  | _, .natural, _, _, _, _, _, _, _, _, _, h, _ | _, .label, _, _, _, _, _, _, _, _, _, h, _
  | _, .boolean, _, _, _, _, _, _, _, _, _, h, _ | _, .variable _, _, _, _, _, _, _, _, _, _, h, _
  | _, .emptyRow, _, _, _, _, _, _, _, _, _, h, _ | _, .field .., _, _, _, _, _, _, _, _, _, h, _
  | _, .prototype .., _, _, _, _, _, _, _, _, _, h, _ | _, .custody _, _, _, _, _, _, _, _, _, _, h, _
  | _, .variant _, _, _, _, _, _, _, _, _, _, h, _ | _, .computation .., _, _, _, _, _, _, _, _, _, h, _ => by
    simp [callable] at h

theorem aliasChain_last_bound {a : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain a start path finish) (nonvar : ∀ idx, finish ≠ .variable idx) :
    start = finish ∨
      ∃ lastIdx, a.bounds.lookup lastIdx = some finish ∧ sameType a start finish = true := by
  induction chain with
  | nil _ => exact .inl rfl
  | @cons index body finish path aliased pure tail ih =>
    have hStep : sameType a (.variable index) body = true :=
      (sameType_iff _ _ _).mpr (alias_equivalent a index body aliased pure)
    rcases ih nonvar with rfl | ⟨lastIdx, hlook, hsame⟩
    · exact .inr ⟨index, Assumptions.alias_bound aliased, hStep⟩
    · exact .inr ⟨lastIdx, hlook, sameType_trans hStep hsame⟩

def unvisitedBoundsNodes (bounds : Bounds) (seen : List Nat) : Nat :=
  ((bounds.filter fun p => !seen.contains p.1).map fun p => tyNodes p.2).sum

theorem unvisitedBoundsNodes_nil (bounds : Bounds) :
    unvisitedBoundsNodes bounds [] = (bounds.map (tyNodes ·.2)).sum := by
  induction bounds with
  | nil => rfl
  | cons hd tl ih =>
    have h : (!([] : List Nat).contains hd.1) = true := rfl
    simpa [unvisitedBoundsNodes, h] using ih

theorem unvisitedBoundsNodes_cons_def (hd : Nat × Ty) (tl : Bounds) (seen : List Nat) :
    unvisitedBoundsNodes (hd :: tl) seen =
      if (!seen.contains hd.1) = true then tyNodes hd.2 + unvisitedBoundsNodes tl seen
      else unvisitedBoundsNodes tl seen := by
  unfold unvisitedBoundsNodes
  simp only [List.filter_cons]
  split <;> simp

theorem unvisitedBoundsNodes_cons_le (bounds : Bounds) (i : Nat) (seen : List Nat) :
    unvisitedBoundsNodes bounds (i :: seen) ≤ unvisitedBoundsNodes bounds seen := by
  induction bounds with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    rw [unvisitedBoundsNodes_cons_def, unvisitedBoundsNodes_cons_def]
    cases h1 : (!(i :: seen).contains hd.1) with
    | true =>
      have h2 : (!seen.contains hd.1) = true := by
        cases hc : seen.contains hd.1 with
        | false => rfl
        | true =>
          have hmem : hd.1 ∈ i :: seen := List.mem_cons_of_mem i (List.contains_iff_mem.mp hc)
          have hc' : (i :: seen).contains hd.1 = true := List.contains_iff_mem.mpr hmem
          rw [hc'] at h1; cases h1
      simp only [h2, ↓reduceIte]
      omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      split <;> omega

theorem lookup_unvisitedBoundsNodes {bounds : Bounds} {i : Nat} {bound : Ty} {seen : List Nat}
    (hlook : bounds.lookup i = some bound) (hfresh : seen.contains i = false) :
    tyNodes bound + unvisitedBoundsNodes bounds (i :: seen) ≤ unvisitedBoundsNodes bounds seen := by
  induction bounds with
  | nil => simp [List.lookup] at hlook
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [List.lookup] at hlook
    by_cases hik : (i == k) = true
    · simp only [hik, Option.some.injEq] at hlook
      have hk : i = k := eq_of_beq hik
      subst hk; subst hlook
      have hDrop : (!(i :: seen).contains i) = false := by
        have hc : (i :: seen).contains i = true := List.contains_iff_mem.mpr List.mem_cons_self
        rw [hc]; rfl
      have hKeep : (!seen.contains i) = true := by rw [hfresh]; rfl
      have hRest := unvisitedBoundsNodes_cons_le tl i seen
      rw [unvisitedBoundsNodes_cons_def, unvisitedBoundsNodes_cons_def]
      simp only [hDrop, hKeep, Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [hik] at hlook
      have hne : k ≠ i := fun h => by subst h; simp at hik
      have hSame : (!(i :: seen).contains k) = (!seen.contains k) := by
        cases hck : seen.contains k with
        | true =>
          have hc' : (i :: seen).contains k = true :=
            List.contains_iff_mem.mpr (List.mem_cons_of_mem i (List.contains_iff_mem.mp hck))
          rw [hc']
        | false =>
          cases hc' : (i :: seen).contains k with
          | false => rfl
          | true =>
            rcases List.mem_cons.mp (List.contains_iff_mem.mp hc') with rfl | hm
            · exact False.elim (hne rfl)
            · rw [List.contains_iff_mem.mpr hm] at hck; cases hck
      have hRec := ih hlook
      rw [unvisitedBoundsNodes_cons_def, unvisitedBoundsNodes_cons_def, hSame]
      split <;> omega

theorem tyNodes_pos (t : Ty) : 0 < tyNodes t := by
  cases t <;> simp [tyNodes] <;> omega

theorem specDepth_le_potential {a : Assumptions} {r : Reuse} {q : Quantity} {d c : Ty} :
    ∀ (target : Ty),
      callable target = .arrow r q d c →
      ∀ (t : Ty) (seen : List (Nat × Ty)),
        sameType a t target = true →
        (∀ p ∈ seen, ∃ m₁ e₁,
          a.bounds.lookup p.1 = some (.specification m₁ e₁) ∧
          callable p.2 = .arrow r q d c ∧
          sameType a e₁ p.2 = true ∧
          specDepth target ≤ specDepth p.2) →
        specDepth target ≤ tyNodes t + unvisitedBoundsNodes a.bounds (seen.map Prod.fst)
  | .arrow _ _ _ _, _, _, _, _, _ => Nat.zero_le _
  | .specification m₀ e₀, hcall, t, seen, agrees, hseen => by
    simp only [callable] at hcall
    have hHead := equivalent_head ((sameType_iff _ _ _).mp agrees)
    simp only [graph, observe_specification, labelHead] at hHead
    obtain ⟨obs, hexp, htag⟩ := expose_ordinary_of_head hHead
    obtain ⟨source', path, chain, _, nonvar', hsrc'⟩ := expose_constructor_chain hexp
    have hLast := aliasChain_last_bound chain nonvar'
    clear chain nonvar'
    cases source' with
    | specification m₁ e₁ =>
      rcases hLast with rfl | ⟨lastIdx, hlook, hsameSrc⟩
      · obtain ⟨_, he⟩ := specification_components ((sameType_iff _ _ _).mp agrees)
        have hseen' : ∀ p ∈ seen, ∃ m' e',
            a.bounds.lookup p.1 = some (.specification m' e') ∧
            callable p.2 = .arrow r q d c ∧
            sameType a e' p.2 = true ∧
            specDepth e₀ ≤ specDepth p.2 := by
          intro p hp
          obtain ⟨m', e', hl, hc, hs, hle⟩ := hseen p hp
          exact ⟨m', e', hl, hc, hs, by simp [specDepth] at hle; omega⟩
        have ih := specDepth_le_potential e₀ hcall e₁ seen ((sameType_iff _ _ _).mpr he) hseen'
        have hmPos := tyNodes_pos m₁
        simp only [specDepth, tyNodes]
        omega
      · have hSpecAgrees : sameType a (.specification m₁ e₁) (.specification m₀ e₀) = true :=
          sameType_trans (sameType_symm hsameSrc) agrees
        obtain ⟨_, he⟩ := specification_components ((sameType_iff _ _ _).mp hSpecAgrees)
        have heSame : sameType a e₁ e₀ = true := (sameType_iff _ _ _).mpr he
        have hfresh : (seen.map Prod.fst).contains lastIdx = false := by
          cases hc : (seen.map Prod.fst).contains lastIdx with
          | false => rfl
          | true =>
            obtain ⟨⟨idx', prevT⟩, hmem, hidx⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
            simp only at hidx; subst idx'
            obtain ⟨m', e', hl, hcallPrev, hsamePrev, hle⟩ := hseen (lastIdx, prevT) hmem
            rw [hlook] at hl; injection hl with hl; injection hl with _ heEq; subst heEq
            have hPrevEq : sameType a e₀ prevT = true :=
              sameType_trans (sameType_symm heSame) hsamePrev
            have hDepthEq : specDepth e₀ = specDepth prevT := (callable_arrow_agrees hcall hcallPrev hPrevEq).1
            change specDepth (.specification m₀ e₀) ≤ specDepth prevT at hle
            simp only [specDepth] at hle
            omega
        have hseen' : ∀ p ∈ (lastIdx, e₀) :: seen, ∃ m' e',
            a.bounds.lookup p.1 = some (.specification m' e') ∧
            callable p.2 = .arrow r q d c ∧
            sameType a e' p.2 = true ∧
            specDepth e₀ ≤ specDepth p.2 := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hold
          · exact ⟨m₁, e₁, hlook, hcall, heSame, Nat.le_refl _⟩
          · obtain ⟨m', e', hl, hc, hs, hle⟩ := hseen p hold
            exact ⟨m', e', hl, hc, hs, by simp [specDepth] at hle; omega⟩
        have ih := specDepth_le_potential e₀ hcall e₁ ((lastIdx, e₀) :: seen) heSame hseen'
        have hDrop := lookup_unvisitedBoundsNodes hlook hfresh
        have hmPos := tyNodes_pos m₁
        have htPos := tyNodes_pos t
        simp only [List.map_cons, tyNodes] at ih hDrop
        simp only [specDepth]
        omega
    | «variable» _ => simp [constructorHead] at hsrc'
    | _ =>
      simp only [constructorHead, Head.constructor.injEq] at hsrc'
      subst hsrc'
      simp at htag
  | .natural, h, _, _, _, _ | .label, h, _, _, _, _ | .boolean, h, _, _, _, _
  | .variable _, h, _, _, _, _ | .emptyRow, h, _, _, _, _ | .field .., h, _, _, _, _
  | .prototype .., h, _, _, _, _ | .custody _, h, _, _, _, _ | .variant _, h, _, _, _, _
  | .computation .., h, _, _, _, _ => by simp [callable] at h

theorem exposeCallable_of_specDepth_le {a : Assumptions} :
    ∀ {target : Ty} {r : Reuse} {q : Quantity} {d c t : Ty} {fuel : Nat},
      callable target = .arrow r q d c →
      sameType a t target = true →
      specDepth target < fuel →
      ∃ d' c', callable (exposeCallable a fuel t) = .arrow r q d' c' ∧
        sameType a d' d = true ∧ sameType a c' c = true
  | .arrow r₀ q₀ d₀ c₀, r, q, d, c, t, fuel, hcall, agrees, hlt => by
    simp only [callable, Ty.arrow.injEq] at hcall
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcall
    cases fuel with
    | zero => simp [specDepth] at hlt
    | succ fuel =>
      obtain ⟨d', c', hwhnf, hd, hc⟩ := whnf_arrow_inv agrees
      exact ⟨d', c', by simp [exposeCallable, hwhnf, callable], hd, hc⟩
  | .specification m₀ e₀, r, q, d, c, t, fuel, hcall, agrees, hlt => by
    simp only [callable] at hcall
    cases fuel with
    | zero => simp [specDepth] at hlt
    | succ fuel =>
      simp only [specDepth, Nat.add_lt_add_iff_right] at hlt
      obtain ⟨m', e', hwhnf, _, he⟩ := whnf_specification_inv agrees
      obtain ⟨d', c', hcall', hd, hc⟩ := exposeCallable_of_specDepth_le hcall he hlt
      exact ⟨d', c', by simpa [exposeCallable, hwhnf, callable] using hcall', hd, hc⟩
  | .natural, _, _, _, _, _, _, h, _, _ | .label, _, _, _, _, _, _, h, _, _
  | .boolean, _, _, _, _, _, _, h, _, _ | .variable _, _, _, _, _, _, _, h, _, _
  | .emptyRow, _, _, _, _, _, _, h, _, _ | .field .., _, _, _, _, _, _, h, _, _
  | .prototype .., _, _, _, _, _, _, h, _, _ | .custody _, _, _, _, _, _, _, h, _, _
  | .variant _, _, _, _, _, _, _, h, _, _ | .computation .., _, _, _, _, _, _, h, _, _ => by
    simp [callable] at h

/-- `exposeCallable` with the fuel `Prepare` supplies (`tyNodes t + boundsNodes + 1`) unfolds
every callable specification/alias chain to an explicit `.arrow` with agreeing components, over
**all** `Assumptions`! -/
public theorem exposeCallable_transport {a : Assumptions} {target t : Ty}
    {r : Reuse} {q : Quantity} {d c : Ty}
    (agrees : sameType a t target = true) (shape : callable target = .arrow r q d c) :
    ∃ d' c',
      callable (exposeCallable a (tyNodes t + (a.bounds.map (tyNodes ·.2)).sum + 1) t) =
        .arrow r q d' c' ∧
      sameType a d' d = true ∧ sameType a c' c = true := by
  have hle := specDepth_le_potential target shape t [] agrees (by intro _ h; cases h)
  rw [List.map_nil, unvisitedBoundsNodes_nil] at hle
  exact exposeCallable_of_specDepth_le shape agrees (Nat.lt_succ_of_le hle)

/-! ## 3. Context Refinement (`Refines`) Under `ShareableComplete` -/

public def QuantityRefines (a : Assumptions) (b' b : Binding) : Prop :=
  b'.quantity = b.quantity ∨
    (b'.quantity = .affine ∧ b'.type.bearsCustody = false ∧ b.quantity ≠ .unrestricted) ∨
    (b'.quantity = .unrestricted ∧ b'.type.shareableUnder a.shareableVariables = true)

public def BindingRefines (a : Assumptions) (b' b : Binding) : Prop :=
  sameType a b'.type b.type = true ∧ QuantityRefines a b' b

public inductive Refines (a : Assumptions) : Context → Context → Prop where
  | nil : Refines a [] []
  | cons {b' b : Binding} {Γ' Γ : Context} :
      BindingRefines a b' b → Refines a Γ' Γ → Refines a (b' :: Γ') (b :: Γ)

public theorem refines_refl {a : Assumptions} (Γ : Context) : Refines a Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons b rest ih => exact .cons ⟨sameType_refl _ _, .inl rfl⟩ ih

public theorem refines_same_quantity {a : Assumptions} {Γ' Γ : Context} {t t' : Ty} {q : Quantity}
    (agrees : sameType a t' t = true) (tail : Refines a Γ' Γ) :
    Refines a (⟨t', q⟩ :: Γ') (⟨t, q⟩ :: Γ) := .cons ⟨agrees, .inl rfl⟩ tail

public theorem refines_length {a : Assumptions} {Γ' Γ : Context} (h : Refines a Γ' Γ) :
    Γ'.length = Γ.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

public theorem refines_getElem {a : Assumptions} {Γ' Γ : Context} (h : Refines a Γ' Γ) :
    ∀ {index : Nat} {binding : Binding}, Γ[index]? = some binding →
      ∃ binding', Γ'[index]? = some binding' ∧ BindingRefines a binding' binding := by
  induction h with
  | nil => intro index binding found; simp at found
  | cons head _ ih =>
    intro index binding found
    cases index with
    | zero => simp at found; subst found; exact ⟨_, rfl, head⟩
    | succ index => simpa using ih (by simpa using found)

theorem safeQuantity_refines {a : Assumptions} {b' b : Binding} (h : QuantityRefines a b' b)
    {count : Nat} (safe : safeQuantity b.quantity count = true) :
    safeQuantity b'.quantity count = true := by
  rcases h with same | ⟨affine, _, notU⟩ | ⟨unrestricted, _⟩
  · rw [same]; exact safe
  · rw [affine]; cases hq : b.quantity <;> simp_all [safeQuantity] <;> omega
  · rw [unrestricted]; rfl

public theorem safeUses_refines {a : Assumptions} {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {uses : Uses} (safe : safeUses Γ uses = true) : safeUses Γ' uses = true := by
  induction h generalizing uses with
  | nil => exact safe
  | cons head _ ih =>
    cases uses with
    | nil => simp [safeUses] at safe
    | cons count rest =>
      simp only [safeUses, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        beq_iff_eq, Nat.add_right_cancel_iff] at safe ⊢
      have tail := ih (uses := rest) (by simp [safeUses, safe.1, safe.2.2])
      simp only [safeUses, Bool.and_eq_true, beq_iff_eq] at tail
      exact ⟨tail.1, safeQuantity_refines head.2 safe.2.1, tail.2⟩

public theorem validContext_refines {a : Assumptions} (sc : ShareableComplete a = true)
    {Γ' Γ : Context} (h : Refines a Γ' Γ)
    (valid : validContext a.shareableVariables Γ = true) :
    validContext a.shareableVariables Γ' = true := by
  induction h with
  | nil => exact valid
  | @cons b' b _ _ head _ ih =>
    simp only [validContext, List.all_cons, Bool.and_eq_true] at valid ⊢
    refine ⟨?_, ih valid.2⟩
    have hb := valid.1
    rcases head with ⟨agrees, same | ⟨affine, noCust, _⟩ | ⟨unrestricted, share⟩⟩
    · simp only [mustBeLinear] at hb ⊢
      rw [same, shareable_congr sc agrees, bearsCustody_congr sc agrees]
      exact hb
    · simp [affine, mustBeLinear, noCust]
    · simp [unrestricted, share, mustBeLinear, Ty.bearsCustody_of_shareableUnder share]

public theorem reusableCaptures_refines {a : Assumptions} (sc : ShareableComplete a = true)
    {Γ' Γ : Context} (h : Refines a Γ' Γ) {uses : Uses}
    (captures : reusableCaptures a.shareableVariables Γ uses = true) :
    reusableCaptures a.shareableVariables Γ' uses = true := by
  induction h generalizing uses with
  | nil => exact captures
  | @cons b' b _ _ head _ ih =>
    cases uses with
    | nil => simp [reusableCaptures] at captures
    | cons count rest =>
      simp only [reusableCaptures, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        beq_iff_eq, Nat.add_right_cancel_iff] at captures ⊢
      have tail := ih (uses := rest) (by simp [reusableCaptures, captures.1, captures.2.2])
      simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq] at tail
      refine ⟨tail.1, ?_, tail.2⟩
      have hb := captures.2.1
      rcases head with ⟨agrees, same | ⟨affine, _, notU⟩ | ⟨unrestricted, share⟩⟩
      · rw [same, shareable_congr sc agrees]; exact hb
      · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hb ⊢
        rcases hb with zero | ⟨isU, _⟩
        · exact .inl zero
        · exact absurd (by simpa using isU) notU
      · simp [unrestricted, share]

public theorem reusableAllowed_refines {a : Assumptions} (sc : ShareableComplete a = true)
    {Γ' Γ : Context} (h : Refines a Γ' Γ) {reuse : Reuse} {uses : Uses}
    (allowed : reusableAllowed a reuse Γ uses = true) :
    reusableAllowed a reuse Γ' uses = true := by
  simp only [reusableAllowed, Bool.or_eq_true] at allowed ⊢
  exact allowed.imp id (reusableCaptures_refines sc h)

public theorem linearFree_refines {a : Assumptions} {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {uses : Uses} (free : linearFree Γ uses = true) : linearFree Γ' uses = true := by
  induction h generalizing uses with
  | nil => exact free
  | @cons b' b _ _ head _ ih =>
    cases uses with
    | nil => rfl
    | cons count rest =>
      simp only [linearFree, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at free ⊢
      refine ⟨?_, ih free.2⟩
      have q := head.2
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at free ⊢
      rcases free.1 with zero | notLinear
      · exact .inl zero
      · refine .inr ?_
        rcases q with same | ⟨affine, _, _⟩ | ⟨unrestricted, _⟩
        · rw [same]; exact notLinear
        · rw [affine]; decide
        · rw [unrestricted]; decide

public theorem branchesAgree_refines {a : Assumptions} {Γ' Γ : Context} (h : Refines a Γ' Γ)
    {first second : Uses} (agreeing : branchesAgree Γ first second = true) :
    branchesAgree Γ' first second = true := by
  induction h generalizing first second with
  | nil => cases first <;> cases second <;> rfl
  | @cons b' b _ _ head _ ih =>
    cases first with
    | nil => rfl
    | cons x first =>
      cases second with
      | nil => rfl
      | cons y second =>
        simp only [branchesAgree, Bool.and_eq_true] at agreeing ⊢
        refine ⟨?_, ih agreeing.2⟩
        have q := head.2
        have here := agreeing.1
        rcases q with same | ⟨affine, _, _⟩ | ⟨unrestricted, _⟩
        · rw [same]; exact here
        · rw [affine]; rfl
        · rw [unrestricted]; rfl

public theorem argumentAllowed_refines {a : Assumptions} (sc : ShareableComplete a = true)
    {Γ' Γ : Context} (h : Refines a Γ' Γ) {q : Quantity} {t t' : Ty} {uses : Uses}
    (agrees : sameType a t' t = true) (allowed : argumentAllowed a q Γ t uses = true) :
    argumentAllowed a q Γ' t' uses = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at allowed ⊢
  refine ⟨⟨by rw [sameType_isComputation agrees]; exact allowed.1.1,
    allowed.1.2.imp id (linearFree_refines h)⟩, ?_⟩
  rcases allowed.2 with notU | ⟨share, captures⟩
  · exact .inl notU
  · exact .inr ⟨by rw [shareable_congr sc agrees]; exact share, reusableCaptures_refines sc h captures⟩

/-! ## 4. The Expanded Syntactic Fragment (`.extend`, `.mix`, `.fix`, `.case`) -/

mutual
/-- Terms whose type preparation predicts from the context and declared bounds alone. -/
public inductive Synthable : Term → Prop where
  | bound (index : Nat) : Synthable (.bound index)
  | nat (value : Nat) : Synthable (.nat value)
  | boolean (value : Bool) : Synthable (.boolean value)
  | label (value : String) : Synthable (.label value)
  | app {function argument : Term} : Synthable function → Checkable argument →
      Synthable (.app function argument)
  | letIn {body argument : Term} : Synthable body → Synthable argument →
      Synthable (.app (.lam body) argument)
  | get {target : Term} (name : String) : Synthable target → Synthable (.get target name)
  | binary (primitive : Primitive) {left right : Term} : Checkable left → Checkable right →
      Synthable (.binary primitive left right)
  | extend {target : Term} {fields : List (String × Term)} :
      Synthable target → FieldsSynthable fields → Synthable (.extend target fields)
  | mix {lower upper : Term} : Synthable lower → Synthable upper →
      Synthable (.mix lower upper)
  | fix {spec inheritedTerm : Term} : Synthable spec → Checkable inheritedTerm →
      Synthable (.fix spec inheritedTerm)
  | caseCons {scrutinee : Term} {name : String} {body : Term} {rest : List (String × Term)} :
      Synthable scrutinee → Synthable body → FieldsCheckable rest →
      Synthable (.case scrutinee ((name, body) :: rest))
/-- Terms preparation checks against an expected type. -/
public inductive Checkable : Term → Prop where
  | synth {term : Term} : Synthable term → Checkable term
  | lam {body : Term} : Checkable body → Checkable (.lam body)
  | letIn {body argument : Term} : Checkable body → Synthable argument →
      Checkable (.app (.lam body) argument)
  | fixLam {body inheritedTerm : Term} : Checkable body → Synthable inheritedTerm →
      Checkable (.fix (.lam body) inheritedTerm)
  | ifBool {condition whenTrue whenFalse : Term} : Checkable condition → Checkable whenTrue →
      Checkable whenFalse → Checkable (.ifBool condition whenTrue whenFalse)
  | record {fields : List (String × Term)} : labelsDistinct fields = true → FieldsCheckable fields →
      Checkable (.record fields)
  | inject (tag : String) {payload : Term} : Checkable payload → Checkable (.inject tag payload)
  | case {scrutinee : Term} {arms : List (String × Term)} : Synthable scrutinee → FieldsCheckable arms →
      Checkable (.case scrutinee arms)
public inductive FieldsSynthable : List (String × Term) → Prop where
  | nil : FieldsSynthable []
  | cons {name : String} {body : Term} {rest : List (String × Term)} : Synthable body →
      FieldsSynthable rest → FieldsSynthable ((name, body) :: rest)
public inductive FieldsCheckable : List (String × Term) → Prop where
  | nil : FieldsCheckable []
  | cons {name : String} {body : Term} {rest : List (String × Term)} : Checkable body →
      FieldsCheckable rest → FieldsCheckable ((name, body) :: rest)
end

/-! ## 5. Preparation Motive & Per-Constructor Completeness -/

variable {a : Assumptions}

public def SynthOK (a : Assumptions) (Γ : Context) (t : Term) (derived : Ty) (uses : Uses) : Prop :=
  ∀ path, ∃ tree predicted, prepare a noHints Γ path t .synth = .ok (tree, predicted) ∧
    sameType a predicted derived = true ∧
    ∀ annotations, Realizes annotations path tree →
      Yields (synthAt a annotations Γ path t) (fun r => r.type = predicted ∧ r.uses = uses) ∧
      ∀ expected, sameType a predicted expected = true →
        Yields (checkAt a annotations Γ path t expected) (fun r => r.uses = uses)

public def CheckOK (a : Assumptions) (Γ : Context) (t : Term) (expected : Ty) (uses : Uses) : Prop :=
  ∀ path, ∃ tree result, prepare a noHints Γ path t (.check expected) = .ok (tree, result) ∧
    ∀ annotations, Realizes annotations path tree →
      Yields (checkAt a annotations Γ path t expected) (fun r => r.uses = uses)

public def Modes (a : Assumptions) (Γ : Context) (t : Term) (derived : Ty) (uses : Uses) : Prop :=
  (Synthable t → ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' t derived uses) ∧
  (Checkable t → ∀ Γ', Refines a Γ' Γ → ∀ expected, sameType a derived expected = true →
    CheckOK a Γ' t expected uses)

public def LamInv (a : Assumptions) (Γ : Context) (body : Term) (derived : Ty) (uses : Uses) : Prop :=
  ∃ reuse quantity domain codomain bodyUses,
    sameType a (.arrow reuse quantity domain codomain) derived = true ∧ uses = bodyUses.tail ∧
    safeUses (⟨domain, quantity⟩ :: Γ) bodyUses = true ∧
    validContext a.shareableVariables (⟨domain, quantity⟩ :: Γ) = true ∧
    quantity.fits (bodyUses.headD 0) = true ∧
    Modes a (⟨domain, quantity⟩ :: Γ) body codomain bodyUses

public def Motive (a : Assumptions) (Γ : Context) (t : Term) (derived : Ty) (uses : Uses) : Prop :=
  Modes a Γ t derived uses ∧ ∀ body, t = .lam body → LamInv a Γ body derived uses

theorem yields_elim {α : Type} {result : Except CheckRefusal α} {P : α → Prop}
    (yielded : Yields result P) : ∃ value, result = .ok value ∧ P value := by
  cases result with
  | ok value => exact ⟨value, rfl, yielded⟩
  | error _ => exact False.elim yielded

theorem synthOK_conversion {Γ : Context} {t : Term} {actual expected : Ty} {uses : Uses}
    (ok : SynthOK a Γ t actual uses) (agrees : sameType a actual expected = true) :
    SynthOK a Γ t expected uses := by
  intro path
  obtain ⟨tree, predicted, prepared, same, run⟩ := ok path
  exact ⟨tree, predicted, prepared, sameType_trans same agrees, run⟩

theorem motive_conversion {Γ : Context} {t : Term} {actual expected : Ty} {uses : Uses}
    (m : Motive a Γ t actual uses) (agrees : sameType a actual expected = true) :
    Motive a Γ t expected uses := by
  obtain ⟨⟨synth, check⟩, lam⟩ := m
  refine ⟨⟨fun s Γ' r => synthOK_conversion (synth s Γ' r) agrees,
    fun c Γ' r target agreement => check c Γ' r target (sameType_trans agrees agreement)⟩, ?_⟩
  intro body eq
  obtain ⟨reuse, quantity, domain, codomain, bodyUses, same, rest⟩ := lam body eq
  exact ⟨reuse, quantity, domain, codomain, bodyUses, sameType_trans same agrees, rest⟩

theorem synthOK_finish {Γ : Context} {t : Term} {derived : Ty} {uses : Uses}
    (predicted : Ty) (agrees : sameType a predicted derived = true)
    (tree : List Nat → AnnotationTree)
    (prepared : ∀ path, prepare a noHints Γ path t .synth = .ok (tree path, predicted))
    (synthesized : ∀ annotations path, Realizes annotations path (tree path) →
      ∃ s : Synth a Γ t, s.type = predicted ∧ s.uses = uses ∧ (annotations path).isNone ∧
        ∀ mode, elaborate a annotations Γ path t mode = finish a annotations path s mode) :
    SynthOK a Γ t derived uses := by
  intro path
  refine ⟨tree path, predicted, prepared path, agrees, ?_⟩
  intro annotations realizes
  obtain ⟨s, sType, sUses, none_, unfolds⟩ := synthesized annotations path realizes
  constructor
  · change Yields (elaborate a annotations Γ path t .synth) _
    rw [unfolds]
    simp only [finish, ascribe]
    rw [Option.isNone_iff_eq_none.mp none_]
    exact ⟨sType, sUses⟩
  · intro expected agreement
    change Yields (elaborate a annotations Γ path t (.check expected)) _
    have hagrees : sameType a s.type expected = true := by rw [sType]; exact agreement
    simp [unfolds, finish, hagrees, Yields, sUses]

theorem checkOK_of_synthOK {Γ : Context} {t : Term} {derived expected : Ty} {uses : Uses}
    (ok : SynthOK a Γ t derived uses) (agreement : sameType a derived expected = true)
    (sameTree : ∀ path tree predicted, prepare a noHints Γ path t .synth = .ok (tree, predicted) →
      prepare a noHints Γ path t (.check expected) = .ok (tree, expected)) :
    CheckOK a Γ t expected uses := by
  intro path
  obtain ⟨tree, predicted, prepared, same, run⟩ := ok path
  refine ⟨tree, expected, sameTree path tree predicted prepared, ?_⟩
  intro annotations realizes
  exact (run annotations realizes).2 expected (sameType_trans same agreement)

theorem variableUses_length {Γ Γ' : Context} (h : Γ'.length = Γ.length) (index : Nat) :
    variableUses Γ' index = variableUses Γ index := by simp [variableUses, h]

theorem zeroUses_length {Γ Γ' : Context} (h : Γ'.length = Γ.length) : zeroUses Γ' = zeroUses Γ := by
  simp [zeroUses, h]

theorem realizes_root {annotations : Annotations} {path : List Nat}
    {here : Option LambdaAnnotation} {children : List AnnotationTree}
    (realizes : Realizes annotations path (.node here children)) : annotations path = here := by
  simpa only [List.append_nil, AnnotationTree.lookup] using realizes []

theorem realizes_child {annotations : Annotations} {path : List Nat}
    {here : Option LambdaAnnotation} {children : List AnnotationTree}
    (realizes : Realizes annotations path (.node here children)) (index : Nat) (tree : AnnotationTree)
    (at_ : children[index]? = some tree) : Realizes annotations (path ++ [index]) tree := by
  intro suffix
  simpa only [List.append_assoc, List.cons_append, List.nil_append, AnnotationTree.lookup,
    AnnotationTree.child, at_, Option.getD_some] using realizes (index :: suffix)

theorem leaf_none {annotations : Annotations} {path : List Nat} (realizes : Realizes annotations path leaf) :
    (annotations path).isNone = true := by
  simp [realizes_root realizes]

theorem motive_bound {Γ : Context} {index : Nat} {binding : Binding} (found : Γ[index]? = some binding) :
    Motive a Γ (.bound index) binding.type (variableUses Γ index) := by
  have synth : ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' (.bound index) binding.type (variableUses Γ index) := by
    intro Γ' r
    obtain ⟨binding', found', agrees, _⟩ := refines_getElem r found
    refine synthOK_finish binding'.type agrees (fun _ => leaf)
      (fun path => by simp [prepare, found', pure, Except.pure]) ?_
    intro annotations path realizes
    refine ⟨⟨binding'.type, variableUses Γ' index, .bound found'⟩, rfl,
      variableUses_length (refines_length r) index, leaf_none realizes, ?_⟩
    intro mode
    rw [elaborate]
    split
    · rename_i b h; rw [found'] at h; cases h; rfl
    · rename_i h; rw [found'] at h; contradiction
  refine ⟨⟨fun _ => synth, fun _ Γ' r expected agreement => ?_⟩, fun _ h => by cases h⟩
  refine checkOK_of_synthOK (synth Γ' r) agreement ?_
  intro path tree predicted prepared
  obtain ⟨binding', found', _⟩ := refines_getElem r found
  simp [prepare, found', pure, Except.pure] at prepared ⊢
  exact prepared.1

theorem motive_literal {Γ : Context} {t : Term} {type : Ty}
    (derivation : ∀ Γ : Context, PartialTyping a Γ t type (zeroUses Γ))
    (notLam : ∀ body, t ≠ .lam body)
    (prepared : ∀ Γ path mode, prepare a noHints Γ path t mode =
      .ok (leaf, match mode with | .synth => type | .check expected => expected))
    (unfolds : ∀ annotations Γ path mode, elaborate a annotations Γ path t mode =
      finish a annotations path ⟨type, zeroUses Γ, derivation Γ⟩ mode) :
    Motive a Γ t type (zeroUses Γ) := by
  have synth : ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' t type (zeroUses Γ) := by
    intro Γ' r
    refine synthOK_finish type (sameType_refl _ _) (fun _ => leaf) (fun path => prepared Γ' path .synth) ?_
    intro annotations path realizes
    exact ⟨⟨type, zeroUses Γ', derivation Γ'⟩, rfl, zeroUses_length (refines_length r), leaf_none realizes,
      unfolds annotations Γ' path⟩
  refine ⟨⟨fun _ => synth, fun _ Γ' r expected agreement => ?_⟩, fun body h => absurd h (notLam body)⟩
  refine checkOK_of_synthOK (synth Γ' r) agreement ?_
  intro path tree predicted p
  rw [prepared] at p ⊢
  cases p; rfl

theorem motive_natural (Γ : Context) (value : Nat) : Motive a Γ (.nat value) .natural (zeroUses Γ) :=
  motive_literal (fun Γ => .natural Γ value) (fun _ h => by cases h)
    (fun _ _ mode => by cases mode <;> rfl) (fun _ _ _ _ => rfl)

theorem motive_boolean (Γ : Context) (value : Bool) : Motive a Γ (.boolean value) .boolean (zeroUses Γ) :=
  motive_literal (fun Γ => .boolean Γ value) (fun _ h => by cases h)
    (fun _ _ mode => by cases mode <;> rfl) (fun _ _ _ _ => rfl)

theorem motive_label (Γ : Context) (value : String) : Motive a Γ (.label value) (literalType value) (zeroUses Γ) :=
  motive_literal (fun Γ => .label Γ value) (fun _ h => by cases h)
    (fun _ _ mode => by cases mode <;> rfl) (fun _ _ _ _ => rfl)


theorem motive_lambda_modes (sc : ShareableComplete a = true) {Γ : Context} {body : Term}
    {annotation : LambdaAnnotation} {uses : Uses}
    (safe : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) uses = true)
    (valid : validContext a.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: Γ) = true)
    (captures : reusableAllowed a annotation.reuse Γ uses.tail = true)
    (fits : annotation.parameter.fits (uses.headD 0) = true)
    (ihModes : Modes a (⟨annotation.domain, annotation.parameter⟩ :: Γ) body annotation.codomain uses) :
    Motive a Γ (.lam body) (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain)
      uses.tail := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body' h => ?_⟩
  · have bodyCheckable : Checkable body := by
      cases c with
      | synth s => cases s
      | lam b => exact b
    obtain ⟨d', c', hwhnf, hd, hc⟩ := whnf_arrow_inv (sameType_symm agreement)
    have binder : Refines a (⟨d', annotation.parameter⟩ :: Γ')
        (⟨annotation.domain, annotation.parameter⟩ :: Γ) :=
      refines_same_quantity hd r
    have bodyOK := ihModes.2 bodyCheckable _ binder c' (sameType_symm hc)
    intro path
    obtain ⟨bodyTree, _, bodyPrepared, bodyRun⟩ := bodyOK (path ++ [0])
    refine ⟨.node none [bodyTree], expected, ?_, ?_⟩
    · simp [prepare, noHints, hwhnf, bodyPrepared, bind, Except.bind, pure, Except.pure]
    · intro annotations realizes
      have root := realizes_root realizes
      have child := realizes_child realizes 0 bodyTree rfl
      obtain ⟨checked, accepted, sameUses⟩ := yields_elim (bodyRun annotations child)
      have safe' : safeUses (⟨d', annotation.parameter⟩ :: Γ') checked.uses = true := by
        rw [sameUses]; exact safeUses_refines binder safe
      have valid' : validContext a.shareableVariables (⟨d', annotation.parameter⟩ :: Γ') = true :=
        validContext_refines sc binder valid
      have captures' : reusableAllowed a annotation.reuse Γ' checked.uses.tail = true := by
        rw [sameUses]
        exact reusableAllowed_refines sc (match binder with | .cons _ tail => tail) captures
      have fits' : annotation.parameter.fits (checked.uses.headD 0) = true := by rw [sameUses]; exact fits
      change Yields (elaborate a annotations Γ' path (.lam body) (.check expected)) _
      rw [elaborate]
      simp only [root]
      split
      · rename_i reuse' parameter' domain' codomain' shape
        simp only [representativeHead, root, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          hwhnf, Ty.arrow.injEq] at shape
        obtain ⟨rfl, rfl, rfl, rfl⟩ := shape
        simp [checkAt] at accepted
        simp [accepted, need_ok safe', need_ok valid', need_ok captures', need_ok fits', bind, Except.bind, pure,
          Except.pure, Yields]
        exact congrArg List.tail sameUses
      · rename_i hne
        exfalso
        exact hne annotation.reuse annotation.parameter d' c'
          (by simp [representativeHead, root, hwhnf])
  · cases h
    exact ⟨annotation.reuse, annotation.parameter, annotation.domain, annotation.codomain, uses,
      sameType_refl _ _, rfl, safe, valid, fits, ihModes⟩

theorem motive_lambda (sc : ShareableComplete a = true) {Γ : Context} {body : Term}
    {annotation : LambdaAnnotation} {uses : Uses}
    (safe : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) uses = true)
    (valid : validContext a.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: Γ) = true)
    (captures : reusableAllowed a annotation.reuse Γ uses.tail = true)
    (fits : annotation.parameter.fits (uses.headD 0) = true)
    (ih : Motive a (⟨annotation.domain, annotation.parameter⟩ :: Γ) body annotation.codomain uses) :
    Motive a Γ (.lam body) (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain)
      uses.tail :=
  motive_lambda_modes sc safe valid captures fits ih.1
theorem safeUses_head {b : Binding} {Γ : Context} {uses : Uses} (safe : safeUses (b :: Γ) uses = true) :
    safeQuantity b.quantity (uses.headD 0) = true := by
  cases uses with
  | nil => simp [safeUses] at safe
  | cons head tail =>
    simp only [safeUses, Bool.and_eq_true, List.zip_cons_cons, List.all_cons] at safe
    exact safe.2.1

/-! ### Applications & Let-Redexes -/

theorem app_run {annotations : Annotations} {Γ : Context} {path : List Nat} {function argument : Term}
    {functionType domain codomain : Ty} {reuse : Reuse} {quantity : Quantity} {fu au : Uses}
    (root : annotations path = some (hint functionType codomain))
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (functionChecks : Yields (checkAt a annotations Γ (path ++ [0]) function functionType) (fun r => r.uses = fu))
    (argumentChecks : Yields (checkAt a annotations Γ (path ++ [1]) argument domain) (fun r => r.uses = au))
    (allowed : argumentAllowed a quantity Γ domain au = true) :
    Yields (synthAt a annotations Γ path (.app function argument))
      (fun r => r.type = codomain ∧ r.uses = addUses fu au) ∧
    ∀ expected, sameType a codomain expected = true →
      Yields (checkAt a annotations Γ path (.app function argument) expected) (fun r => r.uses = addUses fu au) := by
  obtain ⟨fn, fnOk, fnUses⟩ := yields_elim functionChecks
  obtain ⟨arg, argOk, argUses⟩ := yields_elim argumentChecks
  have allowed' : argumentAllowed a quantity Γ domain arg.uses = true := by rw [argUses]; exact allowed
  have rawHead : representativeHead a annotations path functionType = functionType := by
    simp [representativeHead, root]
  simp only [checkAt] at fnOk argOk
  constructor
  · change Yields (elaborate a annotations Γ path (.app function argument) .synth) _
    rw [elaborate]
    simp only [root, hint, fnOk, Except.map, bind, Except.bind, checkedSynth]
    split
    · rename_i r q d c observed
      rw [rawHead, shape] at observed
      cases observed
      simp [argOk, need_ok allowed', finish, ascribe, root, hint, sameType_refl, Yields,
        fnUses, argUses]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [rawHead]; exact shape)).elim
  · intro expected agreement
    change Yields (elaborate a annotations Γ path (.app function argument) (.check expected)) _
    rw [elaborate]
    simp only [root, hint, fnOk, Except.map, bind, Except.bind, checkedSynth]
    split
    · rename_i r q d c observed
      rw [rawHead, shape] at observed
      cases observed
      simp [argOk, need_ok allowed', finish, agreement, Yields, fnUses, argUses]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [rawHead]; exact shape)).elim

theorem app_run_unannotated {annotations : Annotations} {Γ : Context} {path : List Nat}
    {function argument : Term} {functionType domain codomain : Ty}
    {reuse : Reuse} {quantity : Quantity} {fu au : Uses}
    (root : annotations path = none)
    (shape : callable (whnf a functionType) = .arrow reuse quantity domain codomain)
    (functionSynths : Yields (synthAt a annotations Γ (path ++ [0]) function)
      (fun r => r.type = functionType ∧ r.uses = fu))
    (argumentChecks : Yields (checkAt a annotations Γ (path ++ [1]) argument domain) (fun r => r.uses = au))
    (allowed : argumentAllowed a quantity Γ domain au = true) :
    Yields (synthAt a annotations Γ path (.app function argument))
      (fun r => r.type = codomain ∧ r.uses = addUses fu au) ∧
    ∀ expected, sameType a codomain expected = true →
      Yields (checkAt a annotations Γ path (.app function argument) expected) (fun r => r.uses = addUses fu au) := by
  obtain ⟨fn, fnOk, fnType, fnUses⟩ := yields_elim functionSynths
  obtain ⟨arg, argOk, argUses⟩ := yields_elim argumentChecks
  have allowed' : argumentAllowed a quantity Γ domain arg.uses = true := by rw [argUses]; exact allowed
  have whnfHead : representativeHead a annotations path fn.type = whnf a functionType := by
    simp [representativeHead, root, fnType]
  simp only [synthAt, checkAt] at fnOk argOk
  constructor
  · change Yields (elaborate a annotations Γ path (.app function argument) .synth) _
    rw [elaborate]
    simp only [root, fnOk, bind, Except.bind]
    split
    · rename_i r q d c observed
      rw [whnfHead, shape] at observed
      cases observed
      simp [argOk, need_ok allowed', finish, ascribe, root, Yields, fnUses, argUses]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [whnfHead]; exact shape)).elim
  · intro expected agreement
    change Yields (elaborate a annotations Γ path (.app function argument) (.check expected)) _
    rw [elaborate]
    simp only [root, fnOk, bind, Except.bind]
    split
    · rename_i r q d c observed
      rw [whnfHead, shape] at observed
      cases observed
      simp [argOk, need_ok allowed', finish, agreement, Yields, fnUses, argUses]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [whnfHead]; exact shape)).elim

theorem lam_run {annotations : Annotations} {Γ : Context} {path : List Nat} {body : Term}
    {annotation : LambdaAnnotation} {bodyUses : Uses}
    (root : annotations path = some annotation)
    (bodyChecks : Yields (checkAt a annotations (⟨annotation.domain, annotation.parameter⟩ :: Γ) (path ++ [0])
      body annotation.codomain) (fun r => r.uses = bodyUses))
    (safe : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) bodyUses = true)
    (valid : validContext a.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: Γ) = true)
    (captures : reusableAllowed a annotation.reuse Γ bodyUses.tail = true)
    (fits : annotation.parameter.fits (bodyUses.headD 0) = true) :
    Yields (checkAt a annotations Γ path (.lam body)
      (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain))
      (fun r => r.uses = bodyUses.tail) := by
  obtain ⟨checked, ok, sameUses⟩ := yields_elim bodyChecks
  have safe' : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) checked.uses = true := by
    rw [sameUses]; exact safe
  have captures' : reusableAllowed a annotation.reuse Γ checked.uses.tail = true := by
    rw [sameUses]; exact captures
  have fits' : annotation.parameter.fits (checked.uses.headD 0) = true := by
    rw [sameUses]; exact fits
  simp only [checkAt] at ok
  change Yields (elaborate a annotations Γ path (.lam body) (.check _)) _
  rw [elaborate]
  simp [root, ok, need_ok safe', need_ok valid, need_ok captures', need_ok fits', bind, Except.bind, pure,
    Except.pure, finish, checkedSynth, sameType_refl, Yields, sameUses]

theorem applyPrepared_arrow {hints : Annotations} {Γ : Context} {path : List Nat} {argument : Term}
    {mode : Mode} {functionTree : AnnotationTree} {functionType domain codomain : Ty}
    {reuse : Reuse} {quantity : Quantity}
    {prepareArgument : Ty → Except PrepareRefusal AnnotationTree} {argumentTree : AnnotationTree}
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (argumentPrepared : prepareArgument domain = .ok argumentTree) :
    applyPrepared a hints Γ path argument mode functionTree functionType prepareArgument =
      .ok (.node (some (hint functionType codomain)) [functionTree, argumentTree],
        match mode with | .synth => codomain | .check expected => expected) := by
  cases mode <;> simp [applyPrepared, shape, argumentPrepared, bind, Except.bind, pure, Except.pure]

theorem prepare_app_general {hints : Annotations} {Γ : Context} {path : List Nat}
    {function argument : Term} {mode : Mode} (notLam : ∀ body, function ≠ .lam body) :
    prepare a hints Γ path (.app function argument) mode = (do
      let (functionTree, functionType) ← prepare a hints Γ (path ++ [0]) function .synth
      applyPrepared a hints Γ path argument mode functionTree functionType
        (fun domain => do
          let (tree, _) ← prepare a hints Γ (path ++ [1]) argument (.check domain)
          pure tree)) := by
  cases function with
  | lam body => exact absurd rfl (notLam body)
  | _ => simp only [prepare]

theorem synthable_not_lam {t : Term} (s : Synthable t) (body : Term) : t ≠ .lam body := by
  cases s <;> simp

theorem applyPrepared_complete (sc : ShareableComplete a = true) {Γ Γ' : Context}
    (r : Refines a Γ' Γ) {path : List Nat} {function argument : Term}
    {functionType domain codomain fT : Ty} {functionTree : AnnotationTree}
    {reuse : Reuse} {quantity : Quantity} {fu au : Uses}
    (fSame : sameType a fT functionType = true)
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (allowed : argumentAllowed a quantity Γ domain au = true)
    (fRun : ∀ annotations, Realizes annotations (path ++ [0]) functionTree →
      Yields (synthAt a annotations Γ' (path ++ [0]) function) (fun res => res.type = fT ∧ res.uses = fu) ∧
      ∀ expected, sameType a fT expected = true →
        Yields (checkAt a annotations Γ' (path ++ [0]) function expected) (fun res => res.uses = fu))
    (argCheck : ∀ d', sameType a domain d' = true → CheckOK a Γ' argument d' au) :
    ∃ here argumentTree c',
      (∀ mode,
        applyPrepared a noHints Γ' path argument mode functionTree fT
          (fun d => do
            let (tree, _) ← prepare a noHints Γ' (path ++ [1]) argument (.check d)
            pure tree) =
        .ok (.node here [functionTree, argumentTree],
          match mode with | .synth => c' | .check expected => expected)) ∧
      sameType a c' codomain = true ∧
      ∀ annotations, Realizes annotations path (.node here [functionTree, argumentTree]) →
        Yields (synthAt a annotations Γ' path (.app function argument))
          (fun res => res.type = c' ∧ res.uses = addUses fu au) ∧
        ∀ expected, sameType a c' expected = true →
          Yields (checkAt a annotations Γ' path (.app function argument) expected)
            (fun res => res.uses = addUses fu au) := by
  cases hCall1 : callable fT with
  | arrow r₁ q₁ d₁ c₁ =>
    obtain ⟨_, rfl, rfl, hd₁, hc₁⟩ := callable_arrow_agrees hCall1 shape fSame
    obtain ⟨xt, _, xPrepared, xRun⟩ := argCheck d₁ (sameType_symm hd₁) (path ++ [1])
    refine ⟨some (hint fT c₁), xt, c₁, ?_, hc₁, ?_⟩
    · intro mode
      exact applyPrepared_arrow hCall1 (by simp [xPrepared, bind, Except.bind, pure, Except.pure])
    · intro annotations realizes
      have fChild := realizes_child realizes 0 functionTree rfl
      have xChild := realizes_child realizes 1 xt rfl
      exact app_run (realizes_root realizes) hCall1 ((fRun annotations fChild).2 fT (sameType_refl _ _))
        (xRun annotations xChild) (argumentAllowed_refines sc r hd₁ allowed)
  | _ =>
    cases hCall2 : callable (whnf a fT) with
    | arrow r₂ q₂ d₂ c₂ =>
      have hWhnfSame : sameType a (whnf a fT) functionType = true :=
        sameType_trans (whnf_sameType a fT) fSame
      obtain ⟨_, rfl, rfl, hd₂, hc₂⟩ := callable_arrow_agrees hCall2 shape hWhnfSame
      obtain ⟨xt, _, xPrepared, xRun⟩ := argCheck d₂ (sameType_symm hd₂) (path ++ [1])
      refine ⟨none, xt, c₂, ?_, hc₂, ?_⟩
      · intro mode
        cases mode <;>
          simp [applyPrepared, hCall1, hCall2, xPrepared, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have fChild := realizes_child realizes 0 functionTree rfl
        have xChild := realizes_child realizes 1 xt rfl
        exact app_run_unannotated (realizes_root realizes) hCall2 (fRun annotations fChild).1
          (xRun annotations xChild) (argumentAllowed_refines sc r hd₂ allowed)
    | _ =>
      let deeper := exposeCallable a (tyNodes fT + (a.bounds.map (tyNodes ·.2)).sum + 1) fT
      obtain ⟨d₃, c₃, hCall3, hd₃, hc₃⟩ := exposeCallable_transport fSame shape
      change callable deeper = .arrow reuse quantity d₃ c₃ at hCall3
      obtain ⟨xt, _, xPrepared, xRun⟩ := argCheck d₃ (sameType_symm hd₃) (path ++ [1])
      refine ⟨some (hint deeper c₃), xt, c₃, ?_, hc₃, ?_⟩
      · intro mode
        cases mode <;>
          simp [applyPrepared, hCall1, hCall2, deeper, hCall3, xPrepared, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have fChild := realizes_child realizes 0 functionTree rfl
        have xChild := realizes_child realizes 1 xt rfl
        have hDeeperSame : sameType a fT deeper = true := exposeCallable_sameType a _ fT
        exact app_run (realizes_root realizes) hCall3 ((fRun annotations fChild).2 deeper hDeeperSame)
          (xRun annotations xChild) (argumentAllowed_refines sc r hd₃ allowed)

theorem motive_application (sc : ShareableComplete a = true) {Γ : Context} {function argument : Term}
    {functionType domain codomain : Ty} {fu au : Uses} {reuse : Reuse} {quantity : Quantity}
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (allowed : argumentAllowed a quantity Γ domain au = true)
    (ihF : Motive a Γ function functionType fu) (ihA : Motive a Γ argument domain au)
    (argumentUses : au = occurrences Γ.length argument) :
    Motive a Γ (.app function argument) codomain (addUses fu au) := by
  have general : Synthable function → Checkable argument → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.app function argument) codomain (addUses fu au) ∧
      ∀ path tree predicted expected,
        prepare a noHints Γ' path (.app function argument) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.app function argument) (.check expected) = .ok (tree, expected) := by
    intro sf ca Γ' r
    have notLam := synthable_not_lam sf
    have fOK := ihF.1.1 sf Γ' r
    refine ⟨?_, ?_⟩
    · intro path
      obtain ⟨ft, fT, fPrepared, fSame, fRun⟩ := fOK (path ++ [0])
      obtain ⟨here, xt, c', hApply, hc, hRun⟩ :=
        applyPrepared_complete sc r fSame shape allowed fRun (ihA.1.2 ca Γ' r)
      refine ⟨.node here [ft, xt], c', ?_, hc, hRun⟩
      rw [prepare_app_general notLam]
      simp only [fPrepared, bind, Except.bind]
      exact hApply .synth
    · intro path tree predicted expected prepared
      obtain ⟨ft, fT, fPrepared, fSame, fRun⟩ := fOK (path ++ [0])
      obtain ⟨here, xt, c', hApply, _, _⟩ :=
        applyPrepared_complete sc r fSame shape allowed fRun (ihA.1.2 ca Γ' r)
      have hp1 : prepare a noHints Γ' path (.app function argument) .synth =
          .ok (.node here [ft, xt], c') := by
        rw [prepare_app_general notLam]
        simp only [fPrepared, bind, Except.bind]
        exact hApply .synth
      have hp2 : prepare a noHints Γ' path (.app function argument) (.check expected) =
          .ok (.node here [ft, xt], expected) := by
        rw [prepare_app_general notLam]
        simp only [fPrepared, bind, Except.bind]
        exact hApply (.check expected)
      rw [hp1] at prepared
      cases prepared
      exact hp2
  have letIn : ∀ body, function = .lam body → Synthable argument → ∀ Γ', Refines a Γ' Γ →
      (Synthable body → SynthOK a Γ' (.app (.lam body) argument) codomain (addUses fu au)) ∧
      (Checkable body → ∀ expected, sameType a codomain expected = true →
        CheckOK a Γ' (.app (.lam body) argument) expected (addUses fu au)) := by
    intro body isLam sx Γ' r
    obtain ⟨reuse0, q0, d0, c0, bodyUses, same, fuEq, safe, valid, fits0, bodyModes⟩ := ihF.2 body isLam
    obtain ⟨_, rfl, rfl, hd1, hc1⟩ := callable_arrow_agrees (rfl : callable (.arrow ..) = .arrow ..) shape same
    have xOK := ihA.1.1 sx Γ' r
    have lengths := refines_length r
    have linear_of_used : ¬ (linearFree Γ' (occurrences Γ'.length argument) = true) → q0 = .linear := by
      intro used
      rw [lengths, ← argumentUses] at used
      have notFree : ¬ (linearFree Γ au = true) := fun free => used (linearFree_refines r free)
      simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at allowed
      exact allowed.1.2.resolve_right notFree
    have linear_of_not_affine : ∀ argumentType, sameType a argumentType domain = true →
        ¬ ((!argumentType.bearsCustody && linearFree Γ' (occurrences Γ'.length argument)) = true) →
        q0 = .linear := by
      intro argumentType agrees notAff
      cases hcust : argumentType.bearsCustody with
      | true =>
        have hd0Cust : d0.bearsCustody = true := by
          rw [← bearsCustody_congr sc (sameType_trans agrees (sameType_symm hd1))]
          exact hcust
        exact validContext_custody_linear valid List.mem_cons_self hd0Cust
      | false =>
        have used : ¬ (linearFree Γ' (occurrences Γ'.length argument) = true) :=
          fun hf => notAff (by simp [hcust, hf])
        exact linear_of_used used
    have binderOf : ∀ argumentType, sameType a argumentType domain = true →
        BindingRefines a ⟨argumentType, letQuantity a Γ' argumentType argument⟩ ⟨d0, q0⟩ := by
      intro argumentType agrees
      refine ⟨sameType_trans agrees (sameType_symm hd1), ?_⟩
      unfold letQuantity
      split
      · rename_i condition
        exact .inr (.inr ⟨rfl, (Bool.and_eq_true_iff.mp condition).1⟩)
      · rename_i condition
        split
        · rename_i affCond
          have hNoCust : argumentType.bearsCustody = false := by
            simpa using (Bool.and_eq_true_iff.mp affCond).1
          refine .inr (.inl ⟨rfl, hNoCust, fun unrestricted => condition ?_⟩)
          simp only at unrestricted
          subst unrestricted
          simp only [argumentAllowed, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at allowed
          rw [Bool.and_eq_true_iff, shareable_congr sc agrees, lengths, ← argumentUses]
          exact ⟨allowed.2.1, reusableCaptures_refines sc r allowed.2.2⟩
        · rename_i notAff
          exact .inl (linear_of_not_affine argumentType agrees notAff).symm
    have qOf : ∀ argumentType, sameType a argumentType domain = true →
        letQuantity a Γ' argumentType argument = .linear → q0 = .linear := by
      intro argumentType agrees isLinear
      unfold letQuantity at isLinear
      split at isLinear
      · cases isLinear
      · split at isLinear
        · cases isLinear
        · rename_i notAff; exact linear_of_not_affine argumentType agrees notAff
    have fitsOf : ∀ argumentType, sameType a argumentType domain = true →
        (letQuantity a Γ' argumentType argument).fits (bodyUses.headD 0) = true := by
      intro argumentType agrees
      have refines := (binderOf argumentType agrees).2
      cases hq : letQuantity a Γ' argumentType argument with
      | linear => rw [qOf argumentType agrees hq] at fits0; exact fits0
      | unrestricted => rfl
      | erased =>
        unfold letQuantity at hq
        split at hq
        · cases hq
        · split at hq <;> cases hq
      | affine =>
        rw [hq] at refines
        have head := safeUses_head safe
        rcases refines with same' | ⟨_, _, notU⟩ | ⟨h, _⟩
        · rw [← same'] at head; simpa [Quantity.fits, safeQuantity] using head
        · cases q0 <;> simp_all [Quantity.fits, safeQuantity]
        · cases h
    have allowedOf : ∀ argumentType, sameType a argumentType domain = true →
        argumentAllowed a (letQuantity a Γ' argumentType argument) Γ' argumentType au = true := by
      intro argumentType agrees
      have notActivity : (!argumentType.isComputation) = true := by
        simp only [argumentAllowed, Bool.and_eq_true] at allowed
        rw [sameType_isComputation agrees]; exact allowed.1.1
      unfold letQuantity
      split
      · rename_i condition
        rw [lengths, ← argumentUses] at condition
        have free := linearFree_of_reusableCaptures (Bool.and_eq_true_iff.mp condition).2
        simp only [argumentAllowed, notActivity, Bool.true_and, bne_self_eq_false, Bool.false_or, free,
          Bool.or_true]
        exact condition
      · split
        · rename_i affCond
          have free : linearFree Γ' au = true := by
            have hf := (Bool.and_eq_true_iff.mp affCond).2
            rwa [lengths, ← argumentUses] at hf
          simp [argumentAllowed, notActivity, free]
        · simp [argumentAllowed, notActivity]
    have once : ∀ Γ'' uses, reusableAllowed a .once Γ'' uses = true := by intros; rfl
    refine ⟨fun sb => ?_, fun cb expected agreement => ?_⟩
    · intro path
      obtain ⟨xt, xT, xPrepared, xSame, xRun⟩ := xOK (path ++ [1])
      have binder := binderOf xT xSame
      have binderRefines : Refines a (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (⟨d0, q0⟩ :: Γ) :=
        .cons binder r
      obtain ⟨bt, bT, bPrepared, bSame, bRun⟩ := bodyModes.1 sb _ binderRefines (path ++ [0] ++ [0])
      let annotation : LambdaAnnotation := ⟨xT, bT, letQuantity a Γ' xT argument, .once⟩
      refine ⟨.node (some (hint (.arrow .once (letQuantity a Γ' xT argument) xT bT) bT))
          [.node (some annotation) [bt], xt], bT, ?_, sameType_trans bSame hc1, ?_⟩
      · have bPrepared' : prepare a noHints (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (path ++ [0, 0]) body .synth
            = .ok (bt, bT) := by simpa using bPrepared
        simp only [prepare, noHints, xPrepared, bPrepared', bind, Except.bind]
        exact applyPrepared_arrow (by rfl) rfl
      · intro annotations realizes
        have fChild := realizes_child realizes 0 _ rfl
        have xChild := realizes_child realizes 1 xt rfl
        have bChild := realizes_child fChild 0 bt rfl
        have bodyChecks := (bRun annotations bChild).2 bT (sameType_refl _ _)
        have fnChecks := lam_run (annotation := annotation) (realizes_root fChild) bodyChecks
          (safeUses_refines binderRefines safe) (validContext_refines sc binderRefines valid) (once _ _)
          (fitsOf xT xSame)
        have run := app_run (realizes_root realizes) rfl fnChecks
          ((xRun annotations xChild).2 xT (sameType_refl _ _)) (allowedOf xT xSame)
        rw [fuEq]
        exact run
    · intro path
      obtain ⟨xt, xT, xPrepared, xSame, xRun⟩ := xOK (path ++ [1])
      have binder := binderOf xT xSame
      have binderRefines : Refines a (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (⟨d0, q0⟩ :: Γ) :=
        .cons binder r
      obtain ⟨bt, _, bPrepared, bRun⟩ := bodyModes.2 cb _ binderRefines expected
        (sameType_trans hc1 agreement) (path ++ [0] ++ [0])
      let annotation : LambdaAnnotation := ⟨xT, expected, letQuantity a Γ' xT argument, .once⟩
      refine ⟨.node (some (hint (.arrow .once (letQuantity a Γ' xT argument) xT expected) expected))
          [.node (some annotation) [bt], xt], expected, ?_, ?_⟩
      · have bPrepared' : ∃ t, prepare a noHints (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (path ++ [0, 0]) body
            (.check expected) = .ok (bt, t) := ⟨_, by simpa using bPrepared⟩
        obtain ⟨t, bPrepared'⟩ := bPrepared'
        simp only [prepare, noHints, xPrepared, bPrepared', bind, Except.bind, pure, Except.pure]
        exact applyPrepared_arrow (by rfl) rfl
      · intro annotations realizes
        have fChild := realizes_child realizes 0 _ rfl
        have xChild := realizes_child realizes 1 xt rfl
        have bChild := realizes_child fChild 0 bt rfl
        have bodyChecks := bRun annotations bChild
        have fnChecks := lam_run (annotation := annotation) (realizes_root fChild) bodyChecks
          (safeUses_refines binderRefines safe) (validContext_refines sc binderRefines valid) (once _ _)
          (fitsOf xT xSame)
        have run := app_run (realizes_root realizes) rfl fnChecks
          ((xRun annotations xChild).2 xT (sameType_refl _ _)) (allowedOf xT xSame)
        rw [fuEq]
        exact run.2 expected (sameType_refl _ _)
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with
    | app sf ca => exact (general sf ca Γ' r).1
    | letIn sb sx => exact (letIn _ rfl sx Γ' r).1 sb
  · cases c with
    | synth s =>
      cases s with
      | app sf ca =>
        obtain ⟨ok, sameTree⟩ := general sf ca Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)
      | letIn sb sx => exact (letIn _ rfl sx Γ' r).2 (.synth sb) expected agreement
    | letIn cb sx => exact (letIn _ rfl sx Γ' r).2 cb expected agreement

/-! ### Projection, Primitives, `.mix` & `.fix` -/

theorem motive_get {Γ : Context} {target : Term} {targetType member : Ty}
    {uses : Uses} {name : String} {fuel : Nat}
    (found : targetType.lookup a.bounds fuel name = some member) (free : linearFree Γ uses = true)
    (ih : Motive a Γ target targetType uses) :
    Motive a Γ (.get target name) member uses := by
  have lookup : lookupV a.bounds [] targetType name = some member := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  have synth : Synthable target → ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' (.get target name) member uses ∧
      ∀ path tree predicted expected, prepare a noHints Γ' path (.get target name) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.get target name) (.check expected) = .ok (tree, expected) := by
    intro st Γ' r
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨tt, tT, tPrepared, tSame, tRun⟩ := ih.1.1 st Γ' r (path ++ [0])
      obtain ⟨member', found', same'⟩ := lookupV_transport tSame lookup
      refine ⟨.node none [tt], member', ?_, same', ?_⟩
      · simp [prepare, tPrepared, found', bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        obtain ⟨value, ok, vType, vUses⟩ := yields_elim (tRun annotations (realizes_child realizes 0 tt rfl)).1
        simp only [synthAt] at ok
        have free' : linearFree Γ' value.uses = true := by rw [vUses]; exact linearFree_refines r free
        constructor
        · change Yields (elaborate a annotations Γ' path (.get target name) .synth) _
          rw [elaborate]
          simp only [root, ok, bind, Except.bind]
          split
          · rename_i m h
            rw [vType, found'] at h; cases h
            simp [finish, ascribe, root, Yields, vUses, need_ok free']
          · rename_i h; rw [vType, found'] at h; contradiction
        · intro expected agreement
          change Yields (elaborate a annotations Γ' path (.get target name) (.check expected)) _
          rw [elaborate]
          simp only [root, ok, bind, Except.bind]
          split
          · rename_i m h
            rw [vType, found'] at h; cases h
            simp [finish, agreement, Yields, vUses, need_ok free']
          · rename_i h; rw [vType, found'] at h; contradiction
    · obtain ⟨tt, tT, tPrepared, tSame, _⟩ := ih.1.1 st Γ' r (path ++ [0])
      obtain ⟨member', found', _⟩ := lookupV_transport tSame lookup
      simp [prepare, tPrepared, found', bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | get _ st => exact (synth st Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | get _ st =>
        obtain ⟨ok, sameTree⟩ := synth st Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)

theorem motive_binary {Γ : Context} {primitive : Primitive} {left right : Term}
    {input output : Ty} {lu ru : Uses}
    (types : primitiveTypes primitive = (input, output))
    (ihL : Motive a Γ left input lu) (ihR : Motive a Γ right input ru) :
    Motive a Γ (.binary primitive left right) output (addUses lu ru) := by
  have hin : input = (primitiveTypes primitive).1 := by rw [types]
  have hout : output = (primitiveTypes primitive).2 := by rw [types]
  subst hin; subst hout
  have synth : Checkable left → Checkable right → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.binary primitive left right) (primitiveTypes primitive).2 (addUses lu ru) ∧
      ∀ path tree predicted expected, prepare a noHints Γ' path (.binary primitive left right) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.binary primitive left right) (.check expected) = .ok (tree, expected) := by
    intro cl cr Γ' r
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨lt, _, lPrepared, lRun⟩ := ihL.1.2 cl Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [0])
      obtain ⟨rt, _, rPrepared, rRun⟩ := ihR.1.2 cr Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [1])
      refine ⟨.node none [lt, rt], (primitiveTypes primitive).2, ?_, sameType_refl _ _, ?_⟩
      · simp [prepare, lPrepared, rPrepared, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        obtain ⟨lv, lOk, lUses⟩ := yields_elim (lRun annotations (realizes_child realizes 0 lt rfl))
        obtain ⟨rv, rOk, rUses⟩ := yields_elim (rRun annotations (realizes_child realizes 1 rt rfl))
        simp only [checkAt] at lOk rOk
        constructor
        · change Yields (elaborate a annotations Γ' path (.binary primitive left right) .synth) _
          rw [elaborate]
          simp [lOk, rOk, bind, Except.bind, finish, ascribe, root, Yields, lUses, rUses]
        · intro expected agreement
          change Yields (elaborate a annotations Γ' path (.binary primitive left right) (.check expected)) _
          rw [elaborate]
          simp [lOk, rOk, bind, Except.bind, finish, agreement, Yields, lUses, rUses]
    · obtain ⟨lt, _, lPrepared, _⟩ := ihL.1.2 cl Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [0])
      obtain ⟨rt, _, rPrepared, _⟩ := ihR.1.2 cr Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [1])
      simp [prepare, lPrepared, rPrepared, bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | binary _ cl cr => exact (synth cl cr Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | binary _ cl cr =>
        obtain ⟨ok, sameTree⟩ := synth cl cr Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)

theorem motive_mix (sc : ShareableComplete a = true) {Γ : Context} {lower upper : Term}
    {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses}
    (lowerShape : callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle))
    (upperShape : callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided))
    (captures : reusableCaptures a.shareableVariables Γ (addUses lu uu) = true)
    (shareSelf : self.shareableUnder a.shareableVariables = true)
    (shareInherited : inherited.shareableUnder a.shareableVariables = true)
    (shareMiddle : middle.shareableUnder a.shareableVariables = true)
    (ihL : Motive a Γ lower lowerType lu) (ihU : Motive a Γ upper upperType uu) :
    Motive a Γ (.mix lower upper)
      (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided))
      (addUses lu uu) := by
  have synth : Synthable lower → Synthable upper → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.mix lower upper)
        (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided))
        (addUses lu uu) ∧
      ∀ path tree predicted expected,
        prepare a noHints Γ' path (.mix lower upper) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.mix lower upper) (.check expected) = .ok (tree, expected) := by
    intro sl su Γ' r
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨lt, lT, lPrepared, lSame, lRun⟩ := ihL.1.1 sl Γ' r (path ++ [0])
      obtain ⟨ut, uT, uPrepared, uSame, uRun⟩ := ihU.1.1 su Γ' r (path ++ [1])
      let lDeeper := exposeCallable a (tyNodes lT + (a.bounds.map (tyNodes ·.2)).sum + 1) lT
      let uDeeper := exposeCallable a (tyNodes uT + (a.bounds.map (tyNodes ·.2)).sum + 1) uT
      obtain ⟨self₁, lInner, hLCall, hSelf₁, hLInner⟩ := exposeCallable_transport lSame lowerShape
      obtain ⟨self₂, uInner, hUCall, hSelf₂, hUInner⟩ := exposeCallable_transport uSame upperShape
      change callable lDeeper = .arrow .reusable .unrestricted self₁ lInner at hLCall
      change callable uDeeper = .arrow .reusable .unrestricted self₂ uInner at hUCall
      obtain ⟨inh₁, mid₁, hLWhnf, hInh₁, hMid₁⟩ := whnf_arrow_inv hLInner
      obtain ⟨mid₂, prov₂, hUWhnf, hMid₂, hProv₂⟩ := whnf_arrow_inv hUInner
      let lowerRep := retargetCallable lDeeper
        (.arrow .reusable .unrestricted self₁ (.arrow .reusable .unrestricted inh₁ mid₁))
      let upperRep := retargetCallable uDeeper
        (.arrow .reusable .unrestricted self₁ (.arrow .reusable .unrestricted mid₁ prov₂))
      let mixType := Ty.arrow .reusable .unrestricted self₁ (.arrow .reusable .unrestricted inh₁ prov₂)
      let predicted := if sameType a mixType upperRep then upperRep else mixType
      have hMixDeriv : sameType a mixType
          (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) = true :=
        sameType_arrow hSelf₁ (sameType_arrow hInh₁ hProv₂)
      have hPredDeriv : sameType a predicted
          (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) = true := by
        dsimp only [predicted]
        by_cases h : sameType a mixType upperRep = true
        · simp [h, sameType_trans (sameType_symm h) hMixDeriv]
        · simp [h, hMixDeriv]
      refine ⟨.node (some (hint lowerRep upperRep)) [lt, ut], predicted, ?_, hPredDeriv, ?_⟩
      · simp [prepare, lPrepared, uPrepared, lDeeper, uDeeper, hLCall, hUCall, hLWhnf, hUWhnf,
          lowerRep, upperRep, mixType, predicted, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have lChild := realizes_child realizes 0 lt rfl
        have uChild := realizes_child realizes 1 ut rfl
        have hLD : sameType a lT lDeeper = true :=
          exposeCallable_sameType a (tyNodes lT + (a.bounds.map (tyNodes ·.2)).sum + 1) lT
        have hUD : sameType a uT uDeeper = true :=
          exposeCallable_sameType a (tyNodes uT + (a.bounds.map (tyNodes ·.2)).sum + 1) uT
        have hLowerRepSame : sameType a lT lowerRep = true := by
          refine sameType_trans hLD ?_
          refine sameType_retargetCallable hLCall (sameType_refl a self₁) ?_
          exact sameType_trans (sameType_whnf a lInner)
            (by rw [hLWhnf]; exact sameType_arrow (sameType_refl a inh₁) (sameType_refl a mid₁))
        have hUpperRepSame : sameType a uT upperRep = true := by
          refine sameType_trans hUD ?_
          refine sameType_retargetCallable hUCall (sameType_trans hSelf₂ (sameType_symm hSelf₁)) ?_
          refine sameType_trans (sameType_whnf a uInner) ?_
          rw [hUWhnf]
          exact sameType_arrow (sameType_trans hMid₂ (sameType_symm hMid₁)) (sameType_refl a prov₂)
        obtain ⟨lv, lOk, lUses⟩ := yields_elim ((lRun annotations lChild).2 lowerRep hLowerRepSame)
        obtain ⟨uv, uOk, uUses⟩ := yields_elim ((uRun annotations uChild).2 upperRep hUpperRepSame)
        simp only [checkAt] at lOk uOk
        have hRepL : callable (representativeHead a annotations path lowerRep) =
            .arrow .reusable .unrestricted self₁ (.arrow .reusable .unrestricted inh₁ mid₁) := by
          simp [representativeHead, root, lowerRep, retargetCallable_callable]
        have hRepU : callable (representativeHead a annotations path upperRep) =
            .arrow .reusable .unrestricted self₁ (.arrow .reusable .unrestricted mid₁ prov₂) := by
          simp [representativeHead, root, upperRep, retargetCallable_callable]
        have hCap' : reusableCaptures a.shareableVariables Γ' (addUses lv.uses uv.uses) = true := by
          rw [lUses, uUses]; exact reusableCaptures_refines sc r captures
        have hShSelf : self₁.shareableUnder a.shareableVariables = true := by
          rw [shareable_congr sc hSelf₁]; exact shareSelf
        have hShInh : inh₁.shareableUnder a.shareableVariables = true := by
          rw [shareable_congr sc hInh₁]; exact shareInherited
        have hShMid : mid₁.shareableUnder a.shareableVariables = true := by
          rw [shareable_congr sc hMid₁]; exact shareMiddle
        constructor
        · change Yields (elaborate a annotations Γ' path (.mix lower upper) .synth) _
          rw [elaborate]
          simp only [root, hint, lOk, uOk, Except.map, bind, Except.bind, checkedSynth]
          split
          · rename_i selfA inhA midA selfB midB provB hlObs huObs
            rw [hRepL] at hlObs; rw [hRepU] at huObs
            cases hlObs; cases huObs
            simp only [↓reduceDIte, need_ok hCap', need_ok hShSelf, need_ok hShInh, need_ok hShMid,
              finish, ascribe, root, hint, Yields, lUses, uUses]
            by_cases hm : sameType a mixType upperRep = true
            · simp [mixType, predicted, hm]
            · simp [mixType, predicted, hm]
          · rename_i hne
            exact (hne self₁ inh₁ mid₁ self₁ mid₁ prov₂ hRepL hRepU).elim
        · intro expected agreement
          have hMixExp : sameType a mixType expected = true := by
            dsimp only [predicted] at agreement
            by_cases hm : sameType a mixType upperRep = true
            · simp only [hm, ↓reduceIte] at agreement
              exact sameType_trans hm agreement
            · simp only [hm, Bool.false_eq_true, ↓reduceIte] at agreement
              exact agreement
          change Yields (elaborate a annotations Γ' path (.mix lower upper) (.check expected)) _
          rw [elaborate]
          simp only [root, hint, lOk, uOk, Except.map, bind, Except.bind, checkedSynth]
          split
          · rename_i selfA inhA midA selfB midB provB hlObs huObs
            rw [hRepL] at hlObs; rw [hRepU] at huObs
            cases hlObs; cases huObs
            simp [need_ok hCap', need_ok hShSelf, need_ok hShInh, need_ok hShMid,
              finish, mixType, hMixExp, Yields, lUses, uUses]
          · rename_i hne
            exact (hne self₁ inh₁ mid₁ self₁ mid₁ prov₂ hRepL hRepU).elim
    · obtain ⟨lt, lT, lPrepared, lSame, _⟩ := ihL.1.1 sl Γ' r (path ++ [0])
      obtain ⟨ut, uT, uPrepared, uSame, _⟩ := ihU.1.1 su Γ' r (path ++ [1])
      obtain ⟨self₁, lInner, hLCall, _, hLInner⟩ := exposeCallable_transport lSame lowerShape
      obtain ⟨self₂, uInner, hUCall, _, hUInner⟩ := exposeCallable_transport uSame upperShape
      obtain ⟨inh₁, mid₁, hLWhnf, _, _⟩ := whnf_arrow_inv hLInner
      obtain ⟨mid₂, prov₂, hUWhnf, _, _⟩ := whnf_arrow_inv hUInner
      simp [prepare, lPrepared, uPrepared, hLCall, hUCall, hLWhnf, hUWhnf,
        bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | mix sl su => exact (synth sl su Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | mix sl su =>
        obtain ⟨ok, sameTree⟩ := synth sl su Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)

theorem prepare_fix_nonlam {hints : Annotations} {Γ : Context} {path : List Nat}
    {spec inheritedTerm : Term} {mode : Mode} (notLam : ∀ body, spec ≠ .lam body) :
    prepare a hints Γ path (.fix spec inheritedTerm) mode = (do
      let (specTree, specType) ← prepare a hints Γ (path ++ [0]) spec .synth
      let deeper := exposeCallable a (tyNodes specType + (a.bounds.map (tyNodes ·.2)).sum + 1) specType
      match callable deeper with
      | .arrow .reusable .unrestricted target inner =>
        match whnf a inner with
        | .arrow .reusable .unrestricted inherited _ =>
          let fixedSpec := retargetCallable deeper
            (.arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target))
          let (inheritedTree, _) ← prepare a hints Γ (path ++ [1]) inheritedTerm (.check inherited)
          pure (.node (some (hint fixedSpec target)) [specTree, inheritedTree],
            match mode with | .synth => target | .check expected => expected)
        | _ => throw (.shape (path ++ [0]) "fixable specification" specType)
      | _ => throw (.shape (path ++ [0]) "fixable specification" specType)) := by
  rw [prepare]
  · rfl
  · intro body _ h _ _; exact notLam body h

theorem motive_fix (sc : ShareableComplete a = true) {Γ : Context} {spec inheritedTerm : Term}
    {specType inherited target : Ty} {su iu : Uses}
    (shape : callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target))
    (shareTarget : target.shareableUnder a.shareableVariables = true)
    (allowed : argumentAllowed a .unrestricted Γ inherited iu = true)
    (captures : reusableCaptures a.shareableVariables Γ su = true)
    (ihS : Motive a Γ spec specType su) (ihI : Motive a Γ inheritedTerm inherited iu) :
    Motive a Γ (.fix spec inheritedTerm) target (addUses su iu) := by
  have general : Synthable spec → Checkable inheritedTerm → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.fix spec inheritedTerm) target (addUses su iu) ∧
      ∀ path tree predicted expected,
        prepare a noHints Γ' path (.fix spec inheritedTerm) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.fix spec inheritedTerm) (.check expected) = .ok (tree, expected) := by
    intro ss ci Γ' r
    have notLam := synthable_not_lam ss
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨st, sT, sPrepared, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
      let deeper := exposeCallable a (tyNodes sT + (a.bounds.map (tyNodes ·.2)).sum + 1) sT
      obtain ⟨tgt₁, inner, hCall, hTgt₁, hInner⟩ := exposeCallable_transport sSame shape
      change callable deeper = .arrow .reusable .unrestricted tgt₁ inner at hCall
      obtain ⟨inh₁, out₁, hWhnf, hInh₁, hOut₁⟩ := whnf_arrow_inv hInner
      let fixedSpec := retargetCallable deeper
        (.arrow .reusable .unrestricted tgt₁ (.arrow .reusable .unrestricted inh₁ tgt₁))
      obtain ⟨it, _, iPrepared, iRun⟩ := ihI.1.2 ci Γ' r inh₁ (sameType_symm hInh₁) (path ++ [1])
      refine ⟨.node (some (hint fixedSpec tgt₁)) [st, it], tgt₁, ?_, hTgt₁, ?_⟩
      · rw [prepare_fix_nonlam notLam]
        simp [sPrepared, deeper, hCall, hWhnf, fixedSpec, iPrepared, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have sChild := realizes_child realizes 0 st rfl
        have iChild := realizes_child realizes 1 it rfl
        have hSD : sameType a sT deeper = true :=
          exposeCallable_sameType a (tyNodes sT + (a.bounds.map (tyNodes ·.2)).sum + 1) sT
        have hFixedSame : sameType a sT fixedSpec = true := by
          refine sameType_trans hSD ?_
          refine sameType_retargetCallable hCall (sameType_refl a tgt₁) ?_
          refine sameType_trans (sameType_whnf a inner) ?_
          rw [hWhnf]
          exact sameType_arrow (sameType_refl a inh₁) (sameType_trans hOut₁ (sameType_symm hTgt₁))
        obtain ⟨sv, sOk, sUses⟩ := yields_elim ((sRun annotations sChild).2 fixedSpec hFixedSame)
        obtain ⟨iv, iOk, iUses⟩ := yields_elim (iRun annotations iChild)
        simp only [checkAt] at sOk iOk
        have hRep : callable (representativeHead a annotations path fixedSpec) =
            .arrow .reusable .unrestricted tgt₁ (.arrow .reusable .unrestricted inh₁ tgt₁) := by
          simp [representativeHead, root, fixedSpec, retargetCallable_callable]
        have hShTgt : tgt₁.shareableUnder a.shareableVariables = true := by
          rw [shareable_congr sc hTgt₁]; exact shareTarget
        have hAllowed' : argumentAllowed a .unrestricted Γ' inh₁ iv.uses = true := by
          rw [iUses]; exact argumentAllowed_refines sc r hInh₁ allowed
        have hCap' : reusableCaptures a.shareableVariables Γ' sv.uses = true := by
          rw [sUses]; exact reusableCaptures_refines sc r captures
        constructor
        · change Yields (elaborate a annotations Γ' path (.fix spec inheritedTerm) .synth) _
          rw [elaborate]
          simp only [root, hint, sOk, Except.map, bind, Except.bind, checkedSynth]
          split
          · rename_i tA iA oA hObs
            rw [hRep] at hObs; cases hObs
            simp [iOk, need_ok hShTgt, need_ok hAllowed', need_ok hCap', finish, ascribe,
              root, hint, sameType_refl, Yields, sUses, iUses]
          · rename_i hne
            exact (hne tgt₁ inh₁ tgt₁ hRep).elim
        · intro expected agreement
          change Yields (elaborate a annotations Γ' path (.fix spec inheritedTerm) (.check expected)) _
          rw [elaborate]
          simp only [root, hint, sOk, Except.map, bind, Except.bind, checkedSynth]
          split
          · rename_i tA iA oA hObs
            rw [hRep] at hObs; cases hObs
            simp [iOk, need_ok hShTgt, need_ok hAllowed', need_ok hCap', finish,
              agreement, Yields, sUses, iUses]
          · rename_i hne
            exact (hne tgt₁ inh₁ tgt₁ hRep).elim
    · obtain ⟨st, sT, sPrepared, sSame, _⟩ := ihS.1.1 ss Γ' r (path ++ [0])
      obtain ⟨tgt₁, inner, hCall, _, hInner⟩ := exposeCallable_transport sSame shape
      obtain ⟨inh₁, _, hWhnf, hInh₁, _⟩ := whnf_arrow_inv hInner
      obtain ⟨it, _, iPrepared, _⟩ := ihI.1.2 ci Γ' r inh₁ (sameType_symm hInh₁) (path ++ [1])
      rw [prepare_fix_nonlam notLam] at prepared ⊢
      simp [sPrepared, hCall, hWhnf, iPrepared, bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  have fixLam : ∀ body, spec = .lam body → Checkable body → Synthable inheritedTerm →
      ∀ Γ', Refines a Γ' Γ → ∀ expected, sameType a target expected = true →
        CheckOK a Γ' (.fix (.lam body) inheritedTerm) expected (addUses su iu) := by
    intro body isLam cb si Γ' r expected agreement path
    obtain ⟨reuse0, q0, d0, c0, bodyUses, same, suEq, safe, valid, fits0, bodyModes⟩ := ihS.2 body isLam
    obtain ⟨_, hr0, hq0, hd0, hc0⟩ := callable_arrow_agrees (rfl : callable (.arrow ..) = .arrow ..) shape same
    subst hr0; subst hq0
    obtain ⟨it, iT, iPrepared, iSame, iRun⟩ := ihI.1.1 si Γ' r (path ++ [1])
    let specGoal := Ty.arrow .reusable .unrestricted expected (.arrow .reusable .unrestricted iT expected)
    have hCap0 : reusableAllowed a .reusable Γ bodyUses.tail = true := by
      rw [← suEq]; simp [reusableAllowed, captures]
    have hLamMotive := motive_lambda_modes (annotation := ⟨d0, c0, .unrestricted, .reusable⟩)
      sc safe valid hCap0 fits0 bodyModes
    have hSpecAgrees : sameType a (.arrow .reusable .unrestricted d0 c0) specGoal = true :=
      sameType_arrow (sameType_trans hd0 agreement)
        (sameType_trans hc0 (sameType_arrow (sameType_symm iSame) agreement))
    obtain ⟨st, sRes, sPrepared, sRun⟩ :=
      hLamMotive.1.2 (.lam cb) Γ' r specGoal hSpecAgrees (path ++ [0])
    refine ⟨.node (some (hint specGoal expected)) [st, it], expected, ?_, ?_⟩
    · rw [prepare]
      · simp only [iPrepared, specGoal, sPrepared, bind, Except.bind, pure, Except.pure]
      · rfl
    · intro annotations realizes
      have root := realizes_root realizes
      have sChild := realizes_child realizes 0 st rfl
      have iChild := realizes_child realizes 1 it rfl
      obtain ⟨sv, sOk, sUses⟩ := yields_elim (sRun annotations sChild)
      obtain ⟨iv, iOk, iUses⟩ := yields_elim ((iRun annotations iChild).2 iT (sameType_refl _ _))
      simp only [checkAt] at sOk iOk
      have hRep : callable (representativeHead a annotations path specGoal) =
          .arrow .reusable .unrestricted expected (.arrow .reusable .unrestricted iT expected) := by
        simp [representativeHead, root, specGoal, callable]
      have hShExp : expected.shareableUnder a.shareableVariables = true := by
        rw [← shareable_congr sc agreement]; exact shareTarget
      have hAllowed' : argumentAllowed a .unrestricted Γ' iT iv.uses = true := by
        rw [iUses]; exact argumentAllowed_refines sc r iSame allowed
      have hCap' : reusableCaptures a.shareableVariables Γ' sv.uses = true := by
        rw [sUses, ← suEq]; exact reusableCaptures_refines sc r captures
      change Yields (elaborate a annotations Γ' path (.fix (.lam body) inheritedTerm) (.check expected)) _
      rw [elaborate]
      simp only [root, hint, sOk, Except.map, bind, Except.bind, checkedSynth]
      split
      · rename_i tA iA oA hObs
        rw [hRep] at hObs; cases hObs
        simp [iOk, need_ok hShExp, need_ok hAllowed', need_ok hCap', finish, sameType_refl,
          Yields, sUses, ← suEq, iUses]
      · rename_i hne
        exact (hne expected iT expected hRep).elim
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | fix ss ci => exact (general ss ci Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | fix ss ci =>
        obtain ⟨ok, sameTree⟩ := general ss ci Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)
    | fixLam cb si => exact fixLam _ rfl cb si Γ' r expected agreement

/-! ### Introductions, Records, `.extend`, & `.case` / `.effectCase` -/

theorem motive_ifBool {Γ : Context} {condition whenTrue whenFalse : Term} {result : Ty} {cu tu fu : Uses}
    (ihC : Motive a Γ condition .boolean cu) (ihT : Motive a Γ whenTrue result tu)
    (ihF : Motive a Γ whenFalse result fu) (agreeing : branchesAgree Γ tu fu = true) :
    Motive a Γ (.ifBool condition whenTrue whenFalse) result (addUses cu (joinUses tu fu)) := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  obtain ⟨cc, ct, cf⟩ : Checkable condition ∧ Checkable whenTrue ∧ Checkable whenFalse := by
    cases c with
    | synth s => cases s
    | ifBool cc ct cf => exact ⟨cc, ct, cf⟩
  intro path
  obtain ⟨tc, _, pc, rc⟩ := ihC.1.2 cc Γ' r .boolean (sameType_refl _ _) (path ++ [0])
  obtain ⟨tt, _, pt, rt⟩ := ihT.1.2 ct Γ' r expected agreement (path ++ [1])
  obtain ⟨tf, _, pf, rf⟩ := ihF.1.2 cf Γ' r expected agreement (path ++ [2])
  refine ⟨.node none [tc, tt, tf], expected, ?_, ?_⟩
  · simp [prepare, pc, pt, pf, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    obtain ⟨vc, okc, uc⟩ := yields_elim (rc annotations (realizes_child realizes 0 tc rfl))
    obtain ⟨vt, okt, ut⟩ := yields_elim (rt annotations (realizes_child realizes 1 tt rfl))
    obtain ⟨vf, okf, uf⟩ := yields_elim (rf annotations (realizes_child realizes 2 tf rfl))
    simp only [checkAt] at okc okt okf
    change Yields (elaborate a annotations Γ' path (.ifBool condition whenTrue whenFalse) (.check expected)) _
    rw [elaborate]
    have agreeing' : branchesAgree Γ' vt.uses vf.uses = true := by
      rw [ut, uf]; exact branchesAgree_refines r agreeing
    simp [introduce, root, okc, okt, okf, bind, Except.bind, pure, Except.pure, Yields, uc, ut, uf,
      need_ok agreeing']

theorem motive_inject {Γ : Context} {tag : String} {payload : Term}
    {payloadType row : Ty} {uses : Uses} {fuel : Nat}
    (found : row.lookup a.bounds fuel tag = some payloadType) (nonComputation : payloadType.isComputation = false)
    (ih : Motive a Γ payload payloadType uses) :
    Motive a Γ (.inject tag payload) (.variant row) uses := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  have cp : Checkable payload := by
    cases c with
    | synth s => cases s
    | inject _ cp => exact cp
  obtain ⟨row', hwhnf, hrow⟩ := whnf_variant_inv (sameType_symm agreement)
  have lookup : lookupV a.bounds [] row tag = some payloadType := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  obtain ⟨payload', found', same'⟩ := lookupV_transport hrow lookup
  have nonActivity : (!payload'.isComputation) = true := by
    rw [sameType_isComputation same', nonComputation]; rfl
  have sum : ∀ annotations path, annotations path = none →
      injectionHead a annotations path expected = .variant row' := by
    intro annotations path none'
    simp [injectionHead, representativeHead, none', hwhnf]
  intro path
  obtain ⟨pt, _, pp, rp⟩ := ih.1.2 cp Γ' r payload' (sameType_symm same') (path ++ [0])
  refine ⟨.node none [pt], expected, ?_, ?_⟩
  · simp [prepare, noHints, injectionSum, hwhnf, found', pp, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    obtain ⟨v, ok, vu⟩ := yields_elim (rp annotations (realizes_child realizes 0 pt rfl))
    simp only [checkAt] at ok
    change Yields (elaborate a annotations Γ' path (.inject tag payload) (.check expected)) _
    rw [elaborate]
    simp only [introduce, root]
    split
    · rename_i r' shape
      rw [sum annotations path root] at shape
      cases shape
      split
      · rename_i m h
        rw [found'] at h; cases h
        simp [ok, need_ok nonActivity, bind, Except.bind, pure, Except.pure, Yields, vu]
      · rename_i h; rw [found'] at h; contradiction
    · rename_i hne
      exact (hne _ (sum annotations path root)).elim

public def RowAgrees (a : Assumptions) : Ty → Ty → Prop
  | .emptyRow, .emptyRow => True
  | .field n m t, .field n' m' t' => n = n' ∧ sameType a m m' = true ∧ RowAgrees a t t'
  | _, _ => False

theorem rowAgrees_sameType : ∀ {r r' : Ty}, RowAgrees a r r' → sameType a r r' = true := by
  intro r
  induction r with
  | field n m t _ iht =>
    intro r' h
    cases r' <;> simp only [RowAgrees] at h
    obtain ⟨hn, hm, ht⟩ := h
    subst hn; exact sameType_field hm (iht ht)
  | emptyRow => intro r' h; cases r' <;> simp only [RowAgrees] at h; exact sameType_refl _ _
  | _ => intro r' h; cases r' <;> simp only [RowAgrees] at h

theorem sameType_overlay {inh' inh : Ty} (hInh : sameType a inh' inh = true) :
    ∀ {r' r : Ty}, RowAgrees a r' r → sameType a (overlay r' inh') (overlay r inh) = true := by
  intro r'
  induction r' with
  | field n m t _ iht =>
    intro r h
    cases r <;> simp only [RowAgrees] at h
    obtain ⟨hn, hm, ht⟩ := h
    subst hn
    exact sameType_field hm (iht ht)
  | emptyRow =>
    intro r h
    cases r <;> simp only [RowAgrees] at h
    exact hInh
  | _ =>
    intro r h
    cases r <;> simp only [RowAgrees] at h

theorem lookupV_head (name : String) (member tail : Ty) :
    lookupV a.bounds [] (.field name member tail) name = some member :=
  (lookupV_iff _ _ _ _).2 ⟨1, by simp [Ty.lookup]⟩

theorem lookupV_field_ne {name other : String} {member tail result : Ty} (ne : name ≠ other) :
    lookupV a.bounds [] (.field name member tail) other = some result ↔
      lookupV a.bounds [] tail other = some result := by
  rw [lookupV_iff, lookupV_iff]
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [Ty.lookup] at h
    | succ fuel => simp [Ty.lookup, ne] at h; exact ⟨fuel, h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel + 1, by simp [Ty.lookup, ne, h]⟩

theorem lookupRow_agrees {Γ : Context} :
    ∀ {fields : List (String × Term)} {row : Ty} {uses : Uses}, FieldsTyping a Γ fields row uses →
    labelsDistinct fields = true → ∀ (expected : Ty),
    (∀ name member, name ∈ fields.map Prod.fst → lookupV a.bounds [] row name = some member →
      ∃ member', lookupV a.bounds [] expected name = some member' ∧ sameType a member' member = true) →
    ∃ row', lookupRow a expected fields = some row' ∧ RowAgrees a row' row
  | [], _, _, .nil _, _, _, _ => ⟨.emptyRow, rfl, trivial⟩
  | (name, body) :: rest, _, _, .cons (type := type) (row := tail) _ restTyped _, distinct, expected, transport => by
    simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      beq_iff_eq] at distinct
    obtain ⟨member', found, same⟩ := transport name type (by simp) (lookupV_head name type tail)
    obtain ⟨row', rest', agrees⟩ := lookupRow_agrees restTyped distinct.2 expected (by
      intro other member mem found'
      have ne : name ≠ other := by
        intro h; subst h
        obtain ⟨arm, inside, eq⟩ := List.mem_map.mp mem
        exact distinct.1 arm inside eq
      exact transport other member (by simp [mem]) ((lookupV_field_ne ne).2 found'))
    exact ⟨.field name member' row', by simp [lookupRow, found, rest', bind, Option.bind], rfl, same, agrees⟩

theorem forest_of_node {annotations : Annotations} {path : List Nat} {here : Option LambdaAnnotation}
    {children : List AnnotationTree} (realizes : Realizes annotations path (.node here children)) :
    ForestRealizes annotations path 0 children := by
  intro offset suffix
  simpa only [Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append, AnnotationTree.lookup,
    AnnotationTree.child] using realizes (offset :: suffix)

theorem forest_head {annotations : Annotations} {path : List Nat} {index : Nat} {tree : AnnotationTree}
    {trees : List AnnotationTree} (realizes : ForestRealizes annotations path index (tree :: trees)) :
    Realizes annotations (path ++ [index]) tree := by
  simpa using realizes 0

theorem forest_tail {annotations : Annotations} {path : List Nat} {index : Nat} {tree : AnnotationTree}
    {trees : List AnnotationTree} (realizes : ForestRealizes annotations path index (tree :: trees)) :
    ForestRealizes annotations path (index + 1) trees := by
  intro offset
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using realizes (offset + 1)

public def FieldsMotive (a : Assumptions) (Γ : Context) (fields : List (String × Term)) (row : Ty)
    (uses : Uses) : Prop :=
  (FieldsCheckable fields → ∀ Γ', Refines a Γ' Γ → ∀ row', RowAgrees a row' row → ∀ path index,
    ∃ trees, prepareFieldsCheck a noHints Γ' path index fields row' = .ok trees ∧
      ∀ annotations, ForestRealizes annotations path index trees →
        Yields (checkFields a annotations Γ' path index fields row') (fun r => r.uses = uses)) ∧
  (FieldsSynthable fields → ∀ Γ', Refines a Γ' Γ → ∀ path index,
    ∃ trees row', prepareFieldsSynth a noHints Γ' path index fields = .ok (trees, row') ∧
      RowAgrees a row' row ∧
      ∀ annotations, ForestRealizes annotations path index trees →
        Yields (synthFields a annotations Γ' path index fields)
          (fun r => r.type = row' ∧ r.uses = uses))

theorem fieldsMotive_nil (Γ : Context) : FieldsMotive a Γ [] .emptyRow (zeroUses Γ) := by
  refine ⟨fun _ Γ' r row' agrees path index => ?_, fun _ Γ' r path index => ?_⟩
  · cases row' <;> simp [RowAgrees] at agrees
    refine ⟨[], rfl, fun annotations _ => ?_⟩
    simp [checkFields, pure, Except.pure, Yields, zeroUses_length (refines_length r)]
  · refine ⟨[], .emptyRow, rfl, trivial, fun annotations _ => ?_⟩
    simp [synthFields, pure, Except.pure, Yields, zeroUses_length (refines_length r)]

theorem fieldsMotive_cons {Γ : Context} {name : String} {body : Term} {rest : List (String × Term)}
    {type row : Ty} {bu ru : Uses} (nonComputation : type.isComputation = false)
    (ihB : Motive a Γ body type bu) (ihR : FieldsMotive a Γ rest row ru) :
    FieldsMotive a Γ ((name, body) :: rest) (.field name type row) (addUses bu ru) := by
  refine ⟨fun fc Γ' r row' agrees path index => ?_, fun fs Γ' r path index => ?_⟩
  · have ⟨cb, cr⟩ : Checkable body ∧ FieldsCheckable rest := by
      cases fc with | cons cb cr => exact ⟨cb, cr⟩
    cases row' with
    | field name' member' tail' =>
      obtain ⟨hn, hm, ht⟩ := agrees
      subst hn
      obtain ⟨tree, _, pb, rb⟩ := ihB.1.2 cb Γ' r member' (sameType_symm hm) (path ++ [index])
      obtain ⟨trees, pr, rr⟩ := ihR.1 cr Γ' r tail' ht path (index + 1)
      refine ⟨tree :: trees, by simp [prepareFieldsCheck, pb, pr, bind, Except.bind, pure, Except.pure], ?_⟩
      intro annotations realizes
      obtain ⟨vb, okb, ub⟩ := yields_elim (rb annotations (forest_head realizes))
      obtain ⟨vr, okr, ur⟩ := yields_elim (rr annotations (forest_tail realizes))
      simp only [checkAt] at okb
      have nonActivity : (!member'.isComputation) = true := by
        rw [sameType_isComputation hm, nonComputation]; rfl
      rw [checkFields]
      simp [okb, okr, need_ok nonActivity, bind, Except.bind, pure, Except.pure, Yields, ub, ur]
    | _ => all_goals (simp [RowAgrees] at agrees)
  · have ⟨sb, sr⟩ : Synthable body ∧ FieldsSynthable rest := by
      cases fs with | cons sb sr => exact ⟨sb, sr⟩
    obtain ⟨tree, bT, pb, bSame, rb⟩ := ihB.1.1 sb Γ' r (path ++ [index])
    obtain ⟨trees, row', pr, rAgrees, rr⟩ := ihR.2 sr Γ' r path (index + 1)
    refine ⟨tree :: trees, .field name bT row',
      by simp [prepareFieldsSynth, pb, pr, bind, Except.bind, pure, Except.pure],
      ⟨rfl, bSame, rAgrees⟩, ?_⟩
    intro annotations realizes
    obtain ⟨vb, okb, bType, ub⟩ := yields_elim (rb annotations (forest_head realizes)).1
    obtain ⟨vr, okr, rType, ur⟩ := yields_elim (rr annotations (forest_tail realizes))
    simp only [synthAt] at okb
    have nonActivity : (!vb.type.isComputation) = true := by
      rw [bType, sameType_isComputation bSame, nonComputation]; rfl
    rw [synthFields]
    simp [okb, okr, need_ok nonActivity, bind, Except.bind, pure, Except.pure, Yields, bType, rType, ub, ur]

theorem motive_record {Γ : Context} {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (typed : FieldsTyping a Γ fields row uses) (ih : FieldsMotive a Γ fields row uses) :
    Motive a Γ (.record fields) row uses := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  obtain ⟨distinct, fc⟩ : labelsDistinct fields = true ∧ FieldsCheckable fields := by
    cases c with
    | synth s => cases s
    | record d fc => exact ⟨d, fc⟩
  obtain ⟨row', found, agrees⟩ := lookupRow_agrees typed distinct expected
    (fun name member _ found => lookupV_transport (sameType_symm agreement) found)
  intro path
  obtain ⟨trees, pf, rf⟩ := ih.1 fc Γ' r row' agrees path 0
  refine ⟨.node (some (selfHint row')) trees, expected, ?_, ?_⟩
  · simp [prepare, distinct, found, pf, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    obtain ⟨v, ok, vu⟩ := yields_elim (rf annotations (forest_of_node realizes))
    have toExpected : sameType a row' expected = true := sameType_trans (rowAgrees_sameType agrees) agreement
    change Yields (elaborate a annotations Γ' path (.record fields) (.check expected)) _
    rw [elaborate]
    simp [introduce, root, selfHint, hint, ok, bind, Except.bind, pure, Except.pure, finish, checkedSynth,
      toExpected, Yields, vu, need_ok distinct]

theorem motive_extend {Γ : Context} {target : Term} {fields : List (String × Term)}
    {targetType row : Ty} {tu fu : Uses} {fuel : Nat}
    (distinct : labelsDistinct fields = true)
    (isRow : targetType.isRow a.bounds fuel = true)
    (free : linearFree Γ tu = true)
    (ihT : Motive a Γ target targetType tu) (ihF : FieldsMotive a Γ fields row fu) :
    Motive a Γ (.extend target fields) (overlay row targetType) (addUses tu fu) := by
  have synth : Synthable target → FieldsSynthable fields → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.extend target fields) (overlay row targetType) (addUses tu fu) ∧
      ∀ path tree predicted expected,
        prepare a noHints Γ' path (.extend target fields) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.extend target fields) (.check expected) = .ok (tree, expected) := by
    intro st sf Γ' r
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨tt, tT, tPrepared, tSame, tRun⟩ := ihT.1.1 st Γ' r (path ++ [0])
      obtain ⟨trees, row', fPrepared, rAgrees, fRun⟩ := ihF.2 sf Γ' r (path ++ [1]) 0
      have hOverlay : sameType a (overlay row' tT) (overlay row targetType) = true :=
        sameType_overlay tSame rAgrees
      refine ⟨.node none [tt, .node none trees], overlay row' tT, ?_, hOverlay, ?_⟩
      · simp [prepare, tPrepared, fPrepared, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have tChild := realizes_child realizes 0 tt rfl
        have fForest := forest_of_node (realizes_child realizes 1 (.node none trees) rfl)
        obtain ⟨pv, pOk, pType, pUses⟩ := yields_elim (tRun annotations tChild).1
        obtain ⟨mv, mOk, mType, mUses⟩ := yields_elim (fRun annotations fForest)
        simp only [synthAt] at pOk
        have isRow' : isRowV a.bounds [] pv.type = true := by
          rw [pType]
          exact (isRowV_iff a.bounds tT).mpr
            (equivalent_finite_row_transport ((sameType_iff _ _ _).mp tSame) fuel isRow)
        have free' : linearFree Γ' pv.uses = true := by
          rw [pUses]; exact linearFree_refines r free
        constructor
        · change Yields (elaborate a annotations Γ' path (.extend target fields) .synth) _
          rw [elaborate]
          simp [root, pOk, mOk, need_ok isRow', need_ok distinct, need_ok free',
            bind, Except.bind, pure, Except.pure, Yields, pType, mType, pUses, mUses]
        · intro expected agreement
          have hExp : sameType a (overlay mv.type pv.type) expected = true := by
            rw [mType, pType]; exact agreement
          change Yields (elaborate a annotations Γ' path (.extend target fields) (.check expected)) _
          rw [elaborate]
          simp [root, pOk, mOk, need_ok isRow', need_ok distinct, need_ok free',
            bind, Except.bind, pure, Except.pure, hExp, Yields, pUses, mUses]
    · obtain ⟨tt, tT, tPrepared, _, _⟩ := ihT.1.1 st Γ' r (path ++ [0])
      obtain ⟨trees, row', fPrepared, _, _⟩ := ihF.2 sf Γ' r (path ++ [1]) 0
      simp [prepare, tPrepared, fPrepared, bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | extend st sf => exact (synth st sf Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | extend st sf =>
        obtain ⟨ok, sameTree⟩ := synth st sf Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)

/-! ### Cases & Effect Cases Over Arbitrary `Assumptions` -/

public def MembersAgree (a : Assumptions) (row' : Ty) : Ty → Prop
  | .field name payload tail =>
      (∃ payload', rowMember row' name = some payload' ∧ sameType a payload' payload = true) ∧
      MembersAgree a row' tail
  | _ => True

theorem lookupRow_arms_agrees {Γ : Context} :
    ∀ {q : Quantity} {arms : List (String × Term)} {row result : Ty} {uses : Uses},
      ArmsTyping a Γ q arms row result uses →
      labelsDistinct arms = true →
      ∀ (expected : Ty),
        (∀ name member, name ∈ arms.map Prod.fst → lookupV a.bounds [] row name = some member →
          ∃ member', lookupV a.bounds [] expected name = some member' ∧ sameType a member' member = true) →
        ∃ row', lookupRow a expected arms = some row' ∧ RowAgrees a row' row
  | _, [], _, _, _, .nil .., _, _, _ => ⟨.emptyRow, rfl, trivial⟩
  | _, (name, body) :: rest, _, _, _, .cons (payload := payload) (row := tail) _ _ _ _ restTyped _, distinct, expected, transport => by
    simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      beq_iff_eq] at distinct
    obtain ⟨member', found, same⟩ := transport name payload (by simp) (lookupV_head name payload tail)
    obtain ⟨row', rest', agrees⟩ := lookupRow_arms_agrees restTyped distinct.2 expected (by
      intro other member mem found'
      have ne : name ≠ other := by
        intro h; subst h
        obtain ⟨arm, inside, eq⟩ := List.mem_map.mp mem
        exact distinct.1 arm inside eq
      exact transport other member (by simp [mem]) ((lookupV_field_ne ne).2 found'))
    exact ⟨.field name member' row', by simp [lookupRow, found, rest', bind, Option.bind], rfl, same, agrees⟩

theorem membersAgree_cons_ne {Γ : Context} {row' : Ty} {first : String} {head : Ty} :
    ∀ {q : Quantity} {arms : List (String × Term)} {row result : Ty} {uses : Uses},
      ArmsTyping a Γ q arms row result uses →
      (∀ arm ∈ arms, arm.1 ≠ first) →
      MembersAgree a row' row →
      MembersAgree a (.field first head row') row
  | _, [], _, _, _, .nil .., _, _ => trivial
  | _, (name, body) :: rest, _, _, _, .cons _ _ _ _ restTyped _, hne, ⟨⟨p', hp', hs⟩, htail⟩ => by
    have hne0 : first ≠ name := (hne (name, body) List.mem_cons_self).symm
    refine ⟨⟨p', by simp [rowMember, hne0, hp'], hs⟩, ?_⟩
    exact membersAgree_cons_ne restTyped (fun arm hm => hne arm (List.mem_cons_of_mem _ hm)) htail

theorem membersAgree_of_rowAgrees {Γ : Context} :
    ∀ {q : Quantity} {arms : List (String × Term)} {row row' result : Ty} {uses : Uses},
      ArmsTyping a Γ q arms row result uses →
      labelsDistinct arms = true →
      RowAgrees a row' row →
      MembersAgree a row' row
  | _, [], _, _, _, _, .nil .., _, _ => trivial
  | _, (name, body) :: rest, _, row', _, _, .cons _ _ _ _ restTyped _, distinct, agrees => by
    cases row' <;> simp only [RowAgrees] at agrees
    rename_i name' payload' tail'
    obtain ⟨hn, hp, ht⟩ := agrees; subst hn
    simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.any_eq_false, beq_iff_eq] at distinct
    refine ⟨⟨payload', by simp [rowMember], hp⟩, ?_⟩
    exact membersAgree_cons_ne restTyped (fun arm hm h => distinct.1 arm hm h)
      (membersAgree_of_rowAgrees restTyped distinct.2 ht)

public def ArmRefines (a : Assumptions) (q' q : Quantity) (row' : Ty) (arms : List (String × Term)) : Prop :=
  q' = q ∨
    (q' = .affine ∧ armsCustody row' arms = false ∧ q ≠ .unrestricted) ∨
    (q' = .unrestricted ∧ armsShareable a row' arms = true)

theorem armRefines_tail {q' q : Quantity} {row' : Ty} {arm : String × Term} {rest : List (String × Term)}
    (h : ArmRefines a q' q row' (arm :: rest)) : ArmRefines a q' q row' rest := by
  rcases h with same | ⟨affine, noCust, notU⟩ | ⟨unr, sh⟩
  · exact .inl same
  · refine .inr (.inl ⟨affine, ?_, notU⟩)
    simp only [armsCustody, List.any_cons, Bool.or_eq_false_iff] at noCust
    exact noCust.2
  · refine .inr (.inr ⟨unr, ?_⟩)
    simp only [armsShareable, List.all_cons, Bool.and_eq_true] at sh
    simpa [armsShareable] using sh.2

public def ArmsMotive (a : Assumptions) (Γ : Context) (q : Quantity)
    (arms : List (String × Term)) (row result : Ty) (uses : Uses) : Prop :=
  (FieldsCheckable arms → ∀ Γ', Refines a Γ' Γ → ∀ row', MembersAgree a row' row → ∀ q', ArmRefines a q' q row' arms →
    ∀ result', sameType a result result' = true → ∀ path index,
    ∃ trees, prepareArms a noHints Γ' q' path index row' result' arms = .ok trees ∧
      ∀ annotations, ForestRealizes annotations path index trees →
        Yields (checkArms a annotations Γ' q' path index row' result' arms)
          (fun r => r.uses = uses ∧ RowAgrees a r.row row ∧ r.quantity = q')) ∧
  (∀ name body rest, arms = (name, body) :: rest →
    Synthable body → FieldsCheckable rest →
    ∀ Γ', Refines a Γ' Γ → ∀ row', MembersAgree a row' row → ∀ q', ArmRefines a q' q row' arms → ∀ path,
    ∃ payload' firstTree first,
      rowMember row' name = some payload' ∧
      prepare a noHints (⟨payload', q'⟩ :: Γ') (path ++ [0]) body .synth = .ok (firstTree, first) ∧
      sameType a first result = true ∧
      ∀ result', sameType a result result' = true →
        ∃ trees, prepareArms a noHints Γ' q' path 1 row' result' rest = .ok trees ∧
          ∀ annotations, ForestRealizes annotations path 0 (firstTree :: trees) →
            Yields (checkArms a annotations Γ' q' path 0 row' result' ((name, body) :: rest))
              (fun r => r.uses = uses ∧ RowAgrees a r.row row ∧ r.quantity = q'))

theorem armsMotive_nil (Γ : Context) (q : Quantity) (result : Ty) :
    ArmsMotive a Γ q [] .emptyRow result (zeroUses Γ) := by
  refine ⟨fun _ Γ' r row' _ q' _ result' _ path index => ?_, fun _ _ _ h => by cases h⟩
  refine ⟨[], rfl, fun annotations _ => ?_⟩
  simp [checkArms, pure, Except.pure, Yields, zeroUses_length (refines_length r), RowAgrees]

theorem armsMotive_cons (sc : ShareableComplete a = true) {Γ : Context} {name : String} {body : Term}
    {rest : List (String × Term)} {q : Quantity} {payload row result : Ty} {bu ru : Uses}
    (safe : safeUses (⟨payload, q⟩ :: Γ) bu = true)
    (share : validContext a.shareableVariables [⟨payload, q⟩] = true)
    (fits : q.fits (bu.headD 0) = true)
    (agreeing : (rest.isEmpty || branchesAgree Γ bu.tail ru) = true)
    (ihB : Motive a (⟨payload, q⟩ :: Γ) body result bu) (ihR : ArmsMotive a Γ q rest row result ru) :
    ArmsMotive a Γ q ((name, body) :: rest) (.field name payload row) result (joinUses bu.tail ru) := by
  have stepHead : ∀ {Γ' row' payload' q' result' path index tree trees},
      Refines a Γ' Γ →
      rowMember row' name = some payload' →
      sameType a payload' payload = true →
      QuantityRefines a ⟨payload', q'⟩ ⟨payload, q⟩ →
      (∀ annotations, Realizes annotations (path ++ [index]) tree →
        Yields (checkAt a annotations (⟨payload', q'⟩ :: Γ') (path ++ [index]) body result')
          (fun v => v.uses = bu)) →
      (∀ annotations, ForestRealizes annotations path (index + 1) trees →
        Yields (checkArms a annotations Γ' q' path (index + 1) row' result' rest)
          (fun r => r.uses = ru ∧ RowAgrees a r.row row ∧ r.quantity = q')) →
      ∀ annotations, ForestRealizes annotations path index (tree :: trees) →
        Yields (checkArms a annotations Γ' q' path index row' result' ((name, body) :: rest))
          (fun r => r.uses = joinUses bu.tail ru ∧ RowAgrees a r.row (.field name payload row) ∧ r.quantity = q') := by
    intro Γ' row' payload' q' result' path index tree trees r found same headQ rb rr annotations realizes
    have binder : Refines a (⟨payload', q'⟩ :: Γ') (⟨payload, q⟩ :: Γ) := .cons ⟨same, headQ⟩ r
    obtain ⟨vb, okb, ub⟩ := yields_elim (rb annotations (forest_head realizes))
    obtain ⟨vr, okr, ur, rowR, qR⟩ := yields_elim (rr annotations (forest_tail realizes))
    simp only [checkAt] at okb
    have share' : validContext a.shareableVariables [⟨payload', q'⟩] = true :=
      validContext_refines sc (.cons ⟨same, headQ⟩ .nil) share
    have safe' : safeUses (⟨payload', q'⟩ :: Γ') vb.uses = true := by
      rw [ub]; exact safeUses_refines binder safe
    have fits' : q'.fits (vb.uses.headD 0) = true := by
      rw [ub]
      rcases headQ with same' | ⟨affine, _, notU⟩ | ⟨unr, _⟩
      · simp only at same'; rw [same']; exact fits
      · simp only at affine notU; rw [affine]
        cases q <;> simp_all [Quantity.fits] <;> omega
      · simp only at unr; rw [unr]; rfl
    have agreeing' : (rest.isEmpty || branchesAgree Γ' vb.uses.tail vr.uses) = true := by
      rw [ub, ur]
      simp only [Bool.or_eq_true] at agreeing ⊢
      exact agreeing.imp id (branchesAgree_refines r)
    rw [checkArms]
    simp [found, okb, okr, need_ok share', need_ok safe', need_ok fits', need_ok agreeing', qR, bind, Except.bind,
      pure, Except.pure, Yields, ub, ur, RowAgrees, same, rowR]
  have mkHeadQ : ∀ {row' payload' q'},
      rowMember row' name = some payload' →
      ArmRefines a q' q row' ((name, body) :: rest) →
      QuantityRefines a ⟨payload', q'⟩ ⟨payload, q⟩ := by
    intro row' payload' q' found qr
    rcases qr with same' | ⟨affine, noCust, notU⟩ | ⟨unr, sh⟩
    · exact .inl same'
    · refine .inr (.inl ⟨affine, ?_, notU⟩)
      simp only [armsCustody, List.any_cons, Bool.or_eq_false_iff, found] at noCust
      exact noCust.1
    · refine .inr (.inr ⟨unr, ?_⟩)
      simp only [armsShareable, List.all_cons, Bool.and_eq_true, found] at sh
      exact sh.1
  refine ⟨fun fc Γ' r row' agrees q' qr result' agreement path index => ?_,
    fun name' body' rest' hEq sb cr Γ' r row' agrees q' qr path => ?_⟩
  · have ⟨cb, cr⟩ : Checkable body ∧ FieldsCheckable rest := by
      cases fc with | cons cb cr => exact ⟨cb, cr⟩
    obtain ⟨⟨payload', found, same⟩, agreesRest⟩ := agrees
    have headQ := mkHeadQ found qr
    have binder : Refines a (⟨payload', q'⟩ :: Γ') (⟨payload, q⟩ :: Γ) := .cons ⟨same, headQ⟩ r
    obtain ⟨tree, _, pb, rb⟩ := ihB.1.2 cb _ binder result' agreement (path ++ [index])
    obtain ⟨trees, pr, rr⟩ := ihR.1 cr Γ' r row' agreesRest q' (armRefines_tail qr) result' agreement path (index + 1)
    refine ⟨tree :: trees, by simp [prepareArms, found, pb, pr, bind, Except.bind, pure, Except.pure], ?_⟩
    exact stepHead r found same headQ rb rr
  · cases hEq
    obtain ⟨⟨payload', found, same⟩, agreesRest⟩ := agrees
    have headQ := mkHeadQ found qr
    have binder : Refines a (⟨payload', q'⟩ :: Γ') (⟨payload, q⟩ :: Γ) := .cons ⟨same, headQ⟩ r
    obtain ⟨firstTree, first, pf, firstSame, rf⟩ := ihB.1.1 sb _ binder (path ++ [0])
    refine ⟨payload', firstTree, first, found, pf, firstSame, ?_⟩
    intro result' agreement
    obtain ⟨trees, pr, rr⟩ := ihR.1 cr Γ' r row' agreesRest q' (armRefines_tail qr) result' agreement path 1
    refine ⟨trees, pr, ?_⟩
    exact stepHead r found same headQ
      (fun annotations rel => (rf annotations rel).2 result' (sameType_trans firstSame agreement)) rr

theorem armsShareable_of_unrestricted (sc : ShareableComplete a = true) {Γ : Context} {row' : Ty} :
    ∀ {arms : List (String × Term)} {row result : Ty} {uses : Uses},
      ArmsTyping a Γ .unrestricted arms row result uses → MembersAgree a row' row → labelsDistinct arms = true →
      armsShareable a row' arms = true
  | [], _, _, _, .nil _ _ _, _, _ => rfl
  | (name, body) :: rest, _, _, _, .cons (payload := payload) _ _ share _ restTyped _, agrees, distinct => by
    obtain ⟨⟨payload', found, same⟩, agreesRest⟩ := agrees
    simp only [labelsDistinct, Bool.and_eq_true] at distinct
    have tail := armsShareable_of_unrestricted sc restTyped agreesRest distinct.2
    simp only [validContext, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at share
    simp only [armsShareable, List.all_cons, found, Bool.and_eq_true] at tail ⊢
    refine ⟨?_, tail⟩
    rw [shareable_congr sc same]; simpa using share.1

theorem linear_of_armsCustody (sc : ShareableComplete a = true) {Γ : Context} {row' : Ty} :
    ∀ {q : Quantity} {arms : List (String × Term)} {row result : Ty} {uses : Uses},
      ArmsTyping a Γ q arms row result uses → MembersAgree a row' row →
      armsCustody row' arms = true → q = .linear
  | _, [], _, _, _, .nil .., _, h => by simp [armsCustody] at h
  | _, (name, body) :: rest, _, _, _, .cons (payload := payload) _ _ share _ restTyped _, agrees, h => by
    obtain ⟨⟨payload', found, same⟩, agreesRest⟩ := agrees
    simp only [armsCustody, List.any_cons, found, Bool.or_eq_true] at h
    rcases h with hhead | htail
    · have hcust : payload.bearsCustody = true := by
        rw [← bearsCustody_congr sc same]; exact hhead
      exact validContext_custody_linear share List.mem_cons_self hcust
    · exact linear_of_armsCustody sc restTyped agreesRest htail

theorem caseQuantity_refines (sc : ShareableComplete a = true) {Γ Γ' : Context} (r : Refines a Γ' Γ) {q : Quantity}
    {su : Uses} (allowed : caseAllowed a q Γ su = true) {arms : List (String × Term)} {row result row' : Ty}
    {uses : Uses} (typed : ArmsTyping a Γ q arms row result uses) (agrees : MembersAgree a row' row)
    (distinct : labelsDistinct arms = true) :
    ArmRefines a (caseQuantity a Γ' su (armsShareable a row' arms) (armsCustody row' arms)) q row' arms := by
  simp only [caseAllowed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at allowed
  unfold caseQuantity
  by_cases hc : (armsCustody row' arms || !linearFree Γ' su) = true
  · simp only [hc, ↓reduceIte]
    rcases Bool.or_eq_true_iff.mp hc with hcust | hnotFree
    · exact .inl (linear_of_armsCustody sc typed agrees hcust).symm
    · rcases allowed.1 with isL | free
      · exact .inl isL.symm
      · exact absurd (linearFree_refines r free) (by simpa using hnotFree)
  · by_cases hr : (reusableCaptures a.shareableVariables Γ' su && armsShareable a row' arms) = true
    · simp only [hc, hr, Bool.false_eq_true, ↓reduceIte]
      exact .inr (.inr ⟨rfl, (Bool.and_eq_true_iff.mp hr).2⟩)
    · simp only [hc, hr, Bool.false_eq_true, ↓reduceIte]
      have hnoCust : armsCustody row' arms = false := by
        cases h : armsCustody row' arms with
        | false => rfl
        | true => simp [h] at hc
      refine .inr (.inl ⟨rfl, hnoCust, fun isU => hr ?_⟩)
      subst isU
      have captures := allowed.2.resolve_left (by simp)
      rw [Bool.and_eq_true]
      exact ⟨reusableCaptures_refines sc r captures, armsShareable_of_unrestricted sc typed agrees distinct⟩

theorem motive_case (sc : ShareableComplete a = true) {Γ : Context} {scrutinee : Term} {arms : List (String × Term)}
    {row result : Ty} {su au : Uses} {q : Quantity}
    (scrutineeTyped : PartialTyping a Γ scrutinee (.variant row) su) (typed : ArmsTyping a Γ q arms row result au)
    (distinct : labelsDistinct arms = true) (allowed : caseAllowed a q Γ su = true)
    (ihS : Motive a Γ scrutinee (.variant row) su) (ihA : ArmsMotive a Γ q arms row result au) :
    Motive a Γ (.case scrutinee arms) result (addUses su au) := by
  have checkCase : Synthable scrutinee → FieldsCheckable arms →
      ∀ Γ', Refines a Γ' Γ → ∀ expected, sameType a result expected = true →
        CheckOK a Γ' (.case scrutinee arms) expected (addUses su au) := by
    intro ss fa Γ' r expected agreement path
    obtain ⟨st, sT, sp, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
    obtain ⟨rawRow, hSWhnf, hrow⟩ := whnf_variant_inv sSame
    have suOcc : su = occurrences Γ'.length scrutinee := by
      rw [refines_length r]; exact uses_determined scrutineeTyped
    let expectedHead := whnf a expected
    have expHeadAgrees : sameType a result expectedHead = true :=
      sameType_trans agreement (sameType_whnf a expected)
    cases arms with
    | nil =>
      cases typed with | nil =>
      have ma : MembersAgree a .emptyRow .emptyRow := trivial
      let q' := caseQuantity a Γ' (occurrences Γ'.length scrutinee) true
      have hqr : ArmRefines a q' q .emptyRow [] := by
        dsimp only [q']
        rw [← suOcc]
        exact caseQuantity_refines sc r allowed (.nil Γ q result) ma distinct
      obtain ⟨trees, pa, ra⟩ := ihA.1 fa Γ' r .emptyRow ma q' hqr expectedHead expHeadAgrees (path ++ [1]) 0
      simp [prepareArms, pure, Except.pure] at pa; subst pa
      let ann : LambdaAnnotation := ⟨.variant .emptyRow, expectedHead, q', .reusable⟩
      refine ⟨.node (some ann) [st, .node none []], expected, ?_, ?_⟩
      · simp [prepare, sp, hSWhnf, caseRow, expectedHead, Obend.Elab.Prepare.armResult,
          q', ann, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
        have hScrutSame : sameType a sT (.variant .emptyRow) = true :=
          sameType_trans (sameType_whnf a sT) (by rw [hSWhnf]; exact sameType_variant hrow)
        obtain ⟨v, ok, vUses⟩ := yields_elim ((sRun annotations (realizes_child realizes 0 st rfl)).2 (.variant .emptyRow) hScrutSame)
        obtain ⟨ta, okA, uA, rowA, qA⟩ := yields_elim (ra annotations armsForest)
        simp only [checkAt] at ok
        have hHead : representativeHead a annotations path (.variant .emptyRow) = .variant .emptyRow := by
          simp [representativeHead, root]
        have agreesScrutinee : sameType a (.variant .emptyRow) (.variant ta.row) = true :=
          sameType_variant (sameType_symm (rowAgrees_sameType rowA))
        have hQAt : caseQuantityAt a annotations path Γ' su .emptyRow [] = q' := by
          simp [caseQuantityAt, root, ann]
        have allowed' : caseAllowed a ta.quantity Γ' su = true := by
          rw [qA, suOcc]; exact caseQuantity_allowed _ _ _ _
        have finishSame : sameType a expectedHead expected = true := whnf_sameType a expected
        change Yields (elaborate a annotations Γ' path (.case scrutinee []) (.check expected)) _
        rw [elaborate]
        simp [root, ann, ok, Except.map, checkedSynth, hHead, hQAt, okA, vUses, uA,
          need_ok allowed', need_ok agreesScrutinee, finish, finishSame,
          bind, Except.bind, pure, Except.pure, Yields]
    | cons arm rest =>
      obtain ⟨name, body⟩ := arm
      obtain ⟨row', foundRow, rowAgrees⟩ := lookupRow_arms_agrees typed distinct rawRow
        (fun nm member _ fnd => lookupV_transport hrow fnd)
      have ma : MembersAgree a row' row := membersAgree_of_rowAgrees typed distinct rowAgrees
      let q' := caseQuantity a Γ' (occurrences Γ'.length scrutinee)
        (armsShareable a row' ((name, body) :: rest)) (armsCustody row' ((name, body) :: rest))
      have hqr : ArmRefines a q' q row' ((name, body) :: rest) := by
        dsimp only [q']
        rw [← suOcc]
        exact caseQuantity_refines sc r allowed typed ma distinct
      obtain ⟨trees, pa, ra⟩ := ihA.1 fa Γ' r row' ma q' hqr expectedHead expHeadAgrees (path ++ [1]) 0
      let ann : LambdaAnnotation := ⟨.variant row', expectedHead, q', .reusable⟩
      refine ⟨.node (some ann) [st, .node none trees], expected, ?_, ?_⟩
      · simp [prepare, sp, hSWhnf, caseRow, foundRow, q', expectedHead, Obend.Elab.Prepare.armResult,
          pa, ann, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
        have hScrutSame : sameType a sT (.variant row') = true :=
          sameType_trans (sameType_whnf a sT)
            (by rw [hSWhnf]; exact sameType_variant (sameType_trans hrow (sameType_symm (rowAgrees_sameType rowAgrees))))
        obtain ⟨v, ok, vUses⟩ := yields_elim ((sRun annotations (realizes_child realizes 0 st rfl)).2 (.variant row') hScrutSame)
        obtain ⟨ta, okA, uA, rowA, qA⟩ := yields_elim (ra annotations armsForest)
        simp only [checkAt] at ok
        have hHead : representativeHead a annotations path (.variant row') = .variant row' := by
          simp [representativeHead, root]
        have agreesScrutinee : sameType a (.variant row') (.variant ta.row) = true :=
          sameType_variant (sameType_trans (rowAgrees_sameType rowAgrees) (sameType_symm (rowAgrees_sameType rowA)))
        have hQAt : caseQuantityAt a annotations path Γ' su row' ((name, body) :: rest) = q' := by
          simp [caseQuantityAt, root, ann]
        have allowed' : caseAllowed a ta.quantity Γ' su = true := by
          rw [qA, suOcc]; exact caseQuantity_allowed _ _ _ _ _
        have finishSame : sameType a expectedHead expected = true := whnf_sameType a expected
        change Yields (elaborate a annotations Γ' path (.case scrutinee ((name, body) :: rest)) (.check expected)) _
        rw [elaborate]
        simp [root, ann, ok, Except.map, checkedSynth, need_ok distinct, hHead, hQAt, okA, vUses, uA,
          need_ok allowed', need_ok agreesScrutinee, finish, finishSame,
          bind, Except.bind, pure, Except.pure, Yields]
  have synthCase : ∀ name body rest, arms = (name, body) :: rest →
      Synthable scrutinee → Synthable body → FieldsCheckable rest →
      ∀ Γ', Refines a Γ' Γ →
        SynthOK a Γ' (.case scrutinee ((name, body) :: rest)) result (addUses su au) := by
    intro name body rest hArms ss sb fr Γ' r path
    subst hArms
    obtain ⟨st, sT, sp, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
    obtain ⟨rawRow, hSWhnf, hrow⟩ := whnf_variant_inv sSame
    obtain ⟨row', foundRow, rowAgrees⟩ := lookupRow_arms_agrees typed distinct rawRow
      (fun nm member _ fnd => lookupV_transport hrow fnd)
    have ma : MembersAgree a row' row := membersAgree_of_rowAgrees typed distinct rowAgrees
    have suOcc : su = occurrences Γ'.length scrutinee := by
      rw [refines_length r]; exact uses_determined scrutineeTyped
    let q' := caseQuantity a Γ' (occurrences Γ'.length scrutinee)
      (armsShareable a row' ((name, body) :: rest)) (armsCustody row' ((name, body) :: rest))
    have hqr : ArmRefines a q' q row' ((name, body) :: rest) := by
      dsimp only [q']
      rw [← suOcc]
      exact caseQuantity_refines sc r allowed typed ma distinct
    obtain ⟨payload', firstTree, first, foundMem, pf, firstSame, restArm⟩ :=
      ihA.2 name body rest rfl sb fr Γ' r row' ma q' hqr (path ++ [1])
    let firstHead := whnf a first
    have hResFirst : sameType a result firstHead = true :=
      sameType_trans (sameType_symm firstSame) (sameType_whnf a first)
    obtain ⟨trees, pr, ra⟩ := restArm firstHead hResFirst
    let ann : LambdaAnnotation := ⟨.variant row', firstHead, q', .reusable⟩
    have pf' : prepare a noHints (⟨payload', q'⟩ :: Γ') (path ++ [1, 0]) body .synth = .ok (firstTree, first) := by
      simpa using pf
    refine ⟨.node (some ann) [st, .node none (firstTree :: trees)], firstHead, ?_,
      sameType_trans (whnf_sameType a first) firstSame, ?_⟩
    · simp [prepare, sp, hSWhnf, caseRow, foundRow, q', foundMem, pf', firstHead,
        Obend.Elab.Prepare.armResult, pr, ann, bind, Except.bind, pure, Except.pure]
    · intro annotations realizes
      have root := realizes_root realizes
      have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
      have hScrutSame : sameType a sT (.variant row') = true :=
        sameType_trans (sameType_whnf a sT)
          (by rw [hSWhnf]; exact sameType_variant (sameType_trans hrow (sameType_symm (rowAgrees_sameType rowAgrees))))
      obtain ⟨v, ok, vUses⟩ := yields_elim ((sRun annotations (realizes_child realizes 0 st rfl)).2 (.variant row') hScrutSame)
      obtain ⟨ta, okA, uA, rowA, qA⟩ := yields_elim (ra annotations armsForest)
      simp only [checkAt] at ok
      have hHead : representativeHead a annotations path (.variant row') = .variant row' := by
        simp [representativeHead, root]
      have agreesScrutinee : sameType a (.variant row') (.variant ta.row) = true :=
        sameType_variant (sameType_trans (rowAgrees_sameType rowAgrees) (sameType_symm (rowAgrees_sameType rowA)))
      have hQAt : caseQuantityAt a annotations path Γ' su row' ((name, body) :: rest) = q' := by
        simp [caseQuantityAt, root, ann]
      have allowed' : caseAllowed a ta.quantity Γ' su = true := by
        rw [qA, suOcc]; exact caseQuantity_allowed _ _ _ _ _
      constructor
      · change Yields (elaborate a annotations Γ' path (.case scrutinee ((name, body) :: rest)) .synth) _
        rw [elaborate]
        simp [root, ann, ok, Except.map, checkedSynth, need_ok distinct, hHead, hQAt, okA, vUses, uA,
          need_ok allowed', need_ok agreesScrutinee, bind, Except.bind, pure, Except.pure, Yields]
      · intro expected agreement
        change Yields (elaborate a annotations Γ' path (.case scrutinee ((name, body) :: rest)) (.check expected)) _
        rw [elaborate]
        simp [root, ann, ok, Except.map, checkedSynth, need_ok distinct, hHead, hQAt, okA, vUses, uA,
          need_ok allowed', need_ok agreesScrutinee, finish, agreement,
          bind, Except.bind, pure, Except.pure, Yields]
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | caseCons ss sb fr => exact synthCase _ _ _ rfl ss sb fr Γ' r
  · cases c with
    | synth s =>
      cases s with
      | caseCons ss sb fr => exact checkCase ss (.cons (.synth sb) fr) Γ' r expected agreement
    | case ss fa => exact checkCase ss fa Γ' r expected agreement

theorem motive_effectCase (sc : ShareableComplete a = true) {Γ : Context} {scrutinee : Term} {arms : List (String × Term)}
    {planType response row result : Ty} {su au : Uses} {q : Quantity}
    (scrutineeTyped : PartialTyping a Γ scrutinee (.computation planType response (.variant row)) su)
    (typed : ArmsTyping a Γ q arms row (.computation planType response result) au)
    (nonComputation : result.isComputation = false) (distinct : labelsDistinct arms = true)
    (allowed : caseAllowed a q Γ su = true)
    (ihS : Motive a Γ scrutinee (.computation planType response (.variant row)) su)
    (ihA : ArmsMotive a Γ q arms row (.computation planType response result) au) :
    Motive a Γ (.case scrutinee arms) (.computation planType response result) (addUses su au) := by
  have checkCase : Synthable scrutinee → FieldsCheckable arms →
      ∀ Γ', Refines a Γ' Γ → ∀ expected, sameType a (.computation planType response result) expected = true →
        CheckOK a Γ' (.case scrutinee arms) expected (addUses su au) := by
    intro ss fa Γ' r expected agreement path
    obtain ⟨st, sT, sp, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
    obtain ⟨p1, r1, v1, hSWhnf, hp1, hr1, hv1⟩ := whnf_computation_inv sSame
    obtain ⟨rawRow, hVWhnf, hrow⟩ := whnf_variant_inv hv1
    obtain ⟨p2, r2, x2, hExpWhnf, hp2, hr2, hx2⟩ := whnf_computation_inv (sameType_symm agreement)
    have suOcc : su = occurrences Γ'.length scrutinee := by
      rw [refines_length r]; exact uses_determined scrutineeTyped
    let expectedHead := Ty.computation p2 r2 x2
    have resultAgrees : sameType a (.computation planType response result) (.computation p1 r1 x2) = true :=
      sameType_computation (sameType_symm hp1) (sameType_symm hr1) (sameType_symm hx2)
    have nonActivity : (!x2.isComputation) = true := by
      rw [sameType_isComputation hx2, nonComputation]; rfl
    have agreesExpHead : sameType a (.computation p1 r1 x2) expectedHead = true :=
      sameType_computation (sameType_trans hp1 (sameType_symm hp2))
        (sameType_trans hr1 (sameType_symm hr2)) (sameType_refl a x2)
    have finishSame : sameType a expectedHead expected = true := by
      simpa [expectedHead, hExpWhnf] using whnf_sameType a expected
    cases arms with
    | nil =>
      cases typed with | nil =>
      have ma : MembersAgree a .emptyRow .emptyRow := trivial
      let q' := caseQuantity a Γ' (occurrences Γ'.length scrutinee) true
      have hqr : ArmRefines a q' q .emptyRow [] := by
        dsimp only [q']
        rw [← suOcc]
        exact caseQuantity_refines sc r allowed (.nil Γ q (.computation planType response result)) ma distinct
      obtain ⟨trees, pa, ra⟩ := ihA.1 fa Γ' r .emptyRow ma q' hqr
        (.computation p1 r1 x2) resultAgrees (path ++ [1]) 0
      simp [prepareArms, pure, Except.pure] at pa; subst pa
      let scrutRep := Ty.computation p1 r1 (.variant .emptyRow)
      let ann : LambdaAnnotation := ⟨scrutRep, expectedHead, q', .reusable⟩
      refine ⟨.node (some ann) [st, .node none []], expected, ?_, ?_⟩
      · simp [prepare, sp, hSWhnf, caseRow, hVWhnf, hExpWhnf, expectedHead, scrutRep,
          Obend.Elab.Prepare.armResult, q', ann, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
        have hScrutSame : sameType a sT scrutRep = true := by
          refine sameType_trans (sameType_whnf a sT) ?_
          rw [hSWhnf]
          exact sameType_computation (sameType_refl a p1) (sameType_refl a r1)
            (sameType_trans (sameType_whnf a v1) (by rw [hVWhnf]; exact sameType_variant hrow))
        obtain ⟨v, ok, vUses⟩ := yields_elim ((sRun annotations (realizes_child realizes 0 st rfl)).2 scrutRep hScrutSame)
        obtain ⟨ta, okA, uA, rowA, qA⟩ := yields_elim (ra annotations armsForest)
        simp only [checkAt] at ok
        have hHead : representativeHead a annotations path scrutRep = scrutRep := by
          simp [representativeHead, root]
        have hExpRep : representativeHead a annotations path expectedHead = expectedHead := by
          simp [representativeHead, root]
        have agreesScrutinee : sameType a scrutRep (.computation p1 r1 (.variant ta.row)) = true :=
          sameType_computation (sameType_refl a p1) (sameType_refl a r1)
            (sameType_variant (sameType_symm (rowAgrees_sameType rowA)))
        have hQAt : caseQuantityAt a annotations path Γ' su .emptyRow [] = q' := by
          simp [caseQuantityAt, root, ann]
        have allowed' : caseAllowed a ta.quantity Γ' su = true := by
          rw [qA, suOcc]; exact caseQuantity_allowed _ _ _ _
        change Yields (elaborate a annotations Γ' path (.case scrutinee []) (.check expected)) _
        rw [elaborate]
        simp [root, ann, scrutRep, expectedHead, ok, Except.map, checkedSynth, hHead, hExpRep,
          hQAt, okA, vUses, uA, need_ok allowed', need_ok agreesScrutinee, need_ok nonActivity,
          need_ok agreesExpHead, finish, finishSame, bind, Except.bind, pure, Except.pure, Yields]
    | cons arm rest =>
      obtain ⟨name, body⟩ := arm
      obtain ⟨row', foundRow, rowAgrees⟩ := lookupRow_arms_agrees typed distinct rawRow
        (fun nm member _ fnd => lookupV_transport hrow fnd)
      have ma : MembersAgree a row' row := membersAgree_of_rowAgrees typed distinct rowAgrees
      let q' := caseQuantity a Γ' (occurrences Γ'.length scrutinee)
        (armsShareable a row' ((name, body) :: rest)) (armsCustody row' ((name, body) :: rest))
      have hqr : ArmRefines a q' q row' ((name, body) :: rest) := by
        dsimp only [q']
        rw [← suOcc]
        exact caseQuantity_refines sc r allowed typed ma distinct
      obtain ⟨trees, pa, ra⟩ := ihA.1 fa Γ' r row' ma q' hqr
        (.computation p1 r1 x2) resultAgrees (path ++ [1]) 0
      let scrutRep := Ty.computation p1 r1 (.variant row')
      let ann : LambdaAnnotation := ⟨scrutRep, expectedHead, q', .reusable⟩
      refine ⟨.node (some ann) [st, .node none trees], expected, ?_, ?_⟩
      · simp [prepare, sp, hSWhnf, caseRow, hVWhnf, foundRow, q', hExpWhnf, expectedHead, scrutRep,
          Obend.Elab.Prepare.armResult, pa, ann, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
        have hScrutSame : sameType a sT scrutRep = true := by
          refine sameType_trans (sameType_whnf a sT) ?_
          rw [hSWhnf]
          exact sameType_computation (sameType_refl a p1) (sameType_refl a r1)
            (sameType_trans (sameType_whnf a v1)
              (by rw [hVWhnf]; exact sameType_variant (sameType_trans hrow (sameType_symm (rowAgrees_sameType rowAgrees)))))
        obtain ⟨v, ok, vUses⟩ := yields_elim ((sRun annotations (realizes_child realizes 0 st rfl)).2 scrutRep hScrutSame)
        obtain ⟨ta, okA, uA, rowA, qA⟩ := yields_elim (ra annotations armsForest)
        simp only [checkAt] at ok
        have hHead : representativeHead a annotations path scrutRep = scrutRep := by
          simp [representativeHead, root]
        have hExpRep : representativeHead a annotations path expectedHead = expectedHead := by
          simp [representativeHead, root]
        have agreesScrutinee : sameType a scrutRep (.computation p1 r1 (.variant ta.row)) = true :=
          sameType_computation (sameType_refl a p1) (sameType_refl a r1)
            (sameType_variant (sameType_trans (rowAgrees_sameType rowAgrees) (sameType_symm (rowAgrees_sameType rowA))))
        have hQAt : caseQuantityAt a annotations path Γ' su row' ((name, body) :: rest) = q' := by
          simp [caseQuantityAt, root, ann]
        have allowed' : caseAllowed a ta.quantity Γ' su = true := by
          rw [qA, suOcc]; exact caseQuantity_allowed _ _ _ _ _
        change Yields (elaborate a annotations Γ' path (.case scrutinee ((name, body) :: rest)) (.check expected)) _
        rw [elaborate]
        simp [root, ann, scrutRep, expectedHead, ok, Except.map, checkedSynth, need_ok distinct,
          hHead, hExpRep, hQAt, okA, vUses, uA, need_ok allowed', need_ok agreesScrutinee, need_ok nonActivity,
          need_ok agreesExpHead, finish, finishSame, bind, Except.bind, pure, Except.pure, Yields]
  have synthCase : ∀ name body rest, arms = (name, body) :: rest →
      Synthable scrutinee → Synthable body → FieldsCheckable rest →
      ∀ Γ', Refines a Γ' Γ →
        SynthOK a Γ' (.case scrutinee ((name, body) :: rest)) (.computation planType response result) (addUses su au) := by
    intro name body rest hArms ss sb fr Γ' r path
    subst hArms
    obtain ⟨st, sT, sp, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
    obtain ⟨p1, r1, v1, hSWhnf, hp1, hr1, hv1⟩ := whnf_computation_inv sSame
    obtain ⟨rawRow, hVWhnf, hrow⟩ := whnf_variant_inv hv1
    obtain ⟨row', foundRow, rowAgrees⟩ := lookupRow_arms_agrees typed distinct rawRow
      (fun nm member _ fnd => lookupV_transport hrow fnd)
    have ma : MembersAgree a row' row := membersAgree_of_rowAgrees typed distinct rowAgrees
    have suOcc : su = occurrences Γ'.length scrutinee := by
      rw [refines_length r]; exact uses_determined scrutineeTyped
    let q' := caseQuantity a Γ' (occurrences Γ'.length scrutinee)
      (armsShareable a row' ((name, body) :: rest)) (armsCustody row' ((name, body) :: rest))
    have hqr : ArmRefines a q' q row' ((name, body) :: rest) := by
      dsimp only [q']
      rw [← suOcc]
      exact caseQuantity_refines sc r allowed typed ma distinct
    obtain ⟨payload', firstTree, first, foundMem, pf, firstSame, restArm⟩ :=
      ihA.2 name body rest rfl sb fr Γ' r row' ma q' hqr (path ++ [1])
    obtain ⟨p2, r2, x2, hFirstWhnf, hp2, hr2, hx2⟩ := whnf_computation_inv firstSame
    let firstHead := Ty.computation p2 r2 x2
    have hArmTarget : sameType a (.computation planType response result) (.computation p1 r1 x2) = true :=
      sameType_computation (sameType_symm hp1) (sameType_symm hr1) (sameType_symm hx2)
    obtain ⟨trees, pr, ra⟩ := restArm (.computation p1 r1 x2) hArmTarget
    let scrutRep := Ty.computation p1 r1 (.variant row')
    let ann : LambdaAnnotation := ⟨scrutRep, firstHead, q', .reusable⟩
    have pf' : prepare a noHints (⟨payload', q'⟩ :: Γ') (path ++ [1, 0]) body .synth = .ok (firstTree, first) := by
      simpa using pf
    have hPredDeriv : sameType a firstHead (.computation planType response result) = true :=
      sameType_computation hp2 hr2 hx2
    refine ⟨.node (some ann) [st, .node none (firstTree :: trees)], firstHead, ?_, hPredDeriv, ?_⟩
    · simp [prepare, sp, hSWhnf, caseRow, hVWhnf, foundRow, q', foundMem, pf', hFirstWhnf, firstHead, scrutRep,
        Obend.Elab.Prepare.armResult, pr, ann, bind, Except.bind, pure, Except.pure]
    · intro annotations realizes
      have root := realizes_root realizes
      have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
      have hScrutSame : sameType a sT scrutRep = true := by
        refine sameType_trans (sameType_whnf a sT) ?_
        rw [hSWhnf]
        exact sameType_computation (sameType_refl a p1) (sameType_refl a r1)
          (sameType_trans (sameType_whnf a v1)
            (by rw [hVWhnf]; exact sameType_variant (sameType_trans hrow (sameType_symm (rowAgrees_sameType rowAgrees)))))
      obtain ⟨v, ok, vUses⟩ := yields_elim ((sRun annotations (realizes_child realizes 0 st rfl)).2 scrutRep hScrutSame)
      obtain ⟨ta, okA, uA, rowA, qA⟩ := yields_elim (ra annotations armsForest)
      simp only [checkAt] at ok
      have hHead : representativeHead a annotations path scrutRep = scrutRep := by
        simp [representativeHead, root]
      have hFirstRep : representativeHead a annotations path firstHead = firstHead := by
        simp [representativeHead, root]
      have agreesScrutinee : sameType a scrutRep (.computation p1 r1 (.variant ta.row)) = true :=
        sameType_computation (sameType_refl a p1) (sameType_refl a r1)
          (sameType_variant (sameType_trans (rowAgrees_sameType rowAgrees) (sameType_symm (rowAgrees_sameType rowA))))
      have nonActivity : (!x2.isComputation) = true := by
        rw [sameType_isComputation hx2, nonComputation]; rfl
      have agreesFirstHead : sameType a (.computation p1 r1 x2) firstHead = true :=
        sameType_computation (sameType_trans hp1 (sameType_symm hp2))
          (sameType_trans hr1 (sameType_symm hr2)) (sameType_refl a x2)
      have hQAt : caseQuantityAt a annotations path Γ' su row' ((name, body) :: rest) = q' := by
        simp [caseQuantityAt, root, ann]
      have allowed' : caseAllowed a ta.quantity Γ' su = true := by
        rw [qA, suOcc]; exact caseQuantity_allowed _ _ _ _ _
      constructor
      · change Yields (elaborate a annotations Γ' path (.case scrutinee ((name, body) :: rest)) .synth) _
        rw [elaborate]
        simp [root, ann, scrutRep, firstHead, ok, Except.map, checkedSynth, need_ok distinct,
          hHead, hFirstRep, hQAt, okA, vUses, uA, need_ok allowed', need_ok agreesScrutinee, need_ok nonActivity,
          need_ok agreesFirstHead, bind, Except.bind, pure, Except.pure, Yields]
      · intro expected agreement
        change Yields (elaborate a annotations Γ' path (.case scrutinee ((name, body) :: rest)) (.check expected)) _
        rw [elaborate]
        simp [root, ann, scrutRep, firstHead, ok, Except.map, checkedSynth, need_ok distinct,
          hHead, hFirstRep, hQAt, okA, vUses, uA, need_ok allowed', need_ok agreesScrutinee, need_ok nonActivity,
          need_ok agreesFirstHead, finish, agreement, bind, Except.bind, pure, Except.pure, Yields]
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | caseCons ss sb fr => exact synthCase _ _ _ rfl ss sb fr Γ' r
  · cases c with
    | synth s =>
      cases s with
      | caseCons ss sb fr => exact checkCase ss (.cons (.synth sb) fr) Γ' r expected agreement
    | case ss fa => exact checkCase ss fa Γ' r expected agreement

/-! ## 6. The Induction & `prepare_checks` Over Non-Empty `Assumptions` -/

theorem motive_outside {Γ : Context} {t : Term} {derived : Ty} {uses : Uses}
    (notSynth : Synthable t → False) (notCheck : Checkable t → False) (notLam : ∀ body, t ≠ .lam body) :
    Motive a Γ t derived uses :=
  ⟨⟨fun s => (notSynth s).elim, fun c => (notCheck c).elim⟩, fun body h => (notLam body h).elim⟩

/-- Every derivation of a term under `ShareableComplete` assumptions carries the fragment's guarantees. -/
public theorem motive_of_typing (sc : ShareableComplete a = true) {Γ : Context} {t : Term} {derived : Ty} {uses : Uses}
    (typed : PartialTyping a Γ t derived uses) : Motive a Γ t derived uses := by
  refine PartialTyping.rec
    (motive_1 := fun Γ t derived uses _ => Motive a Γ t derived uses)
    (motive_2 := fun Γ fields row uses _ => FieldsMotive a Γ fields row uses)
    (motive_3 := fun Γ q arms row result uses _ => ArmsMotive a Γ q arms row result uses)
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend ?specification
    ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject ?case ?ifBool ?perform ?done
    ?effectCase ?split ?hole ?fieldsNil ?fieldsCons ?armsNil ?armsCons typed
  case bound => intro Γ index binding found; exact motive_bound found
  case natural => intro Γ value; exact motive_natural Γ value
  case boolean => intro Γ value; exact motive_boolean Γ value
  case label => intro Γ value; exact motive_label Γ value
  case lambda =>
    intro Γ body annotation bodyUses _ safe valid captures fits ih
    exact motive_lambda sc safe valid captures fits ih
  case conversion =>
    intro Γ term actual expected uses _ agreement ih
    exact motive_conversion ih agreement
  case application =>
    intro Γ function argument functionType argumentType domain codomain fu au reuse quantity
      _ argumentTyped shape argumentEq allowed ihF ihA
    subst argumentType
    exact motive_application sc shape allowed ihF ihA (uses_determined argumentTyped)
  case record =>
    intro Γ fields row uses fieldsTyped _ ih
    exact motive_record fieldsTyped ih
  case get =>
    intro Γ target targetType member uses name fuel _ found free ih
    exact motive_get found free ih
  case extend =>
    intro Γ target fields targetType row tu fu fuel _ _ distinct isRow free ihT ihF
    exact motive_extend distinct isRow free ihT ihF
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu
      _ _ lowerShape upperShape captures shareSelf shareInherited shareMiddle ihL ihU
    exact motive_mix sc lowerShape upperShape captures shareSelf shareInherited shareMiddle ihL ihU
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu
      _ shape _ shareTarget allowed captures ihS ihI
    exact motive_fix sc shape shareTarget allowed captures ihS ihI
  case binary =>
    intro Γ primitive left right input output lu ru shape _ _ ihL ihR
    exact motive_binary shape ihL ihR
  case inject =>
    intro Γ tag payload payloadType row uses fuel _ found nonComputation ih
    exact motive_inject found nonComputation ih
  case case =>
    intro Γ scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihS ihA
    exact motive_case sc scrutineeTyped armsTyped distinct allowed ihS ihA
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu _ _ _ agreeing ihC ihT ihF
    exact motive_ifBool ihC ihT ihF agreeing
  case effectCase =>
    intro Γ scrutinee arms plan response row result su au q scrutineeTyped armsTyped nonComputation distinct allowed ihS ihA
    exact motive_effectCase sc scrutineeTyped armsTyped nonComputation distinct allowed ihS ihA
  case fieldsNil => intro Γ; exact fieldsMotive_nil Γ
  case fieldsCons =>
    intro Γ name body rest type row bu ru _ _ nonComputation ihB ihR
    exact fieldsMotive_cons nonComputation ihB ihR
  case armsNil => intro Γ q result; exact armsMotive_nil Γ q result
  case armsCons =>
    intro Γ q name body rest payload row result bu ru _ safe share fits _ agreeing ihB ihR
    exact armsMotive_cons sc safe share fits agreeing ihB ihR
  all_goals intros
  all_goals refine motive_outside (fun h => ?_) (fun h => ?_) (fun _ h => ?_)
  all_goals cases h
  all_goals (rename_i s; cases s)

theorem treeAnnotations_realizes' (tree : AnnotationTree) : Realizes (treeAnnotations tree) [] tree :=
  fun _ => rfl

/-- **Preparation is complete on the expanded fragment (`Checkable`) over `ShareableComplete`
assumptions (including non-empty equi-recursive alias bounds).** Every certified erased term in
`Checkable` (covering `.extend`, `.mix`, `.fix`, and `.case` / `.effectCase`) is prepared and
accepted by `checkAgainst` at its type with the derivation's exact usage vector. -/
public theorem prepare_checks {source : AnnotatedTerm} {context : Context}
    (shareableComplete : ShareableComplete source.assumptions = true)
    (fragment : Checkable source.term)
    (certificate : Checked source context) :
    ∃ annotations checked,
      prepareAnnotations { source with annotations := noHints } context certificate.type = .ok annotations ∧
      checkAgainst { source with annotations := annotations } context certificate.type = .ok checked ∧
      checked.uses = certificate.uses := by
  have m := motive_of_typing shareableComplete (show PartialTyping _ _ source.term _ _ from certificate.derivation)
  obtain ⟨tree, _, prepared, run⟩ :=
    m.1.2 fragment context (refines_refl context) certificate.type (sameType_refl _ _) []
  obtain ⟨result, accepted, sameUses⟩ := yields_elim (run (treeAnnotations tree) (treeAnnotations_realizes' tree))
  have safe : safeUses context result.uses = true := by rw [sameUses]; exact certificate.safe
  refine ⟨treeAnnotations tree, ⟨certificate.type, result.uses, result.derivation, safe,
    certificate.contextValid, certificate.assumptionsValid⟩, ?_, ?_, sameUses⟩
  · simp [prepareAnnotations, prepared, bind, Except.bind, pure, Except.pure]
  · simp only [checkAt] at accepted
    simp [checkAgainst, checkAt, accepted, bind, Except.bind, need_ok safe, need_ok certificate.contextValid,
      need_ok certificate.assumptionsValid, pure, Except.pure]

/-- The gate's own form: `prepareChecked` accepts every certified erased term of the fragment. -/
public theorem prepareChecked_complete {source : AnnotatedTerm} {context : Context}
    (shareableComplete : ShareableComplete source.assumptions = true)
    (fragment : Checkable source.term)
    (certificate : Checked source context) :
    (prepareChecked { source with annotations := noHints } context certificate.type).toBool = true := by
  obtain ⟨annotations, checked, prepared, accepted, _⟩ := prepare_checks shareableComplete fragment certificate
  simp [prepareChecked, prepared, accepted, bind, Except.bind, pure, Except.pure, Except.toBool]

public def annotateExecutable (source : AnnotatedTerm) (context : Context) (type : Ty) : Annotations :=
  match prepareAnnotations { source with annotations := noHints } context type with
  | .ok annotations => annotations
  | .error _ => noHints

public theorem annotateExecutable_checks {source : AnnotatedTerm} {context : Context}
    (shareableComplete : ShareableComplete source.assumptions = true)
    (fragment : Checkable source.term)
    (certificate : Checked source context) :
    ∃ checked, checkAgainst { source with annotations := annotateExecutable source context certificate.type }
      context certificate.type = .ok checked := by
  obtain ⟨annotations, checked, prepared, accepted, _⟩ := prepare_checks shareableComplete fragment certificate
  have same : annotateExecutable source context certificate.type = annotations := by
    simp [annotateExecutable, prepared]
  rw [same]
  exact ⟨checked, accepted⟩

/-! ## 7. Inhabitants Over Empty & Non-Empty Equi-Recursive `Assumptions` -/

public theorem appliedLambda_checkable : Checkable appliedLambda.term :=
  .letIn (.synth (.bound 0)) (.nat 1)

public theorem appliedLambda_prepared :
    (prepareChecked { appliedLambda with annotations := noHints } [] .natural).toBool = true :=
  prepareChecked_complete rfl appliedLambda_checkable appliedLambdaChecked

/-- Equi-recursive `NatList` cons payload `{ head : Nat, tail : α₀ }`. -/
public def natListConsPayload : Ty :=
  .field "head" .natural (.field "tail" (.variable 0) .emptyRow)

/-- Equi-recursive `NatList` sum row `[ cons : { head : Nat, tail : α₀ } | nil : Nat ]`. -/
public def natListRow : Ty :=
  .field "cons" natListConsPayload (.field "nil" .natural .emptyRow)

/-- Non-empty equi-recursive `Assumptions` binding `α₀ ↦ variant natListRow`. -/
public def natListAssumptions : Assumptions :=
  { bounds := [(0, .variant natListRow)], shareableVariables := [0] }

public theorem natListAssumptions_nonempty : natListAssumptions.bounds ≠ [] := by
  simp [natListAssumptions]

public theorem natListAssumptions_valid : natListAssumptions.valid = true := by
  decide

public theorem natListAssumptions_shareableComplete :
    ShareableComplete natListAssumptions = true := by
  apply shareableComplete_of_all_shareable natListAssumptions_valid
  intro p hp
  simp only [natListAssumptions, List.mem_singleton] at hp
  subst hp; rfl

/-- Mixin specification type `Nat → Nat → Nat` used in the non-empty-assumptions witness. -/
public def natMixinTy : Ty :=
  .arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural)

/-- Context `[xs : α₀, m : Nat → Nat → Nat]` over `natListAssumptions`. -/
public def natListProbeContext : Context :=
  [⟨.variable 0, .unrestricted⟩, ⟨natMixinTy, .unrestricted⟩]

/-- Erased term exercising `.case` over equi-recursive alias `α₀`, `.fix`, `.mix`, and `.extend`. -/
public def natListProbe : AnnotatedTerm :=
  { term := .case (.bound 0)
      [ ("cons", .get (.extend (.bound 0) [("extra", .nat 1)]) "head")
      , ("nil", .fix (.mix (.bound 2) (.bound 2)) (.bound 0)) ]
    annotations := noHints
    assumptions := natListAssumptions }

public theorem natListProbe_synthable : Synthable natListProbe.term :=
  .caseCons (.bound 0)
    (.get "head" (.extend (.bound 0) (.cons (.nat 1) .nil)))
    (.cons (.synth (.fix (.mix (.bound 2) (.bound 2)) (.synth (.bound 0)))) .nil)

public theorem natListProbe_checkable : Checkable natListProbe.term :=
  .synth natListProbe_synthable

public def natListProbeChecked : Checked natListProbe natListProbeContext :=
  let cCons : Context := ⟨natListConsPayload, .unrestricted⟩ :: natListProbeContext
  let cNil : Context := ⟨.natural, .unrestricted⟩ :: natListProbeContext
  have hWhnf0 : whnf natListAssumptions (.variable 0) = .variant natListRow := rfl
  have hScrut : PartialTyping natListAssumptions natListProbeContext (.bound 0) (.variant natListRow) [1, 0] :=
    .conversion (.bound (binding := ⟨.variable 0, .unrestricted⟩) rfl)
      (hWhnf0 ▸ sameType_whnf natListAssumptions (.variable 0))
  have hConsExt : PartialTyping natListAssumptions cCons
      (.extend (.bound 0) [("extra", .nat 1)])
      (overlay (.field "extra" .natural .emptyRow) natListConsPayload) [1, 0, 0] :=
    .extend (fuel := 3)
      (.bound (binding := ⟨natListConsPayload, .unrestricted⟩) rfl)
      (.cons (.natural cCons 1) (.nil cCons) rfl)
      (by rfl) (by rfl) (by rfl)
  have hConsBody : PartialTyping natListAssumptions cCons
      (.get (.extend (.bound 0) [("extra", .nat 1)]) "head") .natural [1, 0, 0] :=
    .get (fuel := 2) hConsExt rfl (by rfl)
  have hMixSpec : PartialTyping natListAssumptions cNil (.mix (.bound 2) (.bound 2)) natMixinTy [0, 0, 2] :=
    .mix (assumptions := natListAssumptions) (self := .natural) (inherited := .natural) (middle := .natural) (provided := .natural)
      (.bound (context := cNil) (index := 2) (binding := ⟨natMixinTy, .unrestricted⟩) rfl)
      (.bound (context := cNil) (index := 2) (binding := ⟨natMixinTy, .unrestricted⟩) rfl)
      rfl rfl rfl rfl rfl rfl
  have hNilBody : PartialTyping natListAssumptions cNil (.fix (.mix (.bound 2) (.bound 2)) (.bound 0)) .natural [1, 0, 2] :=
    .fix hMixSpec rfl
      (.bound (context := cNil) (index := 0) (binding := ⟨.natural, .unrestricted⟩) rfl)
      rfl rfl rfl
  have hArms : ArmsTyping natListAssumptions natListProbeContext .unrestricted
      [ ("cons", .get (.extend (.bound 0) [("extra", .nat 1)]) "head")
      , ("nil", .fix (.mix (.bound 2) (.bound 2)) (.bound 0)) ]
      natListRow .natural [0, 2] :=
    .cons hConsBody (by rfl) (by rfl) (by rfl)
      (.cons hNilBody (by rfl) (by rfl) (by rfl)
        (.nil natListProbeContext .unrestricted .natural) (by rfl))
      (by rfl)
  ⟨.natural, [1, 2],
    .case hScrut hArms (by rfl) (by rfl),
    (by rfl), (by rfl), natListAssumptions_valid⟩

/-- Witness that `prepareChecked` prepares and certifies an erased program using `.case`, `.fix`,
`.mix`, and `.extend` under non-empty equi-recursive `natListAssumptions`. -/
public theorem natListProbe_prepared :
    (prepareChecked natListProbe natListProbeContext .natural).toBool = true :=
  prepareChecked_complete natListAssumptions_shareableComplete natListProbe_checkable natListProbeChecked

end Obend.Elab.Proofs.PrepareChecks
