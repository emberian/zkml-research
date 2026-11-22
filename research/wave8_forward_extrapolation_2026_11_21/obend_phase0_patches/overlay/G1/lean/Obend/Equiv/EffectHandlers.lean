module
/-
# `Obend.Equiv.EffectHandlers` — One-Shot Algebraic Effect Handlers, Resumption Typing & Handler Laws

Formalizes one-shot (`kQty ∈ {.linear, .affine}`, `Reuse.once`) shallow and deep algebraic effect
handlers over `Obend.Core.Term.Yields`, `Obend.Core.Term.plug`, `Obend.Core.Check.PartialTyping`,
and `Obend.Core.Machine`:
1. **One-Shot Resumption Discipline (`ResumpTy`, `TypedHandler`, `multiShot_resumption_rejected`)**.
2. **Source Yield Inversion & Multi-Turn Shallow Handling (`yields_typed_reify_resumption`,
   `multi_turn_shallow_trace_preserves_typing`, `machine_handler_no_sharedEffect_refusal`)**.
3. **Deep Handler Compiler (`AlgComp`, `compileDeep`, `fuseOp`) & All 3 Algebraic Handler Laws**
   (`compileDeep_preserves_typing`, `handler_return_law`, `handler_op_law`,
   `handler_effectCase_commutes`, `handler_vertical_fusion_iequiv`).
-/
public import Obend.Core.Check
public import Obend.Core.Machine
public import Obend.Core.Proofs.Preservation
public import Obend.Core.Proofs.TypedSubstitution
public import Obend.Equiv.Quote
public import Obend.Equiv.Yields
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Check
import all Obend.Core.Machine
import all Obend.Core.MachineTyping
import all Obend.Core.TypeGraph
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Cases.Activities
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Conservation
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Equiv.Behaviour
public section
namespace Obend.Equiv.EffectHandlers
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Equiv Obend.Core.MachineTyping
set_option autoImplicit false
/-! ## §1. One-Shot Resumption Types & Typed Handler Clauses -/
@[expose] def ResumpTy (R P' R' B : Ty) : Ty := .arrow .once .unrestricted R (.computation P' R' B)
theorem multiShot_resumption_rejected {kQty : Quantity}
    (hone : kQty = .linear ∨ kQty = .affine) (n : Nat) :
    kQty.fits (n + 2) = false ∧ (kQty.fits n = true → n ≤ 1) := by
  rcases hone with rfl | rfl <;> simp [Quantity.fits] <;> omega
theorem isData_shareableUnder (vars : List Nat) :
    ∀ {τ : Ty}, τ.isData = true → τ.shareableUnder vars = true
  | .natural, _ | .boolean, _ | .label, _ | .emptyRow, _ => rfl
  | .field _ m tl, h => by
      simp only [Ty.isData, Bool.and_eq_true] at h
      simp [Ty.shareableUnder, isData_shareableUnder vars h.1, isData_shareableUnder vars h.2]
  | .variant r, h => by simp only [Ty.isData] at h; simp [Ty.shareableUnder, isData_shareableUnder vars h]
  | .variable _, h | .arrow .., h | .specification .., h | .prototype .., h
  | .custody _, h | .computation .., h => by simp [Ty.isData] at h
theorem isPlan_shareableUnder (vars : List Nat) {P : Ty} (hp : P.isPlan = true) :
    P.shareableUnder vars = true ∧ P.isComputation = false := by
  cases P <;> simp [Ty.isPlan] at hp
  exact ⟨by simpa [Ty.shareableUnder] using isData_shareableUnder vars hp, rfl⟩
theorem isData_not_computation {R : Ty} (hr : R.isData = true) : R.isComputation = false := by
  cases R <;> simp [Ty.isData, Ty.isComputation] at hr ⊢

/-- A well-typed one-shot algebraic effect handler from `.computation P R A` to `.computation P' R' B`. -/
structure TypedHandler (θ : Assumptions) (Γ : Context) (kQty : Quantity) (P R P' R' A B : Ty) where
  oneShot : kQty = .linear ∨ kQty = .affine
  planValid : P.isPlan = true
  respData : R.isData = true
  resPure : A.isComputation = false
  outPure : B.isComputation = false
  retQty : Quantity
  opPlanQty : Quantity
  retBody : Term
  opBody : Term
  retUses : Uses
  opUses : Uses
  retTyped : PartialTyping θ (⟨A, retQty⟩ :: Γ) retBody (.computation P' R' B) retUses
  retSafe : safeUses (⟨A, retQty⟩ :: Γ) retUses = true
  retValid : validContext θ.shareableVariables [⟨A, retQty⟩] = true
  retFits : retQty.fits (retUses.headD 0) = true
  opTyped : PartialTyping θ (⟨ResumpTy R P' R' B, kQty⟩ :: ⟨P, opPlanQty⟩ :: Γ)
              opBody (.computation P' R' B) opUses
  opSafe : safeUses (⟨ResumpTy R P' R' B, kQty⟩ :: ⟨P, opPlanQty⟩ :: Γ) opUses = true
  opValidP : validContext θ.shareableVariables [⟨P, opPlanQty⟩] = true
  opFitsK : kQty.fits (opUses.headD 0) = true
  opFitsP : opPlanQty.fits (opUses.tail.headD 0) = true

@[expose] def TypedHandler.retFn {θ Γ kQty P R P' R' A B}
    (H : TypedHandler θ Γ kQty P R P' R' A B) : Term := .lam H.retBody

@[expose] def TypedHandler.opFn {θ Γ kQty P R P' R' A B}
    (H : TypedHandler θ Γ kQty P R P' R' A B) : Term := .lam (.lam H.opBody)

theorem TypedHandler.retFn_typed {θ Γ kQty P R P' R' A B}
    (H : TypedHandler θ Γ kQty P R P' R' A B) (hValidΓ : validContext θ.shareableVariables Γ = true) :
    PartialTyping θ Γ H.retFn (.arrow .once H.retQty A (.computation P' R' B)) H.retUses.tail := by
  have hv : validContext θ.shareableVariables (⟨A, H.retQty⟩ :: Γ) = true := by
    have hr := H.retValid
    simp only [validContext, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hr hValidΓ ⊢
    exact ⟨hr, hValidΓ⟩
  exact .lambda (annotation := ⟨A, .computation P' R' B, H.retQty, .once⟩)
    H.retTyped H.retSafe hv rfl H.retFits

theorem TypedHandler.opFn_typed {θ Γ kQty P R P' R' A B}
    (H : TypedHandler θ Γ kQty P R P' R' A B) (hValidΓ : validContext θ.shareableVariables Γ = true) :
    PartialTyping θ Γ H.opFn
      (.arrow .once H.opPlanQty P (.arrow .once kQty (ResumpTy R P' R' B) (.computation P' R' B)))
      H.opUses.tail.tail := by
  have hvP : validContext θ.shareableVariables (⟨P, H.opPlanQty⟩ :: Γ) = true := by
    have hp := H.opValidP
    simp only [validContext, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp hValidΓ ⊢
    exact ⟨hp, hValidΓ⟩
  have hvK : validContext θ.shareableVariables (⟨ResumpTy R P' R' B, kQty⟩ :: ⟨P, H.opPlanQty⟩ :: Γ) = true := by
    have hk : (kQty != .unrestricted || (ResumpTy R P' R' B).shareableUnder θ.shareableVariables) = true := by
      rcases H.oneShot with rfl | rfl <;> rfl
    have hml : mustBeLinear ⟨ResumpTy R P' R' B, kQty⟩ = true := rfl
    simp only [validContext, List.all_cons, Bool.and_eq_true] at hvP ⊢; exact ⟨⟨hk, hml⟩, hvP⟩
  have hSafeTail : safeUses (⟨P, H.opPlanQty⟩ :: Γ) H.opUses.tail = true := by
    have hlen := source_uses_length H.opTyped
    cases hu : H.opUses with
    | nil => simp [hu] at hlen
    | cons u0 ut =>
      have hs := H.opSafe; rw [hu] at hlen hs
      simp only [safeUses, List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons,
        List.all_cons, Bool.and_eq_true] at hlen hs ⊢
      exact ⟨hs.1, hs.2.2⟩
  have inner := PartialTyping.lambda
    (annotation := ⟨ResumpTy R P' R' B, .computation P' R' B, kQty, .once⟩)
    H.opTyped H.opSafe hvK rfl H.opFitsK
  exact .lambda
    (annotation := ⟨P, .arrow .once kQty (ResumpTy R P' R' B) (.computation P' R' B), H.opPlanQty, .once⟩)
    inner hSafeTail hvP rfl H.opFitsP

private theorem tail_nil_of_len1 {u : Uses} (h : u.length = 1) : u.tail = [] :=
  List.eq_nil_of_length_eq_zero (by simp [h])

private theorem tail2_nil_of_len2 {u : Uses} (h : u.length = 2) : u.tail.tail = [] :=
  List.eq_nil_of_length_eq_zero (by simp [h])

/-! ## §2. Source Yield Inversion, Reified Resumptions & Multi-Turn Shallow Handling -/

@[expose] def reifyResumption (ctx : List SourceFrame) : Term := .lam (plug ctx (.done (.bound 0)))

inductive ClosedCaseFrames : List SourceFrame → Prop where
  | nil : ClosedCaseFrames []
  | snoc {ctx : List SourceFrame} {arms : List (String × Term)} :
      ClosedCaseFrames ctx → (∀ arm ∈ arms, Obend.Core.Invariant.Scoped 1 arm.2) →
      ClosedCaseFrames (ctx ++ [.case arms])

theorem plug_done_steps {ctx : List SourceFrame} (hc : ClosedCaseFrames ctx) (r : Term) :
    Steps (plug ctx (.done r)) (plug ctx r) := by
  induction hc with
  | nil => exact .next (.done r) (.refl r)
  | @snoc inner arms _ _ ih =>
    simpa [plug, List.foldl_append, SourceFrame.plug] using Obend.Equiv.steps_case arms ih

private theorem plug_substitute_single {ctx : List SourceFrame}
    (hc : ClosedCaseFrames ctx) (r : Term) :
    (plug ctx (.done (.bound 0))).substitute (Obend.Equiv.single r) = plug ctx (.done r) := by
  induction hc with
  | nil => simp [plug, Term.substitute, Obend.Equiv.single]
  | @snoc inner arms _ harms ih =>
    have hfold : ∀ (x : Term), plug (inner ++ [.case arms]) x = .case (plug inner x) arms := fun x => by
      simp [plug, List.foldl_append, SourceFrame.plug]
    rw [hfold, hfold, Term.substitute, ih]; congr 1
    refine (List.map_congr_left (fun arm ha => ?_)).trans (List.map_id arms)
    have hsc1 := (Obend.Core.Invariant.scoped_encode_iff 1 arm.2).mp (harms arm ha)
    have hid : arm.2.substitute (liftSubstitution (Obend.Equiv.single r)) = arm.2 :=
      Obend.Core.TermTraverse.scoped_substitute_identity arm.2 1 hsc1 _
        (fun i hi => by cases i with | zero => rfl | succ _ => omega)
    cases arm; simp [hid]

theorem reifyResumption_apply_steps {ctx : List SourceFrame}
    (hc : ClosedCaseFrames ctx) (r : Term) :
    Steps (.app (reifyResumption ctx) r) (plug ctx r) := by
  refine .next (.beta (plug ctx (.done (.bound 0))) r) ?_
  rw [Obend.Equiv.instantiate_eq, plug_substitute_single hc r]; exact plug_done_steps hc r

/-- No closed well-typed pure term (`σ.isComputation = false`) can `Yields`. -/
theorem typed_pure_never_yields {θ : Assumptions} {t : Term} {σ : Ty} {u : Uses}
    (hTyped : PartialTyping θ [] t σ u) :
    σ.isComputation = false → ∀ {plan ctx}, ¬ Yields t plan ctx := by
  refine PartialTyping.rec
    (motive_1 := fun Γ t σ _ _ => Γ = [] → σ.isComputation = false → ∀ {plan ctx}, Yields t plan ctx → False)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend
    ?specification ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject
    ?case ?ifBool ?perform ?done ?effectCase ?split ?hole
    (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    hTyped rfl
  case bound => intro _ _ _ h hΓ; subst hΓ; simp at h
  case natural | boolean | label | lambda | record | specification | prototype | inject | mix | fix | done | hole =>
    intros; rename_i hy; cases hy
  case perform => intro _ _ _ _ _ _ _ _ _ _ hc; simp [Ty.isComputation] at hc
  case effectCase => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; simp [Ty.isComputation] at hc
  case conversion =>
    intro _ _ _ _ _ _ hsame ih hΓ hc _ _ hy
    exact ih hΓ ((Obend.Core.TypeGraph.equivalent_isComputation ((sameType_iff θ _ _).mp hsame)).trans hc) hy
  case application =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcall _ _ ihF _ hΓ _ _ _ hy
    cases hy with | application _ hyf => exact ihF hΓ (Obend.Core.Proofs.Preservation.callable_arrow_not_computation hcall) hyf
  case get =>
    intro _ _ _ _ _ _ _ _ hlk _ ih hΓ _ _ _ hy
    cases hy with | field _ hyt => exact ih hΓ (Obend.Core.Proofs.Preservation.lookup_not_computation _ _ _ _ _ hlk) hyt
  case extend =>
    intro _ _ _ _ _ _ _ _ _ _ _ hisRow _ ihT _ hΓ _ _ _ hy
    cases hy with | extend _ hyt => exact ihT hΓ (Obend.Core.Proofs.Preservation.isRow_not_computation _ _ _ hisRow) hyt
  case reflect => intro _ _ _ _ _ _ _ ih hΓ _ _ _ hy; cases hy with | reflect hyt => exact ih hΓ rfl hyt
  case metadata => intro _ _ _ _ _ _ _ ih hΓ _ _ _ hy; cases hy with | metadata hyt => exact ih hΓ rfl hyt
  case project => intro _ _ _ _ _ _ _ ih hΓ _ _ _ hy; cases hy with | project hyt => exact ih hΓ rfl hyt
  case binary =>
    intro _ prim _ _ inp _ _ _ hprim _ _ ihL ihR hΓ _ _ _ hy
    have hi : inp.isComputation = false := by
      cases prim <;> simp only [primitiveTypes, Prod.mk.injEq] at hprim <;> obtain ⟨rfl, _⟩ := hprim <;> rfl
    cases hy with | binaryLeft _ _ hyl => exact ihL hΓ hi hyl | binaryRight _ _ hyr => exact ihR hΓ hi hyr
  case ifZero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ ihV _ _ hΓ _ _ _ hy; cases hy with | condition _ _ hyv => exact ihV hΓ rfl hyv
  case case => intro _ _ _ _ _ _ _ _ _ _ _ _ ihS _ hΓ _ _ _ hy; cases hy with | case _ hys => exact ihS hΓ rfl hys
  case ifBool => intro _ _ _ _ _ _ _ _ _ _ _ _ ihC _ _ hΓ _ _ _ hy; cases hy with | ifBool _ _ hyc => exact ihC hΓ rfl hyc
  case split =>
    intro _ _ _ _ row _ _ _ _ _ _ _ hcovers _ ihT _ hΓ _ _ _ hy
    have hr : row.tail = .emptyRow := (Bool.and_eq_true_iff.mp hcovers).1 |> beq_iff_eq.mp
    cases hy with | split _ _ hyt => exact ihT hΓ (Obend.Core.Proofs.Preservation.tail_empty_not_computation hr) hyt

private theorem weaken_closed_arms {θ : Assumptions} {R0 : Ty}
    (hb0 : validContext θ.shareableVariables [⟨R0, .unrestricted⟩] = true) :
    ∀ {q : Quantity} {arms : List (String × Term)} {row res : Ty} {au : Uses},
      ArmsTyping θ [] q arms row res au → ArmsTyping θ [⟨R0, .unrestricted⟩] q arms row res [0]
  | q, [], _, res, _, .nil _ _ _ => .nil [⟨R0, .unrestricted⟩] q res
  | q, (_, body) :: rest, _, _, _, .cons (payload := payload) (bu := bu) hbT hsafeB hvalidQ hfits hrT _ => by
      have hbuLen : bu.length = 1 := source_uses_length hbT
      obtain ⟨c0, hbuEq⟩ : ∃ c, bu = [c] := by
        cases h : bu with
        | nil => rw [h] at hbuLen; cases hbuLen
        | cons c tl => rw [h] at hbuLen; exact ⟨c, congrArg (c :: ·) (List.eq_nil_of_length_eq_zero (Nat.succ.inj hbuLen))⟩
      have hbodySc1 : Obend.Core.Invariant.Scoped 1 body := source_scoped hbT
      have hshift1 : Obend.Core.Proofs.Preservation.shiftIndex 1 = liftRename Nat.succ := by
        funext idx; cases idx <;> simp [Obend.Core.Proofs.Preservation.shiftIndex, liftRename, Nat.succ_eq_add_one]
      have hbWeak := Obend.Core.Proofs.Preservation.source_insert_binding hbT 1 ⟨R0, .unrestricted⟩ (by simp) hb0
      rw [hshift1, hbuEq, List.insertIdx_succ_cons, List.insertIdx_zero,
        List.insertIdx_succ_cons, List.insertIdx_zero] at hbWeak
      have hbodyId : body.rename (liftRename Nat.succ) = body :=
        Obend.Core.TermTraverse.scoped_rename_identity body 1
          ((Obend.Core.Invariant.scoped_encode_iff 1 body).mp hbodySc1) _
          (fun i hi => by cases i with | zero => rfl | succ _ => omega)
      rw [hbodyId] at hbWeak
      have hsafeWeak : safeUses [⟨payload, q⟩, ⟨R0, .unrestricted⟩] [c0, 0] = true := by
        rw [hbuEq] at hsafeB; simpa [safeUses, safeQuantity] using hsafeB
      have hfits' : q.fits ([c0, 0].headD 0) = true := by rw [hbuEq] at hfits; exact hfits
      have hagree' : (rest.isEmpty || branchesAgree [⟨R0, .unrestricted⟩] [0] [0]) = true := by
        cases rest.isEmpty <;> rfl
      simpa [joinUses] using ArmsTyping.cons hbWeak hsafeWeak hvalidQ hfits' (weaken_closed_arms hb0 hrT) hagree'

/-- **Source Yield Inversion & Reified Resumption Typing**. -/
theorem yields_typed_reify_resumption {θ : Assumptions} {m plan : Term} {ctx : List SourceFrame}
    {P R A : Ty} (hTyped : PartialTyping θ [] m (.computation P R A) [])
    (hRData : R.isData = true) (hAPure : A.isComputation = false) (hYield : Yields m plan ctx) :
    ClosedCaseFrames ctx ∧
    PartialTyping θ [] plan P [] ∧
    PartialTyping θ [] (reifyResumption ctx) (ResumpTy R P R A) [] := by
  have aux : ∀ {m0 : Term} {τ0 : Ty} {u0 : Uses},
      PartialTyping θ [] m0 τ0 u0 →
      ∀ {P0 R0 A0 : Ty} {p0 : Term} {c0 : List SourceFrame},
        sameType θ τ0 (.computation P0 R0 A0) = true →
        R0.isData = true → A0.isComputation = false → Yields m0 p0 c0 →
        ClosedCaseFrames c0 ∧ PartialTyping θ [] p0 P0 [] ∧
        PartialTyping θ [⟨R0, .unrestricted⟩] (plug c0 (.done (.bound 0))) (.computation P0 R0 A0) [1] := by
    intro m0 τ0 u0 ht0
    refine PartialTyping.rec
      (motive_1 := fun Γ m0 τ0 _ _ => Γ = [] →
        ∀ {P0 R0 A0 : Ty} {p0 : Term} {c0 : List SourceFrame},
          sameType θ τ0 (.computation P0 R0 A0) = true →
          R0.isData = true → A0.isComputation = false → Yields m0 p0 c0 →
          ClosedCaseFrames c0 ∧ PartialTyping θ [] p0 P0 [] ∧
          PartialTyping θ [⟨R0, .unrestricted⟩] (plug c0 (.done (.bound 0))) (.computation P0 R0 A0) [1])
      (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
      ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend
      ?specification ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject
      ?case ?ifBool ?perform ?done ?effectCase ?split ?hole
      (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
      ht0 rfl
    case bound => intro _ _ _ h hΓ; subst hΓ; simp at h
    case natural | boolean | label | lambda | record | specification | prototype | inject | mix | fix | done | hole =>
      intros; rename_i hy; cases hy
    case conversion => intro _ _ _ _ _ _ hsame ih hΓ _ _ _ _ _ hconv hr ha hy; exact ih hΓ (sameType_trans hsame hconv) hr ha hy
    case perform =>
      intro Γ p1 pTy rTy u1 hp1 _ _ _ hΓ P0 R0 A0 p0 c0 hsame _ ha hy
      subst hΓ; have hu1 : u1 = [] := List.eq_nil_of_length_eq_zero (source_uses_length hp1); subst hu1
      cases hy with
      | perform _ =>
        obtain ⟨hP, hR, hA⟩ := Obend.Core.TypeGraph.computation_components ((sameType_iff θ _ _).mp hsame)
        have hRtoA : sameType θ R0 A0 = true :=
          (sameType_iff θ _ _).mpr ((Obend.Core.TypeGraph.equivalent_equivalence θ).trans
            ((Obend.Core.TypeGraph.equivalent_equivalence θ).symm hR) hA)
        exact ⟨.nil, .conversion hp1 ((sameType_iff θ _ _).mpr hP),
          .done (.conversion (.bound (binding := ⟨R0, .unrestricted⟩) rfl) hRtoA) ha⟩
    case effectCase =>
      intro Γ scrut arms pTy rTy row res su au q hsT haT _ hdist _ ihS _ hΓ P0 R0 A0 p0 c0 hsame hr ha hy
      subst hΓ; cases hy with
      | @case _ _ innerCtx _ hys =>
        obtain ⟨hP, hR, _⟩ := Obend.Core.TypeGraph.computation_components ((sameType_iff θ _ _).mp hsame)
        have hScrutSame : sameType θ (.computation pTy rTy (.variant row)) (.computation P0 R0 (.variant row)) = true :=
          (sameType_iff θ _ _).mpr (Obend.Core.TypeGraph.computation_congruence hP hR
            ((Obend.Core.TypeGraph.equivalent_equivalence θ).refl _))
        obtain ⟨hcc, hpT, hPlugInner⟩ := ihS rfl hScrutSame hr rfl hys
        have hb0Valid : validContext θ.shareableVariables [⟨R0, .unrestricted⟩] = true := by
          simp [validContext, isData_shareableUnder _ hr, hr]
        have haWeak := weaken_closed_arms hb0Valid haT
        let rec convArms {arms0 : List (String × Term)} {r0 : Ty} {u0 : Uses} :
            ArmsTyping θ [⟨R0, .unrestricted⟩] q arms0 r0 (.computation pTy rTy res) u0 →
            ArmsTyping θ [⟨R0, .unrestricted⟩] q arms0 r0 (.computation P0 R0 A0) u0
          | .nil _ _ _ => .nil _ _ _
          | .cons hb hs hv hf hr0 hag => .cons (.conversion hb hsame) hs hv hf (convArms hr0) hag
        let rec armSc {a0 : List (String × Term)} {r0 : Ty} {u0 : Uses} :
            ArmsTyping θ [] q a0 r0 (.computation pTy rTy res) u0 → ∀ arm ∈ a0, Obend.Core.Invariant.Scoped 1 arm.2
          | .nil _ _ _, _, hm => by simp at hm
          | .cons hb _ _ _ hr0 _, arm, hm => by
              rcases List.mem_cons.mp hm with rfl | hm'
              · exact source_scoped hb
              · exact armSc hr0 arm hm'
        have hAllowed : caseAllowed θ q [⟨R0, .unrestricted⟩] [1] = true := by
          simp [caseAllowed, linearFree, reusableCaptures, isData_shareableUnder _ hr]
        have hOuter : PartialTyping θ [⟨R0, .unrestricted⟩]
            (.case (plug innerCtx (.done (.bound 0))) arms) (.computation P0 R0 A0) [1] := by
          simpa [addUses] using PartialTyping.effectCase hPlugInner (convArms haWeak) ha hdist hAllowed
        exact ⟨.snoc hcc (armSc haT), hpT, by simpa [plug, List.foldl_append, SourceFrame.plug] using hOuter⟩
    case application => intro Γ _ _ _ _ _ _ _ _ _ _ hfnT _ hcall _ _ _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | application _ hyf => exact False.elim (typed_pure_never_yields hfnT (Obend.Core.Proofs.Preservation.callable_arrow_not_computation hcall) hyf)
    case get => intro Γ _ _ _ _ _ _ htT hlk _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | field _ hyt => exact False.elim (typed_pure_never_yields htT (Obend.Core.Proofs.Preservation.lookup_not_computation _ _ _ _ _ hlk) hyt)
    case extend => intro Γ _ _ _ _ _ _ _ htT _ _ hisRow _ _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | extend _ hyt => exact False.elim (typed_pure_never_yields htT (Obend.Core.Proofs.Preservation.isRow_not_computation _ _ _ hisRow) hyt)
    case reflect => intro Γ _ _ _ _ htT _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | reflect hyt => exact False.elim (typed_pure_never_yields htT rfl hyt)
    case metadata => intro Γ _ _ _ _ htT _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | metadata hyt => exact False.elim (typed_pure_never_yields htT rfl hyt)
    case project => intro Γ _ _ _ _ htT _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | project hyt => exact False.elim (typed_pure_never_yields htT rfl hyt)
    case binary =>
      intro Γ prim _ _ inp _ _ _ hprim hlT hrT _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ
      have hi : inp.isComputation = false := by
        cases prim <;> simp only [primitiveTypes, Prod.mk.injEq] at hprim <;> obtain ⟨rfl, _⟩ := hprim <;> rfl
      cases hy with | binaryLeft _ _ hyl => exact False.elim (typed_pure_never_yields hlT hi hyl) | binaryRight _ _ hyr => exact False.elim (typed_pure_never_yields hrT hi hyr)
    case ifZero => intro Γ _ _ _ _ _ _ _ hvT _ _ _ _ _ _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | condition _ _ hyv => exact False.elim (typed_pure_never_yields hvT rfl hyv)
    case case => intro Γ _ _ _ _ _ _ _ hsT _ _ _ _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | case _ hys => exact False.elim (typed_pure_never_yields hsT rfl hys)
    case ifBool => intro Γ _ _ _ _ _ _ _ hcT _ _ _ _ _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ; cases hy with | ifBool _ _ hyc => exact False.elim (typed_pure_never_yields hcT rfl hyc)
    case split =>
      intro Γ _ _ _ row _ _ _ _ htT _ _ hcovers _ _ _ hΓ _ _ _ _ _ _ _ _ hy; subst hΓ
      have hr : row.tail = .emptyRow := (Bool.and_eq_true_iff.mp hcovers).1 |> beq_iff_eq.mp
      cases hy with | split _ _ hyt => exact False.elim (typed_pure_never_yields htT (Obend.Core.Proofs.Preservation.tail_empty_not_computation hr) hyt)
  obtain ⟨hcc, hpT, hPlugT⟩ := aux hTyped (sameType_refl θ _) hRData hAPure hYield
  have hvR : validContext θ.shareableVariables [⟨R, .unrestricted⟩] = true := by
    simp [validContext, isData_shareableUnder _ hRData, hRData]
  exact ⟨hcc, hpT, .lambda (annotation := ⟨R, .computation P R A, .unrestricted, .once⟩) hPlugT rfl hvR rfl rfl⟩

private theorem closed_app_typed {θ : Assumptions} {f a : Term} {r : Reuse} {q : Quantity} {dom cod : Ty}
    (hf : PartialTyping θ [] f (.arrow r q dom cod) []) (ha : PartialTyping θ [] a dom [])
    (haPure : dom.isComputation = false) (hv : validContext θ.shareableVariables [⟨dom, q⟩] = true) :
    PartialTyping θ [] (.app f a) cod [] := by
  have h' : (q != .unrestricted || dom.shareableUnder θ.shareableVariables) = true ∧
      mustBeLinear ⟨dom, q⟩ = true := by simpa [validContext] using hv
  have hsh := h'.1
  have hall : argumentAllowed θ q [] dom [] = true := by
    cases q <;> simp [argumentAllowed, haPure, linearFree, reusableCaptures] at hsh ⊢ <;> exact hsh
  exact .application hf ha rfl rfl hall

private theorem steps_pure_remains_pure {θ : Assumptions} {t u : Term} {T : Ty}
    (hT : PartialTyping θ [] t T []) (hpure : T.isComputation = false) (hst : Steps t u) :
    ∃ Tu, PartialTyping θ [] u Tu [] ∧ Tu.isComputation = false := by
  induction hst generalizing T with
  | refl => exact ⟨T, hT, hpure⟩
  | next s _ ih =>
    obtain ⟨T1, u1, h1, _, _, _, hrel⟩ := Obend.Core.Proofs.SubjectReduction.step_preserves_typing hT rfl rfl s
    have hu1 : u1 = [] := List.eq_nil_of_length_eq_zero (source_uses_length h1); subst hu1
    have hp1 : T1.isComputation = false := by
      rcases hrel with hsame | hrow | ⟨_, _, _, hdone⟩
      · exact (Obend.Core.TypeGraph.equivalent_isComputation ((sameType_iff θ _ _).mp hsame)).trans hpure
      · exact Obend.Core.Proofs.Preservation.tail_empty_not_computation hrow.2.2.2.1
      · exact False.elim (Obend.Core.Proofs.SubjectReduction.done_absurd hdone hpure)
    exact ih h1 hp1

theorem steps_to_yield_preserves_typing {θ : Assumptions} {m u plan : Term} {ctx : List SourceFrame}
    {P R A : Ty} (hTyped : PartialTyping θ [] m (.computation P R A) [])
    (hst : Steps m u) (hy : Yields u plan ctx) :
    PartialTyping θ [] u (.computation P R A) [] := by
  induction hst with
  | refl => exact hTyped
  | @next _ m1 _ s rest ih =>
    obtain ⟨T1, u1, h1, _, _, _, hrel⟩ := Obend.Core.Proofs.SubjectReduction.step_preserves_typing hTyped rfl rfl s
    have hu1 : u1 = [] := List.eq_nil_of_length_eq_zero (source_uses_length h1); subst hu1
    rcases hrel with hsame | hrow | ⟨rfl, _, _, _⟩
    · exact ih (.conversion h1 hsame) hy
    · exact False.elim (Obend.Core.Proofs.SubjectReduction.not_row rfl hrow.2.1)
    · cases s with
      | done _ =>
        obtain ⟨_, _, _, hvT, hpure, _⟩ := Obend.Core.Proofs.Preservation.source_done_decomposition hTyped
        have hv0 : _ = [] := List.eq_nil_of_length_eq_zero (source_uses_length hvT); rw [hv0] at hvT
        obtain ⟨Tu, huT, huPure⟩ := steps_pure_remains_pure hvT hpure rest
        exact False.elim (typed_pure_never_yields huT huPure hy)

/-- Multi-turn shallow handler execution trace over arbitrarily many `(plan, response)` turns. -/
inductive ShallowHandleTrace {θ : Assumptions} {kQty : Quantity} {P R A B : Ty}
    (H : TypedHandler θ [] kQty P R P R A B) : Term → List (Term × Term) → List Term → Prop where
  | ret {m v : Term} :
      Evaluates m v → PartialTyping θ [] v A [] → ShallowHandleTrace H m [] [.app H.retFn v]
  | turn {m u plan resp : Term} {ctx : List SourceFrame}
      {rest : List (Term × Term)} {restDispatches : List Term} :
      Steps m u → Yields u plan ctx → PartialTyping θ [] resp R [] →
      ShallowHandleTrace H (.app (reifyResumption ctx) resp) rest restDispatches →
      ShallowHandleTrace H m ((plan, resp) :: rest)
        (.app (.app H.opFn plan) (reifyResumption ctx) :: restDispatches)

/-- **Multi-Turn Shallow Handler Typing Preservation**. -/
theorem multi_turn_shallow_trace_preserves_typing {θ : Assumptions} {kQty : Quantity}
    {P R A : Ty} (H : TypedHandler θ [] kQty P R P R A A)
    {m : Term} {turns : List (Term × Term)} {dispatches : List Term}
    (hTyped : PartialTyping θ [] m (.computation P R A) [])
    (hTrace : ShallowHandleTrace H m turns dispatches) :
    dispatches ≠ [] ∧
    (∀ d ∈ dispatches, PartialTyping θ [] d (.computation P R A) []) ∧
    (∀ pr ∈ turns, PartialTyping θ [] pr.1 P [] ∧ PartialTyping θ [] pr.2 R []) := by
  have hRetFn : PartialTyping θ [] H.retFn (.arrow .once H.retQty A (.computation P R A)) [] := by
    have h := H.retFn_typed rfl; rwa [tail_nil_of_len1 (source_uses_length H.retTyped)] at h
  have hOpFn : PartialTyping θ [] H.opFn
      (.arrow .once H.opPlanQty P (.arrow .once kQty (ResumpTy R P R A) (.computation P R A))) [] := by
    have h := H.opFn_typed rfl; rwa [tail2_nil_of_len2 (source_uses_length H.opTyped)] at h
  induction hTrace with
  | ret _ hvT =>
    have hd := closed_app_typed hRetFn hvT H.resPure H.retValid
    exact ⟨by simp, fun d hm => by simp at hm; subst hm; exact hd, by simp⟩
  | turn hst hy hResp _ ih =>
    have huT := steps_to_yield_preserves_typing hTyped hst hy
    obtain ⟨_, hpT, hkT⟩ := yields_typed_reify_resumption huT H.respData H.resPure hy
    have hvK : validContext θ.shareableVariables [⟨ResumpTy R P R A, kQty⟩] = true := by
      rcases H.oneShot with rfl | rfl <;> rfl
    have hDisp := closed_app_typed (closed_app_typed hOpFn hpT (isPlan_shareableUnder θ.shareableVariables H.planValid).2 H.opValidP) hkT rfl hvK
    have hvR : validContext θ.shareableVariables [⟨R, .unrestricted⟩] = true := by
      simp [validContext, isData_shareableUnder _ H.respData, H.respData]
    obtain ⟨_, hallD, hallT⟩ := ih (closed_app_typed hkT hResp (isData_not_computation H.respData) hvR)
    refine ⟨by simp, fun d hm => ?_, fun pr hm => ?_⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact hDisp
      · exact hallD d hm'
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact ⟨hpT, hResp⟩
      · exact hallT pr hm'
private theorem typed_runBounded_yielded {θ : Assumptions} {types : AddressTypes}
    {st stY : Obend.Core.Machine.State} {res : Ty}
    {limits : Obend.Core.Machine.Limits} {ticks : Nat} {planAddr : Obend.Core.Machine.Address}
    (hSt : StateTyping θ types st res)
    (hRun : Obend.Core.Machine.runBounded limits ticks st = .yielded planAddr stY) :
    stY.control = .yielded planAddr ∧
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping θ after stY res) := by
  induction ticks generalizing types st with
  | zero =>
    cases hc : st.control <;> simp [Obend.Core.Machine.runBounded, hc] at hRun
    obtain ⟨rfl, rfl⟩ := hRun; exact ⟨hc, types, type_extension_refl types, ⟨hSt⟩⟩
  | succ t ih =>
    cases hc : st.control <;> simp only [Obend.Core.Machine.runBounded, Obend.Core.Machine.step, hc] at hRun
    case complete | blackhole | refused => simp at hRun
    case yielded =>
      simp only [Obend.Core.Machine.Outcome.yielded.injEq] at hRun
      obtain ⟨rfl, rfl⟩ := hRun; exact ⟨hc, types, type_extension_refl types, ⟨hSt⟩⟩
    all_goals
      by_cases hfits : ((Obend.Core.Machine.stepRaw st).heap.size ≤ limits.heap ∧
          (Obend.Core.Machine.stepRaw st).stack.length ≤ limits.stack)
      · simp only [hfits, decide_true, Bool.true_and, ↓reduceIte] at hRun
        obtain ⟨mid, hext1, ⟨hMid⟩⟩ := Obend.Core.Proofs.Preservation.typed_stepRaw_preserved hSt
        obtain ⟨hctrl, after, hext2, hAfter⟩ := ih hMid hRun
        exact ⟨hctrl, after, type_extension_trans hext1 hext2, hAfter⟩
      · have hf : (decide ((Obend.Core.Machine.stepRaw st).heap.size ≤ limits.heap) &&
            decide ((Obend.Core.Machine.stepRaw st).stack.length ≤ limits.stack)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        simp [hf] at hRun
inductive MachineYieldResumeTrace (θ : Assumptions) (R : Ty) :
    Obend.Core.Machine.State → List (Obend.Core.Machine.Limits × Nat × Term) →
    Obend.Core.Machine.State → Prop where
  | done (st : Obend.Core.Machine.State) : MachineYieldResumeTrace θ R st [] st
  | turn {st stY stNext stFinal : Obend.Core.Machine.State} {planAddr : Obend.Core.Machine.Address}
      {limits : Obend.Core.Machine.Limits} {ticks : Nat} {resp : Term}
      {rest : List (Obend.Core.Machine.Limits × Nat × Term)} :
      Obend.Core.Machine.runBounded limits ticks st = .yielded planAddr stY →
      PartialTyping θ [] resp R [] → Obend.Core.Machine.resume resp stY = some stNext →
      MachineYieldResumeTrace θ R stNext rest stFinal →
      MachineYieldResumeTrace θ R st ((limits, ticks, resp) :: rest) stFinal
/-- **`Core.Machine` `.sharedEffect`-Refusal Freedom & Yield Quiescence Across Multi-Turn Handling**. -/
theorem machine_handler_no_sharedEffect_refusal
    (source : AnnotatedTerm) (checked : Checked source []) {P R A : Ty} (hAct : checked.type = .computation P R A)
    {turns : List (Obend.Core.Machine.Limits × Nat × Term)} {stFinal : Obend.Core.Machine.State}
    (hTrace : MachineYieldResumeTrace source.assumptions R (Obend.Core.Machine.initial source.erase) turns stFinal) :
    (∃ types, Nonempty (StateTyping source.assumptions types stFinal (.computation P R A))) ∧
    (∀ limits ticks retained, Obend.Core.Machine.runBounded limits ticks stFinal ≠ .refused .sharedEffect retained) ∧
    (∀ limits ticks reason retained, Obend.Core.Machine.runBounded limits ticks stFinal ≠ .refused reason retained) ∧
    (∀ planAddr, stFinal.control = .yielded planAddr → Obend.Core.Machine.forcingShared stFinal.stack = false) := by
  have hInit : StateTyping source.assumptions [] (Obend.Core.Machine.initial source.erase)
      (.computation P R A) := hAct ▸ checked_initial_state source checked
  have walk : ∀ {st stF : Obend.Core.Machine.State} {ts : List (Obend.Core.Machine.Limits × Nat × Term)},
      MachineYieldResumeTrace source.assumptions R st ts stF → ∀ {types : AddressTypes},
      StateTyping source.assumptions types st (.computation P R A) →
      ∃ after, Nonempty (StateTyping source.assumptions after stF (.computation P R A)) := by
    intro st stF ts ht; induction ht with
    | done _ => intro types hSt; exact ⟨types, ⟨hSt⟩⟩
    | turn hRun hResp hRes _ ih =>
      intro types hSt
      obtain ⟨hyCtrl, after, _, ⟨hStY⟩⟩ := typed_runBounded_yielded hSt hRun
      obtain ⟨hStNext⟩ := Obend.Core.Proofs.Preservation.typed_resume_preserved hStY hyCtrl hResp hRes
      exact ih hStNext
  obtain ⟨types, ⟨hFinal⟩⟩ := walk hTrace hInit
  refine ⟨⟨types, ⟨hFinal⟩⟩,
    fun l t ret => Obend.Core.Proofs.Preservation.typed_runBounded_no_refusal hFinal l t .sharedEffect ret,
    fun l t r ret => Obend.Core.Proofs.Preservation.typed_runBounded_no_refusal hFinal l t r ret,
    fun planAddr hy => (Obend.Core.Proofs.Preservation.typed_yield_quiescent hFinal hy).1⟩

/-! ## §3. CPS Deep Handler (`AlgComp`, `compileDeep`, `fuseOp`) & All 3 Algebraic Handler Laws -/

inductive AlgComp where
  | done (v : Term) | perform (plan : Term)
  | effectCase (scrut : AlgComp) (arms : List (String × AlgComp))
  | ifBool (cond : Term) (wt wf : AlgComp)

mutual
def AlgComp.toTerm (c : AlgComp) : Term :=
  match c with
  | .done v => .done v | .perform plan => .perform plan
  | .effectCase scrut arms => .case scrut.toTerm (algArmsToTerms arms)
  | .ifBool cond wt wf => .ifBool cond wt.toTerm wf.toTerm
termination_by structural c

def algArmsToTerms (arms : List (String × AlgComp)) : List (String × Term) :=
  match arms with | [] => [] | (tag, body) :: rest => (tag, body.toTerm) :: algArmsToTerms rest
termination_by structural arms
end

mutual
@[expose] def compileDeepWith (opFn kRet : Term) (c : AlgComp) : Term :=
  match c with
  | .done v => .app kRet v | .perform plan => .app (.app opFn plan) kRet
  | .effectCase scrut arms =>
      compileDeepWith opFn (.lam (.case (.bound 0) (compileDeepArms opFn kRet arms))) scrut
  | .ifBool cond wt wf => .ifBool cond (compileDeepWith opFn kRet wt) (compileDeepWith opFn kRet wf)
termination_by structural c

@[expose] def compileDeepArms (opFn kRet : Term) (arms : List (String × AlgComp)) : List (String × Term) :=
  match arms with
  | [] => []
  | (tag, body) :: rest =>
      (tag, (compileDeepWith (opFn.rename Nat.succ) (kRet.rename Nat.succ) body).rename (liftRename Nat.succ)) ::
        compileDeepArms opFn kRet rest
termination_by structural arms
end

@[expose] def compileDeep (retFn opFn : Term) (c : AlgComp) : Term := compileDeepWith opFn retFn c

theorem liftRename_succ_subst_single (u x : Term) :
    (u.rename (liftRename Nat.succ)).substitute (liftSubstitution (Obend.Equiv.single x)) = u := by
  rw [Obend.Core.TermTraverse.rename_substitute]
  conv => rhs; rw [← Obend.Equiv.substitute_bound u]
  congr 1; funext i; cases i <;> simp [liftRename, liftSubstitution, Obend.Equiv.single, Term.rename]

private theorem closed_rename_id {t : Term} (hsc : Obend.Core.Invariant.Scoped 0 t) (f : Nat → Nat) :
    t.rename f = t :=
  Obend.Core.TermTraverse.scoped_rename_identity t 0
    ((Obend.Core.Invariant.scoped_encode_iff 0 t).mp hsc) f (fun _ h => by omega)

private theorem compileDeepArms_subst_closed {opFn kRet : Term}
    (hOp : Obend.Core.Invariant.Scoped 0 opFn) (hRet : Obend.Core.Invariant.Scoped 0 kRet) (x : Term) :
    ∀ (arms : List (String × AlgComp)),
      (compileDeepArms opFn kRet arms).map (fun a => (a.1, a.2.substitute (liftSubstitution (Obend.Equiv.single x)))) =
        arms.map (fun a => (a.1, compileDeepWith opFn kRet a.2))
  | [] => rfl
  | (_, _) :: rest => by
      simp only [compileDeepArms, List.map_cons, closed_rename_id hOp, closed_rename_id hRet,
        liftRename_succ_subst_single, compileDeepArms_subst_closed hOp hRet x rest]

private theorem map_find_compileDeep {opFn kRet : Term} {tag : String} {armComp : AlgComp} :
    ∀ {arms : List (String × AlgComp)},
      arms.find? (·.1 == tag) = some (tag, armComp) →
      (arms.map fun a => (a.1, compileDeepWith opFn kRet a.2)).find? (·.1 == tag) =
        some (tag, compileDeepWith opFn kRet armComp)
  | [], h => by simp at h
  | (nm, _) :: _, h => by
      by_cases he : (nm == tag) = true
      · simp only [List.find?_cons, he, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; simp
      · simp only [Bool.not_eq_true] at he; simp only [List.find?_cons, he] at h
        simpa [he] using map_find_compileDeep h

def AllUnrestricted (vars : List Nat) (Γ : Context) : Prop :=
  ∀ b ∈ Γ, b.quantity = .unrestricted ∧ b.type.shareableUnder vars = true

private theorem allUnrestricted_cons {vars : List Nat} {t : Ty} {Γ : Context}
    (hsh : t.shareableUnder vars = true) (hΓ : AllUnrestricted vars Γ) :
    AllUnrestricted vars (⟨t, .unrestricted⟩ :: Γ) := fun b hb => by
  rcases List.mem_cons.mp hb with rfl | hb'
  · exact ⟨rfl, hsh⟩
  · exact hΓ b hb'

private theorem allUnrestricted_valid {vars : List Nat} {Γ : Context} (hΓ : AllUnrestricted vars Γ) :
    validContext vars Γ = true := by
  induction Γ with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨hq, hsh⟩ := hΓ b (List.mem_cons_self ..)
    have hrest := ih (fun x hx => hΓ x (List.mem_cons_of_mem _ hx))
    simp only [validContext, List.all_cons, Bool.and_eq_true] at hrest ⊢
    exact ⟨by simp [hq, hsh, Ty.bearsCustody_of_shareableUnder hsh], hrest⟩

private theorem allUnrestricted_safe {vars : List Nat} {Γ : Context} (hΓ : AllUnrestricted vars Γ)
    {u : Uses} (hlen : u.length = Γ.length) : safeUses Γ u = true := by
  simp only [safeUses, hlen, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro p hp; obtain ⟨hq, _⟩ := hΓ p.1 (List.of_mem_zip hp).1; simp [hq, safeQuantity]

private theorem allUnrestricted_linearFree {vars : List Nat} {Γ : Context} (hΓ : AllUnrestricted vars Γ)
    (u : Uses) : linearFree Γ u = true := by
  simp only [linearFree, List.all_eq_true]
  intro p hp; obtain ⟨hq, _⟩ := hΓ p.1 (List.of_mem_zip hp).1; simp [hq]

private theorem allUnrestricted_reusable {vars : List Nat} {Γ : Context} (hΓ : AllUnrestricted vars Γ)
    {u : Uses} (hlen : u.length = Γ.length) : reusableCaptures vars Γ u = true := by
  simp only [reusableCaptures, hlen, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro p hp; obtain ⟨hq, hsh⟩ := hΓ p.1 (List.of_mem_zip hp).1; simp [hq, hsh]

private theorem allUnrestricted_branchesAgree {vars : List Nat} :
    ∀ {Γ : Context}, AllUnrestricted vars Γ → ∀ u₁ u₂, branchesAgree Γ u₁ u₂ = true
  | [], _, _, _ | _ :: _, _, [], _ | _ :: _, _, _ :: _, [] => rfl
  | b :: _, hΓ, _ :: r₁, _ :: r₂ => by
      obtain ⟨hq, _⟩ := hΓ b (List.mem_cons_self ..)
      simp [branchesAgree, Quantity.agrees, hq, allUnrestricted_branchesAgree (fun x hx => hΓ x (List.mem_cons_of_mem _ hx)) r₁ r₂]

private theorem weaken_closed_ctx {θ : Assumptions} {t : Term} {τ : Ty}
    (ht : PartialTyping θ [] t τ []) :
    ∀ {Γ : Context}, AllUnrestricted θ.shareableVariables Γ → PartialTyping θ Γ t τ (zeroUses Γ)
  | [], _ => ht
  | b :: _, hΓ => by
      obtain ⟨hq, hsh⟩ := hΓ b (List.mem_cons_self ..)
      have hbV : validContext θ.shareableVariables [b] = true := by
        simp [validContext, hq, hsh, Ty.bearsCustody_of_shareableUnder hsh]
      have hw := Obend.Core.Proofs.Preservation.source_weaken
        (weaken_closed_ctx ht (fun x hx => hΓ x (List.mem_cons_of_mem _ hx))) b hbV
      rw [closed_rename_id (source_scoped ht) Nat.succ] at hw
      simpa [zeroUses, List.replicate_succ] using hw

mutual
inductive AlgCompTyping (θ : Assumptions) : Context → AlgComp → Ty → Ty → Ty → Prop where
  | done {Γ v P R C u} :
      C.isComputation = false → C.shareableUnder θ.shareableVariables = true →
      PartialTyping θ Γ v C u → AlgCompTyping θ Γ (.done v) P R C
  | perform {Γ plan P R u} : PartialTyping θ Γ plan P u → AlgCompTyping θ Γ (.perform plan) P R R
  | effectCase {Γ scrut arms P R row C} :
      row.isData = true → C.isComputation = false → C.shareableUnder θ.shareableVariables = true →
      labelsDistinct (algArmsToTerms arms) = true →
      AlgCompTyping θ Γ scrut P R (.variant row) → AlgArmsTyping θ Γ arms row P R C →
      AlgCompTyping θ Γ (.effectCase scrut arms) P R C
  | ifBool {Γ cond wt wf P R C cu} :
      PartialTyping θ Γ cond .boolean cu →
      AlgCompTyping θ Γ wt P R C → AlgCompTyping θ Γ wf P R C →
      AlgCompTyping θ Γ (.ifBool cond wt wf) P R C

inductive AlgArmsTyping (θ : Assumptions) : Context → List (String × AlgComp) → Ty → Ty → Ty → Ty → Prop where
  | nil (Γ P R C) : AlgArmsTyping θ Γ [] .emptyRow P R C
  | cons {Γ tag body rest payload row P R C} :
      payload.isData = true →
      AlgCompTyping θ (⟨payload, .unrestricted⟩ :: Γ) body P R C →
      AlgArmsTyping θ Γ rest row P R C →
      AlgArmsTyping θ Γ ((tag, body) :: rest) (.field tag payload row) P R C
end

private theorem any_compileDeepArms (opFn kRet : Term) (nm : String) :
    ∀ (xs : List (String × AlgComp)),
      (compileDeepArms opFn kRet xs).any (·.1 == nm) = (algArmsToTerms xs).any (·.1 == nm)
  | [] => rfl
  | (_, _) :: tl => by simp [compileDeepArms, algArmsToTerms, any_compileDeepArms opFn kRet nm tl]

private theorem labelsDistinct_compileDeepArms (opFn kRet : Term) :
    ∀ (arms : List (String × AlgComp)),
      labelsDistinct (compileDeepArms opFn kRet arms) = labelsDistinct (algArmsToTerms arms)
  | [] => rfl
  | (_, _) :: rest => by
      simp [compileDeepArms, algArmsToTerms, labelsDistinct, any_compileDeepArms,
        labelsDistinct_compileDeepArms opFn kRet rest]

private theorem compileDeep_typing_aux {θ : Assumptions} {kQty : Quantity} {P R P' R' A B : Ty}
    (H : TypedHandler θ [] kQty P R P' R' A B) (hOpSc : Obend.Core.Invariant.Scoped 0 H.opFn)
    {Γ : Context} {c : AlgComp} {P0 R0 C : Ty} (hcT : AlgCompTyping θ Γ c P0 R0 C)
    (hP0 : P0 = P) (hR0 : R0 = R) (hΓ0 : AllUnrestricted θ.shareableVariables Γ)
    {kRet0 : Term} {ku0 : Uses} (hkT0 : PartialTyping θ Γ kRet0 (ResumpTy C P' R' B) ku0) :
    ∃ u, PartialTyping θ Γ (compileDeepWith H.opFn kRet0 c) (.computation P' R' B) u := by
  have hOpClosed : PartialTyping θ [] H.opFn
      (.arrow .once H.opPlanQty P (.arrow .once kQty (ResumpTy R P' R' B) (.computation P' R' B))) [] := by
    have h := H.opFn_typed rfl; rwa [tail2_nil_of_len2 (source_uses_length H.opTyped)] at h
  have hOpEq : H.opFn.rename Nat.succ = H.opFn := closed_rename_id hOpSc Nat.succ
  have appUnr : ∀ {Γ : Context} {f a : Term} {q : Quantity} {dom cod : Ty} {fu au : Uses},
      AllUnrestricted θ.shareableVariables Γ →
      PartialTyping θ Γ f (.arrow .once q dom cod) fu → PartialTyping θ Γ a dom au →
      dom.isComputation = false → (q = .unrestricted → dom.shareableUnder θ.shareableVariables = true) →
      PartialTyping θ Γ (.app f a) cod (addUses fu au) := by
    intro Γ f a q dom cod fu au hΓ hf ha hpure hsh
    have hall : argumentAllowed θ q Γ dom au = true := by
      have hlf := allUnrestricted_linearFree hΓ au
      have hrc := allUnrestricted_reusable hΓ (source_uses_length ha)
      cases q <;> simp [argumentAllowed, hpure, hlf, hrc]; exact hsh rfl
    exact .application hf ha rfl rfl hall
  exact AlgCompTyping.rec
    (motive_1 := fun Γ c P0 R0 C _ =>
      P0 = P → R0 = R → AllUnrestricted θ.shareableVariables Γ →
      ∀ {kRet : Term} {ku : Uses}, PartialTyping θ Γ kRet (ResumpTy C P' R' B) ku →
        ∃ u, PartialTyping θ Γ (compileDeepWith H.opFn kRet c) (.computation P' R' B) u)
    (motive_2 := fun Γ arms row P0 R0 C _ =>
      P0 = P → R0 = R → AllUnrestricted θ.shareableVariables Γ →
      ∀ (rowFull : Ty) {kRet : Term} {ku : Uses}, rowFull.isData = true →
        PartialTyping θ Γ kRet (ResumpTy C P' R' B) ku →
        ∃ au, ArmsTyping θ (⟨.variant rowFull, .unrestricted⟩ :: Γ) .unrestricted
          (compileDeepArms H.opFn kRet arms) row (.computation P' R' B) au)
    (fun {Γ v _ _ C vu} hCPure hCSh hvT _ _ hΓ {kRet ku} hkT =>
      ⟨addUses ku vu, appUnr hΓ hkT hvT hCPure (fun _ => hCSh)⟩)
    (fun {Γ plan _ _ pu} hpT hP hR hΓ {kRet ku} hkT => by
      subst hP hR; have hPSh := isPlan_shareableUnder θ.shareableVariables H.planValid
      have hApp1 := appUnr hΓ (weaken_closed_ctx hOpClosed hΓ) hpT hPSh.2 (fun _ => hPSh.1)
      exact ⟨_, appUnr hΓ hApp1 hkT rfl (fun h => by rcases H.oneShot with rfl | rfl <;> cases h)⟩)
    (fun {Γ scrut arms _ _ row C} hRowData _ _ hDist _ _ ihS ihA hP hR hΓ {kRet ku} hkT => by
      subst hP hR; obtain ⟨au, haT⟩ := ihA rfl rfl hΓ row hRowData hkT
      have hVarSh : (Ty.variant row).shareableUnder θ.shareableVariables = true := by
        simpa [Ty.shareableUnder] using isData_shareableUnder θ.shareableVariables hRowData
      let Γ' : Context := ⟨.variant row, .unrestricted⟩ :: Γ
      have hΓ' : AllUnrestricted θ.shareableVariables Γ' := allUnrestricted_cons hVarSh hΓ
      have hScrut0 : PartialTyping θ Γ' (.bound 0) (.variant row) (variableUses Γ' 0) :=
        .bound (binding := ⟨.variant row, .unrestricted⟩) rfl
      have hCaseAllowed : caseAllowed θ .unrestricted Γ' (variableUses Γ' 0) = true := by
        simp [caseAllowed, allUnrestricted_linearFree hΓ', allUnrestricted_reusable hΓ' (source_uses_length hScrut0)]
      have hCaseT : PartialTyping θ Γ' (.case (.bound 0) (compileDeepArms H.opFn kRet arms))
          (.computation P' R' B) (addUses (variableUses Γ' 0) au) :=
        .case hScrut0 haT (by rwa [labelsDistinct_compileDeepArms]) hCaseAllowed
      have hkArmsT : PartialTyping θ Γ (.lam (.case (.bound 0) (compileDeepArms H.opFn kRet arms)))
          (ResumpTy (.variant row) P' R' B) (addUses (variableUses Γ' 0) au).tail :=
        .lambda (annotation := ⟨.variant row, .computation P' R' B, .unrestricted, .once⟩)
          hCaseT (allUnrestricted_safe hΓ' (source_uses_length hCaseT)) (allUnrestricted_valid hΓ') rfl rfl
      exact ihS rfl rfl hΓ hkArmsT)
    (fun {Γ cond wt wf _ _ C cu} hcT _ _ ihT ihF hP hR hΓ {kRet ku} hkT => by
      obtain ⟨tu, htT⟩ := ihT hP hR hΓ hkT; obtain ⟨fu, hfT⟩ := ihF hP hR hΓ hkT
      exact ⟨_, .ifBool hcT htT hfT (allUnrestricted_branchesAgree hΓ tu fu)⟩)
    (fun Γ _ _ _ _ _ _ rowFull {_ _} _ _ => ⟨zeroUses (⟨.variant rowFull, .unrestricted⟩ :: Γ), .nil _ _ _⟩)
    (fun {Γ tag body rest payload row _ _ C} hPayData _ _ ihB ihR hP hR hΓ rowFull {kRet ku} hRowData hkT => by
      subst hP hR
      have hPaySh := isData_shareableUnder θ.shareableVariables hPayData
      have hbPayValid : validContext θ.shareableVariables [⟨payload, .unrestricted⟩] = true := by
        simp [validContext, hPaySh, Ty.bearsCustody_of_shareableUnder hPaySh]
      have hΓPay := allUnrestricted_cons hPaySh hΓ
      obtain ⟨bu, hbT⟩ := ihB rfl rfl hΓPay (Obend.Core.Proofs.Preservation.source_weaken hkT ⟨payload, .unrestricted⟩ hbPayValid)
      have hVarSh : (Ty.variant rowFull).shareableUnder θ.shareableVariables = true := by
        simpa [Ty.shareableUnder] using isData_shareableUnder θ.shareableVariables hRowData
      have hbVarValid : validContext θ.shareableVariables [⟨.variant rowFull, .unrestricted⟩] = true := by
        simp [validContext, hVarSh, hRowData]
      have hshift1 : Obend.Core.Proofs.Preservation.shiftIndex 1 = liftRename Nat.succ := by
        funext idx; cases idx <;> simp [Obend.Core.Proofs.Preservation.shiftIndex, liftRename, Nat.succ_eq_add_one]
      have hbIns := Obend.Core.Proofs.Preservation.source_insert_binding hbT 1 ⟨.variant rowFull, .unrestricted⟩ (by simp) hbVarValid
      rw [hshift1, List.insertIdx_succ_cons, List.insertIdx_zero] at hbIns
      have hΓ1 := allUnrestricted_cons hVarSh hΓ
      have hΓ2 := allUnrestricted_cons hPaySh hΓ1
      obtain ⟨ru, hrT⟩ := ihR rfl rfl hΓ rowFull hRowData hkT
      have hAgree : ((compileDeepArms H.opFn kRet rest).isEmpty ||
          branchesAgree (⟨.variant rowFull, .unrestricted⟩ :: Γ) (bu.insertIdx 1 0).tail ru) = true := by
        simp [allUnrestricted_branchesAgree hΓ1]
      simp only [compileDeepArms, hOpEq]
      exact ⟨_, .cons hbIns (allUnrestricted_safe hΓ2 (source_uses_length hbIns)) hbPayValid rfl hrT hAgree⟩)
    hcT hP0 hR0 hΓ0 hkT0

/-- **Deep Handler Typing Preservation**. -/
theorem compileDeep_preserves_typing {θ : Assumptions} {kQty : Quantity} {P R P' R' A B : Ty}
    (H : TypedHandler θ [] kQty P R P' R' A B) (hRetUnr : H.retQty = .unrestricted)
    {c : AlgComp} (hcTyped : AlgCompTyping θ [] c P R A) :
    PartialTyping θ [] (compileDeep H.retFn H.opFn c) (.computation P' R' B) [] := by
  have hOpSc : Obend.Core.Invariant.Scoped 0 H.opFn := source_scoped (H.opFn_typed rfl)
  have hRetFnT : PartialTyping θ [] H.retFn (ResumpTy A P' R' B) [] := by
    have h := H.retFn_typed rfl
    rw [tail_nil_of_len1 (source_uses_length H.retTyped), hRetUnr] at h; exact h
  obtain ⟨u, huT⟩ := compileDeep_typing_aux H hOpSc hcTyped rfl rfl (by simp [AllUnrestricted]) hRetFnT
  rwa [List.eq_nil_of_length_eq_zero (source_uses_length huT)] at huT

/-- **Law 1 (`β_ret` / Handler Return Law)**. -/
theorem handler_return_law (retBody opFn v : Term) :
    Step (compileDeep (.lam retBody) opFn (.done v)) (instantiate retBody v) ∧
    Ahead (compileDeep (.lam retBody) opFn (.done v)) (instantiate retBody v) ∧
    IEquiv (compileDeep (.lam retBody) opFn (.done v)) (instantiate retBody v) ∧
    (compileDeep (.lam retBody) opFn (.done v) ≈r instantiate retBody v) := by
  have hs : Step (compileDeep (.lam retBody) opFn (.done v)) (instantiate retBody v) := .beta retBody v
  have ha := Ahead.ofStepsRefl (steps_one hs); exact ⟨hs, ha, iequiv_of_ahead ha, requiv_of_ahead ha⟩
/-- **Law 2 (`β_op` / Handler Operation Law & Deep Resumption Invocation)**. -/
theorem handler_op_law (retFn opBody plan payload : Term) (tag : String)
    (arms : List (String × AlgComp)) (armComp : AlgComp)
    (hRetSc : Obend.Core.Invariant.Scoped 0 retFn) (hOpSc : Obend.Core.Invariant.Scoped 2 opBody)
    (hFind : arms.find? (·.1 == tag) = some (tag, armComp)) :
    let opFn := Term.lam (.lam opBody)
    let k_deep := Term.lam (.case (.bound 0) (compileDeepArms opFn retFn arms))
    let rhs := instantiate (opBody.substitute (liftSubstitution (Obend.Equiv.single plan))) k_deep
    Steps (compileDeep retFn opFn (.effectCase (.perform plan) arms)) rhs ∧
    Ahead (compileDeep retFn opFn (.effectCase (.perform plan) arms)) rhs ∧
    IEquiv (compileDeep retFn opFn (.effectCase (.perform plan) arms)) rhs ∧
    (compileDeep retFn opFn (.effectCase (.perform plan) arms) ≈r rhs) ∧
    Steps (.app k_deep (.inject tag payload)) (instantiate (compileDeep retFn opFn armComp) payload) := by
  intro opFn k_deep rhs
  have hStepsOp : Steps (compileDeep retFn opFn (.effectCase (.perform plan) arms)) rhs := by
    change Steps (.app (.app (.lam (.lam opBody)) plan) k_deep) rhs
    refine .next (.application k_deep (.beta (.lam opBody) plan)) ?_
    rw [Obend.Equiv.instantiate_eq]; simp only [Term.substitute]; exact .next (.beta _ k_deep) (.refl _)
  have hAheadOp := Ahead.ofStepsRefl hStepsOp
  have hOpFnSc : Obend.Core.Invariant.Scoped 0 opFn := .lam (.lam hOpSc)
  have hResump : Steps (.app k_deep (.inject tag payload))
      (instantiate (compileDeep retFn opFn armComp) payload) := by
    refine .next (.beta _ (.inject tag payload)) ?_; rw [Obend.Equiv.instantiate_eq]
    simp only [Term.substitute, Obend.Equiv.single, compileDeepArms_subst_closed hOpFnSc hRetSc]
    exact .next (.caseInject tag payload _ _ (map_find_compileDeep hFind)) (.refl _)
  exact ⟨hStepsOp, hAheadOp, iequiv_of_ahead hAheadOp, requiv_of_ahead hAheadOp, hResump⟩
/-- **Law 3a (`effectCase` Commuting Conversion)**. -/
theorem handler_effectCase_commutes (retFn opFn payload : Term) (tag : String)
    (arms : List (String × AlgComp)) (armComp : AlgComp)
    (hRetSc : Obend.Core.Invariant.Scoped 0 retFn) (hOpSc : Obend.Core.Invariant.Scoped 0 opFn)
    (hFind : arms.find? (·.1 == tag) = some (tag, armComp)) :
    Steps (compileDeep retFn opFn (.effectCase (.done (.inject tag payload)) arms))
      (instantiate (compileDeep retFn opFn armComp) payload) ∧
    IEquiv (compileDeep retFn opFn (.effectCase (.done (.inject tag payload)) arms))
      (instantiate (compileDeep retFn opFn armComp) payload) := by
  have hs : Steps (compileDeep retFn opFn (.effectCase (.done (.inject tag payload)) arms))
      (instantiate (compileDeep retFn opFn armComp) payload) := by
    refine .next (.beta _ (.inject tag payload)) ?_; rw [Obend.Equiv.instantiate_eq]
    simp only [Term.substitute, Obend.Equiv.single, compileDeepArms_subst_closed hOpSc hRetSc]
    exact .next (.caseInject tag payload _ _ (map_find_compileDeep hFind)) (.refl _)
  exact ⟨hs, iequiv_of_ahead (Ahead.ofStepsRefl hs)⟩

mutual
@[expose] def mapOps (opMap : Term) (c : AlgComp) : AlgComp :=
  match c with
  | .done v => .done v | .perform plan => .perform (.app opMap plan)
  | .effectCase scrut arms => .effectCase (mapOps opMap scrut) (mapOpsArms opMap arms)
  | .ifBool cond wt wf => .ifBool cond (mapOps opMap wt) (mapOps opMap wf)
termination_by structural c

@[expose] def mapOpsArms (opMap : Term) (arms : List (String × AlgComp)) : List (String × AlgComp) :=
  match arms with
  | [] => []
  | (tag, body) :: rest => (tag, mapOps (opMap.rename Nat.succ) body) :: mapOpsArms opMap rest
termination_by structural arms
end

@[expose] def fuseOp (opMap opFn₂ : Term) : Term :=
  .lam (.lam (.app (.app (opFn₂.rename (fun n => n + 2))
    (.app (opMap.rename (fun n => n + 2)) (.bound 1))) (.bound 0)))

private theorem fuseOp_scoped {opMap opFn₂ : Term}
    (h1 : Obend.Core.Invariant.Scoped 0 opMap) (h2 : Obend.Core.Invariant.Scoped 0 opFn₂) :
    Obend.Core.Invariant.Scoped 0 (fuseOp opMap opFn₂) := by
  have h1' : Obend.Core.Invariant.Scoped 2 (opMap.rename (fun n => n + 2)) :=
    (Obend.Core.Invariant.scoped_encode_iff 2 _).mpr
      (Obend.Core.TermTraverse.scoped_rename opMap 0 2 ((Obend.Core.Invariant.scoped_encode_iff 0 _).mp h1) _ (fun _ h => by omega))
  have h2' : Obend.Core.Invariant.Scoped 2 (opFn₂.rename (fun n => n + 2)) :=
    (Obend.Core.Invariant.scoped_encode_iff 2 _).mpr
      (Obend.Core.TermTraverse.scoped_rename opFn₂ 0 2 ((Obend.Core.Invariant.scoped_encode_iff 0 _).mp h2) _ (fun _ h => by omega))
  exact .lam (.lam (.app (.app h2' (.app h1' (.bound (by omega)))) (.bound (by omega))))

private theorem compileDeep_mapOps_ahead {opMap opFn₂ : Term}
    (hMapSc : Obend.Core.Invariant.Scoped 0 opMap) (hOp2Sc : Obend.Core.Invariant.Scoped 0 opFn₂) :
    ∀ (c : AlgComp) {k₁ k₂ : Term}, Ahead k₁ k₂ →
      Ahead (compileDeepWith (fuseOp opMap opFn₂) k₁ c) (compileDeepWith opFn₂ k₂ (mapOps opMap c)) := by
  have hFuseSc := fuseOp_scoped hMapSc hOp2Sc
  intro c; induction hMeas : sizeOf c using Nat.strongRecOn generalizing c with
  | ind n ih =>
    intro k₁ k₂ hk; cases c with
    | done v => exact .app hk (.refl v)
    | perform plan =>
      have s2 : Steps (.app (.app (fuseOp opMap opFn₂) plan) k₁) (.app (.app opFn₂ (.app opMap plan)) k₁) := by
        unfold fuseOp; refine .next (.application k₁ (.beta _ plan)) ?_
        rw [Obend.Equiv.instantiate_eq]; simp only [Term.substitute]
        refine .next (.beta _ k₁) ?_
        rw [Obend.Equiv.instantiate_eq]; simp only [Term.substitute]
        rw [Obend.Equiv.shift_two_cancel, Obend.Equiv.shift_two_cancel]
        simp only [liftSubstitution, Obend.Equiv.single, Obend.Equiv.shift_one_cancel, Term.substitute]
        exact .refl _
      exact .run s2 (.app (.refl _) hk)
    | ifBool cond wt wf =>
      exact .ifBool (.refl cond) (ih _ (by subst hMeas; simp +arith) wt rfl hk)
        (ih _ (by subst hMeas; simp +arith) wf rfl hk)
    | effectCase scrut arms =>
      have armsRel : ∀ (as : List (String × AlgComp)), (∀ a ∈ as, sizeOf a.2 < n) →
          (compileDeepArms (fuseOp opMap opFn₂) k₁ as).map Prod.fst =
            (compileDeepArms opFn₂ k₂ (mapOpsArms opMap as)).map Prod.fst ∧
          ∀ p ∈ (compileDeepArms (fuseOp opMap opFn₂) k₁ as).zip
                (compileDeepArms opFn₂ k₂ (mapOpsArms opMap as)), Ahead p.1.2 p.2.2 := by
        intro as hlt; induction as with
        | nil => exact ⟨rfl, by simp [compileDeepArms, mapOpsArms]⟩
        | cons hd tl ihtl =>
          obtain ⟨hnames, hzip⟩ := ihtl (fun a ha => hlt a (List.mem_cons_of_mem _ ha))
          have hhd := ih _ (hlt hd (List.mem_cons_self ..)) hd.2 rfl (ahead_rename hk Nat.succ)
          simp only [compileDeepArms, mapOpsArms, closed_rename_id hFuseSc, closed_rename_id hOp2Sc,
            closed_rename_id hMapSc, List.map_cons, hnames, true_and, List.zip_cons_cons]
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
          · exact ahead_rename hhd (liftRename Nat.succ)
          · exact hzip p hp'
      obtain ⟨hnames, hzip⟩ := armsRel arms (fun a ha => by
        subst hMeas; have := List.sizeOf_lt_of_mem ha; cases a; simp +arith at this ⊢; omega)
      exact ih _ (by subst hMeas; simp +arith) scrut rfl (.lam (.case (.bound 0) hnames hzip))

private theorem compileDeep_kRet_ahead {opFn : Term} (hOpSc : Obend.Core.Invariant.Scoped 0 opFn) :
    ∀ (c : AlgComp) {k₁ k₂ : Term}, Ahead k₁ k₂ →
      Ahead (compileDeepWith opFn k₁ c) (compileDeepWith opFn k₂ c) := by
  intro c; induction hMeas : sizeOf c using Nat.strongRecOn generalizing c with
  | ind n ih =>
    intro k₁ k₂ hk; cases c with
    | done v => exact .app hk (.refl v)
    | perform _ => exact .app (.refl _) hk
    | ifBool cond wt wf =>
      exact .ifBool (.refl cond) (ih _ (by subst hMeas; simp +arith) wt rfl hk)
        (ih _ (by subst hMeas; simp +arith) wf rfl hk)
    | effectCase scrut arms =>
      have armsRel : ∀ (as : List (String × AlgComp)), (∀ a ∈ as, sizeOf a.2 < n) →
          (compileDeepArms opFn k₁ as).map Prod.fst = (compileDeepArms opFn k₂ as).map Prod.fst ∧
          ∀ p ∈ (compileDeepArms opFn k₁ as).zip (compileDeepArms opFn k₂ as), Ahead p.1.2 p.2.2 := by
        intro as hlt; induction as with
        | nil => exact ⟨rfl, by simp [compileDeepArms]⟩
        | cons hd tl ihtl =>
          obtain ⟨hnames, hzip⟩ := ihtl (fun a ha => hlt a (List.mem_cons_of_mem _ ha))
          have hhd := ih _ (hlt hd (List.mem_cons_self ..)) hd.2 rfl (ahead_rename hk Nat.succ)
          simp only [compileDeepArms, closed_rename_id hOpSc, List.map_cons, hnames, true_and, List.zip_cons_cons]
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
          · exact ahead_rename hhd (liftRename Nat.succ)
          · exact hzip p hp'
      obtain ⟨hnames, hzip⟩ := armsRel arms (fun a ha => by
        subst hMeas; have := List.sizeOf_lt_of_mem ha; cases a; simp +arith at this ⊢; omega)
      exact ih _ (by subst hMeas; simp +arith) scrut rfl (.lam (.case (.bound 0) hnames hzip))

/-- **Law 3b (Vertical Handler Fusion Theorem up to `Ahead`, `IEquiv`, and `REquiv`)**. -/
theorem handler_vertical_fusion_iequiv (opMap opFn₂ postFn retBody₁ : Term) (c : AlgComp)
    (hMapSc : Obend.Core.Invariant.Scoped 0 opMap)
    (hOp2Sc : Obend.Core.Invariant.Scoped 0 opFn₂)
    (hRet1Sc : Obend.Core.Invariant.Scoped 1 retBody₁) :
    let retTwoPass := Term.lam (.app (postFn.rename Nat.succ) (.app (.lam retBody₁) (.bound 0)))
    let retFused := Term.lam (.app (postFn.rename Nat.succ) retBody₁)
    let singlePass := compileDeep retFused (fuseOp opMap opFn₂) c
    let twoPass := compileDeep retTwoPass opFn₂ (mapOps opMap c)
    let mid := compileDeep retFused opFn₂ (mapOps opMap c)
    Ahead singlePass mid ∧ Ahead twoPass mid ∧ IEquiv singlePass twoPass ∧ (singlePass ≈r twoPass) := by
  intro retTwoPass retFused singlePass twoPass mid
  have hSub0 : instantiate retBody₁ (.bound 0) = retBody₁ := by
    rw [Obend.Equiv.instantiate_eq]
    exact Obend.Core.TermTraverse.scoped_substitute_identity retBody₁ 1
      ((Obend.Core.Invariant.scoped_encode_iff 1 retBody₁).mp hRet1Sc) _
      (fun i hi => by cases i with | zero => rfl | succ _ => omega)
  have hRetAhead : Ahead retTwoPass retFused := by
    refine .lam (.app (.refl _) ?_)
    have hs : Step (.app (.lam retBody₁) (.bound 0)) (instantiate retBody₁ (.bound 0)) := .beta retBody₁ (.bound 0)
    rw [hSub0] at hs; exact Ahead.ofStepsRefl (steps_one hs)
  have h1 : Ahead singlePass mid := compileDeep_mapOps_ahead hMapSc hOp2Sc c (.refl retFused)
  have h2 : Ahead twoPass mid := compileDeep_kRet_ahead hOp2Sc (mapOps opMap c) hRetAhead
  exact ⟨h1, h2, (iequiv_of_ahead h1).trans (iequiv_of_ahead h2).symm,
    (requiv_of_ahead h1).trans (requiv_of_ahead h2).symm⟩

end Obend.Equiv.EffectHandlers
end
