import Obend.AssertAxioms
import Obend.Tactic.Tooth
import Obend.Core.GradedCoreWeldDefs
import Obend.Core.GradedCoreWeld
import Obend.Core.GradedSessionMetatheory
import Obend.Spec.BidirectionalSurfaceElab
import Obend.Spec.FrontEnd

/-!
# Metasystem Witnesses & Teeth: Real-Core4 QTT, Sync/Async Sessions, `Spec.Syntax` Surface Elab & `FrontEnd`
-/

namespace Obend.Tests.GradedSessionAndSurfaceElab
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
open Obend.Core.GradedSessionMetatheory Obend.Polis.CapTP
open Obend.Spec.BidirectionalSurfaceElab
open Obend.Spec
set_option autoImplicit false

abbrev G := ZeroOneOmega

/-! ## 1. `CoreQuantityGrade` (`0 | 1 | α | ω`) & `ZeroOneOmega` on real `Obend.Core.Term.Term` -/

example : ∀ q : Quantity, (CoreQuantityGrade.ofQuantity q).toQuantity = q :=
  CoreQuantityGrade.toQuantity_ofQuantity

example : CoreQuantityGrade.le .zero .affine ∧ CoreQuantityGrade.le .one .affine ∧
    ¬ CoreQuantityGrade.le .zero .one ∧ ¬ CoreQuantityGrade.le .affine .one := by decide

def capTy : Ty := chanTy 0

/-- `fun (c :¹ .custody 0) => c` directly on `Obend.Core.Term.Term`. -/
def handOn : Term := .lam (.bound 0)

theorem handOn_typed :
    CoreGradedHasTy G [] handOn (.arrow .once .linear capTy capTy)
      (Usage.tail (Usage.single 0)) handOn :=
  .lam (.var rfl) (by simp [Usage.single, ZeroOneOmega.le, CoreGradeBridge.gradeOf])

theorem linear_drop_untypable :
    ¬ ∃ B U tₑ, CoreGradedHasTy G [] (.lam (.record [])) (.arrow .once .linear capTy B) U tₑ := by
  rintro ⟨B, U, tₑ, h⟩
  obtain ⟨_, _, _, _, bₑ, W, eT, _, body, fits, _⟩ := h.lam_inv
  obtain ⟨_, rfl, rfl, rfl⟩ := Ty.arrow.inj eT
  have hUnit : ∀ {Γ} {tm b : Term} {T : Ty} {V : Usage G},
      CoreGradedHasTy G Γ tm T V b → tm = .record [] → b = .record [] := by
    intro Γ tm b T V d he
    induction d with | unit => rfl | sub _ _ ih => exact ih he | _ => cases he
  have h1 := linear_cap_used_exactly_once body 0
  have below : (W 0).le .one := (ZeroOneOmega.rig_le _ _).mp fits
  rw [ZeroOneOmega.le_one] at below
  have hOcc := h1.2 below
  simp [hUnit body rfl, termOcc, fieldsOcc] at hOcc

/-- Syntactic zero-grade erasure (`eraseZero`) & two-way bisimulation (`core_zero_grade_erasure_bisim`). -/
def ghostCall (arg : Term) : Term := .app (.lam (.boolean true)) arg

theorem ghostCall_typed :
    CoreGradedHasTy G [] (ghostCall (.boolean false)) .boolean
      (Usage.add (Usage.tail Usage.zero) (Usage.scale .zero Usage.zero))
      (.app (.lam (.boolean true)) (.record [])) :=
  .app (.lam (reuse := .once) (q := .erased) .bool
    (by simp [Usage.zero, ZeroOneOmega.le, CoreGradeBridge.gradeOf])) .bool

theorem ghostCall_bisim_witness :
    (∃ v, Evaluates (ghostCall (.boolean false)) v ∧ Observes v (.boolean true)) ↔
    (∃ vₑ, Evaluates (.app (.lam (.boolean true)) (.record [])) vₑ ∧ Observes vₑ (.boolean true)) :=
  (core_zero_grade_erasure_bisim ghostCall_typed).2.2.1 (.boolean true)

example : Evaluates (.app (.lam (.boolean true)) (.record [])) (.boolean true) := by
  refine ⟨.next (.beta _ _) ?_, .boolean true⟩
  simp [instantiate]
  exact .refl _

/-- Inhabited `GradedCheckReady` → `Obend.Core.Check.PartialTyping` bridge (`graded_eraseZero_partialTyping`). -/
theorem gradedCheckReady_inhabited :
    ∃ uses, PartialTyping {} [] (.app (.lam (.boolean true)) (.record [])) .boolean uses ∧
      UsesFitUsage 0 uses (Usage.add (Usage.tail Usage.zero) (Usage.scale .zero Usage.zero)) := by
  have hLam : GradedCheckReady {} [] (.lam (.boolean true)) (.arrow .once .erased .natural .boolean)
      (Usage.tail Usage.zero) (.lam (.boolean true)) :=
    .lam (g := .zero) .bool (by trivial) (fun _ _ h => by simp at h) rfl (fun h => by cases h)
  have hApp : GradedCheckReady {} [] (.app (.lam (.boolean true)) (.nat 99)) .boolean
      (Usage.add (Usage.tail Usage.zero) (Usage.scale .zero Usage.zero))
      (.app (.lam (.boolean true)) (.record [])) :=
    .app hLam .nat (fun h => (h rfl).elim) (fun h => (h rfl).elim)
      (fun h => by rcases h with h | h <;> cases h) (fun h => by cases h)
  exact graded_eraseZero_partialTyping hApp

/-! ## 2. Synchronous `CoreSessionSoup` over `Yields` & Asynchronous `Polis.CapTP` FIFO Sessions -/

def proto : SessionTy G :=
  .send .one .boolean (.offer (.cons "ok" .endS (.cons "retry" (.recv .one .emptyRow .endS) .nil)))

theorem proto_wellFormed : proto.WellFormed := by
  simp [proto, SessionTy.WellFormed, Branches.WellFormed]

def freshHole : GuardedHole := ⟨SortedDigestSet.empty, SortedDigestSet.empty⟩

theorem freshHole_unspent (k : PendingId) : ¬ freshHole.spentNullifiers.spec k := by
  simp [freshHole, SortedDigestSet.spec, SortedDigestSet.empty]

theorem freshHole_unopen (k : PendingId) : ¬ freshHole.openPromises.spec k := by
  simp [freshHole, SortedDigestSet.spec, SortedDigestSet.empty]

theorem freshHole_wf : freshHole.WellFormed := by
  intro k ho _; exact freshHole_unopen k ho

/-- Multi-turn synchronous `RendezvousCoreTrace` over real `Core.Term.Yields` (`posSend` → `settleCloseWait`). -/
theorem rendezvousCoreTrace_inhabited :
    let h0 := allocatePromise freshHole 1
    let s0 : CoreSessionSoup G :=
      ⟨.send .one .boolean .endS, .recv .one .boolean .endS,
       .perform (.inject "send" (.boolean true)), .perform (.inject "recv" (.record [])),
       h0, h0, 1, 1, false⟩
    s0.WellFormed ∧ ∃ turns s1, turns.length = 1 ∧ RendezvousCoreTrace s0 turns s1 ∧ s1.WellFormed := by
  dsimp only
  have hUnsp0 : freshHole.spentNullifiers.contains 1#256 = false := rfl
  have hOpen : (allocatePromise freshHole 1).openPromises.spec 1 := by
    simp [allocatePromise, hUnsp0]
  have hUnsp : ¬ (allocatePromise freshHole 1).spentNullifiers.spec 1 := by
    simp [allocatePromise, hUnsp0, freshHole_unspent]
  let s0 : CoreSessionSoup G :=
    ⟨.send .one .boolean .endS, .recv .one .boolean .endS,
     .perform (.inject "send" (.boolean true)), .perform (.inject "recv" (.record [])),
     allocatePromise freshHole 1, allocatePromise freshHole 1, 1, 1, false⟩
  have wf0 : s0.WellFormed :=
    ⟨trivial, rfl, allocate_preserves_disjoint _ _ freshHole_wf,
     allocate_preserves_disjoint _ _ freshHole_wf,
     fun _ => ⟨hOpen, hUnsp, hOpen, hUnsp⟩, fun h => by cases h⟩
  have st1 : RendezvousCoreStep s0 (.posSendNegRecv ZeroOneOmega.one .boolean (.boolean true)) _ :=
    .posSend rfl rfl rfl (.refl _) (.perform _) (.refl _) (.perform _)
  have tr : RendezvousCoreTrace s0 [_] _ := .cons st1 (.nil _)
  exact ⟨wf0, [_], _, rfl, tr, (rendezvousCoreTrace_preserves_wellFormed wf0 tr).1⟩

/-- Asynchronous `CapTP` FIFO session progress & fidelity witness (`async_captp_session_progress_and_fidelity`). -/
theorem asyncCapTPSession_inhabited :
    let s0 : AsyncCapTPSession G := ⟨.send .one .boolean .endS, .recv .one .boolean .endS, [], [], freshHole, false⟩
    ∃ (hole' : GuardedHole) (sFinal : AsyncCapTPSession G),
      AsyncSessionWF s0 ∧
      AsyncSessionTrace s0 sFinal ∧
      sFinal.closed = true ∧
      hole'.spentNullifiers.spec 42 := by
  dsimp only
  obtain ⟨hole', _, hSpent, tr1⟩ := sync_send_refines_to_async_captp
    ZeroOneOmega.one Ty.boolean .endS (.boolean true) freshHole 42 (freshHole_unopen 42) (freshHole_unspent 42)
  let s0 : AsyncCapTPSession G :=
    ⟨.send ZeroOneOmega.one .boolean .endS, .recv ZeroOneOmega.one .boolean .endS, [], [], freshHole, false⟩
  have wf0 : AsyncSessionWF s0 :=
    ⟨trivial, trivial, freshHole_wf, .inl ⟨rfl, rfl⟩,
     ⟨List.nodup_nil, fun _ h => by cases h⟩, ⟨List.nodup_nil, fun _ h => by cases h⟩, fun h => by cases h⟩
  have appendTrace : ∀ {a b c : AsyncCapTPSession G},
      AsyncSessionTrace a b → AsyncSessionTrace b c → AsyncSessionTrace a c :=
    fun h1 h2 => by induction h1 with | refl => exact h2 | step s _ ih => exact .step s (ih h2)
  have trFull : AsyncSessionTrace s0 ⟨.endS, .endS, [], [], hole', true⟩ :=
    appendTrace tr1 (.step (.closeAsync rfl rfl rfl rfl rfl) (.refl _))
  exact ⟨hole', _, wf0, trFull, rfl, hSpent⟩

/-! ## 3. `BidirectionalSurfaceElab` directly on `Obend.Spec.Syntax` + `FaceIdeal4` Synergy -/

def effEnv : Env :=
  { planRow := .field "log" .natural (.field "audit" .boolean .emptyRow), response := .natural }

def accountExpr : Syntax.Expr := .record [("balance", .nat "10"), ("open", .bool true)]
def accountRow : Ty := .field "balance" .natural (.field "open" .boolean .emptyRow)

example : ((synthSurface {} [] 8 accountExpr).ok?.map (·.type)) = some accountRow := by decide +kernel
example : ((synthSurface {} [] 8 (.member accountExpr "balance")).ok?.map (·.type)) = some .natural := by
  decide +kernel
example : (synthSurface {} [] 8 (.var "x")).diag? =
    some (.unboundVariable "x") := by decide +kernel
example : (synthSurface {} [] 8 (.closure [⟨"c", "Nat", "once:linear"⟩] "_" (.nat "0"))).diag? =
    some (.linearityViolation "c" .linear 0) := by decide +kernel
example : (synthSurface {} [] 8 (.closure [⟨"x", "_", "unrestricted"⟩] "_" (.var "x"))).diag? =
    some (.missingAnnotation "x") := by decide +kernel
example : (checkSurface {} [] 8 (.closure [⟨"x", "_", "unrestricted"⟩] "_" (.var "x"))
    (.arrow .reusable .unrestricted .natural .natural)).diag? = none := by decide +kernel
example : (synthSurface effEnv [] 8 (.call (.member (.var "perform") "launch") [.nat "1"])).diag? =
    some (.effectLeak "launch" effEnv.planRow) := by decide +kernel
example : ((synthSurface effEnv [] 8 (.call (.member (.var "perform") "log") [.nat "1"])).ok?.map (·.type)) =
    some (.computation (.variant effEnv.planRow) .natural .natural) := by decide +kernel

/-- `elabSyntaxBody` & `elabSyntaxMethod` over `Syntax.Pattern` (`zero` / `succ`)! -/
def predBody : Syntax.Body :=
  .cases (.var "n") [(.zero, .expr (.nat "0")), (.succ "p", .expr (.var "p"))]

example : ((elabSyntaxMethod {} [] 8
    { name := "pred", params := [⟨"n", "Nat", "unrestricted"⟩], resultType := "Nat",
      qualifier := "primary", body := predBody, signature := .null }).ok?.map (·.type)) =
    some (.arrow .reusable .unrestricted .natural .natural) := by decide +kernel

/-- Law scoping & contract step elaboration on `Syntax.ContractDecl`. -/
def nonNegative : Obend.Spec.Law.LawExpr := .leC (.field "balance") 100

example : (elabContractDecl {} [] 8
    { name := "cap", targetType := "Account", law := some nonNegative, step := some accountExpr }).diag? =
    none := by decide +kernel

example : (elabContractDecl {} [] 8
    { name := "owned", targetType := "Account", law := some (.leC (.field "owner") 1),
      step := some accountExpr }).diag? =
    some (.lawOutsideRow "owned" "owner" accountRow) := by decide +kernel

/-- Inhabited witness of `elabSyntaxExpr_checks_bidirectionally` & `surface_qtt_cubical_delegated_synergy`. -/
def linBoolId : Syntax.Expr := .closure [⟨"x", "Bool", "once:linear"⟩] "_" (.var "x")
def linBoolIdTy : Ty := .arrow .once .linear .boolean .boolean

example : (checkSurfaceQtt {} [] 8 linBoolId linBoolIdTy).isSome = true := by decide +kernel

theorem surface_cubical_synergy_inhabited :
    ∃ ctx out,
      checkSurfaceQtt {} [] 8 linBoolId linBoolIdTy = some ⟨ctx, out⟩ ∧
      Obend.Core.Cubical2LTT.IsSubcomplex (Obend.Core.Cubical2LTT.CofibSyntax4.join (.dim0 0) (.dim1 0)).denote ∧
      (Obend.Core.Cubical2LTT.FaceIdeal4.dim0 0).join (Obend.Core.Cubical2LTT.FaceIdeal4.dim1 0) ≠
        Obend.Core.Cubical2LTT.FaceIdeal4.top := by
  cases h : checkSurfaceQtt {} [] 8 linBoolId linBoolIdTy with
  | none =>
    have hs : (checkSurfaceQtt {} [] 8 linBoolId linBoolIdTy).isSome = true := by decide +kernel
    rw [h] at hs; cases hs
  | some p =>
    have hApprox : Obend.Core.Cubical2LTT.ApproxRun [.affine 1 0 2 1]
        (Int.ofNat (Obend.Core.Cubical2LTT.runStageOne [10]
          (bindByQttStage .one (.litU64 7) (.addU64 (.varOne 0) (.varOne 1)))).toNat) 19 :=
      .cons (y := 19) (by decide) (.nil _)
    have hSyn := surface_qtt_cubical_delegated_synergy h (q := .linear) (by decide)
      .endS 0 1 (.join (.dim0 0) (.dim1 0)) 0 (payloadExpr := .litU64 7)
      (realizer := .addU64 (.varOne 0) (.varOne 1)) rfl rfl [10] [1] [2] [.affine 1 0 2 1] 19 hApprox
    exact ⟨p.1, p.2, rfl, hSyn.2.2.2.2.1, hSyn.2.2.2.2.2.2.2.2.1⟩

/-! ## 4. `FrontEnd` Typed Lock Check & `acceptSyntaxExpr_never_refused` -/

example : FrontEnd.checkLockedImportsTyped
    [⟨"./A.obend", "A", .span 0 18 1⟩] [⟨"./A.obend", "A", .span 0 18 1⟩] = true := by decide

example : FrontEnd.checkLockedImportsTyped
    [⟨"./A.obend", "A", .span 0 18 1⟩] [⟨"./B.obend", "A", .span 0 18 1⟩] = false := by decide

theorem acceptSyntaxExpr_inhabited :
    ∃ acc : FrontEnd.AcceptedSyntaxExpr {} 8 linBoolId linBoolIdTy,
      ∀ limits ticks reason retained,
        Obend.Core.Machine.runBounded limits ticks
          (Obend.Core.Machine.initial acc.elaborated.val.term) ≠ .refused reason retained := by
  cases h : checkSyntaxExpr {} [] 8 linBoolId linBoolIdTy with
  | inl _ =>
    have hs : (checkSyntaxExpr {} [] 8 linBoolId linBoolIdTy).diag? = none := by decide +kernel
    rw [h] at hs; cases hs
  | inr _ =>
    obtain ⟨acc, _, _⟩ := FrontEnd.acceptSyntaxExpr_complete h
    exact ⟨acc, FrontEnd.acceptSyntaxExpr_never_refused acc⟩

/-! ## 5. Mutation-Killing `#tooth` Witnesses & Kernel Axiom Audit -/

#tooth linear_cap_used_exactly_once by mutation ZeroOneOmega.add :=
  fun a b => match a, b with | .zero, g => g | g, .zero => g | .one, .one => .one | _, _ => .omega

#tooth core_grade_occurrence_bounds by mutation CoreQuantityGrade.add :=
  fun a b => match a, b with | .zero, g => g | g, .zero => g | .one, .one => .one | _, _ => .omega

#tooth graded_eraseZero_partialTyping by mutation CoreQuantityGrade.gradeOfNat := fun _ => .omega

#tooth session_step_preserves_duality by mutation Action.co := fun a => a

#tooth wellTyped_dual_endpoints_progress by mutation SessionTy.isEnd := fun _ => false

#tooth session_capTP_settlement by mutation sessionEvents :=
  fun k actions _ => PromiseEvent.allocate k :: actions.map (fun _ => PromiseEvent.deliver k)

#tooth consumeQueue_append by mutation consumeQueue := fun S _ => some S

#tooth effectAllowed_sound by mutation effectAllowed := fun _ _ => some Ty.natural

#tooth lawScope_sound by mutation lawScope := fun _ _ _ => none

#tooth law_obligations_enforce by mutation obligationsHold := fun _ _ _ _ => true

#tooth resolve_sound by mutation resolve := fun _ _ => some 0

#tooth Quantity.fits_qtt_iff by mutation Quantity.toZeroOneOmega := fun _ => .omega

#tooth delegated_channel_subject_reduction by mutation termOcc := fun _ _ => 0

#tooth checkSurface_qtt_grade_bridge by mutation termOcc := fun _ _ => 0

#tooth qtt_erasable_iff_stageZero by mutation qttToStageGrade := fun _ => .one

#tooth bindByQttStage_wellStaged by mutation bindByQttStage := fun _ p r => .letOne p r

#tooth surface_qtt_cubical_delegated_synergy by mutation bindByQttStage := fun _ p r => .letOne p r

#tooth Obend.Spec.FrontEnd.checkLockedImportsTyped_sound by mutation
  Obend.Spec.FrontEnd.checkLockedImportsTyped := fun _ _ => true

#assert_axioms_tree

end Obend.Tests.GradedSessionAndSurfaceElab
