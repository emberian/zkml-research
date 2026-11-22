import Obend.Equiv.LogicalRelationDefs
import Obend.Equiv.LogicalRelation
import Obend.Core.CanonicityDefs
import Obend.Core.Canonicity
import Obend.Equiv.EffectHandlers
import Obend.Spec.Proofs.OpenObjectAlgebra
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/CoreMetatheoryElevationTest.lean` — Verification, `#kind` Representation Independence & `#tooth` Suite

End-to-end inhabitedness witnesses, concrete `#kind "Counter.T"` Reynolds Representation Independence
(Unary Counter `{ count : Nat }` vs Binary Counter `{ half : Nat, odd : Bool }` with `privRow₁ ≠ privRow₂`,
universal polymorphic client `SameRuns`, and non-rigid counterexample), `0`-grade non-interference,
canonicity + `Machine.runBounded` normalization, one-shot algebraic effect handlers, C4 open-object
algebra, 14 `#tooth` mutation kills across all 4 pillars, `#assert_axioms_tree`, and `0` closed-theorem audit.
-/

namespace Obend.Tests.CoreMetatheoryElevationTest

open Obend.Core Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.AliasExposure Obend.Equiv
open Obend.Equiv.LogicalRelation Obend.Core.Canonicity
open Obend.Equiv.EffectHandlers Obend.Spec.Proofs.OpenObjectAlgebra

set_option autoImplicit false

-- ============================================================================
-- 1. Concrete `#kind "Counter.T"` Representation Independence (`privRow₁ ≠ privRow₂`)
-- ============================================================================

def counterKind : Obend.Core.Nominal.KindId := "Counter.T"
def brandVal : Term := .inject counterKind (.record [])
def θ_counter : Assumptions := ⟨[(0, Ty.kinded counterKind .emptyRow)], [0], [0], []⟩

def privRow₁ : Ty := .field "count" .natural .emptyRow
def privRow₂ : Ty := .field "half" .natural (.field "odd" .boolean .emptyRow)

theorem counter_private_layouts_distinct : privRow₁ ≠ privRow₂ := by decide

def counterModSig : Ty :=
  .field "zero" (.variable 0) (.field "read" (.arrow .reusable .unrestricted (.variable 0) .natural) .emptyRow)

def mkUnaryState (n : Nat) : Term := .record [(Obend.Core.Nominal.brandLabel, brandVal), ("count", .nat n)]
def mkBinaryState (h : Nat) (odd : Bool) : Term :=
  .record [(Obend.Core.Nominal.brandLabel, brandVal), ("half", .nat h), ("odd", .boolean odd)]

def binaryDecodeFn : Term :=
  .lam (.lam (.ifBool (.bound 0)
    (.binary .add (.binary .multiply (.nat 2) (.bound 1)) (.nat 1))
    (.binary .multiply (.nat 2) (.bound 1))))

def unaryOps : Term := .record [("zero", mkUnaryState 6), ("read", .lam (.get (.bound 0) "count"))]
def binaryOps : Term := .record [("zero", mkBinaryState 3 false), ("read", .lam (.split (.bound 0) ["half", "odd"] binaryDecodeFn))]

def counterStepRel : StepRel where
  rel _ v₁ v₂ := ∃ h odd, v₁ = mkUnaryState (2 * h + if odd then 1 else 0) ∧ v₂ = mkBinaryState h odd
  val_left := by rintro _ _ _ ⟨_, _, rfl, _⟩; exact .record _
  val_right := by rintro _ _ _ ⟨_, _, _, rfl⟩; exact .record _
  closed_left := by
    rintro _ _ _ ⟨_, _, rfl, _⟩
    refine .record fun p hp => ?_
    rcases List.mem_cons.mp hp with rfl | hp2
    · exact .inject (.record (by intro _ h; cases h))
    · rcases List.mem_cons.mp hp2 with rfl | hp3
      · exact .natural _
      · cases hp3
  closed_right := by
    rintro _ _ _ ⟨_, _, _, rfl⟩
    refine .record fun p hp => ?_
    rcases List.mem_cons.mp hp with rfl | hp2
    · exact .inject (.record (by intro _ h; cases h))
    · rcases List.mem_cons.mp hp2 with rfl | hp3
      · exact .natural _
      · rcases List.mem_cons.mp hp3 with rfl | hp4
        · exact .boolean _
        · cases hp4
  antitone _ h := h

theorem counter_validBrandRel : ValidBrandRel .pure θ_counter 0 counterKind .emptyRow counterStepRel where
  onlyRigid Y hY := by simp [θ_counter] at hY; exact hY
  boundEq := rfl
  brandedRecords := by
    rintro k _ _ ⟨h, odd, rfl, rfl⟩; refine ⟨_, _, rfl, rfl, rfl, rfl, fun nm mTy _ hlk => ?_⟩
    obtain ⟨fl, hfl⟩ := (lookupV_iff θ_counter.bounds .emptyRow nm mTy).mp hlk; cases fl <;> simp [Ty.lookup] at hfl

private theorem kinded_lookup_only_brand {fl : Nat} {nm : String} {m : Ty}
    (h : (Ty.kinded counterKind .emptyRow).lookup θ_counter.bounds fl nm = some m) :
    1 ≤ fl ∧ nm = Obend.Core.Nominal.brandLabel ∧ m = Obend.Core.Nominal.kindTy counterKind := by
  cases fl with
  | zero => simp [Ty.lookup] at h
  | succ f' =>
    simp only [Ty.kinded, Ty.lookup] at h
    by_cases he : Obend.Core.Nominal.brandLabel = nm
    · subst he; simp only [↓reduceIte, Option.some.injEq] at h; exact ⟨by omega, rfl, h.symm⟩
    · simp [he] at h; cases f' <;> simp [Ty.lookup] at h

private theorem mkCounterDischarges (priv : Ty) (extra : Nat)
    (hSh : (Ty.kinded counterKind priv).shareableUnder [] = true)
    (hRow : (Ty.kinded counterKind priv).isRow [] (2 + extra) = true) :
    Obend.Core.Proofs.Templates.Discharges
      (singleTySubst 0 (Ty.kinded counterKind priv)) θ_counter {} extra where
  fixed j hj := by simp [θ_counter] at hj; simp [singleTySubst, hj]
  bounds j hj := by simp [θ_counter] at hj; cases j <;> simp [θ_counter, List.lookup] at hj ⊢
  aliases j hj := by simp [θ_counter] at hj; cases j <;> simp [Assumptions.alias, θ_counter, List.lookup] at hj ⊢
  closed j _ hj h := by simp [θ_counter] at hj; cases j <;> simp [θ_counter, List.lookup] at hj h
  lookup k bd hk hbd fuel nm m hlk := by
    simp [θ_counter] at hk; subst hk; simp [θ_counter] at hbd; subst hbd
    obtain ⟨hfl, rfl, rfl⟩ := kinded_lookup_only_brand hlk
    obtain ⟨f', hf'⟩ : ∃ f', fuel + extra = f' + 1 := ⟨fuel + extra - 1, by omega⟩
    rw [hf']; simp [singleTySubst, Ty.kinded, Ty.lookup, Obend.Core.Nominal.kindTy, Ty.instantiate]
  row k bd hk hbd fuel hrw := by
    simp [θ_counter] at hk; subst hk; simp [θ_counter] at hbd; subst hbd
    cases fuel with
    | zero => simp [Ty.isRow] at hrw
    | succ f1 =>
      cases f1 with
      | zero => simp [Ty.kinded, Ty.isRow] at hrw
      | succ f2 => exact Ty.isRow_mono (by simpa [singleTySubst] using hRow) (by omega)
  shareable j := by
    by_cases hj : j = 0
    · simp [singleTySubst, hj, θ_counter, hSh]
    · simp [singleTySubst, hj, θ_counter, Ty.shareable]
  custody j := by
    by_cases hj : j = 0
    · simpa [singleTySubst, hj] using Ty.bearsCustody_of_shareableUnder hSh
    · simp [singleTySubst, hj]
  pure j := by by_cases hj : j = 0 <;> simp [singleTySubst, hj, Ty.kinded, Ty.isComputation]
  holes _ _ h := by simp [θ_counter] at h

theorem counter_discharges_unary :
    Obend.Core.Proofs.Templates.Discharges (singleTySubst 0 (Ty.kinded counterKind privRow₁)) θ_counter {} 1 :=
  mkCounterDischarges privRow₁ 1 rfl rfl

theorem counter_discharges_binary :
    Obend.Core.Proofs.Templates.Discharges (singleTySubst 0 (Ty.kinded counterKind privRow₂)) θ_counter {} 2 :=
  mkCounterDischarges privRow₂ 2 rfl rfl

private theorem binaryDecode_rest (h : Nat) (odd : Bool) :
    Steps (applyAll binaryDecodeFn [.nat h, .boolean odd]) (.nat (2 * h + if odd then 1 else 0)) := by
  simp only [applyAll, binaryDecodeFn]
  refine .next (.application (.boolean odd) (.beta _ (.nat h))) ?_
  rw [Obend.Equiv.instantiate_eq]; simp only [Term.substitute, liftSubstitution, Obend.Equiv.single, Term.rename]
  refine .next (.beta _ (.boolean odd)) ?_
  rw [Obend.Equiv.instantiate_eq]; simp only [Term.substitute, Obend.Equiv.single]
  cases odd with
  | false => exact .next (.ifFalse _ _) (.next (.primitive .multiply (.nat 2) (.nat h) (.nat (2 * h)) (.natural 2) (.natural h) rfl) (.refl _))
  | true =>
    exact .next (.ifTrue _ _) (.next (.binaryLeft .add (.nat 1)
      (.primitive .multiply (.nat 2) (.nat h) (.nat (2 * h)) (.natural 2) (.natural h) rfl))
      (.next (.primitive .add (.nat (2 * h)) (.nat 1) (.nat (2 * h + 1)) (.natural _) (.natural 1) rfl) (.refl _)))

private theorem binaryDecode_steps (h : Nat) (odd : Bool) :
    Steps (.split (mkBinaryState h odd) ["half", "odd"] binaryDecodeFn) (.nat (2 * h + if odd then 1 else 0)) :=
  .next (.splitRecord _ ["half", "odd"] binaryDecodeFn [.nat h, .boolean odd] rfl) (binaryDecode_rest h odd)

private theorem unaryGet_steps (h : Nat) (odd : Bool) :
    Step (.get (mkUnaryState (2 * h + if odd then 1 else 0)) "count") (.nat (2 * h + if odd then 1 else 0)) :=
  .field _ "count" _ rfl

private theorem binaryDecodeFn_scoped (g : Nat) : Obend.Core.Invariant.Scoped g binaryDecodeFn :=
  .lam (.lam (.ifBool (.bound (by omega))
    (.binary (.binary (.natural 2) (.bound (by omega))) (.natural 1))
    (.binary (.natural 2) (.bound (by omega)))))

private theorem unaryOps_scoped : Obend.Core.Invariant.Scoped 0 unaryOps :=
  .record (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl)
              · exact counterStepRel.closed_left (k := 0) ⟨3, false, rfl, rfl⟩
              · exact .lam (.get (.bound (by omega))))

private theorem binaryOps_scoped : Obend.Core.Invariant.Scoped 0 binaryOps :=
  .record (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl)
              · exact counterStepRel.closed_right (k := 0) ⟨3, false, rfl, rfl⟩
              · exact .lam (.split (.bound (by omega)) (binaryDecodeFn_scoped 1)))

private theorem expose_var0 : expose (baseAssumptions θ_counter) (.variable 0) = .nominal 0 :=
  expose_rigid (baseAssumptions θ_counter) 0 rfl

theorem counter_ops_expRel (k : Nat) :
    ExpRel .pure θ_counter (brandRelEnv 0 counterStepRel) counterModSig k unaryOps binaryOps := by
  have natLitRel : ∀ η' j n, LRApprox .pure θ_counter η' true .natural j (.nat n) (.nat n) := fun _ _ _ =>
    valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead])
  have zeroL : ∀ j, LRApprox .pure θ_counter (brandRelEnv 0 counterStepRel) true (.variable 0) j (mkUnaryState 6) (mkBinaryState 3 false) :=
    fun _ => valApprox_to_expApprox rfl (by unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte]; rw [expose_var0]; simp only [brandRelEnv, ↓reduceIte]; exact ⟨3, false, rfl, rfl⟩)
  have zeroR : ∀ j, LRApprox .pure θ_counter (brandRelEnv 0 counterStepRel).flip true (.variable 0) j (mkBinaryState 3 false) (mkUnaryState 6) :=
    fun _ => valApprox_to_expApprox rfl (by unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte]; rw [expose_var0]; simp only [RelEnv.flip, brandRelEnv, ↓reduceIte]; exact ⟨3, false, rfl, rfl⟩)
  have readL : ∀ j, LRApprox .pure θ_counter (brandRelEnv 0 counterStepRel) true
      (.arrow .reusable .unrestricted (.variable 0) .natural) j
      (.lam (.get (.bound 0) "count")) (.lam (.split (.bound 0) ["half", "odd"] binaryDecodeFn)) := fun _ => by
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    refine ⟨_, _, rfl, rfl, .get (.bound (by omega)), .split (.bound (by omega)) (binaryDecodeFn_scoped 1), fun _ _ a₁ a₂ ha₁ ha₂ harg => ?_⟩
    have haRel := harg.resolve_left (by decide)
    have hid := Obend.Core.TermTraverse.scoped_substitute_identity binaryDecodeFn 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 _).mp (binaryDecodeFn_scoped 0)) (Obend.Equiv.single a₂) (fun _ h => by omega)
    have hinst₁ : instantiate (.get (.bound 0) "count") a₁ = (SourceFrame.field "count").plug a₁ := by
      simp [Obend.Equiv.instantiate_eq, Obend.Equiv.single, SourceFrame.plug]
    have hinst₂ : instantiate (.split (.bound 0) ["half", "odd"] binaryDecodeFn) a₂ = (SourceFrame.split ["half", "odd"] binaryDecodeFn).plug a₂ := by
      simp [Obend.Equiv.instantiate_eq, Term.substitute, Obend.Equiv.single, SourceFrame.plug, hid]
    rw [hinst₁, hinst₂]
    refine expApprox_bind_frame (.field "count") (.split ["half", "odd"] binaryDecodeFn) (by simp) (by simp)
      (.get ha₁) (.split ha₂ (binaryDecodeFn_scoped 0)) rfl haRel fun _ _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte] at hvr; rw [expose_var0] at hvr; simp only [brandRelEnv, ↓reduceIte] at hvr
    obtain ⟨h, odd, rfl, rfl⟩ := hvr
    dsimp only [SourceFrame.plug]
    exact expApprox_step_left_later (.get (counterStepRel.closed_left (k := 0) ⟨h, odd, rfl, rfl⟩))
      (.split (counterStepRel.closed_right (k := 0) ⟨h, odd, rfl, rfl⟩) (binaryDecodeFn_scoped 0))
      (unaryGet_steps h odd) (binaryDecode_steps h odd) (fun j'' _ => natLitRel _ j'' _)
  have readR : ∀ j, LRApprox .pure θ_counter (brandRelEnv 0 counterStepRel).flip true
      (.arrow .reusable .unrestricted (.variable 0) .natural) j
      (.lam (.split (.bound 0) ["half", "odd"] binaryDecodeFn)) (.lam (.get (.bound 0) "count")) := fun _ => by
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    refine ⟨_, _, rfl, rfl, .split (.bound (by omega)) (binaryDecodeFn_scoped 1), .get (.bound (by omega)), fun _ _ a₁ a₂ ha₁ ha₂ harg => ?_⟩
    have haRel := harg.resolve_left (by decide)
    have hid := Obend.Core.TermTraverse.scoped_substitute_identity binaryDecodeFn 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 _).mp (binaryDecodeFn_scoped 0)) (Obend.Equiv.single a₁) (fun _ h => by omega)
    have hinst₁ : instantiate (.split (.bound 0) ["half", "odd"] binaryDecodeFn) a₁ = (SourceFrame.split ["half", "odd"] binaryDecodeFn).plug a₁ := by
      simp [Obend.Equiv.instantiate_eq, Term.substitute, Obend.Equiv.single, SourceFrame.plug, hid]
    have hinst₂ : instantiate (.get (.bound 0) "count") a₂ = (SourceFrame.field "count").plug a₂ := by
      simp [Obend.Equiv.instantiate_eq, Obend.Equiv.single, SourceFrame.plug]
    rw [hinst₁, hinst₂]
    refine expApprox_bind_frame (.split ["half", "odd"] binaryDecodeFn) (.field "count") (by simp) (by simp)
      (.split ha₁ (binaryDecodeFn_scoped 0)) (.get ha₂) rfl haRel fun _ _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte] at hvr; rw [expose_var0] at hvr; simp only [RelEnv.flip, brandRelEnv, ↓reduceIte] at hvr
    obtain ⟨h, odd, rfl, rfl⟩ := hvr
    have sFirst : Step (.split (mkBinaryState h odd) ["half", "odd"] binaryDecodeFn)
        (applyAll binaryDecodeFn [.nat h, .boolean odd]) :=
      .splitRecord _ ["half", "odd"] binaryDecodeFn [.nat h, .boolean odd] rfl
    have sRest := binaryDecode_rest h odd
    have hMidSc : Obend.Core.Invariant.Scoped 0 (applyAll binaryDecodeFn [.nat h, .boolean odd]) :=
      .app (.app (binaryDecodeFn_scoped 0) (.natural h)) (.boolean odd)
    dsimp only [SourceFrame.plug]
    refine expApprox_step_left_later (.split (counterStepRel.closed_right (k := 0) ⟨h, odd, rfl, rfl⟩) (binaryDecodeFn_scoped 0))
      (.get (counterStepRel.closed_left (k := 0) ⟨h, odd, rfl, rfl⟩)) sFirst (steps_one (unaryGet_steps h odd)) fun _ _ => ?_
    rw [lrApprox_exp_pure_eq rfl]
    refine ⟨hMidSc, .natural _, ?_, ?_⟩
    · intro m1 _ _ _ _ hst hy
      obtain ⟨m2, hsN⟩ := steps_iff_stepsN.mp sRest
      obtain ⟨_, hrem⟩ := stepsN_consume_prefix hst hsN (fun _ => value_no_step (.natural _))
      generalize m2 - m1 = d at hrem
      cases hrem with | zero _ => exact yields_not_value hy (.natural _) | step s _ => exact absurd s (yields_no_step hy _)
    · intro m1 _ vf hst hvf
      obtain ⟨m2, hsN⟩ := steps_iff_stepsN.mp sRest
      obtain ⟨_, hrem⟩ := stepsN_consume_prefix hsN hst (fun _ => value_no_step hvf)
      generalize m1 - m2 = d at hrem
      cases hrem with
      | zero _ => exact ⟨_, ⟨.refl _, .natural _⟩, by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead]⟩
      | step s _ => exact absurd s (value_no_step (.natural _))
  have mkDir : ∀ {η'} {fs₁ fs₂ : List (String × Term)},
      Obend.Core.Invariant.Scoped 0 (.record fs₁) → Obend.Core.Invariant.Scoped 0 (.record fs₂) →
      (∀ name mTy, lookupV θ_counter.bounds [] counterModSig name = some mTy →
        ∃ b₁ b₂, fs₁.find? (·.1 == name) = some (name, b₁) ∧ fs₂.find? (·.1 == name) = some (name, b₂) ∧
          ∀ j (_ : j < k), LRApprox .pure θ_counter η' true mTy j b₁ b₂) →
      LRApprox .pure θ_counter η' true counterModSig k (.record fs₁) (.record fs₂) := fun h1 h2 hm =>
    valApprox_to_expApprox rfl (by unfold LRApprox; simp only [counterModSig, Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]; exact ⟨_, _, rfl, rfl, h1, h2, hm⟩)
  dsimp only [unaryOps, binaryOps]
  refine ⟨mkDir unaryOps_scoped binaryOps_scoped fun nm mTy hlk => ?_,
          mkDir binaryOps_scoped unaryOps_scoped fun nm mTy hlk => ?_⟩
  · obtain ⟨fl, hfl⟩ := (lookupV_iff θ_counter.bounds counterModSig nm mTy).mp hlk
    cases fl with
    | zero => simp [Ty.lookup] at hfl
    | succ f1 =>
      by_cases hz : "zero" = nm
      · subst hz; simp [counterModSig, Ty.lookup] at hfl; subst hfl; exact ⟨_, _, rfl, rfl, fun j _ => zeroL j⟩
      · cases f1 with
        | zero => simp [counterModSig, Ty.lookup, hz] at hfl
        | succ f2 =>
          by_cases hr : "read" = nm
          · subst hr; simp [counterModSig, Ty.lookup, hz] at hfl; subst hfl; exact ⟨_, _, rfl, rfl, fun j _ => readL j⟩
          · cases f2 <;> simp [counterModSig, Ty.lookup, hz, hr] at hfl
  · obtain ⟨fl, hfl⟩ := (lookupV_iff θ_counter.bounds counterModSig nm mTy).mp hlk
    cases fl with
    | zero => simp [Ty.lookup] at hfl
    | succ f1 =>
      by_cases hz : "zero" = nm
      · subst hz; simp [counterModSig, Ty.lookup] at hfl; subst hfl; exact ⟨_, _, rfl, rfl, fun j _ => zeroR j⟩
      · cases f1 with
        | zero => simp [counterModSig, Ty.lookup, hz] at hfl
        | succ f2 =>
          by_cases hr : "read" = nm
          · subst hr; simp [counterModSig, Ty.lookup, hz] at hfl; subst hfl; exact ⟨_, _, rfl, rfl, fun j _ => readR j⟩
          · cases f2 <;> simp [counterModSig, Ty.lookup, hz, hr] at hfl

/-- **Concrete `#kind "Counter.T"` Universal Polymorphic Client Theorem**. -/
theorem counter_representation_independence_all_clients {client : Term} {u : Uses}
    (hTyped : PartialTyping θ_counter [⟨counterModSig, .unrestricted⟩] client .natural u)
    (hSafe : safeUses [⟨counterModSig, .unrestricted⟩] u = true)
    (hPure : Obend.Equiv.observes client = false) :
    SameRuns (instantiate client unaryOps) (instantiate client binaryOps) :=
  (kind_brand_representation_independence rfl counter_validBrandRel
    counter_discharges_unary counter_discharges_binary rfl rfl
    unaryOps_scoped binaryOps_scoped (fun _ => counter_ops_expRel)
    hTyped hSafe (fun _ => hPure) (.inl rfl)).2.2

def polyReadZeroClient : Term := .app (.get (.bound 0) "read") (.get (.bound 0) "zero")

example : SameRuns (instantiate polyReadZeroClient unaryOps) (instantiate polyReadZeroClient binaryOps) := by
  have hMod0 : PartialTyping θ_counter [⟨counterModSig, .unrestricted⟩] (.bound 0) counterModSig [1] :=
    .bound (binding := ⟨counterModSig, .unrestricted⟩) rfl
  have hClient : PartialTyping θ_counter [⟨counterModSig, .unrestricted⟩] polyReadZeroClient .natural [2] :=
    .application (.get (fuel := 2) hMod0 rfl rfl) (.get (fuel := 1) hMod0 rfl rfl) rfl rfl rfl
  exact counter_representation_independence_all_clients hClient rfl (by simp [polyReadZeroClient, Obend.Equiv.observes])

/-- **Non-Rigid Counterexample**: raw `.get (.get (.bound 0) "zero") "count"` distinguishes the two layouts! -/
def rawCountProbe : Term := .get (.get (.bound 0) "zero") "count"

theorem non_rigid_probe_breaks_sameRuns :
    ¬ SameRuns (instantiate rawCountProbe unaryOps) (instantiate rawCountProbe binaryOps) := by
  intro hSame
  have hEval₁ : Evaluates (instantiate rawCountProbe unaryOps) (.nat 6) := by
    simp only [rawCountProbe, Obend.Equiv.instantiate_eq, Term.substitute, Obend.Equiv.single]
    exact ⟨.next (.target "count" (.field _ "zero" _ rfl)) (.next (.field _ "count" _ rfl) (.refl _)), .natural 6⟩
  obtain ⟨v₂, hSteps₂, hv₂⟩ := hSame.2.1 ⟨.nat 6, hEval₁⟩
  simp only [rawCountProbe, Obend.Equiv.instantiate_eq, Term.substitute, Obend.Equiv.single] at hSteps₂
  cases hSteps₂ with
  | refl => cases hv₂
  | @next _ _ _ s₁ r₁ =>
    cases s₁ with
    | target _ s₀ =>
      cases s₀ with
      | target _ sb => cases sb
      | field _ _ _ hf =>
        simp only [List.find?, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨_, rfl⟩ := hf
        cases r₁ with
        | refl => cases hv₂
        | next s₂ _ =>
          cases s₂ with
          | field _ _ _ hf2 => simp [Obend.Core.Brand.brandLabel] at hf2
          | target _ sb2 => exact value_no_step (.record _) sb2

-- ============================================================================
-- 2. Inhabitedness Witnesses (`0`-Grade Non-Interference, Canonicity, Handlers, C4)
-- ============================================================================

example : TypedCtxEquiv .pure {} [] (instantiate (.nat 42) (.nat 0)) (instantiate (.nat 42) (.nat 999)) .natural :=
  ((erased_relational_noninterference (θ := {}) (Γ := []) (A := .natural) rfl
    (.natural [⟨.natural, .erased⟩] 42) rfl (fun _ => by simp [Obend.Equiv.observes]) (.natural 0) (.natural 999)).2 rfl).2

example : ∃ (n : Nat) (limits₀ : Machine.Limits) (ticks₀ : Nat),
    Evaluates (.binary .add (.nat 19) (.nat 23)) (.nat n) ∧
    ∀ limits ticks, Obend.Core.Proofs.GroundExecution.Covers limits limits₀ → ticks₀ ≤ ticks →
      ∃ st, Machine.runBounded limits ticks (Machine.initial (.binary .add (.nat 19) (.nat 23))) =
        Machine.Outcome.finished (.natural n) st :=
  total_nat_machine_terminates (θ := {}) rfl rfl (.binary (primitive := .add) rfl (.natural [] 19) (.natural [] 23))

def idCompHandler : TypedHandler {} [] .linear (.variant (.field "ask" .emptyRow .emptyRow))
    .natural (.variant (.field "ask" .emptyRow .emptyRow)) .natural .natural .natural where
  oneShot := .inl rfl
  planValid := rfl
  respData := rfl
  resPure := rfl
  outPure := rfl
  retQty := .unrestricted
  opPlanQty := .unrestricted
  retBody := .done (.bound 0)
  opBody := .app (.bound 0) (.nat 7)
  retUses := [1]
  opUses := [1, 0]
  retTyped := .done (.bound (binding := ⟨.natural, .unrestricted⟩) rfl) rfl
  retSafe := rfl
  retValid := rfl
  retFits := rfl
  opTyped := .application (.bound (binding := ⟨ResumpTy .natural _ .natural .natural, .linear⟩) rfl)
    (.natural _ 7) rfl rfl rfl
  opSafe := rfl
  opValidP := rfl
  opFitsK := rfl
  opFitsP := rfl

example : PartialTyping {} [] (compileDeep idCompHandler.retFn idCompHandler.opFn (.done (.nat 5)))
    (.computation (.variant (.field "ask" .emptyRow .emptyRow)) .natural .natural) [] :=
  compileDeep_preserves_typing idCompHandler rfl (.done rfl rfl (.natural [] 5))

example : Evaluates (.get (.fix (compileAugmentStack "score" .add [.nat 10, .nat 20, .nat 30, .nat 40]) (.record [])) "score")
    (.nat 100) :=
  (augment_c4_monoid_fold "score" ["D", "B", "C", "A"]
    (fun s => if s == "D" then 10 else if s == "B" then 20 else if s == "C" then 30 else 40)).1

-- ============================================================================
-- 3. Semantically Falsifying `#tooth` Mutation Kills Across All 4 Pillars (14 Kills)
-- ============================================================================

#tooth Obend.Equiv.LogicalRelation.fundamental_lemma by mutation
  Obend.Equiv.LogicalRelation.RelEnv.flip := fun η => η

#tooth Obend.Equiv.LogicalRelation.lr_sound_typedCtxEquiv by mutation
  Obend.Equiv.LogicalRelation.TypedCtxEquiv := fun _ _ _ t₁ t₂ _ => t₁ = t₂

#tooth Obend.Equiv.LogicalRelation.erased_relational_noninterference by mutation
  Obend.Equiv.LogicalRelation.OpenRel := fun _ _ _ _ t₁ t₂ _ => t₁ = t₂

#tooth Obend.Equiv.LogicalRelation.kind_brand_representation_independence by mutation
  Obend.Equiv.LogicalRelation.consSubst := fun _ _ _ => .bound 7

#tooth Obend.Core.Canonicity.total_canonicity by mutation
  Obend.Core.Canonicity.IsTotalTerm := fun _ => true

#tooth Obend.Core.Canonicity.total_ground_machine_terminates by mutation
  Obend.Core.Canonicity.PositiveBounds := fun _ => true

#tooth Obend.Core.Canonicity.lawCompile_emits_totalTerm by mutation
  Obend.Core.Canonicity.isTotalFields := fun _ => false

#tooth Obend.Equiv.EffectHandlers.reifyResumption_apply_steps by mutation
  Obend.Equiv.EffectHandlers.reifyResumption := fun _ => .lam (.nat 0)

#tooth Obend.Equiv.EffectHandlers.compileDeep_preserves_typing by mutation
  Obend.Equiv.EffectHandlers.compileDeep := fun _ _ _ => .nat 0

#tooth Obend.Equiv.EffectHandlers.handler_return_law by mutation
  Obend.Equiv.EffectHandlers.compileDeepWith := fun op k _ => .app op k

#tooth Obend.Equiv.EffectHandlers.handler_vertical_fusion_iequiv by mutation
  Obend.Equiv.EffectHandlers.fuseOp := fun _ op2 => op2

#tooth Obend.Spec.Proofs.OpenObjectAlgebra.mix_idLayer_unit_iequiv by mutation
  Obend.Spec.Proofs.OpenObjectAlgebra.idLayer := .lam (.lam (.nat 0))

#tooth Obend.Spec.Proofs.OpenObjectAlgebra.around_intercepts_subclass_override by mutation
  Obend.Spec.Proofs.OpenObjectAlgebra.compileTwoBandStack := fun mro =>
    Obend.Spec.Proofs.OpenObjectAlgebra.foldMixStack (mro.reverse.filterMap fun (prim, _) =>
      if prim.isEmpty then none else some (Obend.Spec.Proofs.OpenObjectAlgebra.mkExtLayer prim))

#tooth Obend.Spec.Proofs.OpenObjectAlgebra.augment_c4_monoid_fold by mutation
  Obend.Spec.Proofs.OpenObjectAlgebra.AugmentQual.seedTerm := fun _ => .nat 99

-- ============================================================================
-- 4. `#assert_axioms_tree` + Strict `0 sorryAx` & `0` Closed-Theorem Audit
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targetMods : List Name :=
    [ `Obend.Equiv.LogicalRelationDefs, `Obend.Equiv.LogicalRelation
    , `Obend.Core.CanonicityDefs, `Obend.Core.Canonicity
    , `Obend.Equiv.EffectHandlers, `Obend.Spec.Proofs.OpenObjectAlgebra ]
  let mut checkedCount : Nat := 0
  let mut universalCount : Nat := 0
  let mut closedOffenders : Array Name := #[]
  for (cName, info) in env.constants.map₁.toList do
    let some modIdx := env.getModuleIdxFor? cName | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless targetMods.contains modName do continue
    checkedCount := checkedCount + 1
    let axs ← liftCoreM <| collectAxioms cName
    for ax in axs do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError m!"Disallowed axiom {ax} found in {cName}"
    if let .thmInfo _ := info then
      if !cName.isInternal && !cName.isInternalDetail &&
         !cName.components.any (fun c => c == `_tooth || c == `_native) &&
         cName.components.getLast? != some `sizeOf_spec then
        if ← liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
          closedOffenders := closedOffenders.push cName
        else
          universalCount := universalCount + 1
  if checkedCount == 0 then
    throwError "Zero constants inspected across Core Metatheory Elevation modules!"
  unless closedOffenders.isEmpty do
    throwError m!"Closed theorems found (must be 0): {closedOffenders.toList}"
  if universalCount == 0 then
    throwError "Zero universal theorems reported!"
  logInfo m!"Core Metatheory Elevation verified: {checkedCount} constants across all 6 library modules (0 sorryAx, 0 custom axioms, 0 native_decide), {universalCount} universal theorems, 0 closed theorems, 14 #tooth kills"

end Obend.Tests.CoreMetatheoryElevationTest
