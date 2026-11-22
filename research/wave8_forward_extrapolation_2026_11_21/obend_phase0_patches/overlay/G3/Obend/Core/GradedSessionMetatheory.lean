module
/-
# Obend.Core.GradedSessionMetatheory — session-typed channels welded onto Core4 & CapTP

Welds `ZeroOneOmega` (`0, 1, ω`) + `CoreQuantityGrade` (`0, 1, α, ω`) Quantitative Type Theory,
binary session types (`SessionTy`, `Branches`, `SStep`, `Trace`), synchronous dual coroutine
rendezvous (`CoreSessionSoup` over `Obend.Core.Term.Yields` & multi-turn `RendezvousCoreTrace`),
and asynchronous promise-pipelined FIFO queues (`AsyncCapTPSession` +
`async_captp_session_progress_and_fidelity` over `Obend.Polis.CapTP`) directly onto real
`Obend.Core.Term.Term` and `Obend.Core.Ty.Ty`, with zero shadow `GTerm`/`GType` ASTs.
-/
public import Obend.Core.GradedCoreWeldDefs
public import Obend.Core.GradedCoreWeld
public import Obend.Polis.CapTP
import all Obend.Core.GradedCoreWeldDefs
import all Obend.Core.GradedCoreWeld
import all Obend.Polis.CapTP

public section
namespace Obend.Core.GradedSessionMetatheory
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
open Obend.Polis.CapTP
set_option autoImplicit false

local infixl:65 " ⊞ " => ResourceRig.add
local infixl:70 " ⊠ " => ResourceRig.mul
local infix:50 " ⊑ " => ResourceRig.le
local notation "𝟘" => ResourceRig.zero
local notation "𝟙" => ResourceRig.one

/-! ## Classical 3-point QTT rig `ZeroOneOmega` (`0, 1, ω`) & Linear Capability Conservation -/

inductive ZeroOneOmega where
  | zero | one | omega
  deriving DecidableEq, Repr

@[expose] def ZeroOneOmega.add : ZeroOneOmega → ZeroOneOmega → ZeroOneOmega
  | .zero, g => g
  | .one, .zero => .one
  | .one, .one => .omega
  | .one, .omega => .omega
  | .omega, _ => .omega

@[expose] def ZeroOneOmega.mul : ZeroOneOmega → ZeroOneOmega → ZeroOneOmega
  | .zero, _ => .zero
  | .one, g => g
  | .omega, .zero => .zero
  | .omega, .one => .omega
  | .omega, .omega => .omega

@[expose] def ZeroOneOmega.le (a b : ZeroOneOmega) : Prop := a = b ∨ b = .omega

instance (a b : ZeroOneOmega) : Decidable (ZeroOneOmega.le a b) :=
  inferInstanceAs (Decidable (a = b ∨ b = .omega))

instance : ResourceRig ZeroOneOmega where
  zero := .zero
  one := .one
  add := ZeroOneOmega.add
  mul := ZeroOneOmega.mul
  le := ZeroOneOmega.le
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; rfl
  zero_mul := by intro a; rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  le_refl := by intro a; exact .inl rfl
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  add_le_add := by intro a a' b b'; cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  mul_le_mul := by intro a a' b b'; cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  add_eq_zero := by intro a b; cases a <;> cases b <;> decide
  mul_eq_zero := by intro a b; cases a <;> cases b <;> decide
  le_zero := by intro a; cases a <;> decide
  one_ne_zero := by decide

@[simp] private theorem ZeroOneOmega.rig_zero : (ResourceRig.zero : ZeroOneOmega) = .zero := rfl
@[simp] private theorem ZeroOneOmega.rig_one : (ResourceRig.one : ZeroOneOmega) = .one := rfl
@[simp] theorem ZeroOneOmega.rig_add (a b : ZeroOneOmega) : ResourceRig.add a b = a.add b := rfl
@[simp] theorem ZeroOneOmega.rig_mul (a b : ZeroOneOmega) : ResourceRig.mul a b = a.mul b := rfl
@[simp] theorem ZeroOneOmega.rig_le (a b : ZeroOneOmega) : ResourceRig.le a b ↔ a.le b := by
  cases a <;> exact ⟨id, id⟩

theorem ZeroOneOmega.weakenable_iff (g : ZeroOneOmega) :
    ZeroOneOmega.le .zero g ↔ g = .zero ∨ g = .omega := by cases g <;> decide

theorem ZeroOneOmega.contractible_iff (g : ZeroOneOmega) :
    ZeroOneOmega.le (g.add g) g ↔ g = .zero ∨ g = .omega := by cases g <;> decide

theorem ZeroOneOmega.linear_split (a b : ZeroOneOmega) :
    a.add b = .one ↔ (a = .one ∧ b = .zero) ∨ (a = .zero ∧ b = .one) := by
  cases a <;> cases b <;> decide

theorem ZeroOneOmega.le_one (g : ZeroOneOmega) : ZeroOneOmega.le g .one ↔ g = .one := by
  cases g <;> decide

def ZeroOneOmega.toQuantity : ZeroOneOmega → Quantity
  | .zero => .erased
  | .one => .linear
  | .omega => .unrestricted

instance : CoreGradeBridge ZeroOneOmega where
  gradeOf
    | .erased => .zero
    | .linear => .one
    | .affine | .unrestricted => .omega

theorem linear_cap_used_exactly_once {Γ : List Ty} {t tₑ : Term}
    {A : Ty} {U : Usage ZeroOneOmega} (h : CoreGradedHasTy ZeroOneOmega Γ t A U tₑ) :
    ∀ k, (U k = .zero → termOcc k tₑ = 0) ∧ (U k = .one → termOcc k tₑ = 1) := by
  induction h with
  | @var _ i _ _ =>
    intro k
    by_cases e : i = k
    · subst e; simp [Usage.single, termOcc]
    · have eki : ¬ k = i := fun h => e h.symm
      simp [Usage.single, termOcc, e, eki]
  | unit => intro k; simp [Usage.zero, termOcc, fieldsOcc]
  | nat | bool | label => intro k; simp [Usage.zero, termOcc]
  | lam _ _ ih => intro k; exact ih (k + 1)
  | @app _ _ q _ _ _ _ fₑ aₑ U V _ _ ihf iha =>
    intro k; have hf := ihf k; have ha := iha k
    simp only [Usage.add, Usage.scale, ZeroOneOmega.rig_add, ZeroOneOmega.rig_mul]
    generalize CoreGradeBridge.gradeOf (R := ZeroOneOmega) q = π
    generalize U k = u at hf ⊢; generalize V k = v at ha ⊢
    cases π <;> cases u <;> cases v <;>
      simp_all [ZeroOneOmega.add, ZeroOneOmega.mul, erasable, termOcc, fieldsOcc]
  | @binary _ _ _ _ _ _ lₑ rₑ U V _ _ _ ihl ihr =>
    intro k; have hl := ihl k; have hr := ihr k
    simp only [Usage.add, termOcc, ZeroOneOmega.rig_add]
    generalize U k = u at hl ⊢; generalize V k = v at hr ⊢
    cases u <;> cases v <;> simp_all [ZeroOneOmega.add]
  | @ite _ _ _ _ _ cₑ tₑ eₑ U V _ _ _ ihc iht ihe =>
    intro k; have hc := ihc k; have ht := iht k; have he := ihe k
    simp only [Usage.add, termOcc, ZeroOneOmega.rig_add]
    generalize U k = u at hc ⊢; generalize V k = v at ht he ⊢
    cases u <;> cases v <;> simp_all [ZeroOneOmega.add] <;> omega
  | @pair _ q _ _ _ _ aₑ bₑ U V _ _ ihb iha =>
    intro k; have hb := ihb k; have ha := iha k
    simp only [Usage.add, Usage.scale, ZeroOneOmega.rig_add, ZeroOneOmega.rig_mul]
    generalize CoreGradeBridge.gradeOf (R := ZeroOneOmega) q = π
    generalize U k = u at hb ⊢; generalize V k = v at ha ⊢
    cases π <;> cases u <;> cases v <;>
      simp_all [ZeroOneOmega.add, ZeroOneOmega.mul, erasable, termOcc, fieldsOcc]
  | @letPair _ _ _ _ _ _ _ fₑ pₑ U V _ _ _ ihf ihp =>
    intro k; have hf := ihf k; have hp := ihp k
    simp only [Usage.add, termOcc, ZeroOneOmega.rig_add]
    generalize U k = u at hf ⊢; generalize V k = v at hp ⊢
    cases u <;> cases v <;> simp_all [ZeroOneOmega.add] <;> omega
  | inject _ _ _ ih | perform _ _ _ ih => exact ih
  | @sub _ _ tₑ _ U U' _ relaxed ih =>
    intro k; have hk := ih k
    have below : (U k).le (U' k) := (ZeroOneOmega.rig_le _ _).mp (relaxed k)
    generalize U k = u at hk below; generalize U' k = u' at below ⊢
    cases u <;> cases u' <;> simp_all [ZeroOneOmega.le]

theorem binder_discipline {Γ : List Ty} {b tₑ : Term}
    {T : Ty} {U : Usage ZeroOneOmega}
    (h : CoreGradedHasTy ZeroOneOmega Γ (.lam b) T U tₑ) :
    ∃ reuse q A B bₑ, T = .arrow reuse q A B ∧ tₑ = .lam bₑ ∧
      (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q = .one → termOcc 0 bₑ = 1) ∧
      (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q = .zero → termOcc 0 bₑ = 0) := by
  obtain ⟨reuse, q, A, B, bₑ, W, eT, eE, body, fits, _⟩ := h.lam_inv
  have exact := linear_cap_used_exactly_once body 0
  have below : (W 0).le (CoreGradeBridge.gradeOf q) := (ZeroOneOmega.rig_le _ _).mp fits
  refine ⟨reuse, q, A, B, bₑ, eT, eE, ?_⟩
  generalize CoreGradeBridge.gradeOf (R := ZeroOneOmega) q = π at below ⊢
  generalize W 0 = w at exact below
  cases π <;> cases w <;> simp_all [ZeroOneOmega.le]

/-- **Apex Theorem (`qtt_step_preserves_typing_and_linear_caps`).**
    Stepping a typed Core4 program preserves its `CoreGradedHasTy` derivation, steps its
    zero-erased runtime term in lockstep, and conserves exact single-use linear capabilities. -/
theorem qtt_step_preserves_typing_and_linear_caps {Γ : List Ty}
    {t t' tₑ : Term} {A : Ty} {U : Usage ZeroOneOmega}
    (h : CoreGradedHasTy ZeroOneOmega Γ t A U tₑ) (s : Step t t') :
    ∃ tₑ', Step tₑ tₑ' ∧ CoreGradedHasTy ZeroOneOmega Γ t' A U tₑ' ∧
      ∀ k, U k = .one → termOcc k tₑ = 1 ∧ termOcc k tₑ' = 1 := by
  obtain ⟨tₑ', sₑ, h'⟩ := h.step s
  exact ⟨tₑ', sₑ, h', fun k hk =>
    ⟨(linear_cap_used_exactly_once h k).2 hk, (linear_cap_used_exactly_once h' k).2 hk⟩⟩

theorem qtt_steps_preserve_linear_caps {Γ : List Ty}
    {t t' tₑ : Term} {A : Ty} {U : Usage ZeroOneOmega}
    (h : CoreGradedHasTy ZeroOneOmega Γ t A U tₑ) (s : Steps t t') :
    ∃ tₑ', Steps tₑ tₑ' ∧ CoreGradedHasTy ZeroOneOmega Γ t' A U tₑ' ∧
      ∀ k, U k = .one → termOcc k tₑ' = 1 := by
  obtain ⟨tₑ', sₑ, h'⟩ := qtt_zero_grade_erasure_sound h s
  exact ⟨tₑ', sₑ, h', fun k hk => (linear_cap_used_exactly_once h' k).2 hk⟩

/-! ## Binary session types over real `Obend.Core.Ty.Ty` payloads -/

mutual
/-- Binary session protocol types whose message payloads are real `Obend.Core.Ty.Ty` types. -/
inductive SessionTy (R : Type) where
  | endS
  | send (q : R) (payload : Ty) (cont : SessionTy R)
  | recv (q : R) (payload : Ty) (cont : SessionTy R)
  | offer (branches : Branches R)
  | select (branches : Branches R)
/-- Labelled branches of an internal (`select`) or external (`offer`) choice. -/
inductive Branches (R : Type) where
  | nil
  | cons (label : String) (cont : SessionTy R) (rest : Branches R)
end

deriving instance DecidableEq, Repr for SessionTy, Branches

mutual
def SessionTy.toCoreTy {R : Type} (chanId : Nat) : SessionTy R → Ty
  | .endS => .custody chanId
  | .send _ payload cont =>
    .computation (.variant (.field "send" payload .emptyRow)) .emptyRow (cont.toCoreTy chanId)
  | .recv _ payload cont =>
    .computation (.variant (.field "recv" .emptyRow .emptyRow)) payload (cont.toCoreTy chanId)
  | .offer B =>
    .computation (.variant (.field "offer" .emptyRow .emptyRow))
      (.variant B.toLabelRow) (.variant (B.toCoreRow chanId))
  | .select B =>
    .computation (.variant (.field "select" .label .emptyRow))
      .emptyRow (.variant (B.toCoreRow chanId))

def Branches.toCoreRow {R : Type} (chanId : Nat) : Branches R → Ty
  | .nil => .emptyRow
  | .cons l S B => .field l (S.toCoreTy chanId) (B.toCoreRow chanId)

def Branches.toLabelRow {R : Type} : Branches R → Ty
  | .nil => .emptyRow
  | .cons l _ B => .field l .emptyRow B.toLabelRow
end

abbrev chanTy (chanId : Nat) : Ty := .custody chanId

section Sessions
variable {R : Type}

mutual
def SessionTy.dual : SessionTy R → SessionTy R
  | .endS => .endS
  | .send q T S => .recv q T S.dual
  | .recv q T S => .send q T S.dual
  | .offer B => .select B.dual
  | .select B => .offer B.dual

def Branches.dual : Branches R → Branches R
  | .nil => .nil
  | .cons l S B => .cons l S.dual B.dual
end

mutual
theorem SessionTy.dual_dual : ∀ S : SessionTy R, S.dual.dual = S
  | .endS => by simp only [SessionTy.dual]
  | .send _ _ S => by simp only [SessionTy.dual, SessionTy.dual_dual S]
  | .recv _ _ S => by simp only [SessionTy.dual, SessionTy.dual_dual S]
  | .offer B => by simp only [SessionTy.dual, Branches.dual_dual B]
  | .select B => by simp only [SessionTy.dual, Branches.dual_dual B]

theorem Branches.dual_dual : ∀ B : Branches R, B.dual.dual = B
  | .nil => by simp only [Branches.dual]
  | .cons _ S B => by simp only [Branches.dual, SessionTy.dual_dual S, Branches.dual_dual B]
end

@[expose] def SessionTy.isEnd : SessionTy R → Bool
  | .endS => true
  | _ => false

theorem SessionTy.isEnd_dual (S : SessionTy R) : S.dual.isEnd = S.isEnd := by
  cases S <;> simp only [SessionTy.dual, SessionTy.isEnd]

@[expose] def Branches.find : Branches R → String → Option (SessionTy R)
  | .nil, _ => none
  | .cons l S B, x => if l = x then some S else B.find x

theorem Branches.find_dual : ∀ (B : Branches R) (x : String) (S : SessionTy R),
    B.find x = some S → B.dual.find x = some S.dual
  | .nil, _, _, h => by simp [Branches.find] at h
  | .cons l _ B, x, S, h => by
    simp only [Branches.find] at h; simp only [Branches.dual, Branches.find]
    by_cases hl : l = x
    · simp only [hl, ↓reduceIte, Option.some.injEq] at h ⊢; rw [h]
    · simp only [hl, ↓reduceIte] at h ⊢; exact Branches.find_dual B x S h

mutual
def SessionTy.WellFormed : SessionTy R → Prop
  | .endS => True
  | .send _ _ S => S.WellFormed
  | .recv _ _ S => S.WellFormed
  | .offer B => B ≠ .nil ∧ B.WellFormed
  | .select B => B ≠ .nil ∧ B.WellFormed

def Branches.WellFormed : Branches R → Prop
  | .nil => True
  | .cons _ S B => S.WellFormed ∧ B.WellFormed
end

mutual
theorem SessionTy.wellFormed_dual : ∀ (S : SessionTy R), S.WellFormed → S.dual.WellFormed
  | .endS, _ => trivial
  | .send _ _ S, wf => SessionTy.wellFormed_dual S wf
  | .recv _ _ S, wf => SessionTy.wellFormed_dual S wf
  | .offer B, ⟨hne, wfB⟩ =>
    ⟨(by intro h; cases B with | nil => exact hne rfl | cons _ _ _ => cases h),
     Branches.wellFormed_dual B wfB⟩
  | .select B, ⟨hne, wfB⟩ =>
    ⟨(by intro h; cases B with | nil => exact hne rfl | cons _ _ _ => cases h),
     Branches.wellFormed_dual B wfB⟩
  termination_by structural S _ => S

theorem Branches.wellFormed_dual : ∀ (B : Branches R), B.WellFormed → B.dual.WellFormed
  | .nil, _ => trivial
  | .cons _ S B, ⟨wfS, wfB⟩ => ⟨SessionTy.wellFormed_dual S wfS, Branches.wellFormed_dual B wfB⟩
  termination_by structural B _ => B
end

theorem Branches.find_wellFormed : ∀ (B : Branches R) (x : String) (S : SessionTy R),
    B.WellFormed → B.find x = some S → S.WellFormed
  | .nil, _, _, _, h => by simp [Branches.find] at h
  | .cons l _ B, x, S, wf, h => by
    simp only [Branches.WellFormed] at wf; simp only [Branches.find] at h
    by_cases hl : l = x
    · simp only [hl, ↓reduceIte, Option.some.injEq] at h; rw [← h]; exact wf.1
    · simp only [hl, ↓reduceIte] at h; exact Branches.find_wellFormed B x S wf.2 h

inductive Action (R : Type) where
  | send (q : R) (payload : Ty)
  | recv (q : R) (payload : Ty)
  | select (label : String)
  | offer (label : String)
  deriving DecidableEq, Repr

@[expose] def Action.co : Action R → Action R
  | .send q T => .recv q T
  | .recv q T => .send q T
  | .select l => .offer l
  | .offer l => .select l

inductive SStep : SessionTy R → Action R → SessionTy R → Prop where
  | send {q : R} {T : Ty} {S : SessionTy R} : SStep (.send q T S) (.send q T) S
  | recv {q : R} {T : Ty} {S : SessionTy R} : SStep (.recv q T S) (.recv q T) S
  | select {B : Branches R} {l : String} {S : SessionTy R} :
      B.find l = some S → SStep (.select B) (.select l) S
  | offer {B : Branches R} {l : String} {S : SessionTy R} :
      B.find l = some S → SStep (.offer B) (.offer l) S

theorem SStep.deterministic {S S₁ S₂ : SessionTy R} {a : Action R}
    (h₁ : SStep S a S₁) (h₂ : SStep S a S₂) : S₁ = S₂ := by
  cases h₁ with
  | send => cases h₂; rfl
  | recv => cases h₂; rfl
  | select f₁ => cases h₂ with | select f₂ => exact Option.some.inj (f₁.symm.trans f₂)
  | offer f₁ => cases h₂ with | offer f₂ => exact Option.some.inj (f₁.symm.trans f₂)

theorem SStep.dual {S S' : SessionTy R} {a : Action R} (h : SStep S a S') :
    SStep S.dual a.co S'.dual := by
  cases h with
  | send => simp only [SessionTy.dual, Action.co]; exact .recv
  | recv => simp only [SessionTy.dual, Action.co]; exact .send
  | select f => simp only [SessionTy.dual, Action.co]; exact .offer (Branches.find_dual _ _ _ f)
  | offer f => simp only [SessionTy.dual, Action.co]; exact .select (Branches.find_dual _ _ _ f)

theorem SStep.wellFormed {S S' : SessionTy R} {a : Action R} (h : SStep S a S')
    (wf : S.WellFormed) : S'.WellFormed := by
  cases h with
  | send => simpa only [SessionTy.WellFormed] using wf
  | recv => simpa only [SessionTy.WellFormed] using wf
  | select f => simp only [SessionTy.WellFormed] at wf; exact Branches.find_wellFormed _ _ _ wf.2 f
  | offer f => simp only [SessionTy.WellFormed] at wf; exact Branches.find_wellFormed _ _ _ wf.2 f

theorem session_step_preserves_duality {S T S' T' : SessionTy R} {a : Action R}
    (linked : T = S.dual) (ours : SStep S a S') (theirs : SStep T a.co T') : T' = S'.dual := by
  subst linked; exact SStep.deterministic theirs ours.dual

theorem session_send_payload_agrees {S S' S'' : SessionTy R} {q q' : R} {T T' : Ty}
    (ours : SStep S (.send q T) S') (theirs : SStep S.dual (.recv q' T') S'') : T' = T := by
  cases ours; simp only [SessionTy.dual] at theirs; cases theirs; rfl

theorem SessionTy.canStep : ∀ (S : SessionTy R), S.WellFormed →
    S.isEnd = true ∨ ∃ a S', SStep S a S'
  | .endS, _ => .inl rfl
  | .send q T S, _ => .inr ⟨.send q T, S, .send⟩
  | .recv q T S, _ => .inr ⟨.recv q T, S, .recv⟩
  | .offer .nil, wf | .select .nil, wf => by simp [SessionTy.WellFormed] at wf
  | .offer (.cons l S _), _ => .inr ⟨.offer l, S, .offer (by simp [Branches.find])⟩
  | .select (.cons l S _), _ => .inr ⟨.select l, S, .select (by simp [Branches.find])⟩

theorem wellTyped_dual_endpoints_progress {S T : SessionTy R} (wf : S.WellFormed)
    (linked : T = S.dual) :
    (S.isEnd = true ∧ T.isEnd = true) ∨
      ∃ a S' T', SStep S a S' ∧ SStep T a.co T' ∧ T' = S'.dual := by
  subst linked
  rcases SessionTy.canStep S wf with ended | ⟨a, S', step⟩
  · exact .inl ⟨ended, by rw [SessionTy.isEnd_dual]; exact ended⟩
  · exact .inr ⟨a, S', S'.dual, step, step.dual, rfl⟩

inductive Trace : SessionTy R → List (Action R) → SessionTy R → Prop where
  | done (S : SessionTy R) : Trace S [] S
  | step {S S' S'' : SessionTy R} {a : Action R} {rest : List (Action R)} :
      SStep S a S' → Trace S' rest S'' → Trace S (a :: rest) S''

theorem Trace.dual {S S' : SessionTy R} {actions : List (Action R)} (h : Trace S actions S') :
    Trace S.dual (actions.map Action.co) S'.dual := by
  induction h with | done _ => exact .done _ | step s _ ih => exact .step s.dual ih

theorem Trace.deterministic {S S₁ S₂ : SessionTy R} {actions : List (Action R)}
    (h₁ : Trace S actions S₁) (h₂ : Trace S actions S₂) : S₁ = S₂ := by
  induction h₁ with
  | done _ => cases h₂; rfl
  | step s _ ih => cases h₂ with | step s' rest => cases SStep.deterministic s s'; exact ih rest

theorem Trace.wellFormed {S S' : SessionTy R} {actions : List (Action R)} (h : Trace S actions S')
    (wf : S.WellFormed) : S'.WellFormed := by
  induction h with | done _ => exact wf | step s _ ih => exact ih (s.wellFormed wf)

example : ∃ S a S', Trace (R := ZeroOneOmega) S [a] S' :=
  ⟨.send .one .boolean .endS, .send .one .boolean, .endS, .step .send (.done .endS)⟩

theorem session_trace_sound {S T S' T' : SessionTy R} {actions : List (Action R)}
    (wf : S.WellFormed) (linked : T = S.dual)
    (ours : Trace S actions S') (theirs : Trace T (actions.map Action.co) T') :
    T' = S'.dual ∧
      ((S'.isEnd = true ∧ T'.isEnd = true) ∨
        ∃ a S'' T'', SStep S' a S'' ∧ SStep T' a.co T'' ∧ T'' = S''.dual) := by
  subst linked
  have same : T' = S'.dual := Trace.deterministic theirs ours.dual
  exact ⟨same, wellTyped_dual_endpoints_progress (ours.wellFormed wf) same⟩

/-! ## CapTP Promise Settlement Weld -/

@[expose] def sessionEvents (k : PendingId) (actions : List (Action R)) (final : SessionTy R) :
    List PromiseEvent :=
  .allocate k :: (actions.map (fun _ => PromiseEvent.deliver k) ++
    (if final.isEnd then [PromiseEvent.resolve k] else []))

theorem countResolved_deliveries {α : Type} (s : GuardedHole) (k : PendingId) (xs : List α)
    (rest : List PromiseEvent) :
    countResolved s (xs.map (fun _ => PromiseEvent.deliver k) ++ rest) k = countResolved s rest k := by
  induction xs with | nil => rfl | cons _ _ ih => simp [countResolved, promiseStep, ih]

theorem resolve_open (t : GuardedHole) (k : PendingId) (isOpen : t.openPromises.spec k)
    (unspent : ¬ t.spentNullifiers.spec k) : ∃ t', resolvePromise t k = some t' := by
  have h₁ : t.spentNullifiers.contains k = false := by
    cases hc : t.spentNullifiers.contains k with
    | false => rfl
    | true => exact absurd ((SortedDigestSet.contains_eq_spec _ _).mp hc) unspent
  have h₂ : t.openPromises.contains k = true := (SortedDigestSet.contains_eq_spec _ _).mpr isOpen
  simp [resolvePromise, h₁, h₂]

theorem session_capTP_settlement (s : GuardedHole) (k : PendingId)
    (fresh : ¬ s.spentNullifiers.spec k) (actions : List (Action R)) (final : SessionTy R) :
    countResolved s (sessionEvents k actions final) k = if final.isEnd then 1 else 0 := by
  have unspent : s.spentNullifiers.contains k = false := by
    cases hc : s.spentNullifiers.contains k with
    | false => rfl
    | true => exact absurd ((SortedDigestSet.contains_eq_spec _ _).mp hc) fresh
  have allocated : allocatePromise s k = { s with openPromises := s.openPromises.insert k } := by
    simp [allocatePromise, unspent]
  have head : countResolved s (sessionEvents k actions final) k =
      countResolved (allocatePromise s k) (if final.isEnd then [PromiseEvent.resolve k] else []) k := by
    simp only [sessionEvents, countResolved, promiseStep]
    rw [countResolved_deliveries]; simp
  rw [head]
  cases final.isEnd with
  | false => rfl
  | true =>
    obtain ⟨t', resolved⟩ := resolve_open (allocatePromise s k) k
      (by rw [allocated]; exact (SortedDigestSet.spec_insert _ _ _).mpr (.inl rfl))
      (by rw [allocated]; exact fresh)
    simp [countResolved, promiseStep, resolved]

theorem linked_endpoints_settle_together {S S' : SessionTy R} {actions : List (Action R)}
    (s s' : GuardedHole) (k k' : PendingId) (fresh : ¬ s.spentNullifiers.spec k)
    (fresh' : ¬ s'.spentNullifiers.spec k') (ours : Trace S actions S') :
    Trace S.dual (actions.map Action.co) S'.dual ∧
    (countResolved s (sessionEvents k actions S') k = 1 ↔
      countResolved s' (sessionEvents k' (actions.map Action.co) S'.dual) k' = 1) := by
  refine ⟨ours.dual, ?_⟩
  rw [session_capTP_settlement s k fresh, session_capTP_settlement s' k' fresh', SessionTy.isEnd_dual]

theorem session_capTP_at_most_once (s : GuardedHole) (k : PendingId) (actions : List (Action R))
    (final : SessionTy R) (replay : List PromiseEvent) :
    countResolved s (sessionEvents k actions final ++ replay) k ≤ 1 :=
  guardedHole_resolve_at_most_once s _ k

end Sessions

/-! ## Synchronous Dual `CoreSessionSoup` over `Obend.Core.Term.Yields` & Multi-Turn `RendezvousCoreTrace` -/

structure CoreSessionSoup (R : Type) where
  posSession : SessionTy R
  negSession : SessionTy R
  posTerm    : Term
  negTerm    : Term
  holePos    : GuardedHole
  holeNeg    : GuardedHole
  pendingPos : PendingId
  pendingNeg : PendingId
  settled    : Bool

def CoreSessionSoup.WellFormed {R : Type} (soup : CoreSessionSoup R) : Prop :=
  soup.posSession.WellFormed ∧
  soup.negSession = soup.posSession.dual ∧
  soup.holePos.WellFormed ∧
  soup.holeNeg.WellFormed ∧
  (soup.settled = false →
    soup.holePos.openPromises.spec soup.pendingPos ∧
    ¬ soup.holePos.spentNullifiers.spec soup.pendingPos ∧
    soup.holeNeg.openPromises.spec soup.pendingNeg ∧
    ¬ soup.holeNeg.spentNullifiers.spec soup.pendingNeg) ∧
  (soup.settled = true →
    soup.posSession = .endS ∧ soup.negSession = .endS ∧
    soup.holePos.spentNullifiers.spec soup.pendingPos ∧
    soup.holeNeg.spentNullifiers.spec soup.pendingNeg)

inductive CoreSessionTurn (R : Type) where
  | posSendNegRecv (q : R) (ty : Ty) (payload : Term)
  | negSendPosRecv (q : R) (ty : Ty) (payload : Term)
  | posSelectNegOffer (label : String)
  | negSelectPosOffer (label : String)
  | settleCloseWait

inductive RendezvousCoreStep {R : Type} :
    CoreSessionSoup R → CoreSessionTurn R → CoreSessionSoup R → Prop where
  | posSend {soup : CoreSessionSoup R} {q : R} {ty : Ty} {S' : SessionTy R}
      {pMid nMid payload : Term} {pCtx nCtx : List SourceFrame} :
      soup.settled = false →
      soup.posSession = .send q ty S' → soup.negSession = .recv q ty S'.dual →
      Steps soup.posTerm pMid → Yields pMid (.inject "send" payload) pCtx →
      Steps soup.negTerm nMid → Yields nMid (.inject "recv" (.record [])) nCtx →
      RendezvousCoreStep soup (.posSendNegRecv q ty payload)
        { soup with posSession := S', negSession := S'.dual,
                    posTerm := plug pCtx (.record []), negTerm := plug nCtx payload }
  | negSend {soup : CoreSessionSoup R} {q : R} {ty : Ty} {S' : SessionTy R}
      {pMid nMid payload : Term} {pCtx nCtx : List SourceFrame} :
      soup.settled = false →
      soup.posSession = .recv q ty S' → soup.negSession = .send q ty S'.dual →
      Steps soup.posTerm pMid → Yields pMid (.inject "recv" (.record [])) pCtx →
      Steps soup.negTerm nMid → Yields nMid (.inject "send" payload) nCtx →
      RendezvousCoreStep soup (.negSendPosRecv q ty payload)
        { soup with posSession := S', negSession := S'.dual,
                    posTerm := plug pCtx payload, negTerm := plug nCtx (.record []) }
  | posSelect {soup : CoreSessionSoup R} {B : Branches R} {lbl : String} {S' T' : SessionTy R}
      {pMid nMid : Term} {pCtx nCtx : List SourceFrame} :
      soup.settled = false → soup.posSession = .select B → B.find lbl = some S' →
      SStep soup.negSession (.offer lbl) T' →
      Steps soup.posTerm pMid → Yields pMid (.inject "select" (.label lbl)) pCtx →
      Steps soup.negTerm nMid → Yields nMid (.inject "offer" (.record [])) nCtx →
      RendezvousCoreStep soup (.posSelectNegOffer lbl)
        { soup with posSession := S', negSession := T',
                    posTerm := plug pCtx (.record []), negTerm := plug nCtx (.inject lbl (.record [])) }
  | negSelect {soup : CoreSessionSoup R} {B : Branches R} {lbl : String} {S' T' : SessionTy R}
      {pMid nMid : Term} {pCtx nCtx : List SourceFrame} :
      soup.settled = false → soup.negSession = .select B → B.find lbl = some T' →
      SStep soup.posSession (.offer lbl) S' →
      Steps soup.posTerm pMid → Yields pMid (.inject "offer" (.record [])) pCtx →
      Steps soup.negTerm nMid → Yields nMid (.inject "select" (.label lbl)) nCtx →
      RendezvousCoreStep soup (.negSelectPosOffer lbl)
        { soup with posSession := S', negSession := T',
                    posTerm := plug pCtx (.inject lbl (.record [])), negTerm := plug nCtx (.record []) }
  | settleCloseWait {soup : CoreSessionSoup R} {pMid nMid : Term}
      {pCtx nCtx : List SourceFrame} {holePos' holeNeg' : GuardedHole} :
      soup.settled = false → soup.posSession = .endS → soup.negSession = .endS →
      Steps soup.posTerm pMid → Yields pMid (.inject "close" (.record [])) pCtx →
      Steps soup.negTerm nMid → Yields nMid (.inject "wait" (.record [])) nCtx →
      resolvePromise soup.holePos soup.pendingPos = some holePos' →
      resolvePromise soup.holeNeg soup.pendingNeg = some holeNeg' →
      RendezvousCoreStep soup .settleCloseWait
        { soup with posTerm := plug pCtx (.record []), negTerm := plug nCtx (.record []),
                    holePos := holePos', holeNeg := holeNeg', settled := true }

inductive RendezvousCoreTrace {R : Type} :
    CoreSessionSoup R → List (CoreSessionTurn R) → CoreSessionSoup R → Prop where
  | nil (soup : CoreSessionSoup R) : RendezvousCoreTrace soup [] soup
  | cons {s₀ s₁ s₂ : CoreSessionSoup R} {turn : CoreSessionTurn R} {rest : List (CoreSessionTurn R)} :
      RendezvousCoreStep s₀ turn s₁ → RendezvousCoreTrace s₁ rest s₂ →
      RendezvousCoreTrace s₀ (turn :: rest) s₂

theorem rendezvousCoreStep_preserves_wellFormed {R : Type}
    {s s' : CoreSessionSoup R} {turn : CoreSessionTurn R}
    (wf : s.WellFormed) (step : RendezvousCoreStep s turn s') :
    s'.WellFormed := by
  obtain ⟨wfPos, hDual, wfHP, wfHN, hUnset, _⟩ := wf
  cases step with
  | posSend hNotSet hPos _ _ _ _ _ =>
    rw [hPos] at wfPos
    exact ⟨wfPos, rfl, wfHP, wfHN, hUnset, fun h => by rw [hNotSet] at h; cases h⟩
  | negSend hNotSet hPos _ _ _ _ _ =>
    rw [hPos] at wfPos
    exact ⟨wfPos, rfl, wfHP, wfHN, hUnset, fun h => by rw [hNotSet] at h; cases h⟩
  | posSelect hNotSet hPos hFind hNegStep _ _ _ _ =>
    have hPosStep : SStep s.posSession (.select _) _ := hPos ▸ SStep.select hFind
    exact ⟨hPosStep.wellFormed wfPos, session_step_preserves_duality hDual hPosStep hNegStep,
      wfHP, wfHN, hUnset, fun h => by rw [hNotSet] at h; cases h⟩
  | @negSelect B lbl S' T' _ _ _ _ hNotSet hNeg hFind hPosStep _ _ _ _ =>
    have hNegStep : SStep s.negSession (.select lbl) T' := hNeg ▸ SStep.select hFind
    have hDual' : T' = S'.dual := by
      have hd := SStep.deterministic hPosStep (by
        have h1 := hNegStep.dual; rw [hDual, SessionTy.dual_dual] at h1; exact h1)
      rw [hd, SessionTy.dual_dual]
    exact ⟨hPosStep.wellFormed wfPos, hDual', wfHP, wfHN, hUnset,
      fun h => by dsimp only at h; rw [hNotSet] at h; cases h⟩
  | settleCloseWait _ hPos hNeg _ _ _ _ hResP hResN =>
    exact ⟨wfPos, hDual,
      resolve_preserves_disjoint _ _ _ wfHP hResP,
      resolve_preserves_disjoint _ _ _ wfHN hResN,
      fun h => Bool.noConfusion h,
      fun _ => ⟨hPos, hNeg, resolve_spends _ _ _ hResP, resolve_spends _ _ _ hResN⟩⟩

theorem rendezvousCoreTrace_preserves_wellFormed {R : Type}
    {s₀ s' : CoreSessionSoup R} {turns : List (CoreSessionTurn R)}
    (wf₀ : s₀.WellFormed) (tr : RendezvousCoreTrace s₀ turns s') :
    s'.WellFormed ∧
    (s'.settled = true →
      resolvePromise s'.holePos s'.pendingPos = none ∧
      resolvePromise s'.holeNeg s'.pendingNeg = none) := by
  have wf' : s'.WellFormed := by
    induction tr with
    | nil => exact wf₀
    | cons st _ ih => exact ih (rendezvousCoreStep_preserves_wellFormed wf₀ st)
  refine ⟨wf', fun hSet => ?_⟩
  obtain ⟨_, _, hSpP, hSpN⟩ := wf'.2.2.2.2.2 hSet
  exact ⟨resolve_refuses_spent _ _ hSpP, resolve_refuses_spent _ _ hSpN⟩

/-! ## Graded Core4 Channel Delegation & Subject Reduction (`Rendezvous` over `Core.Term.Term`) -/

def sendTerm (q : Quantity) (chan payload : Term) : Term :=
  .perform (.inject "send" (pairTerm q payload chan))
def recvTerm (chan : Term) : Term := .perform (.inject "recv" chan)
def closeTerm (chan : Term) : Term := .perform (.inject "close" chan)
def waitTerm (chan : Term) : Term := .perform (.inject "wait" chan)
def closePair : Term := pairTerm .linear (closeTerm (.bound 0)) (waitTerm (.bound 1))
def closedPair : Term := pairTerm .linear (.record []) (.record [])

inductive Rendezvous : List Ty → Term → List Ty → Term → Prop where
  | communicate (Γ : List Ty) (q : Quantity) (A : Ty)
      (S : SessionTy ZeroOneOmega) (chanPos chanNeg : Nat) (payload : Term) :
      Rendezvous
        (chanTy chanPos :: chanTy chanNeg :: Γ)
        (pairTerm .linear
          (sendTerm q (.bound 0) ((payload.rename (shiftAt 0)).rename (shiftAt 0)))
          (recvTerm (.bound 1)))
        (chanTy chanPos :: chanTy chanNeg :: Γ)
        (pairTerm .linear (.bound 0)
          (pairTerm q ((payload.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1)))
  | close (Γ : List Ty) (chanPos chanNeg : Nat) :
      Rendezvous (chanTy chanPos :: chanTy chanNeg :: Γ) closePair Γ closedPair

def communicationUsage {R : Type} [ResourceRig R] (π : R) (U : Usage R) : Usage R :=
  Usage.add (Usage.single 1) (Usage.scale 𝟙
    (Usage.add (Usage.single 0) (Usage.scale π (Usage.insertAt 0 𝟘 (Usage.insertAt 0 𝟘 U)))))

theorem close_wait_subject_reduction (Γ : List Ty) (chanPos chanNeg : Nat) :
    Rendezvous (chanTy chanPos :: chanTy chanNeg :: Γ) closePair Γ closedPair ∧
    CoreGradedHasTy ZeroOneOmega Γ closedPair (pairRow .linear .emptyRow .emptyRow)
      Usage.zero closedPair := by
  refine ⟨.close Γ chanPos chanNeg, ?_⟩
  have h := CoreGradedHasTy.pair (R := ZeroOneOmega) (q := .linear) (Γ := Γ)
    CoreGradedHasTy.unit CoreGradedHasTy.unit
  have heq : Usage.add Usage.zero
      (Usage.scale (CoreGradeBridge.gradeOf (R := ZeroOneOmega) .linear) Usage.zero) = Usage.zero := by
    funext _; rfl
  have hEr : erasable (CoreGradeBridge.gradeOf (R := ZeroOneOmega) .linear) = false := by decide
  rw [heq, hEr] at h; exact h

theorem rendezvous_subject_reduction {Γ : List Ty}
    {payload payloadₑ : Term} {q : Quantity} {A : Ty}
    {S : SessionTy ZeroOneOmega} {chanPos chanNeg : Nat} {U : Usage ZeroOneOmega}
    (hExact : q ≠ .affine)
    (typed : CoreGradedHasTy ZeroOneOmega Γ payload A U payloadₑ) :
    let π := CoreGradeBridge.gradeOf (R := ZeroOneOmega) q
    let before := pairTerm .linear
      (sendTerm q (.bound 0) ((payload.rename (shiftAt 0)).rename (shiftAt 0)))
      (recvTerm (.bound 1))
    let after := pairTerm .linear (.bound 0)
      (pairTerm q ((payload.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1))
    let afterₑ := pairTerm .linear (.bound 0)
      (pairTerm q (if erasable π then .record []
        else (payloadₑ.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1))
    let Γ₀ := chanTy chanPos :: chanTy chanNeg :: Γ
    let T := pairRow .linear (chanTy chanPos) (pairRow q A (chanTy chanNeg))
    Rendezvous Γ₀ before Γ₀ after ∧
      CoreGradedHasTy ZeroOneOmega Γ₀ after T (communicationUsage π U) afterₑ ∧
      (∀ k, communicationUsage π U k = .one → termOcc k afterₑ = 1) := by
  let _ := hExact; dsimp only
  have hWeak : CoreGradedHasTy ZeroOneOmega (chanTy chanPos :: chanTy chanNeg :: Γ)
      ((payload.rename (shiftAt 0)).rename (shiftAt 0)) A
      (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U))
      ((payloadₑ.rename (shiftAt 0)).rename (shiftAt 0)) :=
    (typed.weaken (Γ₁ := []) (chanTy chanNeg)).weaken (Γ₁ := []) (chanTy chanPos)
  have hInner := CoreGradedHasTy.pair (q := q)
    (CoreGradedHasTy.var (Γ := chanTy chanPos :: chanTy chanNeg :: Γ) (i := 1) rfl) hWeak
  have hAfter := CoreGradedHasTy.pair (q := .linear) hInner
    (CoreGradedHasTy.var (Γ := chanTy chanPos :: chanTy chanNeg :: Γ) (i := 0) rfl)
  have hNotEr : erasable (CoreGradeBridge.gradeOf (R := ZeroOneOmega) .linear) = false := by decide
  rw [hNotEr] at hAfter; simp only [Bool.false_eq_true, ↓reduceIte] at hAfter
  have hSameU : Usage.add (Usage.add (Usage.single 1)
      (Usage.scale (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q)
        (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U))))
      (Usage.scale (CoreGradeBridge.gradeOf (R := ZeroOneOmega) .linear) (Usage.single 0)) =
      communicationUsage (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q) U := by
    funext n
    change ZeroOneOmega.add (ZeroOneOmega.add (Usage.single 1 n)
        (ZeroOneOmega.mul (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q)
          (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U) n)))
        (ZeroOneOmega.mul .one (Usage.single 0 n)) =
      ZeroOneOmega.add (Usage.single 1 n)
        (ZeroOneOmega.mul .one (ZeroOneOmega.add (Usage.single 0 n)
          (ZeroOneOmega.mul (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q)
            (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U) n))))
    generalize Usage.single (R := ZeroOneOmega) 1 n = a
    generalize Usage.single (R := ZeroOneOmega) 0 n = b
    generalize CoreGradeBridge.gradeOf (R := ZeroOneOmega) q = π
    generalize Usage.insertAt 0 ZeroOneOmega.zero (Usage.insertAt 0 ZeroOneOmega.zero U) n = u
    cases a <;> cases b <;> cases π <;> cases u <;> rfl
  rw [hSameU] at hAfter
  exact ⟨.communicate Γ q A S chanPos chanNeg payload, hAfter,
    fun k hk => (linear_cap_used_exactly_once hAfter k).2 hk⟩

theorem delegated_channel_subject_reduction {Γ : List Ty}
    {payload payloadₑ : Term} {S : SessionTy ZeroOneOmega}
    {delegatedId chanPos chanNeg : Nat} {U : Usage ZeroOneOmega}
    (typed : CoreGradedHasTy ZeroOneOmega Γ payload (chanTy delegatedId) U payloadₑ) :
    let after := pairTerm .linear (.bound 0)
      (pairTerm .linear ((payload.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1))
    let afterₑ := pairTerm .linear (.bound 0)
      (pairTerm .linear ((payloadₑ.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1))
    let Γ₀ := chanTy chanPos :: chanTy chanNeg :: Γ
    let T := pairRow .linear (chanTy chanPos) (pairRow .linear (chanTy delegatedId) (chanTy chanNeg))
    CoreGradedHasTy ZeroOneOmega Γ₀ after T (communicationUsage .one U) afterₑ ∧
      (∀ k, communicationUsage .one U k = .one → termOcc k afterₑ = 1) := by
  have h := rendezvous_subject_reduction (q := .linear) (S := S)
    (chanPos := chanPos) (chanNeg := chanNeg) (by decide) typed
  exact ⟨h.2.1, h.2.2⟩

/-! ## Asynchronous `Polis.CapTP` FIFO Queue Session Refinement -/

inductive AsyncMsg (R : Type) where
  | valMsg (q : R) (ty : Ty) (payload : Term) (msgId : PendingId)
  | branchMsg (label : String) (msgId : PendingId)
  deriving Repr

@[expose] def consumeQueue {R : Type} [DecidableEq R] :
    SessionTy R → List (AsyncMsg R) → Option (SessionTy R)
  | S, [] => some S
  | .recv q T S', .valMsg q' T' _ _ :: rest =>
    if q = q' ∧ T = T' then consumeQueue S' rest else none
  | .offer B, .branchMsg lbl _ :: rest =>
    match B.find lbl with
    | some S' => consumeQueue S' rest
    | none => none
  | _, _ :: _ => none

theorem consumeQueue_append {R : Type} [DecidableEq R] :
    ∀ (q₁ q₂ : List (AsyncMsg R)) (S : SessionTy R),
      consumeQueue S (q₁ ++ q₂) = (consumeQueue S q₁).bind (fun S' => consumeQueue S' q₂)
  | [], _, _ => rfl
  | .valMsg q' T' _ _ :: rest, q₂, .recv q T S' => by
    simp only [List.cons_append, consumeQueue]
    by_cases h : q = q' ∧ T = T'
    · simp [h, consumeQueue_append rest q₂ S']
    · simp [h]
  | .valMsg _ _ _ _ :: _, _, .endS | .valMsg _ _ _ _ :: _, _, .send _ _ _
  | .valMsg _ _ _ _ :: _, _, .offer _ | .valMsg _ _ _ _ :: _, _, .select _ => rfl
  | .branchMsg lbl _ :: rest, q₂, .offer B => by
    simp only [List.cons_append, consumeQueue]
    cases B.find lbl with | none => rfl | some S' => exact consumeQueue_append rest q₂ S'
  | .branchMsg _ _ :: _, _, .endS | .branchMsg _ _ :: _, _, .send _ _ _
  | .branchMsg _ _ :: _, _, .recv _ _ _ | .branchMsg _ _ :: _, _, .select _ => rfl

structure AsyncCapTPSession (R : Type) where
  posSession : SessionTy R
  negSession : SessionTy R
  qPosToNeg  : List (AsyncMsg R)
  qNegToPos  : List (AsyncMsg R)
  hole       : GuardedHole
  closed     : Bool

def AsyncMsg.msgId {R : Type} : AsyncMsg R → PendingId
  | .valMsg _ _ _ k | .branchMsg _ k => k

def QueueIdsOpen {R : Type} (hole : GuardedHole) (q : List (AsyncMsg R)) : Prop :=
  (q.map AsyncMsg.msgId).Nodup ∧
  ∀ m ∈ q, hole.openPromises.spec m.msgId ∧ ¬ hole.spentNullifiers.spec m.msgId

def AsyncDualBuffer {R : Type} [DecidableEq R] (st : AsyncCapTPSession R) : Prop :=
  (st.qNegToPos = [] ∧ consumeQueue st.negSession st.qPosToNeg = some st.posSession.dual) ∨
  (st.qPosToNeg = [] ∧ consumeQueue st.posSession st.qNegToPos = some st.negSession.dual)

def AsyncSessionWF {R : Type} [DecidableEq R] (st : AsyncCapTPSession R) : Prop :=
  st.posSession.WellFormed ∧ st.negSession.WellFormed ∧ st.hole.WellFormed ∧
  AsyncDualBuffer st ∧ QueueIdsOpen st.hole st.qPosToNeg ∧ QueueIdsOpen st.hole st.qNegToPos ∧
  (st.closed = true → st.posSession = .endS ∧ st.negSession = .endS ∧
    st.qPosToNeg = [] ∧ st.qNegToPos = [])

inductive AsyncSessionStep {R : Type} [DecidableEq R] :
    AsyncCapTPSession R → AsyncCapTPSession R → Prop where
  | enqueuePosVal {st : AsyncCapTPSession R} {q : R} {T : Ty} {S' : SessionTy R}
      {payload : Term} {k : PendingId} :
      st.closed = false → st.qNegToPos = [] → st.posSession = .send q T S' →
      ¬ st.hole.openPromises.spec k → ¬ st.hole.spentNullifiers.spec k →
      AsyncSessionStep st
        { st with posSession := S',
                  qPosToNeg := st.qPosToNeg ++ [.valMsg q T payload k],
                  hole := allocatePromise st.hole k }
  | enqueuePosBranch {st : AsyncCapTPSession R} {B : Branches R} {lbl : String}
      {S' : SessionTy R} {k : PendingId} :
      st.closed = false → st.qNegToPos = [] → st.posSession = .select B → B.find lbl = some S' →
      ¬ st.hole.openPromises.spec k → ¬ st.hole.spentNullifiers.spec k →
      AsyncSessionStep st
        { st with posSession := S',
                  qPosToNeg := st.qPosToNeg ++ [.branchMsg lbl k],
                  hole := allocatePromise st.hole k }
  | enqueueNegVal {st : AsyncCapTPSession R} {q : R} {T : Ty} {S' : SessionTy R}
      {payload : Term} {k : PendingId} :
      st.closed = false → st.qPosToNeg = [] → st.negSession = .send q T S' →
      ¬ st.hole.openPromises.spec k → ¬ st.hole.spentNullifiers.spec k →
      AsyncSessionStep st
        { st with negSession := S',
                  qNegToPos := st.qNegToPos ++ [.valMsg q T payload k],
                  hole := allocatePromise st.hole k }
  | enqueueNegBranch {st : AsyncCapTPSession R} {B : Branches R} {lbl : String}
      {S' : SessionTy R} {k : PendingId} :
      st.closed = false → st.qPosToNeg = [] → st.negSession = .select B → B.find lbl = some S' →
      ¬ st.hole.openPromises.spec k → ¬ st.hole.spentNullifiers.spec k →
      AsyncSessionStep st
        { st with negSession := S',
                  qNegToPos := st.qNegToPos ++ [.branchMsg lbl k],
                  hole := allocatePromise st.hole k }
  | dequeueNegVal {st : AsyncCapTPSession R} {q : R} {T : Ty} {S' : SessionTy R}
      {payload : Term} {k : PendingId} {rest : List (AsyncMsg R)} {hole' : GuardedHole} :
      st.closed = false → st.negSession = .recv q T S' →
      st.qPosToNeg = .valMsg q T payload k :: rest → resolvePromise st.hole k = some hole' →
      AsyncSessionStep st { st with negSession := S', qPosToNeg := rest, hole := hole' }
  | dequeueNegBranch {st : AsyncCapTPSession R} {B : Branches R} {lbl : String}
      {S' : SessionTy R} {k : PendingId} {rest : List (AsyncMsg R)} {hole' : GuardedHole} :
      st.closed = false → st.negSession = .offer B → B.find lbl = some S' →
      st.qPosToNeg = .branchMsg lbl k :: rest → resolvePromise st.hole k = some hole' →
      AsyncSessionStep st { st with negSession := S', qPosToNeg := rest, hole := hole' }
  | dequeuePosVal {st : AsyncCapTPSession R} {q : R} {T : Ty} {S' : SessionTy R}
      {payload : Term} {k : PendingId} {rest : List (AsyncMsg R)} {hole' : GuardedHole} :
      st.closed = false → st.posSession = .recv q T S' →
      st.qNegToPos = .valMsg q T payload k :: rest → resolvePromise st.hole k = some hole' →
      AsyncSessionStep st { st with posSession := S', qNegToPos := rest, hole := hole' }
  | dequeuePosBranch {st : AsyncCapTPSession R} {B : Branches R} {lbl : String}
      {S' : SessionTy R} {k : PendingId} {rest : List (AsyncMsg R)} {hole' : GuardedHole} :
      st.closed = false → st.posSession = .offer B → B.find lbl = some S' →
      st.qNegToPos = .branchMsg lbl k :: rest → resolvePromise st.hole k = some hole' →
      AsyncSessionStep st { st with posSession := S', qNegToPos := rest, hole := hole' }
  | closeAsync {st : AsyncCapTPSession R} :
      st.closed = false → st.posSession = .endS → st.negSession = .endS →
      st.qPosToNeg = [] → st.qNegToPos = [] →
      AsyncSessionStep st { st with closed := true }

inductive AsyncSessionTrace {R : Type} [DecidableEq R] :
    AsyncCapTPSession R → AsyncCapTPSession R → Prop where
  | refl (st : AsyncCapTPSession R) : AsyncSessionTrace st st
  | step {s₀ s₁ s₂ : AsyncCapTPSession R} :
      AsyncSessionStep s₀ s₁ → AsyncSessionTrace s₁ s₂ → AsyncSessionTrace s₀ s₂

private theorem queueIdsOpen_snoc {R : Type} {hole : GuardedHole} {q : List (AsyncMsg R)}
    {m : AsyncMsg R} (hq : QueueIdsOpen hole q)
    (hNotOpen : ¬ hole.openPromises.spec m.msgId) (hNotSpent : ¬ hole.spentNullifiers.spec m.msgId) :
    QueueIdsOpen (allocatePromise hole m.msgId) (q ++ [m]) := by
  have hUnspentBool : hole.spentNullifiers.contains m.msgId = false := by
    cases hc : hole.spentNullifiers.contains m.msgId with
    | false => rfl
    | true => exact absurd ((SortedDigestSet.contains_eq_spec _ _).mp hc) hNotSpent
  have hAlloc : allocatePromise hole m.msgId =
      { hole with openPromises := hole.openPromises.insert m.msgId } := by
    simp [allocatePromise, hUnspentBool]
  have hNotIn : m.msgId ∉ q.map AsyncMsg.msgId := fun hmem => by
    obtain ⟨x, hx, heq⟩ := List.mem_map.mp hmem; exact hNotOpen (heq ▸ (hq.2 x hx).1)
  refine ⟨by rw [List.map_append, List.map_singleton, List.nodup_append]
             exact ⟨hq.1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun x hx y hy heq => by
               simp only [List.mem_singleton] at hy; subst hy; subst heq; exact hNotIn hx⟩,
    fun x hx => ?_⟩
  rw [hAlloc]
  rcases List.mem_append.mp hx with hxin | hxlast
  · obtain ⟨ho, hs⟩ := hq.2 x hxin
    exact ⟨(SortedDigestSet.spec_insert _ _ _).mpr (.inr ho), hs⟩
  · simp only [List.mem_singleton] at hxlast; subst hxlast
    exact ⟨(SortedDigestSet.spec_insert _ _ _).mpr (.inl rfl), hNotSpent⟩

private theorem queueIdsOpen_empty_alloc {R : Type} (hole : GuardedHole) (k : PendingId) :
    QueueIdsOpen (R := R) (allocatePromise hole k) [] :=
  ⟨List.nodup_nil, fun _ h => by cases h⟩

private theorem queueIdsOpen_tail_resolve {R : Type} {hole hole' : GuardedHole}
    {m : AsyncMsg R} {rest : List (AsyncMsg R)} {k : PendingId}
    (hq : QueueIdsOpen hole (m :: rest)) (hRes : resolvePromise hole k = some hole')
    (hId : m.msgId = k) :
    QueueIdsOpen hole' rest := by
  subst hId
  obtain ⟨hNodup, hMem⟩ := hq
  obtain ⟨hNotIn, hRestNodup⟩ := List.nodup_cons.mp hNodup
  unfold resolvePromise at hRes; split at hRes
  · cases hRes
  · cases Option.some.inj hRes
    refine ⟨hRestNodup, fun x hx => ?_⟩
    have hne : x.msgId ≠ m.msgId := fun heq => hNotIn (heq ▸ List.mem_map_of_mem hx)
    obtain ⟨ho, hs⟩ := hMem x (List.mem_cons_of_mem _ hx)
    exact ⟨(SortedDigestSet.spec_erase _ _ _).mpr ⟨ho, hne⟩,
      fun hsp => (SortedDigestSet.spec_insert _ _ _).mp hsp |>.elim hne hs⟩

private theorem resolve_preserves_spent {hole hole' : GuardedHole} {k x : PendingId}
    (hRes : resolvePromise hole k = some hole') (hx : hole.spentNullifiers.spec x) :
    hole'.spentNullifiers.spec x := by
  have hsp := step_preserves_spent hole (.resolve k) x hx
  simp only [promiseStep, hRes] at hsp
  exact hsp

theorem asyncSessionStep_preserves_wf {R : Type} [DecidableEq R]
    {s s' : AsyncCapTPSession R} (wf : AsyncSessionWF s) (step : AsyncSessionStep s s') :
    AsyncSessionWF s' ∧
    (∀ k, s.hole.spentNullifiers.spec k → s'.hole.spentNullifiers.spec k) := by
  obtain ⟨wfP, wfN, wfH, hDual, hOpenPN, hOpenNP, _⟩ := wf
  cases step with
  | @enqueuePosVal q T S' _ k hNotCl hEmptyNP hPos hNoOpen hNoSpent =>
    have wfP' : S'.WellFormed := by rw [hPos] at wfP; exact wfP
    have hCons : consumeQueue s.negSession s.qPosToNeg = some (.recv q T S'.dual) := by
      rcases hDual with ⟨_, hc⟩ | ⟨hEmptyPN, hc⟩
      · simpa [hPos, SessionTy.dual] using hc
      · rw [hEmptyNP] at hc; simp only [consumeQueue, Option.some.injEq] at hc
        have hNegEq : s.negSession = s.posSession.dual := by rw [hc, SessionTy.dual_dual]
        rw [hEmptyPN, consumeQueue, hNegEq, hPos]; rfl
    exact ⟨⟨wfP', wfN, allocate_preserves_disjoint _ _ wfH,
      .inl ⟨hEmptyNP, by dsimp only; rw [consumeQueue_append, hCons]; simp [consumeQueue]⟩,
      queueIdsOpen_snoc hOpenPN hNoOpen hNoSpent,
      by dsimp only; rw [hEmptyNP]; exact queueIdsOpen_empty_alloc s.hole k,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun x hx => step_preserves_spent s.hole (.allocate k) x hx⟩
  | @enqueuePosBranch B lbl S' k hNotCl hEmptyNP hPos hFind hNoOpen hNoSpent =>
    have wfP' : S'.WellFormed := by rw [hPos] at wfP; exact Branches.find_wellFormed B lbl S' wfP.2 hFind
    have hCons : consumeQueue s.negSession s.qPosToNeg = some (.offer B.dual) := by
      rcases hDual with ⟨_, hc⟩ | ⟨hEmptyPN, hc⟩
      · simpa [hPos, SessionTy.dual] using hc
      · rw [hEmptyNP] at hc; simp only [consumeQueue, Option.some.injEq] at hc
        have hNegEq : s.negSession = s.posSession.dual := by rw [hc, SessionTy.dual_dual]
        rw [hEmptyPN, consumeQueue, hNegEq, hPos]; rfl
    exact ⟨⟨wfP', wfN, allocate_preserves_disjoint _ _ wfH,
      .inl ⟨hEmptyNP, by dsimp only; rw [consumeQueue_append, hCons]; simp [consumeQueue, Branches.find_dual B lbl S' hFind]⟩,
      queueIdsOpen_snoc hOpenPN hNoOpen hNoSpent,
      by dsimp only; rw [hEmptyNP]; exact queueIdsOpen_empty_alloc s.hole k,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun x hx => step_preserves_spent s.hole (.allocate k) x hx⟩
  | @enqueueNegVal q T S' _ k hNotCl hEmptyPN hNeg hNoOpen hNoSpent =>
    have wfN' : S'.WellFormed := by rw [hNeg] at wfN; exact wfN
    have hCons : consumeQueue s.posSession s.qNegToPos = some (.recv q T S'.dual) := by
      rcases hDual with ⟨hEmptyNP, hc⟩ | ⟨_, hc⟩
      · rw [hEmptyPN] at hc; simp only [consumeQueue, Option.some.injEq] at hc
        have hPosEq : s.posSession = s.negSession.dual := by rw [hc, SessionTy.dual_dual]
        rw [hEmptyNP, consumeQueue, hPosEq, hNeg]; rfl
      · simpa [hNeg, SessionTy.dual] using hc
    exact ⟨⟨wfP, wfN', allocate_preserves_disjoint _ _ wfH,
      .inr ⟨hEmptyPN, by dsimp only; rw [consumeQueue_append, hCons]; simp [consumeQueue]⟩,
      by dsimp only; rw [hEmptyPN]; exact queueIdsOpen_empty_alloc s.hole k,
      queueIdsOpen_snoc hOpenNP hNoOpen hNoSpent,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun x hx => step_preserves_spent s.hole (.allocate k) x hx⟩
  | @enqueueNegBranch B lbl S' k hNotCl hEmptyPN hNeg hFind hNoOpen hNoSpent =>
    have wfN' : S'.WellFormed := by rw [hNeg] at wfN; exact Branches.find_wellFormed B lbl S' wfN.2 hFind
    have hCons : consumeQueue s.posSession s.qNegToPos = some (.offer B.dual) := by
      rcases hDual with ⟨hEmptyNP, hc⟩ | ⟨_, hc⟩
      · rw [hEmptyPN] at hc; simp only [consumeQueue, Option.some.injEq] at hc
        have hPosEq : s.posSession = s.negSession.dual := by rw [hc, SessionTy.dual_dual]
        rw [hEmptyNP, consumeQueue, hPosEq, hNeg]; rfl
      · simpa [hNeg, SessionTy.dual] using hc
    exact ⟨⟨wfP, wfN', allocate_preserves_disjoint _ _ wfH,
      .inr ⟨hEmptyPN, by dsimp only; rw [consumeQueue_append, hCons]; simp [consumeQueue, Branches.find_dual B lbl S' hFind]⟩,
      by dsimp only; rw [hEmptyPN]; exact queueIdsOpen_empty_alloc s.hole k,
      queueIdsOpen_snoc hOpenNP hNoOpen hNoSpent,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun x hx => step_preserves_spent s.hole (.allocate k) x hx⟩
  | @dequeueNegVal q T S' _ k rest hole' hNotCl hNeg hQ hRes =>
    have wfN' : S'.WellFormed := by rw [hNeg] at wfN; exact wfN
    have hq' := hOpenPN; rw [hQ] at hq'
    have hEmptyNP : s.qNegToPos = [] := by
      rcases hDual with ⟨he, _⟩ | ⟨he, _⟩
      · exact he
      · rw [hQ] at he; cases he
    exact ⟨⟨wfP, wfN', resolve_preserves_disjoint _ _ _ wfH hRes,
      .inl ⟨hEmptyNP, by
        dsimp only
        rcases hDual with ⟨_, hc⟩ | ⟨he, _⟩
        · rw [hNeg, hQ] at hc; simpa [consumeQueue] using hc
        · rw [hQ] at he; cases he⟩,
      queueIdsOpen_tail_resolve hq' hRes rfl,
      by dsimp only; rw [hEmptyNP]; exact ⟨List.nodup_nil, fun _ h => nomatch h⟩,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun _ hx => resolve_preserves_spent hRes hx⟩
  | @dequeueNegBranch B lbl S' k rest hole' hNotCl hNeg hFind hQ hRes =>
    have wfN' : S'.WellFormed := by rw [hNeg] at wfN; exact Branches.find_wellFormed B lbl S' wfN.2 hFind
    have hq' := hOpenPN; rw [hQ] at hq'
    have hEmptyNP : s.qNegToPos = [] := by
      rcases hDual with ⟨he, _⟩ | ⟨he, _⟩
      · exact he
      · rw [hQ] at he; cases he
    exact ⟨⟨wfP, wfN', resolve_preserves_disjoint _ _ _ wfH hRes,
      .inl ⟨hEmptyNP, by
        dsimp only
        rcases hDual with ⟨_, hc⟩ | ⟨he, _⟩
        · rw [hNeg, hQ] at hc; simpa [consumeQueue, hFind] using hc
        · rw [hQ] at he; cases he⟩,
      queueIdsOpen_tail_resolve hq' hRes rfl,
      by dsimp only; rw [hEmptyNP]; exact ⟨List.nodup_nil, fun _ h => nomatch h⟩,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun _ hx => resolve_preserves_spent hRes hx⟩
  | @dequeuePosVal q T S' _ k rest hole' hNotCl hPos hQ hRes =>
    have wfP' : S'.WellFormed := by rw [hPos] at wfP; exact wfP
    have hq' := hOpenNP; rw [hQ] at hq'
    have hEmptyPN : s.qPosToNeg = [] := by
      rcases hDual with ⟨he, _⟩ | ⟨he, _⟩
      · rw [hQ] at he; cases he
      · exact he
    exact ⟨⟨wfP', wfN, resolve_preserves_disjoint _ _ _ wfH hRes,
      .inr ⟨hEmptyPN, by
        dsimp only
        rcases hDual with ⟨he, _⟩ | ⟨_, hc⟩
        · rw [hQ] at he; cases he
        · rw [hPos, hQ] at hc; simpa [consumeQueue] using hc⟩,
      by dsimp only; rw [hEmptyPN]; exact ⟨List.nodup_nil, fun _ h => nomatch h⟩,
      queueIdsOpen_tail_resolve hq' hRes rfl,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun _ hx => resolve_preserves_spent hRes hx⟩
  | @dequeuePosBranch B lbl S' k rest hole' hNotCl hPos hFind hQ hRes =>
    have wfP' : S'.WellFormed := by rw [hPos] at wfP; exact Branches.find_wellFormed B lbl S' wfP.2 hFind
    have hq' := hOpenNP; rw [hQ] at hq'
    have hEmptyPN : s.qPosToNeg = [] := by
      rcases hDual with ⟨he, _⟩ | ⟨he, _⟩
      · rw [hQ] at he; cases he
      · exact he
    exact ⟨⟨wfP', wfN, resolve_preserves_disjoint _ _ _ wfH hRes,
      .inr ⟨hEmptyPN, by
        dsimp only
        rcases hDual with ⟨he, _⟩ | ⟨_, hc⟩
        · rw [hQ] at he; cases he
        · rw [hPos, hQ] at hc; simpa [consumeQueue, hFind] using hc⟩,
      by dsimp only; rw [hEmptyPN]; exact ⟨List.nodup_nil, fun _ h => nomatch h⟩,
      queueIdsOpen_tail_resolve hq' hRes rfl,
      fun h => by dsimp only at h; rw [hNotCl] at h; cases h⟩,
      fun _ hx => resolve_preserves_spent hRes hx⟩
  | closeAsync _ hP hN hQPN hQNP =>
    exact ⟨⟨wfP, wfN, wfH, hDual, hOpenPN, hOpenNP, fun _ => ⟨hP, hN, hQPN, hQNP⟩⟩, fun _ hx => hx⟩

/-- **Asynchronous `CapTP` FIFO Session Progress & Fidelity (`async_captp_session_progress_and_fidelity`).** -/
theorem async_captp_session_progress_and_fidelity {R : Type} [DecidableEq R]
    {s₀ s' : AsyncCapTPSession R} (wf₀ : AsyncSessionWF s₀)
    (tr : AsyncSessionTrace s₀ s')
    (kFresh : PendingId)
    (hFreshOpen : ¬ s'.hole.openPromises.spec kFresh)
    (hFreshSpent : ¬ s'.hole.spentNullifiers.spec kFresh) :
    AsyncSessionWF s' ∧
    (∀ k, s₀.hole.spentNullifiers.spec k → s'.hole.spentNullifiers.spec k) ∧
    ((s'.closed = true ∧ s'.posSession = .endS ∧ s'.negSession = .endS ∧
      s'.qPosToNeg = [] ∧ s'.qNegToPos = []) ∨
     ∃ s'', AsyncSessionStep s' s'') := by
  have hInv : AsyncSessionWF s' ∧
      (∀ k, s₀.hole.spentNullifiers.spec k → s'.hole.spentNullifiers.spec k) := by
    clear hFreshOpen hFreshSpent
    induction tr with
    | refl => exact ⟨wf₀, fun _ h => h⟩
    | step st _ ih =>
      obtain ⟨wf₁, hMono₁⟩ := asyncSessionStep_preserves_wf wf₀ st
      obtain ⟨wf₂, hMono₂⟩ := ih wf₁
      exact ⟨wf₂, fun k hk => hMono₂ k (hMono₁ k hk)⟩
  obtain ⟨wf', hMono⟩ := hInv
  refine ⟨wf', hMono, ?_⟩
  by_cases hCl : s'.closed = true
  · obtain ⟨hP, hN, hQPN, hQNP⟩ := wf'.2.2.2.2.2.2 hCl
    exact .inl ⟨hCl, hP, hN, hQPN, hQNP⟩
  · have hClF : s'.closed = false := Bool.eq_false_iff.mpr hCl
    right
    obtain ⟨wfP, wfN, _, hDual, hOpenPN, hOpenNP, _⟩ := wf'
    rcases hDual with ⟨hEmptyNP, hConsPN⟩ | ⟨hEmptyPN, hConsNP⟩
    · cases hQ : s'.qPosToNeg with
      | cons m rest =>
        rw [hQ] at hConsPN
        obtain ⟨hMOpen, hMUnspent⟩ := hOpenPN.2 m (by simp [hQ])
        obtain ⟨hole', hRes⟩ := resolve_open s'.hole m.msgId hMOpen hMUnspent
        cases m with
        | valMsg q' T' _ _ =>
          cases hN : s'.negSession with
          | recv q T _ =>
            rw [hN] at hConsPN; simp only [consumeQueue] at hConsPN
            by_cases heq : q = q' ∧ T = T'
            · rcases heq with ⟨rfl, rfl⟩; exact ⟨_, .dequeueNegVal hClF hN hQ hRes⟩
            · simp [heq] at hConsPN
          | _ => rw [hN] at hConsPN; simp [consumeQueue] at hConsPN
        | branchMsg lbl _ =>
          cases hN : s'.negSession with
          | offer B =>
            rw [hN] at hConsPN; simp only [consumeQueue] at hConsPN
            cases hFind : B.find lbl with
            | none => simp [hFind] at hConsPN
            | some _ => exact ⟨_, .dequeueNegBranch hClF hN hFind hQ hRes⟩
          | _ => rw [hN] at hConsPN; simp [consumeQueue] at hConsPN
      | nil =>
        rw [hQ, consumeQueue, Option.some.injEq] at hConsPN
        cases hP : s'.posSession with
        | endS =>
          rw [hP, SessionTy.dual] at hConsPN; exact ⟨_, .closeAsync hClF hP hConsPN hQ hEmptyNP⟩
        | send _ _ _ =>
          exact ⟨_, .enqueuePosVal (payload := .record []) hClF hEmptyNP hP hFreshOpen hFreshSpent⟩
        | select B =>
          cases B with
          | nil => rw [hP] at wfP; simp [SessionTy.WellFormed] at wfP
          | cons lbl cont _ =>
            exact ⟨_, .enqueuePosBranch (lbl := lbl) (S' := cont) hClF hEmptyNP hP (by simp [Branches.find]) hFreshOpen hFreshSpent⟩
        | recv q T S' =>
          have hN : s'.negSession = .send q T S'.dual := by rw [hConsPN, hP, SessionTy.dual]
          exact ⟨_, .enqueueNegVal (payload := .record []) hClF hQ hN hFreshOpen hFreshSpent⟩
        | offer B =>
          have hN : s'.negSession = .select B.dual := by rw [hConsPN, hP, SessionTy.dual]
          cases B with
          | nil => rw [hP] at wfP; simp [SessionTy.WellFormed] at wfP
          | cons lbl cont _ =>
            exact ⟨_, .enqueueNegBranch (lbl := lbl) (S' := cont.dual) hClF hQ hN (by simp [Branches.dual, Branches.find]) hFreshOpen hFreshSpent⟩
    · cases hQ : s'.qNegToPos with
      | cons m rest =>
        rw [hQ] at hConsNP
        obtain ⟨hMOpen, hMUnspent⟩ := hOpenNP.2 m (by simp [hQ])
        obtain ⟨hole', hRes⟩ := resolve_open s'.hole m.msgId hMOpen hMUnspent
        cases m with
        | valMsg q' T' _ _ =>
          cases hP : s'.posSession with
          | recv q T _ =>
            rw [hP] at hConsNP; simp only [consumeQueue] at hConsNP
            by_cases heq : q = q' ∧ T = T'
            · rcases heq with ⟨rfl, rfl⟩; exact ⟨_, .dequeuePosVal hClF hP hQ hRes⟩
            · simp [heq] at hConsNP
          | _ => rw [hP] at hConsNP; simp [consumeQueue] at hConsNP
        | branchMsg lbl _ =>
          cases hP : s'.posSession with
          | offer B =>
            rw [hP] at hConsNP; simp only [consumeQueue] at hConsNP
            cases hFind : B.find lbl with
            | none => simp [hFind] at hConsNP
            | some _ => exact ⟨_, .dequeuePosBranch hClF hP hFind hQ hRes⟩
          | _ => rw [hP] at hConsNP; simp [consumeQueue] at hConsNP
      | nil =>
        rw [hQ, consumeQueue, Option.some.injEq] at hConsNP
        cases hN : s'.negSession with
        | endS =>
          rw [hN, SessionTy.dual] at hConsNP; exact ⟨_, .closeAsync hClF hConsNP hN hEmptyPN hQ⟩
        | send _ _ _ =>
          exact ⟨_, .enqueueNegVal (payload := .record []) hClF hEmptyPN hN hFreshOpen hFreshSpent⟩
        | select B =>
          cases B with
          | nil => rw [hN] at wfN; simp [SessionTy.WellFormed] at wfN
          | cons lbl cont _ =>
            exact ⟨_, .enqueueNegBranch (lbl := lbl) (S' := cont) hClF hEmptyPN hN (by simp [Branches.find]) hFreshOpen hFreshSpent⟩
        | recv q T S' =>
          have hP : s'.posSession = .send q T S'.dual := by rw [hConsNP, hN, SessionTy.dual]
          exact ⟨_, .enqueuePosVal (payload := .record []) hClF hQ hP hFreshOpen hFreshSpent⟩
        | offer B =>
          have hP : s'.posSession = .select B.dual := by rw [hConsNP, hN, SessionTy.dual]
          cases B with
          | nil => rw [hN] at wfN; simp [SessionTy.WellFormed] at wfN
          | cons lbl cont _ =>
            exact ⟨_, .enqueuePosBranch (lbl := lbl) (S' := cont.dual) hClF hQ hP (by simp [Branches.dual, Branches.find]) hFreshOpen hFreshSpent⟩

theorem sync_send_refines_to_async_captp {R : Type} [DecidableEq R]
    (q : R) (T : Ty) (S : SessionTy R) (payload : Term)
    (hole : GuardedHole) (k : PendingId)
    (hNoOpen : ¬ hole.openPromises.spec k) (hNoSpent : ¬ hole.spentNullifiers.spec k) :
    ∃ hole',
      resolvePromise (allocatePromise hole k) k = some hole' ∧
      hole'.spentNullifiers.spec k ∧
      AsyncSessionTrace
        ⟨.send q T S, .recv q T S.dual, [], [], hole, false⟩
        ⟨S, S.dual, [], [], hole', false⟩ := by
  have hUnspent : hole.spentNullifiers.contains k = false := by
    cases hc : hole.spentNullifiers.contains k with
    | false => rfl
    | true => exact absurd ((SortedDigestSet.contains_eq_spec _ _).mp hc) hNoSpent
  have hAlloc : allocatePromise hole k = { hole with openPromises := hole.openPromises.insert k } := by
    simp [allocatePromise, hUnspent]
  obtain ⟨hole', hRes⟩ := resolve_open (allocatePromise hole k) k
    (by rw [hAlloc]; exact (SortedDigestSet.spec_insert _ _ _).mpr (.inl rfl))
    (by rw [hAlloc]; exact hNoSpent)
  exact ⟨hole', hRes, resolve_spends _ _ k hRes,
    .step (.enqueuePosVal (payload := payload) rfl rfl rfl hNoOpen hNoSpent)
      (.step (.dequeueNegVal rfl rfl rfl hRes) (.refl _))⟩

end Obend.Core.GradedSessionMetatheory
end
