module
/-
# Obend.Law.Proofs.Typing — the generated laws check at `lawTy S`, with no annotations

The Law lane left owed that a generated law has the type it is written for (REPORT-LAW-20261030,
"Not done": Core4's lambdas carry no annotations, so `lawTy S` was documentation). This module
discharges it against the bidirectional checker itself: for every state type `S` that is
canonical and shareable (first-order data, fields in label order) and has the fields the law
reads at the types it reads them, `Bidirectional.checkAgainst` accepts the law at `lawTy S` with
NO annotations (`noAnn`) and empty assumptions. Every check is the checker's own computation
(`elaborate`), read through one lemma per term form (`chk_*`, `syn_*`), never a re-implementation.

The forms a law uses are introduction or elimination forms the checker types from the expected
type alone: three lambdas against `lawTy S` (`chk_lam`), `case` on a synthesized scrutinee whose
arms cover its closed row in order (`chk_case`), `ifBool`, injections into a sum (`chk_inject`),
field selection on a variable (`syn_get`), the primitives. `lawOf6_checks` reduces a law to its
six clauses, each checked at `verdictTy` in the context `clauseCtx S P` (the occasion's payload,
the request, the new state, the old state). `keeps S I` applies an arbitrary closed invariant in
the clause, and a closed lambda synthesizes only with an annotation, so the algorithmic checker
refuses it unannotated (`Teeth.keeps_unannotated_refused`); `keeps_typed` gives it a derivation in
the declarative system (`PartialTyping`) whenever `I` is checked at `S → boolean`, by typing
`keepsOpen S` (the invariant a variable) with the checker and substituting `I` for the variable.
-/
public import Obend.Law.Std
public import Obend.Core.Bidirectional
public import Obend.Core.MachineTyping
public import Obend.Tactic.Tooth
public import Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.Check
namespace Obend.Law.Typing
open Obend.Law
open Obend.Core.Ty
open Obend.Core.Term (Term Primitive)
open Obend.Core.Check
open Obend.Core.Bidirectional (elaborate Synth Against finish introduce representativeHead whnf
  checkArms checkFieldsByLabel checkAgainst rowMember need_ok sameType_whnf)
set_option autoImplicit false

/-- No annotation anywhere. -/
@[expose] public def noAnn : Annotations := fun _ => none

/-- No binder of `ctx` is `linear`, so the checker's linear premises (an argument, a projection,
the branches of a join) hold whatever the uses. Laws bind nothing `linear`. -/
@[expose] public def NoLinear (ctx : Context) : Prop := ∀ b ∈ ctx, b.quantity ≠ .linear

public theorem NoLinear.cons {ctx : Context} {T : Ty} {q : Quantity} (h : NoLinear ctx) (hq : q ≠ .linear) :
    NoLinear (⟨T, q⟩ :: ctx) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hq
  · exact h b hb

public theorem linearFree_noLinear {ctx : Context} (h : NoLinear ctx) (uses : Uses) : linearFree ctx uses = true := by
  unfold linearFree
  rw [List.all_eq_true]
  intro pair member
  have := h pair.1 (List.of_mem_zip member).1
  simp [this]

public theorem branchesAgree_noLinear : ∀ {ctx : Context}, NoLinear ctx → ∀ first second : Uses,
    branchesAgree ctx first second = true
  | [], _, _, _ => by cases ‹Uses› <;> rfl
  | _ :: _, _, [], _ => rfl
  | _ :: _, _, _ :: _, [] => rfl
  | b :: ctx, h, _ :: first, _ :: second => by
    simp only [branchesAgree, Bool.and_eq_true]
    refine ⟨?_, branchesAgree_noLinear (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) first second⟩
    have := h b List.mem_cons_self
    cases hq : b.quantity <;> simp_all [Quantity.agrees]

/-- `t` synthesizes `T` in `ctx`, at every position, with no annotations. -/
@[expose] public def Syn (ctx : Context) (t : Term) (T : Ty) : Prop :=
  NoLinear ctx → ∀ path, ∃ r : Synth {} ctx t, elaborate {} noAnn ctx path t .synth = .ok r ∧ r.type = T

/-- `t` checks against `T` in `ctx`, at every position, with no annotations. -/
@[expose] public def Chk (ctx : Context) (t : Term) (T : Ty) : Prop :=
  NoLinear ctx → ∀ path, ∃ r : Against {} ctx t T, elaborate {} noAnn ctx path t (.check T) = .ok r

theorem finish_check {ctx : Context} {t : Term} (path : List Nat) (s : Synth {} ctx t) (T : Ty)
    (h : s.type = T) : ∃ r : Against {} ctx t T, finish {} noAnn path s (.check T) = .ok r := by
  subst h; simp only [finish, sameType_refl, dite_true]; exact ⟨_, rfl⟩

theorem lookupV_empty (name : String) : (T : Ty) → lookupV [] [] T name = rowMember T name
  | .field prior member tail => by
    have := lookupV_empty name tail
    simp only [lookupV, unvisited, List.filter_nil, List.length_nil, lookupW, walkRow, rowMember] at this ⊢
    rw [this]; split <;> simp_all
  | .natural | .label | .boolean | .variable _ | .arrow .. | .emptyRow | .specification .. | .prototype ..
  | .custody _ | .variant _ | .computation .. => by
    simp [lookupV, unvisited, lookupW, walkRow, rowMember]

public theorem syn_bound {ctx : Context} {i : Nat} {b : Binding} (h : ctx[i]? = some b) : Syn ctx (.bound i) b.type := by
  intro _ p
  simp only [elaborate]
  split
  · rename_i b' hb; rw [h] at hb; cases hb; exact ⟨_, rfl, rfl⟩
  · rename_i hb; rw [h] at hb; cases hb

public theorem chk_bound {ctx : Context} {i : Nat} {b : Binding} (h : ctx[i]? = some b) : Chk ctx (.bound i) b.type := by
  intro _ p
  simp only [elaborate]
  split
  · rename_i b' hb; rw [h] at hb; cases hb; exact finish_check _ _ _ rfl
  · rename_i hb; rw [h] at hb; cases hb

public theorem chk_nat (ctx : Context) (k : Nat) : Chk ctx (.nat k) .natural := by
  intro _ p; simp only [elaborate]; exact finish_check _ _ _ rfl
public theorem chk_boolean (ctx : Context) (b : Bool) : Chk ctx (.boolean b) .boolean := by
  intro _ p; simp only [elaborate]; exact finish_check _ _ _ rfl
public theorem chk_label (ctx : Context) (s : String) : Chk ctx (.label s) .label := by
  intro _ p; simp only [elaborate]; exact finish_check _ _ _ rfl

public theorem syn_get {ctx : Context} {t : Term} {T M : Ty} {f : String} (h : Syn ctx t T)
    (hm : rowMember T f = some M) : Syn ctx (.get t f) M := by
  intro hn p
  obtain ⟨r, hr, hT⟩ := h hn (p ++ [0])
  simp only [elaborate, noAnn, hr, bind, Except.bind]
  split
  · rename_i m hl
    have : lookupV [] [] r.type f = some M := by rw [hT, lookupV_empty, hm]
    have hm' : m = M := by simp_all
    subst hm'; rw [need_ok (linearFree_noLinear hn _)]; exact ⟨_, rfl, rfl⟩
  · rename_i hl
    have : lookupV [] [] r.type f = some M := by rw [hT, lookupV_empty, hm]
    simp_all

public theorem chk_get {ctx : Context} {t : Term} {T M : Ty} {f : String} (h : Syn ctx t T)
    (hm : rowMember T f = some M) : Chk ctx (.get t f) M := by
  intro hn p
  obtain ⟨r, hr, hT⟩ := h hn (p ++ [0])
  simp only [elaborate, noAnn, hr, bind, Except.bind]
  have : lookupV [] [] r.type f = some M := by rw [hT, lookupV_empty, hm]
  split
  · rename_i m hl
    have hm' : m = M := by simp_all
    subst hm'; rw [need_ok (linearFree_noLinear hn _)]; exact finish_check _ _ _ rfl
  · simp_all

public theorem chk_binary {ctx : Context} {p : Primitive} {l r : Term}
    (hl : Chk ctx l (primitiveTypes p).1) (hr : Chk ctx r (primitiveTypes p).1) :
    Chk ctx (.binary p l r) (primitiveTypes p).2 := by
  intro hn path
  obtain ⟨a, ha⟩ := hl hn (path ++ [0])
  obtain ⟨b, hb⟩ := hr hn (path ++ [1])
  simp only [elaborate, ha, hb, bind, Except.bind]
  exact finish_check _ _ _ rfl

public theorem chk_ifBool {ctx : Context} {c x y : Term} {T : Ty}
    (hc : Chk ctx c .boolean) (hx : Chk ctx x T) (hy : Chk ctx y T) : Chk ctx (.ifBool c x y) T := by
  intro hn path
  obtain ⟨a, ha⟩ := hc hn (path ++ [0])
  obtain ⟨b, hb⟩ := hx hn (path ++ [1])
  obtain ⟨d, hd⟩ := hy hn (path ++ [2])
  simp only [elaborate, introduce, noAnn, ha, hb, hd, bind, Except.bind, pure, Except.pure,
    need_ok (branchesAgree_noLinear hn _ _)]
  exact ⟨_, rfl⟩

public theorem chk_unit (ctx : Context) : Chk ctx (.record []) .emptyRow := by
  intro _ path
  simp only [elaborate, introduce, noAnn, Option.isSome_none, Bool.false_eq_true, ite_false,
    labelsDistinct, checkFieldsByLabel, bind, Except.bind, pure, Except.pure,
    Obend.Core.Bidirectional.need, sameType_refl]
  exact ⟨_, rfl⟩

public theorem chk_inject {ctx : Context} {tag : String} {payload : Term} {T row P : Ty}
    (hT : T.canonical = .variant row) (hP : rowMember row tag = some P) (hc : P.isComputation = false)
    (h : Chk ctx payload P) : Chk ctx (.inject tag payload) T := by
  intro hn path
  obtain ⟨a, ha⟩ := h hn (path ++ [0])
  simp only [elaborate, introduce, noAnn]
  have hw : Obend.Core.Bidirectional.injectionHead {} noAnn path T = .variant row := by
    have head : representativeHead {} noAnn path T = .variant row := hT
    simp [Obend.Core.Bidirectional.injectionHead, head]
  have hl : lookupV [] [] row tag = some P := by rw [lookupV_empty, hP]
  split
  · rename_i row' hs
    rw [hw] at hs; cases hs
    split
    · rename_i P' hf
      have : P' = P := by simp_all
      subst this
      simp only [ha, bind, Except.bind]
      rw [need_ok (by simp [hc])]
      exact ⟨_, rfl⟩
    · simp_all
  · rename_i hs; rw [hw] at hs; exact absurd rfl (hs row)

/-- Every binder is unrestricted at a shareable type. -/
@[expose] public def Clean (ctx : Context) : Prop := ∀ b ∈ ctx, b.quantity = .unrestricted ∧ b.type.shareable = true

public theorem Clean.cons {ctx : Context} {T : Ty} (h : Clean ctx) (hT : T.shareable = true) :
    Clean (⟨T, .unrestricted⟩ :: ctx) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ⟨rfl, hT⟩
  · exact h b hb

public theorem Clean.noLinear {ctx : Context} (h : Clean ctx) : NoLinear ctx := fun b hb => by
  rw [(h b hb).1]; decide

theorem safeUses_clean {ctx : Context} {uses : Uses} (h : Clean ctx) (hl : uses.length = ctx.length) :
    safeUses ctx uses = true := by
  simp only [safeUses, hl, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro x hx
  rw [(h x.1 (List.of_mem_zip hx).1).1]; rfl

theorem validContext_clean {ctx : Context} (h : Clean ctx) : validContext [] ctx = true := by
  simp only [validContext, List.all_eq_true]
  intro b hb
  simp [(h b hb).2]

theorem reusableCaptures_clean {ctx : Context} {uses : Uses} (h : Clean ctx) (hl : uses.length = ctx.length) :
    reusableCaptures [] ctx uses = true := by
  simp only [reusableCaptures, hl, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro x hx
  have := h x.1 (List.of_mem_zip hx).1
  simp [this.1, this.2]

public theorem chk_lam {ctx : Context} {body : Term} {D C : Ty} (hctx : Clean ctx) (hD : D.canonical.shareable = true)
    (h : Chk (⟨D.canonical, .unrestricted⟩ :: ctx) body C.canonical) : Chk ctx (.lam body) (fnTy D C) := by
  intro hn path
  obtain ⟨a, ha⟩ := h (hn.cons (by decide)) (path ++ [0])
  have hc : Clean (⟨D.canonical, .unrestricted⟩ :: ctx) := hctx.cons hD
  have hl := Obend.Core.MachineTyping.source_uses_length a.derivation
  simp only [elaborate, noAnn]
  split
  · rename_i reuse q dom cod hs
    have hw : representativeHead {} noAnn path (fnTy D C) =
        .arrow .reusable .unrestricted D.canonical C.canonical := rfl
    rw [hw] at hs; cases hs
    simp only [ha, bind, Except.bind]
    rw [need_ok (safeUses_clean hc hl), need_ok (validContext_clean hc)]
    have : reusableAllowed {} .reusable ctx a.uses.tail = true := by
      simp only [reusableAllowed]
      rw [reusableCaptures_clean hctx (by simp [List.length_tail, hl])]; rfl
    rw [need_ok this]
    exact ⟨_, rfl⟩
  · rename_i hs
    exact absurd rfl (hs .reusable .unrestricted D.canonical C.canonical)

/-- Arms that cover a closed row in its order, each body checking under its payload. -/
public inductive ArmsChk (ctx : Context) (row result : Ty) : Ty → List (String × Term) → Prop
  | nil : ArmsChk ctx row result .emptyRow []
  | cons {l : String} {P tail : Ty} {body : Term} {rest : List (String × Term)} :
      rowMember row l = some P → P.shareable = true →
      Chk (⟨P, .unrestricted⟩ :: ctx) body result → ArmsChk ctx row result tail rest →
      ArmsChk ctx row result (.field l P tail) ((l, body) :: rest)

theorem reusable_clean {ctx : Context} {uses : Uses} (h : Clean ctx) (hl : uses.length = ctx.length) :
    reusableCaptures ([] : List Nat) ctx uses = true := by
  simp only [reusableCaptures, hl, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro x hx
  obtain ⟨q, sh⟩ := h x.1 (List.of_mem_zip hx).1
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact .inr ⟨q, by simpa using sh⟩

theorem armsShareable_chk {ctx : Context} {row result : Ty} :
    ∀ {sub : Ty} {arms : List (String × Term)}, ArmsChk ctx row result sub arms →
      Obend.Core.Bidirectional.armsShareable {} row arms = true
  | _, _, .nil => rfl
  | _, _, .cons hm hs _ rest => by
    have tail := armsShareable_chk rest
    simp only [Obend.Core.Bidirectional.armsShareable, List.all_cons, hm, Bool.and_eq_true] at tail ⊢
    exact ⟨by simpa using hs, tail⟩

theorem armsCustody_chk {ctx : Context} {row result : Ty} :
    ∀ {sub : Ty} {arms : List (String × Term)}, ArmsChk ctx row result sub arms →
      Obend.Core.Bidirectional.armsCustody row arms = false
  | _, _, .nil => rfl
  | _, _, .cons hm hs _ rest => by
    have tail := armsCustody_chk rest
    simp only [Obend.Core.Bidirectional.armsCustody, List.any_cons, hm, Bool.or_eq_false_iff] at tail ⊢
    exact ⟨Ty.bearsCustody_of_shareable hs, tail⟩

theorem checkArms_ok {ctx : Context} {row result : Ty} (hctx : Clean ctx) :
    ∀ {sub : Ty} {arms : List (String × Term)}, ArmsChk ctx row result sub arms →
      ∀ path idx, ∃ typed, checkArms {} noAnn ctx .unrestricted path idx row result arms = .ok typed ∧
        typed.row = sub ∧ typed.quantity = .unrestricted
  | _, _, .nil, path, idx => ⟨_, rfl, rfl, rfl⟩
  | _, _, .cons (P := P) hm hs hb rest, path, idx => by
    have hc : Clean (⟨P, .unrestricted⟩ :: ctx) := hctx.cons hs
    obtain ⟨a, ha⟩ := hb hc.noLinear (path ++ [idx])
    obtain ⟨t, ht, hr, hq⟩ := checkArms_ok hctx rest path (idx + 1)
    have hl := Obend.Core.MachineTyping.source_uses_length a.derivation
    simp only [checkArms, hm, bind, Except.bind]
    rw [need_ok (by simp [validContext, hs])]
    simp only [ha]
    rw [need_ok (safeUses_clean hc hl), need_ok (show Quantity.unrestricted.fits (a.uses.headD 0) = true from rfl)]
    simp only [ht, pure, Except.pure, need_ok (show (_ || branchesAgree ctx a.uses.tail t.uses) = true by
      simp [branchesAgree_noLinear hctx.noLinear]), dif_pos hq]
    exact ⟨_, rfl, by simp [hr], rfl⟩

public theorem chk_case {ctx : Context} {s : Term} {arms : List (String × Term)} {V row result : Ty}
    (hctx : Clean ctx) (hs : Syn ctx s V) (hV : V.canonical = .variant row)
    (ha : ArmsChk ctx row result row arms) (hd : labelsDistinct arms = true) (hne : arms ≠ []) :
    Chk ctx (.case s arms) result := by
  cases arms with
  | nil => exact absurd rfl hne
  | cons arm rest =>
    obtain ⟨name, body⟩ := arm
    intro hn path
    obtain ⟨v, hv, hvT⟩ := hs hn (path ++ [0])
    obtain ⟨t, ht, hr, hq⟩ := checkArms_ok hctx ha (path ++ [1]) 0
    have vl := Obend.Core.MachineTyping.source_uses_length v.derivation
    have quantity : Obend.Core.Bidirectional.caseQuantityAt {} noAnn path ctx v.uses row ((name, body) :: rest) = .unrestricted := by
      simp [Obend.Core.Bidirectional.caseQuantityAt, noAnn, caseQuantity, linearFree_noLinear hctx.noLinear, reusable_clean hctx vl,
        armsShareable_chk ha, armsCustody_chk ha]
    simp only [elaborate, noAnn, hv, bind, Except.bind]
    rw [need_ok hd]
    have hw : representativeHead {} noAnn path v.type = .variant row := by rw [hvT]; exact hV
    simp only [hw]
    rw [quantity]
    simp only [ht]
    have : sameType {} v.type (.variant t.row) = true := by
      rw [hr, ← hV, hvT]; exact sameType_whnf {} V
    have allowed : caseAllowed {} t.quantity ctx v.uses = true := by
      simp [hq, caseAllowed, linearFree_noLinear hctx.noLinear, reusable_clean hctx vl]
    rw [need_ok allowed, need_ok this]
    exact ⟨_, rfl⟩

/-! ## Derived forms -/

public theorem chk_bin {ctx : Context} {p : Primitive} {l r : Term} {A B : Ty} (hp : primitiveTypes p = (A, B))
    (hl : Chk ctx l A) (hr : Chk ctx r A) : Chk ctx (.binary p l r) B := by
  have h := chk_binary (ctx := ctx) (p := p) (l := l) (r := r)
  rw [hp] at h; exact h hl hr

public theorem chk_okT (ctx : Context) : Chk ctx okT verdictTy :=
  chk_inject rfl rfl rfl (chk_unit ctx)

public theorem chk_refusedT (ctx : Context) (why : String) : Chk ctx (refusedT why) verdictTy :=
  chk_inject rfl rfl rfl (chk_label ctx why)

public theorem chk_guard {ctx : Context} {c rest : Term} {why : String} (hc : Chk ctx c .boolean)
    (hr : Chk ctx rest verdictTy) : Chk ctx (guard c why rest) verdictTy :=
  chk_ifBool hc hr (chk_refusedT ctx why)

public theorem chk_guards {ctx : Context} {rest : Term} : ∀ {l : List (Term × String)},
    (∀ p ∈ l, Chk ctx p.1 .boolean) → Chk ctx rest verdictTy → Chk ctx (guards l rest) verdictTy
  | [], _, hr => hr
  | (_, _) :: _, h, hr => chk_guard (h _ List.mem_cons_self) (chk_guards (fun p hp => h p (List.mem_cons_of_mem _ hp)) hr)

public theorem chk_allOf {ctx : Context} {l : List (Term × String)} (h : ∀ p ∈ l, Chk ctx p.1 .boolean) :
    Chk ctx (allOf l) verdictTy :=
  chk_guards h (chk_okT ctx)

public theorem chk_anyOf {ctx : Context} : ∀ {cs : List Term}, (∀ c ∈ cs, Chk ctx c .boolean) →
    Chk ctx (anyOf cs) .boolean
  | [], _ => chk_boolean ctx false
  | c :: _, h => chk_ifBool (h c List.mem_cons_self) (chk_boolean ctx true)
      (chk_anyOf fun c' hc => h c' (List.mem_cons_of_mem _ hc))

public theorem chk_andT {ctx : Context} {a b : Term} (ha : Chk ctx a .boolean) (hb : Chk ctx b .boolean) :
    Chk ctx (andT a b) .boolean := chk_ifBool ha hb (chk_boolean ctx false)

public theorem chk_notT {ctx : Context} {a : Term} (ha : Chk ctx a .boolean) : Chk ctx (notT a) .boolean :=
  chk_ifBool ha (chk_boolean ctx false) (chk_boolean ctx true)

/-- A field of a variable: `ctx[i]` has type `T`, whose field `f` is `M`. -/
public theorem chk_field {ctx : Context} {i : Nat} {b : Binding} {f : String} {M : Ty} (h : ctx[i]? = some b)
    (hm : rowMember b.type f = some M) : Chk ctx (.get (.bound i) f) M :=
  chk_get (syn_bound h) hm

/-! ## The law skeleton -/

/-- The context a clause is checked in: the occasion's payload, the request, the new state, the
old state. -/
@[expose] public def clauseCtx (S P : Ty) : Context :=
  [⟨P, .unrestricted⟩, ⟨reqTy, .unrestricted⟩, ⟨S, .unrestricted⟩, ⟨S, .unrestricted⟩]

/-- Each of the six clauses checks at `verdictTy` under its occasion's payload. -/
@[expose] public def Clauses (S : Ty) (b ad rl rt wr iv : At → Term) : Prop :=
  Chk (clauseCtx S .label) (ad ⟨1⟩) verdictTy ∧ Chk (clauseCtx S unitTy) (b ⟨1⟩) verdictTy ∧
  Chk (clauseCtx S .natural) (iv ⟨1⟩) verdictTy ∧ Chk (clauseCtx S .label) (rl ⟨1⟩) verdictTy ∧
  Chk (clauseCtx S unitTy) (rt ⟨1⟩) verdictTy ∧ Chk (clauseCtx S unitTy) (wr ⟨1⟩) verdictTy

/-- **A law checks at `lawTy S`**: the bidirectional checker accepts it closed, with no
annotations and empty assumptions. -/
@[expose] public def ChecksAt (law : Term) (S : Ty) : Prop :=
  ∃ c, checkAgainst ⟨law, noAnn, {}⟩ [] (lawTy S) = .ok c

theorem reqTy_canonical : reqTy.canonical = reqTy := by decide
theorem verdictTy_canonical : verdictTy.canonical = verdictTy := by decide

/-- A canonical row's members are canonical. -/
public theorem rowMember_isCanonical {f : String} {M : Ty} : ∀ {S : Ty}, S.isCanonical →
    rowMember S f = some M → M.isCanonical
  | .field n m t, ⟨hm, ht, _⟩, h => by
    simp only [rowMember] at h
    split at h
    · cases h; exact hm
    · exact rowMember_isCanonical ht h
  | .natural, _, h | .label, _, h | .boolean, _, h | .variable _, _, h | .arrow .., _, h
  | .emptyRow, _, h | .specification .., _, h | .prototype .., _, h | .custody _, _, h
  | .variant _, _, h | .computation .., _, h => by simp [rowMember] at h

/-- **A law built by `lawOf6` checks at `lawTy S` when its six clauses do.** -/
public theorem lawOf6_checks {S : Ty} {b ad rl rt wr iv : At → Term} (hS : S.isCanonical)
    (hsh : S.shareable = true) (h : Clauses S b ad rl rt wr iv) : ChecksAt (lawOf6 b ad rl rt wr iv) S := by
  obtain ⟨had, hb, hiv, hrl, hrt, hwr⟩ := h
  have hc := Ty.canonical_of_isCanonical hS
  have c0 : Clean [] := fun _ h => by cases h
  have c1 : Clean [⟨S, .unrestricted⟩] := c0.cons hsh
  have c2 : Clean [⟨S, .unrestricted⟩, ⟨S, .unrestricted⟩] := c1.cons hsh
  have c3 : Clean [⟨reqTy, .unrestricted⟩, ⟨S, .unrestricted⟩, ⟨S, .unrestricted⟩] := c2.cons rfl
  have body : Chk [⟨reqTy, .unrestricted⟩, ⟨S, .unrestricted⟩, ⟨S, .unrestricted⟩]
      (lawCase6 b ad rl rt wr iv) verdictTy := by
    refine chk_case c3 (syn_get (syn_bound rfl) rfl) rfl ?_ rfl (by simp)
    refine .cons rfl rfl had (.cons rfl rfl hb (.cons rfl rfl hiv (.cons rfl rfl hrl
      (.cons rfl rfl hrt (.cons rfl rfl hwr .nil)))))
  have l3 : Chk [⟨S, .unrestricted⟩, ⟨S, .unrestricted⟩] (.lam (lawCase6 b ad rl rt wr iv))
      (fnTy reqTy verdictTy) := chk_lam c2 (by rw [reqTy_canonical]; rfl)
        (by rw [reqTy_canonical, verdictTy_canonical]; exact body)
  have l2 : Chk [⟨S, .unrestricted⟩] (.lam (.lam (lawCase6 b ad rl rt wr iv)))
      (fnTy S (fnTy reqTy verdictTy)) := chk_lam c1 (by rw [hc]; exact hsh) (by
        rw [hc]; simp only [fnTy, Ty.canonical, reqTy_canonical, verdictTy_canonical]; exact l3)
  have l1 : Chk [] (lawOf6 b ad rl rt wr iv) (lawTy S) := chk_lam c0 (by rw [hc]; exact hsh) (by
        rw [hc]; simp only [fnTy, Ty.canonical, reqTy_canonical, verdictTy_canonical, hc]; exact l2)
  obtain ⟨r, hr⟩ := l1 c0.noLinear []
  have hl := Obend.Core.MachineTyping.source_uses_length r.derivation
  unfold ChecksAt checkAgainst Obend.Core.Bidirectional.checkAt
  simp only [hr, bind, Except.bind]
  rw [need_ok (safeUses_clean c0 hl), need_ok (validContext_clean c0), need_ok (by decide)]
  exact ⟨_, rfl⟩

/-- `lawOf` is `lawOf6` with one change clause. -/
public theorem lawOf_checks {S : Ty} {b ad rl rt c : At → Term} (hS : S.isCanonical)
    (hsh : S.shareable = true) (h : Clauses S b ad rl rt c c) : ChecksAt (lawOf S b ad rl rt c) S :=
  lawOf6_checks hS hsh h

/-! ## The generators -/

public theorem clean_clause {S P : Ty} (hsh : S.shareable = true) (hP : P.shareable = true) :
    Clean (clauseCtx S P) := by
  have c0 : Clean [] := fun _ h => by cases h
  exact ((c0.cons hsh).cons hsh |>.cons rfl).cons hP

theorem forall_pair {p : Term × String → Prop} {c : Term} {w : String} {l : List (Term × String)}
    (h : p (c, w)) (hl : ∀ q ∈ l, p q) : ∀ q ∈ (c, w) :: l, p q := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact h
  · exact hl q hq

theorem forall_nil {p : Term × String → Prop} : ∀ q ∈ ([] : List (Term × String)), p q := by
  intro q hq; cases hq

/-- A scalar type: what `eqAt` compares. -/
@[expose] public def Scalar (T : Ty) : Prop := T = .natural ∨ T = .label ∨ T = .boolean

theorem Scalar.shareable {T : Ty} (h : Scalar T) : T.shareable = true := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem chk_eqAt {ctx : Context} {T : Ty} {x y : Term} (hT : Scalar T) (hx : Chk ctx x T)
    (hy : Chk ctx y T) : Chk ctx (eqAt T x y) .boolean := by
  rcases hT with rfl | rfl | rfl
  · exact chk_bin rfl hx hy
  · exact chk_bin rfl hx hy
  · exact chk_ifBool hx hy (chk_notT hy)

mutual
/-- A type `eqAt` compares at: a scalar, or a record type each of whose fields is one. -/
public inductive EqTy : Ty → Prop
  | scalar {T : Ty} : Scalar T → EqTy T
  | row {T : Ty} : EqRow T T → EqTy T
/-- `EqRow T R`: every field of the row `R` is a field of `T` (as `get` finds it) at an `EqTy` type. -/
public inductive EqRow : Ty → Ty → Prop
  | nil {T : Ty} : EqRow T .emptyRow
  | cons {T : Ty} {f : String} {M tail : Ty} : rowMember T f = some M → EqTy M → EqRow T tail →
      EqRow T (.field f M tail)
end

/-- A term both synthesizes and checks at `T`, as a variable and a field selection do. -/
@[expose] public def SynChk (ctx : Context) (t : Term) (T : Ty) : Prop := Syn ctx t T ∧ Chk ctx t T

public theorem synChk_bound {ctx : Context} {i : Nat} {b : Binding} (h : ctx[i]? = some b) :
    SynChk ctx (.bound i) b.type := ⟨syn_bound h, chk_bound h⟩

public theorem synChk_get {ctx : Context} {t : Term} {T M : Ty} {f : String} (h : Syn ctx t T)
    (hm : rowMember T f = some M) : SynChk ctx (.get t f) M := ⟨syn_get h hm, chk_get h hm⟩

public theorem synChk_field {ctx : Context} {i : Nat} {b : Binding} {f : String} {M : Ty}
    (h : ctx[i]? = some b) (hm : rowMember b.type f = some M) : SynChk ctx (.get (.bound i) f) M :=
  synChk_get (syn_bound h) hm

mutual
/-- **`eqAt T` checks at `boolean`** for every `EqTy` type, records included. -/
public theorem chk_eqTy {ctx : Context} {T : Ty} {x y : Term} : EqTy T → SynChk ctx x T → SynChk ctx y T →
    Chk ctx (eqAt T x y) .boolean
  | .scalar hs, hx, hy => chk_eqAt hs hx.2 hy.2
  | .row hr, hx, hy => chk_eqRow hr hx.1 hy.1
public theorem chk_eqRow {ctx : Context} {T R : Ty} {x y : Term} : EqRow T R → Syn ctx x T → Syn ctx y T →
    Chk ctx (eqAt R x y) .boolean
  | .nil, _, _ => chk_boolean _ _
  | .cons hm hM ht, hx, hy => chk_andT (chk_eqTy hM (synChk_get hx hm) (synChk_get hy hm)) (chk_eqRow ht hx hy)
end

mutual
public theorem EqTy.shareable {T : Ty} : EqTy T → T.shareable = true
  | .scalar hs => hs.shareable
  | .row hr => EqRow.shareable hr
public theorem EqRow.shareable {T R : Ty} : EqRow T R → R.shareable = true
  | .nil => rfl
  | .cons _ hM ht => by simp [Ty.shareable, EqTy.shareable hM, EqRow.shareable ht]
end

/-- **`ownerSigns S` checks at `lawTy S`** for every canonical, shareable `S`. -/
public theorem ownerSigns_checks {S : Ty} (hS : S.isCanonical) (hsh : S.shareable = true) :
    ChecksAt (ownerSigns S) S := by
  have c (P : Ty) : Chk (clauseCtx S P) (allOf [(eqLabel ((⟨1⟩ : At).reqF "agent") ((⟨1⟩ : At).reqF "principal"),
      "not signed by the owner")]) verdictTy :=
    chk_allOf (forall_pair (chk_bin rfl (chk_field rfl rfl) (chk_field rfl rfl)) forall_nil)
  exact lawOf_checks hS hsh ⟨c _, c _, c _, c _, c _, c _⟩

theorem chk_listed {S P : Ty} (ids : List String) :
    Chk (clauseCtx S P) (listedT ids ⟨1⟩) .boolean := by
  apply chk_anyOf
  intro c hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
  exact chk_bin rfl (chk_field rfl rfl) (chk_label _ i)

/-- **`allowlistLaw S ids` checks at `lawTy S`.** -/
public theorem allowlist_checks {S : Ty} (ids : List String) (hS : S.isCanonical) (hsh : S.shareable = true) :
    ChecksAt (allowlistLaw S ids) S := by
  have c (P : Ty) : Chk (clauseCtx S P) (allOf [(listedT ids ⟨1⟩, "not on the allowlist")]) verdictTy :=
    chk_allOf (forall_pair (chk_listed ids) forall_nil)
  exact lawOf_checks hS hsh ⟨c _, c _, c _, c _, c _, c _⟩

/-- **`bounded S f max` checks at `lawTy S`** when `f` is a natural field of `S`. -/
public theorem bounded_checks {S : Ty} (f : String) (max : Nat) (hS : S.isCanonical)
    (hsh : S.shareable = true) (hf : rowMember S f = some .natural) : ChecksAt (bounded S f max) S := by
  have c (P : Ty) : Chk (clauseCtx S P) (allOf [(leNat ((⟨1⟩ : At).newF f) (natT max), f ++ " over the bound")])
      verdictTy :=
    chk_allOf (forall_pair (chk_bin rfl (chk_field rfl hf) (chk_nat _ _)) forall_nil)
  exact lawOf_checks hS hsh ⟨c _, c _, c _, chk_okT _, chk_okT _, c _⟩

/-- **`windowedLaw S T W limit g` checks at `lawTy S`** when `S` has natural `count` and `epoch`
and a field `g` of a type `eqAt` compares (`EqTy`: a scalar, or a record of such). -/
public theorem windowed_checks {S T : Ty} (W limit : Nat) (g : String) (hS : S.isCanonical)
    (hsh : S.shareable = true) (hT : EqTy T) (hcount : rowMember S "count" = some .natural)
    (hepoch : rowMember S "epoch" = some .natural) (hg : rowMember S g = some T) :
    ChecksAt (windowedLaw S T W limit g) S := by
  have epoch (P : Ty) : ∀ q ∈ inOneEpoch W ⟨1⟩, Chk (clauseCtx S P) q.1 .boolean :=
    forall_pair (chk_bin rfl (chk_bin rfl (chk_field rfl rfl) (chk_nat _ _)) (chk_bin rfl (chk_field rfl rfl) (chk_nat _ _)))
      (forall_pair (chk_bin rfl (chk_field rfl hepoch) (chk_bin rfl (chk_field rfl rfl) (chk_nat _ _))) forall_nil)
  have inc (P : Ty) : Chk (clauseCtx S P)
      (Term.ifBool (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)) (natT 0) (natT 1)) .natural :=
    chk_ifBool (chk_eqTy hT (synChk_field rfl hg) (synChk_field rfl hg)) (chk_nat _ _) (chk_nat _ _)
  have fresh (P : Ty) : Chk (clauseCtx S P) (guards (inOneEpoch W ⟨1⟩)
      (allOf [(eqNat ((⟨1⟩ : At).newF "count") (natT 0), "count at birth")])) verdictTy :=
    chk_guards (epoch P) (chk_allOf (forall_pair (chk_bin rfl (chk_field rfl hcount) (chk_nat _ _)) forall_nil))
  have change (P : Ty) : Chk (clauseCtx S P) (guards (inOneEpoch W ⟨1⟩)
      (.ifBool (eqNat ((⟨1⟩ : At).newF "epoch") ((⟨1⟩ : At).oldF "epoch"))
        (allOf [(eqNat ((⟨1⟩ : At).newF "count") (addNat ((⟨1⟩ : At).oldF "count")
            (Term.ifBool (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)) (natT 0) (natT 1))), "count not bumped"),
                (leNat ((⟨1⟩ : At).newF "count") (natT limit), "over the rate limit")])
        (allOf [(ltNat ((⟨1⟩ : At).oldF "epoch") ((⟨1⟩ : At).newF "epoch"), "epoch went back"),
                (eqNat ((⟨1⟩ : At).newF "count")
                  (Term.ifBool (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)) (natT 0) (natT 1)), "count not reset"),
                (leNat ((⟨1⟩ : At).newF "count") (natT limit), "over the rate limit")]))) verdictTy := by
    refine chk_guards (epoch P) (chk_ifBool (chk_bin rfl (chk_field rfl hepoch) (chk_field rfl hepoch)) ?_ ?_)
    · exact chk_allOf (forall_pair (chk_bin rfl (chk_field rfl hcount) (chk_bin rfl (chk_field rfl hcount) (inc P)))
        (forall_pair (chk_bin rfl (chk_field rfl hcount) (chk_nat _ _)) forall_nil))
    · exact chk_allOf (forall_pair (chk_bin rfl (chk_field rfl hepoch) (chk_field rfl hepoch))
        (forall_pair (chk_bin rfl (chk_field rfl hcount) (inc P))
          (forall_pair (chk_bin rfl (chk_field rfl hcount) (chk_nat _ _)) forall_nil)))
  exact lawOf_checks hS hsh ⟨fresh _, fresh _, change _, chk_okT _, chk_okT _, change _⟩

/-! ### Machines -/

/-- The row of `stateTy states`. -/
@[expose] public def stateRow (states : List String) : Ty :=
  states.foldr (fun s row => .field s .emptyRow row) .emptyRow

theorem rowMember_stateRow {y : String} : ∀ {states : List String}, y ∈ states →
    rowMember (stateRow states) y = some .emptyRow
  | x :: xs, h => by
    simp only [stateRow, List.foldr_cons, rowMember]
    split
    · rfl
    · rename_i hne
      have : y ∈ xs := by
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd rfl hne
        · exact h
      exact rowMember_stateRow this

theorem labelsDistinct_states {s : String} : ∀ {states : List String}, states.Nodup →
    labelsDistinct (states.map fun x => (x, Term.boolean (decide (x = s)))) = true
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 h
    simp only [List.map_cons, labelsDistinct, Bool.and_eq_true, Bool.not_eq_true',
      List.any_eq_false, List.mem_map, beq_iff_eq]
    refine ⟨?_, labelsDistinct_states hxs⟩
    rintro _ ⟨y, hy, rfl⟩ rfl
    exact hx hy

theorem armsChk_states {ctx : Context} {states : List String} {s : String} :
    ∀ ys : List String, (∀ y ∈ ys, y ∈ states) →
      ArmsChk ctx (stateRow states) .boolean (stateRow ys) (ys.map fun x => (x, Term.boolean (decide (x = s))))
  | [], _ => .nil
  | y :: ys, h => .cons (rowMember_stateRow (h y List.mem_cons_self)) rfl (chk_boolean _ _)
      (armsChk_states ys fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- `isState states t s` checks at `boolean` when `t` synthesizes the (canonical) state sum. -/
theorem chk_isState {ctx : Context} {states : List String} {t : Term} {s : String} (hctx : Clean ctx)
    (hnd : states.Nodup) (hne : states ≠ []) (hcan : (stateTy states).isCanonical)
    (ht : Syn ctx t (stateTy states)) : Chk ctx (isState states t s) .boolean :=
  chk_case hctx ht (Ty.canonical_of_isCanonical hcan) (armsChk_states states fun _ h => h)
    (labelsDistinct_states hnd) (by simpa [List.map_eq_nil_iff] using hne)

/-- **`machineLaw S f states initial edges` checks at `lawTy S`** when `f` is a field of `S` of the
state sum over `states` (distinct, nonempty). -/
public theorem machine_checks {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} (hS : S.isCanonical) (hsh : S.shareable = true)
    (hf : rowMember S f = some (stateTy states)) (hnd : states.Nodup) (hne : states ≠ []) :
    ChecksAt (machineLaw S f states initial edges) S := by
  have hcan := rowMember_isCanonical hS hf
  have start (P : Ty) (hP : P.shareable = true) : Chk (clauseCtx S P)
      (allOf [(isState states ((⟨1⟩ : At).newF f) initial, f ++ " does not start at " ++ initial)]) verdictTy :=
    chk_allOf (forall_pair (chk_isState (clean_clause hsh hP) hnd hne hcan (syn_get (syn_bound rfl) hf))
      forall_nil)
  have invoke : Chk (clauseCtx S .natural) (allOf [(anyOf (edges.map fun (x, m, y) =>
      andT (eqNat (⟨1⟩ : At).payload (natT m))
        (andT (isState states ((⟨1⟩ : At).oldF f) x) (isState states ((⟨1⟩ : At).newF f) y))), "no edge")])
      verdictTy := by
    refine chk_allOf (forall_pair (chk_anyOf ?_) forall_nil)
    intro c hc
    obtain ⟨⟨x, m, y⟩, _, rfl⟩ := List.mem_map.1 hc
    have cl := clean_clause (P := .natural) hsh rfl
    exact chk_andT (chk_bin rfl (chk_bound (i := 0) (b := ⟨.natural, .unrestricted⟩) rfl) (chk_nat _ _))
      (chk_andT (chk_isState cl hnd hne hcan (syn_get (syn_bound rfl) hf))
        (chk_isState cl hnd hne hcan (syn_get (syn_bound rfl) hf)))
  exact lawOf6_checks hS hsh ⟨start _ rfl, start _ rfl, invoke, chk_refusedT _ _, chk_refusedT _ _,
    chk_refusedT _ _⟩

/-- The checked generator: whatever `machine` emits checks at `lawTy S`. -/
public theorem machine_ok_checks {S : Ty} {f : String} {states : List String} {initial : String}
    {methods : List String} {edges : List (String × String × String)} {law : Term}
    (hS : S.isCanonical) (hsh : S.shareable = true) (hf : rowMember S f = some (stateTy states))
    (h : machine S f states initial methods edges = .ok law) : ChecksAt law S := by
  unfold machine Obend.Law.need at h
  simp only [bind, Except.bind] at h
  split at h <;> try (simp at h)
  rename_i hnd
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  rename_i hin
  split at h <;> try (simp at h)
  cases h
  have hne : states ≠ [] := by rintro rfl; simp at hin
  exact machine_checks hS hsh hf (by simpa using hnd) hne

/-! ### Quorum -/

theorem chk_bit {ctx : Context} {t : Term} (i : Nat) (h : Chk ctx t .natural) : Chk ctx (bit t i) .natural :=
  chk_bin rfl (chk_bin rfl h (chk_nat _ _)) (chk_nat _ _)

theorem chk_foldl_bits {ctx : Context} {t : Term} (h : Chk ctx t .natural) :
    ∀ (l : List Nat) {acc : Term}, Chk ctx acc .natural →
      Chk ctx (l.foldl (fun acc i => addNat acc (bit t i)) acc) .natural
  | [], _, ha => ha
  | i :: l, _, ha => chk_foldl_bits h l (chk_bin rfl ha (chk_bit i h))

theorem chk_popcount {ctx : Context} {t : Term} (cnt : Nat) (h : Chk ctx t .natural) :
    Chk ctx (popcount t cnt) .natural :=
  chk_foldl_bits h _ (chk_nat _ _)

theorem proposalTy_canonical {T : Ty} (hT : T.isCanonical) : (proposalTy T).canonical = proposalTy T := by
  simp [proposalTy, Ty.canonical, Ty.canonical_of_isCanonical hT, Ty.insertCanonical]

/-- **`quorumLaw S T members k g` checks at `lawTy S`** when `S` has a natural `approvals`, a
`proposal` of `proposalTy T` and a field `g` of a type `eqAt` compares (`EqTy`: a scalar, or a record of such). -/
public theorem quorum_checks {S T : Ty} (members : List String) (k : Nat) (g : String)
    (hS : S.isCanonical) (hsh : S.shareable = true) (hT : EqTy T)
    (hap : rowMember S "approvals" = some .natural) (hpr : rowMember S "proposal" = some (proposalTy T))
    (hg : rowMember S g = some T) : ChecksAt (quorumLaw S T members k g) S := by
  have hTs := hT.shareable
  have pc := proposalTy_canonical (rowMember_isCanonical hS hg)
  have reset (P : Ty) : Chk (clauseCtx S P) (eqNat ((⟨1⟩ : At).newF "approvals") (natT 0)) .boolean :=
    chk_bin rfl (chk_field rfl hap) (chk_nat _ _)
  have fresh (P : Ty) : Chk (clauseCtx S P) (allOf [(eqNat ((⟨1⟩ : At).newF "approvals") (natT 0),
      "approvals at birth")]) verdictTy := chk_allOf (forall_pair (reset P) forall_nil)
  have quorate (P : Ty) : Chk (clauseCtx S P)
      (leNat (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length)) .boolean :=
    chk_bin rfl (chk_nat _ _) (chk_popcount _ (chk_field rfl hap))
  have member (P : Ty) : Chk (clauseCtx S P) (isMember members ⟨1⟩) .boolean := chk_listed members
  have relaw : Chk (clauseCtx S .label) (guards [(isMember members ⟨1⟩, "not a member")]
      (allOf [(leNat (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length), "no quorum"),
        (proposedLaws ⟨1⟩, "not the proposal")])) verdictTy := by
    refine chk_guards (forall_pair (member _) forall_nil)
      (chk_allOf (forall_pair (quorate _) (forall_pair ?_ forall_nil)))
    have cl := clean_clause (P := .label) hsh rfl
    refine chk_case cl (syn_get (syn_bound rfl) hpr) pc ?_ rfl (by simp)
    exact .cons rfl rfl (chk_bin rfl (chk_bound (i := 0) (b := ⟨.label, .unrestricted⟩) rfl)
        (chk_bound (i := 1) (b := ⟨.label, .unrestricted⟩) rfl))
      (.cons rfl hTs (chk_boolean _ _) .nil)
  have change (P : Ty) (hP : P.shareable = true) : Chk (clauseCtx S P)
      (guards [(isMember members ⟨1⟩, "not a member"),
            (ltNat ((⟨1⟩ : At).newF "approvals") (natT (pow2 members.length)), "approvals out of range")]
      (.ifBool (notT (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)))
        (allOf [(leNat (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length), "no quorum"),
                (proposedSet T g ⟨1⟩, "not the proposal"),
                (eqNat ((⟨1⟩ : At).newF "approvals") (natT 0), "approvals not reset")])
        (.ifBool (notT (sameProposal T ⟨1⟩ (fun b => b.newF "proposal") (fun b => b.oldF "proposal")))
          (allOf [(eqNat ((⟨1⟩ : At).newF "approvals") (natT 0), "approvals not reset")])
          (.ifBool (eqNat ((⟨1⟩ : At).newF "approvals") ((⟨1⟩ : At).oldF "approvals")) okT
            (guard (anyOf (members.zipIdx.map fun (m, i) => approvalBy ⟨1⟩ m i)) "not an approval" okT)))))
      verdictTy := by
    have cl := clean_clause hsh hP
    have clL := cl.cons (T := .label) rfl
    have clT := cl.cons hTs
    refine chk_guards (forall_pair (member _) (forall_pair
      (chk_bin rfl (chk_field rfl hap) (chk_nat _ _)) forall_nil)) ?_
    refine chk_ifBool (chk_notT (chk_eqTy hT (synChk_field rfl hg) (synChk_field rfl hg))) ?_ ?_
    · refine chk_allOf (forall_pair (quorate _) (forall_pair ?_ (forall_pair (reset _) forall_nil)))
      refine chk_case cl (syn_get (syn_bound rfl) hpr) pc ?_ rfl (by simp)
      exact .cons rfl rfl (chk_boolean _ _) (.cons rfl hTs
        (chk_eqTy hT (synChk_bound (i := 0) (b := ⟨T, .unrestricted⟩) rfl) (synChk_field rfl hg)) .nil)
    refine chk_ifBool (chk_notT ?_) (chk_allOf (forall_pair (reset _) forall_nil)) ?_
    · refine chk_case cl (syn_get (syn_bound rfl) hpr) pc ?_ rfl (by simp)
      refine .cons rfl rfl ?_ (.cons rfl hTs ?_ .nil)
      · refine chk_case clL (syn_get (syn_bound rfl) hpr) pc ?_ rfl (by simp)
        exact .cons rfl rfl (chk_bin rfl (chk_bound (i := 0) (b := ⟨.label, .unrestricted⟩) rfl)
            (chk_bound (i := 1) (b := ⟨.label, .unrestricted⟩) rfl))
          (.cons rfl hTs (chk_boolean _ _) .nil)
      · refine chk_case clT (syn_get (syn_bound rfl) hpr) pc ?_ rfl (by simp)
        exact .cons rfl rfl (chk_boolean _ _) (.cons rfl hTs
          (chk_eqTy hT (synChk_bound (i := 0) (b := ⟨T, .unrestricted⟩) rfl)
            (synChk_bound (i := 1) (b := ⟨T, .unrestricted⟩) rfl)) .nil)
    refine chk_ifBool (chk_bin rfl (chk_field rfl hap) (chk_field rfl hap)) (chk_okT _)
      (chk_guard (chk_anyOf ?_) (chk_okT _))
    intro c hc
    obtain ⟨⟨m, i⟩, _, rfl⟩ := List.mem_map.1 hc
    exact chk_andT (chk_bin rfl (chk_bit i (chk_field rfl hap)) (chk_nat _ _))
      (chk_andT (chk_bin rfl (chk_field rfl hap) (chk_bin rfl (chk_field rfl hap) (chk_nat _ _)))
        (chk_bin rfl (chk_field rfl rfl) (chk_label _ _)))
  exact lawOf_checks hS hsh ⟨fresh _, fresh _, change _ rfl, relaw, chk_refusedT _ _, change _ rfl⟩

/-- The checked generators: whatever they emit checks. -/
public theorem allowlist_ok_checks {S : Ty} {ids : List String} {law : Term} (hS : S.isCanonical)
    (hsh : S.shareable = true) (h : allowlist S ids = .ok law) : ChecksAt law S := by
  unfold allowlist Obend.Law.need at h
  simp only [bind, Except.bind] at h
  split at h <;> try (simp at h)
  cases h; exact allowlist_checks ids hS hsh

public theorem windowed_ok_checks {S T : Ty} {W limit : Nat} {g : String} {law : Term}
    (hS : S.isCanonical) (hsh : S.shareable = true) (hT : EqTy T)
    (hcount : rowMember S "count" = some .natural) (hepoch : rowMember S "epoch" = some .natural)
    (hg : rowMember S g = some T) (h : windowed S T W limit g = .ok law) : ChecksAt law S := by
  unfold windowed Obend.Law.need at h
  simp only [bind, Except.bind] at h
  split at h <;> try (simp at h)
  cases h; exact windowed_checks W limit g hS hsh hT hcount hepoch hg

public theorem quorum_ok_checks {S T : Ty} {members : List String} {k : Nat} {g : String} {law : Term}
    (hS : S.isCanonical) (hsh : S.shareable = true) (hT : EqTy T)
    (hap : rowMember S "approvals" = some .natural) (hpr : rowMember S "proposal" = some (proposalTy T))
    (hg : rowMember S g = some T) (h : quorum S T members k g = .ok law) : ChecksAt law S := by
  unfold quorum Obend.Law.need at h
  simp only [bind, Except.bind] at h
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  cases h; exact quorum_checks members k g hS hsh hT hap hpr hg

/-! ## Laws in an outer context, application, and `keeps`

`keeps S I` applies a closed invariant `I` in each clause. An unannotated lambda does not
synthesize, so the algorithmic checker cannot type `keeps S I` without an annotation at the
application; the declarative system can. `keeps_typed` says: when `I` is checked (with whatever
annotations it carries) at `S → boolean`, `keeps S I` has a derivation at `lawTy S`. The proof
types `keepsOpen S`, the law with the invariant a VARIABLE of that type, by the checker itself
(`keepsOpen_checked`), and substitutes `I` for it (`TypedSubstitution.checked_msubst`). -/

public theorem Clean.append {Γ Δ : Context} (h1 : Clean Γ) (h2 : Clean Δ) : Clean (Γ ++ Δ) := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact h1 b hb
  · exact h2 b hb

/-- An application: the function synthesizes a reusable arrow, the argument checks at its domain. -/
public theorem chk_app {ctx : Context} {f a : Term} {D C : Ty} (hctx : Clean ctx) (hD : D.canonical.shareable = true)
    (hf : Syn ctx f (fnTy D C)) (ha : Chk ctx a D.canonical) : Chk ctx (.app f a) C.canonical := by
  intro hn path
  obtain ⟨r, hr, hT⟩ := hf hn (path ++ [0])
  obtain ⟨b, hb⟩ := ha hn (path ++ [1])
  have hl := Obend.Core.MachineTyping.source_uses_length b.derivation
  simp only [elaborate, noAnn, hr, bind, Except.bind]
  split
  · rename_i reuse q dom cod hs
    have hw : representativeHead {} noAnn path r.type = .arrow .reusable .unrestricted D.canonical C.canonical := by
      rw [hT]; rfl
    rw [hw] at hs
    simp only [Obend.Core.Check.callable] at hs
    cases hs
    simp only [hb]
    have hallow : argumentAllowed {} .unrestricted ctx D.canonical b.uses = true := by
      have hcomp : D.canonical.isComputation = false := by
        cases hc : D.canonical <;> simp_all [Ty.isComputation, Ty.shareable]
      simp [argumentAllowed, hcomp, hD, reusableCaptures_clean hctx hl,
        linearFree_of_reusableCaptures (reusableCaptures_clean hctx hl)]
    rw [need_ok hallow]
    exact finish_check _ _ _ rfl
  · rename_i hs
    have hw : representativeHead {} noAnn path r.type = .arrow .reusable .unrestricted D.canonical C.canonical := by
      rw [hT]; rfl
    rw [hw] at hs
    exact absurd rfl (hs .reusable .unrestricted D.canonical C.canonical)

/-- Each of the six clauses checks at `verdictTy` under its payload, with `Γ` outside the law. -/
@[expose] public def ClausesIn (Γ : Context) (S : Ty) (b ad rl rt wr iv : At → Term) : Prop :=
  Chk (clauseCtx S .label ++ Γ) (ad ⟨1⟩) verdictTy ∧ Chk (clauseCtx S unitTy ++ Γ) (b ⟨1⟩) verdictTy ∧
  Chk (clauseCtx S .natural ++ Γ) (iv ⟨1⟩) verdictTy ∧ Chk (clauseCtx S .label ++ Γ) (rl ⟨1⟩) verdictTy ∧
  Chk (clauseCtx S unitTy ++ Γ) (rt ⟨1⟩) verdictTy ∧ Chk (clauseCtx S unitTy ++ Γ) (wr ⟨1⟩) verdictTy

/-- **A law built by `lawOf6` checks at `lawTy S` in an outer context `Γ`** when its clauses do. -/
public theorem lawOf6_chk_in {S : Ty} {Γ : Context} {b ad rl rt wr iv : At → Term} (hS : S.isCanonical)
    (hsh : S.shareable = true) (hΓ : Clean Γ) (h : ClausesIn Γ S b ad rl rt wr iv) :
    Chk Γ (lawOf6 b ad rl rt wr iv) (lawTy S) := by
  obtain ⟨had, hb, hiv, hrl, hrt, hwr⟩ := h
  have hc := Ty.canonical_of_isCanonical hS
  have c1 : Clean (⟨S, .unrestricted⟩ :: Γ) := hΓ.cons hsh
  have c2 : Clean (⟨S, .unrestricted⟩ :: ⟨S, .unrestricted⟩ :: Γ) := c1.cons hsh
  have c3 : Clean (⟨reqTy, .unrestricted⟩ :: ⟨S, .unrestricted⟩ :: ⟨S, .unrestricted⟩ :: Γ) := c2.cons rfl
  have body : Chk (⟨reqTy, .unrestricted⟩ :: ⟨S, .unrestricted⟩ :: ⟨S, .unrestricted⟩ :: Γ)
      (lawCase6 b ad rl rt wr iv) verdictTy := by
    refine chk_case c3 (syn_get (syn_bound rfl) rfl) rfl ?_ rfl (by simp)
    refine .cons rfl rfl had (.cons rfl rfl hb (.cons rfl rfl hiv (.cons rfl rfl hrl
      (.cons rfl rfl hrt (.cons rfl rfl hwr .nil)))))
  have l3 : Chk (⟨S, .unrestricted⟩ :: ⟨S, .unrestricted⟩ :: Γ) (.lam (lawCase6 b ad rl rt wr iv))
      (fnTy reqTy verdictTy) := chk_lam c2 (by rw [reqTy_canonical]; rfl)
        (by rw [reqTy_canonical, verdictTy_canonical]; exact body)
  have l2 : Chk (⟨S, .unrestricted⟩ :: Γ) (.lam (.lam (lawCase6 b ad rl rt wr iv)))
      (fnTy S (fnTy reqTy verdictTy)) := chk_lam c1 (by rw [hc]; exact hsh) (by
        rw [hc]; simp only [fnTy, Ty.canonical, reqTy_canonical, verdictTy_canonical]; exact l3)
  exact chk_lam hΓ (by rw [hc]; exact hsh) (by
        rw [hc]; simp only [fnTy, Ty.canonical, reqTy_canonical, verdictTy_canonical, hc]; exact l2)

/-- The binding of a `keeps` invariant: a reusable `S → boolean`. -/
@[expose] public def invBinding (S : Ty) : Binding := ⟨fnTy S .boolean, .unrestricted⟩

/-- `keeps S` with its invariant a free variable (index `0` outside the law). -/
@[expose] public def keepsOpen (S : Ty) : Term :=
  let c (a : At) := guard (.app (.bound (a.depth + 3)) a.new) "invariant" okT
  lawOf S c c (fun _ => okT) c c

theorem chk_keepsClause {S P : Ty} (hS : S.isCanonical) (hsh : S.shareable = true) (hP : P.shareable = true) :
    Chk (clauseCtx S P ++ [invBinding S])
      (guard (.app (.bound ((⟨1⟩ : At).depth + 3)) (⟨1⟩ : At).new) "invariant" okT) verdictTy := by
  have hc := Ty.canonical_of_isCanonical hS
  have cl : Clean (clauseCtx S P ++ [invBinding S]) :=
    (clean_clause hsh hP).append (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb; exact ⟨rfl, by simp [invBinding, fnTy, Ty.shareable]⟩)
  refine chk_guard ?_ (chk_okT _)
  have := chk_app (D := S) (C := .boolean) cl (by rw [hc]; exact hsh)
    (syn_bound (i := 4) (b := invBinding S) rfl) (by rw [hc]; exact chk_bound (i := 2) (b := ⟨S, .unrestricted⟩) rfl)
  exact this

/-- **`keepsOpen S` checks at `lawTy S` with the invariant a variable of type `S → boolean`.** -/
public theorem keepsOpen_checked {S : Ty} (hS : S.isCanonical) (hsh : S.shareable = true) :
    ∃ c : Checked ⟨keepsOpen S, noAnn, {}⟩ [invBinding S], c.type = lawTy S := by
  have cΓ : Clean [invBinding S] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb; exact ⟨rfl, by simp [invBinding, fnTy, Ty.shareable]⟩
  have hk : Chk [invBinding S] (keepsOpen S) (lawTy S) :=
    lawOf6_chk_in hS hsh cΓ ⟨chk_keepsClause hS hsh rfl, chk_keepsClause hS hsh rfl,
      chk_keepsClause hS hsh rfl, chk_okT _, chk_keepsClause hS hsh rfl, chk_keepsClause hS hsh rfl⟩
  obtain ⟨r, hr⟩ := hk cΓ.noLinear []
  have hl := Obend.Core.MachineTyping.source_uses_length r.derivation
  have : ∃ c, checkAgainst ⟨keepsOpen S, noAnn, {}⟩ [invBinding S] (lawTy S) = .ok c := by
    unfold checkAgainst Obend.Core.Bidirectional.checkAt
    simp only [hr, bind, Except.bind]
    rw [need_ok (safeUses_clean cΓ hl), need_ok (validContext_clean cΓ), need_ok (by decide)]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := this
  refine ⟨c, ?_⟩
  unfold checkAgainst at hc
  simp only [bind, Except.bind] at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc
      · split at hc
        · cases hc
        · cases hc; rfl

theorem checkAgainst_type {src : AnnotatedTerm} {ctx : Context} {T : Ty} {c : Checked src ctx}
    (h : checkAgainst src ctx T = .ok c) : c.type = T := by
  unfold checkAgainst at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; rfl

/-- A law has a derivation at `lawTy S` in the declarative system (`PartialTyping`), closed. -/
@[expose] public def Typed (law : Term) (S : Ty) : Prop :=
  ∃ uses, Obend.Core.Check.PartialTyping {} [] law (lawTy S) uses

/-- What the checker accepts has a derivation. -/
public theorem ChecksAt.typed {law : Term} {S : Ty} (h : ChecksAt law S) : Typed law S := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c.uses, checkAgainst_type hc ▸ c.derivation⟩

/-- **`keeps S I` is typed at `lawTy S`** whenever its invariant `I` (a closed term, with whatever
annotations it carries) is checked at `S → boolean`. -/
public theorem keeps_typed {S : Ty} (hS : S.isCanonical) (hsh : S.shareable = true) {I : AnnotatedTerm}
    (hasm : I.assumptions = {}) (closed : Obend.Core.Invariant.Scoped 0 I.term)
    (hI : ∃ c : Checked I [], c.type = fnTy S .boolean) : Typed (keeps S I.term) S := by
  obtain ⟨c, hc⟩ := keepsOpen_checked hS hsh
  obtain ⟨ci, hci⟩ := hI
  let σ : Nat → Option AnnotatedTerm := fun x => if x = 0 then some I else none
  have hσ : ∀ x f, σ x = some f → Obend.Core.Invariant.Scoped 0 f.term ∧
      f.assumptions = (⟨keepsOpen S, noAnn, {}⟩ : AnnotatedTerm).assumptions ∧
      ∃ b : Binding, [invBinding S][x]? = some b ∧ ∃ d : Checked f [invBinding S], d.type = b.type := by
    intro x f hf
    by_cases hx : x = 0
    · subst hx
      simp only [σ, if_pos rfl, Option.some.injEq] at hf
      subst hf
      refine ⟨closed, hasm, invBinding S, rfl, ?_⟩
      have hv : validContext I.assumptions.shareableVariables [invBinding S] = true := by
        rw [hasm]; simp [validContext, invBinding, fnTy, Ty.shareable]
      obtain ⟨_, d⟩ := Obend.Core.Proofs.TypedSubstitution.partialTyping_closed_transport ci.derivation
        closed [invBinding S] hv
      refine ⟨⟨ci.type, zeroUses [invBinding S], d, by simp [safeUses, zeroUses, invBinding, safeQuantity], hv,
        ci.assumptionsValid⟩, ?_⟩
      simp [hci, invBinding]
    · simp [σ, hx] at hf
  obtain ⟨c', hc', _⟩ := Obend.Core.Proofs.TypedSubstitution.checked_msubst c σ hσ
  have hren : ∀ f, I.term.rename f = I.term := fun f =>
    Obend.Core.Invariant.scoped_rename_identity closed f (fun _ h => absurd h (Nat.not_lt_zero _))
  have hfill : Obend.Core.Proofs.Substitution.fillTerm σ 0 = fun i => if i = 0 then I.term else .bound i := by
    funext i
    rw [Obend.Core.Proofs.Substitution.fillTerm_zero]
    by_cases hi : i = 0
    · subst hi; simp [σ]
    · simp [σ, hi]
  have heq : (Obend.Core.Proofs.Substitution.msubst σ ⟨keepsOpen S, noAnn, {}⟩).term = keeps S I.term := by
    simp only [Obend.Core.Proofs.Substitution.msubst, hfill]
    simp [keepsOpen, keeps, lawOf, lawCase, lawCase6, law3, guard, refusedT, okT, At.new, Term.substitute,
      Obend.Core.Term.liftSubstitution, hren, Term.rename]
  have hsc : Obend.Core.Invariant.Scoped 0 (keeps S I.term) := by
    rw [← heq]
    have h1 := Obend.Core.Proofs.Substitution.typed_scoped c.derivation
    simp only [Obend.Core.Proofs.Substitution.msubst, hfill]
    refine Obend.Core.Invariant.scoped_substitute h1 _ 0 ?_
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    simpa using closed
  have d := c'.derivation
  simp only [AnnotatedTerm.erase, heq] at d
  obtain ⟨_, d'⟩ := Obend.Core.Proofs.TypedSubstitution.partialTyping_closed_transport d hsc [] rfl
  rw [hc', hc] at d'
  exact ⟨_, d'⟩

/-! ## Teeth

The hypotheses are inhabited (concrete canonical state types the stdlib teeth use, typed at the
fields they read), and they are needed: the checker itself refuses a law read at a field the state
type lacks. The `#tooth` mutations are in the legacy leaf `Obend.Law.Proofs.TypingTeeth`: a
mutation re-checks every proof downstream of it, and the checker's proofs have bodies a `module`
cannot see. -/

namespace Teeth

public theorem isCanonical_of {S : Ty} (h : S.canonical = S) : S.isCanonical := h ▸ Ty.canonical_isCanonical S

@[expose] public def totalTy : Ty := .field "total" .natural .emptyRow
@[expose] public def councilTy : Ty :=
  .field "approvals" .natural (.field "proposal" (proposalTy .natural) (.field "total" .natural .emptyRow))
@[expose] public def ratedTy : Ty :=
  .field "count" .natural (.field "epoch" .natural (.field "total" .natural .emptyRow))
@[expose] public def doorTy : Ty := .field "door" (stateTy ["open", "shut"]) .emptyRow

theorem bounded_typed : ChecksAt (bounded totalTy "total" 5) totalTy :=
  bounded_checks "total" 5 (isCanonical_of (by decide)) rfl rfl

theorem quorum_typed : ChecksAt (quorumLaw councilTy .natural ["ann", "bob", "cy"] 2 "total") councilTy :=
  quorum_checks _ 2 "total" (isCanonical_of (by decide)) rfl (.scalar (.inl rfl)) rfl rfl rfl

theorem windowed_typed : ChecksAt (windowedLaw ratedTy .natural 10 1 "total") ratedTy :=
  windowed_checks 10 1 "total" (isCanonical_of (by decide)) rfl (.scalar (.inl rfl)) rfl rfl rfl

theorem machine_typed : ChecksAt (machineLaw doorTy "door" ["open", "shut"] "shut"
    [("shut", 0, "open"), ("open", 1, "shut")]) doorTy :=
  machine_checks (isCanonical_of (by decide)) rfl rfl (by decide) (by simp)

/-- The field hypothesis is needed: a bound on a field the state lacks does not check. -/
example :
    (checkAgainst ⟨bounded totalTy "count" 5, noAnn, {}⟩ [] (lawTy totalTy)).toBool = false := by decide
/-- And the type is the law's: `bounded` does not check at a type whose verdict is not `verdictTy`. -/
example :
    (checkAgainst ⟨bounded totalTy "total" 5, noAnn, {}⟩ [] (fnTy totalTy totalTy)).toBool = false := by decide

/-- A record type: a pair of naturals. -/
@[expose] public def pairTy : Ty := .field "hi" .natural (.field "lo" .natural .emptyRow)
@[expose] public def councilPairTy : Ty :=
  .field "approvals" .natural (.field "proposal" (proposalTy pairTy) (.field "total" pairTy .emptyRow))
@[expose] public def ratedPairTy : Ty :=
  .field "count" .natural (.field "epoch" .natural (.field "total" pairTy .emptyRow))

public theorem pairTy_eq : EqTy pairTy :=
  .row (.cons rfl (.scalar (.inl rfl)) (.cons rfl (.scalar (.inl rfl)) .nil))

/-- **Beyond scalars**: a quorum and a rate limit guarding a RECORD field check. -/
public theorem quorum_typed_record : ChecksAt (quorumLaw councilPairTy pairTy ["ann", "bob", "cy"] 2 "total") councilPairTy :=
  quorum_checks _ 2 "total" (isCanonical_of (by decide)) rfl pairTy_eq rfl rfl rfl

theorem windowed_typed_record : ChecksAt (windowedLaw ratedPairTy pairTy 10 1 "total") ratedPairTy :=
  windowed_checks 10 1 "total" (isCanonical_of (by decide)) rfl pairTy_eq rfl rfl rfl

/-- A closed invariant: the total is at most 5. -/
@[expose] public def totalAtMost5 : Term := .lam (leNat (.get (.bound 0) "total") (natT 5))

theorem totalAtMost5_checked :
    ∃ c, checkAgainst ⟨totalAtMost5, noAnn, {}⟩ [] (fnTy totalTy .boolean) = .ok c := by
  cases h : checkAgainst ⟨totalAtMost5, noAnn, {}⟩ [] (fnTy totalTy .boolean) with
  | ok c => exact ⟨c, rfl⟩
  | error e =>
      have : (checkAgainst ⟨totalAtMost5, noAnn, {}⟩ [] (fnTy totalTy .boolean)).toBool = true := by decide
      rw [h] at this; cases this

/-- `keeps` with a real invariant is typed. -/
theorem keeps_typed_tooth : Typed (keeps totalTy totalAtMost5) totalTy := by
  obtain ⟨c, hc⟩ := totalAtMost5_checked
  exact keeps_typed (I := ⟨totalAtMost5, noAnn, {}⟩) (isCanonical_of (by decide)) rfl rfl
    (.lam (.binary (.get (.bound (by decide))) (.natural _))) ⟨c, checkAgainst_type hc⟩

/-- The algorithmic checker refuses `keeps` unannotated: the invariant's lambda does not synthesize. -/
theorem keeps_unannotated_refused :
    (checkAgainst ⟨keeps totalTy totalAtMost5, noAnn, {}⟩ [] (lawTy totalTy)).toBool = false := by decide

end Teeth

end Obend.Law.Typing
