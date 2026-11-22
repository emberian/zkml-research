/-
# `LcnfToPancake.lean` — Verified First-Order `LcnfCode → PStmt` Lowering (`lean4:v4.35.0`, `Init`-Only)

Standalone `Init`-only Lean `v4.35.0` formalization of the first-order tail/join `LcnfCode`
IR (matching `Obend.Lower.LCNF` constructor-for-constructor) and its verified lowering
`compileLcnfToPancake : LcnfCode → PStmt` into HOL4-faithful CakeML Pancake (`PanSemV435`)
under path-sensitive `CondSClk` fuel synthesis and non-vacuous `RefinesClkPan` contracts (`G6`).
-/
import RefinesClkPan

namespace OrbPancakeV435

set_option autoImplicit false

/-! ## 0. Standalone First-Order Tail/Join `LcnfCode` Syntax & Reference Evaluator (Matching `Obend.Lower.LCNF`) -/

/-- Arithmetic / comparison operators (`Obend.Lower.NatOp`). -/
inductive NatOp where
  | add | sub | mul | div | mod | beq | ble
  deriving DecidableEq, Repr, Inhabited

/-- Atomic ANF arguments (`Obend.Lower.LCNF.LcnfArg`). -/
inductive LcnfArg where
  | bvar     (idx : Nat)
  | lit      (n : Nat)
  | boolLit  (b : Bool)
  | erased
  | stateTok (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Let-bound RHS computations (`Obend.Lower.LCNF.LcnfLetValue`). -/
inductive LcnfLetValue where
  | arg        (a : LcnfArg)
  | natOp      (op : NatOp) (lhs rhs : LcnfArg)
  | ctor       (tag : String) (fields : List (String × LcnfArg))
  | record     (fields : List (String × LcnfArg))
  | proj       (field : String) (target : LcnfArg)
  | app        (fn : LcnfArg) (arg : LcnfArg)
  | stateRead  (tok : LcnfArg) (addr : LcnfArg)
  | stateWrite (tok : LcnfArg) (addr : LcnfArg) (val : LcnfArg)
  deriving Repr, Inhabited

/-- Tail/join LCNF code blocks (`Obend.Lower.LCNF.LcnfCode`). -/
inductive LcnfCode where
  | letValue (val : LcnfLetValue) (body : LcnfCode)
  | jpDecl   (jpId : Nat) (numParams : Nat) (jpBody : LcnfCode) (body : LcnfCode)
  | jmp      (jpId : Nat) (args : List LcnfArg)
  | ifBool   (cond : LcnfArg) (thenBranch elseBranch : LcnfCode)
  | cases    (scrut : LcnfArg) (arms : List (String × List String × LcnfCode))
  | return   (arg : LcnfArg)
  | unreach
  deriving Repr, Inhabited

/-- Structured LCNF runtime values (`Obend.Lower.LCNF.LcnfVal`). -/
inductive LcnfVal where
  | scalar   (n : Nat)
  | bool     (b : Bool)
  | erased
  | stateTok (id : Nat)
  | ctor     (tag : String) (fields : List (String × LcnfVal))
  | record   (fields : List (String × LcnfVal))
  deriving Repr, Inhabited

def LcnfVal.toNat? : LcnfVal → Option Nat
  | .scalar n => some n
  | _ => none

/-- Lexical join-point closure (`Obend.Lower.LCNF.LcnfJpClosure`). -/
structure LcnfJpClosure where
  jpId          : Nat
  numParams     : Nat
  declEnv       : List LcnfVal
  savedJpsDepth : Nat
  jpBody        : LcnfCode
  deriving Repr, Inhabited

/-- Ordered named-field extraction (`Obend.Core.Term.splitValues`). -/
def splitValues {α : Type} (fields : List (String × α)) : List String → Option (List α)
  | [] => some []
  | name :: rest =>
    match fields.find? (fun p => p.1 == name), splitValues fields rest with
    | some (_, v), some vs => some (v :: vs)
    | _, _ => none
termination_by structural nms => nms

def evalLcnfArgVal (env : List LcnfVal) : LcnfArg → Option LcnfVal
  | .bvar idx    => env[idx]?
  | .lit n       => some (.scalar n)
  | .boolLit b   => some (.bool b)
  | .erased      => some .erased
  | .stateTok id => some (.stateTok id)

def readLinearStore (st : List (Nat × Nat)) (addr : Nat) : Nat :=
  match st.find? (fun p => p.1 == addr) with
  | some (_, v) => v
  | none => 0

def writeLinearStore (st : List (Nat × Nat)) (addr val : Nat) : List (Nat × Nat) :=
  (addr, val) :: st.filter (fun p => p.1 != addr)

mutual
def evalLcnfLetValueVal : Nat → List LcnfVal → List LcnfJpClosure →
    List (Nat × Nat) → LcnfLetValue → Option (LcnfVal × List (Nat × Nat))
  | 0, _, _, _, _ => none
  | _ + 1, env, _, st, v => do
    match v with
    | .arg a => return (← evalLcnfArgVal env a, st)
    | .natOp op l r =>
      let .scalar lv ← evalLcnfArgVal env l | none
      let .scalar rv ← evalLcnfArgVal env r | none
      let res := match op with
        | .add => LcnfVal.scalar (lv + rv)
        | .sub => .scalar (lv - rv)
        | .mul => .scalar (lv * rv)
        | .div => .scalar (lv / rv)
        | .mod => .scalar (lv % rv)
        | .beq => .bool (lv == rv)
        | .ble => .bool (lv <= rv)
      return (res, st)
    | .ctor tag fs =>
      let vals ← fs.mapM fun (name, a) => do return (name, ← evalLcnfArgVal env a)
      return (.ctor tag vals, st)
    | .record fs =>
      let vals ← fs.mapM fun (name, a) => do return (name, ← evalLcnfArgVal env a)
      return (.record vals, st)
    | .proj field tgt =>
      let .record fs ← evalLcnfArgVal env tgt | none
      let (_, val) ← fs.find? (fun p => p.1 == field)
      return (val, st)
    | .app _ _ => none
    | .stateRead tok addr =>
      let .stateTok _ ← evalLcnfArgVal env tok | none
      let .scalar a ← evalLcnfArgVal env addr | none
      return (.scalar (readLinearStore st a), st)
    | .stateWrite tok addr val =>
      let .stateTok _ ← evalLcnfArgVal env tok | none
      let .scalar a ← evalLcnfArgVal env addr | none
      let .scalar v ← evalLcnfArgVal env val | none
      return (.scalar v, writeLinearStore st a v)

def evalLcnfCodeVal : Nat → List LcnfVal → List LcnfJpClosure →
    List (Nat × Nat) → LcnfCode → Option (LcnfVal × List (Nat × Nat))
  | 0, _, _, _, _ => none
  | fuel + 1, env, jps, st, c => do
    match c with
    | .return a => return (← evalLcnfArgVal env a, st)
    | .unreach => none
    | .letValue v body =>
      let (val, st') ← evalLcnfLetValueVal fuel env jps st v
      evalLcnfCodeVal fuel (val :: env) jps st' body
    | .jpDecl id n jpBody body =>
      evalLcnfCodeVal fuel env (⟨id, n, env, jps.length, jpBody⟩ :: jps) st body
    | .jmp id args =>
      let jp ← jps.find? (fun entry => entry.jpId == id)
      if args.length != jp.numParams then none else do
        let vals ← args.mapM (evalLcnfArgVal env)
        evalLcnfCodeVal fuel (vals ++ jp.declEnv)
          (jps.drop (jps.length - jp.savedJpsDepth)) st jp.jpBody
    | .ifBool cond t f =>
      let .bool b ← evalLcnfArgVal env cond | none
      evalLcnfCodeVal fuel env jps st (if b then t else f)
    | .cases scrut arms =>
      let .ctor tag fs ← evalLcnfArgVal env scrut | none
      let (_, names, body) ← arms.find? (fun (armTag, _, _) => armTag == tag)
      let vals ← splitValues fs names
      evalLcnfCodeVal fuel (vals.reverse ++ env) jps st body
end

/-- Top-level scalar LCNF evaluator (`evalLcnf` / `Obend.Lower.LCNF.evalLcnfCode`). -/
def evalLcnfCode (fuel : Nat) (env : List Nat) (jps : List LcnfJpClosure)
    (st : List (Nat × Nat)) (c : LcnfCode) : Option (Nat × List (Nat × Nat)) := do
  let (val, st') ← evalLcnfCodeVal fuel (env.map LcnfVal.scalar) jps st c
  return (← val.toNat?, st')


/-! ## 1. Collision-Free Constructor Tag Table & Disjoint Local Slot Supply -/

mutual
/-- Collect all constructor tag strings appearing in `.ctor` or `.cases` across `c`. -/
def collectTags : LcnfCode → List String
  | .return _ => []
  | .unreach => []
  | .jmp _ _ => []
  | .letValue (.ctor tag _) body => tag :: collectTags body
  | .letValue _ body => collectTags body
  | .jpDecl _ _ jpBody body => collectTags body ++ collectTags jpBody
  | .ifBool _ t f => collectTags t ++ collectTags f
  | .cases _ arms => collectArmsTags arms
termination_by structural c => c

def collectArmsTags : List (String × List String × LcnfCode) → List String
  | [] => []
  | (tag, _, body) :: rest => tag :: (collectTags body ++ collectArmsTags rest)
termination_by structural arms => arms
end

/-- First-occurrence index of `tag` in `tags`. -/
def lookupTagIdx : List String → String → Option Nat
  | [], _ => none
  | hd :: tl, t => if hd == t then some 0 else (lookupTagIdx tl t).map (· + 1)
termination_by structural tags => tags

theorem lookupTagIdx_lt {tags : List String} {t : String} {i : Nat}
    (h : lookupTagIdx tags t = some i) : i < tags.length := by
  induction tags generalizing i with
  | nil => simp [lookupTagIdx] at h
  | cons hd tl ih =>
    simp only [lookupTagIdx] at h
    if heq : hd == t then
      simp [heq] at h; subst h; simp
    else
      simp [heq] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := ih hj
      simp; omega

theorem lookupTagIdx_inj {tags : List String} {t1 t2 : String} {i : Nat}
    (h1 : lookupTagIdx tags t1 = some i) (h2 : lookupTagIdx tags t2 = some i) :
    t1 = t2 := by
  induction tags generalizing i with
  | nil => simp [lookupTagIdx] at h1
  | cons hd tl ih =>
    simp only [lookupTagIdx] at h1 h2
    cases e1 : (hd == t1) <;> cases e2 : (hd == t2) <;> simp [e1, e2] at h1 h2
    · obtain ⟨j1, hj1, heq1⟩ := h1
      obtain ⟨j2, hj2, heq2⟩ := h2
      have hjeq : j1 = j2 := by omega
      subst hjeq
      exact ih hj1 hj2
    · omega
    · omega
    · have ht1 : hd = t1 := beq_iff_eq.mp e1
      have ht2 : hd = t2 := beq_iff_eq.mp e2
      exact ht1.symm.trans ht2

/-- Kind-tagged local variable name generator (`'v'` = computational var, `'h'` = join hit flag,
    `'a'` = join argument slot). Injective on `(kind, id)` by length/head inspection. -/
def mkSlot (kind : Char) (id : Nat) : String :=
  String.ofList (kind :: List.replicate id '_')

theorem mkSlot_inj {k1 k2 : Char} {i1 i2 : Nat} (h : mkSlot k1 i1 = mkSlot k2 i2) :
    k1 = k2 ∧ i1 = i2 := by
  have hl : (mkSlot k1 i1).toList = (mkSlot k2 i2).toList := congrArg String.toList h
  simp only [mkSlot, String.toList_ofList, List.cons.injEq] at hl
  refine ⟨hl.1, ?_⟩
  have hlen := congrArg List.length hl.2
  simpa [List.length_replicate] using hlen

theorem mkSlot_ne_of_kind {k1 k2 : Char} (hk : k1 ≠ k2) (i1 i2 : Nat) :
    mkSlot k1 i1 ≠ mkSlot k2 i2 :=
  fun h => hk (mkSlot_inj h).1

theorem mkSlot_ne_of_lt {k1 k2 : Char} {i1 i2 : Nat} (hlt : i1 < i2) :
    mkSlot k1 i1 ≠ mkSlot k2 i2 :=
  fun h => by have := (mkSlot_inj h).2; omega

/-! ## 2. First-Order LCNF Range- & Shape-Safe Type System (`FoScalarTy`, `FoTy`, `checkFoLcnf`) -/

/-- Pure syntactic first-order RHS check (excludes closures and linear state tokens). -/
def foPureLetVal : LcnfLetValue → Bool
  | .arg _ | .natOp _ _ _ | .ctor _ _ => true
  | _ => false

mutual
/-- Pure syntactic first-order code predicate (every nested branch/arm/join body uses `foPureLetVal`). -/
def foPureCode : LcnfCode → Bool
  | .return _ | .unreach | .jmp _ _ => true
  | .letValue lv body => foPureLetVal lv && foPureCode body
  | .ifBool _ t f => foPureCode t && foPureCode f
  | .cases _ arms => foPureArms arms
  | .jpDecl _ _ jpBody body => foPureCode jpBody && foPureCode body
termination_by structural c => c

def foPureArms : List (String × List String × LcnfCode) → Bool
  | [] => true
  | (_, _, body) :: rest => foPureCode body && foPureArms rest
termination_by structural arms => arms
end

/-- First-order 1-word (`Shape.One`) types admitted across join-point parameters and scalars. -/
inductive FoScalarTy where
  | scalar (maxVal : Nat)
  | bool
  | erased
  deriving DecidableEq, Repr, Inhabited

/-- First-order LCNF value types (1-word scalars/bools/erased + tagged scalar-field ADTs). -/
inductive FoTy where
  | one (st : FoScalarTy)
  | ctor (tag : String) (fieldNames : List String) (fieldBounds : List Nat)
  deriving DecidableEq, Repr, Inhabited

def FoTy.toShape : FoTy → Shape
  | .one _ => .One
  | .ctor _ fieldNames _ => .Comb (List.replicate (fieldNames.length + 1) .One)

def FoScalarTy.wf : FoScalarTy → Bool
  | .scalar hi => decide (hi < 2 ^ 64)
  | .bool      => true
  | .erased    => true

def FoScalarTy.subTy : FoScalarTy → FoScalarTy → Bool
  | .scalar a, .scalar b => decide (a ≤ b) && decide (b < 2 ^ 64)
  | .bool,     .bool     => true
  | .erased,   .erased   => true
  | _,         _         => false

def FoScalarTy.join : FoScalarTy → FoScalarTy → Option FoScalarTy
  | .scalar a, .scalar b =>
    let m := max a b
    if decide (m < 2 ^ 64) then some (.scalar m) else none
  | .bool,   .bool   => some .bool
  | .erased, .erased => some .erased
  | _,       _       => none

def joinScalarList : List FoScalarTy → List FoScalarTy → Option (List FoScalarTy)
  | [], [] => some []
  | x :: xs, y :: ys =>
    match x.join y, joinScalarList xs ys with
    | some z, some zs => some (z :: zs)
    | _, _ => none
  | _, _ => none
termination_by structural xs => xs

/-- Join-point typing signature (`jpId` + 1-word parameter bounds). -/
structure JpSig where
  jpId   : Nat
  params : List FoScalarTy
  deriving DecidableEq, Repr, Inhabited

def inferArgFoTy (envTys : List FoTy) : LcnfArg → Option FoTy
  | .bvar idx   => envTys[idx]?
  | .lit n      => if decide (n < 2 ^ 64) then some (.one (.scalar n)) else none
  | .boolLit _  => some (.one .bool)
  | .erased     => some (.one .erased)
  | .stateTok _ => none

def inferArgScalarTy (envTys : List FoTy) (a : LcnfArg) : Option FoScalarTy :=
  match inferArgFoTy envTys a with
  | some (.one st) => if st.wf then some st else none
  | _ => none

def inferCtorFields (envTys : List FoTy) :
    List (String × LcnfArg) → Option (List String × List Nat)
  | [] => some ([], [])
  | (nm, a) :: rest =>
    match inferArgFoTy envTys a, inferCtorFields envTys rest with
    | some (.one (.scalar b)), some (nms, bs) =>
      if decide (b < 2 ^ 64) && !(nms.contains nm) then
        some (nm :: nms, b :: bs)
      else
        none
    | _, _ => none
termination_by structural fs => fs

def inferLetValFoTy (tags : List String) (envTys : List FoTy) : LcnfLetValue → Option FoTy
  | .arg a => inferArgFoTy envTys a
  | .natOp op l r =>
    match inferArgFoTy envTys l, inferArgFoTy envTys r with
    | some (.one (.scalar b1)), some (.one (.scalar b2)) =>
      if decide (b1 < 2 ^ 64) && decide (b2 < 2 ^ 64) then
        match op with
        | .add =>
          if decide (b1 + b2 < 2 ^ 64) then some (.one (.scalar (b1 + b2))) else none
        | .sub => some (.one (.scalar b1))
        | .mul =>
          if decide (b1 * b2 < 2 ^ 64) then some (.one (.scalar (b1 * b2))) else none
        | .beq => some (.one .bool)
        | .ble => some (.one .bool)
        | .div | .mod => none
      else
        none
    | _, _ => none
  | .ctor tag fields =>
    match lookupTagIdx tags tag, inferCtorFields envTys fields with
    | some idx, some (nms, bs) =>
      if decide (idx < 2 ^ 64) then some (.ctor tag nms bs) else none
    | _, _ => none
  | .record _ | .proj _ _ | .app _ _ | .stateRead _ _ | .stateWrite _ _ _ => none

def mergeOptParams : Option (List FoScalarTy) → Option (List FoScalarTy) → Option (Option (List FoScalarTy))
  | none, y => some y
  | x, none => some x
  | some xs, some ys => (joinScalarList xs ys).map some

mutual
/-- Untrusted parameter-type inference helper scanning `jmp targetJpId` sites inside `body`.
    Soundness does NOT rely on this helper: `checkFoCode` independently verifies every jump. -/
def inferJpParams (tags : List String) (targetJpId numParams : Nat) (envTys : List FoTy) :
    LcnfCode → Option (Option (List FoScalarTy))
  | .return _ => some none
  | .unreach  => some none
  | .jmp id args =>
    if id == targetJpId then
      if args.length == numParams then
        (args.mapM (inferArgScalarTy envTys)).map some
      else
        none
    else
      some none
  | .letValue v body =>
    match inferLetValFoTy tags envTys v with
    | some ty => inferJpParams tags targetJpId numParams (ty :: envTys) body
    | none => none
  | .ifBool _ t f =>
    match inferJpParams tags targetJpId numParams envTys t,
          inferJpParams tags targetJpId numParams envTys f with
    | some p1, some p2 => mergeOptParams p1 p2
    | _, _ => none
  | .cases scrut arms =>
    match inferArgFoTy envTys scrut with
    | some (.ctor cTag cNames cBounds) =>
      let armEnv := (cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys
      inferJpParamsArm tags targetJpId numParams armEnv cTag cNames arms
    | _ => none
  | .jpDecl innerId innerN innerJpBody innerBody =>
    if innerId == targetJpId then none
    else
      match inferJpParams tags innerId innerN envTys innerBody with
      | some innerOpt =>
        let innerParams := innerOpt.getD (List.replicate innerN (.scalar 0))
        match inferJpParams tags targetJpId numParams envTys innerBody,
              inferJpParams tags targetJpId numParams (innerParams.map FoTy.one ++ envTys) innerJpBody with
        | some p1, some p2 => mergeOptParams p1 p2
        | _, _ => none
      | none => none
termination_by structural c => c

def inferJpParamsArm (tags : List String) (targetJpId numParams : Nat) (armEnv : List FoTy)
    (cTag : String) (cNames : List String) :
    List (String × List String × LcnfCode) → Option (Option (List FoScalarTy))
  | [] => none
  | (aTag, armNames, armBody) :: rest =>
    if aTag == cTag then
      if armNames == cNames then inferJpParams tags targetJpId numParams armEnv armBody else none
    else
      inferJpParamsArm tags targetJpId numParams armEnv cTag cNames rest
termination_by structural arms => arms
end

def checkArgsSubTy (envTys : List FoTy) : List LcnfArg → List FoScalarTy → Bool
  | [], [] => true
  | a :: as, expected :: es =>
    match inferArgScalarTy envTys a with
    | some actual => actual.subTy expected && checkArgsSubTy envTys as es
    | none => false
  | _, _ => false
termination_by structural as => as

def checkArmTagsValid (tags : List String) : List (String × List String × LcnfCode) → Bool
  | [] => true
  | (atag, _, _) :: rest =>
    (match lookupTagIdx tags atag with
     | some idx => decide (idx < 2 ^ 64)
     | none => false) && checkArmTagsValid tags rest
termination_by structural arms => arms

mutual
/-- Check whether `c` is a well-typed first-order LCNF block returning a scalar `≤ retBound < 2^64`
    (or jumping to an active `JpSig` in `jpSigs`). -/
def checkFoCode (tags : List String) (envTys : List FoTy) (jpSigs : List JpSig) :
    LcnfCode → Option Nat
  | .return a =>
    match inferArgFoTy envTys a with
    | some (.one (.scalar b)) => if decide (b < 2 ^ 64) then some b else none
    | _ => none
  | .unreach => none
  | .jmp id args =>
    match jpSigs.find? (fun s => s.jpId == id) with
    | some sig =>
      if args.length == sig.params.length && checkArgsSubTy envTys args sig.params then
        some 0
      else
        none
    | none => none
  | .letValue v body =>
    match inferLetValFoTy tags envTys v with
    | some ty => checkFoCode tags (ty :: envTys) jpSigs body
    | none => none
  | .ifBool cond t f =>
    match inferArgFoTy envTys cond with
    | some (.one .bool) =>
      match checkFoCode tags envTys jpSigs t, checkFoCode tags envTys jpSigs f with
      | some b1, some b2 => some (max b1 b2)
      | _, _ => none
    | _ => none
  | .cases scrut arms =>
    match scrut, inferArgFoTy envTys scrut with
    | .bvar _, some (.ctor cTag cNames cBounds) =>
      if checkArmTagsValid tags arms && foPureArms arms then
        let armEnv := (cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys
        checkFoArm tags armEnv jpSigs cTag cNames arms
      else
        none
    | _, _ => none
  | .jpDecl jpId numParams jpBody body =>
    if jpSigs.any (fun s => s.jpId == jpId) then none
    else
      match inferJpParams tags jpId numParams envTys body with
      | some optParams =>
        let paramTys := optParams.getD (List.replicate numParams (.scalar 0))
        if paramTys.length == numParams && paramTys.all FoScalarTy.wf then
          match checkFoCode tags envTys (⟨jpId, paramTys⟩ :: jpSigs) body,
                checkFoCode tags (paramTys.map FoTy.one ++ envTys) jpSigs jpBody with
          | some b1, some b2 => some (max b1 b2)
          | _, _ => none
        else
          none
      | none => none
termination_by structural c => c

def checkFoArm (tags : List String) (armEnv : List FoTy) (jpSigs : List JpSig)
    (cTag : String) (cNames : List String) :
    List (String × List String × LcnfCode) → Option Nat
  | [] => none
  | (aTag, armNames, armBody) :: rest =>
    if aTag == cTag then
      if armNames == cNames then checkFoCode tags armEnv jpSigs armBody else none
    else
      checkFoArm tags armEnv jpSigs cTag cNames rest
termination_by structural arms => arms
end

private theorem checkFoArm_eq_find (tags : List String) (armEnv : List FoTy) (jpSigs : List JpSig)
    (cTag : String) (cNames : List String) :
    ∀ arms, checkFoArm tags armEnv jpSigs cTag cNames arms =
      match arms.find? (fun a => a.1 == cTag) with
      | some (_, armNames, armBody) =>
        if armNames == cNames then checkFoCode tags armEnv jpSigs armBody else none
      | none => none
  | [] => rfl
  | (aTag, armNames, armBody) :: rest => by
    simp only [checkFoArm, List.find?]
    cases aTag == cTag <;> simp [checkFoArm_eq_find]

/-- Top-level first-order closed scalar `LcnfCode` checker (`some maxRetVal` when well-typed). -/
def checkFoLcnf (c : LcnfCode) : Option Nat :=
  let tags := collectTags c
  if decide (tags.length < 2 ^ 64) then
    checkFoCode tags [] [] c
  else
    none

mutual
private theorem checkFoCode_bound_lt (tags : List String) :
    ∀ (c : LcnfCode) (envTys : List FoTy) (jpSigs : List JpSig) (b : Nat),
      checkFoCode tags envTys jpSigs c = some b →
      b < 2 ^ 64 ∧ foPureCode c = true
  | .return a, envTys, _, b, h => by
    simp only [checkFoCode] at h
    cases ha : inferArgFoTy envTys a with
    | none => simp [ha] at h
    | some ty =>
      rw [ha] at h
      cases ty with
      | ctor _ _ _ => simp at h
      | one st =>
        cases st with
        | bool | erased => simp at h
        | scalar hi =>
          dsimp only at h
          by_cases hlt : hi < 2 ^ 64 <;> simp [hlt] at h
          subst h; exact ⟨hlt, rfl⟩
  | .unreach, _, _, _, h => by simp [checkFoCode] at h
  | .jmp id _, _, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hf : jpSigs.find? (fun s => s.jpId == id) with
    | none => simp [hf] at h
    | some sig =>
      rw [hf] at h
      dsimp only at h
      split at h <;> simp at h
      subst h; exact ⟨by decide, rfl⟩
  | .letValue v body, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hty : inferLetValFoTy tags envTys v with
    | none => simp [hty] at h
    | some ty =>
      rw [hty] at h
      have hlv : foPureLetVal v = true := by
        cases v <;> simp [inferLetValFoTy, foPureLetVal] at hty ⊢
      obtain ⟨hlt, hp⟩ := checkFoCode_bound_lt tags body (ty :: envTys) jpSigs b h
      exact ⟨hlt, by simp [foPureCode, hlv, hp]⟩
  | .ifBool cond t f, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hc : inferArgFoTy envTys cond with
    | none => simp [hc] at h
    | some ty =>
      rw [hc] at h
      cases ty with
      | ctor _ _ _ => simp at h
      | one st =>
        cases st <;> simp at h
        cases ht : checkFoCode tags envTys jpSigs t <;>
          cases hf : checkFoCode tags envTys jpSigs f <;> simp [ht, hf] at h
        obtain ⟨hlt1, hp1⟩ := checkFoCode_bound_lt tags t envTys jpSigs _ ht
        obtain ⟨hlt2, hp2⟩ := checkFoCode_bound_lt tags f envTys jpSigs _ hf
        subst h
        exact ⟨by omega, by simp [foPureCode, hp1, hp2]⟩
  | .cases scrut arms, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases scrut with
    | lit _ | boolLit _ | erased | stateTok _ => simp at h
    | bvar idx =>
      cases hs : inferArgFoTy envTys (.bvar idx) with
      | none => simp [hs] at h
      | some sty =>
        rw [hs] at h
        cases sty with
        | one _ => simp at h
        | ctor cTag cNames cBounds =>
          dsimp only at h
          cases hcond : (checkArmTagsValid tags arms && foPureArms arms) with
          | false => rw [hcond] at h; simp at h
          | true =>
            simp only [hcond, ↓reduceIte] at h
            simp only [Bool.and_eq_true] at hcond
            exact ⟨checkFoArm_bound_lt tags _ jpSigs cTag cNames arms b h,
              by simp [foPureCode, hcond.2]⟩
  | .jpDecl jpId numParams jpBody body, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hany : jpSigs.any (fun s => s.jpId == jpId) with
    | true => simp [hany] at h
    | false =>
      simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
      cases hinf : inferJpParams tags jpId numParams envTys body with
      | none => simp [hinf] at h
      | some optP =>
        rw [hinf] at h
        dsimp only at h
        split at h <;> try simp at h
        cases hb1 : checkFoCode tags envTys (⟨jpId, optP.getD (List.replicate numParams (.scalar 0))⟩ :: jpSigs) body with
        | none => rw [hb1] at h; cases h
        | some b1 =>
          cases hb2 : checkFoCode tags ((optP.getD (List.replicate numParams (.scalar 0))).map FoTy.one ++ envTys) jpSigs jpBody with
          | none => rw [hb1, hb2] at h; cases h
          | some b2 =>
            rw [hb1, hb2] at h
            injection h with h
            obtain ⟨hlt1, hp1⟩ := checkFoCode_bound_lt tags body _ _ _ hb1
            obtain ⟨hlt2, hp2⟩ := checkFoCode_bound_lt tags jpBody _ _ _ hb2
            subst h
            exact ⟨by omega, by simp [foPureCode, hp2, hp1]⟩
termination_by structural c => c

private theorem checkFoArm_bound_lt (tags : List String) (armEnv : List FoTy) (jpSigs : List JpSig)
    (cTag : String) (cNames : List String) :
    ∀ (arms : List (String × List String × LcnfCode)) (b : Nat),
      checkFoArm tags armEnv jpSigs cTag cNames arms = some b →
      b < 2 ^ 64
  | [], _, h => by simp [checkFoArm] at h
  | (aTag, armNames, armBody) :: rest, b, h => by
    simp only [checkFoArm] at h
    cases heq : (aTag == cTag) with
    | true =>
      simp only [heq, ↓reduceIte] at h
      cases hnm : (armNames == cNames) with
      | false => simp [hnm] at h
      | true =>
        simp only [hnm, ↓reduceIte] at h
        exact (checkFoCode_bound_lt tags armBody armEnv jpSigs b h).1
    | false =>
      simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
      exact checkFoArm_bound_lt tags armEnv jpSigs cTag cNames rest b h
termination_by structural arms => arms
end

/-! ## 3. Path-Sensitive Clock Synthesis (`synthLcnfClk`), Fuel Bound (`minLcnfFuel`) & Emitter -/

mutual
/-- Path-sensitive `CondSClk` fuel bound synthesized for an `LcnfCode` block. -/
def synthLcnfClk : LcnfCode → Nat
  | .return _               => 0
  | .unreach                => 0
  | .jmp _ _                => 1
  | .letValue _ body        => synthLcnfClk body
  | .ifBool _ t f           => max (synthLcnfClk t) (synthLcnfClk f)
  | .cases _ arms           => synthArmsClk arms
  | .jpDecl _ _ jpBody body => synthLcnfClk body + synthLcnfClk jpBody
termination_by structural c => c

def synthArmsClk : List (String × List String × LcnfCode) → Nat
  | [] => 0
  | (_, _, body) :: rest => max (synthLcnfClk body) (synthArmsClk rest)
termination_by structural arms => arms
end

mutual
/-- Guaranteed step-fuel upper bound for `Obend.Lower.LCNF.evalLcnfCodeVal`. -/
def minLcnfFuel : LcnfCode → Nat
  | .return _               => 1
  | .unreach                => 1
  | .jmp _ _                => 1
  | .letValue _ body        => 1 + minLcnfFuel body
  | .ifBool _ t f           => 1 + max (minLcnfFuel t) (minLcnfFuel f)
  | .cases _ arms           => 1 + minArmsFuel arms
  | .jpDecl _ _ jpBody body => 1 + minLcnfFuel body + minLcnfFuel jpBody
termination_by structural c => c

def minArmsFuel : List (String × List String × LcnfCode) → Nat
  | [] => 0
  | (_, _, body) :: rest => max (minLcnfFuel body) (minArmsFuel rest)
termination_by structural arms => arms
end

theorem minLcnfFuel_pos : ∀ c : LcnfCode, 1 ≤ minLcnfFuel c
  | .return _ | .unreach | .jmp _ _ => Nat.le_refl 1
  | .letValue _ _ | .ifBool _ _ _ | .cases _ _ | .jpDecl _ _ _ _ => by
    simp only [minLcnfFuel]; omega

/-- Compiled join-point descriptor carrying its fresh `'h'` flag slot and `'a'` parameter slots. -/
structure CompiledJp where
  jpId      : Nat
  numParams : Nat
  hitSlot   : String
  argSlots  : List String
  deriving Repr, Inhabited

def argShape (varSlots : List (String × Shape)) : LcnfArg → Shape
  | .bvar idx => match varSlots[idx]? with | some (_, sh) => sh | none => .One
  | _         => .One

def compileArg (varSlots : List (String × Shape)) : LcnfArg → PExp
  | .bvar idx     => match varSlots[idx]? with | some (nm, _) => .lvar nm | none => .const 0#64
  | .lit n        => .const (BitVec.ofNat 64 n)
  | .boolLit b    => .const (if b then 1#64 else 0#64)
  | .erased       => .const 0#64
  | .stateTok tid => .const (BitVec.ofNat 64 tid)

def compileFastNatOp (op : NatOp) (e1 e2 : PExp) : PExp :=
  match op with
  | .add => .binop .Add [e1, e2]
  | .mul => .panop .Mul [e1, e2]
  | .beq => .cmp .Equal e1 e2
  | .ble => .cmp .NotLower e2 e1
  | _    => .const 0#64

def wrapDecZeros : List String → PStmt → PStmt
  | [], inner => inner
  | s :: ss, inner => .dec s .One (.const 0#64) (wrapDecZeros ss inner)
termination_by structural ss => ss

def assignJpArgs (varSlots : List (String × Shape)) : List String → List LcnfArg → PStmt
  | [], [] => .skip
  | dst :: dsts, a :: as =>
    .seq (.lassign dst (compileArg varSlots a)) (assignJpArgs varSlots dsts as)
  | _, _ => .skip
termination_by structural dsts => dsts

def bindJpParams : List String → List String → PStmt → PStmt
  | [], [], inner => inner
  | p :: ps, a :: as, inner => .dec p .One (.lvar a) (bindJpParams ps as inner)
  | _, _, inner => inner
termination_by structural ps => ps

def bindCtorFields (eScrut : PExp) (fieldIdx : Nat) : List String → PStmt → PStmt
  | [], inner => inner
  | fSlot :: fSlots, inner =>
    .dec fSlot .One (.rfield fieldIdx eScrut) (bindCtorFields eScrut (fieldIdx + 1) fSlots inner)
termination_by structural fSlots => fSlots

def mkFreshSlots (kind : Char) (start : Nat) : Nat → List String
  | 0 => []
  | k + 1 => mkSlot kind start :: mkFreshSlots kind (start + 1) k
termination_by structural k => k

theorem mkFreshSlots_length (kind : Char) : ∀ (start k : Nat), (mkFreshSlots kind start k).length = k
  | _, 0 => rfl
  | start, k + 1 => by simp [mkFreshSlots, mkFreshSlots_length kind (start + 1) k]

theorem mem_mkFreshSlots {kind : Char} {x : String} :
    ∀ {start k : Nat}, x ∈ mkFreshSlots kind start k → ∃ j, start ≤ j ∧ j < start + k ∧ x = mkSlot kind j
  | _, 0, h => by cases h
  | start, k + 1, h => by
    simp only [mkFreshSlots, List.mem_cons] at h
    rcases h with rfl | htl
    · exact ⟨start, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots htl
      exact ⟨j, by omega, by omega, rfl⟩

mutual
/-- Syntax-directed lowering of `Obend.Lower.LCNF.LcnfCode` to `PanSem.PStmt`, threading a
    strictly monotone slot counter `nextId` so every `Dec` binder is globally fresh. -/
def compileCode (tags : List String) (varSlots : List (String × Shape))
    (jpSlots : List CompiledJp) (nextId : Nat) : LcnfCode → PStmt × Nat
  | .return a => (.ret (compileArg varSlots a), nextId)
  | .unreach  => (.skip, nextId)
  | .jmp id args =>
    match jpSlots.find? (fun cj => cj.jpId == id) with
    | some cj =>
      let assigns := assignJpArgs varSlots cj.argSlots args
      (.seq assigns (.seq (.lassign cj.hitSlot (.const 1#64)) .tick), nextId)
    | none => (.tick, nextId)
  | .letValue (.arg a) body =>
    let sh := argShape varSlots a
    let vSlot := mkSlot 'v' nextId
    let (cBody, nextId') := compileCode tags ((vSlot, sh) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot sh (compileArg varSlots a) cBody, nextId')
  | .letValue (.natOp .sub l r) body =>
    let vSlot := mkSlot 'v' nextId
    let eL := compileArg varSlots l
    let eR := compileArg varSlots r
    let (cBody, nextId') := compileCode tags ((vSlot, .One) :: varSlots) jpSlots (nextId + 1) body
    let satSub := .ite (.cmp .Lower eL eR) .skip (.lassign vSlot (.binop .Sub [eL, eR]))
    (.dec vSlot .One (.const 0#64) (.seq satSub cBody), nextId')
  | .letValue (.natOp op l r) body =>
    let vSlot := mkSlot 'v' nextId
    let eOp := compileFastNatOp op (compileArg varSlots l) (compileArg varSlots r)
    let (cBody, nextId') := compileCode tags ((vSlot, .One) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot .One eOp cBody, nextId')
  | .letValue (.ctor tag fields) body =>
    let tIdx := (lookupTagIdx tags tag).getD 0
    let sh := Shape.Comb (List.replicate (fields.length + 1) .One)
    let vSlot := mkSlot 'v' nextId
    let eCtor := PExp.rstruct (.const (BitVec.ofNat 64 tIdx) :: fields.map (fun f => compileArg varSlots f.2))
    let (cBody, nextId') := compileCode tags ((vSlot, sh) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot sh eCtor cBody, nextId')
  | .letValue _ body =>
    let vSlot := mkSlot 'v' nextId
    let (cBody, nextId') := compileCode tags ((vSlot, .One) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot .One (.const 0#64) cBody, nextId')
  | .ifBool cond t f =>
    let (cT, id1) := compileCode tags varSlots jpSlots nextId t
    let (cF, id2) := compileCode tags varSlots jpSlots id1 f
    (.ite (compileArg varSlots cond) cT cF, id2)
  | .cases scrut arms =>
    compileArms tags (compileArg varSlots scrut) varSlots jpSlots nextId arms
  | .jpDecl jpId numParams jpBody body =>
    let hitSlot := mkSlot 'h' nextId
    let argSlots := mkFreshSlots 'a' (nextId + 1) numParams
    let nextId1 := nextId + 1 + numParams
    let cj : CompiledJp := ⟨jpId, numParams, hitSlot, argSlots⟩
    let (cBody, nextId2) := compileCode tags varSlots (cj :: jpSlots) nextId1 body
    let pSlots := mkFreshSlots 'v' nextId2 numParams
    let jpVarSlots := (pSlots.map (fun s => (s, Shape.One))) ++ varSlots
    let (cJpBody, nextId3) := compileCode tags jpVarSlots jpSlots (nextId2 + numParams) jpBody
    let tailIf := PStmt.ite (.lvar hitSlot) (bindJpParams pSlots argSlots cJpBody) .skip
    (.dec hitSlot .One (.const 0#64) (wrapDecZeros argSlots (.seq cBody tailIf)), nextId3)
termination_by structural c => c

def compileArms (tags : List String) (eScrut : PExp) (varSlots : List (String × Shape))
    (jpSlots : List CompiledJp) (nextId : Nat) :
    List (String × List String × LcnfCode) → PStmt × Nat
  | [] => (.skip, nextId)
  | (armTag, fieldNames, armBody) :: rest =>
    let k := fieldNames.length
    let fSlots := mkFreshSlots 'v' nextId k
    let armVarSlots := (fSlots.reverse.map (fun s => (s, Shape.One))) ++ varSlots
    let (cArm, id1) := compileCode tags armVarSlots jpSlots (nextId + k) armBody
    let (cRest, id2) := compileArms tags eScrut varSlots jpSlots id1 rest
    let tIdx := (lookupTagIdx tags armTag).getD 0
    let guard := PExp.cmp .Equal (.rfield 0 eScrut) (.const (BitVec.ofNat 64 tIdx))
    (.ite guard (bindCtorFields eScrut 1 fSlots cArm) cRest, id2)
termination_by structural arms => arms
end

/-- **Top-Level Verified `LcnfCode → PStmt` Compiler (`compileLcnfToPancake`)**. -/
def compileLcnfToPancake (c : LcnfCode) : PStmt :=
  (compileCode (collectTags c) [] [] 0 c).1

/-! ## 4. Exact Agreement with Generic `CondSClk.synthStmtClk` -/

private theorem synthStmtClk_wrapDecZeros (ss : List String) (inner : PStmt) :
    synthStmtClk (wrapDecZeros ss inner) = synthStmtClk inner := by
  induction ss with
  | nil => rfl
  | cons _ tl ih => simp [wrapDecZeros, ih]

private theorem synthStmtClk_assignJpArgs (vs : List (String × Shape)) :
    ∀ (dsts : List String) (args : List LcnfArg),
      synthStmtClk (assignJpArgs vs dsts args) = some 0
  | [], [] => rfl
  | _ :: dsts, _ :: args => by
    simp [assignJpArgs, synthStmtClk_assignJpArgs vs dsts args]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

private theorem synthStmtClk_bindJpParams :
    ∀ (ps as : List String) (inner : PStmt),
      synthStmtClk (bindJpParams ps as inner) = synthStmtClk inner
  | [], [], _ => rfl
  | _ :: ps, _ :: as, inner => by simp [bindJpParams, synthStmtClk_bindJpParams ps as inner]
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl

private theorem synthStmtClk_bindCtorFields (e : PExp) :
    ∀ (idx : Nat) (fs : List String) (inner : PStmt),
      synthStmtClk (bindCtorFields e idx fs inner) = synthStmtClk inner
  | _, [], _ => rfl
  | idx, _ :: fs, inner => by simp [bindCtorFields, synthStmtClk_bindCtorFields e (idx + 1) fs inner]

mutual
private theorem compileCode_clk_and_mono (tags : List String) :
    (c : LcnfCode) →
    ∀ (varSlots : List (String × Shape)) (jpSlots : List CompiledJp) (nextId : Nat),
      synthStmtClk (compileCode tags varSlots jpSlots nextId c).1 = some (synthLcnfClk c) ∧
      nextId ≤ (compileCode tags varSlots jpSlots nextId c).2
  | .return _, _, _, nextId => ⟨rfl, Nat.le_refl _⟩
  | .unreach,  _, _, nextId => ⟨rfl, Nat.le_refl _⟩
  | .jmp id args, varSlots, jpSlots, nextId => by
    simp only [compileCode, synthLcnfClk]
    cases jpSlots.find? (fun cj => cj.jpId == id) with
    | none => exact ⟨rfl, Nat.le_refl _⟩
    | some cj =>
      refine ⟨?_, Nat.le_refl _⟩
      have ha := synthStmtClk_assignJpArgs varSlots cj.argSlots args
      simp [synthStmtClk, ha]
  | .letValue v body, varSlots, jpSlots, nextId => by
    cases v with
    | arg a =>
      have h := compileCode_clk_and_mono tags body ((mkSlot 'v' nextId, argShape varSlots a) :: varSlots) jpSlots (nextId + 1)
      exact ⟨by simpa [compileCode, synthLcnfClk] using h.1, by simp only [compileCode]; omega⟩
    | natOp op l r =>
      have h := compileCode_clk_and_mono tags body ((mkSlot 'v' nextId, .One) :: varSlots) jpSlots (nextId + 1)
      cases op <;>
        exact ⟨by simp [compileCode, synthLcnfClk, synthStmtClk, h.1],
               by simp only [compileCode]; omega⟩
    | ctor tag fields =>
      have h := compileCode_clk_and_mono tags body
        ((mkSlot 'v' nextId, Shape.Comb (List.replicate (fields.length + 1) .One)) :: varSlots)
        jpSlots (nextId + 1)
      exact ⟨by simpa [compileCode, synthLcnfClk] using h.1, by simp only [compileCode]; omega⟩
    | record _ | proj _ _ | app _ _ | stateRead _ _ | stateWrite _ _ _ =>
      have h := compileCode_clk_and_mono tags body ((mkSlot 'v' nextId, .One) :: varSlots) jpSlots (nextId + 1)
      exact ⟨by simpa [compileCode, synthLcnfClk] using h.1, by simp only [compileCode]; omega⟩
  | .ifBool cond t f, varSlots, jpSlots, nextId => by
    simp only [compileCode, synthLcnfClk]
    have ht := compileCode_clk_and_mono tags t varSlots jpSlots nextId
    have hf := compileCode_clk_and_mono tags f varSlots jpSlots (compileCode tags varSlots jpSlots nextId t).2
    exact ⟨by simp [synthStmtClk, ht.1, hf.1], Nat.le_trans ht.2 hf.2⟩
  | .cases scrut arms, varSlots, jpSlots, nextId =>
    compileArms_clk_and_mono tags arms (compileArg varSlots scrut) varSlots jpSlots nextId
  | .jpDecl jpId numParams jpBody body, varSlots, jpSlots, nextId => by
    simp only [compileCode, synthLcnfClk]
    have hb := compileCode_clk_and_mono tags body varSlots
      (⟨jpId, numParams, mkSlot 'h' nextId, mkFreshSlots 'a' (nextId + 1) numParams⟩ :: jpSlots)
      (nextId + 1 + numParams)
    let nextId2 := (compileCode tags varSlots
      (⟨jpId, numParams, mkSlot 'h' nextId, mkFreshSlots 'a' (nextId + 1) numParams⟩ :: jpSlots)
      (nextId + 1 + numParams) body).2
    have hj := compileCode_clk_and_mono tags jpBody
      (((mkFreshSlots 'v' nextId2 numParams).map (fun s => (s, Shape.One))) ++ varSlots)
      jpSlots (nextId2 + numParams)
    dsimp only [nextId2] at hj
    refine ⟨?_, ?_⟩
    · simp only [synthStmtClk, synthStmtClk_wrapDecZeros, synthStmtClk_bindJpParams, hb.1, hj.1, Nat.max_zero]
    · have h1 := hb.2
      have h2 := hj.2
      omega
termination_by structural c => c

private theorem compileArms_clk_and_mono (tags : List String) :
    (arms : List (String × List String × LcnfCode)) →
    ∀ (eScrut : PExp) (varSlots : List (String × Shape)) (jpSlots : List CompiledJp) (nextId : Nat),
      synthStmtClk (compileArms tags eScrut varSlots jpSlots nextId arms).1 = some (synthArmsClk arms) ∧
      nextId ≤ (compileArms tags eScrut varSlots jpSlots nextId arms).2
  | [], _, _, _, nextId => ⟨rfl, Nat.le_refl _⟩
  | (armTag, fieldNames, armBody) :: rest, eScrut, varSlots, jpSlots, nextId => by
    simp only [compileArms, synthArmsClk]
    have ha := compileCode_clk_and_mono tags armBody
      (((mkFreshSlots 'v' nextId fieldNames.length).reverse.map (fun s => (s, Shape.One))) ++ varSlots)
      jpSlots (nextId + fieldNames.length)
    have hr := compileArms_clk_and_mono tags rest eScrut varSlots jpSlots
      (compileCode tags
        (((mkFreshSlots 'v' nextId fieldNames.length).reverse.map (fun s => (s, Shape.One))) ++ varSlots)
        jpSlots (nextId + fieldNames.length) armBody).2
    refine ⟨?_, ?_⟩
    · simp only [synthStmtClk, synthStmtClk_bindCtorFields, ha.1, hr.1]
    · have h1 := ha.2
      have h2 := hr.2
      omega
termination_by structural arms => arms
end

/-- Generic `CondSClk.synthStmtClk` recovers `synthLcnfClk c` identically on every compiled `LcnfCode`. -/
theorem synthStmtClk_compileLcnfToPancake (c : LcnfCode) :
    synthStmtClk (compileLcnfToPancake c) = some (synthLcnfClk c) :=
  (compileCode_clk_and_mono (collectTags c) c [] [] 0).1

/-! ## 5. Compositional Block Semantics (`evalFoBlock`) & Equivalence with `evalLcnfCodeVal` -/

/-- Intra-block LCNF outcome before enclosing `jpDecl` handlers catch outgoing tail jumps. -/
inductive FoOutcome where
  | returned (v : LcnfVal)
  | jumped   (jpId : Nat) (args : List LcnfVal)

def evalFoLetVal (env : List LcnfVal) : LcnfLetValue → Option LcnfVal
  | .arg a => evalLcnfArgVal env a
  | .natOp op l r =>
    match evalLcnfArgVal env l, evalLcnfArgVal env r with
    | some (.scalar lv), some (.scalar rv) =>
      match op with
      | .add => some (.scalar (lv + rv))
      | .sub => some (.scalar (lv - rv))
      | .mul => some (.scalar (lv * rv))
      | .div => some (.scalar (lv / rv))
      | .mod => some (.scalar (lv % rv))
      | .beq => some (.bool (lv == rv))
      | .ble => some (.bool (lv <= rv))
    | _, _ => none
  | .ctor tag fs =>
    (fs.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)).map (.ctor tag)
  | _ => none

mutual
/-- Fuel-free structural evaluator for first-order `LcnfCode` blocks. -/
def evalFoBlock (env : List LcnfVal) : LcnfCode → Option FoOutcome
  | .return a => (evalLcnfArgVal env a).map .returned
  | .unreach  => none
  | .jmp id args => (args.mapM (evalLcnfArgVal env)).map (.jumped id)
  | .letValue v body =>
    match evalFoLetVal env v with
    | some val => evalFoBlock (val :: env) body
    | none => none
  | .ifBool cond t f =>
    match evalLcnfArgVal env cond with
    | some (.bool b) => if b then evalFoBlock env t else evalFoBlock env f
    | _ => none
  | .cases scrut arms =>
    match evalLcnfArgVal env scrut with
    | some (.ctor tag fs) => evalFoArm env tag fs arms
    | _ => none
  | .jpDecl jpId numParams jpBody body =>
    match evalFoBlock env body with
    | none => none
    | some (.returned v) => some (.returned v)
    | some (.jumped tid argVals) =>
      if tid == jpId then
        if argVals.length == numParams then
          evalFoBlock (argVals ++ env) jpBody
        else
          none
      else
        some (.jumped tid argVals)
termination_by structural c => c

def evalFoArm (env : List LcnfVal) (tag : String) (fs : List (String × LcnfVal)) :
    List (String × List String × LcnfCode) → Option FoOutcome
  | [] => none
  | (armTag, names, body) :: rest =>
    if armTag == tag then
      match splitValues fs names with
      | some vals => evalFoBlock (vals.reverse ++ env) body
      | none => none
    else
      evalFoArm env tag fs rest
termination_by structural arms => arms
end

private theorem evalFoArm_eq_find (env : List LcnfVal) (tag : String) (fs : List (String × LcnfVal)) :
    ∀ arms, evalFoArm env tag fs arms =
      match arms.find? (fun (armTag, _, _) => armTag == tag) with
      | some (_, names, body) =>
        match splitValues fs names with
        | some vals => evalFoBlock (vals.reverse ++ env) body
        | none => none
      | none => none
  | [] => rfl
  | (armTag, names, body) :: rest => by
    cases h : (armTag == tag) <;> simp [evalFoArm, List.find?, h, evalFoArm_eq_find]

/-- Dispatch an `FoOutcome` through a well-nested stack of `LcnfJpClosure` frames. -/
def applyJps : List LcnfJpClosure → FoOutcome → Option LcnfVal
  | _, .returned v => some v
  | [], .jumped _ _ => none
  | jp :: rest, .jumped tid args =>
    if jp.jpId == tid then
      if args.length == jp.numParams then
        match evalFoBlock (args ++ jp.declEnv) jp.jpBody with
        | some out => applyJps rest out
        | none => none
      else
        none
    else
      applyJps rest (.jumped tid args)
termination_by structural jps => jps

def jpsFuel : List LcnfJpClosure → Nat
  | [] => 0
  | jp :: rest => minLcnfFuel jp.jpBody + jpsFuel rest
termination_by structural jps => jps

@[simp] private theorem applyJps_returned (jps : List LcnfJpClosure) (v : LcnfVal) :
    applyJps jps (.returned v) = some v := by
  cases jps <;> rfl

/-- Predicate characterizing lexical join-closure stacks built by `evalLcnfCodeVal`. -/
inductive SavedDepthWF : List LcnfJpClosure → Prop where
  | nil : SavedDepthWF []
  | cons {jp : LcnfJpClosure} {rest : List LcnfJpClosure} :
      jp.savedJpsDepth = rest.length →
      foPureCode jp.jpBody = true →
      SavedDepthWF rest →
      SavedDepthWF (jp :: rest)

private theorem option_mapM_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.length = ys.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hx : f x <;> simp [hx] at h
    cases hxs : xs.mapM f <;> simp [hxs] at h
    subst h
    simp [option_mapM_length f xs _ hxs]

private theorem foPureArms_mem :
    ∀ {arms : List (String × List String × LcnfCode)} {atag : String}
      {anms : List String} {abody : LcnfCode},
      foPureArms arms = true →
      (atag, anms, abody) ∈ arms →
      foPureCode abody = true ∧ minLcnfFuel abody ≤ minArmsFuel arms
  | [], _, _, _, _, hm => by cases hm
  | (_, _, _) :: rest, _, _, _, hp, hm => by
    simp only [foPureArms, minArmsFuel, Bool.and_eq_true] at hp ⊢
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq; exact ⟨hp.1, by omega⟩
    · obtain ⟨h1, h2⟩ := foPureArms_mem hp.2 htl
      exact ⟨h1, by omega⟩

private theorem evalFoLetVal_iff {fuel : Nat} (hpos : 1 ≤ fuel)
    {env : List LcnfVal} {jps : List LcnfJpClosure} {st : List (Nat × Nat)}
    {v : LcnfLetValue} (hp : foPureLetVal v = true) :
    ∀ {val : LcnfVal} {st' : List (Nat × Nat)},
      (evalLcnfLetValueVal fuel env jps st v = some (val, st') ↔
        st' = st ∧ evalFoLetVal env v = some val) := by
  intro val st'
  cases fuel with
  | zero => omega
  | succ _ =>
    cases v with
    | arg a =>
      simp only [evalLcnfLetValueVal, evalFoLetVal]
      cases evalLcnfArgVal env a <;> simp [and_comm, eq_comm]
    | natOp op l r =>
      simp only [evalLcnfLetValueVal, evalFoLetVal, Bind.bind, Option.bind, pure]
      cases hl : evalLcnfArgVal env l with
      | none => simp
      | some vl =>
        cases vl <;> try simp
        cases hr : evalLcnfArgVal env r with
        | none => simp
        | some vr =>
          cases vr <;> try simp
          cases op <;> simp [and_comm, eq_comm]
    | ctor tag fs =>
      simp only [evalLcnfLetValueVal, evalFoLetVal]
      have hmapEq : (fs.mapM fun (name, a) => do return (name, ← evalLcnfArgVal env a)) =
          (fs.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)) := rfl
      rw [hmapEq]
      cases (fs.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)) <;>
        simp [and_comm, eq_comm]
    | record _ | proj _ _ | app _ _ | stateRead _ _ | stateWrite _ _ _ =>
      simp [foPureLetVal] at hp

private theorem savedDepth_le_of_find {jps : List LcnfJpClosure}
    (hwf : SavedDepthWF jps) :
    ∀ {id : Nat} {jp : LcnfJpClosure},
      jps.find? (fun e => e.jpId == id) = some jp →
      jp.savedJpsDepth ≤ jps.length := by
  induction hwf with
  | nil => intro _ _ h; simp at h
  | @cons hd rest hdepth _ _ ih =>
    intro id jp h
    simp only [List.find?] at h
    cases heq : (hd.jpId == id) with
    | true =>
      simp only [heq, Option.some.injEq] at h
      subst h
      simp [hdepth]
    | false =>
      simp only [heq] at h
      have h1 := ih h
      simp; omega

private theorem applyJps_find {jps : List LcnfJpClosure}
    (hwf : SavedDepthWF jps) {id : Nat} {jp : LcnfJpClosure}
    (hfind : jps.find? (fun e => e.jpId == id) = some jp) :
    foPureCode jp.jpBody = true ∧
    SavedDepthWF (jps.drop (jps.length - jp.savedJpsDepth)) ∧
    minLcnfFuel jp.jpBody + jpsFuel (jps.drop (jps.length - jp.savedJpsDepth)) ≤ jpsFuel jps ∧
    ∀ (vals : List LcnfVal),
      vals.length = jp.numParams →
      applyJps jps (.jumped id vals) =
        match evalFoBlock (vals ++ jp.declEnv) jp.jpBody with
        | some out => applyJps (jps.drop (jps.length - jp.savedJpsDepth)) out
        | none => none := by
  induction hwf with
  | nil => simp at hfind
  | @cons hd rest hdepth hbody hrest ih =>
    simp only [List.find?] at hfind
    cases heq : (hd.jpId == id) with
    | true =>
      simp only [heq, Option.some.injEq] at hfind
      subst hfind
      have hsub1 : (hd :: rest).length - hd.savedJpsDepth = 1 := by simp [hdepth]
      have hdrop : (hd :: rest).drop ((hd :: rest).length - hd.savedJpsDepth) = rest := by
        rw [hsub1]; rfl
      refine ⟨hbody, hdrop.symm ▸ hrest, ?_, fun vals hlen => ?_⟩
      · rw [hdrop]; simp [jpsFuel]
      · rw [hdrop]; simp [applyJps, heq, hlen]
    | false =>
      simp only [heq] at hfind
      obtain ⟨hb, hrd, hfuel, hfn⟩ := ih hfind
      have hle : jp.savedJpsDepth ≤ rest.length := savedDepth_le_of_find hrest hfind
      have hdropEq : (hd :: rest).drop ((hd :: rest).length - jp.savedJpsDepth) =
          rest.drop (rest.length - jp.savedJpsDepth) := by
        have hsub : (rest.length + 1) - jp.savedJpsDepth = (rest.length - jp.savedJpsDepth) + 1 := by
          omega
        simp only [List.length_cons, hsub, List.drop_succ_cons]
      refine ⟨hb, hdropEq.symm ▸ hrd, ?_, fun vals hlen => ?_⟩
      · rw [hdropEq]; simp only [jpsFuel]; omega
      · simp only [applyJps, heq, Bool.false_eq_true, ↓reduceIte]
        rw [hfn vals hlen, hdropEq]

private theorem applyJps_jumped_some {jps : List LcnfJpClosure} (hwf : SavedDepthWF jps)
    {id : Nat} {vals : List LcnfVal} {v : LcnfVal}
    (happ : applyJps jps (.jumped id vals) = some v) :
    ∃ jp outJ,
      jps.find? (fun e => e.jpId == id) = some jp ∧
      vals.length = jp.numParams ∧
      evalFoBlock (vals ++ jp.declEnv) jp.jpBody = some outJ ∧
      applyJps (jps.drop (jps.length - jp.savedJpsDepth)) outJ = some v := by
  induction hwf with
  | nil => simp [applyJps] at happ
  | @cons hd rest hdepth _ hrest ih =>
    simp only [applyJps] at happ
    cases heq : (hd.jpId == id) with
    | true =>
      simp only [heq, ↓reduceIte] at happ
      cases hlen : (vals.length == hd.numParams) with
      | false => simp [hlen] at happ
      | true =>
        simp only [hlen, ↓reduceIte] at happ
        cases hout : evalFoBlock (vals ++ hd.declEnv) hd.jpBody with
        | none => simp [hout] at happ
        | some outJ =>
          rw [hout] at happ
          have hsub1 : (hd :: rest).length - hd.savedJpsDepth = 1 := by simp [hdepth]
          have hdrop : (hd :: rest).drop ((hd :: rest).length - hd.savedJpsDepth) = rest := by
            rw [hsub1]; rfl
          exact ⟨hd, outJ, by simp [List.find?, heq], beq_iff_eq.mp hlen, hout, hdrop.symm ▸ happ⟩
    | false =>
      simp only [heq, Bool.false_eq_true, ↓reduceIte] at happ
      obtain ⟨jp, outJ, hf, hl, hout, happ'⟩ := ih happ
      have hle : jp.savedJpsDepth ≤ rest.length := savedDepth_le_of_find hrest hf
      have hdropEq : (hd :: rest).drop ((hd :: rest).length - jp.savedJpsDepth) =
          rest.drop (rest.length - jp.savedJpsDepth) := by
        have hsub : (rest.length + 1) - jp.savedJpsDepth = (rest.length - jp.savedJpsDepth) + 1 := by
          omega
        simp only [List.length_cons, hsub, List.drop_succ_cons]
      exact ⟨jp, outJ, by simp [List.find?, heq, hf], hl, hout, hdropEq.symm ▸ happ'⟩

/-- Forward equivalence: any `evalLcnfCodeVal` success on `foPureCode` agrees with `evalFoBlock` + `applyJps`. -/
private theorem evalLcnfCodeVal_eq_applyJps :
    ∀ (fuel : Nat) (c : LcnfCode) (env : List LcnfVal) (jps : List LcnfJpClosure)
      (st st' : List (Nat × Nat)) (v : LcnfVal),
      foPureCode c = true →
      SavedDepthWF jps →
      evalLcnfCodeVal fuel env jps st c = some (v, st') →
      st' = st ∧ ∃ out, evalFoBlock env c = some out ∧ applyJps jps out = some v := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [evalLcnfCodeVal] at h
  | succ f ih =>
    intro c env jps st st' v hp hjps hev
    cases c with
    | «return» a =>
      simp only [evalLcnfCodeVal, Bind.bind, Option.bind, pure] at hev
      cases ha : evalLcnfArgVal env a with
      | none => simp [ha] at hev
      | some valA =>
        simp only [ha, Option.some.injEq, Prod.mk.injEq] at hev
        rcases hev with ⟨rfl, rfl⟩
        exact ⟨rfl, .returned valA, by simp [evalFoBlock, ha], applyJps_returned jps valA⟩
    | unreach => simp [evalLcnfCodeVal] at hev
    | letValue lv body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalLcnfCodeVal] at hev
      cases hlv : evalLcnfLetValueVal f env jps st lv with
      | none => simp [hlv] at hev
      | some p =>
        obtain ⟨val, stMid⟩ := p
        have hfpos : 1 ≤ f := by
          cases f with
          | zero => simp [evalLcnfLetValueVal] at hlv
          | succ _ => omega
        obtain ⟨hstMid, hfoLv⟩ := (evalFoLetVal_iff hfpos hp.1).mp hlv
        subst stMid
        simp only [hlv, Bind.bind, Option.bind] at hev
        obtain ⟨hst, out, hfoB, happ⟩ := ih body (val :: env) jps st st' v hp.2 hjps hev
        exact ⟨hst, out, by simp [evalFoBlock, hfoLv, hfoB], happ⟩
    | ifBool cond t fls =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalLcnfCodeVal] at hev
      cases hc : evalLcnfArgVal env cond with
      | none => simp [hc] at hev
      | some cv =>
        cases cv <;> simp [hc] at hev
        rename_i bv
        cases bv with
        | true =>
          obtain ⟨hst, out, hfo, happ⟩ := ih t env jps st st' v hp.1 hjps hev
          exact ⟨hst, out, by simp [evalFoBlock, hc, hfo], happ⟩
        | false =>
          obtain ⟨hst, out, hfo, happ⟩ := ih fls env jps st st' v hp.2 hjps hev
          exact ⟨hst, out, by simp [evalFoBlock, hc, hfo], happ⟩
    | cases scrut arms =>
      simp only [foPureCode] at hp
      simp only [evalLcnfCodeVal] at hev
      cases hs : evalLcnfArgVal env scrut with
      | none => simp [hs] at hev
      | some sv =>
        cases sv <;> simp [hs] at hev
        rename_i tag fs
        cases hf : arms.find? (fun (armTag, _, _) => armTag == tag) with
        | none => simp [hf] at hev
        | some arm =>
          obtain ⟨atag, names, armBody⟩ := arm
          cases hsp : splitValues fs names with
          | none => simp [hf, hsp] at hev
          | some vals =>
            simp only [hf, hsp, Option.bind_some] at hev
            have hpArm := (foPureArms_mem hp (List.mem_of_find?_eq_some hf)).1
            obtain ⟨hst, out, hfo, happ⟩ := ih armBody (vals.reverse ++ env) jps st st' v hpArm hjps hev
            exact ⟨hst, out, by simp [evalFoBlock, hs, evalFoArm_eq_find, hf, hsp, hfo], happ⟩
    | jpDecl id n jpBody body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalLcnfCodeVal] at hev
      have hjps' : SavedDepthWF (⟨id, n, env, jps.length, jpBody⟩ :: jps) :=
        .cons rfl hp.1 hjps
      obtain ⟨hst, outB, hfoB, happB⟩ := ih body env _ st st' v hp.2 hjps' hev
      refine ⟨hst, ?_⟩
      cases outB with
      | returned rv =>
        simp only [applyJps_returned] at happB
        exact ⟨.returned rv, by simp [evalFoBlock, hfoB], by simpa using happB⟩
      | jumped tid argVals =>
        simp only [applyJps] at happB
        have hcomm : (id == tid) = (tid == id) := by
          cases h1 : (id == tid) <;> cases h2 : (tid == id) <;> simp_all [beq_iff_eq]
        rw [hcomm] at happB
        cases htid : (tid == id) with
        | true =>
          simp only [htid, ↓reduceIte] at happB
          cases hlen : (argVals.length == n) with
          | false => simp [hlen] at happB
          | true =>
            simp only [hlen, ↓reduceIte] at happB
            cases houtJ : evalFoBlock (argVals ++ env) jpBody with
            | none => simp [houtJ] at happB
            | some outJ =>
              rw [houtJ] at happB
              exact ⟨outJ, by simp [evalFoBlock, hfoB, htid, hlen, houtJ], happB⟩
        | false =>
          simp only [htid, Bool.false_eq_true, ↓reduceIte] at happB
          exact ⟨.jumped tid argVals, by simp [evalFoBlock, hfoB, htid], happB⟩
    | jmp id args =>
      simp only [evalLcnfCodeVal] at hev
      cases hfind : jps.find? (fun entry => entry.jpId == id) with
      | none => simp [hfind] at hev
      | some jp =>
        rw [hfind] at hev
        dsimp only [Bind.bind, Option.bind] at hev
        cases hne : (args.length != jp.numParams) with
        | true => simp [hne] at hev
        | false =>
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at hev
          cases hvals : args.mapM (evalLcnfArgVal env) with
          | none => simp [hvals] at hev
          | some vals =>
            rw [hvals] at hev
            dsimp only [Bind.bind, Option.bind] at hev
            obtain ⟨hpBody, hjpsDrop, _, hfn⟩ := applyJps_find hjps hfind
            have hlenEq : vals.length = jp.numParams := by
              have h1 := option_mapM_length (evalLcnfArgVal env) args vals hvals
              have h2 : args.length = jp.numParams := by simpa [bne_eq_false_iff_eq] using hne
              omega
            obtain ⟨hst, outJ, hfoJ, happJ⟩ :=
              ih jp.jpBody (vals ++ jp.declEnv) _ st st' v hpBody hjpsDrop hev
            refine ⟨hst, .jumped id vals, by simp [evalFoBlock, hvals], ?_⟩
            rw [hfn vals hlenEq, hfoJ]
            exact happJ

/-- Converse fuel adequacy: `evalFoBlock` + `applyJps` implies `evalLcnfCodeVal` succeeds for all `fuel ≥ minLcnfFuel c + jpsFuel jps`. -/
private theorem evalFoBlock_implies_evalLcnfCodeVal :
    ∀ (fuel : Nat) (c : LcnfCode) (env : List LcnfVal) (jps : List LcnfJpClosure)
      (st : List (Nat × Nat)) (out : FoOutcome) (v : LcnfVal),
      foPureCode c = true →
      SavedDepthWF jps →
      evalFoBlock env c = some out →
      applyJps jps out = some v →
      minLcnfFuel c + jpsFuel jps ≤ fuel →
      evalLcnfCodeVal fuel env jps st c = some (v, st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c _ _ _ _ _ _ _ _ _ hle
    have := minLcnfFuel_pos c
    omega
  | succ f ih =>
    intro c env jps st out v hp hjps hfo happ hfuel
    cases c with
    | «return» a =>
      simp only [evalFoBlock] at hfo
      cases ha : evalLcnfArgVal env a <;> simp [ha] at hfo
      subst hfo
      simp only [applyJps_returned, Option.some.injEq] at happ
      subst happ
      simp [evalLcnfCodeVal, ha]
    | unreach => simp [evalFoBlock] at hfo
    | letValue lv body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalFoBlock] at hfo
      cases hlv : evalFoLetVal env lv with
      | none => simp [hlv] at hfo
      | some val =>
        rw [hlv] at hfo
        simp only [minLcnfFuel] at hfuel
        have hbpos := minLcnfFuel_pos body
        have hfpos : 1 ≤ f := by omega
        have hevLv : evalLcnfLetValueVal f env jps st lv = some (val, st) :=
          (evalFoLetVal_iff hfpos hp.1).mpr ⟨rfl, hlv⟩
        simp only [evalLcnfCodeVal, Bind.bind, Option.bind, hevLv]
        exact ih body (val :: env) jps st out v hp.2 hjps hfo happ (by omega)
    | ifBool cond t fls =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalFoBlock] at hfo
      cases hc : evalLcnfArgVal env cond with
      | none => simp [hc] at hfo
      | some cv =>
        cases cv <;> simp [hc] at hfo
        rename_i bv
        simp only [minLcnfFuel] at hfuel
        simp only [evalLcnfCodeVal, Bind.bind, Option.bind, hc]
        cases bv with
        | true =>
          simp only [↓reduceIte] at hfo ⊢
          exact ih t env jps st out v hp.1 hjps hfo happ (by omega)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hfo ⊢
          exact ih fls env jps st out v hp.2 hjps hfo happ (by omega)
    | cases scrut arms =>
      simp only [foPureCode] at hp
      simp only [evalFoBlock] at hfo
      cases hs : evalLcnfArgVal env scrut with
      | none => simp [hs] at hfo
      | some sv =>
        cases sv <;> simp [hs] at hfo
        rename_i tag fs
        rw [evalFoArm_eq_find] at hfo
        cases hf : arms.find? (fun (armTag, _, _) => armTag == tag) with
        | none => simp [hf] at hfo
        | some arm =>
          obtain ⟨atag, names, armBody⟩ := arm
          rw [hf] at hfo
          dsimp only at hfo
          cases hsp : splitValues fs names with
          | none => simp [hsp] at hfo
          | some vals =>
            rw [hsp] at hfo
            obtain ⟨hpArm, hfuelArm⟩ := foPureArms_mem hp (List.mem_of_find?_eq_some hf)
            simp only [minLcnfFuel] at hfuel
            simp only [evalLcnfCodeVal, Bind.bind, Option.bind, hs, hf, hsp]
            exact ih armBody (vals.reverse ++ env) jps st out v hpArm hjps hfo happ (by omega)
    | jpDecl id n jpBody body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalFoBlock] at hfo
      cases houtB : evalFoBlock env body with
      | none => simp [houtB] at hfo
      | some outB =>
        rw [houtB] at hfo
        let jpNew : LcnfJpClosure := ⟨id, n, env, jps.length, jpBody⟩
        have hjps' : SavedDepthWF (jpNew :: jps) := .cons rfl hp.1 hjps
        have happB : applyJps (jpNew :: jps) outB = some v := by
          cases outB with
          | returned rv =>
            dsimp only at hfo
            injection hfo with hEq; subst hEq
            simpa using happ
          | jumped tid argVals =>
            dsimp only at hfo
            have hcomm : (id == tid) = (tid == id) := by
              cases h1 : (id == tid) <;> cases h2 : (tid == id) <;> simp_all [beq_iff_eq]
            simp only [applyJps, jpNew, hcomm]
            cases htid : (tid == id) with
            | true =>
              simp only [htid, ↓reduceIte] at hfo ⊢
              cases hlen : (argVals.length == n) with
              | false => simp [hlen] at hfo
              | true =>
                simp only [hlen, ↓reduceIte] at hfo ⊢
                rw [hfo]; exact happ
            | false =>
              simp only [htid, Bool.false_eq_true, ↓reduceIte] at hfo ⊢
              injection hfo with hEq; subst hEq
              exact happ
        simp only [minLcnfFuel] at hfuel
        simp only [evalLcnfCodeVal]
        exact ih body env (jpNew :: jps) st outB v hp.2 hjps' houtB happB
          (by simp only [jpsFuel, jpNew]; omega)
    | jmp id args =>
      simp only [evalFoBlock] at hfo
      cases hvals : args.mapM (evalLcnfArgVal env) with
      | none => simp [hvals] at hfo
      | some vals =>
        rw [hvals] at hfo
        simp only [Option.map_some, Option.some.injEq] at hfo
        subst hfo
        obtain ⟨jp, outJ, hfind, hlenV, houtJ, happJ⟩ := applyJps_jumped_some hjps happ
        obtain ⟨hpBody, hjpsDrop, hfuelDrop, _⟩ := applyJps_find hjps hfind
        have hlenArgs : args.length = jp.numParams :=
          (option_mapM_length (evalLcnfArgVal env) args vals hvals).trans hlenV
        have hneFalse : (args.length != jp.numParams) = false := by
          simp [hlenArgs]
        simp only [minLcnfFuel] at hfuel
        simp only [evalLcnfCodeVal, hfind, Bind.bind, Option.bind, hneFalse, Bool.false_eq_true, ↓reduceIte, hvals]
        exact ih jp.jpBody (vals ++ jp.declEnv) _ st outJ v hpBody hjpsDrop houtJ happJ (by omega)

/-! ## 6. Compiler Simulation Proof (`compileCode_sound`) -/

private theorem bv64_add_ofNat {a b : Nat} (hab : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  have ha : a < 2 ^ 64 := by omega
  have hb : b < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

private theorem bv64_add_right_cancel {u w v : Word} (h : u + v = w + v) : u = w := by
  apply BitVec.eq_of_toNat_eq
  have hu := u.isLt
  have hw := w.isLt
  have hv := v.isLt
  have ht : (u + v).toNat = (w + v).toNat := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add] at ht
  omega

private theorem bv64_sub_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply bv64_add_right_cancel (v := BitVec.ofNat 64 b)
  rw [BitVec.sub_add_cancel, bv64_add_ofNat (by omega)]
  have hsub : a - b + b = a := by omega
  rw [hsub]

private theorem bv64_mul_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a * b < 2 ^ 64) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

private theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem bv64_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = (a == b) := by
  cases heq : (a == b) with
  | true =>
    have hab : a = b := beq_iff_eq.mp heq
    subst hab; simp
  | false =>
    cases hbv : (BitVec.ofNat 64 a == BitVec.ofNat 64 b) with
    | false => rfl
    | true =>
      have hw : BitVec.ofNat 64 a = BitVec.ofNat 64 b := beq_iff_eq.mp hbv
      have ht := congrArg BitVec.toNat hw
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
      exact absurd (beq_iff_eq.mpr ht) (by simp [heq])

private theorem word10_ne_zero (b : Bool) :
    ((if b then (1#64 : Word) else 0#64) != 0#64) = b := by
  cases b <;> decide

private theorem res_var_self (lc : FMap String PanVal) (v : String) (old : Option PanVal) :
    res_var lc (v, old) v = old := by
  cases old <;> simp [res_var, DOMSUB, FUPDATE]

private theorem res_var_ne (lc : FMap String PanVal) (v x : String) (old : Option PanVal)
    (hne : x ≠ v) :
    res_var lc (v, old) x = lc x := by
  cases old <;> simp [res_var, DOMSUB, FUPDATE, hne]

/-- Encoding relation for 1-word scalar/boolean/erased LCNF values. -/
def encodeScalar : LcnfVal → FoScalarTy → Word → Prop
  | .scalar n, .scalar hi, w => n ≤ hi ∧ hi < 2 ^ 64 ∧ w = BitVec.ofNat 64 n
  | .bool b,   .bool,      w => w = (if b then 1#64 else 0#64)
  | .erased,   .erased,    w => w = 0#64
  | _,         _,          _ => False

private theorem encodeScalar_subTy {v : LcnfVal} {actual expected : FoScalarTy} {w : Word}
    (henc : encodeScalar v actual w) (hsub : actual.subTy expected = true) :
    encodeScalar v expected w := by
  cases actual <;> cases expected <;> simp [FoScalarTy.subTy] at hsub
  · rename_i a b
    cases v <;> simp [encodeScalar] at henc ⊢
    exact ⟨by omega, hsub.2, henc.2.2⟩
  · exact henc
  · exact henc

/-- Relational representation of distinct-name scalar constructor fields in `PanVal.rstruct`. -/
inductive CtorFieldsRel : List (String × LcnfVal) → List String → List Nat → List PanVal → Prop where
  | nil : CtorFieldsRel [] [] [] []
  | cons {nm : String} {n b : Nat} {fs : List (String × LcnfVal)}
      {nms : List String} {bs : List Nat} {pvs : List PanVal} :
      n ≤ b → b < 2 ^ 64 → nm ∉ nms →
      CtorFieldsRel fs nms bs pvs →
      CtorFieldsRel ((nm, .scalar n) :: fs) (nm :: nms) (b :: bs) (.word (BitVec.ofNat 64 n) :: pvs)

private theorem ctorFieldsRel_shapes {fs : List (String × LcnfVal)} {nms : List String}
    {bs : List Nat} {pvs : List PanVal} (h : CtorFieldsRel fs nms bs pvs) :
    shapes_of pvs = List.replicate nms.length Shape.One ∧ fs.length = nms.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ ih => simp [shapes_of, List.replicate_succ, ih.1, ih.2]

private theorem find_skip_of_not_mem {nm : String} {v : LcnfVal}
    {fs : List (String × LcnfVal)} {nms : List String} (hnot : nm ∉ nms) :
    splitValues ((nm, v) :: fs) nms = splitValues fs nms := by
  induction nms with
  | nil => rfl
  | cons m ms ih =>
    have hne : (nm == m) = false :=
      beq_eq_false_iff_ne.mpr (fun heq => hnot (heq ▸ List.Mem.head _))
    have hnot' : nm ∉ ms := fun hm => hnot (List.Mem.tail _ hm)
    simp only [splitValues, List.find?, hne, ih hnot']

private theorem ctorFieldsRel_splitValues {fs : List (String × LcnfVal)} {nms : List String}
    {bs : List Nat} {pvs : List PanVal} (h : CtorFieldsRel fs nms bs pvs) :
    splitValues fs nms = some (fs.map Prod.snd) := by
  induction h with
  | nil => rfl
  | @cons nm n _ fs' nms' _ _ _ _ hnot _ ih =>
    simp only [splitValues, List.find?, beq_self_eq_true, find_skip_of_not_mem hnot, ih, List.map]

/-- Full first-order value representation in `PanVal`. -/
def encodeFoVal (tags : List String) : LcnfVal → FoTy → PanVal → Prop
  | v, .one st, .word w => encodeScalar v st w
  | .ctor tag fs, .ctor cTag cNames cBounds, .rstruct (.word wTag :: pvs) =>
    tag = cTag ∧
    ∃ idx, lookupTagIdx tags tag = some idx ∧ idx < 2 ^ 64 ∧
      wTag = BitVec.ofNat 64 idx ∧
      CtorFieldsRel fs cNames cBounds pvs
  | _, _, _ => False

private theorem encodeFoVal_shape {tags : List String} {v : LcnfVal} {ty : FoTy} {pv : PanVal}
    (h : encodeFoVal tags v ty pv) : shape_of pv = ty.toShape := by
  cases ty with
  | one _ =>
    cases pv with
    | word _ => rfl
    | rstruct _ => cases h
  | ctor cTag cNames cBounds =>
    cases v <;> try cases h
    cases pv with
    | word _ => cases h
    | rstruct vs =>
      cases vs with
      | nil => cases h
      | cons v0 pvs =>
        cases v0 with
        | rstruct _ => cases h
        | word wTag =>
          obtain ⟨_, _, _, _, _, hrel⟩ := h
          have hsh := (ctorFieldsRel_shapes hrel).1
          simp [shape_of, shapes_of, FoTy.toShape, List.replicate_succ, hsh]

/-- Environment invariant linking `env`, `envTys`, `varSlots`, and `s.locals`. -/
inductive EnvMatches (tags : List String) :
    List LcnfVal → List FoTy → List (String × Shape) → FMap String PanVal → Prop where
  | nil (lc : FMap String PanVal) : EnvMatches tags [] [] [] lc
  | cons {v : LcnfVal} {ty : FoTy} {slot : String} {vs : List LcnfVal}
      {tys : List FoTy} {slots : List (String × Shape)} {lc : FMap String PanVal}
      {pv : PanVal} :
      lc slot = some pv →
      encodeFoVal tags v ty pv →
      EnvMatches tags vs tys slots lc →
      EnvMatches tags (v :: vs) (ty :: tys) ((slot, ty.toShape) :: slots) lc

private theorem EnvMatches.congr {tags : List String} {env : List LcnfVal} {envTys : List FoTy}
    {varSlots : List (String × Shape)} {lc lc' : FMap String PanVal}
    (h : EnvMatches tags env envTys varSlots lc)
    (heq : ∀ p ∈ varSlots, lc' p.1 = lc p.1) :
    EnvMatches tags env envTys varSlots lc' := by
  induction h with
  | nil _ => exact .nil lc'
  | @cons v ty slot vs tys slots _ pv hlc henc _ ih =>
    have hhead : lc' slot = some pv := (heq (slot, ty.toShape) (List.Mem.head _)).trans hlc
    exact .cons hhead henc (ih (fun p hp => heq p (List.Mem.tail _ hp)))

private theorem EnvMatches.lookup {tags : List String} {env : List LcnfVal} {envTys : List FoTy}
    {varSlots : List (String × Shape)} {lc : FMap String PanVal}
    (h : EnvMatches tags env envTys varSlots lc) :
    ∀ (idx : Nat) {ty : FoTy}, envTys[idx]? = some ty →
      ∃ v slot pv,
        env[idx]? = some v ∧
        varSlots[idx]? = some (slot, ty.toShape) ∧
        lc slot = some pv ∧
        encodeFoVal tags v ty pv := by
  induction h with
  | nil _ => intro idx _ hget; simp at hget
  | @cons v ty0 slot vs tys slots _ pv hlc henc _ ih =>
    intro idx ty hget
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      exact ⟨v, slot, pv, rfl, rfl, hlc, henc⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hget ⊢
      exact ih k hget

/-- Slot-index upper bound for computational `'v'` slots. -/
def VarSlotsWF (nextId : Nat) (varSlots : List (String × Shape)) : Prop :=
  ∀ p ∈ varSlots, ∃ i, i < nextId ∧ p.1 = mkSlot 'v' i

private theorem VarSlotsWF.mono {n1 n2 : Nat} {vs : List (String × Shape)}
    (hle : n1 ≤ n2) (h : VarSlotsWF n1 vs) : VarSlotsWF n2 vs :=
  fun p hp => let ⟨i, hi, heq⟩ := h p hp; ⟨i, by omega, heq⟩

private theorem VarSlotsWF.lookup {nextId : Nat} {vs : List (String × Shape)}
    (h : VarSlotsWF nextId vs) {idx : Nat} {slot : String} {sh : Shape}
    (hget : vs[idx]? = some (slot, sh)) : ∃ i, i < nextId ∧ slot = mkSlot 'v' i :=
  h (slot, sh) (List.mem_of_getElem? hget)

/-- Well-formedness and index-disjointness of the active `CompiledJp` stack. -/
inductive JpStackWF : Nat → List JpSig → List CompiledJp → Prop where
  | nil (n : Nat) : JpStackWF n [] []
  | cons {n0 n1 : Nat} {sig : JpSig} {sigs : List JpSig} {cjs : List CompiledJp} :
      JpStackWF n0 sigs cjs →
      sig.jpId ∉ sigs.map JpSig.jpId →
      n0 + 1 + sig.params.length ≤ n1 →
      JpStackWF n1 (sig :: sigs)
        (⟨sig.jpId, sig.params.length, mkSlot 'h' n0, mkFreshSlots 'a' (n0 + 1) sig.params.length⟩ :: cjs)

private theorem JpStackWF.mono {n1 n2 : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    (hle : n1 ≤ n2) (h : JpStackWF n1 sigs cjs) : JpStackWF n2 sigs cjs := by
  cases h with
  | nil _ => exact .nil n2
  | cons hsub hnot hbound => exact .cons hsub hnot (by omega)

def ArgSlotsBound (argSlots : List String) (lc : FMap String PanVal) : Prop :=
  ∀ a ∈ argSlots, ∃ w : Word, lc a = some (.word w)

def JpsIdle (jpSlots : List CompiledJp) (lc : FMap String PanVal) : Prop :=
  ∀ cj ∈ jpSlots, lc cj.hitSlot = some (.word 0#64) ∧ ArgSlotsBound cj.argSlots lc

/-- Pointwise relation between jump argument values and staged `'a'` local slots. -/
inductive ScalarSlotsRel :
    List LcnfVal → List FoScalarTy → List String → FMap String PanVal → Prop where
  | nil (lc : FMap String PanVal) : ScalarSlotsRel [] [] [] lc
  | cons {v : LcnfVal} {st : FoScalarTy} {slot : String} {vs : List LcnfVal}
      {sts : List FoScalarTy} {slots : List String} {lc : FMap String PanVal} {w : Word} :
      lc slot = some (.word w) →
      encodeScalar v st w →
      ScalarSlotsRel vs sts slots lc →
      ScalarSlotsRel (v :: vs) (st :: sts) (slot :: slots) lc

private theorem ScalarSlotsRel.congr {vs : List LcnfVal} {sts : List FoScalarTy}
    {slots : List String} {lc lc' : FMap String PanVal}
    (h : ScalarSlotsRel vs sts slots lc) (heq : ∀ a ∈ slots, lc' a = lc a) :
    ScalarSlotsRel vs sts slots lc' := by
  induction h with
  | nil _ => exact .nil lc'
  | @cons v st slot vs' sts' slots' _ w hlc henc _ ih =>
    exact .cons ((heq slot (List.Mem.head _)).trans hlc) henc
      (ih (fun a ha => heq a (List.Mem.tail _ ha)))

private theorem ScalarSlotsRel.length_eq {vs : List LcnfVal} {sts : List FoScalarTy}
    {slots : List String} {lc : FMap String PanVal}
    (h : ScalarSlotsRel vs sts slots lc) : vs.length = sts.length := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ ih => simp [ih]

/-- Post-jump stack state: exactly the target join point has `hitSlot = 1#64` and populated `argSlots`;
    all other active join points remain idle (`hitSlot = 0#64`). -/
inductive JpTriggered (tid : Nat) (argVals : List LcnfVal) (lc : FMap String PanVal) :
    List JpSig → List CompiledJp → Prop where
  | here {sig : JpSig} {cj : CompiledJp} {sigs : List JpSig} {cjs : List CompiledJp} :
      sig.jpId = tid →
      lc cj.hitSlot = some (.word 1#64) →
      ScalarSlotsRel argVals sig.params cj.argSlots lc →
      JpsIdle cjs lc →
      JpTriggered tid argVals lc (sig :: sigs) (cj :: cjs)
  | there {sig : JpSig} {cj : CompiledJp} {sigs : List JpSig} {cjs : List CompiledJp} :
      sig.jpId ≠ tid →
      lc cj.hitSlot = some (.word 0#64) →
      ArgSlotsBound cj.argSlots lc →
      JpTriggered tid argVals lc sigs cjs →
      JpTriggered tid argVals lc (sig :: sigs) (cj :: cjs)

private theorem jpStack_slots_lt {n : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    (h : JpStackWF n sigs cjs) :
    ∀ cj ∈ cjs,
      (∃ i < n, cj.hitSlot = mkSlot 'h' i) ∧
      (∀ a ∈ cj.argSlots, ∃ j < n, a = mkSlot 'a' j) := by
  induction h with
  | nil _ => intro _ hm; cases hm
  | @cons n0 n1 sig sigs' cjs' hsub _ hbound ih =>
    intro cj hm
    rcases List.mem_cons.mp hm with rfl | htl
    · refine ⟨⟨n0, by omega, rfl⟩, fun a ha => ?_⟩
      obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots ha
      exact ⟨j, by omega, rfl⟩
    · obtain ⟨⟨i, hi, hh⟩, hargs⟩ := ih cj htl
      exact ⟨⟨i, by omega, hh⟩, fun a ha => let ⟨j, hj, eq⟩ := hargs a ha; ⟨j, by omega, eq⟩⟩

private theorem JpsIdle.congr_of_wf {n : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    {lc lc' : FMap String PanVal} (hwf : JpStackWF n sigs cjs) (hidle : JpsIdle cjs lc)
    (heq : ∀ i < n, lc' (mkSlot 'h' i) = lc (mkSlot 'h' i) ∧ lc' (mkSlot 'a' i) = lc (mkSlot 'a' i)) :
    JpsIdle cjs lc' := by
  intro cj hcj
  obtain ⟨⟨i, hi, hh⟩, hargs⟩ := jpStack_slots_lt hwf cj hcj
  obtain ⟨hhit, hbnd⟩ := hidle cj hcj
  refine ⟨by rw [hh, (heq i hi).1, ← hh, hhit], fun a ha => ?_⟩
  obtain ⟨j, hj, rfl⟩ := hargs a ha
  obtain ⟨w, hw⟩ := hbnd (mkSlot 'a' j) ha
  exact ⟨w, (heq j hj).2.trans hw⟩

private theorem JpTriggered.congr_of_wf {n : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    {tid : Nat} {argVals : List LcnfVal} {lc lc' : FMap String PanVal}
    (hwf : JpStackWF n sigs cjs)
    (htrig : JpTriggered tid argVals lc sigs cjs)
    (heq : ∀ i < n, lc' (mkSlot 'h' i) = lc (mkSlot 'h' i) ∧ lc' (mkSlot 'a' i) = lc (mkSlot 'a' i)) :
    JpTriggered tid argVals lc' sigs cjs := by
  induction hwf with
  | nil _ => cases htrig
  | @cons n0 n1 sig sigs' cjs' hsub _ hbound ih =>
    have heqSub : ∀ i < n0, lc' (mkSlot 'h' i) = lc (mkSlot 'h' i) ∧ lc' (mkSlot 'a' i) = lc (mkSlot 'a' i) :=
      fun i hi => heq i (by omega)
    cases htrig with
    | here hid hhit hrel hidle =>
      refine .here hid ((heq n0 (by omega)).1.trans hhit) ?_ (JpsIdle.congr_of_wf hsub hidle heqSub)
      refine hrel.congr (fun a ha => ?_)
      obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots ha
      exact (heq j (by omega)).2
    | there hne hhit hbnd hrest =>
      refine .there hne ((heq n0 (by omega)).1.trans hhit) ?_ (ih hrest heqSub)
      intro a ha
      obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots ha
      obtain ⟨w, hw⟩ := hbnd (mkSlot 'a' j) ha
      exact ⟨w, (heq j (by omega)).2.trans hw⟩

/-- Argument compilation simulation (`compileArg` vs `evalLcnfArgVal` + `inferArgFoTy`). -/
private theorem compileArg_sound {θ : Type} {tags : List String}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    {s : PanState θ} (henv : EnvMatches tags env envTys varSlots s.locals)
    {a : LcnfArg} {ty : FoTy} (hty : inferArgFoTy envTys a = some ty) :
    ∃ v pv,
      evalLcnfArgVal env a = some v ∧
      eval s (compileArg varSlots a) = some pv ∧
      argShape varSlots a = ty.toShape ∧
      encodeFoVal tags v ty pv := by
  cases a with
  | bvar idx =>
    simp only [inferArgFoTy] at hty
    obtain ⟨v, slot, pv, henvGet, hslotsGet, hlc, henc⟩ := henv.lookup idx hty
    exact ⟨v, pv, henvGet, by simp [compileArg, hslotsGet, hlc],
      by simp [argShape, hslotsGet], henc⟩
  | lit n =>
    simp only [inferArgFoTy] at hty
    by_cases hlt : n < 2 ^ 64 <;> simp [hlt] at hty
    subst hty
    exact ⟨.scalar n, .word (BitVec.ofNat 64 n), rfl, rfl, rfl, ⟨Nat.le_refl n, hlt, rfl⟩⟩
  | boolLit b =>
    simp only [inferArgFoTy, Option.some.injEq] at hty
    subst hty
    exact ⟨.bool b, .word (if b then 1#64 else 0#64), rfl, rfl, rfl, rfl⟩
  | erased =>
    simp only [inferArgFoTy, Option.some.injEq] at hty
    subst hty
    exact ⟨.erased, .word 0#64, rfl, rfl, rfl, rfl⟩
  | stateTok _ => simp [inferArgFoTy] at hty

private theorem inferCtorFields_sound {θ : Type} {tags : List String}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    {s : PanState θ} (henv : EnvMatches tags env envTys varSlots s.locals) :
    ∀ (fields : List (String × LcnfArg)) {nms : List String} {bs : List Nat},
      inferCtorFields envTys fields = some (nms, bs) →
      ∃ fs pvs,
        (fields.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)) = some fs ∧
        evalList s (fields.map (fun f => compileArg varSlots f.2)) = some pvs ∧
        fields.length = nms.length ∧
        CtorFieldsRel fs nms bs pvs
  | [], _, _, h => by
    simp only [inferCtorFields, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨[], [], rfl, rfl, rfl, .nil⟩
  | (nm, a) :: rest, nms, bs, h => by
    simp only [inferCtorFields] at h
    cases ha : inferArgFoTy envTys a with
    | none => simp [ha] at h
    | some tyA =>
      rw [ha] at h
      cases tyA with
      | ctor _ _ _ => simp at h
      | one st =>
        cases st with
        | bool | erased => simp at h
        | scalar b =>
          cases hrest : inferCtorFields envTys rest with
          | none => simp [hrest] at h
          | some p =>
            obtain ⟨nms', bs'⟩ := p
            rw [hrest] at h
            dsimp only at h
            cases hcond : (decide (b < 2 ^ 64) && !(nms'.contains nm)) with
            | false => rw [hcond] at h; simp at h
            | true =>
              simp only [hcond, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
                decide_eq_false_iff_not, decide_eq_true_eq] at hcond
              obtain ⟨va, pva, heva, hpva, _, henca⟩ := compileArg_sound henv ha
              cases pva with
              | rstruct _ => cases henca
              | word wa =>
                cases va <;> simp [encodeFoVal, encodeScalar] at henca
                rename_i na
                rcases henca with ⟨hle, _, rfl⟩
                obtain ⟨fs', pvs', hfs', hpvs', hlen', hrel'⟩ := inferCtorFields_sound henv rest hrest
                refine ⟨(nm, .scalar na) :: fs', .word (BitVec.ofNat 64 na) :: pvs', ?_, ?_, by simp [hlen'],
                  .cons hle hcond.1 hcond.2 hrel'⟩
                · rw [List.mapM_cons]
                  dsimp only [Bind.bind, Option.bind, pure] at hfs' ⊢
                  rw [heva]
                  dsimp only
                  rw [hfs']
                · simp [hpva, hpvs']

/-- State-setup / state-teardown characterization of `wrapDecZeros`. -/
private theorem evaluate_wrapDecZeros {θ : Type} :
    ∀ (start k : Nat) (inner : PStmt) (s : PanState θ),
      ∃ sInner : PanState θ,
        sInner.clock = s.clock ∧
        (StateWF s → StateWF sInner) ∧
        (∀ a ∈ mkFreshSlots 'a' start k, sInner.locals a = some (.word 0#64)) ∧
        (∀ x, (∀ j, start ≤ j → j < start + k → x ≠ mkSlot 'a' j) → sInner.locals x = s.locals x) ∧
        ∃ sOut : PanState θ,
          let rMid := evaluate inner sInner
          evaluate (wrapDecZeros (mkFreshSlots 'a' start k) inner) s = (rMid.1, sOut) ∧
          sOut.clock = rMid.2.clock ∧
          (StateWF rMid.2 → StateWF sOut) ∧
          (∀ x, (∀ j, start ≤ j → j < start + k → x ≠ mkSlot 'a' j) → sOut.locals x = rMid.2.locals x)
  | _, 0, inner, s => by
    refine ⟨s, rfl, id, ?_, fun _ _ => rfl, (evaluate inner s).2, rfl, rfl, id, fun _ _ => rfl⟩
    intro _ hm; cases hm
  | start, k + 1, inner, s => by
    let a0 := mkSlot 'a' start
    let s1 : PanState θ := { s with locals := FUPDATE s.locals (a0, .word 0#64) }
    obtain ⟨sInner, hclkIn, hwfIn, hbndIn, hpresIn, sOut1, hev1, hclkOut1, hwfOut1, hpresOut1⟩ :=
      evaluate_wrapDecZeros (start + 1) k inner s1
    refine ⟨sInner, hclkIn, fun h => hwfIn ⟨h.1, h.2⟩, ?_, ?_,
      { sOut1 with locals := res_var sOut1.locals (a0, s.locals a0) }, ?_, hclkOut1,
      fun h => let h1 := hwfOut1 h; ⟨h1.1, h1.2⟩, ?_⟩
    · intro a ha
      simp only [mkFreshSlots, List.mem_cons] at ha
      rcases ha with rfl | htl
      · rw [hpresIn a0 (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
        simp [s1, FUPDATE]
      · exact hbndIn a htl
    · intro x hx
      rw [hpresIn x (fun j hj1 hj2 => hx j (by omega) (by omega))]
      have hne0 : x ≠ a0 := hx start (Nat.le_refl _) (by omega)
      simp [s1, FUPDATE, hne0]
    · simp only [mkFreshSlots, wrapDecZeros]
      rw [evaluate_dec, eval_const]
      dsimp only
      have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
      simp only [hsh, ↓reduceIte]
      rw [hev1]
    · intro x hx
      have hne0 : x ≠ a0 := hx start (Nat.le_refl _) (by omega)
      dsimp only
      rw [res_var_ne _ _ _ _ hne0]
      exact hpresOut1 x (fun j hj1 hj2 => hx j (by omega) (by omega))

/-- Execution of `assignJpArgs` populates `argSlots` with `ScalarSlotsRel` while preserving all non-target slots. -/
private theorem evaluate_assignJpArgs {θ : Type} {tags : List String} {vBound : Nat}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    (vswf : VarSlotsWF vBound varSlots) :
    ∀ (aStart : Nat) (args : List LcnfArg) (paramTys : List FoScalarTy) (s : PanState θ),
      StateWF s →
      EnvMatches tags env envTys varSlots s.locals →
      args.length = paramTys.length →
      checkArgsSubTy envTys args paramTys = true →
      ArgSlotsBound (mkFreshSlots 'a' aStart paramTys.length) s.locals →
      ∃ argVals sOut,
        args.mapM (evalLcnfArgVal env) = some argVals ∧
        evaluate (assignJpArgs varSlots (mkFreshSlots 'a' aStart paramTys.length) args) s = (.normal, sOut) ∧
        sOut.clock = s.clock ∧
        StateWF sOut ∧
        ScalarSlotsRel argVals paramTys (mkFreshSlots 'a' aStart paramTys.length) sOut.locals ∧
        (∀ x, (∀ j, aStart ≤ j → j < aStart + paramTys.length → x ≠ mkSlot 'a' j) →
          sOut.locals x = s.locals x)
  | _, [], [], s, hwf, _, _, _, _ =>
    ⟨[], s, rfl, evaluate_skip s, rfl, hwf, .nil _, fun _ _ => rfl⟩
  | _, _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | _, [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | aStart, a :: as, expected :: es, s, hwf, henv, hlen, hsub, hbnd => by
    simp only [checkArgsSubTy] at hsub
    cases hact : inferArgScalarTy envTys a with
    | none => simp [hact] at hsub
    | some actual =>
      rw [hact] at hsub
      simp only [Bool.and_eq_true] at hsub
      simp only [inferArgScalarTy] at hact
      cases haTy : inferArgFoTy envTys a with
      | none => simp [haTy] at hact
      | some tyA =>
        rw [haTy] at hact
        cases tyA with
        | ctor _ _ _ => simp at hact
        | one stA =>
          dsimp only at hact
          split at hact <;> simp at hact
          subst hact
          obtain ⟨va, pva, heva, hpva, _, henca⟩ := compileArg_sound henv haTy
          cases pva with
          | rstruct _ => cases henca
          | word wa =>
            have hencExp : encodeScalar va expected wa := encodeScalar_subTy henca hsub.1
            let dst := mkSlot 'a' aStart
            obtain ⟨wOld, hwOld⟩ := hbnd dst (by simp [List.length_cons, mkFreshSlots, dst])
            have hvalid : is_valid_value s .Local dst (.word wa) = true := by
              simp [is_valid_value, lookup_kvar, hwOld]
            let s1 := set_kvar .Local dst (.word wa) s
            have hwf1 : StateWF s1 := ⟨hwf.1, hwf.2⟩
            have henv1 : EnvMatches tags env envTys varSlots s1.locals :=
              henv.congr (fun p hp => by
                obtain ⟨i, _, hiEq⟩ := vswf p hp
                have hne : p.1 ≠ dst := hiEq ▸ mkSlot_ne_of_kind (by decide) i aStart
                simp [s1, set_kvar, set_var, FUPDATE, hne])
            have hbnd1 : ArgSlotsBound (mkFreshSlots 'a' (aStart + 1) es.length) s1.locals := by
              intro a' ha'
              obtain ⟨j, hj1, _, rfl⟩ := mem_mkFreshSlots ha'
              have hne : mkSlot 'a' j ≠ dst := (mkSlot_ne_of_lt (by omega : aStart < j)).symm
              obtain ⟨w', hw'⟩ := hbnd (mkSlot 'a' j) (by simp [List.length_cons, mkFreshSlots, ha'])
              exact ⟨w', by simp [s1, set_kvar, set_var, FUPDATE, hne, hw']⟩
            obtain ⟨valsRest, sOut, hmapRest, hevRest, hclkRest, hwfOut, hrelRest, hpresRest⟩ :=
              evaluate_assignJpArgs vswf (aStart + 1) as es s1 hwf1 henv1 (by simpa using hlen) hsub.2 hbnd1
            refine ⟨va :: valsRest, sOut, by simp [List.mapM_cons, heva, hmapRest], ?_, hclkRest, hwfOut, ?_, ?_⟩
            · simp only [List.length_cons, mkFreshSlots, assignJpArgs]
              rw [evaluate_seq, evaluate_assign, hpva]
              dsimp only
              rw [hvalid]
              exact hevRest
            · simp only [List.length_cons, mkFreshSlots]
              have hdstOut : sOut.locals dst = some (.word wa) := by
                rw [hpresRest dst (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
                simp [s1, set_kvar, set_var, FUPDATE]
              exact .cons hdstOut hencExp hrelRest
            · intro x hx
              simp only [List.length_cons] at hx
              rw [hpresRest x (fun j hj1 hj2 => hx j (by omega) (by omega))]
              have hne0 : x ≠ dst := hx aStart (Nat.le_refl _) (by omega)
              simp [s1, set_kvar, set_var, FUPDATE, hne0]

/-- Jump-dispatch across `JpStackWF`: executes `assignJpArgs ;; lassign hitSlot 1 ;; tick` and produces `JpTriggered`. -/
private theorem evaluate_jmp_stack {θ : Type} {tags : List String} {vBound n : Nat}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    (vswf : VarSlotsWF vBound varSlots)
    {jpSigs : List JpSig} {jpSlots : List CompiledJp}
    (jpswf : JpStackWF n jpSigs jpSlots)
    {id : Nat} {args : List LcnfArg} {sig : JpSig}
    (hfind : jpSigs.find? (fun s => s.jpId == id) = some sig)
    (hlen : args.length = sig.params.length)
    (hsub : checkArgsSubTy envTys args sig.params = true)
    {s : PanState θ} (hwf : StateWF s) (hclk : 1 ≤ s.clock)
    (henv : EnvMatches tags env envTys varSlots s.locals)
    (hidle : JpsIdle jpSlots s.locals) :
    ∃ cj argVals s1,
      jpSlots.find? (fun c => c.jpId == id) = some cj ∧
      args.mapM (evalLcnfArgVal env) = some argVals ∧
      evaluate (.seq (assignJpArgs varSlots cj.argSlots args)
        (.seq (.lassign cj.hitSlot (.const 1#64)) .tick)) s = (.normal, s1) ∧
      s.clock ≤ s1.clock + 1 ∧
      StateWF s1 ∧
      JpTriggered id argVals s1.locals jpSigs jpSlots ∧
      (∀ idx, s1.locals (mkSlot 'v' idx) = s.locals (mkSlot 'v' idx)) ∧
      (∀ k idx, n ≤ idx → (k = 'h' ∨ k = 'a') → s1.locals (mkSlot k idx) = s.locals (mkSlot k idx)) := by
  induction jpswf with
  | nil _ => simp at hfind
  | @cons n0 n1 sigHd sigsTl cjsTl hsubWf _ hbound ih =>
    let cjHd : CompiledJp := ⟨sigHd.jpId, sigHd.params.length, mkSlot 'h' n0,
      mkFreshSlots 'a' (n0 + 1) sigHd.params.length⟩
    simp only [List.find?] at hfind
    cases heq : (sigHd.jpId == id) with
    | true =>
      rw [heq] at hfind
      simp only [Option.some.injEq] at hfind
      subst hfind
      obtain ⟨hhit0, hbnd0⟩ := hidle cjHd (List.Mem.head _)
      have hidleTl : JpsIdle cjsTl s.locals := fun c hc => hidle c (List.Mem.tail _ hc)
      obtain ⟨argVals, sArgs, hmap, hevArgs, hclkArgs, hwfArgs, hrelArgs, hpresArgs⟩ :=
        evaluate_assignJpArgs vswf (n0 + 1) args sigHd.params s hwf henv hlen hsub hbnd0
      have hhitArgs : sArgs.locals (mkSlot 'h' n0) = some (.word 0#64) :=
        (hpresArgs _ (fun j _ _ => mkSlot_ne_of_kind (by decide) n0 j)).trans hhit0
      have hvalidHit : is_valid_value sArgs .Local (mkSlot 'h' n0) (.word 1#64) = true := by
        simp [is_valid_value, lookup_kvar, hhitArgs]
      let sHit := set_kvar .Local (mkSlot 'h' n0) (.word 1#64) sArgs
      have hclkHit : (sHit.clock == 0) = false := by
        have hpos : 0 < sHit.clock := by simp [sHit, set_kvar, set_var, hclkArgs]; omega
        cases hsc : sHit.clock with
        | zero => omega
        | succ _ => rfl
      let s1 := dec_clock sHit
      refine ⟨cjHd, argVals, s1, by simp [cjHd, List.find?, heq], hmap, ?_, ?_, ⟨hwfArgs.1, hwfArgs.2⟩, ?_, ?_, ?_⟩
      · dsimp only [cjHd]
        rw [evaluate_seq, hevArgs]
        dsimp only
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [evaluate_seq, evaluate_assign, eval_const]
        dsimp only
        rw [hvalidHit]
        simp only [↓reduceIte, beq_self_eq_true]
        rw [evaluate_tick, hclkHit]
        rfl
      · simp only [s1, dec_clock_clock, sHit, set_kvar, set_var, hclkArgs]; omega
      · refine .here (beq_iff_eq.mp heq) (by simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE]) ?_ ?_
        · exact hrelArgs.congr (fun a ha => by
            obtain ⟨j, _, _, rfl⟩ := mem_mkFreshSlots ha
            have hne : mkSlot 'a' j ≠ mkSlot 'h' n0 := mkSlot_ne_of_kind (by decide) j n0
            simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hne])
        · refine JpsIdle.congr_of_wf hsubWf hidleTl (fun i hi => ⟨?_, ?_⟩)
          · have hneH : mkSlot 'h' i ≠ mkSlot 'h' n0 := mkSlot_ne_of_lt hi
            have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot 'h' i ≠ mkSlot 'a' j :=
              fun j _ _ => mkSlot_ne_of_kind (by decide) i j
            simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
          · have hneH : mkSlot 'a' i ≠ mkSlot 'h' n0 := mkSlot_ne_of_kind (by decide) i n0
            have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot 'a' i ≠ mkSlot 'a' j :=
              fun j hj1 _ => mkSlot_ne_of_lt (by omega)
            simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
      · intro idx
        have hneH : mkSlot 'v' idx ≠ mkSlot 'h' n0 := mkSlot_ne_of_kind (by decide) idx n0
        have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot 'v' idx ≠ mkSlot 'a' j :=
          fun j _ _ => mkSlot_ne_of_kind (by decide) idx j
        simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
      · intro k idx hge _
        have hneH : mkSlot k idx ≠ mkSlot 'h' n0 := (mkSlot_ne_of_lt (by omega : n0 < idx)).symm
        have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot k idx ≠ mkSlot 'a' j :=
          fun j _ hj2 => (mkSlot_ne_of_lt (by omega : j < idx)).symm
        simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
    | false =>
      rw [heq] at hfind
      obtain ⟨hhit0, hbnd0⟩ := hidle cjHd (List.Mem.head _)
      have hidleTl : JpsIdle cjsTl s.locals := fun c hc => hidle c (List.Mem.tail _ hc)
      obtain ⟨cj, argVals, s1, hcjFind, hmap, hev1, hclk1, hwf1, htrig1, hvPres, hhaPres⟩ :=
        ih hfind hidleTl
      refine ⟨cj, argVals, s1, by simp [List.find?, heq, hcjFind], hmap, hev1, hclk1, hwf1, ?_, hvPres, ?_⟩
      · refine .there (beq_eq_false_iff_ne.mp heq) ?_ ?_ htrig1
        · exact (hhaPres 'h' n0 (Nat.le_refl _) (Or.inl rfl)).trans hhit0
        · intro a ha
          obtain ⟨j, hj1, _, rfl⟩ := mem_mkFreshSlots ha
          obtain ⟨w, hw⟩ := hbnd0 (mkSlot 'a' j) ha
          exact ⟨w, (hhaPres 'a' j (by omega) (Or.inr rfl)).trans hw⟩
      · intro k idx hge hk
        exact hhaPres k idx (by omega) hk

/-- State-setup / state-teardown characterization of `bindJpParams`. -/
private theorem evaluate_bindJpParams_raw {θ : Type} (tags : List String) :
    ∀ (pStart aStart : Nat) (argVals : List LcnfVal) (paramTys : List FoScalarTy)
      (inner : PStmt) (s : PanState θ),
      StateWF s →
      ScalarSlotsRel argVals paramTys (mkFreshSlots 'a' aStart paramTys.length) s.locals →
      ∃ sInner : PanState θ,
        let k := paramTys.length
        let pSlots := mkFreshSlots 'v' pStart k
        sInner.clock = s.clock ∧
        StateWF sInner ∧
        (∀ x, (∀ j, pStart ≤ j → j < pStart + k → x ≠ mkSlot 'v' j) → sInner.locals x = s.locals x) ∧
        (∀ env envTys varSlots,
          EnvMatches tags env envTys varSlots sInner.locals →
          EnvMatches tags (argVals ++ env) (paramTys.map FoTy.one ++ envTys)
            ((pSlots.map (fun nm => (nm, Shape.One))) ++ varSlots) sInner.locals) ∧
        ∃ sOut : PanState θ,
          let rMid := evaluate inner sInner
          evaluate (bindJpParams pSlots (mkFreshSlots 'a' aStart k) inner) s = (rMid.1, sOut) ∧
          sOut.clock = rMid.2.clock ∧
          (StateWF rMid.2 → StateWF sOut) ∧
          ((∀ idx, rMid.2.locals (mkSlot 'v' idx) = sInner.locals (mkSlot 'v' idx)) →
            ∀ idx, sOut.locals (mkSlot 'v' idx) = s.locals (mkSlot 'v' idx)) ∧
          (∀ x, (∀ c, x ≠ mkSlot 'v' c) → sOut.locals x = rMid.2.locals x)
  | _, _, [], [], inner, s, hwf, .nil _ =>
    ⟨s, rfl, hwf, fun _ _ => rfl, fun _ _ _ h => h,
      (evaluate inner s).2, rfl, rfl, id, fun h => h, fun _ _ => rfl⟩
  | pStart, aStart, v :: vs, st :: sts, inner, s, hwf, .cons (w := w) hlcA hencA hrelRest => by
    let p0 := mkSlot 'v' pStart
    let a0 := mkSlot 'a' aStart
    let s1 : PanState θ := { s with locals := FUPDATE s.locals (p0, .word w) }
    have hwf1 : StateWF s1 := ⟨hwf.1, hwf.2⟩
    have hrel1 : ScalarSlotsRel vs sts (mkFreshSlots 'a' (aStart + 1) sts.length) s1.locals :=
      hrelRest.congr (fun a ha => by
        obtain ⟨j, _, _, rfl⟩ := mem_mkFreshSlots ha
        have hne : mkSlot 'a' j ≠ p0 := mkSlot_ne_of_kind (by decide) j pStart
        simp [s1, FUPDATE, hne])
    obtain ⟨sInner, hclkIn, hwfIn, hpresIn, hliftEnv, sOut1, hev1, hclkOut1, hwfOut1, hvOut1, hnonVOut1⟩ :=
      evaluate_bindJpParams_raw tags (pStart + 1) (aStart + 1) vs sts inner s1 hwf1 hrel1
    refine ⟨sInner, hclkIn, hwfIn, ?_, ?_,
      { sOut1 with locals := res_var sOut1.locals (p0, s.locals p0) }, ?_, hclkOut1,
      fun h => let h1 := hwfOut1 h; ⟨h1.1, h1.2⟩, ?_, ?_⟩
    · intro x hx
      simp only [List.length_cons] at hx
      rw [hpresIn x (fun j hj1 hj2 => hx j (by omega) (by omega))]
      have hne0 : x ≠ p0 := hx pStart (Nat.le_refl _) (by omega)
      simp [s1, FUPDATE, hne0]
    · intro env envTys varSlots henv
      have hp0In : sInner.locals p0 = some (.word w) := by
        rw [hpresIn p0 (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
        simp [s1, FUPDATE]
      simp only [List.length_cons, List.cons_append, List.map_cons, mkFreshSlots]
      exact .cons (ty := .one st) hp0In hencA (hliftEnv env envTys varSlots henv)
    · simp only [List.length_cons, mkFreshSlots, bindJpParams]
      rw [evaluate_dec, eval_lvar, hlcA]
      dsimp only
      have hsh : (Shape.One == shape_of (.word w)) = true := rfl
      simp only [hsh, ↓reduceIte]
      rw [hev1]
    · intro hmidV idx
      have hv1 := hvOut1 hmidV
      dsimp only
      if heq : idx = pStart then
        subst heq
        exact res_var_self sOut1.locals p0 (s.locals p0)
      else
        have hne : mkSlot 'v' idx ≠ p0 := fun h => heq (mkSlot_inj h).2
        rw [res_var_ne _ _ _ _ hne, hv1 idx]
        simp [s1, FUPDATE, hne]
    · intro x hx
      dsimp only
      rw [res_var_ne _ _ _ _ (hx pStart)]
      exact hnonVOut1 x hx

/-- State-setup / state-teardown characterization of `bindCtorFields` for `.cases` arms. -/
private theorem evaluate_bindCtorFields {θ : Type} (tags : List String)
    {scrutSlot : String} {si : Nat} (hsiSlot : scrutSlot = mkSlot 'v' si)
    {rvs : List PanVal} :
    ∀ (vStart fieldIdx : Nat)
      {fs : List (String × LcnfVal)} {nms : List String} {bs : List Nat} {pvs : List PanVal},
      CtorFieldsRel fs nms bs pvs →
      ∀ (accVals : List LcnfVal) (accTys : List FoTy) (accSlots : List (String × Shape))
        (inner : PStmt) (s : PanState θ),
        si < vStart →
        StateWF s →
        s.locals scrutSlot = some (.rstruct rvs) →
        (∀ j, j < pvs.length → rvs[fieldIdx + j]? = pvs[j]?) →
        VarSlotsWF vStart accSlots →
        EnvMatches tags accVals accTys accSlots s.locals →
        ∃ sInner : PanState θ,
          let k := nms.length
          let fSlots := mkFreshSlots 'v' vStart k
          sInner.clock = s.clock ∧
          StateWF sInner ∧
          VarSlotsWF (vStart + k) ((fSlots.reverse.map (fun nm => (nm, Shape.One))) ++ accSlots) ∧
          EnvMatches tags ((fs.map Prod.snd).reverse ++ accVals)
            ((bs.reverse.map (fun b => FoTy.one (.scalar b))) ++ accTys)
            ((fSlots.reverse.map (fun nm => (nm, Shape.One))) ++ accSlots) sInner.locals ∧
          (∀ x, (∀ c, x ≠ mkSlot 'v' c) → sInner.locals x = s.locals x) ∧
          ∃ sOut : PanState θ,
            let rMid := evaluate inner sInner
            evaluate (bindCtorFields (.lvar scrutSlot) fieldIdx fSlots inner) s = (rMid.1, sOut) ∧
            sOut.clock = rMid.2.clock ∧
            (StateWF rMid.2 → StateWF sOut) ∧
            ((∀ idx, rMid.2.locals (mkSlot 'v' idx) = sInner.locals (mkSlot 'v' idx)) →
              ∀ idx, sOut.locals (mkSlot 'v' idx) = s.locals (mkSlot 'v' idx)) ∧
            (∀ x, (∀ c, x ≠ mkSlot 'v' c) → sOut.locals x = rMid.2.locals x)
  | vStart, _, _, _, _, _, .nil, accVals, accTys, accSlots, inner, s, _, hwf, _, _, hvswf, henv =>
    ⟨s, rfl, hwf, by simpa [mkFreshSlots] using hvswf, henv, fun _ _ => rfl,
      (evaluate inner s).2, rfl, rfl, id, fun h => h, fun _ _ => rfl⟩
  | vStart, fieldIdx, _, _, _, _, @CtorFieldsRel.cons nm n b fs' nms' bs' pvs' hnb hbLt _ hrelRest,
      accVals, accTys, accSlots, inner, s, hsiLt, hwf, hscrut, hrvsGet, hvswf, henv => by
    let f0 := mkSlot 'v' vStart
    have hget0 : rvs[fieldIdx]? = some (.word (BitVec.ofNat 64 n)) := by
      have h0 := hrvsGet 0 (by simp)
      simpa using h0
    let s1 : PanState θ := { s with locals := FUPDATE s.locals (f0, .word (BitVec.ofNat 64 n)) }
    have hwf1 : StateWF s1 := ⟨hwf.1, hwf.2⟩
    have hscrutNe : scrutSlot ≠ f0 := hsiSlot ▸ mkSlot_ne_of_lt hsiLt
    have hscrut1 : s1.locals scrutSlot = some (.rstruct rvs) := by
      simp [s1, FUPDATE, hscrutNe, hscrut]
    have hvswf1 : VarSlotsWF (vStart + 1) ((f0, Shape.One) :: accSlots) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | htl
      · exact ⟨vStart, by omega, rfl⟩
      · obtain ⟨i, hi, heq⟩ := hvswf p htl
        exact ⟨i, by omega, heq⟩
    have henv1 : EnvMatches tags (.scalar n :: accVals) (FoTy.one (.scalar b) :: accTys)
        ((f0, Shape.One) :: accSlots) s1.locals := by
      refine EnvMatches.cons (pv := .word (BitVec.ofNat 64 n)) (ty := .one (.scalar b))
        (by simp [s1, FUPDATE]) ⟨hnb, hbLt, rfl⟩ ?_
      exact henv.congr (fun p hp => by
        obtain ⟨i, hi, hpEq⟩ := hvswf p hp
        have hne : p.1 ≠ f0 := hpEq ▸ mkSlot_ne_of_lt hi
        simp [s1, FUPDATE, hne])
    have hrvsGet1 : ∀ j, j < pvs'.length → rvs[(fieldIdx + 1) + j]? = pvs'[j]? := by
      intro j hj
      have h1 := hrvsGet (j + 1) (by simp; omega)
      have hidx : fieldIdx + (j + 1) = (fieldIdx + 1) + j := by omega
      rw [← hidx, h1]; rfl
    obtain ⟨sInner, hclkIn, hwfIn, hvswfIn, henvIn, hnonVIn, sOut1, hev1, hclkOut1, hwfOut1, hvOut1, hnonVOut1⟩ :=
      evaluate_bindCtorFields tags hsiSlot (vStart + 1) (fieldIdx + 1) hrelRest
        (.scalar n :: accVals) (FoTy.one (.scalar b) :: accTys) ((f0, Shape.One) :: accSlots)
        inner s1 (by omega) hwf1 hscrut1 hrvsGet1 hvswf1 henv1
    have haddEq : vStart + 1 + nms'.length = vStart + (nms'.length + 1) := by omega
    have hslotsEq :
        ((mkFreshSlots 'v' vStart (nms'.length + 1)).reverse.map (fun nm => (nm, Shape.One))) ++ accSlots =
        ((mkFreshSlots 'v' (vStart + 1) nms'.length).reverse.map (fun nm => (nm, Shape.One))) ++
          ((f0, Shape.One) :: accSlots) := by
      simp [mkFreshSlots, f0, List.reverse_cons, List.map_append, List.append_assoc]
    have hvalsEq :
        (((nm, LcnfVal.scalar n) :: fs').map Prod.snd).reverse ++ accVals =
        (fs'.map Prod.snd).reverse ++ (LcnfVal.scalar n :: accVals) := by
      simp [List.reverse_cons, List.append_assoc]
    have htysEq :
        ((b :: bs').reverse.map (fun x => FoTy.one (.scalar x))) ++ accTys =
        (bs'.reverse.map (fun x => FoTy.one (.scalar x))) ++ (FoTy.one (.scalar b) :: accTys) := by
      simp [List.reverse_cons, List.map_append, List.append_assoc]
    refine ⟨sInner, hclkIn, hwfIn, ?_, ?_, ?_,
      { sOut1 with locals := res_var sOut1.locals (f0, s.locals f0) }, ?_, hclkOut1,
      fun h => let h1 := hwfOut1 h; ⟨h1.1, h1.2⟩, ?_, ?_⟩
    · simp only [List.length_cons]; rw [hslotsEq, ← haddEq]; exact hvswfIn
    · simp only [List.length_cons]; rw [hvalsEq, htysEq, hslotsEq]; exact henvIn
    · intro x hx
      rw [hnonVIn x hx]
      simp [s1, f0, FUPDATE, hx vStart]
    · simp only [List.length_cons, mkFreshSlots, bindCtorFields]
      rw [evaluate_dec, eval_rfield, eval_lvar, hscrut]
      dsimp only
      rw [hget0]
      dsimp only
      have hsh : (Shape.One == shape_of (.word (BitVec.ofNat 64 n))) = true := rfl
      simp only [hsh, ↓reduceIte]
      rw [hev1]
    · intro hmidV idx
      have hv1 := hvOut1 hmidV
      dsimp only
      if heq : idx = vStart then
        subst heq
        exact res_var_self sOut1.locals f0 (s.locals f0)
      else
        have hne : mkSlot 'v' idx ≠ f0 := fun h => heq (mkSlot_inj h).2
        rw [res_var_ne _ _ _ _ hne, hv1 idx]
        simp [s1, FUPDATE, hne]
    · intro x hx
      dsimp only
      rw [res_var_ne _ _ _ _ (hx vStart)]
      exact hnonVOut1 x hx

/-- Unified outcome postcondition for `compileCode_sound`. -/
def BlockPost {θ : Type} (retBound : Nat) (jpSigs : List JpSig) (jpSlots : List CompiledJp)
    (s0 : PanState θ) (out : FoOutcome) (r : PanResult) (s1 : PanState θ) : Prop :=
  match out with
  | .returned v =>
    ∃ n, v = .scalar n ∧ n ≤ retBound ∧ retBound < 2 ^ 64 ∧
      r = .ret (.word (BitVec.ofNat 64 n))
  | .jumped tid argVals =>
    r = .normal ∧
    JpTriggered tid argVals s1.locals jpSigs jpSlots ∧
    (∀ idx, s1.locals (mkSlot 'v' idx) = s0.locals (mkSlot 'v' idx))

private theorem BlockPost.widen_bound {θ : Type} {b1 b2 : Nat} (hle : b1 ≤ b2) (hlt : b2 < 2 ^ 64)
    {jpSigs : List JpSig} {jpSlots : List CompiledJp}
    {s0 : PanState θ} {out : FoOutcome} {r : PanResult} {s1 : PanState θ}
    (h : BlockPost b1 jpSigs jpSlots s0 out r s1) :
    BlockPost b2 jpSigs jpSlots s0 out r s1 := by
  cases out with
  | returned v =>
    obtain ⟨n, rfl, hn, _, hr⟩ := h
    exact ⟨n, rfl, by omega, hlt, hr⟩
  | jumped _ _ => exact h

private theorem mkSlot_h_ne_v (i j : Nat) : mkSlot 'h' i ≠ mkSlot 'v' j :=
  mkSlot_ne_of_kind (by decide) i j

private theorem mkSlot_a_ne_v (i j : Nat) : mkSlot 'a' i ≠ mkSlot 'v' j :=
  mkSlot_ne_of_kind (by decide) i j

private theorem BlockPost.after_dec_v {θ : Type} {retBound nextId : Nat}
    {jpSigs : List JpSig} {jpSlots : List CompiledJp}
    (jpswf : JpStackWF nextId jpSigs jpSlots)
    {s0 sIn smid : PanState θ} {vIdx : Nat} {out : FoOutcome} {r : PanResult}
    (hsInV : ∀ idx, idx ≠ vIdx → sIn.locals (mkSlot 'v' idx) = s0.locals (mkSlot 'v' idx))
    (hpost : BlockPost retBound jpSigs jpSlots sIn out r smid) :
    BlockPost retBound jpSigs jpSlots s0 out r
      { smid with locals := res_var smid.locals (mkSlot 'v' vIdx, s0.locals (mkSlot 'v' vIdx)) } := by
  cases out with
  | returned v => exact hpost
  | jumped tid argVals =>
    obtain ⟨hr, htrig, hvPres⟩ := hpost
    refine ⟨hr, ?_, ?_⟩
    · refine JpTriggered.congr_of_wf jpswf htrig (fun i _ => ⟨?_, ?_⟩)
      · dsimp only; exact res_var_ne _ _ _ _ (mkSlot_h_ne_v i vIdx)
      · dsimp only; exact res_var_ne _ _ _ _ (mkSlot_a_ne_v i vIdx)
    · intro idx
      dsimp only
      if heq : idx = vIdx then
        subst heq
        exact res_var_self smid.locals _ _
      else
        have hne : mkSlot 'v' idx ≠ mkSlot 'v' vIdx := fun h => heq (mkSlot_inj h).2
        rw [res_var_ne _ _ _ _ hne, hvPres idx, hsInV idx heq]

mutual
/-- **Core Structural Compiler Simulation Theorem (`compileCode_sound`)**:
    Every `LcnfCode` block passing `checkFoCode` evaluates in `evalFoBlock` to some `out` and
    executes in `PanSem.evaluate` under `synthLcnfClk c` fuel with `0` `TimeOut`/`Error`,
    consuming at most `synthLcnfClk c` ticks and satisfying `BlockPost`. -/
private theorem compileCode_sound {θ : Type} (tags : List String) :
    ∀ (c : LcnfCode) (env : List LcnfVal) (envTys : List FoTy)
      (varSlots : List (String × Shape)) (jpSigs : List JpSig) (jpSlots : List CompiledJp)
      (nextId retBound : Nat) (s0 : PanState θ),
      checkFoCode tags envTys jpSigs c = some retBound →
      StateWF s0 →
      synthLcnfClk c ≤ s0.clock →
      VarSlotsWF nextId varSlots →
      JpStackWF nextId jpSigs jpSlots →
      EnvMatches tags env envTys varSlots s0.locals →
      JpsIdle jpSlots s0.locals →
      ∃ out r s1,
        evalFoBlock env c = some out ∧
        evaluate (compileCode tags varSlots jpSlots nextId c).1 s0 = (r, s1) ∧
        s0.clock ≤ s1.clock + synthLcnfClk c ∧
        StateWF s1 ∧
        BlockPost retBound jpSigs jpSlots s0 out r s1
  | .return a, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, _, _, _, henv, _ => by
    simp only [checkFoCode] at hchk
    cases ha : inferArgFoTy envTys a with
    | none => simp [ha] at hchk
    | some tyA =>
      rw [ha] at hchk
      cases tyA with
      | ctor _ _ _ => simp at hchk
      | one stA =>
        cases stA with
        | bool | erased => simp at hchk
        | scalar hi =>
          simp only at hchk
          split at hchk <;> simp at hchk
          subst hchk
          obtain ⟨va, pva, heva, hpva, _, henca⟩ := compileArg_sound henv ha
          cases pva with
          | rstruct _ => simp [encodeFoVal] at henca
          | word wa =>
            cases va <;> simp [encodeFoVal, encodeScalar] at henca
            rename_i n
            rcases henca with ⟨hn, hlt, rfl⟩
            refine ⟨.returned (.scalar n), .ret (.word (BitVec.ofNat 64 n)), empty_locals s0,
              by simp [evalFoBlock, heva], ?_, by simp [empty_locals, synthLcnfClk],
              ⟨hwf.1, hwf.2⟩, ⟨n, rfl, hn, hlt, rfl⟩⟩
            simp only [compileCode]
            rw [evaluate_ret, hpva]
            rfl
  | .unreach, _, _, _, _, _, _, _, _, hchk, _, _, _, _, _, _ => by
    simp [checkFoCode] at hchk
  | .jmp id args, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hfind : jpSigs.find? (fun s => s.jpId == id) with
    | none => simp [hfind] at hchk
    | some sig =>
      rw [hfind] at hchk
      dsimp only at hchk
      cases hcond : (args.length == sig.params.length && checkArgsSubTy envTys args sig.params) with
      | false => simp [hcond] at hchk
      | true =>
        simp only [hcond, ↓reduceIte, Option.some.injEq] at hchk
        subst hchk
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        simp only [synthLcnfClk] at hclk
        obtain ⟨cj, argVals, s1, hcjFind, hmap, hev1, hclk1, hwf1, htrig1, hvPres, _⟩ :=
          evaluate_jmp_stack hvswf hjpswf hfind hcond.1 hcond.2 hwf hclk henv hidle
        refine ⟨.jumped id argVals, .normal, s1, by simp [evalFoBlock, hmap], ?_, hclk1, hwf1,
          ⟨rfl, htrig1, hvPres⟩⟩
        simp only [compileCode, hcjFind]
        exact hev1
  | .letValue lv body, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hty : inferLetValFoTy tags envTys lv with
    | none => simp [hty] at hchk
    | some ty =>
      rw [hty] at hchk
      dsimp only at hchk
      simp only [synthLcnfClk] at hclk
      let vSlot := mkSlot 'v' nextId
      have hvswf' : VarSlotsWF (nextId + 1) ((vSlot, ty.toShape) :: varSlots) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | htl
        · exact ⟨nextId, by omega, rfl⟩
        · exact (hvswf.mono (by omega)) p htl
      have hjpswf' : JpStackWF (nextId + 1) jpSigs jpSlots := hjpswf.mono (by omega)
      cases lv with
      | record _ | proj _ _ | app _ _ | stateRead _ _ | stateWrite _ _ _ =>
        simp [inferLetValFoTy] at hty
      | arg a =>
        simp only [inferLetValFoTy] at hty
        obtain ⟨va, pva, heva, hpva, hshEq, henca⟩ := compileArg_sound henv hty
        let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, pva) }
        have henvIn : EnvMatches tags (va :: env) (ty :: envTys) ((vSlot, ty.toShape) :: varSlots) sIn.locals := by
          refine .cons (by simp [sIn, FUPDATE]) henca ?_
          exact henv.congr (fun p hp => by
            obtain ⟨i, hi, hpEq⟩ := hvswf p hp
            have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
            simp [sIn, FUPDATE, hne])
        have hidleIn : JpsIdle jpSlots sIn.locals :=
          JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
            ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
             by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
        obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
          compileCode_sound tags body (va :: env) (ty :: envTys) ((vSlot, ty.toShape) :: varSlots)
            jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
        have hshVal : (ty.toShape == shape_of pva) = true := beq_iff_eq.mpr (encodeFoVal_shape henca).symm
        refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
          by simp [evalFoBlock, evalFoLetVal, heva, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
          hpostB.after_dec_v hjpswf (fun idx hne => by
            have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
            simp [sIn, FUPDATE, hneS])⟩
        simp only [compileCode, hshEq]
        rw [evaluate_dec, hpva]
        dsimp only [sIn] at hevB
        dsimp only
        simp only [hshVal, ↓reduceIte]
        rw [hevB]
      | ctor tag fields =>
        simp only [inferLetValFoTy] at hty
        cases htIdx : lookupTagIdx tags tag with
        | none => simp [htIdx] at hty
        | some tIdx =>
          cases hflds : inferCtorFields envTys fields with
          | none => simp [htIdx, hflds] at hty
          | some p =>
            obtain ⟨nms, bs⟩ := p
            rw [htIdx, hflds] at hty
            dsimp only at hty
            by_cases htIdxLt : tIdx < 2 ^ 64 <;> simp [htIdxLt] at hty
            subst hty
            obtain ⟨fs, pvs, hfs, hpvs, hlenEq, hrel⟩ := inferCtorFields_sound henv fields hflds
            let pv := PanVal.rstruct (.word (BitVec.ofNat 64 tIdx) :: pvs)
            have hencPv : encodeFoVal tags (.ctor tag fs) (.ctor tag nms bs) pv :=
              ⟨rfl, tIdx, htIdx, htIdxLt, rfl, hrel⟩
            have hshCtor : Shape.Comb (List.replicate (fields.length + 1) .One) = (FoTy.ctor tag nms bs).toShape := by
              simp [FoTy.toShape, hlenEq]
            let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, pv) }
            have henvIn : EnvMatches tags (.ctor tag fs :: env) (.ctor tag nms bs :: envTys)
                ((vSlot, (FoTy.ctor tag nms bs).toShape) :: varSlots) sIn.locals := by
              refine .cons (by simp [sIn, FUPDATE]) hencPv ?_
              exact henv.congr (fun q hq => by
                obtain ⟨i, hi, hqEq⟩ := hvswf q hq
                have hne : q.1 ≠ vSlot := hqEq ▸ mkSlot_ne_of_lt hi
                simp [sIn, FUPDATE, hne])
            have hidleIn : JpsIdle jpSlots sIn.locals :=
              JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                 by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
            obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
              compileCode_sound tags body (.ctor tag fs :: env) (.ctor tag nms bs :: envTys)
                ((vSlot, (FoTy.ctor tag nms bs).toShape) :: varSlots)
                jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
            have hshVal : ((FoTy.ctor tag nms bs).toShape == shape_of pv) = true :=
              beq_iff_eq.mpr (encodeFoVal_shape hencPv).symm
            refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
              by simp only [evalFoBlock, evalFoLetVal]; rw [hfs]; simp [hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
              hpostB.after_dec_v hjpswf (fun idx hne => by
                have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                simp [sIn, FUPDATE, hneS])⟩
            simp only [compileCode, htIdx, Option.getD_some, hshCtor]
            rw [evaluate_dec, eval_rstruct, evalList_cons, eval_const, hpvs]
            dsimp only [sIn, pv, Option.map] at hevB ⊢
            rw [hshVal]
            simp only [↓reduceIte]
            rw [hevB]
      | natOp op l rArg =>
        simp only [inferLetValFoTy] at hty
        cases hlTy : inferArgFoTy envTys l with
        | none => simp [hlTy] at hty
        | some tyL =>
          rw [hlTy] at hty
          cases tyL with
          | ctor _ _ _ => simp at hty
          | one stL =>
            cases stL with
            | bool | erased => simp at hty
            | scalar b1 =>
              cases hrTy : inferArgFoTy envTys rArg with
              | none => simp [hrTy] at hty
              | some tyR =>
                rw [hrTy] at hty
                cases tyR with
                | ctor _ _ _ => simp at hty
                | one stR =>
                  cases stR with
                  | bool | erased => simp at hty
                  | scalar b2 =>
                    dsimp only at hty
                    cases hb12 : (decide (b1 < 2 ^ 64) && decide (b2 < 2 ^ 64)) with
        | false => simp [hb12] at hty
        | true =>
          simp only [hb12, ↓reduceIte] at hty
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb12
          obtain ⟨vl, pvl, hevl, hpvl, _, hencl⟩ := compileArg_sound henv hlTy
          obtain ⟨vr, pvr, hevr, hpvr, _, hencr⟩ := compileArg_sound henv hrTy
          cases pvl with
          | rstruct _ => simp [encodeFoVal] at hencl
          | word wl =>
            cases vl <;> simp [encodeFoVal, encodeScalar] at hencl
            rename_i nl
            rcases hencl with ⟨hnl, _, rfl⟩
            cases pvr with
            | rstruct _ => simp [encodeFoVal] at hencr
            | word wr =>
              cases vr <;> simp [encodeFoVal, encodeScalar] at hencr
              rename_i nr
              rcases hencr with ⟨hnr, _, rfl⟩
              have hnl64 : nl < 2 ^ 64 := by omega
              have hnr64 : nr < 2 ^ 64 := by omega
              cases op with
              | div | mod => simp at hty
              | sub =>
                simp only [Option.some.injEq] at hty
                subst hty
                let sZ := { s0 with locals := FUPDATE s0.locals (vSlot, .word 0#64) }
                have hlNe : eval sZ (compileArg varSlots l) = some (.word (BitVec.ofNat 64 nl)) := by
                  cases l with
                  | bvar idx =>
                    simp only [inferArgFoTy] at hlTy
                    obtain ⟨_, slot, _, _, hslotsGet, hlc, _⟩ := henv.lookup idx hlTy
                    obtain ⟨i, hi, hslotEq⟩ := hvswf.lookup hslotsGet
                    have hne : slot ≠ vSlot := hslotEq ▸ mkSlot_ne_of_lt hi
                    simpa [compileArg, hslotsGet, sZ, FUPDATE, hne, hlc] using hpvl
                  | _ => exact hpvl
                have hrNe : eval sZ (compileArg varSlots rArg) = some (.word (BitVec.ofNat 64 nr)) := by
                  cases rArg with
                  | bvar idx =>
                    simp only [inferArgFoTy] at hrTy
                    obtain ⟨_, slot, _, _, hslotsGet, hlc, _⟩ := henv.lookup idx hrTy
                    obtain ⟨i, hi, hslotEq⟩ := hvswf.lookup hslotsGet
                    have hne : slot ≠ vSlot := hslotEq ▸ mkSlot_ne_of_lt hi
                    simpa [compileArg, hslotsGet, sZ, FUPDATE, hne, hlc] using hpvr
                  | _ => exact hpvr
                let satSub := PStmt.ite (.cmp .Lower (compileArg varSlots l) (compileArg varSlots rArg))
                  .skip (.lassign vSlot (.binop .Sub [compileArg varSlots l, compileArg varSlots rArg]))
                have hSat : ∃ sSat : PanState θ,
                    evaluate satSub sZ = (.normal, sSat) ∧
                    sSat.clock = s0.clock ∧
                    StateWF sSat ∧
                    sSat.locals vSlot = some (.word (BitVec.ofNat 64 (nl - nr))) ∧
                    (∀ x, x ≠ vSlot → sSat.locals x = s0.locals x) := by
                  by_cases hltSub : nl < nr
                  · have hsub0 : nl - nr = 0 := by omega
                    have hcmp : word_cmp .Lower (BitVec.ofNat 64 nl) (BitVec.ofNat 64 nr) = true := by
                      simp [word_cmp, bv64_ult_ofNat hnl64 hnr64, hltSub]
                    refine ⟨sZ, ?_, rfl, ⟨hwf.1, hwf.2⟩, by simp [sZ, FUPDATE, hsub0],
                      fun x hne => by simp [sZ, FUPDATE, hne]⟩
                    simp only [satSub]
                    rw [evaluate_ite, eval_cmp, hlNe, hrNe]
                    dsimp only
                    rw [hcmp]
                    have ho : ((1#64 : Word) != 0#64) = true := by decide
                    simp only [ho, ↓reduceIte]
                    exact evaluate_skip sZ
                  · have hleSub : nr ≤ nl := by omega
                    have hcmp : word_cmp .Lower (BitVec.ofNat 64 nl) (BitVec.ofNat 64 nr) = false := by
                      simp [word_cmp, bv64_ult_ofNat hnl64 hnr64, hltSub]
                    have hvalidZ : is_valid_value sZ .Local vSlot (.word (BitVec.ofNat 64 nl - BitVec.ofNat 64 nr)) = true := by
                      simp [is_valid_value, lookup_kvar, sZ, FUPDATE]
                    let sSet := set_kvar .Local vSlot (.word (BitVec.ofNat 64 nl - BitVec.ofNat 64 nr)) sZ
                    refine ⟨sSet, ?_, rfl, ⟨hwf.1, hwf.2⟩,
                      by simp [sSet, set_kvar, set_var, FUPDATE, bv64_sub_ofNat hnl64 hleSub],
                      fun x hne => by simp [sSet, set_kvar, set_var, sZ, FUPDATE, hne]⟩
                    simp only [satSub]
                    rw [evaluate_ite, eval_cmp, hlNe, hrNe]
                    dsimp only
                    rw [hcmp]
                    have hz : ((0#64 : Word) != 0#64) = false := by decide
                    simp only [Bool.false_eq_true, ↓reduceIte, hz]
                    rw [evaluate_assign, eval_binop2, hlNe, hrNe]
                    dsimp only [word_op, Option.map]
                    rw [hvalidZ]
                    rfl
                obtain ⟨sSat, hevSat, hclkSat, hwfSat, hvSat, hotherSat⟩ := hSat
                have henvSat : EnvMatches tags (.scalar (nl - nr) :: env)
                    (FoTy.one (.scalar b1) :: envTys) ((vSlot, .One) :: varSlots) sSat.locals := by
                  refine .cons (ty := .one (.scalar b1)) hvSat ⟨by omega, hb12.1, rfl⟩ ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    exact hotherSat p.1 (hpEq ▸ mkSlot_ne_of_lt hi))
                have hidleSat : JpsIdle jpSlots sSat.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨hotherSat _ (mkSlot_h_ne_v i nextId),
                     hotherSat _ (mkSlot_a_ne_v i nextId)⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sound tags body (.scalar (nl - nr) :: env)
                    (FoTy.one (.scalar b1) :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sSat hchk hwfSat
                    (by rw [hclkSat]; exact hclk) hvswf' hjpswf' henvSat hidleSat
                rw [hclkSat] at hclkB
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne =>
                    hotherSat _ (fun h => hne (mkSlot_inj h).2))⟩
                simp only [compileCode]
                rw [evaluate_dec, eval_const]
                dsimp only
                have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [evaluate_seq]
                dsimp only [sZ] at hevSat
                rw [hevSat]
                dsimp only
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [hevB]
              | add =>
                dsimp only at hty
                by_cases hbAdd : b1 + b2 < 2 ^ 64 <;> simp [hbAdd] at hty
                subst hty
                have haddLt : nl + nr < 2 ^ 64 := by omega
                let wOut := BitVec.ofNat 64 (nl + nr)
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.scalar (nl + nr) :: env)
                    (FoTy.one (.scalar (b1 + b2)) :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one (.scalar (b1 + b2)))
                    (by simp [sIn, FUPDATE]) ⟨by omega, hbAdd, rfl⟩ ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sound tags body (.scalar (nl + nr) :: env)
                    (FoTy.one (.scalar (b1 + b2)) :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                have hwAdd : BitVec.ofNat 64 nl + (BitVec.ofNat 64 nr + 0#64) = wOut := by
                  rw [BitVec.add_zero, bv64_add_ofNat haddLt]
                rw [evaluate_dec, eval_binop2, hpvl, hpvr]
                dsimp only [sIn, wOut, word_op, List.foldr, Option.map] at hevB hwAdd ⊢
                rw [hwAdd]
                have hsh : (Shape.One == shape_of (.word (BitVec.ofNat 64 (nl + nr)))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
              | mul =>
                dsimp only at hty
                by_cases hbMul : b1 * b2 < 2 ^ 64 <;> simp [hbMul] at hty
                subst hty
                have hmulLe : nl * nr ≤ b1 * b2 := Nat.mul_le_mul hnl hnr
                have hmulLt : nl * nr < 2 ^ 64 := by omega
                let wOut := BitVec.ofNat 64 (nl * nr)
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.scalar (nl * nr) :: env)
                    (FoTy.one (.scalar (b1 * b2)) :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one (.scalar (b1 * b2)))
                    (by simp [sIn, FUPDATE]) ⟨hmulLe, hbMul, rfl⟩ ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sound tags body (.scalar (nl * nr) :: env)
                    (FoTy.one (.scalar (b1 * b2)) :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                rw [evaluate_dec, eval_panop2, hpvl, hpvr]
                dsimp only [sIn, wOut, pan_op, Option.map] at hevB ⊢
                rw [bv64_mul_ofNat hnl64 hnr64 hmulLt]
                have hsh : (Shape.One == shape_of (.word (BitVec.ofNat 64 (nl * nr)))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
              | beq =>
                simp only [Option.some.injEq] at hty
                subst hty
                let bOut := (nl == nr)
                let wOut : Word := if bOut then 1#64 else 0#64
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one .bool)
                    (by simp [sIn, FUPDATE]) rfl ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sound tags body (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, bOut, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                rw [evaluate_dec, eval_cmp, hpvl, hpvr]
                dsimp only [sIn, wOut, bOut, word_cmp] at hevB ⊢
                simp only [bv64_beq_ofNat hnl64 hnr64]
                have hsh : (Shape.One == shape_of (.word (if (nl == nr) = true then 1#64 else 0#64))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
              | ble =>
                simp only [Option.some.injEq] at hty
                subst hty
                let bOut : Bool := (nl <= nr)
                let wOut : Word := if bOut then 1#64 else 0#64
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one .bool)
                    (by simp [sIn, FUPDATE]) rfl ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sound tags body (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                have hbleEq : word_cmp .NotLower (BitVec.ofNat 64 nr) (BitVec.ofNat 64 nl) = bOut := by
                  simp only [word_cmp, bv64_ult_ofNat hnr64 hnl64, bOut]
                  by_cases h1 : nr < nl <;> by_cases h2 : nl ≤ nr <;> simp [h1, h2] <;> omega
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, bOut, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                rw [evaluate_dec, eval_cmp, hpvr, hpvl]
                dsimp only [sIn, wOut] at hevB ⊢
                simp only [hbleEq]
                have hsh : (Shape.One == shape_of (.word (if bOut = true then 1#64 else 0#64))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
  | .ifBool cond t fls, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hcTy : inferArgFoTy envTys cond with
    | none => simp [hcTy] at hchk
    | some tyC =>
      rw [hcTy] at hchk
      cases tyC with
      | ctor _ _ _ => simp at hchk
      | one stC =>
        cases stC <;> simp at hchk
        cases ht : checkFoCode tags envTys jpSigs t <;>
          cases hf : checkFoCode tags envTys jpSigs fls <;> simp [ht, hf] at hchk
        rename_i bt bf
        subst hchk
        have hbtLt := (checkFoCode_bound_lt tags t envTys jpSigs bt ht).1
        have hbfLt := (checkFoCode_bound_lt tags fls envTys jpSigs bf hf).1
        have hmaxLt : max bt bf < 2 ^ 64 := by omega
        obtain ⟨vc, pvc, hevc, hpvc, _, hencc⟩ := compileArg_sound henv hcTy
        cases pvc with
        | rstruct _ => simp [encodeFoVal] at hencc
        | word wc =>
          cases vc <;> simp [encodeFoVal, encodeScalar] at hencc
          rename_i bv
          subst hencc
          simp only [synthLcnfClk] at hclk
          cases bv with
          | true =>
            obtain ⟨out, r, s1, hfoT, hevT, hclkT, hwf1, hpostT⟩ :=
              compileCode_sound tags t env envTys varSlots jpSigs jpSlots nextId bt s0
                ht hwf (by omega) hvswf hjpswf henv hidle
            refine ⟨out, r, s1, by simp [evalFoBlock, hevc, hfoT], ?_,
              by simp only [synthLcnfClk]; omega, hwf1,
              hpostT.widen_bound (by omega) hmaxLt⟩
            simp only [compileCode]
            rw [evaluate_ite, hpvc]
            dsimp only
            have ho : ((1#64 : Word) != 0#64) = true := by decide
            simp only [ho, ↓reduceIte]
            exact hevT
          | false =>
            let id1 := (compileCode tags varSlots jpSlots nextId t).2
            have hid1 : nextId ≤ id1 := (compileCode_clk_and_mono tags t varSlots jpSlots nextId).2
            obtain ⟨out, r, s1, hfoF, hevF, hclkF, hwf1, hpostF⟩ :=
              compileCode_sound tags fls env envTys varSlots jpSigs jpSlots id1 bf s0
                hf hwf (by omega) (hvswf.mono hid1) (hjpswf.mono hid1) henv hidle
            refine ⟨out, r, s1, by simp [evalFoBlock, hevc, hfoF], ?_,
              by simp only [synthLcnfClk]; omega, hwf1,
              hpostF.widen_bound (by omega) hmaxLt⟩
            simp only [compileCode]
            rw [evaluate_ite, hpvc]
            dsimp only
            have hz : ((0#64 : Word) != 0#64) = false := by decide
            simp only [hz, Bool.false_eq_true, ↓reduceIte]
            exact hevF
  | .cases scrut arms, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases scrut with
    | lit _ | boolLit _ | erased | stateTok _ => simp at hchk
    | bvar idx =>
      cases hsTy : inferArgFoTy envTys (.bvar idx) with
      | none => simp [hsTy] at hchk
      | some tyS =>
        rw [hsTy] at hchk
        cases tyS with
        | one _ => simp at hchk
        | ctor cTag cNames cBounds =>
          dsimp only at hchk
          cases hcond : (checkArmTagsValid tags arms && foPureArms arms) with
          | false => simp [hcond] at hchk
          | true =>
            simp only [hcond, ↓reduceIte] at hchk
            simp only [Bool.and_eq_true] at hcond
            rw [checkFoArm_eq_find] at hchk
            cases hfind : arms.find? (fun a => a.1 == cTag) with
            | none => simp [hfind] at hchk
            | some arm =>
              rw [hfind] at hchk
              obtain ⟨mTag, armNames, mBody⟩ := arm
              dsimp only at hchk
              cases hnames : (armNames == cNames) with
              | false => simp [hnames] at hchk
              | true =>
                simp only [hnames, ↓reduceIte] at hchk
                have hnamesEq : armNames = cNames := beq_iff_eq.mp hnames
                subst armNames
                simp only [inferArgFoTy] at hsTy
                obtain ⟨vScrut, scrutSlot, pvScrut, henvGet, hslotsGet, hlcScrut, hencScrut⟩ :=
                  henv.lookup idx hsTy
                obtain ⟨si, hsiLt, hsiSlot⟩ := hvswf.lookup hslotsGet
                cases vScrut <;> try cases hencScrut
                rename_i rTag fs
                cases pvScrut with
                | word _ => cases hencScrut
                | rstruct rvs =>
                  cases rvs with
                  | nil => cases hencScrut
                  | cons rv0 pvs =>
                    cases rv0 with
                    | rstruct _ => cases hencScrut
                    | word wTag =>
                      obtain ⟨htagEq, cIdx, hcIdx, hcIdxLt, rfl, hrel⟩ := hencScrut
                      subst rTag
                      have heScrut : compileArg varSlots (.bvar idx) = .lvar scrutSlot := by
                        simp [compileArg, hslotsGet]
                      have hspEq : splitValues fs cNames = some (fs.map Prod.snd) :=
                        ctorFieldsRel_splitValues hrel
                      simp only [synthLcnfClk] at hclk
                      obtain ⟨out, r, s1, hfoM, hevArms, hclkArms, hwf1, hpostArms⟩ :=
                        compileArms_sound tags arms scrutSlot si hsiSlot cTag cIdx cNames cBounds
                          fs pvs mTag mBody env envTys varSlots jpSigs jpSlots nextId retBound s0
                          hsiLt hcIdx hcIdxLt hrel hcond.1 hfind hchk hwf hclk hvswf hjpswf henv hidle hlcScrut
                      refine ⟨out, r, s1, ?_, ?_, hclkArms, hwf1, hpostArms⟩
                      · simp [evalFoBlock, evalLcnfArgVal, henvGet, evalFoArm_eq_find, hfind, hspEq, hfoM]
                      · simp only [compileCode, heScrut]
                        exact hevArms
  | .jpDecl jpId numParams jpBody body, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hany : jpSigs.any (fun s => s.jpId == jpId) with
    | true => simp [hany] at hchk
    | false =>
      simp only [hany, Bool.false_eq_true, ↓reduceIte] at hchk
      cases hinf : inferJpParams tags jpId numParams envTys body with
      | none => simp [hinf] at hchk
      | some optParams =>
        rw [hinf] at hchk
        dsimp only at hchk
        let paramTys := optParams.getD (List.replicate numParams (.scalar 0))
        cases hpcond : (paramTys.length == numParams && paramTys.all FoScalarTy.wf) with
        | false => simp [paramTys, hpcond] at hchk
        | true =>
          change (if (paramTys.length == numParams && paramTys.all FoScalarTy.wf) = true then _ else none) = some retBound at hchk
          simp only [hpcond, ↓reduceIte] at hchk
          simp only [Bool.and_eq_true, beq_iff_eq] at hpcond
          have hboth : ∃ bBody bJp,
              checkFoCode tags envTys (⟨jpId, paramTys⟩ :: jpSigs) body = some bBody ∧
              checkFoCode tags (paramTys.map FoTy.one ++ envTys) jpSigs jpBody = some bJp ∧
              max bBody bJp = retBound := by
            dsimp only [paramTys]
            cases h1 : checkFoCode tags envTys (⟨jpId, optParams.getD (List.replicate numParams (.scalar 0))⟩ :: jpSigs) body with
            | none => rw [h1] at hchk; cases hchk
            | some bBody =>
              cases h2 : checkFoCode tags ((optParams.getD (List.replicate numParams (.scalar 0))).map FoTy.one ++ envTys) jpSigs jpBody with
              | none => rw [h1, h2] at hchk; cases hchk
              | some bJp =>
                rw [h1, h2] at hchk
                exact ⟨bBody, bJp, rfl, rfl, Option.some.inj hchk⟩
          obtain ⟨bBody, bJp, hb1, hb2, hretEq⟩ := hboth
          subst hretEq
          have hbBodyLt := (checkFoCode_bound_lt tags body _ _ bBody hb1).1
          have hbJpLt := (checkFoCode_bound_lt tags jpBody _ _ bJp hb2).1
          have hmaxLt : max bBody bJp < 2 ^ 64 := by omega
          simp only [synthLcnfClk] at hclk
          let hitSlot := mkSlot 'h' nextId
          let argSlots := mkFreshSlots 'a' (nextId + 1) numParams
          let nextId1 := nextId + 1 + numParams
          let cj : CompiledJp := ⟨jpId, numParams, hitSlot, argSlots⟩
          have hnotMem : jpId ∉ jpSigs.map JpSig.jpId := by
            intro hm
            rcases List.mem_map.mp hm with ⟨s, hs, rfl⟩
            have : jpSigs.any (fun x => x.jpId == s.jpId) = true :=
              List.any_eq_true.mpr ⟨s, hs, beq_self_eq_true _⟩
            rw [hany] at this; cases this
          have hjpswfBody : JpStackWF nextId1 (⟨jpId, paramTys⟩ :: jpSigs) (cj :: jpSlots) := by
            have hcjEq : cj = ⟨jpId, paramTys.length, mkSlot 'h' nextId, mkFreshSlots 'a' (nextId + 1) paramTys.length⟩ := by
              simp [cj, hitSlot, argSlots, hpcond.1]
            rw [hcjEq]
            exact .cons hjpswf hnotMem (by simp [nextId1, hpcond.1])
          let sHit0 : PanState θ := { s0 with locals := FUPDATE s0.locals (hitSlot, .word 0#64) }
          let cBody := (compileCode tags varSlots (cj :: jpSlots) nextId1 body).1
          let nextId2 := (compileCode tags varSlots (cj :: jpSlots) nextId1 body).2
          have hmonoBody : nextId1 ≤ nextId2 :=
            (compileCode_clk_and_mono tags body varSlots (cj :: jpSlots) nextId1).2
          let pSlots := mkFreshSlots 'v' nextId2 numParams
          let jpVarSlots := (pSlots.map (fun s => (s, Shape.One))) ++ varSlots
          let cJpBody := (compileCode tags jpVarSlots jpSlots (nextId2 + numParams) jpBody).1
          let tailIf := PStmt.ite (.lvar hitSlot) (bindJpParams pSlots argSlots cJpBody) .skip
          obtain ⟨sInner, hclkIn0, hwfInFn, hbndArgsIn, hpresArgsIn, sOutWrap, hevWrap, hclkWrap, hwfWrapFn, hpresArgsOut⟩ :=
            evaluate_wrapDecZeros (nextId + 1) numParams (.seq cBody tailIf) sHit0
          have hclkIn : sInner.clock = s0.clock := hclkIn0
          have hwfIn : StateWF sInner := hwfInFn ⟨hwf.1, hwf.2⟩
          have hsInnerNonFrame : ∀ x, x ≠ hitSlot →
              (∀ j, nextId + 1 ≤ j → j < nextId + 1 + numParams → x ≠ mkSlot 'a' j) →
              sInner.locals x = s0.locals x := by
            intro x hneH hneA
            rw [hpresArgsIn x hneA]
            simp [sHit0, FUPDATE, hneH]
          have henvIn : EnvMatches tags env envTys varSlots sInner.locals :=
            henv.congr (fun p hp => by
              obtain ⟨i, _, hpEq⟩ := hvswf p hp
              exact hsInnerNonFrame p.1
                (hpEq ▸ mkSlot_ne_of_kind (by decide) i nextId)
                (fun j _ _ => hpEq ▸ mkSlot_ne_of_kind (by decide) i j))
          have hidleIn : JpsIdle (cj :: jpSlots) sInner.locals := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | htl
            · refine ⟨?_, fun a ha => ⟨0#64, hbndArgsIn a ha⟩⟩
              rw [hpresArgsIn hitSlot (fun j _ _ => mkSlot_ne_of_kind (by decide) nextId j)]
              simp [sHit0, FUPDATE]
            · refine JpsIdle.congr_of_wf hjpswf hidle (fun i hi => ⟨?_, ?_⟩) c htl
              · exact hsInnerNonFrame _ (mkSlot_ne_of_lt hi) (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)
              · exact hsInnerNonFrame _ (mkSlot_ne_of_kind (by decide) i nextId) (fun j hj1 _ => mkSlot_ne_of_lt (by omega))
          obtain ⟨outB, rB, sMidB, hfoB, hevB, hclkB, hwfMidB, hpostB⟩ :=
            compileCode_sound tags body env envTys varSlots (⟨jpId, paramTys⟩ :: jpSigs) (cj :: jpSlots)
              nextId1 bBody sInner hb1 hwfIn (by rw [hclkIn]; omega)
              (hvswf.mono (by omega)) hjpswfBody henvIn hidleIn
          rw [hclkIn] at hclkB
          -- Case-analyze `outB` (`returned` vs `jumped`)
          cases outB with
          | returned rv =>
            obtain ⟨n, rfl, hnLe, _, hrB⟩ := hpostB
            subst hrB
            have hevSeq : evaluate (.seq cBody tailIf) sInner = (.ret (.word (BitVec.ofNat 64 n)), sMidB) := by
              rw [evaluate_seq, hevB]; rfl
            let sFinal := { sOutWrap with locals := res_var sOutWrap.locals (hitSlot, s0.locals hitSlot) }
            refine ⟨.returned (.scalar n), .ret (.word (BitVec.ofNat 64 n)), sFinal,
              by simp [evalFoBlock, hfoB], ?_, ?_, ?_, ⟨n, rfl, by omega, hmaxLt, rfl⟩⟩
            · simp only [compileCode]
              rw [evaluate_dec, eval_const]
              dsimp only
              have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
              simp only [hsh, ↓reduceIte]
              dsimp only [argSlots, sHit0, hitSlot] at hevWrap
              rw [hevWrap, hevSeq]
            · simp only [sFinal, synthLcnfClk]; rw [hclkWrap, hevSeq]; dsimp only; omega
            · have hw1 := hwfWrapFn (by rw [hevSeq]; exact hwfMidB)
              exact ⟨hw1.1, hw1.2⟩
          | jumped tid argVals =>
            obtain ⟨hrB, htrigB, hvPresB⟩ := hpostB
            subst hrB
            cases htrigB with
            | here hidEq hhitMid hrelMid hidleMid =>
              dsimp only at hidEq
              subst hidEq
              have hlenArgs : argVals.length = numParams :=
                hrelMid.length_eq.trans hpcond.1
              have hrelMid' : ScalarSlotsRel argVals paramTys (mkFreshSlots 'a' (nextId + 1) paramTys.length) sMidB.locals := by
                simpa [cj, argSlots, hpcond.1] using hrelMid
              obtain ⟨sJpIn, hclkJpIn, hwfJpIn, hpresJpIn, hliftJpEnv, sOutBind, hevBind, hclkBind, hwfBindFn, hvBindOut, hnonVBindOut⟩ :=
                evaluate_bindJpParams_raw tags nextId2 (nextId + 1) argVals paramTys cJpBody sMidB hwfMidB hrelMid'
              have henvMid : EnvMatches tags env envTys varSlots sJpIn.locals :=
                henv.congr (fun p hp => by
                  obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                  have h1 : sJpIn.locals p.1 = sMidB.locals p.1 :=
                    hpresJpIn p.1 (fun j hj1 _ => hpEq ▸ mkSlot_ne_of_lt (by omega))
                  have h2 : sMidB.locals p.1 = sInner.locals p.1 := hpEq ▸ hvPresB i
                  have h3 : sInner.locals p.1 = s0.locals p.1 :=
                    hsInnerNonFrame p.1
                      (hpEq ▸ mkSlot_ne_of_kind (by decide) i nextId)
                      (fun j _ _ => hpEq ▸ mkSlot_ne_of_kind (by decide) i j)
                  exact h1.trans (h2.trans h3))
              have henvJp : EnvMatches tags (argVals ++ env) (paramTys.map FoTy.one ++ envTys)
                  jpVarSlots sJpIn.locals := by
                have hpEq : pSlots = mkFreshSlots 'v' nextId2 paramTys.length := by simp [pSlots, hpcond.1]
                simpa [jpVarSlots, hpEq] using hliftJpEnv env envTys varSlots henvMid
              have hvswfJp : VarSlotsWF (nextId2 + numParams) jpVarSlots := by
                intro p hp
                rcases List.mem_append.mp hp with hp1 | hp2
                · rcases List.mem_map.mp hp1 with ⟨nm, hnm, rfl⟩
                  obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots hnm
                  exact ⟨j, hj2, rfl⟩
                · exact (hvswf.mono (by omega)) p hp2
              have hidleJp : JpsIdle jpSlots sJpIn.locals :=
                JpsIdle.congr_of_wf hjpswf hidleMid (fun i _ =>
                  ⟨hpresJpIn _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j),
                   hpresJpIn _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)⟩)
              obtain ⟨outJ, rJ, sMidJ, hfoJ, hevJ, hclkJ, hwfMidJ, hpostJ⟩ :=
                compileCode_sound tags jpBody (argVals ++ env) (paramTys.map FoTy.one ++ envTys)
                  jpVarSlots jpSigs jpSlots (nextId2 + numParams) bJp sJpIn
                  hb2 hwfJpIn (by rw [hclkJpIn]; omega) hvswfJp (hjpswf.mono (by omega)) henvJp hidleJp
              rw [hclkJpIn] at hclkJ
              have hevBind' : evaluate (bindJpParams pSlots argSlots cJpBody) sMidB = (rJ, sOutBind) := by
                have hpEq : pSlots = mkFreshSlots 'v' nextId2 paramTys.length := by simp [pSlots, hpcond.1]
                have haEq : argSlots = mkFreshSlots 'a' (nextId + 1) paramTys.length := by simp [argSlots, hpcond.1]
                rw [hpEq, haEq, hevBind, hevJ]
              have hevSeq : evaluate (.seq cBody tailIf) sInner = (rJ, sOutBind) := by
                rw [evaluate_seq, hevB]
                dsimp only [tailIf]
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [evaluate_ite, eval_lvar]
                have hh1 : sMidB.locals hitSlot = some (.word 1#64) := hhitMid
                rw [hh1]
                dsimp only
                have hnz : ((1#64 : Word) != 0#64) = true := by decide
                simp only [hnz, ↓reduceIte]
                exact hevBind'
              let sFinal := { sOutWrap with locals := res_var sOutWrap.locals (hitSlot, s0.locals hitSlot) }
              refine ⟨outJ, rJ, sFinal,
                by simp [evalFoBlock, hfoB, hlenArgs, hfoJ], ?_, ?_, ?_, ?_⟩
              · simp only [compileCode]
                rw [evaluate_dec, eval_const]
                dsimp only
                have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
                simp only [hsh, ↓reduceIte]
                dsimp only [argSlots, sHit0, hitSlot] at hevWrap
                rw [hevWrap, hevSeq]
              · simp only [sFinal, synthLcnfClk]
                rw [hclkWrap, hevSeq]; dsimp only
                rw [hclkBind, hevJ]; dsimp only at hclkJ ⊢
                omega
              · have hw1 := hwfWrapFn (by rw [hevSeq]; exact hwfBindFn (by rw [hevJ]; exact hwfMidJ))
                exact ⟨hw1.1, hw1.2⟩
              · cases outJ with
                | returned rv =>
                  obtain ⟨n, rfl, hnLe, _, hrJ⟩ := hpostJ
                  exact ⟨n, rfl, by omega, hmaxLt, hrJ⟩
                | jumped tid2 argVals2 =>
                  obtain ⟨hrJ, htrigJ, hvPresJ⟩ := hpostJ
                  refine ⟨hrJ, ?_, ?_⟩
                  · refine JpTriggered.congr_of_wf hjpswf htrigJ (fun i hi => ⟨?_, ?_⟩)
                    · simp only [sFinal]
                      rw [res_var_ne _ _ _ _ (mkSlot_ne_of_lt hi)]
                      rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)]
                      rw [hevSeq]; dsimp only
                      rw [hnonVBindOut _ (fun c => mkSlot_ne_of_kind (by decide) i c)]
                      rw [hevJ]
                    · simp only [sFinal]
                      rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) i nextId)]
                      rw [hpresArgsOut _ (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
                      rw [hevSeq]; dsimp only
                      rw [hnonVBindOut _ (fun c => mkSlot_ne_of_kind (by decide) i c)]
                      rw [hevJ]
                  · intro idx
                    simp only [sFinal]
                    rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) idx nextId)]
                    rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)]
                    rw [hevSeq]; dsimp only
                    have hvMid : sOutBind.locals (mkSlot 'v' idx) = sMidB.locals (mkSlot 'v' idx) :=
                      hvBindOut (by rw [hevJ]; exact hvPresJ) idx
                    rw [hvMid, hvPresB idx]
                    exact hsInnerNonFrame _ (mkSlot_ne_of_kind (by decide) idx nextId)
                      (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)
            | there hneId hhitMid _ htrigOuter =>
              dsimp only at hneId
              have htidFalse : (tid == jpId) = false :=
                beq_eq_false_iff_ne.mpr (fun h => hneId h.symm)
              have hevSeq : evaluate (.seq cBody tailIf) sInner = (.normal, sMidB) := by
                rw [evaluate_seq, hevB]
                dsimp only [tailIf]
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [evaluate_ite, eval_lvar]
                have hh0 : sMidB.locals hitSlot = some (.word 0#64) := hhitMid
                rw [hh0]
                dsimp only
                have hz : ((0#64 : Word) != 0#64) = false := by decide
                simp only [hz, Bool.false_eq_true, ↓reduceIte]
                exact evaluate_skip sMidB
              let sFinal := { sOutWrap with locals := res_var sOutWrap.locals (hitSlot, s0.locals hitSlot) }
              refine ⟨.jumped tid argVals, .normal, sFinal,
                by simp [evalFoBlock, hfoB, htidFalse], ?_, ?_, ?_, ⟨rfl, ?_, ?_⟩⟩
              · simp only [compileCode]
                rw [evaluate_dec, eval_const]
                dsimp only
                have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
                simp only [hsh, ↓reduceIte]
                dsimp only [argSlots, sHit0, hitSlot] at hevWrap
                rw [hevWrap, hevSeq]
              · simp only [sFinal, synthLcnfClk]
                rw [hclkWrap, hevSeq]; dsimp only
                omega
              · have hw1 := hwfWrapFn (by rw [hevSeq]; exact hwfMidB)
                exact ⟨hw1.1, hw1.2⟩
              · refine JpTriggered.congr_of_wf hjpswf htrigOuter (fun i hi => ⟨?_, ?_⟩)
                · simp only [sFinal]
                  rw [res_var_ne _ _ _ _ (mkSlot_ne_of_lt hi)]
                  rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)]
                  rw [hevSeq]
                · simp only [sFinal]
                  rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) i nextId)]
                  rw [hpresArgsOut _ (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
                  rw [hevSeq]
              · intro idx
                simp only [sFinal]
                rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) idx nextId)]
                rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)]
                rw [hevSeq]; dsimp only
                rw [hvPresB idx]
                exact hsInnerNonFrame _ (mkSlot_ne_of_kind (by decide) idx nextId)
                  (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)
termination_by structural c => c

private theorem compileArms_sound {θ : Type} (tags : List String) :
    ∀ (arms : List (String × List String × LcnfCode))
      (scrutSlot : String) (si : Nat) (_ : scrutSlot = mkSlot 'v' si)
      (cTag : String) (cIdx : Nat) (cNames : List String) (cBounds : List Nat)
      (fs : List (String × LcnfVal)) (pvs : List PanVal)
      (mTag : String) (mBody : LcnfCode)
      (env : List LcnfVal) (envTys : List FoTy) (varSlots : List (String × Shape))
      (jpSigs : List JpSig) (jpSlots : List CompiledJp) (nextId retBound : Nat) (s0 : PanState θ),
      si < nextId →
      lookupTagIdx tags cTag = some cIdx →
      cIdx < 2 ^ 64 →
      CtorFieldsRel fs cNames cBounds pvs →
      checkArmTagsValid tags arms = true →
      arms.find? (fun a => a.1 == cTag) = some (mTag, cNames, mBody) →
      checkFoCode tags ((cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys) jpSigs mBody = some retBound →
      StateWF s0 →
      synthArmsClk arms ≤ s0.clock →
      VarSlotsWF nextId varSlots →
      JpStackWF nextId jpSigs jpSlots →
      EnvMatches tags env envTys varSlots s0.locals →
      JpsIdle jpSlots s0.locals →
      s0.locals scrutSlot = some (.rstruct (.word (BitVec.ofNat 64 cIdx) :: pvs)) →
      ∃ out r s1,
        evalFoBlock ((fs.map Prod.snd).reverse ++ env) mBody = some out ∧
        evaluate (compileArms tags (.lvar scrutSlot) varSlots jpSlots nextId arms).1 s0 = (r, s1) ∧
        s0.clock ≤ s1.clock + synthArmsClk arms ∧
        StateWF s1 ∧
        BlockPost retBound jpSigs jpSlots s0 out r s1
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfind, _, _, _, _, _, _, _, _ => by
    simp at hfind
  | (armTag, fieldNames, armBody) :: rest, scrutSlot, si, hsiSlot, cTag, cIdx, cNames, cBounds,
      fs, pvs, mTag, mBody, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hsiLt, hcIdx, hcIdxLt, hrel, htagsValid, hfind, hchkM, hwf, hclk, hvswf, hjpswf, henv, hidle, hscrut => by
    simp only [checkArmTagsValid, Bool.and_eq_true] at htagsValid
    cases htIdx : lookupTagIdx tags armTag with
    | none => simp [htIdx] at htagsValid
    | some tIdx =>
      rw [htIdx] at htagsValid
      simp only [decide_eq_true_eq] at htagsValid
      simp only [List.find?] at hfind
      simp only [synthArmsClk] at hclk
      cases heqTag : (armTag == cTag) with
      | true =>
        rw [heqTag] at hfind
        simp only [Option.some.injEq, Prod.mk.injEq] at hfind
        rcases hfind with ⟨hmTagEq, hfnEq, hmEq⟩
        subst mTag
        subst fieldNames
        subst mBody
        have htagEq : armTag = cTag := beq_iff_eq.mp heqTag
        subst armTag
        have htEq : tIdx = cIdx := by
          rw [hcIdx] at htIdx; exact Option.some.inj htIdx.symm
        subst tIdx
        let k := cNames.length
        let fSlots := mkFreshSlots 'v' nextId k
        let armVarSlots := (fSlots.reverse.map (fun s => (s, Shape.One))) ++ varSlots
        let cArm := (compileCode tags armVarSlots jpSlots (nextId + k) armBody).1
        obtain ⟨sInner, hclkIn, hwfIn, hvswfIn, henvIn, hnonVIn, sOut, hevBind, hclkOut, hwfOutFn, hvOut, hnonVOut⟩ :=
          evaluate_bindCtorFields tags hsiSlot nextId 1 hrel env envTys varSlots cArm s0
            hsiLt hwf hscrut (fun j _ => by simp [Nat.add_comm 1 j]) hvswf henv
        have hidleIn : JpsIdle jpSlots sInner.locals :=
          JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
            ⟨hnonVIn _ (fun c => mkSlot_h_ne_v i c),
             hnonVIn _ (fun c => mkSlot_a_ne_v i c)⟩)
        obtain ⟨out, r, smid, hfoM, hevM, hclkM, hwfMid, hpostM⟩ :=
          compileCode_sound tags armBody ((fs.map Prod.snd).reverse ++ env)
            ((cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys)
            armVarSlots jpSigs jpSlots (nextId + k) retBound sInner
            hchkM hwfIn (by rw [hclkIn]; omega) hvswfIn (hjpswf.mono (by omega)) henvIn hidleIn
        rw [hclkIn] at hclkM
        refine ⟨out, r, sOut, hfoM, ?_, ?_, hwfOutFn (by rw [hevM]; exact hwfMid), ?_⟩
        · simp only [compileArms, htIdx, Option.getD_some]
          rw [evaluate_ite, eval_cmp, eval_rfield, eval_lvar, eval_const, hscrut]
          dsimp only
          simp only [List.getElem?_cons_zero, word_cmp, beq_self_eq_true, ↓reduceIte]
          have hnz : ((1#64 : Word) != 0#64) = true := by decide
          simp only [hnz, ↓reduceIte]
          dsimp only [fSlots, k, cArm] at hevBind ⊢
          rw [hevBind, hevM]
        · simp only [synthArmsClk]; rw [hclkOut, hevM]; dsimp only; omega
        · cases out with
          | returned rv =>
            rw [hevM] at hevBind
            exact hpostM
          | jumped tid argVals =>
            obtain ⟨hrM, htrigM, hvPresM⟩ := hpostM
            refine ⟨hrM, ?_, ?_⟩
            · refine JpTriggered.congr_of_wf hjpswf htrigM (fun i _ => ⟨?_, ?_⟩)
              · rw [hnonVOut _ (fun c => mkSlot_h_ne_v i c), hevM]
              · rw [hnonVOut _ (fun c => mkSlot_a_ne_v i c), hevM]
            · exact hvOut (by rw [hevM]; exact hvPresM)
      | false =>
        rw [heqTag] at hfind
        have hidxNe : cIdx ≠ tIdx := fun h => by
          subst h
          have := lookupTagIdx_inj htIdx hcIdx
          exact absurd (beq_iff_eq.mpr this) (by simp [heqTag])
        have hbvFalse : (BitVec.ofNat 64 cIdx == BitVec.ofNat 64 tIdx) = false := by
          rw [bv64_beq_ofNat hcIdxLt htagsValid.1]
          exact beq_eq_false_iff_ne.mpr hidxNe
        let k := fieldNames.length
        let fSlots := mkFreshSlots 'v' nextId k
        let armVarSlots := (fSlots.reverse.map (fun s => (s, Shape.One))) ++ varSlots
        let id1 := (compileCode tags armVarSlots jpSlots (nextId + k) armBody).2
        have hid1 : nextId + k ≤ id1 :=
          (compileCode_clk_and_mono tags armBody armVarSlots jpSlots (nextId + k)).2
        obtain ⟨out, r, s1, hfoM, hevRest, hclkRest, hwf1, hpostRest⟩ :=
          compileArms_sound tags rest scrutSlot si hsiSlot cTag cIdx cNames cBounds
            fs pvs mTag mBody env envTys varSlots jpSigs jpSlots id1 retBound s0
            (by omega) hcIdx hcIdxLt hrel htagsValid.2 hfind hchkM hwf (by omega)
            (hvswf.mono (by omega)) (hjpswf.mono (by omega)) henv hidle hscrut
        refine ⟨out, r, s1, hfoM, ?_, by simp only [synthArmsClk]; omega, hwf1, hpostRest⟩
        simp only [compileArms, htIdx, Option.getD_some]
        rw [evaluate_ite, eval_cmp, eval_rfield, eval_lvar, eval_const, hscrut]
        dsimp only
        simp only [List.getElem?_cons_zero, word_cmp, hbvFalse, Bool.false_eq_true, ↓reduceIte]
        have hz : ((0#64 : Word) != 0#64) = false := by decide
        simp only [hz, Bool.false_eq_true, ↓reduceIte]
        exact hevRest
termination_by structural arms => arms
end

/-! ## 7. Exported End-to-End Correctness, `Core4` Weld & Multi-Turn Batch Theorems -/

/-- Closed-program totality + tight `RefinesClkTight` theorem for `compileLcnfToPancake`. -/
theorem compileLcnfToPancake_tight {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound) :
    ∃ n : Nat,
      n ≤ retBound ∧
      retBound < 2 ^ 64 ∧
      (∀ fuel, minLcnfFuel c ≤ fuel → evalLcnfCode fuel [] [] [] c = some (n, [])) ∧
      RefinesClkTight (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun _ r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  simp only [checkFoLcnf] at hchk
  split at hchk <;> try simp at hchk
  obtain ⟨hboundLt, hpure⟩ := checkFoCode_bound_lt (collectTags c) c [] [] retBound hchk
  -- Extract canonical `n` by running `compileCode_sound` on `emptyPanState () (synthLcnfClk c)`
  let sDummy := emptyPanState () (synthLcnfClk c)
  have hvswf0 : VarSlotsWF 0 [] := fun _ h => by cases h
  have hidle0 : JpsIdle [] sDummy.locals := fun _ h => by cases h
  obtain ⟨out0, r0, _, hfo0, _, _, _, hpost0⟩ :=
    compileCode_sound (collectTags c) c [] [] [] [] [] 0 retBound sDummy
      hchk (emptyPanState_wf () _) (Nat.le_refl _) hvswf0 (.nil 0) (.nil _) hidle0
  cases out0 with
  | jumped _ _ => cases hpost0.2.1
  | returned rv =>
    obtain ⟨n, rfl, hnLe, _, _⟩ := hpost0
    refine ⟨n, hnLe, hboundLt, ?_, ?_⟩
    · intro fuel hfuel
      have hevVal := evalFoBlock_implies_evalLcnfCodeVal fuel c [] [] [] (.returned (.scalar n))
        (.scalar n) hpure .nil hfo0 rfl (by simpa [jpsFuel] using hfuel)
      simp [evalLcnfCode, hevVal, LcnfVal.toNat?]
    · intro s0 ⟨hwf0, _⟩ hclk0
      have hidleS0 : JpsIdle [] s0.locals := fun _ h => by cases h
      obtain ⟨out, r, s1, hfo, hev, hclk1, hwf1, hpost⟩ :=
        compileCode_sound (collectTags c) c [] [] [] [] [] 0 retBound s0
          hchk hwf0 hclk0 hvswf0 (.nil 0) (.nil _) hidleS0
      rw [hfo0] at hfo
      injection hfo with houtEq
      subst houtEq
      obtain ⟨n', hscEq, _, _, hrEq⟩ := hpost
      injection hscEq with hnEq
      subst hnEq
      subst hrEq
      exact ⟨.ret (.word (BitVec.ofNat 64 n)), s1, hev, PanResult.noConfusion, PanResult.noConfusion, hclk1, ⟨hwf1, rfl⟩⟩

/-- **Primary `G6` Theorem (`compileLcnfToPancake_correct`)**:
    Every well-typed first-order `LcnfCode` term `c` evaluates in `evalLcnfCode` to a `< 2^64`
    scalar `n` AND executes in `PanSem.evaluate` under synthesized `CondSClk` fuel `synthLcnfClk c`
    with `0` `TimeOut` and `0` `Error` (`RefinesClkPan`) to `.ret (.word (BitVec.ofNat 64 n))`. -/
theorem compileLcnfToPancake_correct {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound) :
    ∃ n : Nat,
      n ≤ retBound ∧
      retBound < 2 ^ 64 ∧
      evalLcnfCode (minLcnfFuel c) [] [] [] c = some (n, []) ∧
      synthStmtClk (compileLcnfToPancake c) = some (synthLcnfClk c) ∧
      RefinesClkPan (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  obtain ⟨n, hn, hlt, hfuel, htight⟩ := compileLcnfToPancake_tight (θ := θ) c retBound hchk
  exact ⟨n, hn, hlt, hfuel (minLcnfFuel c) (Nat.le_refl _),
    synthStmtClk_compileLcnfToPancake c, htight.toRefinesClkPan⟩

/-- **Joint Premise Inhabitation for `compileLcnfToPancake_correct`**:
    For every `ffiInit : θ` and `c : LcnfCode`, there exists a concrete `s0 : PanState θ`
    satisfying both `EntryWF (fun _ => True) s0` and `s0.clock ≥ synthLcnfClk c`. -/
theorem compileLcnfToPancake_premises_inhabited {θ : Type} (ffiInit : θ) (c : LcnfCode) :
    ∃ s0 : PanState θ, EntryWF (fun _ => True) s0 ∧ s0.clock ≥ synthLcnfClk c :=
  ⟨emptyPanState ffiInit (synthLcnfClk c), ⟨emptyPanState_wf ffiInit _, trivial⟩, Nat.le_refl _⟩

/-- Multi-turn batch checker over a sequence of first-order `LcnfCode` request handlers. -/
def checkFoLcnfBatch : List LcnfCode → Option (List Nat)
  | [] => some []
  | c :: cs => do
    let b ← checkFoLcnf c
    let bs ← checkFoLcnfBatch cs
    return b :: bs
termination_by structural cs => cs

/-- Cumulative path-sensitive clock bound across a multi-turn batch `List LcnfCode`. -/
def synthBatchClk : List LcnfCode → Nat
  | [] => 0
  | c :: cs => synthLcnfClk c + synthBatchClk cs
termination_by structural cs => cs

/-- Multi-turn batch execution of compiled `LcnfCode` handlers threading persistent `PanState`
    (`memory`, `globals`, `ffi`, and remaining `clock`) across turns. -/
def runCompiledLcnfBatch {θ : Type} : List LcnfCode → PanState θ → Option (List Word × PanState θ)
  | [], s => some ([], s)
  | c :: cs, s =>
    match evaluate (compileLcnfToPancake c) s with
    | (.ret (.word w), s1) =>
      match runCompiledLcnfBatch cs s1 with
      | some (ws, sFinal) => some (w :: ws, sFinal)
      | none => none
    | _ => none
termination_by structural cs => cs

/-- `Init`-only turn-by-turn evaluation relation pairing each `LcnfCode` turn with its exact scalar output. -/
inductive BatchEvalRel : List LcnfCode → List Nat → Prop where
  | nil : BatchEvalRel [] []
  | cons {c : LcnfCode} {n : Nat} {cs : List LcnfCode} {ns : List Nat} :
      evalLcnfCode (minLcnfFuel c) [] [] [] c = some (n, []) →
      BatchEvalRel cs ns →
      BatchEvalRel (c :: cs) (n :: ns)

/-- **Apex Multi-Turn Batch Trace Theorem (`runCompiledLcnfBatch_sound`)**:
    Every checked batch `cs : List LcnfCode` executes end-to-end across `runCompiledLcnfBatch`
    from any `StateWF s0` with `s0.clock ≥ synthBatchClk cs` with `0` `TimeOut`/`Error`,
    preserving `StateWF` and cumulative clock bounds while agreeing turn-by-turn with
    `Obend.Lower.LCNF.evalLcnfCode` (and `compileLcnfToCore4` on `isJoinFreePureBlock` turns). -/
theorem runCompiledLcnfBatch_sound {θ : Type} :
    ∀ (cs : List LcnfCode) (bounds : List Nat) (s0 : PanState θ),
      checkFoLcnfBatch cs = some bounds →
      StateWF s0 →
      synthBatchClk cs ≤ s0.clock →
      ∃ (ns : List Nat) (sFinal : PanState θ),
        runCompiledLcnfBatch cs s0 = some (ns.map (BitVec.ofNat 64), sFinal) ∧
        s0.clock ≤ sFinal.clock + synthBatchClk cs ∧
        StateWF sFinal ∧
        BatchEvalRel cs ns
  | [], bounds, s0, hchk, hwf0, _ => by
    simp only [checkFoLcnfBatch, Option.some.injEq] at hchk
    exact ⟨[], s0, rfl, by simp [synthBatchClk], hwf0, .nil⟩
  | c :: cs, bounds, s0, hchk, hwf0, hclk0 => by
    simp only [checkFoLcnfBatch] at hchk
    cases hc : checkFoLcnf c with
    | none => simp [hc] at hchk
    | some b =>
      rw [hc] at hchk
      cases hcs : checkFoLcnfBatch cs with
      | none => simp [hcs] at hchk
      | some bs =>
        simp only [synthBatchClk] at hclk0
        obtain ⟨n, _, _, hfuelC, htightC⟩ := compileLcnfToPancake_tight (θ := θ) c b hc
        obtain ⟨r1, s1, hev1, _, _, hclk1, hwf1, hr1⟩ :=
          htightC s0 ⟨hwf0, trivial⟩ (by omega)
        subst hr1
        obtain ⟨nsRest, sFinal, hrunRest, hclkRest, hwfFinal, hrelRest⟩ :=
          runCompiledLcnfBatch_sound cs bs s1 hcs hwf1 (by omega)
        have hevC : evalLcnfCode (minLcnfFuel c) [] [] [] c = some (n, []) :=
          hfuelC (minLcnfFuel c) (Nat.le_refl _)
        refine ⟨n :: nsRest, sFinal, ?_, by simp only [synthBatchClk]; omega, hwfFinal,
          .cons hevC hrelRest⟩
        simp only [runCompiledLcnfBatch, hev1, hrunRest, List.map_cons]




/-- Canonical fuel-complete scalar evaluator `evalLcnf`. -/
def evalLcnf (c : LcnfCode) : Option Nat :=
  (evalLcnfCode (minLcnfFuel c) [] [] [] c).map Prod.fst

/-- Direct `evalLcnf` corollary of `compileLcnfToPancake_correct`. -/
theorem compileLcnfToPancake_evalLcnf_correct {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound) :
    ∃ n : Nat,
      evalLcnf c = some n ∧
      n ≤ retBound ∧
      RefinesClkPan (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  obtain ⟨n, hn, _, hev, _, href⟩ := compileLcnfToPancake_correct (θ := θ) c retBound hchk
  exact ⟨n, by simp [evalLcnf, hev], hn, href⟩

/--
info: 'OrbPancakeV435.synthStmtClk_compileLcnfToPancake' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms synthStmtClk_compileLcnfToPancake

/--
info: 'OrbPancakeV435.compileLcnfToPancake_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms compileLcnfToPancake_correct

/--
info: 'OrbPancakeV435.runCompiledLcnfBatch_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runCompiledLcnfBatch_sound

end OrbPancakeV435
