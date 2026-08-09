/-
# Theory.IndexedProgram -- typed free programs and cross-carrier folds

This file is a candidate-independent semantic foundation.  Operations are
first-order shapes indexed by a typestate.  Each operation chooses both a
dependent response type and the typestate of its continuation.  `Program` is
the corresponding intrinsically typed free program.

The important comparison principles are deliberately cross-carrier:

* `fold_fusion` transports a fold through an algebra morphism;
* `fold_rel` transports a logical relation through two related algebras.

Neither theorem identifies arbitrary readings merely because they consume the
same syntax.  The final example includes a concrete mismatched algebra which
computes a different answer.
-/
import Mathlib.Tactic

namespace Minidregg.Theory.IndexedProgram

universe u v w x y z

/-! ## First-order values -/

/-- A first-order codec with its executable round-trip law.  The carrier may
be abstract, but any value crossing a semantic boundary has canonical bytes
and a decoder which recovers values produced by the encoder. -/
structure LawfulCodec (α : Type u) where
  encode : α → List UInt8
  decode : List UInt8 → Option α
  decode_encode : ∀ a, decode (encode a) = some a

/-- A compact universe of first-order value codes.  Syntax stores codes and
values of `El code`; it never stores semantic closures. -/
structure FirstOrderUniverse where
  Code : Type u
  El : Code → Type v
  codec : (c : Code) → LawfulCodec (El c)

/-! ## Indexed signatures and free programs -/

/-- An indexed algebraic-effect signature.  At typestate `i`, `Op i` is the
type of available operation shapes.  An operation chooses a dependent response
type; the concrete response determines the continuation typestate. -/
structure IxSignature (Ix : Type u) where
  Op : Ix → Type v
  Resp : {i : Ix} → Op i → Type w
  next : {i : Ix} → (op : Op i) → Resp op → Ix

/-- The intrinsically typed free program over `Sig` with result family `A`.
`call op k` exposes exactly one continuation for each possible response, at
the typestate selected by `Sig.next op`. -/
inductive Program {Ix : Type u} (Sig : IxSignature.{u, v, w} Ix)
    (A : Ix → Type x) : Ix → Type (max u v w x) where
  | pure {i : Ix} (a : A i) : Program Sig A i
  | call {i : Ix} (op : Sig.Op i)
      (k : (r : Sig.Resp op) → Program Sig A (Sig.next op r)) : Program Sig A i

/-! ## Algebras and the executable fold -/

/-- An algebra reads a program into an indexed carrier `C`. -/
structure Algebra {Ix : Type u} (Sig : IxSignature.{u, v, w} Ix)
    (A : Ix → Type x) (C : Ix → Type y) where
  pure : {i : Ix} → A i → C i
  call : {i : Ix} → (op : Sig.Op i) →
    ((r : Sig.Resp op) → C (Sig.next op r)) → C i

/-- The executable fold of an intrinsically typed program. -/
def fold {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} (alg : Algebra Sig A C) :
    {i : Ix} → Program Sig A i → C i
  | _, .pure a => alg.pure a
  | _, .call op k => alg.call op fun r => fold alg (k r)

@[simp] theorem fold_pure {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} (alg : Algebra Sig A C)
    {i : Ix} (a : A i) :
    fold alg (.pure a) = alg.pure a :=
  rfl

@[simp] theorem fold_call {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} (alg : Algebra Sig A C)
    {i : Ix} (op : Sig.Op i)
    (k : (r : Sig.Resp op) → Program Sig A (Sig.next op r)) :
    fold alg (.call op k) = alg.call op (fun r => fold alg (k r)) :=
  rfl

/-! ## Cross-carrier comparison principles -/

/-- `φ` is an algebra morphism from `src` to `dst`: it preserves both returned
values and operation nodes.  The carriers may be entirely different. -/
structure AlgebraHom {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} {D : Ix → Type z}
    (src : Algebra Sig A C) (dst : Algebra Sig A D)
    (φ : (i : Ix) → C i → D i) : Prop where
  pure : ∀ {i : Ix} (a : A i), φ i (src.pure a) = dst.pure a
  call : ∀ {i : Ix} (op : Sig.Op i)
      (k : (r : Sig.Resp op) → C (Sig.next op r)),
    φ i (src.call op k) = dst.call op (fun r => φ (Sig.next op r) (k r))

/-- **Fold fusion.** A cross-carrier algebra morphism commutes with the fold. -/
theorem fold_fusion {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} {D : Ix → Type z}
    {src : Algebra Sig A C} {dst : Algebra Sig A D}
    {φ : (i : Ix) → C i → D i} (h : AlgebraHom src dst φ)
    {i : Ix} (p : Program Sig A i) :
    φ i (fold src p) = fold dst p := by
  induction p with
  | pure a => exact h.pure a
  | call op k ih =>
      calc
        φ _ (src.call op (fun r => fold src (k r))) =
            dst.call op (fun r => φ _ (fold src (k r))) :=
          h.call op (fun r => fold src (k r))
        _ = dst.call op (fun r => fold dst (k r)) := by
          apply congrArg (dst.call op)
          funext r
          exact ih r

/-- Two algebras preserve an indexed logical relation node-by-node.  Unlike an
algebra morphism, `R` need not be functional or equality-shaped. -/
structure AlgebraRel {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} {D : Ix → Type z}
    (left : Algebra Sig A C) (right : Algebra Sig A D)
    (R : (i : Ix) → C i → D i → Prop) : Prop where
  pure : ∀ {i : Ix} (a : A i), R i (left.pure a) (right.pure a)
  call : ∀ {i : Ix} (op : Sig.Op i)
      (lc : (r : Sig.Resp op) → C (Sig.next op r))
      (rc : (r : Sig.Resp op) → D (Sig.next op r)),
    (∀ r, R (Sig.next op r) (lc r) (rc r)) →
      R i (left.call op lc) (right.call op rc)

/-- **Logical-relation fold theorem.** Nodewise-related algebras yield related
readings of every well-typed program. -/
theorem fold_rel {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {C : Ix → Type y} {D : Ix → Type z}
    {left : Algebra Sig A C} {right : Algebra Sig A D}
    {R : (i : Ix) → C i → D i → Prop} (h : AlgebraRel left right R)
    {i : Ix} (p : Program Sig A i) :
    R i (fold left p) (fold right p) := by
  induction p with
  | pure a => exact h.pure a
  | call op k ih =>
      exact h.call op (fun r => fold left (k r))
        (fun r => fold right (k r)) ih

/-! ## A deterministic handler and interpreter -/

/-- A handler executes one operation against an indexed state.  Its dependent
pair contains the response and a state at precisely the response-selected next
typestate. -/
structure Handler {Ix : Type u} (Sig : IxSignature.{u, v, w} Ix)
    (S : Ix → Type y) where
  handle : {i : Ix} → (op : Sig.Op i) → S i →
    Σ r : Sig.Resp op, S (Sig.next op r)

/-- The result of executing from an unknown final typestate. -/
abbrev Outcome {Ix : Type u} (A : Ix → Type x) (S : Ix → Type y) :=
  Σ i : Ix, A i × S i

/-- State-transformer carrier used by `execAlgebra`. -/
abbrev ExecCarrier {Ix : Type u} (A : Ix → Type x) (S : Ix → Type y) (i : Ix) :=
  S i → Outcome A S

/-- A handler induces an executable state-transformer algebra. -/
def execAlgebra {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {S : Ix → Type y} (h : Handler Sig S) :
    Algebra Sig A (ExecCarrier A S) where
  pure := fun a s => ⟨_, a, s⟩
  call := fun op k s =>
    match h.handle op s with
    | ⟨r, s'⟩ => k r s'

/-- Execute a free program by folding the algebra induced by `h`. -/
def interpret {Ix : Type u} {Sig : IxSignature.{u, v, w} Ix}
    {A : Ix → Type x} {S : Ix → Type y} (h : Handler Sig S)
    {i : Ix} (p : Program Sig A i) : S i → Outcome A S :=
  fold (execAlgebra h) p

/-! ## Small executable witness and mismatch tooth -/

namespace Example

/-- Two typestates used only to exercise dependent continuation indexing. -/
inductive Phase
  | idle
  | ready
deriving DecidableEq, Repr

/-- `choose` is available while idle; `tick` only after choosing `true`. -/
inductive DemoOp : Phase → Type
  | choose : DemoOp .idle
  | tick : DemoOp .ready

def demoSig : IxSignature Phase where
  Op := DemoOp
  Resp := fun op => match op with
    | .choose => Bool
    | .tick => Unit
  next := fun op r => match op, r with
    | .choose, false => .idle
    | .choose, true => .ready
    | .tick, () => .ready

abbrev DemoResult : Phase → Type := fun _ => Nat
abbrev DemoState : Phase → Type := fun _ => Nat

/-- The `true` continuation type-checks at `.ready`, where `tick` is available;
the `false` continuation remains at `.idle`. -/
def demoProgram : Program demoSig DemoResult .idle :=
  .call .choose fun
    | false => .pure 3
    | true => .call .tick fun _ => .pure 7

/-- An executable handler which takes the ready branch and updates its state at
both operations. -/
def yesHandler : Handler demoSig DemoState where
  handle := fun op s => match op with
    | .choose => ⟨true, s + 1⟩
    | .tick => ⟨(), s + 10⟩

/-- Positive executable witness: the dependent response selects `.ready`, the
continuation runs, and the final result/state are computed by `interpret`. -/
theorem demo_interpret :
    interpret yesHandler demoProgram 0 =
      (⟨.ready, (7, 11)⟩ : Outcome DemoResult DemoState) :=
  rfl

/-- Count every syntactic operation into `Nat`, including both response
continuations because a fold reads the whole free program tree. -/
def countNat : Algebra demoSig DemoResult (fun _ => Nat) where
  pure := fun _ => 0
  call := fun op k => match op with
    | .choose => 1 + k false + k true
    | .tick => 1 + k ()

/-- The corresponding cross-carrier reading into `Int`. -/
def countInt : Algebra demoSig DemoResult (fun _ => Int) where
  pure := fun _ => 0
  call := fun op k => match op with
    | .choose => 1 + k false + k true
    | .tick => 1 + k ()

/-- Casting node counts is an algebra morphism. -/
def countCastHom : AlgebraHom countNat countInt (fun _ n => (n : Int)) where
  pure := by intro i a; rfl
  call := by
    intro i op k
    cases op <;> simp [countNat, countInt]

/-- Positive cross-carrier witness: fusion, rather than same-carrier
initiality, forces the two readings to agree. -/
theorem demo_fusion :
    ((fold countNat demoProgram : Nat) : Int) = fold countInt demoProgram :=
  fold_fusion countCastHom demoProgram

/-- A deliberately wrong `Int` algebra charges `tick` twice. -/
def wrongCountInt : Algebra demoSig DemoResult (fun _ => Int) where
  pure := fun _ => 0
  call := fun op k => match op with
    | .choose => 1 + k false + k true
    | .tick => 2 + k ()

/-- **Mismatch tooth.** Sharing syntax supplies no agreement when the target
algebra does not preserve the declared reading. -/
theorem wrong_algebra_mismatch :
    ((fold countNat demoProgram : Nat) : Int) ≠ fold wrongCountInt demoProgram := by
  decide

end Example

end Minidregg.Theory.IndexedProgram
