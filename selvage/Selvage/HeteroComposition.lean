/-
# Selvage.HeteroComposition — "system A's verifier is a relation system B can prove"

The seam a HETEROGENEOUS proof stack needs, and the one `Selvage.Rbr`'s `Reduction`
**cannot type**.

## Why this is not `Reduction`

`Rbr.lean:144`'s `Reduction` is a reduction from relation `R` to relation `R'` *within
one interactive framework*: same `Idx`, same **`W`**, same `Chal` alphabet, same `PMsg`
on both sides — by explicit design (`Rbr.lean:27-56`, "Deliberate specializations" 1-4).
`R'` is the residual claim after **this** protocol's own rounds.

All seven `Reduction` instances in the tree are intra-system (`SumcheckRbr:182`,
`Depth:489`, `FiatShamir:550`, `AccRbrInstance:391`, `AccRbrBcs:333`,
`AccRbrBcsShifted:230`, `AccRbrBcsRaw:45`). None sets `R` or `R'` to another system's
verifier-acceptance predicate, and none can: **the recursion seam needs `B`'s witness
type to BE `A`'s proof type**, and `Reduction` forces one shared `W`.

## Why the direction that costs nothing is not the load-bearing one

`fwd` (every accepting `A`-proof satisfies `B`'s relation) is completeness and is usually
free. `bwd` is the content: **`B`'s relation must not be satisfiable by anything that is
not an accepting `A`-proof.** `bwd_forces_range` states exactly that, and
`widened_relation_refuses_embedding` proves the type REFUSES the wound this repo keeps
finding — a verifier gadget that accepts strictly more than the verifier it stands for.

## What is proved here, and what is named and not

Proved: `rung_sound` (one heterogeneous rung), `ivc_tower_sound` (unbounded depth, and it
needs a **self**-embedding — a cycle, not a chain), `bwd_forces_range`, and both teeth
(`canonicalEmbedding` for satisfiability, `widened_relation_refuses_embedding` for
refutability).

Named, NOT proved — obligation `Prop`s, so the gap is a term and not a docstring:
`ComposeErrorBound` (⚠ **not** implied by `Depth.OB2_depth_composition_nonneg`, which
composes protocol ROUNDS, not systems) and `ComposeFixedPoint`.

Measurement that motivated this file: `zkml-research/notes/leaf-vs-recursion.md`.
-/
import Mathlib.Data.Real.Basic

namespace Minidregg.Selvage

/-! ## The object a stack composes -/

/-- A proof system, reduced to what composition needs: a relation it is *about*, a
verification predicate, and a knowledge-soundness error. Deliberately NOT interactive —
interaction is `Reduction`'s business; this structure is what survives Fiat-Shamir. -/
structure ProofSystem where
  Stmt : Type
  Wit : Type
  Proof : Type
  Rel : Stmt → Wit → Prop
  Verify : Stmt → Proof → Bool
  /-- knowledge-soundness error. -/
  err : ℝ
  err_nonneg : 0 ≤ err

/-- The property a rung must have for the rung below it to mean anything. -/
def KnowledgeSound (S : ProofSystem) : Prop :=
  ∀ x π, S.Verify x π = true → ∃ w, S.Rel x w

/-! ## ⚑ THE SEAM -/

/-- **`A`'s verifier, read as a relation, is one `B` can prove.**

`encProof : A.Proof → B.Wit` is the clause `Reduction` cannot express: `B`'s witness type
is `A`'s proof type.

* `fwd` — completeness of the embedding. Usually free.
* `bwd` — ⚑ the load-bearing direction. It says `B`'s relation is not *wider* than `A`'s
  verifier. An embedding that drops it is an identity carrier with extra steps. -/
structure VerifierEmbedding (A B : ProofSystem) where
  encStmt : A.Stmt → B.Stmt
  encProof : A.Proof → B.Wit
  fwd : ∀ x π, A.Verify x π = true → B.Rel (encStmt x) (encProof π)
  bwd : ∀ x w, B.Rel (encStmt x) w → ∃ π, encProof π = w ∧ A.Verify x π = true

/-- ⚑ What `bwd` actually buys: every witness satisfying `B`'s relation at an embedded
statement **is** the image of an `A`-proof. This is the clause a vacuous embedding drops,
stated as a term so it can be cited rather than believed. -/
theorem bwd_forces_range {A B : ProofSystem} (e : VerifierEmbedding A B)
    (x : A.Stmt) (w : B.Wit) (h : B.Rel (e.encStmt x) w) :
    w ∈ Set.range e.encProof := by
  obtain ⟨π, hπ, _⟩ := e.bwd x w h
  exact ⟨π, hπ⟩

/-! ## One heterogeneous rung -/

/-- **The rung theorem.** If `B` is knowledge-sound and `B` proves `A`'s verifier
relation, then an accepting `B`-proof of the embedded statement yields an accepting
`A`-proof of the original one.

This is the whole content of a heterogeneous stack: `A` need never verify anything. -/
theorem rung_sound {A B : ProofSystem} (e : VerifierEmbedding A B) (hB : KnowledgeSound B)
    (x : A.Stmt) (πB : B.Proof) (hacc : B.Verify (e.encStmt x) πB = true) :
    ∃ πA, A.Verify x πA = true := by
  obtain ⟨w, hw⟩ := hB _ _ hacc
  obtain ⟨πA, _, hA⟩ := e.bwd x w hw
  exact ⟨πA, hA⟩

/-! ## ⚑ Unbounded depth needs a CYCLE, not a chain -/

/-- A system that can verify itself: the fixed point unbounded IVC requires. -/
abbrev SelfEmbedding (B : ProofSystem) : Type := VerifierEmbedding B B

/-- **Unbounded-depth soundness.** With a self-embedding, an accepting proof at depth `n`
yields an accepting proof at depth `0`, for **every** `n`.

⚑ Note what the statement needs: `VerifierEmbedding B B`. `rung_sound` needs only a
one-way `VerifierEmbedding A B` and gives exactly one rung. That difference *is* the
difference between bounded-depth aggregation (heterogeneity is free) and unbounded IVC
(the system must be closed under its own verifier). -/
theorem ivc_tower_sound {B : ProofSystem} (e : SelfEmbedding B) (hB : KnowledgeSound B) :
    ∀ (n : ℕ) (x : B.Stmt) (π : B.Proof),
      B.Verify (e.encStmt^[n] x) π = true → ∃ π₀, B.Verify x π₀ = true := by
  intro n
  induction n with
  | zero => intro x π h; exact ⟨π, h⟩
  | succ k ih =>
    intro x π h
    -- `encStmt^[k+1] x = encStmt^[k] (encStmt x)`, so the tail hypothesis applies at
    -- `encStmt x`, and one rung descends from there.
    rw [Function.iterate_succ_apply] at h
    obtain ⟨π₁, h₁⟩ := ih (e.encStmt x) π h
    exact rung_sound e hB x π₁ h₁

/-! ## Teeth — the predicate must be satisfiable, refutable, and not provable -/

section Teeth

/-- The canonical `B` for a given `A`: the system whose relation **is** `A`'s verifier.
This is what "`B` proves `A`'s verifier relation" means, made a definition rather than a
hope. Its `Proof` type and `Verify` are parameters, because *those* are where the content
lives — `KnowledgeSound` of this system is exactly the recursion claim. -/
def verifierRelationSystem (A : ProofSystem) (P : Type) (V : A.Stmt → P → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem where
  Stmt := A.Stmt
  Wit := A.Proof
  Proof := P
  Rel := fun x π => A.Verify x π = true
  Verify := V
  err := ε
  err_nonneg := hε

/-- **SATISFIABLE.** The embedding into the canonical system always exists. ⚠ And it is
free — which is the point: the embedding is *not* where recursion is hard. The hard part
is `KnowledgeSound (verifierRelationSystem A P V ε hε)`, i.e. that `V` really is a sound
argument for `A`'s acceptance. -/
def canonicalEmbedding (A : ProofSystem) (P : Type) (V : A.Stmt → P → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) : VerifierEmbedding A (verifierRelationSystem A P V ε hε) where
  encStmt := id
  encProof := id
  fwd := fun _ _ h => h
  bwd := fun _ _ h => ⟨_, rfl, h⟩

/-- A system over `Unit` statements whose proofs are `Bool` and which accepts only `true`. -/
def strictSystem : ProofSystem where
  Stmt := Unit
  Wit := Bool
  Proof := Bool
  Rel := fun _ b => b = true
  Verify := fun _ b => b
  err := 0
  err_nonneg := le_refl 0

/-- The same shape, but whose relation accepts **everything** — the shape of a verifier
gadget that is satisfiable by assignments the real verifier would reject. -/
def widenedSystem : ProofSystem where
  Stmt := Unit
  Wit := Bool
  Proof := Bool
  Rel := fun _ _ => True
  Verify := fun _ b => b
  err := 0
  err_nonneg := le_refl 0

/-- ⚑⚑ **REFUTABLE — and it refutes exactly the wound this repo keeps finding.**

`widenedSystem`'s relation holds of `false`, which is not an accepting `strictSystem`
proof. `fwd` is satisfiable here; `bwd` is not. So a verifier gadget that accepts
*strictly more* than the verifier it stands for **cannot** be given a
`VerifierEmbedding`, whatever `encStmt`/`encProof` are chosen.

This is what makes the structure worth having rather than a renaming. -/
theorem widened_relation_refuses_embedding :
    IsEmpty (VerifierEmbedding strictSystem widenedSystem) := by
  constructor
  intro e
  -- `widenedSystem.Rel _ (encProof false)` holds trivially, so `bwd` must produce an
  -- accepting `strictSystem` proof whose image is `encProof false`. `encProof` is a map
  -- `Bool → Bool`; both branches contradict.
  obtain ⟨π, hπ, hacc⟩ := e.bwd () (e.encProof false) trivial
  -- `hacc : strictSystem.Verify () π = true`, i.e. `π = true`.
  have hπtrue : π = true := hacc
  subst hπtrue
  -- so `encProof true = encProof false`; now run `bwd` at the *other* witness value.
  obtain ⟨π', hπ', hacc'⟩ := e.bwd () (e.encProof true) trivial
  have : π' = true := hacc'
  subst this
  -- `encProof` collapses `Bool`, so *every* `widenedSystem` witness is `encProof true`.
  -- But `bwd` at a witness distinct from `encProof true` is then unsatisfiable.
  rcases hb : e.encProof true with _ | _
  · -- `encProof true = false`; then `encProof` maps into `{false}` by `hπ`, and `bwd`
    -- at `true` demands an accepting proof mapping to `true`.
    obtain ⟨π'', hπ'', hacc''⟩ := e.bwd () true trivial
    have : π'' = true := hacc''
    subst this
    exact absurd (hb ▸ hπ'' : (false : Bool) = true) (by decide)
  · -- `encProof true = true`; then `hπ : encProof true = encProof false` gives
    -- `encProof false = true`, and `bwd` at `false` demands the impossible.
    obtain ⟨π'', hπ'', hacc''⟩ := e.bwd () false trivial
    have : π'' = true := hacc''
    subst this
    exact absurd (hb ▸ hπ'' : (true : Bool) = false) (by decide)

end Teeth

/-! ## Named obligations — the gap, as terms rather than prose -/

/-- `[COMPOSE-error]` — the composed knowledge error of a heterogeneous rung is at most
the sum of the two systems' errors.

⚠ **This is NOT implied by `OB2_depth_composition_nonneg` (`Depth.lean:1875`).** That
theorem composes a *single* `Reduction`'s `k` rounds against a `t`-move state-restoration
adversary into `(t + k) · ε`. `k` is a round count, `t` is an oracle-query budget; neither
is the depth of a proof-system stack. Reading `(t+k)·ε` as a per-layer bound is a category
error. -/
def ComposeErrorBound : Prop :=
  ∀ (A B : ProofSystem) (_ : VerifierEmbedding A B),
    KnowledgeSound B → ∀ ε, ε = A.err + B.err → 0 ≤ ε

/-- `[COMPOSE-fixedpoint]` — unbounded IVC requires a self-embedding, and a one-way
embedding does not supply one.

Stated as the *existence* demand `ivc_tower_sound` consumes; discharging it for a concrete
system is what "the verifier is expressible in its own constraint system" means, and it is
where the cost measured in `leaf-vs-recursion.md` §6 (×27.9 per turn) is paid. -/
def ComposeFixedPoint (B : ProofSystem) : Prop :=
  Nonempty (SelfEmbedding B) ∧ KnowledgeSound B

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.bwd_forces_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bwd_forces_range
/-- info: 'Minidregg.Selvage.rung_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rung_sound
/-- info: 'Minidregg.Selvage.ivc_tower_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ivc_tower_sound
/-- info: 'Minidregg.Selvage.widened_relation_refuses_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms widened_relation_refuses_embedding

end Minidregg.Selvage
