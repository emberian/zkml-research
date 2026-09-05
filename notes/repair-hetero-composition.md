# Repair lane: `HeteroComposition.lean` says the true thing — CHECKPOINT (plan only, nothing on disk)

Lane note, 2026-09-05. Tree `~/dev/minidregg` main at `60f0499`. **State at checkpoint: NO file
edited.** `Selvage/HeteroComposition.lean`, `Selvage/HeteroCompositionSuccinct.lean`,
`Selvage/HeteroCompositionErrorBound.lean` are all at HEAD and green. `pgrep -f "lake build"`
was empty. This note is the design a fresh session should execute, with the reasons that were
paid for while reading.

## The one fact that shapes every decision

**A fixed `ProofSystem` cannot honestly carry a positive knowledge error.** `Verify : Stmt →
Proof → Bool` is deterministic; if any `(x, π)` is accepted with no witness, the adversary that
outputs it fails with probability 1 under ANY measure (Dirac). So `KnowledgeSound (S :
ProofSystem) ε` quantified over all adversaries collapses to the perfect form for every `ε`
(unnormalised measures: scale the Dirac by `ε + 1`). The F₅ positive-error object
(`accBcsSystem_F5 b oneOracle`, refuted at the FIXED oracle by `accBcsSystem_F5_not_knowledgeSound`)
is knowledge-sound at `(b+2)/5` only **over the oracle**: `FsKnowledgeSoundRO` prices the SR game
whose coins include the final challenges that define `fsOracle o ρs`. Therefore:

* the error-carrying object is an **oracle-indexed family** `S : O → ProofSystem` (the verifier's
  randomness is `O`; a system with none has `O = Unit`);
* the error is relative to an **adversary class** (the ROM lives in the class: it fixes how the
  oracle is drawn relative to the adversary's output). Against `Set.univ` only error `0` has
  content, and that IS the perfect form — as a theorem, not a second definition.

## The definitions to land in `Selvage/HeteroComposition.lean` (imports stay `Mathlib.Data.Real.Basic`)

```lean
structure ProofSystem where            -- err / err_nonneg REMOVED (see "err" below)
  Stmt Wit Proof : Type
  Rel : Stmt → Wit → Prop
  Verify : Stmt → Proof → Bool

/-- Knowledge-soundness FAILURE at one run: accepted, and no witness at all
(extractor-free reading; `ExtractFailure` names the extractor). Moved from Succinct:159. -/
def KsFailure (S : ProofSystem) (x : S.Stmt) (π : S.Proof) : Prop :=
  S.Verify x π = true ∧ ∀ w, ¬ S.Rel x w

/-- Error semantics: the weakest a union bound needs. Moved from ErrorBound:210, PLUS `empty`
(without it `μ ∅` is unbounded and the perfect form would not be the ε = 0 case). -/
structure EventMeasure (Ω : Type) where
  μ : (Ω → Prop) → ℝ
  nonneg : ∀ E, 0 ≤ μ E
  mono : ∀ E F, (∀ ω, E ω → F ω) → μ E ≤ μ F
  subadd : ∀ E F, μ (fun ω => E ω ∨ F ω) ≤ μ E + μ F
  empty : μ (fun _ => False) = 0

/-- An adversary against the family: coins, their measure, and the run — oracle, statement,
proof — as functions of the coins. -/
structure Adversary {O : Type} (S : O → ProofSystem) where
  Ω : Type
  m : EventMeasure Ω
  oracle : Ω → O
  stmt : (ω : Ω) → (S (oracle ω)).Stmt
  proof : (ω : Ω) → (S (oracle ω)).Proof

def Adversary.failure (𝒜 : Adversary S) : ℝ :=
  𝒜.m.μ fun ω => KsFailure (S (𝒜.oracle ω)) (𝒜.stmt ω) (𝒜.proof ω)

/-- ⚑ THE definition. -/
def KnowledgeSound {O : Type} (S : O → ProofSystem) (𝒞 : Set (Adversary S)) (ε : ℝ) : Prop :=
  ∀ 𝒜 ∈ 𝒞, 𝒜.failure ≤ ε

/-- The perfect form is the univ/0 case (holds at every 0 ≤ ε, because measures are
unnormalised — scale a Dirac). -/
theorem knowledgeSound_univ_iff (S : O → ProofSystem) {ε : ℝ} (hε : 0 ≤ ε) :
    KnowledgeSound S Set.univ ε ↔ ∀ o x π, (S o).Verify x π = true → ∃ w, (S o).Rel x w
```
(→): Dirac on `Unit` at a failing run, scaled by `ε + 1` (a `scaledDirac c ω₀ : EventMeasure`).
(←): the event is pointwise `False`; `mono` then `empty`.

Composition (this REPLACES `ComposeErrorBound` in place and absorbs `composeSystem`,
`ComposeErrorBoundStrict`, `composeErrorBoundStrict_closes`, `rung_sound_ro`, `TowerSoundRO`):

```lean
def composeSystem (A B : ProofSystem) (e : VerifierEmbedding A B) : ProofSystem   -- from ErrorBound:135, no err
def composeFamily (A : ProofSystem) (S : O → ProofSystem) (e : ∀ o, VerifierEmbedding A (S o)) :
    O → ProofSystem := fun o => composeSystem A (S o) (e o)
/-- the rung adversary read against the target: statement pushed through encStmt -/
def Adversary.target (𝒜 : Adversary (composeFamily A S e)) : Adversary S
/-- ⚑ the transfer event: an EXISTENTIAL over A-proofs (the extractor-efficiency clause) -/
def Adversary.sourceFailure (𝒜 : Adversary (composeFamily A S e)) : ℝ :=
  𝒜.m.μ fun ω => ∃ πA, KsFailure A (𝒜.stmt ω) πA

/-- [COMPOSE-error], honestly: the composed error is at most the sum along the rung. -/
def ComposeErrorBound : Prop :=
  ∀ {O : Type} (A : ProofSystem) (S : O → ProofSystem) (e : ∀ o, VerifierEmbedding A (S o))
    (𝒜 : Adversary (composeFamily A S e)), 𝒜.failure ≤ 𝒜.sourceFailure + 𝒜.target.failure
theorem rung_sound : ComposeErrorBound   -- containment through bwd, then subadd (ErrorBound:293 verbatim)
```
`ivc_tower_sound` (self-embedding family `e : ∀ o, SelfEmbedding (S o)`), proof-descent shape as
before, at error: for `𝒜 : Adversary S` and `n`,
`𝒜.m.μ (fun ω => (S _).Verify (encStmt^[n] (stmt ω)) (proof ω) = true ∧ ¬ ∃ π₀, (S _).Verify (stmt ω) π₀ = true)
  ≤ ∑ k < n, 𝒜.m.μ (fun ω => ∃ π, KsFailure (S _) (encStmt^[k+1] (stmt ω)) π)`,
by `HasProof (k+1) ∧ ¬ HasProof k ⊆ ∃ π, KsFailure … (encStmt^[k+1] x) π` (bwd) and induction
on `n` with `Function.iterate_succ_apply'`; corollary: each level ≤ ε ⇒ `≤ n * ε`. At `univ`/0
every level is empty and the old `ivc_tower_sound` is recovered. The per-level existential
hypotheses are exactly `[HETERO-err-tower]`'s open clause at the SR class — the residual stays
NAMED there, no longer as a parallel `TowerSoundRO` def.

`ComposeFixedPoint` stays, re-typed: `(S : O → ProofSystem) (𝒞) (ε) := Nonempty (∀ o,
SelfEmbedding (S o)) ∧ KnowledgeSound S 𝒞 ε`.

Coordinator's addition (one theorem, pinned):
```lean
def ExtractFailure (S) (E : S.Stmt → S.Proof → S.Wit) (x) (π) : Prop := S.Verify x π = true ∧ ¬ S.Rel x (E x π)
/-- Canonical witness generator ⇒ the extractor `E s π := W s` has knowledge error ≤ the
soundness error. Runtime model: extraction EXECUTES W (replay-time, not polylog). -/
theorem knowledgeSound_of_canonicalWitness (S : O → ProofSystem) (W : ∀ o, (S o).Stmt → (S o).Wit)
    (hW : ∀ o s, (∃ w, (S o).Rel s w) → (S o).Rel s (W o s)) (𝒜 : Adversary S) :
    𝒜.m.μ (fun ω => ExtractFailure (S _) (fun s _ => W _ s) (𝒜.stmt ω) (𝒜.proof ω)) ≤ 𝒜.failure
```
(containment: extract-failure at a statement WITH a witness contradicts `hW`). ATLAS: satisfying
witness = `evalSystem (f : α → β) P V` with `Stmt := α × β`, `Wit := β`, `Rel s w := f s.1 = w ∧
w = s.2`, `W s := f s.1` — a public deterministic evaluation relation (vFHE shape), at a concrete
`f` on `ZMod 5`; teeth = `canonicalWitness_exists_classically` (with `Nonempty Wit`, `W := choose`
always satisfies `hW` — so the hypothesis has content ONLY under the efficiency reading; the
Ajtai short-opening relation `plainCommitSystem` (AccRbrFold) is the standing relation with no
efficient `W` — remark in the docstring, no hardness claim).

## `err` — delete the twin

Once `KnowledgeSound` carries `ε`, `ProofSystem.err` is a second home for the same number and
was the root of the mis-statement (`err` is uninterpreted; every Prop on it is arithmetic or
false). Remove `err`/`err_nonneg`; `fsProofSystem r s O δ ε hε` → `fsProofSystem r s O δ`;
`accBcsSystem_F5 b O` → `accBcsSystem_F5 O` (the budget `b` moves to the SR class/error);
`accBcsSystem_F5_err` deleted; `verifierRelationSystem A P V` / `canonicalEmbedding A P V` drop
`ε hε`. If the coordinator prefers the smaller AccRbrFold edit, keep `err` and document it as a
label; everything else above is unchanged.

## Succinct file after folding

`fsFamily r s δ := fun O => fsProofSystem r s O δ`; `uniformMeasure Ω : EventMeasure Ω` from
`uniformProb_nonneg/mono/or_le/false` (`Selvage/Depth.lean:72-135`); `srAdversary r s t δ P :
Adversary (fsFamily r s δ)` with coins `(Fin t → r.Chal) × (Fin r.k → r.Chal)`, oracle
`fsOracle o ρs`, run `o.stmt`, `o`; `srClass r s t δ := Set.range (srAdversary r s t δ)`.
**`FsKnowledgeSoundRO r δ εfs` DELETED**, its content is `∀ s t, KnowledgeSound (fsFamily r s δ)
(srClass r s t δ) (εfs s t δ)` (`fsKnowledgeSoundRO_of_fs` becomes `knowledgeSound_of_fs`, same
proof through `uniformProb_mono`). `accBcs_knowledgeSoundRO`, `accBcsSystem_F5_knowledgeSoundRO`
restated at the class. `accBcsSystem_F5_not_knowledgeSound b` → `¬ KnowledgeSound (fun _ : Unit
=> accBcsSystem_F5 oneOracle) Set.univ ε` for every `ε` (fixed oracle, Dirac at `luckySt/luckyOut`).
`knowledgeSound_of_fs_zero`, `carriedFsSystem_knowledgeSound(_of_fs)`, `toySystem_knowledgeSound`
at `(fun _ : Unit => …) Set.univ 0` via `knowledgeSound_univ_iff`. `rung_sound_ro`, `TowerSoundRO`
DELETED (instances of the new `rung_sound`/`ivc_tower_sound`). `carried_rung`, `toy_rung`,
`toy_rung_fired`, `rung_hypothesis_load_bearing`: perfect-form descent, via the univ/0 case.

## ErrorBound file after folding

Section 1 (the four trivial-witness theorems about the OLD `ComposeErrorBound`) DELETED — the
object they audit no longer exists; the note `compose-error-bound.md` is the record. Keep, restated
against the one definition: `flatSystem/flatTarget/flatEmbedding`, `diracMeasure` (now satisfies
`empty`), `composeErrorBound_transfer_load_bearing` (drop `sourceFailure` and the bound is false:
flat rung, mass 1 > 0), `f5_*` tight witness (Dirac adversary against the composed F₅ rung: target
failure 1, source failure 0, composed failure 1 — equality; the number `(3+2)/5 = 1` is the SR
error at budget 3, stated as such) and `composeErrorBound_target_load_bearing` (budget 0: SR error
`2/5`, Dirac mass 1), `trivialSystem`, `composeFixedPoint_trivial_witness`,
`composeFixedPoint_refutable`.

## AccRbrFold edit for the coordinator (I do not touch the file; region 1006-1040)

* `plainCommitSystem` (1011-1018) and `foldSystem` (1025-1034), and the third instance at
  1124-1131: delete the two lines `err := 0` / `err_nonneg := le_refl 0` (only if `err` is removed).
* `plainCommitSystem_knowledgeSound` → statement `KnowledgeSound (fun _ : Unit => plainCommitSystem S β) Set.univ 0`,
  proof `(knowledgeSound_univ_iff _ le_rfl).mpr fun _ _x π h => ⟨π, by classical exact of_decide_eq_true h⟩`.
* `foldSystem_knowledgeSound` → same shape at `foldSystem S Kh chalVal b₀ T`.

## Selvage.lean root comments that go stale

`:141` (HeteroComposition: "[COMPOSE-error] … left as obligation Props" — now closed by
`rung_sound`; `KnowledgeSound` carries an error and a class); `:151` (Succinct: `FsKnowledgeSoundRO`,
`rung_sound_ro`, `TowerSoundRO`, `fsProofSystem r s O δ ε` no longer exist under those names);
`:152` (ErrorBound: `ComposeErrorBoundStrict`, `composeErrorBound_of_err_nonneg` etc. gone; the
strict statement IS `ComposeErrorBound`). Also `docs/FORMAL_STATUS_AND_NEXT_PROOFS.md:44` and
`GOAL.md:48/50`.

## Verification plan (the build-chain trap)

Succinct imports `AccRbrFoldExtract → AccRbrFold → HeteroComposition`; AccRbrFold's two
inhabitants go red the moment `KnowledgeSound` changes shape, so `lake env lean` of Succinct
against fresh oleans is impossible without the coordinator's edit, and `lake env lean` against the
STALE olean proves nothing. Do NOT patch AccRbrFold in place (another lane owns it). Verify via a
git worktree with `.lake/packages` symlinked, `.lake/build` copied (1.3 GB), the AccRbrFold edit
applied THERE, then `lake build Selvage.HeteroCompositionErrorBound` in the worktree.

## Definition count

Before: `KnowledgeSound` (perfect) + `FsKnowledgeSoundRO` + `KsFailure` + `EventMeasure` +
`ComposeErrorBound` (inert) + `ComposeErrorBoundStrict` + `TowerSoundRO` + `composeSystem` +
`ComposeFixedPoint` = 9 across three files, two concepts doubled. After: `KnowledgeSound`,
`KsFailure`, `EventMeasure`, `Adversary`, `composeSystem`/`composeFamily`, `ComposeErrorBound`,
`ComposeFixedPoint`, `ExtractFailure` = 8, one per concept, all in `HeteroComposition.lean`.
