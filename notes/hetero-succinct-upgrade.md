# Census upgrade 4 — `HeteroComposition.KnowledgeSound` at a system whose proof is not the witness

**Lane note, 2026-09-05.** Unit: `unit-witness-census.md` §7 item 4. Tree: `~/dev/minidregg`
main at `c604944` (Selvage/ clean; `AccRbrFoldExtract.lean` at `8041a7e`). One NEW file,
`Selvage/HeteroCompositionSuccinct.lean` (832 lines), `lake env lean` clean — 0 errors,
0 warnings, 17 `#guard_msgs`-pinned `#print axioms`, all `[propext, Classical.choice,
Quot.sound]`. No `sorry`, no `axiom`. `scripts/check-import-boundary.sh` OK. Targeted
`lake build` NOT run: another lane held `lake build Compiler.CommittedTerminalFactored7` for
the whole session (`pgrep` gate). Nothing committed.

## The structure, quoted (`Selvage/HeteroComposition.lean:50-61`)

```lean
structure ProofSystem where
  Stmt : Type
  Wit : Type
  Proof : Type
  Rel : Stmt → Wit → Prop
  Verify : Stmt → Proof → Bool
  /-- knowledge-soundness error. -/
  err : ℝ
  err_nonneg : 0 ≤ err

def KnowledgeSound (S : ProofSystem) : Prop :=
  ∀ x π, S.Verify x π = true → ∃ w, S.Rel x w
```

`KnowledgeSound` is **perfect** — every accepting proof has a witness — and reads no error.
In `HeteroComposition.lean` the `err` field is read by the obligation `ComposeErrorBound`
(`:235`) and by no theorem. `accFsSound_bcs` (`AccRbrBcs.lean:748`) is a counting bound:
`Pr[accept ∧ extractor fails] ≤ (t + k)·accRbrError`, `= (t + 2)/5` at F₅. The two meet
only at error zero. That is the finding; the file is organized around it.

## The census's statement change, built — and refuted

`fsProofSystem r s O δ ε hε : ProofSystem` (generic, every `Reduction`, every oracle):

```lean
  Stmt := Stmt r
  Wit := r.W
  Proof := SrOutput r s
  Rel := fun x w => RelaxedMem r.R δ x.idx x.x x.y w
  Verify := fun x o => decide (FsAccepts r s O δ x o)
  err := ε
```

with `FsAccepts r s O δ x o := o.stmt = x ∧ ∃ x' y', fiatShamir r s O o = some (x', y') ∧
RelaxedMem r.R' δ x.idx x' y' o.w'` — Def B.2's acceptance event (FS verifier accepts AND the
decider accepts the carried `w'`). Deviation from the census, stated: `Rel` is the δ-relaxed
`R_{≤δ}`, which is what the extractor lands in; `Rel := r.R` is its δ-free fibre and
coincides with it when the proximity alphabet is a subsingleton (`carriedFsSystem_rel_iff`).

`accBcsProofSystem … (b s : ℕ) O := fsProofSystem (accReductionBcs …) s O δ ((b + ch.length)
· accRbrError F errstar δ) _` — the census's system, `err` = the number `accFsSound_bcs`
proves at query budget `b`. F₅: `AccRbrBcsExample.accBcsSystem_F5 b O`, `δ = 1/32`,
`err = (b + 2)·(1/5)` (`accBcsSystem_F5_err`).

| keystone | status |
|---|---|
| `honest_accepted` — `bcs_state_alive`'s honest committed transcript accepted at `oneOracle` (`γbase = (1,1)`) | PROVED |
| `badOut_rejected` — columns that do not open ⇒ `Verify = false` | PROVED |
| `accBcsSystem_F5_knowledgeSoundRO` — ROM-game knowledge soundness at `(b+2)/5` from `bcs_fs_fired` | PROVED |
| `accBcsSystem_F5_not_knowledgeSound b : ¬ KnowledgeSound (accBcsSystem_F5 b oneOracle)` | **PROVED — the census's target is FALSE** |

The refutation: genesis `luckyGenesis := ⟨0, fun _ => (q2, 3)⟩` on `xWord` (`q2 xWord = 2`,
so `R`'s first conjunct fails for EVERY `w`; `R_{≤1/32}` cannot move `xWord` —
`eq_of_fracHamming_lt_inv`), proof string = `oneWord` honestly committed in both rounds;
at `oneOracle` the fold `xWord + oneWord + oneWord` evaluates to `4` = the folded target
`3 + 1·0 + 1·1` (`lucky_fold_satisfies`, by `decide`). Same oracle accepts the honest
transcript. This is `accRbrError`'s `1/|F|` event surfacing at the `ProofSystem` seam.

Why the census's route cannot fire (`accBcs_fs_error_ne_zero`): the bridge
`knowledgeSound_of_fs_zero` needs `εfs s 0 δ = 0`; here it is `2/5`.

## What closed (proved)

* `knowledgeSound_of_fs_zero` — **the bridge**: `FsStraightlineKnowledgeSoundness r univ εfs`
  with `εfs s 0 δ = 0` ⇒ `KnowledgeSound (fsProofSystem r s O δ ε hε)` at every `O`. Proof:
  the 0-move `constProver`, `uniformProb_pos_of_witness`, `fiatShamir_congr`.
* `FsKnowledgeSoundRO r δ εfs` — the positive-error statement that IS true: for every SR
  prover, `Pr[FsAccepts at the game's oracle ∧ ¬∃ w, R_{≤δ}] ≤ εfs s t δ`; equals
  `Pr[KsFailure (fsProofSystem r s (fsOracle o ρs) δ …) o.stmt o]` (`ksFailure_fs_iff`).
  `fsKnowledgeSoundRO_of_fs` from any FS-straightline statement; `accBcs_knowledgeSoundRO`
  at the generic acc system under `accFsSound_bcs`'s hypotheses.
* `rung_sound_ro` — the rung at positive error for oracle-uniform embedding families: via
  `bwd`, `Pr[accept ∧ the embedded A-statement has no accepting A-proof] ≤ εfs`.
* `carriedFsSystem S T hT Kh chalVal b₀ s O` — `fsProofSystem` at
  `AccRbrFoldExtract.foldReductionCarried`, `err = 0`. `KnowledgeSound` PROVED two ways:
  `carriedFsSystem_knowledgeSound_of_fs` (the bridge on `foldCarried_fs_sound`) and
  `carriedFsSystem_knowledgeSound` from **`carried_srExtract_sound`** — the NAMED extractor
  `srExtract (foldCarriedRbr …)` (Construction B.5 on the un-fold) outputs a
  `budget b₀ (2T)`-short genesis opening on every accepting proof string; deterministic,
  through `wAt_carried_state` (`foldExtract_state` iterated). `Proof = SrOutput ≠ Wit` by
  type; `ToyFold.toy_srExtract_ne_id` shows the extractor changes the carried witness
  (`(e₀, e₀) ↦ (0, e₀)`). Toy keystones: `toy_honest_accepted`, `toy_bad_rejected`.

## The consumer gained

`relDecider B` (the decider of `B`'s relation; the shape of both existing inhabitants) and
`relDeciderEmbedding B : VerifierEmbedding (relDecider B) B` (identity carrier, `decide`'s two
directions). **`carried_rung`** = `rung_sound (relDeciderEmbedding _)
(carriedFsSystem_knowledgeSound …)`; **`ToyFold.toy_rung`** / `toy_rung_fired` at the toy.
First application of `rung_sound` whose `hB` is a theorem about an extractor, not
`fun _ π h => ⟨π, …⟩`. Honest scope: the embedding is the identity carrier
(`canonicalEmbedding`'s shape); the content is `hB`.

Falsifier for the rung: `AccRbrBcsExample.rung_hypothesis_load_bearing b` — at
`accBcsSystem_F5 b oneOracle` the accepted `luckyOut` has NO `relDecider`-proof, so the
rung's conclusion is false there; `hB` is load-bearing and cannot be supplied
(`accBcsSystem_F5_not_knowledgeSound`).

## Named, not closed

* `[HETERO-succinct]` — a succinct `KnowledgeSound` inhabitant. Refuted at every positive
  error; the error-zero inhabitant with a real extractor carries `T + 1` openings
  (`AccRbrFoldExtract`'s scope note). Open.
* `[HETERO-err-tower]` — `TowerSoundRO` (a `Prop`, ATLAS fields in its docstring):
  `ivc_tower_sound` at positive error. `n = 1` has `rung_sound_ro`'s shape; `n ≥ 2` is not a
  union bound — `bwd` returns an existential, not an adversary the SR game prices. This is
  the extractor-efficiency clause of IVC, named. Open.
* `HeteroComposition.KnowledgeSound` itself: to consume any positive-error argument it must
  read `err` and quantify over the oracle (the `FsKnowledgeSoundRO` shape). Not modified
  (file boundary). Also noticed, not acted on: `ComposeErrorBound` (`:230`) is provable
  from `err_nonneg` alone — `∀ ε, ε = A.err + B.err → 0 ≤ ε` — its content is nil.

## File list

* NEW `~/dev/minidregg/Selvage/HeteroCompositionSuccinct.lean` (not committed, not added to
  `Selvage.lean` — the umbrella import line is the orchestrator's call).
* NEW `~/dev/zkml-research/notes/hetero-succinct-upgrade.md` (this note).
* Nothing else touched.
