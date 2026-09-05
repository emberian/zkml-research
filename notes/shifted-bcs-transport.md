# Census upgrade 5 — `accRbrKnowledgeSoundBcsShifted`: retired, with the floor proved

**Lane note, 2026-09-05.** Unit: `unit-witness-census.md` §7 item 5. Tree: `~/dev/minidregg`
(branch `main`, on top of `658bacb`). Nothing committed; file list at the bottom.

## The two types, verbatim

**The demand** — `Selvage/AccRbrBcsShifted.lean:369` (the Prop at `:374`):

```lean
def accRbrKnowledgeSoundBcsShifted (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) (εfold : ℝ → ℝ) : Prop :=
  ∃ rbr : RbrKnowledgeSoundness
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q),
    (∀ (δ : ℝ) (st : Stmt (accReductionBcsShifted …))
        (tr : Transcript (BcsMsg Root' F Op t) F) (w : Fin ch.length → Fin m → F),
        rbr.kstate.state δ st tr w = true → ColsConsistent S q tr.rounds) ∧
    ∀ (i : Fin (ch.length + 1)) (st : Stmt (accReductionBcsShifted …)),
      ∀ δ ∈ Set.Ioo (0 : ℝ) δs, rbr.err i st δ ≤ εfold δ
```

`RbrKnowledgeSoundness` (`Selvage/Rbr.lean:281`) is WARP Def 4.2: a Def-4.1 `KStateFn`
(`empty_iff` / `prover_monotone` / `full_iff`), a deterministic round extractor
`Stmt → Transcript → W → W`, per-round errors `err : Fin k → Stmt → ℝ → ℝ`, and the round
bound `extract_sound`: for every `δ`, statement, round `i`, prefix `rs` of length `i` and
pending message `π`, `uniformProb Chal (fun ρ => ∃ w, state(rs,π; extract(rs++[(π,ρ)], w)) =
false ∧ state(rs++[(π,ρ)]; w) = true) ≤ err i st δ`. Oracle-free; quantifies over ALL
prefixes and ALL statements. The reduction is the UNLINKED shifted one
(`AccRbrBcsShifted.lean:214`): its verifier checks every opening and the genesis anchor and
outputs `(aggregate, bcsWord (last message))` — nothing ties consecutive roots.

**The supply** — `Selvage/OracleLogLinkedAssembly.lean:461`:

```lean
theorem linkedAdaptiveIncrementSound_proved
    {dC : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδsC : δs ≤ dC / 2)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) :
    LinkedAdaptiveIncrementSound C foldRoot ch hm hch δs hδpos hδone S dom d q wv errstar
```

with (`OracleLogLinkedTarget.lean:167`)

```lean
def LinkedAdaptiveIncrementSound (errstar : ℝ → ℝ) : Prop :=
  ∃ olr : OracleLogReduction
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)   -- = accReductionBcsShiftedLinked … wv
      (linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (accRbrError F errstar),
    ∀ s, olr.extractLog s = linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv s
```

An `OracleLogReduction` (`OracleLogExtraction.lean:206`) is a ROM-game object: a
log-only straightline extractor, and `sound_log` bounding, for every SR prover, the
probability over the game's coins of `(stmt ∈ Z ∧ extractor fails ∧ accept-with-R'_{≤δ})`
by `(t + k)·ε`. The reduction is the LINKED one (`OracleLogLinked.lean:430`: verifier
grown by `LinkOpened S q (S.commit (wv i)) (πs i.castSucc) (πs i.succ) (ρs i.castSucc)`
against a designated family `wv`); the statement set asserts `wv` witnesses every link.

## Decision: RETIRE — and the reason is a theorem, not a mismatch

The three structural mismatches (different `Reduction`; ROM-game vs per-round oracle-free
error; restricted statement set vs all statements) would each block a transport. But the
honest finding is sharper: **the demand is FALSE below error one**, at every instance with
a witness-less statement whose aggregate is always solvable — so there is nothing to
transport INTO. The unlinked shifted verifier never reads a relation between consecutive
roots; a prover that anchors the genesis word, commits anything in between, and commits a
word solving the aggregate as its LAST message is accepted with a satisfied output at
every challenge vector. Def 4.2's chain then forces the knowledge state true at every
prefix of that run down to the empty transcript, where `empty_iff` pins it to `R_{≤δ}` —
which the statement lacks. So some round error is `≥ 1` for EVERY state and EVERY
extractor. This is the Def-4.2 twin of `adaptiveViaLog_accRbrError_false`
(`OracleLogProgram.lean`), which killed the same verifier in the ROM game and led to the
linked reduction. The linked log route is not a "transport source"; it is the corrected
statement, and it supersedes.

The object's own docstring said its teeth were "any `εfold < 1` rules out the DEGENERATE
state". The floor says it rules out every state — the original residual (a) ("a genuinely
new round bound for the adaptive fold-satisfiability event") could not have closed at this
verifier.

## Statements landed — `Selvage/AccRbrBcsShiftedTransport.lean` (new, 805 lines)

Elaborates clean single-file (`lake env lean`: 0 errors, 0 warnings, all eleven
`#guard_msgs` axiom pins matched at `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no `axiom`). Import: `Selvage.OracleLogLinkedAssembly` only; boundary script green.

| decl | what |
|---|---|
| `DegenerateStateProp`, `degenerateKState (r : Reduction)` | the Def-4.1 state exact at the two pinned ends, false elsewhere — all three clauses proved for EVERY reduction |
| `degenerateRbr r : RbrKnowledgeSoundness r` | every reduction is Def-4.2 sound at error `1` (identity extractor, `uniformProb_le_one`) |
| `accRbrKnowledgeSoundBcsShifted_one` | **satisfiable pole**: the shifted object at `εfold ≡ 1`, column clause met (state true only on empty or accepted-full transcripts) |
| `commitMsg` (+`_opens`, `_word`) | honest commitment message of a word at the BCS alphabet, general |
| `untetheredMsg`, `untetheredRounds` (+`_length`, `_local`, `_update`, `_ofFn`) | the untethered adversary: level 0 anchors `f₀`, last level commits the solver's word at the fold challenges, else zero; level `c` reads the schedule only below `c` |
| `untethered_verify` | the unlinked shifted verifier accepts the untethered run at EVERY schedule, output `(aggregate, z γ)` |
| **`shiftedRbr_floor`** | for every `rbr : RbrKnowledgeSoundness (accReductionBcsShifted …)`, `δ` on the window, statement with no `R_{≤δ}` witness, and solver `z` (RS codeword satisfying the aggregate at every schedule): `∃ i, 1 ≤ rbr.err i st δ` |
| **`accRbrKnowledgeSoundBcsShifted_forces_one`** | the Prop forces `1 ≤ εfold δ` |
| `accRbrKnowledgeSoundBcsShiftedLinked` | **named obligation** `[ACC-rbr-bcs-shifted-linked]`: the same shape at the LINKED reduction, ATLAS-fielded |
| `accRbrKnowledgeSoundBcsShiftedLinked_one` | its satisfiable pole at `εfold ≡ 1` |
| `not_of_uniformProb_le_zero` | a `≤ 0` uniform probability has an empty event (contrapositive of `AccRbrFold.uniformProb_pos_of_witness`, which is outside this import cone — owner to hoist both into `Depth.lean`) |
| `rbr_chain_of_err_zero` | at round errors `≤ 0` the Def-4.2 chain is deterministic: alive at any prefix ⇒ alive at the empty transcript |
| F₅: `farGenesis` (`q2 = 3`), `farSt`, `farSt_no_witness` (`δ < 1/4`), `farZ γv := (3 + γv 1) • 1⃗`, `farZ_solves` | the floor's premises, discharged on the landed chain |
| **`shifted_forces_one_F5`**, **`shifted_accRbrError_false_F5`** | any admissible `εfold ≥ 1` on the whole window; the intended price `1/5` is FALSE |
| **`shifted_retired_log_stands_F5`** | the ledger sentence as a theorem: unlinked Def-4.2 dead below `1` ∧ `LinkedAdaptiveIncrementSound … msEx (fun _ => 0)` (cites `linkedAdaptiveIncrementSound_F5`) |
| `linkedOnes_F5`, `farStLinked`, `farFold_satisfies_ones` (kernel `decide`), **`linked_zero_false_F5`** | **teeth for the linked obligation**: at the all-ones designation `εfold ≡ 0` is FALSE — the all-ones schedule folds `xWord + 1⃗ + 1⃗` onto the witness-less aggregate `q2 = 4` exactly, and a zero-error chain would manufacture a witness |

ATLAS pairs: retired object — `_one` (satisfiable) / `_forces_one` + `_F5` (teeth, tight);
linked obligation — `_Linked_one` (satisfiable) / `linked_zero_false_F5` (teeth) /
`accReductionBcsShiftedLinked_F5` + `linked_completeness_F5` (premise, cited).

## What is NOT closed

`[ACC-rbr-bcs-shifted-linked]` at `accRbrError`: the shifted state design (old residual (b))
at the linked reduction — the oracle-free per-round object whose inhabitant would let
`OB2_depth_composition_nonneg_proved` / `fsKeystone_proved` price the deployed-ZK shape
instead of the bespoke `(t + k)` assembly. Named, fielded, open. The floor does NOT go
through at the linked verifier (the last word is forced by `LinkOpened`), which is exactly
why the linked object is the right home.

## Ledger amendment

`Selvage/AccRbrBcsShifted.lean` `## Ledger`, the `accRbrKnowledgeSoundBcsShifted` bullet
(was `:550-552`): now says RETIRED with the floor pair, the untethered reason, that the
log route at the linked reduction SUPERSEDES it, that residual (a) is answered negatively as
stated and (b) re-homed as `accRbrKnowledgeSoundBcsShiftedLinked`. Docstring-only edit
inside the `/-! -/` block; the file re-elaborates clean.

## Owner actions

* `Selvage.lean` is out of my touch list: add `import Selvage.AccRbrBcsShiftedTransport`
  (and, if desired, update the `:59` one-liner that still says "NOT inhabited"). Until
  then the umbrella does not compile the new file.
* Hoist `not_of_uniformProb_le_zero` / `AccRbrFold.uniformProb_pos_of_witness` into
  `Depth.lean` beside `uniformProb_false`.
* Census §7 item 5 can be marked: resolved by retirement; the `H`-class row for
  `AccRbrBcsShifted.lean:374` becomes "refuted below 1, satisfiable at 1".

## Exact file list

* NEW `~/dev/minidregg/Selvage/AccRbrBcsShiftedTransport.lean`
* MODIFIED (docstring only, the `## Ledger` bullet) `~/dev/minidregg/Selvage/AccRbrBcsShifted.lean`
* NEW `~/dev/zkml-research/notes/shifted-bcs-transport.md` (this note)

Not committed. No `git stash`, no `git add -A`.
