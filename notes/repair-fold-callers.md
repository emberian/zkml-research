# Repair: the four `FoldRoundBound`-parametric callers are retired

Lane record, 2026-09-05. Follow-up to `fold-extractor-upgrade.md` (commit
`8041a7e`): that lane proved `FoldRoundBound … extractFn ε` forces `1 ≤ ε δ`
for every extractor (`foldRoundBound_floor`) and landed the true object
(`foldReductionCarried`, error 0) BESIDE the four callers it refuted. This
lane does the replacement half: the tree consumes the carried object, the
vacuous callers are deleted, the docstrings say the current truth.

## 1. Consumer census (written before any edit)

Grep: `foldRbrOfRoundBound\|fold_depth_composition\|fold_fs_sound\|fold_fs_price_msis\|FoldRoundBound`
over `*.lean *.md *.sh *.py`, excluding `.lake/` and `vendor/`.

| caller | consumers (code) | consumers (docstring / prose) |
|---|---|---|
| `foldRbrOfRoundBound` (def, `AccRbrFold.lean:581`) | `fold_depth_composition`, `fold_fs_sound` (in-file, parametric pass-through); `foldOB2Unguarded_false` (`:711`) at `zeroFoldScheme`, identity extractor, `εfold ≡ 1` via `foldRoundBound_one` | `AccRbrFold.lean:50`, `:553`; `AccRbrFoldExtract.lean:66`; `Selvage.lean:142` (root comment); `GOAL.md` (log) |
| `fold_depth_composition` (thm, `:608`, pinned `:1420`) | none | `AccRbrFold.lean:60`, `:706`; `AccRbrFoldExtract.lean:404`; `Selvage.lean:142` |
| `fold_fs_sound` (thm, `:622`, pinned `:1422`) | `fold_fs_price_msis` (in-file) | `AccRbrFold.lean:60`; `AccRbrFoldExtract.lean:418`; `Selvage.lean:142` |
| `fold_fs_price_msis` (thm, `:639`, pinned `:1424`) | none | `AccRbrFold.lean:64`; `Selvage.lean:142` |

`extractFn` / `h` ever passed: ONLY `fun _ _ Y => Y` at `fun _ => 1` with
`foldRoundBound_one` (the `foldOB2Unguarded_false` corner). No consumer ever
supplied a round bound below `ε ≡ 1` — consistent with the floor: none exists.

Outside `Selvage/`: `Assurance/`, `Compiler/`, `Kernel/`, `Pred/`, `Theory/`
— zero hits for any of the five names. Importers of `AccRbrFold`:
`Selvage.lean`, `Selvage/AccRbrFoldExtract.lean`,
`Selvage/HeteroCompositionSuccinct.lean` (imports `AccRbrFoldExtract`, and
already consumes the TRUE objects: `foldReductionCarried`, `foldCarriedRbr`,
`foldCarried_fs_sound`, `foldExtract_state` — never the four callers).

VerifierEmbedding (AccRbrFold's "consumer wired three ways":
`foldZeroToPlain` `:1084`, `plainToFoldZero` `:1109`,
`foldSystem_one_iff_plain` `:1137`, and the fail-open IsEmpty theorem
`ToyFold.dropped_norm_check_refuses_embedding` `:1331`): none reads any of
the four callers or `FoldRoundBound`. Nothing to re-wire; they must simply
survive elaboration.

`FoldRoundBound`-parametric theorems/defs before: 4 (the callers) + the
pair (`foldRoundBound_one` satisfiable, `foldRoundBound_floor` refutation) +
instances of the pair (`ToyFold.toy_roundBound_zero_id_false`,
`ToyFold.toy_roundBound_floor`, `DualModeParams.production_roundBound_floor`).

## 2. Decisions

* `fold_depth_composition`, `fold_fs_sound`, `fold_fs_price_msis`: no
  consumer beyond each other → DELETE, with their three pins (deliberate;
  listed in §4). Role → `foldCarried_depth_composition` /
  `foldCarried_fs_sound` (`AccRbrFoldExtract.lean`, error 0, no extractor
  parameter). `fold_fs_price_msis`'s "Nebula `Q·ε_MSIS` split" has NO carried
  analog because the carried round bound has no `ε_MSIS` term: that
  accounting belongs to the decider (binding of each opened commitment,
  `fold_binding` at the doubled budget), not to Def 4.2 — the docstring
  rewrite says so.
* `foldRbrOfRoundBound`: its one real consumer is `foldOB2Unguarded_false`,
  which needs SOME `RbrKnowledgeSoundness (foldReduction zeroFoldScheme …)`
  witness for the `Z = ∅` error-algebra corner. The witness it used is the
  trivial `ε ≡ 1` instance — by the floor the only kind the compressing fold
  has at a binding instance. Re-point: the five-field instance is built
  INLINE in that proof (`foldKState` + identity extractor + `err ≡ 1` +
  `foldRoundBound_one`), then `foldRbrOfRoundBound` is DELETED. No new named
  object: the trivial instance appears exactly where it is used, once.
  `FoldOB2Unguarded`'s statement (over `foldReduction`, all `rbr`) is
  unchanged.
* `FoldRoundBound` (the Prop) STAYS, docstring rewritten: refuted below
  `ε = 1` for every extractor; pair = `foldRoundBound_one` (tight) +
  `foldRoundBound_floor`; the `ε_MSIS` home it was said to be does not exist
  in the single-transcript model.
* `ToyFold.toy_roundBound_zero_id_false` (id extractor, `b₀ = 0`) is kept —
  outside this brief's four — but its docstring now says
  `toy_roundBound_floor` (every extractor, `b₀ = 1`) subsumes it. Candidate
  for a later deletion; flagged, not done.

## 3. Deleted (names) — `Selvage/AccRbrFold.lean`

* `foldRbrOfRoundBound` (def) — the `extractFn`-generic Def-4.2 packaging.
* `fold_depth_composition` (theorem + its `#guard_msgs` pin).
* `fold_fs_sound` (theorem + pin).
* `fold_fs_price_msis` (theorem + pin).
* The section header `/-! ### The depth composition for the fold shape —
  PROVED, riding [OB-2′] -/` → a 7-line signpost to the carried compositions.

Tree-wide grep afterwards (`*.lean *.md *.sh`, excluding `.lake/`,
`vendor/`): ONE hit, `Selvage.lean:142` — the root import comment, outside
this lane's touch list (§8). `GOAL.md` names none of the four.

## 4. Re-pointed (from → to)

* `foldOB2Unguarded_false`'s Def-4.2 witness:
  `foldRbrOfRoundBound zeroFoldScheme … (fun _ _ Y => Y) (fun _ => 1)
  (foldRoundBound_one …)` → the same five fields built INLINE at that one
  use (`kstate := foldKState …`, identity `extract`, `err ≡ 1`,
  `extractTime := 0`, `extract_sound := foldRoundBound_one … δ hδ st i rs
  hlen π`). Pin retained, footprint unchanged
  `[propext, Classical.choice, Quot.sound]`.
* Docstring citations, `AccRbrFold.lean`: header `:47–64`
  (`foldRbrOfRoundBound` "ONLY missing piece" → `foldRoundBound_floor`;
  `fold_depth_composition`/`fold_fs_sound` → `foldCarried_depth_composition`
  / `foldCarried_fs_sound`; `fold_fs_price_msis`'s `Q·ε_MSIS` split → the
  decider's `fold_binding` per opened commitment); `foldOB2Unguarded_false`
  docstring (`fold_depth_composition` → `foldCarried_depth_composition`);
  `foldRoundBound_one` docstring (now says TIGHT by the floor);
  `ToyFold.toy_roundBound_zero_id_false` docstring (now says subsumed by
  `toy_roundBound_floor`).
* Docstring citations, `AccRbrFoldExtract.lean`: header keystone pair
  (`one` + `toy_roundBound_zero_id_false` → `one` + `foldRoundBound_floor`);
  the "four callers remain caller-conditional" bullet → "retired; the
  compositions live here"; `foldCarried_depth_composition` /
  `foldCarried_fs_sound` docstrings ("the fold analog of `fold_*`" → "THE
  depth / FS composition for the fold shape").

## 5. The `:549` docstring (now `:558`), rewritten

Was: "the ONLY missing piece of a full `RbrKnowledgeSoundness` instance …
where the per-absorbed-commitment ε_MSIS term lives"; teeth =
`toy_roundBound_zero_id_false`. Now: the round bound at the COMPRESSING
witness type, statement-first and REFUTED below error 1 — NOT where an
ε_MSIS term lives, no such home exists in the single-transcript model
(`foldRoundBound_floor`, zero-absorb); nothing in the tree consumes an
inhabitant below `ε ≡ 1`, the one use is the trivial instance in
`foldOB2Unguarded_false`; the Def-4.2 instance that exists is
`foldCarriedRbr` at `foldReductionCarried` (price: relaxed source relation
`budget b₀ (2T)`, capacity halved to `T ≤ 2^46 − 1`); the ε_MSIS accounting
is the decider's `fold_binding`. ATLAS fields: satisfiable
`foldRoundBound_one` (TIGHT); teeth `foldRoundBound_floor`, discharged at
`ToyFold.toy_roundBound_floor` and `DualModeParams.production_roundBound_floor`
(`toy_roundBound_zero_id_false` = the id-extractor special case at
`b₀ = 0`, subsumed); premise-inhabitation unchanged.

## 6. Scope narrowing (coordinator addition, external review)

`AccRbrFoldExtract.lean` "Honest scope" bullet 1 said "knowledge soundness
of the additive fold costs exactly the compression; rewinding buys it back".
Stronger than the attack establishes: the zero-absorb attack refutes a
contract that admits an already-invalid genesis opening and asks a
challenge-dependent step to certify the missing shortness (the challenge
space is irrelevant to it); the `T + 1`-openings conclusion is a statement
about the PUBLIC-TRANSCRIPT-ONLY extractor. Rewritten to name the three
resource models and confine the claim to (i): (i) public-transcript-only
(what the verifier sees — what `RbrKnowledgeSoundness` and the `(t+k)·ε`
compositions model); (ii) straight-line with a trapdoor / RO-query
interface / prescribed prover access; (iii) online (extract each incoming
witness, update a running state, discard — live extractor memory, total
extraction work, output size, decider work are four quantities). "Routes not
in this tree: (ii), (iii), and rewinding." The `T + 1` theorem is unchanged
(right in model (i)). No citations added as claims.

The same sentence survives, verbatim, at `Selvage.lean:144` (root import
comment: "knowledge soundness costs exactly the compression in the
single-transcript Def-4.2 model, and rewinding buys it back") — outside this
lane's touch list; and in spirit in `fold-extractor-upgrade.md`'s verdict
(another lane's record; erratum here rather than an edit there).

## 7. Counts

`FoldRoundBound`-parametric declarations (`h : FoldRoundBound …` consumed,
or `FoldRoundBound …` concluded):
* before: 4 callers + pair (`foldRoundBound_one`, `foldRoundBound_floor`) +
  3 instances (`toy_roundBound_zero_id_false`, `toy_roundBound_floor`,
  `production_roundBound_floor`) = 9.
* after: **0 callers**; the Prop, its pair, and the 3 instances remain = 5.

Pins: `AccRbrFold.lean` 16 → 13 (the three deleted theorems' pins, removed
deliberately with their objects); `AccRbrFoldExtract.lean` 9 → 9; every
remaining footprint unchanged. `AccRbrFold.lean` 1448 → 1409 lines;
`AccRbrFoldExtract.lean` 634 → 649.

## 8. Residuals outside this lane's touch list (for the orchestrator)

* `Selvage.lean:142` still says "the Def 4.2 round bound is statement-first
  (FoldRoundBound — satisfiable at ε≡1, REFUTED at ε≡0/id on the toy, the
  per-absorbed-commitment ε_MSIS home; … single-transcript pricing open)"
  and "Depth/FS composition PROVED … (fold_depth_composition, fold_fs_sound,
  the Q·ε_MSIS split fold_fs_price_msis)". Proposed: "the Def 4.2 round
  bound is statement-first (FoldRoundBound — satisfiable at ε≡1 and TIGHT
  there: foldRoundBound_floor refutes it below 1 for every extractor, so it
  is no ε_MSIS home; [ACC-rbr-fold-resid](a) RESOLVED at the carried fold,
  AccRbrFoldExtract). Depth/FS composition PROVED at the carried fold at
  error 0 (foldCarried_depth_composition, foldCarried_fs_sound); the
  Q·ε_MSIS accounting is the decider's fold_binding per opened commitment,
  not a round-bound term".
* `Selvage.lean:144`: the "costs exactly the compression … rewinding buys it
  back" sentence needs the §6 model-(i) narrowing.
* `Selvage/HeteroCompositionSuccinct.lean:43` cites `AccRbrFold.lean:1073`,
  `:1078` (`plainCommitSystem_knowledgeSound`, `foldSystem_knowledgeSound`);
  after this lane's deletions they are at `:1036`, `:1040`.
* `ToyFold.toy_roundBound_zero_id_false` (+ pin) is subsumed by
  `toy_roundBound_floor`; candidate deletion, not in this brief.

## 9. Files and status

Touched (NOT committed):
* `/Users/ember/dev/minidregg/Selvage/AccRbrFold.lean`
* `/Users/ember/dev/minidregg/Selvage/AccRbrFoldExtract.lean`
* `/Users/ember/dev/zkml-research/notes/repair-fold-callers.md` (this note)

Elaboration: `lake env lean` on both files, exit 0 (all 22 remaining pins
pass). `lake build Selvage.AccRbrFold Selvage.AccRbrFoldExtract
Selvage.HeteroCompositionSuccinct` (pgrep empty first): Build completed
successfully, the three modules rebuilt, no warnings from them.
`scripts/check-import-boundary.sh` OK; `scripts/check-proof-hygiene.sh` PASS
(274 guarded footprints). VerifierEmbedding (`foldZeroToPlain`,
`plainToFoldZero`, `foldSystem_one_iff_plain`,
`ToyFold.dropped_norm_check_refuses_embedding`) consumed none of the four;
untouched, pins pass.
