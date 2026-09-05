# Repair — the `basefoldTableRbr` / `basefoldTableRbrAllQueries` twin, resolved by proof

**2026-09-05**, minidregg `main` (on top of `60f0499`), lane: repair-table-twin. Brief: Selvage.lean:150's
"TWIN QUESTION" — two `RbrKnowledgeSoundness` instances of the SAME reduction with different hypotheses.
Decide by theorem which supersedes; ATLAS "delete the twin".

## Checkpoint status (usage wall hit mid-lane)

| file | status |
|---|---|
| `Selvage/BaseFoldRbrTable.lean` | **UNTOUCHED, at HEAD, green.** |
| `Selvage/BaseFoldRbrTableDescent.lean` | **UNTOUCHED, at HEAD, green.** |
| `Assurance/SpartanR1CS.lean` | **UNTOUCHED, at HEAD, green** — and needs NO edit (see consumers). |
| `notes/repair-table-twin-edit_table.py` | the prepared, **unrun, unelaborated** edit script for `BaseFoldRbrTable.lean` (line-range splices with anchor assertions + string replacements with count assertions). Every new theorem below is in it verbatim. |

Nothing committed; the umbrella is unaffected. The decision below is final and justified; the Lean is drafted,
not elaborated. The next session runs the script, elaborates, then does the Descent-file deletions listed at
the end.

## The two statements (copied)

```lean
-- Selvage/BaseFoldRbrTable.lean:456  (a77779a)
noncomputable def basefoldTableRbr (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate := basefoldTableKState hm S dom q
  extract := fun _st tr w => tableExtract dom m q tr w   -- = extractTable dom m q (last msg).cols
  err := fun _i _st _δ => (2 : ℝ) / Fintype.card F
  extractTime := fun _ => 0
  extract_sound := ...  -- alive at tr‖ρ ⇒ columns verify ⇒ extractTable π.cols = w (binding) ⇒ scalar event

-- Selvage/BaseFoldRbrTableDescent.lean:396  (2dcd284)
noncomputable def basefoldTableRbrAllQueries (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate := basefoldTableKState hm S dom q
  extract := fun _st _tr w => w
  err := fun _i _st _δ => (2 : ℝ) / Fintype.card F
  extractTime := fun _ => 0
  extract_sound := ...  -- alive at tr‖ρ ⇒ rt commits w ⇒ w = the unique table (window) ⇒ scalar event
```

Same `kstate`, same `err`, same `extractTime`; they differ ONLY in `extract`. Consumers' FS conclusions
(`basefoldTable_fs_sound` vs `_allQueries`, `_fs_holds` vs `_allQueries`) are the identical `Prop` modulo
hypotheses — `FsStraightlineKnowledgeSoundness` is `∃ E, …`, so the extractor is invisible there.

## The decision: MERGE (option a), with the identity extractor — not a case split

**Theorem that decides it** (`roundBad_extractTable_iff`, drafted): at `2^m ≤ t`, `dom ∘ q` injective,
```lean
(∃ w, kstate.state δ st ⟨rs, some π⟩ (extractTable dom m q π.cols) = false ∧
      kstate.state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true)
  ↔ RoundBad (basefoldTableRbr hm S dom q hcard) δ st rs π ρ          -- the identity instance
```
Proof: a witness alive at `tr‖ρ` has its columns verified against a root committing it, so
`extractTable dom m q π.cols = w` (`extractTable_of_alive` := `extractTable_committed` on the alive
state's `hcols`/`hrt`). Def 4.2 measures an extractor ONLY on the alive set (the event is
`∃ w, dead(extract(tr‖ρ, w)) ∧ alive(w)`), and there the two extractors are pointwise equal. Two extractors
with literally the same round events are one Def-4.2 object; the identity is the one with no hypotheses.
Corollary `extractTable_round_bound`: the column instance's `extract_sound` bound (`≤ 2/|F|`) from the
identity instance's `extract_sound` + the iff — so `basefoldTableRbr`-hypotheses ⇒ AllQueries conclusion is
trivial (subset of hypotheses), and the CONVERSE restricted to `2^m ≤ t` is this corollary. Nothing is lost
at the `RbrKnowledgeSoundness` level.

**Why identity, not the brief's case split** (`extractTable` where `2^m ≤ 2t`, identity otherwise): the
case-split extractor agrees with the identity on the alive set too, so it has ZERO additional Prop content
in Def 4.2 — it is more data proving the same thing, and it cannot even be typed against the reduction's
alphabet (`descentExtract` reads `FriQueryOpening` at `pairQuery`, a `t+t`-column message on a different
query map, not this reduction's `TableMsg F Op t` at `q`). Fewer objects: one instance, identity.

**Why the identity is honest Def-4.2 knowledge soundness and not a lie**: the reduction carries its witness
UNCHANGED — `W' = W = (Fin m → Bool) → F`, `R'` re-pins the same root `out.rt = S.commit (basefoldWord dom
tbl)`. For such a reduction the identity IS the extractor (WARP's chain composes a target witness back to a
source witness; here they are the same object), and its `extract_sound` is a real theorem with real content:
the `SumcheckRbrStateProp` clause can die at `tr` while alive at `tr‖ρ` — the 2/|F| event, priced by
`basefoldSumcheckRbr`. The place where bytes are decoded is the stage whose target witness is `Unit` — the
commitment-opening/descent stage (`accExtractBcs`), not the sumcheck leg. The column-reading instance
duplicated that stage's extractor inside this leg's instance: the "landed beside" pattern.

**What the AllQueries/identity instance loses, stated exactly** (drafted theorems):
* `basefoldTableRbr_srExtract : srExtract (basefoldTableRbr …) s o ρs log = o.w'` — Construction B.5 reads
  no bytes (via `wAt_of_extract_id`, moved from the Descent file).
* `basefoldTableRbr_srExtract_committed`: on the FS event (`RelaxedMem R' δ () x' y' o.w'` with
  `x'.rt = S.commit (basefoldWord dom tbl)`), `srExtract = tbl` (via `basefoldTable_target_pins`, moved).
* `basefoldTable_publicView`: at `2^m ≤ t`, `hq`, on any `SrOutput` whose first-round openings verify
  against a root committing `tbl`, `extractTable dom m q (o.πs ⟨0,hm⟩).cols = tbl` — the table is a
  function of the PROOF STRING alone, whatever `w'`. This is `extractTable_committed` read on the
  transcript: commitment extractability, NOT a property of the instance.
* `basefoldTable_srExtract_eq_publicView`: on the FS event at `2^m ≤ t`, `srExtract (basefoldTableRbr …)
  = extractTable dom m q (o.πs ⟨0,hm⟩).cols`. Off the event the decoder is still the table and the
  extractor is still `w'`: the whole difference between the twins is the value of a Def-4.2 extractor
  OUTSIDE the event it is measured on.
* The concrete consumer that needs a transcript-computable extractor and to which the identity instance
  does NOT apply: a **realizer** — `Compiler/CommittedTerminalRealizer.lean:41` ("the tree's only
  extractor with a proof, `extractTable`, needs `2^m ≤ t`") and its `[CT-sampled]` residual (`:691`). A
  realizer holds bytes and no candidate `w'`; it cites `extractTable_committed` (`2^m ≤ t`) /
  `descentExtract_committed` (`2^m ≤ 2t`), by docstring only (no Lean import) — both survive unchanged, so
  the Compiler citation needs NO change. Below `2t < 2^m` no public-view decoder exists
  (`no_public_view_extractor_f5`, Descent file, kept).

## Consumers (grep tree-wide, excluding the two files)

* `Assurance/SpartanR1CS.lean:693-741` — cites `basefoldTable_fs_holds` (name survives, hypotheses weaken),
  `basefoldTable_acceptsEverywhere_holds`, `BaseFoldTableAcceptsEverywhere`,
  `basefoldTable_honest_acceptsEverywhere` (all untouched). **No edit needed.**
* `Compiler/CommittedTerminalRealizer.lean:41, :691` — docstring citations of `extractTable`,
  `basefoldTableVerify` (untouched). **No edit needed.**
* `GOAL.md:15` — "Twin decision on basefoldTableRbr vs basefoldTableRbrAllQueries" → decided: merge.
* Neither RBR instance has ANY Lean-level consumer outside the two Selvage files.

## The merged object (what lands in `Selvage/BaseFoldRbrTable.lean`, all in the script)

* `basefoldTableRbr (hm) (S) (dom) (q) (hcard)` — identity extractor, `err = 2/|F|`, `extract_sound` =
  the AllQueries proof verbatim. `basefoldTableRbr_err`, `basefoldTableRbr_extract_eq` (`rfl`, identity).
* DELETED: `tableExtract`, `tableExtract_append`, `basefoldTableRbr_wAt_zero`, the old
  `basefoldTableRbr_srExtract_committed` (replaced by the FS-event version above).
* NEW section "The twin, resolved": `extractTable_of_alive`, `roundBad_extractTable_iff`,
  `extractTable_round_bound`, `basefoldTable_publicView`, `basefoldTable_srExtract_eq_publicView`.
* MOVED IN from Descent: `wAt_of_extract_id`, `basefoldTable_target_pins`, `basefoldTableRbr_srExtract`
  (was `basefoldTableRbrAllQueries_srExtract`).
* `basefoldTable_fs_sound` / `basefoldTable_fs_holds` / `basefoldLeg_fs_both`: `hdt`, `hq` dropped
  (the `_allQueries` twins are deleted; these names are the survivors since SpartanR1CS cites them).
* F5: `rbrF5`, `stF5`, `rbrF5_state_alive`, `basefoldTable_teeth_f5`, `rbrF5_err`, `tableFs_sound_f5`
  move to `q₁` (`t = 1 < 2^m` — the query count the deleted hypothesis forbade; `q₁` moves in from the
  Descent example); `q₂`, `q₂_inj`, `honestMsg`, `extractTable_recovers_F5` stay at `t = 2` as the
  DECODER's keystones. **Pins deliberately changed**: the instance's F5 keystones are now at `t = 1`.
* Pins added: `basefoldTableRbr_srExtract`, `roundBad_extractTable_iff`, `extractTable_round_bound`,
  `basefoldTable_publicView`, `basefoldTable_srExtract_eq_publicView` (all expected
  `[propext, Classical.choice, Quot.sound]`). Header rewritten (twin paragraph, honest scope, ATLAS fields).

## Remaining edits, exactly (next session)

1. `cd ~/dev/minidregg && python3 ~/dev/zkml-research/notes/repair-table-twin-edit_table.py` (asserts every
   anchor; aborts without writing on any mismatch), then `lake env lean Selvage/BaseFoldRbrTable.lean`.
   Likely elaboration nits: `hR'.1` through the `@[reducible]` reduction's `R'` (works in the Descent file's
   `basefoldTable_target_pins`); `hδ : δ ∈ Set.Ioo 0 1` against `r.δstar` in `extractTable_round_bound`
   (defeq, `δstar := 1`); `uniformProb F` vs `uniformProb r.Chal` instance defeq (worked in `extract_sound`).
2. `Selvage/BaseFoldRbrTableDescent.lean`: DELETE §4 (`section AllQueries`, lines 375-511:
   `basefoldTableRbrAllQueries`, `_err`, `_extract_eq`, `wAt_of_extract_id`, `_srExtract`,
   `basefoldTable_target_pins`, `basefoldTable_fs_sound_allQueries`, `basefoldTable_fs_holds_allQueries`);
   DELETE §6's "The all-`t` instance at `t = 1`" subsection (lines 844-901: `q₁`, `rbrAllQueriesF5`,
   `stAllQueriesF5`, `rbrAllQueriesF5_state_alive`, `basefoldTable_teeth_allQueries_f5`,
   `rbrAllQueriesF5_err`, `tableFs_sound_allQueries_f5`); DELETE their 7 `#guard_msgs` pins (lines 913-920,
   951-959); `:587-588` docstring `basefoldTable_fs_holds_allQueries` → `basefoldTable_fs_holds`; header
   lines 4-9 ("lands the table-witness leg with an extractor that erasure-decodes…" → "…and beside it the
   decoder `extractTable`…"), lines 39-55 (§3 paragraph → "the Def-4.2 instance is `basefoldTableRbr`,
   identity extractor, all `t`; the two twins were one instance, `roundBad_extractTable_iff`"), lines 85-97
   (drop `rbrAllQueriesF5_state_alive`, `rbrAllQueriesF5_err`, `tableFs_sound_allQueries_f5`). Then
   `lake env lean Selvage/BaseFoldRbrTableDescent.lean`.
3. Targeted `lake build Selvage.BaseFoldRbrTable Selvage.BaseFoldRbrTableDescent Assurance.SpartanR1CS`
   after a real `pgrep` check (`ps -eo command | grep "[l]ake build" | grep -v "zsh -c"` — plain `pgrep -f`
   matches other lanes' shell wrappers whose TEXT contains "lake build").
4. Grep tree-wide for `basefoldTableRbrAllQueries|_allQueries|rbrAllQueriesF5|tableExtract\b|
   basefoldTableRbr_wAt_zero` → must be ∅ except:
   * `Selvage.lean:146` — root comment: replace "basefoldTableRbr's extract is REAL: extractTable = … on the
     last message's opened columns … Construction B.5 returns the committed table" with "basefoldTableRbr's
     extract is the identity (the reduction carries its witness unchanged; R' pins w' to the committed table,
     basefoldTable_target_pins), hcard only, every t; the column decoder extractTable is the SAME extractor
     on the alive set (roundBad_extractTable_iff) and is a commitment-extractability theorem at 2^m ≤ t
     (basefoldTable_publicView)"; and "SCOPE ON THE LABEL: 2^m ≤ t and 2^m ≤ |ι|" → "the instance assumes
     2^m ≤ |ι| only; the DECODER needs 2^m ≤ t".
   * `Selvage.lean:150` — delete the sentence "the all-t Def-4.2 instance basefoldTableRbrAllQueries (…)"
     and the whole "⚠ TWIN QUESTION for a later pass: …" sentence; replace with "the Def-4.2 instance is
     BaseFoldRbrTable's basefoldTableRbr (identity extractor, all t) — the twin retired by
     roundBad_extractTable_iff".
   * `GOAL.md:15` — mark decided (merge).
