# The `[ERASURE-list]` lift — resolved by refutation, a factor of two, and the target witness

**2026-09-05**, minidregg `main` (on top of `c85b521`), lane: BaseFoldRbrTableDescent. Specified by the
lane brief ("make the table extractor run at the DEPLOYED query count") against
`notes/sumcheck-table-witness.md` ("scope on the label", the `[ERASURE-list]` paragraph) and
`Selvage/BaseFoldRbrTable.lean` (`extractTable`, `extractTable_of_colsExact`, `extractTable_committed`,
hypotheses `2^m ≤ t`, `2^m ≤ |ι|`).

## Files (exact list; nothing committed)

| file | status |
|---|---|
| `Selvage/BaseFoldRbrTableDescent.lean` | **NEW**, 961 lines. `lake env lean`: exit 0, zero output (no warnings; 22 `#guard_msgs`-pinned `#print axioms`, all `[propext, Classical.choice, Quot.sound]`). No `sorry`/`axiom`/`native_decide`/`#guard`. `lake build Selvage.BaseFoldRbrTableDescent` (targeted, after `pgrep -f "lake build"` empty): built this one module only, 3.0 s; the only warnings in the replay are the pre-existing `ZkArgument.lean:164-165` unused variables, not mine. |
| `scripts/check-import-boundary.sh` | green (Theory, Selvage). |

Untouched: `Selvage/BaseFoldRbrTable.lean`, `Selvage/BaseFoldRbr.lean`, `Selvage/BaseFoldBcs*`,
`Selvage/Erasure.lean` (no extension was needed), `Selvage.lean`, `Assurance/*`, `Compiler/*`,
`Theory/*`, `Kernel/*`. The other `M`/`??` entries in `git status` belong to other lanes.

## The finding that reshaped the unit

The obligation as worded — *recover the table from `t < 2^m` columns plus the fold roots and an
accepting descent, by the inverse fold; the round-`i` word at the queried positions is determined by
the round-`(i+1)` word and the challenge* — is **false**, and provably so on every folding domain:

* The fold at ONE challenge is 2-to-1. Its two components `(foldEven f, foldOdd f)` are a bijective
  re-coordinatization of the level word (`componentsEquiv`), and `fold α` is the projection
  `E + α·O`. Kernel: `wordOfComponents (−α·O) O`, nonzero whenever `O ≠ 0` — at the polynomial level,
  `(X − α)·q(X²)`. `fold_not_injective [Nonempty κ] α : ∃ f ≠ 0, fold D f α = 0`.
* Fold roots are commitments: they bind, they do not reveal. A public-view extractor sees `2t`
  symbols of the top word (the sibling pairs) plus hashes; at `2t < 2^m` this is information-
  theoretically insufficient — `no_public_view_extractor_f5` (`m = 2`, `t = 1`) proves no function of
  the opened pair AND the entire level-1 word returns the table.

So the brief's `basefoldTableRbrDescent` with a public-view inverse-fold extractor cannot exist. What
DOES exist, each stated and proved:

1. **A factor of two.** The deployed round-0 openings are sibling pairs (`OpenedFriQuery`'s first two
   conjuncts) — `TableMsg`-shaped columns at the doubled query map `pairQuery`. The landed extractor runs
   on them at `2^m ≤ 2t` (`descentExtract`, `descentExtract_committed`, `descentExtract_of_openedFriQuery`).
2. **The all-`t` Def-4.2 instance.** In WARP's framework the knowledge-state witness of the extended
   transcript is already the committed table (binding + window, `basefoldWord_injective`), and
   Construction B.5 seeds extraction with the prover's target candidate `w'`, which `R'` pins to the
   table. The identity extractor is sound at `2/|F|` per round for every `t`, with only `hcard`
   (`basefoldTableRbrAllQueries`); FS-compiled at `(t + m)·2/|F|` for every query count.
3. **The descent leg lives at the sampled-IOR soundness theorem, not in a round bound.** Its job is
   "acceptance ⇒ the target witness exists" — `basefoldCommittedIor_coherent_exact_sound` (CITED),
   bridged to the table leg's claim object by `basefoldExactClaim_iff_holds`. The per-round event it
   excludes is NAMED (`DescentMiss`), inhabited, refuted, and bounded by citing
   `friAdaptive_coherent_query_miss`.

## Statements (copied)

```lean
-- 1. The inverse fold
def wordOfComponents (D : FoldingData F dom domSq) (E O : κ → F) : ι → F :=
  fun i => E (D.sq i) + dom i * O (D.sq i)
def componentsEquiv (D) : (ι → F) ≃ (κ → F) × (κ → F)          -- f ↦ (foldEven f, foldOdd f)
theorem fold_wordOfComponents (E O) (α) (k) : fold D (wordOfComponents D E O) α k = E k + α * O k
theorem pair_of_two_folds (f g : ι → F) {α β : F} (hαβ : α ≠ β) (k : κ)
    (hα : fold D f α k = fold D g α k) (hβ : fold D f β k = fold D g β k) :
    f (D.sec k) = g (D.sec k) ∧ f (D.neg (D.sec k)) = g (D.neg (D.sec k))
theorem fold_kernel (O) (α) : fold D (wordOfComponents D (fun k => -α * O k) O) α = 0
theorem fold_not_injective [Nonempty κ] (α : F) : ∃ f : ι → F, f ≠ 0 ∧ fold D f α = 0

-- 2. The sibling-pair extractor
def pairQuery (D) (k : Fin t → κ) : Fin (t + t) → ι     -- sec (k a) | neg (sec (k a))
noncomputable def descentExtract (D) (dom) (m) (k : Fin t → κ) (o : Fin t → FriQueryOpening F OpBig OpSmall) :
    (Fin m → Bool) → F := extractTable dom m (pairQuery D k) (pairCols o)
theorem pairQuery_injective (hk : Function.Injective k) : Function.Injective (dom ∘ pairQuery D k)
theorem descentExtract_committed (S : BindingCommitment Root F ι Op)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t + t) (hk : Function.Injective k)
    (hrt : rt = S.commit (basefoldWord dom tbl))
    (hleft : ∀ a, S.verifyOpen rt (D.sec (k a)) (o a).left (o a).leftPath)
    (hright : ∀ a, S.verifyOpen rt (D.neg (D.sec (k a))) (o a).right (o a).rightPath) :
    descentExtract D dom m k o = tbl
theorem descentExtract_of_openedFriQuery ... (hopen : ∀ a, OpenedFriQuery S.toOpeningScheme Ssmall D rt rt' α (k a) (o a)) :
    descentExtract D dom m k o = tbl

-- 3. The full-word decoder (IOR resolution)
noncomputable def descentExtractWord (dom) (m) (w : ι → F) := tableOfPoly m (codewordPoly dom (2 ^ m) w)
theorem basefoldWord_descentExtractWord (hw : w ∈ reedSolomonCode dom (2 ^ m)) :
    basefoldWord dom (descentExtractWord dom m w) = w
theorem descentExtractWord_basefoldWord (hcard) (tbl) : descentExtractWord dom m (basefoldWord dom tbl) = tbl

-- 4. The all-t instance
noncomputable def basefoldTableRbrAllQueries (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate := basefoldTableKState hm S dom q      -- the landed state, reused
  extract := fun _st _tr w => w                  -- identity: the witness IS the committed table
  err := fun _ _ _ => (2 : ℝ) / Fintype.card F
  extract_sound := ...  -- PROVED: alive ⇒ rt commits w ⇒ w is THE table (window); event ⊆ scalar event
theorem basefoldTableRbrAllQueries_srExtract ... : srExtract (basefoldTableRbrAllQueries hm S dom q hcard) s o ρs log = o.w'
theorem basefoldTable_target_pins (hrt : x'.rt = S.commit (basefoldWord dom tbl))
    (hR' : (basefoldTableReduction hm S dom q).R' () x' y' w') : w' = tbl
theorem basefoldTable_fs_sound_allQueries (hm) (S) (dom) (q) (hcard) :
    FsStraightlineKnowledgeSoundness (basefoldTableReduction hm S dom q) Set.univ
      (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F))
theorem basefoldTable_fs_holds_allQueries ... :   -- basefoldTable_fs_holds with hdt, hq removed
    uniformProb ... (¬ o.stmt.x.Holds S dom ∧ ∃ x' y', fiatShamir ... = some (x', y') ∧ RelaxedMem R' δ _ x' y' o.w')
      ≤ ((t' : ℝ) + (m : ℝ)) * (2 / Fintype.card F)

-- 5. The descent leg
theorem basefoldExactClaim_iff_holds (S : ∀ n, BindingCommitment ..) (T : FoldingTower F ιL m) (z) (H) (word) :
    BaseFoldExactClaim T z H word ↔ (⟨(S 0).commit word, z, H⟩ : MleEvalClaim (RootL 0) F m).Holds (S 0) (T.dom 0)
def DescentMiss (S) (T) (st : FriAdaptiveTranscript S) (r : Fin m → F) (qCount) (Q) : Prop :=
  (∃ j : Fin m, st.wordAt r (j + 1) _ ≠ fold (T.data j j.isLt) (st.wordAt r j _) (r j)) ∧
  ∀ j, FriAdaptiveRoundQueriesAccept S T st r j (Q j)
theorem descentMiss_coherent_le (T) (st) (hmell : m ≤ ell) (r) (qCount) (htau1 : tau ≤ 1)
    (htau : ∀ j : Fin m, tau ≤ 1 / (Fintype.card (PowerTwoFriLevels ell (j + 1)) : ℝ)) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
      (fun seed => DescentMiss SP T st r qCount (powerTwoCoherentSchedule hmell seed)) ≤ (1 - tau) ^ qCount
theorem basefoldCommittedIor_no_witness_sound ... (hword0 : st.word 0 _ = word)
    (hnot : ¬ (⟨(SP 0).commit word, z, H⟩ : MleEvalClaim _ F m).Holds (SP 0) (T.dom 0)) (hpm) (hdeg) :
    uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => BaseFoldCommittedIorAccepts SP T st z H prover qCount x.1 (powerTwoCoherentSchedule hmell x.2))
      ≤ (m : ℝ) * (3 / Fintype.card F) + (1 - tau) ^ qCount
```

## The inverse-fold lemma

`pair_of_two_folds` is the identity that IS true: two words with the same fold at two DISTINCT
challenges agree on the whole sibling pair (solve the 2×2 system in `(E, O)`; `mul_left_cancel₀` on
`α − β`). Witness: the honest word trivially. Falsifier: `fold_not_injective` (general) and
`fold_not_injective_f5` (`kernelWord = (3, 4, 0, 1)`, the evaluations of `X − 3`, folds to `0` at
challenge `3`, by `decide`). One challenge per round is what the protocol has, so the descent cannot
invert.

## The named event and which proximity theorem bounds it

`DescentMiss S T st r q Q` — some committed fold transition `w_{j+1} ≠ fold(w_j, r_j)`, yet every
sampled fibre opens consistently. Bounded by `friAdaptive_coherent_query_miss` (CITED) at
`(1 − τ)^q`, `τ ≤ 1/|ι_{j+1}|` via `one_div_card_le_relDist` (`descentMiss_coherent_le`). ATLAS fields:

* satisfiable — `descentMiss_inhabited_f5`: `missTranscript` (honest top word, level-1 word `(4, 0)`
  where the honest fold is the constant `4`) passes the one query at position `0`;
* falsifier — `descentMiss_teeth_f5`: the same transition is refused by the query at position `1`
  (`friAdaptiveRoundQueries_pins` forces `0 = 4`);
* the brief's falsifier — `fold_check_teeth_f5` / `fold_check_refuses_f5`: at the honest claim `4`,
  challenge `3`, the transcript (honest top word, constant-zero level-1 word, sumcheck message
  `3 + 3X²` with Boolean sum `4` and value `0` at `3`) passes the degree check, the Boolean-sum check,
  the terminal code check and the braided terminal equation, and `BaseFoldCommittedIorAccepts` rejects
  it ONLY through the round-0 fold check.

Why this is not a round bound: the RBR round event is over the round's CHALLENGE; the query miss is
over the QUERY seed, which the IOR-level `Reduction` does not sample (`verify` reads the oracle in full;
queries are BCS's). `DescentMiss` is priced at the sampled-verifier layer, where it belongs.

## The instance decided

* **`m = 1`, `t = 1 < 2 = 2^m`** — `descentExtract_recovers_F5`: from ONE query's sibling pair
  (positions `0` and `3`), verified against the ideal root, the extractor returns `table` exactly. The
  landed extractor needed `t = 2`. Premise inhabitation `k₁_inj`, `regime_f5 : 1 < 2^1 ∧ 2^1 ≤ 1 + 1`.
* **`m = 2`, `t = 1`** (the brief's suggested witness) — does NOT recover: `descent_public_view_teeth_f5`
  exhibits `tbl₁ = descentExtractWord dom0 2 0` and `tbl₂ = descentExtractWord dom0 2 (0, 0, 2, 0)`
  (both genuine `m = 2` tables by `reedSolomonCode_card_eq_top` at rate one), distinct, equal on the
  opened pair `{0, 3}`, and with EQUAL folds at challenge `2` (the spike is `(X − 2)(1 − X²)` on the
  domain). `no_public_view_extractor_f5` makes the impossibility explicit.
* **The all-`t` instance at `t = 1`** — `rbrAllQueriesF5` with `rbrAllQueriesF5_state_alive`,
  `basefoldTable_teeth_allQueries_f5` (the landed `[2,1]`-root tooth at `q₁`), `rbrAllQueriesF5_err = 2/5`,
  `tableFs_sound_allQueries_f5` at `(t + 1)·2/5`.

## What closed vs. what is named

**Closed.** Items 1–3 of the brief, re-scoped as above: the inverse-fold identity with both poles; the
descent extractor at the deployed message shape with `descentExtract_committed` (binding at the top
root + the round-0 openings; regime `2^m ≤ 2t`); the Def-4.2 instance valid for all `t` with error the
sumcheck term `2/|F|` (`basefoldTableRbrAllQueries`, FS at `(t + m)·2/|F|`); the descent's named event
with its bound; the two legs joined at one claim object.

**Named (not closed), the exact missing lemma.** Every bound here is at the quantization floor
`τ = 1/|ι_{j+1}|` or at exact membership — vacuous at `2^16`–`2^20` rows with 19 queries, as the
brief's VERDICTS §2 numbers say. The deployed price `(1 − δ)^q` at macroscopic `δ` is
`[PROX-fold-distance]`'s macroscopic regime. Its carrier already exists (`FoldDistancePreserving` /
`FoldDistanceTransition`), its consumer already exists (`friAdaptive_coherent_sampled_sound`, with
radii `radius j`, `foldRadius j`, `hgap`, `hfold`), and its realizers are: sub-quantization
(`foldDistancePreserving_of_lt_inv_card`, `b = 1`, PROVED, deployed-vacuous), half-threshold
(`foldDistanceTransition_halfThreshold`, PROVED, radius halves per round so `τ ≈ δ/2^m`,
deployed-vacuous), macroscopic (`foldDistancePreserving_of_isProximityGenerator`, which consumes
`IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d) B err` — WHIR Thm 4.8 / BCIKS
2020/654 — the tree's ONE standing hypothesis, named in `Selvage/ReedSolomon.lean:38` and never
assumed). I added no new `Prop`: ATLAS law 1 says a named hypothesis is an assumption, and the carrier
with realizer slots already exists. Nothing in the new file is priced on it.

**Re-scoped, with the reason on the label.** `[ERASURE-list]` as a PUBLIC-VIEW lift is refuted
(`fold_not_injective`, `no_public_view_extractor_f5`). Its honest replacement has two parts, both now in
the tree: (a) the table enters the RBR chain through the target witness — at BCS resolution, through the
commitment's extractability from the random-oracle log (`[COMMIT-CR]`'s realizer, `BaseFoldRawCommittedIor`
/ `CollisionResistanceROM`), not through `t` columns; (b) the descent guarantees that witness exists when
the deployed verifier accepts (`basefoldCommittedIor_no_witness_sound`), priced as above.

**Naming.** The brief's `basefoldTableRbrDescent` is `basefoldTableRbrAllQueries`: the name says what
the extractor is (identity, all `t`), because "descent" would claim a computation the file proves
impossible. `descentExtract` is the sibling-pair extractor and carries its `2^m ≤ 2t` regime on the label.

**Supersession question for the coordinator.** `basefoldTableRbrAllQueries` needs a strict subset of
`basefoldTableRbr`'s hypotheses on the same reduction and the same knowledge state. The landed instance's
extra content is that its extractor is a public-view computation (`extractTable_committed`), true only at
`2^m ≤ t` (now `2^m ≤ 2t` via `descentExtract`). ATLAS "delete the twin" would fold the landed instance
into a corollary of the all-`t` one plus the public-view theorem — but `BaseFoldRbrTable.lean` was off
limits this lane, and `Assurance/SpartanR1CS.lean` consumes it; not done, flagged.

## Consumers gained

* `basefoldCommittedIor_coherent_exact_sound` → `basefoldCommittedIor_no_witness_sound` (over
  `MleEvalClaim.Holds`; first consumer that speaks the table leg's vocabulary).
* `friAdaptive_coherent_query_miss` → `descentMiss_coherent_le`.
* `basefoldTableKState`, `basefoldSumcheckRbr`, `basefoldWord_injective` → `basefoldTableRbrAllQueries`.
* `extractTable_committed` → `descentExtract_committed` (at the doubled map).
* `fsKeystone_proved` → `basefoldTable_fs_sound_allQueries`.
* `foldEven_add_mul_foldOdd` → `componentsEquiv`.
* Cited, never re-derived: `codewordPoly_eval`, `codewordPoly_degree_lt`, `codewordPoly_eq_of_witness`,
  `booleanMobiusPolynomial_tableOfPoly`, `tableOfPoly_booleanMobiusPolynomial`,
  `reedSolomonCode_card_eq_top`, `mobius_descent_terminal`, `friAdaptiveRoundQueries_pins`,
  `one_div_card_le_relDist`, `wAt_of_le`/`wAt_of_lt`, `basefoldTable_source_teeth`.
* New general lemma: `wAt_of_extract_id` (Construction B.5 through an identity extractor returns its seed).

## Elaboration status

* `Selvage/BaseFoldRbrTableDescent.lean` — green (single-file, ~3 s, exit 0, no output; targeted
  `lake build` green, this module only).
* Boundary script — green.
