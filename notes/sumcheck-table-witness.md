# Census upgrade 1 — the sumcheck leg's witness becomes the committed table

**2026-09-05**, minidregg `main` (on top of `51999d9`), lane: BaseFoldRbrTable. Specified by
`notes/unit-witness-census.md` §1 (row `sumcheckReduction`, `W := Unit`), §7 item 1, §8
(the `BaseFoldRbr.lean:120-125` paragraph), §9 (`basefoldSumcheck_fs_sound` has no consumer).

## Files (exact list; nothing committed)

| file | status |
|---|---|
| `Selvage/BaseFoldRbrTable.lean` | **NEW**, 940 lines. `lake env lean`: exit 0, zero warnings, 12 `#guard_msgs`-pinned `#print axioms`, all `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`native_decide`/`#guard`. Also `lake build Selvage.BaseFoldRbrTable` (targeted, run only after `pgrep -f "lake build"` was empty): built this one module, nothing else rebuilt. |
| `Assurance/SpartanR1CS.lean` | **MODIFIED** (the brief allows it only for a discharge; this is one): `+ import Selvage.BaseFoldRbrTable`, §5 header sentence corrected (it said neither obligation is discharged), `spartanOpeningProtocol_basefoldTable` + `_inhabited`, two pins. `lake env lean`: exit 0; the only warning is the pre-existing `push_neg` deprecation at `:658`, not mine. |
| `scripts/check-import-boundary.sh` | green (Theory, Selvage). |

Untouched: `Selvage/SumcheckRbr.lean`, `Selvage/BaseFoldRbr.lean`, `Selvage/MultilinearCommitment.lean`
(the `W := Unit` object stays as the census-agreed scope statement — its docstring at `:120` is the
pointer to the new file), `Assurance/ZkmlMatmulBaseFold*.lean`, everything else. The other `M`/`??`
entries in `git status` belong to other lanes.

## Ground truth re-verified

`sumcheckReduction` `W := Unit` at `SumcheckRbr.lean:177`; `basefoldSumcheckReduction`
at `BaseFoldRbr.lean:35` with `table` a parameter and `R := fun _ H _ _ => H = S`; docstring `:120-125`
defers extraction to the commitment layer; `MultilinearCommitment.lean:24` names the braided
instance as the remaining object; `holds_iff_of_committed` at `:96`; `accExtractBcs` at
`AccRbrBcs.lean:483` (reads the last message, `bcsWord = recoverFromColumns` on its columns);
`recoverFromColumns_sound` at `Erasure.lean:128`, `committed_word_recovered` at `:170`;
`SpartanOpeningProtocol` at `SpartanR1CS.lean:704`; `basefoldSumcheck_fs_sound` had no consumer.
Style anchor per coordinator: `Selvage/LightClientKnowledge.lean` (`lcExtract` — extractor as a pure
function of one execution's public view, `_eq_ofFn_committed` pin). `FoldRoundBound` not used.

## Statements (copied)

```lean
structure TableMsg (F Op : Type) [Field F] (t : ℕ) where
  poly : Polynomial F            -- the round polynomial
  cols : Fin t → F               -- opened columns of the COMMITTED word (root is in the statement)
  ops  : Fin t → Op

noncomputable def extractTable (dom : ι ↪ F) (m : ℕ) (q : Fin t → ι) (cols : Fin t → F) :
    (Fin m → Bool) → F :=
  tableOfPoly m (codewordPoly dom (2 ^ m) (recoverFromColumns dom (2 ^ m) q cols))

theorem extractTable_committed (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t) {q} (hq : Function.Injective (dom ∘ q))
    {rt} {tbl} (hrt : rt = S.commit (basefoldWord dom tbl)) {π : TableMsg F Op t}
    (hver : π.Opens S q rt) : extractTable dom m q π.cols = tbl
-- proof: committed_word_recovered → codewordPoly_eq_of_witness → tableOfPoly_booleanMobiusPolynomial

@[reducible] noncomputable def basefoldTableReduction (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι) : Reduction where
  X  := MleEvalClaim Root F m          -- (rt, pt, val)
  W  := (Fin m → Bool) → F             -- THE TABLE
  X' := BaseFoldTerminalClaim Root F m -- (rt, z, r, c')
  R  := fun _ c _ tbl => c.rt = S.commit (basefoldWord dom tbl) ∧ mle tbl c.pt = c.val
  R' := fun _ out _ tbl => out.rt = S.commit (basefoldWord dom tbl) ∧
          out.val = mle tbl out.chal * eqMle out.pt out.chal
  k := m; PMsg := TableMsg F Op t; Chal := F; δstar := 1
  verify := fun _ c _ πs ρs => basefoldTableVerify S q c πs ρs
  -- verifier: every message's columns open against c.rt ∧ scRunValid 2 c.val (round polys);
  -- output ⟨c.rt, c.pt, ρs, scRunClaim c.val (round polys)⟩

theorem basefoldTable_source_exists_iff_holds ... :
    (∃ tbl, (basefoldTableReduction hm S dom q).R () c y tbl) ↔ c.Holds S dom := Iff.rfl

noncomputable def basefoldTableRbr (hm : 0 < m) (S) (dom) (q)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t) (hq : Function.Injective (dom ∘ q)) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate  := basefoldTableKState hm S dom q     -- cols consistent ∧ rt commits tbl ∧ SumcheckRbrStateProp at tbl
  extract := fun _st tr w => tableExtract dom m q tr w   -- = extractTable of the last message's columns
  err     := fun _ _ _ => (2 : ℝ) / Fintype.card F
  extract_sound := ...   -- PROVED: binding pins the alive witness to the decoded table;
                         -- the round event is CONTAINED in basefoldSumcheckRbr's at that table

theorem basefoldTableRbr_srExtract_committed ... (hrt : o.stmt.x.rt = S.commit (basefoldWord dom tbl))
    (hver : ∀ i, (o.πs i).Opens S q o.stmt.x.rt) :
    srExtract (basefoldTableRbr hm S dom q hcard hdt hq) s o ρs log = tbl

theorem basefoldTable_fs_sound ... :
    FsStraightlineKnowledgeSoundness (basefoldTableReduction hm S dom q) Set.univ
      (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F))

theorem basefoldTable_fs_holds ... (P : SrProver (basefoldTableReduction hm S dom q) s) :
    uniformProb ((Fin t' → F) × (Fin m → F)) (fun coins => ... ¬ o.stmt.x.Holds S dom ∧
        ∃ x' y', fiatShamir _ s (fsOracle o ρs) o = some (x', y') ∧ RelaxedMem R' δ _ x' y' o.w')
      ≤ ((t' : ℝ) + (m : ℝ)) * (2 / Fintype.card F)

theorem basefoldLeg_fs_both ... :
    (∀ tbl z, FsStraightlineKnowledgeSoundness (basefoldSumcheckReduction hm tbl z) Set.univ ε) ∧
    FsStraightlineKnowledgeSoundness (basefoldTableReduction hm S dom q) Set.univ ε
  -- ε := fun _ t _ => (t + m) * (2/|F|); proof := ⟨basefoldSumcheck_fs_sound hm, basefoldTable_fs_sound ...⟩

def BaseFoldTableAcceptsEverywhere (hm) (S) (dom) (q) (c : MleEvalClaim Root F m) : Prop :=
  ∃ P : (ℕ → F) → ℕ → TableMsg F Op t, PrefixMeasurable (fun χ i => (P χ i).poly) ∧
    ∀ ρs : Fin m → F, ∃ x' y' w', basefoldTableVerify S q c (fun i => P (chalOf ρs) i) ρs = some (x', y') ∧
      (basefoldTableReduction hm S dom q).R' () x' y' w'

theorem basefoldTable_acceptsEverywhere_holds (hm) (S) (dom) (q) (hcard : 2 ^ m ≤ Fintype.card ι)
    (hF : 2 * m < Fintype.card F) (c) (hacc : BaseFoldTableAcceptsEverywhere hm S dom q c) : c.Holds S dom

-- Assurance/SpartanR1CS.lean
theorem spartanOpeningProtocol_basefoldTable {Root ι Op : Type} [Fintype ι] (S) (dom) {tq} (q : Fin tq → ι)
    (ht : 0 < t) (hcard : 2 ^ t ≤ Fintype.card ι) (hF : 2 * t < Fintype.card F) :
    SpartanOpeningProtocol S dom (BaseFoldTableAcceptsEverywhere ht S dom q)
```

## ATLAS fields

* **Satisfying witness.** `rbrF5_state_alive`: on `MleEvalClaimExample.honestClaim` (root of
  `basefoldWord dom0 table`, `z = 3`, value `mle table 3 = 4`), the knowledge state is alive at
  the empty transcript with `table` as witness. `extractTable_recovers_F5`: from the two honest
  columns at `q₂ = (0, 1)` the extractor returns `table` exactly (`m = 1`, `t = 2 = 2^1`,
  ideal commitment). `basefoldTable_honest_acceptsEverywhere` / `..._inhabited`: the honest
  strategy accepts everywhere, for every `m`, every table.
* **Falsifier.** `basefoldTable_source_teeth` (generic) and `basefoldTable_teeth_f5`: the root
  committing `table' = [2, 1]` with the SAME value `4` at `z = 3` (`mle [2,1] 3 = 3·2+3·1 = 4`)
  is REFUSED by `R` at witness `table` and accepted at witness `table'` — the relation is about
  the committed table, not the scalar (`basefoldWord_injective` + `table ≠ table'` by `decide`).
* **Premise inhabitation.** `q₂_inj` (distinct positions at the erasure bound), the window
  `2^1 ≤ |Fin 4|`, `rbrF5_err = 2/5`, `tableFs_sound_f5` at `(t + 1)·2/5`.

## What closed vs. what is named

**Closed:** items 1–3 of the brief and item 4 (Spartan). `extract` is real (`accExtractBcs` shape:
reads the last message, erasure-decodes; the handed-in witness is ignored when a message exists);
`extract_sound` is proved by containment into `basefoldSumcheckRbr` at the decoded table, so the
round price is the scalar leg's `2/|F|` with no slack. No obligation `Prop` was needed.

**Scope on the label (hypotheses, not assumptions):** `hdt : 2^m ≤ t` and `hq` (unique-decoding
erasure regime), `hcard : 2^m ≤ |ι|` (degree window); the deterministic theorem also needs
`2m < |F|`. At deployed parameters `t ≪ 2^m`, so THIS extractor does not run there. The lemma
that is missing for deployment is the list-decoding lift `[ERASURE-list]`/`[OOD-pin-proximity]`:
*from `t < 2^m` verified columns of the committed word TOGETHER WITH the RS-descent leg's fold
roots and an accepting descent, recover the (unique, by mutual correlated agreement at the
proximity radius) table* — i.e. the extractor of the braided descent leg, which
`BaseFoldRbr.lean:18-22` keeps separate from this leg. Nothing here is priced on that regime.

Also: `basefoldTableReduction` captures `[Fintype F]` (for `chalFintype`) and nothing else from the
section; each round message carries the columns of the STATEMENT's root (no per-round root — that is
the descent leg's), mirroring `accReductionBcs`'s alphabet minus the recommitment.

## Consumers gained

* `basefoldSumcheck_fs_sound` → **first consumer** `basefoldLeg_fs_both` (both resolutions of the leg
  compile at one price). Honest note: the table leg's own FS theorem comes from `fsKeystone_proved`
  on `basefoldTableRbr`, not by transport from the scalar FS theorem — the two SR games have
  different message alphabets, so no transport exists or is needed; the consumer is the bundle.
* `basefoldSumcheckRbr` → `basefoldTableRbr.extract_sound` (the round argument is reused, not re-proved).
* `MleEvalClaim.Holds` → `basefoldTable_source_exists_iff_holds` (`Iff.rfl`), `basefoldTable_fs_holds`,
  `basefoldTable_acceptsEverywhere_holds`.
* `SpartanOpeningProtocol` → DISCHARGED at `Accepts := BaseFoldTableAcceptsEverywhere`
  (`spartanOpeningProtocol_basefoldTable`), inhabited (`_inhabited`).
* Cited, never re-derived: `committed_word_recovered`, `codewordPoly_eq_of_witness`,
  `tableOfPoly_booleanMobiusPolynomial`, `basefoldWord_injective`, `basefold_sumcheck_terminal`,
  `adaptive_sumcheck_soundness`, `fsKeystone_proved`, `wAt`/`srExtract`, `scRunValid_append_single`.
* New general lemmas (small, reusable): `scRunClaim_ofFn`, `scRunValid_ofFn_iff` (the `scRun*`
  vocabulary of `SumcheckRbr` in the whole-transcript `scChain`/`chalOf` vocabulary of
  `SumcheckReduction`), `scChain_congr`, `uniformProb_eq_one_of_forall`.

## Item 4: which, and why; what the other would need

Chose **Spartan**: its content (accept-everywhere ⇒ holds) is field-agnostic and lives in Selvage; the
Assurance side is a one-line application, so the discharge is verified end-to-end. The matmul route is
mechanically cheaper but shallower — three specializations of the keystone at
`Z := {st | st.x = claims.output}` etc. Not done; the exact statement each claim needs is

```lean
FsStraightlineKnowledgeSoundness (basefoldTableReduction hm SC domC qC)
  {st | st.x = claims.output} (fun _ t _ => (t + (μ + ν)) * (2 / |F|))   -- and left (μ+κ), right (κ+ν)
```

obtained from `fsKeystone_proved.sound _ (basefoldTableRbr ...) {st | st.x = claims.output} ...`
exactly as `basefoldTable_fs_sound` is at `Set.univ`; the extractor is `srExtract (basefoldTableRbr ..)`,
pinned by `basefoldTableRbr_srExtract_committed`. That would replace the three "given word"
theorems' witness with the extracted table; it does not touch their RS-descent price
`dim · 3/|F|`, which stays the IOR theorem's.

## Elaboration status per file

* `Selvage/BaseFoldRbrTable.lean` — green (single-file, ~5 s; targeted `lake build` green).
* `Assurance/SpartanR1CS.lean` — green (single-file; pre-existing `push_neg` deprecation warning only).
* Boundary script — green.
