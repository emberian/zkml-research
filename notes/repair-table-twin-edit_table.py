import sys
p = '/Users/ember/dev/minidregg/Selvage/BaseFoldRbrTable.lean'
lines = open(p).read().split('\n')

def splice(start, end, new, first_anchor, last_anchor):
    """Replace 1-indexed lines start..end (inclusive) with new (a string)."""
    global lines
    assert first_anchor in lines[start - 1], (start, lines[start - 1])
    assert last_anchor in lines[end - 1], (end, lines[end - 1])
    lines = lines[:start - 1] + new.split('\n') + lines[end:]

HEADER = r'''/-
# Selvage.BaseFoldRbrTable — the sumcheck leg's witness becomes the committed table

`Selvage/BaseFoldRbr.lean` enters BaseFold's degree-two sumcheck leg into the
RBR kernel with `sumcheckReduction`'s witness type `Unit` and the table a
DEFINITION PARAMETER: its source relation is `H = mle table z`, a statement
predicate, and its docstring (`:120-125`) defers extraction of the committed
multilinear to the commitment layer (`MleEvalClaim`, Merkle binding,
`[COMMIT-CR]`).  `Selvage/MultilinearCommitment.lean:24` names what that
deferral owes: *"the remaining object is exactly the braided BaseFold
`Reduction`/`RbrKnowledgeSoundness` instance."*  This file is that object,
landed BESIDE the scalar leg because the scalar leg's own docstring points
here: the `W := Unit` reduction stays as the census-agreed honest scope
statement, and the table-witness reduction is its derived consumer.

* `TableMsg` — a round message: the round polynomial together with the `t`
  opened columns of the committed word (values + opening proofs).  The word
  is never sent; the root is in the STATEMENT, so no per-round root travels
  (the recommitted fold roots are the RS-descent leg's, not this leg's).
* `basefoldTableReduction` — the WARP `Reduction` with statement
  `MleEvalClaim` (root, point, value), witness THE TABLE, and source relation
  `rt = S.commit (basefoldWord dom tbl) ∧ mle tbl pt = val` — verbatim the
  body of `MleEvalClaim.Holds`'s existential (`basefoldTable_source_exists_iff_holds`).
  The verifier checks every opening against the statement's root and the
  sumcheck's completed-round checks, and outputs the terminal claim
  `(rt, z, r, c')`; the target relation is the braid `c' = mle tbl r * eqMle z r`
  (`basefold_sumcheck_terminal`, CITED).
* `extractTable` — **the public-view decoder**, a pure function of one
  execution's opened columns: erasure-decode them (`recoverFromColumns`,
  CITED), read the polynomial (`codewordPoly`, CITED), invert the Möbius
  packing (`tableOfPoly`, CITED).  `extractTable_committed`: through binding
  it returns EXACTLY the committed table, at `2^m ≤ t` opened columns at
  distinct positions.  This is a COMMITMENT-EXTRACTABILITY theorem — the
  table is a function of the proof string — and not the reduction's round
  extractor; the twin paragraph below says why.
* `basefoldTableRbr` — the Def-4.2 instance, `extract_sound` PROVED, at
  EVERY query count: `extract` is the identity, because the reduction carries
  its witness unchanged (`W' = W`, the root travels through `R'`), so the
  knowledge-state witness of the extended transcript is already the committed
  table, pinned by binding and the degree window (`basefoldWord_injective`);
  the per-round `∃ w`-event then refines into the SCALAR leg's event at that
  table, priced by `basefoldSumcheckRbr` (CITED) at `2/|F|`.  Only the window
  `2^m ≤ |ι|` is assumed.  No slack over the scalar leg.
* `basefoldTable_fs_sound` / `basefoldTable_fs_holds` — Fiat–Shamir of the
  table-witness leg (`fsKeystone_proved`, CITED), and its consumer-facing
  corollary over `MleEvalClaim.Holds`: an FS adversary whose output claim
  does NOT hold and is accepted succeeds with probability at most
  `(t + m) · 2/|F|`.  `basefoldLeg_fs_both` is the first consumer of
  `basefoldSumcheck_fs_sound`: both resolutions of the leg compile at ONE
  price — the witness upgrade costs nothing at the FS layer.

**The twin, resolved (ATLAS: delete the twin).**  Two `RbrKnowledgeSoundness`
instances of THIS reduction existed for one night: one whose `extract` read
the round message's columns through `extractTable` (hypotheses `2^m ≤ t`,
`dom ∘ q` injective, `2^m ≤ |ι|`), and one whose `extract` was the identity
(hypothesis `2^m ≤ |ι|` only; it lived in `Selvage/BaseFoldRbrTableDescent.lean`
as `basefoldTableRbrAllQueries`).  They were ONE instance, proved:
`roundBad_extractTable_iff` — on every witness alive at the extended
transcript the column decoder RETURNS that witness (`extractTable_of_alive`),
so the two extractors generate literally the same Def-4.2 round event, and
the column instance's round bound is the corollary `extractTable_round_bound`.
Def 4.2 measures an extractor only on the alive set; two extractors equal
there are one object, and the identity is the one with no hypotheses.  What
the column reading was actually carrying is a DIFFERENT theorem: the table is
computable from the proof string alone at `2^m ≤ t`
(`basefoldTable_publicView`), and on the FS event the instance's straightline
extractor coincides with that public-view value
(`basefoldTable_srExtract_eq_publicView`).  Off the FS event the instance's
extractor returns the prover's candidate `w'` (`basefoldTableRbr_srExtract`).
So a consumer that receives BYTES and no candidate — a realizer
(`Compiler/CommittedTerminalRealizer.lean:41`, its `[CT-sampled]` residual) —
consumes `extractTable_committed`, or `descentExtract_committed`
(`Selvage/BaseFoldRbrTableDescent.lean`, `2^m ≤ 2t`), never this instance;
below `2t < 2^m` no public-view decoder exists (`no_public_view_extractor_f5`)
and the table's provenance is the commitment's extractability, `[COMMIT-CR]`.
The consumers that DO cite this file — `Assurance/SpartanR1CS.lean`'s
`spartanOpeningProtocol_basefoldTable` through `basefoldTable_acceptsEverywhere_holds`
and `basefoldTable_fs_holds` — never read the extractor.

**Honest scope, on the label.**  The instance assumes only the degree window
`2^m ≤ |ι|`; its price is the scalar leg's.  The DECODER `extractTable` is
unique-decoding-regime: `2^m ≤ t` distinct opened positions (`hdt`, `hq`).
At deployed parameters `t ≪ 2^m`, so the decoder does not run there, and the
FS theorem's extracted table is the target candidate that `R'` pins.  Nothing
here is priced on any proximity regime.

**ATLAS fields (law 2), over the landed F₅ BaseFold instance**
(`BaseFoldExample.table`, `ProximityExample.ldtTower`, the ideal commitment):

* satisfiable — `rbrF5_state_alive` (the knowledge state is alive on the
  honest claim with the honest table as witness, at `t = 1 < 2 = 2^m`, below
  the decoder's regime) and `extractTable_recovers_F5` (the decoder returns
  `table` from two honest columns, `t = 2 = 2^m`);
* falsifier — `basefoldTable_teeth_f5`: a root committing a DIFFERENT table
  `[2, 1]` with the SAME claimed value `4` at `z = 3` is REFUSED by the
  relation at witness `table` and accepted at witness `[2, 1]` — the relation
  is about the committed table, not about the scalar;
* premise inhabitation — the window `2 ≤ 4` and the F₅ round price
  `rbrF5_err = 2/5` at `t = 1`; `q₂_inj` (two distinct positions at
  `t = 2 = 2^1`) for the decoder.
-/'''

INSTANCE = r'''/-- ⭐ **The Def-4.2 instance for the table-witness leg, at EVERY query count.**
`kstate` is the committed-column-consistent state; `extract` is the identity —
the reduction carries its witness unchanged (`W' = W`, the root travels
through `R'`), so the knowledge-state witness of the extended transcript is
already the committed table, pinned by binding and the degree window
(`basefoldWord_injective`, CITED); `err = 2/|F|` — the scalar leg's own price,
no slack.  `extract_sound` PROVED: the alive witness at the extension is the
unique table `rt` commits, and the round event is CONTAINED in the scalar
leg's round event at that table, which `basefoldSumcheckRbr` (CITED) prices.

Regime: `2^m ≤ |ι|` (the degree window) and nothing else — no erasure
hypothesis, because no bytes are decoded here.  The column decoder
`extractTable` is the SAME extractor on the alive set
(`roundBad_extractTable_iff`, below) and carries its own regime. -/
noncomputable def basefoldTableRbr (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate := basefoldTableKState hm S dom q
  extract := fun _st _tr w => w
  err := fun _i _st _δ => (2 : ℝ) / Fintype.card F
  extractTime := fun _ => 0
  extract_sound := by
    classical
    intro δ hδ st i rs hlen π
    by_cases hex : ∃ tbl : (Fin m → Bool) → F, st.x.rt = S.commit (basefoldWord dom tbl)
    · obtain ⟨tbl, hrt⟩ := hex
      have hsc := (basefoldSumcheckRbr hm tbl st.x.pt).extract_sound
        δ hδ ⟨(), st.x.val, fun _ => ()⟩ i (tableRounds rs)
        (by rw [tableRounds_length, hlen]) π.poly
      rw [basefoldSumcheckRbr_err] at hsc
      refine le_trans (uniformProb_mono ?_) hsc
      intro ρ hev
      obtain ⟨w, hdead, halive⟩ := hev
      rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive
      rw [basefoldTableKState_state_eq, decide_eq_false_iff_not] at hdead
      obtain ⟨hcols, hrt', hsum⟩ := halive
      have hw : w = tbl := basefoldWord_injective S dom hcard (hrt'.symm.trans hrt)
      subst hw
      refine ⟨(), ?_, ?_⟩
      · rw [basefoldSumcheckRbr_state_eq, decide_eq_false_iff_not]
        intro hsc'
        exact hdead ⟨fun e he => hcols e (List.mem_append_left _ he), hrt', hsc'⟩
      · rw [basefoldSumcheckRbr_state_eq, decide_eq_true_eq]
        rw [tableRounds_append] at hsum
        exact hsum
    · refine le_trans (le_of_eq (uniformProb_false ?_)) (by positivity)
      rintro ρ ⟨w, -, halive⟩
      rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive
      exact hex ⟨w, halive.2.1⟩

/-- The table-witness leg pays exactly two field roots per round — the scalar
leg's price, unchanged by the witness upgrade. -/
@[simp] theorem basefoldTableRbr_err (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (i : Fin m)
    (st : Stmt (basefoldTableReduction hm S dom q)) (δ : ℝ) :
    (basefoldTableRbr hm S dom q hcard).err i st δ = (2 : ℝ) / Fintype.card F := rfl

/-- **The extractor is pinned**: it returns the witness it is handed. -/
theorem basefoldTableRbr_extract_eq (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι)
    (st : Stmt (basefoldTableReduction hm S dom q)) (tr : Transcript (TableMsg F Op t) F)
    (w : (Fin m → Bool) → F) :
    (basefoldTableRbr hm S dom q hcard).extract st tr w = w := rfl'''

B5_AND_TWIN = r'''/-! ## The backward composition (Construction B.5) returns the target candidate -/

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- Construction B.5 through an identity extractor returns its seed at every level. -/
theorem wAt_of_extract_id {r : Reduction} (rbr : RbrKnowledgeSoundness r)
    (hid : ∀ st tr w, rbr.extract st tr w = w) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) :
    ∀ (n i : ℕ), rounds.length - i = n → wAt rbr st rounds w' i = w'
  | 0, i, hn => wAt_of_le rbr st rounds w' (by omega)
  | n + 1, i, hn => by
      rw [wAt_of_lt rbr st rounds w' (by omega), hid,
        wAt_of_extract_id rbr hid st rounds w' n (i + 1) (by omega)]

/-- **The straightline FS extractor returns the prover's target candidate**:
Construction B.5 (`srExtract`, CITED) through the identity extractor is the
seed `w'`.  No byte of the proof string is read; the knowledge claim's
content is that `R'` pins `w'` to the committed table (next). -/
theorem basefoldTableRbr_srExtract (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (s : ℕ)
    (o : SrOutput (basefoldTableReduction hm S dom q) s) (ρs : Fin m → F)
    (log : List (SrMove (basefoldTableReduction hm S dom q) s × F)) :
    srExtract (basefoldTableRbr hm S dom q hcard) s o ρs log = o.w' :=
  wAt_of_extract_id _ (fun _ _ _ => rfl) _ _ _ _ 0 rfl

/-- The target relation pins the candidate: whatever `w'` satisfies `R'` at an
output whose root commits `basefoldWord dom tbl` IS `tbl` (binding + the
degree window, `basefoldWord_injective`, CITED). -/
theorem basefoldTable_target_pins (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι)
    {x' : BaseFoldTerminalClaim Root F m} {y' : Fin 1 → Unit} {w' tbl : (Fin m → Bool) → F}
    (hrt : x'.rt = S.commit (basefoldWord dom tbl))
    (hR' : (basefoldTableReduction hm S dom q).R' () x' y' w') : w' = tbl :=
  basefoldWord_injective S dom hcard (hR'.1.symm.trans hrt)

/-- ⭐ **The straightline FS extractor returns the committed table on the FS
event.**  The event `FsStraightlineKnowledgeSoundness` prices has the
prover's candidate in `R'_{≤δ}` at an output `x'`; whenever that output's
root commits `basefoldWord dom tbl`, `srExtract` (Construction B.5, CITED)
outputs `tbl`.  The extracted witness is attached to the prover's commitment
through the target relation, not by reading the columns. -/
theorem basefoldTableRbr_srExtract_committed (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (hcard : 2 ^ m ≤ Fintype.card ι) (s : ℕ)
    (o : SrOutput (basefoldTableReduction hm S dom q) s) (ρs : Fin m → F)
    (log : List (SrMove (basefoldTableReduction hm S dom q) s × F)) {δ : ℝ}
    {x' : BaseFoldTerminalClaim Root F m} {y' : Fin 1 → Unit} {tbl : (Fin m → Bool) → F}
    (hrt : x'.rt = S.commit (basefoldWord dom tbl))
    (hR' : RelaxedMem (basefoldTableReduction hm S dom q).R' δ () x' y' o.w') :
    srExtract (basefoldTableRbr hm S dom q hcard) s o ρs log = tbl := by
  rw [basefoldTableRbr_srExtract]
  obtain ⟨ystar, hR, -⟩ := hR'
  exact basefoldTable_target_pins hm S dom q hcard hrt hR

/-! ## The twin, resolved: the column decoder IS this extractor on the alive set

A second instance of this reduction — `extract` reading the round message's
columns through `extractTable`, at `2^m ≤ t` and `dom ∘ q` injective — was
landed beside the identity one.  Def 4.2 measures an extractor only where the
extended transcript's witness is ALIVE, and there the decoder returns that
witness; so the two extractors generate the same round event, and the column
instance's bound is a corollary.  Its genuine extra content is
`basefoldTable_publicView` — a theorem about the proof string, not about the
extractor — and `basefoldTable_srExtract_eq_publicView` says exactly where
the instance's straightline output and the public-view value coincide: on the
FS event. -/

omit [Fintype F] in
/-- On a witness alive at the extended transcript, the column decoder of the
pending message RETURNS that witness (`extractTable_committed`, CITED): the
columns verify against the root, and the root commits the witness. -/
theorem extractTable_of_alive (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) {c : MleEvalClaim Root F m}
    {rs : List (TableMsg F Op t × F)} {π : TableMsg F Op t} {ρ : F}
    {w : (Fin m → Bool) → F} (halive : TableStateProp S dom q c (rs ++ [(π, ρ)]) none w) :
    extractTable dom m q π.cols = w := by
  obtain ⟨hcols, hrt, -⟩ := halive
  exact extractTable_committed S dom hcard hdt hq hrt
    (hcols (π, ρ) (List.mem_append_right _ (List.mem_singleton_self _)))

/-- ⭐ **The two extractors are one on the alive set.**  The Def-4.2 round
event of the column-decoding extractor — some witness alive at `tr‖ρ` while
`extractTable` of the pending columns is dead at `tr` — is EXACTLY `RoundBad`
of the identity instance, at `2^m ≤ t`: the decoder's output on the alive
side is the witness itself.  Two extractors with the same round events are
the same Def-4.2 object; this is the theorem that retired the column
instance. -/
theorem roundBad_extractTable_iff (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (δ : ℝ) (st : Stmt (basefoldTableReduction hm S dom q))
    (rs : List (TableMsg F Op t × F)) (π : TableMsg F Op t) (ρ : F) :
    (∃ w : (Fin m → Bool) → F,
        (basefoldTableKState hm S dom q).state δ st ⟨rs, some π⟩ (extractTable dom m q π.cols)
          = false ∧
        (basefoldTableKState hm S dom q).state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true) ↔
      RoundBad (basefoldTableRbr hm S dom q hcard) δ st rs π ρ := by
  constructor
  · rintro ⟨w, hdead, halive⟩
    have halive' := halive
    rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive'
    rw [extractTable_of_alive S dom q hcard hdt hq halive'] at hdead
    exact ⟨w, hdead, halive⟩
  · rintro ⟨w, hdead, halive⟩
    have halive' := halive
    rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive'
    refine ⟨w, ?_, halive⟩
    rw [extractTable_of_alive S dom q hcard hdt hq halive']
    exact hdead

/-- **The column instance's round bound is a corollary**: the Def-4.2 bound
for the extractor that decodes the pending message's columns, at the identity
instance's price `2/|F|`, from `roundBad_extractTable_iff` and
`extract_sound`.  This is the retired instance's `extract_sound`, verbatim in
its event, with `hdt`/`hq` now visibly used only to identify the events. -/
theorem extractTable_round_bound (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (st : Stmt (basefoldTableReduction hm S dom q)) (i : Fin m)
    {rs : List (TableMsg F Op t × F)} (hlen : rs.length = (i : ℕ)) (π : TableMsg F Op t) :
    uniformProb F (fun ρ => ∃ w : (Fin m → Bool) → F,
        (basefoldTableKState hm S dom q).state δ st ⟨rs, some π⟩ (extractTable dom m q π.cols)
          = false ∧
        (basefoldTableKState hm S dom q).state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true)
      ≤ (2 : ℝ) / Fintype.card F := by
  have h := uniformProb_roundBad_le (basefoldTableRbr hm S dom q hcard) hδ st i hlen π
  rw [basefoldTableRbr_err] at h
  exact le_trans (uniformProb_mono fun ρ hρ =>
    (roundBad_extractTable_iff hm S dom q hcard hdt hq δ st rs π ρ).mp hρ) h

/-- ⭐ **What the column reading actually carries: the table is a function of
the proof string alone**, at `2^m ≤ t`.  On any state-restoration output whose
first-round openings verify against a root committing `basefoldWord dom tbl`,
the decoder of the first message's columns is `tbl` — whatever candidate `w'`
the prover supplied and whatever the challenges.  This is commitment
extractability at the unique-decoding regime (`extractTable_committed`, read
on the transcript); it is NOT a property of `basefoldTableRbr`'s extractor,
and it is what a consumer holding bytes and no candidate cites. -/
theorem basefoldTable_publicView (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (s : ℕ)
    (o : SrOutput (basefoldTableReduction hm S dom q) s) {tbl : (Fin m → Bool) → F}
    (hrt : o.stmt.x.rt = S.commit (basefoldWord dom tbl))
    (hver : (o.πs ⟨0, hm⟩).Opens S q o.stmt.x.rt) :
    extractTable dom m q (o.πs ⟨0, hm⟩).cols = tbl :=
  extractTable_committed S dom hcard hdt hq hrt hver

/-- ⭐ **Where the instance's extractor and the public-view decoder coincide:
on the FS event, at `2^m ≤ t`.**  The straightline extractor of
`basefoldTableRbr` returns the candidate `w'`; the decoder returns the table
the first-round openings commit to; when the candidate is in `R'_{≤δ}` at an
output carrying the statement's root — the event
`FsStraightlineKnowledgeSoundness` prices — the two are equal.  Off that
event the decoder is still the table and the extractor is still `w'`: the
whole difference between the retired column instance and this one is the
value of a Def-4.2 extractor OUTSIDE the event it is measured on. -/
theorem basefoldTable_srExtract_eq_publicView (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (s : ℕ)
    (o : SrOutput (basefoldTableReduction hm S dom q) s) (ρs : Fin m → F)
    (log : List (SrMove (basefoldTableReduction hm S dom q) s × F)) {δ : ℝ}
    {x' : BaseFoldTerminalClaim Root F m} {y' : Fin 1 → Unit} {tbl : (Fin m → Bool) → F}
    (hrt : o.stmt.x.rt = S.commit (basefoldWord dom tbl))
    (hx : x'.rt = S.commit (basefoldWord dom tbl))
    (hR' : RelaxedMem (basefoldTableReduction hm S dom q).R' δ () x' y' o.w')
    (hver : (o.πs ⟨0, hm⟩).Opens S q o.stmt.x.rt) :
    srExtract (basefoldTableRbr hm S dom q hcard) s o ρs log
      = extractTable dom m q (o.πs ⟨0, hm⟩).cols := by
  rw [basefoldTableRbr_srExtract_committed hm S dom q hcard s o ρs log hx hR',
    basefoldTable_publicView hm S dom q hcard hdt hq s o hrt hver]
'''

F5_HEAD = r'''/-- One column position — `t = 1 < 2 = 2^1`, BELOW the decoder's regime: the
instance needs no columns to run. -/
def q₁ : Fin 1 → Fin 4 := fun _ => 0

/-- The two query positions `{0, 1}` — `t = 2 = 2^1`, at the erasure bound,
where the decoder runs. -/
def q₂ : Fin 2 → Fin 4 := ![0, 1]

/-- **Premise inhabitation for the decoder**: the positions are distinct under
the level-0 domain. -/
theorem q₂_inj : Function.Injective (dom0 ∘ q₂) := by decide

/-- The ideal commitment over the level-0 domain — the inhabited binding floor. -/
abbrev S₄ : BindingCommitment (Fin 4 → ZMod 5) (ZMod 5) (Fin 4) Unit :=
  idealCommitment (ZMod 5) (Fin 4)

/-- The native Def-4.2 object on the landed F₅ BaseFold instance, at `t = 1`. -/
noncomputable def rbrF5 :
    RbrKnowledgeSoundness (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁) :=
  basefoldTableRbr (by decide) S₄ dom0 q₁ (by decide)'''

# Apply from the bottom up so earlier line numbers stay valid.

# F5 head: lines 822-836 (q₂ .. rbrF5)
splice(822, 836, F5_HEAD, 'The two query positions', 'basefoldTableRbr (by decide) S₄ dom0 q₂ (by decide) (by decide) q₂_inj')

# Block: B.5 section + twin section replaces lines 511-542 (old backward composition, incl. trailing blank)
splice(511, 542, B5_AND_TWIN, '/-! ## The backward composition', '')

# Block: instance, err, extract_eq: lines 445-509
splice(445, 509, INSTANCE, '/-- ⭐ **The Def-4.2 instance for the table-witness leg.**', 'tableExtract_append dom m q rs π ρ w')

# Block: delete the round extractor (tableExtract) section: lines 415-435
splice(415, 435, '/-! ## The Def-4.2 instance -/\n', '/-! ## The round extractor -/', '')

# Header: lines 1-68
splice(1, 68, HEADER, '/-', '-/')

s = '\n'.join(lines)

def rep(a, b, cnt=1):
    global s
    assert s.count(a) == cnt, (s.count(a), a[:90])
    s = s.replace(a, b)

# FS theorems: drop hdt hq
rep("(hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)\n    (hq : Function.Injective (dom ∘ q)) :\n",
    "(hcard : 2 ^ m ≤ Fintype.card ι) :\n", 2)
rep("(hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)\n    (hq : Function.Injective (dom ∘ q)) (s t' : ℕ) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)",
    "(hcard : 2 ^ m ≤ Fintype.card ι)\n    (s t' : ℕ) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)")
rep("fsKeystone_proved.sound _ (basefoldTableRbr hm S dom q hcard hdt hq) Set.univ",
    "fsKeystone_proved.sound _ (basefoldTableRbr hm S dom q hcard) Set.univ")
rep("(fun i st _ δ _ => le_of_eq (basefoldTableRbr_err hm S dom q hcard hdt hq i st δ))",
    "(fun i st _ δ _ => le_of_eq (basefoldTableRbr_err hm S dom q hcard i st δ))")
rep("obtain ⟨E, hE⟩ := basefoldTable_fs_sound hm S dom q hcard hdt hq",
    "obtain ⟨E, hE⟩ := basefoldTable_fs_sound hm S dom q hcard")
rep("    basefoldTable_fs_sound hm S dom q hcard hdt hq⟩",
    "    basefoldTable_fs_sound hm S dom q hcard⟩")
rep("""`t`-query ROM adversary whose
output claim `(rt, z, H)` has NO table witness (no `tbl` with `rt` committing
it and `mle tbl z = H`) and whose FS-compiled transcript is accepted succeeds
with probability at most `(t + m) · 2/|F|`.  `fsKeystone_proved` (CITED)
applied to `basefoldTableRbr`. -/""",
    """`t`-query ROM adversary whose
output claim `(rt, z, H)` has NO table witness (no `tbl` with `rt` committing
it and `mle tbl z = H`) and whose FS-compiled transcript is accepted succeeds
with probability at most `(t + m) · 2/|F|` — at every query count, no erasure
regime.  `fsKeystone_proved` (CITED) applied to `basefoldTableRbr`. -/""")

# F5 body: the instance-side keystones move to q₁; the decoder's stay at q₂.
rep("noncomputable def stF5 : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂) :=",
    "noncomputable def stF5 : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁) :=")
rep("""/-- **Satisfying witness**: the knowledge state is alive on the honest claim,
at the empty transcript, with the honest table as witness. -/""",
    """/-- **Satisfying witness**: the knowledge state is alive on the honest claim,
at the empty transcript, with the honest table as witness — at `t = 1`, a
query count the column decoder cannot reach. -/""")
rep("""    ¬ (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table ∧
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table' :=
  basefoldTable_source_teeth (by decide) S₄ dom0 q₂ (by decide) table_ne_table'""",
    """    ¬ (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table ∧
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table' :=
  basefoldTable_source_teeth (by decide) S₄ dom0 q₁ (by decide) table_ne_table'""")
rep("""/-- The round price computes to `2/5` on the live instance. -/
theorem rbrF5_err (i : Fin 1)
    (st : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂)) (δ : ℝ) :""",
    """/-- The round price computes to `2/5` on the live instance, at `t = 1`. -/
theorem rbrF5_err (i : Fin 1)
    (st : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁)) (δ : ℝ) :""")
rep("""/-- The compiled table-witness leg on the F₅ instance: a `t`-query FS
adversary whose claim has no table witness is accepted with probability at
most `(t + 1) · 2/5` — a live finite-field number. -/
theorem tableFs_sound_f5 :
    FsStraightlineKnowledgeSoundness
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂) Set.univ
      (fun _s t _δ => ((t : ℝ) + 1) * (2 / 5)) := by
  have h := basefoldTable_fs_sound (m := 1) (by decide) S₄ dom0 q₂ (by decide) (by decide)
    q₂_inj""",
    """/-- The compiled table-witness leg on the F₅ instance at `t = 1`: a `t`-query
FS adversary whose claim has no table witness is accepted with probability at
most `(t + 1) · 2/5` — a live finite-field number, at a query count the
column decoder cannot reach. -/
theorem tableFs_sound_f5 :
    FsStraightlineKnowledgeSoundness
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₁) Set.univ
      (fun _s t _δ => ((t : ℝ) + 1) * (2 / 5)) := by
  have h := basefoldTable_fs_sound (m := 1) (by decide) S₄ dom0 q₁ (by decide)""")

# Pins: add the new theorems after the srExtract_committed pin.
rep("""/-- info: 'Minidregg.Selvage.basefoldTableRbr_srExtract_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbr_srExtract_committed
""",
    """/-- info: 'Minidregg.Selvage.basefoldTableRbr_srExtract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbr_srExtract
/-- info: 'Minidregg.Selvage.basefoldTableRbr_srExtract_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbr_srExtract_committed
/-- info: 'Minidregg.Selvage.roundBad_extractTable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundBad_extractTable_iff
/-- info: 'Minidregg.Selvage.extractTable_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extractTable_round_bound
/-- info: 'Minidregg.Selvage.basefoldTable_publicView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_publicView
/-- info: 'Minidregg.Selvage.basefoldTable_srExtract_eq_publicView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_srExtract_eq_publicView
""")

assert 'hdt hq' not in s.replace('hcard hdt hq', 'X'), 'stray hdt hq'
assert 'tableExtract' not in s, 'tableExtract survives'
assert 'AllQueries' not in s.replace('basefoldTableRbrAllQueries`', 'Y'), 'AllQueries survives outside the header citation'
open(p, 'w').write(s)
print('ok', len(s.split('\n')), 'lines')
