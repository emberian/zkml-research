/-
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
* `extractTable` — **a pure function of one execution's public view**: the
  opened columns.  Erasure-decode them (`recoverFromColumns`, CITED), read the
  polynomial (`codewordPoly`, CITED), invert the Möbius packing
  (`tableOfPoly`, CITED).  `extractTable_committed`: through binding it
  returns EXACTLY the committed table.
* `basefoldTableRbr` — the Def-4.2 instance, `extract_sound` PROVED: the
  extractor reads the round's message; the alive witness at the extension is
  pinned to the decoded table by binding; the per-round `∃ w`-event then
  refines into the SCALAR leg's event at that table, priced by
  `basefoldSumcheckRbr` (CITED) at `2/|F|`.  No slack over the scalar leg.
* `basefoldTable_fs_sound` / `basefoldTable_fs_holds` — Fiat–Shamir of the
  table-witness leg (`fsKeystone_proved`, CITED), and its consumer-facing
  corollary over `MleEvalClaim.Holds`: an FS adversary whose output claim
  does NOT hold and is accepted succeeds with probability at most
  `(t + m) · 2/|F|`.  `basefoldLeg_fs_both` is the first consumer of
  `basefoldSumcheck_fs_sound`: both resolutions of the leg compile at ONE
  price — the witness upgrade costs nothing at the FS layer.

**Honest scope, on the label.**  The extractor is the unique-decoding-regime
extractor: it needs `2^m ≤ t` opened columns at distinct positions
(`hdt`, `hq`) and `2^m ≤ |ι|` (`hcard`, the BaseFold degree window).  At
deployed parameters `t ≪ 2^m`, so THIS extractor does not run there; the lift
to `t < 2^m` is the list-decoding seam `[ERASURE-list]` /
`[OOD-pin-proximity]` (`Selvage/Erasure.lean`), which is where the RS-descent
leg's proximity machinery enters, exactly as `Selvage/BaseFoldRbr.lean:18-22`
says.  Nothing here is priced on that regime; the theorems below require the
regime as a hypothesis and the F₅ keystones inhabit it (`m = 1`, `t = 2`).

**ATLAS fields (law 2), over the landed F₅ BaseFold instance**
(`BaseFoldExample.table`, `ProximityExample.ldtTower`, the ideal commitment):

* satisfiable — `rbrF5_state_alive` (the knowledge state is alive on the
  honest claim with the honest table as witness) and `extractTable_recovers_F5`
  (the extractor returns `table` from two honest columns);
* falsifier — `basefoldTable_teeth_f5`: a root committing a DIFFERENT table
  `[2, 1]` with the SAME claimed value `4` at `z = 3` is REFUSED by the
  relation at witness `table` and accepted at witness `[2, 1]` — the relation
  is about the committed table, not about the scalar;
* premise inhabitation — `q₂_inj` (two distinct positions at `t = 2 = 2^1`),
  the window `2 ≤ 4`, and the F₅ round price `rbrF5_err = 2/5`.
-/
import Selvage.BaseFoldRbr
import Selvage.MultilinearCommitment
import Selvage.Erasure

namespace Minidregg.Selvage

open Polynomial

variable {Root Op F ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
  {m t : ℕ}

/-! ## The message alphabet: round polynomial + opened columns of the committed word -/

/-- A round message of the table-witness leg: the sumcheck round polynomial
and the `t` opened columns of the committed word (values + opening proofs)
at the query positions.  The root is the statement's, so none travels here. -/
structure TableMsg (F Op : Type) [Field F] (t : ℕ) : Type where
  /-- The round polynomial. -/
  poly : Polynomial F
  /-- The opened column values at the `t` spot-checked positions. -/
  cols : Fin t → F
  /-- The opening proofs (Merkle paths in deployment). -/
  ops : Fin t → Op

/-- The message's openings all verify against the STATEMENT's root. -/
def TableMsg.Opens (S : OpeningScheme Root F ι Op) (q : Fin t → ι) (rt : Root)
    (π : TableMsg F Op t) : Prop :=
  ∀ j, S.verifyOpen rt (q j) (π.cols j) (π.ops j)

/-- Committed-column consistency of a transcript prefix: every completed
round's columns open from the statement's root. -/
def TableColsConsistent (S : OpeningScheme Root F ι Op) (q : Fin t → ι) (rt : Root)
    (rs : List (TableMsg F Op t × F)) : Prop :=
  ∀ e ∈ rs, e.1.Opens S q rt

/-- Read the message transcript as the scalar sumcheck's transcript: keep the
round polynomials and the challenges, drop the columns. -/
def tableRounds (rs : List (TableMsg F Op t × F)) : List (Polynomial F × F) :=
  rs.map fun e => (e.1.poly, e.2)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem tableRounds_length (rs : List (TableMsg F Op t × F)) :
    (tableRounds rs).length = rs.length := by
  unfold tableRounds
  rw [List.length_map]

omit [Fintype F] [DecidableEq F] in
theorem tableRounds_append (rs : List (TableMsg F Op t × F)) (π : TableMsg F Op t)
    (ρ : F) :
    tableRounds (rs ++ [(π, ρ)]) = tableRounds rs ++ [(π.poly, ρ)] := by
  unfold tableRounds
  rw [List.map_append]
  rfl

omit [Fintype F] [DecidableEq F] in
theorem tableRounds_ofFn {kk : ℕ} (πs : Fin kk → TableMsg F Op t) (ρs : Fin kk → F) :
    tableRounds (List.ofFn fun i => (πs i, ρs i))
      = List.ofFn fun i => ((πs i).poly, ρs i) := by
  unfold tableRounds
  rw [List.map_ofFn]
  rfl

/-! ## The extractor: a pure function of the opened columns -/

/-- **The table extractor** — a pure function of one execution's public view,
the opened columns: erasure-decode them to the committed word
(`recoverFromColumns`, CITED), read the word's polynomial (`codewordPoly`,
CITED), and invert the Boolean Möbius packing (`tableOfPoly`, CITED).  Total:
junk outside the regime, never a partial function. -/
noncomputable def extractTable (dom : ι ↪ F) (m : ℕ) (q : Fin t → ι)
    (cols : Fin t → F) : (Fin m → Bool) → F :=
  tableOfPoly m (codewordPoly dom (2 ^ m) (recoverFromColumns dom (2 ^ m) q cols))

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- The BaseFold word is a genuine codeword of the degree-`2^m` window. -/
theorem basefoldWord_mem (dom : ι ↪ F) (tbl : (Fin m → Bool) → F) :
    basefoldWord dom tbl ∈ reedSolomonCode dom (2 ^ m) :=
  mem_reedSolomonCode_iff.mpr
    ⟨booleanMobiusPolynomial m tbl, degree_booleanMobiusPolynomial_lt m tbl, fun _ => rfl⟩

omit [Fintype F] in
/-- **The extractor recovers the table, exactly — binding-free core.**  If the
columns are literally the BaseFold word's symbols at `t ≥ 2^m` distinct
positions, erasure recovery returns the word (`recoverFromColumns_sound`,
CITED), the window pins its polynomial (`codewordPoly_eq_of_witness`, CITED),
and the Möbius round trip returns the table. -/
theorem extractTable_of_colsExact (dom : ι ↪ F) (hcard : 2 ^ m ≤ Fintype.card ι)
    (hdt : 2 ^ m ≤ t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    {tbl : (Fin m → Bool) → F} {cols : Fin t → F}
    (hcols : ∀ j, cols j = basefoldWord dom tbl (q j)) :
    extractTable dom m q cols = tbl := by
  unfold extractTable
  rw [recoverFromColumns_sound dom hdt hq (basefoldWord_mem dom tbl) hcols,
    codewordPoly_eq_of_witness (f := basefoldWord dom tbl) dom hcard
      (degree_booleanMobiusPolynomial_lt m tbl)
      (fun _ => rfl),
    tableOfPoly_booleanMobiusPolynomial]

omit [Fintype F] in
/-- **The extractor recovers the committed table, through binding.**  The
columns enter ONLY through verified openings against a `BindingCommitment`
of the BaseFold word (`committed_word_recovered`, CITED — binding composed
with erasure recovery); nothing is assumed about how the prover produced
them. -/
theorem extractTable_committed (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) {rt : Root} {tbl : (Fin m → Bool) → F}
    (hrt : rt = S.commit (basefoldWord dom tbl)) {π : TableMsg F Op t}
    (hver : π.Opens S q rt) :
    extractTable dom m q π.cols = tbl := by
  unfold extractTable
  rw [committed_word_recovered S dom hdt hq hrt (basefoldWord_mem dom tbl) hver,
    codewordPoly_eq_of_witness (f := basefoldWord dom tbl) dom hcard
      (degree_booleanMobiusPolynomial_lt m tbl)
      (fun _ => rfl),
    tableOfPoly_booleanMobiusPolynomial]

/-! ## The reduction -/

/-- The output statement of the table-witness leg: the same root, the public
point `z`, the challenge point `r`, and the terminal claim `c'`.  Its truth is
the braid `c' = mle tbl r * eqMle z r` for the table `rt` commits. -/
structure BaseFoldTerminalClaim (Root F : Type) (m : ℕ) : Type where
  /-- The committed root, carried through unchanged. -/
  rt : Root
  /-- The public evaluation point `z`. -/
  pt : Fin m → F
  /-- The challenge point `r`. -/
  chal : Fin m → F
  /-- The terminal sumcheck claim. -/
  val : F

open Classical in
/-- The table-witness verifier: every message's columns open against the
statement's root, and the completed sumcheck rounds pass their degree and
Boolean-sum checks; on success output the terminal claim at the challenge
point. -/
noncomputable def basefoldTableVerify (S : OpeningScheme Root F ι Op) (q : Fin t → ι)
    (c : MleEvalClaim Root F m) (πs : Fin m → TableMsg F Op t) (ρs : Fin m → F) :
    Option (BaseFoldTerminalClaim Root F m × (Fin 1 → Unit)) :=
  if (∀ i, (πs i).Opens S q c.rt) ∧
      scRunValid 2 c.val (tableRounds (List.ofFn fun i => (πs i, ρs i))) then
    some (⟨c.rt, c.pt, ρs, scRunClaim c.val (tableRounds (List.ofFn fun i => (πs i, ρs i)))⟩,
      fun _ => ())
  else none

/-- ⭐ **BaseFold's sumcheck leg with the committed table as witness** — the
braided object `Selvage/MultilinearCommitment.lean:24` names.  Statement: an
`MleEvalClaim` `(rt, z, H)`.  Witness: a Boolean table.  Source relation:
`rt = S.commit (basefoldWord dom tbl) ∧ mle tbl z = H` — the conjunction the
census spells out, and verbatim the body of `MleEvalClaim.Holds`.  Target
relation: the terminal claim is `mle tbl r * eqMle z r` at the same root.

Compare `basefoldSumcheckReduction` (`Selvage/BaseFoldRbr.lean:35`): there the
table is a definition parameter and `W := Unit`; here it is the witness, the
statement carries the root, and the message carries the openings the
extractor reads.

ATLAS fields: satisfying witness `BaseFoldRbrTableExample.rbrF5_state_alive`;
falsifier `BaseFoldRbrTableExample.basefoldTable_teeth_f5` (same value,
different root: refused); premise inhabitation
`BaseFoldRbrTableExample.q₂_inj` with the window `2 ≤ 4` at `t = 2`. -/
@[reducible] noncomputable def basefoldTableReduction (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι) : Reduction where
  Idx := Unit
  X := MleEvalClaim Root F m
  A := Unit
  X' := BaseFoldTerminalClaim Root F m
  A' := Unit
  W := (Fin m → Bool) → F
  n := 1
  n' := 1
  n_pos := by decide
  n'_pos := by decide
  R := fun _ c _ tbl => c.rt = S.commit (basefoldWord dom tbl) ∧ mle tbl c.pt = c.val
  R' := fun _ out _ tbl =>
    out.rt = S.commit (basefoldWord dom tbl) ∧
      out.val = mle tbl out.chal * eqMle out.pt out.chal
  k := m
  k_pos := hm
  PMsg := TableMsg F Op t
  Chal := F
  pmsgNonempty := ⟨⟨0, fun _ => 0, fun j => S.openAt 0 (q j)⟩⟩
  chalFintype := inferInstance
  chalNonempty := ⟨0⟩
  δstar := 1
  δstar_pos := by norm_num
  δstar_le_one := le_rfl
  verify := fun _ c _ πs ρs => basefoldTableVerify S q c πs ρs

omit [DecidableEq F] [Fintype ι] in
/-- The source relation is exactly the census's conjunction. -/
theorem basefoldTable_source_iff (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (c : MleEvalClaim Root F m)
    (y : Fin (basefoldTableReduction hm S dom q).n → (basefoldTableReduction hm S dom q).A)
    (tbl : (Fin m → Bool) → F) :
    (basefoldTableReduction hm S dom q).R () c y tbl ↔
      c.rt = S.commit (basefoldWord dom tbl) ∧ mle tbl c.pt = c.val :=
  Iff.rfl

omit [DecidableEq F] [Fintype ι] in
/-- A witness exists for the source relation iff the claim HOLDS in
`Selvage/MultilinearCommitment.lean`'s sense: the relation is `Holds` with its
existential opened. -/
theorem basefoldTable_source_exists_iff_holds (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (c : MleEvalClaim Root F m)
    (y : Fin (basefoldTableReduction hm S dom q).n → (basefoldTableReduction hm S dom q).A) :
    (∃ tbl, (basefoldTableReduction hm S dom q).R () c y tbl) ↔ c.Holds S dom :=
  Iff.rfl

/-- **Falsifier, generic.**  A root committing a DIFFERENT table with the SAME
claimed value is refused at the honest table's witness (binding + the degree
window, `basefoldWord_injective`, CITED) — and accepted at the other table's.
The relation is about the committed table, not the scalar. -/
theorem basefoldTable_source_teeth (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι)
    {tbl tbl' : (Fin m → Bool) → F} (hne : tbl ≠ tbl') {z : Fin m → F}
    (hz : mle tbl' z = mle tbl z)
    (y : Fin (basefoldTableReduction hm S dom q).n → (basefoldTableReduction hm S dom q).A) :
    ¬ (basefoldTableReduction hm S dom q).R ()
        ⟨S.commit (basefoldWord dom tbl'), z, mle tbl z⟩ y tbl ∧
      (basefoldTableReduction hm S dom q).R ()
        ⟨S.commit (basefoldWord dom tbl'), z, mle tbl z⟩ y tbl' := by
  refine ⟨?_, rfl, hz⟩
  rintro ⟨hrt, -⟩
  exact hne (basefoldWord_injective S dom hcard hrt.symm)

/-! ## The knowledge state -/

/-- **The table-witness knowledge state**: committed-column consistency of the
completed rounds (every message's columns open against the statement's root)
∧ the root commits the witness table ∧ the SCALAR leg's knowledge state
(`SumcheckRbrStateProp`, reused) at that table on the projected transcript.
Pending messages are read through the scalar state only (their columns are
checked when the round completes). -/
def TableStateProp (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (c : MleEvalClaim Root F m) (rs : List (TableMsg F Op t × F))
    (pending : Option (TableMsg F Op t)) (tbl : (Fin m → Bool) → F) : Prop :=
  TableColsConsistent S q c.rt rs ∧
  c.rt = S.commit (basefoldWord dom tbl) ∧
  SumcheckRbrStateProp 2 (mle tbl c.pt) (basefoldHonest tbl c.pt) c.val (tableRounds rs)
    (pending.map TableMsg.poly)

omit [Fintype F] [DecidableEq F] in
/-- The zero-padded schedule of an `ofFn` transcript is `chalOf` of its
challenge tuple. -/
theorem scSchedule_ofFn {kk : ℕ} (gs : Fin kk → Polynomial F) (ρs : Fin kk → F) {j : ℕ}
    (hj : j < kk) :
    scSchedule (List.ofFn fun i => (gs i, ρs i)) j = chalOf ρs j := by
  unfold scSchedule chalOf
  rw [List.getElem?_ofFn, dif_pos hj, dif_pos hj]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- The honest truth after a full `ofFn` transcript is the braid terminal
`mle tbl r * eqMle z r` (`basefold_sumcheck_terminal`, CITED). -/
theorem scTruthAfter_ofFn (tbl : (Fin m → Bool) → F) (z : Fin m → F)
    (gs : Fin m → Polynomial F) (ρs : Fin m → F) :
    scTruthAfter (mle tbl z) (basefoldHonest tbl z) (List.ofFn fun i => (gs i, ρs i))
      = mle tbl ρs * eqMle z ρs := by
  rw [scTruthAfter_eq_of_prefix (basefoldHonest_prefixMeasurable tbl z) _ (chalOf ρs)
      (fun j hj => scSchedule_ofFn gs ρs (by rwa [List.length_ofFn] at hj)),
    List.length_ofFn, basefold_sumcheck_terminal]

omit [Fintype F] [DecidableEq F] in
theorem scTruthAfter_tableRounds_ofFn (tbl : (Fin m → Bool) → F) (z : Fin m → F)
    (πs : Fin m → TableMsg F Op t) (ρs : Fin m → F) :
    scTruthAfter (mle tbl z) (basefoldHonest tbl z)
        (tableRounds (List.ofFn fun i => (πs i, ρs i)))
      = mle tbl ρs * eqMle z ρs := by
  rw [tableRounds_ofFn]
  exact scTruthAfter_ofFn tbl z (fun i => (πs i).poly) ρs

open Classical in
/-- The Def-4.1 knowledge state for the table-witness leg, three clauses
PROVED: empty — columns vacuous, collapses to the source relation; prover
moves — pending-blind on columns, the scalar clause's own monotonicity;
full — the verifier's opening checks ARE the column conjunct, and the scalar
clause collapses to the braid terminal through `scTruthAfter_tableRounds_ofFn`. -/
noncomputable def basefoldTableKState (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) :
    KStateFn (basefoldTableReduction hm S dom q) where
  state := fun _δ st tr tbl => decide (TableStateProp S dom q st.x tr.rounds tr.pending tbl)
  empty_iff := by
    intro δ hδ st w
    simp only [Transcript.empty, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hrt, -, hval, -⟩
      refine ⟨st.y, ⟨hrt, hval.symm⟩, ?_⟩
      rw [fracHamming_self]
      exact hδ.1.le
    · rintro ⟨ystar, ⟨hrt, hval⟩, -⟩
      exact ⟨fun _ he => absurd he (by simp), hrt, trivial, hval.symm, trivial⟩
  prover_monotone := by
    intro δ hδ st rs w hlen hdead π
    rw [decide_eq_false_iff_not] at hdead ⊢
    intro halive
    apply hdead
    obtain ⟨hcols, hrt, hsc⟩ := halive
    exact ⟨hcols, hrt, hsc.1, hsc.2.1, trivial⟩
  full_iff := by
    intro δ hδ st πs ρs w
    simp only [Transcript.ofFull, decide_eq_true_eq]
    constructor
    · rintro ⟨hcols, hrt, hvalid, halign, -⟩
      have hall : ∀ i, (πs i).Opens S q st.x.rt := fun i =>
        hcols (πs i, ρs i) (by rw [List.mem_ofFn]; exact ⟨i, rfl⟩)
      refine ⟨⟨st.x.rt, st.x.pt, ρs,
        scRunClaim st.x.val (tableRounds (List.ofFn fun i => (πs i, ρs i)))⟩,
        fun _ => (), ?_, ?_⟩
      · show basefoldTableVerify S.toOpeningScheme q st.x πs ρs = _
        unfold basefoldTableVerify
        rw [if_pos ⟨hall, hvalid⟩]
      · refine ⟨fun _ => (), ⟨hrt, ?_⟩, ?_⟩
        · show scRunClaim st.x.val (tableRounds (List.ofFn fun i => (πs i, ρs i)))
            = mle w ρs * eqMle st.x.pt ρs
          rw [halign, scTruthAfter_tableRounds_ofFn]
        · rw [fracHamming_self]
          exact hδ.1.le
    · rintro ⟨x', y', hver, hrel⟩
      change basefoldTableVerify S.toOpeningScheme q st.x πs ρs = some (x', y') at hver
      unfold basefoldTableVerify at hver
      split_ifs at hver with hv
      · have hx : x' = ⟨st.x.rt, st.x.pt, ρs,
            scRunClaim st.x.val (tableRounds (List.ofFn fun i => (πs i, ρs i)))⟩ :=
          (congrArg Prod.fst (Option.some.inj hver)).symm
        subst hx
        obtain ⟨ystar, ⟨hrt, hval⟩, -⟩ := hrel
        refine ⟨?_, hrt, hv.2, ?_, trivial⟩
        · intro e he
          rw [List.mem_ofFn] at he
          obtain ⟨i, rfl⟩ := he
          exact hv.1 i
        · rw [scTruthAfter_tableRounds_ofFn]
          exact hval

omit [DecidableEq F] [Fintype ι] in
open Classical in
/-- The state field, exposed for round proofs. -/
theorem basefoldTableKState_state_eq (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (δ : ℝ) (st : Stmt (basefoldTableReduction hm S dom q))
    (tr : Transcript (TableMsg F Op t) F) (tbl : (Fin m → Bool) → F) :
    (basefoldTableKState hm S dom q).state δ st tr tbl
      = decide (TableStateProp S dom q st.x tr.rounds tr.pending tbl) := rfl

/-! ## The round extractor -/

/-- **The round extractor**, in transcript shape: read the extended
transcript's last message and decode its columns.  `accExtractBcs`'s shape —
the witness handed in is not consulted when a message exists; the witness is
computed from the public view. -/
noncomputable def tableExtract (dom : ι ↪ F) (m : ℕ) (q : Fin t → ι)
    (tr : Transcript (TableMsg F Op t) F) (w : (Fin m → Bool) → F) : (Fin m → Bool) → F :=
  match tr.rounds.getLast? with
  | some e => extractTable dom m q e.1.cols
  | none => w

omit [Fintype F] [DecidableEq F] [Fintype ι] in
/-- The extractor on a one-round extension, in closed form. -/
theorem tableExtract_append (dom : ι ↪ F) (m : ℕ) (q : Fin t → ι)
    (rs : List (TableMsg F Op t × F)) (π : TableMsg F Op t) (ρ : F)
    (w : (Fin m → Bool) → F) :
    tableExtract dom m q ⟨rs ++ [(π, ρ)], none⟩ w = extractTable dom m q π.cols := by
  unfold tableExtract
  rw [List.getLast?_concat]

open Classical in
/-- The scalar leg's state, exposed through `basefoldSumcheckRbr`. -/
theorem basefoldSumcheckRbr_state_eq (hm : 0 < m) (table : (Fin m → Bool) → F)
    (z : Fin m → F) (δ : ℝ) (st : Stmt (basefoldSumcheckReduction hm table z))
    (tr : Transcript (Polynomial F) F) (w : Unit) :
    (basefoldSumcheckRbr hm table z).kstate.state δ st tr w
      = decide (SumcheckRbrStateProp 2 (mle table z) (basefoldHonest table z) st.x
          tr.rounds tr.pending) := rfl

/-- ⭐ **The Def-4.2 instance for the table-witness leg.**  `kstate` is the
committed-column-consistent state, `extract` decodes the round message's
columns, `err = 2/|F|` — the scalar leg's own price, no slack.
`extract_sound` PROVED: a knowledge-state witness alive at the extended
transcript has its columns verified, so binding pins it to the decoded table
(`extractTable_committed`); the round event is then CONTAINED in the scalar
leg's round event at that table, which `basefoldSumcheckRbr` (CITED) prices.

Regime: `2^m ≤ |ι|` (the degree window), `2^m ≤ t` and `dom ∘ q` injective
(unique-decoding erasure recovery) — stated, not assumed; see the module
header for what this excludes. -/
noncomputable def basefoldTableRbr (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) :
    RbrKnowledgeSoundness (basefoldTableReduction hm S dom q) where
  kstate := basefoldTableKState hm S dom q
  extract := fun _st tr w => tableExtract dom m q tr w
  err := fun _i _st _δ => (2 : ℝ) / Fintype.card F
  extractTime := fun _ => 0
  extract_sound := by
    classical
    intro δ hδ st i rs hlen π
    have hsc := (basefoldSumcheckRbr hm (extractTable dom m q π.cols) st.x.pt).extract_sound
      δ hδ ⟨(), st.x.val, fun _ => ()⟩ i (tableRounds rs)
      (by rw [tableRounds_length, hlen]) π.poly
    rw [basefoldSumcheckRbr_err] at hsc
    refine le_trans (uniformProb_mono ?_) hsc
    intro ρ hev
    obtain ⟨w, hdead, halive⟩ := hev
    rw [basefoldTableKState_state_eq, decide_eq_true_eq] at halive
    rw [basefoldTableKState_state_eq, decide_eq_false_iff_not] at hdead
    have hdead' : ¬ TableStateProp S dom q st.x rs (some π) (extractTable dom m q π.cols) := by
      rw [← tableExtract_append dom m q rs π ρ w]
      exact hdead
    obtain ⟨hcols, hrt, hsum⟩ := halive
    have hπ : π.Opens S q st.x.rt :=
      hcols (π, ρ) (List.mem_append_right _ (List.mem_singleton_self _))
    have hw : extractTable dom m q π.cols = w := extractTable_committed S dom hcard hdt hq hrt hπ
    subst hw
    refine ⟨(), ?_, ?_⟩
    · rw [basefoldSumcheckRbr_state_eq, decide_eq_false_iff_not]
      intro hsc'
      exact hdead' ⟨fun e he => hcols e (List.mem_append_left _ he), hrt, hsc'⟩
    · rw [basefoldSumcheckRbr_state_eq, decide_eq_true_eq]
      rw [tableRounds_append] at hsum
      exact hsum

/-- The table-witness leg pays exactly two field roots per round — the scalar
leg's price, unchanged by the witness upgrade. -/
@[simp] theorem basefoldTableRbr_err (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (i : Fin m)
    (st : Stmt (basefoldTableReduction hm S dom q)) (δ : ℝ) :
    (basefoldTableRbr hm S dom q hcard hdt hq).err i st δ = (2 : ℝ) / Fintype.card F := rfl

/-- **The extractor is pinned**: on a one-round extension it IS the column
decoder of the pending message — no witness consulted. -/
theorem basefoldTableRbr_extract_eq (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (st : Stmt (basefoldTableReduction hm S dom q))
    (rs : List (TableMsg F Op t × F)) (π : TableMsg F Op t) (ρ : F)
    (w : (Fin m → Bool) → F) :
    (basefoldTableRbr hm S dom q hcard hdt hq).extract st ⟨rs ++ [(π, ρ)], none⟩ w
      = extractTable dom m q π.cols :=
  tableExtract_append dom m q rs π ρ w

/-! ## The backward composition (Construction B.5) returns the committed table -/

/-- The Construction B.5 chain, from the top, on a nonempty transcript: the
output is the decoder of the FIRST round's message. -/
theorem basefoldTableRbr_wAt_zero (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (st : Stmt (basefoldTableReduction hm S dom q))
    (e : TableMsg F Op t × F) (rest : List (TableMsg F Op t × F)) (w' : (Fin m → Bool) → F) :
    wAt (basefoldTableRbr hm S dom q hcard hdt hq) st (e :: rest) w' 0
      = extractTable dom m q e.1.cols := by
  rw [wAt_of_lt _ _ _ _ (by simp)]
  rfl

/-- ⭐ **The straightline FS extractor returns the committed table.**  On any
FS proof string whose first-round openings verify against a root committing
`basefoldWord dom tbl`, `srExtract` (Construction B.5, CITED) outputs `tbl` —
whatever candidate `w'` the prover supplied.  The extracted witness is
attached to the prover's commitment, not handed over by the prover. -/
theorem basefoldTableRbr_srExtract_committed (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (s : ℕ)
    (o : SrOutput (basefoldTableReduction hm S dom q) s) (ρs : Fin m → F)
    (log : List (SrMove (basefoldTableReduction hm S dom q) s × F))
    {tbl : (Fin m → Bool) → F} (hrt : o.stmt.x.rt = S.commit (basefoldWord dom tbl))
    (hver : ∀ i, (o.πs i).Opens S q o.stmt.x.rt) :
    srExtract (basefoldTableRbr hm S dom q hcard hdt hq) s o ρs log = tbl := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold srExtract
  rw [List.ofFn_succ, basefoldTableRbr_wAt_zero]
  exact extractTable_committed S dom hcard hdt hq hrt (hver 0)

/-! ## Fiat–Shamir -/

/-- ⭐ **The table-witness leg, Fiat–Shamir compiled.**  Straightline,
loss-free, with the grinding factor named: a `t`-query ROM adversary whose
output claim `(rt, z, H)` has NO table witness (no `tbl` with `rt` committing
it and `mle tbl z = H`) and whose FS-compiled transcript is accepted succeeds
with probability at most `(t + m) · 2/|F|`.  `fsKeystone_proved` (CITED)
applied to `basefoldTableRbr`. -/
theorem basefoldTable_fs_sound (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) :
    FsStraightlineKnowledgeSoundness (basefoldTableReduction hm S dom q) Set.univ
      (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F)) :=
  fsKeystone_proved.sound _ (basefoldTableRbr hm S dom q hcard hdt hq) Set.univ
    (fun _ => (2 : ℝ) / Fintype.card F)
    (fun _ _ => by positivity)
    (fun i st _ δ _ => le_of_eq (basefoldTableRbr_err hm S dom q hcard hdt hq i st δ))

/-- ⭐ **The consumer-facing corollary, over `MleEvalClaim.Holds`.**  Any
`t`-query FS adversary that outputs a claim which does NOT hold
(`¬ c.Holds S dom`) yet has its proof string accepted with the prover's own
terminal candidate in the target relation succeeds with probability at most
`(t + m) · 2/|F|`.  This is the probabilistic content of
`Assurance/SpartanR1CS.lean`'s `SpartanOpeningProtocol` for BaseFold's
sumcheck leg; the deterministic `Accepts c → c.Holds` shape needs
accept-at-every-challenge, which is not this theorem. -/
theorem basefoldTable_fs_holds (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) (s t' : ℕ) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (P : SrProver (basefoldTableReduction hm S dom q) s) :
    uniformProb ((Fin t' → F) × (Fin m → F)) (fun coins =>
        let log := srTrace P coins.1
        let o := P.out (log.map Prod.snd)
        let ρs : Fin m → F := srFinalChal P coins.1 coins.2
        ¬ o.stmt.x.Holds S dom ∧
        ∃ (x' : BaseFoldTerminalClaim Root F m) (y' : Fin 1 → Unit),
          fiatShamir (basefoldTableReduction hm S dom q) s (fsOracle o ρs) o = some (x', y') ∧
          RelaxedMem (basefoldTableReduction hm S dom q).R' δ o.stmt.idx x' y' o.w')
      ≤ ((t' : ℝ) + (m : ℝ)) * (2 / Fintype.card F) := by
  obtain ⟨E, hE⟩ := basefoldTable_fs_sound hm S dom q hcard hdt hq
  refine le_trans (uniformProb_mono ?_) (hE s t' δ hδ P)
  intro coins h
  obtain ⟨hnot, hacc⟩ := h
  refine ⟨Set.mem_univ _, ?_, hacc⟩
  rintro ⟨ystar, ⟨hrt, hval⟩, -⟩
  exact hnot ⟨_, hrt, hval⟩

/-- ⭐ **Both resolutions of the leg compile at ONE price.**  The scalar leg
(`W := Unit`, table a parameter — `basefoldSumcheck_fs_sound`, CITED, its
first consumer) and the table-witness leg (`basefoldTable_fs_sound`) are
Fiat–Shamir straightline knowledge-sound at the same `(t + m) · 2/|F|`: the
witness upgrade — from a scalar-preservation statement to extraction of the
committed table — costs nothing at the FS layer.  The scalar half holds at
EVERY table, in particular at whatever `extractTable` returns. -/
theorem basefoldLeg_fs_both (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (hcard : 2 ^ m ≤ Fintype.card ι) (hdt : 2 ^ m ≤ t)
    (hq : Function.Injective (dom ∘ q)) :
    (∀ (tbl : (Fin m → Bool) → F) (z : Fin m → F),
      FsStraightlineKnowledgeSoundness (basefoldSumcheckReduction hm tbl z) Set.univ
        (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F))) ∧
    FsStraightlineKnowledgeSoundness (basefoldTableReduction hm S dom q) Set.univ
      (fun _s t _δ => ((t : ℝ) + (m : ℝ)) * (2 / Fintype.card F)) :=
  ⟨fun tbl z => basefoldSumcheck_fs_sound hm tbl z,
    basefoldTable_fs_sound hm S dom q hcard hdt hq⟩

/-! ## Accept-everywhere soundness: the deterministic reading of `[SPARTAN-pcs]`

`Assurance/SpartanR1CS.lean`'s `SpartanOpeningProtocol S dom Accepts` is
`∀ c, Accepts c → c.Holds S dom` — deterministic.  A protocol with soundness
error `2m/|F|` discharges it only at the accept-at-EVERY-challenge predicate:
a claim some prover strategy gets accepted at every challenge vector is true.
The probabilistic content is `basefoldTable_fs_holds` above; this section is
the deterministic corollary, proved from the landed adaptive whole-transcript
bound (`adaptive_sumcheck_soundness`, CITED) at `2m < |F|`, where the bound
is `< 1` and accept-everywhere (probability `1`) contradicts it. -/

omit [Fintype F] [DecidableEq F] in
/-- The padded schedule of the shorter tuple agrees with the longer one below
its length. -/
theorem chalOf_castSucc {v : ℕ} (ρs : Fin (v + 1) → F) {j : ℕ} (hj : j < v) :
    chalOf (fun i : Fin v => ρs i.castSucc) j = chalOf ρs j := by
  unfold chalOf
  rw [dif_pos hj, dif_pos (Nat.lt_succ_of_lt hj)]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- `scChain` at `i` reads only the challenge at `i - 1`. -/
theorem scChain_congr {H : F} {g : ℕ → Polynomial F} {χ χ' : ℕ → F} {i : ℕ}
    (h : ∀ j, j < i → χ j = χ' j) : scChain H g χ i = scChain H g χ' i := by
  cases i with
  | zero => rfl
  | succ n => simp only [scChain, h n (Nat.lt_succ_self n)]

omit [Fintype F] [DecidableEq F] in
/-- The run claim of a full `ofFn` transcript is the memoryless chain's last
value. -/
theorem scRunClaim_ofFn (H : F) (g : ℕ → Polynomial F) {v : ℕ} (ρs : Fin v → F) :
    scRunClaim H (List.ofFn fun i : Fin v => (g i, ρs i)) = scChain H g (chalOf ρs) v := by
  cases v with
  | zero => simp [scRunClaim, scChain]
  | succ v =>
      rw [List.ofFn_succ', List.concat_eq_append, scRunClaim_append_single]
      show _ = (g v).eval (chalOf ρs v)
      rw [← chalOf_coe ρs (Fin.last v)]
      rfl

omit [Fintype F] [DecidableEq F] in
/-- Completed-round validity of a full `ofFn` transcript, in the whole-transcript
sumcheck vocabulary: every round's polynomial has the degree bound and its
Boolean sum is the chain value before it. -/
theorem scRunValid_ofFn_iff (d : ℕ) (H : F) (g : ℕ → Polynomial F) :
    ∀ {v : ℕ} (ρs : Fin v → F),
      scRunValid d H (List.ofFn fun i : Fin v => (g i, ρs i)) ↔
        ∀ i, i < v → (g i).degree < ((d + 1 : ℕ) : WithBot ℕ) ∧
          (g i).eval 0 + (g i).eval 1 = scChain H g (chalOf ρs) i
  | 0, _ => by simp [scRunValid]
  | v + 1, ρs => by
      have ih := scRunValid_ofFn_iff d H g (fun i => ρs i.castSucc)
      rw [List.ofFn_succ', List.concat_eq_append, scRunValid_append_single]
      simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
      rw [ih, scRunClaim_ofFn]
      constructor
      · rintro ⟨hlt, hdeg, hsum⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · obtain ⟨h1, h2⟩ := hlt i hi'
          exact ⟨h1, h2.trans (scChain_congr fun j hj => chalOf_castSucc ρs (lt_trans hj hi'))⟩
        · exact ⟨hdeg, hsum.trans (scChain_congr fun j hj => chalOf_castSucc ρs hj)⟩
      · intro h
        refine ⟨fun i hi => ?_, (h v (Nat.lt_succ_self v)).1, ?_⟩
        · obtain ⟨h1, h2⟩ := h i (Nat.lt_succ_of_lt hi)
          exact ⟨h1, h2.trans (scChain_congr fun j hj => (chalOf_castSucc ρs (lt_trans hj hi)).symm)⟩
        · exact (h v (Nat.lt_succ_self v)).2.trans
            (scChain_congr fun j hj => (chalOf_castSucc ρs hj).symm)

/-- A predicate true everywhere has uniform probability exactly `1`. -/
theorem uniformProb_eq_one_of_forall {C : Type} [Fintype C] [Nonempty C] {p : C → Prop}
    (h : ∀ c, p c) : uniformProb C p = 1 := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- **Accept-at-every-challenge.**  Some prefix-measurable prover strategy —
round messages (polynomial + columns) as functions of the challenge prefix —
makes the table-witness verifier accept at EVERY challenge vector, each time
with a table candidate in the target relation.  This is the deterministic
`Accepts` at which `SpartanOpeningProtocol` can be discharged; the
probabilistic `Accepts` is priced by `basefoldTable_fs_holds`. -/
def BaseFoldTableAcceptsEverywhere (hm : 0 < m) (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (q : Fin t → ι) (c : MleEvalClaim Root F m) : Prop :=
  ∃ P : (ℕ → F) → ℕ → TableMsg F Op t,
    PrefixMeasurable (fun χ i => (P χ i).poly) ∧
    ∀ ρs : Fin m → F,
      ∃ (x' : BaseFoldTerminalClaim Root F m) (y' : Fin 1 → Unit) (w' : (Fin m → Bool) → F),
        basefoldTableVerify S q c (fun i => P (chalOf ρs) i) ρs = some (x', y') ∧
        (basefoldTableReduction hm S dom q).R' () x' y' w'

/-- The honest prover strategy for a claim on `tbl` at `z`: the honest round
polynomials, the honest columns, and the honest openings — a prefix-measurable
message family. -/
noncomputable def honestTableStrategy (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (q : Fin t → ι) (tbl : (Fin m → Bool) → F) (z : Fin m → F) (χ : ℕ → F) (i : ℕ) :
    TableMsg F Op t :=
  ⟨basefoldHonest tbl z χ i, fun j => basefoldWord dom tbl (q j),
    fun j => S.openAt (basefoldWord dom tbl) (q j)⟩

omit [Fintype F] [DecidableEq F] [Fintype ι] in
@[simp] theorem honestTableStrategy_poly (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (q : Fin t → ι) (tbl : (Fin m → Bool) → F) (z : Fin m → F) (χ : ℕ → F) (i : ℕ) :
    (honestTableStrategy S dom q tbl z χ i).poly = basefoldHonest tbl z χ i := rfl

omit [DecidableEq F] [Fintype ι] in
/-- **Satisfiable**: the honest prover — honest round polynomials, honest
columns — accepts at EVERY challenge vector on the honest claim, with the
honest table as terminal candidate.  The accept-everywhere predicate is
inhabited, so its discharge of `[SPARTAN-pcs]` below is not vacuous. -/
theorem basefoldTable_honest_acceptsEverywhere (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (tbl : (Fin m → Bool) → F) (z : Fin m → F) :
    BaseFoldTableAcceptsEverywhere hm S dom q ⟨S.commit (basefoldWord dom tbl), z, mle tbl z⟩ := by
  classical
  refine ⟨honestTableStrategy S dom q tbl z, ?_, fun ρs => ?_⟩
  · intro χ χ' i h
    simp only [honestTableStrategy_poly]
    exact basefoldHonest_prefixMeasurable tbl z χ χ' i h
  have hvalid : scRunValid 2 (mle tbl z) (tableRounds (List.ofFn fun i : Fin m =>
      (honestTableStrategy S dom q tbl z (chalOf ρs) i, ρs i))) := by
    rw [tableRounds_ofFn]
    simp only [honestTableStrategy_poly]
    rw [scRunValid_ofFn_iff 2 (mle tbl z) (basefoldHonest tbl z (chalOf ρs)) ρs]
    intro i hi
    exact ⟨basefoldHonest_degree tbl z (chalOf ρs) i hi, basefoldHonest_boolean_sum tbl z ρs i hi⟩
  refine ⟨⟨S.commit (basefoldWord dom tbl), z, ρs, scRunClaim (mle tbl z)
      (tableRounds (List.ofFn fun i : Fin m =>
        (honestTableStrategy S dom q tbl z (chalOf ρs) i, ρs i)))⟩,
    fun _ => (), tbl, ?_, rfl, ?_⟩
  · unfold basefoldTableVerify
    rw [if_pos ⟨fun _ _ => S.verifyOpen_commit _ _, hvalid⟩]
  · show scRunClaim (mle tbl z) (tableRounds (List.ofFn fun i : Fin m =>
        (honestTableStrategy S dom q tbl z (chalOf ρs) i, ρs i))) = mle tbl ρs * eqMle z ρs
    rw [tableRounds_ofFn]
    simp only [honestTableStrategy_poly]
    rw [scRunClaim_ofFn (mle tbl z) (basefoldHonest tbl z (chalOf ρs)) ρs,
      basefold_sumcheck_terminal]

/-- ⭐ **Accept-everywhere soundness — the deterministic `[SPARTAN-pcs]`
content.**  Inside the degree window and at `2m < |F|`, every claim the
table-witness verifier accepts at EVERY challenge vector HOLDS: its root
commits a table whose multilinear takes the claimed value.  Proof: the
prover's own terminal candidates all commit to the same table `tbl₀`
(binding, `basefoldWord_injective`); if the claimed value were wrong, every
challenge vector would accept a false claim — probability `1` — against
`adaptive_sumcheck_soundness`'s `2m/|F| < 1` (CITED).  With `Accepts :=
BaseFoldTableAcceptsEverywhere`, this IS `SpartanOpeningProtocol S dom Accepts`
unfolded; the Assurance-side restatement is a one-line application. -/
theorem basefoldTable_acceptsEverywhere_holds (hm : 0 < m)
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F) (q : Fin t → ι)
    (hcard : 2 ^ m ≤ Fintype.card ι) (hF : 2 * m < Fintype.card F)
    (c : MleEvalClaim Root F m) (hacc : BaseFoldTableAcceptsEverywhere hm S dom q c) :
    c.Holds S dom := by
  classical
  obtain ⟨P, hpm, hall⟩ := hacc
  have hunpack : ∀ ρs : Fin m → F, ∃ tbl : (Fin m → Bool) → F,
      c.rt = S.commit (basefoldWord dom tbl) ∧
      scRunValid 2 c.val (tableRounds (List.ofFn fun i => (P (chalOf ρs) i, ρs i))) ∧
      scRunClaim c.val (tableRounds (List.ofFn fun i => (P (chalOf ρs) i, ρs i)))
        = mle tbl ρs * eqMle c.pt ρs := by
    intro ρs
    obtain ⟨x', y', w', hver, hrt, hval⟩ := hall ρs
    unfold basefoldTableVerify at hver
    split_ifs at hver with hv
    have hx : x' = ⟨c.rt, c.pt, ρs,
        scRunClaim c.val (tableRounds (List.ofFn fun i => (P (chalOf ρs) i, ρs i)))⟩ :=
      (congrArg Prod.fst (Option.some.inj hver)).symm
    subst hx
    exact ⟨w', hrt, hv.2, hval⟩
  obtain ⟨tbl₀, hrt₀, -, -⟩ := hunpack (fun _ => 0)
  have htbl : ∀ tbl, c.rt = S.commit (basefoldWord dom tbl) → tbl = tbl₀ := fun tbl h =>
    basefoldWord_injective S dom hcard (h.symm.trans hrt₀)
  refine ⟨tbl₀, hrt₀, ?_⟩
  by_contra hne
  have hfalse : ∀ ρs : Fin m → F,
      AdaptiveAcceptsFalse (fun χ i => (P χ i).poly) (basefoldHonest tbl₀ c.pt) c.val
        (mle tbl₀ c.pt) ρs := by
    intro ρs
    obtain ⟨tbl, hrt, hvalid, hclaim⟩ := hunpack ρs
    rw [htbl tbl hrt] at hclaim
    rw [tableRounds_ofFn, scRunValid_ofFn_iff 2 c.val (fun i => (P (chalOf ρs) i).poly) ρs]
      at hvalid
    rw [tableRounds_ofFn, scRunClaim_ofFn c.val (fun i => (P (chalOf ρs) i).poly) ρs] at hclaim
    exact ⟨fun i hi => (hvalid i hi).2,
      hclaim.trans (basefold_sumcheck_terminal tbl₀ c.pt ρs).symm, fun h => hne h.symm⟩
  have hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      ((fun χ i => (P χ i).poly) χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ) := by
    intro χ i hi
    obtain ⟨tbl, -, hvalid, -⟩ := hunpack (fun j => χ j)
    rw [tableRounds_ofFn,
      scRunValid_ofFn_iff 2 c.val (fun i => (P (chalOf fun j : Fin m => χ j) i).poly)
        (fun j => χ j)] at hvalid
    have hp := hpm χ (chalOf fun j : Fin m => χ j) i
      (fun j hj => by rw [chalOf, dif_pos (lt_trans hj hi)])
    show (P χ i).poly.degree < _
    rw [show (P χ i).poly = (P (chalOf fun j : Fin m => χ j) i).poly from hp]
    exact (hvalid i hi).1
  have hbound := adaptive_sumcheck_soundness (v := m) (d := 2) (H := c.val) hpm
    (basefoldHonest_prefixMeasurable tbl₀ c.pt) hdeg
    (fun χ i hi => basefoldHonest_degree tbl₀ c.pt χ i hi)
    (fun r i hi => basefoldHonest_boolean_sum tbl₀ c.pt r i hi)
  rw [uniformProb_eq_one_of_forall hfalse] at hbound
  have hF' : (m : ℝ) * (((2 : ℕ) : ℝ) / (Fintype.card F : ℝ)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast (show m * 2 < Fintype.card F by omega)
  exact absurd hbound (not_le.mpr hF')

/-! ## F₅ keystones: the landed one-variable BaseFold instance -/

namespace BaseFoldRbrTableExample

open BaseFoldExample ProximityExample MleEvalClaimExample

/-- The two query positions `{0, 1}` — `t = 2 = 2^1`, at the erasure bound. -/
def q₂ : Fin 2 → Fin 4 := ![0, 1]

/-- **Premise inhabitation**: the positions are distinct under the level-0
domain. -/
theorem q₂_inj : Function.Injective (dom0 ∘ q₂) := by decide

/-- The ideal commitment over the level-0 domain — the inhabited binding floor. -/
abbrev S₄ : BindingCommitment (Fin 4 → ZMod 5) (ZMod 5) (Fin 4) Unit :=
  idealCommitment (ZMod 5) (Fin 4)

/-- The native Def-4.2 object on the landed F₅ BaseFold instance. -/
noncomputable def rbrF5 :
    RbrKnowledgeSoundness (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂) :=
  basefoldTableRbr (by decide) S₄ dom0 q₂ (by decide) (by decide) q₂_inj

/-- The honest first-round message: the honest round polynomial and the two
honest columns of the committed word. -/
noncomputable def honestMsg : TableMsg (ZMod 5) Unit 2 :=
  ⟨basefoldHonest table ![3] (fun _ => 0) 0, fun j => basefoldWord dom0 table (q₂ j),
    fun _ => ()⟩

/-- **Satisfiable / the extractor computes**: from the honest message's two
opened columns, verified against the root, the extractor returns EXACTLY
`table` — the whole binding → erasure → window → Möbius pipeline fires on
built objects. -/
theorem extractTable_recovers_F5 : extractTable dom0 1 q₂ honestMsg.cols = table :=
  extractTable_committed (rt := basefoldWord dom0 table) S₄ dom0 (by decide) (by decide)
    q₂_inj rfl (fun _ => rfl)

/-- The honest claim as a native statement of the table-witness reduction —
`MleEvalClaimExample.honestClaim`, reused. -/
noncomputable def stF5 : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂) :=
  ⟨(), honestClaim, fun _ => ()⟩

/-- **Satisfying witness**: the knowledge state is alive on the honest claim,
at the empty transcript, with the honest table as witness. -/
theorem rbrF5_state_alive :
    rbrF5.kstate.state (1 / 2) stF5 Transcript.empty table = true := by
  refine (rbrF5.kstate.empty_iff (1 / 2) ?_ stF5 table).mpr ?_
  · change (1 / 2 : ℝ) ∈ Set.Ioo 0 1
    norm_num
  · refine ⟨stF5.y, ⟨rfl, rfl⟩, ?_⟩
    rw [fracHamming_self]
    norm_num

/-- The other table with the same value at `z = 3`: `[2, 1]`, and
`mle [2,1] 3 = 3·2 + 3·1 = 4 = mle [1,2] 3`. -/
def table' : (Fin 1 → Bool) → ZMod 5 := fun b => if b 0 then 1 else 2

theorem table_ne_table' : table ≠ table' := by decide

theorem mle_table'_eq : mle table' ![3] = mle table ![3] := by decide

/-- **Falsifier**: the root committing `[2, 1]`, with the honest claimed value
`4` at `z = 3`, is REFUSED by the source relation at witness `table` — same
scalar, different root — and accepted at witness `[2, 1]`. -/
theorem basefoldTable_teeth_f5 :
    ¬ (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table ∧
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂).R ()
        ⟨S₄.commit (basefoldWord dom0 table'), ![3], mle table ![3]⟩ (fun _ => ()) table' :=
  basefoldTable_source_teeth (by decide) S₄ dom0 q₂ (by decide) table_ne_table'
    mle_table'_eq _

/-- The round price computes to `2/5` on the live instance. -/
theorem rbrF5_err (i : Fin 1)
    (st : Stmt (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂)) (δ : ℝ) :
    rbrF5.err i st δ = 2 / 5 := by
  rw [rbrF5, basefoldTableRbr_err, ZMod.card]
  norm_num

/-- The compiled table-witness leg on the F₅ instance: a `t`-query FS
adversary whose claim has no table witness is accepted with probability at
most `(t + 1) · 2/5` — a live finite-field number. -/
theorem tableFs_sound_f5 :
    FsStraightlineKnowledgeSoundness
      (basefoldTableReduction (m := 1) (by decide) S₄ dom0 q₂) Set.univ
      (fun _s t _δ => ((t : ℝ) + 1) * (2 / 5)) := by
  have h := basefoldTable_fs_sound (m := 1) (by decide) S₄ dom0 q₂ (by decide) (by decide)
    q₂_inj
  have hfun : (fun (_s t : ℕ) (_δ : ℝ) =>
        ((t : ℝ) + ((1 : ℕ) : ℝ)) * (2 / (Fintype.card (ZMod 5) : ℝ)))
      = fun (_s t : ℕ) (_δ : ℝ) => ((t : ℝ) + 1) * (2 / 5) := by
    funext s t δ
    rw [ZMod.card]
    norm_num
  rwa [hfun] at h

end BaseFoldRbrTableExample

/-- info: 'Minidregg.Selvage.extractTable_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extractTable_committed
/-- info: 'Minidregg.Selvage.basefoldTableRbr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbr
/-- info: 'Minidregg.Selvage.basefoldTableRbr_srExtract_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTableRbr_srExtract_committed
/-- info: 'Minidregg.Selvage.basefoldTable_fs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_fs_sound
/-- info: 'Minidregg.Selvage.basefoldTable_fs_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_fs_holds
/-- info: 'Minidregg.Selvage.basefoldLeg_fs_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldLeg_fs_both
/-- info: 'Minidregg.Selvage.basefoldTable_honest_acceptsEverywhere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_honest_acceptsEverywhere
/-- info: 'Minidregg.Selvage.basefoldTable_acceptsEverywhere_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldTable_acceptsEverywhere_holds
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableExample.extractTable_recovers_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableExample.extractTable_recovers_F5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableExample.rbrF5_state_alive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BaseFoldRbrTableExample.rbrF5_state_alive
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableExample.basefoldTable_teeth_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldRbrTableExample.basefoldTable_teeth_f5
/-- info: 'Minidregg.Selvage.BaseFoldRbrTableExample.tableFs_sound_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BaseFoldRbrTableExample.tableFs_sound_f5

end Minidregg.Selvage
