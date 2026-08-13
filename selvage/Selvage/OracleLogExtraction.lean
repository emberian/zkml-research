/-
# Selvage.OracleLogExtraction — [ACC-rbr-bcs-shifted-resid](a) route (i): the
ORACLE-LOG vocabulary — straightline extraction that reads the prover's
random-oracle QUERY LOG.

`Selvage/AccRbrBcsShifted.lean` built the fold-root carrier and named the residual
exactly: at the shifted round-`i+1` extension the FRESH challenge is INERT for
the fold data — the newly scorable increment `w_i = ρ_i⁻¹ • (h_{i+1} − h_i)` is
weighted by the ROUND-`i` challenge, already fixed when `h_{i+1}`'s root was
chosen — so Def 4.2's `uniformProb` over the fresh challenge cannot be priced
by the landed fixed-pair `accSound_rbr` event. Route (i) said: go OUTSIDE
`Reduction`'s oracle-free shape, to the BCS/ROM mechanism the deployment
actually uses — the prover derives every challenge by QUERYING the oracle, so
its QUERY LOG carries the temporal record `Reduction` erases. This file builds
that vocabulary and proves the parts of the route that close today.

What lands here:
* `OracleLog` (+ `answerOf`, the cons/nil laws, `answerOf_eq_none`) — the
  prover's query run as the extraction's input; NOT a mirror: the landed SR/FS
  game's trace IS an oracle log (`srTrace_answerOf`, citing
  `srHandlerRun_lookup`), and **the FS challenges ARE log reads**
  (`srFinalChal_eq_answerOf`, citing `srFinalChal_eq_lookup`). The fresh horn
  is a theorem: an UNQUERIED designated prefix gets its challenge from the
  output-independent fresh coin (`unqueried_chal_fresh`) — not querying
  forfeits grinding, and querying exposes the try to the log.
* `StraightlineOracleExtractor` / `OracleLogReduction` — the
  outside-`Reduction` objects: an extractor consuming ONLY (output, log) — no
  challenge-vector input, no rewinding — and a `Reduction` AUGMENTED with the
  ROM game and a log-only extractor at the `(t + k)·εlog` grinding price.
  Every inhabitant lands INSIDE the landed FS/SR statements
  (`OracleLogReduction.fs_sound` / `.sr_sound`, riding `fsStraightline_iff_sr`,
  CITED) — the same `(t + k)` error shape `fsKeystone_proved` proves and
  `lightClientGrinding_sound` deploys as `(t + n)`. The shape is inhabited
  (`trivialOracleLogReduction`), so the structure is not vacuous.
* `logIncrement` / `shiftedLogExtractor` — THE log extractor at the shifted
  BCS alphabet: read the log's ANSWER to the designated round-`i` prefix query
  (that is `ρ_i` — `srFinalChal_eq_answerOf`) and the two consecutive fold-root
  messages, return `ρ_i⁻¹ • (h_{i+1} − h_i)`. PROVED: on honestly-committed
  logs it recovers the increments EXACTLY (`logIncrement_recovers`, via
  `shifted_increment_recovered`, CITED — the seam's `γ⁻¹`-difference map now
  fired from the LOG's answer); it reads the log ONLY at the round-`i` query
  (`logIncrement_congr` — the shifted round event's fresh challenge is inert
  for the extracted witness, the residual's diagnosis now a THEOREM); and it
  genuinely needs the query (`logIncrement_none_of_unqueried` — no query, no
  witness; the log is load-bearing).
* `adaptiveIncrement_sound_via_log` — the target, STATEMENT-FIRST: an
  `OracleLogReduction` for `accReductionBcsShifted` whose extractor IS the
  log-read increment map wherever the log answers. NOT inhabited here;
  inhabiting it is the remaining mass, sharpened below to ONE named per-slot
  lemma `[ORACLE-LOG-program]` (`OracleLogProgram`, a formal `Prop`) plus
  named engineering.

**Keystones** (F₅, landed objects REUSED): `outF5`/`logF5` — a concrete
honest output and 3-entry query log on the landed shifted chain;
`log_recovers_F5` (satisfiable: the extractor reads `msEx` off the log,
`logIncrement_recovers` fired); `log_loadbearing_F5` (teeth: the EMPTY log
extracts nothing) + `log_wrong_answer_F5` (sharper teeth: a log answering the
round-0 query with `2` instead of `1` extracts `2⁻¹ • msEx 0 ≠ msEx 0` — the
ANSWER is load-bearing, not just the query's presence); `log_inert_F5` (the
inertness fired: changing the final — inert — query's answer moves nothing);
`adaptive_pins_extractor_F5` (the statement's clause has teeth: ANY inhabitant
must output `msEx` on the built log). No `sorry`, no vacuous `Prop := True`.
-/
import Selvage.Rbr
import Selvage.FiatShamir
import Selvage.AccRbrBcs
import Selvage.AccRbrBcsShifted

namespace Minidregg.Selvage

/-! ## The oracle log — the prover's query run, as the extraction's input -/

/-- **The prover's random-oracle query log**: the time-ordered sequence of
(query, answer) cells a game run recorded. Definitionally the SR/FS game's
trace type (`srTrace P c : OracleLog (SrMove r s) r.Chal` on the nose) and the
handler's `Oracle.log` field — the log is the LANDED game's object, read at
extraction time, not a new side structure. -/
abbrev OracleLog (Q C : Type) : Type := List (Q × C)

namespace OracleLog

variable {Q C : Type}

section Answers

open Classical

/-- The log's answer to a query: the FIRST recorded response, `none` if the
query was never made — the same partial-map reading as `Oracle.lookup`
(`Selvage/FiatShamir.lean`) and the game's `find?` discipline
(`Selvage/Rbr.lean`, specialization 5). -/
noncomputable def answerOf (L : OracleLog Q C) (q : Q) : Option C :=
  (L.find? fun e => decide (e.1 = q)).map Prod.snd

@[simp] lemma answerOf_nil (q : Q) :
    answerOf ([] : OracleLog Q C) q = none := rfl

lemma answerOf_cons_self (q : Q) (a : C) (L : OracleLog Q C) :
    answerOf ((q, a) :: L) q = some a := by
  unfold answerOf
  rw [List.find?_cons_of_pos (by simp)]
  rfl

lemma answerOf_cons_of_ne {q q' : Q} (h : q' ≠ q) (a : C)
    (L : OracleLog Q C) : answerOf ((q, a) :: L) q' = answerOf L q' := by
  unfold answerOf
  rw [List.find?_cons_of_neg (by simpa using Ne.symm h)]

/-- A query is unanswered iff it never appears — the "didn't query the RO"
event, as the log states it. -/
lemma answerOf_eq_none {L : OracleLog Q C} {q : Q} :
    answerOf L q = none ↔ ∀ e ∈ L, e.1 ≠ q := by
  unfold answerOf
  simp [List.find?_eq_none]

end Answers

end OracleLog

/-! ## The landed game IS a log: the bridges

The oracle-log route is only honest if "the log" is the LANDED game's object.
Three bridges, all cited into place: the trace's answers are the handler's
partial map, the FS challenges are log reads, and unqueried prefixes fall back
to fresh coins. -/

section GameBridge

variable {r : Reduction} {s t : ℕ}

/-- **The game's trace, read as an `OracleLog`, denotes the landed handler's
partial map** — `srHandlerRun_lookup` (`Selvage/FiatShamir.lean`, CITED), turned
around: `answerOf` on `srTrace` is `Oracle.lookup` on the handler run. -/
theorem srTrace_answerOf (P : SrProver r s) (c : Fin t → r.Chal)
    (q : SrMove r s) :
    OracleLog.answerOf (srTrace P c) q = (srHandlerRun P c).1.lookup q :=
  (srHandlerRun_lookup P c q).symm

/-- **The FS challenges ARE log reads**: the game's final challenge at slot
`i` is the log's answer to the designated round-`i` prefix query, with the
fresh coin as fallback (`srFinalChal_eq_lookup`, CITED, through
`srTrace_answerOf`). This is the oracle-log route's ground fact: everything
the FS verifier derives, the prover's own query log already carries — an
extractor reading the log reads the SAME randomness the verifier uses. -/
theorem srFinalChal_eq_answerOf (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k) :
    srFinalChal P c d i
      = (OracleLog.answerOf (srTrace P c) ((srOut P c).query i)).getD (d i)
    := by
  rw [srFinalChal_eq_lookup, srTrace_answerOf]

/-- **The fresh horn — not querying forfeits grinding**: if the designated
round-`i` prefix is NOT in the log, the challenge the FS verifier uses is the
fresh coin `d i`, drawn AFTER the adversary's entire output is fixed. In
particular both fold roots `h_i, h_{i+1}` are output-fixed before the
challenge exists — exactly the fixed-pair territory the landed round events
price (`freshBad_le`'s conditioning, `Selvage/Depth.lean`, CITED). A grinding
adversary must QUERY to see a challenge before committing, and each query is
a log cell the extractor reads: grinding is exposed, abstention is
fixed-pair. -/
theorem unqueried_chal_fresh (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k)
    (h : OracleLog.answerOf (srTrace P c) ((srOut P c).query i) = none) :
    srFinalChal P c d i = d i := by
  rw [srFinalChal_eq_answerOf, h]
  rfl

end GameBridge

/-! ## The straightline oracle extractor, and the log-augmented reduction -/

/-- **A straightline oracle extractor** for reduction `r` at salt size `s`: a
deterministic function of the prover's OUTPUT and its QUERY LOG alone. No
rewinding, and — unlike the landed `SrExtractor` — NO challenge-vector input:
every challenge it needs must be READ from the log, which is where the
verifier's challenges live (`srFinalChal_eq_answerOf`). This is the BCS
straightline-extraction shape: the witness is recovered from the queries the
prover made. -/
abbrev StraightlineOracleExtractor (r : Reduction) (s : ℕ) : Type :=
  SrOutput r s → OracleLog (SrMove r s) r.Chal → r.W

/-- Every log-only extractor is in particular an `SrExtractor` — discard the
supplied challenge vector; the log is the only randomness source it reads.
The log route therefore lands INSIDE the landed FS/SR game, not beside it.
(The converse direction is NOT free: an `SrExtractor` may read the fallback
coins `d` through its challenge-vector input, which no log contains — that
asymmetry is exactly why the log-only shape is the stronger, deployment-
faithful one.) -/
def StraightlineOracleExtractor.toSr {r : Reduction} {s : ℕ}
    (E : StraightlineOracleExtractor r s) : SrExtractor r s :=
  fun o _ρs log => E o log

section LogReduction

/-- **The log-augmented reduction** — the outside-`Reduction` object
`[ACC-rbr-bcs-shifted-resid]`(a) route (i) names. `Reduction` is oracle-free:
its verifier and Def-4.2 extractor never see a query, which is precisely why
the shifted schedule's lagged roots cannot be priced there. This object keeps
the reduction and AUGMENTS it with the ROM game: the soundness clause runs in
the landed lazily-sampled game (`srTrace`/`srFinalChal`/`fiatShamir`, all
CITED — nothing re-derived), and the extractor consumes the QUERY LOG. The
error carries the `(t + k)` grinding factor of `fsKeystone_proved` — the
per-query try-count `lightClientGrinding_sound` deploys as `(t + n)` — times
the per-slot price `εlog`: each fresh challenge the adversary grinds costs a
query slot, and the log exposes it. -/
structure OracleLogReduction (r : Reduction) (Z : Set (Stmt r))
    (εlog : ℝ → ℝ) : Type where
  /-- The straightline log extractor, one per salt size (the BCS salt
  channel; `s = 0` is plain FS). -/
  extractLog : (s : ℕ) → StraightlineOracleExtractor r s
  /-- The ROM-game soundness bound at the grinding price `(t + k) · εlog`:
  the probability that a `t`-query adversary lands in `Z`, the FS verifier
  accepts with the candidate witness in `R'_{≤δ}`, and the LOG-extracted
  witness fails `R_{≤δ}`. -/
  sound_log : ∀ (s t : ℕ), ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ P : SrProver r s,
    uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) (fun coins =>
      let log := srTrace P coins.1
      let o := P.out (log.map Prod.snd)
      let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
      o.stmt ∈ Z ∧
      ¬ RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y (extractLog s o log) ∧
      ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
        fiatShamir r s (fsOracle o ρs) o = some (x', y') ∧
        RelaxedMem r.R' δ o.stmt.idx x' y' o.w')
      ≤ ((t : ℝ) + (r.k : ℝ)) * εlog δ

/-- **Any log-augmented inhabitant lands the landed FS statement** at the
same `(t + k) · εlog` — the WARP-B.4 / `fsKeystone_proved` error shape. The
implication is one-directional by design (`toSr` forgets nothing the log-only
extractor ever had), so the log route strengthens, never forks, the landed
transcript layer. -/
theorem OracleLogReduction.fs_sound {r : Reduction} {Z : Set (Stmt r)}
    {εlog : ℝ → ℝ} (olr : OracleLogReduction r Z εlog) :
    FsStraightlineKnowledgeSoundness r Z
      (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εlog δ) := by
  refine ⟨fun s => (olr.extractLog s).toSr, ?_⟩
  intro s t δ hδ P
  exact olr.sound_log s t δ hδ P

/-- The same inhabitant through the BCS bridge (`fsStraightline_iff_sr`,
CITED): straightline state-restoration knowledge soundness, WARP Def B.2. -/
theorem OracleLogReduction.sr_sound {r : Reduction} {Z : Set (Stmt r)}
    {εlog : ℝ → ℝ} (olr : OracleLogReduction r Z εlog) :
    StraightlineSrKnowledgeSoundness r Z
      (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εlog δ) :=
  (fsStraightline_iff_sr r Z _).mp olr.fs_sound

private lemma relaxedMem_of_total {Idx X A W : Type} {n : ℕ}
    {R : Idx → X → (Fin n → A) → W → Prop}
    (hR : ∀ idx x y w, R idx x y w) {δ : ℝ} (hδ : 0 ≤ δ)
    (idx : Idx) (x : X) (y : Fin n → A) (w : W) :
    RelaxedMem R δ idx x y w :=
  ⟨y, hR idx x y w, by rw [fracHamming_self]; exact hδ⟩

/-- **The augmented shape is inhabited** — `trivialReduction`
(`Selvage/Depth.lean`, CITED) carries an `OracleLogReduction` at `εlog = 0`: its
source relation is total, so the log-extraction-failure clause is empty and
the game event never fires. The SHAPE is non-vacuous; inhabiting it at the
SHIFTED alphabet is the open mass (`adaptiveIncrement_sound_via_log` /
`[ORACLE-LOG-program]`, below). -/
noncomputable def trivialOracleLogReduction :
    OracleLogReduction trivialReduction Set.univ (fun _ => 0) where
  extractLog := fun _s _o _log => ()
  sound_log := by
    intro s t δ hδ P
    refine le_trans (le_of_eq (uniformProb_false fun coins hev => ?_)) ?_
    · obtain ⟨-, hfail, -⟩ := hev
      exact hfail
        (relaxedMem_of_total (fun _ _ _ _ => trivial) hδ.1.le _ _ _ _)
    · rw [mul_zero]

end LogReduction

/-! ## The shifted alphabet: the log reads the increment -/

section ShiftedLog

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- **The log-read increment** at shifted round `i`: read (i) the log's
ANSWER to the designated round-`i` prefix query — that answer IS the
challenge `ρ_i` that folded the increment (`srFinalChal_eq_answerOf`) — and
(ii) the two consecutive fold-root messages `π_i, π_{i+1}` of the output,
whose synthesized words differ by exactly `ρ_i • w_i` (`shifted_alignment`,
CITED). Return `ρ_i⁻¹ • (h_{i+1} − h_i)`; `none` when the prover never made
the round-`i` query — the log is load-bearing (teeth below), and the
unqueried case is the fresh-coin horn (`unqueried_chal_fresh`), not this
extractor's business. -/
noncomputable def logIncrement {s : ℕ}
    (o : SrOutput (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (L : OracleLog (SrMove (accReductionBcsShifted C foldRoot ch hm hch δs
      hδpos hδone S dom d q) s) F)
    (i : Fin ch.length) : Option (Fin m → F) :=
  (L.answerOf (o.query i.castSucc)).map fun ρ =>
    ρ⁻¹ • (bcsWord dom d q (o.πs i.succ) - bcsWord dom d q (o.πs i.castSucc))

/-- **The shifted straightline log extractor** — the whole witness family
read off (output, log) alone: each increment via `logIncrement`, defaulting
to `0` on unqueried rounds (where the challenge is a fresh coin and the
fixed-pair events apply instead). It never receives a challenge vector: the
verifier's challenges are log reads (`srFinalChal_eq_answerOf`), and this
object reads them the same way. -/
noncomputable def shiftedLogExtractor (s : ℕ) :
    StraightlineOracleExtractor
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q)
      s :=
  fun o L i =>
    (logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i).getD 0

/-- **The inertness diagnosis, now a theorem**: the round-`i` log increment
reads the log at the designated round-`i` query ONLY — two logs agreeing
there extract the SAME increment, however they differ elsewhere. In
particular the answer at the round-`i+1` query — the FRESH challenge of Def
4.2's shifted round event, the one `[ACC-rbr-bcs-shifted-resid]`(a)
diagnosed as inert — never enters: no per-round bound quantifying over that
fresh answer can constrain the extracted witness, because the witness does
not read it. The leverage must sit where the log says the challenge was
born, which is what `[ORACLE-LOG-program]` prices. -/
theorem logIncrement_congr {s : ℕ}
    (o : SrOutput (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    {L L' : OracleLog (SrMove (accReductionBcsShifted C foldRoot ch hm hch
      δs hδpos hδone S dom d q) s) F}
    (i : Fin ch.length)
    (h : L.answerOf (o.query i.castSucc) = L'.answerOf (o.query i.castSucc)) :
    logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i
      = logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L' i
    := by
  unfold logIncrement
  rw [h]

/-- **The log recovers the increments** — the straightline-extraction
closure: on any output whose messages are the honest shifted fold-root
recommitments at schedule `ρs`, and any log answering the designated queries
with `ρs`, the round-`i` log increment is EXACTLY the committed increment
`ms i` (`shifted_increment_recovered`, CITED — the seam's `γ⁻¹`-difference
map, fired from the LOG's answer rather than a passed challenge vector). The
witness is a function of the prover's own queries: BCS straightline
extraction, at the shifted alphabet. -/
theorem logIncrement_recovers {s : ℕ} (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q))
    {f₀ : Fin m → F} {ms : Fin ch.length → Fin m → F}
    (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (o : SrOutput (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (L : OracleLog (SrMove (accReductionBcsShifted C foldRoot ch hm hch δs
      hδpos hδone S dom d q) s) F)
    (ρs : Fin (ch.length + 1) → F)
    (hans : ∀ c : Fin (ch.length + 1),
      L.answerOf (o.query c) = some (ρs c))
    (hmsg : ∀ c : Fin (ch.length + 1), o.πs c
      = shiftedMsg S q (padSched fun j : Fin ch.length => ρs j.castSucc)
          f₀ ms (c : ℕ))
    (i : Fin ch.length) (hρ : ρs i.castSucc ≠ 0) :
    logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i
      = some (ms i) := by
  have hpad : padSched (fun j : Fin ch.length => ρs j.castSucc) (i : ℕ)
      = ρs i.castSucc := by
    rw [padSched_lt _ i.isLt]
  unfold logIncrement
  rw [hans i.castSucc, hmsg i.succ, hmsg i.castSucc]
  refine congrArg some ?_
  rw [Fin.val_succ, Fin.val_castSucc, ← hpad]
  exact shifted_increment_recovered S dom hdt hq _ hf₀ hms i
    (by rw [hpad]; exact hρ)

/-- **Teeth, generic — the log is load-bearing**: a prover that never made
the round-`i` designated query gives the extractor NOTHING to read; the
straightline extraction genuinely needs the query. (That prover's challenge
is then the fresh coin — `unqueried_chal_fresh` — so it bought fixed-pair
scoring by abstaining; the two horns partition every run.) -/
theorem logIncrement_none_of_unqueried {s : ℕ}
    (o : SrOutput (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (L : OracleLog (SrMove (accReductionBcsShifted C foldRoot ch hm hch δs
      hδpos hδone S dom d q) s) F)
    (i : Fin ch.length)
    (h : L.answerOf (o.query i.castSucc) = none) :
    logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i
      = none := by
  unfold logIncrement
  rw [h]
  rfl

/-- **[ACC-rbr-bcs-shifted-resid](a) route (i), STATED** (house law:
statement-first; the obligation named before proof work): the adaptive
increment is priced via the oracle log — an `OracleLogReduction` for the
shifted fold-root reduction whose extractor IS the log-read increment map
wherever the log answers. A prover that makes the fresh challenge score a
false increment must have QUERIED the RO in a way the log exposes; grinding
on `ρ_i` costs one query per try, priced by the `(t + k)` factor — the
`lightClientGrinding_sound` `(t + n)` shape applied at the increment, with
the per-slot price `εlog`. NOT inhabited here — the remaining mass is
`[ORACLE-LOG-program]` (below) plus named engineering (module foot).

ATLAS keystone fields (obligation):
* satisfiable: TODO realizer — the hit-horn per-slot bound
  (`OracleLogProgram`) composed with the fresh-horn fixed-pair bound
  (`unqueried_chal_fresh` reattaches the pair: both roots are output-fixed
  when the challenge is fresh) through the `(t + k)` slot union
  (`GameSlotBound`'s choreography, `Selvage/Depth.lean`) — see the residual.
* teeth: the extractor clause pins every inhabitant's output on honest logs
  (`adaptive_pins_extractor_F5` PROVES this bites on the landed F₅ chain);
  and any `εlog` with `(0 + k) · εlog δ < 1` somewhere makes `sound_log` a
  genuine bound, not slack.
* premise-inhabitation: the augmented shape is inhabited
  (`trivialOracleLogReduction`); the shifted reduction and its honest
  accepted run are BUILT (`accReductionBcsShifted_F5`,
  `shifted_completeness_F5`, CITED), and the extractor the clause pins is
  BUILT and fires (`log_recovers_F5`). -/
def adaptiveIncrement_sound_via_log (εlog : ℝ → ℝ) : Prop :=
  ∃ olr : OracleLogReduction
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q)
      Set.univ εlog,
    ∀ (s : ℕ)
      (o : SrOutput (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
        hδone S dom d q) s)
      (L : OracleLog (SrMove (accReductionBcsShifted C foldRoot ch hm hch
        δs hδpos hδone S dom d q) s) F)
      (i : Fin ch.length) (w : Fin m → F),
      logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i
        = some w →
      olr.extractLog s o L i = w

/-- **[ORACLE-LOG-program] — the missing per-slot lemma, stated precisely.**
The hit horn: the round-`i` designated query was FIRST answered at game slot
`j` (`hitAt`, `Selvage/Depth.lean`, CITED — the same slot attribution
`GameSlotBound` unions over), the completed run accepts with the candidate
in `R'_{≤δ}`, and the LOG-READ increment at `i` fails its link. Bounded by
`εslot δ`, per (slot, round) pair — the `(t + k)` union then pays the
try-count, exactly as `freshBad_le`/`gameSlotBound_proved` account the
landed game.

WHY this is the genuinely-new mass and not a re-slotting: at slot `j` the
fresh answer `ρ` is drawn with `h_i` fixed (it sits inside the query) but
`h_{i+1}` NOT yet chosen — the adversary picks it later, and can realize ANY
increment `w` via `h_{i+1} := h_i + ρ • w` (`logIncrement` recovers exactly
that `w`). So the per-slot event cannot be the landed fixed-pair
`accSound_rbr` event (no fixed second word exists at draw time); it must
bound the adversary's CONTINUATION — that after seeing `ρ` it completes an
ACCEPTING run whose log-read increment at `i` is false. That is an
RO-programming / continuation argument over the remaining `≤ t − j` queries:
the folded claim's δ-satisfiability near an increment chosen AFTER `ρ` must
be paid by the acceptance clause at the END of the run (the recommitted full
fold is spot-checked against the aggregate), not by the draw alone — the
adaptive claim-fold-satisfiability event `[ACC-rbr-bcs-resid]`(a)(ii) named,
now carrying its game-side quantifiers explicitly. -/
def OracleLogProgram (εslot : ℝ → ℝ) : Prop :=
  ∀ (s tq : ℕ)
    (P : SrProver (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (i : Fin ch.length) (j : Fin tq), ∀ δ ∈ Set.Ioo (0 : ℝ) δs,
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F)) (fun coins =>
      hitAt P i.castSucc j coins.1 ∧
      (∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
        fiatShamir
            (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
              dom d q) s
            (fsOracle (srOut P coins.1) (srFinalChal P coins.1 coins.2))
            (srOut P coins.1) = some (x', y') ∧
        RelaxedMem
          (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom
            d q).R'
          δ (srOut P coins.1).stmt.idx x' y' (srOut P coins.1).w') ∧
      ¬ LinkAligned C (srOut P coins.1).stmt.x ch i
        (shiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q s
          (srOut P coins.1) (srTrace P coins.1) i))
    ≤ εslot δ

end ShiftedLog

/-! ## Keystones (ATLAS law 2) — the log extractor on the landed F₅ chain -/

namespace OracleLogExample

open RSExample LCExample ZkHidingExample ZkExtractionExample CommitExample
  AccRbrBcsExample AccRbrBcsShiftedExample

/-- The honest FS output on the landed shifted chain at schedule `≡ 1`:
statement = the landed genesis pair, messages = the honest fold-root
recommitments (`msgShifted`, CITED), no salts (`s = 0`, plain FS), candidate
witness = the landed increments. -/
noncomputable def outF5 : SrOutput accReductionBcsShifted_F5 0 :=
  ⟨⟨(), genesis, xWord⟩, fun c => msgShifted (fun _ => 1) (c : ℕ),
    fun _ => Fin.elim0, fun k => msEx k⟩

/-- The prover's query log: the three designated prefix queries, each
answered `1` — the run of an honest prover that queried every round prefix
(the grinding-free trace). -/
noncomputable def logF5 :
    OracleLog (SrMove accReductionBcsShifted_F5 0) (ZMod 5) :=
  [(outF5.query 0, 1), (outF5.query 1, 1), (outF5.query 2, 1)]

/-- The log answers every designated query with `1` — the three cells found
by first-match, distinctness by `SrOutput.query_injective` (CITED). -/
theorem logF5_answers (c : Fin 3) :
    OracleLog.answerOf logF5 (outF5.query c) = some 1 := by
  have hinj := SrOutput.query_injective outF5
  fin_cases c
  · exact OracleLog.answerOf_cons_self _ _ _
  · rw [show logF5 = (outF5.query 0, (1 : ZMod 5)) ::
        [(outF5.query 1, 1), (outF5.query 2, 1)] from rfl,
      OracleLog.answerOf_cons_of_ne
        (fun h => absurd (hinj h) (by decide))]
    exact OracleLog.answerOf_cons_self _ _ _
  · rw [show logF5 = (outF5.query 0, (1 : ZMod 5)) ::
        [(outF5.query 1, 1), (outF5.query 2, 1)] from rfl,
      OracleLog.answerOf_cons_of_ne
        (fun h => absurd (hinj h) (by decide)),
      OracleLog.answerOf_cons_of_ne
        (fun h => absurd (hinj h) (by decide))]
    exact OracleLog.answerOf_cons_self _ _ _

/-- **Satisfiable, fired**: the log extractor reads the landed increments
`msEx` off the concrete query log — `logIncrement_recovers` with every
hypothesis discharged by landed witnesses (`xWord_mem`, `msEx_mem`,
`qPair_inj`). The witness came from the LOG's answers and the output's
roots; no challenge vector was ever passed. -/
theorem log_recovers_F5 (i : Fin 2) :
    logIncrement (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair outF5 logF5 i = some (msEx i) :=
  logIncrement_recovers (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
    goodChain (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair le_rfl qPair_inj xWord_mem msEx_mem outF5 logF5
    (fun _ => 1) logF5_answers (fun _ => rfl) i one_ne_zero

/-- **Teeth, fired — the log is load-bearing**: on the EMPTY log (the prover
that never queried) the extractor recovers nothing. The straightline
extraction needs the query; the abstaining prover is in the fresh-coin horn
(`unqueried_chal_fresh`) instead. -/
theorem log_loadbearing_F5 (i : Fin 2) :
    logIncrement (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair outF5 [] i = none :=
  logIncrement_none_of_unqueried (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
    (by norm_num) S₅ dom₅ 2 qPair outF5 [] i
    (OracleLog.answerOf_nil _)

/-- A log whose round-0 answer DISAGREES with the schedule the messages were
built at: `2` instead of `1`. -/
noncomputable def logF5' :
    OracleLog (SrMove accReductionBcsShifted_F5 0) (ZMod 5) :=
  [(outF5.query 0, 2), (outF5.query 1, 1), (outF5.query 2, 1)]

/-- **Teeth, sharper — the ANSWER is load-bearing, not just the query's
presence**: reading the same output against a log that answers the round-0
query with `2` extracts `2⁻¹ • msEx 0` — and that is NOT the committed
increment (kernel-refuted). The extractor genuinely READS the recorded
challenge; a tampered log yields a wrong witness, which is exactly why the
honest bridge (`srFinalChal_eq_answerOf`: the verifier reads the SAME log)
is the load-bearing fact of the route. -/
theorem log_wrong_answer_F5 :
    logIncrement (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair outF5 logF5' (0 : Fin 2)
      = some ((2 : ZMod 5)⁻¹ • msEx 0) ∧
    (2 : ZMod 5)⁻¹ • msEx 0 ≠ msEx 0 := by
  constructor
  · have hans : OracleLog.answerOf logF5'
        (outF5.query (Fin.castSucc (0 : Fin 2))) = some 2 :=
      OracleLog.answerOf_cons_self _ _ _
    have h1 : bcsWord dom₅ 2 qPair (outF5.πs (Fin.succ (0 : Fin 2)))
        = xWord + msEx 0 := by
      show bcsWord dom₅ 2 qPair (msgShifted (fun _ => 1) 1) = xWord + msEx 0
      rw [shifted_h1_committed_F5]
      decide
    have h0 : bcsWord dom₅ 2 qPair (outF5.πs (Fin.castSucc (0 : Fin 2)))
        = xWord := by
      show bcsWord dom₅ 2 qPair (shiftedMsg S₅ qPair
        (padSched fun _ : Fin 2 => (1 : ZMod 5)) xWord msEx 0) = xWord
      rw [shiftedMsg_word S₅ dom₅ le_rfl qPair_inj _ xWord_mem msEx_mem 0,
        partialFold_zero]
    show (OracleLog.answerOf logF5'
        (outF5.query (Fin.castSucc (0 : Fin 2)))).map
        (fun ρ => ρ⁻¹ •
          (bcsWord dom₅ 2 qPair (outF5.πs (Fin.succ (0 : Fin 2)))
            - bcsWord dom₅ 2 qPair (outF5.πs (Fin.castSucc (0 : Fin 2)))))
      = some ((2 : ZMod 5)⁻¹ • msEx 0)
    rw [hans]
    show some ((2 : ZMod 5)⁻¹ •
        (bcsWord dom₅ 2 qPair (outF5.πs (Fin.succ (0 : Fin 2)))
          - bcsWord dom₅ 2 qPair (outF5.πs (Fin.castSucc (0 : Fin 2)))))
      = some ((2 : ZMod 5)⁻¹ • msEx 0)
    rw [h1, h0, add_sub_cancel_left]
  · decide

/-- A log differing from `logF5` ONLY at the final query's answer — the
inert last challenge of the shifted schedule, i.e. the FRESH challenge of
the round-1 shifted round event. -/
noncomputable def logF5'' :
    OracleLog (SrMove accReductionBcsShifted_F5 0) (ZMod 5) :=
  [(outF5.query 0, 1), (outF5.query 1, 1), (outF5.query 2, 4)]

/-- **The inertness, fired**: changing the log's answer at the round-2 query
— the fresh challenge of the shifted round-1 event — does not move the
extracted round-1 increment at all (`logIncrement_congr` on the landed
chain). The residual's diagnosis computes: the fresh challenge has NOTHING
to price on the extraction side; the leverage lives at the slot where `ρ_1`
was recorded, which is `[ORACLE-LOG-program]`'s home. -/
theorem log_inert_F5 :
    logIncrement (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair outF5 logF5'' (1 : Fin 2)
      = logIncrement (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
          goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
          (by norm_num) S₅ dom₅ 2 qPair outF5 logF5 (1 : Fin 2) := by
  have hinj := SrOutput.query_injective outF5
  have h2 : ∀ a : ZMod 5, OracleLog.answerOf
      [(outF5.query 0, 1), (outF5.query 1, 1), (outF5.query 2, a)]
      (outF5.query (Fin.castSucc (1 : Fin 2))) = some 1 := by
    intro a
    rw [OracleLog.answerOf_cons_of_ne
        (fun h => absurd (hinj h) (by decide))]
    exact OracleLog.answerOf_cons_self _ _ _
  exact logIncrement_congr (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
    (by norm_num) S₅ dom₅ 2 qPair outF5 (1 : Fin 2)
    ((h2 4).trans (h2 1).symm)

/-- **The statement's clause has teeth**: ANY inhabitant of
`adaptiveIncrement_sound_via_log` on the landed F₅ chain must output the
landed increments `msEx` on the built (output, log) pair — the pinning
clause plus `log_recovers_F5` leaves an inhabitant no freedom on honest
logs. The obligation cannot be met by a junk extractor. -/
theorem adaptive_pins_extractor_F5 {εlog : ℝ → ℝ}
    (h : adaptiveIncrement_sound_via_log
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair εlog) :
    ∃ olr : OracleLogReduction accReductionBcsShifted_F5 Set.univ εlog,
      ∀ i : Fin 2, olr.extractLog 0 outF5 logF5 i = msEx i := by
  obtain ⟨olr, hpin⟩ := h
  exact ⟨olr, fun i => hpin 0 outF5 logF5 i (msEx i) (log_recovers_F5 i)⟩

end OracleLogExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here.** The oracle-log vocabulary route (i) needs EXISTS, and
its ground facts are proved by citation into the landed game, not mirrored:
the SR/FS trace IS an `OracleLog` (`srTrace_answerOf` via
`srHandlerRun_lookup`), the FS challenges ARE log reads
(`srFinalChal_eq_answerOf` via `srFinalChal_eq_lookup`), and an unqueried
prefix falls back to an output-independent fresh coin
(`unqueried_chal_fresh`). The outside-`Reduction` objects are DEFINED and
non-vacuous: `StraightlineOracleExtractor` (log-only input; `toSr` embeds it
in the landed game), `OracleLogReduction` (the ROM-game soundness clause at
the `(t + k)·εlog` grinding price), with every inhabitant landing the landed
FS and SR statements (`fs_sound`/`sr_sound` via `fsStraightline_iff_sr`) and
the shape inhabited (`trivialOracleLogReduction`). The straightline
log-reads-the-witness structure is PROVED at the shifted alphabet:
`logIncrement`/`shiftedLogExtractor` recover the committed increments
exactly on honestly-committed logs (`logIncrement_recovers` via
`shifted_increment_recovered`), read the log only at the round's own
designated query (`logIncrement_congr` — the shifted round event's fresh
challenge is formally inert for the witness), and fail without the query
(`logIncrement_none_of_unqueried`). Keystones fire on the landed F₅ chain,
including the kernel-computed teeth that the log's ANSWER (not merely its
presence) is load-bearing (`log_wrong_answer_F5`) and the computed inertness
(`log_inert_F5`).

**What did NOT close, honestly.** `adaptiveIncrement_sound_via_log` is
STATED, not inhabited. The `(t + k)` accounting and the fresh horn are
engineering against landed machinery; the genuinely-open mass is the ONE
per-slot lemma, named formally:

* **[ORACLE-LOG-program]** (`OracleLogProgram`): at the game slot where the
  round-`i` prefix query is first answered, `h_i` is query-fixed but
  `h_{i+1}` is NOT — the adversary can realize ANY increment `w` afterwards
  via `h_{i+1} := h_i + ρ • w`, so the per-slot event cannot be the landed
  fixed-pair `accSound_rbr` event (no fixed second word exists at draw
  time). The lemma must bound the adversary's CONTINUATION: after seeing the
  fresh `ρ`, over its remaining `≤ t − j` queries, the probability of
  completing an ACCEPTING run whose log-read increment at `i` fails its
  link. The acceptance clause (the recommitted full fold spot-checked
  against the aggregate) is what must pay for the post-`ρ` increment choice
  — the adaptive claim-fold-satisfiability event `[ACC-rbr-bcs-resid]`(a)(ii)
  named, now with its game-side quantifiers explicit. This is
  RO-programming / continuation territory; nothing landed prices it yet.
* **Composition engineering** (real work, but shaped by landed proofs): the
  cover of the `sound_log` event by fresh/hit horns at the shifted alphabet
  (the `cover` pattern, `Selvage/Depth.lean`), the fresh-horn bound — where
  `unqueried_chal_fresh` reattaches a genuine fixed-pair event, since BOTH
  roots are output-fixed when the challenge is fresh, plausibly priced by
  the `accSound_rbr` family at a zero-increment specialization — and the
  `(t + k)` union (`freshBad_le`/`gameSlotBound_proved`'s choreography rerun
  with the log extractor in the extractor slot). None re-derives
  probability facts; all reuse the `uniformProb` toolkit.
* **Inherited unchanged**: the shifted state design
  (`[ACC-rbr-bcs-shifted-resid]`(b) — zero-challenge wrinkle, boundary
  rounds), `[ZK-RBR-extract]` open lemma A, and the floor
  `[FS-ROM]`/`[COMMIT-CR]`/`hPG` — consumed, never claimed.

**Honest assessment.** The deployed-ZK adaptive bound is now REDUCED to
`[ORACLE-LOG-program]`: the log vocabulary, the witness-from-log structure,
the inertness formalization, and the `(t + k)` landing surface are all real
and proved, and they convert the shifted-schedule attribution problem into a
single per-slot continuation bound. That bound is the genuinely-open
remaining mass — it is where the RO-programming argument (or the route-(ii)
adaptive fold-satisfiability bound, which is its draw-time core) must be
proved. Within reach means: one hard lemma plus Depth-scale bookkeeping, not
a missing theory.

## Ledger

* `OracleLog` / `answerOf` (+ `_nil`, `_cons_self`, `_cons_of_ne`,
  `_eq_none`) — DEFINED/PROVED: the query log and its partial-map reading.
* `srTrace_answerOf` / `srFinalChal_eq_answerOf` / `unqueried_chal_fresh` —
  PROVED (citations into `Selvage/FiatShamir.lean`): the landed game IS a log;
  FS challenges are log reads; unqueried prefixes are fresh coins.
* `StraightlineOracleExtractor` (+ `toSr`) / `OracleLogReduction`
  (+ `fs_sound`, `sr_sound`) / `trivialOracleLogReduction` —
  DEFINED/PROVED: the outside-`Reduction` shape, embedded in the landed FS
  and SR statements at `(t + k)·εlog`, and inhabited.
* `logIncrement` / `shiftedLogExtractor` — DEFINED: the log-read increment
  at the shifted BCS alphabet; log-only input.
* `logIncrement_congr` / `logIncrement_recovers` /
  `logIncrement_none_of_unqueried` — PROVED: inertness of the fresh
  challenge for the extracted witness; exact recovery on honest logs
  (`shifted_increment_recovered` CITED); the query is load-bearing.
* `adaptiveIncrement_sound_via_log` — STATED (statement-first Prop with
  ATLAS fields): NOT inhabited; the route's target.
* `OracleLogProgram` — STATED: `[ORACLE-LOG-program]`, the per-slot hit-horn
  continuation bound, the sharpened residual.
* Keystones — `outF5`/`logF5` (+ `'`, `''`), `logF5_answers`,
  `log_recovers_F5` (satisfiable), `log_loadbearing_F5` +
  `log_wrong_answer_F5` (teeth: query AND answer load-bearing, kernel-
  computed), `log_inert_F5` (inertness computed),
  `adaptive_pins_extractor_F5` (the statement bites).

`#print axioms` on `srFinalChal_eq_answerOf`, `unqueried_chal_fresh`,
`OracleLogReduction.fs_sound`, `logIncrement_recovers`,
`OracleLogExample.log_recovers_F5`, `OracleLogExample.log_wrong_answer_F5`,
`OracleLogExample.log_inert_F5`,
`OracleLogExample.adaptive_pins_extractor_F5`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
