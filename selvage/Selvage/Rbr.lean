/-
# Selvage.Rbr — round-by-round knowledge soundness: the vocabulary Selvage's extraction rides.

Statement-first transcription of WARP (ePrint 2025/753) §4 and Appendix B — the
extraction skeleton LOOM-RECOMPOSITION §2 commits to: every component enters the
stack with an RBR knowledge-soundness proof, and depth composition to
state-restoration (hence, after BCS/FS, straightline extraction from a single
transcript) is the loss-free union-bound theorem stated here as **[OB-2]**.

What lands here:
* `KStateFn` — WARP Def 4.1, the knowledge state function (three clauses:
  empty transcript, prover-move monotonicity, full transcript).
* `RbrKnowledgeSoundness` — WARP Def 4.2, *relaxed* RBR knowledge soundness:
  per-round errors `ε_i`, extraction times carried as data, and the BACKWARDS
  round extractor — it consumes a knowledge-state witness for the transcript
  *extended by the fresh challenge* and must produce one for the shorter
  transcript; extraction runs from the last round to the first.
* `SrMove`/`SrOutput`/`SrProver`/`srTrace`/`srFinalChal` — WARP Def B.1, the
  state-restoration game with salts.
* `StraightlineSrKnowledgeSoundness` — WARP Def B.2.
* `OB2_depth_composition` — WARP Thm B.4 as a `Prop`-valued obligation
  (`ε_sr(s,t,δ) ≤ (t+k)·ε_rbr(δ)`, salt-size-free). STATED, NOT PROVEN — this
  tree is no-`sorry`, so the obligation is a definition to be inhabited later.

Everything in this file is *statement*; nothing is proven beyond elaboration.

## Deliberate specializations (each one a conscious deviation from the paper)
1. **No general IOR framework.** `Reduction` is the minimal shape sufficient to
   state Defs 4.1/4.2/B.1/B.2: one index type shared by source and target
   relation (the paper's own specialization `𝕚' = 𝕚`, §3.2), the indexer folded
   into `verify`, and a deterministic verifier (WLOG per §3.2).
2. **One challenge alphabet for all rounds.** The paper samples `ρ_i ← {0,1}^{r_i}`
   per round; we fix a single finite nonempty `Chal`. WLOG by padding every
   round to `r := max_i r_i` bits — a uniform sample of the padded round has the
   uniform marginal on its real prefix, and verifier/`KState` ignore the pad.
3. **One prover-message type** `PMsg` for all rounds (messages are never
   sampled; a disjoint union loses nothing).
4. **One witness type `W`** shared by the source relation, the target relation,
   and knowledge-state witnesses. The paper types all witnesses as strings and
   silently uses a knowledge-state witness as an `R`-witness at the empty
   transcript, an `R'`-witness at the full transcript, and seeds the backwards
   extraction with the prover's `R'`-candidate (`w_k := w'`, Construction B.5) —
   so the three types must coincide; we make that explicit.
5. **Elementary finite probability.** `Pr` is counting over a finite coin space
   (`uniformProb`), not a measure. The SR game's uniformly random oracles
   `rnd = (rnd_i)` live on an infinite domain, so we render the game by *lazy
   sampling*: one fresh coin per move, reused via a query log; the `k` final
   prefix evaluations get their own coins (they are pairwise distinct — their
   prefix lengths differ). Equivalence with the uniform-function formulation is
   the standard random-oracle argument and is NOT formalized here.
6. **Extraction times are data, not semantics.** No cost model in this tree:
   `extractTime` fields carry the paper's `et_i` and Thm B.4's `et ≤ Σ et_i`
   clause is bookkeeping outside the Prop (see `OB2_depth_composition` docs).
7. **`ε_rbr` as an arbitrary uniform bound**, not `max` over the statement set
   `Z` (which need not exist for real-valued errors over infinite `Z`); the
   paper's statement is the instantiation at the max when it exists.

## Non-vacuity (house law: no trivially-inhabitable formulations)
`Reduction` carries the side conditions the paper has implicitly: `0 < k` (a
0-round protocol makes the empty transcript full and Def 4.1's first and third
clauses collide), `Nonempty Chal` (an empty challenge space makes every
`uniformProb` degenerate-zero and RBR trivially "sound" with error 0),
`Nonempty PMsg` (else no full transcripts and no SR provers exist and both
sides of B.4 hold vacuously), `0 < δstar ≤ 1` (paper: `δ* ∈ [0,1]`; `δ* ≤ 0`
empties every `δ ∈ (0,δ*)` quantifier), `0 < n`, `0 < n'` (paper: `n ∈ 2^ℕ`;
length-0 words make fractional Hamming distance degenerate). Emptiness of
`Idx`/`X`/`A`/`W` is benign for these statements (it can only make the
obligation's hypothesis and conclusion trivially true together) and is not
guarded.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Set.Defs

namespace Minidregg.Selvage

/-! ## Distance and probability vocabulary -/

/-- Fractional Hamming distance `Δ(u, v)` between two length-`n` words (WARP §3,
notation): the fraction of coordinates where they disagree. `Nat.card` of the
disagreement set, over `n`; for `n = 0` this is the junk value `0` — `Reduction`
guards `0 < n` so the degenerate case is never load-bearing. -/
noncomputable def fracHamming {A : Type} {n : ℕ} (u v : Fin n → A) : ℝ :=
  (Nat.card {i : Fin n // u i ≠ v i} : ℝ) / (n : ℝ)

/-- `R_{≤δ}` — δ-relaxed membership in an indexed relation (WARP App. B, opening
display; exactly the clause bodies of Def 4.1): the implicit instance `y` is
within fractional Hamming distance `δ` of some `y⋆` that puts `(𝕚, 𝕩, y⋆, 𝕨)`
in the relation. The strict relation is the `δ`-free fibre; the slack lives
ONLY here, on the extraction side (LOOM-RECOMPOSITION §1, promise-relation
interface). -/
def RelaxedMem {Idx X A W : Type} {n : ℕ}
    (R : Idx → X → (Fin n → A) → W → Prop) (δ : ℝ)
    (idx : Idx) (x : X) (y : Fin n → A) (w : W) : Prop :=
  ∃ ystar : Fin n → A, R idx x ystar w ∧ fracHamming y ystar ≤ δ

/-- `Pr_{c ← C}[p c]` under the uniform distribution on a finite type, as
elementary counting: `|{c // p c}| / |C|`. The stand-in for every `Pr` in WARP
Defs 4.2 and B.2 — no measure theory in the statement layer. Degenerate-zero
when `C` is empty; every use site draws `C` from a `Reduction`, whose
`chalNonempty` guard closes that vacuity channel. -/
noncomputable def uniformProb (C : Type) [Fintype C] (p : C → Prop) : ℝ :=
  (Nat.card {c : C // p c} : ℝ) / (Fintype.card C : ℝ)

/-! ## Transcripts -/

/-- A prefix of a `k`-round alternating interaction (WARP §3.2): the prover
moves first in each round, so a prefix is a list of completed
(prover message, challenge) rounds plus, possibly, one dangling prover message.
* `pending = none`, `rounds.length < k` — the prover is about to move;
* `pending = some π`, `rounds.length < k` — the verifier is about to move;
* `pending = none`, `rounds.length = k` — the transcript is full.
Shapes outside these (length > `k`, or dangling on a full transcript) are junk
and deliberately unconstrained by `KStateFn`. -/
structure Transcript (P C : Type) where
  /-- Completed rounds `(π₁, ρ₁), …, (π_i, ρ_i)`, in order. -/
  rounds : List (P × C)
  /-- The dangling prover message, when the verifier is about to move. -/
  pending : Option P

/-- The empty transcript `tr = ∅` (Def 4.1, first clause). -/
def Transcript.empty {P C : Type} : Transcript P C := ⟨[], none⟩

/-- The full transcript `(π₁, ρ₁, …, π_k, ρ_k)` (Def 4.1, third clause). -/
def Transcript.ofFull {P C : Type} {k : ℕ} (πs : Fin k → P) (ρs : Fin k → C) :
    Transcript P C :=
  ⟨List.ofFn fun i => (πs i, ρs i), none⟩

/-! ## The reduction shape -/

/-- The minimal interactive-oracle-reduction shape sufficient to state WARP
Defs 4.1/4.2/B.1/B.2 (deliberately NOT a general IOR framework — see the module
header for the seven specializations). A `k`-round public-coin reduction from an
indexed relation `R` (implicit instances: length-`n` words over `A`) to an
indexed relation `R'` (length-`n'` words over `A'`), same index type on both
sides (`𝕚' = 𝕚`, WARP §3.2), one witness type `W` throughout, deterministic
verifier `verify` that either rejects (`none`) or outputs the new explicit and
implicit instance. All alphabet/witness types live in `Type 0`: the intended
instantiations are field elements and vectors; keeping the shape monomorphic
keeps `OB2_depth_composition` universe-free. -/
structure Reduction : Type 1 where
  /-- Index type, shared by source and target relation (WARP: `𝕚' = 𝕚`). -/
  Idx : Type
  /-- Source explicit-instance type. -/
  X : Type
  /-- Source implicit-instance alphabet. -/
  A : Type
  /-- Target explicit-instance type. -/
  X' : Type
  /-- Target implicit-instance alphabet. -/
  A' : Type
  /-- The one witness type (specialization 4 in the module header). -/
  W : Type
  /-- Source implicit-instance length. -/
  n : ℕ
  /-- Target implicit-instance length. -/
  n' : ℕ
  /-- Paper: `n ∈ 2^ℕ`, in particular positive; kills the `fracHamming` `0/0`. -/
  n_pos : 0 < n
  /-- As `n_pos`, for the target side. -/
  n'_pos : 0 < n'
  /-- The source indexed relation (WARP §3.1 quadruples `(𝕚, 𝕩, 𝕪, 𝕨)`). -/
  R : Idx → X → (Fin n → A) → W → Prop
  /-- The target indexed relation. -/
  R' : Idx → X' → (Fin n' → A') → W → Prop
  /-- Number of rounds. -/
  k : ℕ
  /-- Non-vacuity: with `k = 0` the empty transcript is full and Def 4.1's
  first and third clauses collide. -/
  k_pos : 0 < k
  /-- Prover-message alphabet, one type for all rounds (specialization 3). -/
  PMsg : Type
  /-- Challenge alphabet, one finite type for all rounds — the paper's
  `{0,1}^{r_i}` padded to the max (specialization 2). -/
  Chal : Type
  /-- Non-vacuity: with `PMsg` empty (and `k > 0`) no SR prover exists and
  B.4 both sides trivialize. -/
  pmsgNonempty : Nonempty PMsg
  /-- Challenges are sampled: finiteness is what `uniformProb` counts over. -/
  chalFintype : Fintype Chal
  /-- Non-vacuity: an empty challenge space makes every `uniformProb` the junk
  value `0` and RBR "holds" with error 0. -/
  chalNonempty : Nonempty Chal
  /-- Proximity radius `δ*` (WARP §3.2). -/
  δstar : ℝ
  /-- Non-vacuity: `δ* ≤ 0` empties every `δ ∈ (0, δ*)` quantifier and every
  definition below becomes trivially satisfiable. -/
  δstar_pos : 0 < δstar
  /-- Paper: `δ* ∈ [0,1]`. -/
  δstar_le_one : δstar ≤ 1
  /-- The verifier's decision function on a full interaction: reject (`none`)
  or output the new statement. Deterministic WLOG (WARP §3.2); indexer folded
  in; queries not counted (query complexity is an efficiency measure, not part
  of Defs 4.1/4.2). -/
  verify : Idx → X → (Fin n → A) → (Fin k → PMsg) → (Fin k → Chal) →
    Option (X' × (Fin n' → A'))

instance (r : Reduction) : Fintype r.Chal := r.chalFintype
instance (r : Reduction) : Nonempty r.Chal := r.chalNonempty
instance (r : Reduction) : Nonempty r.PMsg := r.pmsgNonempty

/-- A statement `(𝕚, 𝕩, 𝕪)` of the source relation (WARP §3.1: index, explicit
instance, implicit instance; the implicit instance is the oracle
`π_R(𝕚, 𝕩, 𝕪) = 𝕪`, the paper's default). -/
structure Stmt (r : Reduction) where
  /-- The index `𝕚`. -/
  idx : r.Idx
  /-- The explicit instance `𝕩`. -/
  x : r.X
  /-- The implicit instance `𝕪` — the oracle word. -/
  y : Fin r.n → r.A

/-! ## Def 4.1 — the knowledge state function -/

/-- **Knowledge state function** (WARP 2025/753, Def 4.1). A (possibly
inefficient) bit-valued function of a proximity bound `δ ∈ (0, δ*)`, a
statement, a transcript prefix, and a *knowledge-state witness* `w : W`,
constrained by exactly three clauses:

* `empty_iff` — on the empty transcript, the bit is 1 iff `(𝕚, 𝕩, 𝕪, w)` is in
  the δ-relaxation `R_{≤δ}` of the source relation;
* `prover_monotone` — a prover move never turns the bit from 0 to 1 (doom is
  monotone under prover moves; only fresh verifier randomness can rescue — the
  clause the SR union bound leans on, Claim B.6);
* `full_iff` — on a full transcript, the bit is 1 iff the verifier accepts with
  some output `(𝕩', 𝕪')` and `(𝕚, 𝕩', 𝕪', w)` is in `R'_{≤δ}`.

Partial transcripts other than these are unconstrained (the paper constrains
them only through `prover_monotone` chains), as are junk `δ` outside `(0, δ*)`
and junk transcript shapes (see `Transcript`). The state takes plain `δ : ℝ`;
the clauses bind only in the paper's range. -/
structure KStateFn (r : Reduction) where
  /-- `KState_δ(𝕚, 𝕩, 𝕪, tr, w)`, the bit. -/
  state : ℝ → Stmt r → Transcript r.PMsg r.Chal → r.W → Bool
  /-- Def 4.1, empty-transcript clause: `KState_δ(∅, w) = 1` iff
  `(𝕚, 𝕩, 𝕪, w) ∈ R_{≤δ}`. -/
  empty_iff : ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ (st : Stmt r) (w : r.W),
    state δ st Transcript.empty w = true ↔ RelaxedMem r.R δ st.idx st.x st.y w
  /-- Def 4.1, prover-move clause: if the prover is about to move
  (`pending = none`, not full) and the state is 0, it stays 0 for EVERY
  prover message. -/
  prover_monotone : ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ (st : Stmt r)
    (rs : List (r.PMsg × r.Chal)) (w : r.W), rs.length < r.k →
    state δ st ⟨rs, none⟩ w = false →
    ∀ π : r.PMsg, state δ st ⟨rs, some π⟩ w = false
  /-- Def 4.1, full-transcript clause: on `(π₁, ρ₁, …, π_k, ρ_k)` the state is 1
  iff the verifier outputs some `(𝕩', 𝕪')` with `(𝕚, 𝕩', 𝕪', w) ∈ R'_{≤δ}`
  (rejection forces 0). -/
  full_iff : ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ (st : Stmt r)
    (πs : Fin r.k → r.PMsg) (ρs : Fin r.k → r.Chal) (w : r.W),
    state δ st (Transcript.ofFull πs ρs) w = true ↔
      ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
        r.verify st.idx st.x st.y πs ρs = some (x', y') ∧
        RelaxedMem r.R' δ st.idx x' y' w

/-! ## Def 4.2 — relaxed round-by-round knowledge soundness -/

/-- **Relaxed round-by-round knowledge soundness** (WARP 2025/753, Def 4.2).
The data: a knowledge state function, a deterministic round extractor
`extract`, per-round errors `err i st δ` (the paper's `ε_i(𝕚, 𝕩, 𝕪, δ)`), and
per-round extraction times as carried data.

**The extractor runs BACKWARDS.** At a transcript `tr` ending in the round-`i`
prover message (the verifier about to move), `extract` receives the transcript
*extended by the fresh challenge* `tr‖ρ` together with a knowledge-state
witness `w` for the LONGER transcript, and must produce a knowledge-state
witness for the SHORTER `tr`. `extract_sound` bounds, over uniform `ρ`, the
probability that ANY `w` wins the round against the extractor: some `w` is
valid at `tr‖ρ` while `extract`'s output is invalid at `tr`. Composing from the
full transcript back to the empty one turns a target-relation witness into a
source-relation witness — Construction B.5, seeded with the prover's own
candidate `w_k := w'`.

Note the extractor is δ-oblivious (Def 4.2 gives it no `δ` input) while the
error may depend on `δ`; the same `KStateFn`/`extract` pair must work for every
`δ ∈ (0, δ*)`. `extractTime` is data with no cost semantics in this tree
(specialization 6). -/
structure RbrKnowledgeSoundness (r : Reduction) where
  /-- The knowledge state function (Def 4.1) this soundness is measured
  against. -/
  kstate : KStateFn r
  /-- The round extractor `E_rbr(𝕚, 𝕩, 𝕪, tr‖ρ_i, w)` — deterministic,
  δ-oblivious, consumes the NEXT (extended) transcript's knowledge-state
  witness, produces the previous one's. -/
  extract : Stmt r → Transcript r.PMsg r.Chal → r.W → r.W
  /-- Per-round knowledge errors `ε_i(𝕚, 𝕩, 𝕪, δ)`. -/
  err : Fin r.k → Stmt r → ℝ → ℝ
  /-- Per-round extraction times `et_i` — carried data, no cost model; the
  paper's total extraction time is `∑ i, extractTime i` (Def 4.2, last line). -/
  extractTime : Fin r.k → ℕ
  /-- Def 4.2, the round bound: for every `δ ∈ (0, δ*)`, statement, round
  `i` (`rs` lists the `i` completed earlier rounds — the paper's 1-indexed
  round `i+1`), and pending prover message `π`,
  `Pr_ρ[∃ w, KState_δ(tr, E_rbr(tr‖ρ, w)) = 0 ∧ KState_δ(tr‖ρ, w) = 1] ≤ ε_i`. -/
  extract_sound : ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ (st : Stmt r) (i : Fin r.k)
    (rs : List (r.PMsg × r.Chal)), rs.length = (i : ℕ) → ∀ π : r.PMsg,
    uniformProb r.Chal (fun ρ => ∃ w : r.W,
        kstate.state δ st ⟨rs, some π⟩ (extract st ⟨rs ++ [(π, ρ)], none⟩ w)
          = false ∧
        kstate.state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true)
      ≤ err i st δ

/-! ## Def B.1 — the state-restoration game

Rendered by lazy sampling (specialization 5): the game's random oracles
`rnd = (rnd_i)_{i ∈ [k]}` are never materialized; instead each of the `t` moves
carries a fresh coin, used only if the move is new (repeated moves are answered
from the log — that is exactly the consistency `rnd` provides), and the `k`
final prefix evaluations carry their own coins (pairwise distinct queries:
their prefix lengths differ). The round index of the paper's `rnd_i` family is
recovered from the prefix length, so one query type suffices. -/

/-- Salt strings `σ ∈ {0,1}^s` (WARP Def B.1). -/
abbrev Salt (s : ℕ) : Type := Fin s → Bool

/-- A state-restoration move (Def B.1, step 1a): a statement together with a
salted prover-message prefix `((π₁, σ₁), …, (π_i, σ_i))` — the argument of
`rnd_i` for `i` = the prefix length. Prefix lengths outside `[1, k]` are junk
queries the adversary may waste budget on; step 3 never evaluates them. -/
structure SrMove (r : Reduction) (s : ℕ) where
  /-- The statement `(𝕚, 𝕩, 𝕪)` named in the move. -/
  stmt : Stmt r
  /-- The salted prefix `((π₁, σ₁), …, (π_i, σ_i))`. -/
  pfx : List (r.PMsg × Salt s)

/-- The adversary's final output (Def B.1, step 2): a statement, prover
messages and salts for all `k` rounds, and a candidate target-relation
witness `w'`. -/
structure SrOutput (r : Reduction) (s : ℕ) where
  /-- The output statement `(𝕚, 𝕩, 𝕪)` — the one Def B.2's event tests
  against `Z` and `R_{≤δ}`. -/
  stmt : Stmt r
  /-- Prover messages `π₁, …, π_k`. -/
  πs : Fin r.k → r.PMsg
  /-- Salts `σ₁, …, σ_k`. -/
  σs : Fin r.k → Salt s
  /-- The candidate witness `w'` for the target relation. -/
  w' : r.W

/-- A deterministic state-restoration prover as a strategy (Def B.1/B.2): its
`j`-th move is a function of the `j-1` responses received so far, and its final
output a function of all responses. A "`t`-move" prover is this strategy run
for exactly `t` moves by `srTrace` — the budget lives in the game, not the
type. -/
structure SrProver (r : Reduction) (s : ℕ) where
  /-- The next move, given the responses so far. -/
  move : List r.Chal → SrMove r s
  /-- The final output, given all responses. -/
  out : List r.Chal → SrOutput r s

/-- The round-`i` prefix query determined by a final output (Def B.1, step 3):
`(𝕚, 𝕩, 𝕪, (π₁, …, π_{i+1}), (σ₁, …, σ_{i+1}))` for 0-indexed `i`. Its prefix
length is `i + 1`, so the `k` final queries are pairwise distinct. -/
def SrOutput.query {r : Reduction} {s : ℕ} (o : SrOutput r s) (i : Fin r.k) :
    SrMove r s :=
  ⟨o.stmt, ((List.finRange r.k).take ((i : ℕ) + 1)).map fun j => (o.πs j, o.σs j)⟩

section StateRestorationGame

open Classical

/-- The lazily-sampled trace of `SRGame(s, rnd, P̃_sr)` (Def B.1, step 1) run
for `t` moves on coins `c`: the `j`-th move is answered from the log if it was
made before (the consistency the oracle `rnd` provides), else with the fresh
coin `c j`. Returns the paper's `tr_sr`, the move/response list in order.
Noncomputable: query equality is decided classically. -/
noncomputable def srTrace {r : Reduction} {s t : ℕ} (P : SrProver r s)
    (c : Fin t → r.Chal) : List (SrMove r s × r.Chal) :=
  (List.finRange t).foldl (fun log j =>
    let q := P.move (log.map Prod.snd)
    let ρ := match log.find? (fun e => decide (e.1 = q)) with
      | some e => e.2
      | none => c j
    log ++ [(q, ρ)]) ([] : List (SrMove r s × r.Chal))

/-- The final challenges `ρ_i := rnd_i(𝕚, 𝕩, 𝕪, (π₁…π_i), (σ₁…σ_i))` (Def B.1,
step 3), lazily sampled: answered from the game trace if the prefix was queried
during the game, else with the fresh coin `d i` (sound because the `k` final
queries are pairwise distinct — see `SrOutput.query`). -/
noncomputable def srFinalChal {r : Reduction} {s t : ℕ} (P : SrProver r s)
    (c : Fin t → r.Chal) (d : Fin r.k → r.Chal) (i : Fin r.k) : r.Chal :=
  let log := srTrace P c
  let q := (P.out (log.map Prod.snd)).query i
  match log.find? (fun e => decide (e.1 = q)) with
  | some e => e.2
  | none => d i

end StateRestorationGame

/-! ## Def B.2 — straightline state-restoration knowledge soundness -/

/-- The straightline state-restoration extractor's shape (Def B.2): it consumes
the adversary's output, the final challenges, and the game trace `tr_sr` — one
transcript, no rewinding — and produces a source-relation witness. (It does not
need `𝕩'`, `𝕪'`: they are determined by its other inputs.) -/
abbrev SrExtractor (r : Reduction) (s : ℕ) : Type :=
  SrOutput r s → (Fin r.k → r.Chal) → List (SrMove r s × r.Chal) → r.W

/-- **Straightline state-restoration knowledge soundness** (WARP 2025/753,
Def B.2) for a statement set `Z` with error `εsr s t δ`: ONE deterministic
extractor (polymorphic in the salt size) such that for every salt size `s`,
move budget `t`, proximity bound `δ ∈ (0, δ*)`, and deterministic `t`-move
state-restoration prover, the probability (over the game's lazily-sampled
coins) that
* the output statement lands in `Z`, and
* the extracted witness FAILS `R_{≤δ}` on the output statement, and
* the verifier accepts the output with the prover's candidate `w'` in `R'_{≤δ}`
is at most `εsr s t δ`.

The paper's "runs in time at most `et`" clause is not modeled (no cost
semantics; specialization 6). -/
def StraightlineSrKnowledgeSoundness (r : Reduction) (Z : Set (Stmt r))
    (εsr : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ E : (s : ℕ) → SrExtractor r s,
    ∀ (s t : ℕ), ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ P : SrProver r s,
      uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) (fun coins =>
        let log := srTrace P coins.1
        let o := P.out (log.map Prod.snd)
        let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
        o.stmt ∈ Z ∧
        ¬ RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y (E s o ρs log) ∧
        ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
          r.verify o.stmt.idx o.stmt.x o.stmt.y o.πs ρs = some (x', y') ∧
          RelaxedMem r.R' δ o.stmt.idx x' y' o.w')
        ≤ εsr s t δ

/-! ## [OB-2] — Thm B.4, depth composition, stated as the obligation -/

/-- **[OB-2] Loss-free depth composition** (WARP 2025/753, Thm B.4): relaxed
round-by-round knowledge soundness implies straightline state-restoration
knowledge soundness with error `ε_sr(s, t, δ) ≤ (t + k) · ε_rbr(δ)` — linear in
the move budget, salt-size-free, proved in the paper by a union bound over the
at most `t + k` unique moves of the full trace (game moves plus the `k` output
prefixes), with the backwards extractor of Construction B.5
(`w_k := w'`; `w_{i-1} := E_rbr(tr_i, w_i)`; output `w_0`).

Stated with `εrbr` an arbitrary uniform bound on the per-round errors over `Z`
(specialization 7; the paper's `ε_rbr(δ) := max_{i, (𝕚,𝕩,𝕪) ∈ Z} ε_i(𝕚,𝕩,𝕪,δ)`
is the instantiation at the max when it exists). Thm B.4's extraction-time
clause `et ≤ ∑ i, et_i` is data-level bookkeeping (`RbrKnowledgeSoundness.extractTime`),
not part of this Prop — no cost model in this tree.

ATLAS keystone fields (obligation, statement-first):
* satisfiable: TODO realizer — Construction B.5 + the Claim B.6 induction and
  the union bound over the `t + k` unique moves, redone against the
  lazy-sampling rendering of the game.
* teeth: TODO hostile instance — a reduction + adversary family showing the
  bound is not slack junk: e.g. drop `prover_monotone` from `KStateFn` (or the
  log-consistency from `srTrace`) and exhibit an SR prover beating
  `(t + k) · ε_rbr`.
* premise-inhabitation: TODO — exhibit a concrete `Reduction` with a
  `RbrKnowledgeSoundness` instance (WARP Thm 5.8's one-round IOR at toy
  parameters is the intended witness). -/
def OB2_depth_composition : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    (εrbr : ℝ → ℝ),
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) →
    StraightlineSrKnowledgeSoundness r Z
      (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ)

#check OB2_depth_composition

end Minidregg.Selvage
