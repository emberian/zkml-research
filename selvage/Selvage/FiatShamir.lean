/-
# Selvage.FiatShamir — the transcript layer: the ROM as an inhabited handler, and
# Fiat–Shamir of a round-by-round-sound reduction.

LOOM-RECOMPOSITION §2 commits the transcript layer to ONE BCS/FS compilation of
the whole protocol with round-by-round soundness as the invariant: where RBR
holds, Fiat–Shamir in the ROM yields STRAIGHTLINE extraction from a single
transcript — no rewinding, no R–T tree (the CY24/BMNW25 route; what WARP and
holography accumulation both use). This file lands that layer's vocabulary on
top of Selvage/Rbr.lean and Selvage/Depth.lean, statement-first, with built
witnesses.

What lands here:
* `Oracle` — the random oracle as a LAZY-SAMPLING HANDLER: a finite partial
  response map (the log of past queries and their sampled responses), extended
  on demand by `respond`, with the handler laws PROVED (`respond_hit`,
  `respond_fresh_*`, `lookup_respond_self`, `respond_consistent`). It is
  INHABITED (`Oracle.empty`, an `Inhabited` instance) — a concrete handler
  exists as an object of the theory, NOT an `axiom`. Coins come from OUTSIDE
  the handler (the game's coin space): the handler never conjures randomness,
  it only records and replays it — that is the honest-floor rendering of
  "uniformly random function" without an infinite object.
* `srHandlerRun` + the correspondence theorems — the landed SR game of
  Selvage/Rbr.lean (`srTrace`, specialization 5's lazy sampling) IS a run of this
  handler: `srHandlerRun_snd` (same responses), `srHandlerRun_lookup` (same
  partial map), `srFinalChal_eq_lookup` (the game's final challenges are
  handler lookups with the fresh coin as fallback). So the handler is not a
  decorative side structure: the load-bearing game is machine-checked to BE it.
* `fiatShamir` — the FS transform of a public-coin `Reduction`: the
  non-interactive verifier derives challenge `ρ_i := O(𝕚,𝕩,𝕪,(π₁…π_i),(σ₁…σ_i))`
  — the oracle at the transcript prefix (`SrOutput.query`, salts included:
  the BCS salt channel; `s = 0` is plain FS) — and runs the base verifier on
  the derived transcript. Well-definedness is proved: the verdict reads the
  oracle ONLY at the `k` designated prefixes (`fiatShamir_congr`), which are
  pairwise distinct (`SrOutput.query_injective`).
* `FsStraightlineKnowledgeSoundness` — Def B.2's game with the FS verifier in
  the acceptance clause: one deterministic extractor consuming the single
  transcript (output, derived challenges, query log — STRAIGHTLINE), bounding
  the probability that a `t`-query ROM adversary lands in `Z`, the FS verifier
  accepts with the candidate witness in `R'_{≤δ}`, and extraction fails
  `R_{≤δ}`.
* `fsStraightline_iff_sr` — **the BCS bridge, PROVED**: the FS game in the
  lazily-sampled ROM is EXACTLY the state-restoration game of Def B.2. An FS
  adversary's oracle queries are salted transcript prefixes — i.e. SR moves —
  so the two games have the same adversaries, the same coins, and (after
  `fiatShamir_fsOracle`) the same events.
* `FsOfRbrSound` + `FsOfRbrKeystone` — the keystone: FS of a relaxed-RBR
  reduction preserves knowledge soundness in the ROM, straightline, with the
  loss-free error `(t + k) · ε_rbr(δ)`. ATLAS fields are REAL structure
  fields: `oracle_inhabited` (satisfiable — the handler exists, proved
  unconditionally), `teeth` (a BUILT proof string the FS verifier REJECTS
  under one oracle and accepts under another, so the verdict is the oracle's
  doing — `chalReduction`/`chalOutput`), `premise` (a base RBR reduction
  exists — Depth's `trivialReduction`/`trivialRbr`), `sound` (the statement).
  `fsOfRbrSound_iff_depth` proves the statement EQUIVALENT to the repaired
  depth obligation [OB-2′], so `fsKeystone_of_gameSlotBound` assembles the
  whole keystone from [OB-2a] (`GameSlotBound`, Selvage/Depth.lean) — nothing
  new is assumed here. [OB-2a] is now DISCHARGED upstream
  (`gameSlotBound_proved`), so the keystone holds unconditionally:
  `fsKeystone_proved`.

## Residual ledger (honest, named — no `sorry`, no `True` stubs)
* **[OB-2a] inherited — now CLOSED upstream**: `FsOfRbrSound` is proved ⇔
  [OB-2′] (`fsOfRbrSound_iff_depth`), [OB-2′] is proved from `GameSlotBound`
  (Selvage/Depth.lean, `OB2_nonneg_of_gameSlotBound`), and `GameSlotBound` is
  now PROVED there (`gameSlotBound_proved`, via the general lazy-rnd
  resolver + uniformity kernel its doc comment called for). The FS layer
  adds NO new unproved mathematics: its own two reductions
  (game-equivalence, handler correspondence) are closed in this file.
* **[FS-ROM] the one named idealization**: "the deployed sponge/hash realizes
  this lazy-sampling handler" is a MODELING step outside the theory — the
  handler is the ideal object the deployed function is assumed to
  instantiate. It is deliberately NOT an axiom in this tree; it is the
  named gap between `Oracle` and a concrete sponge, priced at deployment.
* **[FS-BCS] oracle-message compilation not modeled at this layer**:
  `Reduction.verify` reads the implicit instance `𝕪` directly — the BCS
  Merkle-compilation of ORACLE messages (vector commitments, opening paths,
  their binding/extraction errors) lives in the link layer / final
  compression, not here. This file compiles the INTERACTION (public coins →
  oracle-derived challenges), which is exactly the transcript layer's job.
* **Query-type instantiation**: the ROM here is instantiated at query type
  `SrMove r s` (salted statement-prefix pairs). Domain separation from other
  oracle uses in the stack is a deployment concern under [FS-ROM].

## Non-vacuity
* `Oracle` inhabitation needs NO hypotheses (the empty handler); that it
  genuinely OPERATES is witnessed by the laws (`respond_fresh_*` really
  extends the log; `respond_consistent` really replays).
* `fiatShamir`'s teeth exhibit BOTH poles on one proof string: rejected under
  the all-`false` oracle, accepted under the all-`true` one
  (`fiatShamir_teeth`) — the challenge derivation is load-bearing, the
  verifier is not constantly-accepting or constantly-rejecting.
* The keystone's `sound` clause carries the [OB-2′] nonnegativity guard
  (`0 ≤ εrbr δ`): Depth.lean proved the unguarded form REFUTABLE
  (`OB2_depth_composition_false`), and this file does not reopen that hole.
-/
import Mathlib.Order.Interval.Set.Defs
import Selvage.Depth

namespace Minidregg.Selvage

/-! ## The ROM as an inhabited lazy-sampling handler -/

/-- The random oracle as a **lazy-sampling handler** over query type `Q` and
response type `C`: a finite log of past queries and their sampled responses —
a PARTIAL response map, extended on demand. `nodupKeys` makes it honestly a
partial function (at most one response per query). This is the ROM of the
honest-floor discipline: an INHABITED structure (`Oracle.empty` below), not an
`axiom`; the "uniformly random function" is never materialized — sampling
happens one coin at a time, and the coins come from the game's finite coin
space, outside the handler. -/
structure Oracle (Q C : Type) where
  /-- The response log: the queries answered so far, with their responses. -/
  log : List (Q × C)
  /-- At most one response per query — the log denotes a partial function. -/
  nodupKeys : (log.map Prod.fst).Nodup

namespace Oracle

variable {Q C : Type}

/-- The fresh handler: nothing sampled yet. THE inhabitation witness — the
concrete lazy-sampling handler exists with no hypotheses at all (not even
`Nonempty C`: a handler that has answered nothing needs no responses). -/
def empty : Oracle Q C := ⟨[], List.nodup_nil⟩

/-- The ROM handler is inhabited — the floor is a built object, not an axiom. -/
instance : Inhabited (Oracle Q C) := ⟨empty⟩

section Handler

open Classical

/-- Look a query up in the log: `some ρ` if answered before (first — hence,
by `nodupKeys`, only — occurrence), `none` if fresh. -/
noncomputable def lookup (O : Oracle Q C) (q : Q) : Option C :=
  (O.log.find? fun e => decide (e.1 = q)).map Prod.snd

@[simp] lemma lookup_empty (q : Q) : (empty : Oracle Q C).lookup q = none := rfl

lemma lookup_eq_none {O : Oracle Q C} {q : Q} :
    O.lookup q = none ↔ ∀ e ∈ O.log, e.1 ≠ q := by
  unfold lookup
  simp [List.find?_eq_none]

/-- **The handler step** — lazy sampling: answer `q` from the log if it was
asked before (CONSISTENCY: the recorded response replays, the coin is unused),
else with the fresh coin (SAMPLING: the coin is recorded so all later replays
agree). Returns the response and the extended handler. -/
noncomputable def respond (O : Oracle Q C) (q : Q) (coin : C) :
    C × Oracle Q C :=
  match h : O.lookup q with
  | some ρ => (ρ, O)
  | none =>
      (coin, ⟨O.log ++ [(q, coin)], by
        rw [List.map_append]
        refine O.nodupKeys.append (List.nodup_singleton _) ?_
        intro a ha hb
        rw [List.map_singleton, List.mem_singleton] at hb
        subst hb
        obtain ⟨e, he, hfst⟩ := List.mem_map.mp ha
        exact lookup_eq_none.mp h e he hfst⟩)

/-- A logged query is answered from the log, and the handler does not move. -/
lemma respond_hit {O : Oracle Q C} {q : Q} {ρ : C} (h : O.lookup q = some ρ)
    (coin : C) : O.respond q coin = (ρ, O) := by
  unfold respond
  split
  · rename_i h'
    rw [h] at h'
    exact (Option.some.inj h') ▸ rfl
  · rename_i h'
    rw [h] at h'
    exact absurd h' (Option.some_ne_none ρ)

/-- A fresh query is answered by the sampled coin. -/
lemma respond_fresh_fst {O : Oracle Q C} {q : Q} (h : O.lookup q = none)
    (coin : C) : (O.respond q coin).1 = coin := by
  unfold respond
  split
  · rename_i h'
    rw [h] at h'
    exact absurd h'.symm (Option.some_ne_none _)
  · rfl

/-- A fresh query extends the log by exactly its (query, coin) entry. -/
lemma respond_fresh_log {O : Oracle Q C} {q : Q} (h : O.lookup q = none)
    (coin : C) : (O.respond q coin).2.log = O.log ++ [(q, coin)] := by
  unfold respond
  split
  · rename_i h'
    rw [h] at h'
    exact absurd h'.symm (Option.some_ne_none _)
  · rfl

private lemma find?_singleton_of_eq (q : Q) (c : C) :
    ([(q, c)].find? fun e => decide (e.1 = q)) = some (q, c) :=
  List.find?_cons_of_pos (by simp)

private lemma find?_singleton_of_ne {q q' : Q} (h : q' ≠ q) (c : C) :
    ([(q, c)].find? fun e => decide (e.1 = q')) = none := by
  rw [List.find?_cons_of_neg (by simpa using Ne.symm h)]
  rfl

private lemma find?_of_lookup_eq_none {O : Oracle Q C} {q : Q}
    (h : O.lookup q = none) :
    (O.log.find? fun e => decide (e.1 = q)) = none :=
  Option.map_eq_none_iff.mp h

/-- After responding, the query is logged with exactly the returned
response — the handler REMEMBERS. -/
lemma lookup_respond_self (O : Oracle Q C) (q : Q) (coin : C) :
    (O.respond q coin).2.lookup q = some (O.respond q coin).1 := by
  cases h : O.lookup q with
  | some ρ => rw [respond_hit h]; exact h
  | none =>
      rw [respond_fresh_fst h]
      show ((O.respond q coin).2.log.find? _).map Prod.snd = _
      rw [respond_fresh_log h, List.find?_append, find?_of_lookup_eq_none h,
        Option.none_or, find?_singleton_of_eq]
      rfl

/-- Responding to `q` does not disturb any other query — the frame law. -/
lemma lookup_respond_ne (O : Oracle Q C) {q q' : Q} (h : q' ≠ q) (coin : C) :
    (O.respond q coin).2.lookup q' = O.lookup q' := by
  cases hq : O.lookup q with
  | some ρ => rw [respond_hit hq]
  | none =>
      show ((O.respond q coin).2.log.find? _).map Prod.snd = _
      rw [respond_fresh_log hq, List.find?_append, find?_singleton_of_ne h,
        Option.or_none]
      rfl

/-- **ROM consistency**: asking the same query twice returns the same
response, whatever coin the second ask carries — the recorded sample
replays. -/
lemma respond_consistent (O : Oracle Q C) (q : Q) (coin coin' : C) :
    ((O.respond q coin).2.respond q coin').1 = (O.respond q coin).1 := by
  rw [respond_hit (lookup_respond_self O q coin)]

end Handler

end Oracle

/-! ## The Fiat–Shamir transform of a public-coin reduction

The FS proof string for a `k`-round public-coin `Reduction` is an
`SrOutput r s` — the named statement, the `k` prover messages, the `k` salts
(the BCS salt channel; `s = 0` is plain FS), and the candidate target-relation
witness. The verifier derives each challenge by querying the oracle at the
transcript prefix through round `i` (`SrOutput.query`, Selvage/Rbr.lean — exactly
the state-restoration game's step-3 queries), then runs the base verifier on
the derived transcript. -/

/-- The **Fiat–Shamir transform**: the non-interactive verifier for reduction
`r` at salt size `s`, relative to a random-oracle function `O`. Challenges are
derived from the transcript prefixes — `ρ_i := O(𝕚,𝕩,𝕪,(π₁…π_i),(σ₁…σ_i))` —
and the base verifier decides. `O` enters as a total function: which partial
handler realizes it, and at which queries it was actually sampled, is the
GAME's business (below), not the verifier's. -/
def fiatShamir (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal)
    (o : SrOutput r s) : Option (r.X' × (Fin r.n' → r.A')) :=
  r.verify o.stmt.idx o.stmt.x o.stmt.y o.πs fun i => O (o.query i)

/-- Well-definedness, half 1: the FS verdict reads the oracle ONLY at the `k`
designated transcript prefixes. -/
lemma fiatShamir_congr {r : Reduction} {s : ℕ} {O O' : SrMove r s → r.Chal}
    (o : SrOutput r s) (h : ∀ i, O (o.query i) = O' (o.query i)) :
    fiatShamir r s O o = fiatShamir r s O' o :=
  congrArg _ (funext h)

/- (`SrOutput.query_pfx_length` — the round-`i` designated query has prefix
length `i + 1` — used to live here; it now lands upstream in Selvage/Depth.lean's
query-structure section, and the twin is deleted.) -/

/-- Well-definedness, half 2: the `k` designated queries are pairwise
distinct (their prefix lengths differ) — so ANY challenge vector is realized
by some total oracle, and `fsOracle` below is well-defined. -/
lemma SrOutput.query_injective {r : Reduction} {s : ℕ} (o : SrOutput r s) :
    Function.Injective o.query := by
  intro i j hij
  have hi := o.query_pfx_length i
  rw [hij, o.query_pfx_length j] at hi
  exact Fin.ext (by omega)

open Classical in
/-- The canonical total oracle consistent with challenge vector `ρs` on the
designated queries of `o` (arbitrary elsewhere — `r.Chal` is nonempty by the
`Reduction` guard). The bridge between the game's lazily-sampled challenges
and the total-function oracle `fiatShamir` consumes. -/
noncomputable def fsOracle {r : Reduction} {s : ℕ} (o : SrOutput r s)
    (ρs : Fin r.k → r.Chal) : SrMove r s → r.Chal :=
  fun q => if h : ∃ i : Fin r.k, o.query i = q then ρs h.choose
    else Classical.arbitrary r.Chal

lemma fsOracle_query {r : Reduction} {s : ℕ} (o : SrOutput r s)
    (ρs : Fin r.k → r.Chal) (i : Fin r.k) :
    fsOracle o ρs (o.query i) = ρs i := by
  have h : ∃ j : Fin r.k, o.query j = o.query i := ⟨i, rfl⟩
  rw [fsOracle, dif_pos h]
  exact congrArg ρs (o.query_injective h.choose_spec)

/-- The FS verdict at the canonical oracle IS the base verdict at the
challenge vector — `fiatShamir` is the interactive verifier with its coins
replaced by oracle answers, nothing more. -/
lemma fiatShamir_fsOracle {r : Reduction} {s : ℕ} (o : SrOutput r s)
    (ρs : Fin r.k → r.Chal) :
    fiatShamir r s (fsOracle o ρs) o =
      r.verify o.stmt.idx o.stmt.x o.stmt.y o.πs ρs :=
  congrArg _ (funext fun i => fsOracle_query o ρs i)

/-! ## The landed game IS a handler run

Selvage/Rbr.lean's state-restoration game lazily samples its oracle via a query
log (specialization 5). Here that rendering is machine-checked to BE a run of
the `Oracle` handler: same responses (`srHandlerRun_snd`), same partial map
(`srHandlerRun_lookup`), and the game's final challenges are handler lookups
with the fresh coin as fallback (`srFinalChal_eq_lookup`). -/

section HandlerRun

open Classical

variable {r : Reduction} {s t : ℕ}

/-- One game step against the handler: ask the strategy's next move, respond
(from the log or the step's fresh coin), record the response. -/
noncomputable def handlerStep (P : SrProver r s) (c : Fin t → r.Chal)
    (st : Oracle (SrMove r s) r.Chal × List r.Chal) (j : Fin t) :
    Oracle (SrMove r s) r.Chal × List r.Chal :=
  ((st.1.respond (P.move st.2) (c j)).2,
    st.2 ++ [(st.1.respond (P.move st.2) (c j)).1])

/-- The SR/FS game as a handler thread: final handler state and the response
list, from the empty handler on coins `c`. -/
noncomputable def srHandlerRun (P : SrProver r s) (c : Fin t → r.Chal) :
    Oracle (SrMove r s) r.Chal × List r.Chal :=
  (List.finRange t).foldl (handlerStep P c) (Oracle.empty, [])

private lemma map_or_congr {α β : Type} {f : α → β} {a b : Option α}
    (h : a.map f = b.map f) (x : Option α) :
    (a.or x).map f = (b.or x).map f := by
  cases a <;> cases b <;> simp_all

/-- One step of the correspondence: if the handler's partial map agrees with
the trace log's `find?` view, it still does after one game step, and the
recorded responses stay in lockstep with `stepFn` (Selvage/Depth.lean). -/
lemma handlerStep_agree (P : SrProver r s) (c : Fin t → r.Chal) (j : Fin t)
    (L : List (SrMove r s × r.Chal)) (O : Oracle (SrMove r s) r.Chal)
    (h : ∀ q, O.lookup q = (L.find? fun e => decide (e.1 = q)).map Prod.snd) :
    ∃ O', handlerStep P c (O, L.map Prod.snd) j =
        (O', (stepFn P c L j).map Prod.snd) ∧
      ∀ q, O'.lookup q =
        ((stepFn P c L j).find? fun e => decide (e.1 = q)).map Prod.snd := by
  set q₀ := P.move (L.map Prod.snd) with hq₀
  cases hf : L.find? fun e => decide (e.1 = q₀) with
  | some e =>
      have hstep' : stepFn P c L j = L ++ [(q₀, e.2)] := by
        rw [stepFn_eq P c L j, ← hq₀, hf]
      have hlk : O.lookup q₀ = some e.2 := by simp [h q₀, hf]
      refine ⟨O, ?_, ?_⟩
      · simp only [handlerStep, ← hq₀]
        rw [Oracle.respond_hit hlk, hstep', List.map_append]
        rfl
      · intro q
        rw [hstep', h q, List.find?_append]
        by_cases hqq : q = q₀
        · subst hqq
          rw [hf, Option.some_or]
        · cases hfq : L.find? fun e' => decide (e'.1 = q) with
          | some e' => rw [Option.some_or]
          | none => rw [Option.none_or, Oracle.find?_singleton_of_ne hqq]
  | none =>
      have hstep' : stepFn P c L j = L ++ [(q₀, c j)] := by
        rw [stepFn_eq P c L j, ← hq₀, hf]
      have hlk : O.lookup q₀ = none := by simp [h q₀, hf]
      refine ⟨(O.respond q₀ (c j)).2, ?_, ?_⟩
      · simp only [handlerStep, ← hq₀]
        rw [Oracle.respond_fresh_fst hlk, hstep', List.map_append]
        rfl
      · intro q
        show ((O.respond q₀ (c j)).2.log.find? _).map Prod.snd = _
        rw [Oracle.respond_fresh_log hlk, hstep', List.find?_append,
          List.find?_append]
        exact map_or_congr (h q) _

/-- The fold form of the correspondence, over any step list. -/
lemma foldl_handlerStep_agree (P : SrProver r s) (c : Fin t → r.Chal) :
    ∀ (js : List (Fin t)) (O : Oracle (SrMove r s) r.Chal)
      (L : List (SrMove r s × r.Chal)),
      (∀ q, O.lookup q = (L.find? fun e => decide (e.1 = q)).map Prod.snd) →
      (js.foldl (handlerStep P c) (O, L.map Prod.snd)).2 =
          (js.foldl (stepFn P c) L).map Prod.snd ∧
        ∀ q, (js.foldl (handlerStep P c) (O, L.map Prod.snd)).1.lookup q =
          ((js.foldl (stepFn P c) L).find? fun e => decide (e.1 = q)).map
            Prod.snd := by
  intro js
  induction js with
  | nil => exact fun O L h => ⟨rfl, h⟩
  | cons j js ih =>
      intro O L h
      obtain ⟨O', heq, hinv⟩ := handlerStep_agree P c j L O h
      rw [List.foldl_cons, List.foldl_cons, heq]
      exact ih O' (stepFn P c L j) hinv

/-- **The game's responses are the handler's responses.** -/
theorem srHandlerRun_snd (P : SrProver r s) (c : Fin t → r.Chal) :
    (srHandlerRun P c).2 = (srTrace P c).map Prod.snd :=
  (foldl_handlerStep_agree P c (List.finRange t) Oracle.empty []
    (fun _ => rfl)).1

/-- **The game's query log denotes the handler's partial map**: `srTrace`'s
`find?` view (which the game uses for consistency, Selvage/Rbr.lean
specialization 5) and the handler's `lookup` agree on every query. -/
theorem srHandlerRun_lookup (P : SrProver r s) (c : Fin t → r.Chal)
    (q : SrMove r s) :
    (srHandlerRun P c).1.lookup q =
      ((srTrace P c).find? fun e => decide (e.1 = q)).map Prod.snd :=
  (foldl_handlerStep_agree P c (List.finRange t) Oracle.empty []
    (fun _ => rfl)).2 q

/-- **The final challenges are handler lookups with lazy fallback**:
`ρ_i = lookup(query i) |>.getD (d i)` — logged queries replay the recorded
sample, never-asked queries draw their own fresh coin. The `c_i = O(tr_{<i})`
of the FS transform, as the handler actually computes it. -/
theorem srFinalChal_eq_lookup (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k) :
    srFinalChal P c d i =
      ((srHandlerRun P c).1.lookup ((srOut P c).query i)).getD (d i) := by
  rw [srFinalChal_def, srHandlerRun_lookup]
  cases hf : (srTrace P c).find?
      (fun e => decide (e.1 = (srOut P c).query i)) <;> simp

end HandlerRun

/-! ## The FS knowledge-soundness statement, and the BCS bridge -/

/-- **Straightline FS knowledge soundness in the ROM** (lazily sampled), for
statement set `Z` with error `εfs s t δ`: ONE deterministic extractor
(polymorphic in the salt size) reading the SINGLE transcript — the
adversary's output, the derived challenges, and the query log; no rewinding —
such that for every salt size `s`, query budget `t`, `δ ∈ (0, δ*)`, and
deterministic `t`-query ROM adversary, the probability (over the game's
lazily-sampled coins) that
* the output statement lands in `Z`, and
* the extracted witness FAILS `R_{≤δ}` on the output statement, and
* the FS verifier `fiatShamir` ACCEPTS the proof string at the (canonical
  extension of the) derived challenges, with the prover's candidate `w'` in
  `R'_{≤δ}`
is at most `εfs s t δ`.

The adversary type is `SrProver` — in the ROM an FS adversary IS a
state-restoration prover: its oracle queries are salted transcript prefixes,
which is what `SrMove` says. `s = 0` is plain FS; positive `s` is the BCS
salt channel. -/
def FsStraightlineKnowledgeSoundness (r : Reduction) (Z : Set (Stmt r))
    (εfs : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ E : (s : ℕ) → SrExtractor r s,
    ∀ (s t : ℕ), ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, ∀ P : SrProver r s,
      uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) (fun coins =>
        let log := srTrace P coins.1
        let o := P.out (log.map Prod.snd)
        let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
        o.stmt ∈ Z ∧
        ¬ RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y (E s o ρs log) ∧
        ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
          fiatShamir r s (fsOracle o ρs) o = some (x', y') ∧
          RelaxedMem r.R' δ o.stmt.idx x' y' o.w')
        ≤ εfs s t δ

/-- **The BCS bridge, proved**: the FS game in the lazily-sampled ROM IS the
state-restoration game of WARP Def B.2 — same adversaries (oracle queries =
SR moves), same coins (lazy sampling = the SR log discipline), same events
(`fiatShamir` at the canonical oracle = the base verifier at the derived
challenges, `fiatShamir_fsOracle`). Both directions, same extractor. -/
theorem fsStraightline_iff_sr (r : Reduction) (Z : Set (Stmt r))
    (ε : ℕ → ℕ → ℝ → ℝ) :
    FsStraightlineKnowledgeSoundness r Z ε ↔
      StraightlineSrKnowledgeSoundness r Z ε := by
  unfold FsStraightlineKnowledgeSoundness StraightlineSrKnowledgeSoundness
  refine exists_congr fun E => ?_
  refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun δ =>
    imp_congr_right fun hδ => forall_congr' fun P => ?_
  have hev : (fun coins : (Fin t → r.Chal) × (Fin r.k → r.Chal) =>
      let log := srTrace P coins.1
      let o := P.out (log.map Prod.snd)
      let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
      o.stmt ∈ Z ∧
      ¬ RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y (E s o ρs log) ∧
      ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
        fiatShamir r s (fsOracle o ρs) o = some (x', y') ∧
        RelaxedMem r.R' δ o.stmt.idx x' y' o.w') =
      (fun coins : (Fin t → r.Chal) × (Fin r.k → r.Chal) =>
      let log := srTrace P coins.1
      let o := P.out (log.map Prod.snd)
      let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
      o.stmt ∈ Z ∧
      ¬ RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y (E s o ρs log) ∧
      ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
        r.verify o.stmt.idx o.stmt.x o.stmt.y o.πs ρs = some (x', y') ∧
        RelaxedMem r.R' δ o.stmt.idx x' y' o.w') := by
    funext coins
    simp only [fiatShamir_fsOracle]
  rw [hev]

/-- **The keystone statement**: Fiat–Shamir of a relaxed-RBR reduction
preserves knowledge soundness in the ROM, STRAIGHTLINE, with the loss-free
error `(t + k) · ε_rbr(δ)` — for every reduction, every RBR instance, every
statement set, and every nonnegative uniform round-error bound. Carries the
[OB-2′] nonnegativity guard: Selvage/Depth.lean machine-checked the unguarded
form false (`OB2_depth_composition_false`), and FS inherits the repair, not
the hole. -/
def FsOfRbrSound : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    (εrbr : ℝ → ℝ),
    (∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ) →
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) →
    FsStraightlineKnowledgeSoundness r Z
      (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ)

/-- The FS keystone statement is EQUIVALENT to the repaired depth obligation
[OB-2′] (`OB2_depth_composition_nonneg`, Selvage/Depth.lean): the transcript
layer adds no unproved mathematics of its own on top of the depth
composition. -/
theorem fsOfRbrSound_iff_depth :
    FsOfRbrSound ↔ OB2_depth_composition_nonneg := by
  unfold FsOfRbrSound OB2_depth_composition_nonneg
  exact forall_congr' fun r => forall_congr' fun rbr => forall_congr' fun Z =>
    forall_congr' fun εrbr => imp_congr_right fun _ =>
      imp_congr_right fun _ => fsStraightline_iff_sr r Z _

/-! ## Teeth: the FS verdict is the oracle's doing -/

/-- The challenge-sensitive one-round reduction: everything `Unit`/trivial
except the challenge alphabet (`Bool`) and the verifier, which accepts iff
the single derived challenge is `true`. The smallest reduction whose FS
verdict is a function of the ORACLE, not of the proof string alone. -/
def chalReduction : Reduction where
  Idx := Unit
  X := Unit
  A := Unit
  X' := Unit
  A' := Unit
  W := Unit
  n := 1
  n' := 1
  n_pos := one_pos
  n'_pos := one_pos
  R := fun _ _ _ _ => True
  R' := fun _ _ _ _ => True
  k := 1
  k_pos := one_pos
  PMsg := Unit
  Chal := Bool
  pmsgNonempty := ⟨()⟩
  chalFintype := inferInstance
  chalNonempty := ⟨true⟩
  δstar := 1
  δstar_pos := one_pos
  δstar_le_one := le_refl 1
  verify := fun _ _ _ _ ρs => if ρs 0 then some ((), fun _ => ()) else none

/-- A concrete FS proof string for `chalReduction` at salt size 0 (plain FS). -/
def chalOutput : SrOutput chalReduction 0 :=
  ⟨⟨(), (), fun _ => ()⟩, fun _ => (), fun _ => Fin.elim0, ()⟩

/-- **Teeth, both poles on ONE proof string**: the FS verifier REJECTS
`chalOutput` under the all-`false` oracle and ACCEPTS it under the all-`true`
one. The challenge derivation is load-bearing: the verdict flips with the
oracle's answer at the transcript prefix, so `fiatShamir` is neither
constantly accepting nor constantly rejecting, and the rejecting transcript
demanded by the keystone is BUILT, not asserted. -/
theorem fiatShamir_teeth :
    fiatShamir chalReduction 0 (fun _ => false) chalOutput = none ∧
    fiatShamir chalReduction 0 (fun _ => true) chalOutput =
      some ((), fun _ => ()) :=
  ⟨rfl, rfl⟩

/-! ## The keystone, ATLAS-fielded -/

/-- **[FS-sound] The FS-of-RBR keystone**, with the ATLAS fields as REAL
structure fields (not doc-comment TODOs):
* `oracle_inhabited` — SATISFIABLE: the ROM handler exists for every
  reduction's query type (a built `Oracle.empty`, not an axiom; proved
  unconditionally, `fsKeystone_oracle_inhabited`);
* `teeth` — a BUILT proof string the FS verifier rejects, and an oracle under
  which the same string is accepted (proved unconditionally,
  `fsKeystone_teeth`);
* `premise` — PREMISE-INHABITATION: a base RBR reduction exists (proved
  unconditionally, `fsKeystone_premise`, via Selvage/Depth.lean's
  `trivialReduction`/`trivialRbr`);
* `sound` — THE STATEMENT: FS of RBR preserves knowledge soundness,
  straightline, at `(t + k) · ε_rbr`. Proved from [OB-2a]
  (`fsKeystone_of_gameSlotBound`) — and [OB-2a] is now discharged upstream
  (`gameSlotBound_proved`, Selvage/Depth.lean: the general lazy-rnd resolver +
  uniformity kernel), so the keystone holds unconditionally
  (`fsKeystone_proved`; the CY24/BMNW25 FS-of-RBR route, WARP Thm B.4). -/
structure FsOfRbrKeystone : Prop where
  /-- Satisfiable: the lazy-sampling ROM handler is inhabited — the floor is
  a built object. -/
  oracle_inhabited : ∀ (r : Reduction) (s : ℕ),
    Nonempty (Oracle (SrMove r s) r.Chal)
  /-- Teeth: some FS proof string is REJECTED under some oracle — and
  accepted under another, so the verdict is the oracle's doing. -/
  teeth : ∃ (r : Reduction) (s : ℕ) (o : SrOutput r s)
    (O O' : SrMove r s → r.Chal),
    fiatShamir r s O o = none ∧ ∃ v, fiatShamir r s O' o = some v
  /-- Premise-inhabitation: a reduction with an RBR knowledge-soundness
  instance exists. -/
  premise : ∃ r : Reduction, Nonempty (RbrKnowledgeSoundness r)
  /-- The statement: FS-of-RBR knowledge-soundness preservation,
  straightline, loss-free. -/
  sound : FsOfRbrSound

/-- Satisfiable, unconditionally: the handler is inhabited (by the built
`Oracle.empty` — no hypotheses, no axiom). -/
theorem fsKeystone_oracle_inhabited (r : Reduction) (s : ℕ) :
    Nonempty (Oracle (SrMove r s) r.Chal) := ⟨Oracle.empty⟩

/-- Teeth, unconditionally: the built rejecting (and accepting) transcript. -/
theorem fsKeystone_teeth : ∃ (r : Reduction) (s : ℕ) (o : SrOutput r s)
    (O O' : SrMove r s → r.Chal),
    fiatShamir r s O o = none ∧ ∃ v, fiatShamir r s O' o = some v :=
  ⟨chalReduction, 0, chalOutput, fun _ => false, fun _ => true,
    fiatShamir_teeth.1, ⟨_, fiatShamir_teeth.2⟩⟩

/-- Premise-inhabitation, unconditionally: Selvage/Depth.lean's trivial
reduction carries an RBR knowledge-soundness instance. -/
theorem fsKeystone_premise :
    ∃ r : Reduction, Nonempty (RbrKnowledgeSoundness r) :=
  ⟨trivialReduction, ⟨trivialRbr⟩⟩

/-- **The keystone, assembled from [OB-2a]**: `GameSlotBound`
(Selvage/Depth.lean) implies the whole FS-of-RBR keystone — the three companion
fields unconditionally, and `sound` through the proved chain [OB-2a] ⟹
[OB-2′] (`OB2_nonneg_of_gameSlotBound`) ⟺ `FsOfRbrSound`
(`fsOfRbrSound_iff_depth`). The transcript layer's own reductions (the BCS
bridge, the handler correspondence) are closed in this file; NOTHING beyond
[OB-2a] is assumed — and [OB-2a] is now proved (`fsKeystone_proved` below). -/
theorem fsKeystone_of_gameSlotBound (H : GameSlotBound) : FsOfRbrKeystone where
  oracle_inhabited := fsKeystone_oracle_inhabited
  teeth := fsKeystone_teeth
  premise := fsKeystone_premise
  sound := fsOfRbrSound_iff_depth.mpr (OB2_nonneg_of_gameSlotBound H)

/-- **The keystone, unconditional**: [OB-2a] is discharged
(`gameSlotBound_proved`, Selvage/Depth.lean), so FS-of-RBR knowledge-soundness
preservation holds with no remaining seam. -/
theorem fsKeystone_proved : FsOfRbrKeystone :=
  fsKeystone_of_gameSlotBound gameSlotBound_proved

#check @Oracle.respond_consistent
#check @srFinalChal_eq_lookup
#check fsStraightline_iff_sr
#check fsOfRbrSound_iff_depth
#check fsKeystone_proved

end Minidregg.Selvage
