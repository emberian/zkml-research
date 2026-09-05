# Light-client extractor upgrade — census §7 item 2, lane note

**Date** 2026-09-05. **Tree** `~/dev/minidregg`, branch `main` at `2df891e` (working tree; nothing committed).
**Brief** make `lightClientKnowledgeSound`'s `hbase`/`hpert` derive from the ONE execution
(`ws`/`f₀`) that `lightClientSound` is anchored at, via `seamCounterfactual`; then couple
`SelvageV0Guarantee`'s `sound`/`knowledge` fields.

## Verdict

**Closed at the word level, unique decoding.** The decoupling named in
`Assurance/SelvageV0.lean:116-120` (old numbering) is gone: `sound` and `knowledge` are now two
probability bounds over ONE sampled schedule about ONE prover `(f₀, ms, cols)`. The blocker
`Selvage/AccSoundRbr.lean:76-83` ("two-point realizer vs one-point Def-4.2 seed") is resolved at
the light-client-EVENT level by an extractor that is a pure function of one execution's public
view; it is NOT re-packaged as a WARP Def-4.2 `RbrKnowledgeSoundness` quadruple (that remains
`[ACC-sound-rbr-game]`, see "What is named, not closed").

## Files (exact list) and elaboration status

| file | status | how checked |
|---|---|---|
| `Selvage/LightClientKnowledge.lean` | **NEW**, 677 lines | `lake env lean` clean: 0 errors, 0 warnings; 6 `#guard_msgs`-pinned `#print axioms`, all `[propext, Classical.choice, Quot.sound]` |
| `Assurance/SelvageV0.lean` | **MODIFIED** (+221/−185) | `lake env lean` clean; 2 new pins (`loomV0_holds`, `SelvageV0Example.ch₁_loomV0_holds`), both `[propext, Classical.choice, Quot.sound]` |
| `scripts/check-import-boundary.sh` | run | `OK: Theory …`, `OK: Selvage …` |

Untouched (not mine): `Selvage/AccExtractChain.lean`, `Selvage/AccSoundRbr.lean`,
`Selvage/ZkExtraction.lean` (read only). No `sorry`, no `axiom`, no `#guard`. No commits.

Oleans: I emitted `.lake/build/lib/lean/Selvage/LightClientKnowledge.olean` and refreshed
`Assurance/SelvageV0.olean` single-file (`lake env lean -o …`) so downstream single-file checks
work; lake will re-derive its own traces on the next build.

### Two things the integrator must know

1. **`Assurance/SelvageV0Manifest.lean` (NOT in my touch list) now fails at exactly one entry** —
   by design: it is the bit-rot guard ("if a cited theorem's type drifts, this file FAILS TO
   BUILD — that failure IS the point"). Read-only single-file check:
   `Assurance/SelvageV0Manifest.lean:707:50 Application type mismatch` (`manifest_loomV0_holds`)
   and the dependent pin at `:1406`. Every other manifest entry elaborates. Drop-in replacement
   for lines 673–709 is at the end of this note.
2. **`Selvage.lean` root does not list the new module** (other lanes are touching `Selvage.lean`
   concurrently; I did not open it). The module is reachable through
   `Assurance.SelvageV0 → Selvage.LightClientKnowledge`, so the `Minidregg` umbrella builds it;
   the `Selvage` umbrella alone will not. One import line to add when convenient:
   `import Selvage.LightClientKnowledge`.

## Statements (copied from the file)

### The extractor — a function of one execution's public view

```lean
def succSched (γs : ℕ → F) : ℕ → F := fun m => γs m + 1
theorem succSched_ne (γs : ℕ → F) (m : ℕ) : γs m ≠ succSched γs m

noncomputable def lcExtract (dom : ι ↪ F) (d : ℕ) {t : ℕ} (q : Fin t → ι) (n : ℕ)
    (γs : ℕ → F) (h₀ : ι → F) (cols : ℕ → Fin t → F) : List (ι → F) :=
  extractChain γs (succSched γs) h₀
    (seamCounterfactual (n := n) dom d q γs (succSched γs) h₀ cols)
```

No witness, no second run, no external `γalt` in the type: the extractor picks `γ + 1`.

```lean
theorem lcExtract_eq_ofFn (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) {n : ℕ} {γs : ℕ → F} {f₀ : ι → F}
    {ms : Fin n → ι → F} {cols : ℕ → Fin t → F}
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hcols : ∀ c : ℕ, c ≤ n → ∀ j, cols c j = partialFold γs f₀ ms c (q j)) :
    lcExtract dom d q n γs (foldWords γs f₀ (List.ofFn ms)) cols = List.ofFn ms
```
(+ `lcExtract_eq_ofFn_committed`: same conclusion with `hcols` replaced by `hrts`/`hver` against a
`BindingCommitment`, via `binding_columns`.) **The extractor returns the prover's own words.**

### Step 1 — `lightClientKnowledgeSound` with `hbase`/`hpert` DERIVED

```lean
theorem lightClientKnowledgeSound_seam {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    {γs : ℕ → F} {f₀ : ι → F} {ms : Fin ch.length → ι → F} {cols : ℕ → Fin t → F}
    (hγ0 : ∀ k : Fin ch.length, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hcols : ∀ c : ℕ, c ≤ ch.length → ∀ j, cols c j = partialFold γs f₀ ms c (q j))
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) (foldWords γs f₀ (List.ofFn ms)))
    (hpert : ∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs (succSched γs) k) A₀ ch)
      (foldWords (updSched γs (succSched γs) k) f₀ (List.ofFn ms))) :
    lcExtract dom d q ch.length γs (foldWords γs f₀ (List.ofFn ms)) cols = List.ofFn ms ∧
    attests C ch ∧
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (lcExtract dom d q ch.length γs (foldWords γs f₀ (List.ofFn ms)) cols)
```
`h₀ := foldWords γs f₀ ws`, `hs := seamCounterfactual …` — both computed from the prover's
`ws`/`f₀` and its opened columns. The only verification hypotheses left are about the prover's own
words at the base and the `n` counterfactual schedules. Proof: `lightClientKnowledgeSound` +
`seamCounterfactual_sound` + `extractChain_seamCounterfactual` (all cited, nothing re-derived).

### Step 2 — the apex: one prover, priced (the field SelvageV0 now cites)

```lean
theorem lightClientKnowledgeSound_oneProver [Fintype ι] [DecidableEq ι] [DecidableEq F]
    [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2) (herr0 : 0 ≤ errstar δ)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    (hcols : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      cols γv c j = partialFold (padSched γv) f₀ ms c (q j)) :
    uniformProb (Fin ch.length → F) (fun γv =>
        (∃ u, relDist (foldWords (padSched γv) f₀ (List.ofFn ms)) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u) ∧
        ¬ (attests C ch ∧
          List.Forall₂ (fun (l : Link Root F ι r) w =>
              ∃ v, relDist w v ≤ δ ∧ AccClaim.Satisfies C l.claim v) ch
            (lcExtract dom d q ch.length (padSched γv)
              (foldWords (padSched γv) f₀ (List.ofFn ms)) (cols γv))))
      ≤ (ch.length : ℝ) * (errstar δ + 2 / (Fintype.card F : ℝ))
```
(+ `lightClientKnowledgeSound_oneProver_committed`: `hcols` ⇒ `S`, `rts`, `ops`, `hrts`, `hver`.)

Read it as `Pr_γ[ verifies ∧ extraction fails ] ≤ n·(err⋆(δ) + 2/|F|)`. No `hbase`, no
`hpert`, no `hfalse`: the two roles the capstone kept apart are the two arms of one case split —
if every committed word is δ-close to a witness, the extractor returns the words themselves
unless some challenge coordinate is `0` (`n/|F|`, `uniformProb_coord_mem`); otherwise some word is
δ-far-false and `lightClientSound` (REUSED verbatim, its `hfalse` being exactly the negation)
prices verification at `n·(err⋆ + 1/|F|)`.

**Pessimistic number, on the label.** `n·(err⋆(δ) + 2/|F|)`, not `n·(err⋆ + 1/|F|)`: the extra
`1/|F|` per link is real for THIS extractor — at `γ_k = 0` link `k`'s word contributes nothing to
any recommitted fold, so no function of the opened columns sees it. Not slack; a priced blind
spot. The exact-word sharpening to `1/|F| + n/|F|` (two-point counting on the prover's own fold,
`lightClientSound_exact`'s shape) is not landed; the δ-form is what the capstone needs.

### ATLAS fields (all machine-checked, F₅, `LCExample.goodChain`)

| field | theorem | content |
|---|---|---|
| satisfiable | `lcExtract_recovers_F5` | honest prover `(xWord, [0, oneWord])`, openings `qLow = {0,1}`, `t = d = 2`: `lcExtract … = [0, oneWord]` |
| premise inhabitation | `knowledge_seam_fires_F5` | Step 1 fires at `C = RS(dom₅,2)`; all hypotheses from `goodChain_aggregate_satisfied` / `decide` / `rfl` |
| premise inhabitation | `oneProver_fires_F5` | the apex fires at `C = ⊤`, δ = 1/16, `hasMutualCorrelatedAgreement_top_affine`, bound `4/5` |
| falsifier, seam | `seam_teeth_noncodeword_F5` | prover with link-1 word `δ₂ = (0,0,1,0)` — meets the channel (`q2 δ₂ = 1`) but `δ₂ ∉ RS(dom₅,2)` (`δ₂_not_mem`, via `open_determines`). The seam-derived link-1 transcript does NOT verify at the perturbed schedule; the TRUE perturbed transcript DOES. The requested "transcript pair where `seamCounterfactual`'s precondition fails and the derived transcript does not verify". |
| falsifier, apex | `oneProver_teeth_noncodeword_F5` | same prover: every hypothesis of the apex except `hms` holds (`C = ⊤`, honest columns by `rfl`, same dials) and the bad event has probability EXACTLY `1 > 4/5`. Drop `hms` and the theorem is false. |

Why the falsifier needed its own opening set: `ZkExtractionExample.qPair = ![0, 2]` opens the
channel position 2, where the seam would decode the non-codeword *correctly*; `qLow = ![0, 1]`
leaves position 2 unopened, and that is where `[ACC-extract-bind]`'s "genuine codewords" promise
is consumed.

## Step 3 — `SelvageV0Guarantee` coupled (done)

New parameter list: `(foldRoot C A₀ ch δ errstar f₀ ms dom d q cols γs S w e f)` — `ws`, `γalt`,
`h₀`, `hs` gone; `ms : Fin ch.length → ι → F`, `dom d q cols` in. `sound` is
`lightClientSound` at `ws := List.ofFn ms` (verbatim); `knowledge` is the apex's committed form
(verbatim); `binding`/`decision` unchanged at the schedule-`γs` accumulator. `loomV0_holds`
forwards; the "Deliberately independent parameters…" sentence is replaced by the theorem name and
the residual bullet "A residual this capstone SURFACES" is rewritten as closed-at-word-level.

Keystone `ch₁_loomV0_holds` now fires BOTH probabilistic fields on the SAME ghost-replay prover
(`ms₁ = rt₁`, the unspent-nullifier word): soundness because it is δ-far-false, knowledge because
its extraction-failure event is contained in its verification event. New keystone objects:
`ms₁`, `dom₁ : FlatIx w₁ ↪ ZMod 5` (explicit `Sum.elim`, injectivity by `decide`), `q₁`,
`q₁_inj`, `ms₁_mem` (full rate: `reedSolomonCode_card_eq_top`), `rts₁`, `cols₁`,
`ch₁_knowledge_fires` (bound `2/5`). Deleted: `γalt₁`, `γs_ne₁`, `ch₁_hpert`, `ch₁_hlen`.

Design note on why `knowledge` is a probability bound and not the deterministic Step 1: with
shared `ms`/`f₀`, `hfalse` (soundness) and `hpert` at all `n` schedules (Step 1) are jointly
inconsistent — the extractor would return the δ-far-false word as a witness. A deterministic
coupled field would make `loomV0_holds` vacuous (ATLAS law 2). The apex needs neither.

## What is named, not closed

* **`[ACC-sound-rbr-game]`** (`Selvage/AccSoundRbr.lean:41-97`) — the WARP Def-4.2 quadruple
  `Reduction`/`KStateFn`/`extract`/`RbrKnowledgeSoundness` around `lcExtract`. The obstruction
  named at `:76-83` (two-point realizer vs one-point seed) is resolved: `lcExtract` is one-point
  (one execution's view) and `lightClientKnowledgeSound_oneProver` is its `extract_sound`-shaped
  event. What is NOT done is the transcript plumbing — Def 4.2's `extract : Stmt → Transcript →
  W → W` is per-round and backward, its event is over `r.Chal` per round with a `KStateFn`; the
  apex is a one-shot event over the whole schedule. Brief item 4 (wire `extractChain` into an
  `RbrKnowledgeSoundness.extract`) was optional and I did not attempt it: it is exactly
  `ZkRbrGame`'s `[ZK-RBR-game-resid]`, and doing it honestly is a lane, not a tail.
* `[FS-ROM]` (uniform → hash-derived schedule), `[COMMIT-CR]`, `[ZK-RBR-extract]` lemma A
  (seam below unique decoding) — unchanged, cited in the new file's ledger.

## Manifest entry — drop-in replacement for `Assurance/SelvageV0Manifest.lean:673-709`

```lean
/-- **`loomV0_holds`** (`Assurance/SelvageV0.lean`) — **THE v0 CAPSTONE**: the
whole tower as ONE theorem. Bundles soundness (`lightClientSound`) and
knowledge soundness (`lightClientKnowledgeSound_oneProver_committed`,
`Selvage/LightClientKnowledge.lean`) at ONE prover's data `(f₀, ms, cols)`,
and binding (`committed_extract_bind`) and decision (`decider_sound`) at the
shared final accumulator — the proof term IS the four citations, no
re-derivation. The old decoupling of the soundness slice's claimed words from
the knowledge slice's transcripts is closed at the word level; the FS
transport (`[FS-ROM]`) and the deployed commitment (`[COMMIT-CR]`) remain. -/
theorem manifest_loomV0_holds {Root : Type*} {F : Type} [Field F] {ι : Type*}
    {r : ℕ} {Op : Type*} [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι]
    [DecidableEq F]
    {foldRoot : Root → F → Root → Root} {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ} {f₀ : ι → F} {ms : Fin ch.length → ι → F}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ)
    (hfalse : ∃ p ∈ ch.zip (List.ofFn ms), ∀ v ∈ C, relDist p.2 v ≤ δ →
      ¬ AccClaim.Satisfies C p.1.claim v)
    (hseam : SeamOk ch) {dom : ι ↪ F} {d t : ℕ} (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q))
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    {S : BindingCommitment Root F ι Op}
    {rts : (Fin ch.length → F) → ℕ → Root}
    {cols : (Fin ch.length → F) → ℕ → Fin t → F}
    {ops : (Fin ch.length → F) → ℕ → Fin t → Op}
    (hrts : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length →
      rts γv c = S.commit (partialFold (padSched γv) f₀ ms c))
    (hver : ∀ (γv : Fin ch.length → F) (c : ℕ), c ≤ ch.length → ∀ j,
      S.verifyOpen (rts γv c) (q j) (cols γv c j) (ops γv c j))
    {γs : ℕ → F} {w e : ι → F} {oe : ι → Op}
    (hrt : (aggregate foldRoot γs A₀ ch).rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen (aggregate foldRoot γs A₀ ch).rt i (e i) (oe i))
    (hsat : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) e)
    (f : ι → F) :
    SelvageV0Guarantee foldRoot C A₀ ch δ errstar f₀ ms dom d q cols γs S w e f :=
  loomV0_holds halign hdC hMCA hδ0 hδB hδC herr0 hfalse hseam hdt hq hms hrts hver
    hrt hopen hsat f
```
The pin at `:1405-1406` keeps its text (`[propext, Classical.choice, Quot.sound]` — verified on
`loomV0_holds` in SelvageV0 itself). `manifest_loomV0_light_client` is untouched and still green.

## Greps for the census

* `grep -n "lcExtract" Selvage/LightClientKnowledge.lean Assurance/SelvageV0.lean` — the
  extractor is consumed by the capstone's `knowledge` field (previously `extractChain` was in no
  consumer's extractor position; it now sits inside `lcExtract`, which is).
* `grep -rn "Deliberately independent" Assurance/` → empty.
* `grep -rn "sorry\|^axiom" Selvage/LightClientKnowledge.lean Assurance/SelvageV0.lean` → empty.
