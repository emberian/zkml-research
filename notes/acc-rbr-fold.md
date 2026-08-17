# AccRbrFold — accumulation at an ADDITIVE commitment alphabet

2026-08-17. LEAN DESIGN+BUILD lane. Target file: `~/dev/minidregg/Selvage/AccRbrFold.lean`.
Brief: `nebula-vega-lessons.md` Q2 gap — Nova-family folding adds commitments; our
`AccRbrBcs`/`AccRbrBcsShifted`/`Depth` machinery accumulates Merkle roots that do not add.
Intended instance: the dual-mode MSIS commitment (`ring-hash-dual-mode.md`).

**INCREMENTAL LOG — newest at the bottom. Status of each deliverable tracked in §Ledger.**

## 0. Design decisions taken before the first line (recorded so drift is visible)

1. **Substrate said out loud: this is Lean-authored statement work in minidregg's Selvage
   tree** — no Rust anywhere, no constraint authoring anywhere; the file states structures
   and proves theorems against the landed `Reduction`/`RbrKnowledgeSoundness`/`Depth`
   machinery (`Selvage/Rbr.lean`, `Selvage/Depth.lean` — [OB-2′] is PROVED there,
   `OB2_depth_composition_nonneg_proved`).
2. **The witness ring is ℤ, not ZMod q.** Shortness lives in the ring of integers; ZMod q
   carries no norm. So the general structure is: challenge ring `R`, witness module `W`,
   commitment module `C`, both `[AddCommGroup] [Module R _]`, `commit : W →ₗ[R] C`, and a
   norm `nrm : W → ℝ` with triangle + challenge-operator-bound axioms as STRUCTURE FIELDS.
   Every `AddCommGroup` is canonically a ℤ-module, so `R := ℤ` is the canonical
   additive-group fold — exactly the brief's "carrier `[AddCommGroup C]` + a scalar action".
   The concrete instance: `W := Fin N → ℤ` (the planes), `C := Fin κ → ZMod q`,
   `commit := cast ∘ mulVec A` — plain-SIS shape, which CONTAINS module-SIS (A instantiated
   at negacyclic rotation blocks); the ring structure of R_q is a parameter choice of A,
   not of the formalization.
3. **The fold algebra is ONE object.** `mFold` (module-level partial fold) is stated over
   any `[Ring R] [AddCommGroup M] [Module R M]` with the SAME formula as the landed
   `partialFold` (`Selvage/ZkExtraction.lean:652`), and the identification
   `mFold = partialFold` at `M := ι → F` is a theorem (`rfl`-level), so there is one fold
   algebra wearing two signatures, not a twin.
4. **The norm budget is a structure-adjacent FIELD, not a comment** (the brief's ⚠):
   `budget b₀ T = b₀ + T·(ρ·B)` — ADDITIVE in T for the flat/chain fold shape (this is the
   Cyclo 2026/359 "additive norm growth" regime; a balanced fold tree would be geometric,
   and the linear accumulator chain — the shape all our Acc* machinery uses — is additive).
5. **MSIS enters as a named hypothesis, honestly labeled.** The Prop stated in Lean is
   nonexistence of a short kernel vector (`MsisHardEx`); at toy parameters it is PROVED, at
   production parameters nonexistence is expected FALSE by pigeonhole and the honest
   hypothesis is computational — which this tree cannot state without a cost model. That
   gap is a named residual (`[FOLD-msis]`), consumed never claimed, like `[COMMIT-CR]`.
6. **Where the RBR gap genuinely lives**: the knowledge state through a fold is
   "the witness is a short opening of the RUNNING accumulator at the running budget" —
   Def 4.1's three clauses hold for it exactly (empty ↔ genesis opening, full ↔ verifier
   output opened at budget T, prover-monotone by pending-blindness). The Def 4.2 round
   bound — extracting a shorter-prefix opening from a longer one, single-transcript — is
   the real content and is entered STATEMENT-FIRST (`FoldRoundBound`), with a constructor
   showing it is the ONLY missing piece, satisfiable at ε = 1, and refutable at ε = 0 with
   the identity extractor. This mirrors how lattice folding genuinely extracts (2–3
   transcripts, relaxed openings with slack) — single-transcript RBR for the fold step is
   an open pricing, the exact analog of `[ACC-rbr-bcs-shifted-resid]`(a).

## 1. What the additive alphabet DISSOLVES (the ⚑ from the brief)

`AccRbrBcsShifted` exists because Merkle fold-roots LAG their challenge: `h_{i+1}` is
committable only after `ρ_i`, so the shifted schedule needs `k+1` rounds, an inert final
challenge, and its residual (a) — the adaptive-increment round bound — is open. At an
additive commitment alphabet the fold root is `C_{i+1} = C_i + ρ_i • Cw_i` — VERIFIER-
COMPUTABLE from the genesis commitment, the per-round commitments, and the challenges.
Nothing lags: `foldReduction` has `k = T` rounds, no inert challenge, and the object
`unshifted_misaligns_F5` proves IMPOSSIBLE to carry as a Merkle message (one fixed word
equal to a ρ-dependent family) is not a message at all — it is `commit_mFold` +
`mFold_sched_local` (the fold commutes with commit; stage c reads only challenges < c).
THE TRADE: the attribution residual dissolves, and the NORM BUDGET appears in its place —
the additive alphabet's own residual, which the structure carries as a field.

## 2. The Z = ∅ corner (brief item 2) — ANSWERED, both halves theorems

**The corner RECURS verbatim; additivity does NOT dissolve it.** The `Depth.lean`
refutation (`OB2_depth_composition_false`) never reads the message algebra — it lives in
the ERROR algebra (an ℝ-valued bound unconstrained off `Z`, instantiated at `−1` against a
nonnegative probability). The fold-shaped unguarded composition (`FoldOB2Unguarded`) is
refuted by the same move at a degenerate-but-genuine fold instance (zero scheme over ℤ,
`ε := −1`, `Z := ∅`, `t = 0`): `foldOB2Unguarded_false`. The guarded composition holds
for every fold instance as a direct application of the landed [OB-2′]
(`fold_depth_composition`, riding `OB2_depth_composition_nonneg_proved`), and the FS layer
rides `fsKeystone_proved` the same way (`fold_fs_sound`), at `(t + T)·ε`. The εMSIS
accounting from the Nebula read — one ε_MSIS per absorbed commitment, Q·ε_MSIS in the ROM
ledger — is the split `(t+T)·(εr + εM) = (t+T)·εr + (t+T)·εM` (`fold_fs_price_msis`).

## 3. Concrete numbers at (q = 2^64 − 257, B = 2^16, K = 4), ρ = 1, b₀ = B

- Budget after T folds: `f(T) = B·(1 + T)` (additive; ρ = 1 short challenges).
- Binding through T folds needs the MSIS hypothesis at `2·f(T)`; that hypothesis has a
  nonvacuous norm gap iff `2·f(T) < q` — holds for **T ≤ 2^47 − 2 = 140,737,488,355,326**.
- At **T = 2^47 − 1** the budget reaches ⌈q/2⌉ = 2^63 − 128 and binding is LOST
  UNCONDITIONALLY AND CONSTRUCTIVELY: the pair `⌈q/2⌉·e₀` and `−⌊q/2⌋·e₀` are two distinct
  in-budget openings of one commitment, for EVERY key A (no primality, no rank argument —
  the wraparound pair). The capacity boundary is exact: safe-through 2^47−2, broken-at
  2^47−1.
- ⚠ the pessimistic reading, stated with the claim: "T ≤ 2^47−2" is where the STRUCTURAL
  wall sits (the hypothesis stops being satisfiable at all past it); actual security is
  MsisHard at `2B(1+T)` — an assumption that WEAKENS as T grows and whose estimator run is
  the dual-mode note's O6, un-run. The theorem is about where binding provably DIES, not
  where it provably survives.

## Ledger (updated as landed)

| # | deliverable | status |
|---|---|---|
| 1 | `AccRbrFold` structure: additive carrier, scalar action, fold step, RBR state, error accumulation | **LANDED** — `FoldCommitScheme` + `mFold` + `foldReduction` + `foldKState` (Def 4.1 clauses PROVED) + `FoldRoundBound` (statement-first, per-fold ε term) |
| 2 | depth composition for the fold shape + Z=∅ answer | **LANDED** — `fold_depth_composition`/`fold_fs_sound` (proved via [OB-2′]); `foldOB2Unguarded_false` (corner RECURS) |
| 3 | dual-mode instantiation; norm budget concrete; bounded-folds theorem; concrete T | **LANDED** — `intFoldScheme`; `binding_of_msisHardEx` ∘ budget; `DualModeParams`: safe-through 2^47−2 / broken-at 2^47−1, exact boundary |
| 4 | teeth: budget-exceeded loses binding (constructive); T=1/plain coincidence; satisfiable+refutable at one instance | **LANDED** — `binding_lost_at_wraparound` (+ fold corollary); `foldZeroToPlain`/`plainToFoldZero` + `foldSystem_one_iff_plain`; toy q=97 both ways |
| 5 | one cross-module consumer | **LANDED** — `VerifierEmbedding` (HeteroComposition) consumed by the T=0 embeddings + `dropped_norm_check_refuses_embedding` (IsEmpty, §5c fail-open made a theorem) |

(statuses above are written ahead as the work plan; each flips to a checked build before
this note claims it — see the build log at the bottom for the actual gate)

## 4. What landed, precisely (single-file green; integration gate below)

The file: `~/dev/minidregg/Selvage/AccRbrFold.lean` (~1450 lines). The shape:

- **Algebra**: `foldStep`/`mFold` over any `[Ring R] [AddCommGroup M] [Module R M]`;
  `mFold_eq_partialFold` is `rfl` — the landed `partialFold` IS the field instance, one
  object two clothings, no twin. `mFold_sched_local` (stage c reads challenges < c) and
  `FoldCommitScheme.commit_mFold` (the fold commutes with commit) together are the
  DISSOLUTION theorem for the shifted lagged-root residual: every fold root is derived,
  `foldReduction` has k = T rounds and no inert final challenge (vs the Merkle side's
  `ch.length + 1`).
- **The scheme**: `FoldCommitScheme` — `commit : W →ₗ[R] C`, `nrm` with triangle +
  operator-bound axioms, `chalSet`, `ρ`, `B` as fields; `budget b₀ T = b₀ + T·(ρ·B)`;
  `nrm_mFold_le`/`nrm_chalFoldList_le` the growth law (additive — the linear chain is the
  flat fold).
- **Binding**: `BindingAt β` ↔-sandwiched with `MsisHardEx` (`bindingAt_of_msisHardEx` at
  2β, `msisHardEx_of_bindingAt` at β — the standard factor-2 reduction, both directions
  proved); `fold_binding` = binding at the budget from MSIS at twice the budget.
- **The RBR layer**: `foldKState` — Def 4.1 with all three clauses PROVED; the state is
  "the witness is a short opening of the RUNNING accumulator at the RUNNING budget",
  uniform across rounds (empty ↔ genesis opening, full ↔ verifier's computed fold opened
  at budget T, prover-monotone by pending-blindness). `FoldRoundBound` statement-first;
  `foldRbrOfRoundBound` proves it is the ONLY missing piece of a full
  `RbrKnowledgeSoundness`; `foldRoundBound_one` (satisfiable) and
  `ToyFold.toy_roundBound_zero_id_false` (refuted at ε≡0 with the id extractor — the
  honest one-fold data inhabits the round event at challenge +1) make it a real floor:
  satisfiable + refutable + not provable. `[ACC-rbr-fold-resid]`(a) named: lattice
  folding extracts from 2–3 transcripts with RELAXED openings (slack ρ−ρ′);
  single-transcript pricing open — the exact additive-alphabet analog of
  `[ACC-rbr-bcs-shifted-resid]`(a).
- **Depth/FS**: `fold_depth_composition` and `fold_fs_sound` at `(t+T)·ε` — direct
  applications of `OB2_depth_composition_nonneg_proved` / `fsKeystone_proved`;
  `fold_fs_price_msis` splits `(t+T)(εr+εM)` — the Nebula Q·ε_MSIS accounting named.
  **Z=∅: `foldOB2Unguarded_false`** — the unguarded fold-shape composition refuted at a
  genuine fold instance (zero scheme over ℤ, ε≡−1, Z=∅, t=0, rbr inhabited via
  `foldRoundBound_one`). The corner RECURS; additivity does not dissolve it.
- **Dual-mode instance**: `intCommit` (ℤ-linear `cast ∘ (A·)` into `ZMod q` — plain-SIS
  shape, module-SIS is a parameter choice of A), `supNat`/`supNorm`, `intFoldScheme`.
  `binding_lost_at_wraparound`: constructive, key-independent, primality-free (the pair
  `⌈q/2⌉·e₀` vs `−⌊q/2⌋·e₀`). `DualModeParams`: `capacity_safe` (T ≤ 2^47−2 ⇒
  2B(1+T) < q), `capacity_broken` (⌈q/2⌉ ≤ B·2^47), `capacity_exact` (tight), and
  `production_break` (T ≥ 2^47−1 ⇒ ¬BindingAt(budget), unconditional).
- **Toy (q=97, A=[1,10], ρ=B=1)**: `msisHardEx_toy` PROVED at bound 4 (97∣Y₀+10Y₁ with
  |·|≤44 forces zero); `toy_binding_T1` (binding through one fold) AND `toy_fold_break`
  (broken at T=48) — one instance, both verdicts.
- **Consumers (cross-module, HeteroComposition)**: `foldZeroToPlain` + `plainToFoldZero`
  (T=0 IS the plain commitment, `VerifierEmbedding` both directions);
  `foldSystem_one_iff_plain` (T=1, zero genesis, unit challenge ↔ plain at ρ·B); and
  ⚑ `dropped_norm_check_refuses_embedding` — the §5c fail-open hazard as an `IsEmpty`
  theorem: the norm-forgetting relation admits NO `VerifierEmbedding` from the budgeted
  one (fwd pins a commitment in range; its unbudgeted coset is infinite along `97k·e₀`;
  accepting proofs live in a finite ball; pigeonhole).
- **Axiom pins**: 16 `#guard_msgs`-pinned `#print axioms` — `[propext, Classical.choice,
  Quot.sound]` (capacity_safe: `[propext, Quot.sound]`), no `sorryAx` anywhere.

## 5. Incidental findings (for the next lane)

- **omega incompleteness, reproduced**: `|Y₀|≤4 ∧ |Y₁|≤4 ∧ Y₀+10Y₁=97c ⊢ Y₁=0` fails
  one-shot but closes with `have hc0 : c = 0 := by omega` first — classic Omega-test
  dark-shadow gap; keep the two-step pattern for divisor-elimination goals.
- **binop% sees through type ascriptions**: `(e.encProof x : Fin 2 → ℤ) + v` still
  elaborates `HAdd (ProofSystem).Wit …` and fails; a named def wrapping the sum
  (`shiftSpike`) is the robust fix when a structure-projection type is the operand.
- **`open Classical in` on a def does not cover its consumers**: every theorem consuming
  a `decide`-baked `Verify` needs its own `classical`.

## Build log

- [x] stage 1: fold algebra + scheme + binding + wraparound break — `lake env lean` green
- [x] stage 2: reduction + kstate + round bound + depth/FS + Z=∅ — green
- [x] stage 3: int instance + toy + production arithmetic + consumers + pins — green
- [x] rooted in `Selvage.lean`, full `lake build Minidregg` green (9004 jobs)
- [x] committed: minidregg `bc29222`, exactly 2 files (`Selvage/AccRbrFold.lean` +
      the one Selvage.lean import line). ⚠ Selvage.lean's worktree carried a SIBLING
      lane's uncommitted `MultisetFingerprint` import (its file untracked) — `--only`
      would have swept it and broken HEAD (caller-committed-callee-not), so the import
      hunk was staged surgically (`git apply --cached` of a filtered patch, then plain
      `git commit` of the index). HEAD verified by `git ls-tree` + `git show`: my file
      present, no dangling MultisetFingerprint import, all four imports tracked.
