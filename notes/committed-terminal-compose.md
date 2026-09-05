# CommittedTerminal compose — the three pieces that make a Stage-0 proof receipt exist end to end

**2026-09-05. Lane on `/Users/ember/dev/minidregg` branch `main` (HEAD moved from `c604944` to
`e3be707` under the lane — another lane committing; unrelated).** Nothing committed, no stash,
no `add -A`. Three new files, all untracked, no other file touched:

| file | lines | what |
|---|---|---|
| `Compiler/CommittedTerminalFactored7.lean` | 619 | `[CT-factored7]`: the generic lane walker; the seven factored terminals realized from the opened word |
| `Compiler/CommittedTerminalCompose.lean` | 378 | `[CT-compose]`: `Fintype Ext6Q`; `readExt6` injective; the gamma event priced; the ONE ledger theorem |
| `Compiler/CommittedTerminalController.lean` | 828 | `[CT-controller-lanes]`: the computable `check`, its reflection, the honest lane prover, completeness, refusals |

Dependency order: realizer → factored7 → compose → controller. Every `file:line` below was opened
before use. `Compiler.lean` is NOT edited: the coordinator adds the three imports after
`import Compiler.CommittedTerminalRealizer` (line 101) if they enter the umbrella.

## 0. Two statements corrected before proof (law: statement-first)

**(a) `factored7_eq_realized` is false as named.** The unit asked to "prove the factored product
equals the single realized terminal". Off the Boolean cube it does not: `mle A r · mle B r ≠
mle (A·B) r` (the MLE of a product is not the product of MLEs — `GateMleExt6.lean:177-205` says
exactly this: the clear residual and the factored `Â·B̂−Ĉ` agree *at every Boolean corner*, and
authenticating the factorization off the cube is the seam). On a satisfying trace the single
terminal is `0` (`demo_honest_terminal_zero`) while the factored expression is generically
nonzero. Kernel-decided refutation on the emitted demo descriptor, same trace, same `γ`, same `r`:

```lean
theorem factored7_ne_single : laneTerminalExpression demoSeven ≠ ext6Zero := by decide +kernel
```

and at Stage 0 the honest `(1, 2)` trace's factored expression printed as
`⟨1131172113, 1997052208, 1704682423, 1480561983, 762620036, 1816366320⟩` (single terminal `0`).
The TRUE relations, proved: each protocol closes against its OWN terminal from the SAME opened
word — `factored7_closes_realized` (below) beside the realizer's `honestRounds_closes_realized` —
and their zero claims coincide (`sum_gammaResidualTable`: `Σ_b gammaResidualTable b = Σ_k γ^k res_k`).

**(b) The ledger has three summands, not one.** "`Pr[bad] ≤ m·2/|F| + 0`" omits the gamma
batching: a failing trace whose `Σ_k γ^k res_k` vanishes is accepted by an honest-looking
sumcheck with no bad round at all (the realizer note's own §4 names this under `[CT-compose]`).
The ledger theorem therefore carries `holds ∨ gammaZero ∨ sumcheckBad`, priced `0` (terminal,
under `S`) + `(N−1)/|Ext6Q|` (gamma) + `m·1/|Ext6Q|` (rounds, degree 1). The `m·2/|F| + 0` the
unit named is delivered as a corollary (`sumcheck_prob_le_two`) — the `2` is the factored
quadratic protocol's per-round price, which this verifier does not pay.

**(c) Which protocol the computable controller runs.** The clear degree-one MLE sumcheck of
`GateMleExt6` (`honestRounds = mleHonest (gammaResidualTable …)`), zero-anchored, closing at the
single realized terminal — the protocol whose terminal `CommittedTerminal` IS. Not the
quadratic factored protocol `Ext6GateProofController.Accepts` reflects: its seven terminals are
realized (piece 1), but its honest round messages are pairwise products over the sparse operand
tables (`Σ_{k,k'}` agreeing on the suffix bits), not built here — `[CT-factored-prover]` in §5.

## 1. `[CT-factored7]` — `Compiler/CommittedTerminalFactored7.lean`

Imports `Compiler.CommittedTerminalRealizer`, `Compiler.GateFactoredExt6`,
`Compiler.Ext6GateProofController` (for `terminalExpression` only).

**§1 the generic lane walker** — `walk gamma f wt l k gpow acc` folds a list with a running
gamma power and a per-position lane weight; every product materialized (`Ext6L`, strict).
`read_walk` / `read_walk_fin` are the one bridge:
```lean
theorem read_walk_fin … : readExt6 (walk gamma f wt l k gpow ext6Zero) =
  ∑ j : Fin l.length, F (l.get j) (readExt6 gpow * readExt6 gamma ^ (j : Nat)) * W (k + j)
```
for any lane payload `f` with field counterpart `F` (`hf`) and weight `wt` with counterpart `W`.
The seven terminals, the zero claim (compose) and the honest round messages (controller) are
instances.

**§2 the seven** — `laneTerminalKind d wv γ r encNat : TerminalKind → Ext6L` (six op-selected
gate walks, gamma-weighted except `mulB`; one root-pin walk from position `|gates|` with
`γ^|gates|`); `laneTerminal7 j := laneTerminalKind (terminalOrder j)`. The bridge, by kind:
```lean
theorem read_laneTerminalKind … (kind : TerminalKind) :
    readExt6 (laneTerminalKind d wv gamma r encNat kind) =
      (terminalFunctional kind d wv enc (readExt6 gamma) (fun i => readExt6 (r i))).eval (liftWord wv)
```
(`mle_operandTable_sparse` exposes the sum inside `mle_operandTable_eq_selectorFunctional_eval`).

**§3 `TerminalOpenings` inhabited** from the opened word (`terminalOpeningsOfLanes`); then
`factoredRounds_terminal_of_openings` (REUSED) closes the factored quadratic chain:
`factored7_closes : scChain (gammaBatched…) (factoredRounds …) (chalOf r') m = terminalExpression (read ∘ laneTerminal7 …)`.

**§4 the realizer for the seven** — `realize7 commit d encNat γ r rt (op : Opening7 n)`
(word + seven claims; `rootMismatch`/`valueMismatch`), `realize7_ok_iff`, `realize7_complete`,
and under the named premise:
```lean
theorem realize7_sound (S : BindingCommitment Root BabyBear (Fin n) Op) … (h : realize7 S.commit … (S.commit w) op = .ok v) :
    v = laneTerminal7 d (traceOf w) gamma r encNat          -- a LANE equality at the committed trace
noncomputable def terminalOpeningsOfBinding … : TerminalOpenings d (traceOf w) enc (readExt6 gamma) (readExt6 ∘ r)
    -- openLinear kind := ⟨readExt6 (v (kindIndex kind)) − constant, …⟩ : the receipt's own seven inhabit the interface
theorem factored7_closes_realized … (hd : descriptorHolds d (traceOf w)) :
    scChain 0 (factoredRounds d (traceOf w) enc (readExt6 gamma) (chalOf r')) (chalOf r') m =
      terminalExpression (fun j => readExt6 (v j))
```
This is what replaces the controller's seven values "on faith": `Accepts`' terminal clause
`scChain 0 … m = terminalExpression receipt.terminalValue` is now a theorem at values a
`BindingCommitment`-backed opening produced.

**§5 ATLAS, kernel-decided on `demoDescriptor` at `idealCommitment`, `m = 5`:** the honest seven
pinned as LITERALS (`demoSeven`, printed once, recomputed by the kernel) — `realize7_complete_demo`
accepted; `realize7_refuses_forged_value` (`mulA` off by one → `valueMismatch`);
`realize7_refuses_forged_word` (tampered word → `rootMismatch`); `factored7_ne_single` (§0a).
**§6 Stage 0 (`m = 13`, 4,148 residuals), compiled `#eval`, throw-teeth:**
```
stage0 factored7: honest (1, 2) accepted, seven terminals realized
stage0 factored7: factored expression on the honest trace { c0 := 1131172113, … } (the single terminal is 0)
stage0 factored7: forged word refused at the honest root
stage0 factored7: forged word authenticated at its own root
```

## 2. `[CT-compose]` — `Compiler/CommittedTerminalCompose.lean`

**§1 the challenge field is finite.** The tree's `uniformProb` needs `Fintype`, and
`Ext6Q = AdjoinRoot ext6Polynomial` had no instance (this is why `GateFactoredExt6` counts bad
etas in an arbitrary `Finset`). Built noncomputably: `ext6Finite := Module.finite_of_finite BabyBear`,
`ext6Fintype := Fintype.ofFinite`, and `card_ext6 : Fintype.card Ext6Q = babyBearP ^ 6` via
`Module.card_eq_pow_finrank` + `ext6Q_finrank`. Also the lane carrier reads injectively —
`readExt6_injective` through `AdjoinRoot.powerBasis` (`ext6Polynomial_natDegree = 6`,
`linearIndependent_iff'`) — the lemma the realizer note sized at ~40 lines; it is what lets lane
decisions carry field theorems (`lane_eq_of_read`).

**§2 the gamma event.** `sum_gammaResidualTable`; then
```lean
theorem card_gammaZero_le (challenges : Finset Ext6Q) … (hfail : ¬ descriptorHolds d wv) :
    (challenges.filter fun γ => (∑ b, gammaResidualTable d wv enc γ b) = 0).card ≤ (descriptorResiduals d wv).length - 1
theorem gammaZero_prob_le … : uniformProb Ext6Q (fun γ => (∑ b, gammaResidualTable d wv enc γ b) = 0) ≤ ((N − 1 : ℕ) : ℝ) / Fintype.card Ext6Q
```
— `card_bad_eta_le` (REUSED) at zero trace/constants/weights, no new root counting.
`laneZeroClaim` (the walker with weight `1`) + `read_laneZeroClaim` make it kernel-decidable:
`laneZeroClaim_honest_zero`, `laneZeroClaim_tampered_ne_zero` (the gamma leg catches the demo's
tampered trace at the demo `γ`), `tampered_zeroClaim_false` (the same in the field, via injectivity).

**§3 the ledger theorem — copied:**
```lean
/-- What the full-word gate proof's verifier decides, read into the field. -/
structure GateProofAccepts (S : BindingCommitment Root BabyBear (Fin n) Op) (d) (encNat) (gamma : Ext6L)
    (r : Fin m → Ext6L) (rt : Root) (op : Opening n) (v : Ext6L) (prover : ℕ → Polynomial Ext6Q) : Prop where
  terminal : realize S.commit d encNat gamma r rt op = .ok v
  rounds : ∀ i, i < m → (prover i).eval 0 + (prover i).eval 1 = scChain 0 prover (chalOf fun i => readExt6 (r i)) i
  closes : scChain 0 prover (chalOf fun i => readExt6 (r i)) m = readExt6 v

theorem gateProof_sound (S : BindingCommitment Root BabyBear (Fin n) Op) (d : ConstraintDescriptor BabyBear)
    (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L) (w : Fin n → BabyBear) (op : Opening n)
    (v : Ext6L) (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q)
    (hacc : GateProofAccepts S d encNat gamma r (S.commit w) op v (P (chalOf fun i => readExt6 (r i)))) :
    descriptorHolds d (traceOf w) ∨
      (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0 ∨
      AdaptiveAcceptsFalse P (mleHonest (gammaResidualTable d (traceOf w) enc (readExt6 gamma)))
        0 (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) (fun i => readExt6 (r i))
```
Proof: `realize_sound` (the terminal, error zero — `S.commit_injective` is the only property
consumed) + `scChain_mleHonest_final` (the honest chain ends at the same MLE) — the sumcheck
event is the tree's own `AdaptiveAcceptsFalse`, nothing re-derived. Prices:
```lean
theorem sumcheck_prob_le … (hpm : PrefixMeasurable P) (hdeg : ∀ χ i, i < m → (P χ i).degree < 2) :
    uniformProb (Fin m → Ext6Q) (AdaptiveAcceptsFalse P (mleHonest table) 0 (∑ b, table b)) ≤ (m : ℝ) * (1 / Fintype.card Ext6Q)
theorem sumcheck_prob_le_two … : … ≤ (m : ℝ) * (2 / Fintype.card Ext6Q) + 0      -- the number the unit named, as a corollary
theorem sumcheck_prob_le_explicit … : … ≤ (m : ℝ) * (1 / ((babyBearP : ℝ) ^ 6))
```
**The Stage-0 ledger, honest sentence:** *full-word gate proof, `m = 13`, `N = 4148`, under a
`BindingCommitment` `S`: terminal error `0`; gamma leg `≤ 4147/p^6`; sumcheck leg `≤ 13/p^6`;
`p = 2^31 − 2^27 + 1`, `p^6 ≈ 2^186`.* The two legs are over different sample spaces (`γ`, then
`r`), stated as the tree's two-stage precedent (`sumcheck_retires_batch`); one joint number over
`(γ, r)` is `[CT-joint-price]` (§5). The commitment premise is the named instance `S`
(`[COMMIT-CR]` is its ledger); `γ` and `r` are transcript inputs — Fiat–Shamir is not priced here.

## 3. `[CT-controller-lanes]` — `Compiler/CommittedTerminalController.lean`

**The obstruction, exhibited exactly.** `Ext6GateProofController.lean:44` opens
`noncomputable section` because `Receipt` (`:216`) carries `gamma`, `roundChallenge`,
`terminalValue`, `eta`, `aggregateValue : Ext6Q` and `roundMessage : Polynomial Ext6Q` — every
operation on them is `AdjoinRoot.instField` (`noncomputable`); `digestToExt6` (`:56`) lands in
`Ext6Q` through `toExt6` (`noncomputable`); `etaAggregateLeft` (`:299`) sums `Finsupp`-weighted
`TraceAffineFunctional`s; `Ext6GateProofDeployment.check` (`:230`) is `decide` under `classical`
and its codecs are `countableCodec` enumerations (`:68`, "deliberately not advertised as a
released native ABI: `Ext6Q` is currently noncomputable"). `cshake` (`Tower256ConcreteBackend.lean:488`)
is `noncomputable def` although `Sp800185Cshake256.controller` (`:183`) is a plain `def` — the
hash is not the blocker. No edit to the controller file makes `Accepts` computable short of
replacing its carrier; per instruction it is untouched and the computable controller is built
beside it.

**Built (all `def`, `#eval` runs them):**
```lean
structure Transcript (m) where message : Fin m → Ext6L × Ext6L   -- (g(0), g(1)) of a degree-≤1 message
                               challenge : Fin m → Ext6L
structure Receipt (Root) (m) where root : Root; gamma : Ext6L; transcript : Transcript m; terminal : Ext6L
inductive Failure | terminal (e : CommittedTerminalRealizer.Failure) | roundCheck | terminalMismatch
def check (commit) (d) (encNat) (gamma) (rt : Root) (op : Opening n) (tr : Transcript m) : Except Failure (Receipt Root m)
  -- realize → every round's g_i(0)+g_i(1) = claim_i on the zero-anchored lane chain → chain closes at the realized terminal
```
`laneChain` mirrors `scChain 0` structurally; `readPoly1 (g0,g1) := C (g1−g0)·X + C g0` is
`roundPoly`'s shape; `read_laneChain`, `roundsOk_iff`, `check_ok_spec`/`check_ok_of`, the three
refusal lemmas. Reflection and the ledger at the controller:
```lean
theorem check_accepts (S) … (h : check S.commit d encNat gamma rt op tr = .ok rc) :
    GateProofAccepts S d encNat gamma tr.challenge rt op rc.terminal (fieldProver tr)
theorem gateProof_sound_lane (S) … (h : check S.commit d encNat gamma (S.commit w) op tr = .ok rc) … (P)
    (hP : ∀ i, i < m → P (chalOf fun q => readExt6 (tr.challenge q)) i = fieldProver tr i) :
    descriptorHolds d (traceOf w) ∨ (∑ b, gammaResidualTable …) = 0 ∨ AdaptiveAcceptsFalse P (mleHonest …) 0 (∑ b, …) r'
```
with `constantStrategy tr` discharging `PrefixMeasurable` and degree `< 2` for `sumcheck_prob_le`.

**The honest lane prover — the real mathematics of the unit.** Round `i`'s message is one walk
over the residual list: for residual `k` at corner `b`, the weight `γ^k · res_k · ∏_{j<i} χ_{b_j}(r_j)`
goes to `g(0)` if `b_i = false`, to `g(1)` if `true` (`roundWalk`, prefix chi computed once per
residual; `laneRound`; `honestTranscript`). Linear in the descriptor, never `2^m`. It is honest
because of
```lean
theorem residualSum_sparse (f) (c : Fin N → Ext6Q) (e) (hf : ∀ x, mle f x = ∑ k, c k * chiEval (e k) x) :
    ∀ j, j ≤ m → ∀ x, residualSum (mle f) x (m - j) = ∑ k, c k * prefixChiEval (e k) x (m - j)
```
(downward induction through `residualSum_eq_roundSum_bool`/`residualSum_step`, REUSED: each
descent pins one coordinate to `0` and `1` and the two chi factors sum to `1`), whence
`roundSum_sparse`, `read_laneRound`, and
```lean
theorem readPoly1_laneRound … : readPoly1 (laneRound d wv gamma r encNat i) = mleHonest (gammaResidualTable d wv enc (readExt6 gamma)) (chalOf r') i
theorem fieldProver_honest … : fieldProver (honestTranscript d wv gamma r encNat) = mleHonest (gammaResidualTable …) (chalOf r')   -- as functions
```
Then:
```lean
theorem receipt_complete (commit) … (hd : descriptorHolds d (traceOf w)) :
    check commit d encNat gamma (commit w) ⟨w, laneTerminal gamma r encNat (descriptorResiduals d (traceOf w))⟩
      (honestTranscript d (traceOf w) gamma r encNat) = .ok ⟨commit w, gamma, honestTranscript …, laneTerminal …⟩
theorem receipt_refuses_tamper (S) … (hne : op.word ≠ w) : check S.commit … (S.commit w) op tr = .error (.terminal .rootMismatch)
theorem receipt_refuses_false_claim … (hz : (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) ≠ 0) :
    check commit … (commit w) ⟨w, laneTerminal …⟩ (honestTranscript d (traceOf w) …) = .error .roundCheck
```
— the last is the gamma leg closed for the *honest* prover: a failing trace's own prover is
refused at round 0 for all but `≤ N−1` gammas; the adversarial prover is the ledger's business.

**ATLAS, kernel-decided on `demoDescriptor` (`m = 5`, 23 residuals):** `receipt_complete_demo`
(the honest 5-round proof accepted; the kernel computed all five messages — they are `(0,0)`
because a satisfying trace's table is zero, and the receipt is pinned to `zeroTr`);
`receipt_refuses_tamper_demo` (root); `receipt_refuses_false_claim_demo` (the tampered trace at
its own root with its own honest prover: `roundCheck`); `receipt_refuses_forged_terminal_demo`
(the tampered trace, its true terminal pinned as the literal
`⟨1612364632, 676004279, 1984653847, 1968643124, 911508879, 94536224⟩`, with the zero transcript:
every round passes, the chain closes at `0 ≠` it: `terminalMismatch`);
`receipt_refuses_tampered_message_demo` (message 2 replaced by `(1,0)`: `roundCheck`).

**Stage 0, compiled `#eval`, throw-teeth (`m = 13`, 4,148 residuals, 4,131 wires):**
```
stage0 controller: honest (1, 2) proof accepted end to end: 13 rounds, terminal 0
stage0 controller: forged word refused at the honest root
stage0 controller: forged word at its own root, its own honest prover refused at a round check (zero claim false)
stage0 controller: forged word with the honest transcript refused at the terminal
```
Read exactly: *the Stage-0 proof receipt exists end to end at full word* — the honest
`(1, 2)` candidate (4,131 wires) is committed (ideal root), opened, its 13 honest degree-one
round messages computed by the lane prover (one walk of 4,148 residuals per round), every round
check and the terminal check decided by `check`, and a `Receipt` returned; the forged `Z = 4`
word is refused on all three routes (root, round, terminal). Time-to-proof on the derived path,
terminal + sumcheck legs, at full word: **the Lean interpreter, inside a ~4-minute single-file
elaboration that also runs the kernel decides** (`#eval` wall-clock, evidence of nothing beyond
"seconds to a couple of minutes"). Label: *full-word resolution; `γ`, `r` transcript inputs (no
Fiat–Shamir); `idealCommitment` root; `[CT-sampled]`, `[CT-merkle-profile]`,
`[CT-fiat-shamir-lanes]` open.*

## 4. Elaboration status, pins, time

Single-file `lake env lean`, `pgrep -f "lake build"` empty before each run (the umbrella that
was running at lane start finished before the first elaboration; it was never started by this
lane):

| file | exit | errors | warnings | wall | pins (`#guard_msgs … #print axioms`) |
|---|---|---|---|---|---|
| `CommittedTerminalFactored7.lean` | 0 | 0 | 0 | 220 s | `read_laneTerminalKind`, `factored7_closes`, `realize7_sound`, `factored7_closes_realized`, `DemoInstance.realize7_complete_demo`, `…refuses_forged_value`, `…refuses_forged_word`, `…factored7_ne_single` → `[propext, Classical.choice, Quot.sound]` |
| `CommittedTerminalCompose.lean` | 0 | 0 | 0 | 8 s | `card_ext6`, `gateProof_sound`, `gammaZero_prob_le`, `sumcheck_prob_le`, `sumcheck_prob_le_two`, `readExt6_injective`, `DemoInstance.laneZeroClaim_tampered_ne_zero`, `…tampered_zeroClaim_false` → same three |
| `CommittedTerminalController.lean` | 0 | 0 | 0 | 185 s | `check_accepts`, `gateProof_sound_lane`, `residualSum_sparse`, `readPoly1_laneRound`, `receipt_complete`, `receipt_refuses_tamper`, `receipt_refuses_false_claim`, `DemoInstance.honestTr_eq_zeroTr`, `…receipt_complete_demo`, `…receipt_refuses_tamper_demo`, `…receipt_refuses_false_claim_demo`, `…receipt_refuses_forged_terminal_demo`, `…receipt_refuses_tampered_message_demo` → same three |

No `sorry`, no `axiom`, no `native_decide`, no `#guard` in any of the three (grep count 0 each).
`scripts/check-import-boundary.sh`: `OK: Theory`, `OK: Selvage` (nothing under `Theory/`,
`Selvage/`, `Assurance/`, `prover/`, `docs/`, `LICENSE*`, `NOTICE` touched). Targeted
`lake build Compiler.CommittedTerminalFactored7 Compiler.CommittedTerminalCompose Compiler.CommittedTerminalController`:
**`Build completed successfully`, exit 0** (oleans for all three under `.lake/build/lib/lean/Compiler/`); never the umbrella. The wall-clock is the kernel decides (§6): the walks are seconds in the
interpreter, minutes in the kernel.

**Two failures on the way, both statement-preserving.** (1) `receipt_complete_demo` first hit
the 200 000-heartbeat cap and then reported "reduction got stuck at `▸`": the *derived*
`DecidableEq` for a structure with function fields casts along each field equality, and the
kernel K-reduces that cast only when both endpoints are the same term — never for two functions
that merely agree pointwise (`fun i => laneRound … i` vs `fun _ => (0,0)` is stuck on the
symbolic `i`). Fixed by hand-written instances through `decidable_of_iff` on the field
conjunction (no casts; the pi instance iterates concrete indices, as `ext6_known_product`
already relies on), and by deciding `honestTr_eq_zeroTr` once (`set_option maxHeartbeats 1000000
in`, the tree's idiom: `BaseFoldBcsQuerySampling.lean:152`) and then the cheap check on
`zeroTr`. Anyone deciding equality of a computed `Transcript`/`Receipt` will hit this again.
(2) `factored7_eq_realized` as handed — §0(a).

## 5. What remains, sized

| obligation | shape | size |
|---|---|---|
| `[CT-factored-prover]` | the quadratic factored protocol's honest round messages in lanes: `Σ_b (Â·B̂−Ĉ)(r_<i, t, b)` collapses to pairs `(k,k')` agreeing on the suffix bits — `O(N²)` naively, `O(N·2^{m−i})` grouped by suffix; plus `readPoly2 = quadHonest` | ~300 |
| `[CT-fiat-shamir-lanes]` | `γ`, `r_i` derived in lanes: `digestToExt6` as six limbs (`Digest.value / p^i % p`, computable) over `Sp800185Cshake256.controller` (a `def`); the causal schedule of `Ext6GateProofPositiveRun` `:105-160` reused | ~200 |
| `[CT-joint-price]` | one `uniformProb (Ext6Q × (Fin m → Ext6Q))` number `≤ (N−1)/|F| + m/|F|` from the two stages via `uniformProb_prod_le` + a union bound | ~60 |
| `[CT-sampled]`, `[CT-merkle-profile]` | unchanged from the realizer note | ~250 + seam; ~120 + CR game |
| `[CT-umbrella]` | `Compiler.lean` imports for the three modules (coordinator's call); a full `lake build Minidregg` after | 3 lines |

## 6. Lessons

* **`decide +kernel` on lane arithmetic costs ~50 s per ~1,000 `ext6MulL`** (each is 36 `ZMod`
  products unfolded through the instance tower). Every decided theorem recomputes its instance;
  the seven-terminal decides made file 1's elaboration 3:40 where the realizer's was 18 s. Budget
  it, or pin literals and decide the cheap comparison (done for `demoSeven`, `tamperedTerminal`).
* **`Fintype Ext6Q` did not exist.** The whole probability layer was unreachable at the deployed
  field; `Module.finite_of_finite` + `Fintype.ofFinite` is three lines and unblocks every
  `uniformProb` statement at `Ext6Q`.
* **The sparse partial-sum identity is the honest prover.** `residualSum_sparse` is ~25 lines
  once the downward induction is set up on `m − j`; everything else in the lane prover is the
  walker bridge again. Anyone building `[CT-factored-prover]` needs the degree-two analogue.
