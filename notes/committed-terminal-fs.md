# CommittedTerminal Fiat–Shamir — the controller's challenges under the tree's FS keystone, the price as one number, and the factored prover

**2026-09-05. Lane on `/Users/ember/dev/minidregg` branch `main` (HEAD moved from `658bacb` to
`60f0499` under the lane — other lanes committing; unrelated). Nothing committed, no stash, no
`add -A`, no lake command while any `lake build` was live (`pgrep -f "lake build"` empty before
every one of mine; the umbrella never started by this lane). Two NEW files, both untracked, no
other file touched:**

| file | lines | what |
|---|---|---|
| `Compiler/CommittedTerminalFiatShamir.lean` | 1,394 | `[CT-fiat-shamir-lanes]` + `[CT-joint-price]`: the gate protocol as a `Reduction`, its RBR instance, `gateProof_fs_sound := fsKeystone_proved.sound …`, the deployed cSHAKE oracle, `fsCheck`/`fsProve`, `stage0Receipt_price` |
| `Compiler/CommittedTerminalFactoredProver.lean` | 667 | `[CT-factored-prover]`: the dense-fold honest prover for the quadratic factored protocol, `check7`, `gateProof7_sound`, completeness conditional on ONE named identity |

Dependency: `Controller → FiatShamir`, `Controller → FactoredProver` (the two are independent of each
other). Every `file:line` below was opened before use. `Compiler.lean` NOT edited (the `git status`
shows other lanes' modifications to `Compiler.lean`, `GOAL.md`, `README.md`, `native/*`, `prover/*`
and an untracked `Compiler/UwueavePreoProjectionV2.lean` — none of them mine).

## 0. Which existing theorem, exactly

The tree's FS theorem is `Selvage/FiatShamir.lean`'s keystone, proved unconditionally:
`fsKeystone_proved : FsOfRbrKeystone`, whose `sound` field is
```lean
def FsOfRbrSound : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (εrbr : ℝ → ℝ),
    (∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ) →
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z → ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) →
    FsStraightlineKnowledgeSoundness r Z (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ)
```
To instantiate it one needs a `Reduction` (Selvage/Rbr.lean) and a `RbrKnowledgeSoundness` instance —
a knowledge state function (Def 4.1) and per-round errors with the round bound proved (Def 4.2).
"The hash is a `def`" therefore meant: build the reduction and its RBR instance, and let the keystone
do the FS transform (`fiatShamir`, the lazy-sampling handler `Oracle`, the `(t + k)` union bound). No
new FS theorem, no axiomatized oracle.

## 1. `[CT-fiat-shamir-lanes]` — `Compiler/CommittedTerminalFiatShamir.lean`

**§1 `Ext6L` is finite, `readExt6` is a bijection.** `Fintype Ext6L` (six lanes are `Fin 6 →
BabyBear`), `card_ext6L : |Ext6L| = p^6`, `readExt6_bijective` from `readExt6_injective` + equal
cardinality, `uniformProb_read : uniformProb Ext6L (p ∘ readExt6) = uniformProb Ext6Q p`. Every lane
probability below is a field probability.

**§2 the protocol as a `Reduction`.**
```lean
noncomputable def gateReduction (hn : 0 < n) : Reduction where
  Idx := Unit; X := Root; A := BabyBear; X' := Unit; A' := Unit; W := Unit
  n := n; n' := 1; k := m + 1; PMsg := RoundMsg; Chal := Ext6L; δstar := 1 / (n : ℝ)
  R := fun _ rt y _ => commit y = rt ∧ descriptorHolds d (traceOf y);  R' := fun _ _ _ _ => True
  verify := fun _ rt y πs ρs => gateVerify commit d encNat rt y πs ρs
```
`k = m + 1` rounds: the gamma round (a junk zeroth prover message, then `γ = ρs 0`) and the `m`
sumcheck rounds. The word is the reduction's IMPLICIT INSTANCE `𝕪`, read in full (full-word
resolution); `verify` IS `check` at the challenges with the terminal recomputed from the word
(`gateVerify_some_iff : … = some _ ↔ commit y = rt ∧ roundsOk … ∧ laneChain … m = laneTerminal …`).
Target relation `True`, witness `Unit`: at full word nothing is handed on, knowledge soundness is
plain soundness. `δ* = 1/n` makes the paper's relaxation exact
(`relaxedMem_iff : δ ∈ (0, 1/n) → (RelaxedMem R δ () rt y w ↔ R () rt y w)`, from
`eq_of_fracHamming_lt`). `noncomputable` because `δstar : ℝ` — so the deployed decider is a separate
`def` reflected into `fiatShamir` (§4), the Controller's own idiom.

**§3 the knowledge state (Def 4.1)**, `gateKState`: `state δ st tr () := decide (commit st.y = st.x ∧
StageOk d encFor st.y tr.rounds)` with
```lean
def StageOk (y) : List (RoundMsg × Ext6L) → Prop
  | [] => descriptorHolds d (traceOf y)
  | (_, gamma) :: rest => roundsOkBelow (trOfRounds rest) rest.length ∧
      readExt6 (laneChain (trOfRounds rest) rest.length) = honestClaim d encFor y gamma (trOfRounds rest) rest.length
```
`honestClaim … i = residualSum (mle (gammaResidualTable …)) (read ∘ challenges) i` (REUSED). The
pending prover message is ignored (`prover_monotone` is `exact h`); `empty_iff` is `relaxedMem_iff`;
`full_iff` is `gateVerify_some_iff` through `residualSum_full` + `read_laneTerminal` (`stageOk_ofFull`).

**§4 RBR (Def 4.2)**, `gateRbr`, identity round extractor, `err i := if i = 0 then (N−1)/|F| else 1/|F|`:
* `stage_bad_zero`: the gamma round's bad event is the gamma event of `CommittedTerminalCompose` (a
  failing trace whose batched residual vanishes at the fresh `γ`) — `≤ (N−1)/|F|` by
  `gammaZero_prob_le` (REUSED) after `uniformProb_read`.
* `stage_bad_succ`: a sumcheck round's bad event — running claim false, pending message passes the
  Boolean check, fresh challenge lands where `readPoly1 π` meets the honest round polynomial
  `honestRound` (`roundPoly (mle table)`, REUSED) — is one root: `card_agreeFinset_lt` (REUSED) at
  degree `< 2`, so `≤ 1/|F|`. The bookkeeping lemmas (`trOfRounds_*`, `laneChain_append_le`,
  `roundsOkBelow_append_succ`, `residualSum_congr`, `read_challenge_append`, `honestClaim_succ`) are
  the transcript-list ↔ lane-transcript bridge.

**§5 the keystone instantiated — the statement, copied:**
```lean
noncomputable def gatePrice (d) (m) : ℝ :=
  0 + ((d.gates.length + d.zeros.length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q + (m : ℝ) * (1 / Fintype.card Ext6Q)

theorem gateProof_fs_sound (hEnc : ∀ wv k, encFor wv k = encNat k) (hn : 0 < n) :
    FsStraightlineKnowledgeSoundness (gateReduction commit d encNat hn) Set.univ
      (fun _s t _δ => ((t : ℝ) + ((m + 1 : ℕ) : ℝ)) * gatePrice d m) :=
  fsKeystone_proved.sound (gateReduction commit d encNat hn) (gateRbr commit d encNat encFor hEnc hn)
    Set.univ (fun _ => gatePrice d m) (fun _ _ => gatePrice_nonneg d) (fun i _ _ _ _ => gateErr_le_gatePrice d i)
```
Spelled out (`gateProof_fs_sound_reading`, `W = Unit`, `R' = True`, `Z = univ`, relaxation exact):
for every salt size, query budget `t`, `δ ∈ (0, 1/n)`, and `t`-query ROM adversary `P : SrProver`,
`Pr[¬(commit y = rt ∧ descriptorHolds d (traceOf y)) ∧ fiatShamir (gateReduction …) s (fsOracle o ρs) o ≠ none] ≤ (t + (m+1)) · gatePrice d m`
over the lazily-sampled coins. **What is and is not consumed:** the reduction consumes only
`S.commit`; the `BindingCommitment` premise is NAMED, and at full word its binding is not
load-bearing — the word is in the statement, so the FS query hashes the word itself. Binding becomes
load-bearing exactly when the word leaves the statement and only its root is hashed: the FS file's
`[FS-BCS]`, this lane's `[CT-merkle-profile]`. The ROM is the tree's inhabited lazy-sampling handler;
"the deployed cSHAKE realizes it" is `[FS-ROM]`.

**§6 the deployed oracle and the non-interactive controller.** The lane transcript as FS input:
`moveWire : SrMove (gateReduction …) 0 → List UInt8 × (List Nat × List (List Nat))` = (root bytes,
word limbs, prefix messages' limbs; salts empty at `s = 0`), through the tree's prefix-decodable
`StreamCodec` (`product bytesStream (product (list nat) (list (list nat)))`) —
**`encodeMove_injective`** (from `decodePrefix_encode`, given an injective root encoder).
`cshakeOracle := digestToExt6L ∘ fsHash.xofDigest "MINIDREGG/CT/FS/V1" ∘ encodeMove` with
`fsHash := Sp800185Cshake256.controller cshakeAlgorithmId digestCodecPin` (`fsHash_eq_backend : fsHash
= Tower256ConcreteBackend.cshake := rfl`; the backend's name is `noncomputable`, this one runs) and
`read_digestToExt6L : readExt6 (digestToExt6L dg) = Ext6GateProofController.digestToExt6 dg`. Then:
```lean
structure FsReceipt (Root) (n m) where root : Root; word : Fin n → BabyBear; messages : Fin (m+1) → RoundMsg; challenges : Fin (m+1) → Ext6L
def fsCheck (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rc : FsReceipt Root n m) : Except FsFailure (Receipt Root m)
  -- every carried challenge = O at its prefix (`challengesExact`, through the computable `prefixQuery`; `output_query_eq` ties it to `SrOutput.query`), then `check`
theorem fsCheck_ok_fiatShamir … (h : fsCheck … O rc = .ok r) : fiatShamir (gateReduction …) 0 O (rc.output …) = some ((), fun _ => ())
theorem fsCheck_refuses_mismatch … (h : ∃ i, rc.challenges i ≠ O ((rc.output …).query i)) : fsCheck … O rc = .error .challengeMismatch
```
**The honest prover's signature**, causal (stage `i+1` extends stage `i`; structural in the stage,
each message computed ONCE at the challenges already drawn — the `let` is load-bearing: the first
version returned closures that re-ran the prover at every access and the Stage-0 exhibit did not
finish in 11 minutes; with the stage forced once it is 2 minutes):
```lean
def fsProve (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root) (y : Fin n → BabyBear) : FsReceipt Root n m :=
  let st := fsStage commit d encNat hn O rt y m
  ⟨rt, y, fun i => st.1.getD i junkMsg, fun i => st.2.getD i ext6Zero⟩
theorem fsProve_challenge … (i) : (fsProve … O rt y).challenges i = O (((fsProve … O rt y).output …).query i)
theorem fsProve_message … (i : Fin m) : (fsProve … O rt y).messages i.succ = laneRound d (traceOf y) (gammaOf ρs) (roundsOf ρs) encNat i   -- via `laneRound_congr` (prefix-measurability of the lane prover, proved)
theorem fsProve_complete … (enc) (hEnc) (hd : descriptorHolds d (traceOf y)) : fsCheck … O (fsProve … O (commit y) y) = .ok ⟨commit y, γ, transcriptOf …, laneTerminal …⟩   -- `receipt_complete` REUSED
theorem fsProve_fiatShamir … : fiatShamir (gateReduction …) 0 O ((fsProve … O (commit y) y).output …) = some ((), fun _ => ())
```
plus `check_zero_of_holds`: a satisfying word's all-zero transcript is accepted at EVERY challenge
vector (`laneRound_of_holds`) — which is exactly why a wrong challenge is something only the FS binding
refuses.

**§7 ATLAS on the demo, kernel-decided** (`m = 5`, 23 residuals, `idealCommitment`): `fsCheck_complete_demo`
(the honest carried receipt accepted under the canonical oracle `oracleOfChallenges γ r` — answers by
prefix length, the computable shape of `fsOracle`); **falsifier** `fsCheck_refuses_forged_gamma_demo`
(`γ + 1` carried: `challengeMismatch`) beside `check_accepts_forged_gamma_demo` (`check` alone ACCEPTS
that transcript at `γ + 1`); **the `fiatShamir_teeth` shape** `fiatShamir_teeth_demo`: ONE proof
string (`teethOutput`: message 1 is `(1, −1)`, the rest zero) is `= none` under the oracle answering
`(γ, r)` and `= some _` under the oracle answering `(γ, r[0 ↦ 1/2])` — round 1 reads `0 = 1 − 2 r₀`.

## 2. `[CT-joint-price]` and `stage0Receipt_price`

The interactive ledger as ONE number over `(γ, r)`:
```lean
theorem gateProof_joint_price (hfail : ¬ descriptorHolds d wv) (P : Ext6Q → (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q) (hpm : ∀ γ, PrefixMeasurable (P γ)) (hdeg : … < 2) :
    uniformProb (Ext6Q × (Fin m → Ext6Q)) (fun c => (∑ b, gammaResidualTable d wv enc c.1 b) = 0 ∨
        AdaptiveAcceptsFalse (P c.1) (mleHonest (gammaResidualTable d wv enc c.1)) 0 (∑ b, gammaResidualTable d wv enc c.1 b) c.2) ≤
      (((descriptorResiduals d wv).length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q + (m : ℝ) * (1 / Fintype.card Ext6Q)
```
(`uniformProb_or_le`, the first coordinate through `Equiv.prodComm` + `uniformProb_prod_le`, the fibres
over `γ` by `sumcheck_prob_le` — all REUSED; the strategy may depend on `γ`.)

**The price theorem, statement copied:**
```lean
theorem stage0Receipt_price {Root Op : Type} [DecidableEq Root] (S : BindingCommitment Root BabyBear (Fin 4131) Op) :
    FsStraightlineKnowledgeSoundness (gateReduction S.commit evmAddDescriptor (bitCorner 13) (by norm_num)) Set.univ
      (fun _s t _δ => ((t : ℝ) + (13 + 1 : ℝ)) *
        ((0 : ℝ) + ((4148 - 1 : ℕ) : ℝ) / ((2013265921 : ℝ) ^ 6) + (13 : ℝ) * (1 / ((2013265921 : ℝ) ^ 6))))
theorem stage0Price_value :
    ((0 : ℚ) + ((4148 - 1 : ℕ) : ℚ) / ((2013265921 : ℚ) ^ 6) + (13 : ℚ) * (1 / ((2013265921 : ℚ) ^ 6))) = 4160 / 2013265921 ^ 6 ∧
      (4160 : ℚ) / 2013265921 ^ 6 < 1 / 2 ^ 173 := by norm_num
```
**The concrete number:** the non-interactive Stage-0 receipt's error is
`(t + 14) · 4160 / 2013265921^6`, i.e. `(t + 14) · 4160 / 66,589,668,549,341,940,845,377,978,930,048,497,497,013,284,102,492,651,521`
≈ `(t + 14) · 6.25 · 10^-53` (`log₂ ≈ −173.42`; kernel-checked through `norm_num`), below `(t + 14) · 2^-173`, for a `t`-query adversary. Every term:
the FS factor `(t + k)` with `k = 13 + 1` (`fsKeystone_proved`), the terminal `0` under the named `S`,
the gamma event `(N − 1)/|F|` at `N = 4,148` (`3,298 + 850`, `evmAddDescriptor_shape`), the sumcheck
`m/|F|` at `m = 13` (sharp, degree one), `|F| = p^6`, `p = 2^31 − 2^27 + 1`. **Honest label: this is
the FULL-WORD price** — the verifier reads the whole 4,131-wire word; `[CT-sampled]` and
`[CT-merkle-profile]` are NOT in it; `[FS-ROM]` is the modeling step; `S`'s binding is named, not
consumed (§1 §5).

## 3. `[CT-factored-prover]` — `Compiler/CommittedTerminalFactoredProver.lean`

**The prover.** Under `bitCorner` residual `k` sits at corner `k`, so the `A`, `B`, `C` tables are the
payload lists padded with zeros to `2^m` (`tableA/B/C`, payloads gate by gate: mul `(γ^k a, b, γ^k
out)`, add `(0, 0, γ^k (out − a − b))`, root pin `(0, 0, −γ^{|gates|+j} z)` — `mulAGamma`, `mulB`,
`combinedC`). Round `i` folds the current least significant coordinate (`fold r : (x₀,x₁) ↦ (1−r)x₀
+ r x₁`) and its message is ONE walk over the paired tables: `(g(0), g(1), cross) = (Σ (a₀b₀−c₀),
Σ (a₁b₁−c₁), Σ (a₁−a₀)(b₁−b₀))` — `quadRoundPoly`'s three numbers. `O(2^{m+1})` in all; at Stage 0
`8,192 ≈ 2N` (the sparse pairwise alternative the compose note sized is `O(N·2^{m−i})` without a
hash-map grouping; the dense fold is what every BaseFold verifier already trusts).
```lean
def honestMessages (d) (wv) (gamma : Ext6L) (r : Fin m → Ext6L) : List RoundMsg2      -- RoundMsg2 := Ext6L × Ext6L × Ext6L
def honestTranscript2 (d) (wv) (gamma) (r) : Transcript2 m := let msgs := honestMessages d wv gamma r; ⟨fun i => msgs.getD i zeroMsg2, r⟩
def check7 (commit) (d) (encNat) (gamma) (rt : Root) (op : Opening7 n) (tr : Transcript2 m) : Except Failure (Receipt7 Root m)
  -- realize7 → every round's g(0)+g(1) = claim on the zero-anchored chain (`laneEval2` evaluates the quadratic) → closes at `laneTerminalExpression v`
```
**Closed:** `readPoly2 (g0, g1, ct) = C ct·X² + C (g1−g0−ct)·X + C g0` (exactly `quadRoundPoly`'s
shape, degree `< 3`); `check7_accepts : … = .ok rc → GateProof7Accepts …` (the degree/rounds/closing
clauses of `Ext6GateProofController.Accepts`, the seven realized); **`gammaBatched_eq_sum_table :
gammaBatchedDescriptorResidual d wv γ = ∑ b, gammaResidualTable d wv enc γ b`** (the residual list
reindexed over gates then root pins — the two protocols' zero claims are the SAME event, so the gamma
leg is priced by the existing `gammaZero_prob_le`); **`gateProof7_sound`** (accepted against `S.commit
w` ⇒ `descriptorHolds ∨ gammaZero ∨ AdaptiveAcceptsFalse P (quadHonest A B C) 0 (Σ (A·B−C))`, via
`realize7_sound` + `factored7_closes`); `sumcheck7_prob_le = quad_sumcheck_soundness` (`m·2/|F|`);
`receipt7_refuses_tamper`.

**Named, not closed — `[CT-factored-prover-honest]`**, as a `Prop` with its consumer proved:
```lean
def FactoredProverHonest : Prop := ∀ m d wv (hfit : d.gates.length + d.zeros.length ≤ 2 ^ m) gamma r (i : Fin m),
    readPoly2 ((honestTranscript2 d wv gamma r).message i) = factoredRounds d wv (residualEmbedding d wv hfit) (readExt6 gamma) (chalOf fun q => readExt6 (r q)) i.val
theorem factoredProver_complete_of_honest (H : FactoredProverHonest) (w) (hfit) (hd : descriptorHolds d (traceOf w)) :
    check7 commit d (bitCorner m) gamma (commit w) ⟨w, laneTerminal7 …⟩ (honestTranscript2 d (traceOf w) gamma r) = .ok ⟨commit w, gamma, honestTranscript2 …, laneTerminal7 …⟩
```
The identity is the fold lemma ("`fold` at `r_i` of the level-`i` tables is the level-`(i+1)`
restriction of the MLEs", `mle_multilinear` coordinate by coordinate) plus the corner reading of the
padded payload lists (`sparseTable_read` at `bitCorner`); its ATLAS fields: satisfiable — its
CONSEQUENCE is kernel-decided on the demo (`check7_complete_demo`: the fold prover's five degree-two
messages and the pinned `demoSeven` pass `check7`; the kernel built the three 32-entry tables, folded
five times, walked the pairs, realized the seven) and compiled at Stage 0; teeth —
`check7_refuses_tampered_message_demo` (message 2's `g(0)` shifted: `roundCheck`),
`check7_refuses_tamper_demo` (root), `check7_refuses_zero_transcript_demo` (the zero transcript closes
at `0 ≠ laneTerminalExpression demoSeven`: `terminalMismatch`); premise-inhabitation — `hfit` at the
demo and Stage 0. Label: *the factored prover exists and its receipts are accepted at Stage 0 and on
the demo; its general completeness is one named identity away* (est. ~250 lines of index bookkeeping:
`Fin (2^{m−i}) ≃ SuffixCube m i` through `Nat.testBit`, `fold_getD`, `padTo` corner reading).

## 4. Exhibits on Stage 0 (`m = 13`, `N = 4,148`, 4,131 wires, `idealCommitment`), compiled `#eval`, throw-teeth

`CommittedTerminalFiatShamir.Stage0Exhibit` (2:12 wall for the whole file; the four lines):
```
stage0 fs: honest (1, 2) non-interactive receipt accepted: gamma and 13 challenges derived by cSHAKE256 from the transcript prefixes, 13 rounds, terminal 0
stage0 fs: derived gamma { c0 := 1858020117, c1 := 1303728375, c2 := 835584048, c3 := 232863351, c4 := 1874699069, c5 := 216193432 }, derived r_0 { c0 := 213792517, … }
stage0 fs: receipt with one challenge not the hash of its prefix refused (challengeMismatch)
stage0 fs: forged word's own FS proof at its own root refused at a round check (zero claim false at its derived gamma)
```
Read exactly: the Stage-0 proof receipt is now NON-INTERACTIVE — `γ` and the thirteen challenges are
cSHAKE256 digests of the transcript prefixes (word, root, messages so far; 14 hashes per prover run, 14
per verification, ~40 KB each under the ideal root), the honest messages computed causally, the whole
thing decided by `fsCheck` (reflected into `fiatShamir` by `fsCheck_ok_fiatShamir`); a receipt with one
challenge altered is refused before any arithmetic; the forged `Z = 4` word's own honest FS run is
refused at round 0 (the gamma event did not occur at its derived `γ` — the exhibit throws if it does).

`CommittedTerminalFactoredProver.Stage0Exhibit` (2:07 wall):
```
stage0 factored prover: honest (1, 2) factored proof accepted end to end: 13 degree-two rounds, closing at the seven realized terminals
stage0 factored prover: message 0 = (0, 0, { c0 := 924368535, c1 := 348301510, c2 := 1045160160, c3 := 145736792, c4 := 545915310, c5 := 362173153 })
stage0 factored prover: forged word refused at the honest root
stage0 factored prover: forged word at its own root, its own honest factored prover refused at a round check (zero claim false)
```
(`g(0) = g(1) = 0` with a NONZERO cross term on the satisfying trace — the factored expression is not
the single terminal, `factored7_ne_single`, seen in the round messages too.)

## 5. Elaboration status, pins

Single-file `lake env lean`, `pgrep -f "lake build"` empty before each; targeted
`lake build Compiler.CommittedTerminalFiatShamir Compiler.CommittedTerminalFactoredProver` run once at
the end (never the umbrella). `scripts/check-import-boundary.sh`: `OK: Theory`, `OK: Selvage`.

| file | exit | errors | wall | `#guard_msgs … #print axioms` pins (all `[propext, Classical.choice, Quot.sound]`) |
|---|---|---|---|---|
| `CommittedTerminalFiatShamir.lean` | 0 | 0 | 2:12 | `gateProof_fs_sound`, `gateProof_fs_sound_reading`, `stage_bad_zero`, `stage_bad_succ`, `gateProof_joint_price`, `Stage0.stage0Receipt_price`, `Stage0.stage0Price_value`, `fsCheck_ok_fiatShamir`, `fsProve_complete`, `fsProve_fiatShamir`, `encodeMove_injective`, `DemoInstance.fsCheck_complete_demo`, `…fsCheck_refuses_forged_gamma_demo`, `…check_accepts_forged_gamma_demo`, `…fiatShamir_teeth_demo` |
| `CommittedTerminalFactoredProver.lean` | 0 | 0 | 2:07 | `check7_accepts`, `gammaBatched_eq_sum_table`, `gateProof7_sound`, `sumcheck7_prob_le`, `factoredProver_complete_of_honest`, `DemoInstance.check7_complete_demo`, `…check7_refuses_tampered_message_demo`, `…check7_refuses_tamper_demo`, `…check7_refuses_zero_transcript_demo` |

No `sorry`, no `axiom`, no `native_decide`, no `#guard` (grep count 0 each, `#guard_msgs` excluded).
Nothing under `Theory/`, `Selvage/`, `Assurance/`, `prover/`, `Kernel/`, `Pred/`, `docs/`, `LICENSE*`,
`NOTICE`, nor `Compiler.lean`, `Selvage.lean`, `GateMleExt6.lean`, `Ext6GateProofController.lean`, the
four `CommittedTerminal*.lean` files, touched.

## 6. Closed vs named

| item | status |
|---|---|
| `[CT-fiat-shamir-lanes]` | **closed**: `gateReduction`, `gateKState`, `gateRbr`, `gateProof_fs_sound` (an instance of `fsKeystone_proved.sound`), the deployed oracle, `fsCheck`/`fsProve` with completeness and reflection, demo decided, Stage 0 compiled |
| `[CT-joint-price]` | **closed**: `gateProof_joint_price`; `stage0Receipt_price` + `stage0Price_value` (`4160 / p^6 < 2^-173` per `(t + 14)`) |
| `[CT-factored-prover]` | **prover, controller, reflection, ledger, price closed**; general completeness reduced to `[CT-factored-prover-honest]` (`FactoredProverHonest`, a `Prop`, consumer `factoredProver_complete_of_honest` proved, consequence decided on the demo and compiled at Stage 0) |
| `[FS-ROM]` | the one named idealization, inherited from Selvage/FiatShamir.lean — the cSHAKE oracle is a `def`, the theory names only `Oracle` |
| `[FS-BCS]` / `[CT-merkle-profile]`, `[CT-sampled]` | unchanged; the word leaving the hashed statement is where `S`'s binding starts to be consumed |
| `[CT-umbrella]` | the coordinator's two import lines in `Compiler.lean` (not edited) |

## 7. Lessons

* **`Reduction` values never compile.** `δstar : ℝ` makes every `Reduction` `noncomputable`; and
  `SrOutput.query` reads `r.k` at runtime, so a computable checker must enumerate `Fin (m + 1)` itself
  (`prefixQuery`) and prove `output_query_eq` on the side. The theory object and the deployed decider
  are two definitions joined by a reflection theorem — the Controller's `check_accepts` idiom again.
* **Closures over a prover re-run the prover.** `fun i => (fsStage … m).1.getD i` recomputes the
  whole causal schedule per access; `fsCheck` and `laneChain` make ~100 accesses. A `let` in the
  receipt constructor fixed an 11-minute non-termination into 2 minutes.
* **`rw` matches binder types syntactically.** `fun i : Fin (m+1) => …` and `fun i : Fin r.k => …`
  are defeq but `rw` (instances transparency) will not see it; `congrArg`/`show`/`Iff.trans` will.
  Likewise `rw` closes goals only at reducible transparency — `openingOf`, `transcriptOf` need an
  explicit `rfl`.
* **Untyped binders over `Fin` lists get monad-coerced.** `fun j => msgs.getD j d` with `j` expected
  in `Fin (m+1)` made Lean coerce the whole `List (Fin (m+1))` into `List ℕ` through `List`'s monad
  (`do let a ← l; pure ↑a`) — silent, and every downstream lemma then fails. Annotate the binder.
* **The two protocols share their zero claim.** `gammaBatched_eq_sum_table` is 40 lines of
  reindexing and it means the factored protocol's gamma leg needs no new counting.
