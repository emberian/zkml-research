# CommittedTerminal realizer — the Stage-0 time-to-proof blocker, first slice

**2026-09-05. Lane on `/Users/ember/dev/minidregg` branch `main` (HEAD `c85b521`).** Nothing
committed, no stash, no `add -A`. One new file: `Compiler/CommittedTerminalRealizer.lean`
(743 lines). No other file touched (`Compiler.lean` NOT edited — the module is standalone;
the coordinator decides whether it enters the umbrella). Every `file:line` below was opened
before use.

## 0. The blocker, quoted, and what the scout listed

`descriptor-reader-scout.md` "The blocker, named": *"`Compiler/GateMleExt6.lean:246
CommittedTerminal` has no realizer, and the controller that would consume one is
`noncomputable`. Until a Lean-owned BabyBear/Ext6 PCS controller exists (§3(c): ~1.8K Lean +
~0.5K opaque Rust + the listed reductions), 'Stage-0 time-to-proof' on the derived path is not a
measurement anyone can take."* The scout's §3(c) list of reductions, quoted: *"plus the
reductions `PROJECT.md` lists as residual (PCS, subfield, proximity, binding, ROM, sampling-bias,
final LDT)"* — and `PROJECT.md:282`'s BabyBear/Ext6 row, verbatim: *"PCS, subfield proof,
proximity, binding, ROM, sampling-bias price, final LDT, recursion, deployed security; the
registry adds no reduction."* `PROJECT.md:367` "Ordered frontier" item 3: *"Instantiate concrete
Ext6 PCS/subfield/proximity/final-LDT reductions inside the landed controller and extensible
global ledger."*

## 1. Scout: what `CommittedTerminal` demands

Copied from `Compiler/GateMleExt6.lean:243-251`:

```lean
/-- An authenticated succinct terminal.  The forthcoming Mobius/FRI assembly
constructs this record by opening its factored selector commitments.  This
module assumes only the resulting equality to the exact clear-table MLE. -/
structure CommittedTerminal
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) where
  value : Ext6Q
  factoredSelectorOpening :
    value = mle (gammaResidualTable d wv enc gamma) r
```

and its one consumer, `:255 honestRounds_closes_committed`: given `descriptorHolds d wv` and an
`opened : CommittedTerminal …`, `scChain 0 (honestRounds …) (chalOf r) m = opened.value`.

**The vacuous pole, named so nobody ships it:** `⟨mle (gammaResidualTable d wv enc gamma) r, rfl⟩`
inhabits the record for every `wv`. The record's *type* carries no succinctness and no
authentication; both live in the *decision* that produces `value` from a root and an opening,
and in the theorem that the decision's output equals the MLE at the *committed* trace.

`grep -rn CommittedTerminal` over the tree: the definition, `honestRounds_closes_committed`, and
its `#print axioms` pin — three hits, all in `GateMleExt6.lean`. The controller
(`Ext6GateProofController.lean`) never names it: its receipt carries `terminalValue : Fin 7 -> Ext6Q`
(`:222`) for the SEVEN factored terminals of `GateFactoredExt6` plus opaque
`traceOpeningProof`/`operandOpeningProof`/`finalLdtProof` bytes (`:225-227`); `Accepts` (`:323`)
checks the sumcheck chain closes against `terminalExpression receipt.terminalValue` and the eta
aggregate, and takes the seven values on faith. The whole controller sits in
`noncomputable section` (`:44`) because `Ext6Q := AdjoinRoot ext6Polynomial`
(`Ext6Conformance.lean:252`).

### Instantiation table

| field / premise | what it demands | existing object | status |
|---|---|---|---|
| `d`, `wv`, `enc` | emitted descriptor, total trace, cube embedding | `demoDescriptor` (`EmitSerialize.lean:177`, 18 gates + 5 roots = 23 residuals); `evmAddDescriptor` (`EvmAddAir.lean:304`, 3,298 + 850 = 4,148); traces from `DescriptorEval.fillAux` (`:101`), `evmAddCandidate` (`:302`) | present; `Statement.encoding` of the controller is `noncomputable` (`Ext6GateProofDeployment.lean:163 demoEncoding` via `Fintype.equivFin`) — **a computable embedding did not exist** → `bitEmbedding`/`residualEmbedding` (new, `Nat.testBit`) |
| `gamma`, `r` | Ext6 challenge and point | only `Ext6Q` (noncomputable); lanes `Fin 6 → BabyBear` with `ext6Mul` + `ext6Mul_correct` (`Ext6Conformance.lean:265/:307`) | mult present; **add/sub/one/zero/pow + transport lemmas did not exist** → §1 of the file |
| `value` | an Ext6 element | `mle` (`Selvage/MultilinearExtension.lean:116`, a `Finset.sum` over `Fin m → Bool`, noncomputable at `Ext6Q`) | **no computable evaluator existed** → `laneTerminal` (sparse, over the residual list) |
| `factoredSelectorOpening` | `value = mle (gammaResidualTable …) r` | `gammaResidualTable_read` (`:162`), `sum_ite_enc` (`AirSumcheckQuadratic.lean:201`) | proved via **new** `mle_gammaResidualTable_sparse` + `read_laneTerminal` |
| the root and its binding (PCS premise) | root pins `wv` | `BindingCommitment` / `commit_injective` (`Selvage/Commitment.lean:122/:161`); `idealCommitment` (`:209`, built); `BinaryMerkle.openingScheme` + `positionBinding_of_collisionFree` (`Selvage/BinaryMerkle.lean:134/:286`) | interface present; **deployed BabyBear-leaf hash profile absent** (`BaseFoldPoseidon2.hashLeaf` is over `Ext4` and `noncomputable`; `Tower256ConcreteBackend.cshake` is `noncomputable`, `:488`) |
| sampled queries | `t` columns + Merkle paths | `basefoldTableVerify` (`BaseFoldRbrTable.lean:206`), `extractTable` (`:138`, needs `2^m ≤ t`) | statement present; **extractor only in the unique-decoding regime** |

### The resolution decision: full word, and why

The realizer is at **full-word resolution** — the verifier reads the whole committed trace
(the checker lane's `[MATMUL-pcs]` scope, `Assurance/ZkmlMatmulSuccinctChecker.lean` header;
`Selvage/BaseFoldIor.lean` header: *"This is deliberately the full-word IOR resolution"*).
Reason: the tree's only extractor with a proof, `BaseFoldRbrTable.extractTable`, is *"the
unique-decoding-regime extractor: it needs `2^m ≤ t` opened columns at distinct positions … At
deployed parameters `t ≪ 2^m`, so THIS extractor does not run there; the lift to `t < 2^m` is the
list-decoding seam `[ERASURE-list]` / `[OOD-pin-proximity]`"* (file header, quoted). A sampled
realizer today would therefore be a verifier whose soundness premise is not in the tree — a
`class`-shaped assumption, law 1. At full word: the terminal step draws no challenge; its error is
**zero** given binding; the price is exactly the binding event the `BindingCommitment` carries
(`[COMMIT-CR]`). **Soundness regime, named:** deterministic/erasure-free at the terminal; the
sumcheck leg keeps `m · 2/|F|` per `basefoldSumcheckRbr` (`Selvage/BaseFoldRbr.lean:82`), and
the batching-over-gamma price is the named residual `[CT-compose]` (§4).

What "full word" costs: verifier work linear in the trace (4,131 words for Stage 0) and in the
residual count (4,148) — not `2^m`. That is the honest first measurement of Stage-0 time-to-proof
on the derived path: *terminal authenticated at full-word resolution; succinctness deferred to
`[CT-sampled]`*.

## 2. What was built (`Compiler/CommittedTerminalRealizer.lean`)

Imports: `Compiler.GateMleExt6`, `Compiler.DescriptorEval`, `Selvage.Commitment`,
`Selvage.BinaryMerkle`. Boundary script green (Compiler may import anything; nothing under
`Theory/`/`Selvage/` touched).

**§1 lane carrier** — `structure Ext6L (c0 … c5 : BabyBear)` — STRICT, not `Fin 6 → BabyBear`
(see §5 for why); `Ext6L.toFn`/`ofFn` (`toFn_ofFn` by `fin_cases`), `readExt6 := toExt6 ∘ toFn`
(noncomputable — it lands in `Ext6Q`); `ext6Zero/One/OfBase/Add/Sub`, `ext6MulL a b :=
ofFn (ext6Mul a.toFn b.toFn)` (the tree's multiplication, materialized), `ext6Pow`;
`read_zero/one/ofBase/add/sub/mul/pow` (`read_mul` is `ext6Mul_correct` transported). No ring
instance: `Ext6L` is a representation, not a second field.

**§2 sparse terminal** — `laneChi` (lane `chiEval`), `laneTerminalGo` (running gamma power),
`laneTerminal gamma r encNat res := Σ_k gamma^k · res_k · chi_{encNat k}(r)` over the residual
list; bridge `read_laneTerminalGo` (invariant over `Finset.range`, `getD` reads).

**§3 the identity** —
```lean
theorem mle_gammaResidualTable_sparse (d wv enc gamma r) :
    mle (gammaResidualTable d wv enc gamma) r =
      ∑ k : Fin (descriptorResiduals d wv).length,
        gamma ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k) *
          chiEval (enc k) r
theorem read_laneTerminal (d wv enc encNat) (hEnc : ∀ k, enc k = encNat k) (gamma r) :
    readExt6 (laneTerminal gamma r encNat (descriptorResiduals d wv)) =
      mle (gammaResidualTable d wv enc (readExt6 gamma)) (fun i => readExt6 (r i))
```
(the padded cube contributes nothing; injectivity of `enc` collapses mask × lift to one term per
residual — `sum_ite_enc` reused.)

**§4 cube encoding** — `bitCorner m k := fun i => k.testBit i`; `bitEmbedding N m (h : N ≤ 2^m)`;
`residualEmbedding d wv h` at the exact `Fin (descriptorResiduals d wv).length` type.

**§5 the realizer's signature and what is decided** —
```lean
structure Opening (n : Nat) where
  word : Fin n → BabyBear      -- the whole committed trace
  value : Ext6L                -- the claimed terminal
inductive Failure | rootMismatch | valueMismatch

def realize {Root} [DecidableEq Root] {n m} (commit : (Fin n → BabyBear) → Root)
    (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool))
    (gamma : Ext6L) (r : Fin m → Ext6L) (rt : Root) (op : Opening n) : Except Failure Ext6L :=
  if commit op.word ≠ rt then .error .rootMismatch
  else if laneTerminal gamma r encNat (descriptorResiduals d (traceOf op.word)) ≠ op.value then
    .error .valueMismatch
  else .ok op.value
```
Decided: (i) the opened word recommits to the statement's root; (ii) the recomputed sparse
terminal equals the claim. NOT decided (deliberately): whether the trace satisfies the
descriptor — the realizer *authenticates* a terminal, `honestRounds`/the sumcheck judge it.

Theorems: `realize_ok_iff`, `realize_complete` (general, any word), `realize_wrong_value_refused`,
`realize_wrong_root_refused`, `realize_value_eq`, and

```lean
noncomputable def committedTerminal … (h : realize commit d encNat gamma r rt op = .ok v) (enc) (hEnc) :
    CommittedTerminal d (traceOf op.word) enc (readExt6 gamma) (fun i => readExt6 (r i))
```
(`noncomputable` because the RECORD's `value : Ext6Q` is; the decision is computable.)

**§6 soundness with the named premise** —
```lean
theorem realize_sound (S : BindingCommitment Root BabyBear (Fin n) Op) (d encNat gamma r)
    (w : Fin n → BabyBear) (op : Opening n) (v : Ext6L)
    (h : realize S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) :
    readExt6 v = mle (gammaResidualTable d (traceOf w) enc (readExt6 gamma)) (fun i => readExt6 (r i))
```
The PCS premise is the `BindingCommitment` instance `S` (the tree's interface); the only property
consumed is `S.commit_injective`. Then `committedTerminalOfBinding : CommittedTerminal d (traceOf w) …`
at the **committed** trace, and

```lean
theorem honestRounds_closes_realized … (hd : descriptorHolds d (traceOf w)) :
    scChain 0 (honestRounds d (traceOf w) enc (readExt6 gamma) (chalOf …)) (chalOf …) m = readExt6 v
```
= `honestRounds_closes_committed` at this realizer. Also `realize_other_word_refused` (binding ⇒
any other word is refused at the root before arithmetic).

**§7 generic Merkle instance** — `realizeMerkle H d encNat gamma r rt op := realize
(BinaryMerkle.openingScheme H k).commit …` over `Fin (2^k)`; `merkleBinding (hfree : ¬ Collision H)
: BindingCommitment …` via `positionBinding_of_collisionFree` (reused); `realizeMerkle_sound` =
`realize_sound` at it. Premise inhabitation: `identitySuite : HashSuite BabyBear IdTree` (the
digest IS the tree; `identitySuite_collisionFree` by constructor injectivity, **axiom-free**) —
the Merkle analogue of `idealCommitment`, succinctness-free, never the deployment. The computable
BabyBear-leaf `HashSuite` is `[CT-merkle-profile]`.

**§8 ATLAS fields, all `decide +kernel` over `demoDescriptor` at `idealCommitment BabyBear (Fin 23)`,
`m = 5`, `gamma = ![3,1,4,1,5,9]`, `r i = ![i+2,7,1,8,2,8]`:**
- `demoWord_holds` — the evaluator-filled trace satisfies the descriptor (kernel ran `fillAux`);
- `demo_honest_terminal_zero` — its terminal is `0` (all residuals zero), computed;
- `realizer_complete` — honest opening accepted, `= .ok ext6Zero` (**satisfiable**);
- `realizer_refuses_forged_opening` — claim off by one → `.error .valueMismatch` (**teeth**);
- `realizer_refuses_forged_word` — aux wire 5 changed under the honest root → `.error .rootMismatch` (**teeth**);
- `tamperedWord_fails` and `demo_tampered_terminal` — the tampered trace violates the descriptor and
  its terminal is **nonzero** (the kernel ran 23 residuals × 5 chi factors of lane arithmetic; the
  realizer is not short-circuited by a zero table).
- premise inhabitation: `idealCommitment` is a built `BindingCommitment`; `merkleBinding` at
  `identitySuite`, and through it `realizerMerkle_complete` / `realizerMerkle_refuses_forged_word`
  decided on the 32-leaf cube (`demoWord32`, `cubeRoot` recomputed by the kernel;
  `merkle_premise_inhabited`).

**§9 Stage-0 exhibit (compiled `#eval`, build-failing teeth, Lane-A idiom)** — ONE exhibit,
two 4,131-wire fills: `evmAddCandidate 1 2` through `realize` at `idealCommitment BabyBear
(Fin 4131)`, `m = 13`, `gamma = ⟨2,7,1,8,2,8⟩`, `r i = ⟨31i+1, 41,59,26,53,58⟩` → **accepted,
terminal 0**; the forged claim `evmAddClaimed 1 2 4` → **refused at the honest root**
(`rootMismatch`) and **authenticated at its own root with the nonzero terminal**
`⟨914111166, 217269891, 1532956607, 75433114, 1735558900, 2002550831⟩` — the sparse terminal ran
over 4,148 residuals × 13 chi factors; the realizer authenticates, `descriptorHoldsCheck` judges.
Printed by the elaboration (§5), not pinned as a theorem: the kernel cannot decide `m = 13`.

Axiom pins (`#guard_msgs`): `read_laneTerminal`, `realize_sound`, `honestRounds_closes_realized`,
`DemoInstance.realizer_complete`, `…refuses_forged_opening`, `…refuses_forged_word`,
`…demo_tampered_terminal`, `realizeMerkle_sound`, `…realizerMerkle_complete`,
`…realizerMerkle_refuses_forged_word` → `[propext, Classical.choice, Quot.sound]`;
`identitySuite_collisionFree` → no axioms.
No `sorry`, no axiom, no `#guard`, no `native_decide`.

## 3. The controller's consumption: the exact obstruction

`Ext6GateProofController.Accepts` (`:323-336`) does not consume `CommittedTerminal`; it consumes
`receipt.terminalValue : Fin 7 → Ext6Q` — the seven factored terminals
(`GateFactoredExt6.lean:627 terminalOrder`, `:545 LinearFunctionalOpening`, `:550 TerminalOpenings`)
— and the eta aggregate over `TraceAffineFunctional`s (`:453`, whose `weights : Nat →₀ Ext6Q` is
`Finsupp`, noncomputable). Making the controller computable *at this instance* is therefore not a
plug-in of `realize`; it is:

1. `[CT-controller-lanes]` — a lane-carried `Receipt` (`gamma`, `roundChallenge`, `terminalValue`,
   `eta`, `aggregateValue` in `Ext6L`; `roundMessage` as coefficient triples, the
   `ZkmlMatmulSuccinctChecker.RoundMessage` idiom), a computable `check`, and `check_iff` proved
   through `readExt6` injectivity (`Module.finrank BabyBear Ext6Q = 6`, `ext6Q_finrank`, gives the
   power basis; the injectivity lemma is ~40 lines). The `Verifier` structure (`:339`) already
   anticipates exactly this: *"The Boolean checker may be emitted later; its theorem is the only
   semantics it has."* ~400 lines, touching `Ext6GateProofDeployment` (the `countableCodec Ext6Q`
   codecs, `:120-127`, are proof-side enumerations that must become lane codecs under new pins).
2. `[CT-factored7]` — the seven terminals are sparse sums of the same shape as `laneTerminal`
   (`operandTable`/`sparseTable`, `GateFactoredExt6.lean:77/:132`), so the realizer generalizes to
   `Fin 7 → Ext6L` from one opened trace (~150 lines); it replaces the opaque
   `traceOpeningProof`/`operandOpeningProof` bytes with the full word.

Neither touches `GateMleExt6.lean` (unchanged: `CommittedTerminal` is inhabited from outside, as
its docstring anticipated).

## 4. What remains, sized

| obligation | shape | size |
|---|---|---|
| `[CT-sampled]` | `basefoldTableVerify` over lanes with `t` Merkle-opened columns; extractor needs `[ERASURE-list]` (list decoding) for `t < 2^m` | ~250 lines verifier; the list-decoding seam is Selvage's, unsized here |
| `[CT-factored7]` | seven lane terminals from one opened trace | ~150 |
| `[CT-controller-lanes]` | lane receipt + computable `check` + `check_iff`; lane codecs | ~400 |
| `[CT-merkle-profile]` | computable BabyBear-leaf `HashSuite` (Poseidon2 `hashNode` is computable; leaf packing is a profile decision) + `[COMMIT-CR]` price | ~120 + the CR game |
| `[CT-compose]` | gamma-batching: failing trace ⇒ `Σ_k γ^k res_k ≠ 0` except ≤ `(N-1)/|Ext6Q|` of γ; compose with `adaptive_sumcheck_soundness` (`SumcheckReduction.lean:296`) at `d = 1` | ~150 |
| Rust | none needed for full word — Lean runs it; the `~0.5K opaque Rust` of the scout is the sampled/FRI fold+Merkle kernels of `[CT-sampled]` | 0 tonight |

Total to the scout's "~1.8K Lean": this lane lands 743 of it (the carrier, the identity, the
realizer, the closing theorem, the ATLAS instance); ≈ 1.1K remains, itemized above.

## 5. Elaboration status and file list

`lake env lean Compiler/CommittedTerminalRealizer.lean`: **exit 0, zero errors, zero warnings,
18.5 s** (laptop, single file, `pgrep -f "lake build"` empty before each run — no targeted
`lake build` was needed; the umbrella was never run). All ten `#guard_msgs` axiom pins matched.
`scripts/check-import-boundary.sh`: OK/OK. `grep -c "sorry\|native_decide\|#guard "` on the
file: 0. The Stage-0 `#eval` printed its three lines (§2 §9) inside that 18.5 s — both 4,131-wire
fills and the `m = 13` terminal — so "Stage-0 time-to-proof" at full-word resolution on the
derived path is, for the terminal leg, **seconds in the Lean interpreter**, label: *terminal
authenticated at full word, sumcheck leg not yet run through a computable controller
(`[CT-controller-lanes]`)*.

**A lesson paid for in one 12-minute, 5 GB run.** `ext6Mul a b` returns a lazy
`Fin 6 → BabyBear` closure (`| 0 => … | 5 => …`); a `laneProd` nest of depth `m` re-evaluates
inner lanes `6^m` times — `6^13 ≈ 1.3·10¹⁰` per chi factor in the interpreter. The kernel had
decided the `m = 5` instance in seconds (`6^5`), which hid it. The strict `structure Ext6L` with
`ofFn` materializing each product is the fix; everything else is unchanged. Anyone building
`[CT-controller-lanes]` on `Fin 6 → BabyBear` closures will hit this again.

**Files.** New: `/Users/ember/dev/minidregg/Compiler/CommittedTerminalRealizer.lean` (743 lines,
untracked, NOT committed); this note. Not touched: `Compiler.lean` (the module is not in the
umbrella; the coordinator adds `import Compiler.CommittedTerminalRealizer` after
`import Compiler.DescriptorEval` if it should be), `Compiler/GateMleExt6.lean` (unchanged —
`CommittedTerminal` is inhabited from outside, exactly as its docstring anticipated),
`Selvage/**`, `Assurance/**`, `prover/**`, `LICENSE*`, `NOTICE`, `docs/**`, any
`Theory/Kernel/Pred` file. The pre-existing working-tree modifications (`Compiler.lean`, `GOAL.md`,
`README.md`, `prover/**`, `native/**`, and the other lanes' untracked files) were present at
session start and are not mine.
