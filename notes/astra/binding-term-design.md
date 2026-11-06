# Computational binding term: patch and limits

[READ] This patch is against minidregg commit `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`; exact file SHA-256 baselines are in `binding/baseline.json`. The companion tree was not edited. The patch preserves the ideal API and adds computational consumers; it does **not** claim to migrate every existing perfect-binding theorem or to certify deployed hash parameters.

## The repair

[READ] The current tree already refutes compressing `BindingCommitment` instances (`Selvage/Commitment.lean:179–195`) and already has a concrete AuthMap forgery-to-collision route (`Selvage/AuthMapCommitment.lean:97–145`, `:208–260`). Yesterday's description of an entirely unrepaired binding layer is stale. The remaining errors include misleading older prose in `Commitment` and `CollisionResistanceROM`, absence of a shared computational budget interface, and the distinction between global binding advantage and conditional per-history audit error.

[DERIVED] The correct object is an **experiment and a bounded output event**. It is not `PositionBinding` equipped with an error number. For a fixed compressing hash, global injectivity is false; no negligible advantage theorem makes it true. A fixed known hash plus a class of all hardwired-output adversaries also permits a precomputed collision: resource counters do not exclude that by themselves. A cryptographic instantiation must specify sampled setup/hash family, adversary uniformity/advice, oracle access and machine resource semantics. The new interface permits sampled setup through `bad : Ω → Result → Prop` and `commit : Ω → Subject → Digest`; the caller must instantiate those semantics honestly.

[DERIVED] New `Selvage.BindingGame` defines a fixed interpreter `Experiment` with `run`, `queries`, and `steps`, then `Within`, adversary-specific `advantage`, and `SecureAt`. Security APIs require a nonempty finite sample space; `prob_true` verifies normalization. Counters are properties of the interpreter fixed before the security claim, not attacker-supplied cost declarations. This finite model can include all randomness in Ω, including setup, oracle responses and adversary coins. It does not prove an implementation interpreter or a cryptographic numerical bound.

[DERIVED] `advantage_reduction` composes an actual transformed code object and a pointwise bad-event reduction with its resource bound. `Experiment.map` charges explicit output-transformation overhead. `ComputationalBinding.flat_binding_advantage` supplies the concrete two-opening-to-two-preimage reduction for the existing `roScheme`; its cost is `(queries+2, steps+extraSteps)`. `extraSteps` must cover materialization, encoding, scanning and comparison of output words in the chosen interpreter. The reduction does not search for an arbitrary collision somewhere in the hash domain.

[DERIVED] Whole-subject binding is a distinct game, `SameRootDifferentSubject`. For content certificates, instantiate its subject with the **entire length-carrying object**, e.g. `List Byte` or a typed statement including all required identities. Position binding alone cannot disambiguate the empty/prefix case. The module does not equate a short opening with extraction of a whole content preimage.

## Certificate and receipt algebra

[DERIVED] `BindingGame.cert_and` proves the single-experiment union bound:

```text
Pr[V1 ∧ V2 ∧ ¬(commit(w1)=root ∧ P1(w1) ∧ P2(w1))]
  ≤ min(1, ε1 + ε2 + εb).
```

[DERIVED] Here each leg's error includes its own commitment relation, and εb bounds the event that the **two actual extracted subjects** differ despite equal commitments in the same sampled hash world. Neither independence nor an ideal binding object is assumed. `cert_and_of_game` ties those subjects directly to `G.run a ω` and requires a resource budget for that extractor/reduction. This is the precise replacement for CERTIFICATES P7's unconnected `bindAdv` field. It remains conditional on knowledge extraction and the security of the transformed game; existential relation soundness alone does not supply an efficient extractor.

[DERIVED] `BindingGame.receipt_and` proves the same clipped error algebra with an explicit `Bind` check and semantic projection theorem `hjoin`. `hjoin` states why both true leg predicates, with the binding check and outside its failure event, imply the target. This preserves the governance judgment's common experiment and subject interpretation. It does not infer physical occurrence from trajectory validity or per-request safety from statistical detection. Assumption sets and provenance remain part of the receipt; no theorem here proves their minimality.

[DERIVED] For CERTIFICATES L2, a single εb must cover the **whole collection of queried roots and all extracted records**, or be replaced by a sum of separately valid binding bounds. For a cross-scheme L4 bridge, charge the bridge proof error and both endpoint binding reductions unless a single explicitly proved bridge bound already includes them. Reusing identical evidence is not independent repetition and does not justify either multiplication of probabilities or gratuitous duplicate charging.

## Two different audit transports

[READ] `Round.BindLeg` at `AuditSampling.lean:253` quantifies over **every history**. A standard global collision advantage does not have that quantifier. On a rare prefix revealing a collision, its conditional future usefulness can have probability one even when the global event is rare. The finite countermodel `Keystone.rare_history_counterexample` and the two-coin `global_not_history_conditional` retain this distinction.

[DERIVED] **Conditional route.** `ComputationalBinding.bindLeg_of_history_game` constructs the existing `Round.BindLeg` only from a valid bounded code object for each history, a security bound covering that entire class, and an event reduction. `sequential_of_history_game` then invokes the existing detection/sequential theorem. It keeps the checker, beacon and semantic miss decomposition as separate obligations. The patch does not assert that ordinary global hash security provides the per-history premises, especially when the history contains a previously discovered collision or unbounded advice.

[DERIVED] **Ordinary global route.** `leakage_of_global_game` proves:

```text
E[real damage through horizon n] ≤ b/q + M·εglobal.
```

[DERIVED] Its comparison process is defined on the original probability space and satisfies the existing detection premise. On complete histories of length n outside the global bad event, real damage is at most that comparison's `b·count`; on bad histories it is at most M. A whole-run resource-bounded adversary reduces the global bad event to the cryptographic game. `RunCoins`, `mean_runHistory` and `prob_runHistory` identify that finite sampled game exactly with AuditSampling's recursive `expOver` and its most-recent-first history convention. `expOver_mono_final` deliberately requires bounds only at the final horizon, so M may really be `n·b`, rather than an impossible uniform cap over arbitrarily long histories.

[DERIVED] The pathwise coupling is substantive. Conditioning an honest-process theorem on a future event called “no collision” is not a substitute: it can bias the beacon and invalidate its detection premise. Nor does a bound on the submitted update alone bound damage on failed envelope proofs. C2 can use the same global transfer with `b=2B` only when its semantic update transport and both update caps hold; any envelope failure must join the bad event and have an independently justified M. No infinite-horizon finite-loss claim follows from a fixed εglobal and M growing with n.

## Concrete non-vacuity and falsification

[DERIVED] The Lean module includes:

- A constant-hash adversary with two distinct accepted subjects and success exactly one. It refutes a zero binding budget at its inhabited `(2 queries, 1 step)` model budget.
- A nonadaptive sampled **compressing** family with three messages and one-bit digests, indexed by two random bits. Every pair-output adversary (all nine pairs) has collision probability at most 1/2. This is a small pairwise-universal family, not a deployment CR claim; it demonstrates a genuinely inhabited probabilistic premise below one without pretending a finite compressing hash is injective.
- An identity-hash zero-error ideal instance, explicitly separate from compression.
- Two individually true certificates with disjoint subject predicates and no common satisfying subject; dropping binding invalidates conjunction.
- A finite positive-probability rare-history conditioning countermodel and a tight global transfer example.

[OPEN] No deployed hash security number is inferred from these toys. No sampled-key model, resource interpreter or quantum random-oracle bound for the deployed implementation has been constructed here. The existing ROM birthday theorem is explicitly nonadaptive and its universally injective `roBinding` constructor is not a computational instance; the patch corrects the prose that conflated them.

## Existing callers and migration

[EXECUTED] `binding/perfect-binding-callers.txt` records `rg -n 'BindingCommitment|PositionBinding'` over the **Selvage directory only** at the baseline. It is a lexical inventory, including comments, not a declaration or live-reachability census. It names 38 source files (including the defining module and the already repaired reduction module); the exact output, rather than this count, is authoritative.

[READ] The exact-property consumers include accumulation (`AccRbrBcs*`), BaseFold (`BaseFoldCommittedIor`, `BaseFoldRbrTable*`, `BaseFoldRawCommittedIor`), FRI (`AdditiveFriQuery`, `HalfThresholdFri*`), erasure/multilinear commitments, extraction, and oracle-log attribution (`OracleLogLinked*`, `OracleLogProgram`, `ZkRbrGame`). Their ideal algebra remains valid at inhabited non-compressing instances. This patch does not silently reinterpret their `BindingCommitment` hypotheses as computational ones.

[DERIVED] Each migrated consumer must (1) retain the actual attempted opening/extracted words; (2) prove its semantic failure implies its protocol error or that retained collision event; (3) construct one bounded reduction for its entire execution/transcript, charging verification/extraction and output-query overhead; (4) use conditional or global audit transport with the correct quantifiers; (5) keep wire/refinement and length/domain encoding obligations explicit. AuthMap's existing per-opening collision witness is the right Merkle starting point. Its `ColumnCollision` union needs an efficient selector over the supplied openings and a whole-run resource analysis; there is no free zero-error replacement for it.

[OPEN] Full migration of the listed ideal callers and a deployed Merkle/PCS executable verifier is outside the small compatible patch. This deliverable supplies checked computational composition and audit adapters, not a declaration that the verifiable-compute stack is now end-to-end computationally sound.

## Validation and application

[EXECUTED] `python3 notes/astra/binding/check_core.py` compiles the independent finite-game module with Lean 4.35.0 and the local Mathlib pin. `check_adapter.py` first requires a successful fresh core build, then checks the adapter against exact source slices of the current `OpeningScheme`, `roScheme`, uniform counting lemmas and AuditSampling through its sequential/leakage theorems. There are no invented substitute axioms or stubs in that harness. Hash manifests bind the checked sources and imports. The script rejects changes during compilation and preserves the source-slice hashes.

[READ] Local Selvage cached `.olean` headers are **4.30.0**, whereas minidregg's pin and Mathlib cache are **4.35.0**. Therefore these checks do not claim the full module import closure builds. The ordinary `lake build Selvage.BindingGame Selvage.BindingBudget` integration check belongs on hbox under `swarm-build`; it was not run on this Mac. No full minidregg/breadstuffs build or remote build was started.

[EXECUTED] `check_boundary.py` runs minidregg's actual `scripts/check-import-boundary.sh` on a private read-only source overlay with the proposed files substituted and the new files included in its Git index. Its log is `binding/import-boundary.log`. The overlay only creates/deletes its own symlinks; no companion source is rewritten. Python bytecode writes into the companion scripts directory are disabled.

[OPEN] Apply the patch in the integrator's own worktree, resolve any concurrent comment/context changes against `baseline.json`, run the scoped module build and the full import-boundary gate there, then select concrete protocol consumers to migrate. In particular, do not assign `A.εbind := εglobal` just because its units match.
