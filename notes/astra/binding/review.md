# Independent binding-patch review

[READ] Reviewer: Astra governance-statement lane, independently assigned by the root. Scope: `binding/source/Selvage/BindingGame.lean`, `BindingBudget.lean`, comment diffs in `Commitment.lean`, `CollisionResistanceROM.lean`, `AuditSampling.lean`, and the two validation harnesses. This lane changed none of those files. The review is of the additive computational interface and its consumers, not a deployed verifier or a complete replacement of existing ideal commitment consumers.

## Semantic findings

1. **Empty uniform sample space — repaired in the working source.** [READ] Initially `prob` divided an indicator sum by `Fintype.card Ω` with only `[Fintype Ω]`. At `Ω = Empty`, Lean's `0 / 0 = 0` gives `prob True = 0`; `SecureAt` could therefore present a vacuous zero-error experiment. The author added `[Nonempty Ω]` to `SecureAt` and public security/composition adapters, and `prob_true` as a normalization tooth. Generic `prob`/`mean` algebra may retain the zero-measure extension, explicitly separated from probabilistic security APIs. The actual adversary-application theorems also require an `a` and its resource-budget witness, so an empty admissible code class cannot instantiate their conclusions for a real adversary.

2. **Actual extracted subjects — repaired with `cert_and_of_game`.** [READ] `cert_and` correctly uses one world-indexed commitment function, one advertised root, and two local subject openings; equal subjects transfer `P₂` to the first subject. But arbitrary semantic functions `w₁,w₂` need not be efficiently extracted from accepted proofs. The new `cert_and_of_game` names one fixed experiment and the actual pair `G.run a ω`, supplies its resource witness, and bounds that pair's collision event using `SecureAt`. This prevents an arbitrary existential witness choice from silently consuming a computational bound. [OPEN] A deployment must still provide an efficient extractor/prover-output reduction and prove its resource model. Ordinary existential relation soundness alone is not knowledge soundness.

3. **Receipt binding is semantically used.** [READ] `receipt_and` requires an explicit `hjoin`: accepted binding and no binding failure transport both local predicates into the target. This is stronger as an interface than merely adding an unused ε-binding term to a same-world conjunction bound. [INFERRED] Its union-bound algebra is sound without independence. If `Bind`, `BadBind` or `Target` are instantiated with vacuous predicates, a useful accepted witness remains an application-level obligation; the generic theorem does not pretend otherwise.

4. **The global-to-history distinction is preserved.** [READ] `bindLeg_of_history_game` requires a resource-bounded admissible code for every history, with a pointwise failure reduction. It does not infer this from one global collision probability. `global_not_history_conditional` and `rare_history_counterexample` exhibit why conditioning on a positive-probability collision-revealing history can raise failure to 1. [INFERRED] The history adapter is intentionally strong and may not be the right deployment route. The global finite-horizon adapter is the ordinary alternative.

5. **Coupling and damage cap are sufficient, not hidden conclusions.** [READ] `mean_bad_transfer` assumes nonnegative comparison `X`, pathwise `Y ≤ X` off the bad event, `Y ≤ M` on it, nonnegative `M`, an expectation bound on `X`, and a probability bound on bad. [INFERRED] These imply the pointwise bound `Y ≤ X + M·1_bad`, hence the stated expectation bound. No nonnegativity of `Y` is needed for that mathematical implication. The audit-specific adapter restricts pathwise premises to final histories of length `n`, matches the actual `expOver` operator through `RunCoins`/`runHistory`, and invokes the existing comparison process's leakage theorem. It does not condition `X` on future success. [OPEN] Real-process coupling and the cap are genuine application obligations. If an envelope failure permits unbounded damage, `M=n·b` is not justified and this route cannot claim it for free.

6. **Sampled compressing witness is properly limited.** [READ] The toy has three messages, two digest values, four equally likely hash seeds, and a fixed pair code class. The `1/2` bound concerns a nonadaptive pair chosen before seed access; every individual hash is still compressing. [INFERRED] This is a useful inhabitance witness distinguishing computational event security from universal injectivity. It is not a deployed hash bound, adaptive random-oracle security theorem, or a claim that the generic `Experiment` structure is an executable machine interpreter.

7. **Fixed resource model remains an interface assumption.** [READ] Queries and steps belong to the fixed experiment, rather than being counters submitted with an adversary. `map` charges explicitly supplied reduction overhead and `Within` is worst-case over worlds. [OPEN] The type does not prove that these functions measure a concrete interpreter, that oracle access is restricted to counted queries, or that abstract output functions are computable. Those realization obligations must remain in the patch's ledger and final report. A security bound for a restricted code class is not automatically a bound for a broader one.

## Validation findings

[READ] An early harness version allowed `check_adapter.py` to import a stale `BindingGame.olean` even if the latest core source failed to compile. The original logs visibly contained a core failure while an old olean existed. That was an in-progress validation failure, not a completed patch theorem.

[READ] The author changed the adapter harness to run the core checker first with `check=True`, pin a source/olean manifest, use saved original source slices for the touched dependency files, and retain exact extracted source plus hashes. This addresses stale-success and concurrent companion-tree concerns. Reviewer additionally requested pre-build source hashes, unchanged-source assertions after Lean exits, and imported-olean hash verification, so a source edit during compilation cannot be mislabeled as checked.

[READ] The final checks below close the in-progress validation findings. A successful slice harness is deliberately narrower than compiling the full `Selvage.BindingBudget` import graph against fresh project artifacts; do not relabel it a full minidregg build.


## Final reviewer verdict

[INFERRED] **Ready as an additive, conditional computational-binding repair; no remaining semantic blocker found in this scope.** The review found and helped repair two semantic/interface defects (empty-world security vacuity and witnesses disconnected from the actual bounded extractor output) plus one validation defect (stale or changed source/artifact acceptance). The remaining obligations are explicitly scoped application work, not hidden perfect-binding assumptions.

[MEASURED] [EXECUTED] Final independent review result: `notes/astra/binding/review-check.json`. The reviewer ran Python SHA-256 comparisons, read both final Lean logs and the actual import-boundary log, then used `git apply --check` followed by `git apply` in **two newly created scratch repositories containing only copied touched files**: one from the captured baseline and one from the then-current minidregg files. Both checks and applications exited 0; all five resulting files were byte-identical to the reviewed `binding/source/` files. No companion-tree file was modified.

[MEASURED] Source/artifact verification passed:

- The core source SHA matches its successful compiler manifest; the generated core olean matches its manifest hash.
- The adapter source, imported core SHA, generated exact-source harness and all five saved dependency slices match the successful adapter manifest.
- Core and adapter final logs both end in `EXIT 0`. The actual import-boundary script on the author's full tracked-source symlink overlay, with all five proposed files substituted, also ends in `EXIT 0`; its allowed library components are unchanged.
- All **39 new theorem declarations** (25 core, 14 adapter, counted by anchored declaration names) have `#guard_msgs`-pinned `#print axioms` checks. No new `axiom`, `opaque`, `unsafe`, `partial` or standalone `sorry` declaration was found by the scoped declaration scan. The completed builds establish the axiom guards, not just the token scan.
- The compressing witness also instantiates `cert_and_of_game` in `certificate_game_fires`, so the certificate composition is exercised on the actual bounded pair output rather than only stated abstractly.

[MEASURED] Reviewed patch SHA-256: `94b94700e709e931e9b9bd5c30834620e1b9a51603ea15a70a134ae4e71de534`.

| Reviewed file | SHA-256 |
|---|---|
| `Selvage/BindingGame.lean` | `e48cbb598e44001ff60bd50161da238f209b701521726e213049151ea2deaf27` |
| `Selvage/BindingBudget.lean` | `46ed39e74b6b026577895a55966cab5f4cf581d4a551ed3202ec3e19fe85f51b` |
| `Selvage/Commitment.lean` | `28c453a73aa0afee3da26ebd0a36268dfa925f1531d7451f0056a640577453b0` |
| `Selvage/AuditSampling.lean` | `81ff2f5d5914f1afdd3d54054050ea4defa271189868a37d71b100bc0db34372` |
| `Selvage/CollisionResistanceROM.lean` | `ed5da9b5173b1e1ac309d76076f96d1070b612ad40c19e9debf10f1593c0cab9` |

[OPEN] Full fresh import-graph compilation/integration remains an hbox task. Concrete hash/ROM bounds, a resource-faithful interpreter/extractor, serialized subject binding, the real audit comparison coupling and finite damage cap, and migration of downstream ideal-only consumers remain deployment obligations. None is supplied by the toy witness or by the abstract union-bound theorem. The patch does not silently claim otherwise.
