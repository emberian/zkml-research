# Independent audit: full-UD sampling budget and BabyBear bridge

[DERIVED] **Accepted in the exact conditional scope below. No mathematical or source-interface defect found; no source correction requested.** The frozen sampling module proves the shrinking schedule, its degree/rate obligations, its actual full-UD fold transitions, and the application to the existing coherent sampled verifier. The BabyBear module proves the cardinality of the existing quotient field. Numerical optimality concerns the stated error expression and uniform-gap construction, not optimal security or query complexity of every FRI protocol.

[SOURCE] Final source/patch hashes were confirmed by their owners before this verdict:

| Package | Source SHA-256 | Patch SHA-256 |
|---|---|---|
| `full_ud_sampling_budget` | `a4bd35ea6f1e1ada77a20a3c8634b7dd7ac89aa0231be3a7db464955c5761c04` | `589ae51ff846889eb5403b1b415755a06a1fd4865466e22fa63902addd9f8852` |
| `full_ud_babybear` | `03f80a278b95dfb767eaf6657ee63b26a643900df5d0cbfb4c1a579399314978` | `fa8a815069f628ef4ae34a1eda2c91989fd3af87c55ccc8f4056aa78d9bc6e25` |

[EXECUTED] Independent patch reconstruction matches both source files byte for byte. The existing integration census passes 25/25 sampling declarations/guards and 12/12 carrier declarations/guards. Every expected axiom is standard; two sampling arithmetic helpers correctly have smaller axiom sets. Eight directly used dependency source/object pairs match their recorded hashes, and existing companion sources match their checked copies. Results are in `source_verification.json`, `census.json`, and `source.log`.

[SOURCE] The producer's final exact-source Lean checks report exit 0, unchanged bytes and empty logs. This audit checked those records and objects; it performs no independent clean/full Lean build. Root owns the combined integration. The formal base remains minidregg `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`, Lean 4.30.0.

## Schedule and optimality

[SOURCE] [FullUDSamplingBudget.lean:16](/Users/ember/dev/zkml-research/research/proof_frontier/2026-09-08/formal/full_ud_sampling_budget/FullUDSamplingBudget.lean:16), `FullUDSamplingRoundConditions`, requires initial radius `2/5`, final radius zero, positive gap at most one, first fold radius equal to half the initial radius, every round's query gap, and positive preserving tail radii below `1/4`. The concrete definitions are:

```text
radius(0) = 2/5
radius(j) = (19-j)/95                 for 1 ≤ j ≤ 19
foldRadius(0) = 1/5
foldRadius(j) = radius(j)             for 1 ≤ j < 19
degree(j) = 2^(19-j)                  for 0 ≤ j ≤ 19
domain size(j) = 2^(20-j)
```

[SOURCE] `fullUDSampling_round_conditions` at line 33 derives every gap, including the final `radius(19)+1/95≤foldRadius(18)`. It does not accept that last inequality as a premise. The named premise and satisfiability witnesses use this proved schedule. `fullUDSampling_teeth` rejects gap `2/95` on the same schedule by inspecting the last round.

[SOURCE] `fullUDSampling_degree_halves`, `fullUDSampling_degree_positive`, and `fullUDSampling_rate` at lines 77, 84 and 89 prove exact halving, positive degree, and rate one half on the actual `PowerTwoFriLevels 20` index types. The final length is two and final degree bound one. The real-valued radius formula outside the used range can be negative, but the consumer only uses levels zero through nineteen and rounds zero through eighteen; no out-of-range radius is used.

[SOURCE] `fullUDSampling_tail_gap_sum` at line 98 telescopes all eighteen positive tail rounds to `18τ+radius(19)≤radius(1)`. Combined with `radius(19)≥0` and `radius(1)+τ≤1/5`, line 119 proves `τ≤1/95`. If the first tail radius must also be `<1/6`, it proves `τ<1/108`. Neither conclusion assumes positive degree/rate as numerical facts about arbitrary FRI schedules: the interpretation as an old/new band comparison is for the explicitly chosen rate-half, first-halving, preserving-tail construction.

[DERIVED] The new schedule attains its maximum gap, since `19/95=1/5` and `18/95<1/4`. The old gap has only the supremum `1/108`, because `18/108=1/6` is excluded. Its strictly interior witness `8191/884736` gives an actual old-band schedule with the **same initial farness radius `2/5`** and spare slack at the first round. Thus it would be incorrect to say that the old analysis could not accommodate initial radius `2/5` at all.

## Exact numerical boundary

[SOURCE] `FullUDSamplingNumericalBudget` at line 133 is precisely
`19·2^20 / 2013265921^4 + (1-τ)^q ≤ 2^-55`.
The four boundary proofs use kernel `norm_num`, followed by monotonicity in query count and admissible gap. The smaller-query failure is a failure of this sufficient bound, not a lower bound on the actual acceptance probability.

[EXECUTED] `arithmetic_review.py` independently verifies the inequalities by integer cross-multiplication. It does not execute or modify the author's `derive.py`. The following intervals for `bound / 2^-55` are exact enclosing intervals with denominator `10^12`:

| Query count and gap | Enclosing decimal interval | Result |
|---|---|---|
| `3603`, `1/95` | `[0.995764010094, 0.995764010095)` | passes |
| `3602`, `1/95` | `[1.006357244244, 1.006357244245)` | fails |
| `4099`, `8191/884736` | `[0.997267465223, 0.997267465224)` | passes |
| `4098`, optimistic old limit `1/108` | `[1.001891587434, 1.001891587435)` | fails |

[DERIVED] Gap monotonicity means every old admissible smaller gap also fails at 4098. Query monotonicity extends each preceding-query failure to all smaller counts at the applicable gap. Together with the attained interior old schedule, the optimal integer counts for this fixed expression are exactly 4099 and 3603: 496 fewer sampled paths. The old comparison proves arithmetic and schedule admissibility; this patch exports a separate actual coherent probability head only for the new schedule. That distinction is preserved in its README.

[EXECUTED] All five same-initial-radius rows in `parameter_delta/results.json` match independent exact comparisons: Ext4 targets 55 and 99 give old/new `4099/3603` and `7535/6624`; Ext4 target 100 is blocked by the fixed challenge term alone; Ext6 targets 120 and 137 give `8942/7861` and `10209/8974`. Each attainable row has a passing interior old witness and a failing preceding count at the optimistic old limit, plus the corresponding new pass/fail pair. These are parameter-model results, not newly realized Ext6 protocols.

[EXECUTED] The review also recomputes every exact summand in the five inherited algebraic budget profiles. Their floor-bit values remain `55,137,16,75,137`; the four principal current/proposed UDR query-ledger values remain `34,45,47,54`. The existing `TwoRegimeQueryBudget.survivalSq` already uses `((1+ρ)/2)^2` for UDR. Radius does not appear in the inherited ErrorBudget error expression. No new saving can be taken from those unchanged columns, and no independent error was removed or discounted here.

## Actual coherent theorem application

[SOURCE] `fullUDSampling_transitions` at line 240 obtains the first round from `foldDistanceTransition_halfThreshold`, with one bad challenge, then weakens to the common bound `2^20`. At every positive round it invokes the frozen `foldDistancePreserving_fullUD`, supplying the derived positive target degree and rate-half radius inequality. Each tail's own exception count is its folded-domain cardinality, weakened to the same common bound using `T.card_level_le_zero`. No transition family or gluing/proximity goal is passed in by the caller.

[SOURCE] `fullUDSampling_coherent_sound` at line 290 calls the existing [HalfThresholdFriCoherent.lean:217](/Users/ember/dev/minidregg/Selvage/HalfThresholdFriCoherent.lean:217), `friAdaptive_coherent_sampled_sound`, with the derived schedule, final nonnegative radius, every gap, and that transition family. It proves the existing `FriAdaptiveCoherentAccepts` event under the exact probability space
`(Fin 19 → F) × (Fin q → PowerTwoFriLevels 20 1)`.
The first component is uniform field challenges. The second is independent uniform initial pair indices sampled with replacement; the existing round maps take remainders modulo the shrinking pair-domain sizes. The same query seeds determine all rounds. For each fixed challenge tuple outside its bad event, the proof selects a discrepant round independently of the query seed and bounds the chance that all queries miss it. This yields the existing `19·2^20/|F|+(1-τ)^q` bound without an extra round multiplier on the query term.

[SOURCE] The remaining quantifiers matter. [HalfThresholdFriQuery.lean:41](/Users/ember/dev/minidregg/Selvage/HalfThresholdFriQuery.lean:41) defines `FriAdaptiveTranscript`: its level-`n` word and root may depend on the **first `n` field challenges**. In particular, the next word may depend on the challenge just drawn. This is stronger than the fixed-all-level-words event in the earlier whole-opening audit. The strategy `st` and commitment family `S` are fixed outside the probability space; words and roots have no query-seed argument. Exact `PositionBinding` is carried by `BindingCommitment`, not proved for a concrete hash implementation here.

[DERIVED] The ideal model therefore allows challenge-prefix adaptivity while excluding dependence of committed words on the sampled query seed. It does not itself establish the actual runtime's commitment ordering, query-seed independence, Fiat–Shamir distribution, or root/word extraction. The generic coherent theorem only needs its proved uniform modulo marginals; supplying a `PowerTwoFriLevels`-sized tower does not by itself identify deployed domain ordering and folding layout with that model. The separate timing/execution audit remains necessary for those claims.

## Existing BabyBear carrier

[SOURCE] [BabyBearFullUD.lean:16](/Users/ember/dev/zkml-research/research/proof_frontier/2026-09-08/formal/full_ud_babybear/BabyBearFullUD.lean:16) transports a `Fintype` through the existing coefficient equivalence. The carrier is exactly [BabyBearExt4.lean:132](/Users/ember/dev/minidregg/Selvage/BabyBearExt4.lean:132), `AdjoinRoot (X^4-C 11)` over `ZMod 2013265921`. Its predecessor proves the quartic irreducible, hence supplies a genuine field. At line 153 it supplies a linear equivalence to four base-field coefficients. `ext4_card` counts that equivalence and uses the proved degree four and `ZMod.card`; no substitute field-cardinality assumption enters.

[EXECUTED] The bounded arithmetic checks independently confirm prime modulus `2013265921`, Euler witnesses for both `11` and `-11`, and the quartic cardinality `16428751811598850197311699254593454081`. This corroborates the source's cardinality ingredients; it is not a new Lean replay of irreducibility or a codec execution check.

[SOURCE] The carrier bridge's `isProximityGenerator_fullUD` invokes the unchanged generic PG theorem and rewrites its denominator with `ext4_card`. Its rate-half probability theorem retains the substantive `¬CorrelatedAgreement` premise. The good line inhabits all PG firing premises on a concrete `Fin(2^20)` embedding. Separately, the pair `(x↦x^(2^19),0)` inhabits the failure premise: root counting bounds common agreement by `2^19`, below the required `(4/5)·2^20`. The base-field cardinality falsifier also rejects replacement of the quartic carrier by its base field.

[DERIVED] That witness embedding uses consecutive base-field elements, including zero. It cannot itself serve as the nonzero multiplicative folding domain required by `FoldingData`. The carrier/cardinality obligation is discharged; construction and identification of the intended 19-round tower remain separate.

[SOURCE] `fullUDSampling_babyBear_55` at line 333 combines the exact carrier cardinality, the actual coherent probability theorem, and the proved 3603 inequality. It still takes the actual tower, an ideal-binding commitment family, a prefix-adaptive transcript, and initial `2/5`-farness. Its arithmetic witnesses do not claim to inhabit all those protocol premises.

## Integration scope

[DERIVED] Credit the checked radius schedule, same-bound 496-path arithmetic improvement, existing coherent theorem instantiation, and actual formal field/cardinality bridge. Do not credit a constructed FFT tower, an initial-farness reduction, concrete binding, adaptive runtime timing, query sampling implementation, Fiat–Shamir/ROM transfer, or total deployed 55-bit security. The 3602/4098 failures are certificate boundaries, not attacks. The `2^-100` obstruction applies to the chosen common challenge bound and field/round parameters, not all possible analyses.

[EXECUTED] Reproduction commands, run from the research root:

```text
python3 research/learn_infer_only/experiments/adversarial_review/full_ud_sampling/arithmetic_review.py > research/learn_infer_only/experiments/adversarial_review/full_ud_sampling/arithmetic.log 2>&1
python3 research/learn_infer_only/experiments/adversarial_review/full_ud_sampling/source_review.py > research/learn_infer_only/experiments/adversarial_review/full_ud_sampling/source.log 2>&1
```

[EXECUTED] Both returned exit 0. No author source, companion, shared verdict, or prior frozen review was edited. No cryptographic execution, external search, or clean/full Lean build was performed. Root owns final integration; proof_frontier owns the separate timing bridge audit.
