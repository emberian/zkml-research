# Decreasing radii in the actual coherent FRI theorem

[EXECUTED] `Selvage/FullUDSamplingBudget.lean` instantiates the existing half-threshold and full-UD transitions and calls `friAdaptive_coherent_sampled_sound`. The initial radius is 2/5, there are 19 rounds, the initial domain has 2^20 positions, and the initial degree bound is 2^19. Every subsequent radius is `(19-j)/95`; the first fold output radius is 1/5, and each later fold preserves its current radius. Each query gap is 1/95. The final radius is zero and the final degree bound is one.

[EXECUTED] The new theorem does not assume a final gap or folding-transition family. The closed-form sequence proves every gap; the concrete degree sequence and `PowerTwoFriLevels 20` prove halving, positive degree and rate one half. Round zero uses the existing half-threshold theorem and each tail round uses the frozen `foldDistancePreserving_fullUD` realizer. A separate concrete whole-word head directly consumes the frozen `proximity_sound_rateHalf_twoFifths_fullUD` theorem.

[EXECUTED] The exact existing ideal coherent-sampling expression is

```
19 * 2^20 / |F| + (94/95)^q.
```

On the existing `BabyBearExt4.Ext4 = AdjoinRoot(X^4-11)` carrier, the frozen BabyBear bridge supplies `|F|=2013265921^4`. The new `fullUDSampling_babyBear_55` theorem gives acceptance probability at most `2^-55` at q=3603. Kernel `norm_num` proves the exact inequality; no floating point, `native_decide`, `sorry`, or axiom is involved.

[EXECUTED] Numerical minimality is proved for every smaller q: 3602 fails at gap 1/95. A general telescoping proof derives `18*tau+radius19 ≤ radius1` from all 18 tail gaps. Together with the first half-threshold output this forces tau≤1/95; the old open tail band forces tau<1/108. Even the optimistic closed old endpoint fails at q=4098. A strictly interior old gap 8191/884736 has a checked complete old-band radius sequence and succeeds in the unchanged expression at q=4099. Thus the exact expression permits 496 fewer samples under the new band. This is a comparison within this uniform-gap half-threshold/preserving-tail construction, not a lower bound for every FRI analysis or protocol. The old comparison includes arithmetic and schedule realization; only the new schedule has a separately exported actual coherent probability head in this patch.

[EXECUTED] The fixed challenge term alone exceeds `2^-100`, irrespective of sample count when tau≤1. The patch does not change the inherited ErrorBudget, current query ledger, runtime parameters, Merkle error, grinding, sumcheck, or Fiat–Shamir terms.

## Exact remaining protocol premises

[OPEN] The conditional probability head still takes an actual `FoldingTower Ext4 (PowerTwoFriLevels 20) 19`, the existing family of ideal `BindingCommitment`s, and a `FriAdaptiveTranscript` whose initial word is 2/5-far. No concrete multiplicative tower, commitment implementation, or initial-farness reduction is constructed in this package. The imported `FriAdaptiveCoherentAccepts` event samples uniform challenges and uniform initial pair indices with replacement and modulo projection; concrete Fiat–Shamir/shared-execution composition is separate. Arithmetic witnesses certify the radius/numerical contracts, not inhabitation of all these deployment premises.

[SOURCE] Source theorem names and exact paths/lines, dependency hashes and frozen package references are recorded in `manifest.json` and `dependency-pins.json`. The candidate imports only frozen full-UD and BabyBear packages plus existing coherent query definitions. Original packages and companion trees remain untouched.

## Reproduction and integration

[EXECUTED] Single-module checks and exact source hashes are in `logs/`; `run_lean.py` records the LEAN_PATH used to consume checked read-only dependency objects. `full-ud-sampling-budget.patch` adds one module only. Apply after the full-UD package with universe successor and the BabyBear bridge. Root owns umbrella integration and whole-tree validation.
