[DERIVED] This package improves the five-round actual-BabyBear coherent-query tail from `(24/25)^q` to `(4/5)^q` through a cumulative consistency-weight invariant. It preserves the frozen affine, degree-M, tower, supplied-opening and commitment-failure packages.

[DERIVED] `ArityEight.Schedule.BabyBear.Weighted.sound` proves

```
Pr[existing five-round coherent acceptance]
 ≤ 1198336 / 2013265921^4 + (4/5)^q
```

for the existing prefix-adaptive words, actual multiplicative tower levels 0→3→6→9→12→15, initial degree 2^19, initially 2/5-far source and terminal degree16 RS check. Every round uses the one scalar β with fixed-prefix injected β^8 g. No independence between β, β² and β⁴ is assumed. `ideal_100` instantiates q=312 and proves the entire displayed ideal bound ≤2^-100. `candidate_311_fails` is an exact arithmetic falsifier for lowering this bound’s query count by one.

[DERIVED] `Weighted.supplied_sound` feeds the same bound into the existing scalar-path supplied verifier and adds its observed `Failure` probability. `CommitmentFreshTrace.BabyBear.Weighted.sound` then reuses the frozen causal fresh-query reduction:

```
Pr[InitiallyFar E default c ∧ supplied acceptance E default c x]
 ≤ 1198336 / 2013265921^4 + (4/5)^q
   + ((3Q²+Q)/2+11Q)/N.
```

The initial farness predicate stays inside the joint event over separate hash and FRI coins. `sound_312` bounds this by `2^-100 + ((3Q²+Q)/2+11Q)/N`. `sound_call_budget` uses the existing actual-call accounting `Q≤B+720q`, when its explicit cache-coverage and prover-log premises hold. The 720q term is unchanged. These are classical finite fresh-query statements, not a Fiat–Shamir or quantum reduction.

[DERIVED] The substantive construction is in `CurveWeightedAgreement`, `FoldingConsistencyWeights`, `ConsistencyMask` and `ArityEightConsistencySchedule`. The existing mutual-CA theorem preserves the caller’s agreement set; weight≤1 supplies its density premise. Average source weights over the actual fold fibres and mask failed literal-next equations. Weighted reconstruction preserves θ=1/5, so no per-round radius gap is spent. Prefix timing fixes the weights and injected word before the next scalar. The finite challenge union has the same old sum. `ConsistencyQueryMass` and `ConsistencyCoherentTransport` prove the terminal mass equals the actual shared sampler’s one-query survival and that q independent coordinates exponentiate it.

[DERIVED] Nonvacuity and controls are checked Lean statements. `WeightedAgreementWitnesses` has nonconstant admissible weights, genuine coefficient disagreement, actual good scalars, and overweight/overlapping-marginal falsifiers. `ConsistencyTransportWitnesses` reuses the actual full-size far monomial strategy, its accepting zero-query and rejecting seed-one controls, and proves strict intermediate consistency mass. `witness_sound` applies the new ideal bound to that strategy. `execution_inhabited` applies the composed bound to the frozen finite-digest causal execution family, whose malformed paths deliberately reject. That final family is a causal-certificate inhabitant, not a far accepted collision-free execution.

[SOURCE] `TARGET.md` identifies the precise source-supported invariant and the minimal existing theorem reuse. Local PDFs are pinned in `SOURCES.json`; two web searches were orientation only, zero Scry SQL, no PDF downloads. No source’s stronger Johnson/list-decoding/circle-protocol result is imported.

[EXECUTED] `MANIFEST.json` records every changed-module exact guarded check, complete theorem census, source/dependency hashes, normal import gate and additive patch replay. The three query-transport modules were checked in the helper isolate against the four exact frozen core sources/oleans; those retained checks are selected directly rather than duplicated. The combined patch is the sole integration route. No broad rebuild or independent-review campaign was run.

[OPEN] The mathematics now closes the coherent-tail bottleneck for this consumer. It does not prove the deployed Rust IR2 verifier refines the scalar supplied-opening acceptance event. Packed MMCS, batching and serialized transcript/parameter transport remain an execution boundary, and the separate fresh-coin model is not Fiat–Shamir. An executable event-preserving IR2 verifier adapter is the next critical bridge; do not tune deployed security parameters from this artifact alone. ErrorBudget remains unchanged.
