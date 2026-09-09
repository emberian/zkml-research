# From source AIR to quotient tests and actual PCS openings

[DERIVED] Five Lean modules add a conditional application-equation bridge to the existing actual packed PCS theorem. This moves beyond the prior deterministic row-scope result: an erroneous source row now gives a counted gamma-cancellation event, a nonzero quotient residual gives a counted OOD event, and a claimed accepting arithmetic expression outside those events must contain a false PCS opening.

## What is proved

[DERIVED] `AirPolynomialOod.lift` is a polynomial-valued fold of the existing `AirSig`. `map_read` derives its naturalness from source initiality; `lift_source` identifies its value on a represented base-domain row with the original field arithmetic. This introduces no second arithmetic language or handwritten AIR.

[DERIVED] `BfvQueryRow.PolynomialOod.native_batch_order` proves that the reversed coefficient vector of the **actual emitted query constraint list**, followed by three supplied lookup polynomials, equals the native recurrence `A := gamma*A+C`. `arithmetic_error_coefficient` uses the existing query theorem to turn an incorrect modular row into a nonzero coefficient, regardless of the lookup polynomials. `terminal_coefficient_inhabited` exhibits the actual column-43 terminal corruption entering that theorem.

[DERIVED] `AirPolynomialOod.ood_soundness` assumes constraints and an erroneous base row are fixed before gamma, and a quotient family depending on gamma is fixed before zeta. For `M+1` constraints and residual degree at most `D`, independent uniform field challenges satisfy

```
Pr[(A_gamma - Z_H*Q_gamma)(zeta) = 0] <= M/|Ext4| + D/|Ext4|.
```

The native query specialization uses `M = emittedSystem.length + 2`; the theorem reads that length from the source list. The previously executed emitter reports 2,744 arithmetic bodies, making that observed instance's `M` 2,746. No Lean theorem here computes the optimizer's entire 2,744-entry length, and the generic theorem does not substitute the recorded count as a premise.

[DERIVED] `Ir2QuotientRecomposition.recompose_eval` proves the native eight-coset weighted sum of four extension-coordinate chunk openings. These are coset Lagrange weights, not coefficient chunks. `actual_quotient_degree` proves degree at most 73,728 for reconstructed `Q` when the 32 coordinate polynomials each have degree at most 16,384; multiplication by `X^8192-1` has degree at most 81,920. This uses the inclusive degree cap supplied by the current PCS theorem. It is not a claim that every full native AIR residual has already been instantiated at `D=81920`.

[DERIVED] `Ir2AirPcsOod.air_pcs_soundness` composes a claimed arithmetic equation with arbitrary canonically typed supplied openings in the actual five-input-root, 23-matrix, 5,271-term PCS profile. Its bound is

```
M/|Ext4| + D/|Ext4|
+ 690880504/p^4
+ (((p-1)/p)*(3/5) + 1/p)^38
+ Pr[BoundaryFailure],       p = 2013265921.
```

`BoundaryFailure` is the union of the existing shaped extraction failure and an opening point on the committed LDE coset. The latter is an event, **not** a requirement that every uniform zeta avoid a finite coset. No numerical price is assigned to this union here. Gamma and zeta precede the PCS alpha/beta/query coins; point claims and input checkpoint logs precede PCS alpha through the existing `CommitmentPlan` type. Quotient and physical-column families depend on gamma but cannot be selected after zeta.

## Scope still explicit

[OPEN] The composed head requires exact low-degree physical polynomials representing extracted input rows. It does not yet extract those polynomials from arbitrary nearby commitment words. The frozen PCS common-nearby-polynomial theorem remains stronger in this respect than this first application corollary.

[OPEN] The head also requires its **compiler-derived opening expression polynomial** to equal the chosen AIR quotient residual. The generic expression-to-opening reduction, actual query source coefficient construction, and native quotient reconstruction are proved; their complete native descriptor/LogUp instance is not assembled in this package. The equality is therefore an explicit integration premise, not a claim of arbitrary native application soundness.

[OPEN] The three lookup polynomial bodies, exact-public multiset coverage, native JSON/decoder and Rust correspondence, challenge transcript/Fiat–Shamir/PoW distribution, and deployed shaped-hash failure probability remain outside the theorem. In particular, this package does not reinterpret the old terminal-vulnerable query proofs as repaired proofs. The separate whole-domain compiler replacement supplies the corrected source assertion scope.

[DERIVED] `Ir2AirPcsOod.Witnesses.actual_packed_head_fires` jointly instantiates the complete composed head on the existing actual-shape commitment/log carrier and false one-valued opening claims. The true physical columns are zero while the claimed arithmetic equation accepts, so the false-opening alternative is necessary. A nonconstant correct quotient supplies the positive pole. `adaptive_quotient_falsifier` shows why fixing a quotient before zeta matters: choosing `Q=1/zeta` afterward defeats the OOD equation at every nonzero zeta. The witness hash is deliberately noncryptographic and makes no deployed security claim.

## Integration and checks

[EXECUTED] [CHECKS.json](CHECKS.json) records the five changed-module kernel runs, exact theorem axiom guards, imported source/object hashes, and import boundary. [proposal/Compiler/](proposal/Compiler/) contains the checked sources; [air-polynomial-ood.patch](air-polynomial-ood.patch) is an additive companion proposal. Apply after the frozen actual PCS join and [whole-domain query patch](../whole_domain/whole-domain-query.patch), with their recorded predecessors. The companion trees were not edited. No broad build, native proof, malformed-proof control, web query, Scry query or PDF download was performed for this bridge.
