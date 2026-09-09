# Select nearby columns before the opening challenge

[DERIVED] `Ir2NearbyColumns.selected_air_pcs_soundness` removes the exact source-codeword premise from the first AIR/PCS application bridge. It accepts arbitrary commitment-time LDE words. Each column's mathematical polynomial is selected from those words **before zeta**, using uniqueness at the existing agreement threshold; no efficient decoder or native extraction implementation is claimed.

[DERIVED] The argument uses the actual parameters. Two degree-at-most-16,384 polynomials each agreeing with a fixed 131,072-entry column on at least 3/5 of its positions agree with each other on at least 1/5 of the domain. `overlap_large` proves the resulting intersection has strictly more than 16,384 elements, and `unique` applies polynomial identity. `selected` chooses that unique nearby polynomial when it exists and returns zero otherwise. `claims_of_joint` proves that every common-nearby explanation supplied by the existing PCS theorem must use these selected polynomials. No universal existence assumption is needed: absence of any required nearby column already excludes a common explanation.

[DERIVED] `SelectedPlan.rows` depends on gamma but cannot depend on zeta; the head requires the actual input rows extracted from each plan to equal those fixed rows. Thus opening claims or their explanations cannot select a different nearby polynomial after seeing zeta. The physical columns in the opening-equation polynomial are **derived selections**, replacing the previous freely supplied physical polynomials plus exact-membership hypotheses.

[DERIVED] The application-equation probability bound remains

```
M/|Ext4| + D/|Ext4|
+ 690880504/p^4
+ (((p-1)/p)*(3/5) + 1/p)^38
+ Pr[BoundaryFailure],       p = 2013265921.
```

The field challenges are fresh as in [the frozen polynomial/OOD bridge](../polynomial_ood/README.md). `BoundaryFailure` retains shaped commitment extraction failure or a PCS opening point on the LDE coset. This extension adds no new error term and assigns no deployed hash or Fiat–Shamir security probability.

[DERIVED] The improvement is strict. `bumped` corrupts one LDE position in every column of a zero word. `bumped_zero_near` and `bumped_selects_zero` prove that zero remains the uniquely selected nearby polynomial; `bumped_not_exact` proves that **no** degree-at-most-16,384 polynomial equals every position of that corrupted word. A false one-valued opening is nevertheless excluded by the new theorem. The old exact-codeword premise would disallow this word entirely. Separately, `selected_head_fires` instantiates every premise of the full stronger head on the existing actual 23-matrix/five-root commitment carrier, and no exact source-polynomial membership proof is supplied to that head.

[OPEN] This theorem does not turn every committed LDE cell into an exact polynomial evaluation. An application witness must use the selected polynomials' evaluations on its base trace domain. The next native application construction must derive those source rows, field descent where needed, all native constraint and lookup equations, and their quotient-expression identity. The earlier source-fold and eight-coset quotient results remain available for that join. Native bytes/JSON/Rust correspondence, the concrete transcript/Fiat–Shamir distribution, and deployed hash extraction probability remain explicit boundaries.

[EXECUTED] Three changed Lean modules passed with 14 exact axiom guards and the import boundary, recorded in [CHECKS.json](CHECKS.json). [ir2-selected-columns.patch](ir2-selected-columns.patch) is additive after [air-polynomial-ood.patch](../polynomial_ood/air-polynomial-ood.patch) and its recorded dependencies. The first five-module bridge was left frozen. Neither companion tree was edited; no native proof, malformed-row control, parameter grid, web search, Scry query or PDF download was run.
