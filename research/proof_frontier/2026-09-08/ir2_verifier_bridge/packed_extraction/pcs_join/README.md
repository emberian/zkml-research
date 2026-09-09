# Actual PCS batching joined to packed IR2 acceptance

[DERIVED] `Ir2Fri.Pcs.packed_pcs_soundness` composes the frozen actual 5,271-term PCS reduction with arbitrary canonically typed packed openings. The accepted event includes all input and FRI Merkle paths, the initial reduced-input equality, the native `[3,3,3,3,2]` fold equations and the final constant. The source and intermediate words are constructed from commitment-time logs by the frozen extractor.

[DERIVED] Five input roots/logs, opening points and claimed values are fixed before alpha. Each FRI root/log may depend on alpha and its preceding beta prefix. The `CommitmentPlan` type enforces this timing; supplied openings may depend on all challenge and query coins. The initial reduction is the actual batch→matrix→point→column alpha loop, using input coordinates `31*t`, rather than an arbitrary reduction supplied as a premise.

[DERIVED] If the fixed extracted input rows and claims lack a common physical-polynomial explanation, the theorem gives

```
Pr[accepted packed PCS/FRI equations]
 ≤ 690880504/p^4
   + (((p−1)/p)*(3/5)+1/p)^38
   + Pr[observed shaped extraction Failure],
p = 2013265921.
```

The challenge numerator is exactly `5270*131072 + 131064`: one alpha curve count plus the five actual FRI transition counts. The bound uses fresh uniform Ext4 alpha and betas and 38 fresh uniform BabyBear words mapped through the actual 17-bit query rule. It makes no identification with Fiat–Shamir output. This join retains the existing query tail and does not claim a new security-bit target.

[DERIVED] A common explanation means one polynomial per actual input column, degree **≤16,384**, simultaneously satisfying every claimed opening and agreeing with extracted rows on one common set of at least `(3/5)*131072` positions. The original degree cap is one higher than the strict quotient cap `<16,384`; the package preserves this boundary. Off-domain opening points are an explicit premise.

[DERIVED] `packed_pcs_false_claim_sound` specializes the head to an incorrect claimed opening when the extracted input columns already equal evaluations of actual physical polynomials of degree ≤16,384. It proves the required failure of a common explanation by polynomial identity on the shared set. The general head does not assume exact codeword membership.

## Connection to the native code

[SOURCE] The unchanged [PCS batching helper](../pcs_batching/STATUS.md) pins the actual verifier loop, 23 matrices in five batches, 5,271 ordered terms, coset factor 31, and shared alpha power across batches. Its single pure arithmetic replay of the retained canonical query matches every matrix checkpoint and the final reduction; no new cryptographic execution was performed for this join.

[DERIVED] The unchanged [packed extraction](../README.md) establishes the salted flattened Ext4 and same-height matrix codecs, native row/column indexing, reversed sibling/address adapter, and actual supplied-log construction. Its failure term compares only same-shape leaves or node records and includes a conservative late-target event. It is not an arbitrary-list collision event automatically triggered by the already demonstrated 20↔24 cross-shape alias.

[OPEN] No deployed Poseidon probability is assigned to extraction failure. The native padding-free leaf sponge and node compression share an untagged permutation; the earlier independent typed macro-query model remains a separate idealization. The actual Fiat–Shamir/PoW challenge game, probability of an on-domain opening point, and arbitrary Rust-to-Lean implementation correspondence also remain outside this theorem. A conditional mathematical packed acceptance theorem and one accepted native replay are not an arbitrary-proof compiler refinement.

[OPEN] This is a PCS proximity statement. An application-level false execution still needs its AIR/constraint and opening-claim reduction. The common nearby-polynomial head is useful when exact source membership is unavailable, but does not by itself prove those application constraints.

## Validation and integration

[DERIVED] `PackedWitnesses.join_premises_inhabited` jointly supplies the actual-shaped commitment logs, extracted zero input rows, off-domain zero opening points and false one-valued claims. The exact zero source polynomials rule out a common nearby explanation, and `sound_fires` applies the composed head. Correcting the claims to zero restores a common explanation on the whole domain. The deliberately noncryptographic hash witness demonstrates premise inhabitation rather than deployed security.

[EXECUTED] `CHECKS.json` retains changed-module checks, exact axiom guards, preserved dependency hashes and the import gate. The additive `ir2-pcs-join.patch` contains only this join and its premise witness. Apply it after the frozen packed extraction and the separately frozen four-module `pcs-batching.patch`; `pcs_dependency_entry.json` describes that existing helper for integration without changing it. No umbrella edits, broad rebuild, new runtime grid, source search or paper extraction were used.
