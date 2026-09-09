# Packed commitment extraction for the canonical IR2 profile

[DERIVED] `Ir2Fri.Packed.supplied_cover` closes the packed-word extraction premise of the frozen native FRI event. For arbitrary canonically shaped supplied input/FRI openings and a deterministic leaf/node hash suite, accepted paths and consistency equations imply the native event on **words constructed from commitment-time logs**, or an explicit observed extraction failure. No global source/FRI word or desired extraction implication is assumed.

[DERIVED] The input word is constructed by decoding all five input-root leaves and applying one fixed pre-FRI reduction function. Every FRI word is constructed by decoding its checkpoint's packed row and using the proved row/column equivalence. The checkpoint root/log for round j depends only on its j previous beta challenges. The final word is the supplied constant polynomial; there is no fictitious final Merkle root.

[DERIVED] `Packed.supplied_fresh_38` composes this implication with the frozen actual-profile proximity theorem:

```
Pr[accepted canonical packed equations]
 ≤ 131064/p^4 + (((p−1)/p)*(3/5)+1/p)^38 + Pr[observed Failure],
p = 2013265921.
```

The first two terms use five fresh uniform Ext4 betas and 38 fresh uniform BabyBear query words. Input farness at radius 2/5 is a premise about the **derived** alpha-reduced input. This is not a statement that false deployed PCS claims already imply that premise, or that the actual Fiat–Shamir challenger supplies those fresh coins.

## What the construction proves

[DERIVED] `PackedLeafEncoding` uses the existing BabyBearExt4 power-basis coefficient equivalence. It proves exact projection and fixed-shape injectivity for FRI leaves `flatten(each Ext4's four coefficients) ++ four salts`, and for input leaves `concat(matrix row ++ its four salts)` in matrix order. Salt offsets include preceding matrices' salt fields. The generic dependent-width proof handles width 2513 without enumerating field values or a large domain.

[DERIVED] `Ir2FriPackedIndices` proves a bijection from each natural field-domain coordinate to its native packed row/column, and the inverse equals the frozen `nativeRowSourceIndex`. This connects every scalar coordinate of the extracted global word to the actual packed leaf containing it.

[DERIVED] `Ir2FriNativeMerklePath` proves the actual bottom-up, low-bit-first sibling traversal equals the existing root-first recomputation after reversing both sibling order and address-bit order. It includes malformed path lengths and a concrete orientation falsifier. Passing the native siblings unchanged to the existing root-first verifier would be wrong.

[DERIVED] `ShapeRootExtraction` resolves a node only through node records. At a leaf it admits only records of that root's fixed public leaf length. Its collision event compares nodes with nodes, or leaves within that expected shape. Cross-role and cross-length aliases are therefore not automatically collisions for this extractor. The other failure branch is the retained finite-log late-target event: a later observed entry hits a previously fixed root or checkpoint node child. This event remains conservative, and no deployed probability price is supplied for it.

[DERIVED] The verifier log is constructed from the supplied leaf/path calls. Checkpoint log inclusion is the concrete retained-prover-log condition. The proof derives all supplied data projections, initial reduced-input equality, every native row equation and transparent terminal equality from these facts.

[DERIVED] `verificationLog_length_le` proves at most 136q leaf/node macro-call records: five input roots cost 90 per query and five FRI roots cost 46. Thus q38 needs at most 5168 verifier records. This is neither a count of distinct fresh queries nor of underlying Poseidon permutations; prover, preprocessing-tree, transcript and proof-of-work work are additional.

## Actual source and the hash distinction

[SOURCE] The inspected pinned P3 source is `/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7`. `commit/src/adapters/extension_mmcs.rs:81–93` flattens extension coordinates. `merkle-tree/src/hiding_mmcs.rs:168–175` appends each supplied salt vector. `merkle-tree/src/mmcs.rs:1065–1110` preserves original order among same-height matrices and hashes their concatenation; `1122–1151` walks siblings bottom-up; `1178–1184` selects the cap. All admitted heights are powers of two, N=2 and cap height0, with no internal-height matrix injection in this profile.

[SOURCE] Input leaf lengths are `[24,2526,192,63,24]`; FRI lengths are `[36,36,36,36,20]`. The fixed admission profile checks widths, random columns and four-word salts. The unmodified native hiding/MMCS code does not itself enforce all those shape predicates. The completed fresh canonical run is retained in the parent runtime bridge's `canonical001/`; this package performs no additional proof replay.

[SOURCE] `symmetric/src/sponge.rs:167–203` uses `PaddingFreeSponge<Poseidon2,16,8,8>` with zero initial state, overwrite absorption, no length tag and no final padding permutation. `symmetric/src/compression.rs:40–51` uses the same permutation for the binary node compression without a leaf/node tag. A list-valued deterministic HashSuite represents these functions, but an independent fresh typed-hash model is an additional assumption.

[EXECUTED] The disjoint [hash-shape constructor](hash_shape/README.md) demonstrates one native20↔24 cross-length collision and checks its distinct canonical roles. A20-word final-FRI leaf and24-word input-batch leaf belong to different fixed shapes; this example does not forge an accepted proof or show a same-shape collision. The original native salt behavior and stronger canonical admission remain distinguished.

[DERIVED] `Ir2PackedFresh.sound` is an **optional conditional ideal macro-query theorem**, reusing the earlier causal oracle handler and the finite family of10 roots. Under its explicit fresh typed-query execution conditions, the shaped residual is bounded by `((3Q²+Q)/2 + 10Q)/N`. `fresh_count_le` relates Q to actual retained prover calls plus136q verification records. No value N is substituted for deployed Poseidon, and no actual typed-hash independence, indifferentiability, FS or QROM theorem is inferred from the source or collision experiment.

## Nonvacuity and remaining work

[DERIVED] `Ir2PackedWitnesses.actual_profile_inhabited` jointly inhabits actual BabyBear shapes/heights, extracted source farness, checkpoint inclusion, no observed failure,38-query acceptance at raw0, and rejection at raw65536. It uses a deliberately noncryptographic constant digest suite and a fixed monomial reduction; same-role/same-shape query keys remain unique even though cross-role/shape aliases exist. It does **not** identify that witness reduction with native PCS batching.

[DERIVED] `Ir2PackedFreshWitness.execution_inhabited` also inhabits the complete conditional execution interface at Q=7, N=1 and q=38, with initial farness and acceptance for every beta vector at the all-zero query sample. The singleton digest is deliberately noncryptographic; this supplies premise inhabitation, not a hash-security example.

[OPEN] The next mathematical obligation is the actual fixed alpha-weighted quotient reduction and a false-claim-to-farness or common-nearby-polynomial theorem. The `pcs_batching/` sibling is independently constructing that result; its active files are excluded from this extraction patch and completion claim. The reduction interface is fixed before the FRI challenges and used identically for supplied and extracted rows, so this follow-on can instantiate it without changing extraction.

[OPEN] An actual Poseidon/sponge extraction-failure bound and the actual Fiat–Shamir/PoW challenge game remain distinct obligations. Rust arithmetic, serialization, shape guards and supplied proof handling are source-inspected/executed boundaries rather than a formally verified Rust-to-Lean compiler refinement. The deterministic theorem applies to arbitrary typed packed proofs; the saved honest runtime replay is not treated as arbitrary-proof refinement.

[EXECUTED] All selected source and patch pins, changed-module checks and the import gate are in `CHECKS.json` and `integration_entry.json`. Main companions and all frozen predecessors are unchanged. No broad rebuild, new proof grid, third-party paper extraction, web query or Scry SQL query was used for this extension.
