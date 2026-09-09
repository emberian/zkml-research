# Actual IR2 FRI proximity bridge

[DERIVED] `Ir2Fri.native_fresh_38` bounds the native interpolation/query event for the observed canonical IR2 profile. For a fixed alpha-reduced source word outside radius 2/5 of the degree-below-16384 Reed–Solomon code on the actual order-131072 BabyBearExt4 subgroup,

```
Pr[native FRI consistency accepts]
  ≤ 131064/p^4 + (((p−1)/p)*(3/5)+1/p)^38,
p = 2013265921.
```

[EXECUTED] Exact rational arithmetic gives approximately `3.713192974180453e−9`. This is a conditional proximity bound. It is not a deployed cryptographic security estimate, and neither the query proof of work nor hashing contributes credited bits here. `fresh_sound` also proves the parameterized bound for every `0 < θ < 7/16` and query count q, replacing 3/5 by 1−θ.

[DERIVED] The probability space is five independent uniform **actual Ext4** challenges and q independent uniform **actual BabyBear** query sample words. The native canonical-bit mask law is proved, including the one extra zero residue. The challenge and query draws are fresh-randomness assumptions; the actual Fiat–Shamir challenger is not silently identified with this experiment.

[DERIVED] The schedule is four width-eight folds followed by width four: domain log heights `17→14→11→8→5→3`, source degree caps `16384→2048→256→32→4→1`. Every input batch in the admitted profile has the same initial height, so no lower-height injected coefficient occurs. Within width eight, the binary challenges are β, β², β⁴; the proof uses one degree-seven curve bound, never independent binary-round bounds. The last width-four curve has degree three. Their derived challenge errors sum to `7*(16384+2048+256+32)+3*8 = 131064`.

[DERIVED] `Words.input` is the fixed alpha-reduced PCS input. `Words.word n` depends only on the first n FRI challenges, so next roots may depend on previous challenges. The first FRI word is a separate commitment: the query event explicitly masks equality to `input` before the first fold. The weighted invariant transports closeness through that initial mask and every later consistency mask. The final word must be constant, as required by the observed one-coefficient final polynomial.

[DERIVED] The source kernel is no longer an unproved folding-equality premise. `P3Barycentric.correctness` proves the native barycentric formula, including β equal to a row node, equals interpolation. `native_eq_foldStep` instantiates this for every actual stage using certified BabyBear roots, row cosets, packed-column bit reversal and exact squaring fibres. `native_query_iff_counted` proves the literal native row checks equal the counted shared-query event for arbitrary field values and challenges. One full 17-bit raw query is transported through every round; only separate query draws are independent.

[DERIVED] `Ir2Fri.Witnesses.premises_inhabited` supplies an actual far source `t^16384` with every committed word equal to one. Its all-zero 38-query vector accepts, while raw bit16 (natural source coordinate one) rejects at the initial equality. Thus source farness, genuine acceptance and rejection are all inhabited without enumerating the field or domain.

## Executed canonical admission

[EXECUTED] The separate runtime lane ran the supported `acceptance_bridge/run.py --canonical TEMPLATE CASE PROOF NEW_OUT` command on the unchanged saved fast001/class0 proof. [The fresh run](../../../vfhe_2026_09_08/query_runtime/acceptance_bridge/canonical001/accepted.json) records native verification and canonical admission both passing. The fixed profile checks the approved template, public-height arity scheduler, pre/post-hiding widths, random-column counts, four-word salts and input bindings. This is an explicitly stronger admission mode; the unmodified native verifier alone is not claimed to enforce those additional predicates.

[SOURCE] The native profile and transcript order were inspected in the pinned `breadstuffs/vendor/plonky3-fri-82cfad73` source. The runtime lane retains exact source hashes and commands. Its canonical [fri_view.json](../../../vfhe_2026_09_08/query_runtime/acceptance_bridge/replay001/fri_view.json) contains all 190 native folds and 38 initial/carry/terminal chains, with canonical Ext4 coefficients in basis `1,X,X²,X³`, `X⁴=11`. Raw native serde values use Montgomery encoding; they must not be read as canonical coefficients. The input PCS uses `x=31*t`, while the FRI row nodes use subgroup t; `input_coset_substitution` records the exact polynomial evaluation substitution.

[EXECUTED] The fresh canonical run's events are byte-identical to the retained replay. The projection independently recomputes all 190 native folds and all 38 chains. These observations establish the saved proof's conformance. They do not prove arbitrary native accepted proofs refine to the global-word theorem.

## Remaining boundaries

[OPEN] **Packed commitment extraction:** derive, for arbitrary canonically admitted proofs, a prefix-fixed global word consistent with supplied salted, flattened Ext4 MMCS leaves, or an appropriate concrete extraction failure. The earlier scalar-leaf commitment-failure theorem does not automatically apply to these packed leaves, same-height matrix concatenations or cap/salt semantics. This is the most direct remaining bridge to an arbitrary-proof theorem.

[OPEN] **PCS and batching:** derive farness of the actual alpha-reduced function from false PCS opening claims, with the observed multi-point reductions, hiding random columns, public preprocessing and coset31 substitution. The theorem's input-farness premise is substantive; the honest replay does not establish it for false claims.

[OPEN] **Challenge generation:** relate the actual alpha/beta/query transcript, Poseidon2 duplex sampling and query-PoW process to an appropriate Fiat–Shamir classical or quantum security game. Fresh-query results are not a FS/QROM reduction.

[OPEN] **Implementation refinement:** the symbolic native kernel/event correspondence is universal inside Lean, but Rust field arithmetic, serialization, MMCS verification, malformed-proof behavior and the executable admission code are not formally compiled/refined to these Lean definitions. The retained source inspection and saved replay have narrower scope.

## Handoff

[EXECUTED] The additive patch and changed-module checks are listed in `CHECKS.json` and `integration_entry.json`. Main minidregg/breadstuffs and every frozen predecessor remain unchanged. The patch depends on the prior full-UD, curve, actual-root, finite-schedule and coherent-tail packages already present in the isolated integration base; it adds no umbrella import and needs no broad rebuild.

[SOURCE] New primary web queries: 0. New Scry SQL queries: 0. No third-party full-paper extraction is included. The source formula follows P3's dual MIT/Apache-2.0 implementation; the new Lean interpolation derivation uses Mathlib theorems.
