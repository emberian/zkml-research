# Actual arity-eight folding with sampled supplied openings

[DERIVED] This package closes a missing consumer of the degree-M full-UD theorem: **actual source-word farness now implies a one-scalar arity-eight sampled transition bound**. It also gives an executable eight-value row checker using supplied BinaryMerkle paths, a finite-log extraction reduction, and an actual BabyBear/coherent-query specialization. It does not establish a whole-protocol or Fiat–Shamir security budget.

## The construction

[DERIVED] `ArityEightFold.fold8` is exactly three existing `FoldingData` folds with challenges `beta, beta^2, beta^4`. `fold8_eq_curve` proves that this is the degree-seven geometric curve of eight fixed parity components. The source word and the three existing domain embeddings determine those components before beta. There are no intermediate-word or independence assumptions.

[DERIVED] `correlatedAgreement_recompose_family` lifts a common agreement set through an existing squaring fibre, simultaneously for every member of a family. Three applications reconstruct an actual degree-below-`8*d` source codeword on the eightfold lifted set. Relative agreement is preserved by the existing exact fibre/cardinality laws. `reconstruction` thus removes the former coefficient non-correlated-agreement premise using actual source farness.

[DERIVED] For output-domain size `n`, positive degree `d`, `theta>0`, and

```
d < (1 - 2*theta)*n,
delta + tau <= theta,   tau <= 1,
f is not theta-close to the source RS code of degree below 8*d,
```

`fold8_sampled_crossing` proves

```
Pr[ next(beta) is delta-close
    AND q sampled equations next(beta)[i] = fold8(f,beta)[i] pass ]
  <= 7*n/|F| + (1-tau)^q.
```

[DERIVED] `fold8_injected_sampled_crossing` replaces the literal fold by
`fold8(f,beta) + beta^8*g`, where `g` is fixed before beta, and changes the challenge term to `8*n/|F|`. The injected word need not be a codeword. The next word may depend on beta, but has no query-seed argument. Each theorem samples one uniform scalar, followed by `q` uniform output indices with replacement.

[DERIVED] The close-next-word condition defines the **crossing event** used in a soundness argument. It is not an extra operation performed by the row checker. A multi-round earliest-crossing reduction remains to be constructed for the variable-arity protocol.

## Supplied paths and commitment timing

[DERIVED] `ArityEightSupplied.rowCheck` is executable. It feeds eight source values/paths, one injected-input value/path and one next-word value/path into the existing `BinaryMerkle.recompute`; it then checks the literal `foldRow8` equation. `rowCheck_eq_true_iff` identifies its acceptance with `RowVerified`. `foldRow8_eq_fold8` proves the eight supplied source values compute the actual fold when they are correct.

[DERIVED] `supplied_injected_crossing_sound` composes this checker with the existing deterministic `EfficientRootOpening.word` extraction. Its conclusion is

```
Pr[raw supplied-path crossing acceptance]
  <= 8*n/|F| + (1-tau)^q + Pr[RoundBad].
```

[DERIVED] Source and injected-input checkpoints/roots are fixed before beta. The next checkpoint/root is a function of beta alone, so it is fixed before queries. Openings and complete execution logs may depend on the query vector. The premises require each checkpoint and every actual supplied opening's hash-call records to occur in that execution log. No accepted path is replaced by existential opening evidence.

[DERIVED] `RoundBad` is the disjunction of the predecessor's observed response collision or late-target event at the three checkpoints. Its probability is explicit and unpriced. The theorem does not identify this event with an efficient collision advantage, derive a ROM bound, or prove that a real runtime has produced the asserted checkpoint/log history. It only uses the finite records provided to the theorem.

## Actual carrier and query interface

[DERIVED] `ArityEightBabyBear.first_injected_crossing` discharges carrier, domain, rate and degree arithmetic on the existing certified BabyBearExt4 tower. The first block is

```
source length 2^20, degree below 2^19
output length 2^17, degree below 2^16
source farness 2/5; theta=1/5, delta=tau=1/10
bound: 2^20 / 2013265921^4 + (9/10)^q.
```

[DERIVED] `actual_far_source_fires` instantiates its source with the predecessor's proved high-degree word. This is one transition's bound; it adds no whole-protocol security bits.

[DERIVED] `ArityEightQueryTransport.coherent_block_uniform` transports any challenge/row event through the existing level-three coherent query projection exactly, cancelling the discarded quotient bits. `babyBear_coherent_first_injected_crossing` therefore gives the same bound for the existing uniform first-pair seed sampler, of size `2^19` per query.

[DERIVED] `p3_first_block_row`, by the frozen transport theorem, identifies the projected row of a runtime-shaped index with `reverseIndex 17 (index/8)`. This is an exact index identity, not a Rust execution or random-challenger refinement.

[SOURCE] The already inspected, pinned p3 source uses successive squared internal challenges at `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:284–334` (squaring at 326), Lagrange row evaluation at 230–252, and matching-height `beta^arity` input addition at `src/prover.rs:237–245` / `src/verifier.rs:469–479`. The corresponding source hashes and frozen orientation/transport dependencies are recorded in `MANIFEST.json`.

[OPEN] This checker authenticates **ten scalar paths**; actual p3 uses packed MMCS rows and its own ordering. The earlier transport package checks the row-order/coefficient identities independently, but this package does not prove their Rust execution equivalence. Multiple heights, variable arities, outer cosets, extra query bits, hash encoding/log completeness, fresh-challenge implementation and Fiat–Shamir remain explicit protocol integration work. No prover speedup or path-count saving is measured here.

## Nonvacuity and checks

[DERIVED] The finite witness uses `F17`, the certified order-16 root `3`, actual multiplicative domains `16→8→4→2`, and `f(X)=X^8`. Existing RS minimum distance proves positive source farness. The literal fold is `[1,-1]` for every scalar; claiming constant `1` accepts row zero and rejects row one. All degree/rate/gap premises fire, including a nontrivial small-field probability expression.

[DERIVED] The supplied-path witness uses a concrete tree-valued toy digest. Its 88-record fixed checkpoint extracts the actual far source and the next constant codeword, contains all supplied paths, and has no observed `RoundBad`. The complete raw event is inhabited for every scalar and query count, and `supplied_bound_fires` applies the composed probability theorem with zero observed failure probability. This is an explicit toy-hash witness, not a cryptographic hash claim.

[EXECUTED] `checks/ExecutableProbe.lean` evaluates the compiled Boolean row checker on all 17 scalar challenges: the accepting row, the false row equation, and truncated supplied paths. The saved output is `(true, true, true)` and checkpoint length `88` (51 verifier controls). Proof witnesses use kernel-checked arithmetic; no `native_decide`, `sorry` or added axiom is used.

[EXECUTED] Only the changed modules and the necessary import gate are checked in this lane. Exact source checks, axiom guards, additive patch and frozen dependency pins are in `MANIFEST.json`; the corresponding logs are under `checks/`. No broad tree rebuild or independent-review campaign is claimed. Main minidregg/breadstuffs and all frozen predecessor packages remain read-only.

[EXECUTED] New web searches: 0. New Scry SQL queries: 0. The construction uses the already inspected sources and proved local interfaces.
