# Finite prefix-adaptive arity-eight supplied soundness

[DERIVED] `ArityEight.Schedule.sound` composes an arbitrary finite number `m` of actual arity-eight transitions on an existing `FoldingTower ... (3*m)`. `supplied_sound` connects this theorem to the existing deterministic checkpoint extractor and actual supplied scalar Merkle paths:

```
Pr[supplied acceptance and terminal RS membership]
 <= sum(j < m, 8 * n_(3*j+3) / |F|)
    + (1-tau)^q + Pr[observed Failure].
```

[DERIVED] The transition errors are derived from the frozen one-scalar degree-eight folding theorem. The middle words need not be far as a strategy premise, and no global acceptance bound is assumed. Every external round uses a fresh scalar; its internal `beta, beta^2, beta^4` remain correlated. There is one shared coherent query vector, with replacement, and one query tail.

## Construction and exact premises

[DERIVED] `Words.word n` takes a `Fin n → F` prefix and returns the word at the existing binary level `3*n`. `Words.input n` takes the same prefix and returns the input at level `3*(n+1)`. Thus the next commitment may depend on the current scalar, while the source and injected input are fixed before that scalar. Neither function receives the query vector.

[DERIVED] The caller supplies a degree schedule and radii satisfying, for every `j : Fin m`,

```
degree(j) = 8*degree(j+1),   degree(j+1) >= 1,
0 < radius(j),
degree(j+1) < (1-2*radius(j))*n_(3*j+3),
radius(j+1) + tau <= radius(j).
```

[DERIVED] The remaining premises are `3*m <= ell`, `tau <= 1`, nonnegative terminal radius, and initial-word farness at `radius(0)`. The finite theorem also permits `m=0`; in that case initial farness and terminal membership cannot both hold. It introduces no field/cardinality assumptions beyond those of the existing finite-field folding theorem.

[DERIVED] `prefix_challenge_bound` is a reusable probability lemma. It uses the existing `splitCoord` equivalence to expose one fresh coordinate and proves that `friPrefix` is unchanged by that coordinate. A per-prefix scalar bound therefore holds for the full challenge tuple. `bad_round_bound` applies the frozen `fold8_injected_uniform_sound` to the actual prefix-selected source and input. `bad_schedule_bound` sums these bounds using the existing finite union theorem; it retains each shrinking domain size separately.

[DERIVED] `earliest_transition_cover` is an induction: outside the explicit bad-round union, farness persists as long as every claimed next word is closer than `tau` to its literal fold. The triangle inequality and radius gaps preserve the invariant. Terminal RS membership contradicts this invariant, so some actual transition must be `tau`-far. `coherent_query_bound` selects such a transition after the challenge tuple is fixed, then uses `powerTwoCoherentRound_uniform_le` at binary index `3*j+2`. No independence between different rounds' projected query rows is assumed or needed.

## Supplied openings and observed logs

[DERIVED] `Checkpoints` has the same prefix types as `Words`. Each entry contains its actual finite log and root. `extracted` calls the existing `EfficientRootOpening.word`, with the exact depth `ell-3*n` or `ell-3*(n+1)`; no parallel commitment or RS semantics are introduced.

[DERIVED] Each round authenticates the frozen `RowVerified`: eight source paths, one injected-input path, one next-word path and the literal fold equation. `supplied_cover` applies the frozen `supplied_row_pins` to every round. The next checkpoint of round `j` is exactly the source checkpoint of round `j+1` at the same prefix.

[DERIVED] The execution log and submitted openings may depend on all external challenges and query seeds. `CheckpointsLogged` requires all used checkpoints to be included in that log; `OpeningsLogged` requires the hash-call records of the actually supplied paths. `Failure` is the finite union of the existing observed `RoundBad` events at those roots. `supplied_sound` retains the probability of this union once.

[OPEN] This finite-log residual is unpriced. The theorem does not establish an efficient collision advantage, fresh-challenge runtime implementation, Fiat–Shamir/ROM/QROM composition, or actual transcript/log completeness. Supplied paths are scalar `BinaryMerkle` openings; no packed-MMCS or Rust verifier equivalence is claimed.

## Five actual BabyBear rounds

[DERIVED] `ArityEightScheduleBabyBear.firstFifteen` projects the first fifteen transition objects from the frozen certified BabyBearExt4 tower. The exact domain and transition equalities are proved; the field carrier and primitive-root facts are inherited unchanged.

```
external levels: 0 → 3 → 6 → 9 → 12 → 15
point counts:    2^20 → 2^17 → 2^14 → 2^11 → 2^8 → 2^5
RS degrees:     2^19 → 2^16 → 2^13 → 2^10 → 2^7 → 2^4
radii:          5/25 → 4/25 → 3/25 → 2/25 → 1/25 → 0
tau:            1/25
```

[DERIVED] The five-round `terminal_sound` and `supplied_terminal_sound` discharge every degree, rate, radius, tower and field-cardinality condition. Existing `2/5` source farness implies the needed `1/5` farness. The resulting bound is

```
(2^20+2^17+2^14+2^11+2^8) / 2013265921^4
  + (24/25)^q + Pr[observed Failure],
```

where the word-only theorem omits the log residual. The numerator is exactly `1198336` by integer addition. The terminal check is RS membership at degree below sixteen; connecting this to the runtime's transparent-final-polynomial branch remains a caller boundary. This package adds no security-bit budget or ErrorBudget change.

## Inhabitation and falsifier

[DERIVED] The concrete witness uses this same full-size, five-round BabyBear tower. The source is the existing provably far `X^(2^19)` word. Four exact arity-eight transitions reduce its exponent successively; the fifth claimed word is the legal constant one. Every external challenge tuple accepts an all-zero shared query vector. Query seed one detects the terminal substitution because the literal terminal monomial takes value minus one there. This is an actual-field witness and falsifier, proved symbolically without finite field enumeration.

[DERIVED] A separate supplied-log witness reuses the frozen tree-valued toy hash and generic honest-path log lemmas. Its checkpoint contains the honest opening records for the six words and five zero injected inputs. Structural proofs establish log validity, no observed collision/late hit, exact extraction, source farness, supplied-path inclusion and acceptance. The whole finite supplied theorem fires with a zero residual. This symbolic complete checkpoint is a premise-inhabitation artifact; it is not materialized, benchmarked or claimed as an efficient runtime strategy. The toy hash is not a cryptographic compression claim.

[SOURCE] The predecessor source pins are retained in `MANIFEST.json`: p3 `two_adic_pcs.rs:284–334` computes internal powers, and `prover.rs:237–245` / `verifier.rs:469–479` add matching-height inputs with `beta^arity`. This package inherits those arithmetic/timing interfaces, without claiming that the full Rust execution is now formalized.

[EXECUTED] Validation consists of the five changed-module Lean checks, exact theorem axiom guards, the required import gate and additive patch replay; see `MANIFEST.json` and `checks/`. All one/two-round, curve, carrier, tower and extraction predecessors remain unchanged. No broad build, new independent-review queue, web search or Scry SQL query is part of this lane.

[EXECUTED] `arity-eight-finite-schedule.patch` adds only the five new modules. Apply it after the selected frozen one/two-round and algebraic/carrier dependencies; `DEPENDENCIES.json` identifies the exact source bytes and `integration_entry.json` provides the incremental integration entry.
