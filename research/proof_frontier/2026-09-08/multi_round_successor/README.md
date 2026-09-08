# Two actual arity-eight rounds with extracted supplied openings

[DERIVED] This successor composes **two external arity-eight transitions** into terminal-codeword soundness. It reuses the frozen one-round fold/curve and supplied-opening theorems unchanged, the existing `FoldingTower` objects, and the existing coherent sampler. The conclusion sums the two fresh-challenge errors and pays **one** sampling tail:

```
Pr[supplied two-round acceptance with terminal RS membership]
 <= (8*n3 + 8*n6)/|F| + (1-tau)^q + Pr[observed Failure].
```

[DERIVED] Here `n3` and `n6` are the existing tower-domain sizes at levels 3 and 6. Each external round uses its own fresh scalar and the internal powers `beta, beta^2, beta^4`. The theorem never treats those three powers as independent random challenges.

## The composed statement

[DERIVED] `ArityEight.TwoRound.Words` in `ArityEightTwoRound.lean` contains an initial source and first injected input fixed before the challenge pair, a middle word and second injected input that may depend on the first scalar, and a final word that may depend on both scalars. None has a query-seed argument. This records the actual prefix dependence without requiring the middle word to be far as an adversarial-strategy premise.

[DERIVED] The degree schedule is `64*d → 8*d → d`, where `d>=1`. For positive radii `rho0,rho1` the hypotheses are

```
8*d < (1-2*rho0)*n3,
d   < (1-2*rho1)*n6,
rho1+tau <= rho0,   tau <= rho1,   tau <= 1,
source is not rho0-close to the source RS code.
```

[DERIVED] `bad_challenge_bound` proves the first challenge bound from source farness. It proves the second bound separately at each first-challenge prefix, using the frozen `fold8_injected_uniform_sound`. That second exceptional event includes the condition that its prefix-selected source is far; a close middle word is handled by the first transition instead.

[DERIVED] `earliest_transition_cover` proves that, off those two explicit challenge events, terminal RS membership forces at least one actual claimed transition to differ from its literal fold by at least `tau`. It derives this from the triangle inequality and radius gaps. It does not assume the desired global event bound.

[DERIVED] `coherent_query_bound` selects that transition after the challenge pair is fixed. The existing exact coherent marginal then supplies `(1-tau)^q`. Both rounds use the same vector of uniform first-pair seeds with replacement; their projected rows need not be independent. `sound` combines these arguments into the two-round word-level terminal bound.

## Supplied paths and extraction

[DERIVED] `ArityEight.TwoRound.Checkpoints` in `ArityEightTwoRoundSupplied.lean` records five actual log/root checkpoints with the same permitted prefix dependence: source, first input, middle, second input, final. `extracted` uses the existing deterministic `EfficientRootOpening.word` at levels 0, 3 and 6.

[DERIVED] `SuppliedAccepts` retains both rounds' actual supplied row openings and the final extracted word's RS membership. Each round uses the frozen `RowVerified`, which authenticates eight scalar source paths, one input path and one next-word path before checking the literal fold equation. `supplied_cover` applies the frozen `supplied_row_pins` twice. In particular, the first round's next word and the second round's source are the **same extracted middle checkpoint**.

[DERIVED] `supplied_sound` adds the observed `Failure` event to the proved word-level bound. This event is the union of the frozen round failures at the actual checkpoint roots: observed typed-query response collisions or late-target hits. Logs and supplied paths may depend on both challenges and the query vector. The premises require that each relevant checkpoint and every supplied opening's hash-call records occur in the execution log.

[OPEN] The observed log event is unpriced. This is not an efficient collision-advantage or ROM bound, and it does not prove a runtime's checkpoint/log completeness or fresh-challenge implementation. Uniform independent **external** scalars are the experiment being proved. No Fiat–Shamir or QROM price is introduced.

## Actual parameter specialization

[DERIVED] `ArityEight.TwoRound.BabyBear.firstSix` in `ArityEightTwoRoundBabyBear.lean` projects the first six transitions of the already certified BabyBearExt4 tower. `firstSix_domains` and `firstSix_transitions` prove the exact existing objects are retained. No root, domain or field assumption is added.

[DERIVED] `terminal_sound` and `supplied_terminal_sound` discharge all carrier, rate, degree and radius arithmetic for

```
source: 2^20 points, degree below 2^19;
middle: 2^17 points, degree below 2^16;
final:  2^14 points, degree below 2^13;
source farness: 2/5;
proof radii: 1/5 → 1/10 → 0;
tau = 1/10;
challenge/query bound:
  (2^20+2^17)/2013265921^4 + (9/10)^q.
```

[DERIVED] The supplied version additionally has `Pr[Failure]`. This is a concrete two-round terminal-codeword theorem, not a newly claimed whole deployed FRI or security-bit budget. The final RS membership condition must be realized by the caller's terminal check; this package does not establish equivalence to p3's transparent-final-polynomial branch.

[SOURCE] The existing coherent API is `Selvage/HalfThresholdFriCoherent.lean`: `powerTwoCoherentRound`, `powerTwoCoherentRound_uniform_le`, and `uniformProb_prod_snd`. This package projects its shared seed vector at binary indices 2 and 5, corresponding to the two arity-eight outputs. The frozen `P3FriQueryTransport.existing_coherent_transport` separately identifies these projected natural-domain rows with bit reversal after division by 8 or 64. No packed-MMCS or Rust execution equivalence is asserted here.

[SOURCE] The active p3 arithmetic and timing inspected by the predecessor remain the construction reference: `two_adic_pcs.rs:284–334` uses squared internal challenges; `prover.rs:237–245` / `verifier.rs:469–479` add matching-height inputs with `beta^arity`. Their source pins, predecessor patches and new source dependencies are retained in `MANIFEST.json`.

## Inhabitation and falsifiers

[DERIVED] The small witness is an actual BabyBearExt4 schedule `128→16→2`, with degrees `64→8→1`, using the existing certified 128th root. Its initial `X^64` word is provably far by existing RS minimum distance. The first literal block is `X^8`; the second is the terminal-domain coordinate plus its injected term.

[DERIVED] In the adaptive word witness, the second injected word is the constant equal to the first scalar, and the final word is the constant `1 + beta1^8*beta0`. `second_input_not_fixed` proves the injected word really changes with the prefix. Both rounds accept zero coherent seeds for every challenge pair; seed one rejects the second round. `sound_fires` applies the complete theorem with all degree, radius, rate and farness premises discharged, giving `144/p^4+(9/10)^q`.

[DERIVED] A separate supplied-path witness uses fixed zero input injections and an explicit tree-valued toy digest. Its finite checkpoint contains the honest logs for the actual source, middle, input and final words. Log consistency and absence of observed failure are proved structurally, without enumerating the field. The checkpoint extractor equals those honest words; the extracted source is far; every supplied path is retained; both supplied rounds accept zero coherent seeds. `supplied_bound_fires` applies the full raw theorem with a zero observed-failure term. This toy digest is a nonvacuity witness, not a cryptographic-hash claim.

[EXECUTED] Validation is limited to exact changed-module Lean checks with all theorem declarations axiom-pinned, the required import gate, and additive patch replay. See `MANIFEST.json` and `checks/`. No main-tree mutation, broad rebuild, new independent-review queue, ErrorBudget change, web query or Scry SQL query is part of this lane.
