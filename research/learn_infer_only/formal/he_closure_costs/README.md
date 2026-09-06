# Proposed finite-window BFV noise patch

[EXECUTED Lean] Four proposed modules compile with Lean 4.30.0 in the owned
research overlay. Every theorem has an observed `#guard_msgs`-pinned
`#print axioms`; closure is a subset of `propext`, `Classical.choice`,
`Quot.sound`, with no added axioms or `sorry`. Sources, exact commands,
numbered failed/successful logs, hashes, import-boundary result and proposed
patch are retained by `../../experiments/he_closure_costs/window_formal/`.
The companion tree was read only. These are proposed additions, not landed
companion modules or a full companion umbrella-build claim.

[DERIVED scope] This proves finite-list integer error algebra and its
composition with a generic exact-ciphertext queue. It does **not** prove the
Rust implementation, ciphertext confidentiality, restricted release, a PQ
security theorem or cryptographic erasure. The earlier genuine BFV/TFHE runs
and pinned lattice-estimator outputs were not rerun during this tranche.

## Statements and the useful boundary

[EXECUTED Lean] `Theory/IntegerWindowNoise.lean` declares `Row`, `Fresh` and
`WindowCorrectness` before the proofs. For every current row and coordinate,
its explicit premise is

```
phase_j = floor(Q * message_j / t) + error_j,  |error_j| <= E.
```

[DERIVED scope] `Fresh` is an arithmetic phase/error predicate, not a proof of
independent coins or cryptographic freshness. The deterministic support bound
does not need independence; enforcing source issuance is a separate obligation.

[EXECUTED Lean] `floor_scaled_residual` proves the exact equation

```
t * phase_j - Q * message_j = t * error_j - (Q * message_j mod t).
```

For a current list of at most W rows and a fixed public integer query of L1
norm at most L, `list_residual_bound` proves

```
|t * readoutPhase - Q * readoutScore| <= W * L * t * (E + 1).
```

Thus `window_correctness` gives exact decoding modulo t when
`2*t*W*L*(E+1)<Q`. `window_signed_correctness` additionally requires
`2*|readoutScore|<t` and returns the exact signed integer. Both accept any
integer lift `readoutPhase + Q*wrap`; wraparound in the ciphertext modulus
is not silently excluded. The rounding function is exact integer
round-half-up; the strict margin excludes tie ambiguity.

[EXECUTED Lean] `signed_query_split`, `readout_positive_negative_split`, and
`split_queryL1` justify separate nonnegative positive/negative query
polynomials and one subtraction. Their combined L1 norm is L, not 2L.
`floor_encoding_shift` handles alternative message representatives modulo t.
`floor_carry_exact` and `floor_carry_bounds` show precisely why summing floor
encodings differs from encoding the sum: for k nonempty rows the correction
is in `[-(k-1),0]`. No exact-scale `W*E` shortcut is assumed.

[EXECUTED Lean] `signedProductSum_bound` and `public_key_noise_bound` give
`2*N*S^2+S` from two signed convolution expansions with each input factor
bounded by S. The actual negacyclic coefficient expansion is an explicit
premise; the theorem does not inspect Rust polynomial representations.

## Composition with the public ciphertext queue

[EXECUTED Lean] `Theory/CiphertextWindowNoise.lean` imports the durable lane's
`Theory.CiphertextWindow.reachable_queue_sum`. For an arbitrary additive
commutative ciphertext group it obtains the exact current queue sum and
length bound from any valid history. The cipher-to-phase map has type
`Ct ->+ ZMod Q`. No nonzero additive homomorphism from a finite ciphertext
group into the integers is assumed.

[EXECUTED Lean] `PhasePremises` requires (1) each current queue entry's modular
phase to equal the integer row phase modulo Q, and (2) the implementation's
integer readout lift to represent the accumulator's phase. `queue_phase_sum`
then maps the queue group equality; `queue_integer_lift` derives the existence
of an integer wrap. `reachable_decode` and `reachable_signed_decode` compose
this result with the finite-list budget. These theorems contain no elapsed
history length term.

[DERIVED limit] The durable theorem checks a lawful canonical logical codec
and identical expired ciphertext bytes/ID. The pinned Rust protobuf serializer
has representation cases and is not modeled by that codec. Actual Rust/RNS
addition, phase mapping, packed multiplication, coefficient selection and
decode/scaler semantics remain refinement obligations. The `phase` argument
is query-specific and must model the two ct-by-plaintext products and their
subtraction. The theorem does not implement a secret-key phase computation
for the operator or authorize it to reveal anything.

## Actual arithmetic and inhabited premises

[EXECUTED Lean] `Assurance/ResidentBfvWindowNoise.lean` instantiates:

| Quantity | Exact value |
|---|---:|
| N | 4096 |
| Q primes | 2199023190017, 4398046486529 |
| Q product | 9671406214650060397780993 |
| t | 4294828033 |
| width / W | 577 / 128 |
| sampler support S | 20 |
| E = 2*N*S²+S | 3276820 |
| coordinate/query absolute bound | 127 |
| L = 577*127 | 73279 |
| signed score bound W*L*127 | 1191223424 |
| 2*t*W*L*(E+1) | 264008552994527828978432 |

[EXECUTED Lean] The margin is strictly below Q, the score bound is strictly
below t/2, and `2*(width-1)<N`. The latter is the numerical no-negacyclic-wrap
premise for the reversed-query coefficient layout, not a proof of the
packed polynomial implementation itself. `actual_signed_window` proves the
signed claim for **every** row list and query meeting `ActualPremises`.

[EXECUTED Lean] The actual-parameter witness contains 128 rows, each with
message 1 and error 1 in its first coordinate, and query -1 there. Its score
is -128, its error is nonzero, and all actual premises are proved. The fresh
phase equation is inhabited as arithmetic; no claim that this witness is a
representative key sample or encrypted fixture is made.

[EXECUTED Lean] `Assurance/ResidentBfvWindowPhase.lean` separately instantiates
the **queue composition** at Q83 with a nonzero logical `ZMod Q` ciphertext,
a lawful codec reused from `Assurance.CiphertextWindowCell`, a checked
admission, identity modular phase map and the same nonzero row/query. Its
closed `Subject` contains reachability, all phase/source/range premises and
signed output -1. This transparent logical coefficient witness is not BFV
and provides no privacy. It prevents the modular composition premises from
being left uninhabited while keeping the implementation distinction visible.

## Falsifiers

[EXECUTED Lean] At the actual Q83 and t32, both scalar phases 0 and 1 round to
plaintext 0. Expiring a replacement phase 1 where the identical stored phase
was 0 adds debt -1 per turnover. At `floor(Q/(2*t))+1` such substitutions,
`wrong_expiry_actual_misses` proves signed output -1 although the exact current
zero queue's output is 0. This is an algebraic long-history counterexample,
not a newly executed BFV attack. `wrong_expiry_not_exact_queue` shows the
missing invariant directly.

[EXECUTED Lean] The modular witness also constructs a different same-output
phase. `same_plaintext_distinct_phase` proves the output agreement and group
inequality; `different_expiry_bytes_refused` applies the lawful codec and
exact byte check to refuse the substitution. The durable lane separately
has actual logical add/expiry histories and bypassed-check debt examples.

[EXECUTED Lean] Tiny scalar controls show that removing the margin permits
fresh noise to change an output (`omitted_margin_fails`), and that modular
correctness does not imply unbounded signed correctness
(`omitted_signed_range_fails`). These are arithmetic counterexamples.

## Source and implementation obligations

[SOURCE construction, inspected locally] Pinned fhe-dregg source paths are
under `/Users/ember/dev/breadstuffs/vendor/fhe-dregg`. Existing lane manifests
pin the files/build and actual Q83 probe. In `src/bfv/keys/public_key.rs:64-94`,
the public-key encryption phase has the source equation
`floor(Q*m/t)+e*u+e1+e2*s`. `src/bfv/plaintext.rs:51-61` and
`src/bfv/parameters.rs:418-436` supply the encoded scaling. The sampler audit
is in `HE_CLOSURE_COSTS.md` and `estimator/AUDIT.md`: configured variance 10
uses CBD parameter 20, support [-20,20]. These source readings motivate the
Lean hypotheses; source code is not an axiom or a proved implementation.

[OPEN] The exact missing implementation steps are: prove the sampler support
and fresh phase expansion for the pinned code; identify a faithful additive
ciphertext quotient/normalization; prove the chosen signed packed readout's
modular phase map and floor-representation correspondence; prove the scaler
and signed decoder meet the integer equations; connect admissions to honest
source encoding and authenticated ranges; connect the logical codec/expiry
guard to actual serialized ciphertext identity. Hidden release and absence
of read-all authority are separate unsolved requirements. The executed HE
fixtures retain a full test secret key and expose a polynomial to that reader.

[DERIVED consequence] The supported mechanism is a finite window with fresh
issuer-encrypted contributions and identical ciphertext expiry. Its source
of a horizon-independent error bound is exact cancellation plus a bounded
current queue, not low rank, generic continual learning or ciphertext
rerandomization. It stores O(W) ciphertexts and does not erase archived inputs.

## Reproduction and integration

[EXECUTED commands] From `/Users/ember/dev/zkml-research`:

```
python3 research/learn_infer_only/experiments/he_closure_costs/window_formal/check_lean.py
python3 research/learn_infer_only/experiments/he_closure_costs/window_formal/package.py
```

[DERIVED integration requirement] Apply the durable lane's ciphertext-window
patch first (for `Theory.CiphertextWindow` and
`Assurance.CiphertextWindowCell`), then this lane's proposed patch. New modules
are rooted in proposed `Theory.lean` / `Assurance.lean` edits. The package checks
patch applicability against captured current root files in an isolated copy;
it does not change or compile the companion roots. A maintainer must fold
root-import edits with other simultaneous patches and run the full companion
umbrella and boundary gates. No current-truth verdict is edited by this lane.
