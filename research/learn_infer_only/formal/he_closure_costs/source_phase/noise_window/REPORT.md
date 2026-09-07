# Supported BFV source noise and the 32-entry window

[EXECUTED] These two successor modules now compile with **34 pinned theorem
axiom checks** (13 Theory, 21 Assurance). They repair the interrupted successors
described in the parent directory's older README. The frozen source-phase
45-pin modules and window 62-pin modules are unchanged. The new additive patch
is `minidregg-bfv-source-window.patch`; exact hashes, commands, captured output,
prerequisites and the import-boundary inventory are in `validation.json` and
`artifact_manifest.json` beside this report. This package has not itself run
the swarm's combined umbrella build.

[DERIVED, Lean-proved] The new result closes a source-equation premise: from
bounded integer coefficients for the secret and encryption factors, it derives
the integer lift and bound of the actual **mathematical negacyclic product**.
It then constructs the source encryption, its phase homomorphism and packed
readout, and proves exact signed decoding of a current list of at most 32 such
inputs at the concrete Q83 parameters. This is an algebraic theorem about a
specified source constructor, not a Rust implementation theorem.

## Contract and proof path

[DERIVED, Lean-proved] In the ring `(ZMod Q)[X]/(X^N+1)`, the literal equations
represented by the frozen core are

```text
pk = (e - a*s, a)
c  = (u*pk.0 + e1 + encoded(message), u*pk.1 + e2)
phase_s(c) = c.0 + c.1*s
           = encoded(message) + u*e + e1 + e2*s.
```

[DERIVED, Lean-proved] `BfvNoiseSource.convolution` uses a negative sign on
wrapped products. `pack_convolution_quotient` proves its relationship to ring
multiplication. `noise_coefficient_lift` (Theory source line 132) consequently
derives the coefficient lift

```text
nu[k] = convolution(u,e)[k] + e1[k] + convolution(e2,s)[k].
```

There is no assumed additive phase homomorphism or assumed polynomial-product
coefficient equality in the new source-to-window theorem. The homomorphism is
constructed in the frozen core and the latter equality is proved here.

[DERIVED, Lean-proved] If every coefficient of `s,e,u,e1,e2` has absolute value
at most `S >= 0`, `supported_noise_lift` (Theory line 168) supplies both the
modular phase equality and `|nu[k]| <= 2*N*S^2 + S`. This uses the existing
finite signed-product bound from `Theory.IntegerWindowNoise`. Independence of
the factors is unnecessary for this deterministic bound.

[DERIVED, Lean-proved] `Assurance.ResidentBfvSourceWindow` defines the source
input contract at line 30, the statement-first 32-entry target at line 58,
`input_fresh` at line 73, `input_phase` at line 80, and
`source_window32_correctness` at line 132. Its premises are:

- all 4,096 coefficients of the shared secret `s` and public-key error `e`, and
  each input's `u,e1,e2`, lie in `[-20,20]`;
- each input message's queried prefix of 577 coefficients lies in `[-127,127]`;
- the public signed query has 577 coefficients in `[-127,127]`;
- the current source-input list has length at most 32.

[DERIVED, Lean-proved] The accumulator is the exact sum of ciphertexts
constructed from that list with the same key. The reversed query is read at
coefficient 576; the frozen core proves that wrapped cross-coefficients do not
alias into this selected coefficient. Source scaling uses the proven identity
`encoded(m) = floor(Q*m/t) mod Q`, including its floor correction. It uses the
concrete inverse `delta*(-t)=1 mod Q`, proved in the frozen 45-pin core.

[DERIVED, Lean-proved] `output_lift_exists` (Assurance line 98) derives the
integer phase up to a multiple of Q from the canonical modular phase. Applying
the existing signed rounding theorem then gives

```text
centered_t(round_half_up(t * phase / Q))
    = sum_{input in current_list} sum_j query[j] * input.message[j].
```

[DERIVED] `outputLift` is a mathematical secret-key phase followed by canonical
representative selection. It is not an evaluator-visible scalar-release API.
The signed-query ring equation corresponds to the frozen positive/negative
plaintext-product subtraction identity; this successor does not refine Rust
plaintext construction or the returned scaler bytes.

## Concrete arithmetic and nonvacuity

[DERIVED, Lean-proved] The parameters and bounds are inherited from the frozen
Q83 witness and checked by `margin32` and `exact32_budgets`:

| Quantity | Exact value |
|---|---:|
| N | 4,096 |
| Q | 9,671,406,214,650,060,397,780,993 |
| Q factors | 2,199,023,190,017 × 4,398,046,486,529 |
| t | 4,294,828,033 |
| source coefficient support S | 20 |
| E = 2 N S² + S | 3,276,820 |
| query L1 bound, 577 × 127 | 73,279 |
| W | 32 |
| signed-score magnitude bound, W × 577 × 127² | 297,805,856 |
| sufficient noise expression, 2 t W L1 (E+1) | 66,002,138,248,631,957,244,608 |

[DERIVED, Lean-proved] The final expression is strictly below Q and twice the
score bound is strictly below t. The proof uses the 32-entry margin directly;
it also preserves a separately stated 128-entry result. Neither margin has an
elapsed-history factor once the exact current list is given.

[DERIVED, Lean-proved] `window32_nonzero_subject` (Assurance line 204) supplies
all premises with 32 copies of a message consisting of ones, all source small
factors and the shared secret/error equal to 20, public `a=7`, and a query
equal to -1 at its first coordinate and zero elsewhere. The decoded score is
-32. `window32_ciphertext_nonzero` (line 215) proves that the resulting
ciphertext accumulator is nonzero. This is an arithmetic premise inhabitant
at the support edge, not a typical sampled key or a security experiment.

[DERIVED, Lean-proved] The falsifiers are concrete:

- `oversized_message_refused` (line 225): changing the message to 128 violates
  the declared input range.
- `actual_fresh_bound_attained` (line 239): the all-20 vectors attain exactly
  3,276,820 at noise coefficient 4,095.
- `smaller_global_noise_bound_fails` (line 248): reducing that uniform bound
  by one is false for the admitted coefficient-support contract.
- `cyclic_sign_is_false` (line 255): for N=2, multiplying the degree-one basis
  element by itself has constant coefficient -1, exposing loss of the
  negacyclic wrap sign.

## Source provenance and remaining boundaries

[SOURCE, code and proof inspection] `source_register.json` preserves the
previously inspected Rust spans and verifies their full-file hashes. Relevant
absolute sources are:

- `/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/keys/public_key.rs`,
  lines 24–36 and 46–102: public-key construction and encryption equations;
- the adjacent `keys/secret_key.rs`, lines 40–52, 101–145 and 198–262:
  sampler call, secret encryption equation and phase/scaler path;
- `plaintext.rs`, lines 51–64, and `parameters.rs`, lines 417–447:
  plaintext conversion, inverse scaling and RNS parameter construction;
- `ops/mod.rs`, lines 15–68, 110–164 and 229–246: ciphertext addition,
  subtraction and plaintext multiplication;
- `/Users/ember/dev/breadstuffs/metatheory/Bfv/Ring.lean`, lines 110–235:
  the pre-existing integer negacyclic convolution and quotient expansion
  proof adapted here to the modular ring.

[OPEN] The theorem assumes bounded integer source witnesses; it does not prove
the Rust sampler supplies them, or prove the correspondence of Rust arrays,
RNS limbs, NTT operations, parameter objects, serialization and this quotient
ring. The source constructor represents a fixed common level; the public-key
level-switch branch is outside this model. The exact round-half-up theorem
does not establish that the implementation's approximate scaler returns the
same bytes in every case.

[OPEN] This module constructs a sum from a source-input list. It does not add
a new theorem connecting arbitrary admitted bytes to `Allowed` source
witnesses, or install those witnesses in the durable journal. The existing
durable queue theorem establishes an exact sum of retained ciphertexts and
identical-object expiry; substituting source-created ciphertexts requires the
same input provenance. A syntactic admission predicate cannot supply it.
Wrong-expiry debt and re-encrypted-expiry counterexamples remain in the frozen
window artifacts; this successor does not replace them.

[OPEN] Confidentiality, restricted release, master-read absence, fork control
and post-quantum security do not follow from these algebraic results. No new
encrypted experiments, estimator runs, timing claims or security-bit estimates
were made during this repair. No new metered search calls were made.

## Reproduction and handoff

[EXECUTED] From `/Users/ember/dev/zkml-research`:

```sh
python3 research/learn_infer_only/experiments/he_closure_costs/source_phase/check_lean.py Theory/BfvNoiseSource Assurance/ResidentBfvSourceWindow
python3 research/learn_infer_only/formal/he_closure_costs/source_phase/noise_window/package.py
```

[EXECUTED] The 34 guards pin observed axiom closures, each a subset of
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or new
axiom declaration. `pin_axioms.py` records the one-time pinning procedure and
refuses to overwrite existing pins. Failed repair elaborations remain in the
existing numbered log history.

[EXECUTED] Packaging applies only these two new modules and their two umbrella
imports in an ignored local copy. The exact read-only companion boundary
script scans the current companion Theory/Selvage sources, relevant frozen
Theory dependencies, and the new Theory source. It never writes into the
companion. The patch is additive to the frozen source-phase 45-pin and window
62-pin patches; the complete window patch also retains its durable 44-pin and
earlier durable dependencies. The root integration lane owns the combined
674-to-708 check and shared status update.
