# Canonical three-limb projection of the pinned BFV source result

2026-09-06. Research patch for the read-only Minidregg tree. The earlier 27-pin
reference, 33-pin engine model, and 23-pin source certificate remain unchanged.

## Result

[DERIVED, kernel checked] The previously forced integer output modulo Q can now
be tied to a canonical three-element target limb array through existing emitted
constraints. The main theorem is
`Minidregg.Compiler.FheTargetProjection.pinnedTargetCheck_sound` in
`Compiler/FheTargetProjectionVerifier.lean:41`. For every pair of full wire
assignments, a passing composed check implies, for each target index i,

```text
0 ≤ target[i] < qi
target[i] = deployedOutput(sourceResidues) mod qi
```

Target limbs are natural numbers, supplying the lower bound by type. The upper
bound and exact residue equation are supplied by the emitted constraints. The
shared integer output and external target array are explicitly equality checked
at the composition boundary.

[DERIVED, kernel checked] `target_factors` proves the exact factorization

```text
Q = 68719403009 × 68719230977 × 137438822401
  = 649033470896967801447398927572993
```

It also proves positivity, each `qi ∣ Q`, and the three pairwise coprimality facts.
`target_reduce` uses the checked divisor relation and `Int.emod_emod_of_dvd` to
prove `(z mod Q) mod qi = z mod qi` for **every integer z**, including negative
source representatives. No informal CRT convention is used as a proof premise;
an inverse CRT reconstruction theorem is not needed for this direction.

## Emitted relation and composition

[DERIVED, kernel checked] The projection relation has six nonnegative integer
balance rows. For each of the three target primes it requires

```text
Y = qi × quotient[i] + target[i]
target[i] + slack[i] = qi − 1
```

Every target, quotient and slack is represented inside the new descriptor.
Existing radix and carry range gadgets force their integer interpretation. The
second row supplies canonicality; no external assertion of a correct residue,
quotient or range enters the soundness theorem.

[DERIVED, kernel checked] There are ten groups: Y followed by three
target/quotient/slack triples. Each group has nineteen radix-64 digits. Each row
uses two existing `BfvSignedAccumulatorAir.weightedSumGadget` instances sharing
their result digits. They have 26 columns and 14-bit carries. Fixed coefficient
capacities, exact radix linearization, and local field-to-integer no-wrap budgets
are proved through `IntegerCertificateEmission.ranged_weighted_sound`. The
budgets are 770,556 and 1,048,575, below BabyBear's 2,013,265,921 modulus. Generic
`AirSimplify` and existing CSE preserve the relation.

[DERIVED, kernel checked] `pinnedTargetCheck` conjoins the **frozen source
checker**, equality of the target descriptor's decoded Y to that source claim,
equality of decoded target limbs to the external array, and the new existing
descriptor checker. This deliberately preserves the settled source descriptor.
It is a composition of two emitted checks over two full assignments, not a single
merged descriptor or a succinct-proof public-input protocol. The source checker
supplies canonicality of the shared Y modulo Q. The standalone projection
descriptor's soundness does not require an external bound on Y.

## Nonvacuity and falsifiers

[DERIVED, kernel checked] `projection_honest` proves semantic honest acceptance
for every natural Y. `captured_matrix_inhabited` proves the nonzero concrete
matrix witness for Y=172481 and all its group capacities.
`maximum_matrix_inhabited` does the same for Y=Q−1 and proves its three limbs are
`qi−1`. Full emitted-layout completeness is a separate residual.

[DERIVED, kernel checked] `pinned_wrong_target_refused` excludes the external
array `[172480,172481,172481]` for the captured source input and shared Y=172481
for **every source and target wire assignment**. `coherent_boundary_falsifier`
keeps the original accepted source certificate inhabited while proving that no
projection certificate can accept the changed first limb.

[EXECUTED] The retained actual Rust tensor
`N4096_structured_rounding_boundary_0`, component 0, coefficient 0, has target
limbs `[172481,172481,172481]`. Its six input residues equal the frozen source
certificate's captured row. The existing Lean composed checker accepts that
exact source assignment and array. The source fixture is read from the frozen
retained data and is not recomputed or changed during the attacks.

[EXECUTED] The same existing checker refuses three distinct controls:

- A changed external first limb while both internal assignments remain honest.
- A changed internal first limb with an adjusted canonicality slack. All five
  other projection balance rows still hold; only row 0, the first QR equation,
  fails. The source assignment remains accepted.
- A **valid** independent projection of 172480 attached to the accepted source
  result 172481. Each descriptor accepts separately, but the shared-Y equality
  pin refuses their composition.

[EXECUTED] A fourth control at Y=Q−1 adds q0 to the first limb and subtracts one
from its quotient. Its QR equation and all four other limb rows remain valid;
only row 1, the canonicality complement, fails. The emitted checker refuses it.
A radix digit of 64 is also refused. `replay-results.json` retains the precise
violated row sets and checks that the original source assignment still accepts.

[EXECUTED] `prepare_fixtures.py` compares **86,208 retained actual Rust coefficient
rows / 258,432 target limbs** against the deterministic source integer reduced
through Q and each target prime. All agree. Five concrete rounding-boundary rows,
including source integers −169790, −514751, −172480, 172481 and 514752, additionally
pass through the existing emitted **projection** checker and match the actual
retained limb arrays. The complete composed source-plus-target checker is executed
for the captured 172481 row; the other four are projection checks plus the prior
source-model differential evidence. No fresh HE encryption or multiplication was
run in this tranche.

## Cost and validation

[EXECUTED] The side descriptor has 7,282 initial variables, 190 scalar digits,
1,140 scalar bit wires, six balance rows and twelve existing accumulators.
Emission gives 152,276 raw gates. Generic simplification plus CSE gives **28,352
gates**: 13,962 multiplication gates and 14,390 addition gates, with 8,710 zero
assertions and a 39,495 wire header.

[DERIVED] Adding its arithmetic count to the frozen source certificate gives
161,027 gates, 37,576 initial variables and 45,208 zero assertions per scalar.
These sums describe two separate descriptors. External equality checks,
commitments, proof overhead, integer convolution and NTT/provenance checks are
not included. They are not latency estimates. The separate sliding-window core
avoids ciphertext-by-ciphertext multiplication; none of this bill is assigned to
that core's Learn operation.

[EXECUTED] `validation-summary.json` records fresh isolated compilation of ten
dependency modules, five new theorem modules and a side-effect-free `Compiler`
umbrella, followed by the companion import-boundary check and all four BFV patch
application checks. The five new modules have **22 exact axiom pins**, grouped
7+3+6+4+2. There is no `sorry`, custom `axiom`, `native_decide`, or `ofReduceBool`
in the theorem sources. Individual standard axiom reports are in
`axiom-pins.json`; no axiom-free claim is made. Companion trees were not edited,
and no full Minidregg build or whole-array kernel reduction was attempted here.

The frozen patch is `minidregg-fhe-target-projection.patch`, SHA256
`61f35e724f5de29d7338a381232b31e60c36cf39845665f8ac4073f150e0ea97`.
Its dependencies are the preceding source-certificate chain, including existing
`IntegerCertificateEmission` and `AirSimplify`. Exact source hashes are retained
in `validation-summary.json`. The patch contains only the five library modules
and two umbrella imports; the IO runner is separate.

Reproduce kernel/import/patch checks using the read-only companion toolchain:

```sh
cd /Users/ember/dev/minidregg
lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/target_projection/validate.py
```

Extract retained engine rows and the frozen source assignment from the research
root, then run the actual Lean checker:

```sh
python3 research/learn_infer_only/experiments/bfv_lift_refinement/target_projection/prepare_fixtures.py
cd /Users/ember/dev/minidregg
lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/target_projection/build.py FheTargetProjection FheTargetProjectionLayout FheTargetProjectionEmit FheTargetProjectionVerifier FheTargetProjectionWitness FheTargetProjectionChecks
```

The lightweight descriptor replay, from the research root, is:

```sh
python3 research/learn_infer_only/experiments/bfv_lift_refinement/target_projection/replay_projection.py
```

[EXECUTED] Compact gzip fixtures, exact uncompressed payload hashes, checked
source hashes and derived cost sums are pinned in
`experiments/bfv_lift_refinement/target_projection/manifest.json`. This tranche
used zero metered searches and zero PDF downloads.

## Remaining scope

[OPEN] The target-array **mathematical projection** boundary is now constrained.
The actual Rust modular/Shoup operations still need a source-to-semantics
refinement theorem. The previous exact word model and actual coefficient replay
remain the stated bridge to the implementation; this new patch does not prove
Rust arithmetic semantics.

[OPEN] Source residue provenance from committed ciphertexts, extension,
integer convolution/NTT, and an end-to-end multiplication controller remain
separate. The two full-assignment checks also need explicit authentication of
the same equalities in a proof protocol. Neither a proof-carrying ciphertext
format nor private release is provided.

[OPEN] Universal semantic honest acceptance and two concrete bounded matrix
witnesses are kernel checked. The full emitted witness acceptance is executed,
and universal completeness of the finite emitted layout remains unproved. A
compositional completeness proof using existing range/weighted constructors is
preferable to reducing a giant checker in the kernel.

[OPEN] Individual group widths and fixed-zero columns can reduce the conservative
cost. There is no master-read absence, secrecy, relinearization, noise, or runtime
claim in this artifact.
