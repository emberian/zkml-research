# Actual BabyBear multiplicative tower for the full-UD sampled consumer

[EXECUTED] This package constructs an actual
`FoldingTower BabyBearExt4.Ext4 (PowerTwoFriLevels 20) 19` and supplies it to
`fullUDSampling_babyBear_55`. Its initial domain has `2^20` nonzero points; after
19 binary folds the domain has two points and the permitted polynomial degree
is below one. No tower, primitive-root or characteristic premise remains in
`MultiplicativeTower.coherent_sound`; the binding scheme, transcript and that
transcript's initial farness remain explicit.

[EXECUTED] The package also proves those ideal-model premises are jointly
inhabited at the actual dimensions. A degree-exactly-`2^19` source word is
`2/5`-far, an explicit strategy has accepting all-zero query seeds, and query
index one rejects the first round. `witnessed_sound` applies the existing bound
to this fully instantiated ideal strategy, using the frozen
`../full_ud_sampling_budget/FullUDSamplingBudget.lean:333`,
`fullUDSampling_babyBear_55`. This is a theorem about the existing
finite uniform challenge/query experiment, not a deployed Fiat–Shamir claim.

## Certified source root

[SOURCE] `/Users/ember/dev/minidregg/prover/src/babybear.rs:3–13` fixes modulus
`2013265921`, two-adicity 27 and root `440564289`. Its `two_adic_generator` at
line 60 repeatedly squares that root to the requested size; the test at line 75
checks `31^15` against it. The active p3 source is the Cargo-pinned checkout
`/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/baby-bear/src/baby_bear.rs:42–50`.
Its root table gives the same maximal root `0x1a427a41` and the 20-bit root
`0x0ba067a3`. Exact file hashes are in `source-evidence.json`.

[EXECUTED] `BabyBearTwoAdic.lean`’s `TwoAdic.GeneratorContract` is statement-first.
`generator_source_value`, `generator_half_order` and `generator_full_order`
certify `440564289 = 31^15`, `g^(2^26) = -1` and `g^(2^27) = 1` inside the
existing `BabyBear := ZMod modulus`. The last two use the already-existing
`BabyBearExt4.squareN` and its power theorem: 26 squarings followed by one more,
with ordinary Lean kernel computation. There is no field enumeration,
`native_decide`, external arithmetic oracle or generator-label assumption.
Mathlib’s `GroupTheory/OrderOfElement.lean:529`,
`orderOf_eq_prime_pow`, yields exact order `2^27`.

[EXECUTED] The proved injective algebra embedding maps that root into the actual
`AdjoinRoot (X^4−11)` extension. Power descent gives exact order `2^bits` for
every supported bit size. `omega20_source_value` proves the actual extension
root is the image of `195061667`, matching the source table. Squaring the maximal
root is a checked falsifier for the false claim that its order stays `2^27`.

[SOURCE] Existing `/Users/ember/dev/minidregg/Selvage/BabyBearExt4.lean:43–59`
supplies the certified repeated-squaring method; its field is the already-proved
quartic carrier at line 131. No parallel field or polynomial quotient is added.
A local `rg` search for `IsPrimitiveRoot|440564289` in the current main Lean
files, under ordinary ignore rules, found no prior root theorem; the instrument
and scope are recorded in `source-evidence.json`.

## Existing domains, fibres and sampler

[EXECUTED] `PowerTwoRootFolding` constructs the existing `FoldingData` and
`FoldingTower` structures; it does not introduce parallel folding or RS semantics.
For an initial root g of exact order `2^ell`, level n is the existing
`PowerTwoFriLevels ell n`, embedded by

```
i ↦ (g^(2^n))^i.
```

[EXECUTED] Primitive-root power injectivity proves each embedding injective.
Every point is nonzero. The next level root is the current root squared, and
its exact size halves. Squaring sends an exponent to its remainder modulo the
next size. The section chooses that exponent in the first half; negation adds
half the current size modulo the current size. A half-turn is proved to be -1,
and characteristic-two exclusion is proved through the actual field embedding.
These are exactly the laws consumed by the existing `FoldingData` record.

[EXECUTED] `TowerContract` is stated before the generic proof work and fixes
the natural-power domain values and the modulo square indices.
`negative_section` and `fold_pair` expose the actual pair of indices
`k` and `k + halfSize`, with denominator `2*gLevel^k`.
`coherent_index_powers` ties the already-existing `powerTwoRoundIndex` to the
geometric path: the selected point at round j is the initial pair-domain point
raised to `2^j`. Thus the model's coherent index map is a proved squaring path.

[EXECUTED] `BabyBearFoldingTower` instantiates this construction at the certified
20-bit root, 19 rounds and actual Ext4 carrier. `domain_source` proves every
supported level uses the corresponding source root. The initial point at index
zero is 1; `consecutive_domain_falsifier` proves this differs from the earlier
consecutive-subfield witness's zero point. The earlier witness was never used as
a multiplicative folding domain.

## Actual farness and nonvacuity

[EXECUTED] `farWord` evaluates `X^(2^19)` on the new actual initial domain.
It is outside the degree-below-`2^19` RS code, by the existing polynomial root
count bound. It lies in the next larger degree window. Applying the existing
RS minimum-distance theorem
(`/Users/ember/dev/minidregg/Selvage/ReedSolomon.lean:149`,
`reedSolomonCode_minDist`) in that larger window proves its distance from
every permitted source word is at least `1/2`, hence greater than `2/5`.
No enumeration of the million-point domain occurs.

[EXECUTED] `tower_and_farness_inhabited` jointly exhibits the actual tower and
this actual far word. `source_degree_falsifier` shows why the degree boundary
matters: increasing it to `2^19+1` makes the same word a codeword and therefore
close. This farness witness does not prove farness for an arbitrary runtime input.

[EXECUTED] `BabyBearFoldingWitnesses` uses the existing ideal binding commitment.
Its initial word is `farWord`; each later selected word is constant 1.
The first fold is independent of the challenge because the source degree is even.
At query zero it is 1; at query one it is -1. The later constant words fold to
constant 1. Consequently all-zero coherent query seeds accept for every
challenge vector and every query count, while a one-query batch at index one
rejects the first round. The actual acceptance event has positive finite
probability. `consumer_inhabited` and `witnessed_sound` therefore realize an
inhabited instance of the existing 3603-query bound on the actual carrier.

[EXECUTED] The resulting numerical upper bound is the frozen schedule's
`2^-55` ideal challenge/query bound. No query arithmetic, security budget or
protocol parameter was changed. The exported external-transcript theorem still
retains binding, transcript and initial-farness premises visibly.

## Source-to-model boundary

[SOURCE] The current minidregg scalar fold at
`prover/src/mle_kernels.rs:407–438` pairs natural-order positions `index` and
`half + index`, with inverse-root twiddle at lines 565–572. Its evaluation helper
at line 650 uses ascending generator powers. This matches the proved index
convention, but that implementation helper uses Ext6; this package does not
assert an Ext6/Ext4 execution equivalence.

[SOURCE] Active vendored p3 `src/two_adic_pcs.rs:230–278` uses bit-reversed
subgroup points and adjacent evaluation rows; `src/prover.rs:214` describes
adjacent conjugates. The verifier shifts row indices right during folding.
The formal natural-order representation pairs opposite halves and projects by
modulo. A bit-reversal transport is still needed to identify those actual arrays.

[SOURCE] The outer PCS path describes evaluations on the coset
`Val::GENERATOR * H` at `two_adic_pcs.rs:626–677`, while the inner FRI fold
constructs points from unshifted two-adic roots at lines 243 and 270. Our tower
is the unshifted subgroup. The polynomial-variable/coset pullback and initial
PCS-to-FRI interpretation remain an explicit execution obligation.

[SOURCE] `src/prover.rs:238–245` may inject the next-height input multiplied by
`beta^arity`; the source also permits variable arity and extra query-index bits.
The current theorem is a fixed 19-round binary fold tower. Its field, domains,
negation/squaring and ideal sampled soundness are proved; batching injection,
arity selection, row/MMCS authentication and query-index decoding are not
silently identified with that theorem.

[OPEN] Remaining deployment work: those layout/coset/batching adapters, the
actual input-farness reduction, concrete commitment binding, and
Fiat–Shamir/challenger/proof-of-work composition. The frozen timing package's
semantic arbitrary-root reduction can consume this tower but still does not
price efficient collision extraction. No extra security bits follow from
constructing this domain.

[EXECUTED] Exact source, patch, checks, theorem/pin census and integration entry
are packaged here. Root owns the whole umbrella integration and independent
review. Companion trees and frozen predecessor artifacts were read-only. This
follow-on used zero web queries and zero Scry SQL.
