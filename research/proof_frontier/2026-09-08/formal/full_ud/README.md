# Full unique-decoding port over the existing RS code

[EXECUTED] The isolated Lean artifact proves the full conservative
unique-decoding core and feeds it to the existing proximity-generator,
mutual-agreement, FRI fold, half-threshold tower and whole-opening committed
consumer types. The work is a patch for minidregg; its main checkout was not
edited. Base commit: `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`.

## Exact result

[EXECUTED] `Selvage/FullUDCore.lean`, `fullUDCardCore`, proves:

```text
1 ≤ d, 2e+d ≤ n, and >n scalar folds f₀+z·f₁ each within e Hamming errors
of the existing reedSolomonCode dom d
  ⇒ ∃ S, n−e ≤ |S| and both input words agree with RS codewords on S.
```

[EXECUTED] No finite-field assumption is required by the integer core: `F`
is an arbitrary field, the index type is finite, and the good scalars are an
explicit finite set. The field and index universes are polymorphic. No new
RS, distance, correlated-agreement, or folding semantics are introduced.

[EXECUTED] `Selvage/ProximityGapFullUD.lean` exports
`reedSolomonCode_isProximityGenerator_fullUD`,
`hasMutualCorrelatedAgreement_fullUD`, and `foldDistancePreserving_fullUD`.
For positive code dimension and nonempty domains, the open radius is
`0 < δ < (1−d/n)/2`; the error remains `n/|F|`.

[EXECUTED] `Selvage/FullUDFriConsumer.lean` directly reuses the existing
`FoldDistancePreserving`, `FoldingTower`, `acceptSet`,
`FriCommittedStatement`, `friCommittedAcceptSet`, and binding reduction.
The exported tower/committed heads retain the numerator
`m*n₀*|F|^(m−1)`. Positive tail dimensions are explicit premises.
The rate-half specialization `proximity_sound_rateHalf_twoFifths_fullUD`
checks initial distance `2/5`, followed by tail distance `1/5`; the latter
is below the new `1/4` threshold and above the old `1/6` threshold.

## Nonvacuity and teeth

[EXECUTED] `FullUDStatement` was written and checked before the proof: its
`FullUDPremise` is inhabited on eight points over `ZMod 11`, degree bound
four and integer radius two. The field is a parameter in the actual theorem;
these witness types are explicitly toys, not deployment surrogates.

[EXECUTED] `FullUDWitnesses.good_line_CA_fullUD` fires the proved generator
at relative radius `1/5` and rate one half. Its closeness probability is one,
strictly above `8/11`. `old_band_rejects_fullUD_witness` proves that this same
site fails the former radius premise.

[EXECUTED] `FullUDTeeth.radius_hypothesis_necessary` proves a falsifier for
omitting the radius premise: on six points over `ZMod 7`, degree bound two
and radius three, all seven scalar folds are close, but no three-position
common agreement set exists. The finite enumeration uses `decide +kernel`;
no native-decide trust shortcut appears.

## Proof closure and source distinction

[SOURCE] Adapted polynomial-matrix and BW arguments come from ArkLib commit
`22dbd4e836c15a21f68889afa69b7130da04abbb`, files
`AffineLines/BWMatrix.lean`, `GoodCoeffs.lean:72,212,464`, and
`JointAgreement.lean:35,442–733`. Source-location pins and current-upstream
comparison are in the parent `FRONTIER.md` and evidence files. Apache 2.0
attribution is retained in every adapted owned module.

[EXECUTED] The dependency path is:

```text
actual nearby RS codeword → error locator → evaluated BW kernel
→ determinant vanishing on the good scalars → bounded Schur-complement kernel
→ bivariate A,B → proved bounded local quotients → polynomial gluing
→ common positions → existing correlated agreement → existing consumers.
```

[EXECUTED] The kernel theorem is imported from the sibling
`polynomial_kernel/all_pins_successor/` package. The bivariate and gluing
modules come from `polynomial_gluing/universe_successor/`. Their exact hashes
are recorded in `manifest.json`. The polynomial representation is Mathlib's
ordinary nested polynomial type. The local quotients needed by the gluing
theorem are constructed and proved to satisfy its degree bounds.

[SOURCE] The resident `ProximityGapUDTight.PolishchukSpielman` is a different
bare-divisibility contract, with additional degree/cardinality premises.
[OPEN] This artifact does not claim that resident `Prop` itself has been
proved; it closes the requested full-UD behavior through actual bounded
quotients and the existing consumer interfaces.

## Artifact and integration

[EXECUTED] `full-ud.patch` contains ten owned modules, with 38 declarations
and 38 axiom guards. `src/` mirrors those bytes. `manifest.json` records the
exact module/declaration census, source hashes, dependency hashes and final
check status. `run_lean.py` records command, exit code, elapsed time, source
hash and whether the source stayed unchanged during each check.

[EXECUTED] `package.py` checks the import boundary, applies the patch in a
clean temporary tree, and compares every resulting file byte for byte.
The final dependency-ordered check records are `logs/freeze-01` through
`freeze-14`. All expected axiom reports are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

[OPEN] Root owns the combined full build and final integration. Apply the
matrix all-pins successor and gluing universe successor, deduplicating their
identical Apache license file, then this owned patch. Proposed umbrella
imports are `Selvage.FullUDFriConsumer` and `Selvage.FullUDWitnesses`.
No umbrella or existing public module is edited by this patch.

[OPEN] The whole-opening committed bound adds no sampled-opening error or
Fiat–Shamir random-oracle reduction. The challenge error is unchanged; no
new composed security-bit claim follows solely from the wider radius.
The separate parameter lane prices sampled-opening schedules.

[EXECUTED] Additional external queries during formalization: zero. Initial
research query counts remain in the parent orientation note.
