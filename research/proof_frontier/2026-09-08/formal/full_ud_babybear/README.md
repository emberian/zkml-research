# Actual BabyBear Ext4 carrier bridge

[EXECUTED] One new module, `Selvage/BabyBearFullUD.lean`, instantiates the
frozen full-UD theorem on the existing deployed quotient carrier
`BabyBearExt4.Ext4 = AdjoinRoot (X^4−11)` over BabyBear. It adds no substitute
field, polynomial representation, RS semantics or folding model.

[SOURCE] `Selvage/BabyBearExt4.lean:132,153` supplies that carrier and its
coefficient linear equivalence. Its irreducibility theorem was replayed in
the new isolate (`logs/carrier-existing-01`). [EXECUTED] `ext4Fintype`
transports the finite structure through that exact equivalence, and
`ext4_card` proves `Fintype.card Ext4 = modulus^4`, where the existing
`modulus` is `2013265921`. `base_field_cardinality_falsifier` proves that
the base field cannot satisfy the quartic cardinality contract.

[EXECUTED] `isProximityGenerator_fullUD` directly supplies the existing
`IsProximityGenerator` interface for any nonempty finite evaluation domain
embedded in Ext4 and positive code dimension. Its radius is
`0<δ<(1−d/n)/2`, and its error is exactly `n/(2013265921^4)`.
The field and its cardinality are discharged, with no new assumption.

[EXECUTED] `rateHalf_probability_bound` specializes the immediately usable
probability statement to `n=2^20`, `d=2^19`, `δ=1/5`: if the input pair lacks
correlated agreement, the fraction of close affine folds is at most
`2^20/(2013265921^4)`. This is a single-generator bound, not a composed
security-bit claim.

[EXECUTED] The statement-first `CarrierCardinality`, `FullUDRealizer` and
`FiringPremise` contracts have concrete evidence. A consecutive-element
base-subfield embedding gives an actual `Fin(2^20) ↪ Ext4`. On that domain,
the nonconstant codeword line has probability one, fires the realizer and
produces correlated agreement at `1/5`; the former one-third-UD radius
condition fails. Separately, the degree-exactly-`d` word `x↦x^d` paired with
zero has no sufficient common agreement set, by the existing polynomial
root bound. That pair inhabits the probability theorem's failure premise,
and the probability theorem is applied to it explicitly. No large-field
or large-domain enumeration is used by these proofs.

[OPEN] The concrete consecutive-element embedding witnesses the RS theorem;
it is not asserted to be a multiplicative folding domain. An application
still supplies its actual evaluation embedding or `FoldingTower`, the
required rate/degree/radius conditions, and failure of agreement or initial
farness. The separate sampling-budget lane supplies a checked schedule;
this artifact does not discharge commitment binding, sampling randomness,
or a Fiat–Shamir random-oracle reduction. The wider radius alone gives no
new security-bit claim.

[EXECUTED] The exact source passes Lean4.30 with 12 declarations and 12 axiom
pins, each requiring exactly `propext`, `Classical.choice`, `Quot.sound`.
`provenance.json` records the final source hash, command, exit code, and the
unchanged-source check. The import boundary and clean patch application pass.
`integration_census.json` uses root's actual declaration/pin checker.

[EXECUTED] All fourteen frozen full-UD dependency hashes remain unchanged in
the new isolate. The owned patch is `babybear-full-ud.patch`; apply it after
the frozen full-UD package. `integration_entry.json` supplies root's manifest
entry; the proposed umbrella import is `Selvage.BabyBearFullUD`. Root owns
the combined integration build. No external queries were added.
