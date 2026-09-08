# Independent audit: full unique-decoding closure

[DERIVED] **Accepted within the scope below. No mathematical or source-interface defect found in the frozen full-UD proof.** The new headline derives its interpolation and bounded local quotient certificates from actual nearby Reed–Solomon codewords. It does not import the desired conclusion as a caller premise. The probability, mutual-agreement, fold, tower, and committed-opening wrappers use the existing consumer definitions.

[OPEN] This is a source/mathematical audit with independent finite arithmetic and census checks. Root owns the combined build. This review performs no new Lean build, no cryptographic execution, and no companion or frozen-source edit.

## Frozen inputs and verification

[EXECUTED] `python3 research/learn_infer_only/experiments/adversarial_review/full_ud/review.py > research/learn_infer_only/experiments/adversarial_review/full_ud/review.log 2>&1` returned exit 0. Commands, source hashes, exact patch reconstruction, census, and finite results are preserved in this directory. The script reads and checks the following inputs:

| Input | SHA-256 |
|---|---|
| `full_ud/full-ud.patch` | `1e7a4c2292766f8b02a80879ef288915d610b67b5c070d8892db8661a8146cb2` |
| all-pins `PolynomialMatrixKernel.lean` | `6c2aa5d0be03d7c00c3aca459eff2532570f205f6af604210f2cf033aaaec5dd` |
| universe-successor `PolynomialBivariate.lean` | `fef487127bd25f43775a238add6bdb3d7becbdd6745af393fd2bd834daa18dd0` |
| universe-successor `PolynomialGluingStatement.lean` | `8f7fb82b2d8003cc034ca1a0035495b38a104f4bbb4c91e62b11b962f0ab4cf0` |
| universe-successor `PolynomialGluing.lean` | `898da7979dd4f3ed387c8a83d9e2a19dd1e70f6dcb82b09098f7c18c7a0b7f41` |

[EXECUTED] All ten full-UD source hashes match its manifest and the actual patch additions byte for byte. Its 38 theorem/lemma declarations have 38 corresponding guards. Including the four shared dependency modules gives 105 declarations and 105 distinct matching guards; each expected axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`. The existing integration census was reused, with its own source hash recorded. This is a lexical check, not an independent Lean parser.

[SOURCE] The producer's 14 dependency-ordered `logs/freeze-01` through `freeze-14` records report successful single-module Lean checks of these exact source hashes, with unchanged source bytes. This review checked those records and logs; it does not relabel them as an independent kernel replay. Base: minidregg `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`, Lean 4.30.0. Copied algebra retains ArkLib authors, Apache-2.0 notices, and the upstream commit `22dbd4e836c15a21f68889afa69b7130da04abbb`.

## Accepted mathematical and consumer scope

[SOURCE] [FullUDStatement.lean:17](/Users/ember/dev/zkml-research/research/proof_frontier/2026-09-08/formal/full_ud/src/Selvage/FullUDStatement.lean:17), `FullUDCardCore`, and [FullUDCore.lean:38](/Users/ember/dev/zkml-research/research/proof_frontier/2026-09-08/formal/full_ud/src/Selvage/FullUDCore.lean:38), `fullUDCardCore`, quantify an arbitrary field, a finite index type, an injective evaluation domain, two arbitrary words, and an explicit finite set of distinct good scalars. With `1 ≤ d`, `2e+d ≤ n`, and more than `n` good scalars, each scalar fold having some existing RS codeword at Hamming distance at most `e`, they produce **one common set** of at least `n-e` positions and a codeword for each input agreeing on that same set. Field finiteness is unnecessary for this integer core.

[DERIVED] The order of quantifiers is substantive: `∃ S, ... ∀ j, ∃ w ... AgreesOn S (f j) w` bounds joint disagreement, not merely the maximum of two separately minimized distances. Equivalently, the union of the two discrepancy sets has size at most `e`. The contrapositive bounds the number of good scalar folds by `n` whenever no such joint explanation exists. No extra, differently defined joint-distance object is introduced.

[SOURCE] Existing semantics are reused exactly: [ReedSolomon.lean:85](/Users/ember/dev/minidregg/Selvage/ReedSolomon.lean:85) defines the image of polynomials of degree `<d`; `mem_reedSolomonCode_iff` exposes their evaluations. [CorrelatedAgreement.lean:75](/Users/ember/dev/minidregg/Selvage/CorrelatedAgreement.lean:75) uses Mathlib Hamming distance divided by `n`; `close` is existential distance `≤δ`, and `CorrelatedAgreement` uses one set of size at least `(1-δ)n`.

[SOURCE] [ProximityGapFullUD.lean:17](/Users/ember/dev/zkml-research/research/proof_frontier/2026-09-08/formal/full_ud/src/Selvage/ProximityGapFullUD.lean:17) converts relative distance with `e=floor(δn)`. Its generator head at line 46 proves the existing affine PG(2) interface for uniform coefficients `(1,z)`, on `0<δ<(1-d/n)/2`, with error `n/|F|`. Finite field and nonempty domain are explicit here. The probability event is exactly the good-scalar filter divided by `|F|`, with the required strict threshold `Pr>n/|F|`.

[SOURCE] `hasMutualCorrelatedAgreement_fullUD` at line 85 invokes the existing RS minimum-distance and CA-to-MCA theorem. Its constant error is monotone and nonnegative; the `max` of the two proximity bounds simplifies to `(1+d/n)/2`. The MCA failure predicate retains the existing quantifier over a possible large agreement set that fails to explain some input word. This is a derived consumer of the same PG result, with the same error.

[SOURCE] `foldDistancePreserving_fullUD` at line 105 passes this PG theorem into [Proximity.lean:1093](/Users/ember/dev/minidregg/Selvage/Proximity.lean:1093). The underlying fold is the existing even/odd decomposition and recomposition. Its bad-set bound is the **folded domain's** cardinality. The source degree is twice the target degree. `FoldingData` carries nonzero evaluation points and `2≠0`, so the unrestricted field scope of the algebraic core does not erase the multiplicative fold's characteristic/domain requirements.

[SOURCE] [FullUDFriConsumer.lean:16](/Users/ember/dev/zkml-research/research/proof_frontier/2026-09-08/formal/full_ud/src/Selvage/FullUDFriConsumer.lean:16), `proximity_sound_halfThen_fullUD`, supplies the wider band to the existing tower machinery. It requires `m>0`, positive initial distance, nonempty levels through `m`, degree halving at every round, and positive target degree plus the new radius inequality at every **positive-index round**. Round zero uses the existing distance-halving theorem; the remaining rounds preserve `δ/2`. The result counts existing `acceptSet` challenge tuples and retains numerator `m*n₀*|F|^(m-1)`.

[DERIVED] Under uniform independent field challenges this numerator gives error at most `m*n₀/|F|`. It is a bound that can be loose or at least one; no general nontrivial security level follows without parameters. At rate one half, the explicit initial distance `2/5` gives tail radius `1/5`, which is below `1/4` and above `1/6`. The rate-half premise is only on positive tail rounds; for `m=1` it is empty, and the result simply uses the old first-round theorem. This is intentional generality, not evidence that a new tail was exercised.

[SOURCE] `committedFri_sound_halfThen_fullUD` at line 82 only applies the existing `friCommittedAcceptSet_subset` and the new tower bound. [HalfThresholdFriTranscript.lean:38](/Users/ember/dev/minidregg/Selvage/HalfThresholdFriTranscript.lean:38) fixes words and roots at **all levels before the challenge tuple**. Its acceptance event at line 416 requires all-position consistent openings in every round and final RS membership. [Commitment.lean:122](/Users/ember/dev/minidregg/Selvage/Commitment.lean:122) carries exact `PositionBinding` as a structure field. This is a deterministic conditional binding reduction for fixed committed words; it is not a sampled-opening or adaptive commitment-tree soundness theorem.

## Audit of the algebraic bridge

[SOURCE] `bw_specialization_of_close` constructs a monic error locator from the actual discrepancy set and multiplies it by the nearby polynomial. Its locator coefficient block is proved nonzero. Zero nearby polynomials are handled explicitly using `d≥1`. The BW matrix has the sign convention `fE-Q=0`, and its coefficient split has lengths `e+1` and `e+d`.

[SOURCE] `det_eq_zero_of_specializations` constructs a nonzero evaluated kernel vector for every good scalar. Only the locator columns depend on the scalar, so each row-selected determinant has degree at most `e+1`. Root counting forces zero determinants. `bounded_kernel_of_specializations` selects an `e+d` row Vandermonde block with constant, invertible determinant, forms its Schur complement with entries of degree at most one, and invokes the proved polynomial kernel theorem. It derives a nonzero locator block of degree at most `e` and the other block of degree at most `e+1`; these are conclusions, not assumptions.

[SOURCE] `bw_bivariate_of_many_close` uses ordinary nested Mathlib polynomials and swaps the variables with explicit degree/evaluation equalities. It derives nonzero `A`, bounds `degX A,degY A≤e`, `degX B≤e+d-1`, `degY B≤e+1`, and the exact line restriction identity at every domain point.

[SOURCE] Inside `fullUDCardCore`, the horizontal quotient is the actual nearby RS polynomial, with degree at most `d-1`. Its identity with the bivariate restriction is proved by more roots than degree: the difference has degree at most `e+d-1`, but vanishes at at least `n-e` distinct points, and `e+d-1<n-e`. The vertical quotient is the actual linear polynomial `f₀(i)+Y f₁(i)`, with degree at most one. Both needed quotient-degree assumptions of corrected gluing are therefore constructed.

[DERIVED] The gluing parameters are `(aX,aY,bX,bY)=(e,e,e+d-1,e+1)` and `(nX,nY)=(n,|good|)`. The crucial strict inequality is
`(e+d-1)/n + (e+1)/|good| < (2e+d)/n ≤ 1`.
It remains strict even at integer equality `2e+d=n`, because `|good|>n`. This prevents a hidden endpoint gap.

[SOURCE] The shared `polishchuk_spielman` proves divisibility by its resultant/coprime argument, obtains quotient degree bounds using the **bounded local quotients**, and cancels on the subset where `A` does not specialize to zero. Root counting loses at most `e` domain points. The core pulls this subset back along the domain embedding and extracts the first two coefficient polynomials of the global quotient; each lies in the existing degree-`<d` code and agrees with its input on the shared subset. No division by a zero specialization is assumed.

## Independent nonvacuity checks

[EXECUTED] `finite_checks.json` independently checks the frozen six-point `F₇` falsifier against all 49 affine codewords and all 2,401 pairs. The seven minimum fold distances are `[2,3,3,3,3,3,3]`; maximum common agreement is exactly two, less than the required three. Positive degree and more-than-`n` good scalars hold; `2e+d≤n` alone fails. This verifies the scope of the falsifier, not sharpness of every radius boundary.

[SOURCE] The frozen Lean witness uses eight points over `F₁₁`, degree bound four, and two actual codewords. It inhabits all core premises and fires the new PG theorem at radius `1/5`, with probability one strictly above `8/11`. The fact that its words are already codewords makes it a valid premise witness but a mild distance test.

[EXECUTED] The review adds arithmetic checks of two noisy variants. Both words are corrupted on the same one or two positions. Their exact joint agreement maxima are seven and six respectively; each word's nearest-code distance is one or two, and every scalar fold remains within that integer radius. The one-error variant also fires the wider relative-radius premise at `1/5`, with probability one. The two-error variant checks the integer equality `2e+d=n`; it is not asserted to satisfy the relative `1/5` premise. These are independent finite computations, not additional Lean declarations.

[EXECUTED] A two-round `F₉₇` multiplicative tower with level sizes `8→4→2`, degree bounds `4→2→1`, and source polynomial `X⁴+2X⁵` has exact source RS distance `4/8`. All structural fold equations, nonzero points, negation closure, squaring fibres, and distance computations were checked. At initial distance `2/5` and tail distance `1/5`, the new positive-tail premise is populated. Exhausting all 9,409 challenge pairs gives exactly 97 acceptances, all at first challenge 48, under the proved numerical bound 1,552. The old tail radius condition fails. This checks a genuine positive tail and nonempty acceptance event without claiming a kernel-checked deployment instance.

## Required limits on closure credit

[DERIVED] No source correction is requested. Carry these qualifications into any integration claim:

- The result is **positive-degree conservative full UD**: integer `2e+d≤n`, and the exported **open** relative band `(1-d/n)/2`. It does not export `d=0`, a closed relative endpoint, or the extra `1/(2n)` from the exact RS minimum-distance expression.
- The good-scalar premise cannot fire over a finite field when `n=|F|`; its error is then one. Likewise, the PG radius interval is empty for `d≥n`. The explicit witnesses show that the headline is not globally vacuous; each deployment still needs applicable parameters.
- The resident bare-divisibility `ProximityGapUDTight.PolishchukSpielman` proposition remains a distinct unproved contract. The new route bypasses it using proved bounded quotients. Do not say that the old proposition itself was discharged or that old callers were rewritten by this patch.
- PG, MCA, fold preservation, and tower/committed bounds are successive uses of one algebraic closure. They are not independent reductions whose security errors can be multiplied or whose gains can be counted repeatedly. The error formulas are unchanged; wider admissible radius alone adds no security bits.
- Whole-opening committed soundness remains conditional on exact binding and fixed level words/roots. No concrete Merkle collision-resistance, sampled-query error, adaptive commitment-tree bound, Fiat–Shamir random-oracle reduction, executable verifier correctness, or deployment field cardinality instance is established here.

[EXECUTED] `import_closure.json` records 45 project modules in the complete lexical import closure, including 14 proposed modules and 31 pre-existing modules. This is deliberately distinct from the inspected theorem call chain above. Merely importing the pre-existing ZK, extraction, or Fiat–Shamir modules through broad existing imports does not close or add credit for their unrelated theorem premises. `ProximityGapUDTight` is not in this import closure.

[OPEN] Root's combined exact-byte build and final integration remain outside this audit. External search queries: zero. Frozen proposals, companion main, and shared verdict files were left unchanged.
