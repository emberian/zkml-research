# ArkLib coding-theory statement audit

[READ] Source snapshot: `/Users/ember/src/ArkLib-latest` at
`4d9d67be64634f09a85206238df9380aa3733a93`; comparator
`/Users/ember/dev/minidregg` at `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`.
All `ArkLib/...` paths below are relative to the first tree; all `Selvage/...`
paths to the second. This is a source/statement audit, not a fresh kernel build.
No companion-tree files were written. No internet/paper search was needed.

## Verdict

[INFERRED] **Import the narrow coding-theory results after an explicit event and
probability transport.** This is substantially better than the September admitted
state, but it is not a drop-in dependency edit. Keep Selvage's sharper one-third
bound on its existing interval, and keep its generic-code/generator theorem.
Do not conclude that ArkLib's presence alone establishes a deployed 73-bit FRI
acceptance bound.

| component | exact source and statement | comparison and verdict |
|---|---|---|
| RS unique-decoding CA | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/EpsCa.lean:81` `ProximityGap.rs_epsCa_le_of_le_relUDR`: for `δ_fld ≤ relUDR` and `δ_fld ≤ δ_int`, `epsCa C δ_fld δ_int ≤ n/q` | [READ/INFERRED] **IMPORT** for full-UDR RS affine lines. Relative UDR is `(n-k)/(2n)` for degree `< k`, including the endpoint. It supplies the currently narrower RS proximity-generator instance at `Selvage/ProximityGapUDSharp.lean:113`, but its error is worse on the overlap. |
| RS unique-decoding MCA | same module `:179` `ProximityGap.rs_mcaError_le_of_le_relUDR`: for `0 < δ ≤ relUDR`, `mcaError (AffineLineGenerator F) C δ ≤ n/q` | [READ/INFERRED] **IMPORT**, after transport, as a direct RS affine instance replacing the *use of* `Selvage/ReedSolomon.lean:207` `reedSolomonCode_hasMutualCorrelatedAgreement` plus an external `hPG`. It does not replace the general theorem itself. |
| RS Johnson MCA, sharper count | `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean:41` `ReedSolomon.mcaError_affineLine_johnson_le`: dimension `D+1`, `1≤D≤n-2`, `eta>0`, radius `1-(sqrt(D/n)+eta)`, error `min 1 (johnsonExceptionCount / q)` | [READ/INFERRED] **IMPORT** this narrow module by preference. Directly supplies the MCA conclusion currently exposed only conditionally by `Selvage/JohnsonRegime.lean:523` `mutualCA_johnson`; removes a requirement to supply `hconj` and `hPG` at this instance. |
| RS Johnson MCA, printed BCHKS25 constant | `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean:235` `CodingTheory.rs_mcaError_le_in_johnson_range`: `1<k`, `0≤δ<1-sqrt((k-1)/n)`, explicit multiplicity/field-size bound | [READ/INFERRED] **IMPORT-CANDIDATE**, but prefer the narrow result above and mirror only its arithmetic comparison. This umbrella itself contains a separate admitted lower-bound theorem at `:341`; importing a file with an unrelated admit is not evidence that this theorem uses that admit, but it unnecessarily broadens the audit surface. |
| BCIKS20 affine-line CA | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean:40` `ProximityGap.RS_correlatedAgreement_affineLines`: `0<deg`, `δ<1-sqrtRate`, CA with explicit `errorBound` | [READ/INFERRED] **IMPORT** to construct the RS `IsProximityGenerator` premise of `Selvage/ReedSolomon.lean:207` and `Selvage/JohnsonRegime.lean:507`; preserve independent sharp local instance. |
| BCIKS20 curves | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:786` `ProximityGap.correlatedAgreement_affine_curves`: same code/radius restrictions; degree-`k` curve pays `k*errorBound` | [READ/INFERRED] **DEFER / ADAPTER REFERENCE**, supplies powers-generator `IsProximityGenerator` instances to `Selvage/CorrelatedAgreement.lean:325`, rather than replacing that generic implication. Not an affine-line theorem applied without a degree multiplier. |
| BCIKS20 affine spaces | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean:1154` `ProximityGap.correlatedAgreement_affine_spaces`: `NeZero k`, `0<deg`, open Johnson radius, `errorBound<1`; uniform point of actual affine subspace | [READ/INFERRED] **DEFER / ADAPTER REFERENCE**, same generic consumer `Selvage/CorrelatedAgreement.lean:325`; no current exact bespoke Selvage affine-space theorem to retire. A uniform coefficient-vector interpretation needs a constant-fiber transport, not a definitional rewrite. |

[READ] Exact Lean imports for the selected results:

```lean
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
-- Optional only with a concrete caller:
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
-- Printed-constant alternative, broader than necessary:
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
```

## What the statements actually quantify

[READ] ArkLib's source definitions are substantive:

- `ArkLib/Data/CodingTheory/ReedSolomon.lean:63–66,208–211` constructs the code
  as the image of `Polynomial.degreeLT F k` under evaluation on an embedding.
  It is degree **strictly below** `k`, just like
  `Selvage/ReedSolomon.lean:83–100`. This is not an assumed code-distance object.
- `ArkLib/Data/CodingTheory/ProximityGenerator/Basic.lean:119–125` defines
  `IsMCA`: there exists a large coordinate set on which the generated word
  extends to a codeword, but some input does not. Its `:191–194` `mcaError`
  is the supremum over **all** input word families of the sampled event's
  probability. That family is inhabited by zero words. No adversary or input
  word is omitted.
- The generator at that module's `:414` is precisely `x ↦ ![1,x]`, matching
  `Selvage/CorrelatedAgreement.lean:451–459`; it is not the alternate
  `(1-x,x)` parameterization accidentally used with unchanged input words.
- `Selvage/CorrelatedAgreement.lean:277–281` defines the corresponding bad
  event by codeword witnesses and agreement on the same set. The change from
  projected-code membership to existential extension is mathematical
  bookkeeping, but still a proof obligation.
- ArkLib's sampling API uses finite uniform `SampleableType`; the explicit
  inhabitant available is `SampleableType.ofFintype F`
  (`ArkLib/Data/CodingTheory/ProximityGenerator/PolynomialGenerator.lean:481`).
  `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds/UniqueDecoding.lean:74`
  uses `SampleableType.prEvent_uniformSample_eq_ofReal` to make the count/q
  connection. Selvage's finite weighted sum is at
  `Selvage/CorrelatedAgreement.lean:218–220`; its specialized count/q identity
  already exists at `Selvage/JohnsonMcaBridge.lean:113–121`.

[INFERRED] A narrow adapter has four obligations: equal RS submodules; equivalence
of the projected-word bad event with `MutualCAFailure`; equality of the finite
uniform probabilities (`ENNReal` versus real); then supremum elimination at the
actual input tuple. It must preserve the same field, coordinate embedding,
degree convention, radius, and word pair. None is a cryptographic assumption.
These obligations are not established merely by matching Lean/Mathlib versions.

## Inhabited, numerically nontrivial witnesses

[MEASURED/EXECUTED] Run:

```sh
python3 notes/astra/arklib/coding-witness.py
```

Output is retained in `notes/astra/arklib/coding-witness.out`. Exact rational
arithmetic and exhaustive trial division up to `floor(sqrt(q))` give:

```text
q=1000003, trial-division prime=True; n=16; dimension k=5; domain i |-> i mod q
UDR=11/32, local one-third limit=11/48, witness delta_ud=5/16, ArkLib epsilon=16/1000003
Johnson rho_minus=1/4, sqrt=1/2, delta=3/8, eta=1/8, m=4
Johnson printed comparison numerator=157527; epsilon=157527/1000003 = 0.15752652742 < 1
```

[INFERRED] Take `F := ZMod 1000003`, `ι := Fin 16`, `domain i := i.val mod q`,
`k := 5`, and the finite uniform sampler. Primality gives `Field F`; cardinality,
nonemptiness, decidable equality, and injectivity are immediate finite witnesses.
The proper code has dimension 5 and minimum distance 12. For UD, `δ=5/16` lies
strictly beyond the local one-third interval and within ArkLib's UDR. For Johnson,
`δ=3/8 > 11/32` is beyond its UDR and below both `1-sqrt(4/16)=1/2` and Selvage's
rounded `1-sqrt(5/16)`. The raw Johnson theorem uses `D=4`, `eta=1/8`, and agreement
threshold `ceil(16*(1/2+1/8))=10`; all its integer premises hold.
The value `157527` is the **printed comparison numerator**, not an evaluation
of `johnsonExceptionCount`. The latter is bounded above by the comparison
estimate via `ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate`
at `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/Johnson/FiniteBounds.lean:869–879`.
For this witness its premises are `4 ≤ 16-2`, `eta=1/8>0`, agreement `5/8≤1`,
and `(5/8)*16=10≤10`. The use and normalization of this lemma to the printed
formula are visible at `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean:280–290`.
Consequently the sharper theorem also inherits a `<1` upper bound; the script
computes the explicit comparison estimate only.

[INFERRED] These examples do not hide an always-zero event: set `f₀=0` and
`f₁(i)=(domain i)^5`. At slope zero, the combination is the zero codeword and
`f₁` cannot be extended to a degree-<5 polynomial on all 16 coordinates, so
MCA fails. At a nonzero slope, a degree-5 polynomial can agree with a degree-<5
polynomial on at most five points. At either chosen radius the required set
has at least ten points. Thus the bad event is exactly `{0}` and has probability
`1/q > 0`. This is a root-counting derivation, **not an executed exhaustive
finite-code check or a checked Lean witness**.

[INFERRED] For BCIKS line/curve/space hypotheses, use the same field/domain/code,
`δ=1/4`, and `errorBound=n/q=16/1000003<1` (its UD branch). A quadratic curve
pays `32/1000003<1`. Choose codeword words `0,1,X`: generated words stay in the
proper code, so the probability premise is 1 and the implication actually fires.
For affine spaces choose `k_space=2`, directions `1,X`; these are linearly
independent on the domain, so the space is not a singleton artifact. No
uninhabited `errorBound<1` or sampler premise is being used.

[REFUTED: suggested Johnson smoke-test parameters] The earlier critique's
`ZMod 17,n=16,d=4` suggestion (`notes/selvage-foundations-critique-2026-11-05.md:132`)
cannot demand a `<1` bound from the **printed Johnson estimate**. Its multiplicity
is at least 3 and reduced rate is `3/16<1`, so for every allowed nonnegative
radius that expression is greater than `16807/51 > 329`. This says the bound is
numerically uninformative at those parameters, not that MCA is false or the
hypotheses are uninhabited. The UD estimate `16/17` does remain below one there.
The larger-field witness above repairs the Johnson test.

## Stronger, weaker, incomparable: the exact qualification

[READ/INFERRED] **UD is not a pointwise dominance result.** ArkLib extends the
proved radius to `(n-k)/(2n)` with error `n/q`; Selvage's
`rs_proximityGap_UD_sharp` (`Selvage/ProximityGapUDSharp.lean:45–61`) uses
`(floor(δ*n)+1)/q` for `k < (1-3δ)n`. On that narrower interval the local error
is usually substantially smaller. The correct comparison is **incomparable as
quantitative packages**, with ArkLib stronger on radius and weaker on the
shared error budget. Retain and select between them; do not silently replace a
sharp local error by an allegedly stronger imported estimate.

[READ] ArkLib's `relativeUniqueDecodingRadius` is `(dist-1)/(2*n)` in NNReal,
not `dist/(2*n)`: `ArkLib/Data/CodingTheory/Basic/DecodingRadius.lean:34–40`.
For positive dimension ≤ block length, `ReedSolomon.lean:533–537` proves it is
`(1-k/n)/2`. It induces the same closed integer-radius ball as integer unique
decoding. It should not be paraphrased as every real radius strictly below half
the exact minimum distance without accounting for Hamming-grid endpoints.

[READ/INFERRED] **Johnson removes unproved premises for this RS instance.**
`Selvage/JohnsonMcaBridge.lean:270–275` is a proposition called
`HaboeckTheorem2`; `:331–339` assumes it and an error-envelope hypothesis.
`Selvage/JohnsonRegime.lean:523–536` additionally assumes a proximity-generator
premise. ArkLib gives direct MCA and an explicit error, extending to reduced
rate `(k-1)/n`. That is stronger foundational coverage at an identified error
function, not proof for every arbitrary caller-provided `err`. A deployment
budget must dominate the imported explicit constant, including the chosen
radius's multiplicity cost. The direct adapter should export MCA first and
only derive `WHIRConjecture412` as a compatibility corollary, avoiding an
unnecessary residual `hPG` dependency.

[READ/INFERRED] **Keep the generic local reduction.**
`Selvage/CorrelatedAgreement.lean:325–335` handles arbitrary submodules, tuple
lengths, weighted generators, and a CA premise. ArkLib's RS affine-line/curve
results cannot replace that scope. Their CA results supply concrete premise
instances; they are incomparable to that generic theorem as standalone types.
For affine spaces, the actual source samples a uniform point of the subspace
(`ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:159–177`), not a coefficient
tuple. Establish the equal-fiber fact before using a tuple sampler.

## Residual checks before landing an import

[OPEN] This worktree has no `.lake` directory. No fresh Lean elaboration,
`#print axioms`, or transitive binary-dependency kernel audit was run here.
The parent audit owns the source escape/import census. Claims above are based
on actual definitions, theorem statements, and visible proof bodies, rather
than README claims; they still need kernel checks with pinned dependencies.
Use an hbox scoped bridge build after dependencies are prepared under its
resource rules. Pin axioms for each selected headline theorem and adapter;
execute the larger-field arithmetic/inhabitation canary in Lean. Do not treat
source-level absence of `sorry` in a leaf as transitive proof cleanliness.

[READ] Stale comments are not an admission census: EpsCa's introductory prose
still calls the BCHKS25 alternative an “external admit” at `:30–32`, while
`CapacityBounds/UniqueDecoding.lean:109` now supplies an actual proof. Conversely,
the CapacityBounds umbrella retains a genuine unrelated lower-bound `sorry`
at `:341`. Check declarations, not these summaries.
