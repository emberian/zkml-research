# Exact pinned-source BFV scalar certificate

2026-09-06. This is a research patch for the read-only Minidregg tree, not a change
to that tree or a shipped BFV verifier. It extends the two completed BFV patches;
their sources and 27/33 exact axiom pins are unchanged.

## Result and statement

[DERIVED, kernel checked] The existing compiler now emits a relation that forces
the actual pinned scaler's deterministic scalar result. Canonicality of all six
input residues, both integer quotient/remainder calculations, and canonicality
of the integer output modulo Q are constrained inside the relation. There is no
prover-selected choice between exact nearest rounding and nearest plus one.

The main endpoints in namespace `Minidregg.Compiler.FheSourceCertificate` are:

| Layer | Checked endpoint |
|---|---|
| Exact signed integer certificate | `sourceCertificateSound`, `FheSourceCertificate.lean:56` |
| Nonnegative balance matrix | `balanced_source_accepts`, `FheSourceCertificateLayout.lean:108` |
| Existing emitted descriptor | `sourceDescriptor_sound`, `FheSourceCertificateEmit.lean:106` |
| Generic simplification plus existing CSE | `optimizedSourceDescriptor_sound`, `FheSourceCertificateOptimized.lean:16` |
| Full-assignment checker with explicit external claim pins | `pinnedSourceCheck_sound`, `FheSourceCertificateVerifier.lean:19` |
| Nonzero concrete matrix witness and layout capacity | `captured_balance_inhabited`, `FheSourceCertificateWitness.lean:28` |

[DERIVED, kernel checked] `pinnedSourceCheck_sound` states that a passing existing
descriptor check, together with equality checks tying the decoded groups to the
external six residues and output, forces
`output = FheRnsScale.deployedOutput r % FheRnsScale.deployedQ`.
`pinned_wrong_neighbor_refused` quantifies over **every wire assignment** for the
captured residue row and external output 172480.

## Exact arithmetic being certified

[SOURCE: previous source audit and checked model] The constants and literal word
semantics come from the pinned `fhe-math 0.1.1` RNS scaler used by the vendored
`fhe-dregg` BFV multiplication path. The previous tranche's
`engine_refinement/Compiler/FheRnsScaleDecomposition.lean:333–373` proves the exact
rounded integer identities from the modeled U256/shift/sign operations for all
canonical six-limb inputs. Implementation hashes and coefficient comparisons are
retained in `experiments/bfv_lift_refinement/engine-run.json` and
`ENGINE_README.md`; this tranche does not claim to replace their source-to-model
inspection with a Rust semantics proof.

[DERIVED] Write `A = Σ rᵢ θGᵢ`, `B = Σ rᵢ θFᵢ`, and
`K = Σ rᵢ ωᵢ − v γ`, using the already pinned constants. The certificate requires

```text
0 ≤ rᵢ < pᵢ                        for all six input limbs
2 A + 2^126 = 2^127 v + rg          0 ≤ rg < 2^127
2 B + 2^127 = 2^128 w + rf          0 ≤ rf < 2^128
K + w = Q u + output               0 ≤ output < Q
```

Here `v`, `w`, and `u` are integer quotients. These are exact Euclidean relations,
so the remainders force both selected roundings, including signed correction
rounding. They imply the deterministic source integer representative `K + w`
modulo `Q = 649033470896967801447398927572993`. `honest_accepts` proves that every
canonical input has an accepting **semantic** certificate.

## Existing compiler composition

[DERIVED, kernel checked] The concrete lowering uses 21 natural-number groups,
each represented by 22 radix-64 digits. Groups 0–5 are the input residues, 6–11
their canonicality complements, 12–14 the Garner quotient/remainder/complement,
15–17 the signed-correction quotient/remainder/complement, 18–19 the canonical
output/complement, and 20 the final output quotient. Signed quotients are encoded
with offsets `w + 2^65` and `u + 2^120`.

[DERIVED, kernel checked] Twelve nonnegative integer balance rows impose six
input complement equalities, the Garner QR relation and remainder complement,
the correction QR relation and remainder complement, and the output QR relation
and complement. The coefficient matrices are fixed constants. A complement row
such as `rf + rfSlack = 2^128 − 1` supplies the strict upper bound; it is not a
caller hypothesis. All digits and carries are range checked by existing gadgets.

[DERIVED, kernel checked] Each balance is emitted as two shared-result instances
of the existing `BfvSignedAccumulatorAir.weightedSumGadget`. The already landed
`IntegerCertificateEmission.ranged_weighted_sound` supplies range-derived
no-wrap soundness. Each accumulator uses 57 columns, 6-bit digits and 15-bit
carries. The checked local column budgets are 1,866,508 and 2,097,151, both below
the deployed BabyBear modulus 2,013,265,921. Matrix coefficient capacity and the
radix linearization are proved, rather than assumed by the descriptor theorem.

[DERIVED, kernel checked] The compiler lane's generic `AirSimplify` pass and the
existing CSE preserve this relation. No alternate AIR or private checker
semantics were introduced. `nPublic` is zero in this local descriptor;
`pinnedSourceCheck` explicitly compares the full assignment's decoded values to
the external claim before invoking the existing Boolean descriptor checker.
That full-assignment wrapper is not a succinct-proof public-input protocol.

## Witness, falsifiers, and executed checks

[DERIVED, kernel checked] The captured source row is

```text
[9675007914, 2505552642, 57236360992,
 4252961403400044537, 411888490947559416, 2145767979390943224]
```

Its previous-tranche selected lift is
`108454153028594899284870262370752`. Exact nearest reference scaling gives
172480; the deterministic pinned source gives **172481**. The semantic witness
accepts 172481, every semantic certificate for 172480 is refused, and a concrete
21-group matrix witness inhabits all balance and group-capacity premises.

[EXECUTED] `check-results.json` records the **existing Lean emitted checker**
accepting this 172481 witness in raw, CSE, and simplified-plus-CSE descriptors.
The optimized checker also accepts four additional canonical rows, including
positive and negative giant integer source representatives before reduction
modulo Q. Each corresponding wrong output is refused. Captured-row controls
refuse 172480, oversized Garner and correction remainders, a noncanonical input
residue, and a radix digit of 64.

[EXECUTED] `layout-results.json` checks 1,003 canonical input rows and refuses
1,003 changed outputs using the exact integer balance specification. This is a
finite executable check, separate from the universal soundness proof.

[EXECUTED] The compressed descriptor and six retained initial-variable fixtures
can be replayed by `replay_descriptor.py`. Its independent Python interpreter
reads the actual serialized existing descriptor, checks topological wire use,
and evaluates its field operations and zero assertions. It is an executable
cross-check, not another proved evaluator. The strongest negative fixture lowers
the encoded correction quotient by one, raises its remainder by `2^128`, and
changes the output to 172480 with its matching complement. **All eleven other
integer balance rows remain satisfied; only row 9, the correction remainder
complement, fails.** The emitted descriptor refuses it. Thus the range row closes
a coherent alternate-rounding certificate.

[EXECUTED: independent review] The adversarial lane independently compiled all
six final modules and their 23 exact pins. Its retained records are
`experiments/adversarial_review/lean_bfv_cert_{semantic,layout,emit,optimized,verifier,witness}_01.json`
and `bfv_certificate_review_02.json`. It independently reconstructed inputs from
the matrix/source formula, replayed the descriptor, and kernel-checked that the
coherent alternate satisfies all rows except row 9 in
`lean_bfv_cert_range_tooth_03.json`. These review records live in that lane's
ownership, not in this patch.

## Measured certificate size

[EXECUTED] Counts below come from emitted descriptors, not an asymptotic estimate.
The uniform 132-bit group layout is deliberately conservative.

| Item | Per scalar |
|---|---:|
| Scalar digits / scalar bit wires | 462 / 2,772 |
| Initial variables, including results/carries and their bits | 30,294 |
| Integer balance rows / existing weighted accumulators | 12 / 24 |
| Raw emitted gates | 1,406,124 |
| Existing CSE gates | 251,119 |
| Generic simplification plus CSE gates | 132,675 |
| Optimized multiplication / addition gates | 64,034 / 68,641 |
| Optimized zero assertions | 36,498 |
| Optimized wire header | 183,105 |

[DERIVED] Independently repeating the final certificate for all `3 × 4096`
coefficients of an unrelinearized tensor would give 1,630,310,400 gates and
372,252,672 initial variables. This is a naive repetition baseline only. It
excludes integer convolution, NTT and limb provenance, commitments, and proof
overhead; it is neither a lower bound nor a latency benchmark. The separate
sliding-window core avoids ciphertext-by-ciphertext multiplication, so **none of
this certificate bill belongs in that core's Learn cost**.

## Validation, reproduction, and artifact pins

[EXECUTED] `validation-summary.json` records fresh isolated compilation of four
dependencies, all six new theorem modules, and a side-effect-free `Compiler`
umbrella, followed by the companion's import-boundary check and patch application
checks. There are 23 declarations with exact `#guard_msgs`-pinned `#print axioms`
reports. No `sorry`, custom `axiom`, `native_decide`, or `ofReduceBool` occurs in
the theorem sources. Standard Lean axioms used are recorded individually in
`axiom-pins.json`; this is not an axiom-free claim. No full Minidregg build was run
for this local tranche. Companion trees were not modified.

The proposed patch is `minidregg-fhe-source-certificate.patch`, SHA256
`55ffecdf2db1d330b0cc76126781dbc39c4ea581fe4edc4fbb7da7830e771d2f`.
It requires the earlier BFV reference and engine-refinement patches,
`Compiler.IntegerCertificateEmission`, and `Compiler.AirSimplify`. Their exact
source hashes are in `validation-summary.json`. The frozen AirSimplify source is
`a731cf62061751104e97619c9804530987a9cd2271b039edefbdcdb8cb583f79`.
Only the six library modules and two `Compiler` imports are in this patch;
executable IO runners are separate.

Recheck the kernel proof/import/patch chain from the read-only companion's
toolchain environment:

```sh
cd /Users/ember/dev/minidregg
lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/source_certificate/validate.py
```

The actual emitted-checker and fixture generation command, in the same environment,
is:

```sh
lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/source_certificate/build.py FheSourceCertificate FheSourceCertificateLayout FheSourceCertificateEmit FheSourceCertificateOptimized FheSourceCertificateVerifier FheSourceCertificateWitness FheSourceCertificateChecks FheSourceCertificateRetain
```

The lightweight replay and integer checks, from the research repository root, are:

```sh
python3 research/learn_infer_only/experiments/bfv_lift_refinement/source_certificate/check_layout.py
python3 research/learn_infer_only/experiments/bfv_lift_refinement/source_certificate/replay_descriptor.py
```

[EXECUTED] `experiments/bfv_lift_refinement/source_certificate/manifest.json`
pins the retained deterministic gzip fixtures, their uncompressed payloads,
source scripts, and theorem modules. Zero metered searches and zero PDF downloads
were used in this tranche.

## Exact residuals and next useful work

- [OPEN] The result binds one canonical **integer modulo Q**. The Rust engine
  returns residues modulo each target prime; the constrained target-limb-array
  projection and source-to-target modular/Shoup refinement are still separate.
  Rust does not materialize the giant integer `K + w` used by this certificate.
- [OPEN] Input residue provenance from committed ciphertexts, extension, integer
  convolution/NTT, and the full unrelinearized multiplication path is not certified
  by this scalar relation. The previous full-coefficient differential tests do
  not turn those seams into Lean theorems.
- [OPEN] Universal **semantic** honest acceptance is proved. Universal completeness
  of this bounded 21-group **emitted layout** is not. The concrete semantic and
  matrix witnesses are kernel checked; the complete emitted assignment acceptance
  is executed evidence. A compositional completeness proof using existing
  weighted-sum/range constructors would be the useful next proof step.
- [EXECUTED limit] A brute-force whole-checker kernel reduction was stopped after
  38.7 seconds, with observed RSS 12,405,216 KiB at 32 seconds. The optimized
  reduction also met an executable implementation reduction boundary. Failed
  attempts are retained separately; neither supplies a theorem. Do not repeat
  the large kernel reduction as a routine check.
- [OPEN] The uniform digit/group budget can be reduced by proving individual
  group bounds and pruning fixed zero columns. Current counts measure this
  conservative emitted instance, not an optimized lower bound.
- [OPEN] There is no proof-protocol public-input/commitment binding, privacy,
  master-read absence, secret release, relinearization, noise, or runtime claim
  in this artifact.
