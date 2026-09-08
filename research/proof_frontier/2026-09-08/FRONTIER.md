# Proof frontier, 2026-09-08: use full unique decoding before pricing capacity

[DERIVED decision] The next concrete formalization is
`reedSolomonCode_isProximityGenerator_fullUD`: replace the current
`B = (2 + d/n)/3` by `B = (1 + d/n)/2`, with the same `n/|F|` error.
It must be proved over the existing `reedSolomonCode` and feed the existing
MCA/folding consumers. A named premise asserting this conclusion is not closure.

[SOURCE baseline] Read README.md, AGENTS.md, swarm/LANE-PREAMBLE.md,
swarm/OVERNIGHT-2026-09-08.md, SLVG_THOUGHT.md, docs/VERDICTS.md §7,
notes/README.md, notes/formal-delta-2026-09-04.md,
notes/proximity-delta-2026-09-04.md, and minidregg CLAUDE.md/ATLAS.md.
The September 4 formal note already mentions ArkLib's full-UD realizer;
this note supplies its port boundary and checks new literature, not priority.

## What changed outside

[SOURCE: statements and scope, not audited reduction] ECCC TR26-164 revision 1,
September 5, proves algorithmic RS list decoding near capacity for all fixed
rates, arbitrary evaluation sets, over sufficiently large prime fields
(Corollary 1.2, p.3). This is list decoding; it is not by itself an MCA input.
[Primary revision](https://eccc.weizmann.ac.il/report/2026/164/revision/1/download).

[SOURCE: theorem and limitations] Fernando Granha Jeronimo, ECCC TR26-169,
September 5 / published September 6, Theorem 1.2 (p.4), states fixed-slack
curve MCA with exception count `n^C(γ,ℓ)`, hence error `n^C(γ,1)/q` for lines.
Domains are arbitrary; `n ≥ n₀` is required. Section 8.4 (p.32) extends the
geometric MCA argument to extension fields of characteristic
`p > max(k−1, Bγ,1)`. Thus “prime fields only” would be too restrictive.
Section 8.5 expressly provides no useful numerical certificate for a prescribed
small length. Fixed slack cannot become an n-dependent slack without tracing
constants. Section 8.3 requires `q > 2^λ n^C*` for its λ-bit certificate.
[Primary paper](https://eccc.weizmann.ac.il/report/2026/169/download).

[DERIVED] These publications change the literature orientation behind §2/§7:
a fixed-slack near-capacity MCA route now has a paper claim. They do not restore
the withdrawn unqualified capacity formula or raise any deployed bit number.
No reduction in either new paper was independently audited end to end here.

[EXECUTED] `python3 research/proof_frontier/2026-09-08/evidence/derive.py` (run from repository root; exact output
in evidence/derive-output.txt) evaluates the inherited ErrorBudget point
`p=2013265921, n=2^20, d=2^19, |F|=p^4`:

| condition on a proposed `n^C/|F|` bound | necessary numerical C ceiling |
|---|---:|
| error < 1 | C < 6.181378119 |
| error < 2^-100 | C < 1.181378119 |
| error < 2^-128 | C < -0.218621881 |

[DERIVED] These are algebraic screening inequalities, not estimates of the
paper's C. An unpriced polynomial exception budget cannot be substituted for
`n/|F|` merely because its radius is better. The existing one-challenge UD term
is about 103.627562385 bits at this point; the composed budget remains separate.

## Current upstream interfaces, checked at source

[EXECUTED] GitHub API tips observed:

- ArkLib `66f3d089a41704597f54d641b78254d2a8f361f8` (September 7).
- VCV-io `40481e538efab1e5b1dbe44470334b961bf2bc3d` (September 8).
- Plonky3 `7230fc572870436e6651762f35c6c3f3f48960d2` (September 7).

[SOURCE] Only ArkLib's relevant source was re-audited in depth here; the other
two tips are orientation, not a new audit of their proof/security contents.
ArkLib's current status still says unrestricted stateful composition remains
admitted (saved evidence/arklib-current-status.md:95).
At the pinned tip, `BCS/Basic.lean` remains a commented construction stub;
`FiatShamir/Basic.lean:170` still admits completeness. Saved exact files are
in evidence/arklib-BCS.lean and evidence/arklib-FS.lean. This is an observation
about these files, not absence across other proof-system libraries.

[SOURCE] The full-UD source is in the existing checkout
`/Users/ember/src/ArkLib-2026-09`, at `22dbd4e` (full pin in SOURCES.json).
The four AffineLines modules below are unchanged in the GitHub comparison
`22dbd4e...66f3d089`; current JointAgreement bytes were fetched and match.
Relevant prefix:
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/`.

| source declaration | location | role |
|---|---|---|
| `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` | UniqueDecoding.lean:29 | complete public full-UD theorem |
| `RS_jointAgreement_of_goodCoeffs_card_gt` | JointAgreement.lean:241 | > n good scalars imply joint agreement |
| `RS_exists_bivariate_AB_of_goodCoeffs_card_gt` | JointAgreement.lean:35 | bounded bivariate A/B witness |
| `RS_exists_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt` | GoodCoeffs.lean:715 | polynomial kernel vector, nonzero A |
| `RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt` | GoodCoeffs.lean:212 | > n roots kill determinant minors |
| `BW_homMatrix` | BWMatrix.lean:28 | one matrix for the interpolation equations |
| `polishchuk_spielman` | ArkLib/Data/CodingTheory/PolishchukSpielman/PolishchukSpielman.lean:45 | quotient/gluing step called by JointAgreement:674 |

[REPORTED upstream trust] These full-UD declaration names occur in neither
`sorry` nor `nonstandard` in the current `scripts/axiom_baseline.json`.
This lane read proof bodies and the upstream trust report; it did not rebuild
ArkLib or independently replay its axiom closure. Importing a module that has
other admitted declarations is not itself evidence of taint in a chosen theorem.

## Exact statement to prove, before implementation

[DERIVED target] Prefer an integer-radius core. It avoids differences between
ArkLib's finite unique-decoding radius and our open real-radius interface.
Here `n = Fintype.card ι`; `d` is dimension / degree **strictly below d**.

```lean
-- Proposed Prop, not a theorem claimed proved by this lane.
def FullUDCardCore (dom : ι ↪ F) (d e : ℕ) : Prop :=
  ∀ (f : Fin 2 → ι → F) (A : Finset F),
    (∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (f 0 + z • f 1) w ≤ e) →
    Fintype.card ι < A.card →
    ∃ S : Finset ι, Fintype.card ι - e ≤ S.card ∧
      ∀ j, ∃ w ∈ reedSolomonCode dom d, AgreesOn S (f j) w
```

[DERIVED theorem obligation] Prove this for finite nonempty index/field types,
`1 ≤ d`, `2*e+d ≤ n`. Do not retain the old small-radius antecedent
`d < (1−3δ)n`. The source argument uses `2*e+d ≤ n`, then polynomial matrix
interpolation and Polishchuk–Spielman to eliminate the old two-point transfer
loss. A finite-field `n<|F|` hypothesis is not mathematically necessary for
the implication, but is necessary for the `A.card>n` premise to fire.

[DERIVED resulting public head] With `d≤n`, derive directly in existing types:

```lean
IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
  ((1 + (d : ℝ) / (Fintype.card ι : ℝ)) / 2)
  (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
```

[DERIVED] For any `0<δ<(1−d/n)/2`, set `e=⌊δn⌋`; then `2e+d≤n` and
`n−e≥(1−δ)n`. Convert the good-slope cardinality to the existing probability
measure. Keep δ=0 and d=0 out of the initial head unless separately needed;
this avoids spending the first port on unconsumed corner cases.

## Witness, falsifier, and live consumers

[DERIVED satisfying witness] Use `F=ZMod 11`, `ι=Fin 8`, domain `i↦i`,
`d=4`, `e=2`, `A=univ`, `f₀(x)=x`, `f₁(x)=1`. Every slope is a codeword,
`|A|=11>8`, and `2e+d=8`. This inhabits the source premise at rate 1/2,
at a radius the current one-third bound does not cover. Prove its field and
embedding facts in the witness, not as axioms. This also witnesses all
nontrivial side conditions; use the existing finite-RS style, not a Unit code.

[EXECUTED falsifier] `evidence/derive.py` sampled candidate pairs with a fixed
seed, then exhaustively checked all 7 scalars and all 49 affine codewords over
F₇ for each witness, and all 49² codeword pairs for common agreement. At
`n=6,d=2,e=3`, `dom=(0,1,2,3,4,5)`, let

```
f0 = (3,0,4,1,3,3)
f1 = (6,4,1,1,6,3)
A  = F7
```

[EXECUTED] All 7 folds have a codeword agreeing in at least 3 of 6 positions;
no codeword pair jointly agrees with `(f0,f1)` in more than 2 positions.
Thus the intended conclusion is false when the radius premise is deleted:
`2e+d=8>6`. Full fold witnesses are saved in derive-output.txt.
This is a computed falsifier to port as a Lean theorem, not a kernel proof.

[SOURCE exact minidregg dependencies, HEAD 6937394e1dc2c2aaff986c7d4b3a258aca5d16fd]
All paths below are relative to `/Users/ember/dev/minidregg`:

| existing declaration | path:line | change or reuse |
|---|---|---|
| `CorrelatedAgreement`, `IsProximityGenerator` | Selvage/CorrelatedAgreement.lean:253,264 | reuse the exact existing language |
| `MutualCAFailure`, `HasMutualCorrelatedAgreement` | same:277,289 | reuse the event, not a replacement probability |
| `correlatedAgreement_of_close_card` | Selvage/ProximityGapUD.lean:215 | full-UD core supersedes its radius bottleneck |
| `reedSolomonCode_isProximityGenerator_UD` | same:475 | replace/generalize body and consumer head |
| `reedSolomonCode_hasMutualCorrelatedAgreement` | Selvage/ReedSolomon.lean:207 | existing CA→MCA, constant error monotone/nonnegative |
| `foldDistancePreserving_UD` | Selvage/ProximityGapUD.lean:534 | feed full-UD hPG into existing generic fold theorem |
| `proximity_sound_halfThen_UD` | Selvage/HalfThresholdFriTower.lean:231 | widen tail admissibility; no new tower induction |
| `committedFri_sound_halfThen_UD` | Selvage/HalfThresholdFriTranscript.lean:466 | consume widened tail with same commitment premises |
| `SoundnessParams`, `errStarUD` | Assurance/ErrorBudget.lean:79,109 | radius-admissibility widens; same error expression |

[DERIVED practical effect] At the inherited rate-1/2 point, the conservative
radius ceiling grows from 1/6 to 1/4; δ=1/5 becomes admissible. This expands
the proved decoder/fold interval without changing the one-challenge term or
claiming a larger composed security number. A half-threshold first round can
then feed δ/2 into the full-UD tail. Sampled recommitment/query/BCS/FS floors
remain independent obligations.

## Port boundary and bounded stopping criterion

[EXECUTED] `evidence/source_closure.py` recursively parses ArkLib source
`import` lines from UniqueDecoding.lean. At local 22dbd4e it finds 38 ArkLib
modules / 14,715 source lines, plus external CompPoly imports; this is a
**file-import inventory**, not theorem-level dependencies. The AffineLines
mathematical spine alone is 2,940 lines excluding its 48-line public wrapper.
The live-tip comparison changes only `Data/MvPolynomial/Multilinear.lean`
inside that local import closure; its difference is recorded in arklib-delta.json.

[SOURCE compatibility] ArkLib checkout uses Lean 4.33.1 / Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, CompPoly
`a09455a22fea4623a2a1c5b363cf6efc61486a83`. Minidregg uses Lean 4.30.0 /
Mathlib `1c2b90b13009c65b090d95a83c98e248deafb6f1`. Direct source import would
bring parallel code/probability definitions and CompPoly polynomial machinery.
It is not a one-file import or a proven compatible port.

[DERIVED recommended port] Reuse our code, distance, agreement, and probability
objects. Port the algebraic `BW_homMatrix` construction, determinant/kernel
bounds, and the needed bivariate quotient/gluing argument using Mathlib's
existing polynomial/resultant types. Do not copy ArkLib's general RS,
interleaving, decoder, or probability infrastructure merely because Prelude
imports them. The named missing primitive is the bounded bivariate A/B
certificate plus `polishchuk_spielman` conclusion, not the whole library.

[SOURCE license] ArkLib LICENSE and per-file headers are Apache-2.0, copyright
2024–2025 ArkLib contributors with named authors. Preserve those notices and
include source pin/attribution for adapted proof text; examine CompPoly's
license before copying any of its code (not done here).

[EXECUTED smaller algebraic slice] The rectangular matrix-kernel theorem
`BWMatrix.lean:1175` has a lexical same-file helper closure of 376 lines:
:606, :618, :630, :742, :760, :789, :937, :944, plus its own body. These are
matrix/polynomial lemmas, not RS or probability definitions. The extraction
and exact names are in evidence/matrix-declaration-closure.json. This is a
source-reference slice, not a kernel dependency census. `Fin.Embedding.snoc`
and `Nat.findGreatest` exist at our Mathlib pin. Root assigned the separate
`polynomial_kernel` lane to port this primitive, with the actual GoodCoeffs:647
consumer identified; this orientation lane does not claim its future result.

[DERIVED next bounded tranche] On an isolated minidregg checkout, first state
and inhabit the integer core; port the F₇ falsifier. Then close the smallest
polynomial-matrix primitive using existing Mathlib only and identify its real
consumer in the A/B construction. Stop with the exact checked primitive and
residual if the resultant/gluing dependency cannot be closed in that tranche.
A full-UD head stays OPEN until the radius premise, witnesses, complete proof,
axiom pins, and existing consumer build all pass. No direct companion edits,
new assumed carrier, or numeric headline should stand in for this work.

## Search and evidence limits

[EXECUTED counts] 4 web search queries; 11 direct web open/click/find requests;
1 Scry SQL query; 2 Scry schema calls (second preserved the response; duplicate
acknowledged); 9 GitHub API requests. No Kagi queries, no eprint requests or PDF
downloads from eprint. ECCC PDFs were read through web text extraction.

[SOURCE instrumentation] Scry academic.catalog reports a built-at extent
ending August 27; its single ordered title query returns seven rows, newest
relevant proximity work July 12. This corpus cannot test September novelty.
Evidence/scry-proximity.json contains the exact result and record id;
SOURCES.json records queries and commands. Absence claims in this note are
only the two pinned ArkLib source-file observations and baseline membership
checks, with their explicit instruments; no field-wide absence is asserted.

[OPEN] No local ArkLib kernel replay, no full proof audit of ECCC 169, no
numerical C/n₀/B certificate, no full-UD port or checked Lean patch, and no
companion/main-tree edits. STATUS.md/NEXT.md identify the resume point.
