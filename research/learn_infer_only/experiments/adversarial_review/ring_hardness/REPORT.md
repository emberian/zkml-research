# Independent ring-hardness mapping and finite-cost review

[DERIVED verdict, 2026-09-08] **Accepted within the declared generic
cost-model scope.** The exact unit-conditioned ring normal form, one-ring
sample loss, Gaussian parameter map, all 24 saved calls and their minima,
and both jointly rebuilt finite parameter points check out. The N=4096
point fails the named filter; N=16384 passes that filter. This is not a
proof of Ring-LWE hardness, a concrete security level, or a strict-QPT
sampler implementation. No author correction is required for this scope.

[EXECUTED scope] This review read frozen sources and retained estimator
outputs, and ran independent public integer/rational and small ring-map
arithmetic. It did not invoke Sage, an estimator, Gaussian sampling,
lattice reduction or a cryptographic protocol. It did not edit author
artifacts, companion trees, shared ledgers or commits. The mathematical
ring construction has a separate independent review; its ideal-sampling
acceptance and the new finite-sampler/QPT lane remain distinct.

## Frozen evidence and provenance

[EXECUTED] Author directory:
`research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_candidate/hardness/`.

| Artifact | SHA-256 |
|---|---|
| `AUDIT.md` | `84e3180ba5f6409dea7e590bbdd40c449a58a1d325efc773ef63ea11d35951ae` |
| `MODEL_AND_GRID.md` | `a3b0e6db5cc15d52fb1eee75ae580045391d7d73dd1ee6ac36797486d7eef7c8` |
| `MANIFEST.json` | `2f90bee88437465514066d879eddbc3918ab1af6d0c8d6592e63b0750adeef53` |
| `GRID.json` | `de246339b8321791cba308e01ef0f929a42d725e3bbdd7a8b533622a7011031a` |
| `estimates.jsonl` | `912c41ac012c82f72d3c1b0fa1d372b66580bb9c1192ffcd8a69b59181a945e4` |
| `SUMMARY.json` | `13ebec65a448b1f88831e4b06bff5bec3c92427ecd663b2a02cf6bf7fbab8f95` |

[EXECUTED] All 14 manifest-listed author artifacts, its manifest/seal,
four frozen parent links, prime certificate and named provenance records
remain unchanged. All 27 pinned estimator files match both current bytes
and the retained `git archive` carrying commit
`53da5982597709ba0fdf94ea37a84d822310fd84`. The runtime report identifies
Sage 10.8. No enclosing-repository `git rev-parse` value is substituted
for the estimator commit. The 53 frozen input records are in `INPUTS.json`.

[SOURCE/EXECUTED] The run manifest commits the exact mapping, grid and
driver hashes as predeclared inputs. The driver reads and validates them
before its nested two-point/four-model/three-path loop, refuses to overwrite
an existing JSONL, and has no retry or extra sweep. Retained START/RESULT
records match all 24 rows and finish with `FINISHED 24 24`; stderr is empty.
This supports the recorded run, not a claim about unobserved host processes.

## Exact ring normal form

[SOURCE/DERIVED] The frozen parent `CANDIDATE.md` §3 assumes one uniform
secret in `R_q=F_q[T]/(T^N+1)`, reused across 64 independent uniform ring
multipliers, with independent coefficient errors of mass proportional to
`exp(-πe²/1024²)`. Its secret dimension is N; its error tuple has 64N
coefficients. The expanded matrix has 64 negacyclic N-by-N blocks.

[DERIVED] On `E={A_1 is a unit}`, define for `i≥2`

```text
A_i' = -A_i A_1^-1,
b_i' = b_i - A_i A_1^-1 b_1 = b_i + A_i' b_1.
```

[DERIVED] In the real experiment, substitution gives exactly
`b_i'=A_i'e_1+e_i`; the original secret cancels. Given any unit `A_1`,
each remaining multiplier is mapped by a bijection, preserving independent
uniform ring values. Given all errors and `A_1`, the map
`s↦A_1s+e_1` is a bijection, so `b_1` is independent uniform even with
all errors retained. Thus the new secret is precisely the independent
coefficient Gaussian `e_1`, independent of `A_i'` and the remaining errors.
It is not a convolution or a Gaussian with a multiplied width.

[DERIVED] In the random experiment, subtracting a fixed function of
`A_i,A_1,b_1` from independent uniform `b_i` leaves independent uniforms.
Conversely, append independent uniform-unit `A_1` and uniform `b_1`, then
set `A_i=-A_i'A_1`, `b_i=b_i'-A_i'b_1`. This reconstructs the full
conditional tuple in either experiment. It also justifies dropping the
independent `A_1,b_1` auxiliary data. The map requires invertibility;
merely requiring a nonzero ring element would fail in the split ring.

[DERIVED] CRT gives independent uniform slots of `A_1`, and therefore

```text
Pr[not E] = 1-(1-1/q)^N ≤ N/q.
```

[DERIVED] Comparing unconditional and conditional laws at both endpoints
costs at most `2N/q` in distinguishing gap. This conservative bound is
valid; it does not condition away the event for free. It is an analysis
condition, not a rejection step or changed setup transcript. It spends
exactly one ring sample, yielding 63N scalar coordinates. The frozen
privacy theorem still names the original uniform-secret Ring-LWE premise;
no estimated cost is substituted for its advantage. Any future replacement
of that premise by a quantitative normalized one must account for the
comparison loss at the place where the computational term is used.

[EXECUTED] Independent small-ring controls in `F_5[T]/(T²+1)` find
16 units among 25 elements, matching the exact CRT unit law. All 400
unit-multiplication/translation maps are permutations, and 40,000 inverse
identities pass. These deterministic public algebra controls exercise the
map; the general conditional-distribution argument above proves it.

## Estimator mapping and its limits

[SOURCE] Pinned `estimator/nd.py:9–35,280–293` maps
`DiscreteGaussianAlpha(alpha,q)` to the standard-deviation parameter
`alpha*q/sqrt(2π)`. The exact rational input `alpha=1024/q` therefore
gives approximately `408.516895131067`, matching every row. The field is
a Gaussian parameter/moment proxy, not an exact infinite-distribution
calculation; `nd.py:230–277` also contains support/density approximations.
Neither the key width nor the scalar flood enters this error parameter.

[SOURCE/DERIVED] `lwe_parameters.py:34–65` replaces the larger uniform
secret by the error distribution and subtracts n samples when enough are
available. All paths explicitly receive this normalized object. Its
Gaussian coordinate means/standard deviations match, while secret and
error vector lengths are checked separately. The primal wrappers at
`lwe_primal.py:228,801` normalize again harmlessly: equal standard
deviations do not trigger another transformation. The public dual wrapper
at `lwe_dual.py:692–739` does not normalize; its optimizer explicitly
requires normalization at lines 254–281. The driver satisfies that
requirement. There are no raw-dual rows to exclude in this run.

| Parameter | N=4096 | N=16384 |
|---|---:|---:|
| Raw secret dimension | 4,096 | 16,384 |
| Raw scalar-coordinate count | 262,144 | 1,048,576 |
| Normalized scalar-coordinate count | 258,048 | 1,032,192 |
| Ring samples retained | 63 | 63 |
| Unit-failure upper bound | `<2^-276` | `<2^-274` |

[DERIVED] The exact map leaves negacyclic blocks. For example, even a
two-coefficient multiplication block is `[[a0,-a1],[a1,a0]]`, whose entries
are correlated. Normalization cannot turn those blocks into an independent
uniform scalar matrix. Both before and after normalization, the number of
uniform ring coefficients is far smaller than the number of entries in
the expanded scalar matrix.

[HYPOTHESIS] The cost estimates additionally assume that generic lattice
shape and success models apply to the selected structured lattices. Primal
uSVP/BDD use GSA (`simulator.py:91–119`, `lwe_primal.py:361–405`); dual
uses its generic short-vector/distinguishing model. Optimizing an arbitrary
number of scalar rows also assumes that corresponding partial ring blocks
behave as predicted. This is visible in the saved optimal dual row counts,
such as 17,370 at N=16,384, which are not whole-ring sample counts. The
matrix construction is possible; its predicted geometry is unproved here.

[SOURCE/DERIVED] The four classes are `MATZOV(nn='list_decoding-classical')`,
`ADPS16(mode='classical')`, `ADPS16(mode='quantum')` and
`MATZOV(nn='list_decoding-dw')`. `reduction.py:637–676` makes the ADPS
reduction costs `2^(0.292β)` and `2^(0.265β)`; these core-SVP costs
omit substantial work. The MATZOV fit at lines 963–995 has documented
coverage through β=1024. The saved β values are 60–632; BDD's additional
SVP dimensions are at most 673. None is at the β=40 floor or outside
that stated fit range. A quantum reduction-cost model does not provide
a full end-to-end quantum implementation of every surrounding operation.

## All calls and minima

[EXECUTED] Exactly 24 distinct declared tuples are retained, all entered
and completed, with zero errors, timeouts or nonfinite numeric fields.
All 56 stored logarithms agree with the retained numeric dictionaries;
BDD totals agree with reduction plus SVP work, and ADPS reduction terms
agree with their named slopes. Optimal dimensions fit within available
samples. The sum of estimator-calculation times is 58.32683895895025
seconds, not attack latency.

[EXECUTED] Independently selected minima over uSVP, BDD and normalized
dual agree with all eight reported records:

| Cost model | N=4096: log2 cost / path / β | N=16384: log2 cost / path / β |
|---|---|---|
| MATZOV classical | 51.944007 / BDD / 60 | 211.909745 / BDD / 629 |
| ADPS16 classical | 17.812000 / uSVP / 61 | 184.252000 / uSVP / 631 |
| ADPS16 quantum core-SVP | 16.165000 / uSVP / 61 | 167.215000 / uSVP / 631 |
| MATZOV quantum depth×width | 55.750336 / BDD / 60 | 199.731572 / BDD / 629 |

[EXECUTED] Larger-point dual costs are respectively 213.429623,
184.544000, 167.480000 and 201.430075. All exceed the corresponding
primal minimum. These four model metrics are kept distinct; there is no
single cost-unit conversion supplied by taking their overall minimum.

[DERIVED] It is appropriate to reject N=4096 from this design's declared
cost filter: even the more detailed MATZOV estimates lie far below 128.
This is a heuristic parameter-screening conclusion, not an executed break.
N=16384 passes the same filter. That outcome is no lower bound against
structured-ring, ideal/subfield, CRT, algebraic, hybrid, BKW, alternative
shape or future methods. Their absence from the 24-entry grid is declared
coverage, not a literature-wide absence claim. A fixed-success cost does
not give the advantage-versus-work curve needed by the privacy reduction.

## Coupled finite parameter and size checks

[EXECUTED/DERIVED] Both points use
`q=4294967767·2^256+1`, with `2^288<q<2^289`. The base-3 certificate
is exact: its `(q-1)/2` power is −1. For every prime divisor of q,
the order consequently has two-adic part `2^256`; that divisor must
be at least `2^256+1>sqrt(q)`. Hence q is prime. No probable-prime
test or estimator establishes that fact. The computed roots have powers
`ζ^N=-1,ζ^(2N)=1`, proving exact order 8192/32768 and complete splitting.
The independent checker also proves the small plaintext prime by trial
division. The large two-adic factor proves splitting, not hardness.

[SOURCE/DERIVED] The ring regularity and ideal proof are separately
reviewed in `../ring_fixed_coordinate/REPORT.md`, SHA-256
`5183db756af984c34a45f270bd7b33700942b2b9a7989bdd9116e517a5567d18`.
Here their hypotheses are instantiated independently for both points:
N is a power of two at least 16, w=64, θ=3/64, k in {1,2},
δ=2^-192, and `wθ-k=3-k>0`. Increasing N changes these numerical
bounds and the coefficient count; the baseline substitution is not reused.

[EXECUTED/DERIVED] The exact raised-power checks are

```text
σK^64 ≥ (N L)^32 q^3,     L=212 or 214,
q^122 ≥ N^64,
N Σ_(i=0)^(k-1) q^(i-64) + 2^N/q^(3N(3-k)/64) < 2^-192.
```

[DERIVED] The first bounds the actual smoothing expression because
`ln(2Nw(1+2^192))/π<L`; the second implies the required short-vector
threshold is at least one. The rank/short event is charged once for the
whole shared-matrix tuple; retained independent recipient rows do not
multiply that bad event. On good matrices the h replaced rows cost
`2hδ`. Both setup k=1 and augmented masking k=2 satisfy their premises.

[EXECUTED/DERIVED] The larger point raises σK from `2^24` to `2^25`
and F from `2^244` to `2^247`. With `BK=8σK, BE=8192`, this changes
`C=wN BK BE` from `2^58` to `2^61`. The eightfold flood increase
keeps the leading smudging ratio controlled. The coefficient tail uses
the integer-Gaussian normalizer being at least one and the decreasing
sum/integral bound `Pr[|G|≥8σ]<3σ·2^-256`. It is a bound on the
stated ideal Gaussian, not a finite sampler's discrepancy.

[EXECUTED] All 17 fixed coalition sizes at each point pass

```text
2 δ_(d-r)(1) + 2T(S + δ_(d-j)(2)) < 2^-168,
τK + T τe < 2^-203  (N=4096), or < 2^-200 (N=16384).
```

[EXECUTED] With d=577, r=16, W=32, T=384, X=14,219,946 and
`D=8,204,908,842`, both pass `D≥2WX+1`, `Δ=floor(q/D)>2W(F+C)`
and the circular endpoint gap `q-2WXΔ≥Δ`. Thus the changed flood
preserves the declared nearest-codepoint decoding range; no floor-scaling
rounding decoder is silently substituted. Exact comparisons determine
acceptance. Informational floating logarithms in `results.json` only
describe the margin and do not decide any inequality.

| Ideal representation or arithmetic | N=4096 | N=16384 |
|---|---:|---:|
| Ciphertext residues | 262,721 | 1,049,153 |
| Ciphertext bytes at 289 bits/residue | 9,490,797 | 37,900,653 |
| Public A+P bytes | 94,847,488 | 379,389,952 |
| Recipient coefficient bits, strict event | 28 | 29 |
| One recipient row bytes | 917,504 | 3,801,088 |
| All 16 recipient rows bytes | 14,680,064 | 60,817,408 |
| Fresh full ring products | 64 | 64 |
| Scalar coefficient products for `const(P_i s)` | 2,363,392 | 9,453,568 |
| Gaussian error coefficients per input | 262,144 | 1,048,576 |
| Recipient-read coefficient products | 262,144 | 1,048,576 |
| Add/subtract residue operations | 262,721 | 1,049,153 |

[DERIVED/EXECUTED clarification] The dN coefficient-product row prices
the d negacyclic constant-coefficient inner products. Fresh encryption
also has d=577 message-scale products `Δa_i`, 577 scalar flood draws,
and N uniform-secret coefficients, plus the public F_p basis transform.
Those are separate from dN; no full encryption operation total is claimed.
The author was notified of this clarification. Public A+P excludes B and
metadata. Strict `|z|<BK` permits 28/29 signed bits; inclusive endpoints
need one more. These are high-probability ideal row sizes, not worst-case
storage for unbounded Gaussians. Ring products grow in cost with degree;
their unchanged count does not imply unchanged runtime or NTT workspace.

## Accepted scope and outstanding work

[DERIVED] The frozen ideal proof's `768 εRLWE+2^-168` remains conditional
on the exact original Ring-LWE advantage. The cost filter neither bounds
that advantage nor converts its factor 768 into a security-bit subtraction.
Its statistical terms, coefficient-tail correctness, modeled attack costs
and mathematical representation sizes are different claims.

[OPEN] Exact unbounded-support Gaussians are not literal bounded-QPT
samplers. Cutoff, finite-precision sampling, bounded runtime and rejection
transcript distributions require their own discrepancy/resource accounting.
Uniform sampling modulo q also needs a finite resource contract. The same
quantum-advice class as the adversary, independent of fresh coins and bit,
must be permitted by a computational assumption; one-copy straight-line
usage does not create that assumption. The separately assigned sampler
lane may close parts of this gap, but its unfinished work is not imported
into the present frozen verdict. LPR dual-ideal/canonical-error/discrete-law
and finite-sample theorem mapping remains a separate source obligation.

[EXECUTED] Reproducible independent command:

```text
python3 research/learn_infer_only/experiments/adversarial_review/ring_hardness/check.py > research/learn_infer_only/experiments/adversarial_review/ring_hardness/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/ring_hardness/stderr.txt
```

[EXECUTED] PASS, exit zero; stdout equals `results.json`, stderr is empty.
The check compares 46 parameter/cost fields in addition to all roots,
34 coalition ledgers, full recorded-call identities, eight minima and
56 numeric logarithms. All 53 named public inputs remain unchanged.
Source discovery used local named files and `rg`; new web queries 0,
Scry queries 0 and PDF downloads 0. Prior primary-source ring theorem
review is cited at its exact frozen scope rather than repeated.
