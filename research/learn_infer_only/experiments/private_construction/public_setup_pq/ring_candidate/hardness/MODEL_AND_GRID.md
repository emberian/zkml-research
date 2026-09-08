# Ring computational plausibility: model and declared grid

[DERIVED, 2026-09-08, before estimator calls] This separate audit leaves the
frozen ring construction and its ideal-distribution proof unchanged. It asks
whether generic primal/dual lattice heuristics already reject the exact
Ring-LWE premise, and prices a jointly repaired dimension. Passing these
heuristics would not establish Ring-LWE hardness or a concrete QPT theorem.

## 1. Exact problem and width map

[SOURCE] The frozen `../CANDIDATE.md` assumes the classical tuple
`(A,As+e)` versus `(A,u)` over `R_q=F_q[T]/(T^N+1)`, with `w=64`
independent uniform ring entries of `A`, one uniform ring secret `s`, and
independent coefficient errors of mass proportional to
`exp(-πe²/1024²)`. Thus `s` has `N` coefficient dimensions. The expanded
matrix consists of 64 negacyclic multiplication blocks of shape `N×N`.
It is not an independent uniform scalar matrix of shape `(64N)×N`.

[SOURCE/DERIVED estimator input] In the existing pinned estimator,
`nd.py:280–293` maps `DiscreteGaussianAlpha(alpha,q)` to standard deviation
`alpha*q/sqrt(2π)`. The raw comparison input is therefore

```python
LWE.Parameters(n=N, q=q, Xs=ND.UniformMod(q),
               Xe=ND.DiscreteGaussianAlpha(QQ(1024)/q, q), m=64*N)
```

[DERIVED] The error standard-deviation parameter is approximately 408.5.
It is neither 1024 nor the flooding width or recipient-key width.
Because `2^288<q<2^289`, `2^-279<1024/q<2^-278`. Increasing `N`
does not change this tiny relative width. The estimator represents Gaussian
moments and finite-support approximations; it is not an exact probability
engine for the infinite discrete Gaussian.

## 2. Ring normal form, with an explicit exceptional event

[SOURCE] `lwe_parameters.py:34–65` converts a larger secret to the error
distribution and removes `n` scalar samples when `m≥2n`. The internally
normalizing primal wrappers are `lwe_primal.py:228,801`. The public dual
wrapper `lwe_dual.py:692–739` passes its argument to an optimizer whose
docstring at lines 254–281 requires normalized input. This audit will
explicitly normalize once for every path, and check the actual resulting
per-coordinate distributions and vector dimensions before each entry.

[DERIVED exact ring counterpart] Scalar normalization alone is not a proof
for this structured distribution. Here a direct ring argument is available.
Let `(A_i,b_i)` be the ring samples and condition on `A_1` being a unit.
For each `i=2,...,w`, define

```text
A_i' = -A_i A_1^-1,
b_i' = b_i - A_i A_1^-1 b_1.
```

[DERIVED] In the real world, `b_i'=A_i' e_1+e_i`. Given the unit `A_1`,
the remaining `A_i'` are still independent uniform ring elements. Since
the original secret is uniform, `b_1` is independent uniform even given
all errors. The new secret `e_1` has independent width-1024 Gaussian
coefficients and is independent of the remaining errors. The random world
likewise maps to independent uniform `b_i'`. Conversely, independently
sample a uniform unit `A_1` and uniform `b_1`, then set
`A_i=-A_i'A_1`, `b_i=b_i'-A_i'b_1`; this reconstructs the conditional
tuple in either world. No Gaussian-width conversion occurs.

[DERIVED loss and count] Complete splitting gives
`Pr[A_1 is not a unit]=1-(1-1/q)^N≤N/q`. Conditioning differs from
each original world by at most this probability, so a conservative
two-world distinguishing-gap comparison charges `2N/q`. This is an
analysis condition, not an extra rejection step in the actual construction.
One entire ring sample is spent: the normalized input has `n=N` and
`m=(w-1)N`. For the two declared points the unit-failure bound is below
`2^-276` and `2^-274`, respectively. We do not treat it as evidence of
computational hardness. The frozen proof still uses its original exact
uniform-secret Ring-LWE premise.

## 3. The remaining heuristic map

[HYPOTHESIS generic geometry] The normal-form argument above is exact on
its stated event. It leaves 63 negacyclic multiplication blocks, so it does
not make the scalar rows independent. Feeding the dimensions and moments
to a generic scalar estimator additionally assumes that the selected
structured q-ary lattices exhibit the basis shapes and success behavior
predicted by that estimator. It also assumes its optimization over a number
of scalar rows remains representative of the corresponding subsets of
ring blocks. We have no theorem or experiment validating those assumptions
for this exact split modulus and distribution.

[SOURCE/INFERRED] The pinned README lines 18–20 describes heuristic cost
and shape predictions. Its `simulator.py:91–119` implements GSA, with
`lwe_primal.py:361–405` applying GSA and Gaussian-heuristic success
conditions. The dual path uses its own root-Hermite/length and distinguishing
model. The proposed calls price generic uSVP, BDD and dual paths. A small
modeled cost is a reason to reject a parameter candidate pending further
scrutiny; a large modeled cost is not a lower bound against all attacks.

[OPEN structured possibilities] The declared estimator coverage omits
ideal/subfield/algebraic exploitation, correlated ring rotations,
automorphisms, CRT-specific opportunities, alternative lattice shapes,
hybrid guessing, dual-hybrid, BKW and unmodeled algorithms. No claim of
their applicability or inapplicability to this modulus follows from the
generic grid. In particular, the prime's explicit large power-of-two factor
in `q-1` proves splitting, not computational security.

[SOURCE models] The fixed paths will use these unchanged source classes:

| label | exact model |
|---|---|
| MATZOV classical | `MATZOV(nn='list_decoding-classical')` |
| ADPS16 classical | `ADPS16(mode='classical')` |
| ADPS16 quantum core-SVP | `ADPS16(mode='quantum')` |
| MATZOV quantum depth×width | `MATZOV(nn='list_decoding-dw')` |

[SOURCE/DERIVED limits] The source definitions are `reduction.py:637–676,
739–756,963–995`; its MATZOV fit comment states coverage through block
size 1024. Core-SVP counts omit costs that other models include. A quantum
reduction-cost choice does not quantize every surrounding subroutine.
Block-size floor 40, timeouts, exceptions, Infinity, extrapolation beyond
the documented fit, and missing outputs will be reported explicitly.
No failed entry or Infinity will be read as evidence of hardness.

## 4. Two jointly consistent points, declared before outputs

[EXECUTED] `python3 prepare_grid.py` performs public integer/Fraction
arithmetic only and records `GRID.json`. Both points use the same prime

```text
q = 4294967767·2^256+1
  = 497323290947860672931310292648754779192460749687510494957169639477681564739617435942913.
```

[DERIVED/EXECUTED] The existing base-3 order certificate proves primality;
it also gives a root of exact order `2N` at both degrees. The new degree
uses a newly computed public root, checked exactly in `GRID.json`.
No new prime search, probable-prime inference or estimator call was used.
Shared parameters are `w=64,d=577,r=16,W=32,T=384,p=28,439,893`,
`D=d(p-1)/2=8,204,908,842`, `σe=2^10`, `BE=8σe`,
`θ=3/64`, and smoothing quotient parameter `2^-192`.

| point | N | σK | F | raw m | normalized m |
|---|---:|---:|---:|---:|---:|
| frozen baseline | 4,096 | 2^24 | 2^244 | 262,144 | 258,048 |
| coupled larger degree | 16,384 | 2^25 | 2^247 | 1,048,576 | 1,032,192 |

[DERIVED repair] Increasing degree fourfold doubles the sufficient key
width and multiplies `C=wN·BK·BE` by eight, from `2^58` to `2^61`.
The flood radius also increases eightfold. The original prime already has
enough decoder margin; there is no need to change `q` or its security
problem. Merely changing the estimator's dimension while retaining the
old key/flood parameter ledger would not be this coupled point.

[EXECUTED finite checks] Both points satisfy the exact raised-power
smoothing inequality, short-vector/rank bounds for `k∈{1,2}`, all 17
coalition-size privacy ledgers, `D≥2WX+1`, and `floor(q/D)>2W(F+C)`.
Their ideal non-LWE privacy term is below `2^-168`. Correctness failure is
below `2^-203` for the baseline and `2^-200` for the larger degree. The
strict key tail bounds include the one-bit storage distinction at the
endpoints. These numbers remain independent of any hardness estimate.

| ideal bit-packed quantity | N=4096 | N=16384 |
|---|---:|---:|
| ciphertext bytes | 9,490,797 | 37,900,653 |
| public A+P bytes | 94,847,488 | 379,389,952 |
| one recipient key bytes, strict tail event | 917,504 | 3,801,088 |
| fresh encode full ring products | 64 | 64 |
| fresh encode scalar coefficient products | 2,363,392 | 9,453,568 |
| fresh encode Gaussian coefficients | 262,144 | 1,048,576 |
| recipient read coefficient products | 262,144 | 1,048,576 |

[DERIVED] A ring product is degree-dependent; keeping its count at 64
does not imply equal runtime at the two degrees. These counts are neither
NTT timings nor allocator/wire-format measurements.

## 5. Call budget, provenance and interpretation

[DERIVED predeclaration] Proposed budget: exactly 24 estimator entries,
`2 points × 3 paths × 4 models`, with 45 seconds per entry. All receive
the explicitly normalized parameter tuple; uSVP and BDD use GSA. There
are no beta-2 probes, endpoint primes, additional noise widths, hidden
parameter sweeps or implicit retries. Exceptions/timeouts count as entries.
The exact grid and count were sent to root before any estimator call.

[EXECUTED source pin] All 27 source files match the existing scalar audit's
manifest for archive commit `53da5982597709ba0fdf94ea37a84d822310fd84`.
The runtime is the already installed Sage 10.8 environment, to be reused
without package or source changes. The snapshot was produced by `git archive`
and has no own `.git`; a naive `git -C ... rev-parse HEAD` resolves the
surrounding research repository and is not an estimator pin. This audit
uses the archive provenance and verified named hashes instead.

[OPEN QPT instantiation] A standard bounded QPT machine cannot output an
unbounded-support Gaussian exactly. The frozen ring statement is an ideal
distribution ledger; finite sampler/cutoff discrepancy and runtime still
need explicit accounting. A literal QPT hypothesis must permit the same
quantum-advice class as the adversary, with advice independent of fresh
coins and the bit. Generic estimates do not establish that hypothesis.
LPR dual-ideal/canonical-embedding/discretization and finite sample-count
theorem mapping also remains unproved here.

[DERIVED interpretation] The factor 768 in the privacy theorem is a
distinguishing-advantage loss. Subtracting `log2(768)` from a cost at a
fixed success probability does not establish a concrete security bound.
No estimated cost will be called certified security bits, and no larger
relative-error repair will be claimed unless its setup/flood/decoder
inequalities are rebuilt together.

[EXECUTED meter at predeclaration] Zero estimator calls, zero Sage calls,
zero cryptographic instances or lattice attacks, zero Gaussian samples,
zero new web/Scry queries and zero PDF downloads. The Python preparation
uses only public parameter arithmetic and source hashes. No broad absence
claim is made.
