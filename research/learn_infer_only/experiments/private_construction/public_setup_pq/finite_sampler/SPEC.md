# A strict bounded-time reference sampler for the repaired ring/scalar proofs

[DERIVED specification, 2026-09-08] This specification is frozen before
any sampler implementation. It supplies a finite random-bit algorithm for
independent centered integer Gaussians with mass proportional to
`exp(-πk²/σ²)`, including the repaired ring widths `σe=2^10,σK=2^25`
and the smudged scalar key width `σK=2^32`. It gives a conservative error
and resource certificate, not a practical implementation or timing claim.
No random samples, private keys, ciphertexts or lattice attacks are generated.

## 1. Exact ideal law, finite coins and scope

[DERIVED] Let `σ=2^a`, integer `a≥0`, and

```text
ρσ(k)=exp(-πk²/σ²),     Zσ=Σ_(k∈Z) ρσ(k),
Dσ(k)=ρσ(k)/Zσ.
```

[DERIVED] The specification consumes independent unbiased bits, with a
fixed worst-case bound. A deterministic CSPRNG with a finite seed does
not produce a statistically uniform long tape; replacing the independent
bits requires a separate computational PRG assumption at the actual
output length/resources and, where needed, against the same QPT/advice
class. No particular CSPRNG is assumed or executed here.

[DERIVED] Every recipient must have independent private sampling coins;
fresh encryption coins stay private. A shared secret seed from which all
recipient rows can be recovered would change the credential lifecycle.
No rejection tape, running-time trace or seed is included in the public
accepted-value transcript. The bounded algorithm may stop early; this is
not a constant-time or side-channel guarantee.

[DERIVED scope] Independent coefficient Gaussians and exact integer
translations are covered. The reference does not by itself implement
general correlated, continuous, rotated, singular-covariance or
conditional multivariate Gaussian samplers used in other ALS reductions.
The ring and direct smudged-scalar constructions need the covered product
laws. Their construction/closure and hardness assumptions remain separate.

## 2. Fixed constants and algorithm

[DERIVED fixed constants]

```text
cutoff B=8σ;   proposal size M=16σ=2^(a+4);
acceptance precision b=256 bits;
arithmetic precision P=320 fractional bits, Q=2^P;
rejection cap R=4096 attempts;  cap fallback = integer zero.
```

[DERIVED algorithm] For attempts 1 through R:

1. Read `a+4` fresh unbiased bits as `v∈[0,M)`, and set `k=v−B`.
2. If `k=−B`, reject this attempt. Otherwise compute the public
   deterministic threshold `Lσ(k)∈[0,2^b]` specified in §3.
3. Read `b` fresh unbiased bits as `u∈[0,2^b)`. Return `k` if
   `u<Lσ(k)`; otherwise continue.

[DERIVED] If all R attempts reject, return zero. The boundary rejection
gives symmetric support `S={k:|k|<B}` without an additional non-power-of-
two proposal sampler. Unused bits need not be generated. A worst-case
reservation uses `R(a+4+b)` bits per output, including a full acceptance
word even on a boundary rejection. No infinite loop or exact comparison
with an irrational is part of the algorithm.

## 3. A fully specified rigorous threshold

[DERIVED contract] The following integer/rational arithmetic gives

```text
0 ≤ ρσ(k) − Lσ(k)/2^b < 2^(1-b),      |k|<B.
```

[DERIVED π interval] Before sampling, use the exact Machin identity
`π=16 arctan(1/5)−4 arctan(1/239)`. For `c∈{5,239}`, let

```text
Ac = Σ_(j=0)^79 (-1)^j / ((2j+1)c^(2j+1)),
Ec = 1/(161 c^161).
```

[DERIVED] Alternating-series bounds give `arctan(1/c)∈[Ac,Ac+Ec]`.
Thus take the rational interval
`[16A5−4(A239+E239), 16(A5+E5)−4A239]`, whose width is less than
`2^-360`. The Machin identity follows by the tangent addition formula
and the angles' principal intervals. Round its endpoints outward to the
`1/Q` grid, obtaining integer endpoints `pL,pU` with `π∈[pL/Q,pU/Q]`
and `pU−pL≤3`. All operations here are finite rational arithmetic; the
same certified constants are reused for every draw.

[DERIVED reduced exponent] For a proposed k, form

```text
uL = floor(pL k²/(256σ²)),
uU = ceil (pU k²/(256σ²)).
```

[DERIVED] Then the real value `z=πk²/(256σ²)` lies in
`[uL/Q,uU/Q]⊂[0,1]`, since `|k|<8σ` and `π<4`. The integer
interval has width at most 4. Endpoints and squares are evaluated with
integer arithmetic; division by `σ²` is a shift because σ is a power
of two. This step does not assign π a machine floating-point value.

[DERIVED Taylor terms] Let `tL_0=tU_0=Q`. For `j=1,...,80`, compute

```text
tL_j = floor(tL_(j-1) uL/(jQ)),
tU_j = min(Q, ceil(tU_(j-1) uU/(jQ))).
```

[DERIVED] These bracket `Q z^j/j!`. Define the signed Taylor interval

```text
sL = Σ_(j even) tL_j − Σ_(j odd) tU_j,
sU = Σ_(j even) tU_j − Σ_(j odd) tL_j,    j=0,...,80.
vL = max(0,sL−1),        vU = min(Q,sU).
```

[DERIVED] The even Taylor polynomial bounds `exp(-z)` from above, and
the next-term remainder is at most `1/81!<1/Q`; hence
`exp(-z)∈[vL/Q,vU/Q]`. All sums are exact integer sums. This subtracts
one grid unit as a remainder bound rather than asserting an exactly
rounded exponential.

[DERIVED width proof] With input width at most 4 grid units, the term
width obeys `d_j≤(d_(j-1)+4)/j+2`, with `d_0=0`. Thus `d_1≤6`
and `d_j≤8` for all subsequent terms. The Taylor interval width is
at most `80·8+1=641` units. Now perform exactly eight directed squarings,
each replacing

```text
vL ← floor(vL²/Q),       vU ← min(Q,ceil(vU²/Q)).
```

[DERIVED] The interval continues to enclose the corresponding power;
its width changes by at most `d↦2d+2`. After eight squarings it encloses
`exp(-256z)=ρσ(k)` with width below `2^19/Q=2^-301`. Finally set
`Lσ(k)=floor(vL/2^(P-b))`. This is a lower threshold, with error below
`2^-b+2^-301<2^(1-b)`. `Lσ(0)=2^b` may instead be supplied directly.

[DERIVED arithmetic cost] A direct threshold evaluation uses 160 bounded
integer products for the Taylor interval and 16 for the squarings, plus
the square of k and two reduced-exponent products: at most 179 integer
products per attempt. The 176 Taylor/squaring products have operands at
most P+1 bits. The three initial products additionally depend on the
`a+4`-bit proposed coefficient. Divisions by `jQ`, shifts, additions and
comparisons are additional work. This is a reference upper count; no
hardware latency is inferred.

## 4. Normalization and cutoff without a spurious σ factor

[DERIVED exact normalization] Periodizing `exp(-πx²/σ²)` gives Fourier
coefficients `σ exp(-πσ²j²)`. Absolute convergence permits evaluating
the Fourier series at zero, yielding the one-dimensional Poisson identity

```text
Zσ = σ Σ_(j∈Z) exp(-πσ²j²) ≥ σ.
```

[DERIVED tail] For integer `B=8σ`, monotonicity and an integral bound give

```text
Σ_(k≥B) ρσ(k)
 ≤ [1+σ²/(2πB)] exp(-πB²/σ²).
Pr_Dσ[|k|≥B]
 ≤ [2/σ+1/(8π)] exp(-64π)
 < 3·2^-256 =: τ.
```

[DERIVED] The last inequality uses σ≥1 and `π>4 ln 2`. The latter
already follows from π>3 and `ln2<7/10`; a finite Taylor lower bound
for `exp(7/10)` proves it exceeds 2. Dividing by `Zσ≥σ` removes the
unnecessary σ factor that would arise from using only `Zσ≥1`.
The cut law is the ideal Gaussian conditioned on S, so its total variation
from the original law is exactly its excluded tail probability.

## 5. Threshold and attempt-cap losses

[DERIVED] Write `Z_S=Σ_(k∈S)ρσ(k)≥σ(1−τ)`, and let
`ρ'_k=Lσ(k)/2^b`. Then `0≤ρσ(k)−ρ'_k<2^(1-b)`. Since there
are fewer than M supported integers, the removed acceptance mass is
`E=Σ_S(ρσ−ρ')<M2^(1-b)`.

[DERIVED accepted-law coupling] Conditional on acceptance, the rounded
law has mass `ρ'_k/(Z_S−E)`. The ideal cut law is a convex mixture of
this retained law and the normalized removed mass. Hence their distance
is at most `E/Z_S`, without losing another normalization denominator:

```text
TV(rounded accepted law, ideal cut law)
 ≤ E/Z_S < [16/(1−τ)] 2^(1-b) < 64·2^-256.
```

[DERIVED acceptance and cap] The per-attempt success probability obeys

```text
α = (Z_S−E)/M ≥ (1−τ)/16 − 2^(1-b) > 1/17.
```

[DERIVED] Independent repeated proposals make the first accepted output
have the rounded accepted law, even conditional on success within R
attempts. Failure probability is at most `(16/17)^4096<2^-256`, since
the binomial theorem gives `(17/16)^16>2`. The fallback mixture therefore
adds less than `2^-256` total variation. Expected attempts, including the
cap, are at most 17; worst-case attempts are exactly bounded by 4096.

[DERIVED per-output certificate] By the three comparisons,

```text
TV(reference finite sampler, Dσ) < (3+64+1)2^-256
                                  = 68·2^-256 < 2^-249.
```

[DERIVED] This is uniform in every allowed σ. It concerns the complete
output law, including fallback; it does not discard rare events after
looking at a transcript. Independent product hybrids and subsequent
classical or QPT channels can sum these bounds.

## 6. Actual workload and reduction-wide draw accounting

[SOURCE/DERIVED] The repaired ring has `wN=1,048,576`, `d=577,r=16`,
and `T=384`. Actual setup samples r recipient rows, not d secret rows.
Encryption samples wN error coefficients per fresh input. The proof's
one-shot computational reduction can conservatively budget d full rows
plus T error vectors, including an extra target error allowance.

| Gaussian draws | repaired ring | smudged scalar repair |
|---|---:|---:|
| coefficients per row/error vector | 1,048,576 | 262,144 |
| actual recipient-key coefficients | 16,777,216 | 4,194,304 |
| all 384 encryption-error coefficients | 402,653,184 | 100,663,296 |
| total actual Gaussian draws, Qactual | 419,430,400 | 104,857,600 |
| proof-only full d-row coefficients | 605,028,352 | 151,257,088 |
| one reduction allowance, Qred | 1,007,681,536 | 251,920,384 |

[SOURCE] The scalar counts use the frozen direct smudged construction's
repaired height `l=262144`, error width `2^10`, key width `2^32`, and
the same d,r,T. This does not import unrelated multivariate ALS samplers.

[DERIVED conservative loss ledger] Let ν denote the per-output bound.
Moving the real finite-sampling scheme to its ideal distribution costs
at most `2 Qactual ν` across the two bit worlds. Replacing each ideal
one-shot LWE reduction by its bounded sampler changes both computational
challenge worlds by at most `2 Qred ν`. The frozen computational loss
has multiplier `2T`; therefore a safe additional term is

```text
δGauss ≤ [2Qactual+4TQred] ν.
```

[DERIVED] Summing this allowance for both repaired ring and scalar points
is below `2^41·68·2^-256<2^-208`, hence below the declared aggregate
Gaussian-sampler budget `2^-192`. This deliberately counts more draws than
a tightly implemented target reduction needs. It does not multiply the
actual setup cost by T or assert that proof-only secrets exist in reality.

## 7. Other finite uniform draws and computational randomness

[DERIVED bounded uniform sampler] For an integer range `[0,m)`, draw
`ceil(log2 m)` unbiased bits, accept values below m, and cap at 512
attempts, falling back to zero. A successful output is exactly uniform;
failure probability is at most `2^-512`. This covers the prime-modulus
coefficients and the scalar flood range of size `2F+1`, with the flood
offset subtracted afterward. The scalar flood is not Gaussian.

[DERIVED coarse workload allowance] A bound of `2^45` such uniform
outputs over both constructions' full finite-to-ideal/reduction ledgers
is conservative for these fixed dimensions, even charging each reduction
for the scalar setup's entire `l·n` public matrix. Their aggregate uniform-
cap loss is below `2^-467`. Together with §6 the additional independent-
bit sampling loss is below `2^-207`, comfortably inside `2^-192`.

[DERIVED computational interface] Bounded rejection, finite rational
constants, integer arithmetic and a bounded bit tape give a strict finite
probabilistic algorithm. For the usual polynomially bounded parameter
families these operations admit bounded polynomial circuits. Quantum
advice is passed once through the existing straight-line reduction; the
same advice class must be allowed by the LWE/PRG hypotheses. A finite
CSPRNG substitution adds a separate distinguishing term at its total
tape length; it cannot be hidden inside the statistical certificate.

## 8. Resource price and alternatives

[DERIVED] The direct reference has at most 17 expected attempts and
4096 worst-case attempts per output. At the repaired ring's 419,430,400
actual Gaussian draws this allows billions of proposals and roughly a
trillion 320-bit arithmetic products in the direct expected-work bound.
The cap bound is much larger. Exact bit/product totals are to be recorded
by a deterministic arithmetic helper; no timing or feasibility measurement
has been made. The reference establishes existence with explicit finite
resources, not inexpensive cryptographic sampling.

[DERIVED optional table price] A full acceptance-threshold table has
`16σ−1` entries of b bits. It is small for σ=1024, but grows to almost
17.2 GB for σ=2^25 and almost 2.2 TB for σ=2^32. A table avoids repeated
exponential evaluation but changes memory and access-pattern costs; no
table is generated here.

[SOURCE alternative, inspected algorithm] Karney's Algorithm D samples
discrete normal laws using exact comparisons when its mean and standard-
deviation parameters are rational. Its rejection and digit-comparison
loops have variable length; the paper supplies an implementation lead
and expected-work discussion. Our π-width corresponds to irrational
standard deviation `σ/sqrt(2π)`, so direct reuse needs a rational-width
approximation bound and explicit loop/digit caps. We do not inherit a
strict finite resource certificate. [Karney, §4](https://arxiv.org/html/1303.6257)

[SOURCE scoped library check] Falcon's public reference `sign.c` uses a
half-Gaussian base with standard deviation 1.8205 and 72-bit precision;
its full sampler requires standard deviation between 1 and 2. That
source is not a drop-in sampler for our widths or aggregate accuracy.
No Falcon algorithm was executed. [Falcon source, lines 1090–1092 and
1348–1353](https://falcon-sign.info/impl/sign.c.html)

[OPEN] A faster audited sampler may replace this reference if its complete
finite output error and worst-case resources fit the same budget. Actual
implementation, side-channel discipline and PRG instantiation are separate
work. No sampler implementation is authorized by this frozen specification
alone, and no private sampling will occur in this source/math lane.
