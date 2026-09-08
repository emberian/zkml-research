# Independent review: finite Gaussian regularity and PQ sizing

[DERIVED disposition, 2026-09-08] **Accept the finite regularity certificate,
the stated ideal-Gaussian correctness bound, and the numerical sizing
accounting.** No correction to the frozen originals is required. These are
finite mathematical certificates and coefficient-one sizing examples, not
certified QPT security parameters. Two source-backed improvements to the
conservative correctness/work accounting are derived in §5 below.

[EXECUTED frozen subjects]

| Subject | SHA256 |
| --- | --- |
| `private_construction/public_setup_pq/costs/FEASIBILITY.md` | `037b1b7995dbaec14cc983c7aea639496d1aeeed164f2a207ce3207c3a70372c` |
| `adversarial_review/public_setup_pq/quantitative_regularity/BOUND.md` | `b07d7714ca6078a63bf1281ad8edbd07dc39094d91f6808e1c3868a3503dc2e5` |

[SOURCE primary evidence] Read the pinned local mirror papers:

- ALS 2015/608, §4.2 pp17–18, Lemmas 3–5 pp21–22 and Appendix C pp33–34;
  SHA256 `a7d5c231b70961ea59ca544c91b2392fb35c166c88e42b898640cfdc7dbb94d0`.
- MP 2011/501, Definition 2.2 and Lemmas 2.3–2.4 pp12–13, including
  equation (2.1) and its proof; also Lemma 2.8 and its tail calculation p14;
  SHA256 `bf1160f088825ed28c343b299f5bc2acdca41cc50293310a03a4506d2fdbdb84`.
- GPV 2007/432, Definition 2.5/Corollary 2.8 pp10–11 and Lemma 5.2 p18;
  SHA256 `7e747881cddd16b7dcf82893682cb9b4c788d7cec5712f80aa4193f2bd30a5b3`.

[EXECUTED access] New local `pdftotext -layout` extracts match the existing
MP/GPV extract pins. MP pp12–14 and GPV pp10–12,18 were rendered and visually
inspected; the relevant ALS formula pages were inspected in the immediately
preceding fixed-coordinate review. Exact source hashes and visual access are
retained. Local `rg` located source passages and estimator conversion code.
No web, Scry, Kagi, PDF download, crypto, private-file or estimator execution
occurred. No field-wide absence claim is made.

## 1. Finite regularity and the shared public matrix

[SOURCE convention] GPV defines `ρ_s(x)=exp(-π||x||²/s²)` and smoothing
using `ρ_(1/s)(Λ*\{0})`. MP agrees. Therefore the exponent in dual mass
is `-πs²||w||²`. The reciprocal typo in ALS's displayed smoothing definition
cannot be read literally while applying its cited smoothing lemmas. BOUND.md
correctly follows the primary MP/GPV convention. No change to the actual
discrete Gaussian law or a substitution of continuous density is involved.

[SOURCE / DERIVED expectation] Transpose MP equation (2.1) to
`A∈Z_q^(M×N)`. Taking the identity basis in its Lemma 2.3 permits
`ηZ=sqrt(ln(2M(1+1/ε0))/π)`. For σ>ηZ, t=ηZ/σ, equation (2.1) gives

```text
E_A[ρ_(1/σ)(Λ_A*)] ≤ (1+ε0) Σ_s max(1/g_s,t)^M,
g_s = q/gcd(s1,...,sN,q).
```

[DERIVED] For q=p^k the number of order-p^i vectors s is exactly
`p^(iN)-p^((i-1)N)`. Including the zero vector's term one, then subtracting
the zero dual vector, gives the stated R. The cosets indexed by s can
repeat on nonsurjective matrices; the source's inequality permits that
overcount. No surjectivity conditioning was inserted into the expectation.
This is an additive-group/p-adic count, not universal hashing over F_q.

[SOURCE / DERIVED pointwise-to-joint step] On surjective A, the quotient
`Z^M/Λ_A` is isomorphic to all syndromes. GPV Corollary 2.8 permits any
real center and bounds distance by `2θ(A)` whenever `0<θ(A)<1/2`.
For larger θ the same inequality follows from distance≤1. Thus one need
not use Markov's inequality or choose a separate good-smoothing event.

[DERIVED] Conditional on each fixed surjective A, independent row hybrids
cost at most `2hθ(A)`. Appending the other independently sampled rows,
their products, and **all actual recipient keys** is a common randomized
kernel retaining A. On a nonsurjective A, bound the complete joint distance
by one. Its exact failure probability is

```text
ρrank = 1-Π_(a=0)^(N-1)(1-p^(a-M)).
```

[DERIVED] Hence `δ_h≤min(1,ρrank+2hR)` is valid and pays rank failure
once for the shared matrix. Paying zero would be unjustified; multiplying
this probability by h is unnecessary. For h=0 the distance is exactly zero.
The result averages over A while retaining A publicly. It does not provide
a pointwise guarantee after conditioning on a selected transcript or grinding
for a matrix. Independent right-block shifts and copies of accepted public
matrix/syndrome entries preserve this joint bound.

## 2. Explicit certificate and total hybrid charging

[DERIVED checked constants] With `λ=ε0=2^-κ`, κ≥1, the proposed integer
conditions imply

```text
4ηZ² < ceil(log2 M)+κ+2 ≤ σ²,
t<1/2,
S≤(q^N-1)2^-M≤λ/2,
R≤λ+(1+λ)λ/2≤7λ/4,
ρrank<λ/2.
```

[DERIVED] The first line uses only `4 ln2<π` and
`2M(1+2^κ)<2^(ceil(log2 M)+κ+2)`. The row condition
`M≥N ceil(log2 q)+κ+1` implies both the S bound and
`M≥N+κ+1`. Therefore `(1+7h)λ/2≤4hλ` for h≥1.
The certificate has explicit constants; this conclusion is not an evaluation
of the hidden constants in ALS Lemmas 4–5.

[EXECUTED] All six supplied certificates, including the actual prime-power
q, pass independently. The required augmented heights are 69,746,286,
330,211 and 1,524,245; their σ1² thresholds are 190,182,184. The copied
INPUTS fields match the frozen cost results and its hash.

[DERIVED / EXECUTED ledger] Setup uses `h=d-r=561`, N=n. The challenge
mask uses `h=d-j`, N=n+1, in the ideal uniform-challenge world of the
previously reviewed proof. There is no additional conditioning on a syndrome.
In acceptance-probability-difference convention,

```text
Adv_public ≤ 2δ_setup + 2T(ε_LWE+ε_red+δ_mask).
```

[EXECUTED] At T=384, κ=160, the regularity numerators are exactly
`8*561+8*384*577=1,777,032` for j=0 and
`8*561+8*384*561=1,727,880` for j=16, each divided by `2^160`.
Both are below `2^-139`. The setup error appears twice in total;
the mask error appears twice per fresh challenge. These terms are not
multiplied by the number of public replays or final reads.

## 3. Gaussian tails and finite correctness

[DERIVED] The original elementary tail is correct for integer center c,
σ≥1 and integer t with tσ integer. The first-term-plus-integral estimate
for the unnormalized positive tail is
`(1+σ/(2πt))exp(-πt²)`. Doubling, dividing by the valid lower bound one
on the normalizer, and using `2+σ/(πt)≤3σ` gives the stated bound.
It is loose, especially for the enormous full-source width, but not false.

[EXECUTED] Exact integer recomputation confirms all t choices, L1/L2
bounds, unit-center terms, and `q>2pWE` inequalities. The two original
union budgets give correctness failure at most `2^-65` for ideal prescribed
sampling over the stated 384-input horizon. Independence is unnecessary
for a union bound. Secret-row independence is needed elsewhere in security.

[DERIVED] Original scalar weights with L1 norm at most W=32 obey the
deterministic W E bound on the joint good event. Exact-original expiry
cancels the same error. Replacing it with a fresh encryption does not.
Adaptive bounded coefficients do not invalidate a simultaneously valid
input-error bound. Gaussian keys have unbounded support; their quoted sizes
are high-probability encodings, not unconditional fixed-size maxima.
Forced truncation, rejection or approximate sampling needs its own distance
or abort accounting.

## 4. Numerical accounting and estimator interface

[EXECUTED] Rational Gaussian elimination, independent of the author's
Bareiss method, reproduces determinant -812,032,080. Trial division verifies
p=28,439,893 and that every intervening integer above twice the maximum
score is composite. All 16 row norms, score bounds and sparse basis counts
match. Maximum score 14,219,936 is strictly below p/2. This certifies the
stated integer-output range, not privacy on an application encoder image.

[EXECUTED] All 23 structural cost fields in each of the three profiles
match direct integer recomputation: packed/aligned ciphertext sizes, A/U
storage, recipient sizes, live/retained storage, Gaussian sample counts,
encryption/registration/read products, and update additions. The actual q
values are minimal p-powers meeting each declared normalization rule;
source and gadget σ2 floors are both retained. The first failed finite
asymptotic-width attempt remains documented and was not executed here.

[DERIVED] The dense encryption count `n(m+d)` includes the two matrix-vector
products and excludes the separate small-field B transform, noise additions,
sampling and modular-reduction implementation costs. Unit and zero Y
coefficients can avoid general multiplication, as the basis counts already
distinguish. Packed sizes exclude framing/allocator state. No operation
count is a latency measurement or a lower bound against every implementation.

[SOURCE exact estimator mapping] Read only the pinned estimator `nd.py`
SHA256 `d87fca7bb191a0fb29b24507897e00c8beba784da552b6b90a982c718fc1c459`.
Its `stddevf`, lines 9–35, divides width by sqrt(2π);
`DiscreteGaussianAlpha`, lines 280–293, applies that conversion to its
argument times q. `UniformMod`, lines 386–402, represents the uniform
modular secret with centered representatives. This code was not imported.

[SOURCE / DERIVED] A future diagnostic must therefore use dimension n-d,
at most m independent generic LWE samples, exact q=p^k, uniform modular
secret, and error distribution `DiscreteGaussianAlpha(β,q)` where
`β=α/(2ξ)`. The input width is **βq**, not αq or σ1/σ2. The three exact
base widths are `2^5,2^71,2^71`; dimensions are 447,447,3519. The library's
standard-deviation parameterization is a modeling convention for the
Gaussian law; it is not an independent exact-variance proof or a QPT theorem.
No earlier structured-ring/CBD estimate applies to these tuples.

[DERIVED missing obligations] Coefficient-one normalization does not fix
the lower-bound constants in the gadget sampler, inverse-norm bound or
βq≥Ω(sqrt(n)) premise. It also leaves the `2^-Ω(n)` sampler/reduction
errors, implementation accuracy, and actual resource-bounded QPT-LWE
assumption open. Correctness `2^-65` and regularity below `2^-139` are
different budgets; neither establishes a 128-bit total security statement.
The same advice-class and complete-transcript conditions from the prior
fixed-coordinate review still apply.

## 5. Source-backed improvements, without changing frozen examples

[SOURCE] MP Lemma 2.8, printed p14, proves a centered lattice Gaussian
is exactly 0-subgaussian for every positive width. Its displayed Chernoff
calculation gives tail `2exp(-πt²)` at t times that width. Because every
center here is integer, subtracting c gives precisely the centered law.

[DERIVED improved coordinate tail] Consequently the width-independent
choice

```text
4t² ≥ ceil(log2(2N))+66
```

[DERIVED] suffices for a `2^-66` union budget over N samples. It removes
the log2 σ term without truncating or changing a distribution. Applied to
the same conservative d m secret-coordinate count, it gives t_z=6,5,5 in
the three profiles. This improves the existing L2 norm certificate as well.

[DERIVED stronger phase certificate] Conditional on a fixed recipient
row Z_i, independent centered e1_i and e0 coordinates satisfy

```text
E[exp(2πu(e1_i-Z_i e0)) | Z_i]
  ≤ exp(π σ_e² u²(1+||Z_i||_2²)).
```

[DERIVED] This follows by multiplying their source subgaussian bounds;
no continuous-Gaussian approximation or independence of different recipient
phases is needed. On `||Z_i||_2≤L2'`, take
`E'=σ_e ceil(sqrt(1+L2'^2)) t_phase`, with
`4t_phase²≥ceil(log2(2Tr))+66`. A union over all T r recipient phases
plus the secret event retains total failure at most `2^-65`. The same
W E' deterministic combination condition then applies. It covers the
actual fixed recipients, not hypothetical arbitrary functional keys.

[EXECUTED] At the unchanged q/widths/m, t_phase=5 in all three profiles.
The resulting integer E' is at least 4,723,507, 2,580 and 5,898 times
smaller than the original conservative E. These are improvements in a
**sufficient coordinate-error bound**, not reductions in actual noise,
runtime measurements or security-bit estimates. The full arbitrary-key
prescription still has its separate source correctness requirement; this
coordinate bound cannot silently replace it.

[DERIVED / EXECUTED matrix rounding] Lemma 4 does not require m to be
a power of two. Keeping the original q and widths, the conservative choice
`m'=4(n+1)ceil(log2q)` passes the same coefficient-one floors and explicit
regularity checks at m'=278,984,500; 1,320,200; 6,096,336. The corresponding
packed ciphertext sizes are 2,372,942,445,559; 53,161,275; 283,506,455 bytes.
The matrix-work term declines in proportion to m'+d. These are optional
arithmetic sensitivity points, still subject to the unknown source constants;
all original examples remain valid conservative sizes.

## 6. Reproduction and remaining work

[EXECUTED] `check.py` independently verifies subject/manifests, input/source
pins, finite profile inequalities, all 69 cost fields, six regularity
certificates, and four exact rank-failure counts over 890 small matrices.
It uses rational/integer arithmetic and reads the estimator source only
through the frozen manifest; it never executes an author module.

```text
python3 research/learn_infer_only/experiments/adversarial_review/pq_finite_costs/check.py > research/learn_infer_only/experiments/adversarial_review/pq_finite_costs/stdout.txt 2> research/learn_infer_only/experiments/adversarial_review/pq_finite_costs/stderr.txt
```

[EXECUTED] Exit 0, stderr empty. Exact improvements and all checked file
hashes are retained in `results.json`. The frozen author files are unchanged;
no private files, Gaussian draws, keys, ciphertexts, estimator/attack runtime,
protocol controls, prior stopped artifacts or commits were used.

[OPEN next] Resolve finite gadget constants/errors and choose an explicit
QPT-LWE/advice/resource assumption before declaring a security tuple. The
subgaussian and matrix-height improvements can then inform a successor
parameter study with an explicit total error budget and application-image
nonvacuity witness. No implementation launch is implied by this review.
Parent owns shared ledgers, adoption and commits.
