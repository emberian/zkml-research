# Explicit regularity for independent Gaussian syndrome rows

[DERIVED result, 2026-09-08] The setup/augmented-mask statistical error can be
bounded with explicit constants. The result below applies to a prime-power
modulus, uses the actual discrete Gaussian on integers, retains the public
matrix and independently generated recipient rows, and gives a simple integer
certificate. It does not quantify the separate LWE reduction errors or the
computational QPT-LWE assumption. Earlier frozen construction/review notes are
unchanged.

## 1. Sources and conventions

[SOURCE] ALS 2015/608 Appendix C, printed pp.33–34, Lemmas 6, 8–10. Its
Lemma 6 is adapted from Micciancio–Peikert, ePrint 2011/501, *Trapdoors for
Lattices: Simpler, Tighter, Faster, Smaller*, printed pp.12–13, Definition 2.2,
Lemma 2.3 and Lemma 2.4, including proof of equation (2.1). Syndrome regularity
comes from Gentry–Peikert–Vaikuntanathan, ePrint 2007/432, *How to Use a Short
Basis*, printed pp.10–11, Definition 2.5 and Corollary 2.8, and p.18,
Lemma 5.2 with proof. All three were read from absolute local mirror paths;
the MP/GPV extracts are saved under `extracts/`. A source manifest records exact
hashes. No ePrint PDF was downloaded.

[SOURCE convention] Write

```text
ρ_s(x) = exp(-π ||x||²/s²),
D_(Z^M,σ,c)(z) = exp(-π||z-c||²/σ²) / Σ_(v∈Z^M) exp(-π||v-c||²/σ²).
```

[SOURCE] GPV Definition 2.5 sets smoothing parameter `η_ε(Λ)` by
`ρ_(1/s)(Λ*\{0})≤ε`, so the summand on the dual lattice is
`exp(-π s²||w||²)`. MP Definition 2.2 agrees. ALS's displayed smoothing
definition on p.33 instead prints division by `s²` on the dual lattice;
this is inconsistent with the cited definition and the increasing-width
smoothing lemmas. The derivation here uses the cited conventional definition,
not that reciprocal typo. Its Gaussian sampling density above has no such
correction. `σ` is a width parameter; the analogous continuous Gaussian has
variance `σ²/(2π)`, not `σ²`.

[DERIVED] A scalar Gaussian folded modulo `q` has probability mass
`Σ_(z≡a mod q) exp(-π(z-c)²/σ²) / Σ_z exp(-π(z-c)²/σ²)` at residue `a`.
Its real-valued density at `a` is not that probability. No continuous-density
collision estimate, unproved Rényi conversion, or prime-field universal-hash
formula is used below.

## 2. General explicit expectation bound

[DERIVED hypotheses] Let `p` be prime, `k≥1`, `q=p^k`, `M≥N≥2`, and
`A←Z_q^(M×N)` uniform entrywise. Let `ε0>0`, and put

```text
ηZ = sqrt(ln(2M(1+1/ε0))/π),
σ > ηZ,                 t = ηZ/σ < 1,
S = Σ_(i=1)^k (p^(iN)-p^((i-1)N)) · max(p^-i,t)^M,
R = (1+ε0)(1+S)-1.
```

[DERIVED lemma] With `Λ_A={z∈Z^M : z^T A=0 mod q}` and
`θ(A)=ρ_(1/σ)(Λ_A*\{0})`,

```text
E_A θ(A) ≤ R.
```

[SOURCE/DERIVED proof] MP Lemma 2.3, applied to the identity basis of
`Z^M`, gives `ηZ≥η_ε0(Z^M)`. Transpose the matrix in MP Lemma 2.4,
equation (2.1), to our row convention. It gives

```text
E_A ρ_(1/σ)(Λ_A*) ≤ (1+ε0) Σ_(s∈Z_q^N) max(1/g_s,t)^M,
g_s = q/gcd(s_1,...,s_N,q).
```

[DERIVED prime-power counting] Exactly `p^(iN)-p^((i-1)N)` vectors have
`g_s=p^i`: the number whose additive order divides `p^i` is `p^(iN)`.
The zero vector alone contributes one. Subtract the zero dual-vector mass
one to obtain `R`. This is the required p-adic distinction: a nonzero
difference can generate a proper subgroup, so its image is not automatically
uniform over `Z_q`.

[SOURCE/DERIVED] MP's proof uses Poisson summation and Gaussian mass on the
dual cosets `Z^M+A s/q`; those cosets can repeat when the matrix is not
surjective, which is why the source has an inequality. The bound remains
valid on those matrices. It is not assuming a full-rank matrix before taking
the expectation.

## 3. From expectation to joint syndrome distance

[DERIVED exact rank term] The rows of `A` generate `Z_q^N` exactly when its
reduction modulo `p` has column rank `N`. Since that reduction is uniform,

```text
ρrank = Pr[not surjective]
      = 1 - Π_(j=0)^(N-1)(1-p^(j-M))
      ≤ (p^N-1)/((p-1)p^M)
      < p^(N-M)/(p-1).
```

[DERIVED] For a fixed surjective matrix and a row
`z←D_(Z^M,σ,c)`, any fixed real center `c` is allowed by GPV Corollary 2.8.
If `0<θ(A)<1/2`, use that corollary and the syndrome/quotient isomorphism
in GPV Lemma 5.2 to get
`SD(z^T A mod q, Uniform(Z_q^N))≤2θ(A)`.
If `θ(A)≥1/2`, the trivial distance bound one is already at most `2θ(A)`.
Thus the same upper bound holds for every surjective matrix without a
high-probability conditioning event. Finite `σ` gives positive `θ(A)`.

[DERIVED multiple-row theorem] Let `h≥1` independently sampled Gaussian
rows have the same left-block width `σ`; their centers may differ. Retain
`A` and any other independent Gaussian rows and their public syndromes,
including all actual recipient rows. Replace the `h` Gaussian syndromes by
independent uniform rows. Their full joint distributions have distance

```text
δ_h ≤ min(1, ρrank + 2h R).
```

[DERIVED proof] Conditional on a surjective `A`, successive row hybrids
cost at most `2hθ(A)`. Other independent rows and their products are generated
by a common postprocessing kernel from `A`; their exposure does not increase
distance. On nonsurjective matrices use distance at most one for the entire
joint tuple, so rank failure is paid once, not once per row. Average over `A`
and use the expectation lemma. If `h=0`, the distance is exactly zero.

[DERIVED] This avoids applying Markov's inequality and then paying a separate
bad-smoothing event. It is a joint average statement with public `A` retained;
it is not a pointwise bound after arbitrary conditioning or grinding on `A`.

## 4. A simple exact integer certificate

[DERIVED certificate] Let `κ≥1` be an integer, `Lq=ceil(log_2 q)`, and
`LM=ceil(log_2 M)`. If

```text
M ≥ N Lq + κ + 1,
σ² ≥ LM + κ + 2,
```

then, for `h≥1`,

```text
δ_h ≤ min(1, 4h · 2^-κ).
```

[DERIVED proof] Set `ε0=λ=2^-κ`. Since `4 ln 2/π<1`,

```text
4ηZ² = (4/π) ln(2M(1+2^κ))
     < LM + κ + 2 ≤ σ².
```

[DERIVED] Hence `t<1/2`. Every nonzero `s` has `g_s≥2`, so
`max(1/g_s,t)≤1/2`; the general sum obeys
`S≤(q^N-1)2^-M≤λ/2`. With `λ≤1/2`,

```text
R ≤ λ+(1+λ)λ/2 ≤ 7λ/4.
```

[DERIVED] Also `M≥N+κ+1` and `p≥2` imply
`ρrank < p^(N-M)/(p-1) ≤ λ/2`. Therefore
`ρrank+2hR ≤ (1+7h)λ/2 ≤ 4hλ` for every `h≥1`.
Every certificate check is integer/rational except the elementary strict
inequality `4 ln 2<π`; no hidden asymptotic constant enters this corollary.

[DERIVED comparison] The cost lane's earlier sufficient checks with `2κ`
margins and `σ²≥ceil(log_2 M)+2κ+3` remain conservative. They were obtained
through a bad-matrix/smoothing event. The direct expectation argument allows
the smaller margins above. This is an improvement of this bound, not a
cryptographic performance claim.

## 5. Applying the bound to the reviewed construction

[DERIVED] For setup, use `N=n`, `M=m/2`, `σ=σ1`, `h=d-r`. The right
Gaussian half contributes an independent shift `R_i A_R`. Appending that
half and shift preserves the full joint distance. Accepted public setup
values are copies of `A` and the missing public rows and add no information.
Gaussian tapes of missing rows are not exposed or generated in actual setup.

[DERIVED] For the QPT mask lemma, use `N=n+1` on
`[A_L | (u-e0)_L]`, `h=d-j`, with the same `M,σ1`. Uniform `u` makes
`u-e0` uniform independently of `e0`, exactly as in the frozen proof.
The corresponding bound includes both syndrome components jointly and all
exposed recipient rows. No extra conditioning on the public-key syndrome
is inserted.

[DERIVED] Put the resulting values into the frozen theorem as

```text
Adv_public ≤ 2 δ_setup
           + 2T[ε_LWE + ε_red + δ_mask].
```

[DERIVED limitation] These are now explicit values for the regularity terms
only. The exact QPT-LWE assumption, Lemma 4/5 sampler/reduction errors and
unknown construction constants, approximate Gaussian sampler accuracy,
finite correctness tails, integer no-wrap and complete-system composition
still need their own accounting. A tiny regularity term is not a statement
of total cryptographic security bits.

## 6. Status and continuation

[EXECUTED] The cost lane's public numerical rows were copied by named fields
into `INPUTS.json`, with the exact source `costs/results.json` hash retained.
The rows share `p=28,439,893`, `d=577`, `r=16`, `T=384`. This checker verifies
primality independently by trial division. It tests the actual displayed
`q=p^k`, left-block row count and Gaussian width; it does not treat the cost
lane's normalized hidden constants as a security instantiation.

| [EXECUTED] cost row | actual M | q exponent k | required M for N=n+1, κ=160 | required σ1² |
|---|---:|---:|---:|---:|
| full-source normalized, n=1024 | 268,435,456 | 2748 | 69,746,286 | 190 |
| fixed-coordinate normalized, n=1024 | 1,048,576 | 13 | 330,211 | 182 |
| fixed-coordinate normalized, n=4096 | 4,194,304 | 15 | 1,524,245 | 184 |

[EXECUTED] All six certificates (`N=n` and `N=n+1` in each row) pass. At
`κ=160`, the total regularity contribution in §5 has exact upper bound
`1,777,032/2^160 < 2^-139` for the worst fixed coalition size `j=0` and
`1,727,880/2^160 < 2^-139` for `j=16`. These are bounds on the regularity
terms only. The difference in the numerator comes from `h=d-j` in the
augmented-mask term; the setup term always uses `d-r`.

[EXECUTED] `check_bounds.py` also enumerates 21,926 public additive-group
vectors across 12 small `(p,k,N)` cases. The exact p-adic counts in §2 match
every case. This checks the subgroup-count identity; it does not sample a
Gaussian or instantiate any cryptographic algorithm. Command/output:

```text
python3 research/learn_infer_only/experiments/adversarial_review/public_setup_pq/quantitative_regularity/check_bounds.py > research/learn_infer_only/experiments/adversarial_review/public_setup_pq/quantitative_regularity/RESULTS.json
```

[EXECUTED] Result: PASS, with script/input hashes and exact integer/rational
outputs in `RESULTS.json`. No Gaussian sampling, cryptographic execution,
estimator, private data or attack code is used.

[REPORTED independent acceptance] The cost lane independently reread §§2–4
and the exact MP/GPV source lemmas and accepted the derivation. Its check
confirmed the p-adic counts, pointwise `2θ` bound, one rank-failure term,
`4 ln 2/π<1` width conversion, and final `4h·2^-κ` constant. This is a
source/math cross-review, not a machine-checked cryptographic proof.

[OPEN next] Fold only these explicit regularity terms into the separate
cost/loss ledger; source Lemma 4/5 constants and reduction errors remain
outside this result. No prior frozen note needs modification.

[EXECUTED source-query counters, this follow-on] Two targeted web search
queries identified the cited MP/GPV ePrint numbers; all theorem content was
then read locally from the original papers. Scry SQL/schema 0/0; Kagi 0;
new PDF downloads 0. No field-wide absence claim is made.
