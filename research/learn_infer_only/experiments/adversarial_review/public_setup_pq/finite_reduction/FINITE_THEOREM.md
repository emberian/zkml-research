# Finite constants for a repaired fixed-coordinate reduction

[DERIVED, 2026-09-08] This note gives a constant-bearing distributional
replacement for the uses of ALS Lemmas 4–5 in the frozen
`../FIXED_COORDINATE_QPT.md`. It uses a larger, explicitly bounded gadget
norm and repairs a factor in the printed ALS reduction. It does not change
the public encryption or recipient-setup algorithms. All earlier frozen
notes remain unchanged; their asymptotic source invocation should not be
read as an audit of the printed recipe at finite parameters.

[DERIVED scope] The conclusion is a finite conditional privacy inequality
for classical interfaces and a fixed coordinate coalition, under an exact
QPT decision-LWE hypothesis. Every mathematical statistical loss is displayed.
An implementation of the reduction's samplers has its own explicit total
variation budget `δs`; no numerical LWE hardness, sampler implementation,
runtime, concrete security level, or resident learning semantics is proved.

## 1. Sources and conventions

[SOURCE] ALS, local ePrint 2015/608: Definition 3, p.9 (discrete input LWE
errors); Lemmas 3–5, pp.21–22; Lemma 3 proof, pp.34–35. LPSS, local ePrint
2014/494, revision dated 2015-08-05: p.8 explicitly permits dropping the
first-row-of-ones restriction by replacing Lemma 8 with Lemma 7; Lemma 16
and Theorem 17, pp.12–13, give the Gaussian-image and unimodular gadget
recipes. Its matrix norm convention is longest-column norm, not operator
norm. We prove the operator norm needed here separately.

[SOURCE] AR, *A Note on Discrete Gaussian Combinations of Lattice Vectors*,
arXiv:1308.2405v2: conventions p.4; Lemma 2.1 p.5; Definition 3.1 p.5;
Theorem 3.2 p.6; Lemma 4.2 pp.8–10. BLPRS, *On the Classical Hardness of
Learning with Errors*, arXiv:1306.0281, local paperbin copy: Lemmas
2.3, 2.5, 2.8 and 2.10, pp.6–7. `SOURCES.json` pins the exact PDFs and
extracts used. ALS p.22 and AR p.8 were rendered and visually inspected.

[SOURCE/DERIVED conventions] A scalar Gaussian of width `s` has weight
`exp(-π x²/s²)`, and continuous variance `s²/(2π)`. A positive symmetric
width matrix `S` has exponent `-π x^T S^-2 x`. `D_(Z^a,S)` is the exact
discrete Gaussian with this weight; an integer center means its translation.
`||.||op` is Euclidean operator norm. `SD` is total variation, with its
usual factor `1/2`; advantage is a difference of acceptance probabilities.
All `log2` and `ln` bases are explicit. Put

```text
g_a(ε) = sqrt(ln(2a(1+1/ε))/π),       a ≥ 1.
```

[SOURCE] BLPRS Lemma 2.5 implies `η_ε(Z^a) ≤ g_a(ε)` under the conventional
smoothing definition `ρ_(1/s)(Λ*\{0})≤ε`. The reciprocal typo documented
in `../quantitative_regularity/BOUND.md` is not used.

## 2. An explicit unimodular gadget

[DERIVED parameters] Choose integers `n≥100`, `L≥M>n`, widths `σ1,σ2>0`,
`εQ∈(0,1/1000)` and `εI∈(0,1/3)`. Let

```text
m = M+L,
σ1 ≥ 9 g_n(εQ),
M > 30 n log2(σ1 n),
q1 = σ1 sqrt(n log2 M),
q2 = 2 sqrt(30 n log2(σ1 n)),
Amax = sqrt(M) q1,
b = max((1+q1 q2) g_(M-n)(εI),
        g_M(1/4), sqrt(ln(2M+4)/π)),
σ2 ≥ Amax b,
K = (1+Amax)(1+σ2 q2 sqrt(LM)).
```

[DERIVED gadget lemma] There is the following Gaussian-sampling construction
which either aborts or gives an integral unimodular matrix `G∈Z^(m×m)`
with `||G^-1||op≤K`. The top `n` rows, with an abort symbol included, are
within distance

```text
δG = min(1, 2^-n + 2L εI + L 2^(1-M))
```

of the nonaborting independent Gaussian target

```text
τ_n = D_(Z,σ1)^(n×M)
      × (D_(Z^L,σ2,e1) × ... × D_(Z^L,σ2,en))^T.
```

[DERIVED proof, quality event] Sample `X∈Z^(n×M)` with independent
width-`σ1` entries. AR Lemma 4.2 says that, except probability `2^-n`,
its columns have norm at most `q1`, and there exist pairwise orthogonal
integral `v_i∈Z^M` with `X v_i=e_i` and `||v_i||≤q2`. Consequently
`X Z^M=Z^n` and `||X||op≤||X||F≤Amax`. For `V=[v_1|...|v_n]`,
`||V||op≤q2` and `XV=I`; hence, for every `y`,
`||y||²=<X^T y,Vy>≤q2||X^T y|| ||y||`.
Thus `s_min(X)≥1/q2`. The quality event is used in the proof, not tested
by finding these witnesses.

[DERIVED construction] Abort if `X` fails either spectral bound just given.
For a passing `X`, choose a positive symmetric `M×M` matrix `S` by its
singular-vector decomposition: on the right singular vector with singular
value `s_i(X)`, set its eigenvalue to `σ2/s_i(X)`; on `ker X`, use
`σ2/s_min(X)`. Then

```text
X S² X^T = σ2² I_n,
s_min(S) ≥ σ2/Amax ≥ b,
||S||op ≤ σ2 q2.
```

[SOURCE/DERIVED image step] Independently sample `r_1,...,r_L` from
`D_(Z^M,S)`. AR Theorem 3.2, for every quality `X`, gives
`SD(X r_j,D_(Z^n,σ2))≤2εI`. It applies to the fixed quality matrix and
every admissible `S`, so choosing `S` from `X` is allowed. A conditional
product hybrid gives total distance at most `2LεI`, retaining `X`.
This uses Theorem 3.2 with the displayed quality bounds, not the simplified
asymptotic threshold in LPSS or a guessed constant in a spectral lemma.

[SOURCE/DERIVED sampling] The final term in `b` permits use of BLPRS
Lemma 2.3 on the lattice `S^-1 Z^M` with scalar parameter one and basis
`S^-1`: its longest Gram–Schmidt vector is at most `1/s_min(S)`.
Multiplying back by `S` gives the claimed exact anisotropic discrete law.
Finite-precision realization of real matrix operations is covered by `δs`
in §5, not silently set to zero in a numerical implementation claim.

[SOURCE/DERIVED norm event] AR Lemma 2.1 at `c=1`, dimension `M`, and
`ε=1/4`, gives

```text
Pr[||r_j|| ≥ ||S||op sqrt(M)]
 ≤ (5/3)(sqrt(2πe) exp(-π))^M
 < 2^(1-M).
```

[DERIVED] The inequality uses `sqrt(2πe) exp(-π)<1/2`. This is a
zero-centered Gaussian norm bound; no claim about arbitrary centers is
needed. Set `R=[r_1|...|r_L]` and abort if
`||R||F>σ2 q2 sqrt(LM)`. For every passing `X` the abort probability is
at most `L 2^(1-M)`. Let `C=[I_n|0]∈Z^(n×L)` and
`X2^T=C+XR`. With `D=[X^T|0]∈Z^(M×L)`, define

```text
H = [ 0    I_L ] [ I_M    0  ]
    [ I_M  -D  ] [ -R^T  I_L]
  = [ -R^T          I_L ] ,
    [ I_M+D R^T     -D  ]
G = H^-T.
```

[DERIVED] Both factors are unimodular integral matrices. Direct block
multiplication gives `H [X^T; X2]=[I_n;0]`; therefore the first `n` rows
of `G` are `[X|X2^T]`. The two factors have operator norms at most
`1+||D||op` and `1+||R||op`, respectively: each is a coordinate
permutation or identity plus a block of that norm. Thus
`||G^-1||op=||H||op≤K`. The image target has exactly the unit-vector
centers prescribed by ALS, not transformed secret rows. Bad quality,
image distance and norm abort are charged once each in `δG`. These are
unconditioned joint bounds; the construction never resamples to condition
away an abort.

## 3. The printed recipe and its correction

[SOURCE] ALS p.22 prints balancing noise
`f←D_(a sqrt(ξ²I-Q'Q'^T))`, adds continuous width-`a` noise to the
last `m-d` coordinates of the discrete width-`a` input, and discretizes
with width `sqrt(2)aξ`; here `a=βq`, `Q=G^-1`, and `Q'` is the last
`m-d` columns of `Q`. The displayed output noise rate is `2βξ`.

[DERIVED, printed-recipe discrepancy] After the discrete-plus-continuous
step, the parameter covariance is `2a² Q'Q'^T`. The printed `f` changes
this to `a²(ξ²I+Q'Q'^T)`. The final discretizer would give
`a²(3ξ²I+Q'Q'^T)`, rather than the required `4a²ξ²I`.
The Gaussian normalizations in ALS and BLPRS do not remove this discrepancy.
The frozen asymptotic theorem statement is not refuted by this calculation;
the literal printed sampling recipe needs repair under the discrete-input
convention of ALS Definition 3.

[REPORTED independent check] `/root/release_construction` visually inspected
the same rendered page and independently confirmed the formula and covariance
accounting on 2026-09-08. This is a source correction found by two readers,
not an author-issued erratum or a claim about an implementation.

[DERIVED repaired transformation] Require `d<n`, `ξ>K`, and let `Z` be
the first `d` rows of `G`. Then `ZQ'=0`. Given a first-`d`-errorless
input `(A,b)`, set `A'=QA mod q`; sample independently

```text
e' ← {0}^d × D_a^(m-d)                       (continuous),
f  ← D_(sqrt(2)a sqrt(ξ²I-Q'Q'^T))           (continuous),
b' = Q(b+e')+f,
c  ← D_(Z^m-b',sqrt(2)aξ)                   (discrete coset),
h  = Z(f+c).
```

[DERIVED] Output `(A', b'+c mod q, Z, h)`. The matrix under the square
root is positive definite because `ξ>K≥||Q'||op`. The factor `sqrt(2)`
on `f` is the only change to the displayed ALS sampling formulas. The
quantity `b'+c` is integral by the coset sampler, and the hint is integral
because `h=Z(b'+c)-[I_d|0]b`. This identity uses `ZQ=[I_d|0]` and the
vanishing first `d` entries of `e'`; `Zb'` itself need not be integral.

[DERIVED finite smoothing conditions] For `εc∈(0,1/2)`, `εr∈(0,1/2]`,
assume

```text
a/sqrt(2) ≥ g_(m-d)(εc),
sqrt(2)aξ ≥ g_m(εr),
sqrt(2)aξ ≥ sqrt(ln(2m+4)/π).
```

[DERIVED LWE world] Write the errorless input lift as `As+[0;e0]`, where
`e0←D_(Z^(m-d),a)`. Reduction modulo `q` changes only integer lifts,
which do not affect the coset used to sample `c`. BLPRS Lemma 2.8 makes
`e0+e'_tail` within `4εc` of a continuous Gaussian of width `sqrt(2)a`.
After multiplication by `Q'` and addition of the repaired `f`, the
continuous noise is exactly spherical of width `sqrt(2)aξ` in the ideal
hybrid. BLPRS Lemma 2.10 then makes its sum with `c` within `8εr` of
`e←D_(Z^m,2aξ)`. At every step `h=Ze`, because `ZQ'=0`.
This is a joint statement about the ciphertext and hint, not merely its
ciphertext marginal. The ideal `e` is independent of `G,A,s`.

[DERIVED uniform world] Introduce an auxiliary independent
`e0←D_(Z^(m-d),a)` and write the uniform input exactly in law as
`b=v+[0;e0] mod q`, with `v←Z_q^m` independent of `e0`. This changes
no input distribution. The same two smoothing steps apply to the noise.
Since `Qv` is integral, the coset used for `c` depends only on that noise,
and `Qv mod q` is uniform independent of `G`, the noise, and `h`.
The ideal result is consequently `(A',u,Z,Ze)`, with uniform `A',u`
and independent `Z,e`. No claim of independence is made by conditioning
on a particular public syndrome or transcript.

[DERIVED each-world bound] For fixed nonaborting `G`, either ideal-world
comparison costs at most `4εc+8εr`. After this comparison the ideal tuple
depends on `G` only through `Z`, so replacing its marginal by the exact
first-`d` row law `τ_d` costs `δG`, including abort. Thus the two-world
advantage loss is at most `2δG+8εc+16εr`. An approximate realization
with per-world total variation at most `δs` adds `2δs`.

## 4. Errorless samples, prime powers, and the QPT hypothesis

[DERIVED finite ALS Lemma 3] Take `q=p^k` with `p` prime, `k≥1`.
The exact probability that an independent uniform `d×n` first block has
no full row rank modulo `p` is

```text
δ3 = 1-Π_(i=0)^(d-1)(1-p^(i-n))
   ≤ (p^d-1)/((p-1)p^n).
```

[SOURCE/DERIVED] For a prime power, full row rank modulo `p` is exactly
the condition for completing this block to an invertible matrix over
`Z_q`; the prime factor is known. Use ALS pp.34–35 to extend the secret
from `n-d` to `n` coordinates and make the first `d` samples errorless.
Keep the abort event and charge `δ3` in each world, for `2δ3` overall.
The reduction uses `m-d` input samples; an `m`-sample assumption suffices
by discarding the unused samples. No prime-field uniformity rule is
applied to arbitrary nonzero differences in `Z_(p^k)`.

[HYPOTHESIS QPT-LWE] For `α=2βξ∈(0,1)`, assume decision LWE on
classical tuples with modulus `q`, uniform secret in `Z_q^(n-d)`, at most
`m` samples, and **discrete** error width `βq=a` has QPT distinguishing
gap at most `εLWE` at the reduction's actual resource bound. This is the
assumption at the stated dimension and noise, not a statement that the
parameters deliver some number of security bits. Reducing `β` changes
the assumption even if encryption's `α` stays fixed.

[DERIVED QPT lift] These transformations operate on classical tuples and
call the target QPT distinguisher once. Classical total variation bounds
remain valid as trace-distance bounds after any QPT channel. If the
adversary is allowed nonuniform quantum advice, the LWE hypothesis must
allow the same advice class; one copy of the advice passes into the single
target invocation. Advice is independent of the fresh secret, setup coins
and challenge bit. This proof provides no cloning, rewinding, quantum
sample access, superposition key oracle, or arbitrary secret-correlated
quantum auxiliary input.

[DERIVED efficiency scope] In an asymptotic QPT family, the dimensions
`M,L`, parameter bit lengths, and the resources needed to attain the stated
sampler discrepancy must be polynomial in the security parameter. Finite
algebraic inequalities alone do not certify those sampling resources. The
large gadget is generated by the reduction, not by public setup.

[DERIVED combined finite bound] With the ideal Gaussian transformations,
or an explicit per-world sampler discrepancy `δs`,

```text
εmhe ≤ εLWE + εred,
εred = 2δ3 + 2δG + 8εc + 16εr + 2δs.
```

[DERIVED] This replaces the unspecified reduction discrepancy of the frozen
fixed-coordinate proof. The loss `δG` is for the complete joint gadget-row
law and is charged before treating ideal `Z` and encryption error as
independent. It is not a bound conditioned on an arbitrary accepted public
matrix or adversarially chosen transcript.

## 5. A simple integer certificate and full privacy ledger

[DERIVED certificate] The following conservative integer inequalities
suffice. They intentionally replace square roots and logarithms by upper
bounds; the check script implements these exact inequalities. Let `κ≥10`,
`λ=2^-κ`, `n≥max(100,κ)`, `n-d≥κ`, and let `σ1≥1` be an integer.
Write `Ln=ceil(log2 n)`, `LM=ceil(log2 M)`, `LL=ceil(log2 L)`,
`Ls=ceil(log2 σ1)`, and use integer upper bounds

```text
Q1 = σ1 ceil(sqrt(n LM)),
Q2 = 2 ceil(sqrt(30n(Ls+Ln))),
A  = ceil(sqrt(M)) Q1,
B  = max((1+Q1 Q2) ceil(sqrt(LM+LL+κ+3)),
         ceil(sqrt(LM+4))),
Kbar = (1+A)(1+σ2 Q2 ceil(sqrt(LM_product))),
LM_product = L*M.             # this is a product, not the logarithm LM
```

[DERIVED] Require

```text
L ≥ M > n,
σ1² ≥ 81(κ+Ln+2),
M > 30n(Ls+Ln),
σ2 ≥ A B,
M ≥ κ+LL+1,
ξ ≥ 2Kbar,
a² ≥ 2(κ+ceil(log2(m-d))+2),
2a²ξ² ≥ κ+ceil(log2 m)+2.
```

[DERIVED proof] Set `εQ=εc=εr=λ`, `εI=λ/(2L)`.
For positive `u`, the bound on `g_u(ε)²` follows by bounding `u` and
`1+1/ε` above by powers of two and using `ln 2/π<1`. In particular
`g_(M-n)(εI)² < LM+LL+κ+3`. The term `LM+4` dominates both the
quarter-smoothing and exact-sampler thresholds. The quality theorem's
strict row-count inequality is preserved. The three gadget terms are at
most `λ` each, so `δG≤3λ`; prime-power rank failure gives `δ3<λ`.
The last two conditions imply the convolution, discretization and exact
discretizer-sampling widths. Thus

```text
εred ≤ 32λ + 2δs.
```

[DERIVED sampler scope] The displayed finite distribution theorem has
`δs=0` for its ideal transformations. To invoke an actual finite-bit QPT
reduction, supply a sampler whose **entire classical output tuple**, in
each world, differs from that ideal law by at most the stated `δs`.
BLPRS Lemma 2.3 supplies the discrete Gaussian sampler under the width
thresholds above. Real square roots, covariance decomposition, continuous
sampling, truncation, and any finite-precision decisions must be implemented
with a total discrepancy budget, not assumed exact because the source calls
the reduction efficient. This note does not implement or certify that
sampler. The inequality remains explicit for any supplied `δs`; using
`δs≤λ` gives the convenient conditional bound `εred≤34λ`.

[DERIVED public-setup privacy] Retain the exact scope of
`../FIXED_COORDINATE_QPT.md`: an honest sampled public setup, accepted
coins copied from its public values, fixed full-rank policy and coordinate
coalition `J`, `j=|J|`, and at most `T` classical valid fresh-input
challenge pairs. Let `δsetup` and `δmask` be the joint regularity bounds
from `../quantitative_regularity/BOUND.md`, for `(N,h)=(n,d-r)` and
`(n+1,d-j)`, respectively. Then

```text
Adv_public ≤ 2δsetup + 2T[εLWE + εred + δmask].
```

[DERIVED] If both regularity certificates use the same `κ`, the finite
reduction certificate holds, and `δs≤λ`, this becomes

```text
Adv_public ≤ 2T εLWE
             + [8(d-r) + 8T(d-j) + 68T] 2^-κ.
```

[DERIVED] The initial setup distance is paid twice, once for each bit world,
and is not multiplied by `T`. The multi-challenge hybrid multiplies the
per-challenge reduction and mask errors. Adaptive histories are generated by
a common efficient channel from the earlier classical transcript and the
adversary's retained quantum state; no rare-transcript conditioning occurs.
Negligibility in asymptotic families requires an appropriate growing
`n-d`, rather than merely `d<n`.

## 6. Correctness and limitations of a finite certificate

[DERIVED] The reduction's `G`, `ξ`, and `β` are not generated by the
public setup algorithm. Increasing the analytical gadget norm and changing
the LWE hypothesis can leave `(q,m,σ1,σ2,α)` and encryption costs fixed.
Increasing `M` does change ciphertext, public matrix and recipient key sizes,
and requires a fresh correctness budget. The certificate checker records
which original parameter profiles pass and which adjusted profiles pass;
it never substitutes a passing adjusted row for an original failing row.

[SOURCE/DERIVED correctness retained] Decryption still has exact phase
`Δa_i+e1_i-Z_i e0 mod q`, where `Δ=q/p`. Scalar combinations with
coefficient L1 norm at most `W` require a separately stated bound
`|e1_i-Z_i e0|<q/(2pW)` over the whole finite workload. Application scores
require their separate centered-integer no-wrap promise. The privacy
inequality above does not include correctness failure; it is a different
event. A correctness-tail certificate and any finite Gaussian sampling
approximation for the **scheme** itself must be added where claimed.

[OPEN limits] This note closes the hidden constants in the mathematical
quality, gadget, Gaussian-conversion and prime-power rank steps by choosing
larger explicit bounds and correcting the recipe. A fully concrete QPT
runtime/hardness statement still needs the finite sampler discrepancy/resource
certificate and an exact hardness hypothesis at `n-d,q,β,m`. No estimator
or cryptographic program was run. The conditional statistical number from
the final ledger must not be described as a cryptographic security level.
