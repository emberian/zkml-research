# A compressed ring fixed-coordinate candidate with absent-master setup

[DERIVED, 2026-09-08] The module syntax in Mera–Karmakar–Marc–Soleimanian
2021/046 §5 admits a restricted construction using ordinary Ring-LWE,
scalar uniform flooding, and the exact joint ring regularity proved in
`RING_REGULARITY.md`. It can omit unused ciphertext coefficients while
retaining all `d` coordinates of the original plaintext space. No ring
master or absent-recipient key is generated in actual setup.

[DERIVED scope] This is a new conditional construction/proof, not an
implementation or an invocation of the paper's full adaptive-key theorem.
It has classical encryption interfaces, a fixed public policy and fixed
coalition. Its computational hypothesis, honest credential lifecycle,
correctness/ranges and finite sampling obligations are explicit below.
No cryptography, estimator or attack execution occurs in this lane.

## 1. Source algorithms and deliberate changes

[SOURCE] 2021/046 §2.3 pp.9–10 defines adaptive IND and its selective
restriction. Section 4 gives the selective noisy-public-key scheme used by
the implementation papers 2022/482 and 2023/721. Section 5 p.21 instead
uses vectors of ring polynomials `z_i∈R^w`, uniform `a∈R_q^w`, noiseless
`P_i=<a,z_i>`, ciphertext `c0=a r+e`, and `c_i=P_i r+f_i+Δx_i·1_R`.
Its Theorem 4 uses multi-hint extended Ring-LWE and the ring LHL of
Theorem 2. We inspected those algorithms, game and reduction sections;
old library execution/defect artifacts are not inputs to this new proof.

[DERIVED differences] We sample `a` without the source's rejection tests;
use a uniform ring secret `r` as fresh encryption randomness; replace its
Gaussian `f_i` by independent scalar uniform flooding; and output only the
constant coefficient of each second ciphertext component. The proof below
uses neither multi-hint Ring-LWE nor complexity leveraging. The source's
incorrect global-nonmultiple/surjectivity implication is isolated and
repaired by the exact CRT rank term in `RING_REGULARITY.md` §2.

[SOURCE/DERIVED provenance] The scalar interval-shift argument is the same
elementary bound proved in the frozen local
`../alternatives/SMUDGED_FIXED_COORDINATE.md`, SHA256
`a7f98b9f17b0e9b37537ca763697f7a9235df498364df4e0dd774f293d9b9327`.
Its scalar-matrix regularity lemma and scalar parameter/hardness results
are not imported. Ring-LWE's uniform-secret syntax is also described by
Lyubashevsky–Peikert–Regev 2013/293, Definition 2.21 and the discrete
variant in §2.6. Our exact coefficient-error assumption is stated below;
we do not transfer canonical-embedding width parameters without conversion.

## 2. Algorithms and credentials

[DERIVED parameters] Choose an odd prime `p`, `d>r`, fixed full-row-rank
`Y∈F_p^(r×d)`, and a public `B∈GL_d(F_p)` with first `r` rows `Y`.
Put `X=(p-1)/2`, and define the bijection
`a(x)=center_p(Bx)∈[-X,X]^d` on all `x∈F_p^d`.
Choose `R=Z[T]/(T^N+1)` for power-of-two `N≥16`, a prime
`q=1 mod 2N`, module width `w≥3`, key width `σK`, error width `σe`,
integer flood radius `F≥1`, and integer encoding denominator `D`.
Let `Δ=floor(q/D)`. All discrete Gaussian coefficients have mass
proportional to `exp(-πt²/σ²)`.

[DERIVED public setup]

1. Draw `A=(A1,...,Aw)←R_q^w` uniformly and independently.
2. Each recipient `i≤r` privately samples `z_i∈R^w` with `Nw`
   independent width-`σK` Gaussian coefficients. It publishes
   `P_i=<A,z_i> mod q` and retains its complete integral row `z_i`.
3. Draw each missing `P_i∈R_q`, `i>r`, directly uniformly. No such
   `z_i` is sampled. Publish `A,P,B,p,q,Δ` and the fixed policy.

[DERIVED encryption] For each fresh private input `x`, sample independent
uniform `s←R_q`, `e∈R^w` with independent width-`σe` coefficients,
and integers `f_i←[-F,F]`, independently for `i=1,...,d`. Output

```text
c0 = A s + e mod q                  ∈ R_q^w,
h_i = const(P_i s) + f_i + Δ a_i(x) mod q  ∈ F_q.
```

[DERIVED read] Recipient `i` computes

```text
v_i = h_i - const(<z_i,c0>) mod q.
```

It decodes to the nearest `Δt mod q` for the declared integer interval
and returns `t mod p`. An integer score is returned only when a separate
application range promise uniquely identifies its centered lift. The
decoder uses these actual `Δ` codepoints; rounding `D v_i/q` silently
would reintroduce a floor-scaling bias.

[DERIVED exact constant-coefficient formula] If
`b(T)=Σ_(k=0)^(N-1)b_k T^k` and `c(T)=Σ_(k=0)^(N-1)c_k T^k`, then

```text
const(bc mod(T^N+1)) = b_0 c_0 - Σ_(k=1)^(N-1)b_k c_(N-k).
```

[DERIVED] This is an `N`-term signed inner product, not a full polynomial
convolution. Its sign follows from `T^N=-1`. Thus encryption needs `w`
full ring products for `c0` and `d` length-`N` signed inner products for
the scalar `h_i`. Each recipient read uses `wN` such coefficient products.

[DERIVED credential lifecycle] The public constructor knows only directly
sampled public `A,P_missing` and published recipient outputs. Each recipient
keeps its own independent integer Gaussian row and can read its coordinate
on every retained issued ciphertext. A fixed coalition receives exactly
those rows. The other recipients' rows remain private; no master is shared
among them. Honest private recipient sampling is a premise. There is no
erasure premise for missing rows, since they are never created.

[DERIVED coins and exposure] Public accepted sampling values are copies of
`A,P_missing`; an implementation's rejection logs need a separate
conditional-simulation argument. Encryption's `s,e,f` and their sampling
tapes are fresh private coins and are not disclosed in the privacy game.
No long-lived secret encryption credential is required. Malicious
registration, adaptive corruption, new recipients and superposition oracle
access are outside this theorem.

## 3. Full joint setup and fixed-coalition privacy

[DERIVED comparison] For proof only, sample all independent Gaussian rows
`Z=(z_i)` and set every `P_i=<A,z_i>`. Let `δ_h(k)` denote the explicit
joint ring regularity bound of `RING_REGULARITY.md` §4. Actual and
hypothetical setup, retaining all `r` actual recipients' rows, have distance
at most `δ_(d-r)(1)`. A complete matrix master exists only in this comparison.

[HYPOTHESIS exact QPT Ring-LWE] Assume decision Ring-LWE for the classical
tuple

```text
(A, A s+e)  versus  (A,u),
A,u uniform in R_q^w,
s uniform in R_q,
e has independent D_(Z,σe) coefficients in the power basis.
```

The shared secret has one ring element, hence `N` coefficient dimensions;
there are `w` ring samples. It is not ordinary LWE with an independent
uniform `(wN)×N` scalar matrix. The power-of-two cyclotomic's canonical
embedding scales Euclidean coefficient norms by `sqrt(N)`, so any cited
worst-case or alternative-normalization theorem needs that conversion.
The quantity `εRLWE` below is the distinguishing gap at the reduction's
actual resources for this exact problem, not an assigned security level.

[DERIVED game and advice] Fix `J⊆[r]` before setup, `j=|J|`. Challenge
pairs may be chosen adaptively through classical interfaces after seeing
all public data and `Z_J`, but must satisfy `Y_J x0=Y_J x1` for every
fresh input. Equivalently their centered `a_J` values agree as integers.
The adversary may retain quantum state. If nonuniform quantum advice is
allowed, the Ring-LWE assumption must allow the same advice class; one
copy is passed to the one-shot target invocation. Advice is independent
of fresh setup/secret coins and the challenge bit.

[DERIVED smudge bound] Choose coefficient bounds `BK,BE` with

```text
τK ≥ Pr[max_(i,j,k) |z_(i,j,k)| > BK],
τe ≥ Pr[max_(j,k) |e_(j,k)| > BE],
C = wN BK BE,
S = min(1, d C/(2F+1)) + τK + τe.
```

[DERIVED] On the bounded event, the shift
`t_i=const(<z_i,e>)` has `|t_i|≤C`. Translating an independent uniform
integer interval of size `2F+1` by an integer `t` has distance
`min(1,|t|/(2F+1))`; a product hybrid sums over the `d` scalar floods.
Thus a real challenge can change to

```text
c0=A s+e,       h_i=const(<z_i,c0>)+f_i+Δa_i
```

at distance at most `S`, retaining even all of `Z,s,e`. No independence
claim is made about the secret-dependent shift. Only the transmitted scalar
flood is shifted, so the bound has `d` outputs, not `dN` outputs.

[DERIVED computational step] Use the stated ordinary Ring-LWE challenge
for `c0`, sample `Z` independently and compute the public `P` and the
modified scalar `h` using the known `Z`. This changes `c0` to independent
uniform `u∈R_q^w` at cost `εRLWE`. The reduction does not need the
unknown challenge secret `s` or error `e`. There is no multi-hint or
noise-convolution reduction.

[DERIVED joint mask step] Apply the ring lemma to `[A;u]∈R_q^(2×w)`
and all `d-j` unexposed rows. Their pairs
`(P_i,<u,z_i>)` become independent uniform ring pairs, retaining `A,u,Z_J`
and the exposed products. Project each second output to its constant
coefficient. It is now an independent uniform scalar, even given the
entire public `P`. It hides `f_i+Δa_i`; the exposed coordinates have
equal `a_i` by challenge validity. Public-view-dependent messages and the
adversary's quantum state are handled by a common channel on the full
joint tuple, not by conditioning on a particular transcript.

[DERIVED compression justification] One could first produce a full ring
second component and then discard all but its constant coefficient.
The other flooding coefficients are independent and never feed `c0` or
the retained constant coefficient. Marginalizing them gives exactly the
algorithm above. The joint mask proof also directly gives the same result
without generating any unused coefficients. This discards ciphertext
coordinates, not plaintext coordinates.

[DERIVED finite theorem] For at most `T` adaptive valid fresh-input pairs,
using difference-of-acceptance-probabilities advantage,

```text
Adv_public ≤ 2 δ_(d-r)(1)
           + 2T [εRLWE + S + δ_(d-j)(2)].
```

[DERIVED] Use a sequential hybrid changing one target challenge at a time.
Other ciphertexts are generated by the original public encryption algorithm;
one augmented ring row suffices per target. Initial setup distance is paid
once per bit world, not `T` times. All reductions are straight-line
classical transformations around a QPT adversary. Exact ideal sampling is
the mathematical model; tuple-level finite sampling discrepancies and
polynomial-resource requirements must be added for an implementation.

## 4. Correctness, retained full space and scalar-window closure

[DERIVED exact phase] For each actual recipient,

```text
v_i = Δa_i + f_i - const(<z_i,e>) mod q.
```

[DERIVED] On the bounded event set `E=F+C`. Any scalar combination of
issued ciphertexts with integer coefficient L1 norm at most `W` has error
at most `WE`, and its accumulated centered plaintext lift has absolute
value at most `WX`. Sufficient conditions for unique nearest-codepoint
decoding, including the gap across the residue-circle boundary, are

```text
D ≥ 2WX+1,       Δ=floor(q/D)>2WE.
```

[DERIVED] For a workload of `T` fresh ciphertexts, coefficient-tail
correctness failure is at most `τK+Tτe` if `τe` is a per-input bound.
Flooding has a deterministic bound. Source conditioning/rejection is not
needed by these algorithms. This correctness event is separate from privacy.

[DERIVED closure] Keep the full `w` ring elements of `c0` and all `d`
scalars of `h` under componentwise addition/subtraction. Exact expiry of
the original ciphertext cancels its original error. A window or signed
linear combination is covered by the `W` bound regardless of total stream
length. Public offsets add `Δ` times the desired integer coordinate lift
to `h`, subject to the same declared lift interval. Reducing individual
messages modulo `p` is already part of `a(x)`; decode the aggregate
integer lift before reducing the result modulo `p`.

[DERIVED full-space claim] The input domain is all `F_p^d`, and `a` is
bijective. Every one of its `d` coordinates enters the retained scalar
ciphertext. In the statistically close honest comparison every coordinate
has a valid Gaussian cancellation row. Thus the construction retains a
full-vector representation instead of encrypting only the permitted
projection values. A nonzero vector in `ker Y_J` gives an ambient valid
challenge pair, but an actual learner's semantic image still needs its own
nonvacuity witness. This is not a claim that `dN` independent plaintext
coefficients survive the ciphertext compression.

[DERIVED limitations] Arbitrary matrix transforms, changed recipient keys,
nonlinear learner steps, unbounded coefficient growth, malicious setup,
selected-output simulation and integrity are not established. Recipient
rows remain direct read capabilities on every retained input ciphertext.

## 5. Public finite witness and its interpretation

[DERIVED/EXECUTED] `check_public_math.py` and `RESULTS.json` give an exact
public-parameter witness and size counts. It uses `N=4096`, `w=64`,
`σK=2^24`, `σe=2^10`, `F=2^244`, `BK=8σK`, `BE=8σe`,
`d=577,r=16,W=32,T=384`, and the earlier public fixture's
`p=28,439,893`, with `D=d(p-1)/2`. A public integer-order certificate
proves primality and complete splitting for the specified 289-bit `q`;
it is not a probable-prime or computational-hardness estimate.

[OPEN decisive next] Independently review the ring regularity proof,
compressed view and source distinctions. Then evaluate the exact
Ring-LWE hypothesis and implementation sampling costs if separately
authorized. No scalar-LWE hardness result, ring implementation timing,
NTT library guarantee or numerical security level is inherited by this
mathematical witness.
