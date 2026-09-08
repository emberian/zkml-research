# Public ring witness: exact inequalities, not a hardness estimate

[EXECUTED, 2026-09-08] Command:
`python3 research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_candidate/check_public_math.py`.
Exit 0. `RESULTS.json` preserves all checks. This is public integer,
rational and polynomial arithmetic only: no keys, ciphertexts, Gaussian
samples, estimator or attack program were generated or run.

## 1. Ring and public modulus certificate

[EXECUTED] The arithmetic witness uses

```text
N=4096, w=64,
q=4294967767·2^256+1
 =497323290947860672931310292648754779192460749687510494957169639477681564739617435942913.
```

[EXECUTED] It lies strictly between `2^288` and `2^289`; exact modular
arithmetic gives `3^((q-1)/2)=-1 mod q`. The bounded public search tried
236 odd coefficients beginning at `2^32+1`, testing bases `2,3,5,7,11`;
the saved `searches/prime_certificate.json` records the successful witness.

[DERIVED primality proof] For any prime divisor `ell` of `q`, the witness
has order whose 2-adic part is exactly `2^256`: its `c·2^255` power is
`-1`, for odd `c=4294967767`, and its `c·2^256` power is one. Therefore
`2^256` divides `ell-1`, so `ell≥2^256+1>sqrt(q)`. A composite integer
has a prime divisor at most its square root. Hence `q` is prime. This
is an order certificate, not a probable-prime test.

[EXECUTED/DERIVED splitting] Put `ζ=3^((q-1)/(2N)) mod q`. The checker
verifies `ζ^N=-1` and `ζ^(2N)=1`; because `2N` is a power of two,
its order is exactly `2N`. Its odd powers are the `N` distinct roots
of `T^N+1`, proving complete splitting over `F_q`.

## 2. Key width and ring regularity

[DERIVED/EXECUTED] Let `σK=2^24`, `θ=3/64`, and Gaussian quotient
error `δ=2^-192`. The coefficient dimension is `Nw=2^18`.
Using `ln2/π<1`, the logarithmic factor in `RING_REGULARITY.md` obeys

```text
ln(2Nw(1+1/δ))/π < 192+18+2 = 212.
```

[EXECUTED] The exact integer inequality
`σK^64 ≥ (212N)^32 q^3` holds; it implies
`σK²≥212N q^(3/32)`, the required squared smoothing-width condition.
The condition `B=q^(61/64)/sqrt(N)≥1` is checked by raising it to an
integer power. No floating-point logarithm or root decides acceptance.

[DERIVED] For `k=1`, `wθ-k=2`, and for `k=2`, `wθ-k=1`. Thus the
short-vector probabilities are at most `2^4096/q^384` and
`2^4096/q^192`, respectively. The CRT rank bound is
`4096 Σ_(i=0)^(k-1) q^(i-64)`. Exact rational arithmetic verifies
rank plus short-vector error below `2^-192` in each case, giving

```text
δ_h(k) < (2h+1)·2^-192,     k∈{1,2}, h≥1.
```

## 3. Flooding, correctness and full privacy ledger

[DERIVED/EXECUTED] Use the fixed public parameters

```text
d=577, r=16, W=32, T=384,
p=28,439,893, X=(p-1)/2=14,219,946,
D=dX=8,204,908,842, Δ=floor(q/D),
σe=2^10, BK=8σK=2^27, BE=8σe=2^13,
F=2^244, C=wN BK BE=2^58, E=F+C.
```

[DERIVED Gaussian tail] For an integer Gaussian width `σ≥1` and
integer threshold `tσ`, `t≥1`, its normalizer is at least one. Bounding
the two tails by the first term plus the decreasing Gaussian integral
gives

```text
Pr[|G|≥tσ] ≤ 2(1+σ/(2πt)) exp(-πt²)
            ≤ 3σ exp(-πt²).
```

[DERIVED] At `t=8`, `π>4ln2` gives the strict upper bound
`3σ·2^-256`. Therefore the all-row and per-input events can use

```text
τK = 3dNw σK·2^-256,
τe = 3Nw σe·2^-256,
S ≤ dC/(2F+1)+τK+τe.
```

[EXECUTED] Exact arithmetic verifies `D≥2WX+1` and `Δ>2WE`, so all
allowed scalar combinations decode on that event. The total correctness
failure bound `τK+Tτe` is strictly below `2^-203`. The saved strict key
storage event is `|z|<BK`; its complement is included in the tail above.
It uses 28 signed bits per coefficient. The inclusive interval `[-BK,BK]`
would instead require 29 bits; the algebra conservatively uses `BK`.

[DERIVED/EXECUTED] Substituting the explicit ring regularity and smudging
bounds into `CANDIDATE.md` gives, for either `j=0` or `j=16`, and hence
for any fixed coalition of actual recipients,

```text
Adv_public < 768 εRLWE + 2^-168.
```

[DERIVED] This number bounds statistical proof terms for ideal exact
samplers. It does not bound `εRLWE`, sampler approximation, runtime or
side-channel leakage. Correctness failure is a distinct quantity and is
not silently folded into privacy.

## 4. Exact representation and arithmetic counts

[EXECUTED] These are bit-packed mathematical sizes, with every ciphertext
or public residue allocated 289 bits; they are not an implementation's
wire format, allocator peak, timing or bandwidth measurement.

| Item | Count or bytes |
|---|---:|
| Compressed ciphertext coefficients | 262,721 |
| Compressed ciphertext | 9,490,797 B |
| Full ring ciphertext before scalar projection | 94,847,488 B |
| Public `A` | 9,469,952 B |
| Public `P` | 85,377,536 B |
| Public `A,P` together | 94,847,488 B |
| One recipient row on the strict tail event | 917,504 B |
| Sixteen recipient rows on that event | 14,680,064 B |
| Fresh encryption, full ring products | 64 |
| Fresh encryption, scalar signed-product multiplications | 2,363,392 |
| Fresh encryption, Gaussian coefficients | 262,144 |
| Fresh encryption, scalar flood draws | 577 |
| Recipient read, coefficient multiplications | 262,144 |
| One add/subtract, residue operations | 262,721 |

[DERIVED] The public `A` is `w` ring elements, instead of a full ordinary
LWE matrix with the corresponding expanded scalar shape. This is precisely
where the matrix storage and convolution speed opportunity comes from.
The Ring-LWE assumption is consequently different. These counts alone
cannot establish that the new witness meets any computational security target.

## 5. Algebraic controls and remaining work

[EXECUTED] Exhaustive small signed-coefficient controls verify the
negacyclic constant-product identity in 6,642 polynomial pairs, and 224
finite interval controls verify the exact uniform-shift formula. The saved
`q=17,N=4` CRT idempotent `[13,15,16,8]` has CRT values `[1,0,0,0]`
and proves the source rejection-test counterexample. These are public
algebra examples, not generated cryptographic state.

[OPEN] Independent theorem review, the exact Ring-LWE computational
hypothesis, a sampler/representation implementation contract, and measured
performance are outstanding. The published 2021/046 implementation
parameters and older scalar-LWE estimates do not certify this point.
