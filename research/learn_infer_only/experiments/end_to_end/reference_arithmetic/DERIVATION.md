# Public BFV byte and arithmetic correspondence

[SOURCE] This packet pins the implementation actually used by the captured
`crypto/src/main.rs` run. Exact absolute paths, line ranges and SHA256 values
are in [source-map.json](source-map.json). The historical source and copied
binary hashes agree with the retained host-runtime pins. Reading and hashing
that binary does not execute it or prove a source-to-binary correspondence.
The recorded dependency fingerprint has no optional `fhe-math` features, so
`src/ntt/mod.rs:5–15` selects its native backend.

## What the bytes mean

[SOURCE] The outer object is `RSBFV001`, kind byte `1`, 32 parameter-identity
bytes, 32 declared-key-identity bytes, an eight-byte little-endian payload
length, and the payload (`crypto/src/main.rs:75–94`). The full canonical
ciphertext payload contains two repeated protobuf byte fields numbered `1`;
the seed and level-zero fields are absent (`bfv/ciphertext.rs:167–181`,
`proto/bfv.proto:5–9`). Each polynomial is protobuf representation `2`, degree
`4096`, coefficient bytes, and variable-time flag `true`.

[SOURCE] The representation tag is easy to misread: **the serialized numbers
are power-basis coefficients even when the tag is NTT**.
`fhe-math/src/rq/convert.rs:15–47` clones an NTT polynomial, changes the clone
to power basis, serializes that clone's coefficients, and preserves the
original representation tag. Its decoder at `:151–210` reads power-basis
coefficients and subsequently applies the requested representation.

[SOURCE] Limb order follows the context's modulus order. The two widths are
`bit_length(q_i-1)`, namely 41 and 42 bits, at moduli `2199023190017` and
`4398046486529` (`zq/mod.rs:747–770`). `fhe-util/src/lib.rs:58–125` concatenates
coefficient bits in increasing coefficient order, least-significant bit
first. There is no per-coefficient byte alignment or limb delimiter.

[DERIVED] For one polynomial the coefficient bytes total
`4096*(41+42)/8 = 42496`; the two polynomial messages and ciphertext protobuf
framing produce 85022 payload bytes. The wrapper adds 81, giving 85103 bytes.
The reference reads each limb as one little-endian integer and extracts
successive fixed-width fields. Its inverse constructs that integer and emits
its bytes. This differs from the production streaming `u128` transcoder.

[EXECUTED] All retained objects pass full independent decode/re-encode and
canonical residue checks. The verifier accepts only the fixed two-component,
unseeded level-zero format used in these captures. This is a scoped decoder,
not a general protobuf or arbitrary-parameter FHE implementation.

## The independent polynomial relation

[SOURCE] The public Learn command computes `acc += fresh; acc -= old` when an
old ciphertext is supplied (`crypto/src/main.rs:224–238`). Ciphertext
add/sub operates independently on each component (`bfv/ops/mod.rs:54–69`,
`:149–164`). For component `c`, modulus `q_i`, and coefficient `k`, the
reference therefore computes

```
L[c,i,k] = (acc[c,i,k] + fresh[c,i,k] - old[c,i,k]) mod q_i.
```

[SOURCE] The Infer command reverses the 577 public query coefficients, forms
their separate nonnegative positive/negative parts, polynomial-encodes each,
multiplies the accumulator by both plaintexts, and subtracts
(`crypto/src/main.rs:240–254`). Polynomial plaintext encoding copies that
prefix, zero-pads to degree 4096, and transforms it
(`bfv/plaintext_vec.rs:93–139`). Ciphertext-plaintext multiplication uses that
unscaled polynomial (`bfv/ops/mod.rs:229–255`). No ciphertext-ciphertext BFV
rescaling, base extension or relinearization occurs on this path.

[DERIVED] Put `b[j]=query[576-j]` for `0≤j≤576`, and zero elsewhere. In
`Z_q[X]/(X^4096+1)`, the expected output is

```
I[c,i,k] = (
    sum_{0<=j<=576, j<=k} acc[c,i,k-j] * b[j]
  - sum_{0<=j<=576, j>k} acc[c,i,4096+k-j] * b[j]
) mod q_i.
```

Integer bilinearity makes this equal to the source's positive product minus
negative product. Both signed and split-product calculations are executed
for the first Infer in each retained suite. The primary reference uses
unbounded Python integers, performs schoolbook multiplication, applies the
negative wrap, and reduces modulo `q_i` only at the end. It does not obtain
coefficients or arithmetic answers through a production-library API.

[DERIVED] Full-array checking matters: for output indices below 576, the
formula includes actual negacyclic wrap terms. A check confined to the
designated readout coefficient 576 would miss those terms. This packet
checks all 4096 coefficients of both components and both RNS limbs.

## Source roots and index order

[SOURCE] `ntt/native.rs:314–347` seeds `ChaCha8Rng` from the public integer
zero, draws a candidate in `[0,q)`, raises it to `(q-1)/(2N)`, and accepts it
when its `2N`-th power is one and its `N`-th power is not one. Here `N=4096`.
The source searches at most 100 candidates. This packet does not reproduce
those random draws or claim a verified literal PRNG/Rust implementation.

[DERIVED] Write `ψ` for a primitive `2N`-th root and `rev_d` for reversal of
exactly `d=log2(N)` bits. The source constructor stores

```
omegas[k]   = ψ ^ rev_d(k)
zetas_inv[k]= ψ ^ -(rev_d(k)+1).
```

Those formulas follow from `native.rs:36–48`: the inverse-power iterator
starts at `ψ^-1`, rather than at one. Normalizing each source butterfly to
modular equations gives `(x+ω*y, x-ω*y)`. Its descending-stride forward loop
(`:67–94`, or the same index schedule in the public variable-time path
`:134–181`) consequently computes

```
Forward(a)[k] = a(ψ ^ (2*rev_d(k)+1)) mod q.
```

[DERIVED] One way to derive the order is to follow the first split into low
and high halves. Evaluation at `x=ψ^(2j+1)` has
`x^(N/2)=ψ^(N/2)*(-1)^j`. The first branch therefore selects the parity of
`j`; each subsequent branch selects its next bit. The branch bits become the
output index in reverse order. Repeating the split ends at the stated odd
root. These `N` roots are distinct and all satisfy `x^N=-1`, so pointwise
products correspond to the stated negacyclic quotient ring.

[DERIVED] The inverse schedule is consistent with the forward table. At a
forward level with `m=2^r` blocks, block `i<m` uses twiddle index `m+i`.
The corresponding reversed level uses inverse index `N-2m+i`, and

```
rev_d(N-2m+i)+1 = rev_d(m+i).
```

Indeed, both sides equal
`2^(d-r-1) + 2^(d-r)*rev_r(i)`. Thus the inverse butterfly
`(x+y, (x-y)*ω^-1)` reverses the matching forward butterfly up to a factor
two. The final `N^-1` removes the factor `2^d` (`native.rs:98–123`). This is
a derivation for the normalized modular equations, not a Lean proof of
the actual lazy reductions, unsafe pointers or machine-word operations.

[EXECUTED] The independent reference deliberately chooses roots by a different
algorithm: test ascending small integer bases, exponentiate by
`(q-1)/(2N)`, and retain the first root with `ψ^N=-1`. The roots are
`707897838669` and `3119419343111`, respectively. Exhaustive trial division
through the integer square root checks both moduli are prime; both selected
roots' 4096-th and 8192-th powers are checked. These are **reference roots**,
not claimed numeric outputs of the source's ChaCha selection.

[DERIVED] The reference's ascending-stride cyclic transform uses
`DFT_{ψ²}(a_j ψ^j)` in natural evaluation order, then an inverse cyclic
transform and the inverse twist. It therefore supplies a distinct algorithm
for the same polynomial product. A different primitive root only permutes
the odd-root evaluations; after the matching inverse, the power-basis
product is unchanged. Equality of root choices is unnecessary for the
serialized arithmetic comparison.

[EXECUTED] The source-indexed normalized schedule agrees with direct odd-root
evaluation on every basis vector at `N=8,16,32`, for two primitive roots at
each size: 112 basis inputs in all. Product and inverse checks also pass.
For each suite's first real Infer, all four complete N4096 public arrays
match the independent transform after the exact bit-reversal permutation;
the source-indexed inverse and product agree as well. Every captured Infer
also matches the primary schoolbook calculation and the independent twisted
cyclic transform over all output coefficients.

## Limits

[OPEN] This closes a sampled public arithmetic cross-check that previously
reused the same library in several roles. It does not establish universal
Rust or compiler refinement, every representation/parameter combination,
noise/decryption correctness, ciphertext key membership, input provenance,
finality/signature verification, or the absence of unrestricted read
credentials. No ciphertext-ciphertext multiplication, source NTT pointer
proof, adversarial extraction/routing test, private vector, secret key, or
decryption operation is part of the executed reference. The finalized utility
envelope is retained as public provenance; this checker does not verify its
signature or rerun its release path.
