# Exact classical programming kernel for the chunked row expander

[DERIVED theorem, 2026-09-08] For a fresh classical random-oracle namespace,
there is a finite randomized kernel that takes a prescribed target row
`u in [0,q)^N`, produces a full capped oracle-chunk table, and makes the
expander return `u` on success. Abort probability is independent of `u` at
fixed parameters. For independent uniform `u`, the **entire** programmed
chunk table is exactly distributed as independent uniform raw bits, with
the original abort probability. The target and the programmed table are
necessarily correlated; their joint law is specified below.

[SOURCE: implementation, fully read] The source is the frozen
`../../ring_seed_transport/expansion/public_expander.py`, SHA256
`ab175083b2a38e382776f07a52a0d8b84e8886085f40f083117de273f0d0aba4`.
Its fixed-size, index-addressed chunks contain 1,024 raw candidate words;
it masks each word to `(q-1).bit_length()` bits, rejects residues at least
`q`, and stops at the Nth accepted candidate or its declared chunk cap.
This note does not edit or execute that cryptographic implementation.

## 1. Objects and assumptions

[DERIVED] Fix a public context `c` containing a valid seed, binding, family,
row index, N and q, with the exact canonical addresses from the source. Let

```
b = ceil(log2 q) = (q-1).bit_length(),
t = ceil(b/8),  r = 8t,  h = r-b,
K = 1024,  C = ceil(4N/K)+16,  M = KC.
```

Let `T=(W_0,...,W_(M-1))` be all raw candidate words in **all C chunks**,
including chunks that the expander would never request after early success.
An ideal fresh chunk table is uniform on `[0,2^r)^M`. Write
`X_i=W_i mod 2^b` and `H_i=floor(W_i/2^b)`. Each `X_i` is uniform on
`[0,2^b)`; each `H_i` is independent uniform on `[0,2^h)`.

[DERIVED] Let `a_i=1[X_i<q]`. On at least N acceptances, let
`s_0<...<s_(N-1)` be the first N accepted positions and define
`Out(T)=(X_s0,...,X_s(N-1))`. Otherwise define `Out(T)=abort`.
The acceptance skeleton is `(a_i)`, and later accepted positions are **not**
part of the returned row. Conditional on a skeleton, accepted low words
are independent uniform in `[0,q)`; rejected low words are independent
uniform in `[q,2^b)`. High words remain independent uniform. Empty rejected
support when q is a power of two simply means such skeletons have zero mass.

[DERIVED premise] All programmed addresses are fresh: no existing oracle
answer has exposed a conflicting prefix at them. At a fixed context, the
base table and its additional oracle tails are sampled independently of
the supplied target and prior transcript. To obtain the exact ideal-table
law, the target is uniform in `[0,q)^N` conditional on that context and
external transcript. If context selection depends on the target, this
conditional-uniformity premise must be proved, not inferred from a uniform
unconditional marginal. Sections 5–6 address freshness and nonuniform targets.

## 2. Concrete finite kernel

[DERIVED algorithm `Program(c,u)`]

1. Sample every one of the `rM` base-table bits independently and uniformly.
2. Locate the first N accepted positions. If there are fewer, retain the
   entire table unchanged and return `(table,abort)`.
3. At each selected position `s_j`, replace **only** the low candidate bits:
   `W'_s_j = (H_s_j << b) | u_j`.
4. Retain every other word byte-for-byte. Return `(T',success)` and reserve
   this complete table as the replies at its exact chunk addresses.

[DERIVED] No additional randomness is needed for replacement: the original
high bits already have the correct independent uniform law. Rejected
candidates, skipped positions, later accepted candidates in the final
used chunk, every completely unused chunk, and the high bits at overwritten
positions all remain present. No zero padding is substituted for random
high bits. Targets are provided to the kernel; their own generation cost
is not hidden in the `rM` base-randomness count.

[DERIVED correctness] Every substituted low word remains below q, so the
acceptance skeleton and first N selected positions are unchanged.
Consequently success returns exactly `u`; abort remains abort. The cap
decision depends only on the original skeleton and is independent of the
target at fixed context. This gives a bounded kernel, not a retry-until-
success algorithm or an abort-to-zero-row substitution.

## 3. Exact distribution proof

[DERIVED pointwise law] Put `p0=2^(-rM)` and fix a target u. For any complete
raw table t, the unconditional output-table probability is

```
Pr[Program(c,u).table = t] =
    p0            if Out(t)=abort,
    q^N * p0      if Out(t)=u,
    0             if Out(t) is successful and differs from u.
```

[DERIVED proof] An abort table is unchanged and has exactly itself as a
preimage; no success table can map to it because the skeleton is preserved.
A successful t with output u has exactly `q^N` preimages: retain its entire
skeleton, all high bits, all rejected words, and every unselected word,
but choose each of its first N accepted low words arbitrarily in `[0,q)`.
All these choices have the same first N accepted positions and are mapped
to t. There are no other preimages. If the output of t differs from u,
correctness excludes every preimage. This proves the formula. **QED.**

[DERIVED fixed-target conditional law] Let `alpha=Pr[Out(T)!=abort]` for an
ideal table. Symmetry/factorization gives
`Pr[Out(T)=u]=alpha/q^N`. Dividing the second line above by alpha shows

```
Law(Program(c,u).table | success)
 = Law(T | Out(T)=u).
```

The right side already includes cap success. On abort, the table has the
ideal table law conditioned on abort, independently of u.

[DERIVED uniform-target theorem] If U is independent uniform in `[0,q)^N`,
average the pointwise formula over its `q^N` possible values. An abort t
gets p0 from every target; a successful t gets `q^N*p0` from exactly its
one extracted target and zero from the others. Thus every table t has
probability p0, exactly the ideal independent-uniform-bit law.

[DERIVED full joint law] The kernel's joint `(U,T',status)` law equals this
ideal experiment: sample T uniformly; if extraction succeeds set U to its
extracted row, and if extraction aborts draw an independent uniform U.
This is the exact joint simulation claim. It is **not** independence of U
and T' on success. Other fresh-address oracle values and unexposed XOF tails
can be sampled independently, extending the equality to the full classical
oracle and every subsequent adaptive recomputation transcript.

## 4. Cap failure and what must not be conditioned away

[DERIVED] Each candidate accepts with `p=q/2^b>=1/2`. For
`S~Binomial(M,p)`, the actual abort probability is
`beta=Pr[S<N]`, independently of the target at fixed N,q. Markov's inequality
gives the same conservative cap bound as the frozen specification:

```
beta <= 2^N (1-p/2)^M <= 2^N (3/4)^M
     <= (81/128)^N (3/4)^16384 < 2^-5461.
```

[DERIVED] The programming kernel has **zero** distributional error against
the ideal capped expander: it retains beta exactly. A cap loss is needed
only when another reference game assumes guaranteed completion or discards
the abort event. With R rows a union bound is at most `R*beta` for fixed
parameters, including adaptive rows when the conditional premises hold.

[DERIVED pitfalls] Repeating base-table sampling until success changes the
unconditional oracle law to its success-conditioned law. Replacing failure
by a deterministic row changes both the output and table relation. A proof
may explicitly compare a conditioned/restarting reference protocol, but
must account for its conditioning/restart behavior; it cannot silently
delete aborts from the original capped experiment. For varying contexts,
abort independence is conditional on the context; do not claim marginal
independence from a target correlated with those parameters.

## 5. Lazy realization, unused chunks and prefix queries

[DERIVED] The full-table kernel is an easy exact sampler and proof object.
An equivalent lazy implementation samples complete chunks in order only
until the chunk containing the Nth acceptance, or until the cap on failure.
It makes the same substitutions and retains the entire final sampled chunk.
Every later capped chunk can be sampled uniformly when first requested.
Those chunks were independent in the full-table proof and were unaffected
by programming. Thus this lazy strategy is a coupling to the full-table
kernel, not an assumption that unused bytes are absent from the transcript.

[DERIVED] Model SHAKE-style queries at a given address by one consistent
infinite random bit stream. The kernel programs the fixed chunk-length
prefix, while any longer suffix is independent and can be sampled lazily.
Shorter requests return the same prefix; longer requests extend the same
stream. Requests at chunk indices beyond the expander cap and unrelated
input addresses remain ordinary independent oracle responses. A simulator
must retain this consistency even though the concrete expander itself asks
only one fixed output length per chunk address.

[DERIVED work] The full-cap version consumes exactly `R*C*K*t` random bytes
for R rows, excluding supplied targets and unrelated oracle queries. It
takes `O(R*C*K*t)` byte work/storage if all tables are retained, with N
overwrites per row. Let `T_N` be the unbounded candidate count to N successes.
The lazy preparation uses at most `ceil(min(T_N,M)/K)` chunks and hence

```
E[preparation bytes per row]
 < t*(N/p + K) <= t*(2N+K).
```

Later adversarial queries can force all C capped chunks and arbitrary oracle
tails to be materialized; their work must be charged separately. The lazy
preparation bound is not the cost of answering an unbounded adversary.

[EXECUTED arithmetic] At N=16384, q289: `t=37`, high padding is seven bits,
`C=80`, `M=81920`. Full-cap cost is 3,031,040 random bytes or 24,248,320 bits
per row. Lazy preparation has expected bytes strictly below 1,250,304 per
row. `CHECKS.json` retains this integer arithmetic. These are counts, not
cryptographic timings or secretly executed matrix generation.

## 6. Namespace chronology and prior classical queries

[DERIVED] Program before publishing the fresh seed/namespace, or reserve a
lazy programmed namespace before any query can reach it. Once an oracle
prefix was returned, it cannot be overwritten silently. The exact theorem
therefore applies conditional on no conflicting prior query; otherwise the
simulation must expose a bad-event/abort or supply a different consistency
argument. Public later recomputation is harmless **after** consistent
programming, because it receives the preserved/programmed full transcript.

[DERIVED classical freshness bound] Suppose a lambda-bit seed is sampled
uniformly and independently of the existing transcript, and at most Qpre
oracle input addresses were queried before programming. At its fixed seed
length, the canonical domain encoding lets any prior input specify at most
one seed. Therefore the probability that a prior query already touched any
of the programmed addresses is at most `Qpre/2^lambda`. No extra factor for
rows/chunks is necessary for this coarse same-seed bound: a matching address
already requires the one seed guess. Multiple independently fresh seeds
can be charged by summing their corresponding conditional bad-event bounds.

[DERIVED chronology limits] This bound does not cover queries made after
the seed becomes public but before its namespace is programmed. If a later
registry binding is needed, either publish a separately fresh seed after
that binding is fixed and program before disclosure, or prove a different
chronology/freshness claim. Unpredictability of an unspecified future binding
cannot simply be assumed. Distinct canonical row/family/chunk addresses
must also remain distinct; overlapping programmed namespaces require joint
handling. The parent owns the A/missing-row and registry dependency order.

## 7. Use in a larger hybrid and scope

[DERIVED data-processing interface] For a common context and kernel, if
the required joint target distribution is within delta total variation of
the conditionally uniform target distribution, applying this kernel to both
changes distance by at most delta. Include context, public auxiliaries,
abort flags and the oracle replies in this common channel. This is a
mathematical route for lifting an already proved joint regularity statement;
it does not prove that the parent's `Z*A` targets satisfy that statement.
No silent conditioning on freshness/success is part of the contraction.

[OPEN] Parent must establish the complete A/missing-row target distribution,
its correlations with registered credentials and context, and the full
construction's hybrids. This note supplies only the exact classical
transcript-programming kernel and explicit freshness interface. It is a
programmable random-oracle argument, not a program that can overwrite fixed
SHAKE256 outputs. There is no concrete-XOF theorem, QROM reprogramming bound,
quantum-query simulation claim, lattice estimate or actual crypto run here.
