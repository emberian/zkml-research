# Float in ZK: three regimes, and where our bf16 finding actually sits

2026-08-11. Sourced from two papers ember unblocked. This revises the framing of
`docs/bf16-exact-arithmetization.md` — that note's two computed facts stand, but
the literature has more of the answer than I assumed, and one paper is close to
being the theoretical foundation for the whole ambition.

## Regime 1 — exact IEEE-754 by binary circuits (the baseline everyone avoids)

**Garg, Jain, Jin, Zhang — "Succinct Zero Knowledge for Floating Point
Computations", CCS'22** (`~/paperbin/zk-float-ccs22.pdf`).

The standard approach converts float ops to binary circuits following IEEE-754.
For w-bit precision each operation is a binary circuit *polynomial* in w. Their
concrete figure, quoted: converting multiplication over IEEE 32-bit floats
(w = 24) gives a binary circuit of **8854 gates**, and prover running time
"increases roughly 9000-fold."

That is the number to beat, and it is why everyone quantizes.

## Regime 2 — relative-error semantics (Garg et al.'s move)

Rather than proving bit-exact IEEE, they prove for each gate `g` with inputs
`a, b` and output wire `c`:

```
|c − g(a,b)| ≤ δ·|g(a,b)|
```

i.e. the output is within relative error δ of the *precise* value, where δ can
be set to machine epsilon. Prover time then grows only **log(w)**. Reported:
**~57× faster than exact IEEE for fp32, ~236× for fp64.**

Their justification is the right one and worth stealing: in numerical linear
algebra, backward error analysis for Gaussian elimination and matrix
decomposition **relies only on relative-error bounds**. So a relative-error
proof composes with standard numerical analysis to give real guarantees about
output accuracy. That argument applies directly to matmul.

⚠ **Their construction is in standard prime-order groups — it is not
post-quantum.** They also contribute a batch range proof in prime-order groups
that avoids bit decomposition. Both are DL-flavoured. The *model* transfers to
a hash-based setting; their *machinery* does not.

## Regime 3 — approximation as a first-class citizen (the interesting one)

**Bitan, DeStefano, Goldwasser, Ishai, Kalai, Thaler — "Sum-check protocol for
approximate computations", 2025** (`~/paperbin/sumcheck-approx-2025-2152.pdf`).

Motivated by exactly our mismatch: *"floating point arithmetic, which is
intrinsically approximate, and verifiable computing protocols for exact
computations."*

They generalize sum-check to claims of the form `Σ_{x∈{0,1}^v} g(x) ≈ H`. The
verifier checks each round with a **tunable error parameter δ**; if Δ is the
error in the prover's initial claim, soundness degrades **gracefully with δ/Δ**.
The generalization is algebraic — it exploits the *metric* structure of
low-degree polynomials.

The headline, quoted: *"the first black-box feasibility result for approximate
arithmetic proof systems: the protocol compiler is independent of how arithmetic
operations are implemented, requiring only that they satisfy error bounds. This
opens a path to verifying approximate computations while sidestepping much of
the prover overhead imposed by existing techniques that require encoding
real-valued data into finite field arithmetic."*

That last clause is the ambition ember stated, in a 2025 paper by Goldwasser,
Ishai, Kalai and Thaler.

Two cautions, both from the abstract:

- It is **"most natural over the complex numbers"**, with the analysis drawing on
  polynomials over the unit circle. That is *not* obviously compatible with a
  hash-based STARK over BabyBear. Instantiation over other domains is claimed
  but the natural home is ℂ.
- Under Fiat–Shamir they report **a new "intermediate security" phenomenon that
  appears intrinsic to approximation.** Unread; but "a new FS phenomenon
  intrinsic to the technique" is exactly the kind of thing that turns into a
  soundness surprise, and it should be read before anything is built on it.

## Where the bf16 finding actually sits

It is not a fourth regime. It is the observation that **at bf16 width, regimes 1
and 2 collapse into each other for two large classes of operation**:

- **Unary functions**: 2^16 values ⇒ the complete graph is a 65_536-row table.
  Exact, at whatever rounding the table encodes. No δ, no error term, no
  approximation machinery. Regime 1's cost without regime 1's price.
- **Multiplication**: 8-bit significands ⇒ the product is exact in fp32
  (verified, 200k pairs). **No rounding circuit exists to build.** Garg et al.'s
  8854 gates are for w = 24; at w = 8 into a 24-bit accumulator there is nothing
  to round.

So the honest claim is narrower and better than "we can do real floating point
cheaply": **bf16 is the width at which the expensive parts of float
arithmetization mostly disappear**, and it happens to be the width ML already
uses. Garg et al.'s speedup is over fp32; ours would be a different argument —
not a faster fp32, but a format where the cost was never incurred.

## Where approximation is still needed, and now has a tool

`docs/bf16-exact-arithmetization.md` flagged **accumulation** as the crux: exact
products, but summing them needs either bit-matched fp32 rounding (expensive,
and inherits GPU reduction-order nondeterminism) or a wide exact accumulator
(order-independent, more accurate than the hardware, but ~280 bits at full bf16
dynamic range).

Bitan et al. give a principled third option: **prove the accumulation
approximately, with a stated error bound**, and compose via Garg et al.'s
numerical-analysis argument. That is a much better fallback than "use a narrower
accumulator and hope."

Open question this raises, and I do not know the answer: whether approximate
sum-check can be instantiated over BabyBear (or an extension) rather than ℂ,
and what the FS "intermediate security" phenomenon costs there. **That is
probably the single highest-value technical question in this whole programme**,
because it decides whether we get regime-3 economics with post-quantum security.

## Status of claims

- **Verified here**: 2^16 bf16 values; bf16×bf16→fp32 exact over 200k random
  pairs against exact rationals.
- **Sourced**: 8854 gates / ~9000-fold (Garg et al. §1–2); log(w) prover growth,
  57×/236× (Garg et al. §2); relative-error model and its numerical-analysis
  justification (Garg et al. §2.1); approximate sum-check statement, δ/Δ
  soundness degradation, black-box feasibility, ℂ/unit-circle naturalness, FS
  "intermediate security" (Bitan et al. abstract).
- **Inferred by me**: that bf16 collapses regimes 1 and 2 for unary and
  multiply; that approximate sum-check is the right tool for accumulation; that
  BabyBear instantiability is the pivotal open question. None of these are
  sourced.
- **Not yet read**: both papers beyond the front matter. Neither the accumulation
  treatment nor the FS phenomenon has been checked.


## Addendum 2026-08-12 — two regimes the full-corpus mine added

**Regime 4 — rounding as a low-degree polynomial, GKR over a ring.**
eprint 2019/762 (Chen, Cheon, Kim, Park; MSR/SNU) reduces ROUNDING to a
low-degree polynomial and runs GKR over a ring rather than a field — from 2019,
explicitly motivated by AI workloads ("VC is currently missing the opportunity
in the whole AI space where approximate computations are unavoidable"). Bitan
et al. 2025/2152 cites it; our record did not. This is the direct ancestor of
the approximate line, with a different (ring) instantiation route.

**Regime 5 — arguments native to ℤ and ℚ.** Zinc (eprint 2025/316, Nethermind):
hash-based succinct arguments over the integers and rationals, no hidden-order
groups, arbitrary moduli including composite — bypassing "arithmetization
overheads of orders of magnitude" instead of choosing a field at all. A
different answer to requantization than any format choice; Limber (2026/1635)
is the same commit-then-fingerprint family.
