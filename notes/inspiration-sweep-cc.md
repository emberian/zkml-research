# Inspiration sweep — complexity theory (cs.CC / ECCC / STOC-FOCS-CCC)

Sweep date: 2026-08-13. Lane: literature scouting for Selvage.

**Corpus baseline.** `~/paperbin` = 1528 PDFs, IACR-eprint-dominated. Instrument: `ls ~/paperbin | grep -i`.
Measured absences *in our corpus* before this sweep:
- zero hits for `proximity` that are IPP — all 29 hits are FRI/Reed–Solomon *proximity gaps* (a different object).
- zero hits for streaming interactive proofs (`stream` hits = KV-cache, stream ciphers, Scribe's low-memory SNARK).
- zero hits for `pcp|dinur|arora|holograph` except one accumulation paper.
- zero hits for `communication|rigidity|kernel|sparsif|sketch` in the complexity sense.
- zero hits for `fortnow|santhanam|algebriz|instance compression`.
So: **the complexity literature is a genuine blind spot, confirmed by instrument, not assumed.**

Everything below was downloaded to `~/paperbin/` with a `cc-` prefix and text-extracted; theorem
statements are quoted from the extracted text, not from abstracts.

---

## FIND 1 — Fortnow–Santhanam, *Infeasibility of Instance Compression and Succinct PCPs for NP* (STOC'08 / JCSS'11)

`~/paperbin/cc-fortnow-santhanam-instance-compression-succinct-pcps-for-np.pdf`
(EATCS–IPEC Nerode Prize 2014.)

**This is the highest-value find and it is the one that constrains us.** It is a lower bound of
exactly the shape the brief asked for: *the boundary of a relation cannot be compressed below X*.

### The statements, quoted

> **Theorem 1.2** If NP is not contained in coNP/poly then there is no set A and function f such
> that given m Boolean formula φ₁, …, φ_m where each φ_i has length at most n, f has the following
> properties
> • f is computable in time polynomial in m and n,
> • f(φ₁, …, φ_m) ∈ A if and only if at least one of the φ_i is satisfiable, and
> • |f(φ₁, …, φ_m)| is bounded by a polynomial in n.

> **Definition 2.2** Let L be a parametric problem and A ⊆ {0,1}\*. L is said to be *compressible
> within A* if there is a polynomial p(·), and a polynomial-time computable function f, such that
> for each x ∈ {0,1}\* and n ∈ ℕ, |f(⟨x, 1ⁿ⟩)| ⩽ p(n) and ⟨x, 1ⁿ⟩ ∈ L iff f(⟨x, 1ⁿ⟩) ∈ A.

> **Theorem 3.1** If OR-SAT is compressible, then coNP ⊆ NP/poly, and hence PH collapses.

> **Corollary 3.2** If SAT is compressible, then coNP ⊆ NP/poly, and PH collapses. The same
> conclusion holds if Clique, DominatingSet or IntegerProgramming are compressible.

And the PCP half — note their definition of *succinct*, which is **precisely our boundary/interior
distinction stated in 2007 vocabulary**:

> A succinct PCP for an NP language L is a probabilistically checkable proof for L where the size
> of the proof is polynomial in the **witness size n** rather than in the **instance size m**.
> Current proofs of the PCP theorem [AS98, ALM+98, Din07] do not yield such PCPs.

> **Theorem 4.2** If SAT has succinct PCPs, then SAT is self-compressible with error less than 2^−m.
> **Theorem 4.3** If SAT has succinct PCPs with completeness c, soundness s, proof size poly(n) and
> query complexity O(1), where c+s is computable in time poly(m) and c−s ⩾ 1/poly(n), then SAT is
> self-compressible.
> **Corollary 4.4** SAT does not have succinct PCPs unless NP ⊆ coNP/poly and PH collapses.
> **Theorem 4.5** If SAT is self-compressible, then SAT has succinct PCPs.

Theorem 4.5 + Corollary 4.4 together make it an **equivalence**: succinct PCP ⟺ instance
compression. So "can I state this relation on its boundary" is not a soft engineering question;
it is a known, named, and partially *closed* complexity question.

### What it touches, and how hard

INFERENCE (mine, flagged): the sharp reading for Selvage is not "boundary discipline is dead". It
is that **the theorem names the operator that kills compression, and that operator is OR.**

- Our workloads compress because they are **AND-shaped**: a matmul is a conjunction of n² inner
  products; sumcheck batches a conjunction by random linear combination, and the boundary is n².
  Random-linear-combination batching is exactly an AND-compressor.
- OR-SAT is the **disjunctive** shape, and FS says a disjunction of m independent size-n claims
  provably has no boundary of size poly(n). No amount of protocol cleverness fixes it; it is a
  PH-collapse-level obstruction, unconditional relative to a very safe assumption.
- So the discipline should read: **AND-composition has a boundary; OR-composition does not.** Any
  place Selvage wants to prove "one of these m branches fired" — a dispatch table, a kernel syscall
  demux, an ML control-flow branch, an FHE bootstrapping-path selector — is exactly where the
  boundary statement is *provably* not cheaper than the interior, and we must pay to make the
  disjunction *witnessed* (prover names the branch) rather than *proved*.

That last sentence is the usable engineering rule and it falls straight out of the theorem: **make
every OR into a witnessed selector, never a proved disjunction.**

**Contradicts us?** It does not contradict "an AIR commits the interior, a sumcheck commits the
boundary." It contradicts the *unqualified* form of "we want a discipline for picking the cheapest
boundary statement of a computation" — there is a proved class of computations with no cheap
boundary, and it is identifiable syntactically (unbatchable disjunction). Distance to usable: the
theorem is usable *today* as a design rule; no formalization needed to benefit.

---

## FIND 1b — the correction to FIND 1, and the actual boundary of the boundary discipline

I wrote the "AND compresses, OR does not" reading above before reading Drucker. **It is wrong and I
am leaving it visible with this correction attached rather than editing it away.**

`~/paperbin/cc-drucker-new-limits-instance-compression-eccc-tr12-112.pdf` (ECCC TR12-112, FOCS'12)

> **Theorem 1.1.** Let L be any NP-complete language. Suppose there is a deterministic polynomial-
> time reduction R that takes an arbitrarily long list of input strings (x₁, …, x_t) and outputs a
> string z, with z ∈ L′ ⟺ ⋀_{j∈[t]} [x_j ∈ L]. Suppose further that R obeys the output-size bound
> |z| ≤ max_{j≤t} |x_j|^{O(1)}, with the polynomial bound independent of t. Then, NP ⊆ coNP/poly.

So **AND-compression is infeasible too** — Drucker closed the AND-distillation conjecture of
Bodlaender–Downey–Fellows–Hermelin. And Drucker also kills the *randomized* version:

> **Theorem 1.3 (Informal).** … Suppose there is a compression scheme compressing an AND of t(n)
> length-n SAT instances into an instance z of a second decision problem L′, where |z| ≤ C·t(n)
> log t(n) … If the scheme's error probability on such inputs is bounded by a sufficiently small
> inverse-polynomial in n …, then there are non-uniform, statistical zero-knowledge proofs for all
> languages in NP. The corresponding result also holds for OR-compression.

**So the real dividing line is not AND vs OR. It is NON-INTERACTIVE vs INTERACTIVE.**

That is the corrected, and I think genuinely load-bearing, lesson for Selvage:

- A **kernel / compression / succinct PCP** is a *non-interactive digest of the instance*. For
  NP-hard shapes this is provably barren, deterministically (FS, Drucker) and probabilistically
  (Drucker Thm 1.3).
- An **IP / IPP / sumcheck boundary** is interactive with soundness error, and escapes all of it —
  IP = PSPACE, GKR, RVW. The escape is *interaction plus error*, not cleverness in statement choice.

**Engineering rule that falls out:** any Selvage proposal of the form *"shrink/preprocess the
statement before proving it"* — witness kernelization, instance sparsification, a smaller equivalent
constraint system produced by a deterministic pass — is a kernelization, and the literature prices
it at the trivial bound. Boundary statements must be **redeemed interactively, never precomputed.**

---

## FIND 2 — Dell & van Melkebeek, *Satisfiability Allows No Nontrivial Sparsification Unless The Polynomial-Time Hierarchy Collapses* (STOC'10 / JACM'14)

`~/paperbin/cc-dell-vanmelkebeek-satisfiability-allows-no-nontrivial-sparsification-eccc-tr10-038.pdf`

**This is the single highest-value find for "is there a lower bound saying the boundary cannot be
compressed below X" — because it gives a concrete X with a concrete exponent, and its cost model is
almost exactly ours.**

### The cost model, quoted — note whose bits count

> **Definition 1 (Oracle Communication Protocol).** An oracle communication protocol for a language
> L is a communication protocol between two players. The first player is given the input x and has
> to run in time polynomial in the length of the input; the second player is computationally
> unbounded but is not given any part of x. At the end of the protocol the first player should be
> able to decide whether x ∈ L. **The cost of the protocol is the number of bits of communication
> from the first player to the second player.**
>
> We often refer to the second player as the oracle. Note that the bits sent by the oracle do not
> contribute towards the cost. **By default the players in an oracle communication protocol are
> deterministic**, but one can consider variants in which one or both players are randomized,
> nondeterministic, etc.

That is: bounded verifier, unbounded prover who *has not seen the input*, and the metered resource
is **verifier → prover** bits. Prover→verifier is free. This is a formalization of "how small can
the statement I hand the prover be", i.e. of *boundary size*, and it predates our framing by 16 years.

### The bounds, quoted

> **Theorem 1.** Let d ≥ 3 be an integer and ǫ a positive real. If coNP ⊄ NP/poly, there is no
> protocol of cost O(n^{d−ǫ}) to decide whether an n-variable d-CNF formula is satisfiable, even
> when the first player is conondeterministic.

> **Theorem 2.** Let d ≥ 2 be an integer and ǫ a positive real. If coNP ⊄ NP/poly, there is no
> protocol of cost O(n^{d−ǫ}) to decide whether a d-uniform hypergraph on n vertices has a vertex
> cover of at most k vertices, even when the first player is conondeterministic.

> **Corollary 1.** Let d ≥ 3 be an integer. If coNP ⊄ NP/poly, then there is no polynomial-time
> reduction from d-Sat to any problem that makes at most O(n^b) queries and only queries strings of
> bitlength O(n^c), where b and c are any nonnegative reals with **b + c < d**.

> **Corollary 2.** Let d ≥ 3 be an integer and ǫ a positive real. If coNP ⊄ NP/poly, then d-Sat does
> not have probabilistically checkable proofs of bitlength O(n^{d−ǫ}) where n denotes the number of
> variables of the input formula.

Corollary 1's `b + c < d` is the shape to internalise: **queries × query-size is conserved.** You may
trade number-of-queries against size-of-each-query, but the *product exponent* cannot go below d.
That is a genuine conservation law for boundary statements, with a proof.

### Where the escape is — stated by the authors, not inferred

Their own conclusion section:

> Another direction regards the extension to the randomized setting with false negatives, and with
> false positives as well as false negatives; **we know how to handle false positives only.**

So Theorem 1 is a bound on *deterministic / co-nondeterministic* protocols. INFERENCE (mine): this
is why sumcheck-based delegation does not contradict it — a public-coin IP with two-sided-ish
soundness error is precisely the case they could not handle, and IP = PSPACE says that case has
polylog verifier→prover communication for SAT. The exponent conservation law `b + c ≥ d` is a law
about *certainty*, and randomness is what buys the exemption. Drucker (FIND 1b) later closed the
randomized case for the *superpolynomial* regime but not for these fine-grained exponents — I did
not find a fine-grained randomized version, and I am flagging that as **not searched to exhaustion**
rather than as an absence.

**Contradicts us?** Not the interactive discipline. It flatly contradicts any plan to get a cheap
boundary by a *non-interactive* route, and it prices exactly how expensive that route is.

**Distance to usable:** immediately usable as a design filter. Formalizing it in Lean is not the
point; it is a reason to refuse a class of designs.

---

## FIND 3 — Rothblum, Vadhan & Wigderson, *Interactive Proofs of Proximity: Delegating Computation in Sublinear Time* (STOC'13)

`~/paperbin/cc-rothblum-vadhan-wigderson-interactive-proofs-of-proximity-stoc2013.pdf`

**Answer to the brief's question "does the IPP literature already have our commit-then-audit theorem
in a stronger form?" — yes, and with matching lower bounds.**

### The positive result

> **Theorem 1.1 (Depth(n^γ) ⊆ IPP).** For every language L computable by log-space uniform circuits
> of depth D = D(n), size S = S(n) and fan-in 2, and every distance ε = ε(n), there exists an
> Interactive Proof of ε-Proximity for L. The proof has perfect completeness and soundness error
> 1/2. For an input of length n, the query complexity is (1/ε)^{1+o(1)}, the communication complexity
> is (ε·n·(1/ε)^{o(1)}·poly(D)), and the number of rounds is O(log n + D·log S).

Read the two costs together: query ≈ 1/ε, communication ≈ ε·n. **Their product is ≈ n, independent
of ε.** That is the commit-then-audit tradeoff curve as a theorem: sampling harder buys you a
proportionally smaller proof and nothing more.

### The boundary-statement theorem — this is our organizing sentence, proved

> **Theorem 1.3 (Informal; AffineMem is "complete").** For every distance bound ε = ε(n), and every
> language L computable by log-space uniform boolean circuits of depth D = D(n), size S = S(n), and
> fan-in 2, for t = t(n) = O(ε·n·log n) and a finite field F, there exists an interactive protocol …
> On input x, the output is (an implicit description of) a matrix A ∈ F^{t×n} and an (explicit)
> vector v ∈ F^t …

i.e. **every low-depth computation's boundary is a sparse affine system on the input**, of height
t = O(ε·n·log n). "The interior is the circuit; the boundary is A·x = v." That is our sentence, with
a completeness theorem attached, from 2013. We should be citing this as the ancestor of our framing.

The residual object is `PVAL(J, v)` — "does the low-degree extension of my input take the claimed
values v on the coordinate set J" — and:

> **Theorem 1.4 (Informal; IPP for PVAL).** … perfect completeness, soundness 1/2, query complexity
> (1/ε)^{1+o(1)}, and O(log(1/ε)) rounds. The communication complexity is ε·n·(1/ε)^{o(1)}, and the
> verifier runtime is ((1/ε) + ε·n)^{1+o(1)}.

### The lower bounds — the part we most need

> **Theorem 4.5.** There is a language L in logspace-uniform NC that has no AM-IPP proof of
> (1/8)-proximity in which the prover's message has length o(√n / log n) and the verifier's query
> complexity is o(√n / log n). Moreover, for every length n, L ∩ {0,1}ⁿ is an F₂ subspace of {0,1}ⁿ
> for which a basis can be constructed in logspace-uniform NC.

> **Theorem 4.9.** There is a language L in logspace-uniform NC such that in any interactive proof of
> (1/8)-proximity for L with prover-to-verifier communication c(n) ≥ log n, verifier query complexity
> q(n), and r(n) verifier messages …, we have
> r(n)^{O(r(n))} · (c(n) + q(n)) · (c(n) log c(n))^{r(n)} = Ω(√n / log n).
> **In particular, if r(n) = O(1), we cannot have c(n) and q(n) both be n^{o(1)}.**

Note the language witnessing the bound is **an F₂ linear subspace with an NC-constructible basis** —
about as structured and benign as a relation gets. So this is not a pathological-language artifact:
*linear algebra over F₂ already hits the wall.*

**What it touches:** directly, our "verify a random subset with a priced refusal". It says the price
is real and quantified, and — crucially for us — that **rounds are the currency that buys you past
√n.** Constant-round commit-then-audit cannot have both a small proof and a small sample. Every
round of accumulation depth we are willing to machine-check is buying an exponent here.

**Contradicts us?** It contradicts an *unqualified* hope for constant-round sublinear-everything
commit-then-audit. It does not contradict the discipline.

**Distance to usable:** Theorem 1.3 (AffineMem completeness) is a statement we could plausibly aim a
Lean formalization at; it is the cleanest available formal content for "boundary of a computation".
The lower bounds are usable today as sizing guidance.

---

## FIND 4 — Chakrabarti, Cormode, McGregor, Thaler & Venkatasubramanian, *On Interactivity in Arthur-Merlin Communication and Stream Computation* (ECCC TR13-180; ToC / ITCS)

`~/paperbin/cc-chakrabarti-cormode-mcgregor-thaler-venkat-interactivity-arthur-merlin-communication-stream-eccc-tr13-180.pdf`
Companion: `~/paperbin/cc-chakrabarti-cormode-mcgregor-robust-lower-bounds-communication-stream-computation.pdf`,
`~/paperbin/cc-chakrabarti-cormode-mcgregor-annotations-in-data-streams.pdf`,
`~/paperbin/cc-cormode-thaler-yi-streaming-graph-computations-annotations.pdf`

**This is the tight theory of verifier-side space the brief asked for. It exists, it is complete for
low round counts, and it has three lessons we do not currently have.**

### (a) The space × communication product is the conserved quantity

> **Theorem 2.3.** There is an annotated data stream algorithm for TRIANGLES with space and help
> costs O(n log n). **Every such algorithm requires the product of the space and help costs to be
> Ω(n²).**

and their own note on the general phenomenon:

> …prior work on annotated data streams …, which typically achieved any combination of space and
> help costs subject to **the product of these two costs being above some threshold.**

So: verifier space × proof length is the invariant. This is the same shape as Dell–van Melkebeek's
`b + c ≥ d` and as RVW's `query × communication ≈ n`. **Three independent literatures agree that the
boundary cost is a product, not a sum.** INFERENCE (mine, and I think it is the sweep's main
structural takeaway): *the right cost model for Selvage's statement-choice discipline is a product
(or an exponent sum), and a design that improves one factor while worsening the other by the same
ratio has bought nothing — it has moved along a level set of a proved invariant.* We should be able
to say, of any proposed boundary statement, which level set it sits on.

### (b) The verifier's message must depend on the input — an exponential separation

> **Theorem 2.1.** The data stream problem INDEX has a two-round SIP with cost O(log n log log n) …
> We stress that this is a very unexpected result! Previous work gave a one-round SIP with cost
> Õ(n^{1/2}) and a (2k−1)-round SIP with cost Õ(n^{1/(k+1)}). … we can pinpoint the essential
> feature that makes our protocol exponentially better than previous constant-round ones: **the
> verifier's messages to the prover must depend on some part of the input.**

This is a sharp warning for our Fiat–Shamir / round-by-round work. There is an exponential gap
between a verifier whose challenges are input-independent and one whose challenges depend on the
input. Any transformation that makes the verifier's messages *derivable from the transcript alone*
is standing on the wrong side of a proved exponential separation in this model.

### (c) A methodological find, and this one is on-brand for our repo

> However, their [Klauck–Prakash] lower bound made an implicit assumption about the model: in our
> terminology, they only showed that OMA^{[2k−1]}(INDEX) = Ω(n^{1/(k+1)}) for each constant k.

A published tightness result stood for years, and it was wrong-in-scope because of an **unstated
model assumption**, invisible until someone separated OMA from OIP and named the difference. A lower
bound is a claim about a model, and the model detail that voids it can be one nobody wrote down.

### (d) The round hierarchy collapses at four

> **Corollary 4.5.** For all f, Ω(R^{[2,B]}(f)^{1/2}) ≤ OIP^{[2]}(f) ≤ O(R^{[2,B]}(f)²). Thus,
> OIP^{[2]} = R^{[2,B]}.
> **Corollary 4.9.** For all f, Ω(MA^{[2,B]}(f)^{1/2}) ≤ OIP^{[3]}(f) ≤ O(MA^{[2,B]}(f)²).
> **Theorem 4.10.** For all f, we have OIP^{[4]}(f) = O(AM(f) log AM(f)). In particular, OIP^{[4]} ⊇ AM.
> …all constant-height levels of the OIP hierarchy collapse to the fourth level.

**Rounds 2, 3, 4 each buy a strictly characterised jump, and then it stops.** If our accumulation
depth is being chosen for soundness-composition reasons, this says the *expressive* return on rounds
in this model saturates at 4 — beyond that, extra rounds must be justified by something other than
what the statement can express.

**Distance to usable:** the product invariant is usable now. The OIP hierarchy is a vocabulary we
should adopt when we describe what a round buys.

---

## FIND 5 — Goldwasser, Kalai & Rothblum, *Delegating Computation: Interactive Proofs for Muggles* (STOC'08)

`~/paperbin/cc-goldwasser-kalai-rothblum-delegating-computation-interactive-proofs-for-muggles-stoc2008.pdf`

The brief asked what the original framing says that the modern sumcheck retelling drops. **Three
things, and the third one is a live cost we may be paying for nothing.**

### (a) The forgotten theorem: a log-space verifier for all of P

> **Theorem 3.** Let L be a language in P … Then, L has a public-coin interactive proof with perfect
> completeness and soundness 1/2, where: The prover runs in time poly(n); **the verifier runs in
> time poly(n) and space O(log(n))**; the communication complexity of the protocol is poly(n).

Everyone quotes Theorem 1 / Corollary 1 (polylog communication for L-uniform NC). Almost nobody
quotes Theorem 3. It is the *space*-bounded-verifier result — the thing the brief says we should be
trading — and it covers **all of P**, not just NC, at the cost of giving up succinct communication.
It also resolved the Condon / Fortnow–Sipser / Fortnow–Lund question about public-coin log-space
verifiers, which the modern retelling has entirely dropped.

### (b) The off-line/on-line split is an *information-theoretic* result, not a cryptographic one

> **Theorem 4.** … There exists an on-line/off-line interactive proof … The verifier runs in two
> phases: (1) an off-line phase before the input x is specified, where the verifier runs in time
> poly(S); (2) an on-line phase which is carried out after the input x is specified, where the
> verifier runs in time n·poly(d, log(S)).

Modern write-ups attribute "preprocessing" to the polynomial commitment scheme / a VK. GKR had it
in 2008 with no cryptography at all, purely as a way to handle *non-uniform* circuits.

### (c) The point that matters most to us: log-space uniformity replaces preprocessing

> A natural question is how this can be done when the verifier cannot even take the circuit in
> question as an additional input (it has no time to read it!). **This is where the condition on the
> log-space uniformity of the circuit family comes in. For such circuit families, the circuit has a
> "short" implicit representation which the verifier can use without ever constructing the entire
> circuit.**

INFERENCE (mine, and I think this is the most actionable thing in the sweep after FIND 2): the
preprocessing/VK apparatus exists to hand the verifier a description of a circuit it cannot read.
GKR's theorem says that for **log-space-uniform** circuit families no such object is needed — the
wiring predicate is *computed*, not *committed*. And Selvage's workloads are exactly the uniform
case: a matmul's wiring predicate is arithmetic on indices; an FHE NTT/keyswitch is index arithmetic;
a kernel state transition is a fixed loop. **We may be carrying a VK/preprocessing epoch — and all
the rotation, registry and re-genesis machinery hanging off it — for a class of circuits whose
wiring the verifier could just evaluate.** Worth a measurement: for each Selvage relation, is the
wiring predicate log-space computable? If yes, the preprocessing is a choice, not a necessity.

**Distance to usable:** (c) is a design question we can answer this week by inspection. (a) is a
statement worth re-deriving for our setting if verifier space ever becomes a binding constraint.

---

## FIND 6 — Gur & Rothblum, *A Hierarchy Theorem for Interactive Proofs of Proximity* (ITCS'17)

`~/paperbin/cc-gur-rothblum-hierarchy-theorem-interactive-proofs-of-proximity-itcs2017.pdf`

**Rounds are a strictly-priced resource, and black-box round reduction is near-optimally bad.**
This is the piece that touches "accumulation depth" hardest.

> **Theorem 1 (Hierarchy theorem, informally stated).** There exists an explicit language L such
> that for every constant r ≥ 1 and for inputs of length n:
> 1. There is an O(r²)-round IPP for L in which the verifier runs in time t = n^{O(1/r)}; and
> 2. The verifier in any r-round IPP for L must run in time at least t′ = t^{100} (where the
>    constant 100 is arbitrary). **Furthermore, either the communication complexity or query
>    complexity of the verifier must be at least t′.**

> **Theorem 2 (Constant Round versus General IPPs).** There exists a language L that has a
> polylog(n)-round IPP with a polylog(n) time verifier and an ω(1)-round IPP with n^{o(1)} time
> verifier, but for every constant r ≥ 1, the verifier in any r-round IPP for L must run in time at
> least n^{Ω(1/r)}.

And the composition consequence:

> Using our hierarchy theorem, we show that **the overhead incurred by the round reduction
> transformation of [Babai–Moran] is close to optimal among all black-box transformations.**

Plus a barrier result that is worth knowing before anyone in our orbit tries to prove something in
this neighbourhood:

> …any proof of the complexity class inclusion #P ⊆ AM … must make use of non-algebrizing
> techniques.

(Algebrization background: `~/paperbin/cc-aaronson-wigderson-algebrization-barrier-relativization.pdf`.)

**What it touches:** round-by-round soundness → Fiat–Shamir → accumulation depth. The message is
that *squashing rounds is not a free refactor*: the r → O(r²) gap is real for an explicit language,
and any black-box squashing (which is what a generic accumulation/folding wrapper is) pays close to
the Babai–Moran overhead. If we squash rounds we should be doing it non-black-box, exploiting the
specific relation — and we should say so.

**Contradicts us?** Not directly, but it prices something we may have been treating as free.

---

## FIND 7 — MA communication complexity is *exactly* the commit-then-audit model, and it has tight bounds

`~/paperbin/cc-klauck-arthur-merlin-games-in-communication-complexity.pdf` (CCC'11)

The Aaronson–Wigderson MA protocol for set disjointness *is* commit-then-audit: Merlin names a block
of size √n, Arthur samples inside it. The matching lower bounds say the shape is optimal:

- `MA(DISJ) = Θ(√n)` — AW upper bound O(√n log n); lower bound Ω(√n) via Razborov's Θ(n) correlation
  bound for DISJ (Klauck's framework: `Ω(AM(f)) ≤ Corr(f) ≤ O(MA(f)²)`).
- And the one that lands nearest our organizing sentence, quoted from Klauck:

> **Corollary 1** QMA(IP₂) ≥ Ω(√n).
> Note that this lower bound is tight within a log factor due to the MA-protocol of Aaronson and
> Wigderson [AW09].

**IP₂ is a bilinear form.** Our sentence says "the interior of a bilinear form is n³, its boundary
n²". In the *two-party commit-then-audit* model, the boundary of a single length-n inner product is
Θ(√n) — not O(log n). Whatever the right accounting is, there is a proved √-shaped floor on the
one-message-prover-plus-sampling boundary of a bilinear form, and it is not zero.

**Distance to usable:** this is the cleanest existing formal answer to "how cheap can a commit-then-
audit statement get". It should be the reference point we size our audit against.

---

## FIND 8 — Amir, Goldreich & Rothblum, *Doubly Sub-Linear Interactive Proofs of Proximity* (ITCS'25)

`~/paperbin/cc-amir-goldreich-rothblum-doubly-sublinear-interactive-proofs-of-proximity-itcs2025.pdf`
(full version ECCC TR24-143)

A design point we have, as far as I can tell, never considered: **an honest prover that cannot read
the whole input.**

> We initiate a study of doubly-efficient interactive proofs of proximity … 1. The query-complexity
> of verification is significantly smaller than the query-complexity of testing. 2. **The
> query-complexity of the honest prover strategy is not much larger than the query-complexity of
> testing.** We call such proof systems doubly-sublinear IPPs (dsIPPs).
>
> A salient feature of (almost all) the IPPs that we present is that **the honest prover does not
> employ an optimal strategy, because it cannot afford to read the entire input** … while an optimal
> prover strategy for the verifiers that we present achieves perfect completeness, **our honest
> provers don't.**

**What it touches:** our prover-side costs on ML and FHE workloads, where the "input" is a weight
tensor or a ciphertext bank that dwarfs the computation we actually care about. The trade offered
here is *give up perfect completeness in exchange for a prover that reads sublinearly.* That is a
knob we do not currently have on the board.

**Contradicts us?** No — it adds an axis. But note it violates a habit: we treat perfect completeness
as free and non-negotiable. Here it is the currency.

---

## FIND 9 — Raz, *A Counterexample to Strong Parallel Repetition* (FOCS'08 / SICOMP)

`~/paperbin/cc-raz-counterexample-to-strong-parallel-repetition.pdf`

The negative composition result the brief asked for — and it arrives wearing our own metaphor.

> We consider the odd cycle game of size m; a two-prover game with value 1 − 1/2m. We show that the
> value of the odd cycle game repeated in parallel n times is at least 1 − (1/m)·O(√n). This implies
> that for large enough n (say, n ≥ Ω(m²)), the value of the odd cycle game repeated in parallel n
> times is at least **(1 − 1/4m²)^{O(n)}**.
>
> Since the odd cycle game is a projection game, a unique game, and a XOR game, this answers
> negatively all versions of the strong parallel repetition problem.

So error decays as `(1 − ε²)^n`, **not** `(1 − ε)^n`. Repetition is *quadratically worse* than the
naive product accounting, and the counterexample is a projection/unique/XOR game — a very tame,
very structured shape, not a pathology. Earlier, Feige–Verbitsky gave games where Θ(log s / log log s)
repetitions are needed before the value drops at all.

**What it touches:** anywhere we amplify soundness by repetition and write `ε^k` in a Lean statement.
For a single-prover public-coin IP, parallel repetition does behave (Goldreich); for anything with a
*game* shape — two independent provers, or a protocol whose soundness analysis factors through a
two-party game — the naive exponent is provably wrong. Worth a grep of our soundness bookkeeping for
places we assume a clean product.

**And the delightful part, which I did not expect to find in a complexity sweep:** Raz's
counterexample is powered by the *foam problem* —

> Their main result is the existence of a body with volume 1 and surface area O(√n) that tiles Rⁿ by
> Zⁿ … In other words, this body tiles Rⁿ as a cube but its surface area is similar to the surface
> area of a [sphere].

A unit-volume body tiling Rⁿ whose **surface area is O(√n) rather than the cube's 2n**. That is
literally "the boundary of a fixed interior can be quadratically smaller than the obvious one", it is
a theorem, and it is the mechanism by which parallel repetition fails to amplify. INFERENCE (mine):
this is the closest thing in the literature to a *geometric* formalisation of our organizing
sentence, and the direction of the surprise is *in our favour* — small boundaries for a fixed
interior exist and are non-obvious — while the *consequence* is against us, because it is exactly
what lets a cheating prover survive repetition. Both halves are worth carrying.

---

## FIND 10 — Gur & Rothblum, *Non-Interactive Proofs of Proximity* (ECCC TR13-078 / ITCS'15) — the MAP layer

`~/paperbin/cc-gur-rothblum-non-interactive-proofs-of-proximity-eccc-tr13-078.pdf`

MAPs = IPPs where the interaction is a single prover→verifier message. This is *precisely* our
commit-then-audit shape with no interaction, and the paper is the systematic study of what one
message buys.

> **Theorem 3.1.** For every constant α > 0, there exists a property Π_α that has an MAP that uses a
> proof of length O(log n) and makes poly(1/ε) queries for every ε > 1/polylog(n), but for which
> **every property tester must make Ω(n^{1−α}) queries.** Furthermore, the MAP has one-sided error.

and the converse-direction limit (their Theorem 2, restated in the text):

> …must make Ω̃(n^{0.999}/p) queries [for a proof of length p]. (In particular, every property tester
> for Π must make Ω̃(n^{0.99}) queries.)

`queries × proof-length ≈ n` again — the **fourth** independent appearance of the product invariant
in this sweep (Dell–van Melkebeek's `b+c ≥ d`, RVW's `q·c ≈ n`, CCMTV's `space × help = Ω(n²)`, and
now MAPs). They also prove MAPs are strictly weaker than 3-message IPPs *at the same communication*:

> …even 3-message IPPs may have exponentially better query complexity than MAPs (while using the
> same amount of communication).

**What it touches:** if Selvage's audit is one-shot (commit, then sample, no further interaction), we
are in MAP-land, and the literature says three messages can be exponentially better at identical
communication. The second and third message are the cheapest thing on the menu.

---

## Also downloaded, lower priority but real

- `~/paperbin/cc-dinur-pcp-theorem-by-gap-amplification.pdf` — Dinur's combinatorial PCP theorem.
  The gap-amplification/composition alternation is the canonical example of "iterate a cheap
  transformation and pay a bounded price per step", which is structurally what accumulation is.
- `~/paperbin/cc-aaronson-wigderson-algebrization-barrier-relativization.pdf` — the barrier. Relevant
  because *sumcheck/arithmetization is the technique that algebrizes*, so anything we hope to prove
  by arithmetization alone is inside the barrier. Their Theorems 3.6–3.8 (P^#P ⊆ IP^A, and the
  NEXP/BFLS step) are the algebrized versions of the classics.
- `~/paperbin/cc-bodlaender-jansen-kratsch-cross-composition-kernelization-lower-bounds.pdf` — the
  *usable recipe* for FIND 1/1b: to prove a relation has no small non-interactive boundary, exhibit
  an OR- or AND-cross-composition into it. Definition 9 + Theorem 4 are the template.
- `~/paperbin/cc-goldreich-digest-of-rothblum-vadhan-wigderson-2013-eccc-tr26-088.pdf` — Goldreich's
  **2026** re-exposition of RVW. Freshest, cleanest entry point to FIND 3; read this before the
  original if formalizing.
- `~/paperbin/cc-chakrabarti-cormode-mcgregor-annotations-in-data-streams.pdf`,
  `~/paperbin/cc-cormode-thaler-yi-streaming-graph-computations-annotations.pdf` — the annotated-
  stream line feeding FIND 4.
- `~/paperbin/cc-bronfman-rothblum-pcps-instance-compression-cryptographic-lens-itcs2022.pdf` —
  ITCS'22 revisit of FS through a cryptographic lens; the modern bridge between FIND 1 and our world.
- `~/paperbin/cc-holmgren-round-by-round-soundness-equals-state-restoration-2019-1261` **failed to
  download** (eprint returned HTML); the result is that round-by-round soundness and BCS
  state-restoration soundness are *equivalent* for public-coin IPs, and **neither is implied by
  random-oracle security of Fiat–Shamir**. We likely already have this; noting it because it is the
  complexity-side framing of our composition work.

---

## What I looked for and did NOT find — corpus and instrument named

- **A lower bound stating that the boundary of a *bilinear form / matmul* specifically cannot be
  compressed below n².** Instrument: Google/WebSearch on rigidity + log-rank + communication
  complexity of matrix product; ECCC search. Found only the *generic* product invariants (FIND 2, 3,
  4, 7, 10) and the rigidity programme, which targets **circuit** lower bounds via Razborov's
  PH^cc connection, not proof size. **Weak evidence of absence** — I did not exhaust ECCC full text.
  Nearest hit is Klauck's `QMA(IP₂) ≥ Ω(√n)` (FIND 7), which is about a single inner product in the
  two-party model, not about the n×n product.
- **A fine-grained (exponent-level) randomized version of Dell–van Melkebeek.** Their own 2010
  conclusion says the randomized-with-false-negatives extension was open ("we know how to handle
  false positives only"); Drucker closed the *superpolynomial* randomized case but with a different
  conclusion (NP ⊆ non-uniform SZK). I did not confirm current status. **Explicitly not searched to
  exhaustion.**
- **A negative result specifically about composing round-by-round-sound protocols.** Searched;
  the literature I surfaced is the *positive* equivalence (Holmgren: RBR ⟺ state-restoration) and the
  round-*hierarchy* negatives (FIND 6). If a genuine anti-composition theorem for RBR soundness
  exists I did not find it, and that is a weak absence claim: instrument was WebSearch, not ECCC
  full-text or DBLP author sweeps of Chiesa/Spooner/Holmgren.

## The one structural claim this sweep supports

Four literatures that do not cite each other — parameterized complexity (Dell–van Melkebeek),
sublinear-time proofs (RVW, Gur–Rothblum), streaming/annotation (CCMTV), and communication complexity
(Klauck/AW) — **independently converge on the same shape: the cost of a boundary statement is a
PRODUCT, and the product is conserved.** `queries × query-size`, `query × communication`,
`space × help`, `proof-length × queries`. Whatever discipline Selvage writes down should have a
product (or exponent-sum) as its cost functional, and every candidate boundary statement should be
placed on a level set of it. A design that halves one factor and doubles the other has moved along a
proved invariant and bought nothing.

### Tooling note

`~/paperbin/cc-goos-kamath-pitassi-watson-query-to-communication-lifting-for-pnp-eccc-tr17-024.pdf`
— **query-to-communication lifting.** This is the modern machine for manufacturing communication
lower bounds: prove a lower bound in the (easy) decision-tree/query world, compose with a gadget,
and the bound *lifts* to communication. If we ever want to prove "*this particular* Selvage relation
has no boundary smaller than X", lifting is the technique that would do it, and it is the reason a
bound like FIND 2's is provable at all. Filed as method, not as a result about us.
