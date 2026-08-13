# Boundary statements: prior art, theorem, compiler

2026-08-13. Speculative lane. **Written incrementally; every inference is marked.**

- **[MEASURED]** — a number I computed from an artifact in this repo, script named.
- **[READ]** — I read it at the cited location, in a file I can point at.
- **[2ND-HAND]** — a search lane read it; I did not verify at source.
- **[MINE]** — my inference. Not checked by anyone. A conjecture.
- **[ASSUMED]** — inherited from the brief, not verified by me.

The claim under examination (`docs/SELVAGE.md` §2, `notes/prover-floor.md`):

> **An AIR commits the INTERIOR of a relation; a sumcheck commits its BOUNDARY.**

---

## 0. The verdict

**The principle is correct, standard, named, and there is a 2025 survey by Justin
Thaler whose entire thesis it is — and that survey is sitting in `~/paperbin`,
twice, under two filenames.**

1. **The community name is `virtual polynomial` / `polynomial virtualization`.**
   Thaler, *"Sum-check Is All You Need: An Opinionated Survey on Fast Provers in
   SNARK Design"*, eprint **2025/2041**, §5.2 *"Reducing commitment costs via
   virtual polynomials"*. Terminology from HyperPlonk [CBBZ23] and Diamond–Posen
   [DP23]; the idea from GKR08. [READ, verified in our copy]
2. **The upper-bound half of our observation is a published theorem, and it is
   twelve years old.** Thaler, *Time-Optimal Interactive Proofs for Circuit
   Evaluation*, CRYPTO 2013, **Theorem 3**: matmul in `n² + O(log n)` field
   elements of communication with prover time `T(n) + O(n²)` for **any**
   unverifiable matmul algorithm T. [READ, verified in our copy]
3. ⚑ **The lower-bound half does not exist.** Nobody has proved that any relation
   *requires* committing more than its statement, and nobody has framed the
   question. **That gap is the only place novelty could live**, and the door is
   being opened right now (Bhadauria–Block–Ghosh–Thaler, TCC 2025). [2ND-HAND]
4. ⚑ **The naive reading of our sentence is refuted by the same survey.** Thaler:
   *"commit to as little data as possible. **Not zero—there's a sweet spot.**"*
   Advice you commit buys a cheaper checking procedure; a pure-boundary statement
   can be the **slower** one. [READ, verified in our copy]
5. **What is ours is the PRICE.** Under this repo's measured constants one
   committed base felt is worth **≈3,120 field multiplications at lb=4, ≈12,331 at
   lb=6**, against **≈40** to virtualize one. A **78×–308×** exchange rate, which
   converts the principle into a threshold rule. [MEASURED]
6. ⚠ **Retire the word "boundary."** It collides with *border rank* (the Zariski
   boundary of a secant variety) in exactly the community — algebraic complexity —
   that would otherwise read our matmul claim. Say **virtual / materialize**, which
   is what the field already says.
7. **On the compiler: it exists in three halves, in three fields with no citation
   path between them** — the derivation engine (Rajopadhye's polyhedral reduction
   simplification **automatically derives the O(N²) ABFT checksum from the O(N³)
   matmul spec**), the cost-model search (ZKML, EuroSys 2024, which **already ships
   the Freivalds move** and disclaims all formal correctness), and the
   machine-checked emission (Clean/ArkLib, which have no search and no cost model).
   ⚑ **And the obvious joining technology is the wrong one: e-graphs preserve
   functional equality, and Freivalds is not an equality — it is a
   soundness-preserving reduction.** That is the unclaimed object. §3.

---

## 1. Prior art

### 1.1 The corpus and the instrument, named first

- **Corpus**: `~/paperbin`, 1,528 files / 1,218 PDFs / 1.4 GB, plus 463
  pre-existing `.txt` extracts.
- **Instrument**: I ran `pdftotext` over **all 1,218 PDFs**, so the grep was
  **full text**, not first-2-pages. That closes instrument-blindness (mechanism
  #2, `notes/the-absence-problem.md`). ⚑ **This should be a standing artifact,
  not a per-lane rebuild** — it took ~2 min and it is the single fix for four
  absence-claim failures in a week. Rebuild:
  ```sh
  cd ~/paperbin && mkdir -p ~/paperbin-txt
  ls *.pdf */*.pdf | while read f; do
    o=~/paperbin-txt/$(echo "$f" | tr / _ | sed 's/\.pdf$/.txt/')
    [ -s "$o" ] || pdftotext -q "$f" "$o"
  done
  ```
- **Non-eprint venues**: ECCC, FOCS/STOC/ITCS/CCC (the `cc-*` shelf in paperbin),
  Thaler's book, plus three web lanes.

⚑ **Mechanism #3 fired, and harder than before.** *Every* decisive citation was
already in `~/paperbin`, correctly named, when the observation was written up as
undeveloped. Worst case: **`sumcheck-is-all-you-need-thaler-survey-2025-2041.pdf`
and `thaler-sumcheck-survey-2025-2041.pdf` are the same paper, in our library,
twice** — the paper whose one-line thesis is our sentence. There is also a `cc-`
shelf of 17 complexity-theory papers (Fortnow–Santhanam, Dell–van Melkebeek,
Rothblum–Vadhan–Wigderson, Gur–Rothblum, Reingold–Rothblum–Rothblum, Drucker,
Klauck, and the whole Chakrabarti–Cormode–McGregor–Thaler annotated-streams line)
that answers §2 outright. **We have the library. We did not read it.**

### 1.2 ⚑ The name: virtual polynomials

Thaler 2025/2041 §5.2, in our copy
`~/paperbin/sumcheck-is-all-you-need-thaler-survey-2025-2041.pdf` (extract line 861): [READ]

> "**Reducing commitment costs via virtual polynomials.** The idea of a virtual
> polynomial is to avoid committing to a polynomial or vector `a` directly, instead
> committing to a smaller or simpler object `b` such that `a` can be expressed as a
> low-degree function of `b`. […] If each `aᵢ` is a low-degree function of `b`, then
> sum-check can still reason about `a` as if it were committed.
> The terminology is recent [CBBZ23, DP23], but the idea dates back at least to the
> original GKR protocol [GKR08]. There, the (multilinear extension of) the vector
> of gate values at each layer of a circuit is treated as a virtual polynomial.
> **The only polynomial that is actually explicitly committed by the prover is the
> input layer of the circuit.** […] The protocols in Jolt, Twist, and Shout also
> lean hard into this idea to minimize commitment costs for the prover."

**That is our sentence, with a name, a citation chain, and a list of systems that
already do it.** "Interior" = what gets *virtualized*; "boundary" = what stays
*committed*.

Same survey, abstract and §1: [READ]

> "The prover's work is dominated by two tasks: (i) committing to data and (ii)
> proving that the committed data is well-formed."
> "Hence the high-level lesson: **commit to as little data as possible.**"

### 1.3 ⚑ The refutation inside the agreement: not zero

Thaler 2025/2041 §1, same file (extract line 50), immediately after that lesson: [READ]

> "commit to as little data as possible. **Not zero—there's a sweet spot.** This is
> for two reasons. First, without any cryptography […] it's impossible (under
> standard complexity-theoretic conjectures) to achieve proofs shorter than the
> bare witness itself [GH98, GVW02]. Second […] **without committing to a fair
> amount of untrusted advice, checking procedures are (in general) expensive** when
> expressed in a format that SNARK machinery can handle efficiently. For example,
> for an operation like division […] it's easy to prove the claimed result q is
> correct if the prover also commits to a remainder R and shows that a = q·b + R."

⚑ **This is a direct refutation of the monotone reading of SELVAGE §2.** "Prove
boundaries, not interiors" as an unqualified maxim is **wrong**, and it is wrong in
the paper that otherwise agrees with us entirely. The two costs are in tension:
committing less means a *harder residual check*. There is an interior optimum, and
the whole engineering question is **where** it sits — which is §2.3.

That also names the umbrella term for the other direction: **untrusted advice.**
Committed data that is not the witness, added *deliberately*, to make the check
cheap. Our LogUp aux columns are untrusted advice. So are Cairo hints, Noir
`unconstrained`, and the `q,R` division trick.

### 1.4 ⚑ The theorem: Thaler CRYPTO 2013, Theorem 3

`~/paperbin/thaler2013-time-optimal-ip.pdf:1876`: [READ, verified at source]

> **Theorem 3.** There is a valid interactive proof protocol for n × n matrix
> multiplication over the field F_q with the following costs. The communication
> cost is **n² + O(log n)** field elements. The runtime of the prover is
> **T(n) + O(n²)** and the space usage is s(n) + o(n²), **where T(n) and s(n) are
> the time and space requirements of _any_ (unverifiable) algorithm for n × n
> matrix multiplication.**

and §3, same file, the mechanism: [READ]

> "In some cases, there is something to be gained by using **a higher-degree
> extension** of Vᵢ, and this is precisely what we exploit here. […] **P can
> evaluate this higher-degree extension at the necessary points without explicitly
> materializing all of the gate values of C**, which would not be possible if we
> had used the multilinear extension of the gate values of C. […] Since P does not
> have to evaluate C in full, this protocol is perhaps best viewed **outside the
> lens of circuit evaluation.**"

Three things to take from this, all load-bearing:

1. **The n³ is not intrinsic, and that is proved, not conjectured.** Our "interior
   is n³" is an artifact of committing *one algorithm's trace*.
2. **The protocol is ω-agnostic.** T(n) is *any* matmul algorithm; the prover may
   run Strassen. So the n³-vs-n² axis and the n^ω axis are genuinely orthogonal —
   worth saying, because they look related and are not.
3. ⚑ **The elision mechanism is a DEGREE RAISE.** Thaler virtualizes the gate
   values by using a *quadratic* extension instead of the multilinear one. **That
   is the same move test §5.2 proposes for the LogUp aux column**, which is why
   that test is the sharp one.

Applied restatement, Thaler's book §4.4.1 *"Preview: The Power of Interaction"*: [READ]

> "Interaction buys the verifier the ability to ensure that the prover correctly
> **materialized intermediate values** in a computation […] **without requiring the
> prover to explicitly materialize those values to the verifier.**"

And the design-lever claim, published four years ago — Thaler, a16z, *"Measuring
SNARK performance"* (2022): [2ND-HAND]

> "For a handful of highly structured problems such as **matrix multiplication,
> convolutions, and several graph problems**, known SNARKs exist that **avoid this
> frontend/backend paradigm and thereby achieve a vastly faster prover.**"

### 1.5 ⚑ The fork is drawn in the wrong place: AIR is not the villain

**CCS** (Setty–Thaler–Wahby, eprint 2023/552) gives *"essentially costless
reductions"* from Plonkish, AIR and R1CS to one generalization. [2ND-HAND — the
lane could not fetch the PDF; eprint rate-limited. **Verify before citing.**]

If that holds, then **R1CS / Plonkish / AIR are interconvertible and the encoding
choice within that family is not a cost lever at all.** The real fork is:

> **commit the interior  ·vs·  virtualize the interior**

i.e. **sumcheck-based or not**, which is a different cut than "AIR vs sumcheck".
Thaler's survey §8 states it as a three-level hierarchy: [2ND-HAND]

> "Slowest: no use of sum-check at all. Faster: uses sum-check, but fails to
> exploit structure in the computation, e.g., using generic circuits. Fastest:
> sum-check paired with awareness of repeated structure — batch-evaluation
> arguments, small-value preservation, sparse sums, virtual polynomials."

⇒ **SELVAGE §2's sentence should not name AIR.** An AIR that virtualizes is fine;
an R1CS that materializes is not. The property is *materialization*, not the
constraint-system family. [MINE]

### 1.6 ⚑ The three tiers our sentence collapses

Thaler's book §4.4.1 draws a distinction we lose, and it is the one that makes
`fold_add` special: [READ]

> "The advantage of the MATMULT protocol described in this section is two-fold.
> First, **it does not care how the prover finds the right answer.** In contrast,
> the GKR protocol demands that the prover compute the answer matrix C in a
> prescribed manner, namely by evaluating the circuit C gate-by-gate. […] In
> contrast, the GKR protocol introduces at least a constant factor overhead."

| tier | committed | prover field work | rounds |
|---|---|---|---|
| **materialize** (AIR/R1CS/Plonkish, no virtualization) | Θ(interior) | Θ(interior) | O(1) |
| **virtualize the circuit** (GKR) | Θ(statement) | Θ(interior), const-factor overhead | Θ(depth) |
| **virtualize the algorithm** (Thaler MATMULT; our `fold_add`) | Θ(statement) | *additive low-order* over the native algorithm | Θ(log n), or **0** |

**On committed count tiers 2 and 3 are identical — which is why our sentence
merges them.** Tier 3 is a strictly stronger property: *algorithm-independence*.
`fold_add` is tier 3, which is why it costs **zero rounds**, and that is the part
of our observation worth keeping sharp.

### 1.7 The names the same idea travels under

| our word | community | their word |
|---|---|---|
| elide the interior | **applied SNARKs** | **virtual polynomial / virtualization** (the canonical name) |
| interior | complexity theory | nondeterministic **verification complexity**; the **Cook–Levin** witness |
| boundary | complexity theory | **witness length** |
| "commit the boundary" | IOP theory | *"approaching the witness length"* / rate-1 IOPs |
| "commit the boundary" | applied SNARKs | *"commit only w̃, not the transcript W̃"* (Thaler Ch. 7/8) |
| deliberately committing interior | theory | **untrusted advice** |
| ditto | zkVM practice | **precompile / builtin / accelerator** |
| ditto | Plonkish | **custom gate** |
| ditto | Cairo | **nondeterministic programming** (√25 by asserting `r²=25`) |
| ditto | Noir | **`unconstrained` functions / Brillig / oracles** |
| elide a whole table | Lasso | *"if t is structured, **no party needs to commit to t**"* — **the lookup singularity** |
| the elision itself | IP theory | **the power of interaction** |
| choosing what to commit | ML compilers | **rematerialization / gradient checkpointing** (§3.3) |

⚠ **False friends, flagged so nobody reaches for them:**
- **border rank** — the Zariski boundary of a secant variety. Pure word collision
  with our "boundary", in the community most likely to read the matmul claim.
- **matrix rigidity** — a different axis entirely (entries changed to drop rank);
  targets circuit depth, not proof size.
- **n^ω** — multiplicative complexity, orthogonal (Thaler Thm 3 is ω-agnostic).
- **certificate complexity** — a genuine terminological collision: it means
  *input positions that pin down an answer* under a fixed 2-party split. A
  complexity reader will misparse our use of it. Do not.
- **"succinct PCP"** — a term of art for a *different axis* (§2.2). Using it will
  make a complexity reader think we are claiming what Fortnow–Santhanam refuted.

### 1.8 ⚑ Genuinely unclaimed: the vocabulary, and only the vocabulary

Nobody in proof systems uses interior/boundary or Stokes-theorem language for
this. [2ND-HAND, five query shapes]. **That is vocabulary, not a result**, and per
§1.7 it is *worse* vocabulary than the field's own. Recommend dropping it.

---

## 2. Can it be stated as a theorem?

### 2.1 ⚑ First, separate two axes the complexity community keeps apart

This is the correction that most changes how the note should be written. [READ, 2ND-HAND]

| | axis | quantity | literature | bears on us? |
|---|---|---|---|---|
| **B** | proof length vs **witness** size, where witness ≪ **instance** | "**succinct PCP**" | Fortnow–Santhanam; Dell–van Melkebeek; Drucker; kernelization | **NO** |
| **C** | committed size vs **computation time** (trace) | *no standard name* | Thaler Thm 3 (upper); **nothing** (lower) | **YES — this is ours** |

For matmul the witness *is* the instance (Θ(n²) either way); the n³ is the *time
of one algorithm*. So the entire Fortnow–Santhanam / Dell–van Melkebeek machinery
— which is the machinery that *looks* most relevant — **does not apply to us.**
Recording their statements anyway, because they will be reached for:

- **Fortnow–Santhanam** (STOC'08/JCSS'11), Cor. 4.4: *SAT does not have succinct
  PCPs unless NP ⊆ coNP/poly and PH collapses.* [READ by lane, verbatim]
- **Dell–van Melkebeek** (STOC'10/JACM'14), Thm 1: *if coNP ⊄ NP/poly, no oracle
  communication protocol of cost O(n^{d−ε}) decides n-variable d-CNF SAT.* The
  quantitative version, and the closest thing anywhere to "minimum size of an
  equivalent statement" — **but it bounds the STATEMENT, not the trace.** [READ by lane]
- ⚑ And the reason axis B is not a barrier for us anyway: **Kalai–Raz's Interactive
  PCP evades it.** Interaction buys exactly the succinctness FS rules out for
  static proof strings. **The barrier is against NON-INTERACTIVE proofs.** [2ND-HAND]

⚠ **Ron-Zewi–Rothblum straddles the two axes and I want to be precise about which
half I am using.** Their general phrasing — *"communication scales with the
**verification complexity** of R rather than the **witness length**"* — is **axis
C**, because verification complexity can exceed witness length for purely
*computational* reasons (matmul: witness 2n², verification n³). Their worked
example, 3-Colorability with witness Θ(|V|) and IOP length Θ(|E|), is **axis B**.
**I use the general statement, not the example.** ⓘ And matmul does satisfy their
side condition: checking `C = AB` with read-many access to the witness is poly-time
and low-space, so RZR Thm 2 applies and gives `(1+γ)·2n²` — consistent with Thaler
Thm 3's `n² + O(log n)`. [MINE — the applicability check; not stated by RZR]

### 2.2 The quantity, and the floor that is trivial

**Definition [MINE, standard-adjacent].** For relation R and a commit-and-prove
argument that commits `v ∈ F^m` and runs an IOP querying only `v`, call `m` the
**commitment cost**; let `μ(R)` be its minimum over sound arguments.

**Floor.** Knowledge soundness ⇒ an extractor recovers `w` from `v` plus an
`o(|w|)` transcript ⇒ `m·log|F| ≥ H(w)`. That is the `Ω(H(w))` leg already in
`prover-floor.md`. Its complexity-theoretic counterpart is
**Goldreich–Håstad / Goldreich–Vadhan–Wigderson** — *NP-complete languages cannot
have interactive proofs where the prover is much more "laconic" than the standard
NP proof* — which **Thaler's survey cites for exactly this purpose** in the
"not zero" passage (§1.3). [READ — the citation; GVW abstract 2ND-HAND]

⚠ **This floor is trivial and I want to be blunt that it is.** It says you must
commit the witness. It does not say anything is *hard*. It is the easy direction.

**Ceiling.** Ron-Zewi–Rothblum, *Local Proofs Approaching the Witness Length*
(eprint 2019/1062, FOCS'20 / JACM'24), Thm 2: for NP relations verifiable in
polynomial time and **bounded polynomial space** (`n^ξ`), an IOP of proof length
**(1+γ)·n**, n = witness length, constant rounds and queries. [READ, in paperbin]
Their §1.1.1 is our sentence in the theory's words:

> "essentially all short PCP constructions only yield constructions in which the
> communication scales with **the verification complexity of R, rather than with
> the length of the original NP witness**."

And their Remark 1.2 names the AIR: [READ]

> "**the Cook–Levin transformation incurs a polynomial blowup to the witness size
> (corresponding to the non-deterministic verification time of the relation)** […]
> the NP relation arising from the Cook–Levin theorem, **in which the witness
> includes, in addition to the satisfying assignment, the values of all of the
> gates in the circuit**."

> ⇒ **An execution trace IS a Cook–Levin witness.** So: *an AIR commits the
> Cook–Levin witness; a virtualizing sumcheck commits the original NP witness.*
> [MINE — the restatement; both halves are RZR's]

### 2.3 ⚑ The price — the part that is ours

`paper/scripts/boundary_exchange_rate.py`, using **only** the constants in `paper/scripts/prover_floor.py`
(themselves MEASURED, sources in that file): mult-equivalents per committed base
felt, w=48, h=2²⁰. [MEASURED]

| lb | hash | encode | sumcheck | **TOTAL / committed felt** |
|---:|---:|---:|---:|---:|
| 1 | 364 | 30 | 40 | **434** |
| 2 | 728 | 50 | 40 | **818** |
| 3 | 1,455 | 90 | 40 | **1,585** |
| **4 (measured optimum)** | 2,910 | 170 | 40 | **3,120** |
| 5 | 5,820 | 330 | 40 | **6,190** |
| **6 (deployed)** | 11,641 | 650 | 40 | **12,331** |

Virtualizing a value instead costs the sumcheck folding term, **≈40
mult-equivalents per value per layer** it participates in.

> **⚑ THE EXCHANGE RATE. One committed base field element is worth ~3,120 field
> multiplications at lb=4 and ~12,331 at lb=6. Virtualizing one costs ~40 per
> layer. ⇒ 78× at lb=4, 308× at lb=6.**
>
> **DECISION RULE: virtualize a value iff the number of sumcheck layers it
> participates in is below ≈78 (lb=4) / ≈308 (lb=6).**

This is the answer to Thaler's *"there's a sweet spot"* — **it locates the sweet
spot, in our constants.** The survey states the tension qualitatively; nobody
prices it, because the theory counts communication and the practice benchmarks
whole systems. **This is the transferable contribution.**

**Cross-check of the marquee number** (same script, full cost function, not element
counts):

| n | AIR felts | virtualized felts | AIR cost | virt cost | ratio |
|---:|---:|---:|---:|---:|---:|
| 256 | 67,108,864 | 196,608 | 2.12e11 | 6.14e08 | **346×** |
| 1024 | 4.29e09 | 3,145,728 | 1.38e13 | 9.93e09 | **1,391×** |
| 4096 | 2.75e11 | 50,331,648 | 8.97e14 | 1.61e11 | **5,590×** |

vs the naive `4n/3` element count: 341× / 1,365× / **5,461×**. Agreement to 2.4%.

⚠ **What I had to reconstruct.** `prover-floor.md:31` states "Ratio = 4n/3" and
SELVAGE §2 states "5,461× at n=4096" with **no script behind either** — `rg`
finds three prose mentions and zero derivations. The `4` is reconstructible as
four committed cells per multiply-accumulate row (`a_ik`, `b_kj`, product, running
accumulator): `4n³/3n² = 4n/3`. **It checks out. It was still an unscripted number
in a marquee position** until this lane. It now has one:
`paper/scripts/boundary_exchange_rate.py`, with its inadequacies named in-file.

### 2.4 ⚑ Is boundary size a property of the relation or the encoding?

The brief asks this directly, and it has a clean answer: [MINE]

> **Statement size is a property of the RELATION.** **Interior size is a property
> of the ARITHMETIZATION.** **Their ratio is therefore not a property of the
> relation at all — it measures how wasteful your encoding is.**

⚠ **And the catch.** `|w|` is not canonical either — you choose the witness. For
`y = H^k(x)` the witness can be *one field element*. Taken literally, "choose
statements whose boundaries are small" says **commit one element and prove
everything**, which is wrong, for reasons the committed-count metric cannot see
(rounds, proof size, recursion) *and* for Thaler's reason (§1.3: the residual
check gets more expensive). **SELVAGE §2 is under-determined as stated and means
nothing without §2.3's cost model attached.**

### 2.5 Is there a class where interior = boundary? Two answers, from opposite directions

**(a) From theory, the elidable class is characterized.** Kalai–Raz 2008 +
[GKR15, RRR16] give poly(witness)-length IOPs for NP relations verifiable in
**bounded depth OR bounded space**; RZR Thm 2 sharpens to `(1+γ)|w|` for bounded
space, and notes a space bound *"is inherent under the widely believed assumption
that P is not contained in SPACE(Õ(n))"*. [READ] ⇒

> **The interior is elidable for relations whose verification is LOW-DEPTH or
> LOW-SPACE; where verification needs both large depth and large space, the trace
> is the statement and materializing it is right.** [MINE — the second clause]

| workload | depth | space | verdict |
|---|---|---|---|
| matmul / ML forward pass | O(log n) | read-only, streaming | virtualizable — the flagship case |
| FHE `fold_add` | **1** | read-only | virtualizable to **zero rounds** |
| FHE NTT butterfly | O(log N) | O(N) | virtualizable (86–406×, `prover-floor.md`) |
| kernel semantic turn | shallow | small state delta | virtualizable by construction — ⚠ **unmeasured**, §5.3 |
| **zkVM execution** | **Θ(T)** | **Θ(memory)** | **not virtualizable — materializing is right** |

⚑ **"Shallow and wide" is the shared property of the three SELVAGE workloads, not
"boundary"** — and it is the literature's own class, and it says what does *not*
qualify. That is a better unifying sentence than the one in SELVAGE §2. [MINE]

**(b) From practice, one instance is proved optimal.** Min Jun Jo, *"A Separation
Principle for Lookup-Based zkML"*, eprint **2026/1390**: in a Shout-style one-hot
lookup argument, *"the per-lookup proving work is a function of the access pattern
alone, never of the table values, so function structure has zero leverage on it."*
[READ] ⇒ for lookups, the statement **is** the access multiset, it is already
achieved, and no structure helps. **A characterized "interior = boundary" class,
arriving from the opposite direction.**

⚠ **Correction to the brief.** The brief calls 2026/1390 "the Ω(m) commitment
floor [that] says you cannot beat the count of committed values." It is not that.
It is a **lookup-specific** separation whose bounds the paper itself labels
*"restricted-model and content-agnostic: rank/degree bounds within a fixed prover
class […] not unconditional complexity bounds."* [READ] The general floor we hold
is the `Ω(|w|)` extraction argument, backed by GH98/GVW02 — **not 1390.**

### 2.6 Non-algebraic relations: the principle does NOT extend as a count reduction

- **A lookup argument does not shrink committed count; it changes DEGREE and
  LOCALITY.** LogUp introduces a fresh aux column of the same height because
  `1/(x+β)` is not low-degree. **71% of every committed element in a zkML proof is
  a LogUp extension-field aux column** (`prover-floor.md`). It is *untrusted
  advice* in Thaler's sense — deliberately committed to make the check cheap.
- **Offline memory checking** commits a sorted permutation of the interior. Same
  count. Thaler's survey §5.4 analyses it exactly this way and calls it costly:
  *"the prover must commit to extra data (the sorted copy), increasing total
  commitment cost."* [2ND-HAND] Twist/Shout are presented as the fix.
- **The exception that proves the rule: Lasso.** *"if the table t is structured
  […] **no party needs to commit to t**, enabling the use of much larger tables
  than prior works (e.g., of size 2^128 or larger)."* [2ND-HAND] ⇒ structure
  elides the **table**; nothing elides the **per-access advice**.

### 2.7 ⚑ The best available lower bound, and its honest limits

**Chakrabarti–Cormode–McGregor–Thaler, *Annotations in Data Streams*** (ICALP'09 /
TALG 2014). An `(h,v)`-scheme has help cost h (annotation bits) and verification
cost v (verifier space). Remark following Thm 3.1: [READ by lane, verbatim]

> "an online MA protocol P for an **arbitrary** two-party communication problem f
> satisfies **hcost(P)·vcost(P) = Ω(R^→(f))**, where R^→(f) is the one-way
> randomized communication complexity of f."

⇒ **A lower bound that is a function of the FUNCTION, not of any algorithm
computing it.** That is the relation-intrinsic quantity our observation posits, and
it is proved. Companion bounds: `hv = Ω(m)` for SELECTION, `hv = Ω(n)` for exact
`F_k`, `hv = Ω(n/t⁴)` for `DISJ_{n,t}`.

⚠ **Two limits, and they are fatal for our use:**
1. It is a **product** bound. It never says "you must send h bits". **A SNARK
   verifier has unbounded space, so v is unbounded and the bound goes vacuous.**
2. It is for streaming/MA protocols; **there is no published bridge to
   commit-and-open arguments.**
3. **Matmul is not in the paper.** [READ by lane — negative finding]

**The live frontier:** Bhadauria, Block, Ghosh, Thaler, *SNARK Lower Bounds via
Communication Complexity*, TCC 2025, eprint **2025/1698** — extracts an
information-theoretic communication core from a polynomial commitment scheme
(Hyrax Ω(√N), Bulletproofs Ω(N), Dory Ω(log N)). Bounds **verifier/core
communication, not committed-value count.** [2ND-HAND — **not in paperbin; fetch it**]

### 2.8 The theorem, stated as well as I can get it — and what resists

**Proposition (upper).** [READ — Thaler CRYPTO'13 Thm 3] For matmul, `n² + O(log n)`
communication with prover time `T(n)+O(n²)` for any unverifiable algorithm T.
Generalization: [READ — RZR Thm 2] for NP relations in poly-time / `n^ξ` space,
IOP length `(1+γ)|w|`.

**Proposition (price).** [MEASURED] Committing a base felt costs `C(lb)` (table
§2.3); virtualizing costs `≈40·layers`. Virtualization is profitable iff
`layers < C(lb)/40`.

**⚑ What resists — and this is where any novelty is.**
1. **There is no lower bound on axis C.** Nobody has shown any relation *requires*
   committing more than its statement. The question is not even framed. A theorem
   of the shape *"relation R has `μ(R) = ω(|w|)`"* would be new — and I could not
   construct one, because `μ` quantifies over all sound arguments and the
   construction side keeps winning (GKR virtualizes anything uniform).
2. `|w|` is not canonical (§2.4).
3. The three-way trade (committed / field work / proof size) has **no total order**
   — committed count dominates only because of measured constants (§3.4).
4. **The interesting content lives in the encoding, and the encoding is not a
   mathematical object until you fix a compiler.** Which is §3.

---

## 3. Would a boundary-statement compiler be real?

### 3.0 ⚑ Verdict first: it exists in three halves, in three communities that do not talk

**No boundary-statement compiler exists. Its three hardest components each exist,
fully built, in a different field, and nobody has joined them.** [2ND-HAND unless
marked; the ZKML quotes are [READ] in our own copy]

| component | who has it | what it is | what it lacks |
|---|---|---|---|
| **derive the cheap identity** from the expensive spec | **Narmour, Job, Yuki, Rajopadhye** — *Simplification of Polyhedral Reductions in Practice* (arXiv 2411.17498) + *Maximal Simplification of Polyhedral Reductions* (**POPL 2025**, PACMPL 9:67–94); on Gautam–Rajopadhye *Simplifying Reductions* (POPL 2006) | **automatically derives the O(N²) ABFT checksum identity from the O(N³) matmul spec**, push-button. Also rediscovers Lyngsø's O(N⁴)→O(N³) RNA algorithm and finds three unknown variants | no proof-system cost model, no commitment cost, no soundness reasoning, no machine-checked equivalence, **zero citations to or from cryptography** |
| **search equivalent encodings under a measured cost model** | **Chen, Waiwitlikhit, Stoica, Kang** — *ZKML*, **EuroSys 2024** | database-style optimizer: logical plans → physical plans → measured FFT/MSM cost model → pick cheapest. Up to 24× | searches **gadget choice and grid layout**, not statement form |
| **pick the protocol by static analysis** | **Vu, Setty, Blumberg, Walfish** — *Allspice*, **IEEE S&P 2013** | *"uses static analysis to compile an input program to the best verification machinery for that program"* — chooses per-program between GKR/CMT and general constraint systems | 13 years stale, pre-SNARK, unformalized, **abandoned** when the field went general-purpose |
| **machine-check the emitted object** | **Clean** (zkSecurity/Verified-zkEVM, Lean 4) + **ArkLib** | Clean is the only artifact satisfying our house rule — an embedded Lean DSL emitting AIR with verified gadgets; ArkLib holds the IOR composition/lifting interfaces where a statement-equivalence theorem would live | **no search, no cost model whatsoever** |

⚑ **The one that matters most is Rajopadhye's.** *"the task of constructing ABFT
checksums can be cast as an instance of the simplifying reductions problem […]
cheap checksum specifications can be obtained systematically from simplification."*
**The half we assumed was the research problem — automatically finding the cheap
checkable identity — is solved, in HPC, and has never met a proof system.**

**And the closest single artifact already ships our flagship move.** ZKML EuroSys
2024 §6.1, verified in our own copy `~/paperbin/zkml-eurosys24-kang.txt:504`: [READ]

> "we can perform matrix multiplication asymptotically more efficiently by using
> **Freivalds' algorithm** to verify matrix multiplication. In particular, **we can
> compute B 'outside' of the circuit and simply verify that B = WA.** To perform
> the verification, we can take a random vector r and verify that Br = WAr, which
> is O(n²). […] The random vector r **must be generated after the matrix and
> results are committed.**"

and its abstract, same file: *"There are **many equivalent ways to implement the
same operations** within ZK-SNARK circuits, and these design choices **can affect
performance by 24×**."* [READ]

⇒ **The matmul boundary move is deployed in a zkML compiler, in our library.**
Two things save the idea from being fully claimed, and they are the honest residue:
1. **It is hardcoded into one gadget, unreachable by the optimizer's search.** The
   cost model prices FFTs and MSMs *given a layout*; it cannot price *a different
   theorem*.
2. §4.4, ZKML's own words: *"A formal proof of correctness [that the circuit
   representation is equivalent to the original computation] is **outside the scope
   of this work**."* [2ND-HAND] **No proof, no checker, not even a differential.**

**What does NOT exist** (all [2ND-HAND], from directed negative searches):
- **CirC does not do this.** Its lowering is fixed rule-based per operator; §3.3's
  optimization suite is *"selectively appl[ied]"* **by the human compiler author**.
  Its one R1CS-specific optimization is linearity/Gaussian elimination. Front-end
  optimization strategy is disclaimed as future work. ⓘ *We hold only
  `ozdemir-circ-SLIDES-not-paper-sp2022.pdf` — the slides, not the paper.*
- **Not one paper applies e-graphs / equality saturation to ZK constraint systems**
  (multiple query shapes incl. a full EGRAPHS-2025 sweep). Adjacent fields are
  dense: Quartz (quantum, PLDI 2022), TENSAT (MLSys 2021), Coward et al. datapath
  (ARITH'22/DAC'23).
- **No MLIR ZK dialect with legalization + cost model + autotuner.** zirgen
  (RISC Zero) and LLZK (Veridise) are MLIR-based but carry **no cost model**.
- **No system machine-checks the CHOICE of arithmetization.** CAV 2023
  field-blasting verifies **one fixed** lowering with *bounded* VCs; Coda (S&P'24),
  Picus (PLDI'23), Kestrel/ACL2 PFCS are **post hoc on hand-written circuits**.
- **Nothing compiles string diagrams into constraint systems** (catgrad, DisCoPy).
- ⚠ **Prior-art hazard: US Patent 12,250,316**, *"Methods and systems for selecting
  an optimal proof system for zero-knowledge and other proofs."* Selects the
  **backend** against user constraints, not the statement form. **Read before publishing.**

### 3.1 ⚑ Restating the problem so it has an algorithm

"Emit the cheapest boundary statement" is not a problem statement. This is: [MINE]

> Given a computation as a DAG of values, **choose a CUT.** Values on the cut are
> **committed**; values above it are **virtualized** and re-established by sumcheck
> against the cut. Cost = `α·|cut| + β·(virtualization work above) + γ·(depth of
> the virtualized region)`, with `α ≈ 3,120` mult-equiv (§2.3), `β ≈ 40` per value
> per layer, `γ` the proof-size/recursion term.

**Boundary-statement compilation is min-cut on the dataflow graph with a depth
penalty.** Real structure, not a slogan:

- `α → ∞`: the cut collapses to the inputs. **That is GKR.**
- `β,γ → ∞`: the cut is everything. **That is a materializing AIR.**
- **Everything in between is the design space, and nobody schedules it.**
- ⚑ **And Thaler's "sweet spot" (§1.3) is exactly the statement that the optimal
  cut is interior.** The survey asserts a sweet spot exists; this is the objective
  function whose minimum it is.

### 3.2 The three parts, and which one is hard

1. **Cost model — WE HAVE IT.** §2.3, measured, in-repo, per-element,
   blowup-aware. Normally the missing piece; here the done one.
2. **Search — BORROWABLE.** §3.3.
3. ⚑ **LEGALIZATION — THIS IS THE WHOLE THING.** *Which cuts admit a sumcheck
   argument at all?* Thaler's definition is the legality condition, verbatim:
   *"committing to a smaller or simpler object b such that a can be expressed as a
   **low-degree function of b**"*. Plus: the verifier must evaluate the wiring
   predicates in polylog time, so the index space must be **structured**.
   `1/(x+β)` fails the first; an irregular circuit fails the second.
   **No cost model can decide this. It is a semantic judgement.**

⇒ **That is where Lean earns its place, and it is the house law, not taste:** the
judgement *"this cut is legal, and the emitted instance is a sound reduction of the
source relation"* must be a **machine-checked theorem about the emitted object**.
A legalization heuristic in a Rust pass is a soundness-bug generator — an illegal
virtualization does not fail loudly, it yields a system that accepts false things.

⚑ **And here is the design finding that decides the whole shape, and it is the
single most useful thing the compiler search returned:**

> **The object being rewritten is a RELATION under a SOUNDNESS-PRESERVING
> REDUCTION ORDER — not a term under functional equality.**

Equality saturation (e-graphs) preserves *functional denotation*. It therefore
**can never** turn n³ multiply-accumulates into an n² checksum, because **Freivalds'
check is not the same function** — it is a different relation that implies the
original with high probability. So the entire e-graph toolchain, which is the
obvious thing to reach for, is **structurally unable** to search this space.
[2ND-HAND — the lane's inference, and I agree with it on inspection]

That both **explains** why the ZK community has no equality-saturation work
(mechanism: wrong equivalence, so it never got off the ground) and **names the
buildable object**: a rewrite system whose relation is `⊑` ("is a sound reduction
of"), with soundness error accumulating along rewrites, and whose steps are
discharged as theorems. **ArkLib's IOR composition and lifting interfaces are
exactly the type of that `⊑`.** Nobody has used them for compilation.

⚠ Note the tension with SELVAGE §1: ArkLib's composition theorems are `sorry`. The
interface we would build on is the part that is not proved.

| stage | what | substrate |
|---|---|---|
| input | the relation as Lean-authored semantics — **not a traced graph** | Lean |
| legalization | per candidate cut: proof that the residual is a low-degree function over a structured index space, and that the emitted instance denotes the source | **Lean, proved** |
| cost | §2.3 exchange rate over the cut | derived |
| search | min-cut / `revolve` over legal cuts | ordinary code |
| emit | the instance **the legalization theorem is about** | Lean `@[export]` |

⚠ **The input must NOT be a traced graph.** A trace is a Cook–Levin witness
already; compiling from one means the interior was materialized *before* the
compiler ran, so it can only ever *recover* statements, never *preserve* them.
Same failure as compiling ML kernels from an unrolled loop nest.

### 3.3 ⚑ The analogy that hands us an algorithm

**Boundary-statement compilation is gradient checkpointing in a different
currency.** [MINE]

| checkpointing | this |
|---|---|
| store an activation | **commit** a value (α ≈ 3,120 mults) |
| recompute from a checkpoint | **virtualize**, re-establish by sumcheck (β ≈ 40/layer) |
| memory budget | committed-element budget |
| recompute depth | sumcheck rounds ⇒ **proof size** (the extra γ term they don't have) |
| Griewank–Walther `revolve`; Chen et al. sublinear-memory | the same search, re-costed |

The objective has the same shape (store/recompute over a DAG), so the
optimal-schedule literature transfers. It also predicts the failure mode:
checkpointing schedules are notoriously sensitive to the store/recompute *ratio*,
and ours swings **4× with one config constant** — **a compiler scheduling against
lb=6 emits a different program than one scheduling against lb=4, and lb=6 is 2.9×
off the measured optimum** (`prover-floor.md` action #1).

### 3.4 Methodology template, and the FHE precedent

- **Quartz: Superoptimization of Quantum Circuits** (Xu et al., **PLDI 2022**) is
  the shape to copy: *"generates candidate circuit transformations by systematically
  exploring small circuits and **verifies the discovered transformations using an
  automated theorem prover**. To optimize a circuit, Quartz uses a **cost-based
  backtracking search** that applies the verified transformations."* Search +
  machine-checked rules + cost model, all three, in one artifact — at the wrong
  altitude (local gate rewrites) and the wrong equivalence (functional). [2ND-HAND]
- ⚑ **The FHE community already treats "which equivalent program" as a synthesis
  problem and the ZK community does not.** Porcupine (PLDI 2021) synthesises
  vectorized HE kernels from a sketch, *verified*, 52% over hand-tuned; Coyote
  (ASPLOS 2023); Google's HEIR (MLIR) for scheme/parameter selection. **That is a
  direct precedent for the thing we would build, one paradigm over.** [2ND-HAND]

### 3.5 Verdict: compiler or slogan?

**Neither — and the honest verdict is more useful than either.**

- ✅ The **objective** is real, priced, measured, and its existence (a sweet spot)
  is asserted independently by Thaler.
- ✅ The **derivation engine** — the half we assumed was the research problem —
  **is built**, in HPC (§3.0).
- ✅ The **cost-model search** is built, in zkML (§3.0).
- ✅ There is a **decision rule with a number** making falsifiable predictions (§5).
- ❌ **Nobody has joined them, and there is a structural reason**: the three live in
  communities with no citation path, and the obvious joining technology (e-graphs)
  is the wrong equivalence (§3.2).
- ❌ **Legality is semantic** and not enumerable by a cost model. Realistically the
  first version is a **library of proved reduction schemas** — bilinear form →
  matmul sumcheck; linear map → single opening; layered circuit → GKR; structured
  table → Lasso/Shout — **plus a scheduler**. Not an open search.
- ❌ It is **not a theorem about optimality**; it is an empirical claim about
  `α/β` with a **sunset condition**: cheaper commitment moves the optimal cut
  *toward* materializing. At lb=1 the ratio is 11×, not 308×. **Our own action item
  #1 (lb=6 → lb=4) moves it 4× and therefore moves every decision this compiler
  would make.**

> **Honest one-liner: not "a heuristic about three examples" — the principle is
> published doctrine and the three examples are instances of a characterized class.
> Not a compiler either — but not because the hard parts are unsolved. They are
> solved, in three fields that have never cited each other. The unclaimed object is
> narrow and nameable: _a rewrite system over relations ordered by
> soundness-preserving reduction, scheduled against a measured commitment price,
> with each step discharged as a Lean theorem about the emitted object._ Every
> clause of that sentence exists somewhere; the conjunction exists nowhere.**

---

## 4. Corrections this lane produced

1. ⚑ **The principle is prior art with a name — `virtual polynomial`** — and the
   survey whose thesis it is (2025/2041) is in `~/paperbin` **twice**. SELVAGE
   §5.3 ("*We noticed interior-vs-boundary. Nobody has turned it into a
   discipline*") is **false** and must be rewritten. The discipline exists; what is
   unclaimed is the **scheduling of it against a measured commitment price**.
2. ⚑ **The monotone reading is refuted by that survey**: *"Not zero—there's a sweet
   spot."* A pure-statement encoding can be slower. §1.3.
3. ⚑ **The fork should not name AIR.** Per CCS, R1CS/Plonkish/AIR are
   interconvertible at essentially no cost; the property is **materialization vs
   virtualization**. §1.5. ⚠ CCS is [2ND-HAND] — verify before publishing this.
4. ⚑ **Retire the word "boundary"** (border-rank collision) and **never say
   "succinct PCP" or "certificate complexity"** for this. §1.7.
5. ⚑ **The brief's description of 2026/1390 is wrong.** §2.5(b).
6. ⚑ **The 5,461× figure had no derivation artifact.** It checks out to 2.4%; it
   now has one. §2.3.
7. ⚑ **Our sentence collapses three tiers**; `fold_add`'s zero-round result is the
   strongest tier (algorithm-independence) and should be claimed as such. §1.6.
8. ⚑ **The unifying property is "shallow and wide"**, which is the literature's own
   class and says what does *not* qualify. §2.5(a).
9. ⚑ **The upper-bound half is 12 years old (Thaler CRYPTO'13 Thm 3); the
   lower-bound half does not exist.** If we want a research claim, it is there.
10. ⚑ **The zkML application is already shipped.** ZKML (EuroSys 2024, in our
    paperbin) uses Freivalds for linear layers — *"compute B outside of the circuit
    and simply verify that B = WA"* — so even the *application* of the principle to
    zkML is not ours. What is unclaimed is that it is **hardcoded in one gadget and
    unreachable by their optimizer's search**, and that they disclaim equivalence.
11. ⚑ **The compiler's hardest half is built in HPC** (Rajopadhye's group,
    POPL 2025 + POPL 2006). We assumed automatic derivation of the cheap identity
    was the research problem. It is a push-button compiler pass with zero
    cryptography citations in either direction.
12. ⚑ **Do not reach for e-graphs** (§3.2). Wrong equivalence, structurally.
13. ⚠ **Allspice (S&P 2013) did protocol selection by static analysis and the field
    dropped it.** Any "nobody has tried this" framing must survive that fact.

---

## 5. The three examples that would most sharply test the principle

Chosen so each can come out **against** it. [MINE]

### 5.1 ⚑ A Poseidon2 permutation — where the exchange rate contradicts the folklore

Folklore says a hash is the canonical non-virtualizable interior: deep, sequential,
nonlinear. **The exchange rate says otherwise.** Poseidon2/BabyBear is RF=8, RP=13
⇒ ~21 rounds ⇒ ~21 sumcheck layers, against a threshold of **78 (lb=4) / 308
(lb=6)**. The rule predicts **virtualizing the permutation's interior beats
committing it by ~4× at lb=4 and ~15× at lb=6** — for the single most-committed
object in the prover.

- **Why sharpest:** counterintuitive, quantitative, immediately falsifiable, on a
  component we have measured to death.
- **Corroborating signal already in hand:** `prover-floor.md` action #2 —
  in-circuit Merkle authentication is **15.2×** our own cheaper path
  (`map_write_chip` 227 ms vs `umem_write_read_nochip` 14.9 ms) and *"re-derives,
  inside an argument that already carries a vector commitment, a fact the PCS could
  establish as an opening."* **That is a virtualization win of the predicted size,
  already measured, not yet recognised as one.**
- **What refutes it:** if degree management forces the permutation state to be
  committed per round anyway, the layer count is not 21.
- ⚠ Per `minted-poseidon2-perm-is-a-reduction-bomb.md`, run this as an
  emitted-object cost count — **never** by `decide`/`rfl` through the hash.

### 5.2 ⚑ The LogUp auxiliary column — the highest-value test in the repo

**71% of every committed element in a zkML proof is a LogUp extension-field aux
column.** It exists to make `1/(x+β)` degree-1. **Can it be virtualized by a
degree-raised sumcheck instead of committed?**

- ⚑ **Thaler's own matmul virtualization is exactly this move** — a *quadratic*
  extension of the gate values instead of the multilinear one (§1.4). So the
  technique is proven to work in at least one place; the question is whether
  LogUp's reciprocal admits it.
- **Yes** ⇒ 71% of committed elements vanish, on the term that dominates: larger
  than the field migration (3.4×), the blowup fix (2.9×) and the linear-op wins
  **combined**.
- **No** ⇒ §2.6 gets its proof and the principle gets a hard quantified boundary.
- ⚠ Price it through the **degree → blowup → hash** chain, not element count.
  `prover-floor.md` action #3: lookup batching looked like 2.43× on elements and
  was a **0.62× net loss** because degree 7 forced lb ≥ 6. That chain is what makes
  this test sharp rather than obvious.

### 5.3 ⚑ The kernel turn — the claim we assert and have never measured

SELVAGE §2 asserts *"the kernel's statements are boundary statements by
construction."* It is the only one of the three workloads with **no number**;
`prover-floor.md` gives the turn a ~10,000× floor-to-best-known gap and calls its
~733-felt witness *"a shape estimate."*

- **Test:** count committed elements in a real turn proof; divide by the state
  delta. The claim predicts O(1). **The 10,000× gap makes O(1) implausible**, so
  this is a test the claim can fail — and if it fails, "three workloads on one
  substrate" (SELVAGE §3.3) loses a leg.
- **Why sharp:** the only workload where we assert the principle *already holds*
  rather than proposing to apply it. An unmeasured "by construction" is exactly the
  shape of claim this repo has learned to distrust.

---

## 6. Open, and what I would do next

1. ⚑ **Read Thaler 2025/2041 end to end.** It is in our library, twice, and it is
   the survey of the thing we are doing. Everything downstream of §5 of that paper
   is unexamined by us.
2. ⚑ **Fetch the eight papers this lane needed and we do not hold.** Checked
   against `~/paperbin`, all absent:
   - **Narmour/Job/Yuki/Rajopadhye**, arXiv 2411.17498 + POPL 2025 (10.1145/3704839)
     — *the derivation engine*. Highest priority of the eight.
   - **Gautam & Rajopadhye**, *Simplifying Reductions*, POPL 2006 — its foundation.
   - **Allspice**, Vu/Setty/Blumberg/Walfish, IEEE S&P 2013 — the 2013 ancestor.
   - **eprint 2025/1698**, SNARK lower bounds via communication complexity — the
     live frontier of §2.7.
   - **eprint 2026/1571**, LAMP (matmul via proximity testing, 30.3× at k=2¹²).
   - **Quartz**, PLDI 2022 — the methodology template.
   - **Porcupine**, PLDI 2021 — the FHE synthesis precedent.
   - **CirC**, S&P 2022 — ⓘ **we hold only the SLIDES**
     (`ozdemir-circ-SLIDES-not-paper-sp2022.pdf`), not the paper.
3. **Verify CCS 2023/552 at source** before publishing correction #3 (the lane was
   rate-limited).
4. **Read GH98 / GVW02 directly.** Currently second-hand via Thaler's citation and
   a lane summary; it is the load-bearing floor. ⚠
   `feedback-read-the-blocker-before-you-relay-it.md`.
5. **Run test 5.2 (LogUp aux).** Highest expected value by a wide margin.
6. **Make the full-text `paperbin` extract a standing artifact**, not a per-lane
   rebuild. Four absence-claim failures in a week share one cause and this is the
   fix.
7. **Rewrite SELVAGE §2 and §5.3** with: the name (virtual polynomials), the
   citation, "shallow and wide" as the unifying property, the exchange rate as the
   decision rule, and a claim scoped to **scheduling**, not to the discipline.
