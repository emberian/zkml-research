# Inspiration sweep — 2026-08-13

Broad, no predetermined target. The brief: find work *adjacent to* our position
that we have not touched, in **their** words. Value is entirely in what is NOT
already in `docs/SELVAGE.md` or `notes/window-review-2026-08-13.md`.

## Corpora and instruments (stated up front, per standing order)

| corpus | instrument | coverage |
|---|---|---|
| IACR eprint full text | `rg` over `…/scratchpad/ft/*.txt`, 25,765 papers | 1996-001 … **2026-777** (≈ April 2026). Cryptology **only**. |
| `~/paperbin` | `ls \| grep -i` over 1,528 filenames + `rg` into extracted `.txt` where present | our own holdings; **filename-only** search unless a `.txt` sibling exists — a paper whose *content* covers a topic its filename doesn't will be missed |
| arXiv cs.PL / cs.LO | delegated lane (`inspiration-sweep-pl.md`) | — |
| arXiv cs.CC / ECCC / classic STOC-FOCS | delegated lane (`inspiration-sweep-cc.md`) | — |

⚠ **Instrument blindness, named**: the eprint mirror is a flat text dump per
paper — full text, so §4.3 *is* visible, unlike the first-2-pages cache that
burned us. But it is cryptology-only, and it has no 2026-778+.

---

**Read the Synthesis section at the end first** — it is the ranked deliverable.
Batches 1–4 are the working record, appended as the finds landed. Companion
files: `inspiration-sweep-cc.md` (complexity) and `inspiration-sweep-pl.md` (PL).

## Batch 1 — eprint full-text, 2026-08-13

### ★★★★ 1. Distiller — eprint 2022/1557, "Less is more: refinement proofs for probabilistic proofs"
Jiang, Chait-Roth, DeStefano, Walfish, Wies (NYU Courant). Extended version of an
IEEE S&P paper.

**What it is, in their words**: "a general-purpose framework, called Distiller, in
which a user translates to constraints **not the original computation but an
abstracted specification of it**. Distiller is the first in this area to perform
such transformations in a way that is provably safe. Furthermore, by taking the
idea of 'encode a check in the constraints' to its literal logical extreme,
Distiller exposes many new opportunities for constraint reduction, resulting in
cost reductions for benchmark computations of **1.3–50×, and in some cases,
better asymptotics**."

**Mechanism**: a refinement chain over transition systems, `T_I ≤_r T_E ≤_q T_S`
(implementation ≼ intermediate ≼ spec), with refinement *mappings* constructed by
a recipe borrowed from refinement calculi; refinement mappings **compose**
(`T1 ≤r T2` and `T2 ≤q T3`). Proof obligations discharged by **SMT** — and §"Distiller
uses mechanized proofs" says explicitly that SMT "is a choice. Nothing [is]
intrinsic … to mechanization", pointing at refinement calculi and at SMTCoq.

**⚠ This CONTRADICTS `SELVAGE.md` §5 innovation 3.** We wrote: "A boundary-statement
compiler. We *noticed* interior-vs-boundary. **Nobody has turned it into a
discipline**: given a computation, emit the cheapest boundary statement, with the
choice justified." Distiller is that discipline, published 2022, with the
justification *provable* and the mechanism *compositional refinement*. It is not
phrased as boundary-vs-interior and it has no asymptotic theory of which
abstraction is cheapest — but "translate the spec, not the computation, and prove
the substitution safe" is our sentence with different nouns.

**What survives for us** (INFERENCE): three things.
1. The *cost* half is still open — Distiller finds opportunities by hand; it has
   no answer to "which abstraction is cheapest", which is where boundary-vs-interior
   (Θ(n) for bilinear forms) is a *theory* and Distiller has a *recipe*.
2. Their obligations go to SMT over transition systems; ours would be Lean over the
   emitted object. Their own §7 says the mechanization is a free choice — so the
   Lean instantiation is invited, not foreclosed.
3. **Distiller has no follow-ups.** Instrument: `rg -i 'Distiller'` over 25,765
   eprint full texts, 2026-777 inclusive → 8 hits, of which exactly one (2022/1557)
   is this work and the other seven are unrelated uses of the English word. The
   discipline was published and *not continued* inside cryptology.

**Distance to usable**: the *idea* is usable today (reframe our §5.3 as "port the
Distiller discipline to a Lean-emitted object and add the cost theory"). The
artifact is a research prototype over R1CS/SMT.

---

### ★★★★ 2. Ring-agnostic doubly-efficient IPs — eprint 2022/587
Eduardo Soria-Vazquez, "Doubly Efficient Interactive Proofs over Infinite and
Non-Commutative Rings" (TCC 2021 / CRYPTO-line work).

**What it is**: GKR generalized to an *arbitrary* ring `R`, possibly
non-commutative and possibly infinite, with **black-box access to its arithmetic**
and to a subset `A ⊆ R` that need only satisfy "limited commutativity and
regularity properties". They had to invent: a definition of polynomial ring over a
non-commutative ring, **left and right multilinear extensions**, a modified layer
consistency equation, and an adapted sum-check.

**Their stated conclusion, verbatim**: "the core conclusion of our results is that
state of the art doubly efficient interactive proofs **do not require much
algebraic structure**. This enables exact rather than approximate computation over
infinite rings as well as **'agile' proof systems, where the black-box choice of
the underlying ring can be easily switched through the software life cycle**."

**Touches**: `SELVAGE.md` §4 open question 3 (**value-ring polymorphism**) and §5
innovation 4 (value-ring-polymorphic constraint authoring). This is the *theorem
side* of the thing we said must be designed in from day one, and it tells us
exactly which algebraic properties the polymorphism actually needs — i.e. what the
Lean typeclass constraints on a polymorphic AIR should be, rather than guessing
`CommRing` and paying for it.

**⚠ Partial contradiction**: our §5.4 says "Every fast system encodes this in its
type system; nobody has done it in a proof-carrying authoring language." That
stands. But "agility of the underlying ring through the software life cycle" as an
explicit design goal, with the minimal algebraic requirements *isolated as a
theorem*, is prior art we did not have, and it argues the retrofit is less fatal
than we assumed — the requirement set is small.

**Distance to usable**: the requirement analysis is usable immediately as a spec
for our typeclass hierarchy. The construction is GKR-shaped, which we do not have
in Lean at all (§4 open question 5).

---

### ★★★ 3. Functorial arithmetization of Σ¹₁ relations — eprint 2022/777
Morgan Thomas, Orbis Labs. "Arithmetization of Σ¹₁ relations in Halo 2".

**What it is**: compile a relation *written as a Σ¹₁ formula in the language of
rings* (existential second-order — Fagin's theorem territory, i.e. exactly NP)
into Halo 2 circuits, "without laborious and error-prone manual circuit design".
The correctness argument is **functorial**: §5 builds a *category of circuits* with
initial objects, products, coproducts and negations, and defines arithmetization
as a functor.

**Touches**: our authoring discipline. This is the **vocabulary we are not
searching in** — "arithmetization *of a logic*", "functorial arithmetization",
Σ¹₁ / descriptive complexity. We author constraints in Lean; nobody in our notes
has asked what *fragment of logic* our authoring language is, or whether the
emit map is a functor (which would make its correctness compositional by
construction rather than by re-proof per gadget).

**Honest limits**: §5 is titled "**Proof sketch** of correctness of the
arithmetization" — not machine-checked, not even fully written. Halo 2 specific.

**Absence check**: `rg -i 'descriptive complexity|Fagin'` over the eprint mirror →
**1 hit**, and it is unrelated (2003/187). Descriptive complexity has essentially
zero footprint in cryptology. INFERENCE: that is a vocabulary gap worth a lane, not
a proven emptiness.

---

### ★★ 4. Adjacent, catalogued (eprint), not previously in `~/paperbin`
Checked with `ls ~/paperbin | grep -icE …` — all zero unless noted.
- **2019/1062** Ron-Zewi–Rothblum, *Local Proofs Approaching the Witness Length* —
  proof length `(1+γ)·|w|`. The complexity-side statement of "the boundary is what
  you pay for". Also **2024/816** *Zero-knowledge IOPs Approaching Witness Length*.
- **2021/842** Bronfman–Rothblum, *PCPs and Instance Compression from a
  Cryptographic Lens* — succinct PCAs whose **length is polynomial only in the
  witness length**, bypassing the succinct-PCP impossibility by bounding the
  adversary. This is "transform the relation so its certificate is witness-sized",
  the exact shape of our boundary thesis, with an impossibility result on one side
  and an LWE assumption buying the way around it. Also **2024/1659** *Instance
  Compression, Revisited*.
- **2016/988** *Zero Knowledge Protocols from Succinct Constraint Detection* — the
  technique is "the constraints on the honest codeword are themselves succinctly
  describable"; a property of the *relation*, not the protocol.
- **2022/009** Kothapalli–Parno, *Algebraic Reductions of Knowledge*, and
  **2024/1060** *Quirky Interactive Reductions of Knowledge* — a composition
  calculus whose objects are **relations** and whose morphisms are protocols. Not
  in paperbin. This is the composition vocabulary nearest our accumulation-depth
  work and we have not used it.
- **2010/339** *A Certifying Compiler for Zero-Knowledge Proofs of Knowledge* and
  **2012/258** *Full Proof Cryptography: Verifiable Compilation of …* — the
  2010–2012 attempt at exactly our "emitted object is the thing proved about"
  discipline, in the Σ-protocol era. Historical, cheap to read, and it will have
  the PL name we are missing.

---

## Batch 2 — vocabularies we are not searching in

The brief asked for "a community whose vocabulary we should be searching in and
are not". Two, and they are not small.

### ★★★★★ 5. Computer-algebra **certificates** (Dumas–Kaltofen–Villard et al.)
`~/paperbin/dumas-kaltofen-essentially-optimal-interactive-certificates-linear-algebra-issac2014.pdf`
(+ 4 more, downloaded this sweep).

**What it is**: since ~2011 the symbolic-computation community (ISSAC/JSC) has
built *interactive certificates* for linear algebra, with a formal optimality
criterion of their own:

> "The certificates are **essentially optimal** if the time (and space) complexity
> of verification is essentially linear in the input size N" — i.e. `N^{1+o(1)}`.

That is our boundary criterion, named, defined, and used as an acceptance test —
**twelve years before we wrote it down as a thesis**. And they have a *catalogue*
of boundary statements, not one example: rank (sparse/structured, over an abstract
field: **2 matrix-vector products + n^{1+o(1)} field ops**), determinant, minimal
and characteristic polynomial, Frobenius normal form, positive semidefiniteness,
triangular equivalence, rank profiles. Verification of the integer-matrix
characteristic polynomial in `(n² log‖A‖)^{1+o(1)}` bit ops.

**Their protocol shape is ours**: "two-round probabilistic Σ-protocols with
perfect completeness", soundness against a cheating Peggy, and — the load-bearing
sentence — "**Fiat-Shamir heuristic turning interactive certificates into**"
non-interactive ones, "under the random oracle model, or heuristics under standard
computational hardness assumptions from cryptography."

**⚑ This is the sharpest adjacency in the sweep.** They have the *statements*
(optimal boundary certificates for a dozen linear-algebra problems, with
optimality proofs) and they compile them with Fiat–Shamir **as a heuristic, with
no round-by-round soundness, no state-restoration analysis, no attained bound** —
which is *precisely* the leg Selvage holds and nobody else does. The two halves
have never met.

**Touches**: §5 innovation 3 (boundary-statement compiler — here is a hand-built
catalogue to generalize from, rather than one example); §3 ambition 3 (ML
workload — rank/char-poly/PSD certificates are the nonlinear parts of an
inference pipeline that a matmul sumcheck does not cover); §1 (our RBR→FS theorem
finds a customer).

**Distance to usable**: the certificates are stated and proved; porting one
(rank, or char-poly) through our compilation layer is a *bounded* piece of work,
not a campaign. INFERENCE, mine: this is the highest-value near-term item the
sweep produced.

**Absence, with corpus and instrument named**: `rg -il 'interactive certificate'`
over 25,765 eprint full texts → **5 files**, none of them this line of work;
`rg -il 'certificate for the determinant|rank certificate|certificates in linear
algebra'` → **1**. `ls ~/paperbin | grep -icE 'kaltofen|dumas|program-checker'`
→ **0**. Cryptology and computer algebra are not citing each other here.

**Ancestor worth naming**: Freivalds (1979) is cited by them as the seed, and
Blum–Kannan *program checkers* / Blum–Luby–Rubinfeld *self-testing/correcting* are
the same idea one level up — "check the answer, do not re-run the program."
`rg -il 'program checker|Blum and Kannan'` over eprint → 26 files, none in this
sense (all cube-attack / side-channel false positives).

---

### ★★★★ 6. **Semiring provenance / semiring semantics** (database theory, 2007→)
`~/paperbin/green-karvounarakis-tannen-provenance-semirings-pods2007.pdf`,
`gradel-tannen-semiring-provenance-first-order-model-checking-1712.01980.pdf`,
`gradel-tannen-provenance-analysis-semiring-semantics-fol-2412.07986.pdf`.

**Absence first**: `rg -il 'provenance semiring|semiring provenance'` over 25,765
eprint full texts → **0 hits**. `grep -rn 'semiring' ~/dev/zkml-research/{notes,docs}`
→ **0**. This vocabulary has *no* footprint in cryptology and none in our work.

**What it is, with the statements**:
- **Prop. 3.5 (Green–Karvounarakis–Tannen, PODS 2007)**, verbatim: "Let
  `h : K → K′` and assume that `K, K′` are commutative semirings. The
  transformation given by `h` from `K`-relations to `K′`-relations commutes with
  any RA⁺ query … `q(h(R)) = h(q(R))` **if and only if `h` is a semiring
  homomorphism**."
- **Prop. 4.2**: `ℕ[X]` is free — for any valuation `v : X → K` there is a
  **unique** semiring homomorphism `Eval_v : ℕ[X] → K`.
- **Thm. 4.3**: `q(R) = Eval_v ∘ q(R̄)` — the semantics in *any* `K` **factors
  through** the provenance semiring.
- Grädel–Tannen extend this to **full first-order logic with negation**, via a
  commutative semiring of polynomials with **dual indeterminates** (each positive
  token paired with a negative one), in quotient semirings.

**Why it matters to us — INFERENCE, mine, stated as such.** Read "`K`-relation" as
"constraint system valued in ring `K`". Then §4 open question 3 (**value-ring
polymorphism**) is *this theorem*:
1. Prop. 3.5 says transport along a value-ring change is **exactly** ring
   homomorphism — and the `iff` makes it a **refutation instrument**: a candidate
   "polymorphic" emit that does not commute is one whose map is not a
   homomorphism, and that is mechanically checkable.
2. Thm. 4.3 prescribes the *shape of the emitted object*: emit **once into the
   free object** (`ℤ[X]` for a ring, `ℕ[X]` for a semiring) — a syntactic
   expression over ℤ-coefficients and variable ids — and let each concrete value
   ring be a **valuation homomorphism**. That is a concrete answer to "the emitted
   AIR object must be polymorphic in the value ring before more constraints are
   written": it must be the *free* object, not a `BabyBear → BabyBear` function.
   Base ↪ extension is a ring hom, so the transport is a corollary rather than a
   retrofit.
3. The negation gap is closed on their side too (dual indeterminates), which is
   the version an AIR needs since constraints subtract.

**Second, longer-range hook** (INFERENCE, weaker): the dregg through-line is
"biscuit Datalog = derivation circuit". Semiring provenance **for Datalog** —
`ω`-continuous semirings, Thm. 6.4/6.5 in the same paper — is the theory of what a
Datalog derivation *is*, valued in an arbitrary semiring. If a capability
derivation is a Datalog proof tree, its provenance polynomial is its witness, and
the value ring is a *parameter*. Nobody in either field has connected these.

**Distance to usable**: Prop 3.5 / Thm 4.3 are two-line statements whose Lean
analogues over `CommRing` are standard algebra. The *design* consequence (emit
into the free object) is actionable this week and is a hard constraint on the
AIR-emit refactor that §4.3 says must happen before more constraints are written.

---

### ★★★ 7. **Randomized Partial Checking** — a deployed commit-then-audit protocol whose published sampling bound was wrong by an exponential base
eprint **2012/063**, Khazaei–Wikström, *Randomized Partial Checking Revisited*.

**What it is**: RPC (Jakobsson–Juels–Rivest 2002) is commit-then-audit for
mix-nets — "**relax the correctness and privacy requirements to achieve a more
efficient mix-net**", open a random subset of the permutation links instead of
proving the shuffle. Deployed in **Civitas** and **Scantegrity**, and in Norwegian
municipal elections tooling.

**The finding, verbatim**: "even if the issues we have identified are handled …
with probability roughly **(3/4)^t and not 2^{-t} as claimed**." Plus practical
attacks breaking *both* correctness and privacy, ten years after publication.

**Why it is a hit for us**: our `notes/audit-sampling-prior-art.md` catalogues six
prior-art families (covert security, spot-checking, PoR/PDP, refereed delegation,
optimistic rollups, inspection games). **RPC is not among them**, and it is the
only one in that class where the *published soundness bound itself* was wrong —
not the implementation, the bound. The mechanism: the audit selection is
**pairwise-dependent by construction** (exactly one of each pair is opened, for
privacy), and the adversary places its cheats so that detection needs *both*
halves of a pair. Marginal per-item detection 1/2; true per-cheat detection 1/4.

**Does it contradict `Selvage/AuditSampling.lean`?** No — and the reason is worth
recording. Our sequential theorem is built on "expectations over **independent
uniform draws, one per round**" (`expOver`), and `BeaconLeg` bounds only the
per-round *marginal* fire probability `∀ h, p − ε_beacon ≤ Pr_ω[fires h ω]`. An
RPC-shaped deployment violates the independence hypothesis outright, so the
theorem would not apply — it would not silently give a wrong number. **But**
(INFERENCE, mine) that is exactly the shape of a hypothesis that fails at
instantiation and is easy to assume away: a privacy requirement (do not reveal
which items were audited together) is a *natural* reason a real beacon becomes
dependent across rounds, and the documented cost of getting that wrong is the base
of the exponential, `(3/4)^t` vs `2^{-t}`. It belongs in the audit note as the
named instantiation hazard for `expOver`.

---

## Batch 3 — the two contradictions, and three more finds

### ★★★★★ 8. ⚠ **A denotational semantics for (safe) Rust exists, in Lean** — eprint 2026/604, CatCrypt
Bas Spitters, March 2026. Not in `~/paperbin` (`grep -icE 'hax|aeneas|verus|rustbelt|creusot'` → 1, and it is not this).

**What it is**: a Lean library of "**172 cryptographic protocols and constructions
with machine-checked security theorems in the computational model**", of which
**110 have the full Rust→Lean pipeline** via the **hax** transpiler. Built in **two
months, with GenAI**, with an explicitly-published methodology for
*specification confidence* (test-vector validation, a "web of formally
[cross-referenced]" definitions, bounds cross-checked against RFCs/NIST/papers).

**⚠ The contradiction, and it is to a doctrine, not to SELVAGE.** `breadstuffs/CLAUDE.md`
states: *"'TRANSLATION VALIDATION' between a Rust AIR and a spec is a LIE: TV needs
a formal SEMANTICS OF THE SOURCE, and **THERE IS NO SEMANTICS OF RUST**."* CatCrypt
§"Verified hax pipeline" says they "**ported a substantial part of the hax pipeline
in Lean (AST, denotational semantics, a number of compilation phases)**", where
"`ImpExpr` **models safe Rust**: references, mutable assignments, loops, …", in
order to shrink "the hax TCB to the front-end parser and the phases not yet
ported."

So: a denotational semantics for a safe-Rust *fragment* exists and is *in Lean*.
(Aeneas, Verus, Creusot and RustBelt are the wider PL-side instances; the PL lane
is checking them.) INFERENCE, mine, and I think it is the right restatement rather
than a retraction:

- The doctrine's **conclusion** is untouched: a Rust *case-test* asserting
  "the AIR accepts iff `applyTurn` holds" on examples proves nothing about all
  inputs, and calling it translation validation is still wrong.
- The doctrine's **stated reason** is now false as written. The honest form is:
  *"our Rust is not written in a semantics-carrying fragment and is not connected
  to one; until it is, there is no source semantics **for our code** to validate
  against."* That is a statement about us, which is repairable, rather than a
  statement about Rust, which is refutable — and it was refuted this year.
- It also names a **route we have not considered**: hax-compatible safe Rust +
  Lean extraction is an actual pipeline, shipping, at 110-artifact scale. It does
  not make a Rust-authored AIR acceptable (the AIR should still be *authored* in
  Lean and emitted). It does mean "Rust side is unreachable by proof" is no longer
  a fact we can assert.

**Second, separate value**: the *specification-confidence methodology* is
published, by someone who built 172 formalisations with AI in two months. Our own
vacuity-checking was ruled "tacit behavior, not a contribution" — CatCrypt §5 is
what it looks like when someone writes that behavior down anyway and defends it as
a contribution. Worth reading against our own PREFLIGHT.

---

### ★★★★ 9. Mergeable SNARGs without depth degradation — eprint 2026/662
Omer Paneth, Rafael Pass, *Verifiable Divide-and-Conquer: Proof-Merging Beyond the
log n-Barrier*, 5 April 2026 — **at the very edge of our mirror** (it holds up to
2026/777).

**Statement, verbatim**: "While mergeable proofs have been known for nearly two
decades … in **all existing approaches security degrades exponentially with the
number of recursive merges**. In this work, we overcome this barrier. Assuming …
(LWE), we construct a mergeable SNARG for P that supports an **unbounded
polynomial number of recursive merges**. The proof size grows only **linearly with
the depth of the merge tree, and is independent of its total size**."

**Touches**: SELVAGE §1's **accumulation depth composition** — the leg where we
hold a machine-checked proof that *the published theorem is false at a corner*,
with the repair. Paneth–Pass is the construction whose entire point is that the
depth degradation is *removable*, in the divide-and-conquer (tree-shaped, not
chain-shaped) setting.

**Not a contradiction** — our result is about a specific published composition
theorem's corner, and theirs is LWE-based and therefore not a drop-in for a
hash-based stack. **But** (INFERENCE) it resets the bar: "how does soundness
degrade with accumulation depth" now has a published answer of *linear in depth,
independent of size*, and any composition theorem we state should be positioned
against that rather than against the pre-2026 folklore. Also: the tree-merge
shape, not the chain, is the one that matches a **distributed** prover — which is
where our three workloads actually go.

**Distance to usable**: it is a feasibility construction under LWE. The *shape*
(merge tree, depth-linear proof) is what to steal.

---

### ★★★ 10. ZODA — the sampled symbols **are** their own proof (eprint 2025/034)
Evans, Mohnblatt, Angeris. Not in `~/paperbin` (`grep -icE 'zoda|angeris'` → 0).

"**A slight modification to the encoding scheme for tensor codes allows sampled
rows and columns of this modified encoding to become proofs of their own
correctness**" — "essentially no incremental costs (in either computation or size)
beyond those of the tensor encoding itself", no trusted setup, plausibly PQ.

**Why it is here**: the brief asked for "commit-then-open arguments with unusual
structure", and this is the most unusual one in the corpus — the overhead of the
argument is *zero* because the argument and the object coincide. Read against our
thesis it is the limit case: **a boundary statement whose certificate is the
boundary itself.** INFERENCE, mine: the interesting question it raises for us is
whether any of our three workloads has an encoding with that property, i.e.
whether the *committed form* of a weight tensor or a ciphertext batch can be
chosen so that the audit sample is self-certifying. That is a genuinely new
question for the audit-sampling line and it is cheap to ask.

---

### ★★★ 11. Author over ℤ, instantiate mod p — eprint 2024/1548
Campanelli, Hall-Andersen, *Fully Succinct Arguments over the Integers from First
Principles*. Not in `~/paperbin`.

Arguments of knowledge for computations over the **infinite ring ℤ**, explicitly
motivated by "**field emulation and field 'switching'**"; the key technique is
**fingerprinting** (arithmetic hashing) to bootstrap from existing prime-field
systems, plus "a novel kind of polynomial commitment allowing queries to a
multivariate integer polynomial **modulo an arbitrary prime p**".

**Touches** §4 open question 3 and the measured ~3× base→extension cliff. This is
the *third* independent answer to value-ring polymorphism in this sweep, and the
three are genuinely different:
- **2022/587** (Soria-Vazquez): find the minimal algebraic axioms; keep the
  protocol, swap the ring. → tells us the **typeclass constraints**.
- **PODS 2007** (Green et al.): emit into the **free object**, evaluate by
  homomorphism. → tells us the **shape of the emitted AIR**.
- **2024/1548** (Campanelli–Hall-Andersen): author over **ℤ**, reduce mod `p` at
  commitment/query time. → tells us **when the ring can be chosen late**, and
  supplies a PCS that supports it.
None of the three is in our notes.

---

### ★★ 12. Also catalogued, not in `~/paperbin`
- **2026/284** *Knowledge Soundness of Polynomial Commitments*; **2026/335**
  *Sumcheck-based zkSNARKs are Non-Malleable* — both land on the PCS seam
  (§4 open question 2) and are 2026-fresh.
- **2025/611** *Proving CPU Executions in Small Space* and **2024/1970** *Scribe:
  Low-memory SNARKs via Read-Write Streaming* — prover **space** as the resource,
  which our levers list does not contain at all.
- **2024/979** *Volatile and Persistent Memory for zkSNARKs*, **2024/1605**
  *Nebula: Efficient read-write memory* — the memory-shape lever (§3 ambition 2's
  "~80×") has a live literature we have one note on.

### Corpus limit, stated
`2026/1127` (the ring-hash open problem cited in SELVAGE §5.6) is **outside this
mirror**, which stops at 2026/777. No absence claim in this note covers late-2026
eprint.

---

## Batch 4 — cross-lane, and one bound I re-read myself

The complexity sweep is in `notes/inspiration-sweep-cc.md` (615 lines, 21 PDFs
under `~/paperbin/cc-*`); the PL/verification sweep is in
`notes/inspiration-sweep-pl.md`. Both are summarized in the handoff; two items
from them belong here because they bear directly on §2's thesis.

### The one that most nearly contradicts the boundary thesis, verified at source
**Dell–van Melkebeek, ECCC TR10-038**, `~/paperbin/cc-dell-vanmelkebeek-*.txt`.
I re-read the statements rather than relaying them.

- **Cost model, verbatim**: "The first player is given the input `x` and has to
  run in time polynomial in the length of the input; the second player is
  computationally unbounded but is not given any part of `x`. … **The cost of the
  protocol is the number of bits of communication from the first player to the
  second player.** … the bits sent by the oracle **do not contribute** towards the
  cost."
- **Theorem 1**: "Let `d ≥ 3` … If `coNP ⊄ NP/poly`, there is **no protocol of
  cost `O(n^{d−ε})`** to decide whether an n-variable d-CNF formula is
  satisfiable, even when the first player is conondeterministic."
- **Corollary 1**: no polynomial-time reduction from d-SAT making `O(n^b)` queries
  of bitlength `O(n^c)` **with `b + c < d`**.
- **Corollary 2**: d-SAT has no PCP of **bitlength `O(n^{d−ε})`** in the number of
  variables `n`.

**Scope, and it matters** (INFERENCE, mine — this is my correction to how the
result should be quoted): the parameter `n` is the **variable count** and `n^d` is
the **clause count**, so this is exactly "you cannot compress the interior of a
*generic* NP relation down toward its boundary, non-interactively." It is **not**
a bound on structured relations: a bilinear form's boundary genuinely is `n²`
(Freivalds, unconditionally). So it does not contradict §2. What it *does* is
delimit the boundary-statement compiler: **there is no generic pre-pass that makes
an arbitrary relation's statement smaller.** The compiler must exploit structure,
per family, which is precisely what the Dumas–Kaltofen catalogue does by hand and
what Distiller does by refinement. And it says such a pass must be **redeemed
interactively**, never precomputed.

### Rational proofs — in our corpus, unread
`~/paperbin/rational-proofs-2017-270.pdf` and `rational-sumchecks-2015-1058.pdf`
are already ours. `grep -rli 'rational proof' ~/dev/zkml-research/` → **0**. The
economics half of our audit theorem — priced refusal, and "priced refusal forces
`q ≤ 0`" — has a formal literature (Azar–Micali rational proofs, rational
arguments, rational sumchecks) that we hold and have never opened. Cheap.

---

## Synthesis — three convergences and three contradictions

Three lanes swept three disjoint literatures (IACR eprint full text; arXiv
cs.CC + ECCC + classic STOC/FOCS; arXiv cs.PL/cs.LO + POPL/PLDI/ITP). They were
not told about each other. They converged three times, which is the strongest
signal in this note.

### Convergence 1 — **the answer to value-ring polymorphism is "semiring", and it is three-times-independently discovered**
- **Database theory, 2007** (this lane): evaluation transports along a value-ring
  change **iff** the map is a homomorphism (GKT Prop. 3.5), and the right emitted
  object is the **free** one, with each concrete ring a valuation (Thm. 4.3).
- **PL, PLDI 2023** (PL lane): Kovach–Kjolstad, *Correct Compilation of Semiring
  Contractions* — a compiler **proved in Lean 4**, **parametric in the semiring**,
  same code covering sparse tensor algebra, relational algebra and shortest paths
  by swapping the semiring, in **~540 lines of Lean**.
- **Cryptology, 2022** (this lane): Soria-Vazquez — doubly-efficient IPs need
  *"not much algebraic structure"*, enabling *"agile proof systems where the
  black-box choice of the underlying ring can be easily switched through the
  software life cycle."*

§4 open question 3 is the one all three answer. **The action is not "invent
value-ring polymorphism"; it is "emit into the free object and let the value ring
be a homomorphism", and there is a 540-line Lean 4 precedent.**

### Convergence 2 — **our authoring discipline has a name, and a 2007 instance**
- **Proof-producing synthesis** (Slind–Owens–Iyoda–Gordon, FAC 2007; PL lane): a
  HOL4 compiler that takes `f` and *automatically produces the theorem*
  `⊢ C implements f`, composably, with a trusted pretty-printer at the boundary.
  That is Selvage's emit path, in the circuit domain, twenty years ago.
- **Relational compilation / Rupicola** (PLDI 2022; PL lane) — "soundly bridges
  the gap from shallowly embedded programs to deeply embedded executable code",
  extraction as proof search.
- **Distiller** (S&P 2023; this lane) — the *statement-choice* half.
- **Functorial arithmetization** (eprint 2022/777; this lane) — the *categorical*
  half.
- And the naming rule the PL lane extracted (Hupel–Nipkow): emitting one AIR with
  an accompanying theorem is **certifying**; a theorem about `emit : Spec → AIR`
  **for all specs** is **verified**. Most of what we have is the former.

### Convergence 3 — **the cost of a boundary statement is a conserved PRODUCT**
Four complexity literatures that do not cite each other (CC lane):
`b + c ≥ d` (Dell–van Melkebeek), `queries × communication ≈ n` (RVW IPPs),
`space × help = Ω(n²)` (CCMTV streaming), `proof-length × queries ≈ n` (MAPs).
A boundary-statement compiler whose cost functional is a single scalar will
happily trade along a proved invariant and report a win. **The functional should
be a product, or an exponent sum.**

### The three contradictions, ranked
1. **§5 innovation 3 is not open.** "Nobody has turned [boundary choice] into a
   discipline" — Distiller did, at S&P 2023, with provable safety. What is open is
   the **cost theory** (which abstraction is cheapest) and the **Lean-side**
   instantiation, and Dell–van Melkebeek Cor. 1/2 says the answer must be
   per-structure rather than generic.
2. **§4.3 / §5.4's "must be designed in from day one" is not supported.**
   Hierarchy Builder (Cohen–Sakaguchi–Tassi) exists to evolve algebraic hierarchies
   *"without breaking user code"*, including splitting a structure in two, and
   MathComp completed exactly that retrofit (PL lane). Combined with GKT Prop 3.5,
   the true statement is narrower: **the retrofit is cheap iff constraints consume
   the ring through an interface, and ruinous iff `Felt` leaked into every
   statement.** That is a check we can run today, not a deadline.
3. **"There is no semantics of Rust" is false as written.** eprint 2026/604
   (CatCrypt) ports "the hax pipeline in Lean (AST, **denotational semantics**,
   a number of compilation phases)" with `ImpExpr` modelling safe Rust. The
   doctrine's conclusion survives; its stated reason does not.

### If only one thing is done with this note
**Port one Dumas–Kaltofen certificate through Selvage's compilation layer.** They
have the optimal boundary statements for linear algebra and compile them with
Fiat–Shamir *as a heuristic*; we have the RBR→FS compiler theorem, state
restoration, and attained bounds, and no statements worth the machinery. The two
halves have never met, the gap is a port rather than a campaign, and it lands
directly on the ML workload.

---

### Housekeeping — why some `~/paperbin` entries are `.txt`-only
`eprint.iacr.org` returned **429 Too Many Requests** for every PDF fetch this
session (11/11, even at a 12 s spacing), and it returns the 429 page **as the
requested filename** — an HTML file with a `.pdf` extension, i.e. a refusal that
renders as the expected artifact. All such files were deleted rather than left in
`paperbin`. The eprint items in this note are therefore filed as **full text
copied from the local mirror**, which is what a future `rg ~/paperbin` needs
anyway; the arXiv/HAL/ACM items have both `.pdf` and `.txt`.
