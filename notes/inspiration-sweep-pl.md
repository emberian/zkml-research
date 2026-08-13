# Inspiration sweep: the PL / logic / verification literature next to Selvage

Lane: literature scouting, PL side only (cs.PL / cs.LO / cs.SE, POPL/PLDI/ICFP/CAV/ITP/CPP,
verified-compilation community). Date: 2026-08-13.

## Corpus and instrument (read this before trusting any "absent")

- **Instrument:** Google-backed web search (title/abstract/full-text mix), plus targeted
  `WebFetch` of the actual PDFs listed below. I did **not** rely on the arXiv API `all:`
  field, which is metadata-only; where a claim rests on search-hit-absence I say so
  explicitly and mark it WEAK.
- **Local corpus checked first:** `~/paperbin` (1528 files) grepped for
  `circ|r1cs|plonk|air|arithmetiz|constraint`, `compil|compcert|translation|certif|pcc`,
  `coq|lean|isabelle|dafny|fstar|hoare|relational|iris|refinement|denotation|semantic`,
  `halide|tvm|tensor|exo|atl|dsl|staged|metaprog`, `popl|pldi|icfp|cav|itp|oopsla`.
  Already held: `coda-refinement-types-zk-circuits.pdf`,
  `paper-veridise-qed2-underconstrained-pldi2023.pdf`,
  `qed2-picus-underconstrained-circom.pdf`,
  `stwo-air-lean-soundness-avigad-starkware-2606.04311.pdf`,
  `verifying-jolt-lookup-semantics-acl2-2024-1841.pdf`, `vcvio-lean*.pdf`,
  `grey-blog-zksecurity-clean-verified-zkvms.txt`.
  **Not held before this sweep:** CirC, the CAV'23 field-blaster, PFCS/ACL2, Rupicola,
  Myreen–Owens, Necula's thesis, Etch/indexed-streams.
- **eprint.iacr.org was 429-rate-limiting** this box during the sweep (other lanes). PDFs
  were pulled from publisher/author mirrors where possible; two are noted as not-fetched.

---

## Q1. The PL name for "the emitted artifact is what the theorem quantifies over"

**Short answer: there are three distinct names and they are NOT synonyms.** The one that
matches Selvage most closely is **proof-producing (relational) compilation / synthesis**,
with **certifying compilation** as the older umbrella and **translation validation** as an
explicitly *different* thing that our instinct about is correct.

### 1a. Proof-producing synthesis / translation — Myreen & Owens (ICFP 2012)

`~/paperbin/myreen-owens-proof-producing-synthesis-ml-icfp2012.pdf`
Magnus O. Myreen, Scott Owens, *Proof-Producing Synthesis of ML from Higher-Order Logic*,
ICFP 2012. Journal version: *Proof-producing translation of higher-order logic into pure and
stateful ML*, JFP 24(2–3), 2014.
<https://cakeml.org/icfp12/icfp12-myreen-owens.pdf>

Their framing of the problem is nearly verbatim ours, from the abstract:

> "to efficiently run these programs, they must be converted (or 'extracted') to functional
> programs in a programming language such as ML or Haskell. With current techniques, **this
> step, which must be trusted, relates similar looking objects that have very different
> semantic definitions**, such as the set-theoretic model of a logic and the operational
> semantics of a programming language."

> "Given a functional program expressed in higher-order logic, our technique provides the
> corresponding program for a functional language defined with an operational semantics,
> and it **provides a mechanically checked theorem relating the two**."

This is the exact discipline: the tool *emits* a deeply-embedded artifact **and** a
certificate theorem in the same run, so the theorem is about the emitted object, not about a
model that someone re-implements. The community phrase for it is **"proof-producing
translation from shallow to deep embedding"** — which is also the direct answer to the
"shallow-to-deep reification" candidate in the brief: the reification is *proof-producing*,
that is the whole content.

**What it guarantees:** a refinement/certificate theorem `f_HOL ≈ prog_CakeML` for the
specific emitted program, per emission. **What it does not:** anything about programs the
translator refuses; the translator is a tactic, not a total verified function, so a
translation failure is a failure, not an unsoundness.

### 1b. Relational compilation — Pit-Claudel et al. (PLDI 2022, "Rupicola")

`~/paperbin/pitclaudel-relational-compilation-rupicola-pldi2022.pdf`
Clément Pit-Claudel, Jade Philipoom, Dustin Jamner, Andres Erbsen, Adam Chlipala,
*Relational compilation for performance-critical applications: extensible proof-producing
translation of functional models into low-level code*, PLDI 2022.
<https://jamner.net/papers/rupicola-PLDI22.pdf> · DOI 10.1145/3519939.3523706

**This is the best single name for what we are doing.** The paper's own framing:

> "running [ITP-verified functional programs] required either **extracting to a similar
> language in an unverified but automated way**, or **proving equivalence with a deeply
> embedded implementation in a verified but manual way**."

and the contribution: recast extraction **as a proof-search problem** to derive
correct-by-construction low-level code, with **sound extensibility** — you add compilation
lemmas, and the compiler is "the set of lemmas you have proved". Selvage's `emit` path is
the same shape, and *"relational compilation"* is the term to use in a paper.

INFERENCE: the extensibility point is the load-bearing one for us. Rupicola's design answer
to "the compiler doesn't know how to emit my gadget" is *prove a new relational lemma*, not
*patch the compiler*. That maps onto per-gadget AIR emission directly.

### 1c. Certifying compilation / PCC — Necula (CMU-CS-98-154)

`~/paperbin/necula-compiling-with-proofs-thesis-cmu-1998.pdf`
George C. Necula, *Compiling with Proofs*, PhD thesis, CMU, 1998.
<https://www.cs.cmu.edu/~rwh/students/necula.pdf>

The crucial distinction, and it cuts in our favour:

- **PCC / certifying compilation does NOT establish source→target semantic preservation.**
  It produces independently-checkable evidence that *the emitted code* satisfies a
  behavioural specification (type safety, memory safety). The theorem's subject is the
  emitted artifact; there is no obligation to relate it to a source at all.
- **Verified compilation (CompCert)** is the opposite: one theorem, once, about *all*
  compilations, and it is squarely a source→target *semantic preservation* theorem — which
  therefore *requires a formal semantics of the source*.

So: if the object we care about is "the emitted AIR accepts exactly the traces the spec
permits", we are in the **certifying / PCC** family (theorem about the artifact), delivered
by the **proof-producing-compilation** mechanism (1a/1b), and we are *not* doing verified
compilation in the CompCert sense, because we have no separate source language to preserve
the semantics *of*.

### 1d. "Translation validation without a source semantics is a lie" — the literature agrees

Translation validation is Pnueli–Siegel–Singerman (TACAS 1998) and Necula (PLDI 2000): after
each compiler run, a *validator* checks that the target refines the source **for that run**.
The refinement relation is between two formal semantics; there is no version of the technique
that does without a source semantics — the validator's proof obligation is literally stated
over the source's transition system. Confirming datum from the credible-compilation
literature (Rinard, MIT): credible compilation is described in the surveys as being
distinguished from translation validation precisely by "**not** being based on an explicitly
formalized semantics" — i.e. the field treats *having a formalized source semantics* as the
defining property of TV, and gives a different name to the thing that lacks one.

⇒ Our house rule ("TV between a Rust AIR and a spec is a lie; there is no semantics of Rust")
is **the standard reading**, not a local eccentricity. The honest name for a Rust-side
case-test suite is *differential testing* or at most *credible compilation without a
formalized semantics*; it is never translation validation.

### 1e. Verified extraction — and why the extraction gap is real, not folklore

Yannick Forster, Matthieu Sozeau, Nicolas Tabareau, *Verified Extraction from Coq to OCaml*,
PACMPL 8(PLDI), 2024, pp. 52–75. <https://pldi24.sigplan.org/details/pldi-2024-papers/3/>
(PDF blocked by HAL's bot-check during the sweep; ACM DOI 10.1145/3656379; repo
<https://github.com/MetaRocq/rocq-verified-extraction>.)

The paper's premise is the *reason* to prefer emitting-with-a-theorem: in ordinary Coq,
**extraction is in the TCB**, alongside the kernel and the downstream compiler. Their fix
targets Malfunction (OCaml's internal Lambda) with a MetaCoq-verified pipeline.

This is the clean citation for "extraction ≠ our discipline": vanilla extraction gives you a
program with **no theorem about it**; the theorem you have is about the Gallina term you
extracted *from*.

### 1f. The community states the verified/certifying dichotomy in *our* setting

`~/paperbin/hupel-nipkow-verified-compiler-isabelle-to-cakeml-esop2018.pdf`
Lars Hupel, Tobias Nipkow, *A Verified Compiler from Isabelle/HOL to CakeML*, ESOP 2018,
LNCS 10801, 999–1026. <https://www21.in.tum.de/~nipkow/pubs/esop18.pdf>

They combine "a simple **proof-producing** translation of recursion equations in Isabelle/HOL
into a **deeply embedded term language**" with a fully verified compilation chain to CakeML,
and describe the result as

> "the first **verified** (as opposed to **certifying**) compiler from function definitions in
> a logic into a programming language"

— naming HOL4's proof-producing code generator as the *certifying* alternative. This is the
sentence to quote when we have to say which box Selvage is in. A one-emission-at-a-time
certificate theorem = **certifying**. A once-and-for-all theorem about the emitter itself =
**verified**. They are different products and the second is strictly more work.

INFERENCE, and worth a decision: Selvage should say which one it is per component. Emitting
a specific AIR with a specific accompanying theorem is *certifying*. A theorem about
`emit : Spec → AIR` for all specs is *verified*. Most of what we have is the former; claiming
the latter without the ∀-spec theorem would be exactly the overclaim the repo's audit notes
already hunt.

### 1g. ⚑ The 2006/2007 ancestor, and it is in the *circuit* domain

`~/paperbin/iyoda-translating-hol-functions-to-hardware-thesis-2007.pdf`
Juliano Iyoda, *Translating HOL functions to hardware*, PhD dissertation / Cambridge
UCAM-CL-TR-682, 2007. <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-682.pdf>
Paper version: Konrad Slind, Scott Owens, Juliano Iyoda, Mike Gordon, *Proof producing
synthesis of arithmetic and cryptographic hardware*, Formal Aspects of Computing 19(3),
343–362, 2007.

The thesis abstract gives the theorem shape verbatim:

> "The compiler takes a function `f` as argument and automatically produces the theorem
> **⊢ C implements f** where `C` is a circuit and `implements` is a correctness relation
> between a circuit and a function. We achieve full mechanisation of proofs by defining
> theorems which are **composable**. The correctness of a circuit can be mechanically
> determined by the correctness of its sub-circuits."

> "A **pretty-printer** translates netlists described in higher-order logic to structural
> Verilog."

This is Selvage's exact architecture, twenty years early, for synchronous hardware:
- the emitted circuit `C` is a **term in the logic**, and it is the theorem's subject;
- the correctness relation is a *named* relation, not a test;
- composition is by composing sub-circuit theorems (cf. PFCS in §2b);
- the boundary to the real world is a **trusted pretty-printer** to Verilog — same boundary as
  Fiat-Crypto's C printer (§3b).

The honest scaling caveat is in the abstract too: "Although this approach does not scale to
industrial-sized applications **yet**" (2006, multiplier + a small microcomputer). Twenty years
of proof-assistant automation later, and with an AIR being a far smaller object than a
microcomputer netlist, that caveat is the thing our project is betting has expired.

⇒ **Answer to "surely this has a name": yes — proof-producing synthesis / relational
compilation, and in the circuit domain the canonical citation is Slind–Owens–Iyoda–Gordon 2007.**

### Name table (use these words precisely)

| Name | Theorem's subject | Needs source semantics? | Per-run or once? |
|---|---|---|---|
| Verified compiler (CompCert) | source⇝target relation | **yes** | once, all runs |
| Translation validation (Pnueli, Necula) | source⇝target relation | **yes** | per run |
| Certifying compiler / PCC (Necula) | **the emitted artifact** vs a spec | no | per run, checkable |
| Foundational PCC (Appel) | the emitted artifact, down to machine semantics + logic | no (target semantics only) | per run |
| Proof-producing synthesis (Myreen–Owens) | **the emitted artifact** ≈ the HOL function | n/a (source *is* the logic) | per run |
| Relational compilation (Rupicola) | **the emitted artifact** ≈ the functional model | n/a (source *is* the logic) | per run, extensible |
| Proof-producing HW synthesis (Slind et al. 2007) | **the emitted circuit** `⊢ C implements f` | n/a (source *is* the logic) | per run, composable |
| Extraction (Coq/Lean, unverified) | *nothing* — trusted step | n/a | never |
| Verified extraction (Forster et al.) | emitted λ-term ≈ Gallina term | n/a | once, all runs |

The row we live in is **proof-producing / relational compilation**, and the reason "source
semantics" is n/a for us is the same reason it is n/a for CakeML's translator: **the source
is the ambient logic**, so there is nothing to axiomatize.

---

## Q2. Verified compilation of arithmetic circuits / constraint systems

> **Read §2f first** — it is the decisive find of the whole sweep.

### 2a. CirC + the CAV'23 field-blaster — the closest thing to a *verified circuit compiler*

- Alex Ozdemir, Fraser Brown, Riad S. Wahby, *CirC: Compiler Infrastructure for Proof
  Systems, Software Verification, and More*, IEEE S&P 2022.
  `~/paperbin/ozdemir-circ-compiler-infrastructure-sp2022.pdf`
- Alex Ozdemir, Riad S. Wahby, Fraser Brown, Clark Barrett, *Bounded Verification for
  Finite-Field-Blasting (In a Compiler for Zero Knowledge Proofs)*, CAV 2023; extended in
  Formal Methods in System Design, 2025 (DOI 10.1007/s10703-025-00476-3).
  ePrint 2023/778 · <https://link.springer.com/content/pdf/10.1007/978-3-031-37709-9_8.pdf>

What CAV'23 actually does, in their own decomposition: **define correctness for a
field-blaster and for a ZKP compiler; give the field-blaster as a set of *encoding rules*
with per-rule verification conditions; prove that if the VCs hold the field-blaster is
correct; discharge *bounded* versions of the VCs with SMT (their finite-field SMT solver);
find four bugs.**

Read the qualifier: **bounded**. The VCs are discharged for bounded bit-widths, by an SMT
solver, not for all inputs in a proof assistant. So the guarantee is *"no counterexample
below the bound, for the rules"*, plus a hand proof that rule-correctness composes.

Placement against our position: this is the **rule-level** analogue of relational
compilation — the compiler pass is justified rule-by-rule and the emitted field constraints
are the objects the rules talk about. It is the strongest prior art for "the emitted
constraint system is the theorem's subject" in ZK, and it is *not* in a proof assistant.

Companion: *Satisfiability Modulo Finite Fields*, Ozdemir, Kremer, Tinelli, Barrett, CAV
2023, and the SMT-LIB theory of finite fields (arXiv 2407.21169) — infrastructure we would
inherit if we ever wanted an SMT escape hatch under a Lean-authored constraint.

### 2b. PFCS / ACL2 — compositional verification of the *emitted* R1CS (Kestrel)

`~/paperbin/coglio-formal-verification-zk-circuits-pfcs-acl2-2311.08858.pdf`
Alessandro Coglio, Eric McCarthy, Eric W. Smith, *Formal Verification of Zero-Knowledge
Circuits*, ACL2 Workshop 2023 (EPTCS), arXiv:2311.08858. Extended: *Compositional Formal
Verification of Zero-Knowledge Circuits*, ePrint 2023/1278.
Project page: <https://www.kestrel.edu/research/fv-of-r1cs/>

Contributions: an ACL2 prime-field library; an ACL2 model of R1CS; the **Axe** toolkit to
"**lift** R1CS circuits into logic" and prove them equivalent to specs; and **PFCS (Prime
Field Constraint Systems)**, a formalism for *hierarchically structured* circuits with
compositional correctness — a gadget's theorem is proved from its sub-gadgets' theorems.

This is the **post-hoc** dual of Selvage: they take the R1CS that a real compiler
(Leo/Aleo, circom) emitted and prove *that artifact* against a spec. Same subject (the
emitted object), opposite direction (lift, not emit). PFCS's compositional gadget structure
is the piece worth stealing — it is the thing that makes gadget-level AIR theorems compose
without re-proving the whole system.

### 2c. Coda — refinement types for circuit authoring (we already hold it)

`~/paperbin/coda-refinement-types-zk-circuits.pdf` — Junrui Liu et al., IEEE S&P 2024.
Authoring language with refinement types; the *typing* discharges circuit correctness.
Closest to "author in a proof-carrying language", but the target is circom-style R1CS and
the guarantee is via a refinement type system + SMT, not a general-purpose logic.

### 2d. Picus / QED² — underconstrained-signal detection (we already hold both)

`~/paperbin/paper-veridise-qed2-underconstrained-pldi2023.pdf`,
`~/paperbin/qed2-picus-underconstrained-circom.pdf` — Pailoor et al., PLDI 2023.
Decides *uniqueness* of the witness (determinism of the constraint system) — a genuinely
different property from "matches a spec", and one we should be able to state as a theorem
rather than run as a tool. It is a **hyperproperty** (2-safety), which connects to Q4.

### 2e. Lean-side neighbours (the nearest competitors to Selvage as an authoring language)

- **Clean** (zkSecurity) — an *embedded* DSL for ZK circuits in Lean 4; `FormalCircuit`
  bundles `main`, `Spec`, `soundness`, `completeness`; recent work adds `Channel` for
  cross-table (multi-AIR) interactions, i.e. zkVM-scale composition.
  Local: `~/paperbin/grey-blog-zksecurity-clean-verified-zkvms.txt`,
  <https://blog.zksecurity.xyz/posts/clean/>.
  **Note the shape:** "it is just Lean, not a standalone DSL, no special compiler" — a
  monadic library. That is the same architectural bet Selvage makes.
- **zkLean** (Galois) — Lean DSL for ZK statements; supports R1CS, lookup tables, MLE-based
  lookups, RAM; ships an **extractor for the Jolt zkVM** that pulls Jolt's frontend
  constraints *into* zkLean, and LLZK (MLIR dialect for ZK circuits) frontends/backends so
  circom circuits can be imported. <https://github.com/GaloisInc/zkLean>
  Their stated TCB: "(1) zkLean's circuit semantics are correct and (2) Lean's core
  typechecker is sound." That first clause is the whole game — same clause we own.
- **Avigad/StarkWare Stwo AIR-in-Lean** — already held
  (`~/paperbin/stwo-air-lean-soundness-avigad-starkware-2606.04311.pdf`); see the existing
  `notes/avigad-stwo-verdict.md`.

---

### 2f. ⚑ THE DECISIVE FIND — Avigad et al. state our gap in their own trust section

**Paper 1.** Jeremy Avigad, Lior Goldberg, David Levit, Yoav Seginer, Alon Titelman, *A
Verified Algebraic Representation of Cairo Program Execution*, CPP 2022, arXiv:2109.14534.
`~/paperbin/avigad-verified-algebraic-representation-cairo-cpp2022-2109.14534.pdf`
Lean 3; verifies that **satisfiability of the deployed Cairo AIR implies** the machine
terminates as claimed (soundness direction only). Their §"What needs to be trusted?":

> "**The polynomials that are found in `constraints_autogen.lean` should match the polynomials
> used by the verifier.**"

That sentence is the entire argument for Selvage's discipline, written by the people with the
strongest claim in the field. The Lean file is *auto-generated from the constraint source* —
the arrow runs **artifact → Lean**, so the match between the Lean object and the deployed
object is an assumption, not a theorem. Selvage runs the arrow **Lean → artifact**, which
converts that assumption into a build-graph fact.

**Paper 2.** *Formal verification of the S-two AIR*, arXiv:2606.04311 (already held:
`~/paperbin/stwo-air-lean-soundness-avigad-starkware-2606.04311.pdf`; see
`notes/avigad-stwo-verdict.md`). In 2026, on the newer prover, they **explicitly consider and
reject** the lift-the-emitted-constraints strategy:

> "A strategy one might consider is to run the code, generate the polynomial constraints and
> messages, translate them to Lean, and reason about them there. **That was not feasible**,
> however. Not only is the encoding too large, but the raw list of polynomials lacks sufficient
> structure. In other words, **it is impossible to reason about the correctness of the
> constraints without reasoning about the code that generates them**: the reason the constraints
> guarantee the existence of computation traces is that the code was written for that purpose,
> and our soundness proof had to reflect that reasoning."

> "The strategy we adopted, therefore, was to **translate the relevant parts of the
> infrastructure code to Lean** and prove that the constraints and messages generated by the
> Lean code have the right properties. … We therefore had to be **strategic in choosing which
> aspects of the code to model in Lean and which aspects to trust.**"

Read that carefully. They independently derive **our premise** — *you must reason about the
generator, not the emitted constraint list* — and then, because the deployed generator is Rust,
the only move available to them is to **port the generator into Lean and trust the port**. Which
is precisely the twin structure `project-lean-must-be-the-implementation.md` forbids, arrived at
by the best team in the space for a good reason.

Selvage's thesis is the third option they did not have: **make the Lean generator the origin**,
so "the code that generates them" *is* the Lean code, and there is no port to be strategic about.
Their §"which aspects to trust" enumerates the residue — global lookup collection, the code that
arranges lookups into constraints — which in a Lean-origin design are objects, not assumptions.

INFERENCE (mine, and it is the paper-shaped claim): **the PL name for the move is inverting a
certifying-compilation arrow — Avigad et al. do post-hoc *lifting*, Selvage does relational
compilation.** No one in the ZK-AIR literature I found is doing the second. That is a real,
narrow, defensible novelty claim, and it does not require us to claim anything about soundness
bounds.

### 2g. AirScript (0xMiden) — our architecture, no theorem

<https://github.com/0xMiden/air-script> — a DSL for AIR constraints; pipeline
`.air` source → AST → MIR → **AirIR (AlgebraicGraph)** → codegen to **Winterfell Rust** and to
**ACE** (Miden VM assembly). I fetched the repo docs: **no formal semantics, no correctness
claim, no verification** ("alpha stage … has not been audited"); the docs say nothing about
field polymorphism or extension-field values.

This is the industrial statement of the same architecture we want, with the theorem missing —
the cleanest "here is the artifact class, here is what nobody proves about it" comparison, and
a plausible *target* if we ever want to emit into an existing ecosystem rather than our own.

## Q3. Polymorphic / ring-generic code generation with proofs

### 3a. Etch / indexed streams — a Lean-4-verified compiler generic over a **semiring**

`~/paperbin/kovach-indexed-streams-etch-lean-pldi2023.pdf`
Scott Kovach, Praneeth Kolichala, Tiancheng Gu, Fredrik Kjolstad, *Indexed Streams: A Formal
Intermediate Representation for Fused Contraction Programs*, PACMPL 7(PLDI) art. 154, 2023.
DOI 10.1145/3591268 · arXiv:2207.13291

Why it matters here: the contraction language is over a **positive/semiring algebra** (it
covers both sparse tensor algebra and relational algebra by *changing the semiring*), the
operator correctness is **proved in Lean**, and the compiler is **540 lines of Lean**
emitting C — roughly two orders of magnitude smaller than TACO. That is the existence proof
that value-ring polymorphism and a machine-checked emitter coexist, in *our* prover, at a
size we can read.

Follow-on: *A Mechanized Algebra of Verified Data Structures for Optimizing Sparse Tensor
Programs*, PACMPL 2025 (DOI 10.1145/3808261).

Caveat I checked: the Lean proof I could confirm from the paper is that the **indexed-stream
operational model is correct with respect to a functional (denotational) semantics**, and
that the stream *combinators* are correct. Whether the final Lean→C emission step carries a
theorem I did **not** verify (I read the abstract + §1–3 only). UNVERIFIED-BY-ME.

The arXiv version's title is even more on-point for us: **"Correct Compilation of Semiring
Contractions"** (arXiv:2207.13291).

### 3b. Fiat Cryptography — parametric in the prime, emitted code carries the proof

`~/paperbin/erbsen-fiat-crypto-simple-high-level-code-sp2019.pdf`
Andres Erbsen, Jade Philipoom, Jason Gross, Robert Sloan, Adam Chlipala, *Simple High-Level
Code for Cryptographic Arithmetic — With Proofs, Without Compromises*, IEEE S&P 2019.
<https://jasongross.github.io/papers/2019-fiat-crypto-ieee-sp.pdf> · <https://github.com/mit-plv/fiat-crypto>

Shape: high-level **templates proven correct in Coq**, *generic over the modulus and the limb
layout*, then **specialized to a particular prime by a certified partial evaluator**, emitting
a low-level AST that is pretty-printed as C. Deployed in BoringSSL / Chrome.

This is the closest existing thing to "value-ring-polymorphic authoring with proofs":
the correctness argument is written **once, for all primes**, and instantiation is a verified
compilation step rather than a re-authoring. Two precise facts from the paper:

> "the overall **trusted computing base also includes a simple pretty-printer** and the C
> language toolchain."

> "**Advantage of our work: small trusted code base.** Every past project we mentioned includes
> either an SMT solver or a computer-algebra system in the trusted code base. … We trust only
> the standard Coq theorem prover … and the (rather short, whiteboard-level) statements of the
> formal claims."

⇒ The theorem's subject is the **deeply-embedded low-level AST inside Coq**; serialization to
C text is trusted. That is *exactly* the boundary Selvage will have (Lean-side AIR object =
theorem's subject; the bytes handed to the prover = a short trusted serializer). It is the
right place to put the boundary, and there is a top-tier precedent for putting it there and
saying so out loud.

### 3c. ATL — verified tensor-program optimization (Coq), and what it is *not*

`~/paperbin/liu-atl-verified-tensor-program-optimization-popl2022.pdf`
Amanda Liu, Gilbert Louis Bernstein, Adam Chlipala, Jonathan Ragan-Kelley, *Verified
tensor-program optimization via high-level scheduling rewrites*, PACMPL 6(POPL), 2022.
DOI 10.1145/3498717

A Coq framework where Halide-style **scheduling** is a sequence of verified, semantics-
preserving **source-to-source rewrites** in a pure functional array language, reaching (and
exceeding) Halide's schedule space. Useful as the model for "optimizing the emitted object is
a chain of proved rewrites", which is what an AIR optimizer would need.
Its genericity is over array shapes/index expressions, **not** over the scalar ring — so it is
weaker than Etch for Q3. Its value to us is the *rewrite-as-theorem* discipline.

### 3d. The negative result for "verified staged metaprogramming"

MetaML/MetaOCaml-style multi-stage programming gives **type- and scope-safety of the generated
code** — "the generated code always compiles" — and nothing about semantic correctness. I found
no MetaOCaml-lineage system whose guarantee is functional correctness of the generated program.
(Instrument: web search over the MetaOCaml bibliography + Kiselyov's page; WEAK-ish absence, but
the positive claims in that literature are uniformly about typing, not correctness.)
⇒ "Verified staged metaprogramming" in the sense we want **is** relational compilation (1b) or
proof-producing synthesis (1a); the staging community solved a different problem.

---

## Q4. Relational / hyperproperty logics for "accepts exactly what the semantics permits"

### 4a. Hyper Hoare Logic — Dardinier & Müller, PLDI 2024

<https://dardinier.me/papers/PLDI24_HHL.pdf> · arXiv:2301.10037 (extended)

Assertions range over **sets of states**, so the logic reasons about both the *absence* and
the *existence* of (combinations of) executions — it proves **and disproves** hyperproperties
in one system, and it is **sound and complete**, mechanized in Isabelle/HOL. Tool: *Hypra*
(Dardinier, Li, Müller).

Why this is the right shelf for us: "the emitted AIR accepts **exactly** the traces the
semantics permits" is a conjunction of
(i) soundness — ∀ satisfying assignment, the trace is permitted (a 1-safety/2-safety-ish
∀-property), and
(ii) completeness — ∀ permitted trace, **∃** a satisfying assignment (a ∀∃ hyperproperty).
Clause (ii) is exactly the shape ordinary Hoare/k-safety logics *cannot* state, and is the
one that a "the constraints accept" test can never establish. HHL states both. Picus/QED²'s
uniqueness property (2d) is a third clause, 2-safety.

INFERENCE: this gives us a precise vocabulary for the Selvage circuit contract —
*soundness = ∀-part, completeness = ∀∃-part, determinism = 2-safety part* — and a citation
for why the ∀∃ part is the hard one.

### 4b. RHLE — modular deductive verification of relational ∀∃ properties

`~/paperbin/dickerson-rhle-forall-exists-relational-aplas2022.pdf`
Robert Dickerson, Qianchuan Ye, Michael K. Zhang, Benjamin Delaware, *RHLE: Modular Deductive
Verification of Relational ∀∃ Properties*, APLAS 2022 (LNCS 13658); arXiv:2002.02904.
<https://robd.io/papers/rhle.pdf>

RHLE names the class directly: ∀∃ properties assert that *for all* executions of one collection
of programs, *there exist* executions of another exhibiting the intended behaviour — and the
paper explicitly lists **refinement** and noninterference as the motivating instances.
"AIR completeness" (every semantically-permitted trace has a satisfying assignment) is a
refinement in exactly this sense.

Relation to 4a: Hyper Hoare Logic subsumes more (it can also *disprove*), RHLE is the modular
deductive-verification framing with a tool. Both are worth reading before we write down the
Selvage circuit contract, because the ∀∃ clause is the one our current statements are most
likely to have quietly dropped.

### 4c. Not applicable, and worth saying

Iris-based relational logics (ReLoC and kin) and product-program constructions target
contextual refinement of *programs with state*. An AIR is a first-order constraint predicate
over a trace table — no heap, no concurrency, no contexts. The heavy relational machinery buys
us nothing; the *vocabulary* (∀∃ refinement, 2-safety) is the transferable part.
This is my judgement from the shape of the artifact, not from a survey. INFERENCE.

---

## Q5. Where the literature pushes back on us

### 5a. On "emitting from Lean beats model + differential test" — mostly SUPPORTED, with one real correction

**Supporting, and strongly:**

1. Avigad et al.'s own trust clause (§2b′): the port/transcription is the residual assumption
   in the state of the art, and it is an assumption *because* the arrow runs artifact→Lean.
2. Forster/Sozeau/Tabareau (§1e): unverified extraction is *in the TCB* — the discipline of
   "there is a theorem about the thing that ships" is a recognised, PLDI-award-track goal.
3. zkLean's own stated TCB reduces to "(1) zkLean's circuit semantics are correct and (2) Lean's
   kernel is sound" — i.e. everyone in this space agrees the *semantics of the emitted object*
   is the irreducible assumption. Emitting removes the *port*; it does not remove the semantics.

**The correction — and it is a real one.** Emitting from Lean makes the theorem be about the
emitted syntax. It does **not** establish that our Lean-side *semantics* of that syntax matches
what the deployed prover/verifier actually computes on it. That residual obligation is exactly
the same kind of obligation that ISA-semantics projects carry, and the PL community's only
answer to it is **differential testing against the real implementation**: Sail's ARMv8 models
are validated against the ARM Architecture Validation Suite (Armstrong et al., POPL 2019,
<https://www.cl.cam.ac.uk/~pes20/sail/sail-popl2019.pdf>), and the K x86-64 semantics
(Dasgupta, Park, Kasampalis, Adve, Roşu, PLDI 2019) is validated by executing tens of thousands
of instruction tests against real hardware.

⇒ So: model+differential-testing does not go away — **it moves down one level**, from the
artifact (where emission kills it) to the *semantics of the artifact* (where nothing kills it).
A Selvage that emits and then never differentially tests its `air_accepts` semantics against the
real evaluator has relocated the gap, not closed it. INFERENCE, but the ISA-semantics precedent
is exact: those projects are *the* case where a formal semantics is the product, and they all
ship a validation suite.

### 5b. On "value-ring polymorphism must be designed in from day one" — CONTRADICTED

The prover community has a well-developed, published answer to retrofitting an algebraic
hierarchy onto an existing library **without breaking clients**:

- Cyril Cohen, Kazuhiko Sakaguchi, Enrico Tassi, *Hierarchy Builder: Algebraic hierarchies Made
  Easy in Coq with Elpi (System Description)*, FSCD 2020, LIPIcs 167:34.
  <https://drops.dagstuhl.de/storage/00lipics/lipics-vol167-fscd2020/LIPIcs.FSCD.2020.34/LIPIcs.FSCD.2020.34.pdf>
  Stated goal, verbatim: "a high level language to build hierarchies of algebraic structures and
  **make these hierarchies evolve without breaking user code**". The mechanism is the
  **factory / builder / abbreviation** triple: the developer publishes an interface and supplies
  compatibility code behind it, so "even a simple refactoring such as **splitting a structure
  into two simpler ones**" becomes tractable.
- *Porting the Mathematical Components library to Hierarchy Builder*, Coq Workshop 2021 —
  an executed, large-scale retrofit of exactly this kind on one of the biggest verified libraries
  in existence. <https://coq-workshop.gitlab.io/2021/abstracts/Coq2021-01-02-mathcomp-hierarchy-builder.pdf>

⇒ **"Retrofit the ring parameter later" is a solved engineering problem in this community, with
a tool, a technique, and a completed case study on MathComp.** The honest statement of our
belief is narrower and still probably true: *retrofitting is cheap when the abstraction is a
structure-with-operations that clients consume through an interface, and expensive when the
concrete ring leaked into every statement.* That is a discipline question (do constraints
mention `Felt` or a `[CommRing R]` parameter), not a from-day-one question.

INFERENCE: for Lean specifically the analogue is Mathlib's typeclass hierarchy plus
`variable {R : Type*} [CommRing R]` at the top of the authoring module. If a Selvage design
document says "we cannot retrofit base-vs-extension-field polymorphism", that claim now has to
answer Hierarchy Builder. Given `CLAUDE.md`'s rule about cost-estimate-becoming-constraint, this
is exactly the shape of belief that ought to be re-priced rather than inherited.

### 5c. What nobody contradicted

I found **no** PL result arguing that a model+differential-test discipline yields a guarantee
comparable to a theorem about the emitted artifact. The literature is unanimous in the other
direction; the only nuance is 5a's relocation argument.

---

## What I did NOT find (and how hard I looked)

- **A verified/certifying compiler that emits AIR (not R1CS) with a theorem about the emitted
  AIR object.** Instrument: web search across `arxiv.org`, `dl.acm.org`, `eprint.iacr.org`,
  conference sites, plus repo fetches; terms combining {verified, certified, proof-producing,
  correct-by-construction} × {AIR, algebraic intermediate representation, STARK constraints,
  trace constraints} × {Lean, Coq, Isabelle}. Everything returned was either (i) post-hoc
  verification of a *deployed* AIR (Avigad et al. ×2), (ii) an unverified emitting DSL
  (AirScript), or (iii) an embedded authoring DSL whose emission story is not the theorem
  (Clean, zkLean). **This is a search-hit absence, so it is MEDIUM evidence, not proof** — but
  it is not arXiv-API-metadata-only, and the ZK-formal-methods corpus is small enough that I
  would expect a hit.
- **Value-ring-polymorphic constraint authoring with proofs.** Nothing in ZK. The nearest
  neighbours are outside ZK entirely (Etch/semirings, Fiat-Crypto/primes). **This gap looks
  real and looks like the most novel axis of our position.** MEDIUM evidence, same caveat.
- **The CAV'23 field-blasting PDF itself.** `eprint.iacr.org` returned HTTP 429 to this box
  throughout the sweep and the Springer mirror served HTML. The claims in §2a are from the
  paper's own abstract/contribution list as surfaced in search, **not from reading the PDF** —
  treat the word "bounded" as load-bearing but re-read before citing. TODO: refetch
  <https://eprint.iacr.org/2023/778.pdf>.
- **The Forster et al. PLDI'24 PDF.** HAL is behind an Anubis bot-check. Claims in §1e are from
  the abstract and the project README. TODO: refetch.

---

## Reading order if only four things get read

1. **Slind–Owens–Iyoda–Gordon 2007 / Iyoda's thesis** — `⊢ C implements f`. Our architecture,
   in the circuit domain, with the composability story and the trusted-pretty-printer boundary
   already worked out. Read the abstract and §on composability first.
2. **Rupicola / relational compilation** (PLDI'22) — this is the modern name and the
   extensibility design (compilation lemmas, incomplete-by-design compiler).
3. **The two Avigad AIR papers' trust sections** (CPP'22 §"What needs to be trusted?";
   arXiv:2606.04311 §2.4) — this is the gap we close, in their words.
4. **Etch / "Correct Compilation of Semiring Contractions"** — existence proof that a
   ring-polymorphic, Lean-verified emitter fits in 540 lines.

## Files added to `~/paperbin` by this sweep

```
iyoda-translating-hol-functions-to-hardware-thesis-2007.pdf
myreen-owens-proof-producing-synthesis-ml-icfp2012.pdf
pitclaudel-relational-compilation-rupicola-pldi2022.pdf
hupel-nipkow-verified-compiler-isabelle-to-cakeml-esop2018.pdf
necula-compiling-with-proofs-thesis-cmu-1998.pdf
avigad-verified-algebraic-representation-cairo-cpp2022-2109.14534.pdf
coglio-formal-verification-zk-circuits-pfcs-acl2-2311.08858.pdf
kovach-indexed-streams-etch-lean-pldi2023.pdf        (= arXiv:2207.13291, "Correct Compilation of Semiring Contractions")
erbsen-fiat-crypto-simple-high-level-code-sp2019.pdf
liu-atl-verified-tensor-program-optimization-popl2022.pdf
dardinier-mueller-hyper-hoare-logic-pldi2024.pdf
dickerson-rhle-forall-exists-relational-aplas2022.pdf
ozdemir-circ-SLIDES-not-paper-sp2022.pdf              (slide deck only — the paper PDF is still missing)
```
Not obtained (blocked): CAV'23 field-blasting (eprint 429), Forster et al. PLDI'24 (HAL
bot-check, ACM paywall-ish), the CirC S&P'22 paper proper.
