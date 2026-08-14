# Selvage: what is complete, at which boundary

Status: 2026-08-09.

Selvage is substantial machine-checked mathematics plus several real Lean-owned controllers. It is
not one deployed succinct ZK proof system. This document replaces earlier uses of “complete” that
collapsed ideal theorems, verifier gadgets, native experiments, and deployment into one label.

## Boundary legend

| Level | Meaning |
|---|---|
| **S** | semantic/formal carrier, theorem, or exact reduction interface |
| **A** | Lean-owned controller/admission over bytes or error |
| **P** | concrete cryptographic proof/security game and priced error |
| **D** | authenticated deployment and consumer cutover |
| **B** | reproducible matched-workload benchmark |

Current Selvage is strongest at **S**, has concrete **A** seams, has conditional **P** shapes, and has
not yet reached an end-to-end **P/D/B** proof-system claim.

## Machine-checked formal core — S

### Reed–Solomon, accumulation, and extraction

- constrained RS claims, same-word batching, cross-word affine folding, exact/UD soundness, and
  arbitrary-depth chain extraction are local Lean theorems;
- light-client, RBR, Fiat–Shamir, and grinding results hold at their stated oracle/commitment and
  rate interfaces;
- commitment/extraction examples make binding premises load-bearing rather than hiding them; and
- semantic history uses the same `AccClaim` carrier rather than a structural hash-chain lookalike.

This does not instantiate a concrete PCS, ROM, commitment, or succinct verifier.

### Sumcheck and derived arithmetization

- `Selvage/Sumcheck` and multilinear-extension modules prove the algebraic layer;
- `Compiler/Air` proves the circuit fold and executor readings agree;
- `AirFlatten` derives degree-≤2 gates with forced auxiliary wires;
- assurance modules retire linear and quadratic gate faces at their theorem interfaces; and
- `Compiler/Emit` produces first-order descriptor data with `emit_faithful`.

This proves what a descriptor means. It does not prove that Rust implements the descriptor or that
an external proof system soundly proves it.

### Multiplicative proximity and rate regimes

- the unique-decoding core and unconditional band `0 < δ < (1-ρ)/3` are proved;
- one threshold-halving round has at most one bad field challenge before a proved UD tail;
- committed coherent runtime-shaped query paths and their miss price are formalized; and
- the rate-1/2 `3/10 → 3/20 < 1/6` specialization is checked.

Concrete Merkle CR/binding and one-execution Fiat–Shamir/ROM composition remain **P** work.

### Johnson/list regime

`JohnsonRegime` proves the list-size inequality and sampling amplification. `JohnsonMcaBridge`
matches the exact published theorem interface and corrects the degree/rate convention. The hard
BCIKS/GS/Hensel algebra remains the explicit proposition `HaboeckTheorem2`, not a locally proved
theorem or hidden axiom. Capacity-level variants have counterexamples; no blanket capacity claim is
made.

### GF(2) tower and additive proximity

- Lean constructs the binary towers, embeddings, Fan–Paar basis/trace facts, and fast multiplication;
- the exact recursive low/high 32-byte Tower256 codec is proved;
- additive domains, novel-basis transforms, quotient folds, coherent queries, and adaptive
  earliest-deviation bounds are proved; and
- the characteristic-two clause binds exact basis order, affine domain, rate schedule,
  roots-before-challenges, queries, terminal, and ideal UD predicate.

The multiplicative *fold* is not reused for the additive protocol — it cannot be:
`Selvage.CharTwoWall.foldingData_charTwo_False` proves the multiplicative `FoldingData` EMPTY at
characteristic two, so every theorem over it is vacuous there. What IS reused, lawfully and
through a proved bridge, is the domain-agnostic RS proximity gap:
`additiveProximityGap_of_isProximityGenerator` transports any PG(2) realizer onto the additive
image domain, and `additiveProximityGap_UD` feeds the hypothesis-free
`reedSolomonCode_isProximityGenerator_UD` through it — so the additive gap is PROVED on the
`δ < (1−ρ)/3` band, not assumed. The bullet list above omits that; it should not.

### Zero knowledge and straight-line extraction

Formal games include constrained masking, multi-round/triangular hiding, straight-line extraction,
and repaired OracleLog linked-target assembly. The current linked construction freezes checked root
preimages before domain-separated queries and exposes shared-ROM fresh/hit/sampling ports.

These are real formal-game results. They do not mean the current runtime is a succinct NIZK. A
concrete hiding deployment still needs proof of committed-word knowledge, opening binding,
shared-ROM composition, and concrete ZK errors.

### Error budgets

The repository proves exact arithmetic for candidate formulas, including the BabyBear⁶ expression
in `(2^-138, 2^-137]`. The old 55-bit BabyBear⁴ expression and old recursive-verifier gadget are
historical results for deleted paths. A candidate formula is not a deployed security level until
the actual controller, fields, PCS, commitments, oracle, PoW, and common game match it.

## Lean-owned controllers — A

### Tower256 additive FRI

The shared backend fixes exact Lean Tower256, cSHAKE256 framing/output, and perfect-tree Merkle
relations. The deterministic controller:

- accepts only arbitrary native bytes or an opaque error;
- decodes proof bytes in Lean;
- derives roots-before-challenges transcript draws and coherent query seeds;
- checks exact Merkle openings, fold equations, and final polynomial; and
- reaches `AdditiveFriAdaptiveCoherentAccepts` and can issue the accepted sample token.

One controller-game coin owns schedule and ledger. This closes **A**, not deployed **P**.

⛑ **The paragraph above describes the LEGACY binding-closed path**
(`Tower256AdditiveFriController`), whose `MerklePcs` carrier is proved EMPTY at every
positive height by `Tower256MerkleCardinalityCore.merklePcs_empty_of_positive` — a 256-bit
cSHAKE root cannot injectively carry more than `2^256` words. Read it as a description of
the shape, not as evidence: `Tower256AdditiveFriControllerAdmission` and
`Tower256AdditiveFriActualReduction` are RETRACTED and carry their own machine-checked
retraction. The live path is `Tower256AdditiveFriRawAdmission` /
`Tower256AdditiveFriCanonicalExecutionGame` over `RawMerklePcs`.

Open **P/D/B** obligations:

- exact cSHAKE-to-uniform-ROM transport — genuinely open, and `Tower256RawHistoryCshakeTrace`'s
  `no_constant_uniform_256_slot` proves a *negative*: a deterministic cSHAKE evaluation cannot be
  relabelled as one uniformly fresh 256-bit slot, so a real ROM/sponge coupling is logically
  necessary and not merely missing;
- the collision PRICE. ⛑ The two halves of the old bullet here have separated. The **raw
  non-binding Merkle/PCS interface LANDED** (`Compiler.Tower256AdditiveFriRawController.RawMerklePcs`,
  inhabited by `Tower256AdditiveFriRawDeployment`), and the **extraction direction is PROVED**
  (`bindingFailure_implies_extractedCollision`, `RawMerklePcs.accepted_value_eq_or_extractedCollision`,
  `extractedCollision_of_columnEquivocation`). What remains is bounding the extracted collision's
  probability: `bindingFailure_price_le_collision` neither chooses nor bounds that price, so CR
  stays an explicit premise on the same coin;
- Fiat–Shamir / `oracleTransport` only. ⛑ The **proximity half is CLOSED**:
  `Selvage.additiveProximityGap_UD` proves the additive gap unconditionally on the
  `δ < (1−ρ)/3` band, `additiveFold_distance_UD` gives one-round soundness with no gap
  hypothesis, `additiveFriAdaptive_coherent_sampled_sound_UD` CONSUMES the far-word premise, and
  the far-word cover is constructed rather than caller-supplied. What is left is the same ROM
  transport as the first bullet, not a second proximity obligation;
- emitted executable checker for the currently noncomputable Tower relation;
- proof/container/domain/level codecs and authenticated work IDs; and
- matched end-to-end prover/verifier benchmarks.

### Tower256 indexed LogUp

Exact Boolean-address decoding, unit-vector incidence, table pushforward, semantic roots, and indexed
evaluation are proved. The extension-local clause-404 dispatcher fixes the clause/controller/
backend/transcript identity and accepts exactly two uniquely keyed byte replies. Wrong counts,
duplicates, missing replies, native errors, or Lean plan failure block. Successful control retains
the existing proof-relevant `VerifiedExecution`.

Clause 404 remains absent from base V1 and deployment. Position binding, concrete PCS/sampled
decider, CR/ROM, mutable RAM, native artifact work profile, history evidence, and common-game budget
remain.

### Ext6 gate proof

`GateFactoredExt6` proves descriptor residual provenance, seven factored operands, degree-two
rounds, public affine terminal forms, and eta aggregation. The landed controller fixes:

- one lawful prefix-decodable canonical statement preimage derived from the Lean descriptor,
  rounds, padding, public values, and cube encoding—never caller-authored statement bytes;
- lawful receipt/field/message codecs;
- cSHAKE-derived gamma, round challenges, and eta;
- exact transcript order; and
- the full algebraic acceptance relation around arbitrary native bytes/error.

The admission theorem names gate algebra, gate PCS, subfield, proximity, binding, oracle transport,
challenge sampling, and final LDT as eight events on one finite coin. Challenge sampling is
separate because radix-`BabyBear` reduction of cSHAKE bytes is not asserted uniform. Its reduction
laws are premises. Those disjoint event classes are now registered in the global extensible ledger
on the same coin, with exact base/extra event probabilities and a finite union bound. Concrete PCS,
subfield proof, proximity, binding/ROM, sampling-bias price, final LDT, reduction laws, recursion,
and deployed 137-bit security remain.

### Semantic history and BCS game

The retained history now supplies exact genesis/chain/link words and challenges, accumulator/fold/
source alignment, semantic-to-finite claim/witness reindexing, roots/opened-column binding, and the
actual unshifted semantic BCS reduction. PCS, commitment-binding, and ROM `Good` events share one
history coin; private admission has only an `ofNotBad` constructor.

⛑ **RETRACTED.** `SemanticHistoryTower256CheckpointGame`'s `JointGameFamily` joins the history
and Tower256 additive predicates on one `Omega`, one `FailureLedger`, exact
WARP-terminal/additive-initial root and schedule equalities, and one four-event union bound — **of
a type that cannot exist.** `Tower256MerkleBindingCardinality.jointGameFamily_impossible` derives
`False` from any inhabitant: the family's `additiveRoundsPositive` plus the tower's `m ≤ ell` force
a positive Merkle height, exactly where `merklePcs_empty_of_positive` refutes the binding-closed
PCS. The union bound, the root/schedule equalities, and `acceptedOfNotBad` are therefore VACUOUS,
not conditional — strictly weaker than the “conditional **P** shape” the next paragraph claims.
The “two ledgers” residual was not closed; the carrier was shown uninhabited. The replacement is
`RawSemanticHistoryCheckpointGame`, and `CarrierCensus.auditedNonTargets` records this.

The history failure event is now the literal retained-history Fiat--Shamir verifier/knowledge
failure rather than an external predicate, and the additive event/UD price and false-accept cover
are Lean-derived. It remains a conditional **P shape**, not the premises themselves. A concrete
same-coin `PcsCrRomReduction.classify`, exact common-coin realization, MCA and RS `codeExact`, PCS
opening, CR/binding, ROM transport, and hiding/sub-UD remain.

## Semantic and deployment joins

Selvage's proof claims meet the semantic kernel only through typed clauses:

- exact requests and family-selected argument bytes are bound to accepted effects;
- canonical patches produce one pre/post state and exact footprint;
- flat multi-cell hyperedges publish joint effects;
- exact-head history admission binds a precise entry, occurrence, receipt root, and supported
  finite post layout; and
- durable settlement has a semantic model but still needs physical implementation refinement.

The deployment registry is fail-closed: base V1 contains zero dialect clauses. The positive
extension deploys clause 406 through authenticated work `9102`, request codec `9003`, response
codec `9005`, and error-or-144-byte native candidate output. Lean alone decodes 36 canonical
BabyBear words and checks the descriptor. This is a narrow byte-backed deployment path, not Rust
semantics or proof-system security. Clause 404 is gated; BFV 901 is reserved with zero proof-suite
and controller pins. A manifest record never supplies cryptographic evidence.

The Lean-authored note-spend relation now enters the release-free computation core through one
request-indexed authority, exact public root/nullifier, output commitment, typed effect, complete
request/effect digests, eager nullifier, and validated patch. This is **S/A relation acceptance**.
Its byte/error controller derives the canonical statement from that accepted core, fixes roots
before its challenge, and treats proof payload bytes as inert. The proof-suite pin remains `0`, the
soundness reduction laws are premises, and no ZK/hiding construction, knowledge proof, CR/ROM/PCS,
or native semantic path is inferred.

## Native compute boundary

The canonical artifact authenticates native ABI codecs and a native work catalog. Base V1 contains
Tower256 dot product work `9101`, carrier `205`, request codec `9001`, and response codec `21`.
The clause-406 deployment extension adds work `9102`, request codec `9003`, response codec `9005`,
and generated 144-byte candidate output. This closes artifact identity and transport selection.

Rust remains opaque and fallible. There is no Rust operational semantics, Lean↔Rust refinement,
FFI proof, or cross-language correctness theorem. Deleted reference prover/verifier, WGPU, sampled
FRI/OOD, Ext6 verifier, and LogUp verifier paths remain historical and must not be cited as current
runtime closure.

## Performance boundary — B, narrow

Source `54295c6` and evidence `4d1f290` validate byte identity and measure direct versus generated
dispatch for work 9101. Ratios across lengths 1–16384 were `0.985–1.040` on hbox and
`0.985–1.025` on persvati. This is an empirical dispatch microbenchmark with no threshold and no
semantic, security, or complete-prover implication.

Integrated source/build evidence is archived from hbox as
`E-20260810T003037-13290-hbox-3f74f634e0e1-lake`: source `3f74f63`, 8729 jobs, command exit 0,
and source-integrity exit 0. Persvati replay is pending because local Tailscale reports
`NeedsLogin`. This is not benchmark, semantics, or security evidence.

## Historical claim corrections

- “The recursive verifier is complete” meant a then-local emittable AIR gadget composition. It did
  not include real CR/ROM, complete root/opening/domain wiring, recursive control, or deployment.
- “The v0 soundness tower is proved” meant an ideal uniform-schedule theorem composition at its
  interfaces. It was not a concrete one-game proof system.
- “Fully native NIZK” meant the formal reduction's own message/relation resolution, not Rust and not
  a deployed NIZK.
- “Deployed BCS alphabet” meant a concrete formal message shape, not a deployed PCS/controller.
- Old BabyBear⁴ prover, FRI, reference verifier, and WGPU results describe deleted experiments.

The theorems and counterexamples remain useful historical evidence. Their old deployment rhetoric
is superseded.

## What remains before a defensible whole

1. Instantiate the history same-coin `PcsCrRomReduction.classify`, common-coin realization, MCA,
   and RS code-exactness.
2. Instantiate exact additive ROM transport, the raw-Merkle collision PRICE (the interface and the
   extraction direction have landed; ⛑ NOT `PositionBinding` — demanding it unconditionally of a
   256-bit root is impossible, `merklePcs_empty_of_positive`), PCS,
   hiding, and sampled-decider reductions at the actual controller parameters.
3. Complete versioned proof/container/domain codecs and authenticated native work profiles.
4. Close Ext6 PCS/subfield/proximity/final-LDT and concrete reductions inside the landed global
   extensible ledger.
5. Close a concrete BFV proof controller and separately authorized disclosure path.
6. Deploy one durable handler and migrate real user/agent consumers.
7. Benchmark admitted end-to-end workloads against alternatives and apply Selvage's kill criteria.

The defensible one-breath claim is:

> minidregg has a large machine-checked proof-system and semantic core, exact Lean-owned additive,
> lookup, Ext6, and history control seams, and an authenticated bytes/error native boundary. The
> remaining work is to close their concrete cryptographic games, deployment handlers, consumer
> migrations, and matched end-to-end performance without weakening those boundaries.
