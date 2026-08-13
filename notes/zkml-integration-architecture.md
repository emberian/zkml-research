# zkML integration architecture — where the pillar lives, and what the first demo is

2026-08-13. Design lane with an executed build spike. Supersedes the "open
questions" section of `catgrad-seam.md` on placement; that note's catgrad-vs-catena
verdict stands unchanged.

Everything below marked **measured** was produced by running something today.
Everything marked **read** was read at source in this session. Everything else is
design, and carries its reason and its reversibility.

---

## 0. The verdict in one paragraph

**The zkML pillar lives in minidregg.** The op vocabulary goes in
`minidregg/Theory/` as a candidate-independent module (option (c)), the per-op
constraint semantics and soundness go in `Selvage/`, emission goes in `Compiler/`,
and the engine target is Selvage's own sumcheck prover (option (a)). The tracer is
a fork of catgrad pinned at `faf053f`, and it is **built and running**. The
brief's proposed "breadstuffs AIR pipeline as the interim" **should be dropped** —
measured against both trees, the interim needs *more* new machinery than the
destination, and three of the four pieces it would need already exist in minidregg
with faithfulness theorems attached.

The honest counterweight, stated up front: breadstuffs has a deployed prover that
produces accepted proofs, a recursion fork, and 132 shipped descriptors. minidregg
has none of that live — its `[EMIT-backend]` residual records that **no Rust
reader currently consumes its descriptor**, and `prover/src/sumcheck.rs` is
degree-1, uncommitted, with Fiat–Shamir as a named open residual `[PROVER-fs]`.
So minidregg is the right *home* and is **not able to prove an inference today**.
The first two rungs of the demo ladder are therefore differential and conformance
rungs, not proof rungs, and are labelled as such.

---

## 1. Where it lives

### Recommendation: (c) then (a) — shared `Theory/` vocabulary, Selvage engine

| Layer | Home | Why this boundary |
|---|---|---|
| Op vocabulary + two readings + agreement | `minidregg/Theory/` | Mathlib-only, mechanically enforced candidate-independent |
| Per-op constraint relation, lookup arguments, ε bounds | `minidregg/Selvage/` | may import `Theory/`; `uniformProb` and all soundness live here |
| Descriptor emission, conformance vectors | `minidregg/Compiler/` | the only layer allowed `Lean.Data.Json` / `IO` |
| Tracer (stager, no constraints) | catgrad fork @ `faf053f` | Rust; carries no soundness weight |

The boundary is not a preference — `scripts/check-import-boundary.sh` enforces it
by grepping every `^import` line. `Theory/` cannot import `Lean.Data.Json`,
`Selvage/`, or anything candidate-specific. That is exactly the property that makes
the op vocabulary survive both migrations we expect.

### The three deciding facts (all read at source)

**1. Expression sharing — matmul's make-or-break, and breadstuffs lacks it.**
breadstuffs' descriptor-level `VmConstraint2` has *no* sharing primitive; its
expressions are trees. The cost is measured in its own tree: emitting the
Poseidon2 permutation as a tree gives **141,439 nodes against 7,355**, and
**70,524 field operations against 2,943** — a ~19× blowup. `LeanTableAir` added a
`defs`/`Shr` list precisely for this, but only at the *table* level; the
descriptor level never got it. Matmul is the most sharing-hungry shape in the
vocabulary. minidregg's `Compiler/EmitShare.lean` is a CSE pass **with its own
faithfulness theorem**, measured at **2,696,666 → 220 gates** on note-spend.

**2. Unbounded-capacity lookup — the bf16 table.** The bf16 plan needs a 2^16-entry
table queried an unknown number of times. breadstuffs' `exact_public_rows` pins the
witness multiplicity column to a descriptor-declared multiplicity (a single `.all`
gate, `loc(0) − prep(2) = 0`), so the **capacity is fixed at emit time** — one
descriptor could not serve two different inference traces. Size is fine
(131,072 cells against a 33.5M cap); the *semantics* disqualify it. The byte table
is the right shape (free witness multiplicity, unbounded reuse), but generalizing
it is a new `RowSemantics` constructor + a new `TableSem` arm + a new Lean-emitted
table AIR + a resolver arm in a 12,130-line file. Against that, minidregg's
`Selvage/BinaryLookup.lean` proves **a table dot product at a Boolean address is
the table's MLE** — so a 2^16 table is *an MLE evaluation*, not 65,536 emitted
rows. The blocker dissolves rather than being worked around.

**3. Matmul as a vector relation already has a home.** breadstuffs' main-trace
degree budget is ≤ 3 *per row*; my measured MNIST trace at batch 2 is **158,800
multiply-accumulates**, which as per-row constraints is 158,800 rows for a
two-layer MLP. minidregg's `Assurance/AirSumcheckQuadratic.lean` already carries
the R1CS-shaped degree-2 face `Σ_b (Â·B̂ − Ĉ)(b)` over MLEs, with the bound
`m·2/|F|` quoted from `adaptive_sumcheck_soundness`. Matmul-as-a-vector-relation
is an *instance* of machinery that exists, not new machinery.

### And `Theory/IndexedProgram.lean` is already the template

It carries `IxSignature` (`Op : Ix → Type`, `Resp`, `next`), `Program`, `Algebra`,
`fold`, plus `fold_fusion` (an algebra morphism commutes with fold) and `fold_rel`
(a logical relation transports). "An op set" is an `IxSignature`; "the field
reading agrees with the numeric reading" is `fold_fusion`. `Compiler/Air.lean`
demonstrates the same pattern one level down — two independent readings (`eval` as
a fold, `evalExec` as hand-recursion) with `eval_agrees_exec` free by initiality.

There is **no `Matrix`, `dotProduct`, or tensor anywhere in `Theory/`** today. A
zkML module would be its first linear-algebra tenant. That is a real cost — no
prior art to copy inside the boundary — and it is the main argument the other way.

### Why the breadstuffs interim should be dropped

Riding the existing pipeline needs four new things: (i) an unbounded-capacity
`RowSemantics`, (ii) descriptor-level expression sharing, (iii) a reusable
comparison/select lowering (the IR has **no `sub`, no `select`, no `cmp`** — only
`var`/`const`/`add`/`mul`; every existing circuit hand-rolls it), and (iv)
emit-time scale headroom. On (iv): `EmitByName.lean` pins its own row count by
`rfl`, already needs `maxRecDepth 8000` at row 126, and that pin has caused **six
recorded outages** — once taking the whole by-name emit surface down for ~19 hours.
There is also a live cultural size limit: a 24 MB descriptor was deliberately
withheld from routing for being the wrong shape.

Three of those four exist in minidregg with theorems. So the interim is not a
cheaper path to the same place; it is a more expensive path to a worse place.
CLAUDE.md's own rule applies literally — *if you catch yourself shipping a
containment while naming the real fix as a later phase, the phases are backwards.*

**Reversibility.** This is the cheap direction. The `Theory/` module is Mathlib-only
and names no engine, no field, and no proof system, so it survives catgrad→catena
and breadstuffs→Selvage alike. If the Selvage engine stalls, the same `Theory/`
module can be consumed by a breadstuffs emitter without edit — the import boundary
guarantees it never learned about either. The expensive, hard-to-reverse decision
would be authoring op semantics *inside* a `Compiler/` or a Rust emitter, and this
design specifically does not.

---

## 2. The tracer — **built, running, committed**

Fork point: **`faf053f`** (`hellas-ai/catgrad`, merge of PR #519). Spike clone at
`/Users/ember/src/catgrad-spike`, commit `253dd37`. Upstream is dormant since
2026-06-10, which is the asset here: nothing moves under the trace format.

### Shape (confirmed by execution)

```
catgrad core::Term
  → Interpreter<ProvingBackend>   [Rust STAGER: shapes, wire ids, trace. NO constraints.]
  → resolved op trace  (op, dtype, concrete shapes, wire ids, branch decisions)
  → Lean: per-op constraint semantics + descriptor emission
  → prover
```

`ProvingBackend` is `Rc<RefCell<Trace>>`; `TracedTensor` is `{shape, wire}` and
carries no data. All 39 `Backend` methods implemented in 729 lines with **zero new
dependencies** (JSON hand-rolled deliberately — a tracer that drags in a
serialization stack has already started to matter more than it should).

### Measured: the swap is two lines, not ten

`run_interpreter` in `examples/hidden.rs` is *already* generic over `Backend`, so
the diff from `hidden.rs` to `trace_mnist.rs` is an import and a constructor. The
seam note's "~10-line diff" estimate is confirmed and was generous; the remaining
+12/−26 is the trace dump and deleting now-dead backend-selection boilerplate.

### Measured: `SimpleMNISTModel`, batch 2, 784→100→10

```
26 ops, 26 wires, branch_demands 0
const x7   broadcast x4   cast x4   add x2   div x2
matmul x2  neg x2         pow x2    reshape x1
scalar output elements: 84520      multiply-accumulates: 158800
```

Four things the run establishes that reading could not:

- **The trace is Copy-free and Nat-free by construction.** `Copy` and the shape
  arithmetic never reach a backend at all — they stage away in the abstract
  interpreter. The 53%-Copy figure from the seam note therefore means the backend
  trace *already is* the arithmetization residue. 26 ops is the whole surface.
- **MNIST is branch-free by execution, not inspection** — `to_bool` was never
  called. This is the static-shape guarantee, observed.
- **The `exp`-as-`pow` problem is visible.** Sigmoid decomposes to
  `neg → broadcast → cast → pow → add → div`, and `pow` takes **two full tensors**.
  Six ops for what bf16 makes one lookup.
- **Cost is concentrated, and the concentration is not where op-counting suggests.**
  158,800 MACs, of which **156,800 (98.7%) are the single 784-contraction matmul**.
  Separately, of the 84,520 scalar output elements, **80,968 (95.8%) are constant
  weights** — those are a *commitment* surface (committed once), not a per-inference
  *constraint* surface. Constraint-relevant elementwise outputs are 3,552. Naming
  these two numbers separately matters; conflating them inflates the circuit by 20×.

### The one design decision I made against the reference: `to_bool` is fail-closed

`ShapeOnlyBackend::to_bool` returns `true` **unconditionally**. A tracer inheriting
that would silently emit a trace of the `then` branch of every `If` and call it the
program — which is the house's *refusal-renders-as-the-expected-verdict* class
exactly. `ProvingBackend::to_bool` panics, and
`tests/test_proving_trace.rs::proving_backend_refuses_data_dependent_branch`
asserts the refusal fires. **Reason:** a tracer that guesses produces a trace of a
program nobody ran, and every downstream proof would be about that program.
**Reversibility:** trivially reversible — the intended v1 form is not "guess" but a
branch-decision table resolved from shapes and bound as public inputs *before*
tracing, at which point `to_bool` reads the table and still never guesses.

### Trace format — v0 shipped, v1 spec

v0 as emitted (`catgrad-trace/v0`, greenfield, no compatibility obligation):

```json
{ "format":"catgrad-trace/v0", "wire_count":26, "op_count":26, "branch_demands":0,
  "ops":[ {"i":4, "op":"matmul", "dtype":"f32",
           "in":[3,0], "out":[4],
           "in_shapes":[[2,784],[784,100]], "out_shapes":[[2,100]],
           "attrs":{"contract":784}} ] }
```

The op name is the `Backend` method, which *is* the vocabulary — the 39-method
trait is the intersection surface, and keying to it (not to catgrad's internals) is
what makes the catena migration free.

**v1 changes, each with its reason:**

1. **Bind parameter `Path`s to wires.** Today a weight enters as an anonymous
   `const` with a digest; the trace cannot say *which* weight. The host holds the
   `BTreeMap<Path, Value>` and must thread it. Without this the weight commitment
   cannot be checked against the trace at all — this is the single most important
   v1 item.
2. **Replace the FNV digest with a real commitment** (Poseidon2 / Merkle over the
   path-ordered weight map). FNV is a placeholder and is labelled as one in the
   code; it is not collision-resistant and must not survive contact with a bound.
3. **Declare public inputs explicitly** — input digest, output digest, model
   commitment, branch table.
4. **Canonicalize.** The digest field earned itself on the first run: ops 5/16 and
   6/17 carry *identical* digests, so sigmoid's constants are re-materialized per
   call, and 4 of 26 ops are identity `f32→f32` casts. A CSE + identity-cast pass
   takes MNIST from 26 ops to roughly 20 for free, and the format already exposes
   the information needed to do it.

---

## 3. The Lean surface

**Do not author this in Rust.** Saying it out loud per house law: **this is
Lean-authored AIR**. The Rust tracer above emits a *trace*, never a constraint;
`proving.rs` contains no `assert_zero`, no builder, and no gate.

### `Theory/TensorOpVocabulary.lean` — candidate-independent

Modelled on `Theory/IndexedProgram.lean`. An `IxSignature` indexed by
`(dtype, shape)`, whose ops are the **intersection vocabulary** with catena, not
catgrad's 32 primitives:

scalar `add/mul/sub/cmp/select/fma` at bf16 and f32 · **matmul as a fold** ·
**ordered reduce** · **pure map** · **index read** · shape-only reshaping
(`reshape/broadcast/transpose/slice/concat`, which carry *no* arithmetic content).

Two algebras over the one signature:

- `refAlg` — the exact numeric reading (bf16 tables; the exact-mult fact).
- `fieldAlg` — the constraint relation over `F`.

`fold_fusion` / `fold_rel` then give agreement transport for free, which is the
whole point of choosing this template: the spec/executable twin is structurally
impossible because there is one signature and two folds, not two programs.
(This is composition D of `context-window-compositions.md`, landed as an
architecture rather than an aspiration.)

### Per-op constraint-relation shapes

| Op class | Relation shape | Basis |
|---|---|---|
| **Pure map, unary, bf16** | one LogUp query into a 2^16 table; **the table is an MLE evaluation, not materialized rows** | `Selvage/BinaryLookup.lean` — table dot product at a Boolean address = the table's MLE |
| **Scalar binary at bf16** | `bf16 × bf16 → fp32` never rounds, so the product is *exact*: a field mul plus a rounding relation only at the store | `docs/bf16-exact-arithmetization.md` |
| **cmp** | sign/limb decomposition + range lookup — **not** a primitive | no `cmp` exists in either IR; both trees build it this way |
| **select** | `s·a + (1−s)·b`, degree 2 — native to the sumcheck face | `Assurance/AirSumcheckQuadratic.lean` |
| **matmul** | **one vector relation**, `Σ_b (Â·B̂ − Ĉ)(b) = 0` over the hypercube — *not* M·N·K row constraints | `Assurance/AirSumcheckQuadratic.lean`; bound `m·2/|F|` |
| **ordered reduce** | a fold chain with a **specified** order | catena's `reducec` lowers to a sequential fold — the order is specified, so accumulate-exactly is well-posed |
| **index read** | ROM/RAM bus lookup | `Compiler/SparseAuthenticatedStateLogupBridge.lean` |
| **reshaping ops** | **no constraints at all** — a wire relabelling | measured: 9 of my 26 MNIST ops are in this class |

Two open numeric questions, unchanged and **not** closed by this design:
**accumulator width** for exact fp32 accumulation of bf16 products, and whether
candle and ndarray agree numerically (f32 addition is non-associative and the two
use different reduction kernels).

### The emitted artifact

Per minidregg's actual mechanism, which is `#eval`-time `IO` file emission — **not**
a 60 MB descriptor directory:

1. a `ConstraintDescriptor F` from `Compiler/Emit.lean`, *after* `EmitShare.lean`
   CSE. `emit_faithful` is unconditional and **both directions** — for every total
   wire vector, the descriptor holds iff the readback satisfies the Lean gate
   system. This is a stronger emission theorem than anything in the breadstuffs
   tree and is the main reason to prefer this path.
2. a **conformance vector** (Lean `#eval` → JSON → Rust differential test), which
   is the existing "emitted-vector binding" discipline. Its own commit message
   states the correct label: *vector agreement is the whole claim — never
   refinement or verification.* Carry that label forward verbatim; Rust has no
   formal semantics and agreement-on-vectors is the entire seam.

---

## 4. The audit hookup — and the number it produces is the headline

`Selvage/AuditSampling.lean` proves: if round `t` is corrupt then for *every*
history the round alarms with probability ≥ `q := p·(1 − ε_chk) − ε_bind −
ε_beacon`, and the expected number of corrupt rounds before the first alarm is
≤ `1/q`. To instantiate it, a deployment must supply a finite nonempty coin space
`Ω`, a `Round Ω` (six Boolean fields), an `AuditParams`, `DetectionLegs`, and
`0 < q`.

### The instantiation for inference

- **A round** = one inference turn: model commitment `M`, input commitment,
  claimed output, trace commitment.
- **`Ω = σ × K`** — the §7 product route: `σ` the beacon draw, `K` the checker's
  own coins. `ChkLeg` then discharges from a bound on `K` alone via
  `chkLeg_of_product`.
- **`corrupt : List Ω → Bool`** takes the **history only**, never the round's coin.
  That typing *is* the adaptivity argument, and it is free.
- **`chkAbort` must force an alarm.** This is where the tracer's fail-closed
  `to_bool` meets the theorem: a trace the tracer refused to produce, a shape
  mismatch, or a missing weight commitment is an *abort*, and `FailOpenRefutation`
  proves `DetectionLegs` is **uninhabitable at any positive q** for a checker whose
  failure reads as acceptance. A zkML deployment that skips a malformed trace
  rather than alarming has `ε_chk = 1` and the theorem says nothing at all.
- **`ε_bind`** = the weight/trace commitment binding — Merkle over the path-ordered
  `BTreeMap<Path, Value>`, which is already the canonical object to commit.
- **`ε_beacon`** = 0 only for a `G=1` beacon (threshold VUF / VDF). Composition C
  is still the route: `pqvrf` + `dregg-pq` + fhegg's threshold ceremonies.

### The transport obligation that bites, and the definitional trap

`[AUDIT-chk-corrupt]` requires the corruption predicate be **δ-far-falseness of
some link**, *not* "the trace fails the relation". The tempting inference-shaped
definition — *"the claimed output ≠ f_M(x)"* — is exactly relation-failure, and it
is **outside the covered set**: a prover whose committed words are δ-close to
satisfying words but wrong sits in the gap. The correct predicate is *some traced
op's committed output word is δ-far from every word satisfying that op's relation*,
with the **same δ** as the light-client bound. Getting this wrong yields a theorem
that appears to apply and does not — precisely the apex-vacuity shape the house has
been burned by. `[AUDIT-chk-anchor]` additionally requires the audited event be
anchored at the honest fold of the *committed* words; the gap to the prover's own
recommitments is `ε_bind`, so the decomposition is consistent **because**
`AuditParams` prices `ε_bind` separately, and is inconsistent for any deployment
that folds it away.

### What ε_chk actually instantiates to — two flavours, and one of them is fatal

**(a) Cryptographic checker** (the checker *is* the sumcheck/STARK verifier on the
emitted descriptor). Then `ε_chk := n·(err⋆(δ) + 1/|F|)` from `lightClientSound`,
under `hT1`/`hT2`. Falls with a security parameter. **This is the one we want.**

**(b) Statistical spot-check** (recompute a sample of ops/rows). Then
`AuditSampling.lean`'s own §8 residual bites, and it is brutal: **a single-path
trace check on width-`N` layers forces `ε_chk ≥ 1 − 1/N`**, hence
`q ≤ p/N − ε_bind − ε_beacon`. For a GPT-2-small layer at `d = 768`, that is
`q ≤ p/768`.

**This is the most valuable thing the audit hookup produces, and it is a negative
result: sampling cannot amortize *within* a wide inference.** Layer width is the
enemy, and it grows with model size. The theorem therefore does **not** say "spot-check
inference cheaply"; it says the checker must be the full-trace cryptographic
verifier, and the audit layer amortizes **which turns get proven, never which ops
within a turn**. That is a clean argument for why the zkML pillar needs the prover
and cannot be replaced by sampling — derived from our own theorem rather than
asserted.

Recorded honestly: the `1 − 1/N` floor is **named but underived** in
`AuditSampling.lean` (§8, around line 1110). Deriving it for the inference shape is
real work and is card **Z4** below, not a result we hold.

---

## 5. The demo ladder — what each rung proves

| Rung | Artifact | What it proves | What it does **not** prove |
|---|---|---|---|
| **0 — DONE** | `ProvingBackend` + MNIST trace (`253dd37`) | the seam is a 2-line swap; MNIST is branch-free *by execution*; the trace is the arithmetization residue; real cost numbers exist | nothing about constraints, soundness, or any proof |
| **1** | `tests/test_models.rs` fixtures as a differential harness | the tracer agrees with ndarray/candle on **shapes** across every fixture, and the op vocabulary is closed (no unexpected primitive) | not numeric agreement — the tracer computes no data |
| **2** | Lean `Theory/` vocabulary + conformance vectors | the two readings agree on emitted vectors, kernel-decided in Lean | **vector agreement, never refinement** — Rust has no semantics |
| **3** | toy GPT-2 (1 layer, d=32, vocab 128, 864 ops, no weights on disk) | the vocabulary covers a transformer, not just an MLP; KV cache as explicit graph I/O; still branch-free | not GPT-2-small; not a proof |
| **4** | one proved MNIST inference through Selvage | end-to-end, with the ε ledger filled in | not fast, not recursive, not private |

**Rung 3 has a concrete measured blocker.** The toy GPT-2 lives in
`catgrad-llm-models/src/models/gpt2.rs` behind a config JSON, and running the
interpreter needs a populated `Parameters` map. Because the tracing backend only
ever sees shapes, parameters can be **synthesized from declared types** — which is
precisely why rung 3 needs no weights on disk — but that synthesis path does not
exist yet (`catgrad-llm/src/run.rs` builds `parameter_types` only from a real
checkpoint load). That is a small, named piece of work, not a research question,
and it is card **Z2**.

---

## 6. Spike evidence

- Clone: `/Users/ember/src/catgrad-spike` @ `253dd37`, forked from `faf053f`.
- `catgrad/src/interpreter/backend/proving.rs` — 729 lines, 39 methods, no deps.
- `catgrad/examples/trace_mnist.rs` — the swap.
- `catgrad/tests/test_proving_trace.rs` — 2 tests, both pass: the branch refusal
  fires, and a traced linear+sigmoid has resolved shapes on every wire with no
  wiring op leaked.
- `phase0/mnist-trace.json` — the emitted trace.
- Full catgrad suite with `--features ndarray-backend`: **51 passed, 0 failed**.
  (Without the feature, `tests/test_if.rs` fails to compile — pre-existing
  feature-gating in the upstream tree, unrelated to this work: it imports
  `backend::ndarray`, which is `#[cfg(feature = "ndarray-backend")]`, and default
  features are empty.)

---

## 7. Dispatch-ready cards

### Z1 — Lean op vocabulary in `Theory/` **(dispatch first; everything else waits on it)**
Author `minidregg/Theory/TensorOpVocabulary.lean`: an `IxSignature` over the
intersection vocabulary (§3), two algebras (`refAlg` numeric, `fieldAlg`
constraint), agreement via `fold_fusion`/`fold_rel`, and a mismatch tooth in the
house style (a *deliberately wrong* reading proved unequal by `decide`).
**Ground truth to paste into the brief:** `Theory/IndexedProgram.lean:93-100`
(`AlgebraHom`), `:265-269` (the tooth), `Theory/CompressedLinearEquation.lean:106-109`
(witness-carries-its-law), `Compiler/Air.lean:47-98` (two readings, agreement by
initiality).
**Gate:** `scripts/check-import-boundary.sh` green (Mathlib-only); no vacuous or
tautological theorem; the tooth actually fails on the wrong algebra; `#assert_axioms`
clean. **Forbidden:** `#guard` (see `docs/GUARD-DISCIPLINE.md`), any import of
`Selvage`/`Compiler`, any mention of a field or proof system.

### Z2 — tracer v1 + differential harness + toy GPT-2 (rungs 1 and 3)
In `/Users/ember/src/catgrad-spike`: bind parameter `Path`s to wires; replace the
FNV digest with a Merkle commitment over the path-ordered weight map; declare public
inputs; add the canonicalization pass (CSE on identical digests + drop identity
casts — MNIST 26→~20 ops). Then drive `tests/test_models.rs` fixtures as a shape
differential, and synthesize `Parameters` from declared types to trace the toy GPT-2
(expect ~864 ops; **verify, do not assume**, the count came from an instrumented
probe on a different tree state).
**Gate:** every fixture traces; op vocabulary closed with a refusal on any
unexpected primitive; GPT-2 trace has `branch_demands == 0`.
**Tripwire, restated in the brief verbatim:** *no `assert_zero`, no builder, no
gate, no constraint anywhere in Rust.* If a lane reaches for one, the work belongs
in Z1.

### Z3 — matmul as a vector relation, against the Selvage engine
Instantiate `Assurance/AirSumcheckQuadratic.lean`'s degree-2 MLE face for the
matmul relation from Z1's vocabulary, and bind it to `prover/src/sumcheck.rs`
through a conformance vector authored in `Compiler/`.
**Named prerequisites, both open:** `prover/src/sumcheck.rs` is **degree-1** today
(`[PROVER-sumcheck-gates]` is the degree-2 rung and is not built), and Fiat–Shamir
is the open residual `[PROVER-fs]`. This card **must** state that it is building
those, not assuming them.
**Gate:** prover+verifier roundtrip where the verifier semantics are Selvage's;
label the result "vector agreement", never refinement or verification.

### Z4 — the inference-shaped audit instantiation (paper first, then Lean)
Write the `Round`/`AuditParams` instantiation of §4 as a Lean file in `Selvage/`,
including the **fail-closed clause with teeth** (a case where the checker aborts and
the theorem *forces* alarm). Derive the `1 − 1/N` width floor for the inference
shape — it is named but underived at `Selvage/AuditSampling.lean` §8 (~line 1110).
**Gate:** `corrupt` is defined as δ-far-falseness, *not* relation-failure, with the
same δ as `lightClientSound`; `[AUDIT-chk-corrupt]`/`[AUDIT-chk-anchor]` carried as
explicit hypotheses, never discharged silently; the headline states the
**pessimistic** `q` with covered scope in the same sentence.
**Sequencing note:** Z4 is independent of Z1–Z3 and can run in parallel; it needs
no tracer and no prover.

---

## 8. What this design does not claim

- No proof of any inference exists. Rung 4 is unbuilt and the engine it targets is
  degree-1 with Fiat–Shamir open.
- The 864-op toy-GPT-2 figure is inherited from the earlier lane probe and was
  **not** re-measured here; my measurements cover MNIST only.
- The accumulator-width question for exact fp32 accumulation of bf16 products is
  open and this design does not close it.
- The `1 − 1/N` audit floor is named in our own file and underived; §4's `q ≤ p/768`
  is an application of a bound we have **not** proved, and is stated as motivation
  for Z4, not as a result.
- catgrad is not deprecated in public and hellas.ai has not been asked the
  catgrad-vs-catena question. `catgrad-seam.md` says that ask should come **before**
  committing engineering; this lane committed a 729-line spike to a private clone,
  which is reversible, but Z2 is the point where that stops being true.
