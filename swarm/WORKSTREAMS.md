# Workstreams — dispatchable cards (steering: ember + Fable; execution: Opus swarms)

Status: QUEUED / IN-FLIGHT / LANDED / BLOCKED(on). Every card names its spec
and gate. Order within tiers = dispatch order.

## Paper 1 — the joint representation (IN-FLIGHT, 4 fable lanes)
red-team re-derivation · modulus-swap experiment · family-law Lean ·
scaffold+claim-ledger. Gate: red team clears; experiment verdict in.

## Build tier (Opus-ready now)
1. **Selvage sumcheck engine, Lean-bound** — REFRAMED (ember caught the
   mis-sequencing): p3-sumcheck M0 LANDED as reconnaissance only (bc2e9f4b9;
   measured API facts: degree-2-pair engine, verifier folds-but-checks-nothing
   [fail-open seam], p3-lookup does not compose). The engine that RUNS is
   Selvage's own: grow minidregg/prover against the Lean sumcheck verifier as
   spec, emitted-vector binding, p3 toy demoted to differential harness in
   tests only (a confession, not a substitute). Gate: prover+verifier
   roundtrip where the verifier semantics are Selvage's, bound to Lean.
2. **Weight registry** — QUEUED→dispatching. Spec: composition B
   (notes/context-window-compositions.md) + range-request technique
   (phase0/e8m0_spread.py). Gate: published commitments for ≥3 Tier-1 models
   + tooling, reproducible.
3. **KPZ encryption fix** — QUEUED. Spec: notes/fhe-scout-verdicts.md item 1.
   Gate: Fheanor depth harness shows depth 1→2.
4. **wgpu fusion toy** — QUEUED. Spec: hpu-seam-study de-risk #3
   (gpu_arena multi-pipeline). Gate: A/B with/without download, measured.
5. **Verified table contents** — QUEUED. Spec: AGENDA pillar V item 1.
6. **Tuple-compression lemma** — QUEUED. Spec: compositions item I.
7. **num_queries pin** — QUEUED. Spec: field-choice-verdict prerequisite.
   (Soundness; field-independent; do before flag day.)

## zkML pillar (Opus-ready; spec for all four: notes/zkml-integration-architecture.md)
Placement DECIDED: minidregg, not breadstuffs. Op vocabulary in `Theory/`
(candidate-independent), semantics in `Selvage/`, emission in `Compiler/`,
engine = card 1's Selvage sumcheck. The breadstuffs "interim" was measured and
DROPPED — it needs more new machinery than the destination.
Rung 0 LANDED: catgrad tracer built + running (`~/src/catgrad-spike` @ 253dd37,
forked at `faf053f`); MNIST = 26 ops, 0 branch demands, 158800 MACs.

Z1. **Lean op vocabulary in `Theory/`** — QUEUED, DISPATCH FIRST (Z2/Z3 wait on
    it). `IxSignature` + two algebras + agreement by `fold_fusion`; template is
    `Theory/IndexedProgram.lean`. Gate: import-boundary green, no vacuous
    theorem, mismatch tooth fails on the wrong algebra. Forbidden: `#guard`.
Z2. **Tracer v1 + differential harness + toy GPT-2** — QUEUED. Path-to-wire
    binding, Merkle weight commitment (FNV is a placeholder), canonicalization,
    fixtures as shape differential. Tripwire verbatim in the brief: NO
    `assert_zero`/builder/gate in Rust.
Z3. **Matmul as a vector relation** — BLOCKED(on: Z1, card 1). Instantiate
    `Assurance/AirSumcheckQuadratic.lean`'s degree-2 MLE face. ⚠ must state it
    BUILDS `[PROVER-sumcheck-gates]` (degree-2) and `[PROVER-fs]`, not assumes.
Z4. **Inference-shaped audit instantiation** — QUEUED, parallel (needs no tracer,
    no prover). Instantiate AuditSampling for inference + derive the `1 − 1/N`
    width floor (named but UNDERIVED, §8 ~line 1110). ⚑ headline finding to
    confirm: sampling cannot amortize WITHIN a wide inference — `q ≤ p/N`.

## GKR substrate tier (spec for all five: notes/gkr-substrate-design.md)
The artifact four lanes converged on. Design pass landed 2026-08-13. Headline
from the pass: **Selvage's sumcheck protocol layer is ALREADY degree-generic**
(`{d : ℕ}` through `adaptive_sumcheck_soundness`) and the round-chain skeleton
in `MultilinearExtension.lean` is proved for an ARBITRARY `g` — degree 1 is
pinned only at the realizer, and `Assurance/AirSumcheckQuadratic.lean` (916 lines,
CLOSED at d=2) is a line-for-line template for d=3. Two laws the substrate is
built on: **never return folding randomness without the terminal value** (the p3
seam), and **never compress `h(1)` out of the round message** — at our pin p3
derives `h(1) := claimed_sum − h(0)`, which makes the round check a *tautology*
rather than a skipped check (`sumcheck/src/data.rs:14-26,118-131`).

G1. **`eq` + zerocheck + multilinear Schwartz–Zippel** — QUEUED, DISPATCH FIRST
    (G2/G4 wait on it). New `Selvage/EqPoly.lean`. A two-vector `eq` is ABSENT in
    our Lean (only the boolean-corner `chiEval`); multilinear SZ is the rung's
    dominant new proof term. Cheapest spike inside it: `eqMle` +
    `eqMle_cubePt` + `eqMle_fold`, ~40 lines, no protocol change.
    Gate: named theorems + `#guard_msgs in #print axioms` (⚠ NOT
    `#assert_axioms` — that tool does not exist in minidregg).
G2. **The degree-3 cubic realizer with an eq factor** — BLOCKED(on: G1).
    New `Assurance/AirSumcheckCubic.lean`. Gate: terminal check FACTORED into the
    input claims (an opaque oracle value is the Class-3 industry bug); the
    `ringChar F > 3` node-injectivity condition stated, not assumed.
G3. **Degree-`d` Rust engine + the folding prover, conformance-bound** —
    BLOCKED(on: G2). ⚠ `round_sum` is today the literal O(4^m) mirror;
    `mle_kernels::fold_mle_table` exists but is not implemented for the prime
    scalar the sumcheck engine uses. Without it the rung caps at m≈12.
    Measure wall-clock + peak RSS at m ∈ {10,16,20}.
G4. **logUp-GKR vs logup\*, priced on the substrate** — BLOCKED(on: G1, G2).
    The deciding term is the **post-challenge commitment floor** on a hash PCS,
    NOT field-op counts (and every published field-op constant is denominated in
    a unit 2026/587 moves by >10×).
G5. **Multilinear PCS seam: interface + ideal inhabitant + equivocator** —
    QUEUED, parallel, blocks on nothing. ⚠ `Selvage/Commitment.lean`'s
    `OpeningScheme` is POSITIONAL (`openAt : … → ι → Op`) — a vector commitment,
    the wrong shape for a multilinear claim; this needs a sibling structure, not
    a reuse. Must NOT attempt the BaseFold/WHIR bridge — that is a campaign;
    `Selvage/MultiplicativeMleTerminal.lean` is its seed.

⚑ Two OPEN decisions the memo refuses to make silently, both ember's:
(i) **the challenge field** — we already hold Ext6 (proved a field, no
`native_decide`) and `Assurance/MixedFieldBudget.lean` prefers it at 137 bits,
but that model's proximity leg is field-size-bound and contains **no query-count
term**, so it cannot see the 100-bit wall grey-lit §3 records; (ii) **prime-only
substrate vs two instantiations** of the (already field-generic) Lean interface —
`prover/src/tower256_kernels.rs` already holds a char-2 two-vector `eq` and an
inversion-free `fraction_add_layer` with no driver above it.

## Verification tier
8. **census-on-Avigad** — QUEUED. Spec: compositions item A. Collegial gift.
9. **KB-vs-Goldilocks recursion benchmark** — QUEUED. Gates the flag day;
   the study exists nowhere.

## Research tier (needs Fable steering before dispatch)
10. **Ring-hash cryptanalysis** — BLOCKED(on: framing a safe adversarial
    brief). Candidate exists (~/src/ring-ro-hash); no security analysis yet.
11. **Three-tree FRI-RBR composition** — QUEUED; window contested.
12. **G-series vFHE gates** (single-prime consequences, N=8192 fork, ring
    noise lift, CPA-D/determinism hinge) — specs in docs/FRONTIER-QUEUE.md.

## Flag day (single re-genesis, when gated items land)
KoalaBear migration + Poseidon2 matrix transpose fix + (pending G1/G2) the
FHE parameter re-choice. Spec: field-choice-verdict + hash-verdict.
