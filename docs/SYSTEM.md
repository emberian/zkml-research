# THE SYSTEM — what we are actually building

2026-08-13. The answer to "what have we arrived at?", written after the full
campaign (9 decision memos, ~50 lanes, every claim traced). One sentence:

**A receipts-native compute fabric: every turn — plaintext, private, or
encrypted — is a typed, authorized, semantic state transition whose proof is
either carried or committed-and-auditable, with the soundness story
machine-checked end to end, and every artifact open.**

## The insight the whole campaign converged on

**We did not arrive at a faster prover. We arrived at a different
STATEMENT.** The zkVM industry proves "a RISC-V machine executed" and pays
for the generality: ~502 trace cells per general RAM touch (SP1, measured)
against 39–44 for the instruction itself; whole cost profiles dominated by
emulating machinery no user asked about. The dregg kernel proves **"this
authorized semantic turn happened, and here is its receipt"** — the
statement users actually need — and the kernel's type system does, at
specification time, the work the zkVM trace pays for at proving time:

- **Authority is request-indexed in the statement**, not re-derived inside a
  VM trace. The turn's semantics ARE the circuit; there is no instruction
  fetch to prove.
- **Memory is what the campaign showed is cheap**: weights and code are
  read-only (preprocessed tables — complexity ~0), state is
  canonical-transition-shaped (validated patches, not general RAM), KV-style
  state is append-dominant (write-once SSA shape, ~6 cells vs ~502). The
  expensive general-RAM case the whole industry optimizes barely appears.
- **The effect system already separates public from private from encrypted**
  (typed ZK/MPC/FHE requests with explicit disclosure), so "which parts get
  which proof treatment" is a type, not an afterthought.

That is the sense in which this is beyond the current ladder: the ladder
(cheap LLM proving → cheap FHE → verifiable FHE) improves layers under an
unchanged statement. We change the statement, and every layer gets cheaper
because it proves less junk.

## The three tiers, one receipt shape

| tier | what runs | what the receipt says | proof regime |
|---|---|---|---|
| **Plaintext turns** | kernel semantic transitions | "this authorized turn happened" | proved per-epoch (accumulate, decide once) |
| **Verified inference** | native-format model serving | "THIS model (registry-pinned) produced THIS output" | bit-exact statement; commit always, prove sampled, audit game with the composed q-budget |
| **Encrypted turns** | BFV ops on fhegg (folds, matvec) | "the ciphertext operations were performed faithfully" | SNARK-over-FHE, sampled; client-side semantic assurance layered separately where parameters allow |

One accumulation spine (per-epoch decide, not per-op verify), one audit
theorem (machine-checked, dispatching now), one registry (weights,
architectures, tables — all publicly committed), one soundness ledger
(two-sided bounds, regime tags in the type).

## What is demonstrable, in dependency order

1. **The registry** — commitments to every Tier-1 open model, computed by
   range-streaming without full downloads, published with tooling. Closes
   the effort-gap attack class nobody else has closed; needs no prover;
   shippable in days.
2. **The audit theorem in Lean** (in flight) — the first machine-checked
   commit-then-audit soundness statement, with the error budget composed
   into one number. This is the theorem that makes tier-2 and tier-3
   DEPLOYABLE at ~1.2× overhead with today's provers.
3. **The fhegg demo**: KPZ one-line fix (free depth level) → rotation-free
   encrypted matvec (closes under the PROVEN noise bound; zero new key
   material) → fold_add proved as a vector relation (the 98,304-equation
   family re-arithmetized) → sampled audits over the op stream the node
   already serves. "An encrypted market operation with a receipt."
4. **The gpt-oss demo**: MXFP4 exact block dots (measured: width-8 windows
   cover 100%) + exact 2^16 tables + LogUp + the audit game = **a served
   token with a receipt** — not the world's fastest proof, the world's most
   honest one: bit-exact against the shipped artifact, two-regime security
   accounting, machine-checked audit soundness, fully open.
5. **The fusion testbed**: wgpu toy (Arena multi-pipeline; days) → F2 spot
   instance riding the HPU dataflow — the producer-consumer fusion
   demonstration nobody has built, honestly framed as a testbed.
6. **The formal crown**: the three-tree FRI-RBR composition (first
   unconditional machine-checked FRI soundness) and the two-regime security
   calculator — the artifacts that make "machine-checked end to end" true
   rather than aspirational, in a window other swarms are actively mining.

## On private and collective training

The honest version, from the depth arithmetic: full training under FHE at
deployable parameters is out of reach (even inference nonlinearities need
the MPC boundary at our depths). What IS reachable and valuable now:
**fine-tune provenance** (LoRA adapters as registry deltas — prove a
fine-tune derives from a pinned base; the inference side is unclaimed),
**training-step auditing** (the same commit-then-audit game over training
steps — refereed-delegation prior art exists, the machine-checked audit
layer is ours), and **collective custody** (fhegg's threshold machinery:
n-of-n ceremonies with proven smudging already deployed — models governed
by quorums, not custodians). Encrypted-data fine-tuning at small scale is a
research target behind the vFHE ladder, not a current promise.

## What we deliberately do not compete on

Raw prover throughput (measured conclusion: sampling amortization beats
prover heroics, and the bubble/fusion work rides others' hardware
improvements); dedicated prover silicon (the market already selected
against it); closed anything.

## Why this point in the tradeoff space is defensible

Every pillar is either measured, machine-checked, or named-as-obligation in
public notes — and the compilation layer of the proof story (BCS, FS
transport, state restoration, accumulation depth, the audit game) is
machine-checked HERE and stubbed-or-absent everywhere else, per a
full-corpus sweep. The kernel statement layer (typed authority, canonical
transitions, receipts, hyperdocument history) exists and builds green at
3,400+ jobs. The combination — semantic statements × honest proof economics
× machine-checked compilation layer × open everything — is a point nobody
else occupies, and each factor makes the others harder to copy.
