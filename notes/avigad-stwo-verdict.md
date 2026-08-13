# The Avigad/StarkWare S-two formalization — verdict and two imports

2026-08-12. Lane report distilled; repo at `~/src/formal-proofs` (build cache
deleted, source kept). Seven authors — Avigad plus six StarkWare staff.

## Verdict: it is the twin, chosen deliberately, carrying a real theorem

Hand-written Lean model of the Rust AIR-builder; provenance is pasted Rust
snippets in docstrings; no extraction, no emitted artifact, no differential
test. The paper says it plainly (§2.4, §6), and the drift is already in-tree —
`IdToBig.lean:19` carries an engineer's note that the Lean does not model the
Rust range-check table selection. The exact failure mode our house law exists
to prevent, in the genre's reference implementation.

AND: `trace_sound` is real — kernel-clean (3 standard axioms), zero live
`sorry` in its closure, the CASM CPU core proved sound against the VM
semantics, with genuine catches (an increase-ap invariant bug; logup security
bits raised). Scope stops at the AIR: no FRI, no Merkle, no Fiat–Shamir, no
completeness, no probability space (cardinality bounds; "challenge misses the
bad set" is a hypothesis). Recursion opcodes and all builtins/hashes uncovered.

**The premise is unaudited.** Nothing in their repo inhabits
`LookupsSatisfied`; the bridge hypotheses (`h_satisfied`, `h_use_agree`,
`h_yield_agree`) assert unmodeled Rust bookkeeping did the right thing, and no
instrument would notice if they were mis-stated. Not a vacuity claim — a
missing-instrument claim. Our carrier-census discipline is the thing they lack.

## What is actually worth building here

"We do Lean" is no longer a differentiator: StarkWare runs a funded in-house
Lean program; ArkLib covers IOR/FRI/sum-check abstractly; a Rust→Lean pipeline
(2605.30106, Charon/Aeneas/hax) is attacking the twin problem directly on
Plonky3 and RISC Zero. What is still worth our building, because it is true and missing:

1. **Verified table CONTENTS against a mathematical spec.** StarkWare
   explicitly carved this out — `h_rc` is an assumption, "must be verified
   separately." Their tables are `[0, 2^k)`; a theorem that *this table is
   GELU to within stated semantics* is unclaimed by anyone.
2. **Emitted-artifact verification in the IR-v2 rail** — with the glass-house
   caveat that our own retired `lean_descriptor_air.rs` rail has faithfulness
   theorems on a path nothing runs.
3. **The FRI/proximity cone** (40K lines, 1,537 theorems — larger than their
   whole S-two dev) — the layer they stop before, where the conjectured leg
   lives. Honesty required in any pitch: our sharp results are at domains
   2^4–2^7 vs their production 2^19+, and ~30 residuals are named hypotheses.

## Two imports

1. **`combine.lean`'s restricted-bad-set trick — portable NOW.** Tuple→field
   compression via `Σ aᵢαⁱ` with badness defined *relative to the conclusion*
   (α bad only if it hides EVERY violation) gives a bad set linear, not
   quadratic, in partition size. Our LogUp has no tuple-compression step at
   all. Any bus-based AIR needs it.
2. **A conditional route past the `CommitSurface`-injective floor**
   (breadstuffs apex). Their move converts "encoding must be injective" into
   "the challenge must miss a small bad set" — sound because α is sampled
   AFTER the tuples are fixed. Our `finCommitSurface` is a fixed `compressN`,
   injectivity false at BabyBear width. The trick transfers ONLY if the commit
   surface is redesigned to bind through a Fiat–Shamir-sampled α. A real
   design change — but a known one with a worked, kernel-clean precedent,
   which is more than the apex floor had yesterday.

Swarm hazard recorded: a concurrent session clobbered a scratchpad file
mid-lane (generic filename collision); the lane caught it by a line-count
mismatch and re-verified every citation from unique paths.
