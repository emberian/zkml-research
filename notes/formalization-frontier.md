# The formalization frontier: ArkLib measured, Selvage positioned, one composition

2026-08-13. Two lanes (ArkLib deep-dive spot-checked by me: 416-taint baseline
and `append_… := sorry` confirmed at source; recursion survey). This note
supersedes the AGENDA Pillar V characterization of ArkLib.

## ArkLib, measured instead of assumed

Their own kernel-transitive sweep (`scripts/axiom_baseline.json`, CI
report-only): **416 sorry-tainted declarations, 133 of them security results.**
Sorried at the top: the compositionality theorems that title their RWC 2026
talk (`append_soundness := sorry` and family), every Security/Implications
textbook implication, **FRI soundness** (`fri_soundness := by sorry`), STIR
main, sumcheck end-to-end (tainted twice), the whole FS/BCS non-interactive
layer (commented-out stubs), zero-knowledge (definition commented out).

Genuinely real and kernel-clean: **the KZG binding reductions** (t-SDH/ARSDH —
the one complete crypto reduction), a strong coding-theory library (Johnson,
Berlekamp-Welch, Guruswami-Sudan, Polishchuk-Spielman, AHIV22, BCIKS20 affine
spaces; the unique-decoding half of correlated agreement proved, list-decoding
half sorried), the definitional framework, and the CWSS composition track.
ArkLibFri is a staging fork — no hidden completed FRI. The lean-lang.org
showcase overclaims vs HEAD (WHIR deleted, BCS a stub). Their RWC abstract
concedes it: "full end-to-end security proofs are ongoing."

**The only complete machine-checked FRI RBR soundness anywhere: Hirai's
standalone `zksecurity/simple-rbr-fri`** — 4,068 lines, **zero sorry, zero
axiom** (spot-verified), Theorem 5.2 of eprint 2025/1993, **conditional on
`FRI_MCA_Hypothesis`** (mutual correlated agreement, explicitly assumed). And
its README: "Most of the formalization was done by Aristotle. Claude Opus-4.5
and Sonnet-4.5 were useful in the last stages too." **The
too-hard-before-AI thesis is already being executed by others.**

## The composition sitting on the shelf

Hirai proved FRI-RBR **modulo MCA**. Our trees hold the largest body of
machine-checked correlated-agreement work in existence (the breadstuffs
campaign; Selvage's CorrelatedAgreement + regime interfaces). **If our CA
statements can instantiate his `FRI_MCA_Hypothesis` — even at unique-decoding
parameters — the composition is the first unconditional machine-checked FRI
RBR soundness theorem.** Honesty gate first: our sharp CA results live at toy
domains (2^4–2^7); the composition claim must be stated at the parameters it
actually holds. Checking statement-compatibility is days, not months, and his
repo is Apache-2.0 mathlib-pinned Lean 4.

## Selvage is already the recommended frontier — unimplemented

The recursion survey's verdict: the technique the 2024–26 literature
recommends for hash-based recursion — **WARP-style accumulation (2025/753)** —
is **already formalized in minidregg/Selvage, 48.5K lines, zero sorry by
grep** (build pending — the rename build doubles as this check), including:

- `Depth.lean` (2,025 lines): WARP's Thm B.4 depth composition
  machine-checked, **including a proof that the paper's as-stated theorem is
  FALSE at a corner** (`OB2_depth_composition_false`, the `Z = ∅` corner) with
  the one-guard repair. A machine-checked defect in a published construction.
- FS-of-RBR with an inhabited lazy-sampling ROM handler; the grinding
  try-count theorem; accumulation at the deployed BCS alphabet with erasure
  extractors.

Absence verified: nobody else has machine-checked recursive/accumulation
soundness end-to-end (ArkLib's composition is sorried; Hirai is base-protocol
only; StarkWare stops at the AIR).

**⚑ The gate, stated plainly: Selvage is 48.5K lines of theory about an
object that does not run.** minidregg/prover is 3,161 lines of kernels with
no accumulator; breadstuffs runs 67K lines of the OLD architecture
(`accumulator.rs` re-verifies FRI in-circuit at every link, ~1,000–3,000
Poseidon2 perms/step vs accumulation's t Merkle openings + two sumchecks).
The migration from in-circuit-verification-per-link to
accumulate-then-decide-per-epoch is THE implementation work, and it turns the
depth theorem into a statement about a deployed object.

## Recommendations adopted from the survey

- **Decode loop**: WARP-shape accumulation (not folding — avoids in-circuit
  verification), with **Deep Thought's memory technique (2024/325)
  transplanted** for KV-cache state — prover cost independent of memory size;
  NOT its Pedersen instantiation. The transplant is unclaimed.
- **vFHE streams**: STARKPack (2024/661, measured: 2.2× verify at 9 traces)
  within a batch; the running accumulator across time.
- **Compression**: keep the measured shrink+wrap (40.2× from native hashing);
  make in-circuit verification once-per-epoch, not per-link.
- **Number honesty carried**: ARC's 32-opening figure assumes list-decoding
  conjectures from the family 2025/2046 refuted; unconditional is 64 openings
  → the accumulation-vs-Fractal win is ~2.75×, not 5.5×. The entire lattice
  folding race (LatticeFold±, Neo, Symphony, Deep Thought) is
  **estimate-only in its own papers** — measured things: BOIL, STARKPack,
  SwitchFold, and our own plonky3-recursion fork.
- Delta items for minidregg's own survey docs: FICS/FACS (WARP wins;
  Remark 1.1 is the why), Symphony's fold-to-SNARK-without-FS-in-circuit
  compiler, ProtogaLattice (4 RO calls/iteration) if the lattice branch is
  ever re-priced, SwitchFold's code-agnostic PCS switching.
