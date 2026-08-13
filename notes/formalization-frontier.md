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


## The wider Lean landscape (companion sweep, same skepticism discipline)

**Mathlib has ZERO error-correcting coding theory** — verified by code search:
no Reed-Solomon, no linear codes, no Berlekamp-Welch (absent from Lean
*anywhere*), no Singleton/MDS. The real Lean coding-theory substrate is
**CompPoly** (Verified-zkEVM): Gao's unique decoder fully proved (refusal
characterized as an iff!), Guruswami-Sudan list decoding proved, STARK fields
with irreducibility certificates — sorry-free in live code. Its own wiki
states its gaps: no FRI/PCS integration, and the Johnson list-SIZE analysis
unproved. Our coding-theory position should be stated against CompPoly, not
against Mathlib.

**The SP1 Hypercube FV post-mortem (2026-05-20) is the wound-class
discipline validated externally at production scale**: of 62 "verified"
opcodes, 51 complete; SLTI **vacuously true** (contradictory hypotheses);
the JALR proof **hypothesized exactly the gap that was the bug** (`h_valid_pc`
assuming the alignment SP1 failed to enforce); LoadHalf/LoadWord proved
**wrong-spec byte semantics**. Every failure mode is one of our minted
classes — premise vacuity, hypothesis-shaped holes, wrong-statement green.
The best public citation for why the carrier census and premise-inhabitation
instruments exist.

**Zcash Ironwood shipped production Lean verification**: 2,700+ theorems,
balance integrity via a knowledge-soundness extractor, triggered by a
counterfeiting bug that sat latent ~4 years. Production-scale Lean crypto
FV is no longer hypothetical — and it was motivated by exactly the class of
silent constraint-omission our discipline targets.

**The CA/MCA composition now has THREE pieces on the table**: Hirai's
FRI-RBR (needs `FRI_MCA_Hypothesis`), the IoTeX rs-proximity-gaps Lean
formalization of the **half-threshold correlated-agreement bound**
(0-sorry, audited — ⚠ its README swaps its own two eprint numbers;
2026/858 is the Lean one, cite by title), and our corpus. Whether any pair
composes is a statement-compatibility check, not a research program.

Also recorded: Isabelle/CryptHOL got AGM + KZG security first (2026/1490);
HOPSCOTCH is a second Lean game-hopping framework (unaudited); the
Hicks-coauthored FV survey's number — automated tools catch **45.7% of bugs
isolated vs 19.6% on full codebases** — is the citable gap our
whole-tree-build discipline addresses; the EF initiative is **$20M/3yr
scoped to "critical components"** — any "verify every component" citation
overclaims; verified-zkevm.org itself is an empty template.
