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


## The closing synthesis: six unclaimed positions, three moves

The frontier lane's final scoreboard (multi-agent, self-correcting — it
retracted its own LogUp-first claim after finding StarkWare's S-two dev
verifies LogUp; positioned the sponge asset honestly; and censused
Isabelle/STARK: 5,476 lemmas, 0 sorry — **and its headline soundness bound
has never been exhibited below 1**, no proximity leg, GF(5) only — the
cleanest external specimen of the vacuity class, landed ten days ago).

**The tree's genuinely unclaimed positions, in order:**
1. **BCS transform soundness** — stub in ArkLib, absent everywhere else;
   ours proved at the deployed root-and-columns alphabet.
2. **RBR→Fiat–Shamir compiler theorem** — absent everywhere; ours
   unconditional at (t+k)·ε_rbr.
3. **State-restoration soundness** — absent everywhere; ours proved.
4. **Sponge indifferentiability in a foundational prover** — first ever
   outside EasyCrypt'19 (the only one in existence). ⚠ Re-aim needed:
   indifferentiability does NOT close [FS-ROM] for knowledge soundness
   (2025/536 §2.3 verbatim); extraction-friendly indifferentiability gets
   the first AND the closure.
5. **An instantiated two-sided soundness bound < 1 at deployment
   parameters** (2^-56 < error ≤ 2^-55, dominant term named). Hirai:
   uninstantiated. Isabelle: never shown < 1. ArkLib: no statement.
   **Nobody else has a number at all.**
6. **Grinding necessity** — everyone else proves sufficiency only; ours
   exhibits 9/25 > 1/5 exactly.

**The edge, named**: everyone else has legs and no composition, or
composition and no legs. The tree owns the COMPILATION half of the stack —
BCS, RBR→FS, state restoration, sponge, and the arithmetic that turns it
into one number.

**Three moves:**
1. **Compose, don't re-prove**: port ArkLib's Polishchuk–Spielman + take
   their proved unique-decoding CA as realizer + discharge Hirai's h_mca =
   **the first unconditional machine-checked FRI RBR soundness theorem,
   assembled from three trees none of which can do it alone. Days.**
2. **Plug FRI into Chiesa–Orrù Corollary 1** — generic in ε^sr, zero
   occurrences of "FRI" in it; our FS-of-RBR keystone + BCS instance are
   the scarce half.
3. **Ship the two-regime security calculator** — ErrorBudget/MixedField/
   PowGrinding generalized over {regime, code, field, extension, grinding},
   reproducing S-two Tables 5–6 as Lean-computed two-sided bounds with the
   regime tag IN THE TYPE. The corroborating need is overwhelming (Isabelle
   bound never < 1; the retracted EasyCrypt LPZK proof — wrong at the
   DEFINITION layer; "no zkVM has end-to-end FV" per 2607.23752).

**And the Proximity Prize's Grand MCA Challenge — $1M, $0 awarded — asks
for δ* WITH a matching lower bound proof: our prove-the-floor-FALSE law,
written by someone else, as a prize.**

Unresolved and flagged: CatCrypt (172 protocols claimed "Novel" incl. FRI/
STARK/PLONK, built in 2 months with GenAI, **main repo private** — the
single largest unknown; if real it claims several positions above);
`lalalune/ArkLib` advertises sorry-free MCA theorems whose files do not
exist at HEAD (unexplained); ArkLib total sorry count differs between
censuses (244 vs 310; load-bearing ones verified individually); ~/paperbin
needs dedup (~120 new PDFs, duplicates under different names, IoTeX
numbering reversed in several filenames — authoritative: 2026/858 =
Threshold Halving, 2026/861 = Action–Orbit).


## Final refinements from the full landscape survey

**Two firsts DOWNGRADED, honestly:**
- **Sumcheck is not a first**: Isabelle AFP has soundness AND completeness
  (CSF 2024) — the first machine-checked sumcheck happened in 2024. A Lean
  sumcheck with *RBR knowledge* soundness would still be first-in-kind
  (ArkLib's is sorried), but the headline is gone.
- **LogUp is not a first**: StarkWare verified the LogUp protocol inside the
  S-two development (main files 0-sorry). A standalone IOP-framework LogUp
  theorem is still open, but must be positioned against 2606.04311 §5.

**The window warning on position #2 (list-decoding-regime CA)**: this is the
hottest race in the field — the $1M Proximity Prize, IoTeX's days-old
self-published claims (2026/858 Lean-formalized half-threshold bound;
2026/861 conditional on a "sparse-worst-case dominance" conjecture —
unaudited, prize-money context), and **deltastar.computer**, now identified:
an **agent-swarm formalization campaign** ("Pinning δ*") mining MCA
thresholds over an ArkLib fork — issue #444 has 1,321 comments — with
kernel-checked results labeled proven/computational/open. (The companion
lane found its advertised sorry-free files absent at the fork's HEAD, so
claims ≠ audited artifacts — but the campaign is real.) **Agent swarms are
already racing in exactly our zone. The window is months, not years.**

**Confidence-ranked firsts, final form**: 1. sponge indifferentiability in a
foundational prover (HIGH — only EasyCrypt CCS'19 exists anywhere, nothing
quantum); 2. list-decoding-regime CA (HIGH, window warning above);
3. RBR→FS compiler + BCS end-to-end (HIGH — stubs and roadmaps everywhere,
work nowhere); 4. state-restoration soundness (HIGH — mechanized nowhere);
5. instantiated FRI bound < 1 at deployment parameters (HIGH — both external
attempts stop exactly where the difficulty lives); 6. light-client
soundness (MEDIUM-HIGH — least competition, least external legibility);
9. ZK simulator/extractor for a hash-based succinct argument (MEDIUM —
nothing public for STARK/IOP-based ZK).

**The confirmed 2025/1993 posture**: the Garreta–Mohnblatt–Wagner paper
explicitly frames itself as "a template for formal verification efforts" and
cites Ethereum's ambition of formally verifying the stack — the ecosystem's
gravity (Vitalik's July "Lean Ethereum" roadmap: recursive STARK
verification + PQ + FV as a pillar) points at exactly the compilation layer
we hold.

**Bottom line, from the survey verbatim**: "your four biggest holdings map
onto the four biggest verified gaps… both external attempts stop
conspicuously exactly where your FRI-reality memory says the difficulty
lives."
