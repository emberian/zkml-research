# SLVG_THOUGHT — what Selvage is, believes, and intends

2026-08-17. The synthesis after the campaign. `docs/VERDICTS.md` holds current
truth claim-by-claim; this file holds the *shape*. When they disagree,
VERDICTS wins on facts and this file wins on intent.

## I. What Selvage is

**The machine-checked compilation layer of proof systems** — the stratum
between "an interactive protocol is round-by-round sound" and "a deployed
non-interactive verifier accepts only true things" — held as **a bag of
composable formal ingredients, not a product.** Nobody else has both legs:
ArkLib's composition theorems are `sorry`; the fast systems (Binius64, Flock,
BinarySpartan — verified at source) carry zero formal content; the one
EF-funded formal effort has 33 sorries in its Binius leaves and no soundness
statement for its own FRI. We are doing **basic research**: chart the
landscape, formalize what is statable, price what is measurable, and keep
every design axis mutable until a measurement or a theorem pins it.

## II. The five load-bearing ideas the campaign earned

1. **Materialize vs virtualize** (née "boundary vs interior" — the literature
   calls it *polynomial virtualization*, and what is ours is the measured
   EXCHANGE RATE and the threshold rule). An AIR commits the Cook–Levin
   witness; a virtualizing sumcheck commits the original NP witness. The fork
   is priced per program point, never assumed.
2. **Counts are the instrument; the clock is a guest.** Exact operation counts
   are deterministic, contention-immune, reproduce to the unit across
   machines and build profiles. A percentage without its denominator is not a
   measurement; a work claim and a latency claim may never share a number
   (`compose()` refuses). The rig enforces this by construction.
3. **The regime lives in the type.** UDR/JBR/withdrawn-CBR errors are
   different types; `cbr_not_reportable` is a theorem; every soundness figure
   carries its regime or it is not a figure. (Deployed: UDR 34 — honesty
   first, then repair.)
4. **Vacuity is a family, and every instrument is blind to the next member.**
   Uninhabited carriers; empty events; trivial existentials; models too weak
   to express the attack they rule out; anti-vacuity teeth that are
   themselves vacuous; impossibility proofs downstream of their subject. The
   gates exist (char-2 census, anti-vacuity ledger, axiom pins that caught a
   `sorry` in a *statement*), and the class test is **refutability, not the
   witness's sincerity.**
5. **The relation is the attack surface.** A hash's cheap verification
   relation is exactly what FreeLunch-style attackers model. The surviving
   design target: cheap in the proof system's operations, expensive in the
   adversary's algebra — `x⁻¹`, dense linear layers, lookups; never a
   witnessed low-degree graph.

## III. The composed architecture (each layer priced or proved)

```
EVM decompilation          ← static half; ~60–140× past the switchboard;
  (program-granular,          decompiler UNTRUSTED via per-output TV;
   no machine left)           Stage 0 = five opcodes end to end
switchboard (pay-per-use)  ← dynamic half; needs free zero-commitment
committed memory           ← Nebula Lemma 2 ⟺ our TwistContinuity;
                              NOT DL-bound; machinery on shelf
PQ folding                 ← Nova-shape over the dual-mode MSIS commitment;
                              4–8% of the FS bill it rides beside
dual-mode ring object      ← one artifact: MSIS commitment (linear mode)
  (q = 2⁶⁴−257, τ = 2)        + FS hash (full mode); openings never cross
                              the de-linearizer
```
Beside it, three tracks that feed it:
- **The binary path**: additive BaseFold landed; ring-switching connectors
  landed; ordered-basis binding CLOSED (the gap three sources agreed on);
  Ligerito priced at 12 lemmas with the errata display-only; Spartan modeled
  and composing. The DL dividend (~10³× at the seam) is what the dual-mode
  folding exists to close.
- **Zero-emulation vFHE**: the limb primes are greenfield — 2-adicity-24
  replacements sieved and concrete, classic FRI over each limb's own prime at
  overhead 1.00×; cross-limb provenance bound algebraically by Z_Q sumcheck
  (the forgery *unwritable*); the rescale proved impossible for any Z_Q
  polynomial, so Hole B routes through the basis witness or single-prime.
- **Dark training**: SGD steps as three openings; low-rank chains where the
  accumulator state IS the model; break-even in STEPS (T=128), not rank;
  weights encrypted because the substrate must never hold a readable mind.

## IV. The deployed system, honestly

BabyBear + Poseidon2 (triple-confirmed: 30.6–210× in-circuit, recursion pins
it in both characteristics, the lookup escape measured shut at 1.96×) + FRI at
lb=6 (the MINIMUM of its iso-security grid) + the landed wins: LDE layout
(byte-identical), grind schedule (byte-identical witness, 10.6× critical
path), batched reduced opening (×1.436 wrap cells, VK-rotation only), packing
grid (×2.011 cumulative measured, ×2.23 derived, **wrap at K≠2 not yet
PROVEN** — the standing tooth). The leaf is too small (K = 26.9 vs their <1):
the architectural lever is making the leaf carry more, not swapping systems.

## V. Method, compressed to what survived

Write the note first, incrementally. Read the binders, not the docstrings.
Read the blocker at source before relaying it. A confession's location list
needs the same grep as a claim. Absence claims carry corpus AND instrument
(paperbin first — four refutations were sitting in it). Exploratory
formalization beats dismissal-by-scoping. A mild "why are we doing X?" from
ember is a stop-work order that has not raised its voice yet. Verification is
a gate on claims, not a source of them. And what is "ours" is the wrong
question — the advantage of holding the full stack is the JOINS.

## VI. Open, ranked

1. Prove a wrap at K≠2 (banks ×2.011). 2. `TwistContinuity` via Nebula
Lemma 2. 3. `AccRbrFold` (folding at the commitment alphabet). 4. EVM
Stage 0. 5. The dual-mode's O2 (sponge indifferentiability — the one wall).
6. [WEFT-subspace] via the branch-number scripts. 7. The one-handle PCS
obligation (Z_Q). 8. H1 at the new limb primes. 9. Knowledge soundness
tree-wide (`Unit` witnesses). 10. The `num_queries` pin push to breadstuffs
(ember's, outward-facing).
