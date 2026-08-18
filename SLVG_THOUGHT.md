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

## IV-b. ⚑ WHAT WE ARE ACTUALLY BUILDING — and the metric error to stop repeating

**2026-08-18, ember, correcting me mid-campaign**: *"we're not trying to do
more Poseidon2/s, we're trying to do **something better**."*

⚑ **Nobody wants Poseidon2 permutations.** That rate is our **Merkle-commitment
overhead — internal accounting, not output.** I measured our own tax, compared
it to a competitor's number about a task someone actually asked for, and called
the gap a standing. **A hash-rate race is adopting their scoreboard for a race
we are not in.**

**What dregg is for, and who else has each:**

| capability | anyone else |
|---|---|
| proving computation over **encrypted** data (vFHE) | **nobody** — Zama's own stated open problem |
| **per-program** circuits carrying a refinement theorem **per output** | nobody — powdr is per-*instruction* and block-granular |
| a **machine-checked compilation layer** | nobody — ArkLib's are `sorry`; Binius64, Flock, BinarySpartan: verified zero |
| training where the **accumulator IS the model**, weights encrypted | nobody |

Binius proving SHA-256 fast on a universal machine is a real achievement on a
real axis, **and it is orthogonal to ours.**

⚑⚑ **THE GAP THIS EXPOSED, which is worse than the metric error**: we have
exquisite instrumentation on the **substrate** — exact permutation counts, exact
field-op counts, phase shares, a rig that structurally refuses to mix units —
and **ZERO end-to-end numbers for any workload a person would ask for.** Not
one measurement of: a decompiled EVM program, an FHE operation with its audit,
an SGD step. *Substrate metrics are correct for substrate decisions and were
never a standing.*

**The rule**: our per-hash rate is a **cost of doing business**. The question is
whether it is **acceptable for the workloads we run** — not whether it is
competitive on workloads we do not run. *If a decompiled transfer proves in a
second, nobody cares that a SHA-256 benchmark would have been slower; if it
takes ten minutes, no hash-rate improvement fixes that.*

## IV-c. ⚑⚑ FIRST END-TO-END NUMBERS — and the axis finding that inverts the decompilation pitch

**2026-08-18, measured on hbox at HEAD** (detached clone, zero dirty, conditions
clean, packed Poseidon2 live at width 8.18) — *the first workload numbers this
project has ever produced:*
- **One dregg Transfer turn (leaf): 15.50 ms** (min-of-9, lb=6, T=8 in-pool,
  spread 1.03×)
- **One ETH finalized sync-committee update, prove+verify: 13.30 ms warm /
  82.98 ms cold** — ⚑ **6.24× on warm-up alone, and the naive way to measure it
  returns the 83.**

⚑⚑ **THE AXIS FINDING: a 6.1× difference in padded trace cells buys 1.2× in
time.** FRI floors every trace at 128 rows at lb=6, so **proof time is almost
entirely fixed cost.**

> ***This inverts the decompilation pitch.*** Killing the machine makes programs
> **small** — and small is exactly where the fixed cost dominates. **The lever
> is AMORTIZATION, not prover speed.** A decompiled ERC20 transfer being 60–140×
> smaller in constraints does not make it 60–140× faster to prove; it makes it
> **cheap to batch**, and the win has to be collected there.

## IV-d. ⚠ E5 DID NOT RE-OPEN — I had the sign backwards

I recorded that our optimizations raised the in-circuit hashing share and
therefore *helped* the binary-field case. **Wrong direction.** `R*` — the
crossover a candidate hash must beat — is **computed from** that very share:
`R* = 1 + (1/m_leaf − 1)/f_circ`. The numerator is the native-side gain
(untouched); the denominator is the **in-circuit penalty exposure** (what grew).
**So `R*` FALLS: 2.49–4.52× → 1.74–2.75×**, and binary candidates (R = 12.7–24.7×)
go from 2.8–9.9× above the bar to **4.6–14.2× above it.**

***Raising the hash share raises the payoff of a FREE hash and the penalty of an
EXPENSIVE one. It is a leverage increase, not a direction change.*** All three
premises hold; the conclusion is **hardened**, not re-opened.

⚑ **And the optimizations closed the LOOKUP door, not the binary one**:
lookup-arithmetized `R = 3.2` was a **0.79× wrap WIN** at the old share and is a
**1.15× LOSS** at the new one — *"the highest-value open measurement" crossed
out of its own band.* Mechanism, in absolute cells with no shares: the Poseidon2
half is constant at ~21.2M, so **the retune is worth ×1.400 with Poseidon2 and
×1.018 with Blake3 — the optimization and the hash swap are mutually
cannibalizing.**

⚠ Three cited numbers corrected: **"~×5" was the DERIVED row** (an AIR that does
not exist) — measured-and-proven **×3.75**, deployed **×2.10**; and **deployed
`f_circ` is 52.36%, not 36.45%** (the "pin deliberately not moved" line is
stale — `834a3f7` is an ancestor of the pinned rev).

## IV-e. ⚑ THE THREE WORKLOADS ARE UNMEASURABLE, AND WHY

- **EVM Stage 0**: its **descriptor reader and FRI backend were both deleted**
  (`d55ef32`, `b297c7d`).
- **vFHE**: the 466 µs is **homomorphic evaluation with ZERO proving** — *its own
  test says so* — and no Lean AIR exists.
- **SGD**: Lean-only, plus a 4-element F₅ table.

⚑ **One Rust descriptor reader closes routability, the units question, and
Stage-0 time-to-proof together.** *That is the single highest-leverage piece of
plumbing in the tree.*
(Null result, recorded so it is not re-proposed: **CSE on the Stage-0 descriptor
removes nothing** — 3,298 → 3,298; the u256 adder is already a DAG, and its 768
bit wires are irreducible by sharing.)

## IV-f. ⚑ ADOPT-DON'T-DESIGN IS NOT AVAILABLE ON OUR RUNG — so build, and check

**2026-08-18, ember**: *"adopting the aged thing isn't necessarily going to be
realistic, we might just need to build our own constructions."* **The week's own
evidence says so, and I had been arguing the other side on a premise that does
not hold here.**

**Why adoption fails on the binary rung specifically:**
- ⚑ **There is no aged binary-rung hash.** Our own books: Vision/Mark-32 is
  *"none found, and nobody has looked."* **CheapLunch, Perrin, Rijmen are all
  PRIME-FIELD assets.** The cryptanalytic age we kept invoking is age *somewhere
  else*.
- ⚑ **And `[M32-flag]` reaches the recommendation itself**: **Mark-32's own MDS
  IS the fast systematic-RS form — the one carrying the 3-deep invariant flag.**
  *The adoption target has the shape we rejected a candidate for.*
- **"Aged" is not tracking "safe" in this field.** In one week's reading:
  Griffin full-round broken at k=1, Anemoi ℓ=1 at 2^70, Rescue-Prime α=3 at
  2^112, Chaghri broken, Rubato broken, AIM attacked twice, Poseidon2b
  round-skipped — **and GSR just took 18 of 21 rounds of the primitive we
  actually deploy**, with *its own defense criterion as the enabling condition.*

**So the real choice is not aged-vs-novel. It is: novel-and-unchecked (theirs)
vs novel-and-checked (ours).** ⚑ **And the differentiator is not that we design
better — it is that we can COMPUTE properties designers ASSERT.** In one week
the gate: killed a candidate on an exact branch number; found an autonomous
quotient at the level a loop had skipped; **found the attacked shape inside the
MDS form our own earlier lane had blessed**; and reproduced a published table
well enough to catch its own dead guard row.

**And we already built the candidate.** The **coset novel transform** wins gate
items 1–4, has **`[WEFT-multiround]`'s quotient half discharged as a theorem at
every level**, measures **0/370 stalled trails**, carries the **one-object
prize** (`weft_one_object`: hash mixing layer *and* code encoding map, one
function), and costs **zero extra ops**. Its honest deficits are named: branch 8
(a certified *instance*) against 25 (a *theorem*), and the **trail half of
`[WEFT-multiround]` narrowed, not closed.**

> **The construction is not the hard part. The check is — and the check is the
> thing we have that nobody else does.**

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
