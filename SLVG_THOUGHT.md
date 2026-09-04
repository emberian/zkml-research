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

> ⚑ **2026-09-04, re-measured** (`notes/formal-delta-2026-09-04.md`). The claim
> survives in ArkLib's own words — its 08-29 status doc: *"unrestricted stateful
> composition theorems remain admitted"*; BCS and FS transfer are Phase-6 roadmap;
> `BCS/Basic.lean` is an 81-line stub, `fiatShamir_completeness := sorry`, every
> `seqCompose_*Soundness` is `by sorry`. **Three wordings above were wrong**:
> ArkLib *has* FRI and Binius soundness **statements** (13 `*_rbrKnowledgeSoundness`
> in Binius), all sorry-tainted — say "admitted statements", not "no statement";
> the Binius leaves carry **32** sorries, not 33; and ArkLib's kernel sweep now
> reads **314** sorry-tainted declarations (was 416), 123 security results (was
> 133). Two things nobody had: **better.codes** (EF FV team + Yukon + zkSecurity,
> 2026-08-20) runs a Lean-kernel-checked, axiom-gated two-sided leaderboard for a
> KoalaBear-sextic IRS at ρ=½ — **[68.02, 116.13] bits** — explicitly "not a
> full-protocol security claim"; and VCVio landed a kernel-clean Σ-protocol
> Fiat–Shamir EUF-CMA (Apr 2026) plus **sorry-free Merkle multi-extractability**
> (09-01). So: our composed FS+FRI+grinding two-sided number is unique *in kind*,
> and "RBR→FS absent everywhere" must be scoped to **IOPs**.

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

## IV-g. ⚑⚑ TWILL — our construction, with a round count that is DERIVED

`notes/weft-c-spec.md` (1,191 lines) + `notes/weft-c-scripts/`.
**Twill = Vision Mark-32's field, geometry, `x⁻¹` S-box and two-step round,
with its MDS replaced by the one-transform coset novel transform.** *One
component swapped, on the one axis we computed.* GF(2³²) Fan–Paar tower, t=24,
rate 16 / capacity 8, four free conditions made **normative**, the `B`/`B⁻¹`
layer **kept with a computed reason** (without it the constant-free round is
`K*`-equivariant — *a shape nothing in our gate can see*), coefficients fixed by
a derivation rather than left as a hole. §1h is a complete implementer's block.

**R = 26 S-box layers = 13 Vision-rounds**, from **seven legs stated separately
with their instruments named** — three exact-defense and measured, one
exact-attack derived, three **labelled inherited**, and the binding one
(Gröbner/CICO, no defense-side bound in either direction) corrected outward by a
**stated empirical prior (×2.1, six instances, labelled a prior not a bound)**.

⭐⭐ **AND THE HEADLINE: branch 8 vs branch 25 does not move the round count AT
ALL.** Every statistical leg clears well inside the algebraic demand — on
**both** sides, with the linear half now `B_l ≥ 8` **proven**. ***The 3× branch
gap is worth ZERO rounds*** (and costs 1.68× native mixing to obtain).
⚑ **The derivation is calibrated**: fed Mark-32's own uncorrected legs, it
returns **exactly Mark-32's 16 steps.**

## IV-h. The adoption target has TWO confirmed defects

- ⚑⚑ **`[M32-flag]` CLOSED as a confirmed defect.** Mark-32's split is the
  natural one — **its own prose says so** — and both halves are coset unions,
  so **its deployed MDS carries the 12 ⊃ 6 ⊃ 3 block-constant flag,
  `deg(minpoly) = 6`, and GF(2⁸) entries: a 2¹⁹² closed set.** A random-split
  control shows none of it.
- ⚑⚑ **`[M32-floor]`, new**: Marvellous (2019/426 §5) recommends `2⌈n/5.5m⌉`
  rounds ***"with a minimum of 10 rounds."*** At m=24 the formula is **vacuous
  — so the floor WAS the number — and Mark-32 ships 8.** *It kept the
  extrapolation and dropped the distrust the floor encodes.*
- ⚠ **And we have been counting its rounds wrong by 2×**: "8 rounds" is **16
  S-box layers / 384 inversions.** The `~3.2× cells/bit` headline inherits the
  error.

## IV-i. Two method laws earned here

- ⭐ **`[WEFT-multiround]`'s trail half now BEATS the generic bound**: 4-step
  minimum active S-boxes **≥ 17 (generic 16)**, ≥ 22 on the cheap route —
  **exactly eight weight-4 codewords in closed form, and no out-support is an
  in-support, so they do not chain.** `|S|=3` closed exhaustively (0/2024).
- ⚑ **A tool's reach is decided by GROUND-FIELD MATCH *and* whether the
  quantity it bounds is STILL MOVING — not by whether a design "feels"
  classical.** *This refutes my own hypothesis*: CLAASP's ground field is `F₂`,
  so **Twill is CHEAPER to express than the gadget-Feistel** (one
  `linear_layer` component per layer) — **and it still buys nothing, because
  `x⁻¹`'s maximal `F₂`-degree saturates the bounded quantity in two steps.**
- ⚠ **Cost verdicts are instrument-dependent**: *"mixing dominates"* is true in
  software and **false on Mark-32's own FPGA numbers** (S-box 80.4%, MDS
  18.4%). Twill at 26 steps is **0.97× Mark-32-at-16 in software and ≈1.5×
  against us on FPGA** — both in the record.
- **Guards fired twice on its OWN instruments**, neither a failure in the code
  under test: a search pruning on genericity **missed a constructive witness
  and reported a clean, wrong 0**; a mutation aimed at a column no witness
  reads reported a **dead 8 vs 8**.

**Standing verdict unchanged**: the char-2 hash slot does not exist (no char-2
AIR, no constraint evaluator, no witness-gen). **This makes the object ready and
defensible, not deployed** — and `cosetPack` survives as the code's encoder
regardless. ⚑ **The fork is now visible with both sides priced: adopt a
published design with a measured structural defect and a round count below its
own strategy's floor, or build one with the defect repaired and no record at
all.**

## IV-j. ⚑ THE PARETO LEDGER — what actually got strictly better

Ember asked the question that should be asked more often: *"have we advanced the
Pareto frontier of any construction at all?"* **Answered from the record, not
memory. Yes — substantially on the proof system, once on a hash component,
nowhere on a hash primitive.**

**Strictly better at the same or less cost, MEASURED and LANDED:**

| construction | move | factor | why it is Pareto, not a trade |
|---|---|---:|---|
| wrap cells — batched reduced opening | 58.2M → 40.6M | **×1.436** | **child proof BYTE-IDENTICAL**, VK rotation only |
| wrap cells — packing K16/rec4 | 40.6M → 29.0M | **×1.400** | **PROVEN, and a corrupted trace refuses** |
| **⇒ cumulative on the wrap** | **58.2M → 29.0M** | **×2.011** | ***same security, half the object*** |
| LDE layout (quotient batching) | phase ×3.57–4.07 | ×1.19+ prove | **proof bytes byte-identical at b=2..8, no flag day** |
| grind schedule (windowed min) | crit path 20,766 → ~1,960 | **×10.6** | **witness byte-identical**; total work +12.6% (a latency claim, kept separate) |
| Poseidon2 chip — `permEmissionNarrow` | 352 → 141 lanes | ×2.34 cells | identity over ℤ, **degree 7 on both arms**, 11 artifacts byte-identical |
| ⚑ **Weft mixing — coset repair** | branch 6 → 8, flag 4-deep → **none** | **ZERO extra ops** | ***strictly better security at identical cost — the cleanest Pareto move of the campaign*** |
| Poseidon2 `R_P` reallocation | same 215 S-boxes | **48 : 1** | *derived, not landed* — from Poseidon's own objective |
| leaf sponge rate | rate-8 → rate-16 | ×0.777 native | **we shipped the TEST convention; the pinned p3's own examples use rate-16** — free |

⚑ **The two that are Pareto in the strict sense — better on one axis, worse on
none — are the coset repair (security up, cost identical) and the `R_P`
reallocation (margin up, S-box count identical).** *Both came from computing
something a designer had asserted.*

**And the honest negative, stated as plainly:**
- **No new hash primitive is deployed or even derivable** — `NR=16` remains
  precedent, and four instruments have reached the gadget-Feistel exactly once,
  for 2 rounds.
- **The char-2 slot does not exist** (no char-2 prover), so **Twill is
  ready-not-deployed.**
- **Nothing here beats binius on their axis**, and *which axis to measure on* is
  still open.
- **The three end-to-end workloads remain unmeasurable** — a deleted descriptor
  reader, no vFHE AIR, a Lean-only SGD.

> **The pattern worth keeping: every Pareto win came from MEASURING something
> that was previously ASSERTED** — a packing default nobody had swept, a
> quotient-chunk batching nobody had profiled, a grind schedule nobody had timed
> at thread counts, a point set nobody had varied, a round-allocation nobody had
> differentiated. **None came from inventing anything.**

## IV-k. ⚑⚑ DECIDABLE-BY-DESIGN: the ceiling, stated as a positive result

`notes/decidable-by-design.md` (`1b94bed`) + four reproducing scripts.

⚑⚑ **THE `x⁻¹` TENSION I FLAGGED DISSOLVES — it was never a tension.**
***FreeLunch-modelable = Gröbner-decidable = attackable-with-known-cost is ONE
property***, and un-modelable = non-decidable = conjecturally-secure-unproven is
its complement.
> **No (decidable ∧ secure) corner exists via this route: the certificate of
> decidability IS the attacker's input.**
`x⁻¹` full-inverse layers **refuse decidability on purpose** — and **2025/259 is
the record of what happened to the designs that accepted it: Griffin, Arion,
Anemoi and Rescue-512 all fell.**

**The Gröbner leg does not collapse — it FACTORS**, and that is the result. The
**decidable half is the ideal degree `D_I`** (corroborated at source by Perrin's
own conclusion slide: *"the 'boring/fastest' step of PoSSo is the only one with
a reliable complexity ⟹ security arguments based on `D_I` are the future!"*).
The **argued half** is the exponent `ω′ ∈ [1,3]` in `cost ≈ D_I^{ω′}` (his open
*"D_I vs D_2I?"*) **plus the minimization over models — the encoding-discovery
problem, which is not decidable.**

**And the trail→differential gap does not collapse for a KEYLESS hash — with
the reason named.** Vaudenay's decorrelation bias bounds distinguisher advantage
**as an average over a secret random key.** ⚑ **A hash permutation is keyless,
so the averaging that would close the gap is unavailable. The gap is structural
— it is exactly where keyless-ness bites.**

**Answering my own Q1, and it kills the proposed gate item as stated**:
**verifying regularity of arbitrary top-forms IS a Gröbner basis in disguise** —
it moves the intractability and saves nothing. **Only the CONSTRUCTIVE FreeLunch
certificate is cheap** (measured **6–45× faster** than the actual GB). So the
gate item is ***"exhibit a FreeLunch order or prove none exists"***, not "test
regularity" — ⚑ **and it can BLOCK a candidate but never BLESS one, because it
decides a per-model upper bound and never a floor.** For **Bobbin**: its `xy=1`
model is **not** directly FreeLunch (products chain-collide), so **its Gröbner
leg is argued, not decided — the degree-2 cell bought no decidable floor.**
⚑ **Consequence worth keeping: the cheapest in-circuit S-box and the
FreeLunch-modelable S-box are DIFFERENT S-BOXES.**

**The meta-rule the three mechanisms unify into**: ***the structure that makes a
question decidable is the structure an attacker reads.***

**And the ceiling, stated as a positive result — the honest maximal claim:**
> **Assumption surface = {one ideal permutation}. Of seven attack classes:
> FIVE decided by terminating computation, ONE decidable per-model as an upper
> bound, ONE irreducibly argued** — each with its structural cause named.
> **Not information-theoretically secure (that would be false). This is the
> strongest true statement available for this class of primitive, and nobody
> has written it down.**

⚠ And the sketch built decidability-first (**SETT**) makes 5 of 7 legs decided
and is **cost-dead on diffusion latency** while moving nothing on the binding
leg — *"decidability-primary is a design LENS, not an OBJECTIVE."*

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
