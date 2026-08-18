# The fastest oracle — the CR-vs-RO split verified at our call sites, and five roads priced

2026-08-18. EXPLORATORY RESEARCH lane. Brief: test the organizing idea that **we spend one
primitive (Poseidon2) on two different requirements** — collision resistance for the Merkle tree
(the O(trace) job) and RO-likeness for Fiat–Shamir (the O(rounds) job) — then chart SIS nodes,
algebraic fingerprints, tree arity, SIMD-shaped hashes, and code-based commitments.

Labels: `[MEASURED]` (run this lane, artifact named) / `[READ]` (at source, file:line or
paper §) / `[DERIVED]` (arithmetic on measured counts) / `[RECALLED]` (sibling note).
Substrate: nothing here authors a constraint; the only code written is a bench and a model
script (`fastest-oracle-scripts/`), both validated against deployed measurements.

---

## 0. THE ONE-BREATH ANSWER

1. ⚑ **The JOB split is real and now exactly measured: the CR job is 92.0% of the prover's
   Merkle-commit permutations, 81.6% of all prover hashing at deployed knobs, and 70.8% of the
   wrap's in-circuit permutations.** The RO job is the remainder — and natively it is mostly the
   PoW grind, not the challenger.
2. ⚑⚑ **But "pay only CR prices for the tree" has no proof route, and this is a theorem-shaped
   fact, not caution.** Every known soundness track for the *compiled, non-interactive* object
   models the tree hash as a random oracle for **extraction** (BCS via 2023/1071 Thm 3.15; the
   2026 duplex-sponge modularization 2025/536 still carries the tree's κ_MT term); a merely-CR
   tree provably CAN kill FS-Kilian **for any FS hash including a true RO** (2019/997); and the
   one production system that put a SIS hash in its commitment (Vortex/Linea) writes plainly
   that *"the hash function used in the construction of the Merkle tree needs to be modeled as
   a random oracle for the scheme to retain extractability"* (2024/185).
3. ⚑ **What the split DOES license** — and this is the harvest: the tree hash need not be the
   challenger's function, need not offer duplex/sampling service, and its call geometry is
   free. The measured harvest of that freedom: **a width-24 rate-16 leaf sponge cuts native
   Merkle-commit ×0.777** `[MEASURED]`, sequenced behind the narrow-AIR landing to also win
   in-circuit (×0.871). **Tree arity is a null knob (×1.00–1.03), settled exactly** — the FRI
   result generalizes to the tree, and for the same reason: nodes are 8% of the job.
4. **Of the charted directions, none crosses the incumbent** on the recursion-facing layers:
   SIS nodes die three separate deaths (§2.1), fingerprints cannot precede their own challenge
   (§2.2), SIMD-shaped hashes fail `R*` by 4.6–14.2× (sibling-settled, §2.4), and code-based
   column commitments are the blowup-drop lever wearing a bigger verifier (§2.5).
5. **The two winners are both boring and both computed here**: the leaf-rate change (§2.3) and
   **swapping the grind hash** — the one place in the deployed stack where a traditional hash
   wins, because its in-circuit check runs once, not per-query (§2.6a): ~8–14% of a deployed
   prove for +9,168 one-time wrap cells.
6. ⚑ **The fixed-cost bound caps the whole lane**: FRI floors every trace at 128 rows and a
   6.1× padded-cell reduction bought 1.2× in time (e5-rederived §4c). A faster oracle helps
   the layers that are NOT floor-bound: the wrap/tower proves (large traces, hash-bound at
   every feasible blowup) and the wrap's committed cells. It does nothing for small leaves.

---

## 1. THE SPLIT, VERIFIED AT THE CALL SITES

### 1a. One primitive, four roles `[READ]`

`circuit/src/plonky3_prover.rs:53-81` (and the recursion tower via
`circuit-prove/src/plonky3_recursion_impl.rs` → `Poseidon2Config::BABY_BEAR_D4_W16`):

| role | type | job |
|---|---|---|
| Merkle **leaf** | `PaddingFreeSponge<Perm16, 16, 8, 8>` — rate 8, cap 8 | CR (binding rows to a digest) |
| Merkle **node** | `TruncatedPermutation<Perm16, 2, 8, 16>` — 2:1 | CR (binding digests upward) |
| **challenger** | `DuplexChallenger<BabyBear, Perm16, 16, 8>` | RO (challenge derivation) |
| **grind** | `GrindingChallenger::grind` on the same duplex | RO (PoW unpredictability) |

All four are the same `Poseidon2BabyBear<16>`. One primitive, one parameter set, one security
margin — for two different requirements. The brief's premise is confirmed at source.

### 1b. The transcript wiring — and a correction to the brief `[READ]`

What the challenger observes/samples, verified in the vendored/pinned code:

- shape data, trace root, preprocessed root, public values → sample α
  (`uni-stark/src/verifier.rs:361-379`);
- quotient root, optional r-commit → sample ζ (`:380-391`);
- **the OOD opened values ARE absorbed** — `two_adic_pcs.rs:966-971` ("Write all evaluations
  to challenger"), prover mirror at `:823`;
- per FRI round: fold-commit root observed, **commit-phase PoW witness checked**, β sampled
  (`vendor/plonky3-fri-82cfad73/src/verifier.rs:219-225`); final poly observed (`:238`);
  arity schedule observed (`:250`); **query PoW witness checked** (`:254`); query indices
  sampled (`:268`).

⚠ **The query-phase Merkle openings and sibling paths never touch the challenger.** They are
checked against the roots by `verify_batch` outside the transcript. The brief's parenthetical
— "the Merkle path enters the FS transcript (it does, via the leaf sponge)" — is **false as
wiring**: what enters the transcript is the **root**, which is the leaf sponge's and the
compressions' *output*. The subtlety ember flagged is real, but it lives one level up — in
what the **security argument** demands of the tree hash (§1d), not in what the transcript
absorbs.

### 1c. The job split, in exact counts

Native prover, deployed point (b=6, q=19, pow=16) `[RECALLED phase-profile §7 + MEASURED
split, §2.3 below]`:

| job | perms | share of prover hashing |
|---|---:|---:|
| CR: Merkle-commit leaf sponges | 195,072 | 73.6% |
| CR: Merkle-commit node compressions | 16,893 | 6.4% |
| CR: FRI-fold Merkle | 4,413 | 1.7% |
| **CR total** | **216,378** | **81.6%** |
| RO: PoW grind (mean draw) | 47,917 | 18.1% |
| RO: challenger absorb/sample | 736 | 0.3% |
| **RO total** | **48,653** | **18.4%** |

In-circuit (the deployed leaf wrap's 38,168 permutations, `[RECALLED leaf-vs-recursion §2c]`):
CR = 70.8% (leaf sponges 64.9% + path compressions 5.9%), RO = 29.2% (transcript absorption +
grind re-check). Native verifier (4,040 perms): same shape — dominated by per-query leaf-sponge
re-execution, i.e. CR-checking.

**So the brief's "the CR job runs O(trace), the RO job runs O(rounds)" is measured true with
one amendment: at deployed pow=16 the RO job is not small natively — the grind alone is ~18%
of prover hashing (~25% of a deployed prove's wall clock), and it is pure RO.** That
observation becomes §2.6a.

### 1d. ⚑⚑ THE THEORY VERDICT — what the tree hash actually has to be

Four sources, each read at the load-bearing passage this lane:

1. **Interactively, CR suffices.** Kilian's argument needs only a CRHF; binding on opened
   positions is a collision argument. This is the true half of the organizing idea.
2. **The deployed object is not interactive.** Its only known soundness track is BCS-in-ROM on
   an RbR-sound IOP. 2023/1071 (the FS-security-of-FRI paper) states the transformation
   verbatim: the prover *"sends the Merkle tree root of the vector (m(s)), **using ρ as the
   'hash function'**"* — the tree hash IS the random oracle — and Theorem 3.15's error
   `Q·ε_rbr + 3(Q²+1)/2^κ` carries the tree's collision/extraction term. The extractor is
   **straightline**: it reads the committed word out of the adversary's oracle *queries*. A
   function you compute yourself (any standard-model CR function, and a fortiori any linear
   map) generates no queries to read.
3. **This is not proof-pedantry — the premise is load-bearing.** 2019/997 (Bartusek–Bronfman–
   Holmgren–Ma–Rothblum): a (contrived) CRHF for which FS-Kilian is unsound *"for a very large
   class of PCPs and **for any Fiat–Shamir hash function**"* — i.e. even a perfect RO
   challenger cannot rescue a tree hash that is only CR. Their conclusion: soundness *"must
   rely on some special structure of both the CRHF and PCP."*
4. **The modern proof is already modular — and the modularity is the usable part.**
   Chiesa–Orrù 2025/536 (paperbin) splits BCS = DSFS[iBCS[IOP]]: the **FS half** runs on an
   ideal *permutation* via the duplex sponge (exactly our `DuplexChallenger` shape — this is
   the paper that finally prices our RO role in its deployed form), while the **tree half**
   keeps its own random oracle, its multi-extraction error κ_MT surviving as a separate term.
   Two functions, two ideal models, separable errors. **And the tree's model is still an
   oracle — its requirement is CR + straightline-extractability, which no known standard-model
   family supplies and which every algebraically-structured function provably does not.**
5. **Production agrees.** Vortex (2022/1633, the Linea prover; list-PC version 2024/185),
   the only deployed system with a SIS hash in the commitment path, keeps the SIS hash at the
   layer whose preimages are *opened* (columns) and puts a SNARK-friendly RO-modeled hash in
   the Merkle tree above the digests: *"the hash function used in the construction of the
   Merkle tree needs to be modeled as a random oracle for the scheme to retain
   extractability"* (2024/185, §5 commitment discussion).

> ### VERDICT on the organizing idea: the *jobs* split (measured, 71–92% CR); the *requirements*
> do not split the way the idea hoped. The tree slot needs "unstructured enough to model as an
> oracle" in every known proof, and the counterexample shows that need is real. **What survives
> is narrower and still valuable: (i) the tree hash owes no duplex/sampling service, so its call
> GEOMETRY is free — §2.3 harvests that; (ii) a merely-CR function IS admissible exactly where
> its preimage is fully opened to the verifier** — the Vortex slot; in our stack that is the
> leaf boundary and only the leaf boundary — §2.1/§2.5 price that; **(iii) the RO job's real
> native cost (the grind) can move to a cheaper oracle under domain separation — §2.6a.**

⚠ One tempting harvest this KILLS: "fewer Poseidon2 rounds for the tree, since it only needs
CR." The tree does not only need CR (points 2–4), so the round margin cannot be shaved against
the weaker property. Not chartable; named so nobody re-derives it hopefully.

⚠ Honesty about the incumbent: Poseidon2 is not a random oracle either — the deployed system
instantiates every one of these theorems heuristically. The distinction that decides §2.1: for
an unstructured permutation the theorem's premise is *unverified*; for a linear map it is
*refuted* (one query distinguishes A·x from an oracle by additivity). Those are different
epistemic states, and only the first ships.

---

## 2. THE DIRECTIONS, SIX COLUMNS EACH

Columns per the brief: (1) security requirement at its slot; (2) native cost; (3) in-circuit
cost; (4) proof size; (5) what breaks in our stack; (6) can we COMPUTE its security or only
assert it.

### 2.1 SIS/Ajtai compression for Merkle nodes — ☠ DEAD in the tree, alive only at the leaf boundary

The brief's hope: `A·x` is linear, hence nearly free in-circuit, CR under SIS. Three
independent walls, any one fatal for the *node* slot:

1. **The proof-track wall (§1d).** A node function is exactly the slot whose preimages are
   *not* all opened (q paths of 2^m nodes), so extraction-from-queries is load-bearing there,
   and a public linear map generates no queries. Swapping Poseidon2→Ajtai in the node slot
   moves the system from "ROM theorem, heuristically instantiated" to "ROM theorem, premise
   refuted." Vortex — the system that most wanted this to work — did not put SIS in its tree.
2. **The digest-geometry wall `[READ Vortex Fig. 22]`.** At 128-bit target the smallest
   Ring-SIS instance in the only production-calibrated table is n=32, q≈2^64 → a **2,048-bit
   digest** (their CPW column already grazes 144 bits there; the safer A2/A3 rows are 4,096
   and 8,192 bits). Our digest is 8 BabyBear felts = **248 bits**. Every sibling in every
   opened path carries the digest: **paths ×8.3–33 in bytes**, and the wrap re-absorbs and
   re-decomposes them. ⚑ The in-circuit "linearity is free" claim inverts here: the node map
   is linear only in its **gadget-decomposed input**, and the decomposition-plus-range-check
   of the children's digests IS the in-circuit cost — the nonlinearity is smuggled back in as
   limb checks on 2–8× more bits than we currently hash. This is ember's flagged obstruction,
   confirmed with production numbers rather than adjectives.
3. **The already-measured wall `[RECALLED ring-hash-dual-mode §4c]`.** The sibling lane priced
   the lattice opening against the Horner chains it would replace in the BabyBear wrap:
   **×0.7–×13, best case parity** — and the galois-levers geometry already banked ×2.011 of
   the ×2.13 prize without any PCS. The R_q-native artifact (where the ring-hash lives) is the
   one place the linear mode is coherent, and that verdict stands unchanged here.

| column | answer |
|---|---|
| requirement | node slot: CR **+ ROM-extractability** — the second half is the one SIS cannot supply |
| native | good: O(mn log n) NTT-shaped, SIMD-friendly (SWIFFT lineage) |
| in-circuit | bad at the node slot: limb decomposition + range checks on 2,048-bit digests; linear map itself free |
| proof size | paths ×8.3–33 |
| breaks | BCS/RbR track for every tree above the swapped level; digest type through the whole recursion tower |
| computable? | **half**: CR reduces to MSIS (with sis-lattice-verdict's caveat — estimator-era games, ~98-bit re-derivations in the wild); the extraction half is not even statable |

**Survivor**: the Vortex-shaped *leaf-boundary* use (hash a fully-opened row/column with SIS,
RO-tree above the digests) — which is not a Merkle-node question at all; it merges into §2.5.

### 2.2 Algebraic fingerprints — the chicken-and-egg is the verdict, and it is already fully harvested

`∏(x_i+γ)` (or `Σ α^i x_i`) is binding only against adversaries who fix data **before** γ. A
commitment must exist before the challenge that would compress it — so a fingerprint can never
BE the commitment. Where a challenge already exists, the stack already fingerprints
aggressively: the reduced opening is `Σ α^k v_k` (88.5% of wrap arithmetic is exactly this
Horner), LogUp is the multiset instance, batch-FRI's α-fold is the codeword instance. **There
is no unharvested site**: every value that meets a fingerprint in our stack does so
post-challenge; every pre-challenge value meets the sponge.

The brief's residual — "a two-phase or deferred-opening structure where a fingerprint
legitimately replaces a hash" — is exactly the door `sumcheck-batched-opening.md` §0a closed
(*"a Merkle leaf supports no evaluation opening"*) and `ring-hash-dual-mode` re-opened only
for an evaluation-binding (homomorphic) commitment: a PCS replacement, priced dead for the
BabyBear wrap (§2.1 wall 3), alive in the R_q-native world. Nothing new is statable here;
re-deriving it from the commit side lands on the same two doors.

**The legitimate cousin is not a fingerprint but VIRTUALIZATION**: don't replace the CR job's
*hash*, delete the *commitment of its execution*. Two rungs, both on the books: (i) in-AIR —
`poseidon2-virtualization.md` measured 352→157 committed felts/perm, Pareto-dominant, not yet
landed; (ii) GKR — prove the wrap's permutation table by sumcheck with only input/output
committed (`gkr-substrate-findings.md`: closer than thought, with the p3 tautology-pitfall and
the missing query leg named there). Referenced, not duplicated: that is a sibling lane's prize.

| column | answer |
|---|---|
| requirement | binding given challenge-after-commit — **unsatisfiable at the commit slot by definition** |
| computable? | yes — Schwartz–Zippel root-counting, the one primitive class we can fully prove (our LogUp Lean already does) — which is precisely why every post-challenge site already uses it |

### 2.3 Tree arity / wider compression — ⚑ THE EXACT COMPUTATION (this lane's contribution)

Instrument: `fastest-oracle-scripts/merkle_geometry.py` — a from-source model of the vendored
`merkle_tree.rs` build (first-digest layer + compress-and-inject), fed the deployed transfer
batch's nine committed matrices, read off the §C spans this lane re-ran
(`fo/raw-spans.log`): main 236×64 / 2×16 / 386×8, perm 72×64 / 4×16 / 12×8, quotient
8×64 / 8×16 / 32×8, LDE height = h·2^b.

> ### VALIDATION: the model reproduces the measured Merkle-commit permutation count **EXACTLY
> at all five blowups** — 26,493 / 52,989 / 105,981 / **211,965** / 423,933 for b=3..7 —
> against `ir2_phase_profile` §D. Zero fitted parameters.

**Finding 1 — the deployed split, previously unmeasured:** at b=6, **leaf sponges 195,072
(92.03%), node compressions 16,893 (7.97%)**. The tree is a sponge with a small compression
tax, not a compression structure with leaves.

**Finding 2 — arity is a null knob, now for the TREE as it was for the fold.** Arity-4 nodes
(hypothetical w32 permutation, cost bracketed 1.8–2.3× w16 by S-box scaling): total
**×1.003–×1.026 — a wash to a loss** — because halving an 8% term while ~doubling its unit
price cancels, and path bytes grow ×1.5 (3 siblings × 0.5 depth). Structural constraints agree:
the vendored tree `const`-asserts N a power of two (arity 3 from w24 is inadmissible as-built),
and no `Poseidon2BabyBear<32>` exists at the pin. **The brief asked for this computation early;
the answer is: close the arity door, it was never where the mass was.**

**Finding 3 — the live knob is the LEAF RATE, and it is measured:** a `PaddingFreeSponge
<Perm24, 24, 16, 8>` (rate 16, capacity unchanged at 8 felts = the same 124-bit collision
budget) halves leaf-sponge count to 103,424. Native w24/w16 ratio **measured this lane at
1.429** (836.5 vs 1195.7 ns/perm, interleaved A/B min-of-41, `p2bench`; per-absorbed-felt
**×0.715**):

> ### Native Merkle-commit ×0.777 `[MEASURED model + measured rate]` — ≈9.5 ms of the ~80 ms
> deployed prove, and the same shape applies to every commit in the tower.

The pinned checkout's own `examples/src/types.rs:44` uses exactly this sponge
(`PaddingFreeSponge<Perm24, 24, 16, 8>`); our deployment took the uni-stark test convention
(w16 rate-8) instead. The ×2 rate was left on the table at config time, not designed away.

**In-circuit, the same swap is SEQUENCED, not free** `[DERIVED]`: leaf-sponge perms scale
×0.53 (Σ⌈w/16⌉/Σ⌈w/8⌉ = 52/98 on this batch) but each w24 perm costs more cells —
wide/deployed chip shape 720/352 = 2.045× → **wrap ×1.055 (a 5.5% LOSS)**; narrow arm-B shape
237/157 = 1.510× → **wrap ×0.871**. And at today's exact counts the two-table split rides the
padding staircase down (38,168 → 16,384+16,384 rows: ×0.627 padded cells — staircase-dependent,
valid only at these counts). **Order of operations: land the narrow AIR (already
Pareto-dominant per the virtualization lane), then the rate-16 leaf sponge wins on both sides.**
A w24 chip is a new Lean-authored emission (`Poseidon2RoundGates.lean` family) and a VK
rotation — ordinary work under house doctrine.

**Finding 4 — caps and pruned paths, computed and small:** the vendored MMCS already carries
the cap knob in-type and the deployed config sets it to zero
(`plonky3_prover.rs:218: TestMmcs::new(hash, compress, 0)`); `verify_batch_pruned` also ships
unused. A height-4 cap saves ~19·4·(#trees) path perms against absorbing 2^4 digests — net
~180 of 38,168 wrap perms (0.5%); query-path prefix dedup is bounded by the same 5.9% path
share. **Independently replicated on another config**: `dregg_mina_config.rs:89` measured
`arity 8 + cap_height 8` *together* worth **1.0%** of the Mina-side budget (paths ~2% of a
Pasta-hashed verify) and left them untaken for exactly this reason. Two configs, two
instruments, same answer: path geometry is not where the mass is.

| column | answer (rate-16 leaf sponge) |
|---|---|
| requirement | unchanged — same permutation family, same capacity, same oracle model |
| native | ×0.777 Merkle-commit `[MEASURED]` |
| in-circuit | ×1.055 now / ×0.871 after narrow-AIR / ×0.63 with the staircase `[DERIVED]` |
| proof size | unchanged (digest still 8 felts) |
| breaks | wrap needs a second (w24) Poseidon2 table — Lean-emitted; VK epoch; config re-emit |
| computable? | same status as incumbent (heuristic permutation, 3-year record; w24 has the identical analysis pedigree as w16) |

### 2.4 Bitsliced / SIMD-shaped compression — settled by siblings; the residual tension priced

The sibling record already answers the direction: `R* = 2.04–3.45` deployed (1.74–2.75 at the
proven packing), Blake3 `R = 30.6×`, Keccak 210.6×, the lookup escape **measured shut at
1.96×** (Stwo's deployed LogUp-Blake counted cell-by-cell), Monolith 3× over budget, and the
binary field does not cross (`hash-landscape.md` §1a/§2/ADD.2, `e5-rederived.md` §1). Nothing
here relitigates that.

What this lane adds: **bitslicing attacks the native column only, and the native column is not
where the constraint binds.** `R` is an arithmetization property; no SIMD shape moves it. Two
cheaper native wins already on the books dominate any hash swap natively: the verifier's
scalar-vs-packed 5× (phase-profile §8) and hash-landscape §4's 18 native-verifier-only entry
points (1.5–2.3× each, zero cryptanalytic risk). A "designed for both the vector unit and the
circuit" candidate would have to beat Poseidon2's measured packing width 8.18 natively AND
land under R≈2 in cells; nothing in the swept literature (incl. the post-Weft gate table's
certified layers) is within 2× of both simultaneously.

| column | answer |
|---|---|
| requirement | full oracle-model service (they'd sit in both slots) |
| native / in-circuit / proof / breaks / computable | see the three sibling notes; fails `R*` by 4.6–14.2×; assert-only security |

### 2.5 Do not hash the trace — the honest accounting says it is the blowup knob in a bigger costume

Ligero/Ligerito-family: commit rows' encodings, open whole **columns**, bind by the code.
Accounting against our measured shape:

- **Native commit hashing does drop** — absorb = N/ρ_row felts vs our N·2^b: at rate 1/4
  against blowup 64, ~16× less data hashed. Real.
- **But the verifier grows, and recursion is priced on the verifier** (leaf-vs-recursion's
  own law). Query count at unique-decoding-ish radii is 5–13× ours; each query opens a whole
  column (Σwidths ≈ 3,738 felts for the deployed child → ~468 sponge perms in-circuit per
  query, against 1,423 perms per query for *everything* today), plus the α-combination row
  check per query. Proof size goes √N-ish; Ligerito buys it back by committing the fold —
  i.e., by adding back rounds of commitments.
- **And the tree above the column digests is still an RO-modeled Merkle tree** (§1d point 5),
  so "hashing stops mattering" is false even in the limit: it stops scaling with the TRACE and
  starts scaling with the CODE's query count.

The net motion — trade prover redundancy-hashing against verifier work and wire — is the same
trade the blowup knob already exposes inside FRI, where we have it measured end to end:
**lb=3 is ×4.6 prover for ×1.8 wire, deployed machinery, zero new soundness surface**
(phase-profile §5). A Ligerito adoption buys a worse version of that trade plus a new proof
stack, unless the SIS-column-hash + algebraic-verification composition (Vortex's
self-recursion, where the column hash's *linearity* lets the next layer verify it as algebra
instead of re-execution) comes with it — and that composition is the R_q-native world
`ring-hash-dual-mode` already chartered, not a BabyBear wrap upgrade. The char-2 Lean spine
(`LigeritoInterleaved.lean`, corrected bounds in `ligerito-exploration.md`) keeps this road
open at the formalization layer, where it belongs for now.

| column | answer |
|---|---|
| requirement | proximity + column binding (CR at the opened boundary — the one legitimate merely-CR slot) + RO tree above digests |
| native | commit hashing ~16× down at rate 1/4 |
| in-circuit | per-query cost up (whole columns); query count up 5–13× |
| proof size | √N-shaped before recursion; strictly worse than FRI at iso-security on our sizes |
| breaks | the entire FRI verifier, the wrap circuit, the Lean FRI ledger |
| computable? | proximity yes (AER24/DG24 bounds, errata already found by our lane); the tree above: same heuristic as today |

### 2.6 Left-field additions (this lane's)

**a. ⚑ Swap the GRIND hash — the one slot where a traditional hash wins inside the deployed
stack.** The grind is pure RO-work (18% of prover hashing, ~25% of a deployed prove's wall
clock, mean 12 ms) whose *verification* runs ONCE — natively one hash, in-circuit one
arithmetized compression per wrap. That asymmetry is everything: Blake3 at ~25–50 ns/hash vs
packed Poseidon2 at 189 ns/lane is a 4–7× faster grind — against the mean 12 ms draw that is
~9–10 ms/proof saved (6–7 ms at the observed 8.2 ms draw) — and the wrap pays a one-time
**+9,168 cells = +0.03%** of 29M to check the winning witness.
Soundness: the PoW term is already a separate additive term in the ledger; under 2025/536's
two-oracle modularity a domain-separated grind oracle is exactly the licensed shape. Wire: the
witness type changes; VK epoch; re-emit — ordinary. ⚠ The deeper question phase-profile §9
already raised — whether 16 grind bits are worth a quarter of the prover at all — is a
soundness-budget decision upstream of this and could zero the whole item.

**b. The RO job's in-circuit 29.2% is an unopened box.** 11,128 wrap perms are "transcript
absorption + grind" as one measured lump. Before anyone optimizes the challenger (e.g. a
rate-16 duplex, which §2.3's arithmetic says is ± nothing certain), decompose that lump; it is
one afternoon with the existing sweep harness and it bounds a whole family of ideas.

**c. What was checked and found already-taken or empty**: absorbing a digest of the OOD values
instead of the values (no win — someone must still absorb the preimage); per-tree caps (0.5%);
shared-prefix dedup (<0.9%); reduced-round tree hash (killed by §1d, stated there).

---

## 3. THE FIXED-COST BOUND, APPLIED — which parts a faster oracle actually helps

`[RECALLED e5-rederived §4c]` FRI floors every trace at 2^(lfpl+lb+1) = 128 rows; a 6.1×
padded-cell drop bought 1.2× in time; a small Lean-emitted AIR proves in 13–16 ms warm and
almost all of it is fixed cost.

| layer | floor-bound? | does hash rate move it? |
|---|---|---|
| small leaf proves (ETH light client, one Transfer) | **yes** | **no** — fixed cost dominates; §2.3/§2.6a save ms only where Merkle-commit is a real share |
| the deployed IR-v2 batch prove | partially | yes — Merkle-commit's per-phase-min is 42.5 ms against a 69–80 ms deployed prove (51–62% depending on composition; the brief's 51% is the conservative end); §2.3 takes ~9.5 ms, §2.6a ~9–10 ms at the mean grind draw |
| **the wrap/tower proves** | **no** (2^16+-row traces, hash-bound at every feasible blowup) | **yes — this is where every hashing win compounds**, natively AND as cells |
| the wrap's committed cells (f_circ = 52.36% deployed) | n/a | yes — §2.3 in-circuit column, the narrow AIR, GKR virtualization |
| native-verify-only surfaces (18 entry points) | no | yes — already chartered at zero risk (hash-landscape §4) |

**The lane's bound, said plainly: a faster oracle is a recursion-layer and batch-layer
instrument. It buys nothing for the small-leaf latency that is currently our binding
constraint on real workloads — amortization does (e5-rederived §5b). The two lanes are
complementary, not competing.**

---

## 4. RANKED RECOMMENDATION

1. **Land the narrow Poseidon2 AIR (arm B)** — already Pareto-dominant, already recommended by
   the virtualization lane; it is also the *gate* for #2's in-circuit half.
2. **Rate-16 leaf sponge (w24) after it** — ×0.777 native Merkle-commit measured, ×0.871 wrap
   after #1, same security object, VK epoch + Lean-emitted w24 chip. The single biggest
   hash-geometry win that exists; the pinned checkout's own examples already use the shape.
3. **Decide the grind's fate** (§2.6a): first the budget question (is pow=16 worth 25% of
   prove), then — if kept — the Blake3 grind swap: ~8–14% of deployed prove for +0.03% wrap
   cells.
4. **Decompose the wrap's 29.2% RO lump** (§2.6b) before touching the challenger.
5. **Close the arity door and the SIS-node door permanently** (this note is the artifact:
   arity ×1.00–1.03 exact; SIS nodes dead three ways with production-calibrated numbers).
6. **Keep the R_q-native and char-2 roads where the siblings put them** — formalization-first,
   no BabyBear transplant; nothing found here reopens either verdict, and the Vortex reading
   strengthens both (their SIS hash lives exactly where ring-hash-dual-mode's linear mode
   says it should: at an opened boundary, under an RO tree).

**What would change this ranking**: a standard-model positive result for FS-Kilian with
CR-only trees over FRI-shaped IOPs (watch the CJJ/SSB + correlation-intractability line — the
known escape, at theory prices nobody can currently pay in-circuit); or a measured w24 packed
rate contradicting the scalar ratio 1.429 (named inadequacy below).

---

## 5. Named inadequacies

- The w24/w16 native ratio is **scalar**-measured; the prover runs **packed** (×4 NEON). Both
  widths pack identically so the ratio should transfer, but it is not measured packed. One
  bench-day to close; it gates #2's exact native figure, not its sign (break-even is r=1.886
  against measured 1.429).
- The wrap in-circuit multipliers for §2.3 use the IR2 batch's count ratio (52/98 = 0.53) as a
  proxy for the wrap child's Σ⌈w/16⌉/Σ⌈w/8⌉; per-matrix child widths would pin it to the unit.
  ±few %.
- FRI-fold Merkle trees (4,413 perms, 2% of hashing) are carried at their measured total, not
  re-modeled; the leaf-rate lever applies to them in the same shape.
- The grind swap's native figure uses literature-range Blake3 short-input latency (25–50 ns),
  not a bench on this box.
- 2019/997's counterexample CRHF is contrived; the citation is used only to show the premise
  is load-bearing, never that Poseidon2-as-tree is attackable.
- Absence claims about "no standard-model route" are scoped to the sources read here plus the
  sibling sweeps; the eprint mirror is cryptology-only (PREFLIGHT corpus-blindness caveat
  applies).

## Provenance

Measured this lane: `fastest-oracle-scripts/merkle_geometry.py` (validates EXACT at five
blowups against `ir2_phase_profile` §D; run 2026-08-18), scratchpad `p2bench` (w16/w24
interleaved A/B, min-of-41, contended laptop — ratio is the deliverable), §C raw-spans re-run
(`fo/raw-spans.log`, EXIT=0, matrix census). Read at source: `plonky3_prover.rs:53-81`,
`plonky3_recursion_impl.rs` backend const, vendored `p3-fri` `verifier.rs`/`two_adic_pcs.rs`
transcript sites, pinned `uni-stark/src/verifier.rs:361-391`, pinned
`merkle-tree/src/merkle_tree.rs` (N-ary + caps + injection algorithm),
`examples/src/types.rs:44`; eprint 2023/1071 (§3.4, Thm 3.15), 2019/997 (abstract + result
statements), 2022/1633 (§7.1-7.2, App. B, Fig. 22), 2024/185 (list-PC defs, Thm 3 proof,
§5 RO-for-extractability passage), paperbin 2025/536 (§2.6, Corollary 1). Recalled siblings,
not re-measured: phase-profile.md, leaf-vs-recursion.md, hash-landscape.md (+ADD.2),
e5-rederived.md, ring-hash-dual-mode.md, sis-lattice-verdict.md, poseidon2-virtualization.md,
gkr-substrate-findings.md, ligerito-exploration.md, post-weft-hash.md. Live sibling lanes
(Weft-C, CLAASP/Feistel, AIR interpreter) referenced nowhere as dependencies — no overlap
found.
