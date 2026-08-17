# Dead ends — each with the number that closed it

**These are months not spent.** They are worth as much as the positive results
and they are the easiest thing for a newcomer to accidentally re-do.

## How to read a closure here

Every entry carries a **provenance tag**, because how a direction was closed
determines how hard it is to re-open:

- **[MEASURED]** — we ran it. Hardest to re-open.
- **[DERIVED]** — we computed it from read code or a read paper. Re-openable if
  a premise moves.
- **[THEIR PAPER]** — closed by someone else's number. ⚠ **Re-opens when their
  number moves**, and one of them is actively moving (see §L3).
- **[ABSENCE]** — closed by not finding something. ⚑ **Weakest, and this
  corpus has burned us twice.** House rule, verbatim:
  > *"Absence from a published corpus is evidence about the corpus, never about
  > reality, and a paper described as unpublished is not evidence at all."*

⚠ **Where `docs/VERDICTS.md` and a note disagree, both are shown.** VERDICTS
says it wins, and in at least three cases below **a later note is right and
VERDICTS is stale** — the rule is backwards for anything after 2026-08-13.

## ⚠ TWO STRATA

Everything unmarked is the **2026-08-16** archaeology pass. Everything tagged
**`[08-17]`** was folded in afterwards, from the ~42 research commits that
landed after that pass. Where a stratum-2 finding **contradicts** a stratum-1
entry, the old entry is kept and the contradiction is stated **at it** — most
sharply at **§L3** (now closed) and **§L6** (now resolved *against our own
earlier scrutiny*).

⚑ **Six closures were added in the second stratum, and they are among the most
useful entries in this file** because each kills something a newcomer would
otherwise re-propose within a week:

| § | what died | what killed it |
|---|---|---|
| **E6** | **ECFFT** | its OWN theorems — a trace-height cap and an error term > 1 — **not constants** |
| **D5** | **the 3.2× lookup arithmetization lever** | measured **1.96×**; the 3.2× was a fat-denominator artifact |
| **D6** | **the job-split** (PRF-able transcript work) | refuted **three independent ways** |
| **D7** | **Weft-1** | branch **6** + a 4-deep subspace flag (⚠ **killed as specified — Weft-2 is a live re-opening**) |
| **E9** | **the ×2.13 sumcheck-batched opening** *over two-adic FRI* | it is a **PCS replacement**, not a backend rewrite |
| **E10** | **deferred accumulation over Merkle-only commitments** | the MLE obligation **cannot travel even one layer** |

---

# A. FHE

## A1. Transciphering — **DEAD**

**The idea**: have the client upload short symmetric ciphertext and let the
server homomorphically decrypt, killing the 10.9–27× BFV expansion.

**The number**: **Pasta-3's homomorphic decryption consumes 269 bits of noise
budget. Our entire ciphertext modulus is 109 bits.** Measured in Pasta's own
Table 9 (SEAL, p = 65537 — *a 17-bit prime, smaller than ours* — N = 16384):
budget 364 bit → 95 bit after decryption.

> It does not overflow our *budget*. It overflows our *modulus*, by 2.5×, at a
> smaller prime than ours, before a single useful operation.

Supporting: break-even needs a **170 kbit/s uplink**, 8.2 GB of key transfer,
85,344 ciphertexts to pay back, and a permanent 4× cost stranding at N ≥ 16384
— the server never gets back to N=4096. Pasta's own benchmark table never uses
N < 16384 for any F_p cipher at any prime.

⚑ **AND THE OBSTRUCTION FIRST NAMED WAS THE WRONG ONE.** The record said
`gcd(t−1,3) = 3` blocks cube-map ciphers at deployed t. Computed:
`t = 1032193`, `t − 1 = 2^14 · 3^2 · 7`, so `x^3` is not a permutation — **but
`x^5` is** (gcd(t−1,5)=1), and the gcd condition applies **only to power-map
S-boxes.** Pasta's own primary S-box is a Feistel, which permutes the vector
regardless. **No plaintext-modulus migration was ever needed and none should
be done.**

The depth law, recorded because it is reusable:
> **Pasta-r: pt-ct depth = 2r, ct-ct depth = (r−1) + ⌈log₂ d⌉.**
Reproduces Pasta's Table 7 exactly; independently confirmed against Rubato's
Table 1. **The absolute floor of the exact F_p transcipher family is ct-ct 3 +
pt-ct 6 ≈ 9 level-equivalents against our ~3.**

**[THEIR PAPER]** for 269 bits · **[DERIVED]** for the gcd refutation.
`docs/VERDICTS.md:216-218` · `notes/fhe-scout-verdicts.md:76-90` ·
`notes/archive/convergence-2026-08-13.md:53-59`.

## A2. Bootstrapping — **DEAD in all four cells**

**The number**: the crossover between *leveled BFV with a bigger modulus* and
*bootstrapped BFV* sits at **circuit depth 13–17. Ours is 2** (measured, 40/40).

**Second, independent kill**: **bootstrapping's own noise consumption is
147–224 bits — more than our whole 109-bit modulus.**

**The move it recommends instead**, stated plainly:
> *"BFV bootstrapping: not needed and not usable at log q = 109; **bigger
> modulus is the move.**"*

⚑ **Carry this partial retraction**: the residue *"if GBFV bootstrapping is
ever wanted, t must change and no 20-bit option exists"* was **deleted** —
that holds only for GBFV cyclotomic primes, and **t = 2^20 is p^r (p=2, r=20),
which HElib bootstraps natively** (`notes/grey-lit-corrections.md:106-108`).

⚠ **Coverage caveat, stated by the scout lane itself**: *"Transciphering depth
and the bootstrapping/NTRU/amortized frontier have candidate sets on disk but
**NO depth verdicts** — absence below is not a negative finding."* The "all four
cells" sentence rests on the depth crossover, the 147–224 bits, and the NTRU
fatigue point, and **nothing else exists in the corpus.**

⚑ **In particular there is NO standalone argument that amortized/batched
bootstrapping does not apply.** Treat it as covered by the depth crossover only.
The one thing recorded specifically: the one amortized method that uses BFV
internally **says in its own footnote that it becomes impractical at exactly
our 20-bit precision.**

**[THEIR PAPER]** for 13–17 and 147–224 · **[MEASURED]** for depth 2.
`docs/VERDICTS.md:217-218` · `notes/archive/convergence-2026-08-13.md:60-66`.

## A3. NTRU-based FHE — **every published parameter set is past the fatigue point**

**The number, as recorded in-repo**: *"every NTRU parameter set in print is past
the concrete fatigue point (**2^1 to 2^73 over**), and NTRU's `Ω(λ log²q)`
dimension growth makes precision its structurally worst axis."*

⚠ **Two figures that circulate and are NOT in the repo** — grep returns zero
tree-wide, so they must be sourced from a transcript before use:
`q_fat = 0.004·N^2.484` (the Ducas–van Woerden concrete average-case fatigue
point), and the count **"11 parameter sets across 6 papers."** The transcript
version adds the mechanism: **5 of 6 papers apply the wrong test** —
`log_N(Q) < 2.484` (i.e. `Q < N^2.484`), **silently dropping the 0.004.**

⚑ **A live unacknowledged gap recorded in passing**: eprint **2026/68**'s sparse
`h = 56` drops the threshold 12×, putting it 2^6.6 over; its full text greps
zero for `DSD` / `dense sublattice` / `NTRUFatigue`, and its λ = 128.2 comes
from the *LWE* estimator. **One script settles it.** Nobody ran it.

**[THEIR PAPER]** applied to **[THEIR PAPER]**. No measurement of ours.

## A4. Scheme switching (BFV ↔ TFHE) — **CLOSED, and it got worse**

**Stage 1 — the number**: plaintext-space mismatch. **t ≈ 20 bits against PBS's
~11-bit input space.** Verdict: *"sound, not worth building."* **[DERIVED]**

**Stage 2 — the upgrade**: eprint **2026/285** ships a **working IND-CPA-D
proof of concept** against OpenFHE's CKKS→FHEW switch. Verdict moves from *"not
worth building"* to **"hazardous."** **[THEIR PAPER]**

⚠ **Scope**: the PoC is against **CKKS→FHEW, not our BFV↔TFHE shape.** The
verdict transfers by analogy, and the note is explicit about it ("sufficient
conditions supplied if ever needed").

## A5. Encrypted attention at depth ≤ 3 — **REFUTED**

**The number**: `t = 2^20` binds any BFV polynomial nonlinearity to **degree
≤ 2 regardless of levels** — 8-bit fixed point needs `2^{8d} < t`, and **BFV
cannot rescale.** Minimum published encrypted attention: **depth 10, one
layer.** Minimax sign minimum: **depth 11.**

**Consequence, and it is the architecture**: nonlinearities go through the
MPC / TFHE-PBS boundary. That is *the only route at our parameters*, not a
preference.

## A6. Three smaller FHE closures

- **The KPZ encoding fix — CLOSED AS A NO-OP.** *"Do not run this
  experiment."* fhe.rs already encrypts with KPZ's exact-division encoding, so
  `r_t(Q)` is structurally absent from our noise path. ⚑ **The error class is
  worth more than the fact**: *"the predicted payoff conflated BITS with
  LEVELS. The `r_t(Q)` term is worth ~8 bits and **1/40 of a level**; a level
  costs 33–42 bits. **In a budget with a cliff, a small absolute saving buys
  nothing unless it crosses the cliff.**"* **[MEASURED, 40 draws]**
- **The slot / BSGS diagonal route does not close** under the *proven*
  worst-case noise bound — **fails by 2.9 bits at D=64**, under any
  key-switching variant, and lives entirely on the heuristic 2√n expansion.
  Coefficient encoding closes with **~49 bits of headroom and zero rotations.**
  **[DERIVED]**
- **Direct coefficient lift without split-sign gives ZERO advantage** over
  SIMD, because negative weights lift to ~t. Split-sign (`W = W⁺ − W⁻`) is
  what makes the coefficient matmul work.

## A7. ⚑ PIR for the embedding table — **NOT a dead end. It is LIVE.**

Listed here only so nobody files it as one. **PIR rotation keys cost 2.01 MB at
our parameters** (12 keys × 0.33 MB at N=4096); **the literature's 857 MB
horror is N=2^16.** *"The field's rotation-phobia does not transfer to us."*
It is under "Evaluate now" and appears nowhere in `docs/VERDICTS.md`.

---

# B. The joint FHE + proof modulus

## B1. The 109-bit joint prime — **H2 CLOSED, false at 109, true at 61**

**The idea**: collapse the 3-limb RNS tower into one ~109-bit prime shared by
FHE and the prover, deleting RNS-emulation-in-circuit.

**The mechanism, one sentence**:
> **A joint field is affordable while it fits a machine word and unaffordable
> the moment it needs two limbs. 61 fits. 109 does not. The deciding variable
> is the machine word, not the number of primes.**

**The numbers**: 16× fewer committed elements × 18.5× dearer per multiply ≈
break-even. Against a NEON-packed BabyBear prover, single-prime at 109 bits is
**1.11–1.53× SLOWER**; at 61 bits it is **1.8× FASTER**.

⚑ **And the hardening pass made it worse**: *"'16× fewer committed elements'
does not reproduce. Derived independently it is **4.80× padded** — which makes
the 109-bit joint prime **3.85× worse, not break-even.**"*

**What the 61-bit arm costs**: 48 bits of noise budget = **exactly one depth
level** (+3.03 bits of margin at depth 1, **−29.94 at depth 2**).

⚑ **A negative result about the *question*, not the answer**: proving one FHE
op costs **≥618× (packed) / 1639× (scalar) performing it**, so at proving
fraction f = 1 the entire FHE-side penalty moves the total by **0.19%.
H2 is decided entirely by the proof side.** And *"H2 collapsed into H1 — they
are not independent gates."*

**[MEASURED]** — M2 Max, min-of-40, both NTTs validated against schoolbook
negacyclic convolution. Artifact: `phase0/h2-rns-vs-single-prime/`.
⚠ Its own caveat: *"proof-side numbers are derived, not measured."*

## B2. KoalaBear as a BFV RNS limb — **not landed, not dead: "real, small, not architectural"**

**The recovered claim**: KoalaBear is a legal negacyclic-NTT limb at N=4096, so
one limb of every ciphertext would be *natively proof-field data.*

⚑ **"77 towers" does not reproduce.** The honest search space gives **479**,
and **33 different unstated companion-exponent windows hit exactly 77.**
*"Do not quote 77 without the window."* The substance survived; the number was
an artifact of an unstated parameter.

**The verdict number**: best case **1.24× elements, 1.29× lookups, 1.46× muls,
FHE side 1.00×.** *"Not ⅓, because **70% of a native row is fixed schedule/bus
overhead**."* It buys 19–46% of one cost and **0% of the complexity** — the
emulation gadget survives for the other two limbs — and the dominant saving
needs a trace re-plan, since 688,128 rows pad to the same 2^20 as 1,032,192.
**Recommendation: leave H2 closed; do not headline the limb route.**

⚠ **Do NOT report it as dead.** *"'A KoalaBear limb under a BabyBear prover is
the two-31-bit-primes config the seam rule forbids' is true today and
**dissolves under the recommended migration** … **conditional on the migration,
not dead.**"*

⚑ **And the lane landed something better than its headline** — promote this,
do not bury it: the depth-2 cliff `log₂Q − 1 − log₂t` **reproduces the measured
88.02 exactly**, and the **+33.0-bit ct×ct increment equals `log₂(2Nt)` to 0.02
bits** ⇒ **the deployed noise expansion is the PROVEN δ_R = N, not the
heuristic 2√N.**

**[DERIVED]** — `paper/scripts/koalabear_limb.py`, 41/41 checks, `e1539a9`.

## B3. The barrel-shift twiddle trick — **CLOSED, and the original claim was false twice**

**The idea**: get Goldilocks-style multiplier-free NTT (shift-only twiddles) at
a joint prime. Zama's HPU NTT has *no multipliers at all* because
`ord(2) = 192` in Goldilocks makes ω a small power of two.

**Closure 1 — it does not transfer to our band.** Shift twiddles need *small*
`ord_p(2)`; **at ~109 bits every candidate's `ord_p(2)` is astronomical —
shift exponents in the 10^25 range.** The equivalent shift for BabyBear would
be **983,040 bits.**

**Closure 2 — p61 does not inherit it.** `ord_p61(2) ≈ 2^57`. *"Don't let Rock-1
prose imply it inherits the Goldilocks shift property."*

**Closure 3 — our own uniqueness claim was false, twice over.** *"'The unique
barrel-shift prime in 65–160 bits' was **false twice over**: Goldilocks is a
**64-bit** prime, outside the claimed window, and **37 primes of the form
Φ_m(2^b) exist in 65–160 bits.**"* The true statement: **among primes Φ_m(2^b)
in 64–160 bits with 2-adicity ≥ 9, Goldilocks is unique** — and it is of that
form **six ways over** (Φ₆(2³²) = Φ₁₂(2¹⁶) = Φ₂₄(2⁸) = Φ₄₈(2⁴) = Φ₉₆(2²) =
Φ₁₉₂(2)). Scoped honestly: the form is **sufficient, not necessary**, so the
capability-level statement is **a bounded scan, not a theorem.**

⚑ **And it was known since 1982** — Duhamel & Hollmann, *"Number-theoretic
transforms with 2 as a root of unity"*, Electronics Letters 18(22), 28 Oct 1982.

**Adjacent, and a clean one-liner**: **Crandall / pseudo-Mersenne primes
`2^a − c` are structurally excluded** — `v₂(p−1) = v₂(c+1) ≤ log₂(c+1)`, and
over all 1,767 primes with c < 4096 the **maximum 2-adicity attained is 12**,
below even the FHE minimum.

⚠ **Artifact blocked**: the scan scripts carry a `factorint` limit bug and a
hand-picked-`ms` bug (gates G13/G14). See `05-ERROR-CLASSES.md`.

**[DERIVED, script]**.

---

# C. Lookups, RAM, and one-hot

## C1. Celer — **NO-GO on five grounds**

Verbatim from the lane, *in increasing order of decisiveness*:

1. **The gap is 2.3–2.6×, not 4.3×** — and the spike's own stated bar was
   *"≥2× or nothing else recovers it."* It clears by a hair, against a
   self-implemented, post-review-added baseline. Measured **2.35× at m=2^28**.
2. **A third of that is already spoken for** by the extra soundness degree.
3. ⚑ **At our table size the advantage is at its weakest** — Fig. 3a/4a:
   **Celer degrades 2.7× with table size; logUp-GKR degrades 9%.** The
   crossover is in **their own Figure 4a and never in the text**: at n=2^16,
   **logUp-GKR WINS below m ≈ 2^21** (0.6× at 2^20).
4. **logUp-GKR's 43 was overpriced by 2× by its own author's cost model** — the
   "win" is substantially an accounting artifact a tuned baseline erases free.
5. ⚑ **The spike names a baseline we do not have.** `grep -rl -i gkr` returns
   **zero** across Plonky3-at-the-pin, breadstuffs and minidregg. The deployed
   lookup is `p3-lookup`'s AIR-column LogUp. *"Building the baseline is most of
   building the contender."*

**And a sixth, structural, found later**: **Celer is group-based (Dory). Its
sublinearity is in *group operations*. It does not transfer to a hash setting
at all.**

⚑ **The constants' provenance, which is the reusable finding**: *"the Celer
'43m vs 10m' row: **both numbers are from one paper's Table 1**, the **43 is
Papini–Haböck's Eq. 5/6, not Celer §4.4**, and it is a re-quote of a
2×-overcounting model."*

⚠ **A live sunset condition on the whole comparison**: *"All field-op constants
are moving — 2026/587 claims >10× sumcheck-prover inside Jolt. Haböck's 43,
Celer's 10, everything in the comparison tables is denominated in a unit this
paper moves. **Do not lock LogUp-vs-Celer until it is read.** (A cost verdict
outlives its premise.)"*

⚠ Provenance note: **the eprint number 2026/1453 appears nowhere in the repo.**
Celer is discussed only by name and content.

## C2. One-hot addressing (Twist / Shout) — **structurally unavailable on our stack**

> **One-hot addressing requires a commitment scheme in which sparse/boolean
> data is structurally cheap. Three members exist: MSM zeros (curves),
> binary-tower bits (Binius/Blaze), and lattice/SIS sparsity. BabyBear +
> Poseidon2 + FRI has NONE of the three — on the authors' own authority.**

## C3. Four more lookup closures

- **Monolith-31 — CLOSED.** *"No 31-bit-prime Monolith exists anywhere:
  **Plonky3's Monolith AIR rejects KoalaBear BY NAME in a source comment, and
  BabyBear breaks the Bars bijection.**"* Measured at matched degree:
  **Poseidon2-KB 164 cols/perm vs Monolith-31 3,520 — 21.5×**, ~900 even
  granting LogUp (5.5×). *"No crossover; the deficit is marginal, not fixed.
  Our LogUp machinery does not change this."* **[ABSENCE + MEASURED]**
- **Nebula's 480× buys nothing for us** — it is against curve-multiset-Spice
  *inside IVC*; in a monolithic STARK with post-commitment challenges the trick
  buys nothing. **The folding substrate does not port.**
- **BKV24's "optimal" Merkle-tree shape is not harvestable** — the bound counts
  **bandwidth, not hash permutations**, and the optimal shape hashes **~2×
  MORE.** *"Do not upgrade a binary Merkle tree expecting a SNARK win."*
- **New lookup arguments beating LogUp-GKR / Shout, May–Aug 2026: none.**
  Verified. **[ABSENCE]**

---

# D. Hashes

## D1. Poseidon3 — **does not exist**

*"Both mirror mentions are **citation collisions** (a circomlib width-3
instance; a StarkWare parameter file). **The family branches by FIELD, not
version**: Poseidon2b (binary, for Binius), Skyscraper-v2 (big primes).
**Wrong mental model to expect a version number.**"* **[ABSENCE]**

⚑ **And the adjacent answer is stronger than the one asked for**:
> **A sideways move inside the AO family is unsupported by any reading of the
> record.** Monolith, Skyscraper, Tip5 and the Marvellous line all have
> strictly less analysis, and **three of four have a documented margin erosion
> in the last year.** The only two destinations the security record supports
> are **Poseidon1-on-MDS** — what the Initiative itself did — **or out of the
> AO family entirely.**

The AO graveyard, from `notes/hash-landscape.md:610-624`: Griffin 🔴 broken at
2^64 · Anemoi+Jive 🔴 2^70 against a 128-bit claim · Arion 🔴 2^53–2^57 ·
Rescue 🔴 2^112 at α=3 · **Skyscraper v1 🔴 2^8.19 on the FULL 10 rounds** ·
Jarvis / GMiMC / Grendel / Starkad / Ciminion / Hydra 🔴 dead.

## D2. Poseidon2 round-skipping (2026/306) — **no action**

Our margin is **+286 bits** and the attack cannot reach our bar even if every
skippable round were free. Reaching it needs `8·r_F + r_P > 59.0`, and **the
maximum available in the paper's own model is 45.** **α=7 is why**; α=3
(KoalaBear) roughly halves the margin — still safe, worth re-deriving on
migration.

⚑ **Three of the escalation's premises were wrong at source**: the 2^106 figure
is **Poseidon2b (the binary variant)**; the post-disclosure round increase was
**Poseidon2b too**; and the Plonky3 call-out is **(64,16) = Goldilocks**, which
we do not instantiate. *A panic priced against a variant we do not run.*

## D3. Delegating the hash instead of building a ring-native one — **DEAD**

**The mechanism**:
> **Delegation pays only when the hash is expensive IN-CIRCUIT.
> Poseidon-over-R_q in 2026/1127 is 856 constraints per permutation.** The
> 6–14× Keccacheck harvests comes from Keccak-f being 20k–50k R1CS *because it
> is bitwise*. **1127's bill is VOLUME (transcript size); delegation attacks
> UNIT COST. There is nothing to harvest.**

**Second, independent**: the delegated argument's **own Fiat–Shamir lands back
in-circuit and is sequential** — one in-circuit hash per sumcheck round,
unbatchable. Applied to a 30-round Poseidon at 856 R_q constraints/perm:
**820k → 1.23M → 2.87M.** *Delegation loses to both our candidates by 3–31×.*

**The constraint table that decides it** (`notes/ring-hash-design.md:772-782`):

| option | Fiat–Shamir cost, R_q constraints |
|---|---:|
| status quo (Poseidon over Z_q) | **2,417,127** = 2^21.2 |
| σ-Poseidon, τ=1 (5.0×) | 483,425 = 2^18.9 |
| σ-Poseidon, τ=4 (8.0×) | **302,141** = 2^18.2 |
| gadget-Feistel (26×) | **92,257** = 2^16.5 |

Of the 2,417,127, **2,402,503 (99.4%) is hash absorb/squeeze.**

**The number that ends the argument**: FS share of a 2.23e6-useful-work step
goes **52.0% (today) → 11.9% (σ-Poseidon) → 4.0% (gadget-Feistel).**
> **At 4% there is nothing left for an architectural escape to remove.**

**The four named escapes, each with its own closing number:**

| escape | paper | in-circuit cost | verdict |
|---|---|---|---|
| **Symphony** | 2025/1905 | 65,536–131,072 whole batch | **the only TRUE escape** (hash → 0). Clears bar A by 2.3–4.6×, straddles bar B — but needs an **uncosted port** from Z_q-SIMD to R_q-native CCS, and is *not clean for hash/Merkle-based folding* |
| **ProtoGaLattice** | 2026/1317 | ~483k–720k *(derived; the paper states none)* | **1.6–2.4× OVER bar A.** ⚑ *"'100 → 4 RO calls' is a **25× cut of the WRONG QUANTITY**"* — RO calls ≠ sponge permutations (~2,650 perms across ~100 calls); **sumcheck messages are 2.6% of the transcript**, so removing sumcheck cannot touch the other 97.4%. **Their own Open Problem #1 concedes it.** |
| **GKR delegation** | 2026/551 + Keccacheck 2025/1764 | 820k–2.87M | **net loss, 2.7–31× over bar.** 2026/551 has **no benchmarks at all**, and its §4.3 warns against our exact use: FS *"should not be instantiated using Poseidon with the same parameters."* |
| **ACLMT** | 2022/941 | — | **removes nothing.** *"Dead as a proof, not broken."* |

⚑ **A soundness hazard that closes GKR delegation independently of cost.**
Symphony cites attacks [KRS25] *"for GKR-based SNARKs if we allow the proven
statement to compute the Fiat–Shamir hash function itself."* **Delegating our
FS hash to a GKR argument and then Fiat–Shamir-ing that argument is precisely
that configuration.** *"Do not quote Keccacheck's or 2026/551's constraint
counts as an escape without settling this — a cheaper verifier for an unsound
configuration is not a win."*

⚑ **The generalizable lesson, verbatim**:
> *"I predicted 'delegate' because delegation composes with the substrate we
> are building anyway — an ARCHITECTURAL argument. **An architectural fit is
> not a cost argument.**"*

**[DERIVED]** — our own `costmodel.py` against 2026/1127's published benchmarked
config. Not measured on hardware.

## D4. The ring hash's own τ verdicts — **both earlier ones refuted; τ=2 leads**

- **Challenge space eliminates τ=1** — `q^1 = 2^64` is too small.
- **Integral cryptanalysis punishes τ=4** — Beyne–Verbauwhede (2025/932) show
  integral properties survive **monotonically longer with extension degree:
  round 1 at prime, 13 at degree 2, 20 at degree 4.**
- > *"The cryptanalysis lane's 'keep τ=1' and the design lane's 'τ=4' were
  > **both wrong, for different reasons.**"*

⚠ **Three citations that must not be quoted**: 2021/1010's "3,971 AIR
constraints" (its own breakdown sums to 3,071, it is an op count with no AIR,
and it misstates its own ring) · our "2026/1127 fn.11" citation (footnote 11 is
a bare URL) · "2025/1764 Keccacheck" against our local file, which is
**2024/1764, a different paper with zero 'keccak' hits.**

## D5. `[08-17]` ⚑ The lookup arithmetization lever — **REFUTED at 1.96×, and the 3.2× was ours**

⚠ **This entry contradicts `03-MEASUREMENTS.md` §1.8**, which records *"the same
two primitives price at ~3.2× under a lookup argument"* and — to its credit —
flags it as **"a pointer, not a result"**. The pointer has now been measured and
it does not hold.

**The idea**: `R` (Blake3-in-AIR ÷ Poseidon2-in-AIR) is a property of the
*arithmetization*, not of the hash. At 30.6× a bit-oriented hash is hopeless
in-circuit; under a **lookup argument** the same pair was believed to price at
~3.2×, which would put a standard hash within reach and delete the whole
"why Poseidon2" argument.

**The number that closed it**, counted cell-by-cell on **Stwo's DEPLOYED
lookup/LogUp Blake AIR** (384 main + 260 interaction cells per round row,
carries virtual, five xor tables at relation arity 3):

> **Blake3 under lookups ≈ 4,680 cells/compression ⇒ R ≈ 15.7× against our
> 300-cell Poseidon2. Lookups buy 1.96×, not the ~10× needed.** The flip bar
> (< 4,000 blowup-cells) is **missed by 4.7×.**

⚑ **Where the 3.16× came from, and it came from us**: it compared **7.9
gates/S-box for *their* Poseidon against our 2.1 cells/S-box** — *a fat
denominator*. **It had been quoted repeatedly as "the highest-value open
measurement."** The measurement happened; the answer is no.

**Riders that close it further**: the table costs **2²⁴ amortized cells**
(break-even ~2¹² compressions), and the table relation lands at **98.7 bits at
BabyBear⁴ without grinding — below the bar on its own.** Keccak under lookups:
**a wash to negative.**

⇒ **Poseidon2 is now triple-confirmed** (in-circuit 30.6–210× directly ·
recursion pinning it in both characteristics · the lookup escape measured shut)
— **four-fold with §D2's `[08-17]` Kagi addendum**, from the attack side.

**[MEASURED]** — `notes/lasso-over-logup.md`, `minidregg/Selvage/DecomposableTable.lean`
(`feef028`), `notes/hash-landscape.md` Addendum 2.

## D6. `[08-17]` The job-split — **refuted three independent ways**

**The idea**: not every hash invocation in the wrap needs an RO. Split the job —
use a cheap PRF-like primitive (Legendre symbols were the candidate) wherever a
full random oracle is not required, and pay for the RO only where the
transcript genuinely needs one.

**Three numbers, each sufficient on its own:**

1. **PRF-able jobs are 2.2% of wrap permutations.** Absorption is compression
   *at its information floor* — there is almost nothing in the wrap that a
   weaker primitive is allowed to do.
2. **Legendre costs 4 R1CS per bit against the sponge's 1.21 cells per bit.**
   The "cheap" primitive is **3.3× more expensive in the unit that bills.**
3. **The key-recovery record puts Ext4 at ~2^64.6 against our 2^123.6 bar** — a
   128-bit key would need a **degree-9 extension.**

**Bonus corroboration from outside**: **Loquat's own circuit is 93.5% hashing**
— independently the same ~94% shape as ours, which is why there was no slack to
find.

**[DERIVED + THEIR PAPER]** — `notes/aligned-hash-space.md`,
`notes/hash-landscape.md` Addendum 1.

## D7. `[08-17]` ⚑ Weft-1 — **killed as specified, and the epitaph beats the number**

⚠⚠ **Read the tag precisely: KILLED AS SPECIFIED, not "closed as a question."
Weft-2 is a live re-opening** — `06-OPEN.md` §5 and `08-ATTACK-BRIEFS.md`
BRIEF 2. Filing this as a settled dead end is exactly the mistake this line
exists to prevent.

**The idea** (from `02-LANDSCAPE.md` §1.4b): a hash whose **mixing layer is the
already-proved `novelPack` / additive-NTT transform** — the "one proved linear
object" prize — with a lane-wise `x⁻¹` S-box, which the attack record says is
the one shape FreeLunch's authors cannot directly model.

**The number**, exact and self-certifying (`branch(M) = branch(M⁻¹)` duality
lets four exact passes exhaust every codeword with min-side ≤ 2):

> **branch(Weft, t=24) = 6** — against **MDS 25**, and against **Poseidon2's own
> layer at 8 (exact, t=16) / ≤10 (t=24)**.

⚑ **And the structural finding is worse than the number, because branch number
cannot see it**: the mixing matrix is **block-triangular along a subspace
flag** — lanes ≥ 2ᵇ map into themselves for b = 1..4 — and the 0-fixing
lane-wise `x⁻¹` S-box **preserves them.** That is a **4-deep chain of
round-invariant lane subspaces: the 2026/306 subspace-trail shape BY
CONSTRUCTION.**

> ***The alignment thesis imports the code's triangularity, and triangularity
> is the opposite of diffusion.***

**The Chaghri caveat resolves the other way**: the mixing spends **zero**
Frobenius terms, so this is the **Starkad/HADES structured-layer death**, not
Chaghri's. Basis-independent (three random domain bases give the identical
answer); the random-matrix control reads **25**.

**What survives**: only the **dense-composed fallback**, which loses the
one-proved-linear-object prize — i.e. the reason for building it. And
`[WEFT-integral]` / `[WEFT-groebner]` **should not be run against the dead
layer.**

⚑ **The reusable output is a gate, not a verdict**: `swarm/BRIEF-TEMPLATE.md`
gained a **branch-number-first design rule** — *compute the branch number of any
proposed linear layer before pricing anything about it* — paid for by this lane.

**[MEASURED, exact]** — `~/src/ring-ro-hash/weft_branch.py` (`737ea7b`),
`notes/hash-landscape.md` Addendum 3, `notes/k16-proof-and-weft.md`.

---

# E. Substrates and proof systems

## E1. The M31 / Stwo substrate — **CLOSED, its main plank refuted at source**

> *"'Stwo's constraint blowup is additive with FRI blowup': **REFUTED at
> source** — the whitepaper's **Eq. 34 states the identical bound and Eq. 35 is
> worse.** The nonlinear lane's M31/Stwo substrate recommendation loses its main
> plank."*

Field-choice line: *"KoalaBear everywhere. Binary towers as the committed second
field. **Not Goldilocks, not M31, not the BFV limbs.**"* Supporting: KoalaBear
has maximal 3-adic inertia where **Goldilocks splits in 2, M31/M61 in 6.**

⚠ **Separate S-two thread** (the *formalization*, not the substrate): the
Avigad/StarkWare Lean work is *"the twin, chosen deliberately"* — a hand-written
Lean model of the Rust AIR-builder, no extraction, no differential test — and
*"**the premise is unaudited. Nothing in their repo inhabits
`LookupsSatisfied`.**"* Scope stops at the AIR: no FRI, no Merkle, no
Fiat–Shamir, no completeness, no probability space. ⚑ **But: "we do Lean" is no
longer a differentiator.**

## E2. NTT-domain-inside-FRI-domain — **novel and worthless**

> *"**NTT-domain-inside-FRI-domain: novel and worthless.** Absent from a
> 25,765-paper corpus; and **not worth building: NTT is 0.27% of the reference
> prover's time (73% is gadget decomposition)**, the matvec reduction is
> provable as a one-line committed-quotient identity anyway, and
> **coset-separation zero-knowledge is forfeited.** **We report it so nobody
> else builds it.**"*

The idea was genuinely sharp: with `p` the ciphertext modulus and
`v₂(p−1) ≥ log₂(2N) + log₂(blowup)`, the negacyclic evaluation set
`ζ_{2N}·⟨ζ_N⟩` is exactly a sub-coset of the FRI domain, so a FRI commitment
*already contains* the NTT and proving `ĉ = NTT(c)` collapses to domain
membership. **It is correct. It saves 0.27%.**

**[ABSENCE]** for novelty · **[MEASURED]** for the 0.27% · **[DERIVED]** for
the ZK forfeit.

## E3. Plonky3 — **abandoned, by policy**

> *"We are abandoning Plonky3. Upstream code may be read for API shapes and used
> as a throwaway differential oracle; **it never enters the trust path.**"*

The originating correction, in full, because it generalizes:
> *"**The existence of `p3-whir` at our pin is NOT an asset and should never
> again be cited as one.** Every 'X already exists upstream, unwired'
> observation in this repo's notes is a **temptation, not an opportunity**:
> wiring it grows exactly the dependency Selvage exists to replace, and puts an
> unverified Rust engine where a Lean-derived one belongs. **'It's already
> there' is not a reason for anything.**"*

⚑ **And it explained a mystery**: *"Nobody here chose Poseidon2. Plonky3 handed
it to us, and we are abandoning Plonky3."*

**[POLICY, ember]** — not a measurement. §7b of the brief template.

## E4. The blowup-6 floor — **an upstream bug we had frozen as a law**

> ⚑⚑⚑ *"The `log_blowup ≥ ⌈log₂(d−1)⌉` floor is gone. **It was one
> `.bit_reverse_rows()` in a crate we already vendor, and our own gate had made
> it a law.**"*

**The mechanism**: `TwoAdicFriPcs::get_evaluations_on_domain`'s slow path
applies one `bit_reverse_rows()` too many. *Right values, wrong rows.* The
caller folds the AIR over permuted trace rows, commits a wrong quotient, and
emits **a complete, well-formed proof its own verifier rejects.** The slow path
is entered exactly when `log_blowup < ⌈log₂(d−1)⌉` — *"**that is the entire
content of the 'degree-7 S-box needs log_blowup ≥ 3' floor. It is not a
soundness bound, not a property of FRI, and not a fact about BabyBear.**"*

**The gate that froze it**: `fri_blowup_global_knob_survey.rs` asserted
`assert!(!chip_refusals.is_empty(), …)`. *"It was written to stop someone
claiming `lb = 2` was free. **It had become the thing stopping anyone from
discovering that it is** — and it would have gone red the moment the bug was
fixed."*

**Upstream**: present on `main` and in every published `p3-fri` through 0.6.3.
Introduced by PR #1352 (2026-03-02) — **the same commit that deleted the
guarding `assert!(lde.height() >= domain.size())`**, so a loud panic became a
silently invalid proof. **PR #1982 is this exact one-line change and was still
OPEN / CHANGES_REQUESTED on 2026-08-14**, with the maintainer's objection
restating the symptom as the requirement — *"precisely the reading our tree
adopted."*

**The trade, in exact counts**: **prover ÷15.2 · verifier ×2.28 · wire ×~2.4 ·
UDR +20 bits · row ceiling ×16.**

⚑ **This is a dead end with a LIVE TAIL — see §L1.** The config flip is **not
landed** and the current recommendation is contested.

**[MEASURED, verified by construction]** — `circuit/tests/fri_extrapolation_row_order.rs`.

## E5. Eight more proof-system closures

- **CSE does not rescue matmul.** The 2,696,666 → 220 figure is a
  Poseidon2/Merkle shape that re-reads subterms; a contraction's `m·k·n`
  products are **pairwise distinct**, so CSE leaves **318,040 gates at
  318,040**. **No gate-level emit of any kind gets below `m·k·n`.** *(The
  conclusion "matmul needs a vector relation" stands; the reason was wrong.)*
- **Poseidon2 virtualization by sumcheck — mechanism REFUTED, direction
  confirmed.** A degree-(α+1) fold costs 77–132 ns against 55 ns to commit, so
  **GKR loses at α=7 by 1.4–2.4× and wins only at α ≤ 3.** The layer budget is
  **0.42–0.71 layers at α=7.** In-AIR narrowing won instead: **352 → 141 gates,
  landed `daa207ae7`.**
- ⚑ **The 78–308× exchange rate was in the WRONG UNIT** — counted field
  multiplications, never converted. **Measured ~5× in wall clock at lb=3.**
  *"Never quote 78×/308× as a wall-clock budget."* ⚠ Every plan priced against
  it needs re-pricing.
- **"Lazy accumulation is free" (0.88×) — dead.** It is a **column** ratio;
  in-tree the lazy fold is 0.84× at B=256 and **break-even at the deployed
  B=4.** *Several notes cited this cell for a claim it does not make.*
- **`fold_add`-as-one-opening at 690× — prover-side only, and B=4**, so the real
  figure is **4.2×**. The verifier moves the *opposite* way, and the shared-tree
  fix collides with per-party root binding. Its prior-art premise also died
  twice: Binius64's blueprint says it almost verbatim, and **Zama 2024/451
  solved our exact statement the AIR way.**
- **"Move the grind off the critical path" — refuted by construction.** Its
  input is the completed FRI commit-phase transcript, which does not exist
  earlier. *Grinding anything earlier binds less and is a weaker protocol.*
  Also **grind window `c = 8` is refuted** — 8.29× work at twice the p99.
- **"`lb=6` is 2.9× off the optimum" — refuted; it was a grind draw.** The grind
  is exponentially distributed and drew 0.04 / 8.2 / 10.1 / 31.9 / 40.0 /
  **40.8 ms** across one ladder. *"The published lb=3 point paid 40.8 ms of
  grind against lb=4's 10.1 — **that 30 ms of coin flip WAS the reported
  optimum.**"*
- **"Conjectured 130" — a WITHDRAWN regime. Never quote it.**
  `ethereum/soundcalc` commit `ffaeb81`, 2025-11-17: *"Remove CBR (due to DG25
  and CS25)."* **57 of the 130-vs-73 headroom is a withdrawal, not a knob.**
  And **capacity is refuted over prime fields with smooth domains — our exact
  setting** — with a cheap proven alternative: **WHIR-UD costs 4× proof size,
  3.4× verifier, and 0× PROVER** against WHIR-CB.
- **Multiplicative FRI does not exist over a binary field.** The fold divides by
  `2` and `2x`; at char 2, `f(x)+f(−x) = 2f(x) = 0` and squaring is Frobenius,
  so the `{x,−x}` fibres are singletons. Migrating `FoldingData` would not be a
  migration — it would be **a different protocol.** ⚑ And the trap:
  `Proximity.lean:178`'s `two_ne : (2:F) ≠ 0` is **uninhabitable at char 2**, so
  *"every theorem over it goes VACUOUSLY TRUE, on a green build."*
- **Changing the proof system between tower layers is not the lever.**
  **`K = wrap/leaf`: ours is 26.9; theirs is < 1.** *Our problem is not the
  proof system — the leaf is too small.* And **folding arity is a null knob**
  (−2.0% hashing, +0.3% arithmetic).
- ⚑ **Binary fields do NOT rescue in-circuit verifier cost.** Measured: the wrap
  is **arithmetic-bound — 36.45% hashing vs 60.75% arithmetic — so a free hash
  is worth only ×1.57.** *"The binary-field case must be argued on cryptanalytic
  surface, not on verifier cost."* Reached independently from the hash side.
  > ⚠⚑ **`[08-17]` THIS ONE'S PREMISE MOVED, AND IT MOVED TOWARD RE-OPENING.**
  > The arithmetic this entry calls dominant is **exactly what §E9's landed
  > algebraic collapse and §1.10's packing retune deleted.** Poseidon2's share
  > of the wrap goes **36.45% → 52.36% → 73.3% measured (~81% derived)**, so a
  > free hash goes **×1.57 → ×2.10 → ~×5.** The wrap is no longer
  > arithmetic-bound; at `a4/K16/rec4` it is decisively hash-bound.
  > **The closure sentence — argue the binary case on cryptanalytic surface —
  > still stands as ADVICE, but the number that made it a dead end does not.**
  > *A cost verdict outliving its premise, caught here rather than six weeks
  > out.* `03-MEASUREMENTS.md` §1.9, §1.10.

## E6. `[08-17]` ⚑ ECFFT — **blocked by its OWN theorems, not by constants**

**The idea**: our BFV RNS limb primes have low 2-adicity (measured **13 / 14 /
17**), which is why the prover emulates them rather than proving over them.
**ECFFT** replaces the multiplicative subgroup with an elliptic-curve
isogeny domain and needs **no 2-adicity at all** — so limb-native, zero-emulation
proving should follow.

⚑ **The kill is unusual and worth the section: the tool is refused by the
theorems in its own papers, at OUR parameters, before a single constant is
compared.**

**Closure 1 — the Hasse trace-height cap.** Part I Thm 4.9 / Part II Thm 8:
curves with a 2^k subgroup are guaranteed only for

```
    2^k ≤ 2√q
```

(the Hasse interval has width `4√q`, so it contains a multiple of `2^k` only up
to that point); `Find_Curve` demands `q ≥ 2^{2(k−1)}`; Part II Thm 1 states the
IOP for computation length `T ≤ √|F|`. ⚑ **And the cap binds the group size ⇒
Riemann–Roch dimension ⇒ TRACE HEIGHT, not the blocklength** — Thm 12's domain
is `|T| = ρ⁻¹·2^ℓ`, so **blowup comes free as extra cosets and is
unconstrained.** Instantiated: `q₀, q₁` sit below 2³⁶ ⇒ `k ≤ 18` ⇒ **max height
2¹⁸**, and the 98,304-equation family pads to **2¹⁹ per limb.**

> **Short by 2×, structurally, before any soundness or constants enter.** And
> `q₂ ≈ 2³⁷` allows exactly 2¹⁹ **with zero margin** — no headroom for
> degree-correction slack, masks, or growth, against a family size that is
> *current*, not target.

**Closure 2 — the error term exceeds 1.** The batched-FRI additive term is
`O(ρ²|T|²/(ε⁷q))`. At height 2¹⁹, lb=3 ⇒ `|T| = 2²²`, over `q₂ ≈ 2³⁷` this
carries `|T|²/q = 2⁴⁴/2³⁷ = 2⁷`: **the bound exceeds 1 outright with base-field
challenges.** The theorem as stated gives *nothing* at our blocklengths over
36/37-bit fields, and the rescue (extension challenges) **is not in the papers**,
whose statements are base-field-challenge only.

**And the constants would have been FINE**, which is what makes this a clean
theorem-kill rather than a pricing one: ~4× the DFT multiply count ⇒ **≈4–6×
the LDE**, and since DFT is 46–80% of prover *arithmetic* while the prover is
**hash-bound by 5.0–7.2×**, that is **≤1.6× on arithmetic and ≈nil on the
total.** ⚠ The one implementation datum in circulation —
`wborgeaud/ecfft-bn254`, `n = 2¹⁴`, **ENTER 275.5 ms vs classic FFT 4.58 ms =
60.2×** — is **the wrong op to quote for a prover**; per-layer EXTEND is
≈60/14 ≈ **4–5× a same-size FFT**, and *nobody has published a tuned
prover-grade number.*

⚑⚑ **THE DOMINATING MOVE, and it is why this dead end is worth more than most
live ones: THE LIMB PRIMES ARE GREENFIELD.**

> ***ECFFT is the tool for fields imposed from outside (secp256k1, P-256). Our
> limb fields are not imposed.*** `fhe.rs`'s `BfvParametersBuilder::set_moduli`
> is a public API.

Sieved: **68 candidate 36-bit and 151 candidate 37-bit primes with 2-adicity
24.** Concrete triple `0xfed000001 / 0xfd9000001 / 0x1ff5000001` gives
**log₂Q = 108.978 against the deployed 109.000 (Δ = −0.022 bits).** With those,
**classic FRI reaches height 2²¹ at blowup 8, per limb, zero emulation, at
overhead 1.00×** — banking the **4.80× committed-element deletion.** Cost: **a
re-genesis flag day + an H1 re-measure + an `[UNRUN]` fhe.rs smoke test.**

⚠ **Two of our own premises were wrong and are corrected at source**: the fold
set is **degree 4096, not 8192**, and the 2-adicities are **13/14/17**, not
"≥14." ⚠ **The circle-STARK route is refuted in the same breath**: all three
limb primes have `v₂(q+1) = 1`, so `p+1` domains are out.

⚠ **And it re-opens something**: limb-native proving **re-opens the cross-limb
provenance hole** that row-interleaving closed. The Z_Q sumcheck (§`02` 2.4b) is
the candidate binding, and it closes Hole A while closing Hole B *against
itself*.

**If EC-FRI is ever wanted**: it reduces to plain RS over exotic domains, our
cone is agnostic at the definition level (`dom : ι ↪ F`; **0 `IsPrimitiveRoot`
tree-wide**), and the fold needs **6 named missing lemmas — only one with real
AG content** (Hasse + Vélu + 2-descent), *"and that one exists in no proof
assistant I know of."*

**[THEIR PAPER]** for both closures — *their theorems, our parameters* ·
**[MEASURED]** for the 2-adicities and the prime sieve · **[DERIVED]** for the
constants. `notes/ecfft.md` · `docs/VERDICTS.md` §3b.

## E7. `[08-17]` Frobenius / minpoly levers on the in-circuit verifier — **CLOSED BY PROOF**

Two of the five Galois pathways died to arguments rather than measurements,
which is why they are here: **they will not be re-proposed.**

- **OOD absorption is already at the information floor.** `observe_ext`
  decomposes to exactly **4 base coefficients = one Ext4 value — the same
  object.** The 82,256 absorbed base felts ≈ **10,282 of the 11,128
  q-independent perms**, so the "absorb the minimal polynomial instead" idea has
  **~846 perms (2.2%) to work with**, and minpoly form is **net negative**
  anyway (adds 3 K-MACs/column/query to delete ~0.005% of `Alu`).
- ⚑ **The tempting conjugate-point variant is UNSATISFIABLE.** It would delete
  ~5,100 absorption perms (13% of wrap perms), but `ζ^{p^j} = ζ·g` requires
  `ord(g) | 4` (j ∈ {1,3}) or `ord(g) | 2` (j=2), **and the trace generator has
  `ord(g) = 2^k ≥ 16`.** A two-line cyclic-group argument, and Lean-statable.
  ⚠ **Even if it were satisfiable** the sample space shrinks `~2¹²⁴ → ≤ p²−1 ≈
  2⁶²`, giving a DEEP union bound of **2⁻⁴⁸ at degree 2¹⁴ — ~76 bits below the
  ~124-bit capacity ledger.** *(The note quotes 2⁻⁴⁸, not any flattering
  figure — worth noticing, given §M.)*
- ⚠ **A misattribution of ours, retracted at source**: ethSTARK v1.2 §3.8.2
  spends the conjugate quotient to prove **F_p-definedness of committed
  columns** — a purpose our base-felt MMCS leaves make *structural* — **not to
  cut costs.** The lever was read into the paper.
- **Fold-orbit: null AT SOURCE.** p3 already spends the ±x orbit fully (the
  prover supplies exactly `2^arity − 1` siblings per phase and the verifier
  seats its own folded value before hashing). ⚑ **This explains the previously
  measured null arity knob** (−2.0% perms, +0.3% Alu) rather than leaving it a
  curiosity.
- **Trace/norm: mathematically identical to packing** (`packEquiv`) — and a
  probabilistic one-trace-check variant would carry a **1/p = 2⁻³¹** error term,
  refused.

**[DERIVED + PROOF]** — `notes/galois-levers.md` §1, §4, §5.

## E8. `[08-17]` The job-split → see §D6

Filed under hashes because the primitive is the transcript sponge, but it is a
proof-system closure too: **PRF-able jobs are 2.2% of wrap permutations**, and
the cheap primitive costs **3.3× more per bit** than the sponge it replaces.

## E9. `[08-17]` ⚑⚑ Sumcheck-batching the reduced opening over two-adic FRI — **A PCS REPLACEMENT, NOT A BACKEND REWRITE**

⚠ **This closes §L3 below.** It had been the single biggest named available win
for days, and the reason nobody took it **had never been written down.**

**The idea**: one sumcheck over `Σ_k α^k v_k` replaces ~14,300 per-column
ExtMuls in the wrap's reduced opening. Priced at **×2.13 on the wrap / ×2.05 per
turn.**

**The obstruction, and it is structural:**

> A sumcheck over the `q · Σw ≈ 390,716` opened values terminates in a single
> claim about **the multilinear extension of those values at a random point,
> `Ṽ(r)`.** The verifier can discharge it in exactly two ways:
> 1. **Recompute `Ṽ(r)` from the values** — Θ(N) again. **No saving.** The
>    sumcheck was free only if someone else answers the final claim.
> 2. **Open it from a commitment to `V`** — but the only commitment the opened
>    values have is **the Merkle leaf of the child's MMCS, and a Merkle root
>    supports no evaluation opening.**
>
> ⚑ And the verifier **already holds every one of those values in the clear** —
> it must, because it hashes them into the per-query leaf sponge (**64.9% of
> in-circuit permutations**). The values are not hidden behind a commitment that
> could be opened; they are **plaintext circuit witnesses that are separately
> hashed.**

> ⚑⚑ ***Batching the reduced opening with a sumcheck requires an
> evaluation-binding commitment on the opened values. Two-adic FRI gives
> univariate openings only. Lever 3(b) is a PCS REPLACEMENT, and its cost is a
> new commitment scheme, not a backend rewrite.***

**That is exactly why SP1 6.4 went Jagged → Stacked → BaseFold and OpenVM 2.0
went Stacked → WHIR**: both are multilinear PCSs whose openings *are* MLE
evaluations, so the terminal claim is answerable. **Ours cannot answer it.**

⚠ **Consequence for our own docs**: `APEX-VERIFIER-AIR-REDUCTION.md`'s Lever D
must be re-tagged **COORDINATION-REQUIRED → PCS-REQUIRED.** The obstruction was
never ownership.

⚑ **Three docs carried three different verdicts on the same phrase, about three
different circuits, and nobody had noticed**: pure upside (`WRAP-NATIVE-HASH-DECISION.md:134`)
· an *ownership* obstruction ("it's in the fork", `APEX-VERIFIER-AIR-REDUCTION.md:157`)
· "now MARGINAL" (`HORIZONLOG.md:18343-18345`), **true of gnark only.**

⚠ **A retraction inside the retraction, and it inverts the finding.** The first
draft of the gnark line said gnark *"may still have the point-sharing half open
— `deriveOpenInputReducedNative` recomputes `S_x` per `(matrix, point)`."*
**False at source.** `chain/gnark/stark_open_input.go:445-465` computes `sx`
**once per matrix, outside the `for pt` loop**, and says so in a comment.
⚑ **Which strengthens the finding: gnark has had BOTH halves since 2026-07-13,
and the Rust in-circuit verifier was the only rung still paying `P` chains per
query.** *(`feedback-read-the-blocker-before-you-relay-it`, again, and it cost
one wrong sentence in a committed doc.)*

**What IS reachable was taken**: the purely algebraic half landed at **×1.436 on
wrap cells** (`03-MEASUREMENTS.md` §1.9), and the **×2.13 endpoint was then
reached by a different road entirely — packing, at ×2.011 measured** (§1.10).

**[DERIVED, structural]** — `notes/sumcheck-batched-opening.md` §0a ·
`docs/LEAF-VS-RECURSION.md`.

## E10. `[08-17]` Deferred (Halo-style) accumulation over Merkle-only commitments — **factor 0**

**The idea**: don't discharge each layer's opening claim in-circuit; **defer and
accumulate**, discharging once at the end. It is the move that makes folding
schemes cheap, and we hold every piece of the machinery.

**The number that closed it**: the sumcheck endpoint claim per layer is over
**`N·q ≈ 195,814` base values**, and interior deferral costs **2N** (N eq-tensor
ext-mults + N MACs) **against the N-MAC α-Horner it replaces.** The sumcheck
rounds themselves (~log N ≈ 18 ext-ops) are free — ⚑ ***the terminal claim is
the whole bill***, which is the same shape as §E9 and for the same reason.

> ⚑ **The MLE obligation cannot travel even ONE layer.** Each layer holds
> exactly its child's opened values, and a univariate-at-ζ view **cannot answer
> an MLE point query.** There is nowhere for a deferred claim to go.

The one native hop that exists is **gnark's, already landed and already retired
as MARGINAL** (the 0.32M-constraint residual). An accumulator binding site would
cost ~19 ext = **10 perms/layer** — i.e. the binding is not the problem; the
discharge is.

**Live only with a multilinear PCS — the SP1/OpenVM road**, which is §E9's
conclusion arriving from the other direction. **Two independent pathways, one
obstruction.**

⚠ **A named-not-proved dependency sits under any future attempt**:
`ComposeErrorBound` (`Selvage/HeteroComposition.lean:230`). And
`OB2_depth_composition_nonneg` composes **protocol ROUNDS, not stack LAYERS** —
reading `(t+k)·ε` as a per-layer bound is a **category error**, recorded because
it has been made.

**[DERIVED]** — `notes/galois-levers.md` §2.

---

# F. zkML

## F1. The bf16 4× thesis — **measured at 1.4×**

The file's own title: *"**Phase 0: the thesis does not hold. 1.4×, not 4×.**
This is the measurement that killed the bf16 4× thesis and with it the plan
built on it — `PLAN.md` is now `notes/archive/PLAN.md`."*

| design | baseline | 54-point sweep | median | points below 2× |
|---|---|---|---|---|
| static shift *(what was assumed)* | 2.63× | 1.51–3.30× | 2.29× | 17/54 |
| **dynamic normalization *(the real design)*** | **1.54×** | **0.85–1.99×** | **1.42×** | **54/54** |

*"At one parameter point bf16 is **slower**."*

**The two errors that produced the 4×:**
1. *"'Requantization is absent, not optimized' — **false.** It is the same
   operation, moved into its expensive setting."*
2. *"**The 75% double-counts.** Of the 75 points, **49.8 are already lookup
   tables.** The two halves of the claimed saving are not additive, and I added
   them."*

**The ablation that located the real win**: baseline 2.63× → saturation removed
1.85× → power-of-two scale removed 1.94× → **both removed 1.05×.** *Jointly
~1.4× — which does not justify reordering a programme around format choice.*

⚑ **The root cause is a contradiction nobody noticed for days**:
> *"**bf16 is NOT a block format — it carries a PER-ELEMENT exponent.** I wrote
> 'block-float bf16' throughout the plan and never noticed those are
> contradictory."*

Two adjacent sub-claims died with it: *"bf16×bf16→fp32 never rounds"* (false as
stated) and **rank-1 exp** (refuted for any exact design).

**[MEASURED]** — `phase0/`, and the pricing is *conservative* (the harness
charges ~2× for a data-dependent shift where Hao et al. measure 3.4×).

## F2. Float-native transformer proving — **closed empirically, by the float camp's own numbers**

**The cleanest closure available**, from Spain (OSDI'26)'s own Figure 4 caption:
*"The first exception is zkGPT, which outperforms Spain on all metrics."* Same
workload, GPT-2 seq=32:

| | zkGPT (quantized) | Spain (float) |
|---|---|---|
| prover | 64 s | **750 s** (11.7×) |
| verifier | 5.8 s | 78 s (13.4×) |
| proof | 88 KB | **1.6 MB** (18.6×) |

Their §8, unprompted: *"Spain's prover isn't the fastest in the literature;
that honor belongs to zkGPT."*
> **The best approximate-float system loses to quantized by ~12×, reported by
> the people with every incentive to show otherwise. That is the cleanest
> empirical answer available to "should we just do float?" and it is no.**

**Spain as a design, rejected with four independent reasons**: its
one-constraint div/sqrt saving is *"deleting the range checks, bought three
ways, every one unavailable to us"* — **squares-are-nonnegative is a theorem of
ORDERED fields and false in F_p** (every F_{p²} element is a square); the
magnitude bound lives in the **dark integer PCS** (hash PCS have none); rounding
is **never proved**. Plus: interactive, **designated-verifier (the verifier
holds the RSA factorization)**, **2^-40 soundness**, ~11× per-constraint backend
penalty by their own A/B.

⚑ **And Spain's composition lemma is correct and vacuous**: at its published ML
parameters the ReLU guarantee is **δ = √ε = 2^-20**, and **Zamir's trigger
weight at GPT-2 effective depth (≥24) is ≤ 10 — ordinary weights.**
> *The best ε-carrying system in the literature is exploitable at its own
> published parameters with ordinary weights at GPT-2 depth.*

⚑ **Zamir's Theorem 1 kills the generic layerwise design outright**: for *any*
network F there exists F′ **exactly functionally equivalent** such that for
every input and **every target z in the output range**, a δ-consistent
transcript exists whose output equals z. *"The attack needs **no weight
inflation at all**. 'Bound the committed weights' is not a mitigation at
transformer depth."*

⚠ **ZIP (CCS'25) needs 37 hours for an 11M-parameter 4-layer mini-BERT.**
⚑ **This figure is transcript-only** — lane `a4e77a94`, session `3e64269c`. It
is **in no file in the repo**; ZIP appears three other times in the notes and
none carries it. **Re-source before publishing.** What the notes *do* carry
about ZIP is an accuracy figure: mini-BERT/SST-2 **85.65% → 77.14%, 8.5
points**; UTKFace *"no convergence."*

⚑ **The 8,854-gate strawman, retracted.** *"I cited Garg et al.'s '8854 gates
for IEEE fp32 multiply, ~9000-fold overhead' as the baseline. The lane traced
it: **nobody ever implemented it.** It propagates **Garg → ZKLP → ZIP by
citation.** Worse, ZKLP reports Garg's own costs as 108/25 while **Garg's Table
1 says 89/35**, and ZKLP concedes *'we are unable to present a fair
comparison.'* **Discount that number.**"*

**The standing "deliberately not doing" list**: IEEE-754 bit-exactness ·
error-tolerant proving · approximate sumcheck as accumulation fallback (*wrong
field, no PCS, 14× the precision of exact*) · **MXINT8-as-conversion** (*zero
shipped models; it proves a derivative*).

## F3. Nine zkML closures worth inheriting

- ⚑ **Public router binding is a PRIVACY BREAK.** A sequence decoder recovers
  **91.2% of tokens top-1 / 94.8% top-10 from expert selections alone**; added
  noise *"reduces but does not eliminate"* it. **Router binding must be
  ZERO-KNOWLEDGE over `topk_ids`** — and our own MoE spec's statement variants
  all assumed the selection could be committed and opened.
- **"MoE router binding is unclaimed" — RETRACTED.** Two refuting papers were
  **already in `~/paperbin/` on the day the absence was declared.** The sweep
  read first-2-page caches and both bury MoE in a subsection.
- **NVFP4 does not transfer.** It preserves within-block exactness but its scale
  is E4M3 with a per-tensor FP32 second level, so *"rescaling is a shift"* and
  our cheap width-8 alignment window **do not transfer.** Our arithmetization is
  **MXFP4-specific.**
- **The registry commitment as shipped is a checksum no prover can open.** See
  `01b-STEERS-RECOVERED.md` §22 for ember's version, which is better.
- **"A public weight-and-architecture registry is an open position" — refuted at
  four layers** (Apple PCC, Berkeley 2504.04715 App. B, Attestable Audits
  2506.23706 *already in our own paperbin*, OpenSSF Model Signing + Rekor).
  What survives: **none binds architecture, none binds which model is active at
  serving time, none is third-party-operated with a public opening.**
- **Proof-aware QAT — refuted independently twice.** And **DeepSeek-V4 does FP4
  QAT at 1.6T scale.**
- **Proof-of-Learning is broken and has been for five years** (Papernot et al.,
  EuroS&P 2023). *"If our answer to Hollow-LLM is a registry, we bind IDENTITY
  and sidestep EFFORT — say that plainly."*
- **"Append-dominant KV" is true of the computation, false of serving.** Fold
  over the **accepted token sequence**, never over cache writes.
- **Ozaki FP4-limbs transplant — refuted as an import.** Its engineering core
  *"is deferred carry / lazy reduction, which ZK has had for years under six
  names in six codebases."* Its distinctive parts (base-13, p×q splits, RNS) are
  hardware artifacts. Numbers softened: full Kulisch **3.5×** (was 4.5×);
  alignment-window **10.3×** (was 17×). **Range checks are 79–99% of cost.**
- ⚑ **Sampling cannot amortize WITHIN a wide inference** — *an argument from our
  own theorem*: instantiating `AuditSampling` at inference forces
  `ε_chk ≥ 1 − 1/N` on width-N layers, so `q ≤ p/N`. **It amortizes which turns
  get proven, never which ops within a turn.** And **sampling amortizes proofs,
  never the ledger** (2025/358: covert security buys no asymptotic ledger
  savings).
- ⚠ **"Open" zkML mostly isn't**: DeepProve `NOASSERTION`; JSTprove *"NO USE
  RIGHTS ARE GRANTED"*; **ezkl has no LICENSE file at all.** And Attestable's
  *"×50,000 faster than ezkl"* uses a **2024-01-28 blog benchmark on linear
  regression and random forests** — *"that comparison is a straw man."*

---

# G. Hardware

- **The Amdahl ceiling for tensor silicon is 1.26× at the deployed point.**
  GEMM-shaped work is only the two LDE rows — **20.8% of prove** — and **MLE
  folding is under 0.1%.** Trace height does not rescue it: swept 2^6→2^12,
  `hash/arith` is flat-to-rising, because the Merkle leaf is a sponge over the
  whole row and scales like the LDE.
- ⚠ **BAT needs one operand PREKNOWN.** Free for NTT twiddles; **not free for an
  MLE fold or a sumcheck round.** *"Grouping them as 'also GEMM-shaped' is true
  and a different claim; **porting by analogy would be the expensive
  mistake.**"*
- **Four-step NTT does not survive to LDE sizes** — the extra-multiply factor
  grows as √N/log N: **341× at N=2^12, 3277× at N=2^20.** Four-step and radix-2
  are the m=2 and m=log N members of one family costing `m·N^{1+1/m}`.
- **Drop MoMA and MORPH from the tensor thread.** MoMA does not use tensor cores
  at all (scalar 2^64-limb Barrett); MORPH's GEMM is base **conversion**, for
  256–753-bit moduli. *(Both are still vendored — see `07-ARTIFACTS.md`.)*
- ⚑ **Two wgpu devices cannot share a buffer, so fusion was unreachable BY
  CONSTRUCTION** until the arena consolidation.
- **Coset-twiddle tables — refuted as the mechanism.** Width-independent in
  counts exactly as predicted, *"and ~zero on a clock."* ⚑ **A
  width-independent counted term is not thereby the cost.** The real one is
  **rayon's cold hand-off** — the same workload inside `ThreadPool::install` is
  **11–27× faster.**
- **Dedicated ZK-prover ASICs — the market selected against them.** **No
  ZK-prover ASIC has ever been fabbed and independently measured** (NoCap,
  zkSpeed, UniZK, zkPHIRE, PipeZK, SZKP — all simulation). **Irreducible shut
  down 2025-11-12** after 3.5 years: *"FPGAs underperformed GPUs."* **Succinct
  went 160×RTX 4090 ($300–400k) → 16×RTX 5090 (<$100k) in six months from
  software alone.** ⚑ Counter-evidence in the same file: **NVIDIA shipped
  `clmad`** (SM80+, CUDA 13.3), sumcheck **4.1–12.9× on B200**, citing Binius.
- **Also zero of the academic FHE ASIC designs (F1, CraterLake, BTS, ARK, SHARP,
  Trinity) has ever been fabricated.** Every number is a cycle-accurate
  simulator. Exactly one DPRIVE chip became silicon (Intel HERACLES), at the
  very end of the program.
- ⚠ **AWS F1 retired 2025-12-20** — every ZPrize FPGA artifact now targets dead
  silicon.
- ⚠ **`ThreadPool::install` as "the biggest untaken lever" is NOW IN DOUBT** —
  advertised 2.2–2.5× from the laptop, **measured 1.14–1.80× on hbox.**

---

# H. Framings and words that were retired

- **"Boundary" — retired as a term.** It collides with **border rank** in
  precisely the community most likely to read a matmul claim. The principle's
  real name is **`polynomial virtualization`** (Thaler 2025/2041). Also never
  "succinct PCP" or "certificate complexity" for this.
- **"Nobody has turned boundary choice into a discipline" — FALSE.** Distiller
  (eprint 2022/1557, IEEE S&P 2023) did it. What survives is narrower and still
  ours: **the cost theory, and the Lean instantiation.**
- **e-graphs as the joining technology — wrong tool.** *"e-graphs preserve
  **functional equality**, and **Freivalds is not an equality — it is a
  soundness-preserving reduction.**"*
- **eprint 2026/1390 is NOT a general Ω(m) commitment floor** — it is a
  lookup-specific, self-described **restricted-model separation**, and it was
  cited as a general floor **at five sites**.
- **Thaler's 0.18–0.33% sumcheck overhead does not apply to decode.** Overhead
  = `1/B + 1/n`; at B=512 that is 0.220%, **at B=1 it is 100.02%, and
  autoregressive decode IS B=1.** ⚑ *"The most-cited number in sumcheck-for-ML
  does not apply to the workload everyone wants to prove, and we have been
  quoting it."*
- **"It composes with our multilinear substrate" — unearned.** Ours is
  `variable {F : Type*} [Field F]` — **field-pinned.** A ring instantiation is a
  typeclass generalization *plus* a re-derivation of every soundness bound from
  `|F|` to `|A|`.
- **SuperNeo's "128× more data" — dead, killed by its own authors.** Feb said
  `64 × 64 = 4,096 **bytes**` vs 32 bytes ⇒ 128×; Aug says `64 × 64 **bits** =
  4,096 bits` vs 256 bits ⇒ **16×.** *"Never cite 128×."*
- **Neo/SuperNeo's fix does not apply to us, three ways**: the fix is *"stop
  being hash-based"* and **we are literally the row Neo labels Arc**; our field
  is off its map (31-bit vs its 61–64-bit parameterizations); and it is
  unmeasured — *"no constraint count for its own recursive verifier."* And
  **Neo is structurally incompatible with binary fields**: pay-per-bit is a
  statement about lattice **norms**, and characteristic-2 fields have none.
  *That question is closed.*
- **Paneth–Pass 2026/662 does not supersede our accumulation composition** — it
  is a SNARG for **P, not NP** (it escapes the barrier by giving up knowledge
  soundness) and requires tree-bounded mergers that **exclude DAG merge
  topologies.**

---

# I. Ligerito — ⚑ **NOT a dead end, and the record almost made it one**

Filed here because a prior lane's verdict — *"Ligerito-family soundness cannot
compose from what we hold"* — read as *not worth pursuing*, and ember's
correction (`01-STEERS.md` §8) is what reopened it. **Exploratory formalization
then refuted two of six "absent" claims and inverted the sequencing.**

1. **NOT broken. The errata are display-only.** *"'Ligerito is broken' would
   have been the flattering-number sin in reverse."* Every base in the theorem
   it quotes (AER24 §3.2 eq 18) has the form `1 − (·)/m`, which settles both
   typos. **The cross-check that decides it**: the note's own `|S_i| = 148` is
   exactly `⌈−100/log₂((1+ρ)/2)⌉`, and the printed base would have given **71**
   — so §6.4 and the benchmarks used the **corrected** base. *The claimed
   100-bit level and the proof sizes stand.*
2. ⚑ **The general-code bound is the useful one, and it sits at OUR proved
   radius.** `d/(3m) ≈ (1−ρ)/3` **is** our proved radius, exactly.
   > *So the cheaper of Ligerito's two bounds is the one our floor already
   > reaches, and the expensive one fails on a leg we have already
   > independently identified as open. **That inverts the intuition that "RS is
   > the easy case."***
3. **The headline RS bound is the expensive one** — it needs `d/2` from
   Diamond–Gruen Cor 3.7 on top of BCIKS Thm 4.1, *"precisely the one our
   `Selvage/ProximityGapUDTight.lean` leaves open behind the named hypothesis
   `PolishchukSpielman`."*
4. **Priced honestly**: the general-code bound costs **241 queries instead of
   148** at λ=100, ρ=1/4 — **a 1.63× proof-size penalty bought in exchange for
   standing entirely on proved ground.**
5. **A third finding neither the paper nor anyone's list had**: §6.4 drops every
   `1/|F|` term on the ground that `|F| ≫ 2^λ`, but **at the paper's own
   experimental parameters the headroom is only 2^28 while the first-round term
   `m₁k₁` is around 2^26–2^30** — *so those terms land at or above the query
   term.*

**What genuinely IS absent**: the `ℓ = m` interleaved proximity gap, column
openings, and any *proof* about tensor coefficients. Our `ℓ = 2` unique-decoding
root-counting proof does not generalize to it.

**[DERIVED + BUILT]** — `Selvage/LigeritoInterleaved.lean`, 567 lines, no
`sorry`, no `axiom`, commit `0c08c93`.

---

# J. Extension degree — Ext5 and Ext6

- **Ext4 → Ext6 buys ZERO bits** by **Fenzi–Sanso Lemma 3.5**, while paying
  every sumcheck round; Ext6 overshoots 128 by 57 bits. **Ext5 is the right
  degree.**
- ⚠ **Do not double-count**: the Fenzi–Sanso loss and the Crites–Stewart
  Elias-radius correction are **the same `1/log p` term** — ~1.5 bits at our
  knobs.
- ⚑ **A second, independent reason Ext6 dies under a KoalaBear migration**:
  `3 ∤ p_KB − 1`, so **there is no binomial degree-6 extension** — 11 files plus
  ErrorBudget120's 137-bit target. *(Same family: **`X⁴−11` becomes reducible**
  at KoalaBear, so leaving it makes the "quartic field" **a ring with zero
  divisors, silently.**)*
- **Ext5 fixes the LogUp wall (100 → 136) and does nothing for the query wall.
  There are two independent 100-bit walls and extension degree moves only one.**
  The query wall is **query-count-bound.**
- **The EF's own per-zkVM table is the closing evidence**: Pico KB⁴ **53** ·
  Airbender M31⁴ **67** · OpenVM BB⁴ **100** · SP1 KB⁴ **100** · ZisK
  Goldilocks³ **128** · zkDTVM KB⁵ **128**. ⚑ **Nothing on a degree-4 31-bit
  field reaches 128.** And **our Ext4's realized soundness is 100 bits**, not
  the field-size 2^123.6.

---

# K. Lattice / SIS

- **Negacyclic lattice PCS (Hachi, Greyhound, LaBRADOR) are dead at KoalaBear** —
  it fully splits `X^d+1` for every d ≤ 1024.
  ⚠ **With a retraction attached**: *"'lattice-PCS-friendly primes and
  FRI-friendly primes are disjoint' — **true only for negacyclic cyclotomics.**"*
- **Verdict is BUILD-TOWARD / WATCH, not adopt.** LatticeFold/Neo's "128 bits"
  *"traces to a 2018 enumeration-era estimator run and **re-derives to ~98 bits
  core-SVP**."*
- ⚑ **Two security conventions differ by ~30 bits and neither family always
  says which** — the LaBRADOR/Greyhound family and the LatticeFold/Neo/RoK
  family. **The single most consequential finding of the SIS lane.**
- **ACLMT (2022/941) — "dead as a proof, not broken."** Its only security proof
  rests on an assumption its own first author has publicly implemented an attack
  against (*"Knowledge K-M-ISIS is false"*), and a co-author states in print
  that this renders the proofs *"vacuous."* **But nobody has produced a concrete
  forgery.** ⚠ *Do not cite it as a proven-secure lattice SNARK; do not call it
  broken either.* And **eprint 2024/30 is a DIFFERENT result** — keep them
  straight.
- **BFV-limbs-as-packed-sumcheck-fields — REFUTED.** The transfer result
  **dropped the `(2k−1)d` numerator from the `p^k` comparison — zero saving at
  λ=100** — and the limbs' two-adicity is consumed by the FHE NTT.
- **Limber's field floor excludes BabyBear.** From the paper's own Remark 5.9
  (`k=1`, `P > 32λm`, `q ≥ 4P²`) at λ=128: **m=6 already needs 2,416,115,716 >
  2,013,265,921.** *"The set of (field, width) pairs where it helps us is
  empty."* ⚑ **And this refutation exists only as Lean, in
  `minidregg/Theory/IntegerFingerprint.lean` — see `07-ARTIFACTS.md` O2.**
  While it sat there, `notes/float-in-zk-three-regimes.md` still presented the
  Zinc/Limber regime as a live alternative.
- ⚑ **Limber's Table 3 is not certified by its own Theorem 5.5.** Evaluating its
  stated `(32λm/P)^s` on its own Table 3 at λ=128 gives 2^−110, 2^−104, 2^−91,
  2^−94, 2^−107 — **none reaches 2^−128** — and the **headline best-overhead row
  (k=13, overhead 0.033) is outright vacuous** (`32λm = 102,400 > P = 65,536`).
  Traced to an Appendix A script using a bad-set count 8× tighter than the
  theorem. **Machine-checked in the same Lean file. The only step missing is
  telling anyone.**

---

# L. ⚑ Live tails — dead ends whose *recommendation* is contested

These are the disagreements. **Do not resolve them from this file.**

## L1. Whether to drop the blowup

- **`docs/VERDICTS.md` §1b**: *"fix the `p3-fri` bug, repair our own gate,
  **drop the blowup at BabyBear**."* §7.0 then records it as *"priced, not
  landed."*
- **`forcodex/06-OPEN.md`**: *"⚠ **my read is NO.** `lb=6` is the **minimum of
  an iso-security grid** by 1.5–3×, and dropping it is **×3.21 worse per turn**
  once the wrap is counted."*
- **They disagree on the recommendation, not on the facts.** The reversal comes
  from counting the tower, which §1b did not.

## L2. "Net ≈65× worse per turn" — VERDICTS is the stale side

- **`docs/VERDICTS.md:472`** says ≈65×.
- **Three later sources say ×3.21 (independent grid: ×2.96)**: *"My 'net ≈65×
  worse per turn' was WRONG. **65× is the ratio of loss to saving; the per-turn
  total is ×3.21.** It had already propagated into a note's summary."* And
  `notes/recursion-tower-profile.md`: *"⚠ **READ THAT LAST LINE PRECISELY — it
  has been misquoted twice.**"*
- ⚑ **VERDICTS was not updated. The rule that "this file wins" is backwards
  here.**

## L3. Sumcheck-batching the reduced opening

- **`forcodex/06-OPEN.md`**: *"the biggest measured available win …
  **×2.05 per turn.** (A lane is on it.)"*
- **`notes/sumcheck-batched-opening.md`** (2026-08-16, that lane's own output):
  > ⚑⚑ *"Batching the reduced opening with a sumcheck requires an
  > **evaluation-binding commitment on the opened values.** Two-adic FRI gives
  > **univariate openings only.** So lever 3(b), as stated, is **not a
  > prover-side rearrangement — it is a PCS replacement**, and its cost is a new
  > commitment scheme, not a backend rewrite."*
  > The ×2.13 is *"derived against an assumption that the sumcheck's terminal
  > claim is free, and it is not free."*
- **The open-items file has not caught up with the lane it dispatched.**
  ⚠ And that note is **untracked on disk** (`07-ARTIFACTS.md` O4).

✅ **`[08-17]` CLOSED — and both halves of the disagreement resolved, in
opposite directions.** The note won: the sumcheck route is a **PCS
replacement** (§E9 now carries the full argument, and `06-OPEN.md` no longer
lists it). But the *number* was then reached by a road neither side had
considered — **packing, at ×2.011 measured** — so the open-items file's
instinct that ×2.13-shaped value was sitting there was **right for the wrong
reason.** ⚠ **The note is now committed** (`b458936`…`0232918`); the
untracked-on-disk warning is stale.
⚑ *This is the most useful shape in the file: a disagreement where **both**
sides held a true half, and resolving it required a third measurement neither
had proposed.*

## L4. "lb=6 is 2.9× off the optimum" — VERDICTS is right here

`notes/what-remains.md:46` still lists it as a standing measurement; VERDICTS
§2 refuted it as a grind draw. **VERDICTS is later and correct; the note was
never patched.**

## L5. The 13.13× blowup speedup — VERDICTS contradicts itself within one section

§1b quotes *"13.13× faster at 4096 rows"* and, four lines later, *"⚠ that is
wall clock on a contended box — the same case re-measured today reads
**7.78×**. **Use the counts.**"* Better still: **the ÷15.19 permutation count.**

## L6. BinarySpartan's existence

`notes/binaryspartan-position.md` and `notes/neo-superneo-read.md` say it could
not be verified to exist. **`docs/BINARY-POSITION.md` says it EXISTS** — ember
holds its title page and abstract from the eprint *review queue*.
**`docs/VERDICTS.md` is silent, so there is no tiebreak.**

The benchmark scrutiny that stands either way: the EF harness runs on an
**M1/8-core, not an M4 Max**; *"'Vega' is P-256 + Hyrax — **discrete-log, NOT
post-quantum**"*; and **Flock reports 82k BLAKE3/s on a SINGLE M4 Max core
against BinarySpartan's 410k on twelve — 2.2–2.4× faster per core, >660k on
ten cores, i.e. it wins outright in aggregate.**

✅⚠ **`[08-17]` RESOLVED — the paper went public (eprint 2026/1656, Setty) and
was read at source. It exists. And it refuted OUR SCRUTINY, not the other way
round.** Taking the "stands either way" paragraph above line by line:

| our claim | verdict at source |
|---|---|
| *"Vega 44.2 is `spartan2` at 541.72 ms"* | ⚑ **REFUTED.** It is the real **Vega_MC, measured 44.23 ms** at 2 KiB. **The mis-identification was ours, and it was the load-bearing step in the "the table is mislabelled" argument.** |
| *"the harness runs on an M1/8-core"* | ⚑ **DISSOLVED.** All rows are **same-machine M4 Max** through Flock's pinned harness (`8790722`), **best-of-five, disclosed.** *"Our M1 data points are obsolete for this comparison."* |
| *"Vega is P-256 + Hyrax, not post-quantum"* | ✅ **STANDS**, and is independently re-confirmed at §4.3/§7 by the Nebula/Vega read. ⚠ **Narrowed**: it applies to the SLIDE's framing; the paper never claims Vega is PQ. |
| *"Flock wins in aggregate"* | ✅ **CONCEDED AND MEASURED BY THE PAPER ITSELF — 1.96× / 1.76× / 1.78× in its own Table 1.** |

> ⚑⚑ ***"Our scrutiny was scrutiny of the SLIDE. The paper is cleaner than the
> slide."*** That is the transferable lesson, and it belongs beside the
> `[ABSENCE]` rule at the top of this file: **reading a preprint through its
> conference deck manufactures errors that look exactly like findings.** Both
> failures here — the mis-identified row and the wrong machine — came from the
> deck, and both survived two lanes.

**What survives as residual criticism** (real, but not the slide's class of
error): peak-of-sweep + best-of-five is favourable-point reporting, disclosed;
the gzip proof-size comparison is a proxy; and the "additive optimizations"
claim **elides the JBR-vs-UDR regime difference — which is not an optimization
one applies but a soundness-accounting choice.**

⚑ **And the read found nothing that refutes us** — six specific contradictions
were checked for, all negative. Two things it *corroborated* independently:
Ligerito's corrected RS base (a printed-base bound would have credited ~2^−200
rather than the paper's stated **2^−102.6**), and our **2²⁸ headroom** figure
for §6.4's dropped `1/|F|` terms — **which is the paper's own stated validity
ceiling, arrived at from the other side.** ⚑ *"The paper is, unknowingly, the
second witness to both."*

⚠ **One owed lemma DISSOLVED**: BinarySpartan's reference [10] is
**eprint 2024/1210** (decomposed eq tables, protocol-neutral), **not 2024/1038**
(constraint packing) — so the GF(2)-linear-independence lemma we thought we
owed is **not owed**, and BinarySpartan is not evidence about it either way.

⚠ **Structural facts about the paper, worth carrying**: **zero theorem
environments** anywhere (the entire security argument is one paragraph), **no
artifact and no repository URL** — while its own reference list links repos for
Binius64, Plonky3, Hashcaster and Flock — and **the words "Fiat–Shamir",
"transcript" and "challenge derivation" do not occur in it.** ⚑ Which means it
is **silent at every layer on ring-switching's ordered basis** — the exact gap
we closed on 08-16 (`docs/BINARY-POSITION.md`), and with no artifact **nobody
can check which situation it is in.**

## L7. "The multilinear/GKR substrate is absent everywhere"

`notes/archive/convergence-2026-08-13.md` headlines it as absent;
`notes/grey-lit-corrections.md` corrects it: *"**FALSE**, and this was the
headline of yesterday's convergence note. Our measurement (zero `gkr` in
Plonky3-at-our-pin) was right; **the generalization was wrong.** Correct
statement: **absent from Plonky3, shipped by six systems.**"* VERDICTS is
silent.

## L8. The secret distribution — affects every noise and security number

Deployed is **CBD(20)** (support ±20, variance 10, σ=√10), pinned in three
source locations. *"Earlier notes recorded it as 'ternary' AND as 'CBD(10)';
**both were misreadings.**"* ⚠ **`notes/fhe-core-theory.md` still carries stale
derived figures** (the ~4.3-bit B_key gap, MATZOV ≈ 122), flagged as superseded
pending a re-run. `docs/VERDICTS.md` carries the corrected label.

## L9. `[08-17]` Weft — killed as specified, contested as a question

The one entry in this file whose **own author is re-opening it.** §D7 has the
number and the epitaph; the contest is over what the number *means*:

- **The kill lane**: branch 6 against MDS 25 and Poseidon2's own 8, plus a
  4-deep invariant subspace flag. *Killed as specified.*
- **Weft-2** (`06-OPEN.md` §5, `08-ATTACK-BRIEFS.md` BRIEF 2): **branch 6 may
  not be disqualifying** — our own differential accounting says branch 6 + `x⁻¹`
  **clears 128 bits in two rounds** — and a **free lane rotation** breaks the
  suffix-shaped flag, with `novelPack` confined to internal rounds and a dense
  external layer (Poseidon2's own architecture).
- ⚑ **The honest statement of where it sits**: *"We verified the rotation kills
  THAT flag; killing one flag is not the absence of flags."* The structure is
  **tower-triangular by construction**, so a second flag is the **expected**
  finding, not a surprise. **And the linear/correlation side was never run.**

**Do not resolve this from this file.** The open question is a **new
subspace-trail search on `r ∘ novelPack`**.

## L10. `[08-17]` Two sibling notes that disagree and nobody reconciled

`notes/aligned-hash-space.md` §0.3 / §5 / §7.2 still asserts `R ≈ 3.2×` for
lookup-Blake2s as *"the one route that crosses `R*`"* and calls the lookup
measurement **"the highest-value open measurement."** `notes/lasso-over-logup.md`
§2.4 **refutes exactly that figure** (§D5 here) and §6.1 asks for the pointer to
be marked RESOLVED.

**Both were written the same night. Neither was edited.** Listed here because
the shape — *a lane answering a sibling's open question, with no third pass to
close the loop* — is how a refuted number stays quotable, and this file exists
to stop exactly that.

---

# M. The meta-result

`docs/VERDICTS.md` §8 states it as a table, and it is the most valuable thing in
this file:

> **Every measurement lane found that the thing we were optimizing was not the
> cost, and the actual cost was somewhere nobody had looked. Six for six.**

| we believed | measured |
|---|---|
| the sumcheck is the prover | **2–17% of it** |
| matmul's cost is the sumcheck | **5%** — the lever is the partial evaluation |
| virtualize Poseidon2 with a sumcheck | **the sumcheck loses**; in-AIR narrowing wins |
| the exchange rate is 78–308× | **~5× in wall clock** — the unit was never converted |
| the blowup floor is mathematics | **a one-line upstream bug we froze as a law** |
| the rank-1 check removes the n² cost | removes the n² **proof**; the **commitment** becomes the step |
| grinding is a small tax | 25% of prove, 46% of proven soundness, and our own hardening commit un-parallelised it |

> **And the *shape* of the error is consistent: a plausible cost model, never
> converted into the unit that bills.** Counted multiplications instead of
> nanoseconds. Asymptotics instead of constants at our sizes. A ratio for a
> relation quoted as a ratio for a system. A distribution's tail read as a mean.
>
> **The rule that falls out: before optimizing a term, measure its share.**
> Every lane that measured first found the target somewhere else; every estimate
> carried without a measurement was wrong **in the same direction — flattering
> the thing we had already decided to work on.**

And the campaign's own verdict on how it chose what to work on:

> **An agenda organized around "what is unclaimed" produces refutations. An
> agenda organized around "what would the best system do" produces artifacts.**
>
> *"Essentially every entry in that ledger was refuted — MoE router binding,
> proof-aware QAT, the MX exponent measurement, the registry-as-open-position,
> the vacuity instruments, the boundary principle, `fold_add`-as-one-opening,
> the prime family. **Not one of those survived as 'first.'**"*

---

# N. What I could not source

Named here so the gap is visible rather than absent.

1. **`q_fat = 0.004·N^2.484`** and **"11 NTRU parameter sets across 6 papers"** —
   zero hits tree-wide. Only *"2^1 to 2^73 over"* survives in a note.
2. **"~125.1 bits, about 3 short"** and **"log q = 109 is 3 bits over the current
   recommended maximum of 106"** — transcript only (lane `a0cbd2ee`), **in no
   file.** Nearest recorded: deployed 98.1 core-SVP / 119.9 MATZOV / 130.5
   HE-standard — *a ~32-bit spread that is the **model**, not the parameters.*
3. **ZIP's 37 hours** — transcript only (lane `a4e77a94`), in no file.
4. **Celer's eprint number (2026/1453)** — appears nowhere in the repo.
5. **A standalone argument that amortized/batched bootstrapping does not
   apply** — does not exist separately from the depth-crossover sentence.

### `[08-17]` Added

6. **`κ = 24` for the dual-mode MSIS commitment** is a **root-Hermite sketch,
   not a lattice-estimator run** — and this repo has already recorded the
   lattice field's "128-bit" labels re-deriving to **~98-bit core-SVP.** The
   estimator run is obligation **O6, un-run**, and §D3/§K's pricing inherits it.
7. **"~250 constraints per hash"**, the constant that converts our 38,168 perms
   into the ≈9.5M constraint-equivalents behind the *~10³ DL dividend* — it is
   **Nebula's**, taken from their text, and we never re-derived it in our own
   unit. The dividend's order of magnitude does not turn on it; the second digit
   does.
8. ⚑ **"Real keccak-f in R1CS ≈ 25–150K per permutation"**, the number that
   decides whether the EVM decompilation prize is ~60–140× or something much
   smaller — the note labels it *"recalled range, not measured."* With real
   keccak the decompiled circuit moves **≈3–4K → ≈80–450K**, so **whoever
   quotes §Pillar-7's prize is quoting the hash choice.**
9. **The Weft mixing layer's evaluation points and basis** (`βⱼ = 2^j`, first 24
   of the dim-5 enumeration) are **[ASSUMED-BY-THE-LANE]**, not read off a
   specification — with a 3-random-basis sensitivity arm that came back
   identical. The branch number is exact *for that instantiation*.
