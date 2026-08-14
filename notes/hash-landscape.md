# The hash landscape — why Poseidon2, and what it would take to leave

2026-08-14. **Basic research, charting a landscape — not choosing a winner.**
The deliverable is a map plus a composable Lean ingredient, and the ingredient
landed (`minidregg@bf0b311`, `Selvage/HashFamily.lean`).

---

## ⚑ THE HEADLINE, IN FOUR LINES

1. **The crossover is `R* = 2.0×–4.5×`**, computed from our own measurements
   (§2). Below that in-circuit ratio a traditional hash wins outright everywhere
   in the tower; above it, Poseidon2 wins. `R` = the candidate's in-circuit cost
   ÷ Poseidon2's.
2. **Measured `R` in a prime field, from our own pinned Plonky3: Blake3 = 30.6×,
   Keccak-f = 210.6×** (§1a). Against `R* = 2.0–4.5×` that is **6.8×–15.2× of
   margin for Blake3** and 47×–105× for Keccak. **Poseidon2 wins, and it is not
   close.**
3. ⚑⚑ **AND THE BINARY FIELD DOES NOT RESCUE IT — this refutes the thesis I
   started with.** The only same-system head-to-head (eprint 2025/1893) puts the
   algebraic advantage on the *verifier* axis at **12.7×–24.7× even in a binary
   field**. The binary field roughly halves `R`; **it does not cross R\*.**
   **What pins us to an algebraic hash is RECURSION, in BOTH characteristics.**
4. ⚑ **So the real lever is not the hash and not the field — it is WHICH LAYERS
   GET RECURSED OVER.** Where a layer's hash is re-executed as constraints, pay
   for Poseidon2. Where it is not, a traditional hash wins immediately.

**And that makes one thing actionable today, at zero cryptanalytic risk** (§4):
the **top layer of the tower is arithmetized by nobody**, so its native hash is a
free choice worth **1.5×–2.3×** at zero in-circuit cost — independently
corroborated at **1.69× ST / 1.26× MT** by the Binius paper's own Plonky3
measurement.

> ### ⚠ I set out to show the binary field dissolves the Poseidon2 justification. It does not. The measurement says the justification is recursion, and recursion survives the field change.

---

## 0. What we are actually paying for, and who decided

**Nobody here chose Poseidon2. Plonky3 handed it to us, and we are abandoning
Plonky3** (`docs/RESEARCH-STANCE.md`). The trade it embodies is a real one and
it has never been checked:

> **We pay 2.78× natively to buy in-circuit cheapness for recursion.**

Both halves of that sentence are measured, by us, and committed:

| half | measurement | source |
|---|---|---|
| native cost | Merkle commit of 2^15 × 135 BabyBear: Blake3 **36.3 ms (8.2 ns/elt)**, Keccak 50.1, **Poseidon2 100.9 ms (22.8 ns/elt)**, Rescue 1660 | `notes/fast-systems-recon.md` |
| it is the dominant term | hash-bound iff `Y > X`; `X ≤ 178` exact, measured `Y = 890` → **margin 5.0×–7.2×, no crossover in b ∈ {3..7}** | `notes/field-op-counts.md` §5 |
| in-circuit share | Poseidon2 is **36.45%** of a leaf wrap's committed cells, **53.98%** of apex/shrink | `notes/recursion-tower-profile.md` §3c |
| the mechanism | a wrap's biggest table **is** its child's verifier, row for row: **38,168 ≡ 38,168**, two independent instruments | `notes/recursion-tower-profile.md` §2 |

That last row is the whole reason the trade exists. **The leaf's native hash gets
re-executed as constraints inside its parent.** Cheap-natively/expensive-in-circuit
is not a wash — it is a choice about *which* of the two you pay, and the tower
makes you pay both.

---

## 1. ⚑ THE THREE-COLUMN MAP

The third column is the point: it is where "SNARK-friendly" stops being necessary.

> ⚠ **UNITS ARE THE MAIN WAY THIS TABLE GOES WRONG.** R1CS constraints, Plonkish
> gates and AIR cells (rows × columns) are different units and are not
> interchangeable. Every cell says which. Prime-field in-circuit numbers are also
> **not comparable across fields** — the same hash costs differently in BabyBear,
> Goldilocks and BN254, by up to 90× (§1c).

### 1a. ⚑ THE PRIME-FIELD COLUMN, MEASURED — not quoted

I replaced my first draft's literature-quoted range ("Keccak is 20k–50k R1CS")
with a **measurement from our own pinned Plonky3 (`rev 82cfad7`)**, because that
checkout ships an AIR for all three hashes and therefore prices them **in one
unit, in one field, at one arithmetization**. Widths are `size_of::<*Cols<u8>>()`
read out of the crates; rows per invocation read from each `generation.rs`.
Harness: `notes/hash-landscape-scripts/crossover.py`.

| hash | AIR | rows/invocation | main cols | **cells/invocation** | **R** |
|---|---|---:|---:|---:|---:|
| **Poseidon2-w16** | ours, deployed | 1 | **300** | **300** | **1.0×** |
| **Blake3** | `p3-blake3-air` | **1** (`num_rows = inputs.len()`) | 9,168 | **9,168** | **30.6×** |
| **Keccak-f** | `p3-keccak-air` | **24** (`NUM_ROUNDS`) | 2,633 | **63,192** | **210.6×** |

⚑ **Blake3 is 6.9× cheaper in-circuit than Keccak in a prime field.** "Traditional
hash" is not one number — Blake3's 32-bit ARX structure lands two 16-bit limbs per
word and **one row per compression**, where Keccak needs 24. Any analysis that
prices "a bitwise hash" from the Keccak figure over-charges Blake3 by ~7×.

**The invocation ratio is 1:1 where it matters.** At a 256-bit digest a 2-to-1
Merkle node is *one* Poseidon2-w16 permutation **or** *one* Blake3 compression, so
the cell ratio **is** `R` for the recursion column — which is Merkle-path
dominated. Bulk *absorption* credits Blake3 2× (64 B/compression against a rate-8
sponge's ~31 B), so an absorb-heavy workload sees `R/2`.

### 1b. The other in-circuit numbers we hold

| hash | field | unit | cost | source |
|---|---|---|---|---|
| **Poseidon2-w16** | BabyBear | **AIR cells/perm** | **300 main + 24 prep = 324** | `recursion-tower-profile.md` §3a |
| Poseidon2-w16 | BabyBear | AIR cols/perm | **298** | `hash-verdict.md` §5 |
| Poseidon2-w16 | **KoalaBear** | AIR cols/perm | **164** (α=3 evaluates inline; α=7 forces a committed intermediate) | `hash-verdict.md` §5 |
| Monolith-31 | KoalaBear | AIR cols/perm | **3,520** (≈900 granting LogUp) | `hash-verdict.md` §4 |
| Poseidon2-w16 | **BabyBear emulated in BN254** | **R1CS/perm** | **16,837** | `breadstuffs/docs/deos/WRAP-NATIVE-HASH-DECISION.md` |
| Poseidon2-w24 | BabyBear emulated in BN254 | R1CS/perm | **27,213** | same |
| Poseidon2 | **BN254 native** | R1CS/perm | **187** | same (gnark std) |

### 1c. ⚑ The 90× in that table is a FIELD-MATCH effect, not a hash effect

**16,837 → 187 R1CS for the same hash.** Nothing about Poseidon2 changed; only
whether its field matched the proof system's. That is the single largest ratio
anywhere in this document, and it is the map's central lesson in miniature:
**hash choice is a second-order term on top of field match.**

### 1d. ⚑⚑ THE BINARY-FIELD COLUMN — and the refutation of my own thesis

**I started this lane believing the binary field dissolves the argument. The best
available measurement says it does not, and the correction is the most valuable
thing here.**

The decisive source is **eprint 2025/1893** (*Poseidon(2)b*, Grassi–**Khovratovich
(EF)**–Koschatko–Rechberger–Schofnegger–Schröppel–Wu, peer-reviewed in CiC),
Table 4. It is the **only same-system, same-machine, same-arithmetization
head-to-head of algebraic vs standard hashes in a binary field that exists**:
Binius v0, AMD Ryzen 9 7900X 12-core, normalized to **seconds per ~1 MB hashed**,
so the columns are directly comparable.

| permutation | kind | prove MT (s/MB) | **verify (ms)** | `R_proxy` |
|---|---|---:|---:|---:|
| Grøstl-P | **standard** | **0.170** | 114.97 | **31.8×** |
| Keccak-f | **standard** | 0.425 | 45.70 | **12.7×** |
| Vision-32b | algebraic | 0.605 | 10.12 | 2.8× |
| Anemoi | algebraic | 0.499 | 12.28 | 3.4× |
| Poseidon-bπ (n=32) | algebraic | 0.150–0.129 | 4.66 | 1.3× |
| Poseidon-bπ (n=64) | algebraic | 0.143 | **3.61** | 1.0× |

**Two findings, and they point in opposite directions.**

1. ✅ **On PROVING, the thesis is right and then some.** Grøstl — a SHA-3 finalist,
   not a SNARK hash — **out-proves Vision Mark-32 by 3.56×**, a hash *designed* for
   binary towers, and beats Keccak by 1.42×. The algebraic proving advantage in a
   binary field is **~1.3×, not the 30–500× it is in a prime field.** That collapse
   is real and it is the strongest datum for the whole binary-field programme.
2. ⚑⚑ **On VERIFICATION it does NOT converge — it stays 12.7×–24.7× apart.** And
   **recursion cost *is* verifier-circuit cost.** So the quantity my crossover
   calls `R` sits at ~12.7–24.7× in a binary field against ~30.6× in a prime field:
   **the binary field roughly halves `R`. It does not cross `R* = 2.0–4.5×`.**

> ### ⚑ **THE THESIS IS HALF RIGHT, AND THE HALF THAT SURVIVES IS THE PROVING HALF.** In a binary field a traditional hash becomes competitive to **prove**. It does **not** become competitive to **verify inside another proof**. Poseidon-bπ wins *both* axes at once, which is the cleanest available refutation of "SNARK-friendly hashes become unnecessary."

⚠ **Stated inadequacy of `R_proxy`:** verify *time* is a proxy for in-circuit cost,
not the same quantity — it carries proof-size-dependent terms a recursive verifier
pays differently. It is the honest available proxy, both sides from one table, and
it agrees in sign and rough size with the prime-field cell measurement in §1a.
**Treat 12.7–24.7× as a shape, not a calibration.**

### The throughput comparison, kept but demoted

| system | hash | field | rate | source |
|---|---|---|---|---|
| **ours (derived)** | **Poseidon2** | BabyBear prime | **~17,700 perms proven/sec** | `docs/RESEARCH-STANCE.md` |
| Flock | **BLAKE3** | binary | **82k/sec**, 1 M4 Max core; >660k on ten | arXiv 2607.27491 / eprint 2026/1329 |
| Flock | SHA-256 | binary | 42k/sec, 1 core | same |
| Flock | Keccak | binary | 30.7k/sec, 1 core | same |
| BinarySpartan | BLAKE3 | binary | 410k/sec on 12 P-cores = **34.2k/core** | EF slide; scrutiny in `notes/binaryspartan-position.md` |

⚠ **I previously read this table as showing `R` inverts. It does not — it is a
different quantity.** It shows that *end-to-end proving throughput* of a standard
hash in a binary field beats ours in a prime field, which is finding 1 above, not
finding 2. **Conflating proving throughput with in-circuit ratio was my error and
the 2025/1893 table is what caught it.** Different systems, different hardware,
different workloads: a **shape-and-sign** claim only.

⚑ **Flock states the thesis better than the tweet does**, and its reasoning is
worth quoting because it is an argument about *coupling*, not speed:

> *"a SNARK-friendly hash is cheap to prove only inside a proof system built over
> the single field it was designed for: it **enshrines that field**… it forces the
> application designer into a false choice."*

That is the real cost of Poseidon2 and it is not on any of my cost tables: **it
welds the hash to the field**, so a field migration and a hash migration stop being
independent moves. Our `HashFamily` (§5) is precisely the de-welding.

### 1e. The rest of the space

⏳ *The prime-field and binary-field literature sweeps for Poseidon1, Rescue-Prime,
Vision, Griffin, Anemoi, Monolith, Skyscraper, Reinforced Concrete, Tip5, and the
in-circuit cost of Blake3/SHA-256/Keccak in a prime field are in flight and will
be folded in here.* What is already settled from our own prior work:

- **Poseidon3 does not exist.** The family branches by FIELD, not version:
  Poseidon2b (binary, for Binius), Skyscraper-v2 (big primes). Expecting a
  version number is the wrong mental model. (`hash-verdict.md` §1)
- **The lookup fork is closed, not deferred**: no 31-bit-prime Monolith exists
  anywhere. Plonky3's Monolith AIR rejects KoalaBear **by name in a source
  comment**, and BabyBear breaks the Bars bijection. (`hash-verdict.md` §4)

---

## 2. ⚑⚑ THE CROSSOVER, COMPUTED FROM OUR OWN NUMBERS

Nobody has written this down, and we have both sides measured. Script:
`notes/hash-landscape-scripts/crossover.py` (every input cited to a committed note).

### The model

Let `ρ_nat = 2.78` (Poseidon2/Blake3 native), `f_nat` = native-hash share of a
leaf prove, `f_circ` = in-circuit-hash share of a wrap's committed cells, and
**`R` = the candidate hash's in-circuit cost ÷ Poseidon2's**, same workload.

Swapping Poseidon2 → Blake3 multiplies

- a **leaf** prove by `m_leaf = (1 − f_nat) + f_nat/ρ_nat`
- a **wrap's cells** by `c = (1 − f_circ) + f_circ·R`
- and a **wrap's time** by `m_wrap = c · m_leaf`

⚑ **That last line is the structural insight and it is why this is genuinely
two-sided.** A wrap is itself a STARK. Its committed trace is 36.45% the
in-circuit hash table, and it *natively hashes that trace* — with the same hash.
So growing the in-circuit table also grows the native hashing, **and the native
hashing just got 2.78× cheaper.** The two effects multiply rather than trading off
independently. Net win iff `c · m_leaf < 1`:

> ### **R\* = ( 1/m_leaf − 1 + f_circ ) / f_circ**

### The answer

| estimator | `f_nat` | leaf speedup | **R\*** (leaf wrap) | **R\*** (apex) |
|---|---:|---:|---:|---:|
| work model, b=6 | 0.8745 | 2.27× | **4.49×** | **3.36×** |
| work model, b=3 | 0.8336 | 2.14× | **4.14×** | **3.12×** |
| clock model, b=6 pow=0 | 0.6297 | 1.68× | **2.85×** | **2.25×** |
| clock model, b=3 post-LDE-fix | 0.5504 | 1.54× | **2.49×** | **2.01×** |

> ## ⚑ **R\* = 2.0× – 4.5× across every estimator and every layer.**
> **A traditional hash wins outright, everywhere in the tower, if its in-circuit
> cost is under ~2–4.5× Poseidon2's. Above that, Poseidon2 wins.**

### Why two estimators, and why I report the band rather than a number

The work model (`Y/(Y+X)`, op counts × the measured conversion rate) says
**83–87% hash**; the clock model (measured per-phase ms) says **55–63%**. They
disagree because `field-op-counts.md` §6 measured *why*: the permutation count
explains **80%** of the hash phase's time but only **25%** of LDE-commit's and
**0.6%** of quotient-eval's. **The LDE's milliseconds are mostly movement, not
arithmetic** — so a work model under-charges it and a clock model over-charges it.
Averaging them would be the sin `COST-MODEL.md` rule 5 names. The band is the
honest object, and **the verdict below does not depend on which end is right.**

### ⚑ WHERE REALITY SITS, AGAINST R\* — in both characteristics

`R` measured (§1a for prime, §1d for binary), against `R* = 2.0–4.5×`:

| candidate | field | **`R`** | margin above `R*` | verdict |
|---|---|---:|---|---|
| **Blake3** | BabyBear prime | **30.6×** | **6.8× – 15.2×** | Poseidon2 wins |
| Keccak-f | BabyBear prime | 210.6× | 47× – 105× | Poseidon2 wins, hugely |
| Keccak-f | binary (verify proxy) | **12.7×** | **2.8× – 6.3×** | Poseidon-b wins |
| Grøstl-P | binary (verify proxy) | **24.7×** | **5.5× – 12.3×** | Poseidon-b wins |

> ### **The verdict is not close in EITHER characteristic, and that is the finding.**
> A prime field puts Blake3 **6.8–15.2×** above the crossover. A binary field cuts
> that to **2.8–6.3×** — a real, roughly 2× improvement — **and still does not
> cross.** The trade Plonky3 handed us is *correct*, and it stays correct when the
> field changes.

⚑ **What that isolates is the actual cause.** Every term in `R*` except `f_circ`
is about *native* cost, and the field change fixes native cost handsomely. `R`
stays high because `R` is about **re-executing a hash as constraints**, and that
is a property of **recursion**, not of the field. So:

> ### **RECURSION is the thing that pins us to an algebraic hash. Not the prime field, and not inertia.**

⚠ **And say the unflattering halves out loud, both of them.** First: the 2.78× we
pay natively is *cheap* for what it buys, so **our own map vindicates the choice we
inherited** — not the answer the question was hoping for. Second: **I set out with
a thesis and the measurement refuted it.** The binary-field programme remains
valuable for the reasons §1d's finding 1 gives, but *"it dissolves the Poseidon2
justification"* is not one of them, and I had written that sentence before I
measured it.

### ⚑ The staircase — why small `R` is exactly free

In-circuit tables are padded to powers of two. The leaf wrap's Poseidon2 table is
**38,168 rows padded to 2^16**, i.e. **1.717× of headroom in rows**; apex is
22,626 → 2^15, **1.448×**. So an in-circuit cost increase up to ~1.4–1.7× (if it
lands in rows) costs **literally nothing**, and then jumps 2× at once. **R\* is a
staircase, not a line**, and the first step is free.

### Named inadequacies of this crossover

- Wrap arithmetic is taken **proportional to cells**; the DFT is `cells·log h`, so
  R\* is mildly optimistic for the swap at large `R`. Low-resolution **by intent**.
- `ρ_nat = 2.78` is a contended-box clock ratio. It is a ratio of **two hash
  workloads** — the pair least corrupted by contention, and both sides equally so.
- The model prices **prover work**. Verification is ~100% hashing
  (`fast-systems-recon.md`), so a native-hash swap helps the *verifier* strictly
  more than this model shows. Not counted; points the same way.
- `R` is treated as one number. A real hash has different ratios for the Merkle
  compression and the sponge absorb (Blake3 absorbs 2× per invocation at our
  digest size). Folding those apart is the obvious refinement.

---

## 3. THE SECURITY DIMENSION, STATED HONESTLY

⏳ *The full cryptanalysis sweep is in flight.* What is already ours and checked:

- **Poseidon2 at our parameters carries a +286-bit margin.** The 2026/306
  round-skipping attack was audited to **no action needed**: our BabyBear
  t=16/t=24 instances cannot be reached even if every skippable round were free
  (`notes/poseidon2-audit-verdict.md`). ⚑ **The margin halves at α=3** — which is
  exactly the KoalaBear migration's S-box — so the 1.82× in-circuit win at
  KoalaBear is **partly bought with security margin**, and that trade is not
  visible in any cost table.
- ⚑ **A free fix that rides a flag day**: 2026/306 attacks Poseidon2's non-MDS
  internal linear layer and **our deployed shape is the attacked one**. The fix
  (transpose to `M̄_ε = M₄ ⊗ P_{t/4}`) is free, same fast matmul, and **not
  shipped in any Plonky3**. It does not justify a flag day; it should ride one.
- ⚑ **Poseidon was NOT broken, and the EF pivot is not an institutional artifact.**
  Source located and verified: **Justin Drake, X, `x.com/drakefjustin/status/2087905684180418733`,
  ~2026-08-12** — *"Goodbye, Poseidon! … The Ethereum Foundation is abandoning
  Poseidon for L1, pivoting to SHA or BLAKE"* and *"In hindsight the key was not
  SNARK-friendly hashes, but hash-friendly SNARKs."* Targets named are **SHA-2 and
  BLAKE2s** (notably *not* Keccak); timeline leanVM 2027, consensus/data/execution
  2028.
  ⚠ **This is one EF researcher on social media, amplified by trade press. There is
  no blog.ethereum.org post, no ethresear.ch post, and no institutional EF
  publication carrying it** — a targeted sweep found none. Cite it as *a senior EF
  researcher's public statement*, never as *"the EF published"*. "Reaches its dream
  conclusion" means Poseidon **survived**.
- ⚑ **The Initiative's own pivot is CONFIRMED at source, and it is Poseidon2 →
  Poseidon1.** Khovratovich's *State of the Art* deck, slide 6: *"Why We Moved from
  Poseidon2: Round Skipping Attack"* → **"Poseidon Initiative pivots to Poseidon1
  (KoalaBear, MDS matrix) for Bounty 2026."** >$1.5M committed, Phase 2 closing
  Dec 2026. **The brief's claim was right**, and it makes §3's MDS-transpose item
  the direction the bounty runners themselves took.
- ⚠ **And the erosion is real, not rhetorical.** The Poseidon1/KoalaBear zero-test
  record advanced **RP 6 → 12 in under three months** (2026-06-03 → 2026-07-27),
  and a **q=3 partial collision was claimed 2026-04-06** against the $992K prize.
  ⚑ **So the honest story of the pivot is that BOTH pressures arrived at once**:
  algebraic cryptanalysis eroding the margin *and* binary-field provers closing the
  performance gap. Reading it as purely performance-driven understates it.
- ⚠ **And leanVM today is KoalaBear — a 31-bit PRIME field**, not a binary-field
  system. The binary-field framing is aspirational relative to what is in the repo.
- **Oddity on the record**: the EF's $992K Poseidon Collision Prize and the
  Density problem are both **paused as of 2026-08-01, unexplained**, with the
  granted-teams list unpublished. An unexplained pause in a cryptanalysis bounty
  is either administrative or interesting and we should not assume which.

### ⚠ The framing that must not slip

**Do not treat "traditional hash" as automatically safer in a circuit context.**
SHA-256 and Blake3 have decades of *differential and linear* cryptanalysis; the
algebraic hashes have years. But the attack that matters for an arithmetized hash
is an **algebraic attack on the arithmetization** (Gröbner / CICO / FreeLunch /
interpolation), which is a **different literature** — and one where the
traditional hashes have had *less* attention, not more, because nobody arithmetized
them until recently. **The asymmetry runs both directions and the honest statement
names which literature each claim comes from.**

---

## 4. ⚑ THE ONE THING ACTIONABLE TODAY, AT ZERO CRYPTANALYTIC RISK

The crossover analysis assumes every layer's hash is re-verified in-circuit. **For
one layer that is false, by construction.**

> **A layer's native hash needs to be SNARK-friendly only if that layer gets
> WRAPPED. The top of the tower is wrapped by nobody.**

The apex proof's own Merkle commitment is re-executed by the light client
**natively**, never as constraints. Its in-circuit Poseidon2 (53.98% of its cells)
verifies its *child* and must stay. But its **own** native hash is a completely
free choice.

| | value |
|---|---|
| **win** | **1.54× – 2.27×** on the apex layer's own proving (the leaf-only row of §2) |
| **in-circuit cost** | **zero** — `R` does not appear; nothing arithmetizes it |
| **cryptanalytic risk** | **zero new** — Blake3 is already in our TCB (`docs/ASSURANCE.md` row 2: "BLAKE3 collision-resistance … out-of-circuit content/transcript hash") |
| **what it re-emits** | the apex VK and the light-client verify path. A rebuild. |

This is precisely the move RISC0 and SP1 already make in the other direction —
`WRAP-NATIVE-HASH-DECISION.md` documents inserting a shrink layer *whose hash
field is chosen to match its consumer*. **The same reasoning applied at the top of
the tower selects Blake3, and we have never applied it there.**

### ⚑ Independently corroborated, and by an unfriendly witness

The Binius paper (eprint 2023/1784, §5.4, Tables 5–6) benchmarks **Plonky3 against
itself with only the Merkle hash swapped** — same field, same protocol, **identical
4.010 MiB proof** — on 8,192 Keccak-f permutations:

| Plonky3 BabyBear, Merkle hash | prove ST | prove MT | verify |
|---|---:|---:|---:|
| Poseidon | 120 s | 17.4 s | 0.639 s |
| **Keccak-256** | **71.2 s** | **13.8 s** | **0.527 s** |

> ### **1.69× ST, 1.26× MT, in a PRIME field, from swapping only the Merkle hash.**

That is *"hash-friendly beats SNARK-friendly"* demonstrated inside Plonky3, by a
paper arguing for binary fields, in the field we are already in — **because
nothing in that benchmark is recursed.** It is the same effect §4 predicts, at the
same size (my derivation says 1.54–2.27×), from an entirely independent instrument.

> ⚠ **I have still not measured it on OUR apex, and I am not going to pretend
> otherwise.** The §4 figure is a derivation from committed shares plus a structural
> fact about who verifies the apex; the table above is someone else's workload. The
> measurement is cheap — swap the outer config's hash and time one apex — and it is
> the next thing to do.

---

## 5. THE LEAN INGREDIENT — landed

`minidregg@bf0b311`, `Selvage/HashFamily.lean`, 421 lines, builds green, `Selvage`
library green, import boundary green, **no `sorry`**.

### ⚑ The finding that changed the design: the interface already existed, twice

The brief asked me to build a `HashFamily`. **Building one would have been a
twin.** What is actually in the tree:

| existing | where | status |
|---|---|---|
| `HashSuite (Value Digest : Type*)` = `leaf` + `node` | `minidregg/Selvage/BinaryMerkle.lean:27` | **zero typeclass constraints** — already fully hash-agnostic |
| `sponge (P : Rate × Cap → Rate × Cap) (iv) (m)` | `minidregg/Selvage/SpongeIndiff.lean:192` | **`[AddCommGroup Rate]` and nothing else**; `P` is a function ARGUMENT |
| `Poseidon2Kernel` / `Blake3Kernel` carrier classes | `breadstuffs/metatheory/Dregg2/Crypto/PortalFloor.lean` | both exist already, as **siblings that do not talk** |
| `KeyedHashFamily` | `breadstuffs/…/Circuit/HashFloorHonesty.lean:164` | the keyed concrete-security game |
| a full **cSHAKE256 / Keccak-f[1600]** Merkle lane | `minidregg/Compiler/Tower256Cshake*.lean` | **a second, non-algebraic hash already driving a Merkle deployment lane** |

> ### **Answer to the brief's question: YES — the mode layer is already
> hash-agnostic, and only the permutation is pinned, at named instance sites where
> it belongs.** It is enforced structurally: `scripts/check-import-boundary.sh`
> forbids `Selvage/` from importing `Compiler/`, so the sponge *cannot* reach the
> deployed permutation and must take it as a parameter.

**What did NOT exist was the join, or a second instance.** With one instance,
"swapping the hash is an instantiation" is an untested claim about code nobody
ever swapped. So the module supplies the join, the two routes, and the swap.

### What it contains

- **`HashFamily Block Value Digest`** — `suite` (Merkle role) + `absorb`
  (transcript role). No field, no characteristic, no permutation, no typeclass.
- ⚑ **`positionBinding_of_family`** — the proof system's binding requirement
  follows from `MerkleObligation` **alone**, never from how the family was built.
  **That term is the swap claim.** `poseidon2_positionBinding` applies it to the
  **deployed** Poseidon2 (`BaseFoldPoseidon2.hashSuite` joined to the existing
  generic sponge at `BaseFoldPoseidon2Rom.permutePair` — no new Poseidon2 anything).
- **Two routes**: `ofSponge` (permutation-based — Poseidon2 and Keccak arrive this
  way, `[AddCommGroup Rate]` only) and `ofChain` (compression-based — Blake3 and
  SHA-256 arrive this way, **no algebraic structure at all**).
- **Instances across two characteristics and two modes**: the deployed Poseidon2,
  a genuine char-2 XOR sponge, an `ℕ` chaining family, and a collapsing negative
  control.

### Teeth — all three legs of the floor law

| leg | theorem | note |
|---|---|---|
| **REFUTABLE** | `collapsing_not_merkleObligation` | **axiom-free** |
| **SATISFIABLE** | `natChain_merkleObligation` | real witness, `Nat.pair` injective |
| **NOT PROVABLE** | `nodeCollision_of_finite_digest` | ⚑ on a finite digest type a compressing node map **always** collides, by pigeonhole |

That third one says `MerkleObligation` is a cryptographic **assumption** and can
never be upgraded to a theorem for any real hash — every deployed digest type is
finite. It restates at this interface the pigeonhole the metatheory tree already
paid for **twice** (`HashFloorHonesty`'s deleted `CollisionResistant`,
`Compress2`'s deleted `compress1CR`, both refuted and removed for causing
vacuity). Selvage cannot import those, so it is stated here rather than cited.
And `charTwo_not_merkleObligation` fires it on **our own demonstrator** — no
instance in the file is claimed collision-resistant.

### ⚑ The char-2 result, read against `CharTwoWall`

`charTwo_family_nonempty` is deliberately the **opposite** result to
`CharTwoWall.foldingData_charTwo_False` one rung down. `FoldingData` is **EMPTY**
at characteristic two (so every theorem over it goes vacuously true there); a
`HashFamily` is **inhabited** there. Together they locate the binary-field wall
exactly:

> ### **The wall is in the FOLD, not in the HASH.** A hash swap and a field swap
> are independent moves, and only one of them hits a wall.

### Honest labels

- **`TranscriptObligation` is `[HASH-transcript-indiff]`: STATED, NOT PROVED**, for
  every instance. Carrying the field does not discharge it. The sponge route's own
  `SpongeIndiffGame` is **open upstream** (its docstring says so). **Nothing in
  this module narrows that gap** and nothing here should be read as if it did.
- `absorb` collision-freedom is **strictly weaker** than the indifferentiability
  Fiat–Shamir needs. It is a separate named obligation so the two are not confused.
- **Nothing reduces `permute`.** The family is `noncomputable` and no theorem
  evaluates it. One Poseidon2 permutation under kernel reduction was measured at
  **47.6 GB / 68 min**, so an interface needing `decide` through the permutation
  would be **unusable at the deployed hash, by measurement.**

### ⚠ What is NOT there, and exactly why

**A real BLAKE3 instance.** A complete, KAT-checked BLAKE3 exists in Lean at
`breadstuffs/metatheory/Dregg2/Crypto/Blake3Compute.lean` (`compress`, `roundFn`,
`permute`, `parentOutput`, `hash`, plus 35 official vectors in `Blake3Kat.lean`),
and **`HashSuite` carries no typeclass constraints at all**, so its `Array UInt32`
digests fit the interface **as-is, with no new mathematics**.

> ⚑ **The obstruction is a BUILD boundary, not a mathematical one.** BLAKE3 lives
> in the `Dregg2` tree of another repository, and the import-boundary check
> restricts `Selvage/` to Mathlib + Theory + Selvage. `ofChain` is exactly the
> shape BLAKE3 arrives by. **What is missing is the artifact reaching this side of
> the boundary — that is the next unit of work, and it is plumbing.**

Cheaper still: minidregg's **own** cSHAKE256/Keccak-f[1600]
(`Compiler/Sp800185Cshake256Core.lean`) is a genuine non-algebraic hash already in
this repo — but in `Compiler/`, behind the same boundary. **Two real traditional
hashes are one import-boundary decision away from being instances.**

---

## 6. WHAT THIS MAP SAYS TO DO

1. **Keep an algebraic hash wherever a layer is recursed over** — in a prime field
   *and* in a binary one. Not from inertia: `R` is 6.8–15.2× above the crossover in
   BabyBear and still 2.8–6.3× above it in a binary field, on our own numbers and
   the best same-system measurement that exists.
2. ⚑ **Take the free apex win** (§4): **1.5–2.3×** at zero in-circuit cost and zero
   new cryptanalytic surface, corroborated at 1.69× ST / 1.26× MT by an independent
   published measurement. One config swap and one timing. **Do this first.**
3. ⚑ **Then audit the whole tower for the same shape.** §4 is one instance of a
   general rule — *a layer's hash must be SNARK-friendly only if that layer is
   re-verified in-circuit* — and nobody has walked the tower asking that question
   layer by layer. Any layer whose hash is not arithmetized is a free 1.5–2.3×.
4. **Re-scope the binary-field programme onto what it actually buys.** It buys the
   **proving** collapse (§1d finding 1: Grøstl out-proves Vision by 3.56×, and the
   algebraic advantage falls from ~30× to ~1.3×) and the **de-welding** of hash
   from field that Flock names. **It does not buy an escape from Poseidon2 in the
   recursion layers** and should stop being sold that way — including by me.
5. **Land a second `HashFamily` instance from a real traditional hash.** The
   mathematics is done; the boundary plumbing is not. Until a second instance
   exists, "the swap is an instantiation" is a claim with one witness. **Two
   candidates are one import-boundary decision away** (§5).
6. **Ride the 2026/306 MDS transpose on the next flag day.** Free, and our
   deployed shape is the attacked one. ⚠ And note the EF's Poseidon Initiative
   moved **Poseidon2 → Poseidon1 (KoalaBear, MDS)** over exactly this attack — so
   this is not a cosmetic fix, it is the direction the people running the bounty
   went.
7. ⚠ **Watch the α=3 trade.** The KoalaBear migration's 1.82× in-circuit win is
   partly bought with security margin (§3). Price it as a security decision, not
   only a cost one.

---

## Provenance

Every number above is either (a) ours and committed, with the note named, or
(b) published, with the source named and the instrument stated. **No number in
§2 comes from the literature** — the crossover is computed entirely from our own
measurements, which is why it is the part of this document I would defend hardest.

⚠ **Corpus disclosure**: the literature sweeps feeding §1d and §3 run against
`~/paperbin` (1,218 PDFs, full text) and `~/dev/gh/forks/IACR-eprint-mirror/`
(IACR only, cryptology only, incomplete). **No absence claim in this document may
be quoted as measured on that basis** — the mirror cannot see arXiv, ITP/CPP, or
any grey literature, and that blindness has produced false absence claims here
before.
