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
5. ⚑⚑ **AND ONE LEVER DOES CROSS `R*`: the ARITHMETIZATION.** Same two primitives
   priced three ways — **102× in R1CS, ~31–56× in a bit-decomposed AIR, ~3.2× under
   a LOOKUP argument** (§2). **`R` is not a property of the hash. It is a property
   of how you arithmetize it**, and the lookup route lands *inside* the crossover
   band. **That is the honest answer to this note's title**, and it is a measurement
   we have not taken.

**Both halves of the trade are now measured by me on ONE pinned checkout** —
in-circuit **30.6×** in Poseidon2's favour (`p3-blake3-air` 9,168 cells vs 300), and
native **5.82×** against it (same AIR, same field, only the Merkle hash swapped:
40,195 ms vs 6,907 ms). **Neither side of this trade is folklore any more.**

**And that makes one thing actionable today, at zero cryptanalytic risk** (§4):
our **standalone proofs that a NATIVE Rust verifier consumes** — 18 such entry
points in `circuit-prove/src/` — pay the full 2.78× Poseidon2 premium and **receive
nothing for it**, because no circuit ever re-executes their hash. Worth
**1.5×–2.3×** each at zero in-circuit cost, independently corroborated at
**1.69× ST / 1.26× MT** by the Binius paper's own Plonky3 measurement.
⚠ *My first draft named the apex as the free layer; reading the code refuted that
(gnark consumes it, and it is already correctly `Poseidon2Bn254`). §4 carries the
retraction and the corrected class.*

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

The third column was supposed to be the point — the place where "SNARK-friendly"
stops being necessary. **It is where the claim gets tested and comes back half
true** (§1d): the *proving* advantage collapses there, the *verifier* advantage
does not, and a recursion tower is priced on the verifier.

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

Filled out across every hash and field in the pinned tree (two independent
derivations — my `size_of` readout and a lane's standalone `rustc` compile of the
`#[repr(C)]` structs — **agreed exactly on every overlapping cell**):

| hash | field / config | cols | degree | LDE blowup | **blowup-cells** |
|---|---|---:|---:|---:|---:|
| Poseidon2 t=16 | **KoalaBear α=3** | **164** | 3 | 4 | **656** |
| Poseidon2 t=16 | BabyBear α=7, REG=1 | 298 | 3 | 4 | 1,192 |
| Poseidon2 t=16 | BabyBear α=7, **REG=0** | **157** | **7** | **8** | **1,256** |
| Poseidon2 t=16 | Mersenne31 α=5, REG=0 | 158 | 5 | 8 | 1,264 |
| **SHA-256** | any 31-bit prime | **7,728** | 3 | 4 | 30,912 |
| **Blake3** | any 31-bit prime | **9,168** | 3 | 4 | 36,672 |
| **Keccak-f** | any 31-bit prime | **63,192** | 3 | 4 | 252,768 |

⚑ **Three findings in that table that a cells-only view hides.**

1. **Blake3 is 6.9× cheaper in-circuit than Keccak**, and **SHA-256 is cheaper
   still** (7,728 vs 9,168). "Traditional hash" is not one number — Blake3's 32-bit
   ARX lands two 16-bit limbs per word and **one row per compression**, where Keccak
   needs 24. Pricing "a bitwise hash" from the Keccak figure over-charges Blake3 ~7×.
2. ⚑ **The narrow degree-7 BabyBear AIR is WORSE than the wide degree-3 one once
   the LDE blowup is charged** — 157 cols at blowup 8 = **1,256** against 298 cols
   at blowup 4 = **1,192**. A width comparison inverts a cost comparison.
3. ⚑⚑ **KoalaBear α=3 beats every BabyBear configuration by 1.8–1.9×** on
   blowup-cells (656 vs 1,192–1,256), and **the S-box exponent is not a knob — the
   prime forces it.** `gcd(α, p−1) = 1` gives: **BabyBear ⇒ α=7 forced** (3 and 5
   both divide `p−1 = 15·2²⁷`), **KoalaBear ⇒ α=3** (`p−1 = 127·2²⁴`), M31 ⇒ α=5,
   Goldilocks ⇒ α=7, binary towers ⇒ α=7 forced. ⚠ **So "α=3 vs α=7" is a FIELD
   choice, not a parameter choice**, and "switch BabyBear to α=3" is not an option
   that exists.

#### ⚑ Cross-checked by a second, independent instrument

Grey-lit ("beam call #2" notes, `hackmd.io/@tcoratger/B16moU0q1x`, surfaced via
`~/paperbin/grey-ethresearch-ragged-gkr-poseidon2b.txt`) reports **in-circuit
proving throughput** for the same three hashes in a prime field: Plonky3 Poseidon2
(t=16, KoalaBear) at **1.75–2M perms/s**, **Blake3 at 30k/s**, **Keccak-256 at
4k/s**. As ratios: **Blake3 ≈ 58–67×, Keccak ≈ 440–500×.**

| hash | my measured **cells** ratio | their measured **throughput** ratio |
|---|---:|---:|
| Blake3 | **30.6×** | 58–67× |
| Keccak-f | **210.6×** | 440–500× |

**Two instruments, different quantities (committed cells vs prover throughput),
different fields (BabyBear vs KoalaBear), agreeing on the ordering and within ~2×
on magnitude.** Throughput running ~2× above the cell ratio is the expected sign —
a wider table costs more than its cell count through per-row and per-column
constants, which is the same effect `field-op-counts.md` Finding 3 measured on the
width-4 quotient chunks. **I use the cell ratio because it is ours and exact; the
throughput ratio says the cell ratio is, if anything, generous to the swap.**

#### ⚑ And the cell ratio is BRACKETED by wall clock, on these exact AIRs

`bench-hash-in-snark` (Han Ju; i9-13900K, 24 threads, Plonky3, rate ½, 256 queries)
benchmarks **`p3-blake3-air`, `p3-keccak-air` and `p3-poseidon2-air` at KoalaBear
t=16 α=3** — i.e. the exact 9,168-col and 164-col AIRs above:

| trace height | Poseidon2 | Blake3 | **P2 : Blake3** |
|---|---:|---:|---:|
| 2¹² | 578 K perms/s | 28.9 K/s | **20.0×** |
| 2¹⁴ | 1.47 M/s | 21.7 K/s | 67.8× |
| 2¹⁶ | 1.84 M/s | 15.8 K/s | 116× |
| 2¹⁹ | 1.71 M/s | 12.9 K/s | **133×** |
| 2²⁰ | 1.60 M/s | **OOM** | — |

**The wall-clock ratio brackets the 55.9× KoalaBear cell ratio from both sides and
crosses it at ~2¹³–2¹⁴.** Below that, the fixed 256-query FRI cost swamps a small
trace and Poseidon2 looks *worse* than cells predict; above it, Blake3's 9,168
columns go bandwidth-bound and Poseidon2 looks *better*. ⚑ **And there is a memory
wall, not only a time one: peak RSS at 2¹⁹ is 0.713 GB vs 36.21 GB — 50.8× — and
Blake3 OOMs at 2²⁰ where Poseidon2 is comfortable.** That is a hard operational
constraint no cost table shows.

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
- ⚑ **The AO-hash line is still live and still winning in prime fields.** Ashlar
  (ethresear.ch, 2026-08-06) reports **191 measured R1CS** against Poseidon 243 /
  Poseidon2 240, and 14,232 EVM gas against Poseidon's 18,229. ⚠ These are
  large-prime, small-width (t=3-ish) numbers and are **not** comparable to the
  BabyBear AIR cells in §1a — but the *direction* matters: people are still
  finding room **below** Poseidon2 in a prime field, which is the opposite of the
  "algebraic hashes are over" reading.

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

### ⚑⚑ THE ONE ROUTE THAT ACTUALLY CROSSES R\* — and it is not a hash and not a field

Every `R` above is for a **bit-decomposed** arithmetization: each XOR and each
modular-add carry becomes booleanity-constrained field elements. That is *why*
Blake3 costs 9,168 cells. **Under a LOOKUP argument it does not.**

Reinforced Concrete (eprint 2021/1038) Table 1, same paper, same unit —
**Plookup gates per invocation**:

| hash | Plookup gates | ratio |
|---|---:|---:|
| Poseidon | **633** | 1.0× |
| Blake2s | **2,000** | **3.16×** |

> ## ⚑⚑ **`R ≈ 3.2×` under a lookup argument — INSIDE the crossover band `R* = 2.0×–4.5×`.**

**Same two primitives. 27× swing from the arithmetization alone** (102× in R1CS,
~31–56× in a bit-decomposed AIR, ~3× in Plookup). ⚑ **The quantity this whole
document turns on is not a property of the hash. It is a property of how you
arithmetize it.**

**So the honest answer to this note's title — *what would it take to leave?* — is:
not a different hash, and not a different field. A lookup-based arithmetization of
the traditional hash.** That is the only lever measured anywhere on this page that
moves `R` across `R*` rather than merely shrinking it.

⚠ **Caveats, and they are real.** (a) Blake2s, not Blake3 — close relatives,
not the same function. (b) Plookup gates are **not** AIR cells; the 633 for Poseidon
is not our 300, and I have **not** reconciled the units. (c) A lookup argument has
its own committed cost (the table, the multiplicity columns, the LogUp sumcheck)
which this ratio may or may not carry. **This is a POINTER, not a result** — but it
is a pointer at the one place the crossover is reachable, and **we already hold
LogUp machinery** (`hash-verdict.md` §4 prices Monolith "granting LogUp").

⚑ **The measurement that would settle it is small and specific**: price a
lookup-based Blake3 AIR in *our* unit — blowup-cells, including the lookup table
and multiplicity columns — against Poseidon2's 1,192. If it lands under ~4,000, the
crossover is reached and this entire verdict flips. **That is the highest-value
open measurement on this page**, and nothing else here comes close to it.

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

### ⚠ FIRST — a refutation I nearly published, and why it was wrong

A literature sweep reported our **"+286-bit margin at α=7"** as **not found in any
paper** and offered replacement figures (+203 collision / +248 preimage at α=7,
+106.6 at α=3). I was about to record that as a correction. **Reading
`notes/poseidon2-audit-verdict.md` at source refutes the refutation**, and the
lesson is the recorded one: *read the blocker before you relay it.*

**Our number was never a published figure. It is OUR derivation, and the note says
so on its face:**

| instance | attack | cost | bar | margin |
|---|---|---|---|---|
| **BabyBear t=16, α=7, R_F=8, R_P=13, Merkle compress** | **2026/306 Lem 4.5** | **2^409.9** | **2^123.6** | **+286.3** |

`409.9 − 123.6 = 286.3` ✓. **The sweep searched for the literal string "286" in
papers — but the claim was never that a paper prints it.** And the two figures
differ for two identifiable reasons, neither of which is an error:

1. **Different bar.** Ours is **2^123.6** — the real 8-BabyBear-limb capacity bound
   — not the generic 128. That is 4.4 bits of the gap.
2. **Different parameter sets.** The sweep's α=7 figure is at **R_P=15** (the
   Poseidon2b *binary* set); ours is our deployed **R_P=13, t=16 Merkle compress**.
   Not comparable, and neither refutes the other.

⚑ **And on the α=3 side the two derivations AGREE TO THE DIGIT.** Independently:
the sweep gets **2^234.6** for α=3 collision; `poseidon2-audit-verdict.md` already
records **t=24 collision 2^234.6 (+110.9)** and **t=16 compression 2^253.6 (+130)**.
**Two instruments, same number.** The "halving at α=3" in the brief is confirmed by
both.

**What IS a real and useful correction from the sweep:**

- ⚑ **Neither Poseidon nor Poseidon2 ever states a security margin in bits, at any
  α.** The published margin is a round count, and it is explicitly arbitrary —
  2019/458 §3, verbatim: *"we **arbitrarily** decided to add: two more rounds with
  full S-Box layers (+2 R_F); 7.5% more rounds with partial S-Box layers."* **So any
  "+N bits" is somebody's derivation and must travel with its bar and parameter
  set** — ours does; not everyone's will.
- ⚠ **Poseidon2 §7.3 misstates its own margin as 12.5%**; the co-designers correct
  it to **7.5%** in 2025/1893 footnote 11.
- ⚑ **CICO is measurably the wrong metric, and the bounty still measures it.**
  2026/306 Table 1 at α=7, ω=2: the attack gains **39.3 bits on CICO but 67.4 on
  3-to-1 preimage.** Our own audit already shows this shape — our cico-4 margin is
  **+83.7**, far tighter than the +286 compression figure. **Quoting +286 without
  saying "Merkle-compress mode" is quoting the flattering member of a pair**, which
  is the sin this repo has a standing rule about. `hash-verdict.md`'s one-line
  *"carry a +286-bit margin"* does exactly that and should name the mode.

### ⚑⚑ AND THE α COST/SECURITY TRADE INVERTS — my draft had it backwards

I wrote that KoalaBear's 1.82× in-circuit win is "partly bought with security
margin." **Held at equal cost, that is false, and the paper that exists to answer
this question says the opposite.**

**eprint 2025/1920, *ALFOMs and the Moirai*** (Boeuf & Perrin, Inria, Nov 2025) —
the only rigorous framework for security-per-constraint — derives, as R_P→∞:

`η_R1CS(α) → log₂(α)/ℓ(α)` and `η_AIR(α) → log₂(α)/α`

| α | η_R1CS | η_AIR | AIR, relative |
|---|---:|---:|---:|
| **3** | **0.792** | **0.528** | **1.00** |
| 5 | 0.774 | 0.464 | 0.88 |
| 7 | 0.702 | 0.401 | **0.76** |

**Monotonically decreasing in α, in both arithmetizations. α=3 delivers 32% more
security per AIR constraint than α=7.** At equal security, α=5 costs 8–19% more in
R1CS and 22–33% more in AIR than α=3. The round count over-compensates: KoalaBear
d=3 at t=16 is 28 rounds / **296 mults**; BabyBear d=7 is 21 rounds / **564 mults**
— **−25% rounds, +90% multiplications.**

⚑ **And 2025/954 (a Poseidon co-designer), Observation 3:** *"The number of rounds
needed to resist the FW-GB w/ subspace attack is **almost the same across all
considered α ∈ {3,6,7}**… the number of linearizable rounds (i.e. t−2) dominates."*
**Against the attack that actually dominates at small fields, α buys nothing — the
attack is governed by state width `t`, not α.**

> ### **So α=3 is the efficiency-adjusted OPTIMUM, not a compromise. My "bought with margin" was wrong.**

⚠ **The honest two-sided version.** What d=3 *does* lose is **observed** margin, and
that loss is real: the 2026 bounty frontier against Poseidon1/KoalaBear/d=3 moved
the zero-test record **R_P 6 → 12 in under three months** (2026-06-03 → 2026-07-27)
and CICO 6 → 10, while the 2025 d=5/d=7 targets went **entirely unclaimed ($40K
left on the table)**. **Efficiency-adjusted security favors α=3; measured
adversarial progress favors α=7.** Those are different claims and both are true.
⚠ And **it is moot for us**: BabyBear *forces* α=7 (§1a). α=3 is a KoalaBear
migration, not a knob.

### The round-skipping attack itself

- **2026/306 (Merz & Rodríguez García)** exploits the **non-MDS internal matrix**
  `Mε = P_{t/4} ⊗ M4`, chosen for circuit efficiency; its branch number `b < t+1`
  creates invariant unconstrained subspaces. Speed-up **2^106** on one recommended
  128-bit set. **First algebraic preimage attack easier than the corresponding
  CICO problem**; first collision attack outperforming its preimage counterpart.
- **Authors' own verdict**: *"due to the algebraic security margin this does not
  mean the primitive falls short of its claimed security level"*, and *"the
  complexity of our attacks surpasses 2^128 whenever α ≥ 3."*
- ⚠ **The disclosure already moved a spec**: *"the number of external rounds in
  [Poseidon2b] was increased after disclosing a preliminary report of our findings
  to Ethereum's Poseidon initiative."*
- ⚑ **CICO is measurably the wrong metric, and the bounty still measures it.**
  2026/306 Table 1: at α=7, ω=2, the attack gains **39.3 bits on CICO but 67.4 on
  3-to-1 preimage.** Priority for the phenomenon is **2025/954** on Neptune.
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

### ⚑ The AO graveyard — the context that decides whether a SIDEWAYS move is sane

Bold = **broken at its own claimed security level**, full-round.

| design | best published attack | status 2026-08 |
|---|---|---|
| **Poseidon / Poseidon2** | 2026/306: 2^106 speed-up, **no full-round break** | **unbroken**; margin eroded; Initiative moved to Poseidon1+MDS |
| **Griffin** | **FreeLunch 2024/347: 2^64 full-round at t≥12**; 2025/259: 2^53 | 🔴 **BROKEN**, ~75-bit shortfall |
| **Anemoi + Jive** | **2026/1281: ℓ=1 α=3 → 2^70 vs a 128-bit claim** | 🔴 **BROKEN** |
| **Arion** | **2025/259: 2^53–2^57, "almost all parameter variants"** | 🔴 **BROKEN** |
| **Rescue / Rescue-Prime** | **2026/1281: full-round α=3 at 2^112; α=5 exactly 2^128** | 🔴 **BROKEN at α=3, zero margin at α=5** |
| **Skyscraper v1** | **2025/102: truncated differential on the FULL 10 rounds in 2^8.19, implemented** | 🔴 **BROKEN ~1 month after publication** |
| Skyscraper v2 | none found | unbroken, **19 months old** |
| **Vision / Vision Mark-32** | **none found — and nobody has looked** | ⚠ **untested, not "safe"** |
| Monolith | practical collision 2 rds; 5-round distinguisher 2^11.3 | unbroken, 1–3 rounds real margin |
| Tip5 | **practical SFS collision on 3 rounds — the designers' own bar** | unbroken, ~1 round of real margin |
| **Jarvis · GMiMC · Grendel · Starkad · Ciminion(ltd) · Hydra** | full-round breaks / withdrawn | 🔴 **DEAD** |

> ### ⚑ **Poseidon2 is the most-attacked and best-surviving AO design, and the field around it is a graveyard.** >$1.5M of bounty-directed adversarial attention over 7 years, no full-round break. **FreeLunch — the technique that killed Griffin, Anemoi and Arion — mentions Poseidon ZERO times** (`pdftotext | grep -c -i poseidon` on 2024/347 → 0).

⚑ **Therefore a SIDEWAYS move inside the AO family is unsupported by any reading of
the record.** Monolith, Skyscraper, Tip5 and the Marvellous line all have strictly
less analysis, and three of four have a documented margin erosion in the last year.
**The only two destinations the security record supports are Poseidon1-on-MDS —
what the Initiative itself did — or out of the AO family entirely.**

⚑ **And the recurring wound is the LINEAR LAYER, three times over**: Starkad's weak
Cauchy matrices (2020/188), HADES's bad-MDS invariant subspaces (2020/179), and
Poseidon2's non-MDS internal matrix (2026/306). **Every one traded diffusion for
circuit cost.** That is the pattern to watch in any AO design we evaluate — and it
is the pattern our own deployed shape sits in.

### 🔴 And the uncomfortable one: BLAKE3 has the THINNEST record here

| | SHA-256 | Keccak / SHA-3 | **BLAKE3** |
|---|---|---|---|
| standardized | **FIPS 180-2, 2002** | **FIPS 202, 2015** | **NO — expired individual IETF draft** |
| rounds | 64 | 24 | **7** (BLAKE=14, BLAKE2s=10) |
| best collision | 37/64 (2^119.1, EUROCRYPT 2026) | 6/24 | **none published** |
| best distinguisher | 45/64 preimage | **9/24 keyed**; full-round zero-sum | ancestors: 8-round BLAKE-256, 7.5-round BLAKE2s |
| independent analysis | ~24 yrs, dozens of groups | **~17 yrs, ~90–100 papers, a 64-entry NIST competition, a 14-yr cash bounty** | **6 yrs, ZERO cryptanalysis papers in the eprint corpus** |

> ⚑ **BLAKE3's round count was cut 30% from BLAKE2s on an inheritance argument,
> landing at 7 rounds against ancestors broken to 7.5–8 — and eprint full-text
> search for "BLAKE3" returns 6 results, none of them cryptanalysis.** Choosing
> BLAKE3 **for its security record would be choosing a record that does not exist.**
> Choosing it for cost, ancestry and Ethereum's coattails is defensible. **Say which
> one you are doing.** If the analysis record is what you want, it is **SHA-256 or
> Keccak-24** — and SHA-256 is also the *cheaper* of the two in-circuit (§1a).

⚠ **And do not take K12/TurboSHAKE to claw back constraints.** 12 rounds is defended
against the *6-round collision*; against the **9-round cube attack** it is a **25%
margin, not 100%**. Go 24 rounds and pay.

### ⚠ The framing that must not slip

**Do not treat "traditional hash" as automatically safer in a circuit context.**
SHA-256 and Keccak have decades of *differential and linear* cryptanalysis; the
algebraic hashes have years. But the attack that matters for an arithmetized hash
is an **algebraic attack on the arithmetization** (Gröbner / CICO / FreeLunch /
interpolation), a **different literature**.

⚑ **The correction that survives the sweep, and it favors the traditional hashes —
but not for the reason usually given.** *This is a derivation from mechanism, and
it should be checked.* When SHA-256 or Keccak-f is arithmetized in a STARK the
prover does **not** get a low-degree system over `F_p`. It gets **bits**, each a
field element pinned by `x(x−1)=0` — verified against the pinned source:
`KeccakCols` commits `a_prime` as `[[[T;64];5];5]`, `Blake3Cols` commits booleans
per row. **So the system an adversary attacks is isomorphic to the GF(2) system
SAT/Gröbner/MQ have ground on since 2010, plus booleanity constraints that only
shrink the variety. Arithmetization creates no new algebraic surface.**

That is structurally the *opposite* of Poseidon, where the primitive is a low-degree
map over **the same `F_p` as the proof system** — a native Gröbner target. **It is
why the FreeLunch line exists for AO primitives and has no counterpart for Keccak.**
So the algebraic record for traditional hashes is thin substantially *because the
attack bounces off bit-oriented designs*, not because nobody tried — 16 years of
effort moved algebraic Keccak hash-mode preimages from 3 rounds to **5**.

⚠ **Two honest counterweights.** (a) Under the one *uniform* algebraic instrument
ever applied across all of them (eprint 2012/421, SAT preimage), **SHA-256 ranks
WORSE than Keccak**: 16/64 = 75% margin vs Keccak's 2/24 = 92%. That instrument is
14 years old and single-source, and **I found no modern replication** — the gap is
itself worth naming. (b) **No published attack on an arithmetized (in-circuit)
SHA-256, Keccak-f or BLAKE3 was found** in `~/paperbin`, the eprint mirror
1996–2026, or by web search, as of 2026-08-14 — *an absence claim, scoped to those
instruments, and those instruments are blind to arXiv and grey literature.*

⚑ **One epistemic caveat that outranks the rest.** Nearly the entire 2022–2026 AO
attack frontier is **one community** — Inria/ANSSI/Simula UiB, with satellites at
TU Graz (who are *simultaneously the designers*) and a few others. **"N years of
analysis" for an AO hash means "N years of one lab's attention, applied in
bursts."** Against SHA-256/Keccak it means a global field. That asymmetry is real
and it is not captured by any round count.

---

## 4. ⚑ THE ONE THING ACTIONABLE TODAY, AT ZERO CRYPTANALYTIC RISK

The crossover analysis assumes every proof's hash is re-verified in-circuit. **For
a whole class of our proofs that is false, by construction.**

> **A proof's hash must be SNARK-friendly only if a CIRCUIT consumes it. Where a
> NATIVE verifier consumes it, the SNARK-friendliness buys literally nothing and
> the 2.78× native premium is pure loss.**

### ⚠ FIRST, A RETRACTION — my draft named the wrong layer

I wrote that the **apex/outer** layer is the free one because "nobody wraps the
apex." **That is wrong, and reading `circuit-prove/src/dregg_outer_config.rs`
refuted it.** The outer layer is consumed by the **gnark BN254 Groth16 wrapper**,
which arithmetizes its Merkle compression — which is exactly why that layer already
runs `Poseidon2Bn254<3>` with `OuterCompress = TruncatedPermutation<Poseidon2Bn254<3>, 2, 1, 3>`
as the twin of gnark's `Poseidon2Bn254Compress`. **The tower already applies this
principle at its top, deliberately, and got the 90–145× swing in
`WRAP-NATIVE-HASH-DECISION.md` from doing so.** My "free apex" was a guess that the
code answers *no* to.

### ⚑ The class that IS free — and it is bigger than the layer I guessed

**Standalone application proofs that are verified NATIVELY in Rust and never enter
the recursion tower.** `circuit-prove/src/` carries **18 files** with native
`pub fn verify_zk` / `verify_*_proof_bytes` entry points — `descent_census`,
`dark_amm_private`, `dark_bazaar_private`, `cert_f`, `cert_qp`, `deco_leaf`, and
others.

Direct evidence, `circuit-prove/src/descent_census.rs`:

```
HIDING_VERIFIER_MANIFEST = "descent-custody-census-fixed8-v2|BabyBear|Poseidon2-state16|
                            exact-fields-v2|HidingFriPcs|salt=4|random-codewords=4"
```

with `pub fn verify_zk(proof, statement)` verifying it **in Rust, natively**.

> ### **These proofs pay the full 2.78× native Poseidon2 premium and receive NOTHING for it, because no circuit ever re-executes their hash.**

| | value |
|---|---|
| **win** | **1.54× – 2.27×** per such proof (the leaf-only row of §2) |
| **in-circuit cost** | **zero** — `R` does not appear; nothing arithmetizes it |
| **verifier win** | **larger** — FRI verification is ~100% hashing (`fast-systems-recon.md`) |
| **cryptanalytic risk** | **zero new** — Blake3 is already in our TCB (`docs/ASSURANCE.md` row 2) |
| **what it re-emits** | each such proof's VK / verifier-manifest fingerprint. A rebuild. |

### The audit that has to happen, and its exact method

**Per proof, one question: does any circuit consume this proof's Merkle hash?**
Concretely — is this config's proof ever passed to a wrap/recursion entry point, or
only to a native `verify_*`? That is a call-graph question, answerable by reading,
and **nobody has asked it proof by proof.** Every proof that answers *no* is a free
1.5–2.3×.

⚠ **I have NOT completed that audit** and the class size above is an
entry-point count, not an audit result. Some of those 18 may be wrapped on paths I
did not follow. **What is established is that the class is non-empty and the
principle is the tree's own** — not that all 18 qualify.

### ⚑⚑ MEASURED, BY ME, ON OUR OWN PINNED PLONKY3 — 5.82×

The §4 claim is no longer a derivation. Our pinned checkout ships two examples that
**prove the identical AIR over the identical field and differ in exactly one thing —
the Merkle/challenger hash**:

- `keccak-air/examples/prove_goldilocks_poseidon2.rs` — Merkle hash `Poseidon2Goldilocks<8>`
- `keccak-air/examples/prove_goldilocks_keccak.rs` — Merkle hash `Keccak-256`

Same `KeccakAir`, same Goldilocks, same `NUM_HASHES = 1365`, same FRI parameters.
**This is the native-hash swap, isolated.** Wall clock, whole binary, this laptop:

| Merkle/challenger hash | runs | **min** | spread |
|---|---:|---:|---|
| **Poseidon2Goldilocks\<8\>** | 6 | **40,195 ms** | 40,195 – 60,864 (load-sensitive) |
| **Keccak-256** | 5 | **6,907 ms** | 6,907 – 7,024 (**1.7%**) |

> ## ⚑ **5.82× — swapping ONLY the native Merkle hash, in a prime field, in the prover we actually use.**

**Reproduce:** `CARGO_TARGET_DIR=<dir> cargo build --release -p p3-keccak-air
--example prove_goldilocks_poseidon2 --example prove_goldilocks_keccak`, then time
both binaries.

⚠ **Honest reading, and it matters.** (a) Contended box — load averaged 17–63; the
Poseidon2 arm's 43% spread is contention, and it converged to 40.2 s as load fell,
so 40,195 ms is a **min-of-6 upper bound**, not a calibrated figure. Keccak's 1.7%
spread on the same box is itself informative. (b) This is **Goldilocks
Poseidon2-w8**, not our BabyBear w16, and a **Keccak-AIR** workload, which is far
more hash-heavy than our descriptor batch. **So 5.82× is an upper bound on the
effect and our geometry will show less** — my §2 derivation says 1.54–2.27× at our
shares. (c) Shape and sign are what I claim; the sign is unambiguous.

⚑ **The two halves of the trade are now BOTH measured by me on ONE pinned checkout,
which is the cleanest statement of this whole map:**

| direction | measurement | who wins |
|---|---|---|
| **in-circuit** (§1a) | Poseidon2 300 cells vs Blake3 9,168 vs Keccak 63,192 | **Poseidon2, 30.6×–210×** |
| **native** (here) | Poseidon2-Merkle 40,195 ms vs Keccak-Merkle 6,907 ms | **Keccak, 5.82×** |

**That is the trade, in one table, from one source tree. Neither side is folklore.**

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
2. ⚑ **Run the consumer audit** (§4), which is reading, not measuring: for each of
   the 18 native `verify_*` entry points in `circuit-prove/src/`, does any circuit
   consume that proof's Merkle hash? Every *no* is a free **1.5–2.3×** at zero
   in-circuit cost and zero new cryptanalytic surface — corroborated at 1.69× ST /
   1.26× MT by an independent published measurement. **Do this first; it is cheap
   and it is the only win on this page that needs no new mathematics.**
3. ⚑ **State the rule where it will be seen:** *a proof's hash must be
   SNARK-friendly only if a CIRCUIT consumes it.* `WRAP-NATIVE-HASH-DECISION.md`
   already applies it at the top of the tower and got 90–145× from it; nothing
   applies it anywhere else, and my own first draft got the layer wrong for want of
   it being written down.
4. ⚑⚑ **Price a LOOKUP-based Blake3 AIR in our own unit — this is the highest-value
   open measurement on the page** (§2). Blowup-cells including the lookup table and
   multiplicity columns, against Poseidon2's 1,192. **Under ~4,000 and this entire
   verdict flips**, because the arithmetization is worth a 27× swing where the hash
   and the field are worth 2–7× each. We already hold LogUp machinery.
5. **Re-scope the binary-field programme onto what it actually buys.** It buys the
   **proving** collapse (§1d finding 1: Grøstl out-proves Vision by 3.56×, and the
   algebraic advantage falls from ~30× to ~1.3×) and the **de-welding** of hash
   from field that Flock names. **It does not buy an escape from Poseidon2 in the
   recursion layers** and should stop being sold that way — including by me.
6. ⚠ **Make `hash-verdict.md` name the MODE on its "+286-bit margin" line** (§3).
   The figure is ours, correctly derived, and correct — but it is the **Merkle-
   compress** margin; the **cico-4** margin at the same parameters is **+83.7**.
   Quoting the larger of a pair without its mode is the flattering-number habit this
   repo has a rule about. **No Poseidon paper states a bits-margin at all**, so every
   such figure must travel with its bar and parameter set."
7. ⚠ **If we ever do leave the AO family, choose SHA-256 or Keccak-24, not Blake3,
   IF the reason is the analysis record** — Blake3 has **zero** cryptanalysis papers
   in the eprint corpus and 7 rounds against ancestors broken to 7.5–8, and SHA-256
   is *also* cheaper in-circuit (7,728 vs 9,168 cells). **If the reason is cost,
   Blake3 is fine — say which reason it is.**
5. **Land a second `HashFamily` instance from a real traditional hash.** The
   mathematics is done; the boundary plumbing is not. Until a second instance
   exists, "the swap is an instantiation" is a claim with one witness. **Two
   candidates are one import-boundary decision away** (§5).
6. **Ride the 2026/306 MDS transpose on the next flag day.** Free, and our
   deployed shape is the attacked one. ⚠ And note the EF's Poseidon Initiative
   moved **Poseidon2 → Poseidon1 (KoalaBear, MDS)** over exactly this attack — so
   this is not a cosmetic fix, it is the direction the people running the bounty
   went.
8. ✅ **Stop worrying that KoalaBear's α=3 buys its speed with margin — held at
   equal cost it is the OPTIMUM** (§3, eprint 2025/1920: α=3 gives 32% more security
   per AIR constraint than α=7). ⚠ But **do** track that the 2026 bounty frontier is
   moving fast against d=3 specifically (R_P 6→12 in a quarter) while d=5/d=7
   targets went unclaimed. Efficiency-adjusted security and observed adversarial
   progress point opposite ways; both are true.

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
