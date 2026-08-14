# The hash landscape — why Poseidon2, and what it would take to leave

2026-08-14. **Basic research, charting a landscape — not choosing a winner.**
The deliverable is a map plus a composable Lean ingredient, and the ingredient
landed (`minidregg@bf0b311`, `Selvage/HashFamily.lean`).

---

## ⚑ THE HEADLINE, IN THREE LINES

1. **The crossover is `R* = 2.0×–4.5×`**, computed from our own measurements
   (§2). Below that in-circuit ratio, a traditional hash wins outright everywhere
   in the tower; above it, Poseidon2 wins.
2. **In a prime field we are not near the crossover — we are 1–2 orders of
   magnitude from it.** So the honest answer to *"are we stuck with Poseidon2?"*
   is **in a prime field, effectively yes, and it is not a close call.**
3. ⚑ **But the escape is not a different hash — it is a different FIELD.** In a
   binary field `R` collapses toward 1 or below, and the entire justification
   evaporates. **The hash question is a field question wearing a hash costume.**

**And one thing is actionable today, at zero cryptanalytic risk** (§4): the
**top layer of the tower is never arithmetized by anyone**, so its native hash is
a free choice worth **1.5×–2.3×** with no in-circuit cost whatsoever.

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

### 1a. Our own in-circuit numbers, which are the only ones I trust unreservedly

| hash | field | unit | cost | source |
|---|---|---|---|---|
| **Poseidon2-w16** | BabyBear | **AIR cells/perm** | **300 main + 24 prep = 324** | `recursion-tower-profile.md` §3a |
| Poseidon2-w16 | BabyBear | AIR cols/perm | **298** | `hash-verdict.md` §5 |
| Poseidon2-w16 | **KoalaBear** | AIR cols/perm | **164** (α=3 evaluates inline; α=7 forces a committed intermediate) | `hash-verdict.md` §5 |
| Monolith-31 | KoalaBear | AIR cols/perm | **3,520** (≈900 granting LogUp) | `hash-verdict.md` §4 |
| Poseidon2-w16 | **BabyBear emulated in BN254** | **R1CS/perm** | **16,837** | `breadstuffs/docs/deos/WRAP-NATIVE-HASH-DECISION.md` |
| Poseidon2-w24 | BabyBear emulated in BN254 | R1CS/perm | **27,213** | same |
| Poseidon2 | **BN254 native** | R1CS/perm | **187** | same (gnark std) |

### 1b. ⚑ The 90× in that table is a FIELD-MATCH effect, not a hash effect

**16,837 → 187 R1CS for the same hash.** Nothing about Poseidon2 changed; only
whether its field matched the proof system's. That is the single largest ratio
anywhere in this document, and it is the map's central lesson in miniature:
**hash choice is a second-order term on top of field match.**

### 1c. The binary-field column — where the argument inverts

Our own derived rate, and the published ones we can compare it to:

| system | hash | field/arithmetization | rate | source |
|---|---|---|---|---|
| **ours (derived)** | **Poseidon2** | BabyBear prime | **~17,700 perms proven/sec** (38,168 in-circuit ops ÷ a 2.16 s wrap) | `docs/RESEARCH-STANCE.md` |
| Flock | **BLAKE3** | binary | **82k compressions/sec**, 1 M4 Max core; >660k on ten | eprint 2026/1329, abstract verified verbatim |
| Flock | SHA-256 | binary | 42k/sec, 1 core | same |
| Flock | Keccak | binary | 30k/sec, 1 core | same |
| BinarySpartan | BLAKE3 | binary | 410k/sec on 12 P-cores = **34.2k/core** | EF slide; see `notes/binaryspartan-position.md` for the scrutiny |

⚑ **A traditional hash proven in a binary field runs 2–5× FASTER than our
algebraic hash proven in a prime field.** The advantage does not merely shrink —
**it reverses.**

> ⚠ **Honest caveats on that comparison, all load-bearing.** Different systems,
> different hardware (M4 Max vs our contended M2 Max), different workloads
> (batch throughput vs one wrap), and our 17,700 is *derived* from a wrap time,
> not measured as a hash rate. It is a **shape-and-sign** claim, not a calibrated
> ratio. What survives the caveats is the sign, and the sign is what decides the
> design.

### 1d. The rest of the space

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

### ⚑ Where prime-field reality actually sits, against R\* = 2–4.5

Poseidon2 is **~300 AIR cells/permutation** in our own tower. Every prime-field
number for a bitwise hash is one to two orders of magnitude above that —
Keccak-f is quoted at **20k–50k R1CS** in our own notes precisely *because it is
bitwise* (`notes/ring-hash-build-verdict.md`). Even allowing generously for the
R1CS-vs-AIR unit gap, **`R` lands at roughly 50–150×, against a crossover of
2–4.5×.**

> ### **The prime-field verdict is not close. It is off by 10–50× of margin.**
> This is not "Poseidon2 narrowly wins." It is "the crossover is nowhere near
> the operating point, and no amount of tuning the trade moves it." **Poseidon2
> is not a preference we inherited and could casually drop; in a prime field it
> is load-bearing by more than an order of magnitude.**

⚠ **And say the unflattering half out loud**: this means the 2.78× we pay
natively is *cheap* for what it buys. Our own map vindicates the inherited choice
in the field we are in — which is not the answer the question was hoping for, and
is the answer.

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
  The "Goodbye, Poseidon! … in hindsight the key was not SNARK-friendly hashes,
  but hash-friendly SNARKs" quote is real and accurately attributed to a senior EF
  researcher — but **there is no EF publication behind it**, and the Poseidon
  Cryptanalysis Initiative is still scheduled through December 2026 with live
  bounties. "Reaches its dream conclusion" means Poseidon **survived**; the pivot
  is performance-and-conservatism driven. (`notes/binaryspartan-position.md` §10.3)
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

> ⚠ **I have not measured this and I am not going to pretend otherwise.** It is a
> derivation from committed shares plus a structural fact about who verifies the
> apex. The measurement is cheap — swap the outer config's hash and time one
> apex — and it is the next thing to do.

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

1. **Keep Poseidon2 in the prime-field tower.** Not from inertia — the crossover
   says it wins by 10–50× of margin, and our own numbers say so.
2. ⚑ **Take the free apex win** (§4): 1.5–2.3× at zero in-circuit cost and zero
   new cryptanalytic surface. Measure it first; it is one config swap and one timing.
3. ⚑ **Understand that the binary-field work is not a benchmark race — it attacks
   our own dominant term.** We are hash-bound at 5.0–7.2×, and we chose our hash
   for a reason that **only holds in a prime field**. That is the connection this
   map exists to make legible.
4. **Land a second `HashFamily` instance from a real traditional hash.** The
   mathematics is done; the boundary plumbing is not. Until a second instance
   exists, "the swap is an instantiation" is a claim with one witness.
5. **Ride the 2026/306 MDS transpose on the next flag day.** Free, and our
   deployed shape is the attacked one.

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
