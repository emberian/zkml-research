# Neo/SuperNeo: cannot be scored, doesn't compose with binary fields — and one over-conclusion to correct

2026-08-14. Full read at `notes/neo-superneo-read.md`.

> ⚠ 2026-09-04: **"no implementation" is dead** — LFDT-Nightstream/Nightstream
> (Lean 17 MB + Rust 6 MB, ★30, pushed 09-04: SuperNeo Π_CCS→Π_RLC→Π_DEC +
> HyperNova-style IVC + Spartan2 decider, "research software"), moven0831/superneo
> (Rust PoC), a Swift/Metal PoC; eprint 2026/242 is at rev 3 (CRYPTO 2026). It was
> already false on 08-14 (Nightstream dates from 2025-08). **"No published
> constraint count for its own recursive verifier" survives** — Nightstream has an
> `--ignored` test that would print the decider R1CS shape, unrun by anyone in
> print. `lova-neo-rmfe-read.md` §2. The binary-field incompatibility and the
> dual-mode kills below stand.

## ⚠ CORRECTION TO THE LANE'S HEADLINE, BEFORE ANYTHING ELSE

The lane concluded **"there is no BinarySpartan — the premise is false"** after
checking five ways (eprint full-text, author search, 810 mirror papers
first-page-grepped, GitHub, the MSR page). **The search was sound; the
inference was not.**

**BinarySpartan exists.** Ember has its **title page and abstract from the
eprint REVIEW QUEUE**, plus an EF slide with its benchmark table. It is
awaiting publication, so **by construction it is in no mirror and no author
listing.** *Not-in-the-archive ≠ does-not-exist* — and this is the
absence-claim failure class again, with the instrument fine and the inference
wrong. (I had sent exactly this warning mid-lane; it either arrived after the
search or was not applied.)

**What the lane's search DID establish, and it is genuinely useful**: the name
traces to **Irreducible's Binius64 blueprint §1.2, "Why Not Binary Spartan?"**
— *a rejected strawman.* ⚑ **So Irreducible considered this design and
rejected it, and Setty then built it and it is the fastest scheme in the EF
client-side benchmark.** That reversal is worth understanding before we form
any position.

## What the lane settled, and these stand

**⚑ The Desktop PDF is a NEWER REVISION.** Desktop = 13 Aug 2026, 59pp;
`~/paperbin`'s copy = 12 Feb 2026, 60pp. Both retained deliberately.

**The 128× figure is DEAD, and the authors killed it themselves in that
revision**: Feb said `64 × 64 = 4,096 **bytes**` vs `32 bytes` ⇒ 128×; Aug says
`64 × 64 **bits** = 4,096 bits` vs `256 bits` ⇒ **16×**. **A prior lane's
arithmetic was right to the digit.** Never cite 128×; the qualitative point
survives with the magnitude overstated 8×.

**Neo cannot be scored — not "was not."** No implementation, no evaluation, no
benchmark, and sharper: **no constraint count for its own recursive verifier.**
Every R1CS number in the paper is about someone else. Its marquee
"low recursion overhead" is *a ✓ in Figure 1 plus the sentence "Our goal is to
achieve logarithmic recursion overhead,"* with the strong form conceded as an
open problem. **Five of six desiderata are analytic; the one requiring
measurement is the unmeasured one.**

**Neo is structurally incompatible with binary fields** — zero occurrences of
"binary field", "characteristic 2", "Binius", or `GF(2)`. **Pay-per-bit is a
statement about lattice NORMS, and characteristic-2 fields have none, so MSIS
has nothing to bind.** So Neo is *not* the folding layer a binary-field Spartan
would recurse with. That question is closed.

## ⚑ Neo's accounting independently corroborates our wrap identity

The lane verified our measurement at source (`1ba443bdd`): 38,168 native
permutations ≡ 38,168 in-circuit ops. **Neo's "the verifier hashes the child's
transcript" is our identity read as design pressure** — so the identity is
**general, not a tower artifact.**

**But its fix does not apply to us**, three ways: (1) the fix is *"stop being
hash-based"* — Ajtai commitments open no Merkle paths, and **we are literally
the row Neo labels Arc**; (2) **our field is off its map** — BabyBear is
31-bit, Neo's three parameterizations are all 61–64 bit and it never mentions
31-bit fields; (3) it is unmeasured.

⚠ **And our own denominators calibrate its rhetoric down**: in-circuit
Poseidon2 is **36.45%** of a leaf wrap / **53.98%** at apex, so the entire
low-recursion pitch **caps at ~1.6–2.2× even driving hashing to zero.**

## Accumulation depth

**Neo does not engage the depth axis at all** — `Π_DEC` makes depth vanish by
paying a k-way decomposition *every round*, and its IVC comes from standard
heuristic-RO compilers with the usual extractor blowup.

**Paneth–Pass 2026/662** (read, archived): proof size **linear in depth,
independent of tree size** — but it is a SNARG for **P, not NP**, i.e. **it
escapes the barrier by giving up knowledge soundness**, and it requires
tree-bounded mergers that **exclude DAG merge topologies**. *It resets a
neighbouring bar; our composition is not superseded.*

⚑ **The real find: Cyclo (2026/359)**, which Neo itself credits as
"equivalent to Neo" and defers its only benchmark to, has **additive norm
growth per round within a bounded number of folds** — a stateable, bounded,
refutable depth budget, **the same shape as our accumulation-depth
composition.** ⚠ And that benchmark is a *commitment-only microbenchmark at
q≈2^50, outside Neo's own parameter regime* — **so there is still no
end-to-end measurement of Neo anywhere.**

## Cheapest next probe

**Neo ships its lattice-estimator sage script (Appendix B.6).** Running it at
`q = BabyBear` settles whether Neo is instantiable at our field width at all —
the paper does not say. Bounded, and it opens or closes the door cleanly.
