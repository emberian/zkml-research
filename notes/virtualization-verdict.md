# "Boundary" is called VIRTUALIZATION, it's standard, and what's ours is the price

2026-08-13. `notes/boundary-statements.md` (849 lines) +
`paper/scripts/boundary_exchange_rate.py`.

## The principle is standard, named, and in our own library

**It is `virtual polynomial` / `polynomial virtualization`.** Thaler,
*"Sum-check Is All You Need"* (eprint 2025/2041) §5.2: *"the only polynomial
actually explicitly committed by the prover is the input layer of the
circuit."* **The whole survey's thesis is our sentence.**

**The upper-bound half is a published theorem, twelve years old** — Thaler
CRYPTO 2013 Thm 3: matmul in `n² + O(log n)` communication, prover time
`T(n) + O(n²)` for *any* unverifiable matmul algorithm. Complexity
counterpart: Kalai–Raz 2008 → RRR16 → Ron-Zewi–Rothblum 2019, whose Remark 1.2
gives the citable restatement:

> **An AIR commits the Cook–Levin witness; a virtualizing sumcheck commits the
> original NP witness.**

⚑ **And mechanism #3 fired hardest yet: 2025/2041 is in `~/paperbin` TWICE
under two filenames**, next to a `cc-` shelf of 17 complexity papers that
answers the theorem question outright. The lane extracted full text from all
**1,218 PDFs**; **that rebuild command should become standing infrastructure**,
since "grep paperbin first" is useless if paperbin isn't text-searchable.

## Four corrections to my framing

1. **The monotone reading is refuted by the same survey**: *"commit to as
   little data as possible. **Not zero — there's a sweet spot.**"* A
   pure-virtualized statement can be *slower*, because committing advice buys
   a cheaper residual check.
2. **The fork should not name AIR.** Per CCS, R1CS/Plonkish/AIR are
   interconvertible at near-zero cost; **the property is
   materialize-vs-virtualize**, not a proof-system family. (CCS claim is
   second-hand — flagged.)
3. ⚑ **Retire the word "boundary"** — it collides with **border rank** in
   precisely the community most likely to read a matmul claim. Also never
   "succinct PCP" or "certificate complexity" for this.
4. ⚑ **My use of 2026/1390 as a general Ω(m) commitment floor is WRONG** — it
   is a **lookup-specific, self-described restricted-model separation**, in the
   paper's own words *"restricted-model and content-agnostic: rank/degree
   bounds within a fixed prover class […] not unconditional complexity
   bounds."* I cited it as a general floor repeatedly. **The general floor we
   do hold is the `Ω(|w|)` extraction argument, backed by GH98/GVW02**
   (`notes/boundary-statements.md` §2.5(b)) — a different object with a
   different proof.
   **Where the bad citation actually is** (grepped, 2026-08-13, so the next
   reader fixes sites instead of hunting them): `notes/ml-to-crypto-mappings.md`
   §A, `notes/speedup-ledger.md` Bin 2 item 1, `notes/moe-router-binding.md`
   §7, `docs/AGENDA.md` Pillar I, and `notes/archive/PLAN.md` §1 — all now
   carry the correction. ⚠ **Not `notes/prover-floor.md`**, which this note
   accused: that file's floor is the `Ω(|w|)` extraction argument and never
   cites 1390. *A confession is a claim like any other; this one was checked at
   source and half of it was false.*
   (Uses of 1390 for its **Proposition 3** — the rank-ρ table-cost result —
   are fine and stay: `docs/PHASE0-RESULT.md`, `notes/speedup-ledger.md` Bin 1.)

## What is actually ours: the exchange rate

**The lower-bound half does not exist.** Nobody has shown any relation
*requires* committing more than its statement, and the question is not framed.
**That is the only place novelty lives** — and it is a real one.

**And the price is ours, measured:** one committed base felt ≈ **3,120 field
multiplications at lb=4, 12,331 at lb=6**; virtualizing one ≈ **40 per layer**.
**A 78×–308× exchange rate** — which *locates* Thaler's asserted sweet spot and
turns it into a **threshold rule**: virtualize while the layer count is below
the exchange rate. Sunset condition stated: the ratio swings **28× across the
blowup knob**.

⚑ **CORRECTED 2026-08-13 by `notes/poseidon2-virtualization.md` §4 — the units.**
78×/308× is in **counted field multiplications**; the mult-equiv → wall-clock
conversion was never taken. Taken (both halves measured on the deployed prover:
54.7 ns per marginal committed felt, 10.97 ns per value per sumcheck layer), the
exchange rate at lb=3 is **≈5 layers, not ≈40**. Hashing SIMD-vectorizes harder
than sumcheck folding does, so a scalar multiplication count **over-prices
commitment by ~8×**. The rule survives; the threshold does not — and the
correction **reverses test #1 below**. Never quote 78×/308× as a wall-clock
budget.

The SELVAGE marquee 5,461× **checks out to 2.4%** and now has a derivation
artifact rather than an assertion.

**Better unifying phrase than "boundary": SHALLOW AND WIDE** — the
literature's own class (bounded depth *or* bounded space), which also says
what does **not** qualify: zkVMs.

## The compiler is three halves, each already built — in a different field

- **Derivation engine — BUILT, in HPC.** Rajopadhye's group (POPL 2025 +
  arXiv 2411.17498) **automatically derives the O(N²) ABFT checksum from the
  O(N³) matmul spec.** We assumed this was the research problem.
- **Cost-model search — BUILT, in zkML.** ZKML (EuroSys 2024, *in our
  paperbin*) already ships the Freivalds move — **hardcoded in one gadget,
  unreachable by its own optimizer, and it disclaims formal correctness.**
- **Machine-checked emission — BUILT, in Lean.** Clean + ArkLib — with no
  search and no cost model.

⚑ **And the obvious joining technology is the wrong one**: e-graphs preserve
**functional equality**, and Freivalds is **not an equality — it is a
soundness-preserving reduction.** That explains the empty ZK/equality-
saturation literature, and it names the unclaimed object precisely:

> **a rewrite system over RELATIONS, ordered by soundness-preserving
> reduction, scheduled against a measured commitment price, with each step a
> Lean theorem about the emitted object.**

⚠ And any "nobody tried this" must survive **Allspice (S&P 2013)**, which did
protocol selection by static analysis and the field dropped it.

## ⚑ The three sharpest tests — and the first one is a live prediction

1. ~~**The Poseidon2 permutation.**~~ ✅ **RESOLVED 2026-08-13 —
   `notes/poseidon2-virtualization.md`.** The prediction was "~21 layers against
   a 78/308 threshold ⇒ virtualizing beats committing by 4–15×". Measured:
   **virtualizing wins by 2.11× prover / 1.28× verifier / 2.24× committed felts
   — but NOT by a sumcheck.** The win is *in-AIR* virtualization of the **211 of
   352 committed felts that are degree 1** (upstream `p3-poseidon2-air` already
   does it; our chip does not): no sumcheck, no degree cost, strictly Pareto.
   The *sumcheck* virtualization this line predicted **LOSES at α=7** by 1.4–2.4×
   against the corrected exchange rate above, and wins only at **α ≤ 3** — which
   is the KoalaBear answer, reached from the other direction.
   ⚠ And the `map_write_chip` 227 ms vs `umem_write_read_nochip` 14.9 ms
   "corroborating signal" **is not one.** Checked at source
   (`breadstuffs/.docs-history-noclaude/PERFORMANCE.md:85-110`): that is a chip
   table PRESENT vs ABSENT comparison — the no-chip shape "hashes nothing
   intra-proof" — not a materialize-vs-virtualize fork on one relation. It
   belongs to the universal-memory result.
2. **The LogUp aux column** — 71% of committed elements. Thaler's own matmul
   virtualization *is* a degree raise, so price it through
   degree→blowup→hash, **not element count.**
3. **The kernel turn** — the only workload where we *assert* the principle
   already holds and have never measured it. The 10,000× gap makes O(1)
   implausible.
