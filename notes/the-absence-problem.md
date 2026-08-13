# Five refutations in one day: our absence claims are the weak part of the method

2026-08-13. Not bad luck. A pattern, with a named mechanism.

## The scoreboard

| claim | fate | where the refutation was |
|---|---|---|
| MoE router binding: "zero papers in 7,090" | **REFUTED** | **two papers in ~/paperbin**, pulled the same day |
| Carrier census / vacuity instruments | **REINVENTION** | mathlib linter (2020), model checking (2001–2003), Dafny flag, FMCAD 2025 |
| The prime + family law | **FOLKLORE** | **Riesel 1994 textbook, Table 5, row h=127** — p61 is the 5th entry, KoalaBear the 4th |
| "Multilinear/GKR substrate absent everywhere" | **REFUTED** | six shipped systems incl. **Ethereum mainnet** |
| Proof-aware QAT: "in nobody's paper" | **REFUTED** | **two papers in ~/paperbin** + an industrially shipped product |

## Update, same day: the count reached TEN

Added by the ML-systems sweep: the MX exponent-spread statistic (published,
**in our paperbin**), the weight registry (four groups, one **in our
paperbin**), proof-aware QAT again, sequential LLM auditing (e-values,
MPI-SWS), and "append-dominant KV" (six counts). **Every single absence
stated as "zero papers" was found by a crypto-shaped query, and the ML
systems / cs.AR / MLSys / ICLR-workshop literature answers the same question
in different words.** That is the mechanism, stated exactly.

## The mechanisms, all four of them

1. **Corpus blindness.** The eprint mirror is cryptology-only and incomplete.
   ML systems, math, formal methods, architecture, and ALL grey literature are
   invisible to it. (Named in PREFLIGHT; it cost us three of the five.)
2. **Instrument blindness.** A first-2-page keyword cache cannot see a §4.3 or
   an appendix. Both MoE refutations and both QAT refutations bury the content
   past page 2.
3. **⚑ We do not grep our own holdings.** Four of the refuting papers were
   *in ~/paperbin, correctly named*, when the absence was declared. This is
   the cheapest possible check and we skipped it every time.
4. **⚑ NEW: arXiv's API `all:` field searches METADATA ONLY, not full text.**
   A zero-hit arXiv query is therefore *much* weaker evidence than it reads
   as. Several of our absences rest on exactly that.

## The rule, going forward

**No absence claim ships without:** (a) a grep of `~/paperbin` first —
literally first, before any search; (b) the corpus AND the instrument named
in the claim itself; (c) at least one non-eprint corpus consulted; (d) an
explicit note if the evidence is metadata-only.

And the framing correction that makes this less painful: **we are not
prospecting for unclaimed territory.** The value of finding that Tailor
already does proof-aware QAT is that *we now know how to do it properly* —
their power-of-two scales and derived-not-tuned shifts are exactly the design
we wanted, already validated. A refuted novelty claim is a found collaborator
and a saved month. Every one of these five made the work better and none of
them made it smaller.

## What actually survives across all five

Not "we were first." In each case a **transfer**, a **narrowing**, or an
**instrument**: the ZK instantiation of QAT (everyone else did FHE/MPC); the
specific FHE×proof constraint pair (everyone else posed one side); ranking
and self-testing on top of a 25-year-old vacuity check; Lean certificates for
a textbook family; and building our own GKR substrate *knowing the pitfalls
six shipped systems already published*. Those are all real and none of them
needed to be first.
