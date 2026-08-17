# Ember's steers — the highest-signal file

Every one of these changed the direction of the work. Written from the live
context of the sessions; where the wording is ember's it is quoted. **A
session-archaeology lane recovered ~30 MORE in `01b-STEERS-RECOVERED.md` —
read that FIRST.** Deduplicating 617 raw messages to 117 unique across 12
sessions, it found that **several turning points I narrate below as my own
noticing were ember's, earlier**:

- ⚑ **The field question came a FULL DAY before the hash question** —
  *"we're only using babybear because plonky3 already was"* (08-13 11:22). So
  §10's "seven things I was treating as fixed" is a **late** recognition of a
  pattern ember had been running for a day.
- ⚑ **The phase-decomposition thesis is EMBER'S** — *"there are probably
  different phases of the process that are bound differently right?"* — **six
  hours before** the synthesis steer that §7 credits with producing
  `COST-MODEL.md`.
- **The origin steer carried a half nobody recorded**: *"isn't that the same
  technique we used to accelerate one of the mina→dregg directions?"* —
  **ember recognised commit-then-audit as ALREADY OURS**, which is *why* the
  audit pillar existed at all.
- **Why `zkml-research` exists is ETHICAL**: *"so we don't accidentally cast
  shade on a 'competitor' (they're actually collaborators, in a way, in my
  view of the worldsystem)."*

⚑⚑ **Two method findings from the archaeology, and they belong at the top:**
1. ***A mild "why are we doing X?" from ember is a stop-work order that has
   not raised its voice yet.*** The Plonky3 question preceded the Plonky3
   shout by **45 minutes** and was **ignored**.
2. ***The only reliable detector of a lost result was ember's memory.*** She
   ran `cv index` herself and said *"look again."* **No instrument of ours
   found those.**

The rest of this file is the part I held directly.

---

## 1. "Stop thinking about moats"

**What I was doing**: framing findings as competitive position — "the open
position is vacant," "unclaimed," an "unclaimed-claims ledger" as an actual
document section.

**The correction**: *"moat" imports the assumption that value comes from what
others cannot have* — the opposite of a project whose whole position is that
verifiability should not be an enterprise feature. Purged, along with the
land-grab vocabulary.

⚑ **And it recurred twice more in different costumes**, which is why it is
first: I kept sorting findings by *provenance* rather than by *what produces
the best outcome*. Ember, third time: **"I don't care what's 'ours' — I'm
trying to find the best possible outcome regardless of who or where it came
from, doing compositions we can do because we own the full stack including
the formal reasoning."** That produced `docs/COMPOSITIONS.md`.

## 2. "Vacuity-checking is tacit behavior, not a contribution"

I had written up our vacuity instruments as a novel methodological
contribution. They are **standard careful practice with a 25-year literature**
(model checking, 2001; mathlib's `#print axioms` discipline, 2020). Early-
development vacuous assumptions are *normal*. The only real difference is
doing it mechanically and marking what stays open.

## 3. "Stop the soundness theater"

**Counted at the time**: ~15 refutations, 4 audits, 3 corrections-of-
corrections against **1 design artifact and 2 builds.**

> *A perfectly honest ledger of a system that is 100× too slow is still 100×
> too slow.*

**The rule that came out of it, and it held**: **verification is a gate on
claims, not a source of them.** A lane producing a verdict about our own
claims must be outnumbered by lanes producing a design, a frontier
measurement, or a build.

## 4. "We are abandoning Plonky3"

Not "we should consider." The framing that mattered: **"it already exists
upstream, unwired" is a TEMPTATION, not an opportunity.** Upstream may be read
for API shapes and used as a throwaway differential oracle; **it never enters
the trust path.** Now §7b of the brief template.

⚑ **And it later explained a mystery**: we use Poseidon2 *because Plonky3
handed it to us* — a fact nobody had stated until the design stopped being
treated as fixed.

## 5. ⚑ "Are you taking measurements on my ridiculously overloaded M2 CPU?????"

**The sharpest correction of the campaign.** I had built a whole phase-
composition cost model on wall-clock numbers taken at load 16–95 — **and used
them to overturn an operation-count model**, writing "the exchange rate was in
the wrong unit, counted multiplications where nanoseconds bill."

**I had the reliability ordering exactly backwards.** On a contended box,
**counted operations are the MORE reliable estimator.**

⚑ **And "ratios are safe" is false**, which is the part I had not thought
through: **hash work is memory-bound and field arithmetic is compute-bound, so
they degrade at different rates under contention** — making `hash/arith`, the
central claim of two days, *precisely* the quantity a busy machine corrupts
most.

**What followed**: op counts primary; wall clock secondary and only for
op-class conversion rates on a quiet machine; **never compose a work claim
with a latency claim**; and build the arithmetic op-count hook, which was the
missing half of the only instrument that worked. **The hook then settled
hash-boundedness properly as a conditional** (`hash-bound iff Y > X`, X exact,
Y measured).

## 6. "Our working files filled up with contradictions"

I had been repairing by **appending a ⚠ marker** rather than rewriting, so
every file led with its own dead claim. 78 files, worst one carrying 28
correction markers. Produced `docs/VERDICTS.md` as **the single current-truth
file with no history in it at all**, and an archive with a README saying
plainly: *history, not truth; do not cite.*

## 7. "What did the lanes find, and how can we synthesize more intelligently?"

I had been **accumulating** — twenty facts appended to a file — not
synthesizing. Produced `docs/COST-MODEL.md`: one phase model everything checks
into. **It paid immediately** (the wins do not multiply; the order changes
their value) **and then failed to populate**, which was the real finding:
*our notes recorded conclusions, not the data conclusions came from.*

## 8. ⚑ "I'm more in favor of exploratory formalization than dismissing out of pocket"

A lane concluded *"Ligerito cannot compose from what we hold"* and I let that
read as *not worth pursuing*. **Those are different questions.**

**Exploratory formalization then refuted two of six "absent" verdicts, inverted
the sequencing** (Ligerito's *general-code* bound sits where our proximity gap
is proved unconditionally; its *headline RS* bound is the expensive one), and
found **the errata were display-only** — calling it broken would have been the
flattering-number sin in reverse.

> **"Does X compose with what we hold?" is a scoping question. "Is X worth
> understanding?" is a different one.** I conflated them.

## 9. "Why *are* we using Poseidon2 — are we stuck with it?"

Dissolved a question I had been treating as settled. Answer: **not stuck, and
staying — but now for a measured reason.** In-circuit it wins 30.6×–210×;
natively it loses 5.82×; the crossover from our own shares is 2.0–4.5× against
a measured 30.6×. ⚠ **And it refuted my claim that binary fields rescue the
trade** — proving converges, *verification does not*, and recursion cost is
verifier cost.

## 10. ⚑ THE STANCE

> *"We're not trying to just build one thing that dominates everything. We're
> trying to flesh out models and implementations of many of these proof
> systems, by implementing the primitives in composable ways. Lean is a bag of
> formal composable ingredients that we build as we chart them out. We're
> basically doing pure basic research, not trying to build a product —
> formalize and evaluate the landscape. **Parts of the design you've been
> tacitly treating as fixed are in fact mutable.**"*

**Seven things I had been treating as fixed and were not**: Poseidon2 ·
BabyBear · FRI-as-the-PCS · AIR-as-the-relation · Ext4 · blowup 6 · **prime
characteristic itself.** Every one moved within two days, and one of them (the
blowup floor) turned out to be **an upstream bug we had frozen as a law in our
own test suite.**

## 11. "Why *can't* we touch 410k hashes/sec? What is our own bound?"

I had asserted a bound without deriving one. Derived: **~17,700 Poseidon2
permutations proven/second**, 12.4× off BinarySpartan's SHA-256 throughput. ⚠
**And I declined to quote the compounded figure**, because our own cost model
says the wins reshuffle phase shares rather than multiplying — **which the
hbox rig later confirmed by refusing to produce it**: work 1.0000×, latency
1.4554×, naive multiplication overstating by **26.6×**.

## 12. The architectural question: separate leaf and recursion systems?

Ember's instinct, and it was right in a way neither of us predicted. **SP1 and
OpenVM both keep one proof system across layers**, changing parameters plus a
hash-field swap. **The deciding quantity is `K = wrap/leaf`: ours is 26.9,
theirs is < 1.**

> ***Our problem is not the proof system. It is that the leaf is too small.***

And ember's suspicion that arbitrary-length extendability might be too
expensive to pay for always: **priced at ×27.9 per turn, paid whether or not a
chain is ever extended.**

## Smaller steers that changed real things

- **"remember that `dev/gh/forks/IACR-eprint-mirror/` exists"** — the complete
  archive to 2026/1053+, against a scratchpad cache that stops at **777**.
  Every absence claim made against that cache was missing ~276 recent papers,
  *in exactly the window where the current binary-field work lands.*
- **"measurements should be conducted carefully on hbox (which is quieter)"**
  → the rig, which found four defects on its first run including that **hbox
  was building the scalar Poseidon2.**
- **"we can also be doing more of the novel work"** and **"avoid verification
  or audit theater, aggressively pursue doing"** — the pivot that produced the
  build lanes.
