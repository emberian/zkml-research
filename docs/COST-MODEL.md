# One cost model everything checks into — and what building it exposed

2026-08-14. Ember asked what the lanes found and **how to synthesize more
intelligently.** The honest answer to the second is that I have been
**accumulating** — twenty facts appended to VERDICTS — not synthesizing. This
is the artifact that would have made the connections visible, plus the problem
that showed up the moment I tried to populate it.

## The model

Prover time is a small number of phases with different scaling laws. Every
measurement should update a share; every proposed win should name a phase.

| phase | scales with | kind |
|---|---|---|
| grind (PoW) | **nothing** | hash |
| LDE (coset NTT) | 2^b | arith |
| Merkle commit | 2^b | hash |
| sumcheck / fold | **nothing** | arith |
| query / opening | **query count** | hash |

*"Hash-bound" means the hash rows sum higher than the arith rows.* That is a
statement about a **mixture**, which is why two lanes could measure it
differently and both be right — they sat at different `b`.

## ⚑ What the model says that the list could not

Composing the two landed wins through the phase shares rather than
multiplying them:

- **The wins do NOT multiply.** 13.13× × 7.49× = 98× is **wrong**, and
  nothing in a flat list of wins says so.
- **Each win's value depends on the ORDER.** The grind fix is worth ~1.28× at
  the deployed point and ~1.46× *after* a blowup drop — because the blowup
  drop shrinks the phases the grind competes with, so **grind's share rises
  from 25% to ~36% and the same fix becomes worth more.**
- **A measured "13.13× faster" is a phase ratio, not a system ratio.** Grind
  alone (25%, blowup-independent) caps any blowup-only speedup at 4×.

## ⚑ And then the model failed to populate — which is the real finding

**I could not fill in the phase shares from our own notes.** They record
*conclusions* ("hash-bound", "25% is grind", "13.13× faster at 4096 rows")
without the table the conclusion came from, without the configuration each
number was taken at, and without whether `pow` was on. The shares above are
**reconstructed from prose and are not trustworthy** — and the composition
arithmetic changes qualitatively depending on whether the 13.13× was measured
at pow=0 (likely, since that was the clean-comparison recommendation) or at
pow=16 (impossible, per the 4× cap above).

**That is the process defect.** A note that says "13.13× faster" is unusable
six hours later; a note that says "prove ms at (lb,q,pow) = (6,19,0): X, and
(2,57,0): Y, at 4096 rows, min-of-N, N=..." composes with everything else
forever.

## The rules that follow

1. **Every measurement records its CONFIGURATION and its RAW numbers**, not
   only its ratio. A ratio without `(lb, q, pow, rows, N)` cannot be composed.
2. **Every proposed win names the PHASE it touches.** A win that cannot name
   its phase has not been understood.
3. **Compose through the model, never by multiplying.** And state the order,
   because the order changes the value.
4. **A phase share is a claim like any other** — it gets a source and a date.
5. **When a new measurement contradicts a share, that is a finding**, not a
   discrepancy to average away. Two lanes disagreeing on "hash-bound" was the
   model telling us they were at different `b`; we treated it as a dispute for
   half a day.

## What to do next, in this order

- **Extract the profiler's actual per-phase table** into this file, with
  configurations. It exists — it was in a lane's output and only the summary
  reached the notes.
- **Re-state the blowup measurement** with its config, so the composition can
  be computed rather than guessed.
- **Then** compose the landed wins honestly and publish one number for "what
  ships if all four land," which nobody currently knows.
