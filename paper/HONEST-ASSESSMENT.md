# Have we found a novel design point? No. Here is exactly what is missing.

2026-08-13, main-context assessment after ember pushed back on the framing.
This document exists to stop the paper from being written on a claim we have
not earned.

## The hole I glossed, and it is the empirical centerpiece

The paper's headline empirical fact is "Zama's deployed system has one
doubling of headroom, imposed by a modulus chosen without checking the
proof-side constraint." **Computed from the experiment lane's own measured
RSS (60 GB at ν=29, ~165 B/eval, linear):**

| ν | prover RSS | note |
|---|---|---|
| 29 | ~60 GB | the lane's last e2e-verified size |
| 30 | ~120 GB | |
| **31** | **~240 GB** | **the Goldilocks 2-adicity ceiling** |
| **32** | **~480 GB** | **first size the swap unlocks** |

**For any prover under ~240 GB, memory binds before 2-adicity does.** The
"one doubling of headroom" is one doubling past a point that already needs a
240 GB machine — and the lane could not e2e-verify past ν=29 for exactly this
reason. The 2-adicity wall is therefore *not currently the binding
constraint for most provers*, and the paper cannot say it is.

This does not kill the observation — 240 GB servers exist, and if streaming
provers (Sparrow/Hobbit-class, which we have surveyed) push the memory wall
out, 2-adicity becomes the real wall. **But that is a conditional claim about
a future prover, and it must be stated that way.**

## What we have actually established (solid)

1. **A prime with machine-checked properties.** p = 2^61−2^54+1: primality,
   2-adicity 54, NTT-legality, maximal 3-adic inertia, the Solinas fold, the
   family law with a 67-digit counterexample, Goldilocks primality, and the
   domain-availability lemma — all kernel-checked, zero obligations. This is
   true regardless of whether anyone should use it.
2. **Measured facts**: the ceiling *mechanism* (constructs to 2^54, refuses
   2^55, at the pinned rev); a 10–40% timing observation on one machine; the
   artifact's RLWE encoding was Goldilocks-structural in two ways with unit
   tests green while decryption was garbage.
3. **Negative results**: barrel-shift capability is take-Goldilocks-or-nothing
   (with the restated theorem); Crandall primes structurally excluded; the
   NTT-in-FRI idea is novel and worthless.
4. **A corrected noise floor** (55–59 bits, from a bit-width-as-magnitude bug).

## What we have NOT established (the gates for any design-point claim)

**H1. It works at OUR parameters.** The experiment ran at Zama's shape
(D=1024, t=16, 4-bit plaintext). Our actual target — t=2^20, d=512, 8-bit
weights — has a floor of 59 bits against a 61-bit prime: **2.4 bits of
margin, untested.** The design point may simply not exist there. *This is the
single most important missing measurement.*

**H2. The tradeoff has never been measured, in either direction.** Single
prime deletes RNS-emulation cost on the proof side and deletes RNS *speed* on
the FHE side (one 61-bit software modmul vs three 32-bit-lane limbs). **We
have zero numbers for the FHE-side loss.** The entire thesis is that the
first exceeds the second, and it is unmeasured.

**H3. Is the speedup a field property or an ark-ff artifact?** Goldilocks at
exactly 64 bits is a known-awkward Montgomery case; 61 bits leaving spare
bits may be an implementation detail, not a design principle. One machine,
one library, one comparison. **A design point cannot rest on that.**

**H4. Is the headroom reachable?** Per the table above: not today, not
without ~480 GB. Needs either a streaming prover or an honest conditional.

**H5. Math prior art.** Lane running. If the family law or the Φ_m(2^b)
classification is known in math.NT, the contribution shrinks to the
application.

**H6. The framing already narrowed once.** HELIOPOLIS §6.2 and 2025/286 DO
pose joint constraint systems; what survives is "nobody runs a search" and
"2-adicity never crossed the boundary." Both are true and both are weaker
than the original claim.

## The honest current status

**We have: a well-characterized prime, a set of machine-checked certificates,
one confirmed mechanism, several corrected numbers, and a set of clean
negative results.** That is a real contribution and it is *not* a novel
design point.

**A design point requires H1 and H2 at minimum** — does it work where we
actually need it, and does the tradeoff favor it. Both are measurements, both
are days of work, and **neither has been attempted.**

Until then the correct description is: *"a candidate representation with
verified properties and an unmeasured tradeoff."* Everything stronger is
premature, and the paper should not be drafted around a claim H1/H2 might
refute.
