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

**H4. Is the headroom reachable? — ⚑ SUBSTANTIALLY RESCUED (ember, and the
arithmetic backs him).** I reasoned from the benchmark's toy end. Scaling to
the workload the field actually cares about, calibrated on Zama's own
measured point (their m=2^17×n=2^8 = 2^25-element matrices sit at ν≈30):

| workload | matrix elements | ν needed | vs Goldilocks 2^31 |
|---|---|---|---|
| one 4096² matmul (7B-class layer) | 2^24 | ~29 | fits |
| one 8192² matmul (70B-class layer) | 2^26 | ~31 | **exactly at the wall** |
| one 7B forward pass | 2^32.7 | ~38 | **exceeds by 2^6.7** |
| one 70B forward pass | 2^36 | ~41 | **exceeds by 2^10** |
| gpt-oss-120b forward (5.1B active) | 2^32.2 | ~37 | exceeds by 2^6.2 |

**A single 70B-class layer matmul already sits exactly at the Goldilocks
ceiling.** And whole-forward-pass instances exceed it by 2^7–2^10, which is
not "one doubling" — it is the difference between **~100–1000 chunked
instances that must be bound together** (Goldilocks) and **one** (p61 at
2^53). Chunk-binding is accumulation/recursion overhead paid per chunk, so
the ceiling is a *scaling* constraint: invisible on toy benchmarks,
dominant exactly when you try to prove real model inference.

**And the memory objection dissolves under the streaming provers we already
surveyed** (Sparrow measures 1.4× native space): naive ν=32 is ~709 GB, but
streaming ν=32 is **~48 GB** and ν=34 is ~192 GB. So the honest statement
is: **with a naive prover memory binds first; with a streaming prover —
which exists in the literature and is on our own queue — 2-adicity is the
hard wall, and it is hit by any real model.** That is a much stronger and
still-honest claim than the "one doubling" framing, and it is the one the
paper should make.

⚠ Still an ARGUMENT, not a measurement: the ν-calibration is a single-point
extrapolation from their benchmark, and nobody has run a streaming prover at
these sizes. H4 moves from "refuted" to "conditional on a stated,
surveyed-feasible prover property" — which is a real gate, not a fatal one.

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

## H4 addendum — the frontier-MoE stress case (Kimi K3, 2.4T)

Ember: Kimi K3 is a 2.4T MoE with many active parameters — and it is Tier-1
MXFP4-native, i.e. exactly the model class our format work targets. Running
the scaling there sharpens the claim into its correct form.

Active-parameter scenarios (K2 was ~1T/32B; larger MoEs trend to more active):

| active | ν needed | chunks @ Goldilocks 2^31 | chunks @ p61 2^53 |
|---|---|---|---|
| 31B (1.3%) | ~40 | 465 | 1 |
| 72B (3%) | ~41 | 1,073 | 1 |
| 120B (5%) | ~42 | 1,788 | 1 |
| 240B (10%) | ~43 | 3,576 | 1 |

**But memory chunks you too, and this is the honest framing:** on a ~200 GB
streaming box (ν_max ≈ 34, from Sparrow-class 1.4× native space), K3 at 5%
active needs **224 chunks from memory alone** — while Goldilocks forces
**1,788**. So the field ceiling costs **~8× more chunks than the machine
actually requires**, and every extra chunk is accumulation/binding overhead
paid per chunk.

**That is the claim's mature form.** Not "we unlock one doubling," and not
"the ceiling never binds" — but: *at frontier-MoE scale both constraints
bind, and the field ceiling multiplies the required chunk count by ~8× over
what the hardware demands. p61 removes the field term entirely, leaving
memory as the sole constraint — which is where it should be, since memory is
a hardware fact and 2-adicity is a choice nobody made deliberately.*

Two things this makes concrete:
- **The MoE and accumulation threads are load-bearing here, not adjacent.**
  Chunk-binding cost is exactly the accumulation work; the router-binding
  spec decides what a chunk must prove. The prime's value is measured *in
  units of chunks avoided*, so it cannot be evaluated without them.
- **Registry side**: committing 2.4T MXFP4 params is ~1.2 TB of one-time
  stream-hashing. Feasible with the range-streaming tool, and it is the
  scale the registry lane should eventually target — not gpt-oss-20b.

Caveat unchanged: ν is a single-point calibration from Zama's benchmark, and
the streaming-prover memory figure is surveyed-but-unmeasured. H1 and H2
remain untouched.
