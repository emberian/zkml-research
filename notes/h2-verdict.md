# H2 CLOSED: the thesis is false at 109 bits, true at 61 — and it now depends on H1

2026-08-13. Measured both directions on an M2 Max, min-of-40, ratios stable
±5% across three whole-program runs, with validation gates (both NTTs checked
against schoolbook negacyclic convolution; fhe-math's own operator timed
alongside so the baseline is not a strawman — ours is 22–28% *slower*, i.e.
conservative against the single-prime side). Artifact:
`phase0/h2-rns-vs-single-prime/`.

## The one-sentence mechanism

**A joint field is affordable while it fits a machine word and unaffordable
the moment it needs two limbs — because the 2-limb penalty is paid on the FHE
side and the proof side simultaneously.** 61 fits. 109 does not. **The
deciding variable is the machine word, not the number of primes.**

## (A) FHE side — the penalty is MUCH smaller than we assumed

Not "3–4×". A single 109-bit modmul is 3.5–3.9× a 36-bit one, **but you do
three of the 36-bit ones**:

| op | RNS 3-limb | single 109-bit | ratio |
|---|---|---|---|
| Shoup modmul | 3 × 0.737 ns | 2.75 ns | 1.16–1.30× |
| forward NTT N=4096 | 80.5 µs | 95.7–98.3 µs | 1.13–1.22× |
| **ct+ct add, reduced (our deployed fold path)** | 2.34 µs | 5.09 µs | **2.18×** |
| ct+ct add, lazy (available to both) | 1.71 µs | 1.51 µs | **0.88×** |
| **general 2-operand modmul (ct×ct tensor)** | — | — | **0.44–0.55× — single-prime WINS** |
| ciphertext in RAM | 98,304 B | 65,536 B | **0.67× — WINS** |

The one bad case is our *deployed* reduced-add fold, because u64 adds
auto-vectorise on NEON and u128 adds do not — **and it is repairable**: 109
bits in u128 leaves 19 spare bits, so a ≤512-add fold with lazy accumulation
runs at 0.88×.

⚠ **Do not carry that 0.88× forward as "lazy accumulation is free."** It is a
*column* ratio (single-prime-109-bit lazy ÷ RNS-3-limb lazy), and measured
in-tree the lazy fold is 0.84× at B=256 but **break-even at the deployed B=4**
(`notes/fold-as-opening.md` §6). Several notes cited this cell for a claim it
does not make.

## (B) Proof side — real in ELEMENTS, evaporates in TIME

Ground truth read from the emitted descriptors (not relayed): all four row
categories of the 98,304-equation family carry `RNS_MODULUS_COUNT = 3`, so
single-prime gives 344,064 live rows ⇒ **2^19 padded, exactly one power of
two**. Width 48 → 20; range checks 48 → 16 (all 21 limb + 11 carry ranges
vanish with the limbs).

**16× fewer committed elements × 18.5× dearer per multiply ≈ break-even to
slightly worse.** Against a NEON-packed BabyBear prover — *what Plonky3
actually runs* — single-prime at 109 bits is **1.11–1.53× SLOWER**, robust
across every range-enforcement model. At 61 bits it is **1.8× FASTER**,
because the field still fits a word and the emulation deleted is *larger*
(5 limbs, not 3).

## (C) ⚑ The asymmetry I briefed is measured, and it does NOT decide

I hypothesised that "FHE cost is paid on 100% of work while proof saving is
paid on the sampled fraction" might decide the question. **Measured: it does
not.** Proving one FHE op costs **≥618× (packed) / 1639× (scalar)** performing
it, so at proving fraction f=1 the entire FHE-side penalty — including the bad
2.18× add — moves the total by **0.19%**. **H2 is decided entirely by the
proof side.** A negative result about the *question*, and it means the
FHE-side half that was missing turns out not to be load-bearing at the design
point. Worth knowing before anyone spent more days on it.

(Proving fraction today is 1/98,304 = 1.0e-5 — one to two orders below every
crossover; the family AIR's design target is 1.0.)

## ⚑ What this does to the paper

> **A single ~109-bit joint prime is a net loss** (1.2–2.2× worse FHE, 1.1–1.5×
> worse proving against a SIMD prover). **No sampling rate rescues it.**
>
> **A single 61-bit joint prime is a net win on both sides** — but only by
> shrinking log q from 109 to 61, i.e. **spending 48 bits of noise budget.**

**Therefore H2's answer is conditional on H1 in a way nobody had stated.**
With H1's measured 2.4 bits of margin at our target (t=2^20, d=512, 8-bit
weights), **the design point exists if and only if H1 holds — and H2 can no
longer be cited as independent support for it.** The paper's two gates are
not independent; one is downstream of the other.

## ⚑ Correction to our reading of the earlier p61 experiment

H3 side-probe: **61-bit vs 36-bit in the same u64 lane is 1.00–1.02×** for
Shoup mul and 0.97–1.02× for the NTT. **Modulus size is free up to 62 bits.**
So the p61-vs-Goldilocks 10–40% result is *not* "61 bits is intrinsically
faster than 36" — it is **64-exactly vs having spare bits**, which is exactly
H3's worry (is the speedup a field property or an ark-ff/Montgomery artifact).

## Incidental, verified

**2^109 − 2^65 + 1 is prime with 2-adicity 65**, and 2^109 − 2^58 + 1 with
2-adicity 58 — the p61 family law extends to 109 bits with a Solinas fold and
an enormous smooth subgroup. It does **not** save the 109-bit design
(measured: the Solinas prime was no faster than a generic 109-bit prime in the
NTT — the cost is the 2-limb width, not the reduction), but the family-law
claim gains a data point.

## ⚑ Two corrections from the limb lane (independent derivation, both sharpen this)

1. **"16× fewer committed elements" does not reproduce.** Derived
   independently it is **4.80× padded** — which, run back through H2's own
   model, makes the 109-bit joint prime **3.85× worse, not break-even.** The
   verdict hardens; the number was too generous to the losing side.
2. **The 61-bit arm's "48 bits of noise budget" cashes out as exactly ONE
   DEPTH LEVEL** (+3.03 bits of margin at depth 1, −29.94 at depth 2). That
   is the concrete price, and it is the crispest statement of the H1
   dependency: **the 61-bit design point costs one multiplication of depth.**

## Named caveats

Proof-side numbers are **derived, not measured** (trace geometry from emitted
descriptors, per-mul costs measured, model = LDE time ∝ elements × per-mul;
hashing/FRI/logup-inverse not separately modelled — they push the same way but
the mix is unmeasured). The 20-column native width is the lane's construction,
and conservative. The box was contended, so absolute microseconds are upper
bounds — every conclusion is a ratio. **Nothing here touches noise budget;
log q 61 vs 109 is H1 and untouched.**
