# The RNS-limb route: real, small, and not architectural — plus two corrections

2026-08-13. `paper/scripts/koalabear_limb.py`, 41/41 checks, commit `e1539a9`.
Verified from scratch rather than trusting the recovered numbers.

## ⚑ The finding that corrects a week of my phrasing

**The proof field is BabyBear, not KoalaBear.** `circuit/src/field.rs:3` says
so; `Cargo.toml` has zero `koala` hits. **KoalaBear appears in four prose
sites and zero config sites.** The field memo's "KoalaBear everywhere" is a
**recommendation we have not executed**, and I have been writing "our
KoalaBear parameters" as though it were our state.

The idea survives the substitution intact — **BabyBear is itself a legal limb**
(2-adicity 27) — and only the name changes. But a KoalaBear limb under a
BabyBear prover would have been **exactly the two-31-bit-primes configuration
the field memo's own seam rule forbids.** Worth having caught before building.

## Verified, and one number that doesn't reproduce

Legality confirmed by *exhibiting* a root of order exactly 8192 rather than
asserting one. The named example lands at log₂Q = 105.5733 exactly.
**"77 towers" does NOT reproduce** — the honest search space gives **479**,
and 33 different unstated companion-exponent windows hit exactly 77. Substance
survives; the number was an artifact of an unstated window.

## ⚑ The depth-2 law — derived, not fitted, and it predicts

- The cliff `log₂Q − 1 − log₂t` **reproduces the measured 88.02 exactly**.
- The measured **+33.0-bit ct×ct increment equals `log₂(2Nt)` to 0.02 bits** —
  ⚑ **so the deployed expansion is the PROVEN δ_R = N, not the heuristic
  2√N.** That is direct evidence that the bound `Bfv/Ring.lean` proves tight
  is the bound the deployed system actually pays.
- The margin closed form reproduces the measured 8.90 to 0.05 bits.
- **198 of 479 in-band towers support depth 2.** Recommended drop-in:
  `BB × (2^39−2^21+1) × (2^39−2^23+1)`, log₂Q = 108.91, identical security,
  costs 2.10 bits of margin.

**This law predicts a measurement it was not fitted to** — the strongest
artifact the lane produced, and it belongs in the paper's noise section.

## Security, corrected

Estimator validated against Kyber first (406/624/874 vs published
406/623/873). **On the shipped CBD(20) the deployed instance is core-SVP
98.1, not our recorded 95.5** — that row was ternary (which is 93.1).

## The verdict: real, small, not architectural

The lane's emulation model predicts radix 2^14 / k=3 / 18 muls / width 48 /
48 ranges — **all four are the shipped Lean values** — then predicts width 20
and 16 ranges native, **independently reproducing the two numbers the H2 lane
derived by a different route.** Best case: **1.24× elements, 1.29× lookups,
1.46× muls, FHE side 1.00×.** Not ⅓, because **70% of a native row is fixed
schedule/bus overhead.**

It buys 19–46% of one cost and **0% of the complexity** (the gadget survives
for the other two limbs), and the dominant saving needs a trace re-plan since
688,128 rows pad to the same 2^20 as 1,032,192.

**Recommendation: leave H2 closed; do not headline the limb route.** Amend H2
with the two corrections and promote the depth-2 law to the paper.

## Process note the lane volunteered

It asserted the recovered example failed depth 2 at −0.28 bits **from the
shape of the argument rather than from the script**; it actually passes at
+5.19. Corrected in place with the miss recorded. That is the same class as
my own relay failure on Poseidon2 — reasoning about what a computation *would*
say instead of running it.
