# The RNS-limb route: real, small, and not architectural — plus two corrections

2026-08-13. `paper/scripts/koalabear_limb.py`, 41/41 checks, commit `e1539a9`.
Verified from scratch rather than trusting the recovered numbers.

## ⚑ Deployed vs evaluated — and I got the tone wrong in both directions

**Checked both trees.** DEPLOYED, everywhere, is **BabyBear = 2013265921 =
15·2²⁷+1**: breadstuffs `circuit/src/field.rs:3`; minidregg
`prover/src/babybear.rs:4` (`P = 2_013_265_921`, 2-adicity 27); `field6.rs` is
`BabyBear[u]/(u⁶−31)`; `Selvage/SmallField.lean:6` says *"DEPLOYED base field
is BabyBear"*; `MixedFieldBudget.lean:97` defines `babyBear := 2013265921`.

**But KoalaBear = 2130706433 = 127·2²⁴+1 is a serious EVALUATION target with
landed proofs** — `Theory/CyclotomicInertia.lean` is a whole module about it
(`orderOf_koalaBear_three_pow` and the family law), the paper's p61 is
literally *"KoalaBear one machine word up"* (same Solinas shape, same cofactor
127), and the field memo recommends migrating. My "four prose sites and zero
config sites" undersold that badly — it was true of one `Cargo.toml` and false
of the research programme.

**And the consequence for THIS lane's objection**: "a KoalaBear limb under a
BabyBear prover is the two-31-bit-primes config the seam rule forbids" is true
**today and dissolves under the recommended migration** — a KoalaBear limb
under a KoalaBear prover is exactly the aligned configuration the idea wants.
**Both primes are legal BFV limbs** (BB 2-adicity 27, KB 24, both ≡ 1 mod
8192), so the route works on whichever field we are on; **what it requires is
that the limb EQUALS the prover field.** So: conditional on the migration, not
dead — while the "real but small" verdict below (70% fixed row overhead) is
independent of which field and stands either way.

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
