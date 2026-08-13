# The KoalaBear limb: recovering a lost result, and pricing it

2026-08-13. REVIVAL lane. A result computed by three independent lanes was
lost to a `SendMessage` failure and never written down. This file is the
handoff-rule remedy: **every number lands here as it is computed**, not at
the end.

**Status: IN PROGRESS — appended live.**

## The claim being revived

> KoalaBear (2^31 − 2^24 + 1) is a legal negacyclic-NTT limb for our BFV at
> N=4096 — prime, 2-adicity 24, KB ≡ 1 mod 8192. And 77 towers of KB × two
> Solinas companions land in the 105–112-bit noise band (example
> `KB·(2^37−2^25+1)·(2^38−2^36+1)`, log₂Q = 105.57).

**Why it is a different object from the two verdicts that surround it.**

- It is NOT refuted by "31 bits is structurally excluded as a ciphertext
  modulus, floor ~37 bits" (`two-rocks.md`). That prices a *whole ciphertext
  modulus*. A 31-bit **limb** of a 105-bit tower is a different object: the
  lattice instance sees log₂Q, not log₂q_i.
- It is NOT what H2 measured (`h2-verdict.md`). H2 priced **single prime vs
  RNS**. The limb route **keeps RNS** — three word-sized limbs, so the FHE
  side is untouched — and asks only that *one* of them equal the proof field.
  H2's own one-sentence mechanism ("affordable while it fits a machine word,
  unaffordable the moment it needs two limbs") **does not bite here at all**:
  every limb still fits a word.

So the limb route is the third option on an axis H2 treated as binary.

## Scripts

- `paper/scripts/koalabear_limb.py` — all number theory + tower enumeration +
  depth-2 ledger. Self-checking; prints PASS/FAIL per claim.
- `paper/scripts/lattice_estimate.py` — core-SVP / MATZOV estimator, validated
  against Kyber-768 and Kyber-1024 before any candidate is quoted.

(Findings appended below as they land.)
