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

---

# FINDINGS

## 1. The number theory reproduces. KoalaBear IS a legal limb.

All computed in `paper/scripts/koalabear_limb.py`, deterministic Miller-Rabin
(every modulus here is < 2^64, so every primality claim is DETERMINISTIC, not
probabilistic).

| claim | verdict |
|---|---|
| KB = 2^31 − 2^24 + 1 = 2130706433, prime | ✅ |
| 2-adicity(KB−1) = 24, KB = 127·2^24 + 1 | ✅ |
| KB ≡ 1 (mod 8192) — negacyclic legality at N=4096 | ✅ |
| ψ of order exactly 8192 exhibited (g=3, ψ^4096 = −1) | ✅ **constructed, not asserted** |
| KB > t, gcd(KB,t)=1, KB < 2^62 (fits the fhe.rs `Modulus` lane) | ✅ |
| Solinas fold 2^31 ≡ 2^24 − 1 (mod KB) | ✅ |
| `KB·(2^37−2^25+1)·(2^38−2^36+1)`, log₂Q = **105.5733** | ✅ exact |

**The recovered claim is correct.** KB is a legal negacyclic-NTT limb at N=4096.

## 2. ⚠ "77 towers" does NOT reproduce as a canonical number — it is search-space bound

Under the widest natural companion space (all Solinas primes `2^a−2^b+1`,
a ∈ [14,62], b ≥ 13, t < c < 2^62) there are **88 companions and 479 towers**
in the 105–112 bit band, not 77.

77 is reachable, but only by choosing an unstated companion-exponent window.
**33 distinct (window, b_min) settings in my sweep hit exactly 77**, e.g.
a ∈ [35,42] with b ≥ 13, or a ∈ [34,45] with b ≥ 20. Since the recovered
example uses a = 37 and 38, a narrow window like [35,42] is the likely
original. Scan: `hunt77.py` (scratchpad).

**Verdict on the count: the substance survives, the number does not.** The
finding is "the band is comfortably populated", and it is — by 479 towers at
the widest honest reading. Do not quote 77 without the window.

## 3. The deployed noise ledger, DERIVED and cross-checked at source

Deployed moduli pinned at source, not relayed:
`fhegg-core/src/bfv_lean.rs:72  FOLD_MODULI = [0xffff_ee001, 0xffff_c4001, 0x1_ffff_e0001]`
(also `metatheory/Bfv/Params.lean:90`, `vendor/fhe-dregg/src/bfv/parameters.rs:171`).

- log₂Q = **108.999992** (not "109" by fiat — computed from the literals)
- 2-adicities **13, 14, 17** — confirming the standing note that q0's 13
  is exactly enough for N=4096 and **not enough for N=8192**
- only `0x1ffffe0001 = 2^37 − 2^17 + 1` is Solinas; the other two are not
- t = 1032193 = **2^20 − 2^14 + 1**, itself prime and itself Solinas,
  2-adicity 14

**Cliff formula derived and confirmed against the measurement:**
`cliff = log₂Q − 1 − log₂t = 108.999992 − 1 − 19.9773 = 88.0227` — the
measured cliff is **88.02**. This is `Q/(2t)`, i.e. BFV decrypts iff
‖noise‖∞ < Δ/2. Exact.

**The ct×ct growth increment is DERIVED, not fitted:** the measured +33.0 bits
equals `log₂(2·N·t) = 1 + 12 + 19.9773 = 32.977` to **0.02 bits**. So the
measured deployed expansion is δ_R = N = 4096 — the *proven worst case*
(`negaMul_normInf_le`, proved tight in `metatheory/Bfv/Ring.lean`), not the
heuristic 2√N. Worth flagging on its own.

**ct×ct #1 is floor-dominated:** its arithmetic term would be 4.0 + 32.98 =
37.0 bits, but it measures 46.1. The floor is RNS-BV key-switching, whose
noise ∝ δ_R·(Σᵢqᵢ)·B_err. Deployed Σqᵢ = 2^37.585; the recorded worst-case
bound is 2^53.91 and the measured floor 2^46.1 sits 8.7 bits below it
(average-case ring expansion ~√N rather than N, plus σ vs 6σ) — a
CALIBRATION, named as such.

**Closed form (3 limbs, BV digits = the limbs):**

> depth-2 margin = log₂Q − log₂(Σᵢqᵢ) − 62.55 bits

Deployed: 108.999992 − 37.585 − 62.55 = **8.87 bits**, against the measured
**8.90**. The model reproduces the measurement it was not fitted to.

## 4. Lattice security — estimator VALIDATED FIRST, then applied

`paper/scripts/lattice_estimate.py`. Primal uSVP, 2016 estimate, GSA,
normal-form LWE. **Validation before any candidate number was quoted:**

| scheme | computed β | published β | Δ |
|---|---|---|---|
| Kyber-512 | 406 | 406 | 0 |
| Kyber-768 | **624** | **623** | +1 |
| Kyber-1024 | **874** | **873** | +1 |

**The shipped secret, pinned at source** (`parameters.rs:272 variance: 10`;
`secret_key.rs:43,125`; `fhe_util::sample_vec_cbd` uses `number_bits =
4·variance` and differences two `2·variance`-bit popcounts): **CBD(20),
support ±20, variance 10, σ = √10 = 3.1623**, for BOTH secret and error —
normal-form LWE. `secret_key.rs:288` asserts the ±20 support in a test.
Earlier labels "ternary" and "CBD(10)" were both wrong; this file uses the
corrected one.

| instance | log₂Q | β | core-SVP-C | MATZOV |
|---|---|---|---|---|
| deployed | 109.00 | 336 | **98.1** | 119.9 |
| KB tower (min band) | 105.00 | 355 | **103.7** | 125.5 |
| KB tower (the example) | 105.57 | 352 | **102.8** | 124.6 |
| KB tower (max band) | 112.00 | 323 | **94.3** | 116.0 |
| ternary-secret control | 109.00 | 319 | 93.1 | 114.9 |
| p61 as a single modulus | 61.00 | 763 | 222.8 | 246.3 |

**Security is a non-issue for this question, and the sign is favourable.**
Security is monotone *decreasing* in log₂Q at fixed N, so every tower at or
below 109 bits is *more* secure than deployed. The 105.57 example gains
**+4.7 core-SVP bits** over deployed. Only towers above ~109 bits lose
anything, and the worst case in the band (112 bits) costs 3.8 bits.

Two corrections this lands on our own record:
- our standing "95.5 core-SVP" for deployed is close but was computed on the
  wrong secret; on the **shipped** CBD(20) it is **98.1**, and the ternary row
  is 93.1. CBD(20) is worth **+5.0 core-SVP bits** over ternary.
- the "31 bits structurally excluded, floor ~37 bits" verdict is confirmed to
  be about a *whole modulus* and is untouched here: a 31-bit **limb** of a
  105-bit tower presents the adversary with log₂Q = 105, not 31.
