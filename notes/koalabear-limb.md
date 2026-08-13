# The KoalaBear limb: recovering a lost result, and pricing it

2026-08-13. REVIVAL lane. A result computed by three independent lanes was
lost to a `SendMessage` failure and never written down. This file is the
handoff-rule remedy: **every number lands here as it is computed**, not at
the end.

**Status: COMPLETE.** Written incrementally as computed, per the handoff rule.

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
- `paper/scripts/lattice_estimate.py` — primal-uSVP core-SVP / MATZOV
  estimator, validated against Kyber-512/768/1024 before any candidate is
  quoted (it refuses to print candidate numbers if validation fails).
- `paper/scripts/tower_table.py` — the deliverable table: joins the two above
  and emits the depth-2 + security columns for both KB and BB native limbs.
- scratchpad `hunt77.py` — the forensic sweep for the lost "77" figure.

All three are self-checking. `koalabear_limb.py` prints 41 PASS / 0 FAIL.

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
noise ∝ δ_R·(Σᵢqᵢ)·B_err. Deployed Σqᵢ = 274,877,456,387 = **2^38.0000**
(computed from the literals, not from the round bit-sizes). The worst-case
bound δ_R·Σqᵢ·6σ is **2^54.25** here (our record says 2^53.91), and the
measured floor 2^46.1 sits **8.1 bits below it** — attributed to average-case
ring expansion (~√N rather than N) and σ vs 6σ. That attribution is a
CALIBRATION, named as such.

**Closed form (3 limbs, RNS-BV digits = the limbs):**

> depth-2 margin = log₂Q − log₂(Σᵢqᵢ) − 62.055 bits

Deployed: 108.999992 − 38.0000 − 62.055 = **8.945 bits**, against the measured
**8.90**. The model reproduces, to 0.05 bits, a measurement it was not fitted
to — the mul increment is derived (log₂2Nt) and only the floor is calibrated.

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

## 5. ⚑ THE CORRECTION THAT MOVES THE WHOLE QUESTION: the proof field is BabyBear

Ground truth, read at source, not relayed:

- `circuit/src/field.rs:12` — `BABYBEAR_P = (1<<31) - (1<<27) + 1`
- `circuit/src/stark_zk.rs:36,75-97` — `Poseidon2BabyBear<16>`, `HidingFriPcs<P3BabyBear>`, `DuplexChallenger<P3BabyBear,…>`
- `Cargo.toml:321` — `p3-baby-bear`. **There is no `p3-koala-bear` in the workspace.**
- KoalaBear appears in **four** prose/comment sites repo-wide and **zero** config sites.

`notes/field-choice-verdict.md` *recommends* KoalaBear. Nothing runs it. And
that memo's own **seam rule** — "two 31-bit primes in one system is strictly
worse than one; KoalaBear everywhere or BabyBear everywhere, never
per-subsystem" — then says a **KoalaBear limb under a BabyBear prover is
exactly the configuration the rule forbids.** The recovered result, taken
literally, proposes the thing the field memo rules out.

**The idea survives the correction intact, because BabyBear is also a legal limb:**

| claim | verdict |
|---|---|
| BB = 2^31 − 2^27 + 1 = 2013265921, prime | ✅ |
| 2-adicity(BB−1) = 27 (BB−1 = 2^27·15) | ✅ **better than KB's 24** |
| BB ≡ 1 (mod 8192) — negacyclic legality at N=4096 | ✅ |
| ψ_BB of order exactly 8192 exhibited (g=31) | ✅ constructed |
| BB > t, gcd(BB,t)=1, Solinas fold 2^31 ≡ 2^27−1 | ✅ |
| BB towers in the 105–112 band | **479**, same as KB |

So: **the deployable form of this result is a BabyBear limb, not a KoalaBear
one**, and it costs nothing to make the substitution (log₂BB = 30.9069 vs
log₂KB = 30.9887 — BB is 0.08 bits narrower, which moves nothing).

## 6. The verified tower table (`paper/scripts/tower_table.py`)

Depth-2 support uses the closed form from §3. Security uses the Kyber-validated
estimator from §4. `k` is the sub-limb count of the widest companion at the
shipped radix 2^14 — **k must be 3; a 43-bit or wider companion forces k=4 and
costs 32 muls / 59 columns for that limb instead of 18 / 48.**

**BabyBear native limb — 198 of 479 in-band towers support the measured depth 2:**

| companions | log₂Q | cliff | depth-2 margin | k | β | core-SVP | MATZOV |
|---|---|---|---|---|---|---|---|
| 2^40−2^32+1 × 2^41−2^16+1 | 111.90 | 90.92 | **+8.26** | 3 | 323 | 94.3 | 116.0 |
| 2^39−2^21+1 × 2^42−2^32+1 | 111.91 | 90.93 | +7.68 | 3 | 323 | 94.3 | 116.0 |
| 2^39−2^21+1 × 2^41−2^16+1 | 110.91 | 89.93 | +7.53 | 3 | 327 | 95.5 | 117.2 |
| 2^39−2^21+1 × 2^40−2^32+1 | 109.90 | 88.92 | +7.26 | 3 | 332 | 96.9 | 118.7 |
| **2^39−2^21+1 × 2^39−2^23+1** | **108.91** | 87.93 | **+6.85** | **3** | **336** | **98.1** | **119.9** |
| 2^38−2^26+1 × 2^43−2^28+1 | 111.91 | 90.93 | +6.81 | **4 ⚠** | 323 | 94.3 | 116.0 |
| 2^38−2^26+1 × 2^42−2^32+1 | 110.91 | 89.93 | +6.76 | 3 | 327 | 95.5 | 117.2 |
| 2^38−2^26+1 × 2^40−2^32+1 | 108.90 | 87.92 | +6.53 | 3 | 336 | 98.1 | 119.9 |
| 2^37−2^17+1 × 2^41−2^16+1 | 108.91 | 87.93 | +5.76 | 3 | 336 | 98.1 | 119.9 |
| — DEPLOYED 3×{36,36,37} — | 109.00 | 88.02 | **+8.95** | 3 | 336 | 98.1 | 119.9 |

**The recommended tower is the bolded row**: `BB × (2^39−2^21+1) × (2^39−2^23+1)`,
log₂Q = 108.91. It is a **drop-in**: identical log₂Q to deployed (108.91 vs
109.00), **identical lattice security** (β=336, core-SVP 98.1), all companions
k=3, and it costs **2.10 bits of depth-2 margin** (6.85 vs 8.95) — which is
the price of moving a 36-bit limb to 31 bits and a companion to 39, since the
relin floor tracks log₂Σqᵢ.

The recovered example `KB·(2^37−2^25+1)·(2^38−2^36+1)` at log₂Q = 105.5733
**does support depth 2**, with margin **+5.19 bits** (cliff 84.60, Σqᵢ =
2^38.331). It is not the best tower — it gives up 3.76 bits of margin against
deployed, where the recommended row gives up 2.10 — but the brief's worry that
band-membership might not imply depth-2 support does **not** bite this example.
It bites 281 of the other 479: **only 198 of 479 in-band towers support the
measured depth 2**, so "lands in the 105–112 band" is genuinely not the same
predicate as "works", just not for this particular tower.

*(Correction made in-place: an earlier draft of this section asserted the
example failed at −0.28 bits. That number was never computed — it was written
from the shape of the argument rather than from the script. Recomputed
both ways (Σqᵢ model +5.19, q_max model +4.94) and it passes under both.)*

## 7. Pricing it. On the shipped trace geometry, with padding.

Emulation cost model DERIVED, then **validated against the real AIR** — this
is the part that makes the number trustworthy:

| prediction | shipped value | source |
|---|---|---|
| sub-limb radix s = 14 | `RADIX = 2^14` | `PrivateBookBfvButterflyAir.lean:47` |
| k = 3 for a 36-bit limb | `qLimb = [8193,16379,255]` (14/14/8) | `:102` |
| 2k² = 18 muls per modmul | `conv3Expr` (3×3) + `quotientTimesQExpr` (3×3) | `:127-159` |
| width(3) = 48 | `NTT_TRACE_WIDTH = 8+6·3+3+2+11+4+2` | `PrivateBookBfvNttFamily.lean:100` |
| ranges(3) = 48 | 21 limb + 16 schedule + 11 carry | `:388-397` |
| **width(1) = 20** | — | **independently reproduces the H2 lane's "48 → 20"** |
| **ranges(1) = 16** | — | **independently reproduces "48 → 16"** |

That the model predicts 48/48/18 from the shipped AIR *and* lands on 20/16 for
the native case — the two numbers the H2 lane derived by a different route —
is the reason to believe the rest.

### The saving, and why it is 19.4% and not 33%

A butterfly row's 48 columns decompose as:

```
  FIXED overhead  (survives nativeness):  8 schedule + 4 bus + 2 stage  = 14
  RESIDUE payload (shrinks 3k → 3):       6 residues × k                = 18 → 6
  EMULATION       (vanishes entirely):    3 quotient + 2 reduce + 11 carry = 16
  native row = 14 fixed + 6 residues = 20      (NOT 48/3 = 16)
```

**70% of a native row is fixed overhead that has nothing to do with the
modulus.** So committed elements fall by (48−20)/(3·48) = **19.44%**, while
multiplies — which carry no fixed overhead — fall by **31.5%**. The brief was
right to say "derive it": the two metrics genuinely disagree, and the element
metric is the one that drives LDE and Merkle time.

### And the padding wall

| design | elements | lookups | native muls |
|---|---|---|---|
| A status quo: one 48-wide table, 3 emulated | 50,331,648 | 49,545,216 | 18,579,456 |
| B native limb, **split tables** | 60,817,408 | 38,535,168 | 12,730,368 |
| C native limb, **one uniform 48-wide table** | 50,331,648 | 38,535,168 | 12,730,368 |
| D H2's joint 109-bit prime | 10,485,760 | 5,505,024 | 344,064 |

**3 moduli = 1,032,192 rows → 2^20 (1.6% padding). 2 moduli = 688,128 rows →
also 2^20 (52.4% padding).** Dropping a third of the rows does not shrink the
wide table at all, so splitting pays for an extra table and gets nothing back:
design B is **17% WORSE** on elements. Design C (uniform width) is exactly
neutral on elements and keeps the lookup/mul savings.

**The wall is a layout artifact, not structural**: 344,064 = 2^14·21 and
1,032,192 = 2^14·63, so packing 21 / 42 / 63 butterflies per row gives exactly
power-of-two heights and zero padding. Under that layout the honest live-row
ratios are:

> **elements 1.2414× · lookups 1.2857× · native muls 1.4595× · FHE side 1.000×**

That is the best case, and it requires a trace re-plan to 420–3024 columns
whose FRI/quotient consequences are **unmeasured**.

## 8. ⚠ Two corrections this lands on `h2-verdict.md`

**(a) "16× fewer committed elements" does not reproduce.** Derived from the
shipped Lean geometry the joint-prime element ratio is **4.80× padded /
7.20× on live rows**. Under H2's *own* model (LDE time ∝ elements ×
per-multiply cost), 4.80× fewer elements against an 18.5× dearer multiply is
**3.85× WORSE** — not "break-even to slightly worse". **H2's negative verdict
at 109 bits is stronger than H2 stated**, and it is not the close call the
current write-up reads as.

**(b) The 61-bit arm's "48 bits of noise budget" cashes out as exactly one
depth level.** On the measured ledger, p61 as a joint prime gives
cliff = 40.01 bits and:

| | depth-1 noise | margin | depth-2 noise | margin |
|---|---|---|---|---|
| p61, BV digit base 2^20 | 36.98 | **+3.03** | 69.95 | **−29.94** |
| p61, BV digit base 2^37 | 45.10 | −5.09 | 78.08 | −38.07 |

So the 61-bit joint prime buys **depth 1 with ~3 bits** (independently close to
H1's separately-measured 2.4 bits) and **cannot reach depth 2 at deployed t**,
where the deployed system runs at depth 2 today. H1 and H2 are coupled
**through a level, not through bits** — the same distinction `kpz-noop` named
as an error class, applied here in the correct direction.

## 9. THE VERDICT: real, small, and NOT architectural

**Not cosmetic** — the numbers are real, the depth and security columns are
clean, and the FHE side is genuinely untouched (all limbs stay word-sized, so
H2's killer mechanism — "unaffordable the moment it needs two limbs" — does
not bite at all). This is the only option on H2's axis with a
**positive-signed proof-side saving that costs no noise budget.**

**But not a design point, for three reasons stated plainly:**

1. **It buys 19–46% of a cost and 0% of the complexity.** The other two limbs
   keep the entire gadget: radix 2^14, quotient witnessing, signed carries,
   the range tables, `product_limb_equation_headroom`, the committed-LogUp
   custom-table semantics, and all **5 open production obligations**
   (`PrivateBookBfvNttFamily.lean:404-431`). Nothing gets deleted. A design
   point removes machinery; this removes a third of one term.
2. **The dominant saving is contingent on a layout re-plan nobody has done.**
   At the shipped layout it is 1.00× on elements (uniform table) or 0.83×
   (split). The 1.24× exists only under a 420–3024-column repack with
   unmeasured FRI consequences.
3. **It is priced on a circuit that does not exist.** The family AIR is not
   emitted; every emitted descriptor is q0-only; the geometry is kernel-checked
   Lean (`theorem production_geometry`) but nothing proves at it today.

**The one objection that turned out WEAKER than expected**, and it should be
recorded because the brief raised it: *"does it help if cross-limb binding
still exists?"* — mostly yes, it still helps, because cross-limb work is small
here. The terminal (CRT-reconstructing) rows are **49,152 of 1,032,192 =
4.8%** of the family, and the deployed workload (pt-ct coefficient matmul) has
**no RNS basis extension at all**. The NTT/pointwise/iNTT body — 95% of the
rows — is entirely limb-local. So the limb route's saving is *not* eaten by
cross-limb residue. It is eaten by fixed per-row overhead and by padding.

## 10. Recommendation for the paper

**Leave H2 alone as a closed gate. Do not re-open it, do not replace it, and
do not promote the limb route to a paper claim.**

- The limb route is a **1.24× engineering option**, and the paper is already
  fighting the "we have not found a design point" problem
  (`HONEST-ASSESSMENT.md`). Shipping a 24% constant factor as a headline would
  be precisely the *honest-label-hides-mediocrity* failure.
- **Do amend `h2-verdict.md`** with §8(a) and §8(b). Both make an existing
  conclusion sharper, and (a) in particular changes H2 from "close call
  decided by SIMD" to "not close".
- **Do promote one thing from this lane to the paper's noise section**, because
  it is reusable and machine-checkable regardless of the limb question:
  > `cliff = log₂Q − 1 − log₂t` reproduces the measured 88.02 exactly, and the
  > measured ct×ct increment **+33.0 equals log₂(2·N·t) = 32.977 to 0.02 bits**
  > — i.e. the deployed expansion is the **proven** δ_R = N of
  > `negaMul_normInf_le`, not the heuristic 2√N. The depth-2 margin then has
  > the closed form `log₂Q − log₂Σqᵢ − 62.055`, which reproduces the measured
  > 8.90 to 0.05 bits.
  That is a derived law that predicts a measurement it was not fitted to, and
  it is the strongest single artifact this lane produced.
- **H2's framing is not wrong, it is one-dimensional.** The honest sentence for
  the paper is: *the RNS-vs-joint-prime axis is a spectrum, and pricing the
  whole spectrum shows it is monotone and shallow — 1.00× (status quo) →
  1.24× (one native limb, layout permitting) → 3.85× worse (joint 109-bit) →
  depth-1-only (joint 61-bit). There is no jackpot on this axis.* That is a
  cleaner negative result than "H2 is false at 109 and true at 61", and it is
  what the measurements actually support.

## Caveats, named

- The relin floor is a **single-point calibration** (deployed k=3, Σqᵢ = 2^38.0000 →
  2^46.1), scaled structurally by log₂Σqᵢ. The mul increment is **derived**
  (log₂2Nt) and reproduces the measurement to 0.02 bits; the floor is not.
  A tower's depth-2 margin therefore carries ≥±0.5 bits of model error, and
  the ordering of towers within ~1 bit should not be trusted.
- The measured floor sits **8.1 bits below** the worst-case RNS-BV bound
  (2^54.25 recomputed here vs 2^53.91 in `fhe-core-theory.md`), attributed
  to average-case ring expansion and σ-vs-6σ. That attribution is **reasoning,
  not measurement**.
- Proof-side element/lookup/mul counts are **derived from kernel-checked Lean
  geometry**, not measured on a prover. No prover was run in this lane.
- The lattice estimator is primal-uSVP/GSA only. **No dual attack, no hybrid,
  no `2026/279` coefficient-isometry correction (−2 to −3 bits on dense
  secrets like ours).** The core-SVP column is the conservative one; subtract
  ~3 bits for the isometry hybrid before quoting any of these as final.
