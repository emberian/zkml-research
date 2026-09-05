# The inert cyclotomic tower — Z[ζ_{3^8}]/(2^64) = GR(2^64, 4374) — priced

2026-09-04. Mathematics + pricing lane for the joint-algebra question (`swarm/ASTRA-ALGEBRA-PROMPT.md`).
The candidate answers `notes/galois-ring-stack.md` §2's obstruction (the negacyclic ring mod 2^k is local
with residue field F_2, so exceptional sets have size ≤ 2) by changing the conductor: O = Z[X]/(Φ_{3^8}),
Φ = X^4374 + X^2187 + 1, ord_6561(2) = 4374, so O/(2^k) ≅ GR(2^k, 4374) with residue field F_{2^4374};
fixed-weight sets A_h = {Σ_{j∈S} ζ^j : |S| = h} have unit pairwise differences, |A_16| ≈ 2^149.2, and the
subring tower GR(2^k,162) ⊂ … ⊂ GR(2^k,4374) via η = ζ^27 carries the challenges (|A_60| ≈ 2^150.1).
Those algebraic facts are the external model's, checked by `scratchpad/joint_algebra_checks.py` (re-run
here: PASS) and extended in **`notes/galois-scripts/inert_tower.py`** (every derived number below; ~10 s;
exhaustive at conductors 27 and 81). Read at source: LPR toolkit 2013/293, Ducas–Durmus 2012/235, PRS17
2017/258, Peikert 2016/351, ABD 2016/127, NTRU Prime 2016/461, Ducas–Engelberts–de Perthuis 2025/1904,
HE Security Standard v1.1 Table 1, LatticeFold 2024/257, LatticeFold+ 2025/247, Cyclo 2026/359, Lova
2024/1964, Albrecht–Lai 2021/202, Lin–Xing–Yao 2023/150, Sailor (UPC thesis 2024); tree notes
`h2-verdict`, `fhe-core-theory`, `galois-ring-stack`, `zq-sumcheck`, `acc-rbr-fold`, `ring-hash-design`,
`sis-lattice-verdict`; `minidregg/Theory/CyclotomicInertia.lean`. Kagi: 6 queries (§6). The lattice estimator
(`~/src/lattice-estimator`, cloned) needs Sage; §1.4 is an own primal-uSVP model calibrated to the standard's row.

## 0. Verdict in three lines

1. **The obstruction is genuinely dissolved — cheaply where the FHE ring lives, ruinously where the proof
   lives.** The ciphertext ring *itself* is a Galois ring with a 2^4374-element strong sampling set, so an
   Ajtai commitment to a BFV ciphertext folds with LatticeFold's requirements met (§3) and the rescale is a
   44-bit shift. But every proof message that is not a challenge is a *dense* element of GR(2^64,162):
   1,296 B and 4,323 u64 mults per product vs BabyBear-Ext4's 16 B and 9–16 — **270–480× per
   multiplication, a bilinear-complexity floor of 20×, 65 GB of round-2 sumcheck tables at v = 25** (§2).
   Challenge sparsity saves ≤ 2× on the fold step only. It is galois-ring-stack's 1/64 law (here 1/69)
   with a bigger residue field: the field made it *sound*, not cheaper.
2. **Folding works with the right extractor.** A_h is a strong sampling set with exact expansion factor
   2h, so LatticeFold/LatticeFold+/Cyclo (relaxed binding, no division) hold at |A| = 2^149, T = 32, MSIS
   at 8TB = 2^24; the no-wrap budget is 2^42 folds (2^40.1 in the subring) — the tree's additive
   recurrence with γ = 32/120 for 1. **Short inverses do not exist**: AL21 Thm 2 / Prop 12 [READ] bound
   subtractive sets over Z[ζ_{p^ℓ}] by p = 3, and every equal-weight difference has 3 | N(δ), so a
   dividing (Schnorr/Lova-style) extractor gets knowledge error 1/3 or a slack in ⟨1−ζ⟩. The integer slack
   3 is a **unit mod 2^64** — galois-ring-stack §2's 2-adic bleed is gone — at norm ×2m ≈ 2^13.7 per level.
3. **FHE at q = 2^64 here is standard, secure, one level shallower, NTT-less**: prime-power cyclotomics
   are the LPR toolkit's own case; ≈ 230–260 bits classical (over-provisioned ~110 bits: the 3-power
   ladder has no 2048–3000 rung); depth 1 at ≈ +4.9 bits vs deployed depth 2; ct×ct = 768k single-
   instruction u64 mults vs 233k Shoup modmults — 1.3–2.2× slower, and h2 measured the FHE side at
   0.19 % of the total. Module-BKZ's odd-conductor gain (2025/1904) prices at ≈ −17 blocksize ≈ −5 bits.
   **TRAP as the single substrate; REAL for the commit-to-ciphertext leg and three by-products** (§5).

## 1. FHE over conductor 3^8 at q = 2^64 (and 2^109)

**1.1 Standardness [READ].** LPR toolkit Def 4.1: *"For a prime power m, define p to be the power basis
(ζ_m^j)_{j∈[φ(m)]}"* — the powerful basis *is* the coefficient basis; Lemma 4.3: s₁ = √m̂ = 81,
s_n = √(m/rad m) = √2187 (m̂ = m, m odd), condition number √3 [DERIVED] — coefficient-embedding noise
bounds lose ≤ √3 against canonical. HElib supports general m (2025/1904 l.239); Ducas–Durmus remove R^∨ at
general cyclotomics with *"only a very slight increase in the magnitude of the noise"* [READ abstract];
PRS17: *"decision Ring-LWE with any number field and any modulus"* [READ] — the inert modulus needs no
splitting hypothesis. **[OURS]** `Theory/CyclotomicInertia.lean:537 orderOf_three_pow_of_mod_nine
(hx : x % 9 = 2 ∨ x % 9 = 5) (k) : orderOf (x : ZMod (3^(k+1))) = 2·3^k` at x = 2, fed to
`:159 irreducible_cyclotomic_of_orderOf_eq_totient`, yields `∀ k, Irreducible (cyclotomic (3^(k+1))
(ZMod 2))` — GR(2^k, 2·3^j) at every rung, a one-line corollary nobody has written; the Galois-ring
carrier is still absent from Mathlib (galois-ring-stack §1). `fhe-scout-verdicts.md:32` [OURS]: fhe.rs has
no non-power-of-two cyclotomics — this ring is a new library, not a parameter.

**1.2 Multiplication cost [DERIVED, script §1].** Coefficients live in Z/2^64: each product is the *low*
64 bits of a 64×64 product — one `mul`, no 128-bit lane, no reduction; adds wrap (this corrects
galois-ring-stack §2's 64×64→128 accounting in the candidate's favour).

| route | op count | op class | note |
|---|---|---|---|
| Karatsuba (unbalanced, cutoff 1), N = 4374, + Φ-reduction (6,560 adds) | **768,273 mults, 5.89 M adds** | u64 low-mul, wrapping add | 4374 = 2·3^7 has one even split: 1.45× the 3^12 = 531,441 of N = 4096 |
| Karatsuba once, then Toom-3 ×7 | 234,375 mults | exact ÷2 → 66-bit intermediates | not in u64 lanes; u128 interpolation unmeasured |
| radix-3 CRT-NTT, length 6561 (Φ ∣ X^6561−1, wrap harmless), 3 primes ≡ 1 (mod 6561) | 492,075 modmults | ~50-bit Shoup | 2.11× the 3-limb count; re-imports prime limbs inside the multiplier (zq-sumcheck Hole-A shape) |
| deployed 3-limb RNS-NTT, N = 4096 (h2-verdict) | 233,472 modmults | Shoup, 0.737 ns measured | 3·(2·24,576 + 4,096) per limb |
| negacyclic Karatsuba, N = 4096, Z/2^64 | 531,441 mults | u64 | galois-ring-stack §2 |

Time bracket [DERIVED, unmeasured; NEON has no u64 lane multiply]: 768k × 0.3–0.5 ns = **230–384 µs** vs
233k × 0.737 ns = 172 µs → **1.3–2.2× slower**. At q ≈ 2^109 words are u128 (3–4 mults each): ≈ 2.7 M
u64-equivalents, 11–16× the NTT. Ciphertext bytes 2·4374·8 = 69,984 vs 98,304 (3 limbs) vs 65,536
(packed 109). **Not load-bearing**: h2-verdict (C) *"Proving one FHE op costs ≥ 618× performing it …
the entire FHE-side penalty moves the total by 0.19 %"* [READ].

**1.3 Noise and levels [DERIVED from h2-verdict + fhe-core-theory, script §3].** Limb lane, 61-bit arm:
*"+3.03 bits of margin at depth 1, −29.94 at depth 2"* [READ]; a level costs 33–42 bits [READ]. Three
more bits of q: +6.03 / −26.94. Ring correction: provable δ_R ≤ 2N = 8748 (monomial op-norm 2, exact —
script §6) vs negacyclic δ_R = N = 4096 proved tight in `Bfv/Ring.lean` [OURS] — +1.09 bits/level.
**Depth 1 at ≈ +4.9 bits; depth 2 fails by ≈ 29 bits; deployed depth 2 → one level fewer.** Gifts at
2^64: Δ = 2^44 exactly, r_t(q) = 0 (the KPZ term fhe-core-theory found already absent), rescale =
`(x + 2^43) >> 44` (galois-ring-stack §6's Hole-B-as-range-check, verbatim). At 2^109 the −2.2 bits of
ring correction meet a deployed depth-2 point whose tightest measured margin is 2.4 bits (h2's H1
figure) — a coin-flip on paper; measure. `deployed_ring_depth` (T = 42 at 109 bits [OURS]) is un-rerun.

**1.4 Security at n = 4374, log q = 64.** Instrument: own primal-uSVP core-SVP model (ADPS16 success
condition, Bai–Galbraith secret scaling, GSA δ(β); script §4), **calibrated** to HE Standard v1.1 Table 1
(BKZ.sieve) [READ]: ternary, n = 4096: 128-bit ↔ log q 109 (the deployed row), 192 ↔ 75, 256 ↔ 58;
n = 2048: 128 ↔ 54. My model gives β = 327 → 0.292β+16.4 = 111.9 at the 128-bit row: **16 bits more
pessimistic** than the standard's instrument; both columns shown.

| point | β | 0.292β | +16.4 (sieve) | calibrated (+16) | HE-standard interpolation |
|---|---|---|---|---|---|
| n 4096, log q 109, ternary (calibration) | 327 | 95.5 | 111.9 | 128 | 128.1 [READ] |
| n 4096, log q 64, ternary | 687 | 200.6 | 217.0 | ≈ 233 | ≈ 230 (between 75→192, 58→256) |
| **n 4374, log q 64, CBD(20) (deployed secret)** | **780** | **227.8** | 244.2 | ≈ 260 | — |
| n 4374, log q 64, ternary (fhegg shares) | 749 | 218.7 | 235.1 | ≈ 251 | — |
| n 4374, log q 109, CBD(20) | 369 | 107.7 | 124.1 | ≈ 140 | — |

Over-provisioned by ~110 bits, and the ladder is coarse: φ(3^7) = 1458 sits below the n = 2048 row (128
↔ log q 54) and is insecure at 64 bits [DERIVED from the table]; no rung lands near the 2048–3000 that
log q = 64 wants. **Odd-conductor attack surface, four legs [READ]:**
- *Subfield attacks* (ABD): *"the presence of a subfield to solve overstretched versions of the NTRU
  assumption"*, faster *"as soon as q is super-polynomial"* — norms an NTRU key down a subfield; BFV has
  none (public/relin keys are RLWE samples). log q = 64 > 2.484·log₂ 4374 = 30 is NTRU-overstretched, so
  **no NTRU-shaped object in this ring** [DERIVED]. Power-of-two conductors have the same subfield tower.
- *Non-dual weak instances* (ELOS/CLS): Peikert 351 §4.4 — *"the dual ideal R^∨ contains many rather
  short nonzero elements … distinguishing attack … for narrow enough spherical Gaussians"*: error-too-
  small, absent at σ = 3.2 with the toolkit's dual handling. Not a conductor property.
- *NTRU Prime*: *"prime-degree large-Galois-group inert-modulus"*; *"NTT-friendly primes are never
  inert"*; *"taking subfields and automorphisms away from the attacker"*. This candidate satisfies the
  inert half and **violates the subfield half by design** — the challenge subring *is* the tower
  Q(ζ_{3^j}). Their hedge (Kronecker–Weber, *"we do not think that it is wise to rely on this"*) is a
  stance, not an attack.
- *Module-BKZ* (2025/1904 eq. (1)): β_eq = β + ln(|Δ_K|/d^d)·β/(d ln β)(1+o(1)) + d − 1; the term
  vanishes for power-of-two conductors and gives *"a subexponential speedup"* otherwise. Thm 9 [Was82
  2.7]: |Δ| = 3^32805 at c = 3^8 [DERIVED] → ln(|Δ|/d^d)/d = −0.144 → at β = 780 **Δβ ≈ −17 ≈ −4.9 bits**.
  Their caveat (l.241): coefficient-embedding schemes *"would require special consideration (see Open
  Question 5)"*. This prices `sis-lattice-verdict.md`'s "unpriced bill" [OURS] to first order.

If we do not control the FHE modulus (VERDICTS §7.3): BFV stays RNS over X^4096+1 and this ring offers
the FHE object nothing; the proof side can still use GR(2^64,162) challenges over Z/2^64 witnesses, but
the ciphertext re-enters as three prime limbs to emulate (galois-ring-stack §6, unchanged).

## 2. Dense extension arithmetic

Sparse challenges do not keep messages sparse: after round 1 every folded table entry and every round
polynomial coefficient is a *dense* element of the challenge ring. Counts (script §2; unbalanced
Karatsuba; Φ_243 = X^162 + X^81 + 1 reduction = 242 adds):

| element | bytes | dense×dense u64 mults (schoolbook / Karatsuba) | adds |
|---|---|---|---|
| BabyBear-Ext4 (deployed) | 16 | 16 / 9 (u32) | ~30 |
| Z_Q + Ext4 (zq-sumcheck §6) | 55 | 48 limb-mults | — |
| GR(2^64,107) (galois-ring-stack §1) | 856 | 11,449 / 1,981 | 14.5k |
| **GR(2^64,162) (this candidate)** | **1,296** | **26,244 / 4,323** | 31.7k |
| GR(2^64,4374) (ambient) | 34,992 | 19.1 M / 768k | 5.9 M |

- **Per-multiplication tax 270× (vs schoolbook Ext4) to 480× (vs Karatsuba Ext4)** [DERIVED]. Floor: a
  degree-162 algebra over a field needs ≥ 2·162 − 1 = 323 bilinear multiplications (Winograd; recalled),
  and any Z/2^64 algorithm reduces mod 2 to one over F_{2^162}: **no multiplier beats 20×**. Sailor
  (l.975 [READ]): *"having the irreducible polynomial … be a sparse polynomial, we can compute a
  multiplication of two elements in GR(p^k, n) in time O(n log n)"* — asymptotic FFT; at n = 162 a
  Kronecker/GMP product (≈ 344 limbs, Toom-4) lands near the 4.3k count [INFERRED].
- **Dense × sparse** (weight 60, stride-27 monomials in the subring basis): 60 shifts × (162 moves + 162
  reduction subs) = **19,440 add-class ops, 0 mults** — about half a Karatsuba product (4.3k mults +
  31.7k adds). Sparsity buys ≤ 2× on the fold, nothing on the round-polynomial products.
- **Sumcheck at zq-sumcheck's worked point (v = 25, deg 3)** [DERIVED]: rounds 2..25 hold Σ 2^{v−i} =
  2^24 − 1 cells × (deg+1)(deg−1) = 8 products = **1.34·10^8 dense products = 5.80·10^11 u64 mults** vs
  **1.2–2.1·10^9 u32 mults** for BabyBear-Ext4 (round 1 is base-ring in both: 1.34·10^8). Tables after
  round 1: 3 × 2^24 × 1,296 B = **65 GB** vs 0.8 GB. Per round i ≥ 2: 2^{25−i} × 8 × 4,323 mults +
  3 × 2^{25−i} × 19,440 fold adds.
- **Bits per soundness bit**: 10,368 bits buy 150.1 bits (v·d/|A| = 75/2^150 ≈ 2^−144) — **1/69**, the
  galois-ring-stack r/(64r) law with the residue field grown to fit the tower. Precedent for exactly
  this trade [READ 2023/150, Table l.211–216]: VOLE-ZK over Z_{2^64} runs in GR(2^64,45) for 40-bit and
  GR(2^64,85) for 80-bit soundness, repaid by RMFE amortisation, not a SNARK.
- Where the algebra *shines* [DERIVED]: the ct×ct identity a·b = c + m·Φ over (Z/2^64)[X] checked by
  evaluation at ρ ∈ A_60 with precomputed powers costs (3·4374 + 4373 + 8747) × 162 = **4.25 M u64 mults
  = 5.5× performing the product**, against h2's ≥ 618× for the BabyBear AIR route. The one seam this
  candidate closes cheaply is the FHE-ciphertext seam.
- Lookups (ML unary tables): logup denominators (x + α), α ∈ A_60, are units automatically (x ∈ Z/2^64
  has residue in F_2, α's does not) [DERIVED]; each inverse is a Hensel lift from F_{2^162}, 6 Newton
  steps × 2 products ≈ **52k u64 mults per term** vs ~10^2 for Ext4. The ML side does not re-import a
  prime field (galois-ring-stack §6 said it would); it pays the same 500× instead.

## 3. Folding

**Requirements on the challenge set [READ; line numbers in the pdftotext].**
- LatticeFold 2024/257: strong sampling set (*"difference c₁ − c₂ is invertible"*, l.187–189); expansion
  factor ‖C_small‖_op := sup ‖ρv̂‖∞/‖v̂‖∞ over the *lifted* product (l.531, eq. 6), *"T := ‖C_small‖_op ≤ c"*
  and *"1/|C_small| in negl(λ)"* (l.941–942); relaxed binding from *"MSIS_{κ,m,8TB}"* (l.1310). The
  extractor divides — *"we can now calculate f₁ because ρ₁ − ρ₁′ is invertible"* (l.1575) — but the
  quotient's shortness comes from the sumcheck norm check plus relaxed binding, **not a short inverse**.
  Sumcheck set separately large (LF+ l.708–711: *"if q is 64-bit, we can set C := F_{q²}"*).
- LatticeFold+ 2025/247: *"A folding challenge set S̄ ⊆ R_q is a strong sampling set with small operator
  norm"* (l.705); Lemma 4.10 error (µ + dk)/|S̄| + …; extraction *"well-defined as u − u′ ∈ S̄ − S̄ is
  invertible"* (l.1602). Its monomial-set range check (§4.2) is stated for X^d+1; the port to
  X^{2r}+X^r+1 (X^{3r} = 1, not X^d = −1) is unverified [INFERRED].
- Cyclo 2026/359: γ_S := max ‖c‖_op, strong or κ_nu-approximate set (l.820–834); norm grows *additively*
  by Lγb per fold both ways (l.527–548); Remark 7 (l.2360): fixed-weight challenges, op-norm βh,
  cardinality (2β+1)^h — the same idea at prime q, with *"the lack of splitting imposes a significant
  computational overhead"* (l.2361–2362).
- Lova 2024/1964: β_C := max ‖(c − c′)^{−1} mod q‖ *"is challenging … In polynomial rings, setting C to be
  the monomials can partially help, but there are limitations even in the cyclotomic ring setting
  [AL21]"* (l.281–285); sidestepped with C := {−1, 0, 1} ⊂ Z and rows differing by ±1 (l.253–288, 686–687),
  soundness ≈ (2/3)^t — ring-agnostic, runs at q = 2^64 unchanged, t ≈ 220 columns for 128 bits [DERIVED].

**Does A_h satisfy each? [DERIVED, script §6 — exhaustive at conductor 27 (h = 2, 3: 11,628 and 332,520
pairs) and 81 (h = 2: 1,023,165 pairs).]**
- Unit differences: every pair — distinct equal-weight supports give a nonzero F_2-polynomial of degree
  < n, nonzero in F_{2^n}, hence a unit in GR(2^k, n).
- Expansion factor **exactly 2h** (monomial op-norm 2 attained; 4 at h = 2, 6 at h = 3 attained): T = 32
  (ambient h = 16) or 120 (subring h = 60); LatticeFold's MSIS norm 8TB = 2^24 / 2^25.9. Size 2^149.2 /
  2^150.1, twenty bits above 2^λ.
- **Short inverses: no, provably.** Equal weight ⇒ δ(1) = 0 ⇒ (1−ζ) | δ ⇒ 3 | N(δ) ⇒ δ ∉ O^×, so δ^{−1} mod
  2^k has no short representative: measured centred ℓ∞ of δ^{−1} is **0.667–1.000 × 2^{k−1}** (median
  0.90–0.99) at k = 8…64; every algebraic norm odd and divisible by 3. AL21 [READ]: *"There is also no
  subtractive set of size n > p over prime-power cyclotomic rings"* (Thm 2: size p, µ_i = (ζ^i−1)/(ζ−1));
  Prop 12: any (s,t)-subtractive set of size n > p has s ∈ ⟨1−ζ⟩^{min{⌈n/p⌉,t}−1}. So a dividing extractor
  gets **knowledge error 1/3 per challenge or a slack in ⟨1−ζ⟩**. The integer slack is 3: (1−X)·g ≡ 3
  (mod Φ) with g = 2Σ_{j<r}X^j + Σ_{r≤j<2r}X^j, ℓ∞ = 2, ℓ1 = m, op-norm exactly m (27, 81 verified) — the
  monomial set {±ζ^j} (2^13.1) is (3, 2)-subtractive. **3 is a unit mod 2^64**, so unlike the negacyclic
  slack 2 (galois-ring-stack §2: one 2-adic bit per use) it costs no binding; it costs norm ×≤ 2m ≈
  2^13.7 per level and ~10 parallel repetitions to reach 128 bits from 13. That is the precise content of
  the external model's warning.

**Norm growth [DERIVED, script §5].** w_{t+1} = w_t + ρ_t v_t, ‖v‖∞ ≤ B = 2^16, b₀ = B: binding needs
2·(b₀ + T·γ·B) < 2^64 — the *same additive chain recurrence* as `acc-rbr-fold.md` §3's `budget b₀ T = b₀ +
T·(ρ·B)` and Cyclo's Lγb. γ = 1 (tree, ρ ∈ {±1}): **T ≤ 2^47 − 2** (reproduced); γ = 32: **T ≤ 2^42 − 1**;
γ = 120: **T ≤ 2^40.1**. Binding dies at the wraparound pair exactly as `binding_lost_at_wraparound`
[OURS] states; q = 2^64 is primality-free there. Extraction (Cyclo-style) adds the same Lγb; a dividing
extractor multiplies by ≤ 2m per level — 2^13.7 — exhausting the 63-bit budget in 3–4 levels.

## 4. The hash

**The obstruction as a Lean Prop.** For any polynomial F over GR(2^k,d) (any arity), x ≡ y (mod 2) ⇒
F(x) ≡ F(y) (mod 2), since (x − y) | (F(x) − F(y)); exhaustively confirmed in GR(4, 6) = Z_4[X]/(Φ_9), 40
random polynomials × 200 (x, z) pairs (script §7). A random function agrees mod 2 with probability 2^{−d},
so a ring-polynomial permutation is distinguished with advantage 1 − 2^{−d} by one pair x, x + 2z — the
external model's §7 and galois-ring-stack §4's T-function attack seen from the residue field: Hensel
gives F(x + 2^i b) ≡ F(x) + 2^i J_F(x) b (mod 2^{i+1}), so **a preimage is one residue-field preimage
plus 63 F_{2^d}-linear solves — the hash is exactly as strong as its reduction over F_{2^d}; 63/64 of the
state buys nothing.** That residue layer is a binary-field hash, where x^7 has algebraic degree wt(7) = 3
and x^{2^i+1} degree 2 [DERIVED] — why Vision/Rescue-class binary designs use x^{−1} and F_2-linearised
layers; those are ring polynomials too (Frobenius is x ↦ x²) and do not escape the congruence.

**Non-polynomial mixing, and its cost here [INFERRED].** The tree's gadget-Feistel (`ring-hash-design.md`
§3: base-2^16 planes, K = 4, P = 2 plane products, 12 rows/round, 27.4 rows/element, three live caveats)
is the escape: the digit map D(x) = ⌊x/2^16⌋ breaks the congruence (witness D(0) = 0, D(2) = 1, script
§7), and at q = 2^64 *exactly* its "broken-by-default" caveat vanishes (γ = B^K − q = 0; galois-ring-stack
§4). Transfer: one GR(2^64,162) word decomposes into 4 × 162 plane coefficients, each range-checked (a
lattice folder's norm check — "free" in that note's accounting; 64 boolean rows per coefficient in an
AIR); the P = 2 plane products and the public affine layer are dense×dense at 4,323 u64 mults each unless
the matrix is sparse-monomial. The 27.4 rows/element was priced over Z_q[X]/(X^16+1) arithmetised in
BabyBear and **does not transfer as a number**, only as a shape; the recursion argument (VERDICTS:
in-circuit Poseidon2 30–210× over Blake3) has no priced analogue here. **Gate**: `∃ x y : GR, x ≡ y [MOD 2]
∧ F x ≢ F y [MOD 2]` — refuted for every polynomial F (the non-vacuity twin `∀ F x z, F (x + 2z) ≡ F x`),
satisfied by the digit map with witness (0, 2). Hours in the tree once the GR carrier exists.

## 5. The four objects, seams, kill test, label

| object | embeds as | native? | seam that remains |
|---|---|---|---|
| BFV ciphertext | 2 × 4374 words of Z/2^64 = GR(2^64,4374) | **yes** — no CRT, rescale = shift, ct×ct 768k u64 mults, depth 1, ≈ 240-bit RLWE | new FHE library [OURS]; one level; no NTT; moot if the modulus is not ours |
| commitment word | Ajtai over GR(2^64,4374), challenges A_16 ⊂ same ring | **yes** — strong sampling set of the *ciphertext ring itself*, T = 32, MSIS at 2^24 | MSIS over an inert-modulus Galois ring un-estimated; relaxed openings only (§3) |
| witness word | Z/2^64 (8 B), challenges in GR(2^64,162) | word yes; **challenge arithmetic no** — 1,296 B, 4,323 mults, 65 GB tables | 270–480× per product, floor 20×: the seam moved from limb emulation (1.00×/limb) into every challenge-side op |
| ML accumulator | int8 dot products in Z/2^64, 38 bits spare | **yes** (galois-ring-stack §6) | unary tables via logup: 52k mults per denominator; exponent align = decomposition witnesses |
| hash (recursion) | gadget-Feistel over GR(2^64,162) | polynomial hashes impossible (§4) | cost un-transferred; sponge indifferentiability still the unproved wall |

**Seams [DERIVED]**: (S1) dense challenge ring on every non-challenge message — dominant (§2); (S2)
relaxed-only extraction: slack 3 or LatticeFold relaxed binding, ×2m per dividing level (§3); (S3) ct×ct
without NTT, 1.3–2.2× FHE-side = 0.19 % of total (§1.2); (S4) hash → digit decomposition, unpriced here
(§4); (S5) one multiplicative level (§1.3); (S6) the ring exists in no deployed FHE stack. Removed vs the
RNS/BabyBear route: limb emulation, the CRT-reconstruction rescale (Hole B), galois-ring-stack §2's
commitment-ring extension (the FHE ring *is* the commitment ring). Removed vs galois-ring-stack's Z/2^64:
its challenge space of 2, its slack-2 bleed, its ML prime-field re-import.

**Kill tests, cheapest first.** (1) **Run — `inert_tower.py`** §2/§6: the 270–480× tax with its 20×
floor and the no-short-inverse lemma; refutation = a GR(2^64,162) product in < 323 bilinear mults (a
theorem says no) or a dividing extractor with |C| > 3 and integral inverses (AL21 Prop 12 says no).
(2) **Lean, hours**: `irreducible_cyclotomic_three_pow_two` from `orderOf_three_pow_of_mod_nine 2` [OURS,
one line]; the §4 congruence Prop with its digit witness — both need the Galois-ring carrier (`AdjoinRoot`
of the monic lift over `ZMod (2^k)`), plumbing. (3) **Rust, a day, decisive**: one sumcheck round at
v = 20 over GR(2^64,162) (Karatsuba + sparse fold) vs Plonky3 BabyBear-Ext4 on the same table; the count
model predicts ≥ 100× wall-clock; below 30× the model is memory-bound-wrong and the label is revisited.
Sign-off, not kill: Karatsuba-4374 vs the h2 NTT harness (`phase0/h2-rns-vs-single-prime/`) for §1.2.

**Label: TRAP** for "one algebra for the four objects" — the dense-extension tax is a theorem-shaped floor
(bilinear complexity × the r/(64r) law), not an engineering gap, and it lands on the object whose cost
decides everything (h2: the proof). **REAL** for (i) *commit-to-the-ciphertext*: an Ajtai commitment over
the FHE ring with a 2^4374-element strong sampling set, LatticeFold-exact, 2^42-fold budget, ct×ct
checkable at 5.5× performing it — the first design in the notes where commitment ring and FHE ring
coincide without an extension seam; (ii) slack-3-is-a-unit, retiring galois-ring-stack §2's "k uses bind
nothing" for every prime-power conductor p ≠ 2 at modulus 2^k; (iii) the module-BKZ bill (≈ 5 bits) for
`sis-lattice-verdict`'s open item. **Cosmetic**: the subring tower — it picks which dense ring the proof
pays for (162 vs 4374 words), not whether it pays.

**Biggest unknown not priced**: MSIS/MLWE hardness over GR(2^64,4374) *as a module over an inert-modulus
Galois ring* at norm 2^24 — no estimator run (Sage absent), no published parameter set at a power-of-two
modulus with a non-trivial residue field, the 2-adic filtration ladder (A·w ≡ 0 mod 2^{64−j} ⇒ A·2^j w ≡ 0
mod 2^64 at norm ×2^j) never run near β ≈ q, 2025/1904's coefficient-embedding caveat open. Second: no
polynomial commitment exists in this ring — opening proof size and verifier time are still empty numbers
(galois-ring-stack §7); the challenge-space obstruction that emptied them is gone, the construction is not there.

## 6. Absence claims — corpus + instrument

- RLWE/BFV over an odd prime-power cyclotomic at a power-of-two modulus with ct×ct: kagi q1 (8 results:
  ELOS-line, cyclic-algebra RLWE, NTRUEncrypt over any cyclotomic, Vive Galois, the estimator — none), kagi
  q5 (11: BFV textbooks; an MDPI hardware survey noting *"TC/Karatsuba-based polynomial multipliers have no
  restrictions on polynomial dimension or modulus selection"* — no instance); galois-ring-stack's q1
  (Jaguar, ct×pt only) stands.
- Lattice commitment / folding over a Galois ring with residue field F_{2^d}, d > 1: kagi q2 (50, top 8
  read: 2025/1767, Neo, LatticeBlindFold, latticezkvm wiki — prime q or hash-based), kagi q4 (47, top 8:
  2017/612, 2016/193, StackExchange — none); galois-ring-stack §2's mirror sweep (13 hits) re-used;
  mirror-txt 1650–1744 (this week's sync) grep "Galois ring / inert / Φ_{3": 1741 (MPC over Z_{2^k}), else 0.
- Fixed-weight exceptional-set challenges over a Galois ring: kagi q3 returned junk (counted); kagi q6
  (36): 2025/263 (Hamming-weight challenges, hash-based, O(√n), read in galois-ring-stack), 2023/150,
  AL21, Sailor — **no lattice folding or sumcheck with fixed-weight unit-difference challenges at an inert
  power-of-two modulus** in print; Cyclo Remark 7 is the prime-q cousin.
- Estimator: cloned, `from estimator import *` fails on `sage.all` (no Sage); §1.4 = own model + the standard's table. Scry unused (congested). Kagi 6/15.
