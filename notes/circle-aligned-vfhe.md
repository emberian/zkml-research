# Circle-aligned vFHE over M31 — priced. The alignment is exact; the object it aligns is not in the relation.

2026-09-04. Pricing lane for one candidate of `swarm/ASTRA-ALGEBRA-PROMPT.md`: an FHE limb over the
Mersenne prime M31 = 2^31 − 1 sharing its root-of-unity structure with the circle STARK (eprint 2024/278,
S-two 2026/532). Script: `notes/circle-scripts/circle_m31.py` (no deps, 0.4 s, `ALL CHECKS PASSED`).
Every number below is [OURS] from that script unless tagged otherwise. No VERDICTS section moves.

## 0. Verdict in three lines

1. **The algebra holds exactly as conjectured.** Over p = 2^31 − 1, X^N + 1 (N = 4096, 8192) splits into N/2
   distinct irreducible quadratics X² − c_j X + 1, so R_p = F_p[X]/(X^N+1) ≅ (F_{p²})^{N/2}; the N-th roots of −1
   are exactly the circle STARK's standard-position coset Q·G_N, and c_j = 2x_j is twice the x-coordinate of
   the circle point — the FHE twiddle table and the circle-FFT twiddle table are the same points.
2. **It buys nothing we can count.** The deployed BFV family (98,304 = 4·2·3·4096 equations; 384 = 3·128
   owner-local Rademacher-row quotient equations) is a coefficient-domain integer relation with no NTT in it;
   the STARK's pointwise algebra F_p^D and the ring (F_{p²})^{N/2} are non-isomorphic F_p-algebras, so no
   basis or twiddle choice virtualizes a ring product into the LDE; and an in-circuit half-split transform costs
   **1.375–1.833× the base multiplications of a fully split 31-bit limb** (33,792–45,056 vs 24,576 at N = 4096),
   the pointwise product 1.5–2.0×. Kyber's incomplete NTT is cheaper than a full one; M31's is dearer.
3. **What remains is the KoalaBear-limb route with M31 as the native limb**, and it prices worse: proof side
   identical by construction (best case 1.24× elements / 1.29× lookups / 1.46× muls, 70 % fixed overhead —
   `koalabear-limb-verdict.md`), depth-2 margin **6.95 bits** (−2.0 vs deployed 8.95 model / 8.90 measured),
   Poseidon2 forced to α = 5 at **1,264 blowup-cells ≈ BabyBear's 1,256, 1.93× KoalaBear's 656**, GSR CICO-1
   **cheaper** (2^23.5 vs 2^27.4; containment needs R_P 14 → 16), 1792 unchanged (2^513.4), QM31 = **124.000**
   bits (+0.37 over BabyBear⁴), clearing neither 100 at the deployed LogUp cap nor 124 anywhere.
   **Label: cosmetic. The twiddle-sharing sub-claim is a trap.**

## 1. The algebra [OURS, `circle_m31.py` Part 1]

| check | result |
|---|---|
| p mod 4, v₂(p+1), v₂(p−1) | 3, **31**, **1** (p − 1 = 2·1073741823, odd cofactor: no multiplicative NTT of any size > 2 in F_p) |
| −1 a square in F_p? | no ⇒ F_{p²} = F_p[i], i² = −1; Frobenius = conjugation |
| circle group C(F_p) | cyclic of order p + 1 = 2^31; generator (2, 1268011823) verified (g^(2^31) = 1, g^(2^30) = −1) |
| ω = g^(2^31/2N) | order 2N; **ω ∉ F_p**; ω^N = −1; ω^p = ω^{−1} = ω̄ (N = 4096 and 8192 both checked) |
| X^N + 1 mod p | **∏_{j<N/2} (X² − c_j X + 1)**, c_j = ω^{2j+1} + ω^{−(2j+1)} = 2x_j: all N/2 distinct, each divides (X^N ≡ −1 checked by square-and-multiply in the quotient), each irreducible (disc = −4y_j², a non-residue). **0 linear factors.** N/2 distinct monic irreducibles of total degree N dividing a degree-N monic ⇒ equality. |
| CRT | **R_p ≅ ∏_j F_p[X]/(X² − c_j X + 1) ≅ (F_{p²})^{N/2}**, j-th component X ↦ ω^{2j+1} = x_j + i·y_j |
| the evaluation set | {ω^{2j+1}} = Q·G_N with Q = ω of order 2N = the **standard position coset of size N** [READ 2024/278 §3.1 :313–315; Prop. 1 :326 needs 2^{n+1} \| p+1 — here 2^13, 2^14 \| 2^31; Def. 1 :192 caps supported sizes at 2^30] |
| smallest centred \|c_j\| | N = 4096: 487,052 = 2^18.9; N = 8192: 16,226 = **2^14.0 < √p = 2^15.5** (Kyber criterion, §2e) |

Two corrections to the brief's framing, both [DERIVED]: (i) the quadratics are **palindromic** X² − c_j X + 1
(Frobenius = inversion), not Kyber's X² − ζ (Frobenius = negation, q ≡ 1 mod N); (ii) there is **no F_p-rational
intermediate factor** — X^{N/2} ± i needs i — so the CRT map is not a Cooley–Tukey NTT one layer short (Kyber's
shape); it is a size-N transform over F_{p²} with conjugate symmetry, which is what Part 2 counts.

## 2. FHE cost at M31 limbs

**2a. Kyber's incomplete NTT, at source.** *"For our prime q = 3329 with q − 1 = 2^8 · 13, the base field Z_q
contains primitive 256-th roots of unity but not primitive 512-th roots. Therefore, the defining polynomial
X^256 + 1 of R factors into 128 polynomials of degree 2 modulo q and the NTT of a polynomial f ∈ R_q is a vector
of 128 polynomials of degree one"* [READ Kyber round-3 spec (2021-08-04) §1.1, our text :208–211]; basecase
products *"ĥ_{2i} + ĥ_{2i+1}X = (f̂_{2i} + f̂_{2i+1}X)(ĝ_{2i} + ĝ_{2i+1}X) mod X² − ζ^{2br₇(i)+1}"* [:261];
FIPS 203 Alg. 12 BaseCaseMultiply: c₀ ← a₀b₀ + a₁b₁γ, c₁ ← a₀b₁ + a₁b₀ [READ NIST.FIPS.203 :1585–1590] = 5 mults
per pair. Counts [DERIVED]: 7 layers × 128 = 896 vs 1,024 for a full NTT (×0.875); pointwise 640 vs 256 (×2.5);
one product from coefficient form 3·896 + 640 = **3,328 = 3·1,024 + 256** — the saved layer pays for the basemul.

**2b. M31, counted (base-field multiplications; the clock is a guest).** The transform F_p[X]/(X^N+1) →
(F_{p²})^{N/2} by the conjugate-symmetric recursion f(ω^k) = f₀(ω^{2k}) + ω^k f₁(ω^{2k}), k odd, pairing k with
N − k so each level does N/4 F_{p²}-products; leaf N = 2 is free (ω = i). Instrumented run = closed form
(m/4)·N·(log₂N − 1), m = 3 (Karatsuba/Gauss) or 4 (schoolbook); outputs checked against Horner.

| N | fully split (N/2)log₂N | half-split m=3 | half-split m=4 | ratio | pointwise full / half (m=3, m=4) |
|---|---|---|---|---|---|
| 4096 | 24,576 | **33,792** | **45,056** | **1.375 / 1.833** | 4,096 / 6,144, 8,192 (×1.5 / ×2.0) |
| 8192 | 53,248 | 73,728 | 98,304 | 1.385 / 1.846 | 8,192 / 12,288, 16,384 |

One ring product from coefficient form (2 fwd + 1 inv + pointwise), N = 4096: 77,824 full vs 107,520 (m=3) /
143,360 (m=4): **×1.38 / ×1.84**. S-two's clock claim — *"AVX2 multiplications are about 40 % faster than with
BabyBear"* [READ 2026/532 :2679] — is a per-multiplication clock, not a count, and would at best cancel the m=3
column; it is not ours to bank. **System weight**: `h2-verdict.md` §C measured that the entire FHE-side penalty
moves the total by 0.19 % at proving fraction f = 1, so the ×1.38–1.84 lands at **≈ 0.3–0.4 % of the total**.
The half-split penalty is real, counted, and nearly free at the system level — which is also why it cannot be a win.

**2c. Limb count to log₂Q ≈ 109 with 31-bit limbs** [DERIVED; margins from `paper/scripts/koalabear_limb.py`'s
model, `depth2_margin`, reproduced at deployed 8.95 vs measured 8.90]:

| tower | log₂Q | cliff | depth-2 margin | note |
|---|---|---|---|---|
| deployed 36/36/37 | 109.000 | 88.02 | **8.95** | measured 8.90 |
| KB recipe BB × (2^39−2^21+1) × (2^39−2^23+1) | 108.907 | 87.93 | 6.85 | `koalabear-limb-verdict.md` |
| **M31 × (2^39−2^21+1) × (2^39−2^23+1)** | 109.000 | 88.02 | **6.95** | same shape; −2.0 bits vs deployed |
| M31 × BB × KB (3 × 31-bit) | 92.896 | 71.92 | **−1.16** | depth 2 fails |
| M31 × BB × KB × q₄ (4 × 31-bit) | 123.896 | 102.92 | 29.43 | 4/3 the rows and NTTs; security §2e |

Only ONE limb can be the prover field: there is exactly one 31-bit Mersenne prime, and every other limb is a
foreign prime — the configuration `koalabear-limb-verdict.md` priced ("the gadget survives for the other two
limbs"). ⌈109/31⌉ = 4 limbs of 31 bits = 124 bits; 3 × 31 = 93 bits is 16 bits short and kills depth 2.

**2d. What a limb costs in proof cells** [OURS, `cross-limb-binding.md` §3]: Layout B (limbs interleaved into
one row, Hole A closed for free) forces one field per row; 36/37-bit residues bridge into a 31-bit field at
**2 felts per residue**: 49,152 felts/ct, **+220,201–294,912 perms/ct at lb = 6** over Layout A. One thing M31
does change here [DERIVED]: **M31 is the largest 31-bit prime**, so residues of BabyBear (< 2^31 − 2^27 + 1) and
KoalaBear (< 2^31 − 2^24 + 1) embed in ONE M31 felt (BabyBear as prover field holds neither KB nor M31 residues).
A 4 × 31-bit tower {M31, BB, KB, q₄} interleaves at 2·4·4096 = **32,768 felts/ct, 0.67× the bridged 49,152** —
at 4/3 the FHE work, a 31-bit-in-31-bit emulation gadget for the three foreign limbs (62-bit products need a
radix-2^16, k = 2 split [INFERRED, not built]; today's is radix-2^14, k = 3), and the security cost next.

**2e. RLWE security.** The lattice problem is (N, total log₂Q, error distribution) — the same for any RNS
decomposition of Q: N = 4096, log₂Q = 109, CBD(20) → core-SVP **98.1** [OURS, `koalabear-limb-verdict.md`,
estimator validated on Kyber 406/624/874]. The 4 × 31-bit tower's 124 bits at N = 4096 is weaker still and
VERDICTS §7.8 already flags 109 as a classical-line point nobody ships (Apple: 83 bits for `.quantum128`);
estimator not re-run here. **What is NOT the same**: the residue degree of M31 in Z[ζ_{2N}] is 2, not 1 — no
F_p-rational evaluation map R_p → F_p exists at all. Literature read at source:
- Kyber round-3 spec §4.4 [READ :1892–1899]: *"when X^n + 1 (almost) fully splits modulo q, there do not exist
  polynomials in the ring that have small norm and many zeros in the NTT representation … X^n + 1 does not have
  any factors (modulo q) of small degree and small norm … all … factors of degree n/2 have ℓ₂-norm at least √q.
  This prevents attacks that map the MLWE instance to a lower-dimensional sub-ring without increasing the errors
  by too much."* Kyber's own ring is N/2 quadratics — the M31 ring has **exactly Kyber's splitting shape**, so
  the spec's argument transfers verbatim [DERIVED]. Our measured smallest \|c_j\| (2^18.9 at N = 4096; 2^14.0 at
  N = 8192, below √p) is recorded without over-reading: a small-c QUADRATIC is not a low-error sub-ring map
  (reducing a degree-N element mod X² − cX + 1 scales the error by ~c^{N/2}); the criterion binds at degree n/2,
  which we did not enumerate [INFERRED].
- Peikert 2016/351 [READ :445–446]: *"hardness of decision is now known for essentially any large enough
  modulus, via 'modulus switching'"*; the ELOS/CLS distinguishing attacks *"use a prime ideal divisor 𝔮 of qR
  having norm N(𝔮) = q^d for some small positive integer d"* [:633–635] and are dead for spherical error — with
  M31, d = 2 is the smallest available; nothing changes.
- Lyubashevsky–Seiler 2017/523 [READ abstract]: partial splitting is chosen for invertibility of short
  challenges, *"completely for free simply by choosing a modulus p"* — an efficiency/functionality axis, not a
  security one.
**Absence**: no source treating q ≡ −1 (mod 2N) rings as a distinct security case. Instruments: Kyber spec
grep `split` (3 hits, quoted); FIPS 203 grep `split` → ∅; 2016/351 grep `split|factor` (only the 𝔮-of-norm-q^d
framing); Kagi 1 (`"Ring-LWE" X^n+1 "q ≡ -1" … quadratic factors security`, 14 results, none on point).

## 3. The proof side

**3a. What a circle STARK needs from a relation** [READ 2024/278; 2026/532]: an AIR over M31 whose constraints
are evaluated pointwise on a circle coset (transition = rotation by the coset generator), LogUp over QM31
(532 §2), quotient/DEEP by the circle vanishing polynomials (278 §3.3, Prop. 3–4). The circle code is *"isomorphic
to a Reed-Solomon code RS_{N+1}[F, S] over a set S ⊆ F_p … distance-preserving and computable within
O(\|D\|·log N) field operations"* [READ 278 Thm 1 :521–524], so the proximity leg is RS machinery; **only the fold
changes** (doubling map π(x) = 2x² − 1, 278 Thm 2/3; 532 App. A.3) — the same six-lemma port class `ecfft.md`
§4 tabulated for ψ-folds, with Lemma 5 (domain chain) replaced by the trivial 2^{n+1} \| p + 1. Soundness:
**Johnson**, 532 Thm 19 with the BCH+25 bounds [READ :1836–1875, quoted in `proximity-delta-2026-09-04.md`];
UDR *"outlined in a line of remarks … taking ℓ(θ) = 1"* [READ 532 :1445–1446, :1535]. ZK: *"in the usual
manner, by inserting sufficient randomness in the encoding of the trace polynomials, and using the [BSCR+19]
randomization of FRI, which carries over to the circle without changes"* [READ 278 :1636–1638]; the
extrapolation-saving variant of 278 App. C *"is not able to support zero-knowledge"* [:174]. Our IR-v2 AIR is
already `impl<AB> Air<AB> for Ir2Air` with `AB::F: PrimeField32` (M31 qualifies) and Plonky3 ships a `circle`
crate (5,292 lines at `a31a1443`, 2026-08-05) [READ]; breadstuffs does not depend on it; witness-gen is
monomorphic (`ecfft.md` §8). The Lean cone: `FoldingData` is root-structure-free (`ecfft.md` §4) — the
commitment layer ports, the fold does not.

**3b. The relation, read at source.** `PRODUCTION_EQUATION_COUNT = 4 * 2 * 3 * DEGREE` = 98,304
(`circuit-prove/src/private_book_bfv_slice.rs:32`, asserted `:584`); `OWNER_BATCH_EQUATION_COUNT =
FOLD_MODULI.len() * COMPRESSION_ROUNDS` = 3 × 128 = **384** owner-local equations with `QUOTIENT_BITS = 24`,
width `DERIVED_ORDER_WIDTH + 3·4096 + ROOT_BLINDING_WIDTH`, coefficients `i128`, one per (modulus, Rademacher
round) (`fhegg-fhe/src/private_book_bfv_exact.rs:38–44, :151–190`) [READ]. ⚠ The brief's pointer
`minidregg/Kernel/PrivateTurn.lean` is a hyperedge/public-indistinguishability file (287 lines, no BFV); the
384 lives in breadstuffs. **The relation is coefficient-domain and linear-with-quotient per limb; it contains
no NTT.** The NTT appears once, prover-side, computing public coefficients (`negacyclic_correlation` against
`pk_adjoint_ntt`) — native FHE-evaluator work, never in-circuit. Consequently a native M31 limb is the
KoalaBear-limb route **verbatim**: width 48 → 20, ranges 48 → 16 for the one native limb, the emulation gadget
kept for the other two, **best case 1.24× elements, 1.29× lookups, 1.46× muls, and the 2^20 row pad unmoved**
[OURS, `koalabear-limb-verdict.md`]. Nothing circle-specific enters.

**3c. "Shared twiddles" — what is shared and what it saves.** Shared, exactly [READ 278 Alg. :2730 `twiddle ←
(Q·G_k).y`, then x-coordinates; OURS: the half-NTT twiddles are ω^k = (x_k, y_k)]: one table of N/2 circle
points. Saved: **one O(N) constant table, in-circuit zero** — the LDE is prover-native work on trace columns in
the circle-polynomial basis; the FHE transform is on monomial coefficients. The obstruction that makes this
permanent [DERIVED, script Part 2 end]: F_p^D (pointwise algebra of an N-point coset) has N F_p-algebra
homomorphisms to F_p; R_p over M31 has **0** (no F_p-root of X^N + 1). Non-isomorphic algebras — no basis, no
twiddle table, no domain choice makes the STARK's pointwise product the ring product. The ring product IS
pointwise, but over (F_{p²})^{N/2}: **two cells and one F_{p²}-product per point**, the CM31 arithmetic S-two
already pays for its own extension columns. `forcodex/04-DEAD-ENDS.md` E2 killed NTT-domain-inside-FRI-domain
as "novel and worthless" on cost; over M31 it is additionally the wrong algebra. If a ct×ct arithmetization ever
needs an in-circuit transform (none exists — VERDICTS §7.5), the counts are §2b's: **33,792–45,056 F_{p²}-
butterfly base-mults vs 24,576 over a fully split limb (+37 % to +83 %)**, each butterfly two constraint rows.

**3d. Poseidon2 over M31 and the GSR/1792 margins.** α = 5 is forced: gcd(3, p−1) = 3, gcd(7, p−1) = 7,
gcd(5, p−1) = 1 [OURS; READ Plonky3 `mersenne-31/src/poseidon2.rs:27–31` *"The smallest valid exponent satisfying
gcd(α, p − 1) = 1 is 5"*; 2024/1635 :158 *"GCD(2^31 − 2, 5) = 1"*]. Plonky3 constants: **t = 16: R_F = 8,
R_P = 14; t = 24: R_P = 22; t = 32: R_P = 30** [READ `:37–65`]. Cost row [OURS `hash-landscape.md` table, that
lane's convention]: **Mersenne31 α=5: 158 cols, degree 5, 1,264 blowup-cells** vs BabyBear α=7 1,256 vs
**KoalaBear α=3 656** — M31 ≈ BabyBear, 1.93× worse than KoalaBear; the field-choice memo's case against BabyBear
(the S-box degree the prime forces) applies to M31 nearly unchanged.
GSR (2026/1692) re-run with `notes/gsr-scripts/gsr_calc.py`'s model at (t 16, α 5, R_F 8, R_P 14) [DERIVED]:

| instance | CICO-1 | CICO-2 | CICO-3 | reach / margin | containment |
|---|---|---|---|---|---|
| BabyBear deployed α=7 R_P=13 | **2^27.4** (< 2^31) | 2^61.1 (< 2^62) | 2^162 | 18 of 21 / 3 | R_P → 15 |
| **M31 α=5 R_P=14** | **2^23.5** (< 2^31) | 2^60.7 (< 2^62) | 2^154 | 19 of 22 / 3 | **R_P → 16** (15 still 2^28.2) |

t − 2k = 14 = R_P: GSR absorbs **100 % of the partial layer at equality**, and the lower α makes the practical
CICO-1 **16× cheaper**. The margin stays 3 (set by R_f0, as §5h says); the CheapLunch front-end skip is
α-independent (VERDICTS §5h) — unchanged. eprint 2026/1792 re-run with `nst_1792.py`'s model at
p = M31, α = 5, R_P = 14 [DERIVED]: Merkle node and leaf sponge both floor at **2^513.4** (basic attack, n = d = 8,
degree capped at p − 2 — the cap binds once α^{R_F+R_P} > p − 2, i.e. 5^14 > p), ω = 2.37: 2^608.4; +385 bits over
2^128, +265 over the 2^248 generic preimage — the same class as BabyBear's 2^511.9, +1.5 bits from the larger p.
**1792 is α-blind at our point; GSR is not.**

## 4. Ext for soundness — QM31 against the two walls [`two-regime-calculator.md` method]

|F| = (2^31 − 1)^4: **log₂ = 124.000** (BabyBear⁴ 123.628, KoalaBear⁴ 123.955) [OURS]. The two walls:
- **LogUp (field-size wall, no regime)**: ε = K·H·R/|F|. At the deployed admitted cap (K 1, H 2^21, R 97):
  QM31 **2^−96.40 → 96 bits** (BabyBear⁴ 2^−96.03 → 96). Clears 100 iff K·H·R ≤ 2^24.00 (**K·R ≤ 7** at H = 2^21;
  BabyBear⁴: 6). **124: never** (needs K·H·R ≤ 1). M31^6 — Plonky3 ships `HasComplexBinomialExtension<3>`
  (degree 6, 186 bits) and degree 3; **no degree 5** [READ `mersenne-31/src/extension.rs:9,41,92`] — would give
  158 bits at the cap at 1.5× the extension cells (the Ext6-overshoots trade of `field-choice-verdict.md` §3).
- **FRI query wall (no field)**: (1 − θ)^s — identical at any field: **UDR 34 / JBR 73** at our (lb 6, q 19,
  pow 16) [OURS]. The circle-FRI **batching** term does carry |D₀|/|F| (532 Thm 19); S-two's own 100-bit
  configurations at QM31 need **25–26 bits of grinding in the batching round and 26 in the query round**
  [READ 532 Table 5 :2565–2600] against our deployed pow 16.
**So QM31 clears 100 only with S-two-style grinding and a K·R ≤ 7 lookup budget, and clears 124 nowhere.**
The +0.37 bit over BabyBear⁴ is cosmetic; the regime structure is ours unchanged.

## 5. The four objects

| object | in F_{M31} / R_p? | what is lost or gained vs BabyBear |
|---|---|---|
| FHE ciphertext element | one limb natively iff that limb IS M31 (R_p half-split, 2 cells/point in transform domain); other 2–3 limbs foreign | gained: every 31-bit prime's residue fits ONE M31 felt (§2d); lost: the half-split ×1.38–1.84 FHE-side (≈ 0.3 % system) |
| commitment word | Merkle leaf: Poseidon2-M31 (α 5, 1,264 cells) or Blake2s (S-two's release, 532 :2355); Ajtai/MSIS word over q = 2^64 − 257: **not M31** — seam unchanged | hash 1.93× worse than KoalaBear; lattice seam identical to today |
| witness word | native | FRI height at lb 6: **2^24** (circle 2^30 cap) vs BabyBear 2^21 vs KoalaBear 2^18 — the only axis that strictly improves; the family's 2^20 fits all but KoalaBear |
| ML accumulator | 26-bit window < 2^31 ✓; bf16 2^16 tables via LogUp over QM31 ✓ | nothing lost on the window; **no multiplicative NTT in F_p** (v₂(p−1) = 1) — any univariate/NTT-shaped gadget must go through the circle FFT; sumcheck is unaffected |

## 6. Seams that remain, the kill test, the label

Seams, each with its cost [DERIVED from the numbers above]:
1. **Two (or three) foreign limbs** — the M31 limb aligns one of three; the rest are emulated (radix-2^14 k=3
   today; k=2 if 31-bit) and bridged (2 felts/residue at 39 bits; 1 felt at 31 bits). Cost: the KB-limb-verdict's
   70 % fixed overhead, or +220–295 k perms/ct at lb 6 for the bridge (cross-limb §3).
2. **Ring product ≠ pointwise product** — permanent (§3c); any in-circuit ring op pays 2 cells + one CM31 product
   per point; an in-circuit transform +37–83 % base-mults.
3. **The fold** — circle FRI's doubling-map fold is a new Lean object (278 Thm 2/3); proximity/BCS/RBR port as-is
   (278 Thm 1). Same class as `ecfft.md` §4 minus its Lemma 5.
4. **Hash** — α = 5 forced; 1,264 blowup-cells; GSR containment R_P → 16. Or Blake2s, which reopens the 30–210×
   in-circuit recursion bill (VERDICTS §5e/E5).
5. **Hole B and the folding ring** — ⌊t·x/Q⌉ still reads the CRT reconstruction; q = 2^64 − 257 is still not the
   proof field. M31 touches neither.

**Kill test** (cheapest, with our tooling):
- **Lean Prop** (the obstruction, with witness and falsifier): for p = 2^31 − 1, N = 4096,
  `¬ Nonempty ((ZMod p)[X] ⧸ Ideal.span {X^N + 1} ≃ₐ[ZMod p] (Fin N → ZMod p))`. Witness: the right side has N
  algebra maps to ZMod p, the left has none because X^N + 1 has no root — `ZMod.exists_sq_eq_neg_one_iff` fails
  at p ≡ 3 mod 4 and x^N is a square for even N. Falsifier: p = KoalaBear 2130706433 ≡ 1 mod 8192, where the NTT
  is the isomorphism (`Theory/CyclotomicInertia.lean` already holds the root). Proving it closes the twiddle claim
  permanently; failing to prove it would mean the arithmetic in §1 is wrong.
- **Script** `notes/circle-scripts/circle_m31.py`: any implementation of R_p → (F_{p²})^{N/2} at N = 4096 in
  fewer than **24,576** base multiplications refutes §2b; the counted floor to beat is 33,792 (m = 3).
- **The measurement that already ran**: the hash row (1,264 vs 656) and the depth-2 margin (6.95 vs 8.95). To
  revive the candidate one must beat KoalaBear on the S-box axis, which the prime forbids.

**Generality label: cosmetic.** The alignment is a true theorem about the same 2^31 points seen from two sides,
and every cost it was supposed to remove is either not present (no NTT in the relation), not removable (the
algebra obstruction), or made larger (the half-split transform, the α = 5 S-box). The twiddle-sharing sub-claim
is a **trap**: a shared constant table that reads as a shared computation. The one real asset — M31 is the top of
the 31-bit range, so BabyBear and KoalaBear residues ride in one felt — belongs to the limb-tower question, not
to the circle, and is priced in §2d with its security bill attached.

## 7. What I could not verify; absence claims with instrument

Not verified: (1) the circle-FRI UDR figure at our knobs from 532's remarks (only the field-freeness and the
regime shape were checked); (2) Plonky3 `p3-circle`'s completeness — present, not built or run; (3) the
4 × 31-bit tower's core-SVP (direction from §7.8 only; `lattice_estimate.py` not re-run); (4) the in-circuit
constraint count of a half-split transform under IR-v2 — derived from base-mult counts, not emitted; (5) the
31-bit-in-31-bit emulation gadget shape (k = 2 inferred); (6) S-two's "40 % faster" is a clock claim, unrepeated;
(7) `hash-landscape.md`'s blowup convention for the 1,264 cell — used as that table uses it for BabyBear.
Absence claims: (a) no literature on q ≡ −1 (mod 2N) as a security case — §2e instruments; (b) nobody has
proposed an FHE limb over M31 aligned with circle STARKs — Kagi 2 (`"circle STARK" OR "Mersenne31" … homomorphic
encryption RLWE BFV limb NTT`, 25 results: tutorials, stwo, Zoltraak-EVM, none FHE) and Kagi 3 (`verifiable FHE
"Mersenne" prime 2^31-1 STARK ciphertext modulus`, 15 results, none), plus notes/ docs/ forcodex/ grep for
`M31|Mersenne|circle` (43 hits, all proof-side; `ecfft.md` §7 and `04-DEAD-ENDS.md` :822 refute circle domains for
the deployed 36/37-bit limbs, which is the converse question). 3 of 15 Kagi queries spent.

## 8. Sources (read at source)
- eprint 2024/278 Circle STARKs, `~/paperbin/circle-starks-m31-2024-278.txt` (Def. 1, Prop. 1, §3.1, Thm 1, Thm 2, :1636, :2730).
- eprint 2026/532 S-two whitepaper, `~/paperbin/stwo-whitepaper-eprint2026-532.txt` (§1.1 tower, §3.4, Thm 19, Table 4–5, §6, :2679).
- Kyber round-3 spec 2021-08-04 (pq-crystals.org, fetched) §1.1, §4.4; NIST FIPS 203 §4.3 Alg. 11–12 (fetched).
- eprint 2016/351 Peikert; 2017/523 Lyubashevsky–Seiler; 2024/1635 RPO/XHash-M31 — local IACR mirror.
- Plonky3 `~/src/Plonky3` at `a31a1443` (2026-08-05): `mersenne-31/src/{poseidon2,extension}.rs`, `circle/`.
- breadstuffs `fhegg-fhe/src/private_book_bfv_exact.rs`, `circuit-prove/src/private_book_bfv_slice.rs` (unmodified).
- Ours: `h2-verdict.md`, `koalabear-limb-verdict.md` + `paper/scripts/koalabear_limb.py`, `cross-limb-binding.md`,
  `ecfft.md`, `avigad-stwo-verdict.md`, `hash-landscape.md`, `two-regime-calculator.md` + `TwoRegimeQueryBudget.lean`,
  `nst-1792-at-our-node.md` + `gsr-scripts/{gsr_calc,nst_1792}.py`, `proximity-delta-2026-09-04.md`, VERDICTS §5h/§7.
