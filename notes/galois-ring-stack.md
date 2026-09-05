# The machine-word Galois-ring stack — everything over Z/2^64 (or GR(2^64, r)) — priced

2026-09-04. Mathematics + literature + pricing lane, one of two candidates for the joint-algebra
question (`swarm/ASTRA-ALGEBRA-PROMPT.md`). Basic research: chart and price; no product selection.
Scripts: `notes/galois-scripts/gr_sumcheck_bits.py` (every derived number below) and
`notes/galois-scripts/hensel_preimage.py` (the kill test, RUN). Read at source, not relayed:
Rinocchio `~/paperbin/ring-rinocchio-…-2021-322.pdf` (Def 5, Lemma 2, Prop 1, §1.2, §7.3, §8.4);
2025/1767 Galois-ring BaseFold (paperbin; Fact 2, Def 10, §4.1, Thm 1/2); 2025/263 (mirror);
Greyhound 2024/1293 (mirror — ⚠ the brief's "2024/924" is Galbraith's isogeny paper); LaBRADOR
2022/1341 (mirror); Albrecht–Lai 2021/202 (paperbin); 2026/1857 (mirror, §3.6, Rem 4.18, §4.3.3.1);
Saber 2018/230 and 2021/995 (mirror); Zinc 2025/316, GlueLUT 2026/494, Bootle et al. 2026/471,
2026/1127, 2025/719, 2024/32 (paperbin/mirror, abstracts + named lines); SWIFFT (paperbin);
`Selvage/Sumcheck.lean`, `ReedSolomon.lean`, `MultilinearExtension.lean` binders;
`breadstuffs/metatheory/Bfv/ZqSumcheck.lean:106,214`. Kagi: 8 queries (listed in §8).

## 0. Verdict in three lines

1. **TRAP as "one algebra".** Z/2^64 puts the four objects in one ring and pays for it at every
   proof-side seam: soundness is bought only by the residue field, so **63/64 of every challenge
   bit is wasted** (r = 107/131 extension words per challenge for 100/124 bits); the negacyclic
   ring mod 2^k is **local with residue field F_2**, so no invertible-difference challenge set of
   size > 2 exists and every lattice PCS / folding extraction / opening proof loses its challenge
   space; and every polynomial hash over Z/2^k is a **T-function**, preimage-found by k linear
   solves (script: 10/10 preimages in 160 evaluations against a 64-bit digest).
2. **The honest survivors are exactly the pieces the tree already holds**: TFHE/HPU ciphertexts
   and integer accumulators are native (§6); the Galois-ring *family's* efficient corner is s = 1,
   i.e. the binary towers of the landed binary path; the hash escape is non-polynomial
   (decomposition/lookup), which is the ring-hash Feistel — and its "broken-by-default" modulus
   defect vanishes at q = 2^64 exactly (§4).
3. **No number exists for the PCS.** Every published lattice PCS uses a prime q chosen for
   splitting control; the two Galois-ring hash-based PCS families are O(√n) (2025/263) or require
   p ≠ 2 (2025/1767 line 414). The proof-size/verifier story for this candidate therefore rests on
   nothing published; the pessimistic reading is Greyhound's 53 KB / O(√N) verifier × ~100
   repetitions, or Rinocchio's own "extension degree logarithmic in the QRP size".

## 1. Sumcheck over GR(2^k, r)

**The bound [READ].** Rinocchio Def 5: `A ⊂ R` is *exceptional* if all pairwise differences are
units; the *Lenstra constant* is the largest such set. Lemma 2 (generalized Schwartz–Zippel, [6]):
`Pr_{a←A^n}[f(a)=0] ≤ deg f / |A|`. Prop 1 ([1]): **the Lenstra constant of GR(p^k, d) is p^d** —
the residue field `GR/(p) ≅ F_{p^d}`, all zero divisors nilpotent, ideal (p). Sumcheck soundness has
the CCKP19 Thm 2 shape `v·deg/|A|` (rounds ADD; `notes/zq-sumcheck.md` §1.3). 2025/1767 Fact 2
samples from the *whole* ring and gets the same `deg/p^r` — tight: `f(x) = 2^{k−1}·x` has degree 1
and vanishes on half of Z/2^k (script §3, 128/256 at k = 8) [MEASURED]. So the 2-adic depth buys
**zero** soundness; the tree's own read of 1767 said so (`multilinear-pcs-landscape.md:1440`,
*"s > 1 buys Z_{p^s} representation and zero bits of soundness"*).

**r needed [DERIVED, script §1]:** `r ≥ bar + log2(v·deg)`; PCS/opening error not included.

| work point | v | deg | v·deg | r @ 100 | r @ 124 | challenge bytes (8r) |
|---|---|---|---|---|---|---|
| zq-sumcheck worked point (§2 there) | 25 | 3 | 75 | **107** | **131** | 856 / 1048 |
| AIR with the α = 7 S-box, 2^16 rows | 16 | 7 | 112 | 107 | 131 | 856 / 1048 |
| 4096² matmul, product of two MLEs | 24 | 2 | 48 | 106 | 130 | 848 / 1040 |

**Element sizes [DERIVED, script §2]:** witness word 8 B; challenge 8r B = **856–1048 B**; one
challenge×challenge multiplication = r² = **11,449–17,161 u64 mults** schoolbook (~1.6–2.3k
Karatsuba) plus the binomial reduction. Against: BabyBear+Ext4 4 B / 16 B / 16 u32 mults at
|A| ≈ 2^123.6 (deployed); Binius GF(2^128) 16 B / 16 B / one carry-less mult; Z_Q+Ext4 (zq-sumcheck
§2/§6) 14 B / 55 B / 48 limb-mults at 2^144. **Soundness bits per challenge bit: fields 1.0;
GR(2^64, r): r/(64r) = 1/64.** The Galois-ring family GR(2^s, r) costs s·r bits and pays r bits;
the efficient corner is s = 1 — binary towers. The machine-word ring is the worst corner.
Rinocchio's own §8.4 [READ]: *"the degree of the extension affects the complexity of the Prover,
CRS size and the Verifier's complexity"*, with amplification making it *"logarithmic in the QRP
size"*; Zinc's reading [READ, 2025/316 p.6]: *"the Galois ring needs to be very large, namely with
elements of bit-size around n·λ … a large embedding overhead"*.

**MLE and the Lean binders [OURS, read].** `MultilinearExtension.lean:92` `Cube` section is
`[CommRing F]` — MLE, agreement, injectivity, multilinearity, round/residual sums all ring-general
already; uniqueness needs `[Nontrivial F]` only. The single `Field` bite is `Sumcheck.lean:77
card_agreeFinset_lt` ← `ReedSolomon.lean:122 card_agreeSet_lt_of_ne` (mathlib `[IsDomain]` root
counting) — and the field-wide statement is FALSE over any ring with zero divisors, so the
statement changes to "agreement inside an exceptional set" (`zq-sumcheck.md` §3). ⚑ **That
statement is already proved in the general form a Galois ring needs**:
`breadstuffs/metatheory/Bfv/ZqSumcheck.lean:106 agree_card_lt_of_proj {R F} [CommRing R] [Field F]
(π : R →+* F) (A : Finset R) (hinj : Set.InjOn π ↑A) … : (A.filter (p.eval = q.eval)).card < d`
— any ring hom into a field, injective on A. For GR(2^k, r) take π = reduction mod 2 into F_{2^r}:
injective on every exceptional set by definition (a difference that is a unit is nonzero mod 2).
The ceiling `:214 samplingSet_card_le (A) (f : R → T) (hf : injective on A) : A.card ≤ card T` gives
Prop 1 (`|A| ≤ 2^r`) with `T := F_{2^r}`. What does NOT exist [INFERRED]: a Galois-ring carrier in
Mathlib (`GaloisField p n` is the field; `GR(2^k, r)` would be `AdjoinRoot` of a monic lift over
`ZMod (2^k)` with the residue map built by `Polynomial.map` + `AdjoinRoot.lift`) — plumbing,
not counting; and the Selvage protocol-layer port itself, still un-performed since 08-16.

## 2. Lattice PCS over Z/2^k

**What is published, and its modulus [READ].** Greyhound 2024/1293: *"Take an odd prime q"*
(l.179), *"q ≡ 5 (mod 8)"* (l.1195) so X^d+1 splits into two factors and Lemma 2.1 [LS18] makes
small-coefficient elements invertible; d = 64, q ≈ 2^32 (l.1626–1627); *"evaluation proofs of size
53KB"* at N = 2^30 (abstract); verifier `O_λ(√N)` (l.1478) — **no verifier milliseconds in the
abstract**; the tree records RoKoko at 13 ms verify as the real comparator (`sis-lattice-verdict.md`).
LaBRADOR 2022/1341: *"q, d are such that X^d+1 splits in two irreducible factors mod q"* (l.237),
challenges with *"c1 − c2 … invertible for any pair"* (l.255, via [LS18 Cor 1.2], l.269), q ≈ 2^32
(l.82), 47–58 KB at 2^10–2^20 constraints (the *statement* modulus 2^64+1 in its abstract is
composite — the commitment modulus is the prime). Hachi 2026/156, SLAP 2023/1469, Cini et al.
2024/281: prime-modulus negacyclic rings (kagi q2/q3). Akita: **no paper found** (kagi q3 → Hachi,
SLAP, Jolt DeepWiki only; `systems-delta-2026-09-04.md` §5.2 has the repo). Saber 2018/230
[READ]: *"all integer moduli are powers of 2 avoiding modular reduction and rejection sampling
entirely"* and *"excludes the use of the number theoretic transform (NTT)"* (l.70) — a KEM, no
challenge set needed, so its power-of-two choice never meets the obstruction below.

**Absence [corpus + instrument].** No lattice polynomial commitment over a power-of-two modulus:
kagi q2 (8 results, all prime-q lattice or hash-based Galois-ring PCS); first-page sweep of every
2024–2026 PDF on the IACR mirror, filtered on proof-system × ring terms → 13 hits (2024/1548,
1964, 1972, 32, 997; 2025/1767, 263, 542; 2026/1127, 159, 242, 471, 494), none a lattice PCS over
Z_{2^k}. The one paper whose title says "SNARKs over Z_{2^k}" (Jia–Li–Xing–Yao–Yuan, CRYPTO 2025,
RS proximity gaps over Galois rings, *"the (1−ρ)/2 gap … still holds"* per the kagi snippet) is
**hash-based, paywalled, and has no eprint** (eprint search page: 1 result, 2025/199; mirror sweep:
no hit) — not read, not quotable beyond the snippet.

**What breaks at q = 2^k [DERIVED / MEASURED, script §5].**
- `X^N + 1 ≡ (X+1)^N (mod 2)`: totally ramified. `R_q = Z_{2^k}[X]/(X^N+1)` is **local** with
  maximal ideal (2, X+1) and residue field **F_2**; u is a unit iff u(1) is odd (brute force at
  k = 3, N = 4: 2048/4096 units, predicate exact). Any exceptional set injects into F_2:
  **Lenstra constant 2.** LaBRADOR/Greyhound/Schnorr-style extraction, folding's 2-transcript
  extraction and every "invertible challenge difference" step have a challenge space of size 2 —
  knowledge error 1/2 per challenge — versus `|F_q^{N/τ}|` per CRT factor at a prime q.
- The [LS18] "short nonzero ⇒ invertible" lemma is a prime-splitting theorem; over 2^k, 2 itself
  is short and a zero divisor. Albrecht–Lai 2021/202 Thm 3 [READ]: even over Z[ζ_{2^ℓ}] no
  (2,t)-subtractive set has size > m+1, and their slack s = 2 is a zero divisor mod 2^k — a
  relaxed opening `A·(2w) = 2t` loses one 2-adic bit of the commitment per use; k uses bind nothing.
- No NTT (Saber, above). Costs [DERIVED, script §7]: a 64-bit negacyclic product at N = 4096 by
  full Karatsuba is 3^12 = 531,441 64×64→128 mults vs 233,472 ~50-bit modmults for a 3-prime
  CRT-NTT (2.28×, plus ~3.5M 128-bit adds); measured anchor 2021/995 abstract [READ]: NTT-Saber is
  *"33%–41% faster"* than Toom–Cook at N = 256 — scaling N^0.585/log N gives ~4.5–4.8× at 4096.
  The CRT-NTT route re-imports three prime limbs as an implementation detail — and as the thing
  the prover must prove (the cross-limb Hole A shape, `zq-sumcheck.md` §4, returns inside the
  multiplication algorithm).
- MSIS/MLWE hardness itself is not the obstruction (Saber's security analysis is for power-of-two
  q); the 2-adic ladder `A·w' ≡ 0 (mod 2^{k−j}) ⇒ A·(2^j w') ≡ 0 (mod 2^k)` turns a short kernel
  vector mod 2^{k−j} into one mod 2^k at norm ×2^j — a filtration the estimator must be run against
  at β near q [INFERRED, un-run; it is the dual-mode note's O6 all over again].

**Escapes [INFERRED, ours, unverified].** Repetition: κ ≈ 100–128 parallel challenges (×κ on every
opening). Extension: run the commitment over `GR(2^k, r)[X]/(X^N+1)` — residue field F_{2^r},
exceptional sets of size 2^r, witness blown up r× (this is the SuperNeo R_K seam 1857 names, §5).
Hash-based over GR: 2025/1767's fold divides by `2·diag(T)` (l.414: *"invertible in GR(p^s, r) if
p ≠ 2"*) — dead at p = 2 as written; an **odd-radix fold** inside the Teichmüller group of
GR(2^k, r) (differences of distinct Teichmüller elements are units) avoids the division by 2, and
the FFT-friendly domain is the smooth part of 2^r − 1: d = 60 gives ~2^34 with radices ≤ 61,
d = 64 gives only 255 (script §6). Nobody has written the proximity gap for it; the tree's
`[BINARY-fold]`-style obligations would all recur.

## 3. Folding over Z_{2^64}

`AccRbrFold` (`notes/acc-rbr-fold.md`): witness ring ℤ, `C := Fin κ → ZMod q`, `commit = cast ∘
mulVec A`, budget `b₀ + T·ρB`. **The norm wall transfers verbatim [DERIVED]**: binding is lost
constructively at `2·B(1+T) ≥ q`; with q = 2^64, B = 2^16, ρ = 1: `T = 2^47 − 1` again (q/2 = 2^63
exactly, so the boundary is even sharper — the pair `2^63·e₀` and `−2^63·e₀` coincide mod q).
`binding_lost_at_wraparound` is primality-free and needs no change; `capacity_safe`/`capacity_
broken` re-instantiate at q = 2^64 by `norm_num`. What is new is not the norm — it is **the
challenge**: `foldReduction` today takes ρ ∈ ℤ short (ρ = 1) and leaves the round bound
`FoldRoundBound` statement-first; the per-fold knowledge error it would carry is `1/|A|` with A an
exceptional set of the challenge ring — **1/2 over Z_{2^k}** (§2). Amplifying by GR(2^64, r)
multiplies the accumulated witness by r (Neo's pay-per-bit needs lattice norms — Z/2^64 has them,
unlike char 2 — but the extension-ring seam is the one Neo/SuperNeo already pay). The 2-adic
zero-divisor structure adds the relaxed-opening loss above (§2, slack 2 = one bit per fold) — an
obstruction the prime-modulus argument never had because there s^T is a unit.

## 4. The hash

**x^α is not a permutation of Z/2^k [MEASURED, script §4]**: units map bijectively for odd α
(group C₂ × C_{2^{k−2}}), non-units collide — image 147/256 (α = 3), 133/256 (5), 130/256 (7)
at k = 8. Permutation polynomials mod 2^w exist (Rivest 2001 criterion [recalled, not read]: a₁
odd, even-index sum even, odd-index sum even), e.g. `x(2x+1)` — degree 2, the cheapest S-box
imaginable.

⚑ **And every one of them is dead, by a mechanism the Gröbner lens never sees [INFERRED, ours;
the mechanism is Klimov–Shamir T-function bit-slicing, CHES 2002, recalled].** Every polynomial
map F over Z/2^k is a T-function, and for i ≥ 1 Taylor gives `F(x + 2^i b) ≡ F(x) + 2^i·J_F(x)·b
(mod 2^{i+1})` — bit-plane i of the output is F₂-affine in bit-plane i of the input given the
lower planes; plane 0 is F mod 2, affine for univariate S-boxes plus linear layers because x^n = x on F₂. A preimage is k linear solves,
and the Jacobian comes from finite differences — the attack is black-box in the design.
**Ran** (`hensel_preimage.py`, k = 32, t = 6, capacity 2, 8 rounds, random invertible-mod-2
linear layers):

| S-box | preimages | mean evaluations (brute force ~2^64) | backtracks | time |
|---|---|---|---|---|
| `x(2x+1)` (permutation polynomial) | **10/10** | **160** | 0 | 11 ms |
| `x³` (not a permutation; J drops rank at even inputs) | 2/10 within a 2·10⁵ budget | 160,306 | 61,101 | 10.6 s |
| T-function distinguisher (LSBs of digest fixed by LSBs of message) | 200/200 | | | |

So a "Poseidon over Z/2^k" cannot exist, and the decidable-by-design question (`notes/decidable-by-
design.md` §1c: *the certificate of decidability is the attacker's input*) is answered at its
extreme: over Z/2^k the certificate is the **derivative**, Gröbner is replaced by Hensel, and it is
cheaper, not harder. Gröbner theory over Z/2^k exists (strong Gröbner bases over Z/m,
Norton–Sălăgean 2001 [recalled]) and is moot for polynomial layers. **Absence**: no
arithmetization-oriented hash over Z/2^k or a Galois ring — kagi q5 (8 results: Anemoi, Arion
2026/1842, 2026/1271, XHash, all prime-field), mirror sweep 0; 2026/1127 (Zama) lists *"the design
of hash functions over rings that permit efficient arithmetizations"* as open [READ] — this section
says the polynomial half of that question is closed negatively. SWIFFT is over Z_257 (prime)
[READ]; the ring-native compressor idea inherits nothing from Z/2^k.

**What survives**: non-T-function nonlinearity. (a) Rotation/XOR designs — Blake3/Keccak, priced
in the tree at 30–210× in-circuit. (b) Lookups: over Z/2^64 the published route is GlueLUT-v2
(2026/494, Q = p^k) — *"perform the lookups over an auxiliary field F_P … then certify the
consistency"* [READ]: the lookup re-imports a prime field; Bootle et al. 2026/471 work over
`Z_q[X]/(X^d+1)` *"for prime q"* (l.185) [READ]. (c) The tree's gadget-decomposition Feistel
(`ring-hash-design.md` §3): its nonlinearity is base-2^16 decomposition — a bit-permutation across
planes, NOT a T-function, so it escapes. ⚑ And at q = 2^64 exactly its caveat 1 disappears: the
plane ambiguity is `γ = B^K − q`, and `B^K = 2^64 = q` gives γ = 0 — decomposition unique, the
Frog-modulus "broken by default" defect gone [DERIVED from §3 of that note]. Conversely, the
dual-mode design's q = 2^64 − 257 is what keeps its *polynomial* layers off the T-function ladder:
mod-q reduction is not triangular. That modulus is load-bearing in a way the note did not record.

## 5. Zero-knowledge

2026/1857 [READ]: blinding via ABDLOP + Libra masking + rejection sampling; the depth is fixed by
Eq. (4.17) `τ_{λ,ξ}·ξ·(K+k)·T(C)·(b−1)·√n_F < b^k`, i.e. `k ≈ ½·log₂ n_F + log₂(τξ(K+k)T(C)(b−1))
= Θ(log n_F)` (Rem 4.18), versus SuperNeo's (4.16) with k = 13 at T = 128, b = 2. Tabulated §3.6:
k = 26–28 at n_F = 2^16, 29–30 at 2^20, 30–31 at 2^21 (T = 256, d = 128, ξ ≈ 20); a fold step is
≈ 5.5 MB (d = 64) / 8.2 MB (d = 128); security ≈ 116 / 121 bits, interactive only; the modulus is
the **64-bit prime 2^64 − 59**, so "k = 64" in the brief's sense is their native point.
**[DERIVED]** at our n_F = 2^24: `k ≈ 31 + ½·(24 − 21) ≈ 33` (b = 2; the (K+k) term moves it by
< 0.1). Smudging instead of rejection would need a mask ≥ 2^λ·‖w‖, i.e. `k += λ/log₂ b = +128`
planes at b = 2 — ~4.5× worse than rejection's 31 [DERIVED]; Θ(λ) vs Θ(log n_F). At q = 2^64
exactly the number is **undefined**: ABDLOP's opening proofs need the [LNP22] challenge space with
invertible differences (§2 wall), and 1857 already reports that ABDLOP is *"only known to be secure
over the base ring R_F and not over the extension ring R_K"* — the extension is the only repair.

## 6. The four objects

| object | native in Z/2^64? | where the seam remains |
|---|---|---|
| **TFHE/HPU ciphertext** | **yes** — HPU ring is ℤ/2^64 (`hpu-seam-study.md`, 162,770 lines read) | proving a PBS: 2025/719 = 2.02 s per bootstrap proof (packed sumcheck over BabyBear + Brakedown/Binius commit) [READ]; 2026/1127 (lattice folding over rings) *"smaller proofs … at the cost of a sharp increase in prover and verifier time"* [READ]. Against 14,221 PBS/s [OURS] that is ~2.9·10⁴× — audit-rate territory, as the HPU note already concluded |
| **BFV ciphertext** | arithmetically pretty, unshipped: decrypt/rescale `⌊t·x/q⌉` with t = 2^20 | q = 2^64 is `(x + 2^43) >> 44` — a 44-bit split witness, no CRT reconstruction: **Hole B becomes a range check** [DERIVED] | ct×ct product needs NTT-or-Karatsuba (§2: ×2.3–4.8, or CRT-NTT re-importing 3 prime limbs). Literature: Jaguar arXiv 2606.11827 [READ abstract] builds HE/2PC CNN inference on *"a power-of-two ciphertext ring"* with *"exact ciphertext-side truncation by local right shifts"* and *"scalar–polynomial accumulation"* replacing NTT — ct×pt only; kagi q1 found no BFV-over-2^64 with ct×ct. If we do not control the FHE modulus (VERDICTS §7.3), BFV stays RNS and this candidate offers it nothing |
| **nonlinearity** | PBS native — the t = 2^20 degree-≤2 restriction (VERDICTS §3) does not apply | buys arbitrary LUTs without an MPC boundary; costs one proved PBS per activation at the numbers above |
| **commitment word** | Ajtai over Z_{2^64}[X]/(X^N+1) commits fine (Saber-style MLWE) | opening, folding, PCS: Lenstra constant 2 (§2, §3) |
| **witness word** | 8 B, wraparound free | challenges GR(2^64, 107–131): 1/64 law, 856–1048 B, 10⁴ u64 mults per challenge mult (§1) |
| **ML accumulator** | int8 dot products: Σ ≤ K·2^14 < 2^63 for K ≤ 2^48 — wraparound never fires; the 26-bit window fits with 38 bits to spare | exponent alignment (shift) and bf16 unary tables are non-polynomial → lookups → GlueLUT-v2's auxiliary prime field [READ]; the ML side re-imports a prime field exactly where BabyBear needed none |

## 7. Seams, cost, kill test, label

**Seams that remain [DERIVED]**: (S1) challenge extension, r = 107/131 words on every challenge-side
op (§1); (S2) opening/folding challenge space of size 2 → ×κ ≈ 100 repetitions or ×r witness (§2,
§3); (S3) ct×ct multiplication → CRT-NTT limbs (the RNS seam, moved inside the multiplier) or
Karatsuba ×2.3–4.8 (§2); (S4) hash → lookups → auxiliary prime field, or Blake3-class 30–210×
(§4); (S5) proximity leg → hash-based over GR with p ≠ 2 required (1767) or an unwritten odd-radix
fold (§2). Nothing in the candidate removes a seam the RNS/BabyBear route has; it moves S3 and adds
S1, S2, S5. The one genuine gain is BFV's rescale as a shift (Hole B → range check), and it needs
a modulus we may not control.

**Kill tests (cheapest first)**: (1) `hensel_preimage.py` — **already run**, 10/10 preimages in 160
black-box evaluations; refutes every polynomial-S-box hash over Z/2^k. (2) Lean Prop, hours:
`∀ A : Finset (Z_{2^k}[X]/(X^N+1)), (∀ a b ∈ A, a ≠ b → IsUnit (a − b)) → A.card ≤ 2`, proved by
`samplingSet_card_le` with `f := (u ↦ u(1) mod 2)`; satisfying witness `{0, 1}`; falsifying twin
at the prime side: q ≡ 1 (mod 2N) with `A := image of F_q` of size q. Refutable ⇒ non-vacuous.
(3) `gr_sumcheck_bits.py` §1–2 — the r table is exact arithmetic; a count harness adds nothing.

**Generality label: TRAP** for "everything over Z/2^64"; **real** for three by-products — the 1/64
law naming s = 1 (binary towers) as the family's efficient corner; the T-function/Hensel closure of
the polynomial-hash question over Z/2^k, with q = 2^64 − 257 now recorded as load-bearing for the
dual-mode ring hash; and the rescale-as-shift observation for a controllable BFV modulus.

**Biggest unknown, stated pessimistically**: there is no proximity leg with p = 2 and no lattice
PCS with q = 2^k in print, so the proof-size and verifier-time story for this candidate is *empty*
— the only numbers that exist (Greyhound 53 KB, O(√N) verifier; LaBRADOR 47–58 KB, linear
verifier; 1857's 5.5–8.2 MB per ZK fold step) are for prime moduli and would be multiplied by the
κ ≈ 100 of S2 or the r of S1 before they apply.

## 8. Absence claims — corpus + instrument

- Lattice PCS over power-of-two q: kagi q2 (8 results, none); mirror first-page sweep 2024–2026
  (13 hits listed in §2, none). Akita paper: kagi q3 (none; repo only).
- BFV over Z/2^64 with ct×ct: kagi q1 (Jaguar only, ct×pt). AO hash over Z/2^k / Galois ring: kagi
  q5 (8 prime-field results), mirror sweep 0. T-function literature: kagi q7 (Klimov–Shamir line
  confirmed to exist; not read).
- Jia et al. CRYPTO 2025: eprint search page → absent; Springer → IdP redirect, ACM DL → 403; not read.
- The eprint 2026 year-listing fetch returned 40 entries (truncated) — instrument failed, not used.
- Kagi total: 8 of 20. Scry not used (congested per preamble; the mirror sweep replaced it).
