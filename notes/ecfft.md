# ECFFT for limb-native proving — verdict: WRONG TOOL FOR OUR CASE, and the 2-adicity check is not moot but MISDIAGNOSED

**Status: research + pricing lane, 2026-08-16. Sources read at origin:** ECFFT part I
(arXiv:2107.08473v2, fetched, full text), part II (eprint 2022/1542, local IACR mirror,
full text). Deployed constants read from `fhegg-core/src/bfv_lean.rs:70-72` and
`fhegg-core/src/threshold.rs:659-677`, not relayed. Every claim below is tagged
[MEASURED] / [SOURCE] (read in the paper) / [DERIVED] (my arithmetic) /
[RECALLED] (memory, unverified).

## 0. TL;DR — the one-paragraph verdict

ECFFT/EC-FRI is post-quantum on exactly the same assumption base as our existing FRI
stack (hash + code distance; the curve is a combinatorial device, nothing is committed
in the curve group — verified at source, §2). But it **cannot reach our geometry**: its
own theorems cap the cyclic 2-group — and hence the code dimension, i.e. the TRACE
HEIGHT — at `2^k ≤ 2√q` (Hasse/Find_Curve), which is 2^18 for our 36-bit limb primes
(both sit just *below* 2^36) and 2^19 with zero margin for the 37-bit one, while the
98,304-equation family pads to 2^19 **per limb**. The binding constraint on
limb-native proving is *field size relative to trace*, not 2-adicity — and 2-adicity is
the one constraint we can simply BUY: the limb primes are ours to choose (greenfield;
`fhe.rs` `BfvParametersBuilder::set_moduli` is a public API), and 36/36/37-bit primes
with v2(q−1) = 24 exist in bulk (68 and 151 candidates counted) with total log Q within
0.03 bits of the deployed set. **Classic FRI over swapped high-2-adicity limb primes
reaches every height in 2^10–2^21 at blowup 8, keeps zero-emulation, and keeps our
RS-shaped Lean proximity cone almost unchanged. ECFFT is the tool for fields imposed
from outside (secp256k1, P-256); our limb fields are not imposed.** What survives from
this lane: the extension-challenge smallness analysis (§5) is mandatory either way, and
the fold-abstraction gap list (§4) is what a port WOULD need if a truly frozen prime
ever appears.

## 1. THE 2-ADICITY ARITHMETIC — done first, as briefed; the brief's premise corrected

**The brief said** "limb primes chosen for N=8192 negacyclic NTT — 2-adicity ≥ 14"
[ASSUMED-BY-BRIEF]. **Measured** [MEASURED]:

The deployed fold set is **degree 4096**, not 8192 (`fhegg-core/src/bfv_lean.rs:70`;
the degree-8192 `correlation_set()` at `threshold.rs:672` is a *different* parameter
set for the distributed-correlation circuit, from `fhe.rs default_parameters_128(20).nth(3)`).
The three fold moduli and their factorizations:

| prime | bits | q−1 factorization | v2(q−1) |
|---|---|---|---|
| `0xffffee001` = 68719403009 | 36 | 2^13 · 17 · 493447 | **13** |
| `0xffffc4001` = 68719230977 | 36 | 2^14 · 11 · 593 · 643 | **14** |
| `0x1ffffe0001` = 137438822401 | 37 | 2^17 · 3 · 5² · 11 · 31 · 41 | **17** |

Negacyclic NTT at N=4096 needs 2^13 | q−1; the first prime has exactly that and no
slack. (All three q+1 have v2 = 1, so Circle-STARK-style p+1 domains are out —
[DERIVED], needs p ≡ 3 mod 4.)

**Max classic-FRI heights per limb (height ≤ 2^(v2 − lb))** [DERIVED]:

| blowup | q0 (v2=13) | q1 (v2=14) | q2 (v2=17) |
|---|---|---|---|
| 2× | 2^12 | 2^13 | 2^16 |
| 4× | 2^11 | 2^12 | 2^15 |
| 8× | 2^10 | 2^11 | 2^14 |

**Against the geometry**: `h2-verdict.md` reads 344,064 live rows ⇒ 2^19 padded for the
single-prime layout of the 98,304-equation family; the RNS layout is ~3× that ⇒ **2^20
padded jointly, 2^19 per limb** if split into three limb-native provers. So:

- ⚑ **2-adicity 13/14 is NOT enough**: at lb=3 it reaches 2^10/2^11 — the bottom of the
  2^10–2^20 range only. The family at 2^19-per-limb needs v2 ≥ 22 at lb=3.
- **q2 alone is a partial exception**: v2=17 plus a 41-smooth odd part (3·5²·11·31·41)
  means *mixed-radix* domains up to 2^17·3·5² ≈ 2^23.2 exist; FRI with radix-3/5 fold
  steps is possible in principle [DERIVED], but that machinery (non-2 folds, non-2
  vanishing polynomials, a mixed-radix NTT) is a bigger port than the fix in §3 and
  only rescues one limb of three.
- **Reachable today with zero changes**: any per-limb relation of height ≤ 2^10 at lb=3
  (≤ 2^12 on q2). That covers the *current* proving fraction (1/98,304 — one row
  category) but not the design target f=1.

**So the check does not moot the lane** — but §3 shows the lane's premise (ECFFT as the
fix) is dominated by a cheaper move the brief did not price.

## 2. Q1 — POST-QUANTUM? YES-NEUTRAL, CONFIRMED AT SOURCE

Read in eprint 2022/1542 (part II), not inherited:

- **Remark 2 (p.4), verbatim mechanism**: the constructions are IOPs; compiling with
  Kilian–Micali / BCS is "secure in the quantum random oracle model, and these generic
  transformations apply to all our results, rendering them post-quantum secure in this
  model," citing Chiesa–Ma–Spooner–Zhandry and Chiesa–Manohar–Spooner [SOURCE].
- **No DL assumption anywhere.** Soundness of EC-FRI (Thm 12/13) is information-
  theoretic, resting on the BCIKS proximity-gap theorem for RS codes [8] — the same leg
  our existing FRI floor stands on. The elliptic curve contributes only the *domain*
  (a coset chain of a cyclic 2^k subgroup of E(F_q)) and the degree-2 maps ψᵢ; nothing
  is ever committed in the curve group, no pairing, no DLP instance exists [SOURCE,
  Thm 8/9 + §6.3].
- **Adversarial curve choice does not matter.** Theorem 9's `Find_Curve` is a Las Vegas
  search (O(2^k log² q log log q)); the output — curves Eᵢ in Weierstrass form, the maps
  φᵢ, ψᵢ, the subgroup — is *advice*, "depend[ing] only on |F| and T" (footnote 6), used
  by prover AND verifier. Soundness (Thm 12/13) quantifies over the domain/maps given
  their *structural* properties (T an evaluation domain at scale ℓ; ψᵢ of degree 2;
  the fiber decomposition of Lemma 4), all deterministically checkable — BCIKS holds
  for RS over **every** evaluation set, so there is no "weak curve" to plant. Setup is
  transparent in exactly the sense our Poseidon2 constants are: run the public search
  from a public seed, or verify the advice's defining equations directly [SOURCE +
  DERIVED for the checkability remark].
- **The honest caveat**: same as FRI's. The concrete Johnson-regime exponent and the
  QROM compilation losses are the ones our FRI-reality memory already tracks
  (conjectured 130 / proven 51–73); EC-FRI inherits that entire landscape unchanged,
  plus its own additive error term (§4). PQ-wise it is *neutral*: not one assumption
  more, not one fewer.

## 3. ⚑ THE DOMAIN CAP — why ECFFT cannot serve the stated prize, and what wins instead

**The cap, at source — and what it actually binds**: Part I Thm 4.9 / Part II Thm 8:
curves with a 2^k subgroup are guaranteed only for `2^k ≤ 2√q` (the Hasse interval has
width 4√q, so it contains a multiple of 2^k only up to that point); `Find_Curve`
demands `q ≥ 2^{2(k−1)}`; Part II Thm 1 states the IOP for computation length
`T ≤ √|F|` [SOURCE]. Note the cap binds the **group size ⇒ Riemann–Roch dimension ⇒
trace height**, NOT the blocklength: Thm 12's domain is `|T| = ρ⁻¹·2^ℓ` — the blowup
comes free as ρ⁻¹ extra *cosets* of the 2^ℓ group (E(F_q)/G has ~q/2^ℓ of them). So
blowup is unconstrained; height is Hasse-capped.

For our primes [DERIVED from those statements + MEASURED prime values]:
- q0, q1 = `0xffffee001`, `0xffffc4001` are both *below* 2^36, so `Find_Curve`'s
  `q ≥ 2^{2(k−1)}` allows **k ≤ 18** ⇒ max height 2^18. Family needs 2^19 per limb —
  **short by 2×, structurally (Hasse), before any soundness or constants enter.**
- q2 = `0x1ffffe0001` ≈ 2^37 allows k = 19 ⇒ height 2^19 with **zero margin** — no
  headroom for degree-correction slack, masks, or growth, and the family is the
  *current* size, not the target.

**Worse, the soundness error at the needed geometry** [SOURCE, Thm 13 + DERIVED]: the
batched-FRI additive term is `O(ρ²|T|²/(ε⁷q))`. At the family's shape — height 2^19,
lb=3 ⇒ |T| = 2^22 — over q2 ≈ 2^37 this carries `|T|²/q = 2^44/2^37 = 2^7`: the bound
**exceeds 1 outright with base-field challenges**. The theorem as stated gives nothing
at our blocklengths over 36/37-bit fields. The rescue is drawing fold challenges from
an extension (§5) — the standard BCIKS-over-extension move our BabyBear stack already
uses — but it is **not in the papers**, whose statements are base-field-challenge only
[SOURCE for absence; DERIVED for the lift]. (Classic FRI over a 36-bit prime has the
*same* smallness and the *same* deployed rescue — this term is field-size, not
curve-specific; it just means EC-FRI is not even self-contained at our size.)

**The dominating alternative, priced** [MEASURED where marked]:

The limb primes are not imposed. `fhe.rs` exposes
`BfvParametersBuilder::set_moduli(&[u64])` (fhe-0.1.1, `src/bfv/parameters.rs:303`)
[MEASURED]; RLWE security depends on (degree, total log Q, error dist), not on which
NTT-friendly primes realize Q; the deployed set is merely `fhe.rs`'s default. Sieved
[MEASURED, sympy]: **68** primes of exactly 36 bits with v2(q−1)=24, **151** of 37 bits.
Top-of-range triple keeping the noise budget:

```
q0' = 0xfed000001  (36-bit, v2 = 24)
q1' = 0xfd9000001  (36-bit, v2 = 24)
q2' = 0x1ff5000001 (37-bit, v2 = 24)
total log Q = 108.978  vs deployed 109.000   (Δ = −0.022 bits; H1 margin untouched
                                              to within rounding, security side ≤)
```

With v2=24: classic FRI reaches **height 2^21 at blowup 8** — the whole 2^10–2^20 range
with a rung to spare, per limb, zero emulation, no curve, no new code family, no new
proximity theorem. What it costs (greenfield doctrine: a rebuild, named):

- new NTT twiddles per prime (mechanical; the wgpu kernels take moduli as data —
  `FourStep::new(&FOLD_MODULI, …)`);
- `FOLD_MODULI` is pinned by drift asserts (`dark_amm.rs:1530` among others) and baked
  into `moduli_digest` wire fields — **flag day: re-emit params, re-genesis, old
  ciphertexts refuse to load**. That is the cheap kind of breakage.
- re-run the H1 noise-margin measurement at the new triple (expected no-op at Δ=0.02
  bits, but measure, don't assume);
- one real check before committing: fhe.rs's own `generate_moduli`/NTT layer accepts
  arbitrary `set_moduli` primes ≡ 1 mod 2N — smoke-test encrypt/decrypt/mul at the new
  triple [UNRUN].

**Why not ECFFT even as a hedge**: it solves the constraint we can delete for free, at
a real constant-factor and formalization cost (§4, §6), and *still* needs the §5
extension analysis that is the actual hard residue. The one world where ECFFT re-enters:
proving statements over a prime someone else froze (a foreign chain's base field, a
standardized curve). Keep this note for that day.

## 4. THE SOUNDNESS STORY — what replaces RS-over-smooth-coset, and the named port gaps

**Shape of EC-FRI, at source (part II §6.3, §6.4, App. B):**

1. The witness lives in Riemann–Roch spaces K⟨ℓ⟩ = L([G⟨ℓ+1⟩]) on E; evaluation
   domains are unions of basic sets S = C ∪ (−C), C a coset of the 2^ℓ subgroup.
2. **The commitment-facing codes are PLAIN RS CODES over special domains**: the local
   isomorphism U₀ ≅ W₀ ⊕ W₀ (eq. 30) splits a curve-word h into two univariate words
   (h₀, h₁) on T = π(S) ⊂ F_q, fiber-by-fiber via an invertible 2×2 matrix per point
   (GL₂ per character; distance preserved over the paired alphabet) [SOURCE §6.4].
3. **The fold is along the x-line maps ψᵢ** (degree-2 rational maps, the isogeny
   pushed to P¹): fᵢ(X) = (χᵢ,₀·(fᵢ,₀∘ψᵢ) + χᵢ,₁·(fᵢ,₁∘ψᵢ)) · X^(2^(k−i−2)−1)
   (Lemma 4), folded as fᵢ₊₁ = fᵢ,₀ + zᵢ·fᵢ,₁ (eq. 27–28). Classic FRI is the special
   case ψ = X², χ₀ = 1, χ₁ = X, no degree-correction factor.
4. **Proximity/correlated agreement: UNCHANGED RS MACHINERY.** Thm 12 soundness
   `(1 − min{δ, √ρ} + o(1))^t`, Thm 13 batched: accept prob above
   `(√ρ + ε)^t + O(ρ²|T|²/(ε⁷q))` ⇒ correlated agreement on |V| ≥ (√ρ+ε)|T| — the
   BCIKS Johnson-regime statement, applied to RS over the arbitrary domain T. **The
   regime is Johnson (√ρ), not UDR, not capacity** [SOURCE]. Nothing curve-specific
   enters the proximity leg; the curve enters only through *which* T and *which* fold
   maps exist.

**Consequence for the Lean cone** (read in `minidregg/Selvage/Proximity.lean:165-194`
and the ingredient inventory): the commitment layer IS already agnostic — `FoldingData`
axiomatizes `dom : ι ↪ F` with no root-of-unity structure (0 `IsPrimitiveRoot` in the
tree, re-confirmed), and the smooth-domain reasoning lives separately in
`CyclotomicInertia`-style `2^ν ∣ p−1` existence lemmas. **Only the FOLD is new.** The
port, in named missing lemmas:

| # | missing lemma | replaces | contents |
|---|---|---|---|
| 1 | `PsiFoldingData` (generalize `FoldingData`) | `neg`/`dom_neg`, `sq`/`domSq_sq` | fiber involution `tw : ι → ι` with `pr ∘ tw = pr`, 2:1 projection `pr : ι → κ`, section, and twist columns `χ₀ χ₁ : ι → F` with per-fiber matrix `[[χ₀ i, χ₁ i],[χ₀ (tw i), χ₁ (tw i)]]` invertible. Classic instance: `tw = neg`, `χ₀ = 1`, `χ₁ = dom` |
| 2 | `psi_decomposition` | even/odd split (`foldEven_sq`/`foldOdd_sq` + reconstruction `E(x²)+x·O(x²)=f(x)`) | Part II Lemma 4: unique `f = (χ₀·(f₀∘ψ) + χ₁·(f₁∘ψ))·X^(d−1)` with `deg fⱼ < 2^(ℓ−1)` for `deg f < 2^ℓ`; the degree-correction exponent is per-level data |
| 3 | `fold_preserves_rs` | "even/odd parts of deg<d are deg<d/2" | image of the ψ-fold lands in RS of half dimension on the pushed domain `ψ(T)` |
| 4 | `pair_alphabet_iso_dist` | (new; no analog needed classically) | U₀ ≅ W₀⊕W₀ is per-fiber GL₂, Hamming distance over the folded alphabet preserved — the entry step from curve-word to RS-pair |
| 5 | domain-chain existence | `goldilocks_domain_exists`-style `2^ν ∣ p−1` | Thm 8/9: the isogeny chain E₀→…→E_k with cyclic G₀, |ψᵢ fibers| = 2. **This is the only lemma with real algebraic-geometry content** (Hasse + Vélu formulas + 2-descent for cyclicity); everything else is polynomial algebra |
| 6 | `coset_invariant` analog | `friFold_coset_invariant` | the ψ-chain maps evaluation domains at scale ℓ to scale ℓ−1 (part II Prop 1 structure) |

The proximity statements themselves (`ProximityGapUD*`, `JohnsonRegime`,
`CorrelatedAgreement`, the RBR/BCS stack) port **as-is** wherever they are stated over
abstract `dom` — the regime question (which of ours are proved vs interfaced) is the
same question as today, untouched by ECFFT. ⚠ Lemma 5 is the expensive one and exists
in NO proof assistant that I know of — but see the corpus caveat: instrument =
IACR mirror + paperbin + this session's reading; arXiv/ITP literature not swept.

## 5. THE SMALLNESS RESIDUE — mandatory under EVERY option, and already half-built

A 36-bit field is too small for ~124-bit FRI soundness *regardless* of domain
machinery: challenge-sample terms carry |T|/q and |T|²/q factors. The deployed answer
at BabyBear (31-bit) is degree-4/5 extension challenges; over 36-bit limbs a **degree-4
extension gives 2^144 challenge space** [DERIVED] — same shape. Our Lean tree already
holds exactly this analysis prime-field-natively (`Selvage/SmallField.lean`:
`smallField_bound_vacuous` / `smallField_bound_allows_certainty` /
`smallField_rescued_by_extension`, `extDomain = Embedding.trans` — domain transport
needs no root structure). **Port cost: instantiate at the (new) limb primes; the
statements are already field-generic.** Under ECFFT the same lift is needed but is NOT
in the papers (base-field challenges only) — one more reason the swap-the-primes route
is cheaper: its extension story is deployed practice with a formal home already.

## 6. Q2 — THE PRICE TABLE (papers' own constants where they give them)

- **Emulation deleted** (the prize, measured previously): 48 → 20 columns; committed
  elements ratio corrected to **4.80× padded** (h2-verdict correction #1, NOT the 16×
  headline — the 16× did not reproduce). Proof side is where the whole verdict lives
  (H2 §C: FHE-side share of total 0.19%).
- **ECFFT constant overhead, papers' own numbers** [SOURCE]: part II states the O(·)
  constants in Thm 12/13 prover/verifier/length are "each at most 10"; part I gives
  asymptotics only (O(n log n) EXTEND/multiply, O(n log² n) full interpolation— and
  the IOP uses the O(n log n) pieces). Per fold layer the fiber solve is a 2×2 linear
  step (~4 mul per pair) against the classic butterfly's 1 mul per pair ⇒ **~4× DFT
  multiply count** [DERIVED from eq. 28; see §7 for measured wall-clock from
  implementations]. DFT is 80% of prover arithmetic at b=6, 46% at b=3
  (field-op-counts §0), and the prover is hash-bound by 5.0–7.2× (§5 there) — so a 4×
  DFT-mul inflation lands as roughly ≤1.6× on the arithmetic side and **≈nil on the
  hash-bound total**: ECFFT's overhead would be affordable IF it reached the geometry.
  It does not (§3). The pricing kills it on reach, not on constants.
- **Swap-the-primes**: overhead **1.00×** by construction (same bit-widths, same NTT
  shapes, same everything; only the constants change). Flag day priced in §3.
- **Fallback if neither** (status quo): keep proving limb arithmetic over BabyBear at
  4.80× committed elements — the measured baseline all of this is bidding against.

## 7. Follow-up literature and implementations — the constants that exist

Corpus + instrument named per policy: IACR mirror (to 2026/1053+), ~/paperbin, plus a
live web search 2026-08-16 (so this section is NOT blind to arXiv/grey lit).

- **wborgeaud/ecfft-bn254** (Rust, BN254 base field, 2-adicity 1) [MEASURED by author,
  read from README]: at n=2^14, ENTER (multipoint eval, the O(n log² n) op) = 275.5 ms
  vs classic FFT 4.58 ms — **60.2× slower than an FFT of the same size** (and 28.1×
  faster than naive). Precomputation via sage (coset + isogeny tables). ⚠ ENTER is the
  *wrong op to quote for a prover*: an LDE is EXTEND-shaped (O(n log n)); ENTER is
  ~log n stacked EXTEND layers, so per-layer EXTEND ≈ 60/14 ≈ **4–5× a same-size FFT**
  [DERIVED] — consistent with the 2×2-fiber-solve-vs-butterfly count (~4× muls).
  Take "ECFFT LDE ≈ 4–6× classic LDE" as the working constant; nobody has published a
  tuned prover-grade number [absence: this corpus + this search].
- **Bordage–Lhotel–Nardi–Randriam, "IOPs of Proximity to AG Codes"** (arXiv 2011.04295,
  CCC 2022): the independent AG-IOPP line — FRI generalized to Kummer curves (linear
  prover, log verifier) and Hermitian towers. Read at abstract level only; soundness
  regime not stated in abstract [flagged, unread-in-full].
- **BCHKS 2025, "On Proximity Gaps for Reed–Solomon Codes"** (ECCC TR25-169): sharper
  list-decoding-regime bounds for standard FRI — feeds our FRI-reality ledger
  (conjectured-130/proven-51–73 pair), orthogonal to the domain question. Not read in
  full; logged for the FRI-reality file's next pass.
- **Syndrome-space proximity gaps for random linear codes** (arXiv 2605.07595, 2026):
  adjacent theory, not domain-relevant here.
- **Circle STARKs** (M31): inapplicable to our primes — needs 2-adic p+1 (p ≡ 3 mod 4);
  all three limb primes have v2(q+1) = 1 [MEASURED, §1].
- Nothing in the 2026 eprint series found extending EC-FRI itself (searched: mirror
  filenames + web). Absence claim scoped to: IACR mirror to ~777 full-text / titles
  beyond, one web search session.

## 8. ARCHITECTURE SKETCH — three limb-native provers, binding, recursion

Sketch assumes the §3 prime swap (v2=24), classic FRI per limb; the same skeleton
holds under EC-FRI where domains permit, so this section is route-independent.

**Leaves — three limb-native provers.** Each limb prime qᵢ gets its own STARK stack:
trace over F_qᵢ (native width ~20 cols vs 48 emulated, per h2), FRI over the 2^24-adic
subgroup of F_qᵢ*, challenges from the degree-4 extension F_qᵢ⁴ (≈2^144, §5). Per-limb
height 2^19 padded at the full family; blowup 8 ⇒ domain 2^22 ≤ 2^24 ✓. Needs per-field
instances of: Poseidon2 (new round constants + MDS per prime — a real design/emit task,
the Lean-authored-AIR law applies), the DFT (mechanical), and the AIR emit path
retargeted from BabyBear to field-generic (the AIR is already field-generic —
`impl<AB> Air<AB> for Ir2Air where AB::F: PrimeField32` — but witness gen is
monomorphic; field-op-counts §0 names this exact seam, and PrimeField32 itself breaks
at 36 bits ⇒ a PrimeField64-shaped bound. **Grep-first law applies: the witness-gen
for 36-bit fields does not exist; this pass is BUILD, not route.**)

**Cross-limb binding.** ⚑ Limb-native proving REOPENS what row-interleaving closed for
free: `cross-limb-verdict.md`'s fix (limbs share one committed row ⇒ shared opening,
+0 felts) is only available when all limbs live in ONE trace over ONE field. Three
proofs over three fields have three transcripts; provenance (`∃source ∀i`) must then be
carried by an explicit cross-proof object. That object is the sibling lane's Z_Q
sumcheck (cross-limb binding lane — reference, not duplicated here); the binding-not-
relation lesson (`cross-limb-verdict.md`: CRT-consistency is a tautology, the forgery
is CRT-consistent) applies verbatim to any cross-field binding proposal.

**Recursion — the wrap identity with non-BabyBear leaves.** A wrap's biggest table is
its child's verifier. Two-stage shape:

1. **Self-wrap per limb**: recurse each limb chain within its own field (FRI over F_qᵢ
   works at wrap heights trivially; the wrap verifier's hash rows are Poseidon2-over-
   F_qᵢ — native, keeping the 40× native-hashing win our BabyBear wrap accounting
   measured (40.9M → 1.02M R1CS, `field-recursion-evidence.md`)). Result: one small
   proof per limb.
2. **One aggregation step pays emulation once, verifier-sized**: a single prover (over
   BabyBear to reuse the existing recursion stack, or over q2' as the widest limb)
   verifies the three small wrap proofs non-natively. Emulating a 36-bit verifier in a
   31-bit field is the SAME 16→4.8× element class as today — but applied to a
   verifier-sized table (2^13–2^15 rows), not the 2^19–2^20 leaf: the emulation cost
   shrinks by the leaf/verifier height ratio (~2^5–2^6×). This is the standard
   asymmetry that makes mixed-field recursion affordable, and it is the entire reason
   limb-native leaves are winnable at all.

**What is reachable NOW at v2 = 13/14/17 (no re-genesis), for completeness** [DERIVED]:
per-limb relations of height ≤ 2^10 / 2^11 / 2^14 at lb=3 — enough for the current
1/98,304 sampled row category and for small per-limb gadget proofs, not for f→1.
q2's 41-smooth odd part additionally admits mixed-radix domains to ~2^23 if radix-3/5
folds were built — strictly dominated by the §3 swap in both effort and reach.

**Decision recommendation, priced**: take the §3 prime swap (a rebuild: params re-emit,
re-genesis, NTT smoke test, H1 re-measure); build the field-generic witness-gen seam;
keep this note as the ECFFT map for any future externally-frozen field. ECFFT itself:
**do not build** at our design point — blocked by its own n ≤ 2√q before constants
enter, and the constants (~4–6× LDE) would have been acceptable if it weren't.
