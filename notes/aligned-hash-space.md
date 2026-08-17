# The aligned-hash space — a PRF/relation constructional alignment, charted

2026-08-16. RESEARCH + CHARTING lane. Ember's frame, verbatim: *"raw binary blake3
or raw field poseidon2 may not be the best possible selections — maybe there's a
PRF constructional alignment that would make everything else fall into place."*
Basic research: map, formalize the statable spine, price against our measured
counts. **Nothing here is a proposal to deploy**; §3 states a design with named
obligations, and the Lean spine landed (`minidregg@c2dd38c`,
`Selvage/HashRelation.lean`).

Grounding, read first: `notes/hash-landscape.md` (baseline 300 cells/compression,
5.82× native, crossover `R* = 2.0–4.5×`), `notes/leaf-vs-recursion.md` §2c (the
perm split this note prices against), `notes/galois-levers.md` §1c (absorption is
at its information floor), `notes/ring-hash-tau-verdict.md` (the τ/integral
lesson), `Selvage/HashFamily.lean` (the two-instance interface this extends).

---

## 0. THE ORGANIZING INSIGHT, TESTED — it survives as economics and SPLITS as cryptography

The brief's thesis: *the circuit needs a cheap RELATION, not a cheap function.*
CCZ-equivalence / graph-degree asymmetry: the verifier checks `R(x,y)` of low
degree with `y` witnessed, never evaluating `H`.

**Verdict after charting: TRUE, and it is the load-bearing fact of the whole
in-circuit hash economy — and the design space it opens is BIMODAL in a way the
thesis alone does not predict.**

1. ✅ **As economics it is simply correct, and measured.** Every number in §1
   confirms it: the relation-designed family delivered `R ≈ 0.3–0.6×` of
   Poseidon — *below* Poseidon, which already sits 30.6× below Blake3 in a prime
   field (`hash-landscape.md` §1a). Our own deployed AIR is itself a relation
   trick: REG=1 witnesses the cube so α=7 checks at degree 3
   (`hash-verdict.md` §5, and now `pow7Witnessed` in Lean).
2. ⚑⚑ **As cryptography the asymmetry is ADVERSARY-SYMMETRIC — and the attack
   papers say so IN THEIR OWN WORDS, read at source this lane.** The relation is
   public; the low-degree system the verifier checks is the system the attacker
   models, witness variables and all. FreeLunch (2024/347), §2.1, verbatim: *"For
   STAP ciphers, the existence of low-degree models is usually possible by
   design: while such systems can be leveraged for cryptanalysis, they are also
   required for a fast verification in many ZK protocols."* And its Remark 1 on
   Griffin is the sharpest possible form: the attack's polynomial modelling *"is
   not new; in fact, it was proposed by the authors of this algorithm for their
   initial security analysis"* — **the attackers used the designers' own
   verification system and changed only the monomial order.** 2025/259 states
   its modelling *"coincides with the forward modeling"* of prior work — one
   witness `z_i` per α-inversion, constraint `z_i^α = f_i`, exactly the
   AIR-style witnessed relation set. 2026/1281 breaks Anemoi through the open
   Flystel — the very relation introduced *"with little verification cost
   overhead in a ZK setting"* (their words) — consumed as the attack
   constraint. **Minimizing the relation minimized the attacker's ideal; three
   papers, one mechanism, zero new modelling.** (One honest caveat: for Anemoi,
   FreeLunch derives an auxiliary polynomial `g*` inside the same ideal — an
   algebraic consequence of the verifier's relations rather than literally one
   of them.)
3. ⚑ **The sharpened form, and it is sharper than the brief's:** the design
   target is not "cheap relation" — it is **a relation cheap in the proof
   system's operations and expensive in the adversary's algebra.** Exactly two
   known resources have that shape:
   - **the lookup**: circuit cost O(1)/limb under LogUp, algebraic degree ≈
     |table| (a 2^8 table is a degree-255 polynomial). The lookup-designed line
     (Monolith / Tip5 / Reinforced Concrete) is the *surviving* cheap line —
     none broken, though young. This is the same lever `hash-landscape.md` §2
     found from the cost side alone (`R ≈ 3.2×` for Blake2s under Plookup, the
     one route that crosses `R*`): **the cost analysis and the security analysis
     independently select the lookup.**
   - **the dense linear layer**: degree 1, near-free in-circuit, and the thing
     whose *absence* is the recurring AO wound (Starkad 2020/188, HADES
     2020/179, Poseidon2's non-MDS internal matrix 2026/306 — every one traded
     diffusion for circuit cost, `hash-landscape.md` §3).
   And one resource that looks asymmetric and is NOT: **witnessing**. The
   attacker introduces the same auxiliary variables the prover does; the
   extended system is the same system. Nondeterminism moves cost, not hardness.
4. ⚑ **Our degree-3 rung makes "relation degree ≤ 3" concrete — and the record
   prices what it costs to hit it naively.** `cubicForm` (one committed slot per
   degree-3 relation, `Assurance/AirSumcheckCubic`) means any hash whose full
   witnessed relation is degree ≤ 3 drops into the engine without splitting.
   Vision's inverse S-box checks at degree 2–3 (the lowest in the family, and
   explicitly stated in Marvellous §7.1: "AIR with degree d = 2"); Griffin/
   Rescue check at degree α. **No hash was designed against a degree-3 sumcheck
   slot; the ones closest to it by accident are Vision (unbroken, unanalyzed)
   and the broken prime-field trio.** §3's sketch is what designing *for* it
   looks like, with the §1 lesson priced in: its S-box hardness budget is
   carried by F2-degree and the linear layer, never by relation degree.

The Lean form of the insight is landed and has teeth (§6): the relation view,
the named soundness obligation a structure cannot smuggle in, the machine-checked
degree-3-relation/degree-7-function asymmetry, and the deployed α=7 shape
graph-sound by `ring`.

---

## 1. THE RELATION-DESIGNED FAMILY — charted, with the record honest

Sources: designs read at source this lane (2022/840, 2022/403, 2020/1143 +
2019/426, 2024/633, 2023/1025, 2023/107, 2021/1038 — extracts in scratchpad,
lane A); breaks from `hash-landscape.md` §3's graveyard (already verified there)
plus lane B's mechanism reads. Costs are the papers' own units — ⚠ NOT
inter-convertible with our BabyBear cells except where derived below.

### 1a. The map

| design | the relation the verifier checks | rel. deg | their circuit cost (their unit) | native (their measurements) | record 2026-08 |
|---|---|---:|---|---|---|
| **Poseidon2** (baseline) | `x^α` forward; REG=1 witnesses the cube | 3 (witnessed) | **300 cells** = ours, measured | 944.6 ns/perm t=8 (Monolith T3); ours 22.8 ns/elt | **unbroken**; margin eroded (2026/306), Initiative moved to Poseidon1+MDS |
| **Anemoi** (2022/840) | closed Flystel: `(y−v)^α + βy² + γ = x`, `(y−v)^α + βv² + δ = u` | **α** (3/5) ⚠ not 2 | R1CS t=8 α=3: **160** vs Poseidon 296; AIR t=2: **126** vs 300 | 128.3 µs vs Poseidon 9.2 µs on BLS12 — **14× slower** | 🔴 **BROKEN** at ℓ=1 α=3: full 21 rounds at **2^70** vs 128 claim (2026/1281 T1; erosion line 2^118 → 2^80 → 2^70 across three papers) |
| **Griffin** (2022/403) | `x − y^d = 0` (one `x^{1/d}`/round) + Horst quadratics | **d** (3/5) | R1CS t=8 d=5: **162** vs Poseidon 363; per-round mults **2t+2** vs 3t | 89–114 µs; faster than Poseidon only at t≥16 | 🔴 **BROKEN**: full-round t≥12 α=3 at **2^64** (2024/347), improved to **2^51–55** (2025/259 T1); 7/10 rounds solved in <4h on ONE CORE |
| **Rescue-Prime** (2020/1143, 2019/426) | `y^α = x` per inverse round, two steps folded | **α** = 3 | AIR hash-mode **66 w·t** (m=2, 64-bit); R1CS 2m/cube | 415 µs vs Poseidon 19 µs (RC T1) — **22× slower**; ours: 1660 ms vs 100.9 ms Merkle | 🔴 **BROKEN** α=3 full 18 rounds **2^112**; α=5 margin exactly 0 (**2^128** on the nose, 2026/1281); Rescue 512-bit set fails outright (2^475, 2025/259) |
| **Vision** (2019/426) / **Mark-32** (2024/633) | `x·x′ = r`, `x(1−r) = 0`, `x′(1−r) = 0` (inverse S-box) + linearized affine | **2** (their §7.1, explicit) | AIR w=4m t=2 **d=2**; Mark-32 gives FPGA only (398 kLUT, 322 kbps/LUT vs Poseidon 34) | inversion = 1.58× a tower mult; no CPU numbers published | ⚠ **untested — zero attack papers, and nobody has looked** |
| **Monolith** (2023/1025) | degree-2 Bricks/Concrete + 8-bit **lookups** for Bars | **2 + lookup** | 192 lookups + 44 deg-2 constraints (t=8); Plonky2 measured **3.49 ms vs Poseidon 6.23 ms** | **129.9 ns/perm** — vs SHA3-256's 189.8 on the same box; ~15× Poseidon | unbroken; 2-round practical collision, margin real but thin; ⚠ **no BabyBear variant exists** (Bars bijection breaks; `hash-verdict.md` §4) |
| **Tip5** (2023/107) | `y = x^7` (12 lanes) + byte-split **lookups** (4 lanes) | **7 + lookup** | 122 base-col-equivalents vs RPO's 16 in Triton (their own −2.68× *net win* story) | 0.851 µs — 8.2× faster than Poseidon, 21× than RPO | unbroken; designers' own 3-round SFS collision = ~1 round margin |
| **Reinforced Concrete** (2021/1038) | degree-3 gates + **lookups** for Bars | **3 + lookup** | **378 Plookup gates** vs Poseidon's 633 (their T1 — the §2 crossover pointer's source) | 3.4 µs BN254 — 5× faster than Poseidon; ST field: 16× | unbroken, 19+ months; BN254-shaped (Bars needs the field structure) |

⚠ **Correction to the brief carried by this table**: the Flystel's verification
relation is degree **α**, not degree 2 — Anemoi never claims degree-2
verification in odd characteristic (the quadratics `Q` are degree 2; `E` is
`x^α`; lane A read Eq. (5) at source). The only degree-2 verification in the
family is **Vision's** — the inverse S-box — plus Monolith's degree-2+lookup.
CCZ is the *organizing trick* of the family, but the F_p instantiations spend it
at degree α.

### 1b. What the map says, in three lines

1. **The relation trick works: the whole family sits at `R ≈ 0.3–0.6×` of
   Poseidon in-circuit** (their own same-paper comparisons — Anemoi 160-vs-296
   R1CS, Griffin 162-vs-363, RC 378-vs-633). Against `hash-landscape.md`'s
   `R* = 2.0–4.5×` these all win the crossover *trivially* — cheaper than the
   incumbent, not merely under the bar.
2. ⚑⚑ **And the entire sub-Poseidon band in a prime field is broken or
   unanalyzed.** Griffin, Anemoi-ℓ1-α3, Rescue-α3: broken by the algebraic
   line that models exactly their verification relations. Vision: zero
   cryptanalysis. Monolith/Tip5/RC: unbroken but young, lookup-carried, and
   none instantiable over BabyBear (Monolith rejects our field by name; RC is
   BN254-shaped; Tip5 is Goldilocks). **Poseidon2 at `R = 1` is the cheapest
   unbroken, most-attacked point available in our field.** That is the same
   conclusion `hash-landscape.md` §3 reached from the graveyard side; the
   relation charting explains *why* the band below it died: the discount and
   the attack surface were the same object.
3. ⚑ **The lookup line is the only *surviving* discount, and it survives for a
   reason the thesis predicts once sharpened** (§0.3): its circuit cheapness is
   combinatorial, not algebraic — a table is a degree-|T| polynomial the
   Gröbner modeller cannot flatten. Monolith's designers state the design rule
   plainly ("can easily be transformed to table lookups for circuits" while
   staying "fast and constant-time in native x86"). This coordinates with the
   sibling Lasso/lookup lane — the highest-value open measurement remains
   `hash-landscape.md` §2's: price a lookup-arithmetized traditional hash in
   our blowup-cells. Referenced, not duplicated, here.
4. ⚑ **And one structural survivor inside the algebraic family, worth naming
   because §3 leans on it: full-field INVERSION blocks the FreeLunch shape.**
   2024/347's own scope statement: XHash12, RPO and Rescue-Prime *"contain a
   layer of inversion operations in all branches, and hence we cannot directly
   obtain a FreeLunch from them"* — and XHash8 comes out at 2^214–2^240,
   *"very secure against the techniques presented in this paper."* The
   resultant line later reached Rescue anyway (its `x^{1/α}` is still a power
   map), but the `x⁻¹`-in-every-branch shape has no direct FreeLunch modelling:
   the triangular one-new-variable-per-round structure the attack needs does
   not form. That is a mechanism-level (not merely record-level) point in favor
   of the inverse S-box — stated as evidence, not immunity.

### 1c. Priced at OUR counts, where the bridge is honest

Only two members can be priced in our unit without inventing an AIR:

- **Poseidon2-w16 BabyBear**: 300 cells / 1,192 blowup-cells (measured, ours).
- **Monolith-31**: 3,520 AIR cols, ≈900 granting LogUp (`hash-verdict.md` §4)
  — `R ≈ 3–11.7×` *and no BabyBear instance exists*.
- The prime-field trio would land ≈ 0.4–0.6× by their own ratios **if their
  round counts survived at 31 bits — and their breaks moot the exercise.**
  [DERIVED, shape-only; no 31-bit specification of any of them exists.]

The honest summary of §1 for us: **in BabyBear, today, there is no deployable
relation-designed hash cheaper than the one we run.** The family's value to us
is the design lesson (§0.3) and the Vision/inverse-S-box shape §3 builds on.

---

## 2. THE CHAR-2 TENSION — Frobenius in the linear layer only? ANSWERED, with the record read at source

The tension: Frobenius freeness makes binary algebraic hashes cheap (squaring is
F2-linear) AND arms attackers. The record, each read at source this lane:

| casualty | what was Frobenius-adjacent | the break | the mechanism, from the paper |
|---|---|---|---|
| **Chaghri** (2022/592) | Gold S-box `x^{2^32+1}` (**F2-degree 2**) + **SPARSE** linearized affine `B(x) = c₁x^{2^3} + c₂` (ONE Frobenius term) | 2022/991 (EUROCRYPT '23): full 8 rounds at **2^38**; reaches 13.5 rounds | **coefficient grouping**: with every layer a sum of Frobenius powers, the whole exponent set after r rounds collapses to one integer vector with recurrence `N'_i = N_{(i−3)%63} + N_{(i−35)%63}` — *"the algebraic degree increases linearly rather than exponentially"* |
| **AIM** (AIMer OWF) | Mersenne S-boxes `x^{2^e−1}` with small `e` — `(a+b)^{2^e−1}` factors into **products of Frobenius images**, an exact low-F2-degree representation | 2023/1133: 2^136.2/2^200.7/2^265.0 vs claims 149/214/280 — *"does not reach the required security levels"* | Möbius-transform exhaustive search on the low-degree representation *the designers knew about* and mis-priced |
| **AIM** again | first-layer S-boxes fed **identical inputs**; power maps linearize on subgroup guess (`x^{2^e−1}` becomes a **Frobenius map, hence F2-linear**, once `x^d` is guessed) | 2023/1397 (ASIACRYPT '23): full AIM-I 2^125.7, AIM-III 2^186.5 | simultaneous linearization of the whole first layer → AIM2 respec |
| **Poseidon2b** (2025/1893) | S-box `x^7` (hw 3, F2-degree 3) — Gold maps are IMPOSSIBLE in even-degree binary fields (their Lemma 1: no hw-2 exponent is coprime to `2^{2^m}−1`) | external rounds increased after 2026/306 disclosure; no full break | designers' own admission, §5.1.2: they *"cannot convincingly argue the security … against [subspace-trail] attacks due to the huge number of subspace trails of the S-box x ↦ x^7"* — F2-degree 3 caps invariant-subspace dimension only at n−3 |

Plus our held datapoint: integral properties survive **monotonically longer with
extension degree** (Beyne–Verbauwhede 2025/932, verified at the authors'
artifact: round 1 prime / 13 at degree 2 / 20 at degree 4 —
`ring-hash-tau-verdict.md`).

### The answer to the brief's design question — YES, and the record's own repair says so

**Is there a binary design that spends Frobenius in the LINEAR layer only,
keeping the nonlinearity Frobenius-opaque? Yes — and the Chaghri FIX is the
proof it is the right axis.** 2022/991's diagnosis, verbatim: *"the
vulnerability of Chaghri exists in the usage of a sparse affine transform."*
Their countermeasure kept the Gold S-box and **densified the linearized
layer** — `B'(x) = c'₁x + c'₂x^{2^2} + c'₃x^{2^8} + c'₄` — *"almost cost-free
for FHE protocols"*, restoring *"an almost exponential increase of the
algebraic degree"*, and the designers adopted it. **The repair to the canonical
char-2 break was: spend MORE Frobenius, in the LINEAR layer.**

The refined discriminators, from the four rows above:

- **F2-degree of the nonlinearity** is the rate-limiter of degree growth
  (Chaghri deg-2 → linear growth → dead; Poseidon2b deg-3 → subspace-trail
  unease, admitted). **`x⁻¹` is the canonical extremal point**: F2-degree
  `n−1` — the maximum any bijection attains — while its verification relation
  is the cheapest nonlinear relation that exists: `x·y = 1` (degree 2), degree
  3 complete with the zero branch (`x²y = x ∧ xy² = y`). Simultaneously
  extremal on both axes — most opaque to every F2-degree-driven attack in the
  table, cheapest for the verifier, and (§1b.4) the shape FreeLunch's own
  authors could not model. No power map shares this: Gold is F2-degree 2 and
  not even invertible in our towers; `x^7` (the forced tower power map,
  `gcd(7, 2^{2^k}−1) = 1` always) is F2-degree 3 and relation degree 7.
- **Density of the linearized mixing** is the second axis, and it is a
  *quantitative* one, not a boolean: one Frobenius term killed Chaghri, three
  fixed it. Any linearized mixing layer must come with its coefficient-grouping
  recurrence actually computed — which is exactly [WEFT-coeffgroup] in §3.

So the shape is: **dense linearized-polynomial mixing + inverse S-box** —
Vision's skeleton, sharpened by the two discriminators. What pointing at Vision
does NOT settle: its record is empty because nobody looked (§1), and Mark-32's
own affine `B` is **sparse** (4 terms — the Chaghri-shaped corner of an
otherwise well-shaped design; its inverse-direction `B⁻¹` is dense, which is
where its degree growth actually lives). §3 inherits the skeleton with the
mixing layer replaced by our proved transform, and names the obligations the
replacement creates.

---

## 3. ⚑ THE MAXIMALLY-ALIGNED SKETCH — "Weft": the hash whose mixing layer IS the proved transform

**Substrate said out loud: this is a DESIGN STATEMENT with named security
obligations, not a proposal to deploy, and its circuit form would be
Lean-authored on the day it becomes one.**

### 3a. The alignment being purchased

The wrap's measured perm economy (`leaf-vs-recursion.md` §2c, exact split of
38,168): **per-query leaf sponge 64.9% + OOD/grind absorption 29.2% = 94.1% of
in-circuit permutations are hashing; 5.9% is Merkle paths.** Meanwhile the
additive-BaseFold line already holds, proved: the LCH novel-basis packing
(`novelPack`, window bijection, unconditional degree bookkeeping —
`Selvage/AdditiveBaseFold.lean`), the char-2 descent `friFold` over cosets
`{x, x+β}`, and the Fan–Paar tower with its packing bijection
(`Theory/BinaryTowerFanPaar.lean`: `towerPack_bijective`, `towerMul_eq_mul`).
The proof system's *code* is an additive-NTT evaluation; the proof system's
*hash* is, today, an unrelated object. Weft is the statement: **make the hash's
mixing layer the same linear map the code already is.**

### 3b. The design, one screen

- **Field**: the Fan–Paar tower `T₅ = GF(2^32)` (already our proved tower;
  Mark-32's field, independently — convergent choice).
- **State**: t = 24 elements (rate 16 = 512 bits, capacity 8 = 256 bits — the
  2-to-1 Merkle compression is one permutation, matching our 1:1 invocation
  geometry).
- **Nonlinear layer**: tower inverse `x ↦ x⁻¹` (0 ↦ 0) on every lane — the §2
  extremal S-box. Witnessed relation per lane: `x²y = x ∧ xy² = y` — **degree 3
  complete, one aux per lane**, i.e. exactly one `cubicForm` slot per lane per
  round in the degree-3 rung. Tower-recursive inversion natively (1.58× a
  multiplication, Mark-32's own measurement).
- **Mixing layer**: the **additive-NTT butterfly network itself** — evaluate
  the state (as coefficients in the novel basis) over a 24-point F2-affine
  coset, i.e. the same `Ŵᵢ`-structured transform `novelPack` proves and the
  same kernel the encoder runs. F2-linear ⇒ all Frobenius spend is here (§2's
  answer embodied).
- **Round constants** from the transcript-separation tags we already use;
  rounds: OPEN — set by the obligations below, floor 8 by Vision's analysis
  shape [ASSUMED-BY-ME until [WEFT-integral] is run; Vision's 8 came from
  Gröbner-3/interpolation-4 rounds ×2 at a *dense-MDS* mixing layer].

### 3c. Consequences, priced

| consequence | what it deletes / shares | priced against |
|---|---|---|
| **hash linear layer ≡ code encoding map** | ONE proved linear object in the TCB (the `novelPack`/additive-NTT chain, already on disk) instead of two; ONE GPU kernel family in the arena instead of hash-MDS + encode | the entire second verification artifact — a *proof-mass* saving, not cells |
| **Merkle-commit and FRI-fold share circuitry** | the wrap already evaluates additive-coset butterflies for `friFold`; the leaf sponge's mixing rows become instances of the same AIR family | the sharing target is the **64.9%** per-query leaf-sponge share — the dominant term of the wrap, which no other lever on our books touches (`sumcheck-batched-opening.md` attacks HornerAcc; this attacks the perms) |
| **S-box relation degree ≤ 3** | the whole permutation's witnessed relation drops into `cubicForm` slots — no bit decomposition anywhere | t·R aux cells + linear-layer constraint terms; [DERIVED, shape-level] ≈ 24·R cells/perm ≈ 200–400 at R=8–16 vs Poseidon2's 300 — **R ≈ 0.7–1.3× in a system where the fold is native char-2** |
| **absorption is bytes, not embeddings** | 512-bit rate absorbs raw digests/rows with no felt-packing layer | the 29.2% absorption share is at its information floor (`galois-levers.md` §1c) — Weft does not shrink it below the floor, it removes the packing overhead around it |

⚠ **The honest scope line: Weft lives on the additive-BaseFold rung, not in
BabyBear.** In our deployed two-adic prime stack, a char-2 hash would need bit
decomposition and lose 30× (`hash-landscape.md` §1a). The sketch is the aligned
end-state of the *binary* line — the line whose fold (`friFold`) and code
(`novelPack`) we have proved and whose `HashFamily` char-2 instance exists. It
is the answer to "what would the binary stack's hash be if everything fell into
place," which is precisely the brief's question.

### 3d. The named security obligations — none waived, one loud

- **[WEFT-subspace] ⚑ THE LOUD ONE — ⛔ RESOLVED 2026-08-17: KILLED AS
  SPECIFIED.**
  ⚑⚑ **RE-OPENED AND CORRECTED THE SAME DAY — `notes/weft2.md`
  (`~/src/ring-ro-hash/weft2_structure.py`). The kill STANDS; its stated REASON
  does not.** (a) **Branch 6 is not disqualifying**: at GF(2³²) one active `x⁻¹`
  is worth 30 bits on *both* sides (measured: δ=4, |W| = 2^(n/2+1) exactly), so
  branch 6 buys 180 bits per 2 rounds against a 128-bit bar — and Poseidon2's own
  internal layer is **branch 2 and ships** (`ring-hash-design.md:326`). The
  Poseidon2 comparator below is also **cross-characteristic** (M_E's {1,2,3}
  entries collapse in char 2; the char-2 reduction reads ≤ 8, which the repair
  matches). (b) **The flag is 5 deep, not 4** — `weft_branch.py:300` loops
  `range(1,5)`, and the skipped level `b=0` is a **fixed lane**: `output lane 0 =
  input lane 0`, an autonomous 32-bit quotient `x₀ ↦ x₀⁻¹ + c₀` that **round
  constants cannot break** (constants break invariant *subspaces*, not invariant
  *quotients*). That is the real kill, `B_l = 2` is its shadow, and **no branch
  number sees it**. (c) A third defect, unrecorded: with `βⱼ = 2ʲ` every matrix
  entry lies in **GF(2⁸)**, so `(GF(2⁸))²⁴` = 2¹⁹² is round-invariant unless the
  constants leave GF(2⁸) — and small-integer transcript tags do not.
  ⭐ (d) **The fallback clause below is NO LONGER the only live form**: evaluating
  on an affine **coset** (same butterflies, shifted twiddles, **zero ops**) gives
  `B_d = 8 EXACT`, `B_l ∈ [8,10]`, **zero** invariant subspaces either side,
  diffusion depth 1, no twisted-subfield structure, and observability at all 24
  lanes — **one transform, so the "ONE proved linear object" prize survives**.
  See also `post-weft-hash.md` §3's two-transform systematic-RS form (MDS *by
  theorem*, branch 25) — the stronger result and the more expensive one (1.68×
  native), and ⚑ it is *still* a GF(2⁸) matrix at the natural point set.
  Measured (`~/src/ring-ro-hash/weft_branch.py` @737ea7b, exact
  and certified, method + numbers in `notes/k16-proof-and-weft.md` §2):
  **branch(novel-eval mixing, t = 24, GF(2³²)) = 6** against the MDS bound 25 —
  below even Poseidon2's non-MDS external layer (8 at t=16 EXACT, ≤10 at t=24).
  Witness: span{X̂₁₆, X̂₂₀} = s₄·(s₂−c), 20 of 24 points zeroed;
  basis-independent (3 random domain bases identical). Worse than the number:
  the evaluation matrix is **block-triangular along the subspace flag** — the
  lane subspaces {lanes ≥ 2^b} for b = 1..4 map into themselves, and the
  lane-wise x⁻¹ S-box (0 ↦ 0) preserves them too, so the round carries a
  **4-deep nested chain of invariant lane subspaces** up to round constants —
  the 2026/306 subspace-trail shape present by construction. The alignment
  thesis imports the code's triangularity, and triangularity is the opposite
  of diffusion. **The fallback clause below is now the only live form** (dense
  layer composed in ⇒ the one-proved-linear-object consequence is lost);
  [WEFT-integral]/[WEFT-groebner] should not be run against the dead layer.
  ⚑ **UPDATE 2026-08-17 (`post-weft-hash.md`): the composed fallback is now
  MEASURED-KILLED too** — branch(D·E) ≤ 11, branch(E·D) ≤ 21 against D alone
  at 25 (`ring-ro-hash@04d0d95`): composition destroys the flag but LOSES
  branch points at higher cost. **And the one-proved-linear-object prize is
  RECOVERED by a different construction**: the systematic-RS form
  `A = V₂·V₁⁻¹` (interpolate on the window, evaluate on a DISJOINT point set —
  Mark-32's own §3.3 MDS) is branch-25-by-theorem on the same proved
  butterflies. The successor design, if the char-2 slot ever opens, is
  Mark-32-adopted — see `post-weft-hash.md` §3–4, §7.
  *(Original statement, kept for the record:)* The additive-NTT butterfly
  network is sparse and structured — 2-point butterflies over F2-affine
  cosets. The recurring AO death is exactly a structured-for-cost linear layer
  (Starkad, HADES, Poseidon2's `Mε` — three for three, `hash-landscape.md`
  §3). The alignment thesis wants the mixing layer to be the encoder; the
  attack record says structured linear layers are where these designs die.
  If the branch number is bad, Weft composes the transform with a cheap dense
  layer and loses some of the sharing — that fallback must be priced, not
  assumed away.
- **[WEFT-integral]**: Beyne–Verbauwhede monotonicity (integral properties
  survive 1 round prime / 13 deg-2 / 20 deg-4) says a degree-2^k tower is the
  extreme point of the axis that punished the ring hash's τ=4. The x⁻¹ S-box's
  maximal F2-degree is the counter-bet. Obligation: the integral/HOD bound at
  Weft's exact parameters (the settling instrument exists — the 2025/932
  authors' own notebook, as in `ring-hash-tau-verdict.md`).
- **[WEFT-coeffgroup]**: coefficient-grouping resistance must be shown against
  *this* linear layer, not inherited from Vision — the attack is precisely
  bookkeeping on how the linear layer routes Frobenius images (§2's Chaghri
  row: the exponent-set recurrence is computable in seconds, 2022/992 gives it
  in O(n)). Density is the quantitative axis — one Frobenius term killed
  Chaghri, three repaired it — so the obligation is concrete: compute the
  recurrence for the 24-point transform's per-coordinate linearized
  polynomials and exhibit the degree-growth bound. With the x⁻¹ S-box at
  F2-degree n−1 this should be the *easiest* obligation on the list; it still
  gets computed, not presumed.
- **[WEFT-groebner]**: relation degree ≤ 3 is adversary-symmetric (§0.2). The
  inverse S-box hands the attacker the same degree-2/3 equations it hands the
  verifier; rounds must be set by the Gröbner analysis at the tower, in the
  post-FreeLunch methodology, not by Vision's 2019 numbers.
- **[WEFT-indiff]**: sponge indifferentiability at rate 16 / capacity 8 —
  inherits the open `SpongeIndiffGame` upstream, same as the deployed hash;
  stated, not discharged, per house law.
- **[WEFT-σ-lesson]**: the ring-hash verdict's transferable lessons apply — a
  de-linearizer that is not itself analyzed is a hole, and any "free" structural
  saving (there, the norm check; here, the shared butterflies) is an ASSUMPTION
  until the AIR is written and counted.

### 3e. The settling measurement

One number decides whether Weft leaves the page: **the Weft permutation's
committed cells in an additive-BaseFold wrap, against Poseidon2's 300/1,192**
— written as a Lean-emitted AIR (house law), with the butterfly-sharing either
realized or priced as separate rows. Under ~2× the aligned line is real; the
64.9% share is the prize it plays for.

---

## 4. THE JOB-SPLITTING CORNER — refuted three independent ways

The idea: Fiat–Shamir needs RO-likeness; grinding and challenge *expansion*
need only PRF/PRG-ness; the Legendre/power-residue PRF checks via a witnessed
square root. Does splitting the transcript's jobs move real cost off the 29.2%
absorption share?

**No — by counts, by per-bit cost, and by the PRF's own security record. Any
one of the three closes it.**

### 4a. By counts: the PRF-able jobs are 2.2% of the wrap

- The 29.2% (11,128 q-independent perms) is **absorption**: 82,256 base felts
  of OOD values ≈ **10,282 perms** of pure data intake (`galois-levers.md`
  §1c), already at the information floor — rate-8 overwrite sponge, no padding,
  4 felts per Ext4 value with all four needed. **Absorption is a compression
  job: it needs collision-binding over the whole transcript, which is exactly
  the property a PRF does not provide.** A keyed PRF consumes a fixed-size
  input; to bind 82k felts it must be iterated into… a sponge/tree, i.e. the
  thing we already have.
- The PRF-able jobs — grind check, squeeze/expansion of challenges and query
  indices — are the *remainder*: **≈846 perms ≈ 2.2% of the wrap's 38,168.**
  [DERIVED: 11,128 − 10,282.] Even a FREE verifiable PRF moves ≤ 2.2%, under
  the staircase's free step (`hash-landscape.md` §2: 1.4–1.7× row headroom).
- Independent corroboration that this shape is universal, from the one system
  that actually ships a Legendre-PRF SNARK: **Loquat** (2024/868) verifies its
  own Legendre-based signature in **102,089 R1CS of which 95,480 — 93.5% — is
  hashing** and 6,609 is everything algebraic. Even where the Legendre PRF IS
  the primitive being proven, the circuit is the transcript's hash volume.
  (Ours: 94.1% of wrap perms are hashing, `leaf-vs-recursion.md` §2c. Same
  number, two systems, no shared code.)

### 4b. By per-bit cost: the PRF loses locally too

The "~1 constraint/bit" folklore is not in the literature; the measured claim
at source (Loquat, p.10, read this lane) is **3 multiplication gates / ~4 R1CS
per Legendre symbol** for the masked residuosity check (`t_ℓ = s_ℓ²` with the
root witnessed off-circuit; Seres–Horváth–Burcsi count the same 4/symbol).
One symbol = one bit. Poseidon2 absorbs at ~300 cells per 248-bit rate block ≈
**1.21 cells/bit**. Units differ (R1CS vs cells), but the direction does not:
**the PRF is not cheaper per bit than the sponge it would replace, even before
security.**

### 4c. By the record: the Legendre PRF cannot clear our bar in our fields

Key-recovery record (lane C, read at the papers): Khovratovich 2019/862
O(√p); BBUV 2019/1357 `O(p log²p/M²)` at M queries; **Kaluđerović–Kleinjung–
Kostić 2020/098: `O(√p · log log p)` with only ~p^{1/4} queries** — they solved
Ethereum's 64/74/84-bit challenges. Quantum, classical queries only: **O(∛p)**.
And the power-residue generalisation is **easier, not harder** — BBUV §7.3:
the r-th-power variant falls by a factor ~r·log²r.

| field | key space | classical attack | quantum | our bar |
|---|---:|---:|---:|---:|
| BabyBear `p` | 2^30.9 | **≈2^17.7** | 2^10.3 | 2^123.6 |
| `p⁴` (Ext4) | 2^123.6 | **≈2^64.6** | **2^41.2** | 2^123.6 |
| needed for 128-bit | ≥2^256 | 2^128 | — | — |

**A 128-bit Legendre key needs a ≥256-bit field — degree ≥9 over BabyBear.**
The Ext4 instantiation sits ~59 bits below our own bar; the base field is not
even wrong. Query-limiting does not rescue it (to hold 128 bits over Ext4 the
adversary must see ≤ ~6 symbols, ever — a publicly verifiable proof leaks all
of them). ⚠ Caveat carried from the harvest: the √q bound for the quadratic
character over an *extension* field is the conservative structural assumption,
not an explicitly published theorem — it would need checking in the fantasy
world where anything else had survived.

### 4d. Where the RO boundary sits, and the prior art for the split

Round-by-round soundness needs each round's challenge to be an RO image of a
*binding digest of the full transcript so far*. What may live below the
boundary is only the *expansion* of an already-RO-derived seed into index bits
(PRG suffices against a computationally bounded prover, at the cost of leaving
the pure ROM story). That is precisely the ≤2.2%.

The split shape does exist in the literature — for GRINDING, with a BLOCK
CIPHER: **Rivain 2026/1625** proves (ideal cipher + ROM) an AES-based PoW for
MPCitH signatures where the RO still binds the ciphertexts into the FS
challenge. That is the correct boundary placement, proved by someone else, and
it moves native grinding cost only — grinding cost is a *security parameter*,
so cheapening the attempt cheapens the attacker identically; a latency
re-shuffle, not a saving. The opposite direction also exists: CAPSS (2025/061)
*unifies* leaves, FS-XOF and grinding on one AO permutation. **Nobody in
either corpus proposes a PRF for challenge derivation** — absence claim, with
instruments: `~/paperbin` (515 extracted texts of 1,635 files, full-text
grepped), IACR mirror 2019–2026 first-page scan (~11,000 PDFs, 38 Legendre
hits, all examined) + full text of the 15 relevant Legendre papers; the mirror
is cryptology-only and first-page matching misses body-only uses.

> ### **The transcript's jobs are already split correctly.** The expensive job
> (absorption) is the one that genuinely needs the RO-style object, and it is
> at its information floor; the jobs a PRF could take are 2.2% of the wrap.
> The alignment prize is not in the transcript's *primitive*; it is in the
> transcript's *volume* — which is the jagged/width story
> (`leaf-vs-recursion.md` §5), not a hash story.

---

## 5. THE NATIVE-SIDE ALIGNMENT — Blake3 IS a Merkle tree (Bao)

Blake3's internal structure is a binary Merkle tree over 1 KiB chunks; Bao
exposes it: the root is a commitment, and a Bao slice is an authenticated
opening. "Commitment = one Blake3 traversal, openings = Bao slices."

**What it deletes natively.** For every proof a NATIVE verifier consumes —
the 18 `verify_*` entry points of `hash-landscape.md` §4 — the separate
Merkle-tree layer over leaf data stops existing: hashing the data IS building
the tree, in one pass, at Blake3's 8.2 ns/elt against Poseidon2's 22.8
(measured, ours). It stacks on §4's already-established 1.5–2.3× native win —
same class, zero new cryptanalytic surface (Blake3 is already in our TCB), and
it additionally deletes the value→felt→rate packing layer (bytes absorb as
bytes). Streaming/incremental verification of large witnesses comes free
(that is what Bao is).

**What it costs in-circuit.** A Bao path is Blake3 compressions: **9,168
cells each vs 300** — the measured 30.6×. Granularity is honest to name: Bao
authenticates 1 KiB chunks, and our FRI query rows (~135 × 4 B ≈ 540 B) fit
in one chunk, so the per-query cost is ~1 compression-chain per level — same
shape as now, 30.6× the unit price. **Recursion-facing layers cannot take it,
by the same crossover that pinned everything else.**

**Does lookup-arithmetization change the verdict?** It is the only thing that
could: `hash-landscape.md` §2's pointer (Blake2s at 3.16× Poseidon under
Plookup) lands *inside* `R* = 2.0–4.5×`. If the sibling lookup lane's
measurement prices a lookup-Blake3 AIR under ~4,000 blowup-cells, then
Bao-committed data becomes recursable at crossover-competitive cost — and the
end-state is **one hash, Blake3, on both sides of the boundary**: commitment
= its own tree natively, openings re-checked in-circuit via lookups. That
would be the traditional-hash mirror image of §3's Weft — the two
maximally-aligned end-states, one per characteristic-of-the-proof-system.
Until that measurement exists, the verdict stands as `hash-landscape.md` §6.2:
take the free native class now; leave recursion on the algebraic hash.

---

## 6. THE LEAN SPINE — landed, with teeth

`minidregg@c2dd38c`, `Selvage/HashRelation.lean` (343 lines), `Selvage` builds
green (3,096 jobs), import boundary green, axiom pins on every tooth, no
`sorry`, no bare `#guard`.

| layer | object | teeth |
|---|---|---|
| relation view | `RelationView H` = `rel` + completeness; **`GraphSound` is the NAMED obligation** | `slack_not_graphSound`: a vacuous check inhabits the interface and is REFUSED the obligation — carrying the structure buys nothing |
| non-graph refusal | `IsGraphOf` | `squareRel_refused`: `y² = x²` over `ZMod 11` relates 1 to both 1 and 10 — the graph of NO function, by the generic `not_graphOf_of_ambiguous` |
| polynomial presentation | `PolyRelationView` — the relation is an `MvPolynomial`, its degree is `totalDegree`, a theorem-bearing number; `Degree3Statable` names the rung's cap | `cubeRootRel_degree3` + `cubeRootRel_graphSound` |
| ⚑ the asymmetry | **`cubeRoot_asymmetry`**: over `ZMod 11`, cube root = `x^7`; its graph relation `y³ = x` is totalDegree-3 and graph-sound, AND no cubic polynomial computes the function (exhaustive, 11⁴ coefficient vectors) | the CCZ/Flystel/Griffin trick as one machine-checked statement, at the smallest scale where it is genuinely present |
| witnessed relation | `WitnessedRelationView` — prover-supplied intermediates; the projected relation is the ∃-image | `pow7Witnessed`: the deployed α=7 REG=1 S-box shape, **graph-sound by `ring` over ANY CommRing** (`[propext]` only), instantiated at the deployed BabyBear |
| deployed fit | `poseidon2NodeGraphView` — the shipped node map fits the interface | honest label carried in-file: the graph view has no degree bound and evaluates nothing (the 47.6 GB perm stays unreduced); the witnessed presentation of the FULL permutation is the named next unit, not smuggled |

Design notes worth recording: the `sorryAx` tripwire fired once during
development — the first build's `#print axioms` pin caught a failed `decide`
that had degraded to `sorry` inside an error recovery, exactly the class the
pins exist for; fixed by `show`-typing the decidable goals. And
`pow7Witnessed_graphSound`'s `[propext]`-only axiom record is the cleanest in
the file — the deployed S-box's soundness needs no choice and no quotients,
just ring identities.

---

## 7. WHAT THIS CHART SAYS TO DO

1. **Keep Poseidon2 on the recursion layers of the prime stack** — §1 closes
   the last escape hatch the crossover left open: the sub-`R*` band exists and
   is broken or unanalyzed. (Same action as `hash-landscape.md` §6.1, now with
   the relation-family evidence attached.)
2. ⚑ **The lookup measurement is now doubly selected** — cost (`hash-landscape`
   §2) and security (§0.3 here) independently pick it. It stays the
   highest-value open measurement; sibling lane's.
3. ~~**Run [WEFT-subspace] before any further Weft work**~~ — **DONE 2026-08-17,
   and the answer was bad: branch 6/25, plus a 4-deep round-invariant lane-
   subspace flag (§3d, `k16-proof-and-weft.md` §2). The sketch as written is
   killed; only the dense-composed fallback survives, re-priced without the
   one-linear-object prize.** ~~fallback~~ — **the fallback is ALSO killed by
   measurement (2026-08-17, `post-weft-hash.md` §2), and the prize returns via
   the systematic-RS form instead (§3 there); the whole slot is moreover
   DISSOLVED for now by the recursion-scenario check (§1 there).**
4. **The job-split is answered: leave the transcript alone** (§4). Any future
   "cheaper FS" idea must attack absorbed VOLUME (jagged/width), not the
   primitive.
5. **Take the Bao/native class alongside the §4 audit of hash-landscape** —
   same audit, same flag day, strictly more deletion (§5).
6. **Next Lean unit, named**: the witnessed `PolyRelationView` of one full
   Poseidon2 round (compose `pow7Witnessed` through the real round structure) —
   turning the deployed AIR's degree-3 presentation into a theorem-bearing
   object instead of a Rust-side fact.

---

## Provenance

Design facts: read at source this lane (eprint 2022/840, 2022/403, 2020/1143,
2019/426, 2024/633, 2023/1025, 2023/107, 2021/1038; extracts under the session
scratchpad, `alignhash-A-*`). Break record: `hash-landscape.md` §3 (verified
there) + attack-mechanism reads at source this lane (2024/347 incl. Remark 1,
2025/259, 2026/1281, 2022/991 + the 2022/592 design, 2023/1133, 2023/1397,
2023/1474, 2025/1893 §3.2.1/§5.1.2, 2025/102; extracts `alignhash-B-*`).
Legendre record read at source (2019/862, 2019/1357, 2020/098, 2021/645,
2024/868 p.10, 2021/182; extracts `alignhash-C-*`). All shares and cells: ours, committed
(`leaf-vs-recursion.md`, `galois-levers.md`, `recursion-tower-profile.md`,
`hash-verdict.md`). Lean: `minidregg@c2dd38c`, built and boundary-checked this
lane. ⚠ Corpus disclosure: literature claims rest on `~/paperbin` + the IACR
mirror (cryptology only, 2026→1053+); absence claims name their corpus and
instrument inline, and the Vision "nobody has looked" is `hash-landscape.md`
§3's, not re-swept here.
