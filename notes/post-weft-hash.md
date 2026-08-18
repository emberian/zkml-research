# Post-Weft: the successor charting, gated — and the dissolve-check that closes the slot

2026-08-17. DESIGN + CERTIFICATION lane, successor to the killed Weft sketch
(`aligned-hash-space.md` §3, killed by `k16-proof-and-weft.md` §2: branch 6 vs
MDS 25, block-triangular along the subspace flag, epitaph *"the alignment thesis
imports the code's triangularity, and triangularity is the opposite of
diffusion"*). The lesson is operationalized here as THE GATE: **every candidate
linear layer got its branch number computed before any other analysis.** Every
claim below is `[MEASURED]` (script + log named), `[READ]` (file/paper + section),
or `[DERIVED]` (labeled). Substrate: nothing here authors a constraint; the Lean
landed is relation-view spine (`minidregg`, §6), Lean-authored.

**Artifacts**: `~/src/ring-ro-hash/post_weft_branch.py`, `xhash_m31_branch.py`,
`mark32_sysrs_branch.py` + their run logs (`*-run.log`), all versioned at
`ring-ro-hash@04d0d95`; `minidregg/Selvage/HashRelationInverse.lean` (builds
green, pinned); this note.

---

## 0. THE GATE TABLE — every layer this lane touched

| layer | field, t | branch | certification | verdict |
|---|---|---:|---|---|
| Weft novel-eval `E` (inherited) | GF(2³²), 24 | **6** | EXACT (min-side ≤ 2 total, duality) | ☠ killed (prior lane) |
| Cauchy dense `D` | GF(2³²), 24 | **25** | by theorem (Cauchy); instrument floor agrees, min-side ≤ 3 exhausted | the MDS yardstick |
| **`E·D`** (survivor 1, "novelPack ∘ D") | GF(2³²), 24 | **∈ [8, 21]** | ≤ 21 by witness (wt-2 cols {19,23}); ≥ 8 proven (min-side ≤ 3 exhausted at 21) | ☠ **killed §2** |
| **`D·E`** (survivor 1, other order) | GF(2³²), 24 | **∈ [8, 11]** | ≤ 11 by witness (wt-3); ≥ 8 proven (floor 11) | ☠ **killed §2** |
| **systematic-RS LCH `A = V₂·V₁⁻¹`** (Mark-32's own construction) | GF(2³²), 24 | **25** | EXACT by RS theorem (superregular parity of an MDS code); instrument floor agrees | ⭐ **the redeemed alignment, §3** |
| **RPO/XHash8 MDS** (circ [7,23,8,26,13,10,9,7,6,22,21,8]) | Goldilocks, 12 | **13** | ⭐ **EXACT, fully certified**: two-sided minor sweep k ≤ 6, all 3,557,930 minors nonsingular (~6 min) — an independent MDS certification of the deployed matrix | passes |
| **XHash-M31 MDS** (truncated circle-circulant) | M31, 24 | **25** | by their Thm 2 + truncation [READ]; instrument floor 25, min-side ≤ 3 exhausted; **row re-derived from formula (14), λ = 2 — and the paper's Eq. 16 display has a TYPO (§5c)** | passes, typo flagged |
| Poseidon2 M_E (comparators, inherited) | BabyBear, 16/24 | 8 / ≤ 10 | EXACT / block analysis | the bar to beat |

Certification vocabulary: EXACT means every codeword class that could beat the
number is exhausted; "floor, min-side ≤ 3 exhausted" means any codeword with
B ≤ 7 was excluded (so branch ≥ 8 is PROVEN) and nothing below the floor exists
with min-side ≤ 3 — it is NOT a claim that branch equals the floor.
⚠ Method note, paid for in §5c: **the passes are a floor instrument, not an
identity instrument** — a corrupted MDS matrix (one wrong entry) still shows
floor 25, because singular minors are sampling-invisible needles at 31 bits.
Identity comes from re-deriving the object from its defining formula.

---

## 1. ⭐ THE DISSOLVE-CHECK, RUN FIRST — the binary path does NOT need a new hash today

The question under the lane: does the additive-BaseFold line need a char-2
algebraic hash at all? Answer by cases on WHERE the binary proof gets verified.
The measured state it rests on:

* `[READ]` The deployed binary line's transcript/Merkle hash is **cSHAKE256**:
  `minidregg/Compiler/Tower256AdditiveFriController.lean` pins
  `Sp800185Cshake256.controller` into the concrete backend (`cshakeExact`
  structure field), and the native kernel is `prover/src/hash_kernels.rs` (raw
  cSHAKE256 XOF).
* `[MEASURED — routability grep, the PROVEN-IN-LEAN ≠ ROUTABLE discipline]`
  **No char-2 circuit prover exists in either tree.** `minidregg/prover/src/`
  holds fold/NTT/sumcheck/tower KERNELS (`additive_ntt.rs`, `binary_tower*.rs`,
  `mle_kernels.rs`) and no AIR, no constraint evaluator, no circuit; breadstuffs'
  GF(2)-hits are all FHE-side. The binary rung is Lean theorems + native kernels.

**Scenario A — binary proofs stay terminal (native verify only).** The hash slot
is native-only; cSHAKE256 (or Blake3, 8.2 ns/elt) is fine and already held. **No
design needed. This is the state today.**

**Scenario B — binary proofs recursed by the deployed BabyBear wrap.** Then the
wrap's in-circuit verifier re-runs the binary transcript, and the correct hash is
**the wrap-native Poseidon2 — the hash we already run, prove, and instrument** —
over packed leaf bytes. Priced:

* ⚠ Correction to the brief first: **ring-switching cannot carry the hash across
  the boundary.** Diamond–Posen's compiler (2024/504, read in
  `ring-switching-connectors.md`) requires `L/K` a *field extension* — it is
  same-characteristic by definition. "Poseidon2 with ring-switching at the
  boundary" therefore means: the PCS stays char-2, and the *transcript/Merkle
  layer* absorbs binary data as packed BabyBear felts. The crossing is at the
  byte→felt codec, not a field embedding.
* **Packing overhead on absorption**: 30 bits/felt is injective (2³⁰ < p), so a
  rate-8 perm absorbs 240 packed bits vs 248 native — ≈ **1.03×**; a
  16-bit-limb codec (cheaper decomposition) is **1.94×**. Applies to the
  absorption share class (29.2% of wrap perms, `leaf-vs-recursion.md` §2c);
  opened leaves additionally pay ~1–2 cells/bit of decomposition, on the opened
  set only. Small.
* ⚑ **The real new term is hash-independent**: the additive fold/sumcheck
  arithmetic over GF(2^k) emulated in a BabyBear circuit. [DERIVED, wide bars]:
  per query-round ≈ 2–4 tower mults; bitwise emulation ≈ 10³ cells/GF(2¹²⁸)
  mult, 8-bit-limb LogUp route ≈ 10²; query-rounds ≈ 2k–8k (UD-radius query
  counts at the proved δ < (1−ρ)/3 are the top of that range) → **0.2M–8M cells
  ≈ 1–30% of the measured 29M-cell wrap**. Unmeasured; first-order comparable
  to the hashing share; entirely a *fold-emulation* cost that NO hash choice
  moves. A char-2 hash makes scenario B strictly worse (30×-class, the
  `hash-landscape.md` §1a wall).
* ⚑ **The one actionable decision NOW, greenfield-cheap, expensive later**: as
  held, binary receipts are cSHAKE256-transcripted = **native-verify-only
  objects** (a Keccak-family sponge in the wrap is the 30×-class death). If
  scenario B is ever wanted, the additive controllers' transcript hash must flip
  to the wrap-native hash — today that is a re-pin of `cshakeExact` and a
  re-emit; after anything builds on binary receipts it is a flag day. Per house
  doctrine: named now, landed when the fork is chosen.

**Scenario C — char-2-native recursion (a binary circuit verifying binary
proofs).** The ONLY scenario where a char-2 algebraic hash slot exists — and it
lacks its entire substrate: no char-2 AIR, no circuit prover, no witness-gen
(the routability grep above). The hash is not the blocker; the missing proof
system is, and the hash question is downstream of the decision to build it.

> ### **VERDICT: the slot dissolves today.** Scenario A holds; scenario B's
> hash answer is the deployed Poseidon2 plus a small packing overhead, with the
> real unmeasured term (fold emulation) hash-independent; scenario C — the only
> home a Weft successor could have — does not exist yet as a stack. **No new
> hash gets built now.** What this lane banks instead: the gate discipline, the
> gated candidate set (§§2–5), the Lean relation spine (§6), and the contingent
> recommendation (§7) for the day scenario C is chosen.

---

## 2. SURVIVOR 1 — the dense-composed fallback: ☠ KILLED BY MEASUREMENT

The fallback clause the Weft kill left alive ("compose the transform with a
cheap dense layer, lose some sharing") is now measured, and it fails the gate.
`[MEASURED]` `post_weft_branch.py` phase 1b/2: `E` = the killed novel-eval
matrix, `D` = Cauchy MDS (branch 25 by theorem, spot-checked):

* **`D·E`: branch ≤ 11** (wt-3 witness; floor 11 with min-side ≤ 3 exhausted;
  certified interval [8, 11]). **`E·D`: branch ≤ 21** (wt-2 witness on cols
  {19, 23}; interval [8, 21]). Against `D` alone at **25**.
* The invariant-subspace FLAG is destroyed in both orders (all four lane-blocks
  fully dense: 44/44, 80/80, 128/128, 128/128 nonzero) — **composition closes
  the flag wound but not the branch wound.** E's codeword geometry survives
  composition with a full MDS: the low-weight structure re-enters through the
  other side.
* Cost side: the composed layer pays D's dense cost PLUS E's butterflies to get
  a layer strictly *worse* than D alone. **E contributes negative branch value
  at positive cost.** Nothing of the sharing prize survives in this form —
  survivor 1 is dominated by plain-dense on every axis and is closed.

---

## 3. ⭐ THE REDEMPTION — the systematic-RS LCH matrix: the alignment thesis done right

Found by reading Mark-32 at source (eprint 2024/633 §3.3), then gated:
**Vision Mark-32's MDS is built FROM the same LCH novel basis (`Ŵᵢ` subspace
polynomials) as the killed Weft mixing** — as the parity map of a *systematic
Reed–Solomon code*: interpolate the state on points ω₀..ω₂₃, evaluate on the
**disjoint** points ω₂₄..ω₄₇.

`A = V₂ · V₁⁻¹`, where `V₁` is literally the killed Weft matrix `E` and `V₂`
the same evaluation map at the next 24 domain points. `[MEASURED]`
`mark32_sysrs_branch.py`: **branch(A) = 25 — EXACT by the RS theorem**
(distance 25 ⟹ `[I | A]` MDS ⟹ A superregular), instrument floor agrees
(min-side ≤ 3 exhausted, nothing < 25), invariant flag destroyed. And `A` is
provably independent of both the novel-basis choice and the `Ŵ` normalization
(any polynomial-basis change and any diagonal cancel in `V₂V₁⁻¹`); the only
choice it depends on is the point split [ASSUMED here: 0..23 / 24..47 —
re-read Mark-32's Sage listing before adopting verbatim].

Why this redeems the thesis:

* **Weft died by evaluating inside its own interpolation window** — that is
  where the block-triangularity came from (`X̂ᵢ, i ≥ 2^b` vanish on V_b ⊂ the
  window). Evaluating on the complement coset is the SAME butterfly network
  run at different twiddles, and it is MDS *by theorem*, not by search.
* **The sharing prize returns in its honest form**: the hash's dense layer =
  interpolate-then-evaluate on the code's own transform — prover cost
  O(t log t) (two LCH passes, not a t² matmul), the same GPU kernel family as
  the encoder, and the Lean proof mass for the transform
  (`Selvage/AdditiveBaseFold.lean`'s `novelPack` chain) covers both factors.
  The "ONE proved linear object in the TCB" consequence, lost when the fallback
  was priced as `dense ∘ novel-eval`, is recovered: A is a *derived object* of
  the proved transform.
* And it is not even a new design: **it is what Mark-32 already ships.** The
  alignment end-state the Weft sketch was reaching for exists in the
  literature, with the right geometry (next section).

⚑ **Live sibling lane, same day**: `notes/weft2.md` (`weft2_structure.py`) is
re-opening the kill's SCOPE from the cryptanalysis side — its Q3 is the
one-transform cousin of this finding (evaluate on an affine COSET `x* + V`:
same butterflies, shifted twiddles, zero extra ops — vs this section's
two-transform parity map with the RS theorem attached). If their coset
variant certifies a high branch number, it is the cheaper of the two; results
pending there. The two lanes converged independently on the same repair axis:
**move the evaluation set off the interpolation window.**

---

## 4. SURVIVOR 2 — "the alignment moved up a level" = ADOPT VISION MARK-32 (with named repairs)

`[READ at source: eprint 2024/633]` Mark-32 IS the Vision-shaped design at
exactly the Weft geometry: **t = 24 over GF(2³²) (the Fan–Paar-adjacent tower
width), rate 16 / capacity 8, 8 rounds**, round = `x⁻¹` → linearized affine
(`B⁻¹` then `B`) → MDS (+ constants), 128-bit claim, and the MDS of §3. Binius'
own hash for binary towers — convergent with our stack's field choices.

**The `HashRelation` instances are stated and LANDED in Lean** (§6): the S-box
half is graph-sound over any field in both presentations —

* `invWitnessed` — Vision's own degree-2 check (`x·y = r`, `x(1−r) = 0`,
  `y(1−r) = 0`, one witness `r`), the family's cheapest verification;
* `invSystem` — witness-free degree-3 system (`x²y = x`, `xy² = y`), inside
  the degree-3 rung's per-constraint cap (`Degree3Statable`, proved).

**The honest obligation list** (a fresh candidate has near-zero age; Vision's
skeleton is 2019-unbroken but *unanalyzed* — nobody has looked, which is not
the same thing):

1. **[M32-coeffgroup]** — `B(x) = β₀x + β₁x² + β₂x⁴ + β₃`: THREE Frobenius
   terms — the Chaghri-*repair* density (one term broke Chaghri, three fixed
   it, 2022/991) — but with ADJACENT exponents {0,1,2} where the repair used
   spread {0,2,8}. The coefficient-grouping recurrence must be COMPUTED for
   this exact `B` (O(n), seconds), not presumed from the count.
2. **[M32-integral]** — the Beyne–Verbauwhede monotonicity axis (degree-2^k
   towers are the extreme point, `ring-hash-tau-verdict.md`) vs the x⁻¹ S-box's
   maximal F₂-degree; run their notebook at t = 24/GF(2³²)/8 rounds.
3. **[M32-groebner]** — rounds were set by the designers' own analysis
   (pre-FreeLunch methodology); the x⁻¹-in-every-branch shape is the one
   2024/347 could not directly model — evidence, not immunity; a post-FreeLunch
   / MIDC-style (Perrin 2024/605) round audit is owed.
4. **[M32-indiff]** — sponge indifferentiability inherits the open upstream
   `SpongeIndiffGame`, same as the deployed hash; stated, not discharged.
5. **[M32-age]** — zero attack papers = zero attention, not strength. Two
   named expert audits exist for XHash (§5); none for Mark-32.
6. **[M32-cells]** — the settling measurement is unchanged from the Weft form:
   committed cells of one permutation in an additive-BaseFold wrap vs
   Poseidon2's 300/1,192. Shape-level [DERIVED] from the Weft pricing: ~24·R
   aux + linear terms ≈ 200–400 cells at R = 8. To be measured on the day the
   §1 scenario-C fork opens, not before.

---

## 5. SURVIVOR 3 — XHash8, read at source, record swept, layer certified

### 5a. The object `[READ: eprint 2023/1045]`

12 lanes over **Goldilocks** (p = 2⁶⁴ − 2³² + 1), sponge rate 8 / capacity 4,
permutation `(I)(F)(B′)(P3)` ×3 rounds. S-boxes: π₀ = x⁷ (full layer),
π₁ = x^{1/7} on **8 of 12** lanes (the "partial inverse layer" that names it),
π₂ = x⁷ over **F_{p³}** (4 cube-extension lanes — the diffusion-through-
nonlinearity trick). MDS = **RPO's circulant** (2022/1577 §2.3, first row
[7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8]). Native: 2.95 µs vs RPO's 8.15
(their T1). Relation shapes: everything is degree ≤ 3 witnessed — π₀/π₂ are
`pow7Witnessed` (π₂ at the cubic extension — same Lean object, §6), π₁ is the
transposed form `powRootWitnessed` (`w = y³`, `x = w²y`).

### 5b. The record — better than the brief carried

* ⚠ Correction: the brief's "FreeLunch-unmodelable survivor" is not quite the
  paper. 2024/347 §4.3 + App. F **does** build a FreeLunch system for XHash8
  (the 4 un-inverted lanes admit it; XHash12/RPO/Rescue with FULL inverse
  layers are the unmodelable ones) — and the attack lands at **2^214**
  (main text; App. F's walk-through ~2^240), far above the 2^64 one-branch
  brute-force baseline, "very secure against the techniques presented in this
  paper," with their honest caveat that the designers' own estimates
  extrapolate from t = 3 toys.
* **Two independent expert audits exist** (found by first-2-page mirror sweep,
  2,581 files 2024–2026): **Perrin 2024/605** (padding safe as claimed;
  generalized-FreeLunch + Monotonous Ideal Degree Conjecture, experimentally
  validated with slack in the safe direction: *"if used as specified, these
  hash functions seem safe from Gröbner bases-based algebraic attacks"*) and
  **Rijmen 2024/656** (differential audit extended — "interesting new
  properties… did not result in any attacks"; saturation distinguisher for a
  single round that does not propagate through (P3); linear comments).
* **CheapLunch (2025/2040), read at source**: extends FreeLunch beyond CICO-1
  and REACHES XHash8 — Proposition 2: `7³⁰ ≤ D_I ≤ 7^{24+6k}` for
  CICO-(12−k, k), k ≤ 4, **validating XHash's own Conjecture 1 (the MIDC) in
  that context**; round skips confirmed applicable (first (F) + 8 S-boxes at
  CICO-1); the break-relevant case is CICO-(8,4) (the real capacity), left as
  a dimension-0 conjecture; abstract: *"our results do not threaten the
  security of any full-round hash function."* (Independently read the same
  day by the sibling Kagi-sweep lane — `hash-landscape.md` ADDENDUM 4, whose
  reframe is right: "unmodelable" was absence-of-analysis wearing a security
  costume; *modeled-by-the-strongest-framework-and-surviving* is strictly
  better, and that is what XHash8 now has.)
* 2025/259 (improved resultant) *places* XHash in its framework and does not
  attack it; 2026/1281 (resultants-meet-resultant) cites it in the intro list
  only. Full-mirror sweep + web sweep 2026-08-17: no attack papers; the
  family now has a peer-reviewed journal version (Designs, Codes &
  Cryptography, 2026).
* **Security-age verdict: the strongest record of any post-Poseidon2 candidate
  on our books** — 3 years, two commissioned expert audits (Perrin, Rijmen),
  two favorable attack-paper analyses (FreeLunch 2^214, CheapLunch), zero
  breaks.

### 5c. The linear layer, certified — and a typo found in the M31 sibling

* **RPO MDS (= XHash8's layer): branch = 13 EXACT, fully certified**
  `[MEASURED]` — two-sided k ≤ 6 minor sweep, all 3,557,930 minors
  nonsingular. This is also an independent MDS certification of the deployed
  RPO matrix (the RPO paper verified it with Polygon Zero's internal test
  procedure; ours is an outside instrument).
* **XHash-M31** (2024/1635, the 31-bit family member, found in the sweep):
  t = **24**, rate **16** / capacity **8** over M31 — *exactly the Weft
  geometry* — α = 5, π₂-analogue over F_{p³} (X³+2), 124-bit generic security;
  MDS = a 32×32 circle-group circulant (Haböck's construction) truncated to
  24×24. `[MEASURED]` `xhash_m31_branch.py`: τ verified as a primitive 64th
  root in C(F_p); **formula (14) re-derives the published first row at λ = 2 —
  31/32 entries exactly, and the 32nd is a TYPO IN THE PAPER'S Eq. 16 display**
  (prints 63026005, formula gives **163026005** — a dropped leading digit,
  confirmed against the PDF layout). Instrument floor 25, min-side ≤ 3
  exhausted; = 25 by their Theorem 2 + the truncation-of-MDS argument [READ].
  ⚠ An implementer transcribing Eq. 16 verbatim ships a wrong matrix — and the
  branch passes would NOT catch it (the typo'd matrix also floors at 25):
  worth reporting upstream; their [ST24] code repo is presumably the authority.

### 5d. Fit to our tower/width — the honest answer is NO, three ways

1. **Field**: XHash8 is "only defined for a fixed prime p ≈ 2⁶⁴" (2024/347's
   words; the spec's own framing). Our prime stack is BabyBear — a 31-bit
   re-instantiation would inherit ZERO of the analysis (round counts, the
   differential bound 2^{−726}, the Gröbner extrapolations are all at 64
   bits), and at 31 bits capacity-4 is untenable (the `hash-verdict.md`
   lesson: capacity binds at 2^62). XHash-M31 shows the family re-instantiates
   at 31 bits — but at M31 for Circle STARKs, not BabyBear, with fresh
   parameters and (so far) none of the XHash8 audit record carried over.
2. **Characteristic**: nothing in the family is char-2; it cannot fill the
   scenario-C slot at all.
3. **Need**: on the prime side the incumbent is Poseidon2 at R = 1,
   triple-confirmed (`hash-landscape.md` ADDENDUM 2); XHash8's STARK cost is
   not priced in our cells and its native win (2.75× over RPO) is against
   RPO, not against our 22.8 ns/elt Poseidon2.

**What XHash8 IS to us**: the proof-of-existence that the §0.3 design target
(relation cheap for the verifier, expensive for the adversary, carried by
full-field inversion + extension-field mixing) can survive three years of
qualified attention — and the donor of the `powRootWitnessed`/π₂ relation
shapes, now in the Lean spine. If a Goldilocks- or M31-shaped stack ever
appears on our books, XHash8/XHash-M31 is the adopt-don't-design answer there.

---

## 6. THE LEAN LANDED — `Selvage/HashRelationInverse.lean`

`minidregg`, builds green (module + `Selvage` root, 3,100 jobs), no `sorry`,
axiom-pinned per decl (`#guard_msgs` + `#print axioms`), no bare `#guard`.
Registered in `Selvage.lean`.

| object | statement | teeth/pins |
|---|---|---|
| `PolySystemRelationView` | relation as a polynomial SYSTEM with per-constraint `totalDegree` (the shape real S-box checks have; `Degree3Statable` = the rung's cap per constraint) | `emptySystem_not_graphSound`: the empty system inhabits the interface and is REFUSED the obligation |
| `invWitnessed` + `invWitnessed_graphSound` | Vision's degree-2 inverse check, graph-sound over ANY field | `[propext, Classical.choice, Quot.sound]` |
| `invSystem` + `invSystem_degree3` + `invSystem_graphSound` | the witness-free degree-3 system, per-constraint cap PROVED, graph-sound over any field | same pins |
| `bareInv_not_complete` | ⚑ the naive `x·y = 1` without the zero branch fails COMPLETENESS at 0 — the zero branch is load-bearing | generic over any field |
| `powRootWitnessed` + `_graphSound` | XHash's π₁ (`y⁷ = x` witnessed at degree ≤ 3); graph-soundness = exactly injectivity of `(·)⁷`, carried as a hypothesis | `[propext]` — ring identities only |
| `xhashRoot13_graphSound` | the shape instantiated at `ZMod 13` (7⁻¹ ≡ 7 mod 12), injectivity by `decide` | |
| `pi2_shape_graphSound` | **π₂ is `pow7Witnessed` at `GaloisField 13 3`** — the extension-field S-box is the same relation object at another `CommRing`, zero new soundness argument | |

Development note for the record: the first build's axiom pins caught a failed
elaboration degraded to `sorryAx` (a `Decidable (x = 0)` hole in the witness
function plus a `rw` that rewrote `x` inside `rt x`) — the tripwire class
firing again, exactly as in the parent file's history.

---

## 7. RECOMMENDATION — ranked by security-age × alignment-retained × cost

**Now: build nothing.** The dissolve-check (§1) closes the slot: terminal
binary proofs keep cSHAKE256; recursed-in-the-wrap binary proofs (scenario B)
take the deployed Poseidon2 + a ~1.03–1.94× packing codec, and their real open
cost (fold emulation, 1–30% of a wrap, [DERIVED]) is hash-independent and is
the measurement to run before any scenario-B commitment. The one decision worth
making early: pick the wrap-native transcript hash for the additive controllers
*before* anything builds on cSHAKE receipts (§1, greenfield-cheap).

**If/when char-2-native recursion (scenario C) is decided**, the ranking:

1. ⭐ **Adopt Vision Mark-32, with the §4 obligations discharged first**
   (coeffgroup computed for its exact `B`, integral bound run, post-FreeLunch
   round audit). Security age: skeleton 2019-unbroken/underanalyzed — the weak
   axis, priced honestly. Alignment retained: HIGHEST POSSIBLE — its MDS is
   the systematic-RS form of our own proved transform (§3: branch 25 by
   theorem, butterflies shared with the encoder, `novelPack` proof mass covers
   both factors), its geometry (t=24/GF(2³²)/r16/c8) is the Weft geometry, and
   its S-box relations are already graph-sound in our Lean spine. Cost:
   degree ≤ 2–3 relations throughout, ≈ 200–400 cells/perm [DERIVED,
   shape-level], O(t log t) native mixing. (If the sibling `weft2.md` lane's
   free coset repair certifies a high branch, the mixing may get cheaper
   still — one transform instead of two; fold its result in before any
   adoption.)
2. **XHash-M31 / XHash8** — only if the stack's field turns M31- or
   Goldilocks-shaped (neither is on our books). Security age: best in class
   (§5b). Alignment retained: LOW for us (wrong prime, no char-2 form).
   Their layers are now independently certified either way (§5c).
3. ☠ **Dense-composed `novelPack ∘ D`** — eliminated by measurement (§2):
   branch ≤ 11/≤ 21 vs 25 at strictly higher cost; dominated on every axis.
4. ☠ **Blake3-with-lookup** — dead at 1.96× (`hash-landscape.md` ADDENDUM 2);
   not relitigated, per the brief.

**The transferable law this lane adds to the record**: the gate held — four
exact passes killed survivor 1 in minutes and certified two live candidates'
layers — AND the gate is a *floor* instrument only: the M31 typo (§5c) shows a
corrupted MDS sails through branch passes. A candidate layer's certification is
therefore two-legged: *re-derive the object from its defining formula, then
gate it.* Both legs are now versioned tooling (`~/src/ring-ro-hash/`).

---

## Provenance

Measured: `post_weft_branch.py` (RPO sweep 3.56M minors ≈ 6 min; E·D/D·E
passes + wt-3 ≈ 8 min), `xhash_m31_branch.py` (τ check, row re-derivation,
floor), `mark32_sysrs_branch.py` (A = V₂V₁⁻¹ floor), all on the laptop,
GF(2³²) twin self-checked against the Lean Fan–Paar relations (200 samples).
Read at source this lane: eprint 2023/1045 (whole design + App. A/B),
2022/1577 §2.3 + Lemma 1, 2024/347 §4.3 + App. F, 2025/259 (XHash passages),
2024/605 (Perrin), 2024/656 (Rijmen, exec summary + findings index),
2024/1635 (§3 + App. A.3), 2024/633 §3.3 + §5 (Mark-32), 2025/2040 §4.1
(CheapLunch on XHash8, Prop. 2); banked into `~/paperbin` under descriptive
names. Corpus disclosure: XHash-attack absence rests on (a) `~/paperbin`
full-text, (b) first-2-page scans of BOTH mirror copies — the lagging
`~/archive` one (2024 complete, 2,581 files) AND the FULL
`~/dev/gh/forks/IACR-eprint-mirror` (2025+2026 complete at scan time, 3,999
files) — every hit classified (2025/2040 CheapLunch favorable; 2025/1593
survey-cite; 2026/1281 intro-cite; 2 false positives OP_TXHASH/xxHash),
(c) a live web sweep 2026-08-17 (no breaks; DCC journal version found).
First-2-page scanning misses body-only mentions (the known instrument limit,
PREFLIGHT); the eprint mirror is cryptology-only. Dissolve-check state:
`[READ]` `Tower256AdditiveFriController.lean` (cSHAKE pin), `prover/src/`
module list (no AIR); shares/cells quoted from `leaf-vs-recursion.md` §2c,
`hash-landscape.md` §1a/ADD.2, `k16-proof-and-weft.md` (all previously
measured, not re-measured here). Concurrent work the same day, referenced
not duplicated: `hash-landscape.md` ADDENDUM 4 (Kagi sweep) and
`notes/weft2.md` (the kill-scope re-open; owns `weft2_structure.py`).

---

## ⭐ SUCCESSOR, 2026-08-18 — `notes/weft-coset-repair.md` (LEAN BUILD lane)

⚑ **§3's systematic-RS form carries a 2026/306-shaped invariant flag, and the gate that
blessed it cannot see it.** `[MEASURED + DERIVED]` For **every** point split in which both
point sets are unions of cosets of a common GF(2)-subspace — precisely the condition that
makes the LCH transform O(t log t) — `A = V₂V₁⁻¹` has a 3-deep nested flag of
**block-constant** invariant subspaces, **dim 12 ⊃ 6 ⊃ 3**, preserved by the mixing layer
AND by every lane-wise S-box. Mechanism: the degree-`<t` polynomials invariant under
translation by `W` are `K[Ŵ_W]` of dimension `t/|W|`, and their value vectors are constant
on each `W`-coset on both sides. The `A² = I` / `deg(minpoly) = 2` result `weft2.md` §7
measured is the `P₂ = x* + P₁` case of the same theorem, with `rank(A+I) = 12`: **half the
state fixed POINTWISE by an MDS layer.**

- ⚠ **Not a break** — it is an invariant SUBSPACE, so a round constant outside it breaks
  it (unlike Weft-1's quotient). It is the attacked SHAPE, present by construction, and
  2026/306 reached 2^106 on Poseidon2 with the analogous structure despite constants.
- **The escape costs the thesis**: a random (non-coset) parity set gives `deg(minpoly) = 24`,
  observability 24/24 and zero stalled trails — and an O(t²) matmul.
- **§7's closing law extends**: the branch passes are not an identity instrument **and not
  a structure instrument**. MDS is not a structure certificate.
- **New obligation [M32-flag]** on the adopt-Mark-32 path (§4): Mark-32's own MDS *is* the
  fast systematic-RS form, so read its Sage point split and test whether both point sets
  are unions of cosets of a common subspace. Cheap, and it belongs next to
  [M32-coeffgroup].
- §1's verdict is **unchanged and reaffirmed**: build nothing now. The successor lane makes
  the object ready, not deployed.

---

## ⚑⚑ SUCCESSOR, 2026-08-18 — `notes/weft-c-spec.md` (DESIGN + ANALYSIS lane)

**Three corrections to this note, all `[READ at source: eprint 2024/633]`, plus one
obligation closed as a confirmed defect.**

1. ⚑⚑ **`[M32-flag]` (§7's hand-off) is CLOSED, and it closes as a DEFECT OF THE DEPLOYED
   MATRIX.** §3.3's Sage listing *and its prose* — *"the extrapolation matrix, which takes
   the values of some polynomial of degree less than `m` on the set `ω₀, …, ω_{m−1}`, and
   returns the evaluations … on `ω_m, …, ω_{2m−1}`"* — fix the split to the **natural**
   one, `0..23 / 24..47`. §4's `[ASSUMED here: 0..23 / 24..47 — re-read Mark-32's Sage
   listing before adopting verbatim]` was **right, and it was the load-bearing assumption.**
   `[MEASURED]` Both halves are unions of cosets of `U₁`, `U₂` and `U₃`, so
   `A = V₂V₁⁻¹` carries the **3-deep block-constant invariant flag dim 12 ⊃ 6 ⊃ 3**, has
   **`deg(minpoly) = 6`**, and stalls **12/12** on the contiguous-pair family and **20/500**
   on random irregular partitions — with a random-split control showing none of it.
2. ⚑ **NEW `[M32-subfield]`**: all 48 points are integers `< 64`, hence in `T₃ = GF(2⁸)`, so
   **Mark-32's MDS entries lie in GF(2⁸)** and `(GF(2⁸))²⁴` — a **2¹⁹²** set — is closed
   under the mixing layer *and* the S-box layer. The escape depends entirely on the `B`
   coefficients and round constants, **which 2024/633 does not publish.** `[MEASURED]`
3. ⚑⚑ **CORRECTION to §4 `[M32-cells]` and to `weft2.md` §6c: Mark-32's "8 rounds" is 16
   S-BOX LAYERS.** Algorithm 1 runs two `x⁻¹` layers per round, and §4.2 states it outright:
   *"Single round … consists of 48 round constant additions, **48 tower-field inversions**,
   48 affine linearized polynomial evaluations and 2 MDS matrix multiplications"* at
   `t = 24`. **384 inversions, not 192.** The `~200–400 cells` estimate is wrong on two
   counts (the 2× and the missing `B`-layer aux cells); the corrected shape-level range is
   **384–1872 cells**, which is not a measurement — see the successor's §5d.
4. ⚑ **NEW `[M32-floor]`**: `[READ at source: eprint 2019/426 §5]` the Marvellous strategy
   Mark-32 cites recommends *"`2⌈n/5.5m⌉` rounds, **with a minimum of 10 rounds**"*. At
   `m = 24, n = 128` the formula is vacuous (`5.5·m·N = 1056` bits at `N = 8`), so **the
   floor of 10 was the whole round count — and Mark-32 ships 8.** ⭐ **The cheapest action
   on the adoption path is therefore a round count, not a cryptanalysis: adopt at 10 rounds,
   +25%, and the deviation disappears.**
5. **NEW `[M32-mode]`**, ⚠ **not asserted**: §3.4's prose, read literally, has the capacity
   *overwritten from the rate output* each block, which would make the construction a
   chop-MD with a 256-bit chaining value rather than a sponge. **Text-only reading; Figure 2
   is not machine-readable from the PDF.** Filed next to `[M32-indiff]`.

**§7's ranking is not overturned** — an unanalyzed *published* design still accumulates
analysis and an unanalyzed private one does not. What changed is that the adoption now
carries **nine** named obligations, two of them measured defects of the shipped object.
