# Weft, re-opened — branch 6 was NOT the killer, and the killer was inside the kill's own script

2026-08-17. CRYPTANALYSIS + DESIGN lane, re-opening `k16-proof-and-weft.md` §2 /
`hash-landscape.md` ADDENDUM 3 / `aligned-hash-space.md` §3d [WEFT-subspace].

Substrate said out loud: **nothing here authors a constraint anywhere.** This is a
computation over the *twins* of the proved Lean objects (`Selvage/AdditiveBaseFold.lean`'s
`novelPack`, `Theory/BinaryTowerFanPaar.lean`'s tower), in the same instrument family the
kill used. If any of this ever becomes a circuit, the AIR is Lean-authored.

Everything is `[MEASURED]` (script that ran, artifact named), `[READ]` (file:line),
or `[DERIVED]` (labeled).

**Artifact**: `~/src/ring-ro-hash/weft2_structure.py` (this lane's, ~107 s; run log
`/tmp/.../weft2-final.log`). It **imports** `weft_branch.py` (the kill's) and
`mark32_sysrs_branch.py` (the post-Weft lane's) unmodified — neither is edited.
Sibling lanes referenced, not duplicated: `post-weft-hash.md` (systematic-RS MDS,
landed), `ring-hash-design.md` (the schedule table).

---

## 0. VERDICT IN FIVE LINES

1. **Branch 6 is NOT disqualifying on its own. The re-opening was right.** At GF(2³²)
   one active S-box is worth **30 bits on BOTH sides** (measured), so branch 6 buys 180
   differential bits per 2 rounds against a 128-bit bar — and ⚑ **Poseidon2's own
   internal layer has branch 2 and ships in 22 of its 30 rounds.**
2. **The kill's verdict was right for a reason it never stated.** The flag is **5 deep,
   not 4** — `weft_branch.py:300` loops `range(1, 5)` and the level it skips, **b = 0**,
   is a *fixed lane*: output lane 0 **equals** input lane 0, so the permutation carries a
   32-bit **autonomous quotient map** `x₀ ↦ x₀⁻¹ + c₀` for any number of rounds. ⚑ **Round
   constants break invariant SUBSPACES; they do not break invariant QUOTIENTS.**
3. **The rotation works and is the wrong repair.** Verified: **all 23** non-trivial lane
   rotations destroy **every** invariant lane subspace, both sides. But rotation cannot
   move a branch number (a permutation preserves Hamming weight), leaves the layer sparse,
   and leaves the **GF(2⁸) subfield structure** untouched.
4. ⭐ **The right repair is FREE and upstream of all of it: evaluate on an affine COSET.**
   Same butterflies, shifted twiddles, zero ops, zero constraints. Result `[MEASURED]`:
   **B_d = 8 EXACT** (= the char-2 reduction of Poseidon2's own external layer, exactly),
   **B_l ∈ [8,10]**, dense, **zero** invariant subspaces on either side, full diffusion in
   **1** round, **no** twisted-subfield structure, `deg(minpoly) = 24`, and the internal-round
   observability condition satisfied at **all 24** S-box lanes.
5. **Weft-2's internal/external split is backwards AND cost-negative** — and the trade
   against adoption does not read the way the brief assumed, because ⚑ **on the binary rung
   there is no aged hash to adopt**: the only char-2 candidate (Vision Mark-32) has
   *"none found — and nobody has looked"* on our own books (`hash-landscape.md:619`).

---

## 1. THE CORRECTED DIFFERENTIAL/LINEAR ACCOUNTING — is branch 6 disqualifying alone? **NO**

### 1a. The two constants the whole argument scales, measured

`[MEASURED]` exhaustively at the tower's GF(2⁸) level (`weft2_structure.py` PART 0):

| quantity | measured at n = 8 | theorem in n | at Weft's n = 32 |
|---|---|---|---|
| differential uniformity of `x⁻¹` | **δ = 4** (exhaustive DDT) | Nyberg: δ = 4 for even n | DP_max = 4/2³² = **2⁻³⁰** |
| Walsh spectrum max | **\|W\| = 32 = 2^(n/2+1) exactly** (exhaustive; the Kloosterman substitution `W(a,b) = W₁(ab)` makes 255 values exhaust the spectrum) | Lachaud–Wolfmann: \|W\| ≤ 2^(n/2+1) | corr ≤ 2⁻¹⁵, LP_max = **2⁻³⁰** |

⚑ **The two sides are symmetric for `x⁻¹`: one active S-box is worth 30 bits differentially
AND 30 bits linearly.** That is the number every branch figure multiplies.

### 1b. The wide-trail table, with the linear column the kill never filled

`[MEASURED]` (`weft2_structure.py` PARTS 1, 5, 7b; `B_l(M) = B_d(Mᵀ)` — a *different*
quantity from `B_d(M)`, and the kill's four passes never touched `Mᵀ`):

| layer (t = 24 unless noted) | **B_d** | **B_l** | diff bits / 2 rds | lin bits / 2 rds |
|---|---:|---:|---:|---:|
| **Weft-1 novelPack, linear domain** (the kill's object) | **6** EXACT | **2** EXACT ⚑ | 180 | 60 |
| **Weft-coset, one transform** (this lane's repair) | **8** EXACT | **[8,10]** | 240 | ≥ 240 |
| systematic-RS `A = V₂V₁⁻¹` (post-Weft lane) | 25 (MDS thm) | 25 | 750 | 750 |
| MDS bound at t = 24 | 25 | 25 | 750 | 750 |
| Poseidon2 M_E t=16 **as deployed (BabyBear)** | 8 EXACT | — | *(prime field)* | — |
| ⚑ Poseidon2 M_E t=24 **reduced to char 2** | ≤ **8** | — | 240 | — |
| ⚑ Poseidon2 **M_I** (internal), as deployed | **2** | — | 60 | — |

**Reading, and it vindicates the re-opening:**

- **The brief's arithmetic is correct as written.** 6 × 30 = 180 bits per 2 rounds; 128
  clears in two rounds; the MDS bound 25 is the ideal, not the bar. Nothing to correct —
  only to sharpen: the per-S-box figure is **30 bits, not 32**, and the **linear side is
  not better than the differential side** (both 2⁻³⁰), which is the half the brief flagged
  as not done.
- ⚑ **The decisive corroboration is in our own repo**: `ring-hash-design.md:326`
  `[READ]` — *"Poseidon2's internal rounds use I + diag(v), branch **2** — weaker than our
  support-3 — and put the strong MDS only in external rounds."* **A design that ships
  branch 2 in most of its rounds cannot be killed on "6 < 25".**
- ⚑ **The kill's comparator was cross-characteristic.** `[MEASURED]` PART 7b: Poseidon2's
  M_E has entries {1,2,3}; in char 2 those collapse to {1,0,1} (the diagonal block factor
  2 becomes **0**, M4 becomes J₄+I₄). The reduced matrix is invertible but is a
  **different object**, and it reads **branch ≤ 8 at t=24** — which the coset repair
  **matches exactly**. So "below even Poseidon2's own layer" compared a char-2 candidate
  against a BabyBear matrix that has no char-2 instance at its published constants.
- **Neither branch number is disqualifying on statistical grounds.** Even B_l = 2 needs
  only ~5 rounds to pass 128 bits *by the bound*. Statistical resistance was never the
  binding constraint for this family; the binding constraints are structural
  (invariant subspaces) and algebraic (Gröbner / CICO / FreeLunch).

⚠ **Honest scope of the statistical row**: these are bounds on *characteristics*. In a
keyless permutation the attacker also has rebound/truncated routes that beat a
characteristic bound. At 30 bits per active S-box in a 768-bit state this is not close —
but the row is a bound, not a proof of resistance.

---

## 2. WHAT ACTUALLY KILLS WEFT-1 — and it was inside the kill's own script

### 2a. ⚑ The flag is 5 deep, and `weft_branch.py:300` loops `range(1, 5)`

`[MEASURED]` PART 2 — the **exhaustive** lattice, not a sample. For a lane-wise 0-fixing
bijection the S-box maps `{supp ⊆ A}` **onto** itself, so the invariant lane-coordinate
subspaces of the round are **exactly** the closed sets of the support digraph
`i → j ⟺ L[j][i] ≠ 0`. Computed by closure, all of them:

```
dim  8 lanes [16,24)   dim 16 lanes [8,24)   dim 20 lanes [4,24)
dim 22 lanes [2,24)    dim 23 lanes [1,24)          <-- the level the kill skipped
```

**Five, not four.** And the missing level is the sharp one, because `X̂₀ = 1` and every
`X̂ᵢ` (i ≥ 1) vanishes at the point `x₀ = 0`:

```
row 0 of M = (1, 0, 0, …, 0)          [MEASURED, asserted in-script]
```

### 2b. The fixed lane, and why round constants cannot touch it

`output lane 0 = input lane 0`, exactly. Evaluation at the point `0` **reads off the
constant coefficient** — that is all it can do. Consequences, in increasing severity:

- **B_l = 2, EXACT** (PART 1). The witness is the weight-1 mask `e₀`, and it is a **fixed
  point of `Mᵀ`** — so it chains: a linear trail with **exactly one active S-box per round,
  for any number of rounds**. The mask lattice `[MEASURED]` is `{0} ⊂ {0,1} ⊂ {0..3} ⊂
  {0..7} ⊂ {0..15}` — the 1-dimensional level is the iterated trail.
- ⚑⚑ **Worse than any trail: it is deterministic.** The round map descends to the quotient
  `K²⁴/U₀` where `U₀ = {v₀ = 0}` (M-invariant, S-invariant), and the induced map is
  `x₀ ↦ x₀⁻¹ + c₀` — a **32-bit permutation of lane 0 that depends on nothing else, for
  any number of rounds**. `π(x)₀ = g(x₀)` for a public bijection `g`.
- ⚑ **The asymmetry that matters and is not in the kill**: an invariant **subspace** is
  broken by a round constant outside it (the standard escape, and the one
  `design_subfield_invariance.py` relies on). An invariant **quotient** is not — the
  constant merely becomes the small map's own round constant. *The kill's "broken only by
  round-constant addition" clause is true of levels b=1..4 and **false** of b=0.*
- **Sponge consequence, either placement**: lane 0 in the rate ⇒ direct control/inversion
  in that coordinate; lane 0 in the capacity ⇒ 32 bits of capacity are a public function
  of the initial value and never absorb anything. Distinguisher at cost 1 either way; the
  permutation is not an RO substitute, so every Fiat–Shamir use is void.

### 2c. ⚑ The third defect, unrecorded anywhere: the matrix is a GF(2⁸) matrix

`[MEASURED]` PART 3. With the kill's stated domain basis `βⱼ = 2ʲ`, the points are the
integers 0..23 = `span(1, x₀, x₁, x₀x₁, x₂) ⊂ T₃ = GF(2⁸)`; `sᵦ` of a GF(2⁸) subspace is
GF(2⁸)-valued; **max entry of M = 253**. And `x⁻¹` maps every subfield into itself. So

> **`(GF(2⁸))²⁴` — a 2¹⁹² set inside 2⁷⁶⁸ — is closed under the mixing layer AND the
> S-box layer.**

Broken only if the round **constants** leave GF(2⁸) — and the sketch specifies constants
"from the transcript-separation tags we already use" (`aligned-hash-space.md:272`). ⚑ **A
tag that is a small integer IS an element of GF(2⁸).** This is exactly
`design_subfield_invariance.py`'s recorded lesson — *"rely on the coefficients, not on the
constants"* — arriving in the char-2 tower, and it is **invisible to every branch number**:
the sensitivity arm that varied the basis reported branch 6 unchanged while silently moving
the entries in and out of the subfield.

---

## 3. THE ROTATION — verified exactly as the brief claimed, and it is the wrong repair

`[MEASURED]` PART 4, all 24 rotations, not the 4 spot-checked:

| k | invariant lane subspaces | full-diffusion depth |
|---:|---:|---:|
| 0 (the kill's object) | **5** | ∞ |
| 1, 2, 3, 5, 7, 8 | **0** | 2 |
| 11, 12, 16 | **0** | 3 |
| 23 | **0** | 6 |

**Every k ∈ [1,23] destroys every invariant lane subspace, on both the coordinate and the
mask side.** The brief's mechanism is exactly right: the invariant sets are contiguous
suffixes, a rotation sends a suffix to a wrapped set, and no wrapped set is a suffix.

**And it is the wrong repair, for three measured reasons:**

1. **It cannot move either branch number.** `B_d(R·M) = B_d(M) = 6` and
   `B_l(R·M) = B_l(M) = 2`, both re-measured — a permutation preserves Hamming weight on
   both sides, so the whole rotation family is branch-invariant. ⚑ **This is the cleanest
   demonstration available that branch number cannot see the property that killed Weft-1:
   the property changes and the number does not.**
2. **It leaves the layer sparse** (columns 16..23 keep 16 zeros each), so the low-weight
   codewords survive; only their *iterability* is destroyed.
3. **It does not touch the subfield.** A row permutation of a GF(2⁸) matrix is a GF(2⁸)
   matrix. `[MEASURED]` PART 7: `rot k=5` still reads `entries GF(2⁸)`.

---

## 4. ⭐ THE COSET — the repair the kill never considered, and it is free

**The idea.** The triangularity came from the evaluation domain **containing** the
subspace flag: `X̂ᵢ` for `i ≥ 2ᵇ` vanishes on `V_b`, and `V_b` is a *prefix of the domain*.
Evaluate instead on an **affine coset** `x* + V` with `x* ∉ V`: no point lies in any `V_b`,
so **no structural zero exists at all**. Because every `sᵦ` is a linearized polynomial,
`sᵦ(x* + v) = sᵦ(x*) + sᵦ(v)` — the coset transform is **the same butterfly network with
shifted twiddle constants**. `[DERIVED, standard]` **Zero field ops, zero constraints**,
and it is what a BaseFold/FRI encoder does anyway.

`[MEASURED]` PART 5, t = 24, `x* = 0xA3C17E59`:

| property | Weft-1 (linear domain) | **Weft-coset** |
|---|---|---|
| zero entries | 213 / 576 | **0 / 576** |
| **B_d** | 6 EXACT | **8 EXACT** |
| **B_l** | **2** EXACT | **[8, 10]** |
| invariant lane subspaces (coord / mask) | 5 / 5 | **0 / 0** |
| full-diffusion depth | ∞ | **1** |
| twisted-subfield class (§5) | GF(2⁸) | **GF(2³²) — none** |
| `deg(minpoly)` | 24 | **24** |
| internal-round observability (§6) | fails at 16/24 lanes, worst 23 | **passes at 24/24** |

**On the exactness of B_d = 8** — the passes exhaust min-side ≤ 3 and find minimum **10**;
the attaining codeword is a **min-side-4** one the passes cannot reach, constructed:

> `f = (s₄ + a)(s₂ + c)` — novel support `{0, 4, 16, 20}` (wt_in 4), vanishing on the
> `s₄ = a` coset (16 points) and one `s₂ = c` coset (4 points) ⇒ wt_out **4** ⇒ B = 8.

Any codeword of sum ≤ 7 has min-side ≤ 3 and would have been found at 10. **So B_d = 8 is
exact and certified**, by the same self-certifying discipline as the kill's 6.

⚑ **And 8 is not an arbitrary number: it is exactly the char-2 reduction of Poseidon2's own
external layer at the same width** (PART 7b). The repaired transform *equals the shipping
shape's char-2 value*, and delivers 240 bits per 2 rounds against a 128-bit bar.

**Second free condition, from §2c**: `x*` must be a **full-field** element. With `x* = 32`
(outside `V₅` but inside GF(2⁸)) every branch number and every flag count is **identical**
— and the entries stay in GF(2⁸), so the 2¹⁹² set survives. `[MEASURED]`, both rows in
PART 5. Two shifts, same branch, different security: the branch number is blind to this
too.

---

## 5. THE FLAG SEARCH ON `r ∘ novelPack` — stated as coverage, not as an absence

Killing one flag is not the absence of flags. What was searched, and how exhaustively:

| family | method | exhaustive? | result |
|---|---|---|---|
| **all invariant lane-coordinate subspaces** | closed sets of the support digraph — for a 0-fixing lane-wise bijection these are *exactly* the S-box-compatible coordinate subspaces, so closure enumerates the whole lattice | **YES** | Weft-1: **5** (coord) + **5** (mask). rot k≠0: **0/0**. coset: **0/0** |
| **differential subspace trails** (Grassi et al. shape) | for a lane-wise S-box a difference supported on A stays supported on A, so a trail is `A → σ(A)`; growth measured as diffusion depth | **YES** over coordinate supports | Weft-1 ∞; rot 2–6 rounds; coset **1** |
| **linear/mask trails** | same lattice on `Mᵀ` | **YES** | the `{0}` fixed point is Weft-1's iterated 1-active trail |
| **subfield sets** `(GF(2^2^k))²⁴` | entry-level subfield test | YES | Weft-1 & rot: GF(2⁸); coset(full-field x*): none |
| ⭐ **twisted-subfield sets** `{(λᵢaᵢ) : a ∈ F²⁴}` — the S-box preserves these as a *family* (λ ↦ λ⁻¹) | `M` maps one into another **iff** some two-sided diagonal twist `D₁MD₂` is an F-matrix; the **cross ratios** `r(j,i) = M[j][i]M[0][0]/(M[0][i]M[j][0])` are that equivalence's *complete invariant*, so the subfield they generate is the answer | **YES over the whole family** | coset(GF(2⁸) shift): **GF(2⁸) — structure**. coset(full-field shift): **GF(2³²) — none exists** |
| `deg(minpoly)` degeneracy (§6) | Krylov rank from a generic vector | YES | novelPack variants **24/24**; the MDS form **6** and **2** (!) |

**NOT covered — stated, not waived**: general K-subspaces outside the coordinate and
scaled-subfield families; higher-order-differential / integral structure ([WEFT-integral],
open); algebraic degree growth ([WEFT-groebner], open); and the **multi-round minimum
active count** — the 1-round branch number is a *bound*, and §3's rotation result shows the
bound and the truth can diverge (`B_l = 2` with the trail dead after one round). **New
named obligation: [WEFT-multiround] — the 2- and 4-round minimum active S-box counts by
MILP/Matsui search, not by ⌊R/2⌋·B.**

---

## 6. WEFT-2 EVALUATED — the split is backwards, and at this S-box it is cost-NEGATIVE

### 6a. The internal-round condition is not a branch number at all

Poseidon2's internal round applies the S-box to **one** lane. An invariant-subspace attack
exists iff there is `U` with `M_I U ⊆ U` and `U ⊆ ker(eⱼᵀ)` — the S-box is then *linear*
on `U`. The largest such `U` is the **unobservable subspace** of `(eⱼᵀ, M_I)`, so the
condition is exactly **observability**: `rank[eⱼᵀ; eⱼᵀM; …; eⱼᵀM²³] = 24`. `[MEASURED]`
PART 6:

| layer | deg(minpoly) | lanes with a defect | worst defect |
|---|---:|---:|---:|
| **novelPack, linear domain (Weft-2 as briefed)** | 24 | **16 / 24** | ⚑ **23 lanes** |
| novelPack, rot k=5 | 24 | 0 / 24 | 0 |
| **novelPack, coset (full-field x\*)** | 24 | **0 / 24** | 0 |
| Poseidon2 `M_I = J + diag` (control) | — | 0 (at its lane 0) | 0 — **and branch(M_I) = 2, and it SHIPS** |

⚑ **Weft-2 as briefed puts the structured layer exactly where the invariant-subspace
condition binds, and it fails there catastrophically**: with the S-box on lane 0 the
internal rounds are purely linear on a **23-lane** subspace. The only safe lanes are
16..23 — the dense rows. **After the coset repair, all 24 lanes pass.** So the split is
not *wrong in principle*; it is wrong **before** the repair and unnecessary **after** it.

### 6b. After the repair, there is nothing to split

The coset transform satisfies **both** requirements simultaneously — the external-round
requirement (B_d = 8 = the char-2 Poseidon2 value, 240 bits/2 rounds) **and** the
internal-round requirement (observability at every lane). So:

> ⭐ **Keep `novelPack` (coset) in EVERY round.** That restores the "ONE proved linear
> object in the TCB" prize that the internal/external split would have forfeited — the
> split needs a *second* linear object by construction, which is the exact consequence the
> kill said was lost.

### 6c. ⚑ And at this S-box the split is cost-negative

`[DERIVED, shape-level — not a Lean-emitted AIR count; `aligned-hash-space.md` §3e's
settling measurement still stands]`

Poseidon2's partial rounds exist because `x⁵`/`x⁷` have **low** algebraic degree and need
many rounds; partial rounds make many rounds cheap. `x⁻¹` has **maximal** F₂-degree
(n−1 = 31), which is why Vision/Rescue/Mark-32 use **8 full rounds and no partial rounds
at all**. There is no long tail of cheap rounds to buy.

| schedule (t=24, `x⁻¹`, 1 aux cell + 2 deg-3 constraints per S-box) | S-boxes | aux cells/perm | cells / absorbed bit (rate 16·32 = 512) |
|---|---:|---:|---:|
| **8 full rounds (Mark-32's schedule)** | 192 | **192** | **0.375** |
| Poseidon2-style split R_F=8 / R_P=22 | 214 | 214 | 0.418 |
| deployed Poseidon2 BabyBear t=16 (R_F=8, R_P=13) | 141 | **300** `[repo figure]` | **1.21** ✔ reproduces the repo's own 1.21 cells/bit |

**The split costs 11% more cells and buys nothing**, because the S-box count is dominated
by the full rounds either way. The headline **~3.2× cells/bit** is contingent — entirely —
on 8 rounds surviving [WEFT-groebner] at the tower, which has **not** been run, and the
degree-2/3 relation is adversary-symmetric.

**Native cost per permutation** (8 rounds; LCH butterfly count `k·2^{k-1}` mults at
n = 32 ⇒ 80 mults/pass; tower inversion = 1.58× a mult, Mark-32's own measurement):

| mixing | mults/round | mults/perm | + S-box (192 × 1.58 = 303) | vs one-transform |
|---|---:|---:|---:|---:|
| **one-transform coset novelPack** | **80** | 640 | **943** | 1.00× |
| two-transform systematic-RS `V₂V₁⁻¹` | 160 | 1280 | 1583 | 1.68× |
| dense 24×24 | 576 | 4608 | 4911 | 5.21× |

⚑ **The mixing layer dominates the native cost, not the S-box.** So the branch 8 → 25
upgrade costs **1.68× native throughput** — and native hashing throughput is the real
bottleneck in STARK proving (Merkle tree building), not cells.

⚠ **One in-circuit caveat that "linear layers are free" hides**: a dense t=24 layer makes
each round's constraint expression 24 terms wide, which in practice forces committing the
state per round (+24 cells/round ≈ +192 cells/perm, doubling the count); an 80-butterfly
network keeps expressions narrow. **Not measured** — it is a real argument for the
structured layer that only a Lean-emitted AIR settles.

---

## 7. ⚑ THE SIBLING LANE'S MDS FORM, RUN THROUGH THESE INSTRUMENTS — two unstated conditions

`post-weft-hash.md` §3 landed the stronger repair on the same axis (**"the structure was
never the problem, the point set was"** — independent convergence, cross-referenced both
ways): `A = V₂·V₁⁻¹`, interpolate on one point set, evaluate on a **disjoint** one ⇒
**MDS by the RS theorem, branch 25**. That is a theorem where mine is an instance fact,
and it is the stronger result. It is also **silent about two families**, which is what this
lane's instruments are for. `[MEASURED]` PART 8:

| `A = V₂V₁⁻¹` | entries | twisted-F | `deg(minpoly)` | internal-round defect (best lane) |
|---|---|---|---:|---:|
| natural split 0..23 / 24..47 | **GF(2⁸)** | **GF(2⁸)** | **6** / 24 | **18 lanes** |
| parity points shifted by a full-field `x*` | GF(2³²) | GF(2³²) — none | **2** / 24 ⚑ `A² = I` | **22 lanes** |

1. ⚑ **MDS does not preclude the subfield set.** With the natural integer point split
   *all 48 points lie in GF(2⁸)*, so `A` is a GF(2⁸) matrix and `(GF(2⁸))²⁴` — 2¹⁹² — is
   closed under the whole round up to constants, **exactly as in Weft-1**. Superregularity
   says nothing about it. **Free repair: shift one point set by a full-field element** —
   the points stay distinct, so the RS/MDS theorem is untouched (measured: entries and
   twisted-F both go to GF(2³²)).
2. ⚑ **`A` has a degenerate minimal polynomial**, and in the subfield-repaired form it is
   an **involution, `A² = I`**. Consequence: the Krylov space from *any* single lane is 6-
   or 2-dimensional, so **every** choice of S-box lane leaves an 18- or 22-lane subspace on
   which partial rounds are linear.
   - ⚠ **This is NOT a break of Mark-32**, which uses **8 full rounds and no partial
     rounds** — involutory MDS matrices are standard practice (ANUBIS, KHAZAD, PRINCE).
   - ⚑ **It IS decisive for architecture**: the systematic-RS form **cannot serve a
     partial/internal round**, and the one-transform coset form (`deg(minpoly) = 24`,
     observability at all 24 lanes) **can**. If a split is ever wanted, the assignment is
     *dense-external / coset-internal* — the opposite of using the RS form everywhere, and
     the opposite face of the brief's Weft-2.
3. **Obligation handed to the adoption path**: read Mark-32's actual Sage listing for its
   point split, its linearized-affine `B` coefficients, and its round constants, and test
   all three for **subfield membership**. Cheap (`u^(2^k) == u`), and the escape it relies
   on today is an accident of instantiation, not a stated condition.

---

## 8. THE TRADE, PRICED — and the brief's framing does not survive contact with our own record

**What custom buys** (alignment; measured or derived above): one GPU kernel family for
hash-and-encode; one already-proved Lean object (`novelPack`) rather than two; relation
degree ≤ 3 matched to the degree-3 rung; tower-native, no bit decomposition; **~3.2×
cells/bit** and **1.68× native mixing** over the two-transform form — *both contingent on
round counts nobody has computed.*

**What custom buys in security: nothing.** Unchanged, and this lane makes the price
**measurable rather than rhetorical**:

> ⚑ **The base rate of "our own careful, tooled analysis missed a total break" is, on this
> exact design, 1 for 1.** The kill was thorough — exact branch number, duality
> certification, basis sensitivity arm, random control, a structural-witness falsifier —
> and it shipped a verdict while a `range(1, 5)` in its own script hid a **fixed lane**
> that breaks the permutation outright. That is the cost of zero cryptanalytic age, in
> units of one measured instance.

**But the brief's counterparty is wrong for this rung.** ⚑ *On the binary rung there is no
aged hash to adopt.* `[READ]` `hash-landscape.md:619`: **Vision / Vision Mark-32 —
*"none found — and nobody has looked" · ⚠ untested, not "safe"***. CheapLunch (2025/2040),
Perrin (2024/605) and Rijmen (2024/656) are **prime-field** assets attached to
XHash8/RPO — and `post-weft-hash.md` §5 already found XHash8 does not fit us three ways
(field, characteristic, need). So:

- The real comparison is **not** "custom vs aged" but **"our object vs a published object
  with the same skeleton, both unanalyzed"** — Weft-2 and Mark-32 are both `x⁻¹` at
  t=24/GF(2³²)/r16/c8, and Mark-32's MDS *is* the systematic-RS form of our own transform.
- On that comparison **adopt still wins, for an epistemic-flywheel reason rather than a
  security-margin one**: an unanalyzed *published* design accumulates analysis and an
  unanalyzed *private* one does not. A named target is worth more than a margin.
- **And the alignment premium custom was supposed to buy is ~0**, because Mark-32 already
  *is* the aligned design (`post-weft-hash.md` §3-4). The only alignment Weft-2 adds over
  Mark-32 is the **one-transform** mixing — worth **1.68× native throughput**, purchased
  with **branch 25 → 8** (i.e. 750 → 240 bits per 2 rounds, both far over a 128-bit bar)
  and with **theorem → measured instance**.

### VERDICT

**Weft-2 is killed as a thing to BUILD — and the kill's *reason* is replaced, which is the
point of the re-opening.** Not "branch 6 < MDS 25" (that comparison is against the ideal,
is cross-characteristic, and is refuted by Poseidon2's own branch-2 internal layer), but:

> **the evaluation domain contained its own interpolation window, which produced a fixed
> lane, a 5-deep flag, and a GF(2⁸) subfield set — none of which any branch number can
> see.**

**What survives and should be routed, not discarded:**

1. ⭐ **The coset condition is a free, general design law** for anything reusing an
   encoder transform as a mixing layer, and it applies to the **adopted** candidate too
   (§7 item 1) — the Mark-32 recommendation should carry it.
2. ⭐ **The one-transform coset form is the only candidate on the table that can serve a
   partial round** (§7 item 2). Bank it in case a char-2 partial-round design is ever
   wanted.
3. **Three free conditions, all cheap, none of them branch numbers**: coset domain;
   full-field shift; full-field round constants.

---

## 9. THE AMENDED GATE (written into `swarm/BRIEF-TEMPLATE.md` §7d)

The gate as it stood — *"compute the branch number FIRST"* — is **paid for by the wrong
half of Weft**, and this lane's subject amends it. Branch number is a **one-round**
quantity; every property that actually killed Weft-1 is **multi-round**, and §3 exhibits
the divergence directly: the rotation family changes the structure completely while
`B_d` and `B_l` do not move at all.

**The amended order, and the reason each step exists:**

1. **STRUCTURE FIRST — the invariant/subspace-trail search, exhaustive over the families
   it can be exhaustive over.** Enumerate the closed sets of the support digraph on **both**
   `M` and `Mᵀ`, indexing from **b = 0** — the level that reads a *fixed lane* is the one a
   loop bound silently skips. Report **∞ diffusion depth** as a hard fail.
2. **The subfield test, entry-level and twisted.** Do the layer's entries lie in a proper
   subfield? Does any two-sided diagonal twist put them there (⇒ compute the subfield
   generated by the cross ratios)? **MDS does not answer this** (§7). Then check the round
   *constants* the same way — a small-integer transcript tag lives in GF(2⁸).
3. **`deg(minpoly)` and per-lane observability**, if any partial/internal round is
   contemplated. Poseidon2's internal condition is observability, **not** a branch number —
   its own internal layer is **branch 2**.
4. **THEN the branch number, on both sides.** `B_d(M)` *and* `B_l(M) = B_d(Mᵀ)`; the kill
   computed only the first, and the second read **2**. Score it against **the bar**, not
   against the MDS ideal, using the S-box's own DP/LP (for `x⁻¹` at GF(2ⁿ): **30 bits per
   active S-box at n=32, on both sides**), and against a **same-characteristic** comparator.
5. **A quotient is not a subspace.** "Broken by round constants" is the standard escape for
   an invariant *subspace*; it is **false** for an invariant *quotient*, which constants
   merely re-parameterise. State which one you found.
6. **If the layer is inherited from another object, the point set is the design decision.**
   Weft died by evaluating **inside its own interpolation window**. Moving the evaluation
   set off the window is free and is the difference between branch 6 with a fixed lane and
   branch 8 (one transform) or 25 (two transforms, MDS by theorem).

---

## 10. Reproduce

```bash
cd ~/src/ring-ro-hash && python3 weft2_structure.py     # ~107 s, all parts
cd ~/src/ring-ro-hash && python3 weft_branch.py         # the kill, unmodified
cd ~/src/ring-ro-hash && python3 mark32_sysrs_branch.py # the sibling lane's MDS form
```

## 11. Obligation-table updates written into the source notes

- `aligned-hash-space.md` §3d [WEFT-subspace]: kill **stands, reason REPLACED** (this note
  §2); the "fallback clause is the only live form" line is **superseded** — the free coset
  repair keeps one transform (§4).
- `hash-landscape.md` ADDENDUM 3: the branch-6 headline is **not the disqualifying fact**
  (§1); the Poseidon2 comparator is **cross-characteristic** (§1b).
- `post-weft-hash.md` §3: coset result **is** the cheaper one-transform cousin (B_d = 8
  exact, §4) — plus two conditions its MDS form does not carry (§7).
- **New named obligation [WEFT-multiround]**: 2- and 4-round minimum active S-box counts by
  search, since §3 shows the 1-round branch bound and the truth diverge.
