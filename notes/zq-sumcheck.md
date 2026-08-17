# Sumcheck natively over Z_Q = F_q0 × F_q1 × F_q2 — the mathematics, the Lean verdict, the unstatability theorem, the price

**Status 2026-08-16, in progress.** Mathematics + Lean lane. Basic research: chart and
formalize; no product selection. Everything measured/read is labelled; the two claims
inherited from the brief are checked in §5 (one holds, one is **half-refuted**).

Sources read at source, not relayed: `metatheory/Bfv/CrossLimb.lean` (whole file),
`notes/cross-limb-binding.md` (whole file), `minidregg/Selvage/Sumcheck.lean` +
`MultilinearExtension.lean` + `ReedSolomon.lean:100–145` + `Depth.lean` binders +
`SumcheckReduction.lean` binders, CCKP19 (`~/paperbin/ring-cckp19-…-2019-762.pdf`,
full text extracted; their Lemma 3 / Theorem 2 / Remark 1 / Theorem 3 / Theorem 4 /
Lemma 6 read directly).

---

## 0. Headlines

1. **The mathematics is real and small.** Sumcheck over `Z_Q` with challenges from a
   *sampling set* `A` (pairwise differences invertible) has soundness `v·d/|A|`;
   `|A| ≤ min qᵢ ≈ 2³⁶` is a **theorem-level ceiling**, not a design choice (§1.4).
   Amplification is one shared ring extension `Z_Q[y]/(f)` with `f` simultaneously
   irreducible mod each prime — a CRT-interleave of three field extensions.
   **A shared Ext2 does NOT clear the repo's ~124-bit bar (2⁷² base). Ext4 does
   (2¹⁴⁴), and beats deployed BabyBear-Ext4 (2^123.6) by ~20 bits.** (§2)
2. **Selvage generalizes, and `Field` bites in exactly ONE lemma** —
   `Selvage/Sumcheck.lean:77 card_agreeFinset_lt` ← `ReedSolomon.lean:122
   card_agreeSet_lt_of_ne`, whose proof is mathlib root counting
   (`Polynomial.roots` / `card_le_degree_of_subset_roots`, both `[IsDomain]`).
   Everything else is already ring-general or field-free *at the binders* (§3).
   ⚑ And the bite is not cosmetic: the field-wide statement is **FALSE over Z_Q**
   (proved, `zq_fieldwide_sz_false`) — the statement must change (count agreement
   *inside A*), not the binder.
3. **The cross-limb provenance forgery (Hole A) is unstatable over Z_Q, and this is
   now a theorem connected to the CrossLimb exhibit**: the honest per-limb
   conjunction over one shared pair *is* one Z_Q equation
   (`boundMul_iff_zqBound`, an `Iff`), and CrossLimb's own frankenstein — the object
   that satisfies every per-limb equation — is a flatly **false** Z_Q statement
   (`zq_same_forgery_refused`). There is no per-limb slot to satisfy. (§4)
4. ⚑ **Hole B (expressibility) SURVIVES the Z_Q route, by a new theorem.**
   Polynomials over a product ring compute **exactly the limb-local functions**
   (`eval` commutes with each projection). The ct×ct rescale `⌊t·x/Q⌉` is not
   limb-local (`rescale_not_limb_local`, CrossLimb), therefore **no polynomial over
   Z_Q computes it** (`rescale_not_zq_polynomial`). The brief's expressibility hope
   is thereby half-refuted: a Z_Q-native statement can *name* the CRT reconstruction
   (it is a well-defined function of the Z_Q element), but can never *arithmetize*
   it as a Z_Q-polynomial identity. The redundant-basis/witness fix is still needed
   for the rescale, exactly as before. (§5)
5. **Price: the brief's "3× the sumcheck work" is pessimistic.** In limb-mul counts
   the Z_Q sumcheck is within ~1× of the bridged-BabyBear sumcheck it replaces
   (3 limbs *instead of* 2 bridge felts + a doubled table, not in addition to them),
   and commitment-side hashing is the same either way (a 36/37-bit residue costs 2
   absorbed BabyBear felts under any route). What the Z_Q route buys is the binding
   *by construction* at the claim layer; what it costs is concentrated at the
   PCS/opening boundary and in new transcript machinery. (§6)

---

## 1. The mathematics, stated precisely

### 1.1 The ring, the sampling set, and the ceiling

`Z_Q = ℤ/Q ≅ F_q0 × F_q1 × F_q2` (CRT), with the deployed tower
`q0 = 0xffffee001 = 2³⁶ − 73,727`, `q1 = 0xffffc4001 = 2³⁶ − 245,759`,
`q2 = 0x1ffffe0001 = 2³⁷ − 131,071`; `Q = q0·q1·q2`, `log₂ Q ≈ 109`
(`Bfv.deployed_moduli_prod` pins `q0·q1·q2 = q4096`). Everything below is stated for
a finite product of finite fields `R = ∏_{i<L} K_i`; the deployed case is `L = 3`.

**Sampling set** (CCKP19 Lemma 3, citing Bishnoi–Clark–Potukuchi–Schmitt): a finite
`A ⊆ R` such that for all distinct `a, b ∈ A`, `a − b` is *not a zero divisor*.
Two simplifications specific to our setting, both easy theorems:

* **In a finite commutative ring, non-zero-divisor ⟺ unit** (multiplication by a
  non-zero-divisor is injective, hence surjective by finiteness). So CCKP19's
  Remark 1 — the "stronger" invertible-differences condition needed for Lagrange
  interpolation of round polynomials from evaluation points — is *automatic* for
  every finite ring, not a lucky property of their examples.
* **In `∏ K_i`, unit ⟺ nonzero in every coordinate** (`Pi.isUnit_iff` +
  `isUnit_iff_ne_zero`). So the sampling condition is: distinct elements of `A`
  differ in **every** limb.

**The canonical maximal set**: `A = {ι(0), ι(1), …, ι(min qᵢ − 1)}` where `ι` is the
diagonal embedding `n ↦ (n mod q₀, n mod q₁, n mod q₂)`. Distinct `a > b` give
`ι(a) − ι(b) = ι(a−b)` with `0 < a−b < min qᵢ ≤ qᵢ`, nonzero mod every `qᵢ`. This is
CCKP19 Example 1 transplanted from `Z_{p^e}` to the CRT product. The verifier's
interpolation nodes `{0,1,…,d}` sit inside it.

**The ceiling (a theorem, formalized as `samplingSet_card_le`)**: *any* sampling set
has `|A| ≤ min_i |K_i|`, because the projection to each coordinate is injective on
`A` (a shared coordinate makes the difference a zero divisor). So

> `|A| = min qᵢ = q1 = 68,719,230,977 ≈ 2^35.999995` — **2³⁶ is the base ceiling,
> and nothing recovers the other 73 bits of `Q` without an extension.**

The exhibit-scale version with teeth: over `ZMod 3 × ZMod 5` the diagonal
`{(0,0),(1,1),(2,2)}` is a sampling set of card `3 = min` — the ceiling is attained
(`zqSamplingA_attains_ceiling`), and by the ceiling theorem no 4-element sampling
set exists.

### 1.2 Degree and MLE, coordinate-wise

* **Polynomials over `R` are triples of coordinate polynomials**: `Polynomial R`
  projects along each `π_i : R →+* K_i` by `Polynomial.map`, coefficient-wise
  (`coeff_map`), and `p = q ↔ ∀ i, p.map π_i = q.map π_i`. Evaluation commutes:
  `π_i (p.eval x) = (p.map π_i).eval (π_i x)` — **limb-locality of ring
  polynomials** (formalized, `eval_fst`/`eval_pi`; the single most load-bearing
  three lines in this note, used with opposite signs in §4 and §5).
* **Degree**: `(p.map π_i).degree ≤ p.degree` (`degree_map_le`; strict drop possible
  when the leading coefficient vanishes in coordinate `i` — a zero-divisor leading
  coefficient, impossible over a field). For the protocol this is the right
  direction: the verifier receives `d+1` ring elements as coefficients, and that
  *syntactic* bound projects to a degree-≤d bound in every coordinate.
* **MLE**: `Selvage/MultilinearExtension.lean`'s entire `Cube` section is **already
  `[CommRing F]`** — `mle`, `mle_agrees`, `mle_injective`, `mle_multilinear`,
  `roundSum`, `residualSum`, the chain identities — and uniqueness
  (`multiAffine_eq_mle`) needs only `[Nontrivial F]`, which `Z_Q` satisfies. Nothing
  to generalize there; the binders are real. Coordinate-wise:
  `π_i ∘ mle f = mle (π_i ∘ f)` composed with `π_i` on the point — a `map_sum`/
  `map_prod` push, so **a Z_Q-MLE is exactly three field MLEs sharing one index
  space**, and a Z_Q-MLE evaluation claim `f̂(r) = c` is three field claims at the
  *projected* common point.

### 1.3 The soundness theorem (what "three parallel sumchecks sharing one challenge" means)

Protocol: the standard sumcheck for `∑_{b∈{0,1}^v} g(b) = H` with `g : R^v → R`,
round messages of degree ≤ d, **challenges drawn uniformly from `A`**, all verifier
equality checks being `R`-equalities (i.e. all `L` coordinates at once).

> **Theorem (ring sumcheck, CCKP19 Thm 2 shape; our proof is the coordinate
> projection).** If the claim is false (`H ≠ S` in `R`), any prover is accepted with
> probability at most `v·d/|A|` over the challenge vector in `A^v`.

*Proof shape, which is also the Lean port map.* `H ≠ S` in `R` ⟹ `H` and `S` differ
in some coordinate `j`; **fix that `j`**. Acceptance is an `R`-equality at every
round, so the coordinate-`j` projections of the transcript form an accepting
transcript of the *field* sumcheck over `K_j` for the false field claim
`π_j H ≠ π_j S` — with round polynomials `p̃.map π_j` (degree ≤ d by
`degree_map_le`) and challenges `π_j(r)`. The field lie-persistence argument
(`Selvage.lie_persists`, ring-agnostic) forces some round to launder in coordinate
`j`; laundering at round `i` means the projected polynomials — distinct, else no
laundering is possible with the claim still false — agree at `π_j(r_i)`, which by
field Schwartz–Zippel happens for at most `d` values of `π_j(r_i)`, and the
projection `A → K_j` is **injective** (sampling condition), so at most `d` elements
of `A`. Union bound over `v` rounds: `v·d/|A|`. ∎

Notes on the shape:

* **No factor-L union loss.** One false coordinate is fixed once, up front. The
  bound is the field bound *in the weakest coordinate*: `v·d/min qᵢ`.
* **The per-round error is `d/|A| ≈ d/2³⁶`, and rounds ADD, not compound.** The
  brief's "36 bits/round base" is the per-round error; the total is `v·d/|A|`
  (union bound over one transcript), not `(1/2³⁶)^v`. Amplification must grow `|A|`
  or repeat transcripts — §2.
* **The final oracle check is ONE `R`-point evaluation** `f̂(r) = c`, `r ∈ A^v ⊆
  R^v` — the "single Z_Q-MLE evaluation" of the brief, literally: three field
  openings at the three projections of the same `r`, welded by being coordinates
  of one ring equality.
* The fully-adaptive version goes through unchanged: prefix-measurability and the
  union-bound engine (`Selvage/Depth.lean`) never touch the ring structure (§3).

### 1.4 What CCKP19 actually prove, for the record

Their Lemma 3 (generalized Schwartz–Zippel, total degree `D`, `Pr ≤ D/|A|`),
Theorem 2 (sumcheck, `nd/|A|`), Theorem 3 (GKR, `(7d·log S + log m)/|A|` — the
figure quoted in the brief), Theorem 4 + Lemma 6 (Galois-ring `Z_{p^e}[t]/(f)`
sampling sets of size `p^deg f`, with sparse irreducible binomial candidates).
Their ring is `Z_{p^e}` (local, NOT a CRT product) — chosen **precisely so that
base-p rounding is expressible by a low-degree polynomial** (`ldr`, their §V). Read
against §5 below: their ring choice is the contrapositive of our Hole-B theorem —
in a CRT product no polynomial computes the rescale, and they avoided the product
exactly to keep rounding polynomial. The two facts corroborate each other.

---

## 2. Amplification: one shared extension, not three, not repetition

The three candidate mechanisms the brief names, priced:

**(a) A shared ring extension — the right answer.** Choose monic `f ∈ Z_Q[y]` of
degree `k` whose reduction mod each `qᵢ` is irreducible (CRT-lift one irreducible
per prime; existence is trivial by CRT + the density of irreducibles; CCKP19
Lemma 6 lists sparse candidates). Then

```
S = Z_Q[y]/(f) ≅ F_{q0^k} × F_{q1^k} × F_{q2^k}
```

is again a product of fields, with sampling-set ceiling `min qᵢ^k ≈ 2^{36k}`,
attained by the same diagonal construction inside each factor. "Extension of each
factor" and "one shared extension of Z_Q" are **the same object** — the CRT
interleave of the three per-field extensions; the shared challenge is one element
of `S`. Tables stay `Z_Q`-valued; round polynomials live over `S` after the first
fold — exactly the deployed BabyBear/Ext4 base-field/challenge-field split.

Concretely: all three primes are NTT-friendly (`≡ 1 mod 2¹³⁺`), hence `≡ 1 mod 4`,
so by the binomial criterion (Lang VI.9.1; the `−4F⁴` clause is vacuous when
`−1` is a square) **`f = y⁴ − c` is simultaneously irreducible for any `c` that is
a quadratic non-residue mod all three primes** — such `c` exist with density 1/8
and are found by three Legendre symbols. One sparse binomial, mul in `S` =
16 `Z_Q`-muls + 3 scalar muls for the reduction.

| mechanism | challenge space | ε at `v·d = 75` | clears ~124-bit bar? |
|---|---:|---:|---|
| base `A ⊆ Z_Q` | `2^36.0` | `2^-29.8` | no |
| shared Ext2 (`k=2`) | `2^72` | `2^-65.8` | **no** |
| shared Ext3 (`k=3`) | `2^108` | `2^-101.8` | no (−22 bits) |
| **shared Ext4 (`k=4`)** | `2^144` | `2^-137.8` | **yes** (+14 over BB-Ext4's `2^-117.4`) |
| repetition, `t` transcripts | `(2^36)^t` effective | `(2^-29.8)^t` | t=4: `2^-119.3` no; t=5 yes |

**(b) Extension of each factor separately** — same ring as (a) by CRT; the only
way to get it wrong is to sample the three extension challenges *independently*,
which reopens a provenance-style seam between the coordinate transcripts. The
shared-`S`-element formulation is the binding.

**(c) Repetition** — `t` independent transcripts multiply errors, but `t = 4` still
misses the bar (`2^-119.3`) and `t = 5` costs 5× prover and verifier for a worse
bound than `k = 4`'s one transcript at ~3× challenge-arithmetic cost. Dominated.

⚠ Bound honesty (the CLAUDE.md rule about quoting the flattering number): all ε
figures above are the **soundness error of the sumcheck reduction alone**, at the
worked point `v = 25 rounds, d = 3`. They do not include the PCS/opening error of
whatever commitment the terminal claim is opened against, and `v·d` scales the
bound linearly — restate at the real `v, d` of any concrete circuit before quoting.

---

## 3. The Lean verdict: where `Field` actually is, read at the binders

Audit of every layer the port touches (file:line = read, not assumed):

| layer | binder as written | verdict |
|---|---|---|
| `Depth.lean` `uniformProb`/`splitCoord`/`uniformProb_prod_le`/`uniformProb_exists_le` | `{C : Type} [Fintype C]` (`Depth.lean:63`) | **field-free already**; instantiate `C := ↥A` |
| `Sumcheck.lean` `lie_persists`/`sumcheck_reduction` (:175, :200) | ambient `[Field F]`, `omit`s only Fintype/DecidableEq | `Field` unused — `Polynomial.eval` equalities; `[CommRing]` (even Semiring) suffices |
| `Sumcheck.lean` `uniformProb_mem_finset`/`uniformProb_coord_mem` (:92, :104) | `omit [Field F] [DecidableEq F]` | field-free by their own `omit`s |
| `SumcheckReduction.lean` adaptive layer (:296, :342) | `[Field F] [Fintype F]` | consumes only the counting bound; no new bite |
| `MultilinearExtension.lean` `Cube` section (:92) | **`[CommRing F]`** (+`[Nontrivial F]` for uniqueness at :205) | already general — nothing to do |
| `MultilinearExtension.lean` `Realizer` (:493) | `[Field F]` | `Field` unused in `roundPoly`/`roundSum` plumbing (`ring` tactic = CommRing); inherits the one bite below |
| **`Sumcheck.lean:77 card_agreeFinset_lt` ← `ReedSolomon.lean:122 card_agreeSet_lt_of_ne`** | `[Field F]` | ⚑ **THE bite**: proof is `Polynomial.mem_roots` + `card_le_degree_of_subset_roots`, mathlib `[IsDomain]` root counting |

**The verdict, stated with its teeth.** The `Field` binder is load-bearing in
exactly one lemma, and there it is **not cosmetically weakenable**, because the
*statement* is false over `Z_Q`: distinct degree-<d polynomials can agree on far
more than `d` ring elements. Formalized as the negative control
`zq_fieldwide_sz_false` (metatheory): over `ZMod 3 × ZMod 5`, `p = C(1,0)·X` and
`q = 0` are distinct, degree < 2, and agree on **5 > 2** points (the whole
`{0}×ZMod 5` fiber). The correct generalization changes the statement — count
agreement **inside a sampling set `A`** — and that statement is proved
(`zq_agree_card_lt`, metatheory, via coordinate projection reusing mathlib's field
root counting; no new root counting).

**The generalized soundness, with the sampling-set parameter** (the statement the
Selvage port discharges; shapes match `Sumcheck.lean` verbatim):

```
theorem sumcheck_soundness_ring
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (A : Finset R) (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsUnit (a - b))
    {v d : ℕ} {prover honest : ℕ → Polynomial R} {H S : R}
    (hProverDeg : ∀ i < v, (prover i).degree < (d+1 : ℕ))
    (hHonestDeg : ∀ i < v, (honest i).degree < (d+1 : ℕ))
    (hHonest : ∀ (r : Fin v → ↥A), ∀ i < v,
      (honest i).eval 0 + (honest i).eval 1 = scChain S honest (chalOf (fun j => ↑(r j))) i) :
    uniformProb (Fin v → ↥A)
      (fun r => AcceptsFalse prover honest H S (fun j => ↑(r j)))
      ≤ (v : ℝ) * ((d : ℝ) / A.card)
```

(For finite `R`, `IsUnit (a−b)` is equivalent to CCKP19's non-zero-divisor
condition — §1.1. `0, 1 ∈ A` is implied nowhere and needed nowhere: the boolean
checks evaluate at ring constants, only *challenges* come from `A`.)

**Port inventory** (what is new work vs. re-binding):
1. `card_agreeFinset_lt` → the `A`-relative version. **PROVED** today in
   metatheory for products of fields (`zq_agree_card_lt`); the arbitrary-CommRing
   version (regular differences, iterated factor theorem via `dvd_iff_isRoot`,
   Bishnoi's proof) is a real but bounded induction nobody needs until a
   non-product ring shows up.
2. The probability layer: instantiate `Depth.lean` at `C := ↥A`. Zero mathematics.
3. Plumbing: `eval` at `↑(r i)` coercions; `LaunderEvent`/`AcceptsFalse` reworded
   over the coerced challenge stream. Zero mathematics.
4. `MultilinearExtension.lean` Realizer: relax `[Field F]` → `[CommRing F]`
   (cosmetic per the audit above) so `mleHonest` serves as the honest Z_Q prover.

Blocker: **none mathematical.** The one repo-boundary fact: `Selvage` lives in
minidregg and `Bfv` in breadstuffs/metatheory, so the connected theorem
("Z_Q-sumcheck soundness applied to the CrossLimb multiplication claim") cannot be
stated in either tree without either the Selvage port or duplicating the protocol
layer; today's metatheory file proves the SZ engine + the unstatability side and
leaves the protocol port as the named Selvage work item.

---

## 4. The vFHE payoff: the forgery is unstatable — theorem shapes (PROVED, §see artifacts)

Vocabulary from `Bfv/CrossLimb.lean` (read: `PerLimbMul` = ∀limb ∃pair;
`BoundMul` = ∃pair ∀limb; the exhibit `exhibitQ = (3,5)`, `exhibitPool =
((1,0),(0,1))`, `exhibitOut = (1,1)` satisfies `PerLimbMul`, refutes `BoundMul`,
and reconstructs to a value no honest evaluation produces).

Over the ring the limbs *are one object*: `Z_15 ≅ ZMod 3 × ZMod 5`. Three theorems:

1. **`boundMul_iff_zqBound`** (an `Iff`, general pool): for the exhibit basis, the
   honest bound relation `BoundMul exhibitQ pool out` holds **iff** the single ring
   statement `∃ ja jb, zq(out) = zq(pool ja) * zq(pool jb)` holds, where `zq` casts
   the limb vectors into `ZMod 3 × ZMod 5`. The per-limb conjunction over a shared
   pair *is* one ring equation — `CrossLimb.boundMul_iff_sharedSelector`'s
   algebraic twin, now with the ring product doing the conjunction.
2. **`zq_same_forgery_refused`**: the SAME frankenstein
   (`exhibitPool`/`exhibitOut`) that satisfies every per-limb equation
   (`exhibit_perLimb`, cited, not re-proved) is a **false ring statement**: no pair
   from the Z_Q pool multiplies to `zq(exhibitOut)`. Unstatability made concrete:
   over Z_Q there is nothing for the forger to satisfy — the attack is not refused
   by an added check; the sentence it needs cannot be formed. A Z_Q-relation about
   pool elements has one selector, quantified **outside** the coordinate split,
   because the coordinates of a ring element are not independent statement slots.
3. **Satisfiability twin** (house law): the honest product does satisfy the ring
   statement, so the refuted predicate is non-vacuous.

Connection to the sumcheck: rendered as a Z_Q-sumcheck instance (the
multiplication relation as a Z_Q-MLE identity over committed Z_Q tables), the
frankenstein is an instance with a **false claim**, caught except with
`v·d/|A|` by §1.3 — versus per-limb systems, where it is a *true* claim about the
wrong statement, invisible at any soundness. The hole moves from "unchecked" to
"unstatable," which is the strongest closure class there is.

⚠ Perimeter, stated so it cannot be over-read: unstatability holds at the
**claim/statement layer**. The commitment layer must still hand the verifier
Z_Q-objects — one handle per ciphertext covering all limbs (one tree whose leaves
carry all three limb values, or three trees welded under one root). If each limb
had its own independently-openable handle, per-limb selection would reappear one
layer down, at the opening index. That is a layout obligation of the PCS, priced
in §6; it is the same obligation `notes/cross-limb-binding.md` §5 found the
deployed fresh-encryption system meets *by accident of witness layout*.

---

## 5. Hole B over Z_Q: nameable, NOT arithmetizable (the brief's claim, checked)

**The new theorem (limb-locality of ring polynomials).** For any `p ∈ R[X]` over
`R = ∏ K_i` and any `x`, `π_i(p.eval x) = (p.map π_i).eval (π_i x)`: coordinate
`i` of a polynomial's output depends only on coordinate `i` of its input. (Three
lines from `hom_eval₂`; formalized both for `Prod` and for `Fin L` products.)

Two corollaries with opposite signs:

* **For Hole A this is the closure**: it is *why* a Z_Q-polynomial identity checked
  at a shared challenge decomposes into per-limb identities with the SAME selector
  and the same challenge — §1.3's projection argument and §4's `Iff` both ride it.
* **For Hole B it is the obstruction**: `rescale_not_limb_local`
  (CrossLimb, cited) exhibits `⌊t·x/Q⌉` reading the reconstruction across limbs;
  therefore **no `p ∈ Z_Q[X]` computes the rescale** (`rescale_not_zq_polynomial`,
  proved on the (3,5) exhibit: inputs `0` and `6` of `ℤ/15` agree mod 3, their
  rescales `0` and `1` differ mod 3, and a polynomial's mod-3 output cannot tell
  them apart). Satisfiable twin: the ct×ct *multiply itself* IS a Z_Q polynomial
  (`X·Y`; `mul_is_zq_polynomial`), so the refuted predicate is not vacuous — the
  multiply is Z_Q-arithmetizable, the rescale alone is not.

**Verdict on the brief's claim** ("a Z_Q-native statement CAN name `⌊t·x/Q⌉`"):
**half true.** The rescale is a well-defined *function* of the Z_Q element (unlike
per-limb, where it is not a function of the limb at all — that is Hole B's original
form), so a Z_Q-native *relation* can name it, quantifying over a committed witness
for the output plus decomposition/range witnesses tying it to the input. What it
can never be is a Z_Q-**polynomial** identity — the thing a sumcheck natively
checks. So the Z_Q route upgrades Hole B from "the object does not exist per-limb"
to "the object exists but needs non-polynomial witness structure" — the same
redundant-basis/reconstruction gadget as before, now with a theorem saying no
cleverness inside `Z_Q[X]` avoids it. CCKP19's own ring choice corroborates: they
took `Z_{p^e}` (NOT a CRT product) precisely to make base-p rounding low-degree
(§1.4).

---

## 6. The price, in counts

Instrument: committed/absorbed felts and ring-multiplications, never clocks.
Reference numbers from `notes/cross-limb-binding.md` §3 (measured/calibrated there):
one ciphertext = 2 polys × 4096 coeffs = 8,192 Z_Q elements = 24,576 limb residues;
Layout-B bridging = 49,152 BabyBear felts/ct; the bridge's commit-cost delta
= +220,201…+294,912 perms/ct @ lb=6 (w=64/w=16), +13,763…+18,432 @ lb=2.

**The brief's "3× the sumcheck work" — corrected.** The honest baseline is not a
free field sumcheck; it is the row-interleaved BabyBear route, whose table is
`2×` the entries (49,152 felts, 16 variables) in a 31-bit field. Counts per
ciphertext-table sumcheck pass (`Σ_rounds ≈ 2·table` evaluations, degree-d cell
work folded into the constant):

| | table | base rounds | base-ring ops per pass | word width | challenge (post-fold) arithmetic |
|---|---|---|---|---|---|
| bridged BabyBear (row-interleave closure) | 49,152 felts = 2^15.6 | 16 | ≈ 2·49,152 BB-ops | 31-bit (u32 mul) | Ext4-BB: 16 BB-muls/op |
| **Z_Q-native** | 8,192 Z_Q = 2^13 | 13 | ≈ 2·8,192 Z_Q-ops = **2·24,576 limb-ops** | 36/37-bit (u64/u128 mul, ≈2× a BB mul) | Ext4-Z_Q: 16 Z_Q-muls = 48 limb-muls/op (~3× BB-Ext4 in muls, on 3× fewer... see text) |

Reading: **base-round work is a wash** — 3 limbs *replace* the 2 bridge felts and
the doubled table (49,152 limb-ops vs 98,304 BB-ops per pass, each limb-op ~2× a
BB-op) — and the Z_Q route runs 3 fewer rounds. Challenge-phase S-arithmetic is
~1.5–3× heavier per op on tables of the same total word count. Net: **within ~1×
either way at count resolution; "3×" was priced against the wrong baseline** (a
single-limb field sumcheck of the same table, which is not a sound rival — it IS
the per-limb hole).

**Where the real costs are** (the honest deltas, neither zero):

1. **Commitment hashing: EQUAL by information content.** A 36/37-bit residue costs
   2 absorbed BabyBear felts under *any* Poseidon2-BabyBear commitment — both
   routes absorb ≈49,152 felts/ct. The bridge perms of
   `notes/cross-limb-binding.md` §3 are paid by both. What the Z_Q route removes is
   the bridge as **committed AIR columns + in-circuit range checks** (the
   decomposition lives only in the hash absorption and the opening recomputation);
   what it keeps is the decomposition at the opening boundary.
2. **The one-handle obligation** (§4 perimeter): leaves carry all 3 limbs, or three
   trees weld under one root (+1 compress per node level ≈ +2^{13}·(tree arity
   overhead) perms — small against 49,152-felt absorption). This is the structural
   binding; +0 probabilistic error.
3. **New machinery (build, not route — the PROVEN-IN-LEAN ≠ ROUTABLE law):**
   Z_Q transcript type, sampling-set challenge derivation (rejection-sample a
   36-bit index... no: draw uniform `n < min qᵢ` and diagonal-embed — 1 draw),
   `S = Z_Q[y]/(y⁴−c)` arithmetic, and a PCS opening for Z_Q-MLE claims. None of it
   exists in Rust today; grep confirms no Z_Q witness-gen anywhere.
4. **Soundness budget:** `v·d/2^144` (Ext4) for the reduction — 14 bits BETTER than
   the deployed BabyBear-Ext4 budget at the same `v·d`; the PCS opening error is
   whatever the chosen commitment adds, unchanged by this note.

**Versus the row-interleaving closure** (`notes/cross-limb-binding.md`'s
recommendation: Layout B + shared opening index, +0 felts beyond the bridge):

| | binding class | Hole A | Hole B | commit felts/ct | extra soundness error | new infra |
|---|---|---|---|---:|---|---|
| row-interleave + shared index | structural (layout discipline, checkable per-AIR) | closed | open | 49,152 | 0 | none (bridge deployed) |
| **Z_Q-native sumcheck** | **algebraic (unstatable at claim layer)** | **closed by construction** | **open — provably not closable inside Z_Q[X] (§5)** | 24,576 native (≈ same absorbed felts) | `vd/2^144` reduction error | transcript + S-arith + PCS opening |

Both close Hole A; neither closes Hole B (now a theorem, not a suspicion, for the
Z_Q side). The algebraic route is *stronger in kind* — the forgery is unstatable
rather than unopenable, and the property survives protocol composition without
re-auditing each AIR's layout — and *more expensive in kind*: it is a new proving
substrate, not a layout rule on the existing one. Basic-research verdict, no
product selection: the counts do not disqualify either; the discriminator is
whether a Z_Q-claim PCS gets built for other reasons (the single-prime route of
`FRONTIER-QUEUE.md` G1 dissolves both holes and this comparison with them).

---

## 7. Artifacts

* **`metatheory/Bfv/ZqSumcheck.lean`** (new, this lane) + one import line in
  `metatheory/Bfv.lean` rooting it in the `Bfv` defaultTarget.
  **Build: `lake build Bfv` GREEN**; the file's three `#assert_all_clean` blocks
  pin **22 keystones**, and `#assert_namespace_axioms Bfv` now pins
  **137 theorems kernel-clean** (was 113 after CrossLimb).
* This note.
* Selvage port: NOT performed (repo boundary + scope); §3 is the exact work order.

## 8. Lean theorem index (Bfv/ZqSumcheck.lean), all kernel-clean

**§1 Limb-locality** (the two-signed keystone):
`ringHom_eval_comm` (`f (p.eval x) = (p.map f).eval (f x)`) · `eval_fst` / `eval_snd`
(Prod) · `eval_pi` / `eval_pi_congr` (`Fin L` products: limb `i` of the output reads
only limb `i` of the input — for EVERY polynomial over the product ring).

**§2 Sampling-set Schwartz–Zippel + the ceiling**:
`agree_card_lt_of_proj` (the engine: one separating, `A`-injective coordinate into a
field bounds agreement in `A` by the degree — mathlib root counting, nothing new) ·
`exists_prod_map_ne` · `zq_agree_card_lt` (the product-of-two-fields statement) ·
`samplingSet_isUnit_iff` (the condition IS CCKP19's invertible differences) ·
`zq_fieldwide_sz_false` ⚑ (NEGATIVE CONTROL: field-wide SZ is FALSE over
`F₃ × F₅` — distinct degree-<2 polynomials agreeing on 5 > 2 points; the reason
the Selvage binder cannot be widened cosmetically) · `samplingSet_card_le` (ceiling
engine) · `deployed_sampling_ceiling` ⚑ (any sampling set of
`F_{q₀} × F_{q₁} × F_{q₂}` has card `≤ 0xffffc4001` — the 2³⁶ base ceiling as a
theorem about the deployed tower) · `zqSamplingA_sound` /
`zqSamplingA_attains_ceiling` (the diagonal attains it) · `zq_sz_fires` (the bound
fires on data: nonempty agreement set, card < 2 via the general theorem).

**§3 Hole A unstatable**:
`limbMulRel_one_iff_zmod` (one limb's integer congruence = one `ZMod` coordinate
equation) · `boundMul_iff_zqBound` ⚑ (CrossLimb's `BoundMul` at the exhibit basis
IFF the single ring statement `∃ ja jb, zq(out) = zq(pool ja)·zq(pool jb)` — the
`∃∀` shape is what a ring equation MEANS) · `zq_same_forgery_refused` ⚑ (the SAME
frankenstein that satisfies `exhibit_perLimb` is a false ring sentence — cited from
CrossLimb, not re-proved) · `zqBound_satisfiable` (house law, inherited through the
iff from `exhibit_bound_satisfiable`).

**§4 Hole B survives**:
`lift15` / `crtRescale` (the rescale as a well-defined FUNCTION of the ring element —
the true half of the brief's claim) · `crtRescale_computed` ·
`rescale_not_zq_polynomial` ⚑ (no polynomial over `F₃ × F₅` computes it — the false
half) · `mul_is_zq_polynomial` (satisfiable twin: the multiply is `X·X`).

**Build-hygiene note for the next lane**: `Field (ZMod p)` lives in
`Mathlib.Algebra.Field.ZMod` (NOT pulled in by `Mathlib.Data.ZMod.QuotientRing`),
and without it + `Fact (Nat.Prime p)` instances, instance search for
`Field (ZMod 3)` dies as a `whnf` HEARTBEAT TIMEOUT, not a clean synth failure —
it looks like a unification loop and is just a missing import.
