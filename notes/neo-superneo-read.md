# Neo & SuperNeo — read of eprint 2026/242

**Paper**: Wilson Nguyen, Srinath Setty (both Microsoft Research), *"Neo and SuperNeo:
Post-quantum folding with pay-per-bit costs over small fields"*, IACR ePrint 2026/242.

⚑ **VERSION MATTERS.** `~/Desktop/2026-242.pdf` is the **13 Aug 2026 revision, 59 pp**
(eprint says last-updated 2026-08-14). `~/paperbin/neo-superneo-pq-folding-small-fields-2026-242.pdf`
is the **12 Feb 2026 version, 60 pp**. The prior lane read the February one. Several
findings below turn on the difference. Both are on disk; new one archived as
`~/paperbin/neo-superneo-pq-folding-small-fields-2026-242-v2026-08.pdf`.

Affiliation changed between versions too: Feb listed Nguyen as "Stanford University,
New York University, and Microsoft Research"; Aug lists him as Microsoft Research.

---

## 0. The three prior-lane claims, settled

### (a) The 128× figure — **prior lane was RIGHT, and the authors have since fixed it**

This is the cleanest possible resolution: the slip was real, and the *August revision
corrects it to exactly the number the prior lane derived*.

| | February 2026 (p. ~173) | August 2026 (p. ~192) |
|---|---|---|
| ring element | `64 × 64 = 4,096 **bytes**` | `64 × 64 **bits** = 4,096 **bits**` |
| field element | `32 **bytes**` | `256 **bits**` |
| conclusion | **`128×` more data** | **`16×` more data** |

The February text was internally consistent but mis-unitted the ring element: a
LatticeFold ring element is 64 coefficients × 64 bits = 4,096 **bits** = 512 bytes, not
4,096 bytes. 512 B / 32 B = **16×**. The prior lane's arithmetic was correct to the digit.

**Verdict: the 128× figure is dead. The real figure is 16×, and it is now the
authors' own number.** Do not cite 128× from the February PDF; anyone quoting it is
quoting a retracted typo. The qualitative point survives — hashing ring elements in a
recursive verifier costs an order of magnitude more than hashing field elements — but
the magnitude was overstated 8×.

### (b) "No implementation section, no constraint count" — **CONFIRMED, and worse than stated**

Sections run 1–8 (Introduction, Technical overview, Overview, Preliminaries, Embeddings,
Interactive reductions, SuperNeo's folding scheme, Concrete parameters), then References,
Appendix A (*AI Disclaimer*), Appendix B (deferred proofs + two sage scripts). **There is
no implementation section, no evaluation section, no benchmark, and no table of measured
costs anywhere in the paper.**

Sharper: **the paper contains no constraint count for its own recursive verifier circuit.**
Every R1CS number in it is about somebody else's scheme —

- Nova / NeutronNova verifier circuit: `≈10,000 R1CS constraints`
- Arc: `2·λ/log(1/ρ)` Merkle openings → `≈1,600,000 R1CS constraints` at λ=128, ρ=1/2, Poseidon
- Lova: `≈3,000 s` prover for subset-sum at length 2^19, vs `500 ms` for Nova at the same size

— and Neo's own "LR: low recursion overheads" is a **✓ in Figure 1 plus an aspiration**:

> "Achieving constant verifier circuit size like Nova or NeutronNova in the lattice setting
> is difficult and **remains an open problem**. Our goal is to achieve logarithmic recursion
> overhead (with similar constants) analogous to HyperNova."

So the marquee property LR is *stated as a goal, checkmarked in the comparison table, and
never measured*. That is the same shape as things this repo calls out: the table column is
the claim, and nothing in the paper can make it go red.

⚠ The paper itself concedes the benchmark belongs to someone else. Of **Cyclo** (ePrint
2026/359, Garreta–Lipmaa–Luhaäär–Osadnik), a third-party reinterpretation the authors
say is "**equivalent to Neo**": its listed contributions are "(1) an alternative
presentation of Neo, (2) [the bounded-depth norm-check removal], and **(3) provide an
initial benchmark**." The only numbers for this construction are in a different group's paper.

**Consequence: Neo cannot be scored against our stack.** Not "was not scored" — *cannot*,
from this document. It is a design + security-proof paper.

### (c) "Competes with rather than composes with a ring-native hash" — **CONFIRMED, and the framing is now sharper**

Neo's whole thesis is *make the transcript field-native so the recursive verifier hashes
field elements*, which is the opposite lever from *make the hash ring-native so it can
absorb ring elements cheaply*. Neo removes ring elements from the sum-check and norm
check entirely so a stock field-native hash suffices. The two approaches are substitutes
attacking the same cost, and adopting Neo would make a ring-native hash **unnecessary**,
not complementary. Prior lane's read stands.

---

## 1. What Neo actually is

**A lattice analog of HyperNova.** Same recipe — commit to a CCS witness with a linearly
homomorphic commitment, run *one* sum-check, fold — with the Pedersen/KZG commitment
swapped for an **Ajtai commitment over a cyclotomic ring**, secure under **Module-SIS**.

- Setting: `R_F := F[X]/(φ(X))`, φ cyclotomic of degree `d`; commitment `c := A·z ∈ R_F^κ`
  for `A ∈ R_F^{κ×n}`, binding when `‖z‖_∞ < b`.
- Relation: **CCS** (generalizes R1CS, Plonkish, AIR).
- Base field `F = F_q` a small **prime** field; sum-check challenge field `K := F_{q^ν}`.
  For a 64-bit field a degree-2 extension gives 128-bit sum-check soundness.
- Both schemes support **multi-folding** (fold many CCS instances at once, amortizing
  the decomposition that controls norm growth).
- Compose with the standard folding→IVC/PCD compilers to get plausibly PQ IVC/PCD.

### The six desiderata (Figure 1)

PQ (post-quantum) · PB (pay-per-bit) · FN (field-native arithmetic) · CS (general,
non-SIMD constraint systems) · SF (small-field) · LR (low recursion overhead).

| Scheme | PQ | PB | FN | CS | SF | LR |
|---|---|---|---|---|---|---|
| HyperNova, NeutronNova | ✗ | ✓ | ✓ | ✓ | ✗ | ✓ |
| Arc | ✓ | ✗ | ✓ | ✓ | ✓ | ✗ |
| LatticeFold, LatticeFold+ | ✓ | ✗ | ✗ | ✗ | ✗ | ✗ |
| Lova | ✓ | ✗ | ✓ | ✗ | ✓ | ✗ |
| SALSAA | ✓ | ✗ | ✗ | ✗ | ✓ | ✗ |
| **Neo** | ✓ | ✓ | ✓ | ✗† | ✓ | ✓ |
| **SuperNeo** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

† Neo requires a SIMD constraint system; SuperNeo removes this.

⚠ This table is the paper's central claim and **five of its six columns are analytic
properties, while LR is the one that would need measurement.** LR is the unmeasured one.

### The actual technical contribution: two norm-preserving embeddings

The whole paper turns on one problem — *how do you put field vectors into the ring
vectors that Ajtai commitments operate on, while preserving norm bounds AND an
evaluation homomorphism?*

**Why NTT (LatticeFold's choice) fails all four of PB/FN/CS/LR at once.** The NTT is a
ring isomorphism `R_F ≅ (F_{q^τ})^{d/τ}`, so it makes ring ops simulate SIMD field ops.
But it is **not norm-preserving**, and that single fact cascades:
- norm of the ring vector doesn't track the norm of the field vectors ⇒ norm checks must
  become *ring* constraints ⇒ sum-check must run **over the ring** (kills FN, and ring
  mults are 10–100× field mults: `≈213 ns` vs "a fraction of a nanosecond" for M61);
- arbitrary-norm ring vectors must be decomposed for Ajtai binding ⇒ commitment cost is
  the same for 1-bit and 64-bit values (kills PB), and packing drops by another
  `log_b|F|` factor;
- peak packing needs `d/τ` *separate* field vectors in one ring vector ⇒ forces SIMD (kills CS);
- and the recursive verifier ends up hashing ring elements (kills LR).

**Neo embedding** — put the `d` field vectors *directly in the coefficient slots*:
`z := Σ_{j=1..d} z^(j)·X^{j-1}`, so `cf(z) ∈ F^{d×n}` has rows exactly `z^(1),…,z^(d)`.
Coefficient vectors *are* the field vectors ⇒ norm-preserving by construction ⇒ norm and
CCS constraints are both plain field constraints ⇒ **sum-check runs purely over the
field, zero ring operations.** Packing `d·n` field elements per length-`n` ring vector,
which is information-theoretically optimal — *but only for `d` separate vectors*, i.e. SIMD.

**Evaluation homomorphism (Theorem 1)** is the non-obvious part, and the August version
has a cleaner proof than the February one. Fold `z'' := z + δ·z'` for low-norm `δ ∈ R_F`;
then the underlying field vectors' evaluations combine as `y'' := y + δ·y'` under
`Emb_K`. February proved it via rotation/circulant matrices (`rot(δ)`, ring mult as a
linear map over the field). August replaces that with a much simpler argument: identify
`F ⊆ K` and `R_F ⊆ R_K = K[X]/(φ(X))`, at which point evaluations and linear combinations
are all linear maps over the *same* ring `R_K` and the homomorphism "follows almost
immediately from this linearity." Same theorem, better proof.

The authors note this embedding has been picked up by follow-ups (LatticeFold+, Symphony,
Hachi) under the names **"tensor of rings"** and **"ring switching"**, and that
LatticeFold+'s authors acknowledge adapting the field-native sum-check and the folding
evaluation homomorphism *from Neo*. So the embedding is the durable contribution and it
has already diffused.

**SuperNeo embedding** — the fix for SIMD. Instead of `d` vectors across coefficient
slots, take **one** field vector `z ∈ F^{d·n}`, chop it into `n` blocks of length `d`,
and pack each block into one ring element: `Pack_F(z) := [z̄_1,…,z̄_n]`. Optimal packing
`d·n` for a *single* vector ⇒ **no SIMD requirement**.

Making evaluations work needs an extra gadget: a linear transform `Trans_F : F^d → F^d`
with `ct(Emb_F(Trans_F(a)) · Emb_F(b)) = ⟨a,b⟩` — "a product over the ring simulates an
inner product over the field," reading the answer off the **constant term**. Extend
blockwise to vectors and rowwise to matrices and you get `ct(M̄_j z̄) = M_j z`, then
`ct((M̄_j z̄)~(r)) = (M_j z)~(r)`. Theorems 9, 10, 11 (the last: folding packed vectors
with scalars in `R_F` preserves the identities).

**SuperNeo's extra property**, and it is the one worth noting for anyone building on it:
it natively folds CCS over an **arbitrary extension field `L` of the commitment field
`F`**, with `L` *not* tied to the NTT splitting of the cyclotomic ring — the relation
field and the sum-check challenge field may differ and are embedded into a common ambient
field `A`. The paper claims no prior lattice folding scheme does this.

### What "pay-per-bit" means concretely (§2.3, and this is the mechanically interesting bit)

Not an abstraction — a statement about how you actually multiply. Committing is a ring
matrix-vector product `A·z`. For `a ∈ R_F`, ring multiplication is a rotation-matrix
product:

```
cf(a·b) = rot(a)·cf(b) = Σ_{i=1..d} b_i · rot(a)_i
```

where `rot(a)_i := cf(a·X^{i-1} mod φ(X))`. With `d ≤ 64` and `⌈log₂|F|⌉ ≤ 64` this is
the fastest implementation (AVX-512). **The dominating cost is the scaling `b_i · rot(a)_i`,
which scales linearly with the norm of `b_i`.** When the `b_i` are bits, the ring
operation degenerates into *adding the rotations where `b_i ≠ 0`* — no multiplies. That
is pay-per-bit, and it falls out of the coefficient embedding for free, because the
coefficients are the witness values.

Nice corollary the paper makes explicit: because security forbids a fully-splitting
cyclotomic (`R_F ≇ F^d`), NTT-based multiplication is *worse* here than scaled rotations —
more memory-intensive, less cache-friendly, and needing degree-4 extension mults
(16 `F_{q^4}` mults) where degree 4 is required for a non-trivial low-norm invertibility bound.

### Interactive reductions (§2.4, §6) — the framework contribution

The security-proof half. Lattice protocols split into `Π_property` (a sound test —
sum-check, random projection — producing algebraic claims) then `Π_special` (a
special-sound protocol taking random linear combinations). Neither stage individually
meets the definition of a **reduction of knowledge**, so the literature proves these
protocols monolithically with "complex, non-blackbox security arguments." Neo introduces
**strong/weak interactive reductions**, generalizing RoK so the stages compose and
`Π := Π_special ∘ Π_property` gets a modular knowledge-soundness proof
(Composition Theorem 12, proof in B.1).

SuperNeo's folding scheme is then assembled as three composed reductions:
`Π_CCS` (§7.3) → `Π_RLC` random linear combination (§7.4) → `Π_DEC` decomposition (§7.5,
Theorem 13). `Π_DEC : CE(B,L) → CE(b,L)^k` is the norm-control step: signed base-`b`
decomposition of the flattened witness from norm `B = b^k` down to `b`, so folding can
continue **without norm growth**. This is the mechanism that matters for depth — see §4.

### Concrete parameters (§8) — the only numbers in the paper

All three parameterizations set `τ = 1` (so `L = F`), `K := F_{q²}`, `A := K`, `b = 2`,
and land at **MSIS ≈ 129 bits of security**, estimated with the lattice-estimator
(sage scripts in B.5/B.6).

| | **Almost Goldilocks** | **Goldilocks** | **Mersenne-61** |
|---|---|---|---|
| `q` | `(2⁶⁴−2³²+1) − 32` | `2⁶⁴−2³²+1` | `2⁶¹−1` |
| `φ(X)` | `X⁶⁴ + 1` | `X⁵⁴ + X²⁷ + 1` | `X⁵⁴ + X²⁷ + 1` |
| `d` | 64 | 54 | 54 |
| `η` | 128 | 81 | 81 |
| `κ` | 15 | 18 | 18 |
| `m` | `2³³` | `2³⁰` | `2²⁸` |
| `n_R` | `2²⁷` | 19,884,107 | 4,971,026 |
| `k`, `K` | 13, [50] | 14, [61] | 14, [61] |
| `B` | `2¹³` | `2¹⁴` | `2¹⁴` |
| challenge set `C` coeffs | `[−1,0,1,2]` | `[−2..2]` | `[−2..2]` |
| `T` (Thm 5) | 128 | 216 | 216 |
| `b_inv` (Thm 4) | ≈ 4 | ≈ 2.5·10⁹ | ≈ 383 |
| `\|C\|` | `2¹²⁸` | `≈2¹²⁵` | `≈2¹²⁵` |
| `\|K\|` | `2¹²⁸` | `2¹²⁸` | `2¹²²` |
| **MSIS security** | **≈129 bits** | **≈129 bits** | **≈129 bits** |

*Almost Goldilocks* is a new field the paper introduces: `(2⁶⁴−2³²+1) − 32`, close enough
to Goldilocks to reuse the Solinas reduction with a small change, and it is the only one
of the three admitting the power-of-two cyclotomic `X⁶⁴+1` with `d=64` matching the field
bit-width exactly.

⚑ Note what these are: **MSIS hardness estimates and parameter feasibility checks.**
They are not prover times, not proof sizes, not verifier circuit sizes. There is nothing
here to compare against a measured stack.

Two "Incompatibility with LatticeFold" remarks worth carrying: for **Goldilocks**, high
2-adicity fully splits any `X^d+1`, so `R_F ≅ F_{q^d}` and LatticeFold's security drops to
the 64-bit NTT-representation field; for **M61**, no power-of-two cyclotomic satisfies
Theorem 4 at all, so LatticeFold's parameters can't even be shown secure. Neo's use of
`X⁵⁴+X²⁷+1` (a non-power-of-two cyclotomic) is what buys both.

---

## 2. ⚑ The BinarySpartan question — **the premise is false**

The brief's Q2 was the one "worth the lane": does Neo compose with BinarySpartan, giving
Setty a full stack? **There is no BinarySpartan.** Checked five independent ways:

1. **IACR ePrint full-text search for "BinarySpartan"** → *no results*.
2. **ePrint author search, Setty, 2026** → **exactly one paper: 2026/242, this one.**
3. **`~/dev/gh/forks/IACR-eprint-mirror/2026/`**, complete through `1053.pdf` (fresh to
   14 Aug 2026): extracted first pages of all **810** papers numbered ≥ 242 and grepped.
   Hits for "Srinath Setty": **{242}**. For "Wilson Nguyen": **{242}**. For
   "BinarySpartan"/"Binary Spartan": **∅**.
4. **GitHub repository search for "BinarySpartan"** → *no repositories found*.
5. **Setty's Microsoft Research publication page**, 2026 entries: *Nebula: Proving Machine
   Executions via Folding Schemes* (with Arasu Arun) and *Vega: Low-Latency Zero-Knowledge
   Proofs over Existing Credentials* (with Darya Kaviani). Neither is about binary fields.
   `microsoft/Spartan2` on GitHub now hosts the **Vega** prover — SHA-256 circuits,
   ≈92 ms proving, 108 KB proofs, 23 ms verification — with **no** mention of binary
   fields, Neo, or folding.

**Where the name probably came from**: the **Binius64 blueprint spec**
(`~/paperbin/binius64-blueprint-spec.txt`) has a section literally titled
**"1.2 Why Not Binary Spartan?"**. That is Irreducible's document, not Setty's, and
"Binary Spartan" there is a *rejected strawman*, not a system — it argues that adapting
Spartan to `F₂` "founders on the wiring check," because an R1CS over `n` witness bits has
`A,B,C` with `O(n)` nonzeros and the prover's partial evaluation costs `O(n)`
multiplications against large-challenge-field elements. The one place this phrase exists
in our corpus is a section explaining **why not to build it**.

### Answering the underlying question anyway: would Neo compose with a binary-field Spartan?

Directly checkable and the answer is unambiguous. **The word "binary field" does not
appear in Neo. Neither does "characteristic 2", "Binius", or `GF(2)` — zero occurrences
in 3,667 lines.** The paper is prime-field-only by construction, at three levels:

- **Small-field support is defined as prime**: "The scheme should work natively over
  small **prime** fields"; "fields whose modulus `q` fits within a machine register."
  All three parameterizations are prime (`2⁶⁴−2³²+1`, that minus 32, `2⁶¹−1`).
- **The security argument is arithmetic in `q`.** Challenge-set size, the low-norm
  invertibility bound `b_inv := 1/τ(z)·q^{1/φ(z)}` (Theorem 4), the strong-sampling-set
  condition `q ≡ 1 (mod z)` with `ord_η(q) = η/z`, and the MSIS estimate all take `q` as
  a large prime modulus. None of it transfers to `F_{2^k}`.
- **Pay-per-bit is a statement about norms**, and norm is what a characteristic-2 field
  does not have. `‖z‖_∞ < b`, signed base-`b` decomposition, the `Π_DEC` norm reduction,
  and "the dominating cost scales linearly with the norm of `b_i`" are all
  integer-magnitude facts about lifting `F_q` residues to `ℤ`. In `F_{2^k}` every element
  has the same "size"; there is no short vector, so **Ajtai/MSIS has nothing to bind and
  pay-per-bit has nothing to pay for.**

**Verdict on Q2: Neo's small-field/pay-per-bit story does not merely "not require"
binary fields — it is structurally incompatible with them.** The lever is the norm of a
lattice vector, and binary fields have no norm. So there is no Setty full stack to
discover: the artifact does not exist, and had it existed as a binary-field Spartan, Neo
could not have been its folding layer.

The composition Neo *does* advertise is the opposite one, and it is prime-field-native:
because Neo targets SNARK-friendly fields like Goldilocks, an IVC proof can be compressed
with **Spartan + a FRI-based PCS** "without requiring any non-native arithmetic or field
emulation." That is the real Setty-stack claim in the paper, it is one sentence long, and
it is unimplemented and unmeasured like the rest.

---

## 3. Recursion accounting: Neo's vs our measured wrap identity

**Our measurement, verified at source** (not inherited from the brief). Commit
`1ba443bdd` *"profile: measure the recursion tower — a wrap commits its child's VERIFIER
as trace"*:

> the deployed rotated transfer child's NATIVE verify costs **38,168** Poseidon2
> permutations; the leaf wrap's IN-CIRCUIT `poseidon2_perm/baby_bear_d4_w16` op count is
> **38,168**. Identical to the unit. A wrap's biggest table IS its child's verifier, row
> for row — so "verifier ×2.28" is a PROVE price, paid one layer up.

Measured twice, by instruments with no shared code path. Same commit also records the
denominators, which matter below: in-circuit Poseidon2 is **36.45%** of a leaf wrap's
committed cells and **53.98%** of the apex/shrink layer's — *"Not ~75% at any denominator."*

### Does Neo's accounting agree with ours?

**Yes, in kind — and Neo is measuring the same physical resource we are, one abstraction
level up.** Neo's unit is *bytes the recursive verifier must hash*; ours is *Poseidon2
permutations*, which is what "hashing that many bytes" costs once you name the sponge.
Neo's entire LR argument is our identity restated as a design principle: the recursive
verifier's cost **is** the child's transcript, so whatever the child emits, the parent
pays for absorbing. Neo derives from that the conclusion that a scheme should minimize
*what kind of object* lands in the transcript (field elements, not ring elements). We
derived from it that the wrap's biggest table is the child's verifier row for row. Same
identity, read in two directions.

Where Neo goes **further than we can currently check**: it claims the identity holds *per
scheme family*, and prices Arc — the row our deployed stack occupies — at
`2·λ/log(1/ρ)` Merkle openings ⇒ **≈1,600,000 R1CS constraints** (λ=128, ρ=1/2, Poseidon).
That is a *derived* figure from a query count, not a measured one, and it is the shape of
number our tower work produces natively. It is worth reproducing against our own
parameters, because our stack is precisely the thing that number describes.

⚠ Where our measurement **calibrates Neo's rhetoric downward**: Neo's framing implies
recursion hashing is the overwhelming cost. Our numbers say it is a **plurality, not a
supermajority** — 36.45% at the leaf wrap, 53.98% at apex. So the *ceiling* on Neo's
entire LR pitch, applied to our stack, is ≈1.6× committed cells at the leaf and ≈2.2× at
apex, and that is the limit reached only by driving in-circuit hashing to **zero**. A
real lattice folding verifier is not free. **Neo's LR win, priced against our own measured
denominators rather than its rhetoric, is bounded by ~2×.** That is worth having and it is
not a step change.

### Does Neo's fix apply to our hash-based prime-field stack?

**No — not as an optimization. It is a substrate replacement, and it lands off our field.**

Three obstructions, in increasing order of how much they cost to clear:

1. **The fix is "stop being hash-based."** Neo's LR does not come from a cheaper hash or
   a smaller transcript within a FRI/Merkle stack. It comes from replacing the commitment
   scheme entirely: Ajtai/MSIS commitments are **linearly homomorphic**, so the folding
   verifier's work is checking linear recombinations (`c = Σ_{i∈[k]} b^{i-1}·c_i`, and the
   matching checks on `y` and each `y_j` in `Π_DEC`) — it opens **no Merkle paths at all**.
   Our stack is literally the Arc row of Figure 1: hash-based, ✗ on PB, ✗ on LR. Neo's
   answer to that row is not a patch to it.

2. **Our field is smaller than anything Neo parameterizes.** We run **BabyBear**
   (`2³¹−2²⁷+1`, `baby_bear_d4_w16`). **Neo contains zero occurrences of "BabyBear",
   "M31", or "31-bit".** Its three worked parameterizations are 61–64 bit
   (Almost-Goldilocks, Goldilocks, M61), and its constructions lean on `d = 54` or `64`
   with `q` large enough for MSIS at `κ ∈ {15,18}`. Whether BabyBear admits a secure
   instantiation at all is **not addressed by the paper**, and it is not a formality —
   `q` enters the low-norm invertibility bound `b_inv` (Thm 4), the strong-sampling-set
   condition, the challenge-set size `|C|`, and the MSIS estimate.
   ✅ **Actionable**: the paper ships the sage scripts (Appendix B.5 hardness/inversion,
   B.6 lattice-estimator). Re-running B.6 with `q = BabyBear` and a candidate `(κ, d, φ)`
   is a cheap, self-contained spike that would settle it — and it is the single highest-
   value thing to take from this paper.

3. **Anything built on it is unmeasured.** See §0(b): no implementation, no verifier
   circuit size, no prover time. We would be porting to a scheme whose headline property
   has never been observed. Given how much of this repo's ledger is "the table column was
   the claim," that is the relevant risk, not the cryptography.

**Bottom line for Q3**: Neo's accounting agrees with ours and independently corroborates
the wrap identity as a *general* fact about recursion, not an artifact of our tower. Its
*fix* does not apply — it is a different substrate, off our field, and unimplemented.
The transferable asset is the sage script and the diagnosis, not the scheme.

---

## 4. Accumulation depth: where Neo sits

### Neo's own depth story is a norm-budget story, and it is depth-*independent* by construction

Lattice folding has a depth problem group-based folding does not: **the witness norm grows
with every fold**, and Ajtai binding only holds while `‖z‖_∞ < b`. Neo's answer is
`Π_DEC` (§7.5, Theorem 13), `CE(B,L) → CE(b,L)^k`: signed base-`b` decomposition drops the
flattened witness norm from `B = b^k` back to `b` **every round**, so folding continues
"without increasing the norms." Depth is therefore *not* a soundness parameter for Neo —
it is paid for with a `k`-way decomposition (and `k`-fold commitment/evaluation work) at
every single step. Multi-folding exists precisely to amortize that.

**Cyclo (2026/359) trades exactly this axis for depth-boundedness**, and it is the
interesting data point for our accumulation work. Its design "eliminates the need for norm
checks on the accumulator by adopting an amortized norm-refreshing design, ensuring that
the witness norm grows **additively** per round within a (generously) bounded number of
folds," and "does not decompose any witnesses into low-norm chunks within the folding
protocol itself." Neo's own summary of Cyclo's contribution (2): *if soundness is only
required for an explicit bounded number of steps, the norm check on the accumulator can
be removed for efficiency.* SuperNeo is stated to be compatible with this.

⚑ **That is a depth-for-cost exchange rate stated in the open, and it is the same shape as
our accumulation-depth composition.** "Additive norm growth per round, valid to depth D"
is a budget one can state, bound, and prove a corner of. If we want a lattice-side
analogue of our depth composition, **Cyclo's Remark 1 / §392 is the object to formalize,
not Neo's `Π_DEC`** — `Π_DEC` makes depth vanish by paying every round, which is exactly
the design that has nothing to say about depth.

⚠ Cyclo's benchmark, the one Neo defers to, is narrower than "a benchmark" implies: it
compares **commitment computation only** ("the most expensive part of the folding scheme,
so the benchmark gives a good indication of concrete efficiency") against LatticeFold+'s
double-commit, using HEXL/AVX-512 with a modulus `q ≈ 2⁵⁰` and a near-split ring chosen
for vectorization — *not* Goldilocks or M61, and admittedly "towards our performance
disadvantage." So even the one benchmark for this construction is a microbenchmark
outside Neo's own parameter regime. **There is still no end-to-end folding or IVC
measurement for Neo anywhere.**

### Where Neo sits relative to Paneth–Pass (2026/662)

Read it. *"Verifiable Divide-and-Conquer: Proof-Merging Beyond the log n-Barrier"*,
Omer Paneth & Rafael Pass (Tel Aviv / Cornell Tech & Technion), 5 April 2026.

The barrier it names is ours: *"recursive invocations of the extractor grow exponentially
with the depth of the merge tree. As a result, the merged proofs are only conjectured to
be sound for constant-depth [trees]... only extends to trees of depth `O(log λ)`."*
Its result (Theorem 1.1, formal Theorem 4.6): assuming **LWE**, a mergeable SNARG
supporting an **unbounded polynomial** number of recursive merges, with merged proof length

```
max_i |Π_i| + |(x_1,…,x_k)| · poly(λ)
```

— i.e. **linear in merge-tree depth, independent of tree size**; and if the per-step
merged instances are `poly(λ)`-bounded, it simplifies to `max_i|Π_i| + poly(λ)`.
Theorem 4.6 builds it from **rate-1 functional BARGs with strong somewhere extraction**.

**Two scope limits that decide the comparison, and they are load-bearing:**

- It is a SNARG for **P** — *deterministic* languages. The paper is explicit that
  SNARK-for-**NP** constructions with explicit knowledge extractors "face strong
  barriers [BCPR16]" and that security "is heuristic and can only be analyzed in
  idealized models." Paneth–Pass escapes the depth barrier **by giving up knowledge
  soundness over NP**, not by beating it there.
- Soundness requires **tree-bounded instance mergers**, which "may exclude merge
  strategies that follow general directed acyclic graphs (DAGs) rather than trees" —
  and the authors say this restriction "appears to be necessary even in very strong
  idealized models that allow straight-line extraction with only additive overhead."

**So, where does Neo sit? It does not sit on this axis at all.** Neo is a folding scheme;
IVC/PCD comes from "applying standard compilers [56,58,86]" — i.e. the heuristic
random-oracle route, with exactly the extractor-blowup depth story Paneth–Pass is written
to escape. **Neo never engages with it.** Its only depth remarks are *about other people*:
that Bünz et al. [25] "only provides 'bounded depth' IVC", and Cyclo's bounded-step
optimization. Neo's knowledge-soundness work (the interactive-reductions framework,
strong vs. weak reductions, Composition Theorem 12) is entirely about composing the
**three reductions within one folding step** — `Π_DEC ∘ Π_RLC ∘ Π_CCS` — not about
composing steps across depth. Notably, `Π_RLC` is *not* knowledge sound for its input
relation and is only a **weak** interactive reduction extracting a **relaxed** witness;
the framework exists to make that compose once, per step.

**Verdict for Q4, three parts:**

1. **Neo does not reset the accumulation-depth bar and does not claim to.** Nothing in it
   competes with our machine-checked accumulation-depth composition, and nothing in it is
   invalidated by it. Different axis entirely: Neo optimizes the per-step object, we bound
   the across-step degradation.
2. **Paneth–Pass genuinely resets a bar, but a neighbouring one.** Depth-linear,
   size-independent, from LWE, unbounded merges — but for **P**, not NP, and trees, not
   DAGs. Our composition lives in the knowledge-soundness/NP world it explicitly steps
   out of, so it is not superseded. It *is* the right thing to position against, and the
   honest framing is "they removed the barrier by removing extraction; we bound it while
   keeping extraction." The DAG exclusion is also worth checking against our own merge
   topology — if ours is a DAG, their result would not cover it even in the P case.
3. **The one thing here that touches our depth work directly is Cyclo's additive
   norm-growth budget**, not Neo. That is a stateable, bounded, refutable depth budget of
   the kind our composition is built to hold — and per this repo's floor discipline, a
   depth budget that is satisfiable, refutable, and not provable is exactly the shape
   worth formalizing.

---

## 5. Summary — what to do with this

**What Neo is**: a genuinely good, genuinely unmeasured paper. The embeddings are the real
contribution and have already diffused into LatticeFold+, Symphony, and Hachi under other
names ("tensor of rings", "ring switching"), with LatticeFold+'s authors crediting Neo for
the field-native sum-check and the folding evaluation homomorphism. The interactive-
reductions framework is a clean fix to a real methodological problem in lattice proofs.
The parameters are worked and the sage scripts ship.

**What it is not**: an implemented system, a measured system, or a scorable one. Six
desiderata, five analytic, and **the one that would need measuring (LR) is checkmarked and
never measured** — its status in the text is "our goal", with the strong form conceded as
"remains an open problem."

**The four answers, compactly:**

| Question | Answer |
|---|---|
| **128× figure** | **Prior lane was right; authors fixed it.** Feb said `bytes`, Aug says `bits`; `128×` → **`16×`**. Dead figure — never cite it. |
| **No impl / no constraint count** | **Confirmed, and stronger**: no implementation section, no evaluation, and **no constraint count for its own recursive verifier**. Benchmark deferred to Cyclo (2026/359), which turns out to be a commitment-only microbenchmark at `q≈2⁵⁰`, outside Neo's parameter regime. |
| **Composes or competes with BinarySpartan** | **The premise is false — BinarySpartan does not exist.** ePrint search ∅, ePrint-author-search Setty 2026 = {242} only, 810 mirror papers ≥242 grepped = {242} only, GitHub ∅, MSR page lists Nebula & Vega. The name traces to Irreducible's Binius64 blueprint §1.2 *"Why Not Binary Spartan?"* — a **rejected strawman**, not a system. And Neo could not have been its folding layer regardless: **zero mentions of binary fields**, and pay-per-bit is a statement about lattice *norms*, which characteristic-2 fields do not have. |
| **Recursion accounting vs our wrap identity** | **Agrees in kind and corroborates it** — Neo's "the verifier hashes the child's transcript" is our 38,168≡38,168 identity read as design pressure. **Its fix does not apply**: substrate replacement (hash-based→Ajtai/MSIS), and off our field (no 31-bit/BabyBear parameterization anywhere). Our own denominators cap the whole LR pitch at **~1.6–2.2×**, not a step change. |

**Highest-value follow-up, one item**: run Appendix B.6's lattice-estimator script with
`q = BabyBear` and a candidate `(κ, d, φ)` to find out whether Neo's construction is even
instantiable at our field width. The paper does not say, its three worked examples are all
61–64 bit, and the script is on disk. That is a bounded spike that either opens the door
or closes it cleanly.

**Second**: Cyclo's additive norm-growth-to-bounded-depth design (2026/359) is the lattice
object closest to our accumulation-depth composition. Worth a read of its Remark 1 in its
own right — Neo only summarizes it.

**Do not**: treat Neo as portable to the deployed stack, or cite any LR number from it.
There are none.

### Artifacts

- `~/paperbin/neo-superneo-pq-folding-small-fields-2026-242-v2026-08.pdf` (+`.txt`) — the
  **Aug 2026 revision**, the current one.
- `~/paperbin/neo-superneo-pq-folding-small-fields-2026-242.pdf` (+`.txt`) — Feb 2026,
  **retained deliberately** as the version carrying the retracted `128×`.
- `~/paperbin/cyclo-lattice-folding-2026-359.pdf` (+`.txt` extracted this pass) — Cyclo.
- `~/paperbin/paneth-pass-verifiable-divide-conquer-mergeable-snarg-2026-662.pdf` (+`.txt`).
