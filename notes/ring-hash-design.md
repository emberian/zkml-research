# Ring-hash candidate: the design note

2026-08-13. **Written incrementally by the revival lane.** The predecessor design
lane died on credits after writing three scripts and no prose. This file is the
prose. Every number below was produced by **re-running the scripts in this
session**; the run outputs are quoted, not remembered.

> ⚑ **BUILD IT — delegation is dead** (§5.2, and `ring-hash-build-verdict.md`).
> Delegation pays only when the hash is expensive *in-circuit*; Poseidon-over-R_q
> is 856 constraints per permutation, so **2026/1127's bill is transcript VOLUME
> and delegation attacks UNIT COST.** At the benchmarked config the gadget-Feistel
> takes Fiat–Shamir from **52.0% of the circuit to 4.0%**, and at 4% there is
> nothing left for an architectural escape to remove.
>
> ⚠ **But do NOT commit to τ=4** (§4.5, revised). An earlier draft of this note
> recommended τ=4 at moderate-to-high confidence; **that was written before
> §4.4b and is withdrawn.** Integral properties in characteristic p survive to
> round **20** at a degree-4 extension against round **1** at a prime field, and
> the effect is monotone in extension degree. **τ=2 is now the leading
> candidate**, provisionally, and one named experiment settles it.

**Still open** (named, not hidden): **τ itself** — run the Beyne–Verbauwhede
`SPN.ipynb` at our parameters (§4.5); the round-count derivation, owed in *every*
τ regime (§4.4); and the Feistel's two structural assumptions (§3, §5.0b).

**Scripts.** They lived only in `~/src/ring-ro-hash/`, **which is not a git
repo** — the exact way the predecessor's work nearly vanished. Now versioned at
`notes/ring-hash-scripts/`. All run in seconds to a minute on a laptop.

| script | what it settles | runtime |
|---|---|---|
| `design_branch_frontier.py` | *(recovered)* branch numbers, exact; the τ=4 closure | 6.8s |
| `design_mds_interleave.py` | *(recovered)* schedule/cost table for σ-density | 3.4s |
| `design_gadget_feistel.py` | *(recovered)* the second candidate, full-scale | 58.2s |
| `design_branch_law_check.py` | **(new)** extends the t+\|K\| law past t=2 | 45s |
| `design_tau_tradeoff.py` | **(new)** prices the fork; C1 at τ>1; joint modulus | ~30s |
| `design_subfield_invariance.py` | **(new)** the τ=4 invariant subfield, and C6 | 2s |
| `costmodel.py` | the 716.8 rows/elt baseline (2026/1127 App C.3) | — |
| `sigma_poseidon.py` | the C1–C5 design conditions + validator | — |
| `density_repricing.py` | why support-3, not support-1 (Chaghri); **superseded on cost by §2.0** | — |

Prior context: `two-rocks.md` §Rock 2 (the survey and the enabling theorem),
`ring-hash-cryptanalysis.md` (the attack-side verdict this note answers).

---

## 0. What this note settles

| question | answer | § |
|---|---|---|
| the recorded **#1 weakness** (branch ≤9 vs MDS 65) | **CLOSED at τ>1** — 2 rows/elt/round reach slot-MDS at τ=4, 4 rows at τ=2 | §1.2 |
| the composite branch law | **t + \|K\|**, not the naive t·\|K\|+1 — refuted by construction at every t tested | §1.4–1.5 |
| the σ price | **HALVED**: ⌈(s−1)/2⌉, not s−1 — Definition 9 verified to carry two automorphism channels | §2.0 |
| best σ-Poseidon point | slot-MDS in full rounds: **143.8/elt (5.0×)** τ=1 · **107.8 (6.7×)** τ=2 · **89.8 (8.0×)** τ=4 | §2.1, §4.1 |
| second candidate | **gadget-Feistel, 27.4 rows/elt (26×)** — higher ceiling, much less mature, 3 hard caveats | §3 |
| ⚑ **the τ fork** | ⚠ **UNSETTLED. τ=1 eliminated; τ=2 leading, provisionally; τ=4 withdrawn.** One named experiment settles it | §4.4b–4.5 |
| **delegate instead of building?** | ⚑ **BUILD IT** — delegation attacks unit cost, our bill is volume; it loses by 3–31× | §5.2 |
| why σ-Poseidon can't reach the packing ceiling | the **S-box floor is 15.3×** ≈ the 16× ceiling; every σ row is given back below it | §5.0b |

**Three things this lane found that were nobody's recorded position:**

1. ⚑ **τ is the exponent of the folding scheme's challenge space** (‖strong
   sampling set‖ = q^τ), and 2026/1127 says *"we may choose τ to obtain
   exponentially-sized strong sampling sets."* **τ=1 collapses it to q = 2^64.**
   The τ=1 preference was asking the host protocol to give up its challenge
   space — a systems cost, not a hash-side tradeoff. **This eliminates τ=1** (it
   does not, as an earlier draft said, decide the whole fork).
2. **C1 (`gcd(α, q^τ−1) = 1`) is twice as constraining at τ=4**, and it makes the
   two candidates want *incompatible* moduli — but a joint modulus exists at
   **2^64 − 279**, found in seconds. No tradeoff is forced.
3. **σ-Poseidon is bounded by its own S-box, not by τ.** The S-box floor is
   **15.3×**, essentially the 16× packing ceiling — so an S-box design *starts*
   at the ceiling and every σ row spent on branch number is given back below it.
   **τ decides whether you land at 8.0× or 5.0×, not whether you can exceed
   15.3×.** The Feistel is not bounded by it at all, because the bound *is* the
   S-box and it has none.

⚠ **And one thing this lane got wrong and then caught**: §4.5's first draft
recommended τ=4 on the strength of the two effects it had measured. A third,
unmeasured, monotone effect (§4.4b) falsified it. **The reversal is recorded in
place rather than edited away** — see §4.5's opening.

---

## 1. The branch-number weakness is CLOSED at τ=4

`ring-hash-cryptanalysis.md` §1 prices the branch deficit as the design's **#1
weakness**: branch ≤9 against an MDS 65, "~7.2× weaker", independent of d. That
pricing is correct **at τ=1** and **for the support-3 layer**. It is not a
property of the design.

### 1.1 What τ is, and why it moves the answer

τ is the degree of the irreducible factors of X^d+1 mod q. The deployed Frog ring
of 2026/1127 has d=16, τ=4: X^16+1 splits into **four quartics**, so there are
ℓ = d/τ = **4 slots**, each a copy of F_{q^4}. At τ=1 (q ≡ 1 mod 32) there are 16
slots, each F_q.

The σ-layer's job is to mix slots. **Slot-MDS means branch ℓ+1.** At τ=1 that is
17 and needs the full dense layer; at τ=4 it is **5**, and the slot-permutation
group has order 4 — so a layer supported on the whole group is small.

### 1.2 Measured (`design_branch_frontier.py` Part D)

Model: p=89 (chosen because ord_32(89) = 4 = τ, reproducing the Frog splitting
structure at a toy size), ℓ=4 slots over F_{p^4}, branch computed exactly by
enumerating support pairs with ranks over F_{p^4} taken via the blown-up regular
representation.

```
  {1,5,-1}   (1 row)              slot-support 3   branch = 4  (max 5)
  {1,5,-1,-5} = G/<q> (2 rows)    slot-support 4   branch = 5  (max 5)   SLOT-MDS
```

**The automorphism set {1, 5, −1, −5} at 2 rows per element per round reaches
branch 5 = slot-MDS.** That is **one extra row** over the support-3 layer the
prior lane costed (which reaches branch 4). The #1 weakness closes for +1
row/element/round — *provided* we go to τ=4, which is a real cost, adjudicated in
§4.

⚠ **Caveat carried from the script, do not drop it.** The Part-D model omits the
Frobenius twist that σ_k carries into the moved slot at τ>1. The script's stated
justification: a twist is a fixed invertible F_p-block, and composed with the
generic multiplication block D it is again a generic invertible block on the same
support pattern, so it cannot change a rank statistic. That argument is sound for
*these* measurements (which are all ranks of support submatrices) and is NOT
sound for anything that depends on the twist's field-theoretic content — which
is exactly where the extension-field risk of §4 lives. The branch measurement is
clean; do not reuse the "twist doesn't matter" line outside it.

### 1.3 The τ=1 picture, exactly (Parts A and C)

At d=8 (exact enumeration to full weight), both q=257 and q=65537:

```
  layer                                 cost  support  branch   law |K|+1
  Sigma {1,5,-1}              (1 row)      1        3       4   MATCHES
  Sigma {1,5,25,-1,-5}       (2 rows)      2        5       6   MATCHES
  Sigma G (dense, generic)   (4 rows)      4        8   8@q=257 / 9@q=65537
  Sigma G, CAUCHY-programmed (4 rows)      4        8       9   MATCHES (both q)
  Prod (I+c1 s5)(I+c2 s-1)   (2 rows)      2        4       5   MATCHES
  Prod ... 3 factors         (3 rows)      3        6       6   6 vs law 7
  Prod ... 4 factors         (4 rows)      4        8       6   6 vs law 9
```

Three things fall out, and two of them are design decisions:

1. **branch(Σ-layer) = |K| + 1 exactly**, for generic coefficients. Certified
   exactly to weight 5 at d=16 (Part C: 229,056 support pairs checked, no
   singular pair), with the upper bound |K|+1 constructive (one active slot
   activates exactly |K| outputs). So at d=16 the 4-row layer's branch is in
   [6,10] with law 10 — the law is not fully certified at proposal size, and
   saying "branch 10 at d=16" would be overclaiming.
2. **Program the dense layer as a Cauchy matrix, don't sample it.** The generic
   dense layer misses MDS at q=257 (branch 8, not 9) — that is birthday, not
   structure (~50 expected singular square submatrices at q=257, ~0.2 at
   q=65537, ~2^-34 at q~2^64). But the σ-basis has d² free coefficients, so the
   slot matrix can be *chosen*: M[i][j] = 1/(x_i+y_j) is MDS at every q by
   theorem, every Cauchy minor being nonzero. **This removes the genericity
   caveat entirely and costs nothing.** Do this.
3. **The product form Π(I + c_i σ_{k_i}) is strictly dominated.** At 4 rows it
   reaches branch 6 against a support law of 9, at *both* moduli — so the
   correlated coefficients are structurally deficient, not birthday-deficient.
   Equal cost, worse branch, no compensating property. **Use the Σ-form.**

### 1.4 A measured law that contradicts the naive bound

Part B composes the free R_q-MDS across t elements with the per-element σ-layer
and measures the full-state branch exactly (t=2, d=4, q=65537, n=8):

```
  sigma support K      |K|   t   branch (exact)   law t+|K|
  [1, 5]                 2   2                4           4   MATCHES
  [1, 5, 7]              3   2                5           5   MATCHES
  [1, 3, 5, 7]           4   2                6           6   MATCHES
```

**Single-round composite branch is t + |K|, not the naive t·|K| + 1.** The free
R_q-MDS *adds* t−1 to the slot branch; it does not multiply it. The attaining
construction (script's own): put a difference on one slot across all t elements,
chosen in the element-MDS's preimage so that t−1 elements cancel after the MDS;
the survivor pays only the σ-layer — weight t in, weight |K| out.

⚠ **Two corrections to how this result has been relayed.** (a) "Certified
exactly to weight 5 at d=16" belongs to the *single-element* law |K|+1 (Part C),
**not** to the composite law t+|K| (Part B). They are different measurements.
(b) Part B as written measures **only t=2**, three data points. See §1.5.

**What the law does and does not mean.** At q~2^64 with DP(x^7) ≤ 6/q, even the
one-round t+|K| bound puts differential trails far below 2^-128 within two
rounds. **The branch gap was never about statistical trails.** It is about
*structured* attacks — invariant subspaces, §D-style slot-locality — which live
at slot granularity. Cross-granularity multiplication ((t+1)(|K|+1) active
S-boxes) only appears over 4 rounds via the AES superbox argument, which is a
standard wide-trail *inference*, not a measurement, and must be labelled that
way.

### 1.5 Extending the t+|K| law past t=2 (this lane)

Three points at one t is thin — and at t=2, |K|=2 the law t+|K|=4 coincides
with 2|K|, so one of the three does not even discriminate. `design_branch_law_check.py`
(new, this lane) splits the claim into its two halves and pushes t up:

- **Upper bound, constructive.** The attaining vector that Part B describes in
  prose but never exhibits: on one slot s, set the per-element values to
  v = Mds_s⁻¹·e_a. We build it and read off wt(x)=t, wt(Mx)=|K| directly.
- **Lower bound, exhaustive.** Certify no support pair of total weight < t+|K|
  is singular, with a work budget; rows over budget are reported as skipped and
  claim nothing.

Result over 30 configurations at (q,d) = (65537,4) and (12289,8), t ∈ 2..6,
|K| ∈ 2..4:

```
  branch = t+|K| EXACTLY (both halves certified) in 13/30 configs;
  17 lower halves over budget; 0 disagreements
  certified over t in [2,3,4] and |K| in [2,3,4], at both (q,d)
```

**The law survives extension: t ∈ {2,3,4}, |K| ∈ {2,3,4}, two ring geometries,
zero disagreements.** And the *upper* half — the half that carries the security
meaning, since it is what says the free R_q-MDS adds t−1 rather than multiplying
— is unconditional and construction-based at **all 30 rows including t=6**. The
naive t·|K|+1 bound is refuted by construction everywhere.

---

## 2. The schedule cost table: how few dense rounds suffice

### 2.0 First: the σ price was HALVED, and this supersedes the recorded pricing

`ring-hash-cryptanalysis.md` and `density_repricing.py` both price a σ-layer of
support s at **s−1** rows/element/round. `design_branch_frontier.py` re-reads
2026/1127's Definition 9 and prices it at **⌈(s−1)/2⌉**. The argument: the
R1CS-with-automorphisms row is

> `A z ∘ B z = C z + σ(C' z) + σ̃(C̃ z)`

with σ = σ_5 and σ̃ = σ_{−1} **both present in one row**, each applied to an
arbitrary linear combination of the witness. So a chain `u_j = σ_5(u_{j−1})`
costs 1 row each, and **one** combine row then reaches
{5^0..5^c} ∪ {−5^0..−5^{c−1}} — support 2c+1 for c rows. The old pricing missed
the σ̃ channel *and* the chain reuse.

Consequences: full support at τ=1 costs **d/2 = 8**, not d−1 = 15; and at τ=4
full slot-support costs **2**, not 3. **Every cost number in §2 and §4 uses the
corrected law.** It also revises the project's recorded headline: the "defensible
3.9×–4.8×" in `density_repricing.py` was computed under the old law; the same
fully-dense-in-full-rounds schedule is **5.0×** under the corrected one.

✅ **The premise is VERIFIED at source.** Definition 9's public parameters are
`pp = (n_r, n_c, t, t', t̃, n_s, deg, ℓ_in, σ, σ̃)` — **two automorphisms**, with
three matrix families `M_j, M'_j, M̃_j` and three multisets `S_i, S'_i, S̃_i` per
term (`|S_i| + |S'_i| + |S̃_i| ≤ deg`), combined as

> `Σ_i c_i · (∘_{j∈S_i} M_j z̃) ∘ (∘_{j∈S'_i} σ(M'_j)·σ(z̃)) ∘ (∘_{j∈S̃_i} σ̃(M̃_j)·σ̃(z̃)) = 0`

Since σ is a ring homomorphism, `σ(M'_j)·σ(z̃) = σ(M'_j z̃)`. Taking three degree-1
terms gives exactly `c₁(M₁z̃) + c₂σ(M'₁z̃) + c₃σ̃(M̃₁z̃) = 0` — **both automorphism
channels in one constraint, each applied to an arbitrary matrix-times-witness
combination.** The halved pricing stands, and it is not a factor-2 risk.

⚠ One real limit the script's paraphrase glosses: **pp fixes exactly two
automorphisms σ, σ̃ for the whole index** — you choose them (σ_5 and σ_{−1} is the
natural pick, and is what 2026/1127 itself uses) but you do not get a fresh
automorphism per row. The chain-plus-combine construction respects this; any
schedule that wants three or more *distinct* automorphisms in a single row does
not.

### 2.1 The schedules

`design_mds_interleave.py`. All at τ=1, d=16 — this is the table that says what
slot-MDS *costs* in the τ=1 regime, and it is therefore the main input to §4.

**(A) Composite slot-support** (exact, structural — boolean products of the
per-round slot patterns):

```
  support-3 every round (1 row/elt)    [3, 5, 7, 9, 11, 13, 15, 16, 16, 16]
  support-9 every round (4 rows/elt)   [9, 16, 16, ...]
  dense every round (8 rows/elt)       [16, 16, ...]
  dense every 4th, support-3 else      [3, 5, 7, 16, 16, ...]
```

Support-3 alone saturates all 16 slots after **8 rounds** (the product sets
{±5^j} grow by one exponent per round); one dense round collapses the wait to
that round's position. **Support saturation is necessary for RO-likeness and
nowhere near sufficient** — say this every time the table is quoted.

**(B) Composite MDS-ness** (d=8, exact to cap): a single dense Cauchy round
makes the composite skeleton MDS **at once**, and subsequent support-3 rounds do
not destroy it. Support-3 alone becomes MDS only when its product set saturates
(round 4 at d=8).

**(C) Slot diffusion of the real permutation, S-box on** (d=16 τ=1 toy, active
slots of 64 after r rounds): support-3 crawls `12 → 20 → 28 → 36 → 44 → 52`;
dense-every-round and even dense-in-round-0-only both hit `64` immediately.

**(D) Cost per absorbed ring element** at proposal geometry (t=9, rate 8, RF=8,
RP=22, α=7, S_α=4), against the 716.8 rows/elt decompose-and-hash baseline of
2026/1127 App C.3:

| σ schedule | rows/perm | per elt | vs 716.8 | branch delivered |
|---|---:|---:|---:|---|
| support-3 every round *(prior lane's headline)* | 646 | 80.8 | 8.9× | 4 of 17 |
| support-9 in full, support-3 in partial | 862 | 107.8 | 6.7× | 10 of 17 in full rounds |
| dense in 4 outer full rounds, support-3 else | 898 | 112.2 | 6.4× | 17 in 4 rounds |
| dense every 4th round, support-3 else | 1087 | 135.9 | 5.3× | 17 every 4th |
| **dense in ALL full rounds, support-3 in partial** | **1150** | **143.8** | **5.0×** | 17 in every full round |
| dense every round | 2536 | 317.0 | 2.3× | 17 everywhere |

The cost law is `rows/perm = S_α·(RF·t + RP) + Σ_rounds (σ rows/elt)·t`,
reproduced exactly for all six rows. The 716.8 baseline is itself reproduced:
`costmodel.py` gives `S_α·(RF·(r+c)+RP) = 4·(8·24+22) = 856` per permutation,
`+2r` per absorb → 44.80 per Z_q element → **16 × 44.80 = 716.8 per ring
element**. ⚠ **Calibration, in our disfavour and therefore worth keeping:** that
model totals the whole FS bill at 2^21.20, while 2026/1127 states its Poseidon
count is "over 2^22" — so **our baseline understates the paper's own figure by
~1.9×, and every speedup ratio quoted here is conservative by about that factor.**
Do not "correct" it upward without re-deriving the transcript accounting. The **S-box floor alone** is
`4·(8·9+22) = 376` rows/perm = **47.0/elt (15.3×)** — that is the σ-free
ceiling on how good any schedule can get, and it bounds the whole design.

The shape of the answer follows Poseidon2's own precedent: Poseidon2's internal
rounds use I + diag(v), branch **2** — weaker than our support-3 — and put the
strong MDS only in external rounds. **Dense-in-full-rounds is the analogous
schedule, and it is the recommended τ=1 point: 143.8/elt, 5.0×.**

---

## 3. The second candidate: the gadget-decomposition Feistel

`design_gadget_feistel.py`. This is a *non-algebraic* alternative — no S-box, no
automorphisms; the nonlinearity is base-B gadget decomposition, which is free
where a folding scheme already proves norms.

**The design.** R_q = Z_q[X]/(X^16+1), gadget base B = 2^16, K = 4 planes
(B^K = 2^64). State (L,R) ∈ R_q^4 × R_q^4, so t=8 elements, sponge rate 7,
capacity 1 element = 1024 bits. Per round: decompose R_i + a_{r,i} into planes
(1 linear row/element, plane norm bound is the folding scheme's own ∞-norm
check — **free**); form P=2 adjacent-plane products Z_{i,j} = Y_{i,j}·Y_{i,j+1}
(P mult rows/element); Feistel-swap with F_r a *public dense linear* form in the
witnessed planes and products (**free** — it fuses into the next round's
decomposition row). Cost **w·(1+P) = 12 rows/round**, NR=16 rounds.

**Measured, at full scale (q = 2^64−59, d=16, 16 rounds):**

1. **Bijectivity**: explicit inverse round-trips **25/25** random full-size
   states (8 ring elements = 8192 bits each). Structural — Feistel inverts for
   any round function — but exhibited constructively at deployment size.
2. **Slot mixing** (τ=1 toy): one flipped input slot reaches **33.0/64 active
   slots after 1 round, 64.0/64 after 2**. Full diffusion in two rounds.
3. **P ≥ 1 is a hard requirement, not an option.** With P=0 the round function
   is linear-up-to-carries and a fixed input difference maps to a **fixed**
   output difference through all 16 rounds — constant in 40/40 samples at
   1 round, and the script confirms P=0 is trivially distinguishable. P=2 kills
   the order-1 differential (0/40 at every round count tested).
4. **Cost**: 192 rows/perm ÷ rate 7 = **27.4 rows per absorbed ring element**.
   **26× cheaper than Poseidon-over-Z_q (716.8) and 5.2× cheaper than the
   σ-Poseidon dense-in-full-rounds point (143.8).**

**The three caveats, and they are load-bearing:**

- ⚑ **At the deployed Frog modulus it is BROKEN BY DEFAULT.** A sponge
  permutation must be a *function* of its input. Base-B decomposition
  constrained only by "recomposes mod q" + "coefficients < B" pins the planes
  uniquely only for coefficients ≥ γ := B^K − q. At Frog
  (q = 15912092521325583641), **γ/q = 0.159 = 2^-2.7**, giving **≈2.55 ambiguous
  coefficients per element** — the script exhibits it constructively: coefficient
  12345 has two valid plane vectors, `[12345,0,0,0]` and
  `[3410,40643,7127,56531]`, both recomposing to 12345 mod q and both passing the
  norm check. **A malicious prover chooses, and each choice changes the hash
  output — free Fiat–Shamir grinding.** At q = 2^64−59, γ = 59, γ/q = 2^-58.1,
  ambiguity per element 5×10^-17: grinding one ambiguous coefficient costs ~2^54,
  priced into the ROM bound as Q·2^-54, **no gate needed**. So this candidate
  *requires a modulus change* — which is ordinary work, but it must be said.
  (⚠ Worth flagging outward: the same representative-malleability exists in
  2026/1127's **own** App C.4 MSIS-hash use at γ/q = 0.159. Whether it is
  exploitable there depends on how u_i enters knowledge soundness. **A question
  we should ask them, not an attack we claim.**)
- ⚑ **NR=16 is precedent plus margin, not cryptanalysis.** It comes from the HKT
  14-round indifferentiability result for 2-branch Feistel **with ideal round
  functions**, and nothing about F is an ideal round function.
- ⚑ **The order-2 differential does not die in one round.** The degree-2 plane
  structure makes the second derivative of a single F state-independent up to
  carries — **constant in 40/40**. Across rounds the next decomposition destroys
  the polynomial structure, but **meet-in-the-middle / boomerang from both ends
  is the obvious attack and is the first attack-me item for this candidate.**

**Assessment.** 27.4/elt is a big number — 26× — and it comes from *not* paying
for an S-box at all. But this candidate is much less mature than the σ-Poseidon
one: its nonlinearity has no analogue in the literature, its round count is
borrowed from an idealised model, and it has a live second-order structure. It
is the higher-ceiling, higher-risk option. Do not quote 27.4 without the three
caveats attached.

---

## 4. The fork: τ=1 vs τ=4

*(cost half done — security half pending cryptanalysis-lane input)*

### 4.1 The fork is real

`ring-hash-cryptanalysis.md`'s handoff says **"keep τ=1 (load-bearing); τ>1
reopens the extension-field S-box question."** The design lane's branch closure
(§1.2) happens **at τ=4**. Nobody had put these on one axis. `design_tau_tradeoff.py`
(new, this lane) does the cost half in the §2 metric; τ changes only how many σ
rows buy slot-MDS (ℓ=16 needs 8 rows; ℓ=4 needs 2), because element size, S-box
cost (x^7 = 4 R_q mults) and round counts are all τ-independent.

| regime | schedule | rows/perm | per elt | vs 716.8 | branch |
|---|---|---:|---:|---:|---|
| τ=1 | support-3 every round | 646 | 80.8 | 8.9× | 4 of 17 — **the #1 weakness** |
| τ=1 | dense in all full rounds | 1150 | 143.8 | 5.0× | 17 = slot-MDS in full rounds |
| τ=1 | dense every round | 2536 | 317.0 | 2.3× | 17 everywhere |
| τ=4 | support-3 every round | 646 | 80.8 | 8.9× | 4 of 5 |
| **τ=4** | **slot-MDS in full, support-3 in partial** | **718** | **89.8** | **8.0×** | **5 = slot-MDS in full rounds** |
| τ=4 | slot-MDS every round | 916 | 114.5 | 6.3× | 5 everywhere |

**The fork in one number each way:**
- slot-MDS in every round: τ=1 costs 317.0/elt, τ=4 costs 114.5 — **τ=4 is 2.77× cheaper**
- slot-MDS in full rounds: τ=1 costs 143.8/elt, τ=4 costs 89.8 — **τ=4 is 1.60× cheaper**

And the comparison that actually decides it — **what does the same budget buy?**
At ~90 rows/elt, **τ=4 buys slot-MDS in every full round; τ=1 buys support-3
only, i.e. the recorded #1 weakness un-fixed.**

**A framing point that the fork's wording hides: τ=4 is the status quo, not the
proposal.** The deployed Frog ring *is* τ=4 (`ord_32(q) = 4`, measured). So "keep
τ=1" is not the conservative branch — it requires **changing the deployed
modulus** to one with q ≡ 1 mod 32, on top of paying 1.6× more for the same
branch. The burden of justification sits on τ=1, and the handoff line phrased it
the other way round.

**Robustness of the cost verdict.** Round counts are held at RF=8/RP=22 for both,
and those are borrowed (a width-~12 prime-field Poseidon set) and underived for
*either* regime — §5 of the cryptanalysis note is right about that. So the honest
form of the cost verdict is a break-even: **τ=4 stays ahead until the
extension-field S-box needs ~3.2× the partial rounds of τ=1** (RP=70 against 22).
That is a wide margin, and it is the right way to state it, because the round
count is exactly the quantity the extension-field question could move.

### 4.2 A hard constraint nobody had checked: C1 at τ>1

The S-box x^α permutes R_q iff it permutes each slot field F_{q^τ}, i.e. iff
**gcd(α, q^τ − 1) = 1** — condition C1 in `sigma_poseidon.py`, which the
docstring correctly calls "strictly stronger than the field condition" but which
had never been evaluated at τ=4 against the moduli actually on the table.
Evaluated now (`design_tau_tradeoff.py`):

```
  deployed Frog  (q mod 7 = 2)
    tau=1/2/4:  gcd(7, q^tau-1) = 1   alpha=7 OK at every tau
  2^64-59        (q mod 7 = 6)
    tau=1:      alpha=7 OK
    tau=2/4:    gcd(7, q^tau-1) = 7   alpha=7 ** ILLEGAL **  (smallest legal: 13, 5 mults)
```

Two consequences, one benign and one new:

1. **The fork is not blocked at Frog.** q ≡ 2 mod 7, so α=7 survives at τ=4.
   Good — the τ=4 branch closure is reachable on the deployed ring.
2. ⚑ **The two candidates want incompatible moduli, and this had not been
   noticed.** 7 | q^τ−1 iff ord_7(q) | τ; since (Z/7)^* is cyclic of order 6,
   τ=1 excludes only q ≡ 1 (17% of primes) but **τ=4 excludes q ≡ ±1 (33%)** —
   C1 is exactly twice as constraining at τ=4. And **2^64−59, the modulus the
   gadget-Feistel *requires*** (§3, tiny γ), is ≡ 6 mod 7, so 7 | q+1 | q^4−1 and
   **α=7 is illegal there at τ=4**; σ-Poseidon would need α=13, 5 mults, +25%
   S-box cost. Meanwhile the deployed Frog modulus is fine for σ-Poseidon at
   every τ and **fatal for the Feistel** (γ/q = 0.159).

   Neither script had checked C1 against the *other* candidate's modulus.

**And the collision is resolvable — don't file it, it took seconds.** Searching
for a prime with tiny γ *and* ord_32(q)=4 (so X^16+1 splits into quartics, τ=4)
*and* gcd(7, q^4−1)=1:

```
  gamma=   279  q = 18446744073709551337   q mod 32 =  9  q mod 7 = 3   gamma/q = 2^-55.9
  gamma=   425  q = 18446744073709551191   q mod 32 = 23  q mod 7 = 4   gamma/q = 2^-55.3
  gamma=   503  q = 18446744073709551113   q mod 32 =  9  q mod 7 = 3   gamma/q = 2^-55.0
```

**q = 2^64 − 279 serves both candidates**: τ=4 so the §1.2 branch closure
applies; α=7 stays legal at 4 mults; and γ/q = 2^-55.9, so the Feistel's
decomposition is unambiguous except with probability ~2^-52 per element —
grinding one ambiguous coefficient costs ~2^52 against ~2^54 at 2^64−59, **two
bits worse in exchange for τ=4 and a legal α=7**. ⚠ The exact ROM accounting for
that residual is the folding scheme's to state and is *not* settled here; what is
settled is that **no modulus tradeoff is forced** and the two candidates remain
independently evaluable.

### 4.3 The security half, part 1: the invariant subfield, measured

The sharpest *concrete* form of "the extension-field S-box question" is an
invariant subspace, and it is checkable rather than speculative. At τ=4 each slot
is F_{q^4}, which **contains the base field F_q**. The S-box x^7 maps F_q into
F_q; and the Frobenius twist σ_k carries at τ>1 is x ↦ x^{q^j}, which **fixes F_q
pointwise**. So *both* the nonlinear layer and the slot permutation preserve

> V = { states whose every slot value lies in F_q } — a subspace of dimension ℓ=4
> inside the d=16-dimensional state.

If the linear layer also preserves V, then V is invariant under the whole round;
on V the permutation is just an ℓ-slot F_q SPN (a ~2^30 object against 2^120 in
the toy), giving a distinguisher and preimages on V. Only the σ-layer
*coefficients* can break it. Measured (`design_subfield_invariance.py`, p=89,
ℓ=4, S-box x^7, the slot-MDS set {1,5,−1,−5}):

```
  sigma coeffs        round consts    state leaves V after round
  scalar (in F_p)     in F_p          NEVER (invariant through 12)  <-- INVARIANT SUBSPACE
  scalar (in F_p)     generic         round 1
  generic F_(p^4)     in F_p          round 1
  generic F_(p^4)     generic         round 1
```

**The invariant subspace is real, and the cure is a checkable condition:**

> ⚑ **C6 (new; τ>1 only): the σ-layer coefficients must not lie in the base field
> F_q.** One subfield test per coefficient (u ∈ F_q iff u^q = u).

Two things make this a *mild* rather than alarming finding:

1. **It is not a new class of condition — it is an existing one, one field
   down.** `ring-hash-cryptanalysis.md` weakness #4 already records that "mixing
   coefficients must be generic ring elements — a scalar/real MDS **revives a
   t-cell invariant subspace** with trivial distinguisher and preimages on it."
   C6 is that same condition widened from "not a scalar in Z_q" to "not in the
   subfield F_q". **τ=4 does not add an unfamiliar requirement; it widens a
   requirement the design already had, and the widened form is machine-checkable.**
2. V is invariant **only when both** the coefficients and the round constants lie
   in F_q — either one outside breaks it in one round. But rely on the
   *coefficients*: a constant outside F_q breaks V by accident of a generic
   instantiation (constants only translate), whereas a coefficient outside F_q
   breaks it structurally, in the layer meant to mix.

⚠ **What this does NOT settle**: the algebraic-degree question over F_{q^4}
(Chaghri-style coefficient grouping — whether iterated x^7 still grows degree
multiplicatively when the Frobenius is a q-power map). That is a separate front
and this script does not touch it. See §4.4.

### 4.4 The security half, part 2: degree growth — where the τ=1 preference comes from

**Located the actual source of the handoff's τ=1 preference**, and it is not
vague: `density_repricing.py` closes with

> "Chaghri's failure mechanism is the algebraic degree of an F2-LINEARIZED
> POLYNOMIAL over an EXTENSION field. At tau = 1 … σ_k carries NO Frobenius twist
> — it is a pure permutation of the d slot coordinates, an F_q-linear permutation
> matrix — so there is no linearized polynomial and coefficient grouping does not
> literally apply. … **At tau > 1 the Frobenius twists are real and Chaghri
> applies directly.** … the 4.8× butterfly figure is defensible at tau=1 and NOT
> defensible at tau>1 without a coefficient-grouping-style degree analysis that I
> have not done."

So "τ>1 reopens the extension-field S-box question" means exactly: **at τ>1 our
σ-layer *is* an F_q-linearized polynomial, which is the object Chaghri was broken
through, and the coefficient-grouping degree analysis is undone.** That is a real
and correctly-identified gap. Two things bear on it, one from the record and one
from §1:

1. **The prior lane already probed an extension-field case and found nothing.**
   `ring-hash-cryptanalysis.md` "What held" records: *"No Chaghri-style degree
   stall **at τ=1 or τ=2** — degree grows multiplicatively because x^α (α=7) is
   not a q-power map."* **τ=2 is an extension field** (slots F_{q^2}, Frobenius
   twists real). So the lane's own measurement already covers a τ>1 case and came
   back clean — and it came back clean *after* the lane retracted a false
   positive there, so it was examined with more care than average, not less.
   This is in direct tension with the same file's "keep τ=1" handoff.
2. **Density: our τ=4 layer is denser than the patched Chaghri.** Chaghri's
   broken B had **support 1**; Liu–Sarkar–Wang–Meier–Isobe's repair, which the
   designers adopted, was **support 3**. The τ=4 slot-MDS set {1,5,−1,−5} is
   **support 4** — above the repair — and it is exactly the layer §1.2 measures
   as slot-MDS. The attack's own stated root cause ("the vulnerability of Chaghri
   exists in the usage of a **sparse** affine transform") is the property we do
   not have at the recommended parameters.

⚠ Neither of these is the degree analysis. **Point 1 is evidence by extension
from τ=2, not a result at τ=4; point 2 is a density comparison, not a bound.**
The coefficient-grouping analysis over F_{q^4} remains genuinely undone, and it
is the single largest open item for the τ=4 branch.

⚑ **And the decisive symmetry the handoff missed: τ=1 does not avoid needing a
degree analysis either.** `ring-hash-cryptanalysis.md` weakness #5 says the round
count "is borrowed, not derived — RF=8/RP=22 is a width-~12 Poseidon set, but the
object is a width-144 SPN … **Deriving it for the actual width and the measured
degree curve is the design lane's first job.**" That job is outstanding **in both
regimes**. So τ=4 does not *add* the requirement for a degree analysis; it
changes *which* analysis (coefficient grouping over F_{q^4} rather than a
wide-trail round-count derivation at width 144). **"τ=1 is safer" is only true if
τ=1 were analysed and τ=4 unanalysed. Neither is analysed.**

### 4.4b ⚑ THE FINDING THAT FALSIFIES §4.5's FIRST DRAFT — integral cryptanalysis in characteristic p

**Beyne & Verbauwhede, "Integral cryptanalysis in characteristic p", ASIACRYPT
2025, eprint 2025/932.** Verified at the **primary artifact** (the authors'
`KULeuven-COSIC/integral-cryptanalysis-characteristic-p`, whose README says it is
*"the code used for the analysis in sections 6.2 and 7.2"*), reading the executed
outputs of `SPN.ipynb` — not relayed from an abstract.

**The result: in large prime characteristic, integral/divisibility properties
survive far past the round where algebraic degree saturates**, so prior degree
estimates for MiMC/Poseidon-family designs are, in the authors' own word,
*"overly optimistic."*

`SPN.ipynb` sweeps **extension degree at fixed d=7, t=8, comparable word size** —
exactly our τ axis. From the cells titled *"SHARK-like properties with higher
divisibility based on saturating sboxes"* (mod p², which degree cannot see):

| slot field | last round with a mod-p² property |
|---|---:|
| **prime** (2^64−2^32+1) | **1** |
| degree-2 extension | **13** |
| **degree-4 extension** | **20** |
| degree-8 extension | 21–22 |

**Monotone in extension degree, large prime characteristic, our exact S-box
shape.** And the artifact's scope statement is *"finite rings of prime
characteristic p that are isomorphic to a product of fields"* — literally
R_q ≅ F_{q^4}^4.

⚑ **This falsifies the premise §4.3 rested on** — that the only
extension-field-specific risk is the invariant subfield and that C6 closes it.
**There is a second, independent, extension-field-specific effect; no coefficient
condition closes it; and it is monotone in exactly the direction τ=4 moves.**
The round-count margin §4.1 priced (3.2×) is measured against RP=22, and a design
needing to clear round 20 rather than round 1 eats a large share of it.

⚠ **What this does NOT establish**: their base primes are 2^17–2^31 and ours is
2^64; **the round counts do not transfer.** The *direction* is solid; the
*magnitude at our parameters is unmeasured.*

### 4.5 VERDICT (REVISED): do not commit to τ=4 — and τ=2 is now the leading candidate

⚠ **This section's first draft said "τ=4, moderate-to-high confidence." That was
written before §4.4b and is withdrawn.** Recording the reversal rather than
quietly editing it, because the failure mode is instructive: **I priced the fork
on the invariant I happened to have a clean measurement for** (branch number,
invariant subfield) and treated the absence of a *measured* problem as the
absence of a problem. The instrument I named in the first draft was even
correctly labelled blind to a coefficient-grouping stall — and the wound turned
out to be in a third place neither instrument looked.

**Three constraints now bear on τ, and they do not point the same way:**

| | τ=1 (ℓ=16, F_q) | **τ=2 (ℓ=8, F_{q²})** | τ=4 (ℓ=4, F_{q⁴}) |
|---|---|---|---|
| challenge space (‖S‖=q^τ, §4.6) | 2^64 — **insufficient** | **2^128 — sufficient** | 2^256 — excess |
| integral property survives to round (§4.4b) | **1 — best** | 13 | 20 — **worst** |
| slot-MDS cost, full rounds (§4.1) | 143.8/elt (5.0×) | **107.8/elt (6.7×)** | 89.8/elt (8.0×) — best |
| S-box cryptanalysis | well-studied | thin | thin |

**τ=1 is eliminated by the challenge space** — 2^64 cannot carry a 128-bit
soundness target without repetition paid by the whole folding scheme, and that is
2026/1127's own stated reason for raising τ. **τ=4 is the most exposed on the one
effect we now know is monotone and unpriced.** **τ=2 is the only point that is
acceptable on all three axes**: exactly enough challenge space, the mid value on
integral survival, and 6.7× — giving up 1.3× of cost against τ=4 to move from the
worst to the middle of the axis that just falsified the previous verdict.

> **Recommendation: τ=2, provisionally — and treat it as provisional.**
> Confidence: **low-to-moderate**, and deliberately lower than the first draft's.
> The honest position is the one the cryptanalysis lane reached independently:
> **the evidence does not settle it, and the missing thing is a measurement, not
> a citation.**

⚑ **THE EXPERIMENT THAT CONVERTS THIS FROM ARGUMENT INTO MEASUREMENT, and it is
hours not days:** run the **authors' own `SPN.ipynb`** at our parameters —
`p = 15912092521325583641`, `d = 7`, comparing `e=4, t=4` (τ=4) against
`e=2, t=8` (τ=2) and `e=1, t=16` (τ=1). It is their tool, on our numbers, on the
exact invariant that broke the first verdict. Needs a SageMath kernel (not
installed; `brew install sagemath`, README pins 10.7; `latte_int` is only needed
for `Feistel.ipynb`, not ours). **Run this before choosing τ.** Nothing else in
§4 substitutes for it.

### 4.5b What §4.4b did not disturb

Recorded so the reversal does not swallow the parts that still hold:
- **§4.6's challenge-space argument stands** and still eliminates τ=1.
- **§1's branch closure stands** — the measurement is a rank statistic and is
  unaffected. **The slot group of the Frog ring is the Klein four-group**
  (σ₅→(3,2,1,0), σ₋₁→(1,0,3,2)); one row reaches 3 of 4 slots, so slot-MDS needs
  2 rows against 8 at τ=1. Independently confirmed.
- **§2.0's ⌈(s−1)/2⌉ law stands**, now doubly confirmed: Definition 9 names
  **σ = σ₅ and σ̃ = σ₋₁ explicitly**, and multiple same-channel terms collapse
  (σ(M′₁z)+σ(M′₂z) = σ((M′₁+M′₂)z)), so there are **exactly two** channels per row.
- **C1 stands**, with an addition: **α ∈ {2,3,4,5} are *never* legal at τ=4**
  (r−1 | 4 ⇒ r | q^4−1 always). Fallback α=11 or 13 costs one extra multiplication.
- **C6 stands and is a named published class, not our invention.** Marvellous
  (eprint 2019/426), verbatim: *"We require that the affine polynomial has
  coefficients which do not lie in any subfield of F_{2^{n/m}} thus frustrating
  this attack."* Sharpened form for us: every σ-layer coefficient and round
  constant c must satisfy **σ₉(c) ≠ c**. Integer coefficients fail; X passes.
  **Cost zero** — a Definition 9 matrix entry is an arbitrary R_q element either way.


### 4.6 A systems-level argument against τ=1 that nobody has made

⚠ Not recorded anywhere in our corpus (grepped: no hits for *exceptional set*,
*strong sampling set*, *challenge space* across `notes/` and `paper/`). It is
elementary, and it points the same way.

Lattice folding needs challenges drawn from an **exceptional set** S ⊆ R_q — a
set whose pairwise *differences are units* — because soundness arguments divide
by challenge differences. In R_q ≅ ∏_{i=1}^{ℓ} F_{q^τ}, an element is a unit iff
**every** CRT slot is nonzero. So:

> **|S| ≤ q^τ, and the bound is tight.** *Proof.* For distinct s, s' ∈ S, s − s'
> is a unit, so its slot-1 component is nonzero, so s and s' differ in slot 1.
> Hence the slot-1 projection S → F_{q^τ} is injective and |S| ≤ q^τ. The
> diagonal copy {(c,…,c) : c ∈ F_{q^τ}} attains it, since (c−c',…,c−c') is a unit
> whenever c ≠ c'. ∎

**τ is exactly the exponent of the challenge space.** At q ~ 2^64:

| τ | slots ℓ | challenge space |
|---|---|---|
| 1 | 16 | **2^64** |
| 2 | 8 | 2^128 |
| 4 | 4 | **2^256** |

**A fully splitting ring — the τ=1 the handoff prefers — has the *smallest
possible* challenge space, q itself.** 2^64 is not enough for a 128-bit
soundness target without parallel repetition or an extension, and repetition is
paid by the *whole folding scheme*, not by the hash. τ=4 gives 2^256 outright.

✅ **Confirmed at source, and it is 2026/1127's own reasoning — not our
inference.** The paper's Definition 4 is exactly this notion ("*a strong sampling
set if a − b has a multiplicative inverse*", crediting [CCKP19]), it gives
verbatim our diagonal construction and our bound —

> "Let R̄ = R_q := Z_q[X]/⟨X^d+1⟩ and suppose q is a prime such that R_q ≅ F_{q^τ}^t.
> Then C := {a ∈ R_q : NTT(a) = (i, i, …, i) ∈ F_{q^τ}, i ∈ F_{q^τ}} is a strong
> sampling set of **size q^τ**."

— and then states the design principle outright:

> **"For a fixed q, we may choose τ to obtain exponentially-sized strong sampling
> sets. This will be useful in our protocol."**

*(Their `t` is the slot count, our ℓ.)* So **the paper deliberately raises τ to
enlarge the challenge space, and τ=1 is precisely the choice that makes their
own construction degenerate to its minimum, q.** This is the strongest item in
§4: it is a cost τ=1 imposes on the *ambient folding scheme* rather than on the
hash — and the hash was only ever a slice of the problem. **A ring-hash design
that demands τ=1 is asking the host protocol to give up its challenge space.**

⚠ **Scope, corrected after §4.4b:** an earlier draft ended this subsection "and
that is the decisive reason the fork resolves to τ=4." **It is not.** This
argument is decisive *against τ=1* — it says nothing about τ=2 vs τ=4, both of
which clear the 128-bit challenge-space requirement (2^128 and 2^256). It sets
the **floor** on τ; §4.4b sets the **ceiling**; τ=2 is where they meet.

---

## 5. Delegation vs. a new hash

### 5.0 The bar, stated first so the verdict is decidable

Three of four ring-native FS "escapes" suggest the open problem may be
**avoidable** — either by not needing an in-circuit hash (Symphony 2025/1905),
by cutting RO calls to a handful (ProtoGaLattice 2026/1317), or by **delegating**
the hash to a cheaper argument (GKR/sumcheck: 2026/551 for Poseidon, Keccacheck
2025/1764 for Keccak-f). **A "we should delegate instead" conclusion is a good
outcome and we should be willing to reach it.** So set the bar before hearing the
evidence.

**The hash is not part of the bill — it is the bill.** `costmodel.py`: of the
2,417,127 R_q constraints of Fiat–Shamir, **2,402,503 (99.4%) is hash
absorb/squeeze.** So anything that removes the hash removes essentially the whole
FS cost, and the comparison is clean.

| option | FS cost (R_q constraints) | FS share of a 2^22–2^23 IVC circuit |
|---|---:|---|
| status quo (Poseidon over Z_q) | 2,417,127 = 2^21.2 | 58% – 29% |
| σ-Poseidon, τ=1 (5.0×) | 483,425 = 2^18.9 | — |
| **σ-Poseidon, τ=4 (8.0×)** | **302,141 = 2^18.2** | 14.5% – 4.8% |
| gadget-Feistel (26×) | 92,257 = 2^16.5 | 4.9% – 1.5% |

> ⚑ **The bar: a delegation scheme must land the *verifier's* in-circuit cost
> below ~3×10^5 R_q constraints to beat σ-Poseidon, and below ~9×10^4 to beat the
> gadget-Feistel.** Prover-side savings do not count — the whole problem is
> *in-circuit* verifier cost. This is the number to hold every escape against.

Two structural questions that decide whether delegation is even applicable, and
which we can answer from our own side:

1. **Does sumcheck/GKR work over R_q at all?** *Yes, and better at τ=4.* Sumcheck
   soundness needs challenges from a strong sampling set, which §4.6 establishes
   has size **q^τ** — 2^256 at τ=4, ample; **2^64 at τ=1, marginal.** So the same
   τ choice that settles §4 also conditions delegation. Pleasing convergence, and
   it means τ=4 should be fixed *before* the delegation question is re-opened.
2. **Does it compose with the substrate we are actually building?** ⚠ **Less
   readily than "it composes with our GKR substrate" suggests.**
   `gkr-substrate-findings.md` records, verified by grep over our trees:
   **"GKR / layered circuits / zerocheck / two-vector `eq` in Lean: all absent"**;
   the commitment seam is **positional — "the wrong shape for a multilinear
   claim"** — and the BaseFold bridge "is a campaign, not a memo section". Our
   substrate is also a **prime-field, FRI-based** engine, whereas this setting is
   R_q lattice folding. **Delegation here is not a matter of reusing something we
   have; it is a second proof system to build and to compose.** That cost belongs
   in the comparison.

### 5.0b The ceiling, decomposed — why the Feistel beats it and why σ-Poseidon can't reach it

A peer scored the theoretical ceiling for a *perfect* ring-native sponge at
~1.5×10^5 (recovering the d=16 encoding waste), and the gadget-Feistel came in
**under** it at 92,257. A number that beats a theoretical ceiling is usually a
modelling slip, so `design_ceiling_decomposition.py` (new) factors both sides:

> `rows/element = (rows per permutation) ÷ (elements absorbed per permutation)`

**The ceiling is a PACKING-ONLY bound** — rate ×16 with Poseidon's permutation
cost *held fixed*. Any design with a cheaper permutation is simply not bounded by
it. That is not an error in the ceiling; it is the ceiling answering a narrower
question.

| design | rows/perm | rate (R_q elts) | rows/elt | FS total | speedup | = perm × rate |
|---|---:|---:|---:|---:|---:|---|
| 2026/1127 baseline | 896 | 1.25 | 716.8 | 2,417,127 | 1.0× | 1.00 × 1.00 |
| **"perfect" sponge (the ceiling)** | 896 | 20.00 | 44.8 | 151,070 | **16.0×** | 1.00 × 16.00 |
| σ-Poseidon τ=1 dense-full | 1150 | 8 | 143.8 | 484,741 | 5.0× | 0.78 × 6.40 |
| σ-Poseidon τ=4 slotMDS-full | 718 | 8 | 89.8 | 302,647 | 8.0× | 1.25 × 6.40 |
| **σ-Poseidon S-BOX FLOOR (σ-free)** | 376 | 8 | 47.0 | 158,489 | **15.3×** | 2.38 × 6.40 |
| **gadget-Feistel (no S-box)** | 192 | 7 | 27.4 | 92,492 | **26.1×** | **4.67 × 5.60** |

**(a) The Feistel's 92,257 is NOT a modelling slip.** It wins on *both* factors —
**4.67× on permutation cost and 5.60× on rate** — because it has **no S-box**:
its nonlinearity is gadget decomposition, whose norm check the folding scheme
already pays for. 4.67 × 5.60 = 26.1×, reproducing the reported figure exactly.
**The arithmetic survives; the risk is not arithmetic.** It rests on the two
assumptions already in §3, and *those* are where to press: (i) the ∞-norm check
covers every plane witness free — but the products Z have coefficients < d·B² and
are witnessed via their own base-B planes; (ii) NR=16 suffices. **If (i) fails
the permutation factor collapses toward the S-box designs.**

**(b) τ is NOT the binding constraint on σ-Poseidon — the σ-layer is.** The
**S-box floor alone is 47.0 rows/elt = 15.3×**, which is essentially the 16×
packing ceiling. So an S-box design *starts at the ceiling*, and every σ row
bought for branch number is given back below it:

- τ=4 slot-MDS costs 342 rows/perm → lands at **8.0×** (gives back 7.3×)
- τ=1 dense costs 774 rows/perm → lands at **5.0×** (gives back 10.3×)

> **σ-Poseidon can never exceed 15.3×, and τ only decides whether it lands at
> 8.0× or 5.0×.** The Feistel is not bounded by 15.3× at all, because that bound
> *is* the S-box.

### 5.1 The escapes, assessed

**Escape 3 (GKR-delegation) — *pending lane detail*.** Escapes 1, 2 and 4
verified at source below; the lane's net verdict is in §5.2.

#### Escape 2 — ProtoGaLattice (2026/1317): NOT an escape. A 33× cut of the *same* bill — which is the good news

The brief asked whether the residual RO calls still have to be arithmetized. **They
do, and the paper says so in the same breath as the claim:**

> "sumcheck imposes a huge number of random oracle calls (≈100 according to
> Latticefold) and therefore a complex verifier circuit. When used in an IVC or
> PCD construction, **all these evaluations of hash functions need to be hardcoded
> into the verifier circuit**, which is a very significant source of inefficiency."

and the result:

> "we obtain a folding scheme for k witnesses of a high-degree polynomial relation
> that **requires only three random oracle calls**. To this, we need to add the
> cost of a range proof … for each of the witnesses."

So: **~100 → 3 (the abstract says four counting the range-proof overhead), a
~25–33× reduction, of exactly the bill a better hash also reduces.** It is a
*reduction*, not an escape — precisely the distinction the brief asked for.

⚑ **CORRECTION — my first draft called this "the best news in the section" and
said the two compose multiplicatively. That was wrong, and the hedge I attached
to it is where the error was.** I flagged that our accounting counts *sponge
permutations from transcript size* while ProtoGaLattice counts *RO calls*, said
reconciling them was required before multiplying, and then wrote the qualitative
composition anyway. **Reconciled, the 25× is a cut of the wrong quantity:**

- **RO *calls* ≠ sponge *permutations*** — there are ~2,650 permutations spread
  across those ~100 calls. Cutting calls to 4 does not cut permutations to 4.
- **Sumcheck messages are only 2.6% of the absorbed transcript.** Removing
  sumcheck — ProtoGaLattice's entire thesis — **cannot touch the other 97.4%**.
  **Their own Open Problem #1 concedes this.**
- Derived in-circuit cost: **~483k–720k**, i.e. **1.6–2.4× OVER** the σ-Poseidon
  bar. The paper states no figure of its own.

**So it is not an escape and it is not a free multiplier either.** The lesson for
this note: *a hedge is not a substitute for doing the reconciliation.* I wrote
down exactly the check that would have caught it and then published the claim the
check was supposed to gate.

⚠ Its own limitation, carried: *"the accumulator we obtain satisfies a relaxed
bound B₁ which is greater than the initial bound B, so **we cannot iterate our
folding scheme forever**. To achieve IVC or PCD, we require the norm bootstrapping
protocol that we introduce next."* The three-RO-call figure is for one folding
step, not for unbounded IVC.

#### Escape 1 — Symphony (2025/1905): verified, and it targets exactly our setting

Headline confirmed verbatim: *"we re-envision how to use folding, and introduce
Symphony, **the first folding-based SNARK that avoids embedding hashes in SNARK
circuits**."*

**It is not a general-purpose remark — it is aimed at our exact bill.** Symphony
is itself **lattice-based** (Ajtai commitments, R_q-multiplications), and it
states our measurement independently: *"the Fiat–Shamir circuit is **dominant**
in lattice-based folding schemes"*, and *"the verifier circuit complexity is
dominated by the Fiat–Shamir heuristic, which is large."* That is the same 99.4%
we measured in §5.0, from the other side.

**Mechanism**: high-arity lattice folding plus a **commit-and-prove compiler**
that moves the Fiat–Shamir transform *outside* the recursive SNARK circuit; the
output is two CP-SNARK proofs plus one SNARK proof. Because hashing gadgets are
what cap folding arity at 2–3, removing them also unlocks high arity — the two
benefits are the same benefit.

⚠ **Its own stated limitation, and it matters for us**: *"it is more nuanced to
compile **hash-based** folding schemes: although we can move the Fiat–Shamir
transform outside the recursive SNARK circuit, the CP-SNARK statement still needs
to check **Merkle-path openings**, which accounts for the dominant part of the
recursive statement and requires instantiating random oracles."* So the escape is
clean for *commitment-based* lattice folding (which 2026/1127 is) and **not**
clean for hash/Merkle-based folding.

⚑ **And a hazard it raises that bears directly on Escape 3**: *"attacks exist
[KRS25] for **GKR-based SNARKs if we allow the proven statement to compute the
Fiat–Shamir hash function itself**."* KRS25 is **Khovratovich, Rothblum,
Soukhanov, "How to Prove False Statements: Practical Attacks on Fiat–Shamir"**
(resolved in Symphony's bibliography). **Delegating our FS hash to a GKR argument
and then Fiat–Shamir-ing that argument is precisely the configuration named
there** — the proven statement computing the FS hash function is the *definition*
of hash delegation. This must be resolved before Escape 3 counts as an escape at
all. ⚠ Not yet run down: whether the attack needs the *same* hash to be both
delegated and used for the outer FS (which a careful two-hash separation would
avoid), or bites more generally. **Do not quote Keccacheck's or 2026/551's
constraint counts as an escape without settling this** — a cheaper verifier for
an unsound configuration is not a win.

#### ⚑ Escape 0, which our own corpus already held: don't be in R_q at all

The lane ranks **Neo/SuperNeo** alongside Symphony as removing more than a
perfect ring hash would. That is **eprint 2026/242 (Nguyen–Setty)**, and it is
**already in our notes** — `mirror-mine-2026-08.md` §4 records it as the *"first
folding scheme that is post-quantum, pay-per-bit, **field-native sumcheck over a
small field (Goldilocks)**, general CCS, low recursion overhead."*

**That is an escape of a different kind from the other four, and it may dominate
all of them: if the folding scheme is *field-native* rather than R_q-native, the
ring-hash problem does not arise.** You hash with an ordinary field Poseidon,
because the transcript is field elements. The entire §4 τ analysis — challenge
space, slot structure, extension-field S-boxes — is an artifact of choosing an
R_q-native folding scheme (LatticeFold / 2026/1127) in the first place.

⚠ **This is a substrate choice, not a hash choice, and it is above this note's
pay grade to make** — 2026/1127's R_q-CCS exists because *TFHE bootstrapping is
natively ring-structured*, and moving to a field-native folding scheme means
re-expressing blind rotation in a field-native constraint system. **That
re-expression is exactly the measurement the lane names as the one number that
would flip the verdict** (§5.2). It is also why "just use Neo" is not free.

`sis-lattice-verdict.md` also records the relevant tension: Neo/SuperNeo's
"Almost Goldilocks" is Goldilocks−32, *"subtracted precisely to destroy
two-adicity"*.

#### Escape 4 — ACLMT: "no valid proof AND no known attack", which is neither of the two things people say

**Albrecht, Cini, Lai, Malavolta, Thyagarajan, "Lattice-Based SNARKs: Publicly
Verifiable, Preprocessing, and Recursively Composable", CRYPTO 2022, eprint
2022/941.** Its Theorem 4 rests on **knowledge k-M-ISIS** (Def. 26); the concrete
instantiation sets η₀=η₁=1, which *is* **knowledge k-R-ISIS** (Def. 27) — so both
variants are at stake, as the brief said. **⚠ Wee–Wu is ASIACRYPT 2023 despite
its 2024/28 eprint number.**

⚠ **The brief's "evidence for the implausibility" is right, and my instinct to
upgrade it to 'broken' would have been wrong.** Three limits on the refutation:

- The attack is built against an **integer/matrix translation** ("MatrixACLMT",
  Assumptions 4.2/4.3), **not** ACLMT's literal ring/module object.
- Its sampler (Alg. 4.4) is a **candidate** resting on a real-rank heuristic —
  *"we do not know how to rule out an extractor that outputs the same
  distribution"* — and the refutation leg is **conditional**: *"under the
  inhomogeneous SIS assumption, either Assumption 4.2 or Assumption 4.3 must be
  false."*
- **Wee–Wu explicitly decline the SNARK break**: *"they do not appear to directly
  break soundness of the SNARKs themselves. It is an interesting question to
  study whether our approach can be extended…"*

**What is nonetheless decisive is author-side concession, including from ACLMT's
own authors:**
- Wee–Wu fn.4: *"Albrecht implemented and confirmed the attack"* — ACLMT's own
  first author, and his gist is titled **"Knowledge K-M-ISIS is false"** (the
  *module* version, i.e. he carried it out of the integer translation himself).
- **RoK, Paper, SISsors** (ASIACRYPT 2024, with **Lai**, an ACLMT co-author),
  fn.4: the assumption *"has subsequently been cryptanalysed … **rendering the
  security proofs vacuous**."*
- **SLAP** (EUROCRYPT 2024, with Albrecht): *"has been recently shown to be (at
  least 'morally') broken."* Albrecht's SIS-with-hints zoo lists
  **"BROKEN Knowledge K-R-ISIS"** with a SageMath attack implementation.

**ACLMT was never revised** (2 revisions, last 2023-02-08, predating Wee–Wu's
publication), and no repair paper exists.

**What survives** — matters if anyone reaches for this again: plain
`k-R-ISIS`/`k-M-ISIS` is **untouched**; the VC as a **weakly binding** commitment
stands (ACLMT's Appendix B is literally *"Vector Commitments without Knowledge
Assumptions"*), but **weak binding is not extractability, so it yields no SNARK**;
and Orbweaver's *restricted* "Knowledge k-P-R-ISIS" is still in play.

⚠ **A disambiguation worth carrying, because it is routinely conflated:** eprint
**2024/30** (Debris-Alazard–Fallahpour–Stehlé, *Quantum Oblivious LWE Sampling*,
STOC 2024) is a **different** result — a quantum break of the *linear-only-
encryption* SNARK line, **not** ACLMT.

> **Corrected one-liner: *ACLMT's SNARK has no valid security proof and no known
> attack.* Do not cite it as a proven-secure lattice SNARK; do not call it broken
> either.**

**Effect on the delegation question: none.** Escape 4 removes nothing on any
formulation, and the corroborating signal is that **none of 2026/1127, Symphony,
ProtoGaLattice or Neo/SuperNeo cites it** — the field has moved to ℓ-succinct
SIS / PRISIS / vanishing-SIS.

### 5.2 VERDICT (REVISED): BUILD IT — delegation is dead

⚠ **This section's first draft said "do not build the ring-native hash yet."
Withdrawn.** Full scoring in `ring-hash-build-verdict.md`; the mechanism, which
is the part worth carrying:

> ⚑ **Delegation pays only when the hash is expensive IN-CIRCUIT.** Keccacheck's
> 6–14× comes from Keccak-f being 20k–50k R1CS *because it is bitwise*.
> **Poseidon-over-R_q in 2026/1127 is 856 constraints per permutation.** There is
> no margin to harvest. **2026/1127's bill is transcript VOLUME; delegation
> attacks UNIT COST.** Different quantities — which is why the escape looked
> plausible and is not.

Second, independent reason: **the delegated argument's own Fiat–Shamir lands back
in-circuit and is sequential** — one in-circuit hash per sumcheck round,
unbatchable. Applied to a 30-round Poseidon at 856 R_q constraints/perm:
**820k–2.87M**, i.e. **2.7–31× over bar**.

| escape | in-circuit cost | verdict |
|---|---|---|
| **Symphony 2025/1905** | 65,536–131,072 whole batch | **the only TRUE escape** — but needs an uncosted port from Z_q-SIMD to R_q-native CCS |
| ProtoGaLattice 2026/1317 | ~483k–720k (derived; paper states none) | 1.6–2.4× **over** bar — a reduction of the same bill, of the wrong quantity |
| 2026/551 | no benchmarks at all | **not the paper the brief described** |
| Keccacheck-shape → Poseidon | 820k–2.87M | **net loss, 2.7–31× over** |
| ACLMT 2022/941 | — | removes nothing; dead as a proof, not broken |

⚑ **The number that ends the argument.** At 2026/1127's **benchmarked** config
(useful work 2.23e6/step), Fiat–Shamir goes from **52.0%** of the circuit today
to **11.9%** with σ-Poseidon and **4.0%** with the gadget-Feistel. **At 4% there
is nothing left for an architectural escape to remove.**

⚠ **Corrections carried:**
- **Keccacheck is eprint 2025/1764.** Our local `ring-r1cs-…-2024-1764.pdf` is
  **2024/1764, a different paper** (zero "keccak" hits). The brief's ID was right
  and the local file is a decoy.
- **2026/551's GKR-for-Poseidon is an Appendix C sub-component with no
  benchmarks**, and its §4.3 explicitly warns against our exact use: FS *"should
  not be instantiated using Poseidon with the same parameters … preferably an
  entirely different hash function."*
- **"It composes with our multilinear substrate" is UNEARNED** — and I wrote it.
  Ours is `variable {F : Type*} [Field F]`, **field-pinned**; a ring
  instantiation is a typeclass generalization *plus re-deriving every soundness
  bound from |F| to |A|*. §5.0's structural note was right for the wrong reason.
- **The honest headline is "FS = 52% of the benchmarked circuit"**, not the
  "32–64× the blind rotation" figure carried in `two-rocks.md`.
- **SuperNeo's "128×" reads as a bits/bytes slip; the real packing ceiling is
  16×** (= d). §5.1's "Escape 0" framing survives as a *substrate* question but
  its magnitude does not.

**And the lesson, which is the transferable part**: the first draft predicted
"delegate" because delegation *fit the architecture we are already building*.
**An architectural fit is not a cost argument.**