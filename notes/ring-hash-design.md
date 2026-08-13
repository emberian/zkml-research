# Ring-hash candidate: the design note

2026-08-13. **Status: IN PROGRESS — written incrementally by the revival lane.**
The predecessor design lane died on credits after writing three scripts and no
prose. This file is the prose. Every number below was produced by re-running the
scripts in this session; the run outputs are quoted, not remembered.

**Scripts.** They lived only in `~/src/ring-ro-hash/`, **which is not a git
repo** — the exact way the predecessor's work nearly vanished. Now versioned at
`notes/ring-hash-scripts/`. All run in seconds to a minute on a laptop.

| script | what it settles | runtime |
|---|---|---|
| `design_branch_frontier.py` | *(recovered)* branch numbers, exact; the τ=4 closure | 6.8s |
| `design_mds_interleave.py` | *(recovered)* schedule/cost table for σ-density | 3.4s |
| `design_gadget_feistel.py` | *(recovered)* the second candidate, full-scale | 58.2s |
| `design_branch_law_check.py` | **(new)** extends the t+|K| law past t=2 | 45s |
| `design_tau_tradeoff.py` | **(new)** prices the fork; C1 at τ>1; joint modulus | ~30s |
| `design_subfield_invariance.py` | **(new)** the τ=4 invariant subfield, and C6 | 2s |
| `costmodel.py` | the 716.8 rows/elt baseline (2026/1127 App C.3) | — |
| `sigma_poseidon.py` | the C1–C5 design conditions + validator | — |
| `density_repricing.py` | why support-3, not support-1 (Chaghri); **superseded on cost by §2.0** | — |

Prior context: `two-rocks.md` §Rock 2 (the survey and the enabling theorem),
`ring-hash-cryptanalysis.md` (the attack-side verdict this note answers).

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

⚠ **This halving is load-bearing for the whole cost case and rests on one
premise: that Definition 9 really carries two independent automorphism channels
per row.** That premise is being verified at source; until it is confirmed,
treat every σ cost here as a factor-2 risk. *(verification pending)*

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

### 4.5 VERDICT: τ=4

**Recommendation: τ=4, at the dense-in-full-rounds schedule (89.8 rows/elt, 8.0×
the decompose-and-hash baseline), conditional on one named analysis.**
Confidence: **moderate-to-high** — raised by §4.6, which turned out to be the
paper's own stated rationale rather than our inference. The cost case is measured
and robust; the residual risk is one undone analysis (item 5).

The six inputs, in the order they should be weighed:

0. ⚑ **The challenge space — decisive, and it is 2026/1127's own argument
   (§4.6).** The strong sampling set has size **q^τ**, and the paper says
   explicitly "*we may choose τ to obtain exponentially-sized strong sampling
   sets.*" τ=1 collapses it to q = 2^64; τ=4 gives 2^256. **This is a cost τ=1
   imposes on the host folding scheme, not on the hash**, and it alone would
   settle the fork.
1. **Cost — measured.** τ=4 reaches slot-MDS for 1.60–2.77× less
   than τ=1, and at τ=1's *equal budget* the #1 weakness simply stays unfixed.
   The verdict survives a **3.2× round-count penalty** before it flips.
2. **Status quo — τ=4 is the deployed ring.** "Keep τ=1" is the branch that
   requires changing the deployed modulus, not the conservative one.
3. **C1 invertibility — clears.** α=7 is legal at τ=4 on the Frog modulus, and a
   joint modulus serving both candidates exists at 2^64−279.
4. **The invariant subfield — real, and cured by a checkable condition (C6)**
   that is the *existing* weakness-#4 condition widened one field down. τ=4
   widens a requirement rather than introducing a strange new class.
5. **Coefficient grouping over F_{q^4} — genuinely open, and the one real cost of
   this verdict.** Mitigated but not closed by: the lane's own clean τ=2
   measurement (an extension-field case), and our support-4 layer sitting above
   the support-3 density that repaired Chaghri. **Not closed. Do not describe it
   as closed.**

**The gating experiment, named so it can be done rather than deferred:** run the
prior lane's own integral/degree instrument at **τ=4** with the {1,5,−1,−5}
layer, against the matched τ=1 and τ=2 runs it already has, and check whether the
degree curve stalls. It is the same instrument, already written, at a third
parameter. ⚠ **State its limitation up front**: an integral over F_q-subspaces
measures F_q-degree, and Frobenius is F_q-**linear**, so this instrument is
**blind by construction to a coefficient-grouping stall in the F_{q^4}-univariate
exponent set.** A clean result from it is weak evidence, not a clearance — and
the real analysis is the exponent-set argument, which is paper work, not a
script.

**If that analysis comes back bad**, the fallback is not τ=1 — it is τ=2 (slots
F_{q^2}, ℓ=8, already measured clean for degree stall), which recovers part of
the branch win at part of the risk. That intermediate was never on the table
because the fork was posed as binary. It is not binary.

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

That, and not the branch number, is the decisive reason the fork resolves to
τ=4.

---

## 5. Delegation vs. a new hash

*(pending — literature lane input outstanding)*

---

## 6. Prior art

**Done — it landed in `ring-hash-cryptanalysis.md` §"Prior art"**, which
previously had zero external citations. Three items; **two of the three came back
partly refuted**:

- **Rubato / Grassi et al. 2023/822** — verified as a full-round break of 5 of 6
  variants, but "warning shot at *our* design" is **overstated**: the attack
  needs a divisor of q, our q is prime, and the paper's own countermeasure is
  "restrict q to prime" (which Rubato's designers then adopted). What transfers
  is the *mechanism by analogy*: their Lemma 1 descends a polynomial map over Z_q
  to every quotient Z_m; **our analogue is the factorization of X^16+1 into τ
  ideals**, on which the S-box acts slot-wise and every automorphism permutes
  slots without mixing — the same wound in ideal-theoretic clothing, and exactly
  what §1 discharges.
- **2021/1010** — the de-linearization remark exists but is a *different idea*
  (domain extension, not RO-likeness), and **the "3,971 AIR constraints" figure
  is refuted and must not be quoted**: its own breakdown sums to 3071, it is an
  op count with no AIR exhibited, and the paper misstates its own ring. **There
  is no usable external datum for "R-SIS hash in an AIR."**
- **SWIFFTX** — verified, and it poses our exact problem in 2008 ("not
  pseudorandom … due to linearity"). Its de-linearizer is two operations and both
  leave the ring. **"Cannot be arithmetized" is our inference, labelled as such**
  — well supported, since the layer's stated goal is high degree over GF(257)
  itself. This is the sharpest statement of our contribution: **de-linearize
  without leaving R_q.**
