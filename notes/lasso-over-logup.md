# Lasso over LogUp — the decomposition read at source, priced in our unit, and stated in Lean

2026-08-16. RESEARCH + LEAN lane. One technique (decomposable-table lookups), two open
problems (the hash in-circuit ratio; the SPARK gap). Companions:
`notes/hash-landscape.md` (the `R* = 2.0–4.5×` crossover and the `R ≈ 3.2×` lookup
pointer this note settles), `notes/spartan-over-what-we-hold.md` (M2, the SPARK gap),
`notes/two-regime-calculator.md` (`logupErr`, `logup_carries_no_regime`).

Provenance legend: **[READ]** primary source at cited file/line · **[MEASURED]** I ran
the command or counted from pinned source · **[DERIVED]** my arithmetic from named
inputs, checkable without trust · **[BUILT]** I wrote it and `lake build` is green.

**Substrate, said out loud (house law):** the new formal artifact is Lean-authored —
`/Users/ember/dev/minidregg/Selvage/DecomposableTable.lean`, landed `feef028`,
`lake build Selvage` green (3097 jobs), import boundary OK, proof hygiene PASS, six
`#print axioms` pins clean. No Rust constraint was written or extended.

---

## 0. Headlines

1. **[READ]** Lasso's load-bearing concept is exactly one identity — Eq. (14),
   `T[r] = g(T₁[r₁], …, T_α[r_c])` with `g` multilinear — and the whole construction
   is Spark (Spartan's sparse-polynomial commitment) reinterpreted: **the "table" whose
   sparse inner product computes a multilinear evaluation is itself decomposable with
   `g = product`.** That sentence is now a theorem (`spark_table_decomposes`), not a
   slogan. §1, §5.
2. ⚑ **The hash payoff, priced in OUR unit: the answer is NO — lookup-arithmetized
   Blake3 lands at `R ≈ 15–16×`, not 3.2×.** Grounded against a deployed
   lookup-arithmetized Blake AIR in a 31-bit field (Stwo's, read at source, counted
   cell by cell): **≈ 4,680 committed cells per Blake3 compression** against our
   Poseidon2's 300 — versus 9,168 bit-decomposed. **The lookup lever buys ≈ 2.0×, not
   the ≈ 10× needed to reach the crossover band `R* = 2.0–4.5×`.** The
   `hash-landscape.md` §2 flip bar ("under ~4,000 blowup-cells and the verdict flips")
   is missed by ≈ 4.7×. The 3.16× Plookup figure was an artifact of a fat Poseidon
   denominator, and §2.4 shows the unit forensics. **The highest-value open
   measurement on that page now has an answer, and the verdict does not flip.**
3. **The SPARK verdict sharpens:** Lasso does not merely *resemble* the missing SPARK —
   **Surge IS Spark**, strengthened (malicious metadata) and generalized (any SOS
   table). So the "no sparse commitment" gap and the "no lookup argument" gap are ONE
   gap with one build. But since §2 removes the hash driver, **the `ñext`/uniformity
   route stands as the cheapest path to succinct Spartan** — two-column in §3.
4. ⚑ **The composition answer: the decomposition does NOT change the soundness
   SHAPE.** Every new term is a polynomial root count over `|F|` — same wall as
   `logupErr = K·H·R/|F|`, no `θ`, no Regime. What it adds: a degree-`(α+1)` sumcheck
   term, α multiset-fingerprint terms, grand-product (or LogUp-pole) terms, and — the
   one genuinely new SHAPE feature — a **validity floor `m < char F`** (counter
   wraparound, Claim 2) that is a precondition, not an error term, and must be pinned
   separately. Full expression in §4, with the two knobs the two-regime calculator
   needs to grow.
5. **[BUILT]** The Lean core: `TableDecomposition` with the combining polynomial
   explicit (`mle gTable` IS `g`, multilinearity structural), satisfiable at Spark's
   tensor table + Jolt's EQ (k=1) + LTU (k=2), and **refutable over every field**: the
   same equality function under the split chunking admits NO decomposition — so
   decomposability is a property of the (function, CHUNKING, α) triple. §5.

---

## 1. Lasso read at source (Q1)

Source: `~/paperbin/lasso-2023-1216.txt` (Setty–Thaler–Wahby, "Unlocking the lookup
singularity with Lasso") + `~/paperbin/jolt-2023-1217.txt` for the table catalog.
All quotes verified at the file. [READ]

### 1.1 The object, and the reduction stack

An **indexed lookup argument** (Def. 1.2): commitments to `a, b ∈ F^m`, public table
`t ∈ F^N`; claim `aᵢ = t[bᵢ]`. Lasso's route (§3, Eq. 5/12/13):

1. `a = M·t` for a sparse `M ∈ {0,1}^{m×N}` with unit rows — equivalent, up to
   `log(m)/|F|` Schwartz–Zippel, to `Σ_y M̃(r,y)·t̃(y) = ã(r)` at a random
   `r ∈ F^{log m}` (Eq. 12).
2. Since row `i` of `M` is the unit vector at `nz(i)`, the LHS is
   `Σ_i eq̃(i,r)·T[nz(i)]` (Eq. 13) — **`m` table reads, weighted by eq**.
3. If `T` is decomposable (§1.3), each read costs `α` sub-table reads plus one `g`,
   and Surge (Fig. 5) proves the whole sum with one sumcheck + memory checking.

### 1.2 Spark, and where the error terms are born

Spark commits a sparse `(log N)`-variate multilinear via dense `(row, col, val)`
polynomials over `log m` variables, then proves the evaluation by proving it
**correctly ran the `O(c·m)` sparse-evaluation algorithm**: split `r` into `c` chunks,
tabulate all `2^{log m}` chunk-Lagrange values `eq̃(·, r_j)` into `c` write-once
memories, and answer each Lagrange evaluation with `c` memory reads. Integrity of the
reads is **offline memory checking** (Blum et al. [BEG+91], Claims 2–4):

- **Claim 2** [READ, lines 1031–1058]: the checker's multiset invariant
  `WS = RS ∪ S` holds iff every read returned the last write — **"Assuming that the
  domain of counts is F and that m … is smaller than the field characteristic |F|"**.
  Remark 2 gives the small-characteristic escape (multiplicative counters,
  `t ↦ t·g`, needing only `|F| > m`). ⚑ **This is a VALIDITY floor, not an error
  term** — at BabyBear (`char = p ≈ 2^31`) and our `2^21` row ceiling it holds with
  ~10 bits of headroom, but a Lean statement must carry it as a hypothesis, and
  nothing in the paper's error expression reminds you of it.
- **Claim 3**: well-formedness of the committed read-value columns `E_{r_x}` ⇔ the
  multiset equation, with `Remark 3` covering out-of-range addresses.
- **Claim 4** [READ, lines 1135–1140]: multiset equality via the public-coin hash
  `H_{τ,γ}(A) = Π_{(a,v,t)∈A} (h_γ(a,v,t) − τ)`, `h_γ(a,v,t) = a·γ² + v·γ + t`,
  soundness error **`O(|A|+|B|)/|F|` over the choice of `γ, τ`**. Note the tuple
  arity: **3** — address, value, count. (Same `R = 3` as every deployed LogUp xor
  relation; §2.1.)
- The multiset products are proven by **sumcheck-based grand products**
  ([Tha13 Prop. 2] / [SL20 §5–6]), `Õ(log m + log N)` rounds, an extra
  `O(m/log³ m)` committed elements.

The paper's own summary of the IOP soundness: **`O(m)/|F|`** (Spark, line 1156–1158);
threshold **`γ = O((m + N^{1/c})/|F|)`** for Surge (line 1644–1646).

⚑ **The headline strengthening**: Spartan assumed the `(row, col, val)` metadata was
committed honestly; Lasso proves Spark secure **with maliciously committed metadata,
with no modification** — that is what makes it a *standard* sparse PCS and what makes
the lookup application sound (the prover commits `dim_i` itself).

### 1.3 Decomposability — the load-bearing definition, verbatim

Eq. (14) [READ, lines 1508–1513], with `k ≥ 1`, `α = k·c` tables of size `N^{1/c}`
and an α-variate **multilinear** `g`, for every `r = (r₁,…,r_c)`:

    T[r] = g(T₁[r₁], …, T_k[r₁], T_{k+1}[r₂], …, T_{2k}[r₂], …, T_{α−k+1}[r_c], …, T_α[r_c])

plus (Jolt Def. 2.5/2.6) each `T̃ᵢ` evaluable in `O(log(N)/c)` time
("MLE-structured"). The low-degree extension `T̂(r) = g(T̃₁(r₁),…)` has degree ≤ `k`
per variable — decomposable ⇒ cheap *some*-degree extension, not necessarily the MLE.

Examples that carry Jolt: AND/XOR/OR via per-byte chunk tables with **`g` linear**
(`c = Σᵢ 2^{8i}·op(a′ᵢ,b′ᵢ)`, Eq. 1 of Jolt); EQ via `g = product` of per-chunk
equality tables; **LTU via `k = 2`** — `LTU = Σᵢ LTᵢ·Π_{j>i} EQⱼ`, two sub-tables per
chunk and a genuinely non-tensor `g` (Jolt Eq. 5). Range checks are the trivial
identity table.

### 1.4 Surge, the protocol (Fig. 5) [READ, lines 1565–1608]

Commit phase: `c` polynomials `dim₁,…,dim_c` (the chunk addresses of each lookup).
Proof phase: prover sends `E_i` (read values), `read_ts_i` (log m-variate),
`final_cts_i` (log N^{1/c}-variate) for each of the α memories. Then:

- **Primary sumcheck** on `h(k) = eq̃(r,k)·g(E₁(k),…,E_α(k))` — `log m` rounds, round
  degree **≤ α + 1** [READ, line 1637–1639], terminating in one query to each `E_i`.
- **Memory checking**: per memory, `H_{τ,γ}(WS) = H_{τ,γ}(RS)·H_{τ,γ}(S)` via grand
  products; terminal queries to `E_i, dim_i, read_ts_i, final_cts_i` — **and the
  verifier evaluates each `t̃ᵢ` on its own** (that is what SOS buys: no table
  commitment, tables of size `2^128` become fine).
- Prover commits `3αm + α·N^{1/c}` field elements, all "small" (in
  `{0,…,max(m, N^{1/c}, q)−1}`).

### 1.5 The soundness theorem, the way a Lean statement would read

Theorem 3 [READ, lines 1652–1658] plus the Eq.-(12) reduction, with every hypothesis
the paper leaves ambient surfaced as a binder. The shape (types from our tree;
`TableDecomposition`/`Decomposes` are landed, the rest is the honest obligation):

```lean
-- m = 2^lm lookups, table over c chunks of w bits (N = 2^(c·w)), α sub-tables
theorem lasso_sound
    {F} [Field F] [Fintype F] {c w α lm : ℕ}
    (D : TableDecomposition F c w α)                        -- LANDED (feef028)
    (T : (Fin c → Fin w → Bool) → F) (hD : Decomposes T D)  -- LANDED
    (hchar : 2 ^ lm < ringChar F)              -- ⚑ Claim 2's counter floor
    (a : (Fin lm → Bool) → F)                  -- the committed lookup vector
    (hbad : ¬ ∃ dim : (Fin lm → Bool) → (Fin c → Fin w → Bool),
        ∀ i, a i = T (dim i))                  -- no unit-row M explains a
    {prover : LassoAdaptiveProver F}           -- sees r, τ, γ, then challenges
    (hdeg : PrimaryRoundDegree prover ≤ α + 1) :
    uniformProb ((Fin lm → F) × (F × F) × SumcheckCoins)
        (LassoAccepts D a prover)
      ≤ (lm : ℝ) / |F|                          -- Eq (12), Schwartz–Zippel
        + (lm : ℝ) * (α + 1) / |F|              -- primary sumcheck
        + (α : ℝ) * (2 * (2^lm + 2^w) + 2) / |F| -- multiset hash, α memories (§4)
        + εGP + εPCS                            -- grand products; openings
```

and the **knowledge** form extracts `M` from `dim₁,…,dim_c` (row `i` is the unit
vector at the concatenated chunk address) — Theorem 3's statement is explicitly about
*knowing* such an `M`. Three hypotheses a Lean statement surfaces that the prose
keeps ambient: the `m < char F` floor; injectivity of the address embedding
`to-field` (our `binaryCubeIndexEquiv` — and note `logup_wrong_rational_accept_prob_le`
already demands the same `Function.Injective J` at the same proof step: **both
arguments live or die on "the table embedding separates rows"**); and the round-degree
cap on the adaptive prover, which our `adaptive_sumcheck_soundness` style already
makes explicit.

### 1.6 What the commitment scheme must supply — and the BaseFold verdict

What Lasso actually requires (§1.1 of the paper): **any multilinear PCS for DENSE
polynomials**, in `log m` and `log(N^{1/c})` variables. ⚑ **The sparse vector never
meets the PCS** — Spark's whole point is that sparsity is handled by the protocol,
and only dense columns (`dim_i, E_i, read_ts_i, final_cts_i`, all `2^{lm}` or `2^w`
entries) are committed. So the brief's worry "Lasso wants a multilinear PCS for the
sparse vectors" resolves as: *it wants a standard dense multilinear PCS, applied to
the dense representation*.

**Does our BaseFold RBR suffice?** In kind, yes; three named gaps [READ,
`notes/basefold-rbr.md`]:

| requirement | our state | gap |
|---|---|---|
| dense multilinear PCS, binding, value-unique | `MleEvalClaim` + `basefoldWord_injective` + `basefoldExactClaim_value_unique` — LANDED | none |
| **extractable** (paper Def. 2.3; the knowledge half of Thm 3) | RBR/FS instances landed with **`W = Unit`, extractor trivial** (`basefold-rbr.md` §3.1: "soundness with a trivial extractor, not extraction of the committed multilinear") | ⚑ real — same object as Spartan M5 |
| **many polynomials, batched openings** (`3α + 1` per instance; "in practice, these would be batched" — Fig. 5) | single-polynomial opening path; the batched-opening lane (`sumcheck-batched-opening.md`) is about the recursion backend, and its §0a obstruction — *the terminal `Ṽ(r)` claim needs a commitment that supports evaluation openings* — is precisely the seam here too | real; priced work, not new mathematics |
| additive homomorphism | **not required** — Lasso's own selling point vs Caulk/cq | none |

⚑ **And one advantage collapses**: Lasso's headline cost story — "all committed
elements are small, so MSM commitment is cheap" (§1.2 of the paper, Remark 1.2) — is
**denominated in multiexponentiation-land**. Under a hash-based PCS (BaseFold: LDE +
Merkle), committing a small element costs exactly what committing any element costs.
For us the honest cost of Lasso is the **count** `3αm + α·N^{1/c}`, with no
small-value discount. This does not break anything; it deletes the reason Lasso
looks an order of magnitude cheaper than LogUp-style alternatives in its own paper.

---

## 2. ⚑ The hash payoff, concretely (Q2) — and the 3.2× does not survive the unit change

The question `hash-landscape.md` §2 left as "the highest-value open measurement":
price a lookup-based Blake3 in blowup-cells against Poseidon2's 1,192; **under ~4,000
and the whole hash verdict flips.**

### 2.1 The design, read from a deployed system — not invented here

Stwo ships a lookup-arithmetized Blake2s/Blake3 AIR over M31 (31-bit prime, same
regime as BabyBear), read at source via `gh api`
(`starkware-libs/stwo`, `crates/examples/src/blake/{mod,round/constraints}.rs`)
[READ]:

- Words are **two 16-bit felts** (`N_FELTS_IN_U32 = 2`).
- **Five XOR tables**: 12/9/8/7/4-bit, each a `relation!(XorElementsW, 3)` — LogUp
  relations of **tuple arity 3** `(a, b, a⊕b)`, with expand parameters `(12,4) (9,2)
  (8,2) (7,2) (4,0)` folding tall tables into column blocks.
- **Additions are native field ops with VIRTUAL carries**: `add3_u32_unchecked`
  commits only the 2 result felts; the carry is the *expression*
  `(a.l + b.l + c.l − sl)·2^{−16}` constrained to `{0,1,2}` — zero committed carry
  cells.
- **Rotations**: by 16 — free relabel; by 12/8/7 — four `split_unchecked` cells
  (each commits one half) then two `xor2` calls routed to the `w` and `16−w` tables.
- LogUp aux: `finalize_logup_in_pairs()` — **2 fractions per QM31 accumulator
  entry** = 4 base cells per 2 lookups.

Per-round-row census, counted from `round/constraints.rs` [MEASURED]:

| item | cells | lookups |
|---|---:|---:|
| state in (16 words × 2 felts) | 32 | |
| message (16 × 2) | 32 | |
| per G: 2 add3 + 2 add2 (2 cells each) | 8 | |
| per G: 4 xor-rotr (4 split + 4 result cells; 4 lookups) | 32 | 16 |
| **8 G's** | **320** | **128** |
| round-relation yield (in/out/msg, 96 felts, 1 fraction) | | 1 |
| **main trace / round row** | **384** | **129** |
| interaction (⌈129/2⌉ × 4 base cells) | **260** | |
| **total / round row** | **644** | |

### 2.2 Blake3, priced in our unit

Blake3 = 7 rounds + a scheduler row (state/message chaining, ≈ 170 cells):

| arithmetization | cells/compression | ×blowup 4 | **R vs Poseidon2 (300 / 1,192)** |
|---|---:|---:|---:|
| bit-decomposed (`p3-blake3-air`, measured) | 9,168 | 36,672 | **30.6×** |
| **lookup/LogUp (Stwo design, counted)** | **≈ 4,680** | **≈ 18,700** | **≈ 15.7×** |
| flip bar (`hash-landscape.md` §2) | — | **< 4,000** | < 3.4× |

> ### ⚑ **The lookup arithmetization buys 1.96× on Blake3 — and lands 3.5–7.9× ABOVE the crossover band `R* = 2.0–4.5×`. The verdict does not flip. Poseidon2 stays correct wherever a layer is recursed over, under BOTH arithmetizations.**

My independent a-priori derivation (byte-chunked, before reading Stwo) came in at
5,500–7,100 cells — the same decade; Stwo is leaner chiefly because carries are
virtual and 16-bit limbs halve the value cells. [DERIVED, converging with READ]

**Table commitment, amortized** (the brief's "at what cost over how many hashes"):
multiplicity cells are per *table entry* — xor12: `2^24`, xor9: `2^18`, xor8: `2^16`,
xor7: `2^14`, xor4: `2^8` — **≈ 2^24.03 ≈ 17.1M cells, once per proof.** Against the
~4,500 cells/compression saved vs bit-decomposition, break-even at **≈ 3,800
compressions (~2^11.9)**; at 2^20 compressions the tables add +16 cells each; at 2^10
they add +16,700 and the lookup version LOSES outright. ⚠ And the 2^24-entry xor12
table cannot stand as one column at our deployed 2^21 row ceiling — it must split
into ≥ 8 column blocks exactly as Stwo's `(12,4)` expand does.

⚑ **And the LogUp field-size wall bites this design at our deployed parameters.**
`two-regime-calculator.md`: at BabyBear⁴ a LogUp cell clears 100 bits only if
`K·H·R ≤ 2^23.63`. This design is `K = 5` xor arguments at `R = 3`; at full `2^21`
height `K·H·R = 5·3·2^21 ≈ 2^24.9` → **≈ 98.7 bits, under the bar** without
lookup-phase grinding or Ext5. Not fatal (16 grind bits or Ext5's +30 clear it), but
it is a term the bit-decomposed AIR simply does not have, and any lookup-Blake3
proposal must carry it.

### 2.3 Keccak-f under lookups — the lever buys ≈ nothing [DERIVED]

Keccak is adds-free, pure bitwise, so the two things the lookup lever actually bought
Blake3 — native adds with virtual carries, and 16-bit value cells — buy nothing (θ, χ,
ι are XOR/AND at every bit; 24 of 25 lanes rotate by non-multiples of 8, forcing
splits; χ's 3-input table would be `2^24` tall and must split into two 2-input
lookups). Byte-limb census per round: ≈ 960 lookups, ≈ 1,350 value cells,
1,900–2,900 total with pair-batched aux → **55k–78k cells/permutation against 63,192
bit-decomposed: `R ≈ 180–260×` vs the measured 210.6×.** Lookup-arithmetized Keccak
in a 31-bit AIR is a wash to slightly negative. (Consistent in sign with gnark's
2.6× — but that was R1CS, where bit-blasting is far more penalized than in an AIR.)
This is a derivation, not a read design; no deployed lookup-Keccak AIR in a 31-bit
field was found to count. ⚠ Absence claim scoped to: `~/paperbin`, the eprint mirror,
Stwo's examples tree, and web search 2026-08-16.

### 2.4 ⚑ Why the 3.16× did not transfer — the unit forensics

Reinforced Concrete Table 1 (Poseidon 633 vs Blake2s 2,000 Plookup gates) is a ratio
of *gates in one TurboPlonk-style system*, and its **denominator is fat**: 633 gates
for a t=3, ~80-S-box Poseidon is **7.9 gates per S-box**, where our deployed AIR pays
**2.1 cells per S-box** (300 cells / 141 S-boxes). The numerator transfers fine — RC's
2,000 Blake2s gates ↔ Stwo's ≈ 6,600 cells for 10-round Blake2s is the same object at
2–3 cells/gate — but the Poseidon side is ≈ 3.7× leaner in our unit than in theirs.
`3.16 × 3.7 ≈ 12×` before rate corrections, ≈ 15.7× measured. **`R` is a property of
the arithmetization — hash-landscape's own lesson — and that cuts both ways: our
Poseidon2 AIR is already at the lookup-optimal end of ITS design space, so the lookup
lever has nothing left to claw back from the denominator.**

⚠ Caveats named: Blake2s ≠ Blake3 (RC row); the Stwo count is Blake2s-configured with
`N_ROUNDS` a knob ("Change these for blake3" [READ]) and my ×7 is that knob turned;
scheduler estimated at ±100 cells; interaction-column width assumes QM31/ext-4 (ours
is BabyBear-ext4, same width). None of these moves the verdict's decade.

### 2.5 What this rules IN — the relation to Lasso proper

The Stwo/AIR design **is** Lasso's decomposition with the combining polynomial
consumed as a CONSTRAINT: the 32-bit XOR "virtual table" of size 2^64 is decomposed
into 8/12-bit sub-tables (Eq. 14 with `g` linear), and `g` is enforced by the
recombination constraint on committed chunk cells rather than by Surge's sumcheck.
Both routes rest on the identical identity — the one `DecomposableTable.lean` now
states. Lasso-proper differs by *virtualizing the result*: only chunk reads and
counters are committed, `g` rides the sumcheck, and the table itself needs **no
multiplicity commitment at all when MLE-structured** (the verifier evaluates `t̃ᵢ`).
That kills §2.2's 17.1M amortized cells — at the price of §4's sumcheck/memory terms
and the `3αm` committed read/counter columns, which for hashing workloads
(`m ≈ 10²–10³ lookups per compression) is the worse trade. **For the hash problem,
the AIR-LogUp consumption of the identity is the right one; for the sparse-matrix
problem (§3), the sumcheck consumption is.** One identity, two consumers — which is
the actual sense of the brief's "second instance of the same machinery."

(Also re-verified: `p3-lookup` at our pinned rev `82cfad7` is a LogUp gadget with a
running-sum auxiliary column per lookup bus — `lookup/src/logup.rs:51` "a running sum
auxiliary column `s`" [READ] — so everything above is expressible on machinery we
already vendor. And Binius64's "byte tables" remain a prover algorithm, not a lookup
argument — `spartan-over-what-we-hold.md` §3.1's finding stands; this note is the
actual-lookup version.)

---

## 3. The Spartan payoff (Q3) — SPARK-via-Lasso vs `ñext`, two columns, no winner declared

First the subsumption question asked plainly: **does Lasso's sparse-eval subsume the
SPARK gap? Yes, definitionally** — Spark *is* Spartan's sparse commitment; Lasso §4
re-proves it with malicious metadata and §5 generalizes it to Surge. And the thesis
"sparse eval IS lookups into decomposable tables" is literal: the Spark table
(entry `j` = `χ_j(ρ)`) is the tensor of `c` chunk-Lagrange tables with `g = product`
— landed as `spark_table_decomposes`. So building the lookup argument builds SPARK,
and vice versa; **one gap, not two.**

| | **SPARK / Lasso route** | **`ñext` / uniformity route** (CCS §5.1) |
|---|---|---|
| settles `Ã(r_x, r_y)` for | **arbitrary** R1CS/CCS matrices | uniform (AIR-shaped) systems only |
| new committed objects | `3αm + α·N^{1/c}` (dim, E, read_ts, final_cts) + their openings | **zero** |
| new error terms | §4's full stack: `(α+1)·log m` sumcheck + α multiset terms + grand products | **none** — verifier evaluates a closed form; IOP unchanged (byte-identical checks, [READ] in spartan note §3.2) |
| validity preconditions | `m < char F` counter floor (or multiplicative counters) | none |
| trust model | none extra — that is the paper's headline strengthening | *removes* the indexer-honesty footnote-10 assumption |
| prerequisites in our tree | `LogupStar` + `BinaryLookup` + `LogupIndexLink` + `DecomposableTable` (landed) + `[LASSO-PRIMARY-SUMCHECK]`, `[LASSO-COUNTER-LAYER]`, `[LASSO-CHUNK-LINK]` | a trace/row/transition notion (`Compiler/Air.lean` has none — real, named prerequisite) + the `ñext` closed-form lemma |
| verifier cost | `O(log)` queries + openings | `O(log D)` field ops, no openings |
| dual use | **the same build serves hash lookups (§2) and any future range-check/bytewise op** | none — structure evaluation only |
| formal difficulty | memory-checking soundness (Claim 2's induction) + grand-product GKR: genuinely new proofs | a `rfl`-flavoured closed-form identity + zero probability theory |

**The two-column reading:** `ñext` remains the cheapest path to a machine-checked
succinct Spartan (the spartan note's M2 verdict survives this deeper look). The Lasso
route's case was always the dual use — and §2 just measured the dual use's flagship
application (hash lookups) as NOT crossing its own bar. What remains on the Lasso
side of the ledger: non-uniform constraint systems (if we ever need them), range
checks and byte ops in zkML quantization (real, unpriced here), and the fact that
`DecomposableTable` + LogupStar means the identity layer is no longer part of the
cost — only the counter layer and the degree-`(α+1)` realizer are.

---

## 4. ⚑ The composition question (Q4) — the full error expression, and what shape it has

### 4.1 The expression

Surge over α memories of size `M = N^{1/c} = 2^w`, `m = 2^{lm}` lookups, one
`(τ, γ)` draw shared across memories (Fig. 5 does this), grand products per
[Tha13 Prop. 2]:

```
ε_Lasso ≤   lm / |F|                                   (E1: Eq-(12) zero-test, SZ)
          + lm · (α + 1) / |F|                          (E2: primary sumcheck,
                                                            round degree ≤ α+1)
          + α · 2·(m + M + 1) / |F|                     (E3: multiset hash, per memory:
                                                            |WS| = |RS ∪ S| = m + M,
                                                            each factor h_γ(·) − τ has
                                                            total degree 2 in (γ,τ);
                                                            bivariate SZ on the product
                                                            difference)
          + α · 3 · (log²m + log²M) / 2 / |F|           (E4: grand-product GKR
                                                            sumchecks, degree-3 rounds
                                                            over ~log² tree layers)
          + (3α + c + 1) · ε_open                       (E5: PCS openings — dim_i, E_i,
                                                            read_ts_i, final_cts_i, ã)
   SUBJECT TO   m < char F                              (V1: counter floor, Claim 2 —
                                                            a PRECONDITION, not a term;
                                                            Remark-2 variant needs |F| > m)
```

E3 is my sharpening of the paper's `O(|A|+|B|)/|F|`: the fingerprint identity is a
polynomial identity in `(γ, τ)` — products of `m + M` irreducible-in-τ factors of
total degree 2 — distinct multisets give distinct polynomials (unique factorization),
so bivariate Schwartz–Zippel prices it at `≤ 2(m + M)/|F|` per memory, `+1`-ish slack
for the pairing of the two sides. [DERIVED; the paper states only the O(·).]

### 4.2 ⚑ The shape verdict — what the two-regime calculator needs

**Every term E1–E4 is a polynomial root count over `|F|`.** No term carries a
decoding radius, a proximity parameter, or a `θ` — the decomposition layer adds
**nothing to the query wall and everything to the LogUp/field wall.**
`logup_carries_no_regime` extends unchanged over the entire stack: a `Regime`
argument would be a type error for every one of these terms, exactly as it is for
`logupErr`.

What the calculator (`TwoRegimeQueryBudget.lean`) can already price: E3 is literally
a `LogUpCfg` instance — `K = α` arguments, `H = m + M` rows, **`R = 3`** (the
Claim-4 tuple arity is the same 3 as every deployed xor relation). What it cannot
yet price, and the two knobs to grow: **sumcheck legs** (rounds × degree: E2's
`lm·(α+1)` and E4's GKR product) — ℚ-exact, regime-free, same `k/|F|` family; and
**the V1 precondition** as a hypothesis field, not a summand (the honest way to keep
"documented ≠ detected" from recurring here: a config with `m ≥ char F` must refuse
to price, not price optimistically).

### 4.3 The LogUp-instantiated variant — what WE would actually build

Modern instantiations (and any build on our tree) replace Claim-4 grand products
with the logarithmic-derivative multiset check. Then E3 + E4 are replaced by exactly
the objects `LogupStar` proves: per memory, defect-polynomial root count
`(|ι|−1)/|F|` **plus the pole term `|ι|/|F|`** (`logup_wrong_or_pole_prob_le` —
poles counted, not excluded), with `logupPushforward` playing `final_cts` (the
multiplicity object) and **timestamps deleted** — which is why the modern shape is
cheaper: no `read_ts`, no `2m` counter cells, no grand products. The residual
obligations are then precisely the file's named pair — `[LOGUP-PULLBACK-SOUND]` and
the c-fold `[LOGUP-ADDRESS-LINK]` = `[LASSO-CHUNK-LINK]` — plus E2. **The V1 floor
changes form but does not vanish**: the log-derivative check needs the multiplicity
encoding to be non-cancelling, which in char 2 is the exact trap
`boolean_sum_one_not_oneHot_charTwo` already exhibits and `LogupStar`'s docblock
already names (unindexed multiset + unit multiplicities: `1 + 1 = 0`). One floor,
two costumes: counters wrap in small characteristic, multiplicities cancel in
characteristic two.

---

## 5. The Lean-statable core (Q5) — landed

`minidregg@feef028`, `Selvage/DecomposableTable.lean` (438 lines with the
`Selvage.lean` registration), `lake build Selvage` green **(3097 jobs — the
umbrella, per the twin lesson, not just the file)**, import boundary OK, proof
hygiene PASS (476 files), six `#print axioms` pins at
`[propext, Classical.choice, Quot.sound]`. [BUILT]

**Twin discipline, checked before writing** [MEASURED]: grep over
`Selvage/ Assurance/ Theory/ Compiler/` for `Lasso|Surge|decomposab|SOS` — zero
declarations (only `BinaryLookup`'s docblock mentions Lasso by name). Nothing that
`BinaryLookup`, `LogupStar`, `LogupIndexLink` or the `Tower256Logup*` deployment
profiles carry is re-declared; the bridge theorem *consumes*
`binaryTableDot_lookupEq_cubePt` rather than restating it.

### What it states

- **`TableDecomposition F c w α`** — sub-tables, a chunk map (Lasso's block layout
  `lassoBlockChunk`/`ofBlocks` is the canonical instance), and **the combining
  polynomial as its cube table**: `g := mle gTable`, so multilinearity — Jolt
  Def. 2.6's requirement — is structural, never a hypothesis.
  `Decomposes T D : ∀ r, T r = mle D.gTable (D.readsAt r)` is Eq. (14) verbatim;
  `extension` is the verifier's `O(α·w)` closed form, `extension_agrees` ties it to
  the cube.
- **`spark_table_decomposes`** — Spark's χ-tensor table decomposes with
  `g = product` (via `mle_prodTable`, itself via the landed `multiAffine_eq_mle`
  uniqueness): *sparse evaluation is a decomposable lookup*, as a theorem.
- **`interleavedEq_decomposes`** (k = 1, every chunk count, general proof) and
  **`LtuExample.ltu_decomposes`** (k = 2, `g = LT_hi + EQ_hi·LT_lo`, kernel
  `decide` over ZMod 5) — the two canonical Jolt shapes, exercising both the tensor
  and the non-tensor `g`.
- **`TableDecomposition.combined_by_chi`** — every sub-table read IS the
  `binaryTableDot`/`binaryLookupEq` object the LogUp family prices. The
  decomposition layer is a second instance of landed machinery, in the type system
  and not just in prose.

### Teeth — both directions, and the refutation is a general theorem, not a `decide`

- **SATISFIABLE**: the three instances above, on real Jolt/Spark shapes.
- **REFUTABLE**: `splitEq_not_decomposable` — the SAME equality function under the
  split chunking (all of `x` in one chunk, all of `y` in the other) admits **no**
  decomposition with one sub-table per chunk, **over every field**. The engine
  (`no_multilinear_eq_factoring`): a multilinear `g` is affine per coordinate
  (`mle_multilinear`), and an affine map with two distinct roots is identically
  zero — it cannot thread the identity matrix's four distinct rows through one
  field coordinate. All four chunk-map cases handled (two degenerate, identity,
  swap). Per GUARD-DISCIPLINE this is the general fact proved, not one instance
  guarded.
- **`splitEq_transpose`** completes the pincer: the refused table is the accepted
  table up to transposing the chunking — **decomposability is a property of the
  (function, chunking, α) triple**, which is the sharpest one-line statement of
  what Lasso's "structured" actually means.
- **`SurgeReadOracle`** names the read-integrity obligation
  (`Accepts a x v → v = mle (subTable a) x`) and
  `surgeReadOracle_all_accepting_refuted` proves the all-accepting oracle
  falsifies it — the obligation cannot quietly read as `True`
  (`sparseEvalOracle_refutable`'s precedent, same reason).

### Honest obligations — named in the file, not built

- **`[LASSO-PRIMARY-SUMCHECK]`** — the degree-`(α+1)` honest-prover realizer for
  `eq·g(E₁,…,E_α)`. The engine (`adaptive_sumcheck_soundness`) carries `d`
  symbolically, so this is one realizer, zero new probability theory — but it is
  not built beyond the landed degree-2/3 rungs.
- **`[LASSO-COUNTER-LAYER]`** — multiset/read integrity (E3+E4 of §4, or the LogUp
  form of §4.3), including the `m < char F` floor as a hypothesis.
- **`[LASSO-CHUNK-LINK]`** — `dim_i` decodes the canonical chunking; the c-fold
  `[LOGUP-ADDRESS-LINK]`.

---

## 6. Corrections and hand-offs to sibling notes

1. ⚑ **`hash-landscape.md` §2's lookup pointer is now answered, negatively.** "Price
   a lookup-based Blake3 AIR in our unit … under ~4,000 and this entire verdict
   flips" → **≈ 18,700 blowup-cells [MEASURED off a deployed design]; no flip; the
   Poseidon2-where-recursed verdict stands under both arithmetizations.** The
   `R ≈ 3.2×` Plookup figure does not survive the unit change (§2.4) — its Poseidon
   denominator is 3.7× fatter per S-box than our AIR's. Recommend hash-landscape's
   item 4 be marked RESOLVED with this pointer.
2. **`spartan-over-what-we-hold.md` M2**: unchanged verdict, sharpened ledger — the
   SPARK gap and a lookup argument are ONE build (Surge IS Spark), the identity
   layer of that build is now landed and free, and the remaining cost is the counter
   layer + one sumcheck realizer. `ñext` still wins for our uniform case.
3. **`two-regime-calculator.md`**: Lasso's E3 is a `LogUpCfg` with `K = α`,
   `H = m + M`, `R = 3`; the calculator needs a sumcheck-leg knob (`rounds × degree`)
   and a validity-precondition field for `m < char F` before it can price a full
   Lasso stack. No `Regime` parameter is needed anywhere — that is a theorem-shaped
   fact, not an omission.
4. ⚠ For any future lookup-Blake3 proposal at our stack: carry §2.2's three riders —
   the 2^24-cell table amortization (break-even ~2^12 compressions), the row-ceiling
   column-splitting, and the `K·H·R` check that lands at ≈ 98.7 bits at BabyBear⁴
   full height without grinding.

### Corpus disclosure

Primary sources read in full or at cited lines: eprint 2023/1216, 2023/1217 (both in
`~/paperbin` with full text), Stwo `crates/examples/src/blake/*` at `dev` HEAD
2026-08-16 via `gh api`, `p3-lookup` at pinned rev `82cfad7`. The Keccak §2.3 figure
is a derivation, and its "no deployed lookup-Keccak-AIR found" is an absence claim
scoped to the instruments named there — the eprint mirror is cryptology-only and the
grey-literature blindness recorded in PREFLIGHT applies.
