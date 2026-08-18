# GSR (eprint 2026/1692) vs. our deployed Poseidon2 — does the partial-layer attack reach us?

**Paper**: Bhati, Tariq, Ashur (3MI Labs / COSIC), *"From Round Skipping to S-Box Skipping:
Attacking Poseidon's Partial Layer via Subspace Restriction"*, eprint **2026/1692**.
Local: `~/paperbin/gsr-sbox-skipping-poseidon-2026-1692.pdf` (+ `.txt`, already extracted —
no `pdftotext` needed). Disclosed to the Ethereum Foundation before publication; EF grant
FY26-2457.

**Read 2026-08-18.** Everything below is either quoted from the paper, read from our source,
or computed here (scripts named inline). Nothing is assumed from reference parameter sets.

---

## VERDICT IN ONE PARAGRAPH

**GSR applies to our deployed Poseidon2 in full — verified by direct computation on the
deployed internal-matrix constants, not by analogy.** The gadget needs only that the partial
layer be an *invertible linear map* whose Krylov space at `e_0` is large enough; Poseidon2's
`J + diag(V)` internal layer has **full Krylov dimension 16**, so every one of GSR's
constraints is independent. The MDS property is not used anywhere in the gadget, and neither
is branch number. **Our whole internal layer linearizes**: at `t=16, k=1` the gadget absorbs
`t−2k = 14` partial rounds and we only have **13**, so GSR eats **100% of the partial layer
plus one full round, with a degree of freedom to spare** — a strictly worse position than the
paper's own target, which retains one unskipped partial round. What saves us is **α = 7, not
Poseidon2**: the residual degree grows as `7^r` instead of `3^r`, and the attack stops at the
three initial full rounds GSR structurally cannot reach. Net: **CICO-1 on 18 of our 21 rounds
at ≈2^27.4 (practical, seconds)**; CICO-2 on 18/21 at ≈2^61.1 against a 2^62 generic bound —
about one bit, i.e. not a meaningful break. **The full 21-round permutation does not fall, and
the sponge's 124-bit collision claim is untouched because it lives at CICO-8, where GSR is
identically vacuous (`t−2k = 0`).** The margin is **3 of 21 rounds (14%) and it is a CEILING**.
The repair is embarrassingly cheap: **`R_P` 13 → 15 kills the practical CICO-1 attack outright
for +1.4% in-circuit cost.**

---

## 1 ⚑ Does GSR apply to Poseidon2's internal layer? — YES, verified by computation

### 1a. What the paper actually claims about Poseidon2 — the exact quotes

**The authors never analyze Poseidon2.** They are aware of it and cite it three times, all in
passing. The complete set of Poseidon2 mentions in the paper:

- §1, line 40 — *"Ashur, Buschman, and Mahzoun [3] refined the Gröbner bases complexity bounds
  for both Poseidon and Poseidon2. Subsequently, Grassi, Koschatko, and Rechberger [13] refined
  Gröbner basis attacks using finite subspace trails to linearize some partial rounds of fixed
  Poseidon, **Poseidon2**, and Neptune instances."*
- §1, line 45 — *"Reduced-round Poseidon and **Poseidon2** bounty challenges were solved using
  resultants and univariate root finding [5]."*
- References [3] and [5] only.

The scope claim is the abstract's, and it is about **Poseidon**, phrased structurally:

> *"Crucially, since the subspace restriction approach is tuned only by `t` and `k`, our results
> apply to the Poseidon structure regardless of the choice of round constants, MDS matrix,
> S-box exponent α, or field size p."*

and §8 — *"GSR exposes a critical vulnerability in the partial layer of Poseidon **(and related
AO ciphers)**, emphasizing the need for a rigorous reevaluation of its algebraic security
margins."*

**So the paper does not answer Q1. It has to be answered structurally.** It also contains
**no countermeasures section** — §8 asks for reevaluation and proposes nothing.

### 1b. The gadget's actual requirement, quoted

This is the load-bearing text, §5.2 *Forward Linearization of the Partial Round S-Boxes*:

> *"For each of the first `t − 2k` partial rounds, let `δ^(r) ∈ F_p` be an arbitrary constant
> chosen by the attacker. We constrain the input to the single active S-box at index 0 to equal
> `δ^(r)`:*
>
> `(S^(r) + C^(r))[0] = δ^(r)`.
>
> *Consequently, the S-box output is deterministically the field element `(δ^(r))^α`. The
> transition to round `r + 1` is given by the affine mapping:*
>
> `S^(r+1) = M · ( S^(r) + C^(r) − δ^(r)·e_0 + (δ^(r))^α·e_0 )`
>
> *where `e_0` is the standard basis vector and `M` is the MDS matrix that satisfies the three
> criteria given in [14]. **Because the mapping is affine**, every state `S^(r)` with
> `1 ≤ r ≤ t − 2k` remains an affine combination of the variables in `X_1`. Enforcing this
> condition for `t − 2k` consecutive partial rounds generates exactly `t − 2k` strictly linear
> constraints on `X_1`."*

and §5.3, the backward step, which is the only other place `M` appears:

> *"Tracing backward, the state before the first MDS matrix is `M^{-1} X_1`. […] To enforce the
> constraint `S_in[j] = 0` for `k` indices, we require: `(M^{-1} X_1)[j] = (C^(0)[j])^α`.
> Evaluating the known constant `(C^(0)[j])^α` circumvents the non-linear compositional inverse
> power map `x^{1/α}` of the S-box. This yields exactly `k` more strictly linear equations."*

**Read what is used and what is not.** The justification is *"because the mapping is affine"* —
a property of `M` being **linear**, full stop. §5.3 additionally needs `M` **invertible**. The
phrase *"the MDS matrix that satisfies the three criteria in [14]"* is describing the object in
Poseidon; **no MDS property, no branch number, and no round-constant property is ever invoked.**
The paper says so itself in the abstract (*"independent to the rounds-constants and MDS matrix
selection"*) and again in §5: *"we make the skipping free of these parameters."*

**There is exactly one hidden requirement the paper does not state**, and it is the one that
decides Q1. The `t − 2k` constraints are the linear functionals

```
ℓ_r(X₁) = e₀ᵀ M_I^{r−1} X₁ = const,     r = 1 … t−2k
```

(coordinate 0 of the state before each partial round). The paper asserts these are *"exactly
`t − 2k` strictly linear constraints"* — i.e. **independent**. That holds iff

```
dim Krylov(M_Iᵀ, e₀)  ≥  t − 2k
```

For a generic MDS this is automatic and invisible, which is why the paper never mentions it.
**For Poseidon2's sparse, deliberately-non-MDS internal matrix it is a real question.**

### 1c. The answer, computed on the deployed constants

Our internal layer is `M_I = J + diag(V)` — all-ones plus a diagonal — read from source
(`/Users/ember/dev/breadstuffs/circuit/src/poseidon2.rs:90-109`, twinned in Lean at
`/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean:99-124`):

```
V = [−2, 1, 2, ½, 3, 4, −½, −3, −4, 2⁻⁸, ¼, ⅛, 2⁻²⁷, −2⁻⁸, −1/16, −2⁻²⁷]
x_i' = sum(x) + V[i]·x_i
```

Note `J + diag(V)` is **symmetric**, so `M_Iᵀ = M_I`. Krylov dimension computed over
F_2013265921 at the actual deployed residues
(script: `…/scratchpad/krylov.py`):

| instance | `t` | `dim Krylov(M_I, e₀)` | needed at k=1 | needed at k=2 | verdict |
|---|---|---|---|---|---|
| **BabyBear w16 (DEPLOYED)** | 16 | **16 — FULL** | 14 | 12 | **independent; gadget applies in full** |
| BabyBear w24 (segment-digest sponge) | 24 | **24 — FULL** | 22 | 20 | **independent; gadget applies in full** |

**⚑ The reason is not bad luck — it is Poseidon2's own design criterion.** Poseidon2 requires
`M_I` to admit **no nontrivial invariant subspace** (Grassi–Rechberger–Schofnegger, ToSC 2021 —
the paper's own reference [14], titled *"Proving resistance against infinitely long subspace
trails: How to choose the linear layer"*). *No invariant subspace containing `e₀`* is precisely
*full Krylov space at `e₀`*, which is precisely *GSR's constraints are independent*. **The
criterion that defends Poseidon2 against subspace trails is the criterion that makes GSR
well-conditioned.** There is no escape through matrix structure: a matrix that defeated GSR by
constraint collapse would be broken by classical subspace trails instead.

CheapLunch reaches the same identity from the other side (2025/2040, p. 22): *"The case
`ℓ > (t − 2k)` corresponds to the case where a nontrivial invariant subspace exists for `M_I`,
which is avoided in the new Poseidon instances."* GSR's contribution is achieving `ℓ = t − 2k`
for **any** `M_I` by fixing the S-box input to an arbitrary `δ` (an *affine* restriction) rather
than to zero (a *linear* subspace trail requiring special structure).

### 1d. On "branch 2" — orthogonal, and the source claim needs correcting

The brief cited `notes/ring-hash-design.md:326` as having **measured** Poseidon2's internal
layer at branch 2, with the worry that low branch might make us *more* exposed.

**Two corrections.**

1. **Branch number is irrelevant to GSR.** Branch number is a *differential/statistical*
   property. GSR uses only linearity, invertibility and Krylov rank. A branch-2 layer and a
   branch-17 layer are equally exposed. Low branch neither helps nor hurts here.
2. ⚠ **`ring-hash-design.md:326` is not a measurement.** The word "measured" does not appear;
   the line is a *precedent/framing* assertion (*"Poseidon2's internal rounds use I + diag(v),
   branch 2 — weaker than our support-3"*), sourced from a script docstring
   (`ring-hash-scripts/design_mds_interleave.py:27-31`) whose measured tables are all about the
   σ-layer, not about Poseidon2. It is currently load-bearing in **five** downstream notes
   (`aligned-hash-space.md:303`, `k16-proof-and-weft.md:179`, `hash-landscape.md:1344`,
   `docs/VERDICTS.md:859`, `weft2.md:88`). The claim is very likely true, but it is **an
   unmeasured line cited as measured in five places** — worth an hour to either measure or
   relabel.

---

## 2. Our numbers under their formula

### 2a. Our parameters, read from source (not assumed)

Unanimous across nine independent transcriptions — Lean, Rust, Go, TypeScript, WGSL, seL4, and
the emitted descriptor JSON. **No disagreement anywhere.**

| | value | source |
|---|---|---|
| field | BabyBear, `p = 2³¹ − 2²⁷ + 1 = 2013265921` | `Poseidon2Binding.lean:136`, `#guard` :147 |
| `t` (width) | **16** | `circuit/src/poseidon2.rs:20`, `Poseidon2RoundGates.lean:101` |
| `α` | **7** | `circuit/src/poseidon2.rs:32` (`SBOX_ALPHA`), `Poseidon2RoundGates.lean:116` |
| `R_F` | **8** = 4 initial + 4 final | `circuit/src/poseidon2.rs:24`, `Poseidon2Binding.lean:141` |
| `R_P` | **13** | `circuit/src/poseidon2.rs:27`, `Poseidon2Binding.lean:142`, `#guard` :151 |
| total | **21** | `#guard TOTAL_ROUNDS == 21` (`Poseidon2RoundGates.lean`) |

Corroborated independently by round-constant array lengths (`RC_INTERNAL: [u32; 13]`,
`RC_EXT_INIT: [[u32;16];4]`) and by the round-index split
`#guard (List.range 21).filter isExternalRound == [0,1,2,3,17,18,19,20]`.

**Two other Poseidon2 instances exist in the tree** and are covered in §4c.

### 2b. Model validation — the calculator reproduces Table 1 exactly

Before applying their formula to us, it reproduces theirs. Script: `…/scratchpad/gsr_calc.py`.
Degree `d = α^(max(0, R_P − (t−2k)) + R_f1)`; SyCZ nests `k−1` Sylvester resultants to degree
`d^(2^(k−1))`, then Cantor–Zassenhaus at `O(D² log p)` time / `O(D log p)` memory.

| paper row | our model | paper Table 1 |
|---|---|---|
| CICO-1 (1,23,4) | 2^20.8 / 2^12.9 | 2^20.8 / 2^12.9 ✓ |
| CICO-2 (1,23,4) | 2^49.3 / 2^27.1 | 2^49.3 / 2^27.1 ✓ |
| CICO-2 (1,20,4) | 2^30.3 / 2^17.6 | 2^30.3 / 2^17.6 ✓ |
| CICO-3 (1,18,4) | 2^55.7 / 2^30.3 | 2^55.7 / 2^30.3 ✓ |
| CICO-4 (1,16,4) | 2^106.4 / 2^55.7 | 2^106.4 / 2^55.7 ✓ |

**5/5 exact.** The model is theirs, not a reconstruction.

### 2c. ⚑ How many of OUR rounds fall

**The structural fact first, because it is worse than the paper's own target.** GSR absorbs
`t − 2k` partial rounds. At `t=16, k=1` that is **14**. We have **13**.

> **`t − 2k = 14 > R_P = 13`. Our entire internal layer fits inside the gadget, with one degree
> of freedom left over.** The paper's own KoalaBear target (`t=24`, `R_P=23`, `t−2k=22`) retains
> one unskipped partial round. **We retain zero.**

This is not incidental — it is Poseidon2's design point turning against it. Poseidon2 reduced
the partial-round count relative to Poseidon (partial rounds are cheap, so you would think more
is free) and landed at `R_P = 13` for `t = 16`, which sits **below** the `t − 2k` absorption
threshold.

Applying their formula at `(BabyBear, t=16, α=7, R_F=8, R_P=13)`:

| | rounds attacked | partial skipped | residual degree | time | memory | generic bound | verdict |
|---|---|---|---|---|---|---|---|
| **CICO-1** | **18 of 21** | **13/13 (all)** | `7⁴ = 2401 = 2^11.2` | **2^27.4** | 2^16.2 | 2^31 | **PRACTICAL** — seconds |
| **CICO-2** | **18 of 21** | 12/13 | `7⁵ = 16807 = 2^14.0` | **2^61.1** | 2^33.0 | 2^62 | ~1 bit — **not meaningful** |
| CICO-3 | 18 of 21 | 10/13 | `7⁷ = 2^19.7` | 2^162.2 | 2^83.6 | 2^93 | **no gain** |
| CICO-≥4 | — | — | — | — | — | — | **no gain** |

**⚑ α = 7 is doing all the work.** The comparison that isolates it: at `t=24` the paper gets
2^20.8 with α=3; our `t=16, α=7` gives 2^27.4 for a structurally *deeper* skip. This matches
`poseidon2-audit-verdict.md:45-48`, which already found α=7 to be the dominant safety factor
("KoalaBear (α=3) roughly HALVES the margin") — **an independent instrument agreeing here.**

**The distinguisher.** §6.1's probability-1 distinguisher covers `t − 2k + 1` rounds — for us
**15 of 21 rounds at k=1**, degree exactly 1. The paper calls its 23-round version *"the longest
distinguisher found for Poseidon"*, with a footnote that Antonio Sanso had independently found a
similar one *"a couple of months earlier but did not pursue it on account of the distinguisher
being 'not interesting'."*

---

## 3. The margin — stated as floor-or-ceiling

**Margin = 3 of 21 rounds (14%).**

**It is a CEILING, and this is the important half of the sentence.** GSR is a *lower bound on
adversarial reach*: it is what one team achieved and published, and every paper in this exact
lineage has pushed reach up and never down —

```
Bariant–Bouvier–Leurent–Perrin 2022   2 initial full rounds
Grassi–Koschatko–Rechberger 2025      + some partial rounds, needs invariant subspace
Sanso–Vitto 2026/1254                 first 2 partial rounds (α=3, t=16)
Vitto 2026/1579 (Slipway)             18 of 28, but needs an RC-dependent MDS
GSR 2026/1692 (this)                  1 full + t−2k partial, ANY matrix, ANY k
```

So `3` is *at most* what we have, and the next paper may take it. Contrast the **τ=2 integral
floor of 24** (`docs/VERDICTS.md:944-957`), which is a **FLOOR**: a *proved lower bound on the
rounds needed*, which future work can only push **up**. **The two are opposite species and must
never be summed or compared as if commensurable.**

**Where the 3 rounds live matters more than the number.** They are the **3 initial full rounds
that GSR structurally cannot reach**, because §5.3's backward step inverts exactly one S-box
layer (it dodges `x^{1/α}` by pushing the CICO constraint through a *known constant* `C⁽⁰⁾[j]`;
that trick works once and only once). Consequently:

> **⚑ Our margin against GSR is set entirely by `R_F/2 − 1`, and `R_P` contributes nothing to it
> at the current round count.** The paper's KoalaBear target has the same 3-round margin
> (31 − 28) for the same reason. Two very different parameter sets, identical margin, because the
> margin is a property of `R_f0` alone.

⚠ **Do not read "3 rounds" as "14% margin, comparable to Poseidon2's stated 7.5%".** The
published Poseidon/Poseidon2 margin is a *round count added arbitrarily* — 2019/458 §3,
verbatim: *"we **arbitrarily** decided to add: two more rounds with full S-Box layers (+2 R_F);
7.5% more rounds with partial S-Box layers"* — and `hash-landscape.md:499-513` already records
that **neither Poseidon nor Poseidon2 ever states a security margin in bits at any α**. GSR does
not change that; it makes the absence sharper.

---

## 4. Does this reach our other designs?

### 4a. σ-Poseidon (ring-hash candidate) — reached, but **dominated by the τ=2 floor**

σ-Poseidon parameters (`notes/ring-hash-design.md`): `R_q = Z_q[X]/(X^16+1)`, `d = 16`,
**`t = 9` ring elements** (a width-144 SPN in `Z_q` coordinates), sponge rate 8, capacity 1,
**α = 7**, **`R_F = 8`, `R_P = 22`, 30 rounds** — round counts explicitly flagged as *"borrowed
(a width-~12 prime-field Poseidon set) and underived for either regime"*
(`ring-hash-design.md:437-439`). Partial layer = support-3 σ-set `{1, σ₅, σ₋₁}`, slot-branch 4.

**GSR's structural reach, which is solver-independent.** Each partial round's S-box input is one
*ring* element = 16 `Z_q` coordinates, so fixing it costs 16 of the 144 scalar DoF. CICO-k in
ring units consumes `16k` at input and `16k` at output, leaving `(144 − 32k)/16 = 9 − 2k`
partial rounds absorbable. **This is `t − 2k` with `t = 9`, exactly as the paper's formula
predicts once `t` is counted in ring elements.**

| | Poseidon2 w16 (deployed) | σ-Poseidon |
|---|---|---|
| `t` | 16 | 9 (ring elements) |
| `R_P` | 13 | 22 |
| GSR absorbs (k=1) | `min(13, 14) = ` **13 partial** | `min(22, 7) = ` **7 partial** |
| **fraction of partial layer linearized** | **13/13 = 100%** | **7/22 = 32%** |
| rounds linearized (1 full + partial) | **14 of 21 = 67%** | **8 of 30 = 27%** |

**⚑ σ-Poseidon is structurally far more resistant to GSR than our deployed Poseidon2 is** — the
opposite of the brief's worry. The reason is the ratio `R_P / t`: σ-Poseidon's 22 partial rounds
against `t = 9` puts `R_P` well *above* the `t − 2k` threshold, where ours sits *below* it.

**Does it compound with the τ=2 integral floor of 24? — No.** The τ=2 integral distinguisher
reaches **round 24** of 30 (`VERDICTS.md:944`, `ring-hash-design.md:698-716`). GSR's linearized
block is **8 rounds**. The integral result **strictly dominates** GSR on this candidate at every
`k`. σ-Poseidon's binding constraint remains what it was yesterday: *"the §4.4 round-count
derivation is now the BINDING open item"*. **GSR does not move the σ-Poseidon verdict and does
not add to its debt.**

⚠ **NAMED OPEN ITEM, and it is transmutable, not terminal.** I priced GSR's *structural reach*
on σ-Poseidon (8 rounds — solid, it follows from DoF counting alone). I did **not** price the
*residual solve*, because the free variables are ring elements, not scalars, and neither
Cantor–Zassenhaus nor the Sylvester resultant applies directly over `R_q`; at τ=2 the ring
splits into 8 copies of `F_{q²}` permuted by σ₅, which needs its own analysis. **This is a
runnable check, not a fact about the world** — the DoF/Krylov half is a 20-line script against
the σ-layer matrix (same shape as `krylov.py` here), and it should be run before σ-Poseidon's
round count is fixed. It does not change the dominance conclusion above (8 ≪ 24) unless the
σ-layer's Krylov rank is *deficient*, which would be a different and separately interesting
finding.

### 4b. gadget-Feistel — **untouched, structurally**

Confirmed at source (`ring-hash-design.md:337-345`): `NR = 16` uniform rounds, **no full/partial
split**, and *"This is a **non-algebraic** alternative — no S-box, no automorphisms"* (line 334).
The phrase "partial round" does not occur in §3 at all.

**GSR's entire mechanism is "fix the input of the single active S-box in a partial round to a
constant `δ`, so its output is the constant `δ^α`."** With no S-box there is nothing to fix, and
with no partial layer there is nothing to fix it in. **gadget-Feistel is immune to GSR by
construction — not by margin.** (Its own open item is unchanged and unrelated:
`ring-hash-design.md:382-384`, *"NR=16 is precedent plus margin, not cryptanalysis."*)

### 4c. The other two deployed Poseidon2 instances

| instance | `t` | `α` | `R_P` | total | GSR CICO-1 | margin | assessment |
|---|---|---|---|---|---|---|---|
| **BabyBear w16** — the deployed permutation | 16 | 7 | 13 | 21 | **18/21 at 2^27.4** | **3** | as §2c |
| **BabyBear w24** — segment-digest sponge (`ivc_turn_chain.rs:899`) | 24 | 7 | **21** | 29 | **26/29 at 2^27.4** | **3** | `t−2k = 22 > 21` — **also absorbs 100% of its partial layer**, same 3-round margin |
| **BN254 w3** — outer "shrink" wrap (`dregg_outer_config.rs:18`) | 3 | 5 | 56 | 64 | 1/56 skipped, 2^282 | — | **immune**: `t−2k = 1`, gadget absorbs one partial round of 56 |

**BN254 w3 is immune for a structural reason worth naming**: GSR's power is `t − 2k`, so a
*narrow* permutation with *many* partial rounds is the shape GSR cannot touch. `t = 3` gives it
one round.

**Our Pasta/Mina Poseidon is also immune**: `PastaPoseidon.lean:31-32` — *"round split: **55 full
rounds, 0 partial rounds**"*. No partial layer, no GSR.

---

## 5. Repairs, priced

**Cost unit, measured, ours** (`forcodex/03-MEASUREMENTS.md:552-565`): the deployed Poseidon2-w16
AIR is **300 cells** for `8×16 + 13 = 141` S-boxes = **2.13 cells per S-box**. A partial round is
**exactly one S-box**, so `+1 R_P = +1 S-box ≈ +2.1 cells ≈ +0.7%`.
⚠ Unit caveat, said out loud: in the *deployed wide arm* the column budget is
`(21+1)×16 = 352` aux columns, where `+1` partial round costs `+16` columns (352 → 368); the
narrow arm (landed, not deployed) is 141 columns where it costs `+1`. The 300-cell figure is a
third convention. **The percentages below use the 2.13 cells/S-box measurement; under the wide
arm's column budget a `+2` repair is 352 → 384, i.e. +9%.** Both are cheap; neither is free.

### The sweep (`…/scratchpad/all_inst.py`)

| `R_P` | total | CICO-1 at full round count | deepest reach | **margin** | Δ S-boxes | Δ cells | Δ % |
|---|---|---|---|---|---|---|---|
| **13 (deployed)** | 21 | **2^27.4 — BEATS 2^31** | 18 | **3** | — | — | — |
| 14 | 22 | 2^27.4 — BEATS | 19 | 3 | +1 | +2.1 | +0.7% |
| **15** | 23 | **2^33.0 — DEAD** | 19 | **4** | **+2** | **+4.3** | **+1.4%** |
| 17 | 25 | 2^44.3 — DEAD | 19 | 6 | +4 | +8.5 | +2.8% |
| **20** | 28 | 2^61.1 — DEAD | 19 | **9** | **+7** | **+14.9** | **+5.0%** |
| 21 | 29 | 2^66.7 — DEAD | 19 | 10 | +8 | +17.0 | +5.7% |

**⚑ The cliff is at `R_P = 15`.** CICO-1 needs residual degree `d ≤ 2^13.0` to beat 2^31; with
`d = 7^(unskipped + 4)` that forces `unskipped = 0`, i.e. `R_P ≤ 14`. **At `R_P = 15` the
practical CICO-1 attack dies at the full round count, for +1.4%.** Note the *reach* saturates at
19 rounds regardless — so beyond 15, every additional partial round buys exactly one round of
margin at ~0.7% each. That is the cheapest margin in the repo.

### Options, in the paper's terms and ours

| repair | effect | cost | assessment |
|---|---|---|---|
| **`R_P` 13 → 15** | kills practical CICO-1 at full round count | **+1.4%** (+4.3 cells) | ⚑ **do this** — it is nearly free and removes the one practical result |
| **`R_P` 13 → 20** | margin 3 → **9 rounds** | **+5.0%** (+14.9 cells) | ⚑ **the real fix.** Buys genuine margin, still under-6%. This is what "restore the margin" costs. |
| **`R_P` 13 → 21** (match the w24 instance) | margin 10, one `R_P` for both widths | +5.7% | tidy: one round schedule across both BabyBear instances |
| different internal layer | **nothing** | any | ⚠ **does not work.** §1c: any invertible `M_I` with full Krylov works for GSR, and deficient Krylov = broken by subspace trails. There is no matrix that fixes this. |
| **all-full-rounds** (13 partial → 13 full) | GSR immune by construction | 141 → 336 S-boxes, **300 → ~715 cells, +138%** | ⚠ the post-Weft `x⁻¹` note already forces ~8 all-full rounds by a different route; but as a *GSR* repair it is **~100× the cost of the `R_P`=20 fix for the same outcome.** Do not buy this to solve GSR. |
| increase `R_F` | +1 round of margin per +1 `R_f0` | +16 S-boxes each ≈ +34 cells ≈ **+11% each** | 16× worse per round of margin than `R_P`. Only relevant if a future attack extends §5.3's backward step past one full round — **which is the thing to watch.** |

**Flag-day cost of the `R_P` change** (per `CLAUDE.md`: say what re-emits). Changing `R_P`
re-emits: the Lean descriptor (`Poseidon2Binding.lean:142`, its `#guard`s, `DescriptorIR2.lean`
`chipParamsJson`), the round-constant tables in **nine** transcriptions (Lean, `circuit/src/
poseidon2.rs`, `sel4/…/crypto-floor`, `fhegg-fhe/src/private_book_bfv_zk.rs`,
`chain/gnark/poseidon2_w16.go`, `bridge/mina-zkapp/…ts`, WGSL, descriptor JSON), the KAT
`#guard perm (List.range 16) = […]`, `POSEIDON2_AUX_COLS` (352 → 384 at `R_P`=15), every VK, and
a re-genesis. **That is a rebuild, which is the answer to "what does it cost".**

---

## 6. GSR vs. CheapLunch — they sit beside each other, and CheapLunch already saw the shape

**CheapLunch (2025/2040) is not contradicted.** Its claim, p. 22, is explicitly about the *full*
round count:

> *"We emphasize that even with ω = 2, we found **no attacks on full Poseidon with its security
> margin** for realistic security levels (80 ≤ λ ≤ 256)."*

GSR attacks `R_f0 = 1`, i.e. **with three initial full rounds removed**. It is a round-reduced
result and does not claim otherwise (§8: *"28 and 25 rounds … out of the recommended 31"*).
**No contradiction. GSR refines the picture inside the margin; CheapLunch's statement about the
full permutation stands.** Our own `forcodex/08-ATTACK-BRIEFS.md:27` cites exactly this
CheapLunch sentence, and it remains correctly cited.

**⚑ But CheapLunch already had the trick, and already flagged Poseidon2 — at our exact
parameters.** CheapLunch p. 23 describes skipping *"the first ℓ partial rounds"* via the
subspace-trail basis `{v : M_I^j v ∈ {0} × F^{t−1}, 0 ≤ j ≤ t−k−1}` — the same mechanism, but
requiring a *linear* subspace (fix the S-box input to **0**). GSR's contribution is the *affine*
generalization (fix it to an arbitrary `δ`), which removes the structural requirement on `M_I`
and lifts the restriction to `k ∈ {1,2}` — the paper says so: *"existing skipping results have
been limited to `k ∈ {1, 2}`."*

And CheapLunch §D.1, verbatim, **on Poseidon2 at `t=16, k=1`**:

> *"Additionally, some instances of Poseidon2 use non-MDS matrices, which may make this
> round-skipping trick **more efficient than expected**. We observed for instance that in the
> case **`t = 16, k = 1`**, two rounds can be freely skipped using the `M_E` matrix from
> Poseidon2. We leave as an open problem a further study of this phenomena."*

> *"non-MDS matrices such as the ones defined in Poseidon2 may be **weaker** against such tricks
> than MDS ones. […] This tends to show that contrary to what was believed by the designers of
> Poseidon2, using non-MDS matrices not only weakens the security against statistical attacks,
> but also **against some algebraic attacks**."*

**That is our width, our `k`, and an explicit open problem left on the table in 2025 — about
`M_E`, the external matrix, which is a *different* and *additional* skip from GSR's `M_I` one.**
The two are plausibly composable (CheapLunch's 2 free `M_E` rounds sit in the initial full rounds
— exactly the 3 rounds that are our entire margin). **I have not verified composability and am
not claiming it.** It is the single highest-value follow-up here, and it is runnable: build
`M_E` for our w16 (`Poseidon2BabyBearW16.lean:70-95`, the `MDSMat4` circulant `[[2,3,1,1],…]`
plus the outer column-sum circulant) and search for CheapLunch's skip vector.

⚑ **If CheapLunch's `M_E` skip composes with GSR's `M_I` skip, the 3-round margin goes to 1.**
That is the scenario that would move the verdict, and it is a computation, not a research
program.

---

## 7. Does the deployed verdict move?

### First, a correction to the framing

The brief called GSR *"the fourth confirmation-or-refutation of a verdict we have called
triple-confirmed."* **The "triple-confirmed" verdict is a COST verdict, not a cryptanalytic
one** — `hash-landscape.md:1113`: *"Poseidon2's position is now triple-confirmed: in-circuit
30.6×–210× directly, recursion pinning it in both characteristics, and the lookup escape
measured shut."* **GSR cannot confirm or refute that; it is about a different quantity.**

There is a separate four-fold confirmation on the *attack* side
(`forcodex/08-ATTACK-BRIEFS.md:27`). **GSR is a fifth data point on that one**, and it is the
first that is not purely confirmatory.

### The verdict

**MOVES — narrowly, and in a way that is cheap to fix.**

**What falls** (state it exactly):
- A **probability-1 distinguisher over 15 of our 21 rounds** at k=1, degree exactly 1.
- **CICO-1 on a round-reduced (1,13,4) = 18-of-21-round variant at ≈2^27.4 / 2^16.2** —
  practical, seconds on a laptop, and it linearizes **100% of our internal layer**.
- CICO-2 on 18/21 at 2^61.1 vs 2^62 generic. **~1 bit. Call this "not a meaningful break"**, not
  a break.

**What stands** (state this exactly too, and do not let it be quiet):
- **The full 21-round permutation.** No attack. The 3 initial full rounds are outside GSR's
  reach by the structure of §5.3, not by a complexity margin.
- **The sponge's collision/preimage claims.** Our capacity is 8 base elements (248 bits) ⇒
  ~124-bit collision resistance — the repo's own 2^123.6 bar. That claim lives at **CICO-k for
  `k` at the capacity**, and **GSR gives nothing there.** Measured: no gain already at **k = 3**
  (2^162.2 vs a 2^93 generic bound); at **k = 4** — the row our own
  `poseidon2-audit-verdict.md` table tracks — it is 2^409.2 vs 2^124 (⚠ *not* to be confused
  with that table's 2^409.9 Lemma-4.5 compression figure — near-identical digits, unrelated
  quantities); and at **k = 8** the
  gadget is *identically vacuous*, `t − 2k = 16 − 16 = 0`, absorbing **zero** partial rounds
  (and one full round, i.e. strictly less than Bariant et al. 2022 already achieved). **The
  instances GSR breaks (k = 1, 2) are not the instances that carry our security claim.**
  ⚑ **This is the single most load-bearing sentence in the note, and it is why the answer is
  "narrow" rather than "severe".**
- `poseidon2-audit-verdict.md`'s bar computation. Its criterion is *"reaching the bar needs
  `8·r_F + r_P > 59.0`, and the maximum available in the paper's own model is 45."* GSR's skip
  budget is `r_F = 1, r_P = 13` ⇒ **21**, still far under 59. **Cross-instrument agreement: the
  audit verdict survives GSR as an input.**
- **σ-Poseidon and gadget-Feistel** (§4a, §4b). And BN254-w3 and Pasta-Poseidon (§4c).

**What changes in how we talk about it:**
1. The deployed margin against the *partial-layer* attack line is **3 of 21 rounds, and it is a
   CEILING**. It should be written that way from now on, next to the τ=2 **floor** of 24, with
   the species labelled — they are not comparable quantities.
2. **`R_P = 13` sits below `t − 2k = 14`.** That is a *named structural defect* in our parameter
   choice, independent of any complexity estimate, and it is the one thing here that is
   unambiguously wrong rather than merely thin.
3. The margin is set by `R_f0`, not `R_P`, at the current round count — so **the thing to watch
   is any extension of §5.3's backward step past one full round**, and **CheapLunch's unclaimed
   `M_E` skip at `t=16, k=1` (§6) is exactly that shape.**

### Recommended action

- **Do the `R_P` 13 → 20 change** (+5.0%, margin 3 → 9). Per `CLAUDE.md`, the cost estimate is
  "a rebuild", and a rebuild is not a reason to prefer the `R_P`=15 containment. ⚠ **I am naming
  `R_P`=15 as a *containment* and `R_P`=20 as the *fix*, and saying so plainly so the phases do
  not get run backwards** — `R_P`=15 lands *above* the cliff for CICO-1 but leaves the margin at
  4, and 4 is the same species of number as 3.
- **Run the `M_E` composability check** (§6). It is a computation, and it is the only open path
  by which this verdict gets worse.
- **Measure or relabel `ring-hash-design.md:326`** (§1d) — an unmeasured line cited as measured
  in five places.

---

## Provenance

- Paper: `~/paperbin/gsr-sbox-skipping-poseidon-2026-1692.txt` (already extracted; no
  `pdftotext` run needed). CheapLunch: `~/paperbin/cheaplunch-extending-freelunch-2025-2040.txt`
  (already extracted). **No PDF in this note required extraction** — both were among paperbin's
  518 `.txt` sidecars.
- Scripts, persisted to **`notes/gsr-scripts/`** (written in a session scratchpad, copied out —
  scratchpads are session-scoped and evaporate):
  - `krylov.py` — Q1: Krylov rank of `M_I` at `e₀` on the deployed w16/w24 constants.
  - `gsr_calc.py` — the paper's degree/SyCZ model; **reproduces Table 1 on 5/5 rows**, which is
    the guard that the model is theirs and not a reconstruction. Run it first.
  - `all_inst.py` — all three deployed instances + the `R_P` repair sweep.

  All three are plain `python3`, no dependencies, and run in under a second.
- Our parameters read from `/Users/ember/dev/breadstuffs/`: `circuit/src/poseidon2.rs:20-109`,
  `metatheory/Dregg2/Circuit/Poseidon2Binding.lean:134-157`,
  `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean:43-199`,
  `metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean:101-256`.
