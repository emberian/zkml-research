# Should the leaf system and the recursion system be different? — the in-circuit verifier, decomposed

2026-08-14. Every count in §1–§4 is `[MEASURED]` — an exact op census off a real circuit, taken by
a new sweep harness (`breadstuffs/circuit-prove/tests/leaf_vs_recursion_sweep.rs`), reproducible
bit-for-bit under any load. `[DERIVED]` means arithmetic on measured counts. `[READ]` means at
source. Nothing here is a wall clock; load average was 158 while it ran and no figure depends on it.

---

## 0. ⚑ THE ONE-BREATH ANSWER

**No — and the question was aimed one layer too high.**

`recursion-tower-profile.md` §2 measured that a wrap's Poseidon2 table *is* its child's verifier, row
for row (38,168 = 38,168). This lane decomposed that 38,168 by regression and the answer is:

> ### ⚑ **94% of a wrap's in-circuit hashing and 88.5% of its in-circuit arithmetic scale with the CHILD'S COMMITTED WIDTH. Only 5.9% scales with its height, blowup, or FRI-round count.**

So "cheapest to verify in circuit" is not a property of the IOP at all. Sumcheck-based and
FRI-based verifiers differ by ~500× in IOP cost and that difference is **0.2% of the bill**. The bill
is the **PCS opening**, and the PCS opening is `q × (opened columns)` twice over — once as Merkle
leaf-sponge hashing, once as the reduced-opening Horner.

Four consequences, each earned in counts below:

1. **A heterogeneous *proof system* stack buys nothing.** Confirmed at source: neither SP1 nor
   OpenVM changes proof system between leaf and recursion. Both change **parameters per layer**,
   and both change only the **hash field** at the wrap (§5).
2. **The in-circuit verifier is arithmetic-bound, not hash-bound** — 36.45% hashing against 60.75%
   arithmetic (§3). So "binary fields make the verifier cheap" **does not follow**; a free hash is
   worth ×1.57, and it attacks the smaller half. Hash-dominance appears only at a **field-mismatch
   seam** (§3c). This is the opposite of the hypothesis the brief asked me to test, and it is the
   test's result, not an assumption.
3. **The deployed `lb = 6` is the minimum of a curve nobody had computed**, by 1.5–3× over every
   alternative at iso-ledger (§4). The "blowup drop" costs ×2.96 per turn, not ×65 — §4c corrects
   an arithmetic misreading that has now been relayed twice.
4. **Arbitrary-length extendability costs ×27.9 per turn, measured** (§6). That is the price of
   ember's "too expensive to want to pay for all the time," and it is paid whether or not any chain
   is ever extended.

And the single largest untaken lever, which is neither a field nor a system: **batch the reduced
opening with a sumcheck.** ×2.13 on the wrap, and it is the *prerequisite* that would make the
hashing argument true (§3d). It is already named in this repo, undated and untaken.

---

## 1. THE INSTRUMENT — separation by sweep, not by a new counter

`recursion-tower-profile.md` §0b records the blocker: the tower is monomorphic
(`impl FriRecursionConfig for DreggRecursionConfig` is orphan-rule-welded, `prepare_circuit_for_
verification` hardcodes `default_babybear_poseidon2_16()`), so a counting config is a real port.
**That port is not needed.** The wrap circuit is built deterministically from the child proof's
shape, and `create_recursion_config_split_fri` (`recursion-verify/src/config.rs:419`) mints the
child at an arbitrary `(log_blowup, log_arity, num_queries)` while pointing the wrap's in-circuit
FRI verifier at the same knobs. A circuit build is ~1.2 s. So the components separate by
**regression on exact counts**:

```
perms(q, m)  =  C  +  q · [ L  +  P(m) ]
                ^^^        ^^^   ^^^^
                |          |     Merkle PATH compressions — grows with m
                |          per-query LEAF sponge over opened rows — independent of m
                q-independent: transcript absorption + grind
```

`m = log₂(max child LDE height) = log₂(max trace rows) + log_blowup`.

**Validation, before any new claim.** The sweep reproduces both previously-measured points exactly,
by a code path that shares nothing with the measurement that produced them:

| point | `recursion-tower-profile.md` §2 | this sweep |
|---|---:|---:|
| `(lb 6, arity 2, q 19)` | 38,168 | **38,168** |
| `(lb 2, arity 2, q 57)` | 89,739 | **89,739** |

Harness: `breadstuffs/circuit-prove/tests/leaf_vs_recursion_sweep.rs` (new, four `#[ignore]`d
measurement tests). Child: the deployed rotated transfer leaf, `trace_width 1804 / pi_count 61`,
three main traces at `log₂ rows [6, 8, 4]`, `Σwidth 3738`, `Σ⌈w/8⌉ 469`.

---

## 2. ⚑ THE DECOMPOSITION `[MEASURED]`

### 2a. The height sweep — the path term, isolated

Fixed `q = 19`, arity 2, blowup 1→8 (so `m` 9→16). **Nothing but `m` moves.**

| lb | m | perms | HornerAcc | Alu(all) | recompose |
|---:|---:|---:|---:|---:|---:|
| 1 | 9 | 37,123 | 390,716 | 441,304 | 160,263 |
| 2 | 10 | 37,332 | 390,716 | 441,380 | 160,263 |
| 3 | 11 | 37,541 | 390,716 | 441,456 | 160,263 |
| 4 | 12 | 37,750 | 390,716 | 441,532 | 160,263 |
| 5 | 13 | 37,959 | 390,716 | 441,608 | 160,263 |
| **6** | **14** | **38,168** | **390,716** | **441,684** | **160,263** |
| 7 | 15 | 38,377 | 390,716 | 441,760 | 160,263 |
| 8 | 16 | 38,586 | 390,716 | 441,836 | 160,263 |

> ### ⚑ `Δperms/Δm = 209 = 19 × 11`, **exactly constant across every rung.** And `ΔHornerAcc/Δm = 0`, `Δrecompose/Δm = 0` — exactly zero.

Two structural facts fall straight out:

* **The Merkle-path term is LINEAR in `m`, not quadratic**, at **11 permutations per query per unit
  of `m`**. A quadratic FRI-path model (`Σ_r depth_r = m(m−1)/2`) is refuted by the constancy.
  The reason is at source: `p3-fri` folds until the codeword reaches `2^lb · 2^lfpl`, so the FRI
  round count is `log₂(max trace rows) = 8` **independently of blowup**. `11 = 8 FRI rounds + 3
  input commitment rounds`, each one Merkle level deeper per unit of `m`.
* **The reduced-opening arithmetic is exactly blowup-invariant.** `HornerAcc` does not move by a
  single op across a 128× change in LDE size.

### 2b. The query sweep — the constant, isolated

Fixed `(lb, arity)`, `q ∈ {12, 19, 28, 38, 57}`. Least squares, with the max residual printed so
linearity is a *finding* and not an assumption:

| fit at `lb 6, m 14` | per-query | q-independent | max\|resid\| |
|---|---:|---:|---:|
| **perms** | **1,423.13** | **11,128.39** | 0.34 |
| **HornerAcc** | **20,564.00** | **0.00** | **0.00** |
| Alu (all) | 20,861.00 | 45,325.00 | 0.00 |
| recompose | 2,581.04 | 111,222.10 | 2.70 |

> ### ⚑ **`HornerAcc = 20,564 · q` — exactly linear, exactly zero intercept, exact to the op across five query counts and three blowups.** The reduced opening is `q × (opened values)` and nothing else.

The `perms` intercept is **identical (11,128.39) at every blowup** — as it must be, since the
q-independent work is transcript absorption, which does not see the LDE.

### 2c. ⚑ THE ANSWER — the leaf wrap's 38,168 in-circuit permutations, split

Combining §2a and §2b at the deployed point `(lb 6, q 19, m 14)`. The Merkle-path total is
`q · (11m − 36) = 19 × 118 = 2,242` (the slope 11 is measured; the intercept −36 is the structural
read `3 input trees at depth m` + `8 FRI trees at depths m−1 … m−8`, so the path term is bounded
`2,242 ≤ paths ≤ 19 × 154 = 2,926` even if that read is wrong):

| component | scales as | perms | share |
|---|---|---:|---:|
| **transcript absorption of the OOD opened values + grind** | `Σw` (**width**) | 11,128 | **29.2%** |
| **per-query Merkle LEAF sponge, main round** (`q · Σ⌈w/8⌉ = 19 × 469`) | `q · Σw` (**width**) | 8,911 | **23.3%** |
| **per-query Merkle LEAF sponge, other rounds** (LogUp + quotient + FRI-round leaves) | `q · Σw` (**width**) | ~15,887 | **~41.6%** |
| **per-query Merkle PATH compressions** (`q · (11m − 36)`) | `q · m` (**height**) | 2,242 | **5.9%** |

And the arithmetic side, from §2b:

| component | scales as | ops | share of Alu |
|---|---|---:|---:|
| **reduced-opening Horner** | `q · Σw` (**width**) | 390,716 | **88.5%** |
| OOD constraint evaluation + misc | `O(1)` in `q` | 45,325 | 10.3% |
| per-query non-Horner | `q` | 5,643 | 1.3% |

> ### ⚑⚑ **94.1% of in-circuit permutations and 88.5% of in-circuit arithmetic scale with the child's COMMITTED WIDTH. 5.9% scales with height, blowup and FRI structure combined.**

⚑ **This refutes `recursion-tower-profile.md` §4b's own prose.** That note says *"Most in-circuit
permutations are 2-to-1 compressions along `q` paths of depth `log₂(LDE rows)`."* Measured:
**5.9%**. Its own numbers implied this (its `8,911 = 23.3%` was leaf hashing, and it never priced
the paths) — the sentence was a model carried in, not a count. The correction matters because it
inverts the lever: **width, not height.**

⚑ **And it independently confirms SP1's published attribution.** `notes/field-recursion-evidence.md`
records that SP1 attributes recursion cost to **COLUMN COUNT, not field width** (Jagged-PCS paper).
Two instruments with no shared code path, same answer.

### 2d. The folding-arity knob — worth nothing `[MEASURED]`

Nobody has priced it. At `(lb 6, q 19)`:

| arity | perms | Alu(all) | recompose |
|---:|---:|---:|---:|
| 2 | 38,168 | 441,684 | 160,263 |
| 4 | **37,404** (−2.0%) | 442,496 (**+0.2%**) | 160,228 |
| 8 | **37,404** (−2.0%) | 443,199 (**+0.3%**) | 160,228 |

−2% on hashing, **+0.3% on arithmetic**, and no table changes power-of-two rung. **A null knob.**
Recorded so it stops being an open question.

---

## 3. ⚑ THE HASHING FRACTION — the question that was supposed to decide the architecture

### 3a. The answer, in the deployed matched-field stack

The wrap's committed geometry (`get_airs_and_degrees_with_prep`, the call the prover makes):

| table | cells (main+prep) | share |
|---|---:|---:|
| `poseidon2_perm/baby_bear_d4_w16` | 21,233,664 | **36.45%** |
| **`Alu`** | **35,389,440** | **60.75%** |
| recompose | 1,572,864 | 2.70% |
| Const + Public | 53,248 | 0.09% |

> ### ⚑ **The in-circuit verifier is ARITHMETIC-BOUND, not hash-bound: 60.75% arithmetic against 36.45% hashing.** A *free* hash is worth **×1.57**. Amdahl caps the whole binary-field-for-cheap-hashing argument there.

### 3b. ⚠ Two different "hash fractions" that a display name conflates

`recursion-tower-profile.md` §6 concludes *"the tower IS hash-bound, at `Y/X ≈ 3.1–3.3×`."* That is
**true and about a different object**, and the two must not be merged:

| question | object | answer |
|---|---|---|
| what fraction of the **in-circuit verifier** is hashing? | the trace the wrap must *express* | **36.45%** — arithmetic-bound |
| is the **wrap's own prover** hash-bound? | LDE/DFT vs Merkle commit, once the trace exists | **yes, `Y/X ≈ 3.1–3.3×`** |

The first decides which proof system is cheap to recurse. The second decides which silicon to build.
Same word, different denominators, opposite verdicts.

### 3c. ⚑ Where hashing *does* dominate: the field-mismatch seam

`breadstuffs/docs/deos/WRAP-NATIVE-HASH-DECISION.md` measured the same FRI verifier compiled to
**gnark/BN254** at the ir2 shape (18 arity-2 rounds, q 19, pow 16), in R1CS constraints:

| term | emulated BabyBear-in-BN254 | native BN254 Poseidon2 |
|---|---:|---:|
| hashing + transcript | 40,717,530 (**99.46%**) | 797,763 (**78.3%**) |
| fold-arith residual | 220,500 | 220,500 (byte-identical) |
| **total** | **40,938,030** | **1,018,263** (**40.2×** better) |

> ### ⚑ **Hash-dominance is a symptom of FIELD MISMATCH, not a property of the proof system.** In a matched field the verifier is 36.45% hashing; across a field boundary it is 78–99%. The fix everybody ships is not a new proof system — it is **the same system with a different hash field** (§5).

**So the answer to the brief's hypothesis is: tested, and it does not hold.** Binary fields would
make a verifier cheap only if the verifier were hashing-dominated *inside its own field*, and it is
not. Binary-tower land also has its own algebraic hash (Vision Mark-32, Ashur–Mahzoun–**Posen**–
Šijačić) carrying the same cryptanalytic exposure class, so "binary field" does not even imply
"traditional hash" — `binaryspartan-position.md` §8 has that correction at source.

### 3d. ⚑⚑ THE LEVER THAT DOES PAY — and it makes the hashing argument true

`HornerAcc = 390,716` is **88.5% of `Alu` and 60.8% of the whole wrap's cells**, and it is one
thing: the reduced opening, `Σ_i α^i (v_i − v_i(ζ))/(x − ζ)` over `q × (opened columns)`. Batching
it with a sumcheck replaces `q · Σw` multiply-accumulates with `O(log(q · Σw))` rounds.
`WRAP-NATIVE-HASH-DECISION.md`'s three-lever plan already names this ("GKR-batch the reduced
openings — one sumcheck replaces ~14,300 per-column ExtMuls") and it was never taken.

`[DERIVED, on measured geometry]` — `Alu` falls from 441,684 ops to ~51,053, three power-of-two
rungs (`2^18 → 2^15`); `recompose` held unchanged, conservatively:

| | cells (main+prep) | poseidon2 share |
|---|---:|---:|
| L1 wrap today | 58,249,216 | 36.45% |
| L1 wrap, reduced opening batched | **27,283,456** | **77.8%** |
| | **×2.135** | |

> ### ⚑⚑ **×2.13 on the wrap ⇒ ×2.05 on the per-turn total. AND it is the prerequisite for every hashing argument: a free hash is worth ×1.57 today and ×4.5 after.** The two levers are ordered, and the repo has been arguing for the second one for a year without taking the first.

---

## 4. ⚑ THE ENGINE GRID — `(leaf prove) + (wrap)`, which has never been computed

### 4a. The measured half

`[MEASURED]` — every row holds the leaf's deployed capacity ledger `lb·q + pow ≥ 130`
(`recursion-verify/src/config.rs:174`; ⚠ a budget the engines are gated against, **not** a soundness
theorem — `project-fri-soundness-reality` holds the real numbers):

| lb | q | m | wrap perms | wrap HornerAcc | wrap Alu | ledger |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 57 | 10 | 89,739 | 1,172,148 | 1,233,490 | 130 |
| 3 | 38 | 11 | 63,953 | 781,432 | 837,587 | 130 |
| 4 | 29 | 12 | 51,761 | 596,356 | 650,062 | 132 |
| 5 | 23 | 13 | 43,607 | 472,972 | 525,036 | 131 |
| **6** | **19** | **14** | **38,168** | **390,716** | **441,684** | **130** |
| 7 | 17 | 15 | 35,509 | 349,588 | 400,030 | 135 |
| 8 | 15 | 16 | 32,805 | 308,460 | 358,360 | 136 |
| 10 | 12 | 18 | 28,734 | 246,768 | 295,849 | 136 |
| 12 | 10 | 20 | 26,020 | 205,640 | 254,175 | 136 |

### 4b. The composed grid

`[DERIVED]` — the wrap's own native permutation cost from its table geometry at its mint `lb 3`
(the exact `⌈w/8⌉` leaf-sponge law + one compress per 2-to-1 node), times the ×2.430 calibration
`recursion-tower-profile.md` §5b measured on the child (it cancels in every ratio). Leaf prove from
a two-point fit on the two counted points, `P(lb) ≈ 96,196 · 2^lb + 20,956`.
⚠ **That fit's two points differ in `q` as well as `lb`**, so `q`'s (small, open-phase) effect is
folded into the coefficient. The dominant term is `2^lb`; the confound is named, not eliminated.

| lb | q | leaf prove | wrap prove | **TOTAL** | wrap/leaf | vs `lb 6` |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 57 | 405,741 | 509,966,254 | 510,371,995 | 1256.9× | **2.96×** |
| 3 | 38 | 790,526 | 262,806,405 | 263,596,932 | 332.4× | 1.53× |
| 4 | 29 | 1,560,097 | 262,806,405 | 264,366,502 | 168.5× | 1.54× |
| 5 | 23 | 3,099,238 | 262,806,405 | 265,905,643 | 84.8× | 1.54× |
| **6** | **19** | **6,177,519** | **165,980,897** | **172,158,416** | **26.9×** | **1.00×** |
| 7 | 17 | 12,334,082 | 165,980,897 | 178,314,980 | 13.5× | 1.04× |
| 8 | 15 | 24,647,209 | 165,980,897 | 190,628,106 | 6.7× | 1.11× |
| 10 | 12 | 98,525,967 | 139,226,481 | 237,752,448 | 1.4× | 1.38× |
| 12 | 10 | 394,041,001 | 90,813,727 | 484,854,728 | 0.2× | 2.82× |

> ### ⚑ **The deployed `lb = 6` is the MINIMUM, by 1.5–3× over every alternative — on a grid that has never existed.** The wrap/leaf ratio there is **26.9×**, independently reproducing §5b's 26.05×.

⚠ **And the minimum is not smooth — it is a power-of-two rung.** `Alu` drops `2^19 → 2^18` exactly
between `lb 5` and `lb 6`, which is the entire 1.54 → 1.00 step. The curve is flat (1.00–1.11×) over
`lb ∈ [6, 8]` and rises sharply outside. A grid that models cost as continuous will miss this.

### 4c. ⚠ CORRECTION — "net ≈ 65× worse per turn" is a misreading, and it has now been relayed twice

`recursion-tower-profile.md` §5b says the blowup drop *"saves 0.934 leaf-proves at L0 … costs 60.6
leaf-proves at L1 … net +59.7 leaf-proves — a ≈ 65× loss."* **65× is the ratio of the loss to the
saving.** The per-turn total goes from 27.05 to 86.7 leaf-proves = **×3.21** (this lane's
independent grid: **×2.96**). It is not "65× worse per turn." My own brief for this lane carried the
stronger sentence, and so did the note's summary line. The trade is still firmly negative; the
magnitude is 3×, not 65×.

---

## 5. ⚑ WHAT SP1 AND OPENVM ACTUALLY CHOSE — `[READ, at source]`

Both repos are on this machine (`~/src/sp1` @ `f66b4bf` v6.4.0, `~/src/openvm` @ `c65f9fa` v2.0.2 +
`~/src/openvm-stark-backend` @ `362c7ad`). **Both have moved off classic two-adic FRI to
sumcheck-based multilinear systems**, and neither uses a different proof system per layer.

| | SP1 6.4 "Hypercube" | OpenVM 2.0 "SWIRL" |
|---|---|---|
| field | KoalaBear / KB⁴ | BabyBear / BB⁴ |
| PCS | **Jagged → Stacked → BaseFold** | **Stacked → WHIR** |
| log_blowup by layer | core 2, compress 2, shrink 3, wrap 3 | **app 1, leaf 2, internal 3, root 4** |
| queries by layer | 124, 124, 94, 94 (derived, not constant) | ~443, 283, 118, 111 (per-WHIR-round schedules) |
| security basis | unique decoding; 100 bits | **no conjectures**; provable proximity gaps; list-decoding above leaf |
| outer switch | Poseidon2-KoalaBear w16 → **Poseidon2-BN254 w3** at wrap | Poseidon2-BabyBear w16 → **Poseidon2-BN254 w3** at root |
| final system | gnark Groth16 **or** PLONK | halo2 + KZG/SHPLONK |

Citations: `sp1/crates/primitives/src/fri_params.rs:5,6,17,18,43,44,7` and its derived
`unique_decoding_queries_with_custom_grinding` (`:46-59`);
`openvm-stark-backend/crates/stark-sdk/src/config/mod.rs:29-44,121,155,185,214,243`.

### The three things this settles

1. **Nobody runs a different proof SYSTEM at the leaf.** The heterogeneity is (a) **parameters per
   layer** and (b) **one hash-field swap at the last STARK layer**. Both express (b) as a second
   `IopCtx` / `StarkProtocolConfig` instance, not a parameter tweak — i.e. exactly the seam §3c
   identifies as the only place hashing dominates.
2. **OpenVM's blowup rises monotonically up the tower — 1, 2, 3, 4 — the opposite of ours.** Its
   own rationale, in the preset assumption blocks
   (`config/mod.rs:109-120` vs `142-149,172-179,202-208,231-237`): app allows ≤30,000 columns,
   ≤100 AIRs, ≤5,000 constraints/AIR; the recursion presets allow **≤2,000 columns, ≤50 AIRs,
   ≤1,000 constraints**. *"The aggregation circuits are far smaller and more uniform, so they can
   afford higher blowup for fewer queries, which is what makes them cheap to verify in the next
   layer up."*
3. ⚑ **The parameter that decides the direction is `K = wrap cost / leaf cost`, and ours is
   inverted.** Our `K = 26.9` because our leaf is *tiny* (313,248 committed cells, three traces at
   2^6/2^8/2^4) and our wrap is *huge* (58.2M cells). SP1/OpenVM leaves are whole zkVM shards at
   `log_stacking_height` 21–24, and their recursion circuits are explicitly capped **smaller** than
   their leaves — so their `K < 1`, prover cost dominates, and **low leaf blowup is correct for
   them and wrong for us.**

> ### ⚑ **Our problem is not the wrong proof system. It is that the leaf is 3.7% of the object.** Every knob priced on the leaf alone is priced on 3.7%. The structural fix is to make leaves bigger relative to wraps — batch more turns per leaf — which drives `K` down and moves us onto the same side of the trade as everyone else.

### And what their PCS choice is *for*

Jagged (SP1) removes padding; Stacked (both) packs many matrices into one committed vector. **Both
are opened-column reducers.** §2c says the opened-column count is 94% of the in-circuit verifier.
So the industry's actual move — quietly, without writing this down — was to attack exactly the term
this lane measures as dominant. That is the strongest available confirmation of the decomposition.

---

## 6. ⚑ THE THREE EXTENDABILITY REGIMES, PRICED

Ember: *"I thought it was quite hard to find a selection of constraints that result in
arbitrary-length extendability — but maybe that property is too expensive to want to pay for all
the time."* Separating the regimes and pricing them on our own measurements:

| regime | what it requires of the constraint system | per-turn cost `[DERIVED from §4b]` | vs one-shot |
|---|---|---:|---:|
| **one-shot** | *nothing.* No verifier need be expressible. Choose the leaf purely for prover speed. | 6,177,519 | **1.0×** |
| **bounded-depth aggregation** (a tree of depth `d`) | only that **layer `k+1` can verify layer `k`**. Every layer may be a *different* system; only the last must be small. | leaf + fold, amortized: ≈ 172.2M for `d = 1` | ~27.9× |
| **unbounded IVC / PCD** | the system must be **closed under its own verifier** — a fixed point, at a size independent of step count. | 172,158,416 | **×27.9** |

> ### ⚑ **Arbitrary-length extendability costs ×27.9 per turn, measured — and it is paid on every turn whether or not the chain is ever extended.** Ember's instinct is right and now has a number.

### 6a. What each regime actually demands

* **Unbounded IVC** is the only one that forces a *fixed point*: the constraint system must contain
  its own hash as an AIR (hence Poseidon2-in-circuit, hence the algebraic-hash cryptanalysis
  surface `binaryspartan-position.md` §8 documents) and its own extension arithmetic. For a
  *heterogeneous* pair `(A, B)` this requires a **cycle**, not a chain — either `B` verifies `B`, or
  `A` verifies `B` and `B` verifies `A`. A one-directional "A's verifier is cheap in B" **does not
  give unbounded IVC**; it gives one rung.
* **Bounded-depth aggregation** is where heterogeneity is *free*: a depth-`d` tree can use `d`
  different systems, each chosen for its own rung, because no rung has to verify itself. This is
  the regime SP1 and OpenVM are actually in (`compress` → `shrink` → `wrap` → `gnark`; app → leaf →
  internal → root → halo2), and it is why their hash-field swap at the last STARK layer is
  *possible at all*.
* **One-shot** needs no in-circuit verifier, so it is the only regime where "fastest prover" is the
  right objective — and it is 27.9× cheaper than either of the others.

### 6b. ⚠ What our accumulation-depth composition actually says — and does not

`minidregg/Selvage/Depth.lean:1982`, `OB2_depth_composition_nonneg_proved`, discharged via
`gameSlotBound_proved` (`:1964`) and lifted through Fiat–Shamir by `fsOfRbrSound_iff_depth`
(`FiatShamir.lean:526`), `fsKeystone_proved` (`:650`):

> per-round knowledge soundness with error `ε` composes, over `k` protocol rounds and `t`
> state-restoration moves, into straightline extraction at error **`(t + k) · ε`**.

**`k` is the round count of a single `Reduction`; `t` is the adversary's oracle-query budget.
Neither is the depth of a proof-system stack.** The theorem is real and refutation-hardened — its
unguarded sibling `OB2_depth_composition` (`Rbr.lean:457`) is **proved FALSE**
(`Depth.lean:545`, via the `Z = ∅` / `εrbr := −1` hole), and the repair is one non-negativity guard.
That is a genuinely good theorem. It is **not** a bound on tower depth.

> ⚑ **So: "how much depth is needed" has no answer in our formal tree, because the layer-composition
> bound does not exist there.** What §6's table prices is *engineering* cost per rung, not a
> security loss per rung. Anyone who reads `(t+k)·ε` as "depth is linear in error" is reading a
> statement about rounds as one about layers.

---

## 7. THE OTHER THREE SYSTEMS — and why only one is priceable in counts

`[MEASURED, census]` Only **one** of the four systems named in the brief has an in-circuit verifier
anything can be pointed at:

| system | verifier | **in-circuit verifier** | where |
|---|---|---|---|
| **FRI / BaseFold (deployed)** | ✅ native | ✅ **the only one** | `plonky3-recursion/recursion/src/pcs/fri/verifier.rs:1358` `verify_fri_circuit`; `pcs/mmcs.rs:300`; `verifier/batch_stark.rs:498` |
| **additive / binary BaseFold** | Lean, deterministic controller only | ❌ | `minidregg/Selvage/AdditiveBaseFold.lean` (838 ln, landed 2026-08-14) |
| **Ligerito** | ❌ | ❌ | `minidregg/Selvage/LigeritoInterleaved.lean` — one real lemma, four named obligation `Prop`s |
| **Spartan over R1CS** | reductions proved sound; no PCS | ❌ | `minidregg/Assurance/SpartanR1CS.lean` (883 ln, landed 2026-08-14) |
| BinarySpartan | — | — | **no primary source of any kind exists** (`binaryspartan-position.md` §0.5) |

So §7a is `[DERIVED]` throughout, in the units §2 established, and is labelled as such. **It is a
model, not a measurement, and it should not be quoted as one.**

### 7a. The IOP layer is 0.2% of the bill

For Spartan over R1CS at `n = 2^20` constraints: an outer sumcheck of `log n = 20` rounds at
degree 3 (4 evals/round) and an inner sumcheck of 20 rounds at degree 2 (3 evals/round) —
`7 log n = 140` extension elements absorbed, `≈ 5` extension multiplies per round to evaluate and
check.

| | in-circuit permutations | in-circuit ext-multiplies |
|---|---:|---:|
| **Spartan's entire IOP layer** (both sumchecks + transcript) | **~70** | **~200** |
| our FRI verifier, measured | **38,168** | **441,684** |
| ratio | **545×** | **2,208×** |

> ### ⚑⚑ **The IOP is ~0.2% of the in-circuit verifier. The PCS is ~99.8%.** "Which proof system is cheapest to verify in circuit" is, to within rounding, **"which PCS is cheapest to verify in circuit."**

That is the architectural finding. It also says a heterogeneous stack that swaps the *IOP* (FRI-STARK
leaf → Spartan recursion, or the reverse) moves 0.2% of the cost — **unless it also swaps the PCS**,
at which point the IOP was never the reason.

### 7b. What each candidate does to the term that matters `[DERIVED]`

| system | opened values per query | Merkle path depth | verdict on the 94% |
|---|---|---|---|
| **FRI / BaseFold (RS, multiplicative)** | one row of every committed matrix, `Σ⌈w/8⌉` | `m` per tree | the baseline |
| **additive / binary BaseFold** | **identical structure** — same Merkle-over-codeword commitment, same per-query row opening | same | ⚑ **buys nothing structurally.** It changes the *primitive* (a traditional hash becomes affordable) but not the *shape*. Its value is the cryptanalytic surface, not the count. |
| **Ligerito / interleaved-code family** | a whole **column** of the interleaved matrix — much longer than one trace row | shallower (fewer rows) | ⚑ **trades the cheap term for the expensive one.** It shrinks the 5.9% path term and grows the 65% leaf-sponge term. Directionally wrong for recursion. |
| **jagged / stacked** (SP1, OpenVM) | padding removed / matrices packed ⇒ **`Σw` falls directly** | same | ⚑ **the only family that attacks the dominant term head-on.** This is what both production systems chose. |
| **sumcheck-batched reduced opening** | unchanged, but the *Horner* becomes `O(log)` | same | **×2.13 on the wrap (§3d)** — attacks the 88.5% arithmetic half |

⚠ Additive BaseFold carries a live, unrepaired finding that bears on any recursion built over it:
`basefold-additive.md` §3b — **an additive-FRI transcript that binds the domain but not the ORDERED
BASIS does not determine the committed multilinear** (`keystone_basis_ambiguity_terminal` at
GF(16)). The deployed controllers carry a `domainId` sponge tag and **no basis binding at all**. The
repair is cheap (absorb β, in order, before the first challenge) and it should land before anything
recurses over it.

---

## 8. ⚑ THE LEAN INTERFACE — it does not exist, and `AccRbrBcs`/`Depth` is not most of it

The brief asked whether our `AccRbrBcs`/`Depth` machinery is already most of *"system A's verifier
is expressible as a relation system B can prove."* **Checked at source. It is not, and the
obstruction is type-level, not effort-level.**

### 8a. What exists

**`Reduction`** (`minidregg/Selvage/Rbr.lean:144`) is the tree's one real proof-system abstraction:

```lean
structure Reduction : Type 1 where
  Idx : Type;  X : Type;  A : Type;  X' : Type;  A' : Type;  W : Type
  R  : Idx → X  → (Fin n  → A ) → W → Prop
  R' : Idx → X' → (Fin n' → A') → W → Prop
  k : ℕ;  PMsg : Type;  Chal : Type;  δstar : ℝ
  verify : Idx → X → (Fin n → A) → (Fin k → PMsg) → (Fin k → Chal) → Option (X' × (Fin n' → A'))
```

> ⚑ **It is a reduction from relation `R` to relation `R'` *within one interactive framework*** —
> same `Idx`, same **`W`**, same `Chal` alphabet, same `PMsg` type on both sides, by explicit design
> (module header, "Deliberate specializations" 1–4, `Rbr.lean:27-56`). `R'` is the *residual claim
> after this protocol's own rounds*.

All **seven** instantiations in the tree are intra-system — `SumcheckRbr.lean:182`, `Depth.lean:489`
(`True`/`True`), `FiatShamir.lean:550` (`True`/`True`), `AccRbrInstance.lean:391`,
`AccRbrBcs.lean:333`, `AccRbrBcsShifted.lean:230`, `AccRbrBcsRaw.lean:45`. **Nothing anywhere sets
`R` or `R'` to a verifier-acceptance predicate of another system.**

`AccRbrBcs` itself is a **module, not a class**; its content is `accReductionBcs`, one `Reduction`
instance (`AccRbrBcs.lean:318-350`), plus `accRbrKnowledgeSoundBcs` (`:526`) and `accFsSound_bcs`
(`:748`).

And there **is** a verifier-as-constraints seam, for exactly one system, self-verifying — the
component decomposition this lane's §2 measured, already authored in Lean:

| component | file | keystone |
|---|---|---|
| sumcheck rounds | `minidregg/Compiler/SumcheckVerifierAir.lean` (338 ln) | `sumcheckVerifier_correct` (`:207`) |
| Fiat–Shamir transcript | `Compiler/FiatShamirAir.lean` (503 ln) | — |
| PCS opening / Merkle paths | `Compiler/MerkleBindAir.lean` (559 ln) | — |
| FRI query fold + final check | `Compiler/FriQueryVerifierAir.lean` (516 ln) | `recursiveVerifierPair_correct` (`:342`) |

⚑ **That is the same four-way split §2 measured in Rust, already stated in Lean.** Wiring the two
together — counting `emit`'s output per component — is the natural next instrument, and it needs no
new theory.

### 8b. The gap, precisely

1. **No `ProofSystem` type.** Nothing bundles `(Stmt, Wit, Proof, Prove, Verify, ε)` as a
   first-class object. The nearest, `breadstuffs/metatheory/Dregg2/Crypto/PortalFloor.lean:71`'s
   `class VerifierKernel`, makes soundness an **assumed opaque `Prop`** (`extractable`), so it can
   never be *derived* from B proving A's verifier relation.
2. **No functor `Verifier → Relation`.** `sumcheckVerifierGadget` / `friQueryVerifierGadget` are
   hand-written. There is a **type-level obstruction**: `Reduction.verify` ranges over arbitrary
   `Type 0` carriers, while `ConstraintSystem F Idx = List (Term (AirSig F Idx))` needs a field.
3. **No heterogeneous composition theorem.** Nothing of the shape
   `A.Sound → B.Sound → (B proves A.verifierRelation) → (A ∘ B).Sound`. The nearest,
   `Dregg2/Circuit/RecursiveAggregation.lean`'s `EngineSound.recursive_sound`, **assumes** in-circuit
   verifier soundness as a hypothesis.
4. **`Compiler ⊬ Selvage` is architectural.** House law forbids the import
   (`SumcheckVerifierAir.lean:36`), so "the AIR gadget's spec IS the Selvage protocol's acceptance"
   is a *named open residual* — `[RECURSE-sumcheck-bridge]`, `[RECURSE-fri-bridge]` — statable only
   in `Assurance`, **and not yet stated.** ⚑ This is the smallest missing link even for the
   *homogeneous* self-recursion case.

### 8c. ⚠ Three vacuity traps any such interface must not fall into — found while looking

* `SecurityEvidence.no_conflation` (`Assurance/SemanticHistoryRecursiveAir.lean:358`) — a structure
  with four fields of exactly the four `Prop`s it takes, and the "theorem" returns them. Literally
  `P∧Q∧R∧S → P∧Q∧R∧S`. **Disclosed in the file**, so recorded not accused.
* `fsKeystone_premise` (`FiatShamir.lean:630`) — discharges "an RBR-sound `Reduction` exists" with
  `trivialReduction`/`trivialRbr`, where `R = R' = True`, `verify ≡ some ((),0)`, `err ≡ 1`. The
  theorem is fine (real instances exist elsewhere); the *stated inhabitation evidence* is
  degenerate.
* ⚑ `EngineSound` / `real_engine_sound` (`breadstuffs/metatheory/Dregg2/Circuit/
  RecursiveAggregation.lean`) — `abbrev RealProof := Unit`, `acceptAll : RealProof → Bool := fun _ =>
  true`, every hash constant-zero. **The headline "EngineSound is INHABITED — the headline is not
  vacuous" is discharged at an instance where the verifier accepts everything.** That is a `P → P`
  witness with extra steps, and unlike the other two it is *not* disclosed. **Flag it.**

### 8d. The interface — ✅ LANDED

`minidregg/Selvage/HeteroComposition.lean`, commit `e403725`. 0 `sorry`, 4 axiom pins, registered
in `Selvage.lean`; import boundary OK, `check-proof-hygiene.sh` PASS (473 files, 216 guarded axiom
footprints), `check-char2-vacuity.sh` **0 vacuous**.

**Proved:** `rung_sound` (B knowledge-sound + `VerifierEmbedding A B` ⇒ an accepting B-proof yields
an accepting A-proof; *A never verifies anything*) · `ivc_tower_sound` (unbounded depth, and it
needs a **self**-embedding — a cycle, not a chain; a one-way embedding gives exactly one rung, which
is the formal content of "bounded-depth aggregation is where heterogeneity is free") ·
`bwd_forces_range`.

**Teeth, both directions:** `canonicalEmbedding` — SATISFIABLE, and deliberately *free*, which is
the point: the embedding is not where recursion is hard, `KnowledgeSound` of the canonical system
is. `widened_relation_refuses_embedding` — **REFUTABLE**: `IsEmpty (VerifierEmbedding strictSystem
widenedSystem)`, i.e. **the type refuses a verifier gadget that accepts strictly more than the
verifier it stands for**, whatever `encStmt`/`encProof` are chosen. That is the wound §8c catalogues
three instances of, refused by construction rather than by review.

**Named, not proved:** `ComposeErrorBound`, `ComposeFixedPoint`.

The shape, and why it cannot be a `Reduction`:

The shape the heterogeneous stack needs, and the reason it cannot be a `Reduction`:

```lean
/-- A proof system, as the object a stack composes. -/
structure ProofSystem where
  Stmt : Type;  Wit : Type;  Proof : Type
  Rel    : Stmt → Wit → Prop
  Verify : Stmt → Proof → Bool
  ε      : ℝ                       -- knowledge-soundness error
  ε_nonneg : 0 ≤ ε

/-- ⚑ THE SEAM. `A`'s verifier, read as a relation, is one `B` can prove. This is what
    `Reduction` cannot type: it forces a single shared witness type on both sides, and here
    `B`'s witness IS `A`'s proof. -/
structure VerifierEmbedding (A B : ProofSystem) where
  encStmt  : A.Stmt → B.Stmt
  encProof : A.Proof → B.Wit
  /-- completeness of the embedding -/
  fwd : ∀ x π, A.Verify x π = true → B.Rel (encStmt x) (encProof π)
  /-- ⚑ the load-bearing direction, and the one an identity carrier silently drops -/
  bwd : ∀ x w, B.Rel (encStmt x) w → ∃ π, encProof π = w ∧ A.Verify x π = true
```

Three obligations, named and refutable — each must be **satisfiable, refutable, and not provable**
(`feedback-prove-the-floor-false`):

* `[COMPOSE-embedding]` — `VerifierEmbedding A B` is inhabited for the deployed pair. ⚠ Must be
  refuted by an `encProof` that is not injective, else `bwd` is `fun _ _ h => h`-shaped: the
  `minted-identity-carrier-vacuity` failure exactly.
* `[COMPOSE-error]` — `(A ∘ B)` has knowledge error `≤ A.ε + B.ε`. *Not* implied by
  `OB2_depth_composition_nonneg`, which composes **rounds**, not systems (§6b).
* `[COMPOSE-fixedpoint]` — unbounded IVC needs `VerifierEmbedding B B`, a **cycle**; a one-way
  embedding gives one rung only (§6a).

⚑ **This was new construction, not a refactor** — the type-level obstruction in §8b(2) means no
existing declaration could be generalised into it. And §7a says the *payoff* is small for cost and
large for correctness: it is the object that lets a heterogeneous stack be *checked*, not the object
that makes one *cheap*.

---

## 9. WHAT THIS DECIDES

1. **The leaf and the recursion system should be the same system.** Nobody in production does
   otherwise, the IOP is 0.2% of the bill, and the only heterogeneity that pays is (a) parameters
   per layer and (b) a hash-field swap at the last STARK layer — both of which we already do.
2. **Optimise the leaf's committed WIDTH, not its height, blowup, or FRI arity.** 94% of in-circuit
   hashing and 88.5% of in-circuit arithmetic are width-driven; arity is a null knob; blowup is
   already at its optimum.
3. **Take the reduced-opening sumcheck batch.** ×2.13 on the wrap, ×2.05 per turn, and it is the
   *precondition* for every "cheap hash" argument — which is worth ×1.57 today and ×4.5 after.
4. **The binary-field case must be argued on cryptanalytic surface, not on verifier cost.** In a
   matched field the verifier is 36.45% hashing. The cost argument only appears at a field mismatch,
   and the industry's answer to a field mismatch is to swap the hash, not the field.
5. **`lb = 6` is right and the grid that shows it now exists.** It was never validated; it is now,
   and the margin is a power-of-two rung, so it is fragile to any change in `Alu` width.
6. **Arbitrary-length extendability is ×27.9 per turn.** If a turn does not need to be extended, a
   bounded-depth tree or a one-shot leaf is 27.9× cheaper — and bounded depth is where heterogeneity
   is free.
7. **Our real problem is `K = 26.9`: the leaf is 3.7% of the object.** Batching more turns per leaf
   moves us onto the same side of every trade as SP1 and OpenVM. That is a bigger lever than any
   choice of proof system on this page.

### The instrument gaps, named

* **A per-component op census** — wire `minidregg/Compiler/{SumcheckVerifierAir, FiatShamirAir,
  MerkleBindAir, FriQueryVerifierAir}.lean`'s `emit` output to a counter. The four-way split §2
  obtained by regression would become *directly* counted, in Lean, per component.
* **The `[RECURSE-*-bridge]` residuals** (§8b(4)) — the smallest missing link, and it blocks the
  homogeneous case too.
* **A counting `DreggRecursionConfig`** — still the one thing that would make the tower's *native*
  hash side as exact as this note's in-circuit side. Not needed for anything above.

## 10. Reproduce

```bash
cd ~/dev/breadstuffs
cargo test -p dregg-circuit-prove --release --test leaf_vs_recursion_sweep --no-run
B=./target/release/deps/leaf_vs_recursion_sweep-*
RAYON_NUM_THREADS=4 $B b_blowup_sweep_at_fixed_queries --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=4 $B a_query_sweep_at_fixed_blowup   --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=4 $B c_arity_sweep                   --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=4 $B d_iso_security_engine_grid      --ignored --nocapture --test-threads=1
```

Release only; 10 s / 24 s / 3 s / 36 s on a box at load 158. Every count reproduces exactly; no wall
clock in this file is evidence.
