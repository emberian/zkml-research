# Every number, with its conditions

Written 2026-08-16 for codex. **This is the file that makes the rest of the
directory usable**, and its shape is dictated by the defect that produced it:

> ⚑ *"A note that says '13.13× faster' is unusable six hours later; a note that
> says 'prove ms at (lb, q, pow, rows, N)' composes forever."*
> — `docs/COST-MODEL.md`, "The model failing to populate — which is the real finding"

`COST-MODEL.md` was written to be the one model everything checks into, and
**it could not be populated from our own notes**: they recorded *conclusions*
("hash-bound", "25% is grind", "13.13× faster at 4096 rows") without the table,
the configuration, or whether `pow` was on. Everything below is the recovery.

---

## 0. How to read any number here

### 0.1 The schema every entry carries

| field | why |
|---|---|
| **configuration** | `(lb, q, pow, rows/workload, threads)`. A ratio without it cannot be composed. |
| **instrument** | permutation count · field-op count · circuit op census · wall clock |
| **machine + load** | absolute ms on a load-95 box is an upper bound at best |
| **N** | min-of-N, p50, p99 — never a mean over a contended box |
| **WORK or LATENCY** | ⚑ **the two may never be composed.** Separate columns, always. |

### 0.2 ⚑ Two tiers, and they are not equally trustworthy

**EXACT tier — permutation counts, field-op counts, circuit op censuses, proof
bytes.** Deterministic, hardware-free, contention-immune. This is not a claim,
it is proved twice:

- **On different hardware.** The hbox rig's count arm reproduces the recorded
  laptop tables **to the unit** — prover perms 27,814 / 54,862 / 108,958 /
  217,150 / 433,534 at b=3..7, verifier 3,698 / 3,812 / 3,926 / 4,040 / 4,154 —
  taken on an Intel i9-12900 at **load 3.97** against the M2 Max's **load
  16–95**. `notes/hbox-rig.md` §3.
- **Across build profiles.** The narrow-emission lane's debug and release builds
  produced **byte-identical count tables**. `docs/VERDICTS.md` §4.
- **Across independent instruments.** A wrap's in-circuit `poseidon2_perm` op
  count and its child's native verify permutation count are **38,168 = 38,168**,
  two instruments with no shared code path. `notes/recursion-tower-profile.md` §2.

**MEASURED tier — wall clock.** Secondary, and *wrong for two days* before that
was noticed. Every clock figure names its box below. `hash/arith` — the central
claim of two days — is exactly the quantity a busy machine corrupts most, because
hash and arithmetic degrade at different rates under contention.

⚠ **A derived quantity is only as clean as its dirtiest input.** A GPU lane's
"traffic-only" figures — the ones agreed to be the right thing to quote — are
computed by subtracting a **sync floor measured on the same loaded box**. They
inherit the contention, just less visibly. `docs/COST-MODEL.md`.

### 0.3 The two boxes

| | **laptop** | **hbox** |
|---|---|---|
| CPU | Apple M2 Max, 12 cores, 96 GB | 12th Gen Intel i9-12900, 24 logical, 123 G |
| topology | uniform | ⚑ **hybrid: cpus 0–15 = 8 P-cores × 2 SMT @5.0–5.1 GHz; 16–23 = 8 E-cores @3.8 GHz** |
| load during measurement | **16–95**, 36–41 login sessions | **1.14–4.0** |
| cell spread (max/min) | **2.1× across three runs** | **1.01–1.27×, ≤1.10× in 33 of 40 cells** |
| SIMD | NEON, `Packing::WIDTH = 4` free | ⛔ **WIDTH 1 (scalar) without `-C target-cpu=native`** |
| governor | — | `powersave`, 800 MHz–5.1 GHz ⇒ **an untimed warm-up is mandatory** |

Sources: `notes/phase-profile.md` §0.5, `notes/hbox-rig.md` §0 and §4.

⚠ **"16 threads" on hbox is 8 physical cores with hyperthreading.** Every
thread-count number from that box must say which side of 8 it sits on.

### 0.4 The four rules, and where they became mechanical

`circuit/tests/hbox_rig.rs` enforces `COST-MODEL.md`'s rules **by construction
rather than by exhortation** (`notes/hbox-rig.md` §1):

| rule | enforcement |
|---|---|
| counts primary, clock secondary | two arms: `Counts` has **no duration field**, `Timing` has **no count field** |
| a result carries its conditions | `Conditions` captured **before and after** every cell; no path emits a number without one |
| a percentage needs its denominator | ⚑ **`Share` cannot render without its phase-set string** |
| never compose work with latency | `Claim::Work` / `Claim::Latency` are distinct variants; **`compose()` returns `Err` on a mixed set** |
| a ratio needs `(lb, q, pow, rows, N)` | `pub struct Point { log_blowup, num_queries, pow_bits, effects, threads }` — the rule became a type |

⚑ **Why the two arms cannot share a run, as a measurement fact:** `CountingPerm`
bumps a relaxed `fetch_add` on a shared cache line once per permutation —
**217,114 atomics at b=6, landing in exactly the phase being measured.** A
counting run's milliseconds are not "slightly high", they are meaningless.

---

## 1. THE EXACT TIER

### 1.1 The prover permutation law

**Configuration:** workload `transferVmDescriptor2`, 1 Transfer, 64 columns ×
188 rows, `q = 19`, `pow = 0`, threads 1, release @ `a31590c378c8`.
**Instrument:** exact scalar-equivalent Poseidon2 permutation counter.
**Claim type: WORK.** Contention-immune; reproduced on both boxes.

```
    P(b) = 3381 · 2^b + 766          (prove − self-verify convention)
```

| b | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|
| law | 27,814 | 54,862 | 108,958 | 217,150 | 433,534 |
| measured on hbox | **27,814** | **54,862** | **108,958** | **217,150** | **433,534** |
| verifier perms | 3,698 | 3,812 | 3,926 | 4,040 | 4,154 |
| proof bytes (`rmp-serde`) | 301,904 | 311,918 | 321,428 | 331,386 | 341,212 |

Decomposition (`notes/hbox-rig.md` §2), each sub-column the same shape:

| phase | law | b=3 | b=6 | b=7 |
|---|---|---:|---:|---:|
| Merkle-commit | `3312·2^b − 3` | 26,493 | 211,965 | 423,933 |
| FRI-fold Merkle | `69·2^b − 3` | 549 | 4,413 | 8,829 |
| challenger | `736` (constant) | 736 | 736 | 736 |
| *three named phases* | `3381·2^b + 730` | 27,778 | 217,114 | 433,498 |
| **+ unspanned** (FRI-commit-other 3, query/open 3, residual 30) | **`3381·2^b + 766`** | **27,814** | **217,150** | **433,534** |

> ⚑ **THERE ARE TWO RECORDED "PROVER PERMUTATION" COLUMNS AND THEY DIFFER BY A
> CONSTANT 36.** Both are in our notes, both are called "prover perms". The `+36`
> is constant in `b`, so **it never changes a ratio, only an absolute** — which
> is exactly why it hides. A pin written at `c = 730` would have fired red on a
> correct prover. *Two phase sets wearing one name.* (`notes/hbox-rig.md` §2)

### 1.2 Per-phase permutation counts, laptop, `q = 19`

`notes/phase-profile.md` §7. Same instrument, `pow = 0` except the last column.

| phase | b=3 | b=4 | b=5 | b=6 | b=7 | b=6, pow=16 |
|---|---:|---:|---:|---:|---:|---:|
| Merkle-commit | 26,493 | 52,989 | 105,981 | 211,965 | 423,933 | 211,965 |
| FRI fold Merkle | 549 | 1,101 | 2,205 | 4,413 | 8,829 | 4,413 |
| open arith (challenger sampling) | 736 | 736 | 736 | 736 | 736 | 736 |
| **PoW grind** | 0 | 0 | 0 | 0 | 0 | **47,917** |
| verifier (self-verify) | 3,698 | 3,812 | 3,926 | 4,040 | 4,154 | 4,040 |
| **total** | **31,512** | **58,674** | **112,884** | **221,190** | **437,688** | **269,106** |
| of which SIMD calls | 6,756 | 13,518 | 27,042 | 54,090 | 108,186 | 66,069 |

**Blowup 6→3 is a 3.50× reduction in hash WORK** — exact, no clock. (The
contended-clock model said 3.61× for the system; only the count survives a busy
box.) `docs/COST-MODEL.md`.

⚑ **Packed/scalar split, measured not inferred** (`notes/phase-profile.md` §8):
at b=6 the prover's Merkle-commit is 211,965 perms **of which 9 are scalar**; the
verifier's 4,040 are **100% scalar**. That asymmetry is a concrete unclaimed 5×
on verify hashing.

⚑ **A trap on the record:** the grind is **SIMD-packed, 4 candidate witnesses per
permutation**. Assuming it is scalar makes the count-vs-rate cross-check appear
to fail by 6× and reads as a broken classifier.

### 1.3 The grind — exact, and it is a DISTRIBUTION not a number

**Configuration:** `query_proof_of_work_bits = 16` (deployed in 6 of 7 config
families; `recursion-verify` default is 14). `notes/grind-phase.md` §0b, §2.
**Instrument:** the returned witness *is* the exact trial count, because
`find_map_first` returns the globally minimal valid witness — **no clock, immune
to load 135.** **Claim type: WORK.**

| | mean | p50 | p90 | p99 | max over N |
|---|---:|---:|---:|---:|---:|
| **trials, `pow=16`, N=256 transcripts** | **67,486** | 53,173 | 149,417 | 277,677 | 398,257 |
| × theory `2^16` | 1.030 | | | | |
| packed perms | 16,872 | 13,294 | 37,355 | 69,420 | 99,565 |
| **ms at 758 ns/call** | **12.79** | 10.08 | 28.32 | 52.62 | **75.47** |

Tail checked against `e^−k` rather than assumed: observed `P(>1×/2×/3× mean)` =
0.402 / 0.133 / 0.039 at pow=16 (N=256) and 0.334 / 0.125 / 0.046 at pow=12
(N=1024), against 0.368 / 0.135 / 0.050.

- **p99 is 53 ms against a mean of 12.8 and a whole-prove budget of 69 ms.**
- **Worst of 256 draws: 75 ms** — larger than the whole prove.
- ⚑ **It is per-PROOF, not per-run.** A fixed transcript reproduces its own draw
  exactly. You cannot retry or benchmark your way past a bad draw.
- **A tower concentrates (`1/√n`); a leaf mint is ONE draw** — the worst case.
- **`sample_bits` delivers 15.999953 bits, not 16** (`30721/2013265921`), because
  `2^16 ∤ p`. A checked approximation rather than an unexamined one.

**Its draw across one parity ladder, one run** (`notes/phase-profile.md` §4) —
this is the sample that manufactured a false optimum:

| (lb, q) | (3,38) | (4,29) | (5,23) | (6,19) | (7,17) | (8,15) |
|---|---:|---:|---:|---:|---:|---:|
| grind ms | **40.8** | 10.1 | **0.04** | 8.2 | 31.9 | 40.0 |

The 40.8 ms draw is the **p96** — the ladder was not unlucky, it was ordinary.

**Grind critical path, `crit` = max batches any one worker scanned**
(`notes/grind-phase.md` §3; contention-free instrument, fixed transcript
`w = 83,061`, min of 5, box parallelism 12, load ~90):

| threads | A `find_map_first` (deployed) | scale | B `find_map_any` (upstream) | scale | C windowed min | scale |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 20,766 | 1.00 | 20,766 | 1.00 | 65,536 | 1.00 |
| 4 | 21,956 | **0.95** | 6,613 | 3.14 | 18,098 | 3.62 |
| 8 | 20,766 | **1.00** | 4,319 | 4.81 | 12,096 | 5.42 |
| **12** | **20,766** | **1.00** | 5,214 | 3.98 | **8,745** | **7.49** |

> ⚑ **Scale 1.00 — the deployed grind had NO parallelism at all**, while burning
> **5.9× the total work at 12 threads** (20,766 → 123,517 batches scanned).

**After the fix** (`11cff8852` / `00b2cf2d5`, all five grind sites, windowed
parallel min at `c = 1/4`): **critical path 10.6× mean / 11.8× p99 at T=12,
total work +12.6%**; BN254 outer **9.49×** (28,954 → 3,147 calls, +13% work).
⚑ **Latency and work in separate columns, and the honest inversion is that the
fix RAISES grind's share of prover WORK, 23.2% → 25.4% at lb=6.**
`docs/VERDICTS.md` §2.

**Post-fix spread cell, six draws at (lb 6, q 19, pow 16)**, `notes/hbox-rig.md` §3:

| amount | 50 | 51 | 52 | 53 | 54 | 55 |
|---|---:|---:|---:|---:|---:|---:|
| grind perms | 49,152 | 49,152 | 65,536 | 32,768 | 16,384 | 98,304 |

min 16,384 · max 98,304 · mean 51,883 · **spread 6.00×**.

> **Any "speedup" below 6× obtained by differencing two grind runs is noise.**

⚑ **Unplanned confirmation:** every draw is an exact multiple of
**16,384 = 2^16/4** — the landed grind window `c = 1/4`. The rig re-derived a
deployed parameter from permutation counts alone, without being told it existed.

**Exchange rate, two-sided and machine-checked** (`minidregg/Assurance/
TwoRegimeQueryBudget.lean` §7, kernel `norm_num` over ℚ, no `native_decide`):
16 grind bits cost **17 queries at UDR · 6 at JBR · 3 at the withdrawn CBR**, and
one fewer query in each case is strictly *less* sound than deployed.
⚠ **A cost argument that says "the grind replaces N queries" without naming its
regime has quoted one of 17 / 6 / 3 — they differ by 5.7× and the flattering one
is the withdrawn regime.**

### 1.4 Field-operation counts

**Configuration:** same workload as §1.1, `q = 19`, `pow = 0`.
**Instrument:** `RecordingDft` (records `(method, height, width, added_bits,
shift)` from a real proof) replayed **in order against a single**
`Radix2DitParallel<CountedBabyBear>`. `notes/field-op-counts.md`.
**Claim type: WORK.** Scalar-equivalent, **by construction** (`CountedBabyBear::
Packing = Self`, WIDTH 1).

| b | LDE commit (6 calls) | LDE quotient-eval (12 calls) | **DFT total** | DFT MUL only |
|---:|---:|---:|---:|---:|
| 3 | 1,725,147 | 62,255 | **1,787,402** | 594,362 |
| 4 | 3,266,179 | 118,502 | **3,384,681** | 1,131,161 |
| 5 | 6,348,387 | 231,284 | **6,579,671** | 2,205,191 |
| 6 | 12,513,091 | 457,424 | **12,970,515** | 4,354,115 |
| 7 | 24,843,075 | 910,856 | **25,753,931** | 8,653,691 |

⚠ **A count in this file may NOT be converted to milliseconds by multiplying by a
scalar-latency rate.** Doing so inflates arithmetic by the SIMD factor (~4× on
NEON) and **is exactly the error that would manufacture a hash-bound verdict.**
Both sides of the comparison are measured as **packed-path lane rates**.

**Counter self-validation** (`§G2`): counted ADDs equal the textbook
`(h/2)·w·log₂h` butterfly count with ratio **1.000 at every size**. MULs are
**0.783–0.847** of it — `dit_layer_twiddle_free` skips the multiply where the
twiddle is one. ⚑ **A hand derivation over-charges multiplies by 18–22% and gets
the adds exactly right**, and the gap *rises* with `h`.

**Extension primitives, counted not assumed** (`§G4`): ext×ext = 19 MUL + 12 ADD;
ext×base = 4 MUL; ext inverse = 23 MUL + 11 ADD + 1 INV. FRI fold = **28.0
multiplies per folded row** at arity 2, stable across heights.
⚠ Stated fidelity gap: the counting field takes generic `quartic_mul` (19) where
deployed uses `quartic_mul_packed` (20) — it **under-states** arithmetic by ~5%,
the conservative direction for a hash-bound claim.

**Open phase**, kernels counted and multiplicities derived *upward*
(P = 2 opening points per committed matrix, an over-count):

| b | mats | open MUL | open ADD+SUB | **open total** |
|---:|---:|---:|---:|---:|
| 3 | 18 | 1,973,660 | 1,755,662 | **3,729,332** |
| 6 | 18 | 9,435,548 | 8,737,294 | **18,172,852** |
| 7 | 18 | 17,963,420 | 16,716,302 | **34,679,732** |

Validated, not asserted: at b=6 it predicts 2.97 ms against §A's measured
3.545 ms — **84% of the phase's time explained by its counted operations.**

### 1.5 The hash-bound verdict as a conditional

`notes/field-op-counts.md` §5. **This is the shape to copy**: everything exact
except one measured constant.

> **The prover is hash-bound iff `Y > X`, where `X ≡ (M + r·A)/P` (exact,
> hardware-free) and `Y ≡ t_perm/t_mul` (the only place a clock enters).**
> `r = t_add/t_mul = 0.803`, measured.

| b | P | M | A | **X (exact)** | Y/X margin at Y=890 |
|---:|---:|---:|---:|---:|---:|
| 3 | 27,778 | 2,568,022 | 2,948,702 | **177.7** | **5.01×** |
| 4 | 54,826 | 4,170,805 | 5,006,558 | **149.4** | 5.96× |
| 5 | 108,922 | 7,376,803 | 9,122,270 | **135.0** | 6.59× |
| 6 | 217,114 | 13,789,663 | 17,353,694 | **127.7** | 6.97× |
| 7 | 433,498 | 26,617,111 | 33,816,542 | **124.0** | **7.18×** |

**Every approximation in X points the same way** (each makes hash-bound *harder*
to conclude): the open phase over-counts opening points; the counting extension
under-prices ext multiplies by 5%; `P` **excludes the grind** (including it at
b=6 takes X 127.7 → 104.6 and the margin 7.0× → 8.5×); `quotient eval` and
`lookup perm` are not counted at all.

**In the tower** the same conditional gives `X_tower ≈ 280` (L1) and `≈ 270`
(L3/L4) against the leaf's 177.7, i.e. **hash-bound at Y/X ≈ 3.1–3.3×, not
5.0–7.2×. The whole difference is one term, `log₂h`.**
`notes/recursion-tower-profile.md` §6.
⚠ **`Y` does not transfer to layer 4** — the BN254 outer MMCS is
`MultiField32PaddingFreeSponge<BabyBear, Bn254, _, 3, 2, 1>` (16 limbs per
permutation, BN254 `t=3`). **Layer 4 needs its own `Y`, never measured.**

### 1.6 The recursion tower — circuit op census

**Instrument:** ⚑ **a permutation counter is BLIND to in-circuit Poseidon2 by
construction** — an in-circuit permutation is an **AIR row**, not a
`permute_mut` call. The primary instrument is the circuit op census
(`Op::NonPrimitiveOpWithExecutor` by `executor.op_type()`).
`notes/recursion-tower-profile.md` §0a. **Claim type: WORK.**

**The identity the tower turns on, measured twice with no shared code path:**

| instrument | object | result |
|---|---|---:|
| permutation counter | the child's **native verify** at `(lb 6, arity 2, q 19, pow 16)` | **38,168** |
| circuit op census | the leaf wrap's **in-circuit** `poseidon2_perm/baby_bear_d4_w16` ops | **38,168** |

> ⚑ **A leaf wrap's Poseidon2 table IS the child's verifier, row for row.**
> Therefore *"verifier ×2.28" is not a verify-side price at all — it is a PROVE
> price, paid one layer up, as trace.*

**Child prove/verify at two engines** (same instrument):

| child engine | prove perms | verify perms |
|---|---:|---:|
| `(lb 6, arity 2, q 19, pow 16)` — deployed | **6,177,520** | **38,168** |
| `(lb 6, arity 2, q 19, pow 0)` | 6,062,832 | 38,168 |
| `(lb 2, arity 2, q 57, pow 16)` — the drop | **405,741** | **89,739** |
| `(lb 2, arity 2, q 57, pow 0)` | 389,357 | 89,739 |

⇒ **prover ÷15.23 (grind-free ÷15.57) · verifier ×2.351** on the *deployed
rotated* child at the *deployed arity-2 wrap engine*. (`blowup-drop.md` reported
÷15.19 and ×2.28 on the *unrotated* batch at arity 8 — same trade, different
object.)

**Layer geometry, real, from `get_airs_and_degrees_with_prep`:**

| L1 leaf wrap table | log₂ rows | main_w | prep_w | cells (main+prep) |
|---|---:|---:|---:|---:|
| Const | 12 | 4 | 6 | 40,960 |
| Public | 11 | 4 | 2 | 12,288 |
| Alu | 18 | 76 | 59 | 35,389,440 |
| **`poseidon2_perm/baby_bear_d4_w16`** | **16** | **300** | 24 | **21,233,664** |
| recompose | 18 | 4 | 2 | 1,572,864 |
| | | | **TOTAL** | **58,249,216** |

⚑ **Three denominators differing by 37 points on the same table** — every share
must say which:

| layer | **cells(main+prep)** | cells(main) | rows |
|---|---:|---:|---:|
| L1 leaf wrap (rotated transfer child) | **36.45%** | 48.36% | 11.00% |
| L1 leaf wrap (Mina accumulator child) | **36.45%** | 48.36% | 11.00% |
| L3/L4 apex-verifier / shrink | **53.98%** | 65.77% | 24.81% |

36.45% is invariant across two unrelated children because their `degree_bits`
are **exactly two rungs apart, table for table** — a structural invariant of the
leaf-wrap circuit, not a coincidence.

**Cost per layer** (`[DERIVED]`, ×2.430 calibration measured on the child where
both numbers exist, so it cancels in every ratio):

| | native Poseidon2 permutations |
|---|---:|
| L0 leaf prove, deployed `(6,19,pow16)` — **counted** | **6,177,520** |
| L1 leaf wrap, deployed — derived | **≈ 160,900,000** |
| **wrap / leaf** | **26.05×** (independent grid: **26.9×**) |

### 1.7 The in-circuit verifier, decomposed by regression

**Instrument:** `circuit-prove/tests/leaf_vs_recursion_sweep.rs`, exact op census
across a sweep; least squares with **max residual printed so linearity is a
finding, not an assumption.** Load average 158 while it ran and **no figure
depends on it.** `notes/leaf-vs-recursion.md`. **Claim type: WORK.**

Height sweep, fixed `q = 19`, arity 2, `m = log₂(max child LDE height)`:

| lb | m | perms | HornerAcc | Alu(all) | recompose |
|---:|---:|---:|---:|---:|---:|
| 1 | 9 | 37,123 | 390,716 | 441,304 | 160,263 |
| **6** | **14** | **38,168** | **390,716** | **441,684** | **160,263** |
| 8 | 16 | 38,586 | 390,716 | 441,836 | 160,263 |

> ⚑ `Δperms/Δm = 209 = 19 × 11`, **exactly constant at every rung**;
> `ΔHornerAcc/Δm = 0` and `Δrecompose/Δm = 0`, **exactly zero.**

Query sweep, `q ∈ {12, 19, 28, 38, 57}`:

| fit at `lb 6, m 14` | per-query | q-independent | max\|resid\| |
|---|---:|---:|---:|
| perms | 1,423.13 | 11,128.39 | 0.34 |
| **HornerAcc** | **20,564.00** | **0.00** | **0.00** |
| Alu (all) | 20,861.00 | 45,325.00 | 0.00 |
| recompose | 2,581.04 | 111,222.10 | 2.70 |

**The 38,168 split:**

| component | scales as | perms | share |
|---|---|---:|---:|
| transcript absorption of OOD values + grind | width | 11,128 | **29.2%** |
| per-query Merkle LEAF sponge, main round | `q · Σw` | 8,911 | **23.3%** |
| per-query Merkle LEAF sponge, other rounds | `q · Σw` | ~15,887 | **~41.6%** |
| per-query Merkle PATH compressions | `q · m` | 2,242 | **5.9%** |

> ⚑⚑ **94.1% of in-circuit permutations and 88.5% of in-circuit arithmetic scale
> with the child's COMMITTED WIDTH. 5.9% with height, blowup and FRI structure
> combined.** This **refutes `recursion-tower-profile.md` §4b's own prose**
> ("most in-circuit permutations are 2-to-1 compressions along query paths") —
> corrected at source.

**Folding arity is a null knob** (measured, so it stops being an open question):
arity 2 → 4 → 8 gives perms 38,168 → 37,404 → 37,404 (−2.0%) and Alu 441,684 →
442,496 → 443,199 (**+0.2/+0.3%**), no table changing power-of-two rung.

**The engine grid — `(leaf prove) + (wrap)`, which had never been computed:**

| lb | q | leaf prove | wrap prove | **TOTAL** | wrap/leaf | vs `lb 6` |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 57 | 405,741 | 509,966,254 | 510,371,995 | 1256.9× | **2.96×** |
| 3 | 38 | 790,526 | 262,806,405 | 263,596,932 | 332.4× | 1.53× |
| **6** | **19** | **6,177,519** | **165,980,897** | **172,158,416** | **26.9×** | **1.00×** |
| 8 | 15 | 24,647,209 | 165,980,897 | 190,628,106 | 6.7× | 1.11× |
| 12 | 10 | 394,041,001 | 90,813,727 | 484,854,728 | 0.2× | 2.82× |

⚠ Named confound: the leaf-prove fit `P(lb) ≈ 96,196·2^lb + 20,956` has **two
points differing in `q` as well as `lb`**, so `q`'s small open-phase effect is
folded into the coefficient. The dominant term is `2^lb`; the confound is named,
not eliminated. ⚠ **And the minimum is a power-of-two rung, not a smooth
optimum** — `Alu` drops `2^19 → 2^18` exactly between lb 5 and lb 6, which is
the entire 1.54 → 1.00 step.

**Extendability, priced:** one-shot 6,177,519 (1.0×) · bounded-depth ≈172.2M for
d=1 · **unbounded IVC 172,158,416 = ×27.9 per turn, paid whether or not any
chain is ever extended.**

**The IOP is 0.2% of the bill** `[DERIVED, labelled as such]`: Spartan's entire
two-sumcheck IOP at `n = 2^20` is **~70 in-circuit permutations / ~200 ext
multiplies** against our FRI verifier's **38,168 / 441,684** — ratios **545× and
2,208×.** Only FRI has a reachable in-circuit verifier today; the rest are
Lean/paper-only.

### 1.8 AIR cells per hash invocation

**Instrument:** `size_of::<*Cols<u8>>()` read out of our pinned Plonky3
(`rev 82cfad7`), rows/invocation from each `generation.rs`. **Two independent
derivations agreed exactly on every overlapping cell.** `notes/hash-landscape.md`
§1a. **Claim type: WORK.**

| hash | rows/invocation | main cols | **cells/invocation** | **R** |
|---|---:|---:|---:|---:|
| **Poseidon2-w16** (ours, deployed) | 1 | **300** | **300** | **1.0×** |
| **Blake3** (`p3-blake3-air`) | 1 | 9,168 | **9,168** | **30.6×** |
| **Keccak-f** (`p3-keccak-air`) | **24** | 2,633 | **63,192** | **210.6×** |

⚠ **Units are the main way this table goes wrong.** R1CS constraints, Plonkish
gates and AIR cells are different units and not interchangeable; prime-field
in-circuit numbers are **not comparable across fields** (the same Poseidon2 is
**16,837 R1CS emulated BabyBear-in-BN254 and 187 R1CS BN254-native — 90×**, and
nothing about the hash changed).

⚑ **A width comparison inverts a cost comparison**: BabyBear α=7 REG=0 is 157
cols at blowup 8 = **1,256 blowup-cells**, *worse* than REG=1's 298 cols at
blowup 4 = **1,192**.

⚑ **`R` is a property of the arithmetization, not of the hash**: the same two
primitives price at **102× in R1CS · ~31–56× in a bit-decomposed AIR · ~3.2×
under a lookup argument** (Reinforced Concrete 2021/1038 Table 1: Poseidon 633
Plookup gates vs Blake2s 2,000). ⚠ That last one is **a pointer, not a result** —
Blake2s not Blake3, Plookup gates not AIR cells, units unreconciled.

---

## 2. THE MEASURED TIER — every number carries its box

### 2.1 Laptop per-phase table — `q=19, pow=0`, single-threaded, per-phase min of 21

**Box: M2 Max, load 16–95, 36 sessions. `RAYON_NUM_THREADS=1`** (the
multithreaded run on this box was *unusable* — it measured `lb=7` as faster than
`lb=6`). **Ratios are the deliverable; the absolute ms are not.**
`notes/phase-profile.md` §2. **Claim type: LATENCY.**

| phase (ms) | b=3 | b=4 | b=5 | b=6 | b=7 | b=8 |
|---|---:|---:|---:|---:|---:|---:|
| LDE commit *(arith)* | 0.750 | 1.604 | 4.392 | 7.710 | 16.647 | 27.277 |
| LDE quotient-eval *(arith)* | 1.445 | 3.357 | 6.109 | 12.925 | 26.416 | 44.331 |
| **Merkle-commit *(hash)*** | **4.696** | **9.579** | **21.479** | **42.509** | **81.578** | **148.305** |
| quotient eval *(arith)* | 1.135 | 1.161 | 1.360 | 1.283 | 1.305 | 1.168 |
| lookup perm *(arith)* | 0.211 | 0.207 | 0.237 | 0.246 | 0.239 | 0.234 |
| FRI fold *(arith)* | 0.032 | 0.041 | 0.054 | 0.072 | 0.123 | 0.181 |
| FRI fold Merkle *(hash)* | 0.166 | 0.296 | 0.621 | 1.198 | 2.225 | 3.909 |
| query/open phase | 0.049 | 0.056 | 0.064 | 0.068 | 0.073 | 0.071 |
| open arith | 1.229 | 1.472 | 2.320 | 3.545 | 5.463 | 8.714 |
| prove residual (unspanned) | 0.405 | 0.409 | 0.485 | 0.485 | 0.522 | 0.493 |
| **prove total** | **10.33** | **19.77** | **37.29** | **72.09** | **135.05** | **236.87** |
| verifier (standalone) | 4.221 | 4.446 | 5.176 | 5.167 | 5.189 | 4.700 |

- **`b = 2` is not in the feasible set** *at the time this was taken*: a degree-7
  S-box needed `log_blowup ≥ 3`, and at lb=2 `create_config_with_fri` did not
  refuse — it returned a config whose proof failed its own self-verify with
  `OodEvaluationMismatch { index: Some(1) }`. ⚠ **That floor was an upstream
  `p3-fri` bug** (see §3).
- **The query/opening phase is 0.05–0.07 ms — essentially free on the prover
  side.** `MerkleTreeMmcs::open_batch` copies stored sibling digests and hashes
  nothing; the query-phase hashing is the *verifier's*. **Tripling queries to hold
  soundness at lower blowup costs essentially nothing**, and that is not visible
  anywhere in the soundness discussion.
- ⚠ **The estimator is a per-phase minimum over reps and does not sum to any
  observed prove time.** Under preemption each phase inflates independently.
- ⚠ **Un-instrumented code is invisible as a phase.** `Pcs::commit` carries no
  span, so bit-reversal and `to_row_major_matrix` copies land in `prove_batch`'s
  own self time — the 0.4–0.6 ms residual. Real work, not error.

**Derived `hash/arith`** (hash = Merkle-commit + FRI-fold Merkle):
1.013 / 1.259 / 1.527 / 1.695 / 1.670 / 1.858 at b=3..8, i.e. **no crossover in
range; extrapolates to b ≈ 2.9.**
⚠ **Superseded by the LDE batching**: `hash/arith` at b=3 moves **0.902 →
1.224** and the crossover shifts **b≈2.9 → b≈2.5** (`docs/COST-MODEL.md`).

**Trace-height sweep** (`pasta-fpmul-sound`, 190 declared → 694 committed
columns, `q=19`, `pow=0`, ⚠ **load 85–95, magnitudes soft, direction is not**):

| log₂ h | 6 | 8 | 10 | 12 |
|---|---:|---:|---:|---:|
| hash/arith at lb=3 | 1.51 | 2.53 | 2.74 | **2.81** |
| hash/arith at lb=6 | 6.23 | 7.54 | 7.07 | **6.85** |

**"Wider/taller traces will make it arithmetic-bound" is false for this
implementation** — the Merkle leaf is a `PaddingFreeSponge` over the whole row,
so it costs `⌈w/8⌉` per row and scales as `w·h·2^b`, the same shape as the LDE.

### 2.2 hbox clock arm — the first defensible timing this project has taken

**Configuration:** `(lb, q 19, pow 0)` — **grind excluded and named as
excluded.** `transferVmDescriptor2`, 64 cols × 188 rows. Release @ `a31590c378c8`
with `-C target-cpu=native` (**packing width 8.18**), cpus 0-15 (P-cores),
governor powersave, nice 15, **N=9 per cell after one untimed warm-up**, one
process per thread count. Values are **min ms**. `notes/hbox-rig.md` §4.
**Claim type: LATENCY.**

b=6, min ms:

| threads | cold caller | vs T=1 | INSIDE pool | vs T=1 | pool/cold |
|---:|---:|---:|---:|---:|---:|
| 1 | 39.801 | 1.00× | 34.925 | 1.00× | 1.14× |
| 4 | 21.119 | 1.88× | 16.109 | 2.17× | 1.31× |
| **8** | **20.553** | **1.94×** | **15.512** | **2.25×** | 1.32× |
| 16 | 31.650 | **1.26×** | 19.067 | 1.83× | 1.66× |

b=7, min ms: T=1 74.213 / T=4 **34.854 (2.13×)** / T=8 39.187 / T=16 54.748.

> ⚑ **T=16 is 1.54× WORSE than T=8 at b=6 and 1.57× worse than T=4 at b=7.**
> `taskset -c 0-15` is 8 physical P-cores × 2 SMT, so a 16-thread pool puts two
> workers on every core and they fight. **The optimum is 4–8; the default is a
> pessimization.** Anyone running this prover at default rayon threads on that
> box has been paying up to 1.57×.

⚠ And it is why **threads had to be a recorded condition**: a curve taken only at
1 and "default" reports this prover as scaling badly, when it scales ~2.2× to 8
threads and then falls off a topology cliff.

### 2.3 The conversion rate `Y` — the only clock in the hash-bound verdict

**Estimator: min over N = 4,000 windows of 4,096 packed operations each, one
thread.** Short windows, many of them — a window is ~3 µs, so a clean sample
needs one un-preempted window out of four thousand. **An 80 ms whole-prover
timing has no such escape, which is the whole reason this is the only timing in
the lane.** Both sides in packed-path, per-lane, scalar-equivalent units.
`notes/field-op-counts.md` §4.

| quantity | value |
|---|---:|
| packed multiply | 0.722 ns/call = **0.1805 ns / scalar-equivalent multiply** |
| scalar multiply | 0.661 ns (**SIMD factor 3.66×**) |
| packed add | 0.580 ns/call = **0.1450 ns / scalar-equivalent add** |
| packed Poseidon2 | 648.19 ns/call = **162.05 ns / scalar-equivalent permutation** |
| scalar inverse | 103.5 ns = **573 multiplies' worth** |
| **Y = t_perm / t_mul** | **897.6** |

**Y across working sets** (min of 200 windows each): 32 KB → 1160.9 · 512 KB →
1095.7 · 4 MB → 1005.2 · **16 MB → 889.8**. ⚑ **Y moves only 1.3× across a 512×
change in working set**, so the cache-vs-DRAM hazard is real but **bounded**, and
the verdict uses the floor 890, not the flattering 1161.

⚑ **Y is not a free parameter**: a Poseidon2-16 permutation is ≈**564
multiplies** of arithmetic, so a *time* ratio of 898 against a *count* ratio of
564 is the right shape — the excess is the additions and round-constant adds.
⚠ Comparing a packed permutation against a **scalar** multiply gives Y ≈ 245
instead of 898 — **a 3.7× error in the quantity the whole verdict turns on.**

Older, coarser rates still in circulation, with their conditions:
Poseidon2 rate on the laptop, min of 4,000 windows × 512 permutations —
**scalar 938 ns/perm, packed×4 758 ns/call = 189 ns/lane, SIMD factor 4.95×**
(`notes/phase-profile.md` §7).

### 2.4 ⚑ What the counts expose that no clock could

At b=6, q=19, pow=0 — per-phase measured ms against counted work
(`notes/field-op-counts.md` §6):

| phase | counted work | predicted ms | measured ms | **explained** |
|---|---|---:|---:|---:|
| Merkle-commit + FRI-fold Merkle | 216,378 perms | 35.06 | 43.71 | **80%** |
| open arith | 9.44 M mul + 8.74 M add | 2.97 | 3.55 | **84%** |
| **LDE commit (6 calls)** | 4.18 M mul + 8.33 M add | **1.96** | **7.71** | **25%** |
| **LDE quotient-eval (12 calls)** | 0.17 M mul + 0.28 M add | **0.073** | **12.93** | **0.6%** |

> ⚑ **The hash side behaves like its count; the LDE does not.** The retraction
> that produced this instrument reasoned the *opposite* (hash memory-bound,
> arithmetic cache-resident) — right that the clock was unreliable, **wrong about
> which side it was unreliable for.**

**A phase carrying 3.5% of the arithmetic is measured at 63% of the time.** Per
call the two LDE phases cost 1.285 ms and 1.077 ms while their per-call *work*
differs by **27×**. ⇒ **the cost is per-CALL and per-narrow-matrix; the fix is a
LAYOUT change, and an arithmetic optimisation aimed there buys nothing.**

⚠ **An instrument that did NOT work, reported as such**: `§G5` replayed each
recorded geometry as a standalone kernel, min-of-25. **Every geometry hit the
same ~2.7–6.0 ms floor** — a 14,788-op call measured 3,773 µs and a 903,884-op
call measured 3,625 µs, i.e. **61× the work in less time.** Scheduling artifact
at load 50–80. **The `ns/op` column it prints is not evidence and is not used.**

### 2.5 The LDE layout change — landed, and the mechanism was not what the counts implied

`docs/COST-MODEL.md`. **Claim type: LATENCY** (arithmetic moves −0.11% total).

- **Coset-twiddle tables: REFUTED as the mechanism.** Width-independent in counts
  exactly as predicted — **and ~zero on a clock** (cold-vs-warm sign-random at all
  14 geometries). ⚑ ***A width-independent counted term is not thereby the cost.***
- **Confirmed by construction**: hold output size `h·2^b` constant and slide the
  split — **butterfly work FALLS 4× while the clock RISES 34×.**
- **Identified**: rayon's cold hand-off (`in_worker_cold`), paid per dispatch by a
  caller that is not a pool worker. Same workload inside `ThreadPool::install` is
  **11–27× faster.**
- **Landed**: **phase 3.57–4.07× single-threaded, whole prove 1.19–1.75×** at
  default threads; proof bytes **byte-identical at b=2..8**; no wire change, no VK
  rotation, no re-emit.
- ⚑ **The absolute gain is ~98% a cold-hand-off artifact**: at b=6 it saves
  **6.05 ms from the caller thread and 0.137 ms from inside the pool.**
- ⚑ **The bigger prize, measured and deliberately not taken**: running the whole
  prover inside `ThreadPool::install` measures **2.2–2.5×** on the laptop and
  **1.14–1.80×** on hbox — *the number it was sold on is ~1.5× optimistic*, which
  is about what one expects from a ratio taken at load 16–95.

### 2.6 The native hash swap — 5.82×

**Configuration:** our pinned Plonky3's `keccak-air/examples/
prove_goldilocks_poseidon2` vs `prove_goldilocks_keccak` — **same `KeccakAir`,
same Goldilocks, same `NUM_HASHES = 1365`, same FRI parameters, differing in
exactly one thing: the Merkle/challenger hash.** Whole-binary wall clock, laptop,
load 17–63. `notes/hash-landscape.md` §4. **Claim type: LATENCY.**

| Merkle/challenger hash | runs | **min** | spread |
|---|---:|---:|---|
| Poseidon2Goldilocks\<8\> | 6 | **40,195 ms** | 40,195–60,864 (**43%**, load-sensitive) |
| Keccak-256 | 5 | **6,907 ms** | 6,907–7,024 (**1.7%**) |

⚠ **This is Goldilocks Poseidon2-w8, not our BabyBear w16, on a Keccak-AIR
workload far more hash-heavy than our descriptor batch. 5.82× is an upper bound
on the effect; our geometry shows less** — the derivation from our own shares
says **1.54–2.27×**. Independently corroborated at **1.69× ST / 1.26× MT** by the
Binius paper's own Plonky3 A/B (2023/1784 §5.4, identical 4.010 MiB proof).

Older native rates, laptop: Merkle commit of 2^15 × 135 BabyBear — Blake3
**36.3 ms (8.2 ns/elt)**, Keccak 50.1, **Poseidon2 100.9 ms (22.8 ns/elt)**,
Rescue 1660 (`notes/fast-systems-recon.md`). ⇒ `ρ_nat = 2.78`, **a contended-box
clock ratio of two hash workloads** — the pair least corrupted by contention, and
both sides equally so.

### 2.7 Numbers narrowed to shape and sign only

**GPU fusion** (`docs/VERDICTS.md` §4b, `notes/arena-consolidation.md`): the same
cell varies **up to 2.1× across three runs** (50 MB fused: 33.6 / 69.2 / 39.0 ms),
so the lane narrowed its own claim to **shape and sign**: fusion wins 36/36 cells,
the win grows with size, the K-sweep asymmetry is monotone in every run. **Not a
calibrated speedup.** ⚠ Its traffic-only figures subtract a sync floor measured
on the same loaded box.

**The grind's `pow` vs `q` ladder** (`notes/grind-phase.md` §4): the byte and
verify columns are usable (**`dB/dq` = 5,826 B/query · `dV/dq` = 0.265 ms/query**,
the byte slope within 8% of an independent fit); ⚠ **the prove-ms column of that
same run is garbage and is not quoted** — it read 401 / 602 / 414 / 469 / 383 ms
across q = 36→15, non-monotone, ±100 ms of contention noise against a real signal
of ~0.05 ms. *Naming which column of your own run is garbage is the point of
running two arms.*

---

## 3. ⚑ SUPERSEDED, RETRACTED, OR MIS-UNITED — the flag list

**Do not quote any left-hand number without the right-hand column.**

| the number in circulation | what it actually is | superseded by |
|---|---|---|
| **"13.13× at 4096 rows"** (blowup 6→2) | **wall clock on a contended box, and a DIFFERENT WORKLOAD** — one descriptor (`pasta-fpmul-sound`) at 4,096 rows, not the IR-v2 descriptor batch. The *same case* re-run reads **7.78×** at load 30–52. **The two workloads must not be composed.** | `notes/blowup-drop.md` §5, §5b; counts say **15.19× fewer prover permutations** on the batch, **3.50× in hash WORK** for 6→3 |
| **"2.11× prove"** (Poseidon2 in-AIR narrowing) | **a wall-clock number.** In counts: **2.3439× committed cells but only 1.9733× prover permutations** per chip, flat in height to four figures — the quotient and FRI terms do not follow the width | `docs/VERDICTS.md` §4. **Per-batch it is 1.0763×**, and the deployed-leaf figure is **1.077×** |
| ⚠ the same lever, third denominator | **"1.1023×" is reachable by an honest-looking choice** — stopping at main traces, when the prover commits three rounds and narrowing shrinks only the first | `docs/VERDICTS.md` §4 |
| **"the tower is ~75% in-circuit Poseidon2"** | **not reached at any denominator on any layer.** Leaf wrap **36.45%** of cells(main+prep); apex/shrink **53.98%**. The closest to 75 is the apex layer's *main-only* **65.77%** — the flattering half of a pair | `notes/recursion-tower-profile.md` §3c |
| **`permEmissionNarrow` "approaches 1.97× in the tower"** | **1.000×.** The tower's Poseidon2 is upstream `p3-poseidon2-circuit-air`, **not** the Lean `CHIP_TABLE_AIR_JSON` the lever re-emits — *a display-name collision inside a cost model*. Its only reach is a 1.34% cut the power-of-two padding absorbs whole | `notes/recursion-tower-profile.md` §4 |
| **"grind is ~25% of a prove"** | **b-dependent and denominator-dependent.** Clock at the deployed point: **15.5%** at b=6, **41% at b=4, 56% at b=3**. The ~25% was true at *some* b and quoted as if global | `docs/COST-MODEL.md` |
| **"grind is 18% vs 23%"** — half a day of argument | **two different numerators over near-identical phase sets.** 18.1% = **47,917 (one draw)** / 265,031; 23.2% = **65,536 (the distribution MEAN)** / 282,686. *[My arithmetic — the notes record the gap as unresolved and decline to average it away.]* The recorded lesson stands: **a percentage without its denominator is not a measurement** | `docs/COST-MODEL.md` "Denominator disclosure"; `notes/blowup-drop.md` §5 |
| **"the exchange rate is 78–308×"** | **counted field multiplications.** Measured in wall clock: **54.68 ns per marginal committed felt vs 10.97 ns per value per sumcheck layer ⇒ ~5×** at lb=3 — hashing SIMD-vectorizes harder than folding does. **Every plan priced against 78–308× as a time budget needs re-pricing** | `notes/poseidon2-virtualization.md` §4; `docs/VERDICTS.md` §4 |
| **"net ≈65× worse per turn"** (the blowup drop across the tower) | ⚑ **65× is the ratio of the LOSS to the SAVING.** The per-turn **total** goes 27.05 → 86.72 leaf-proves = **×3.21**; an independent grid says **×2.96**. *It had already propagated into a note's summary and a downstream lane brief before being caught* | `notes/recursion-tower-profile.md` §5b; `notes/leaf-vs-recursion.md` §4c |
| **"the four landed wins"** | **two of the four are NOT CUT OVER.** `IR2_FRI_LOG_BLOWUP` is still 6 and `CHIP_WIDTH` is still 386. The two that *are* landed are both LATENCY claims; the two carrying WORK claims are the un-landed ones | `notes/hbox-rig.md` §5 |
| **"lb=4 is the measured optimum blowup"** | **a grind draw.** At `pow=0` the ladder is strictly monotone — 14.9 / 20.3 / 34.9 / 67.9 / 120.6 / 243.3 ms — and **lb=3 is fastest by 1.4×**. The published lb=3 point paid a 40.8 ms grind against lb=4's 10.1; **that 30 ms of coin flip was the whole reported optimum.** (The published `prove` column also included a full self-verify, 4.1–8.6 ms) | `notes/phase-profile.md` §5 |
| **"the degree-7 S-box needs `log_blowup ≥ 3`"** | ⚑ **an upstream `p3-fri` bug we had frozen as a law** — one `.bit_reverse_rows()` too many in the extrapolation path. **All twelve survey descriptors now prove AND self-verify at `(2,57)`** | `docs/VERDICTS.md` §7.0 |
| **`LDE quotient-eval` is `get_evaluations_on_domain`'s slow path** | **that path is never taken — zero `coset_idft_batch` and zero `coset_dft_batch` at every blowup.** The phase is the twelve width-4 quotient-CHUNK LDE commits | `notes/field-op-counts.md` Finding 1 |
| **"most in-circuit permutations are Merkle-path compressions"** | **5.9%.** A model carried in, not a count | `notes/leaf-vs-recursion.md` §2c |
| **"16× fewer committed elements"** (H2, single-prime) | derived independently as **4.80× padded**, which makes the 109-bit joint prime **3.85× worse rather than break-even** — the verdict hardens, the number was too generous to the losing side | `notes/h2-verdict.md` |
| **"lazy accumulation is free" (0.88×)** | **a COLUMN ratio** (single-prime-109 lazy ÷ RNS-3-limb lazy). In-tree the lazy fold is 0.84× at B=256 and **break-even at the deployed B=4.** *Several notes cited this cell for a claim it does not make* | `notes/h2-verdict.md`; `notes/fold-as-opening.md` §6 |
| **`fold_add` as one opening, "690×"** | **ratio = B, PROVER-SIDE ONLY, and B is 4 in deployment ⇒ 4.2×** | `docs/VERDICTS.md` §4 |
| **"BinarySpartan 410k hashes/sec" beside "6.2 ms latency"** | ⚑ **a batched THROUGHPUT quoted beside a SINGLE-INSTANCE LATENCY — they differ by 41×.** 2 KiB + SHA-256 padding = 33 compressions; at 219,000 h/s that is **0.151 ms** of throughput-equivalent work against **6.2 ms** claimed. Both can be true; **quoting them together as one system's characterization is the error** | `notes/binaryspartan-position.md` §10.2; `docs/BINARY-POSITION.md` |
| **`apex_shrink_trace_anatomy.rs`'s "MODEL perms @blowup64"** | hardcodes `LOG_BLOWUP = 6` against a deployed `OUTER_FRI_LOG_BLOWUP = 3`. **Over-prices the shrink's hashing by exactly 8×** — 165,806,080 against 20,725,760 | `notes/recursion-tower-profile.md` §3d |
| **`WRAP-NATIVE-HASH-DECISION.md`'s "~11,000 in-circuit perms"** | its formula **hardcodes `q = 19`** and the apex runs **38**. Measured **22,626 = 2.06×** the recorded central value | `notes/recursion-tower-profile.md` §3d |
| **`[9,9,15,14,15]`** (apex degree_bits, in two docs) | measured **`[9,9,16,15,15]`** on a real 2-turn chain — **two tables a rung taller = 2× the committed cells.** Neither source states the chain length it was taken at, and chain length is exactly what moves it | `notes/recursion-tower-profile.md` §3d |
| **"the tower is h = 2^20"** | **no such constant exists.** Heights are emergent from the op-list and measured `2^11`–`2^20`. **Height is a property of the child** | `notes/recursion-tower-profile.md` §1 |
| **"+286-bit Poseidon2 margin"** | correct, **ours**, and **it is the Merkle-COMPRESS mode figure**. The cico-4 margin at the same parameters is **+83.7**. *Quoting the larger of a pair without its mode is the flattering-number habit* | `notes/hash-landscape.md` §3 |
| **"KoalaBear is worth ~3.36×"** | **measured ≈1.05× on the leaf prover.** Hash rate 1.33× is **counted multiplications** (~1.02× in wall clock); the 2× blowup was already inside another lane's 3.4×; ⚑ **the narrowing ratio INVERTS** — absolute committed felts go 157 → 164, **4.5% worse** | `docs/VERDICTS.md` §1b |
| **`map_write_chip` 227 ms as "corroboration"** | **it is not one** — a chip present-vs-absent comparison, not a materialize-vs-virtualize fork on the same relation | `notes/poseidon2-virtualization.md` §6 |
| **"the FRI verifier is 19–40% hashing"** vs **"94% hash"** | different objects. Measured on one real IR-v2 proof, hashing is **47% of prove at b=3 and 64% at b=8** — *the blowup knob moves the mixture but never flips it* | `notes/phase-profile.md` §3 |

---

## 4. COMPOSITION — and the one that refuses

**Rule: compose through the phase model, never by multiplying. And state the
order, because the order changes the value.**

| phase | scales with | kind |
|---|---|---|
| grind (PoW) | **nothing** | hash |
| LDE (coset NTT) | 2^b | ⚠ **mis-typed as "arith"** — 80% of its ms is movement |
| Merkle commit | 2^b | hash |
| sumcheck / fold | **nothing** | arith |
| query / opening | query count | hash |

⚑ **Rule 2 needs a companion: a proposed win must name its phase AND its unit.**
A phase whose milliseconds are 99% movement cannot be improved by a win
denominated in multiplications, and the model has no column that would catch that.

**The honest composition of the four landed wins** (`notes/hbox-rig.md` §5):

| win | phase | unit | landed at HEAD? | factor |
|---|---|---|---|---:|
| LDE layout (`a31590c37`) | LDE | **LATENCY** | ✅ | 3.57–4.07× phase |
| grind schedule (`11cff8852`) | grind | **LATENCY** | ✅ | 10.6× mean; 7.10× counted |
| blowup drop 6→2 | Merkle-commit | **WORK** | ❌ `IR2_FRI_LOG_BLOWUP = 6` | 15.19× |
| `permEmissionNarrow` | Merkle-commit | **WORK** | ❌ `CHIP_WIDTH = 386` | 1.076× per-batch |

```
── composing all four ──
REFUSED — this set mixes 2 WORK claims with 2 LATENCY claims.

── the WORK column ──   phase set = prover Poseidon2 permutations at (lb 6, q 19, pow 0)
                                  = 217,114; Merkle-commit = 211,965 = 97.6%
── composed: 1.0000× ──

── the LATENCY column ── phase set = prove wall clock at (lb 6, q 19, pow 16),
                         phase-profile.md §2 ⚠ CONTENDED LAPTOP, PRE-BATCHING. Shape only.
applied  LDE layout      phase 'LDE'   share 24.3% × 3.660×  ⇒ system 1.2141×
applied  grind schedule  phase 'grind' share 18.3% × 10.600× ⇒ system 1.1987×
── composed: 1.4554× ──
```

> ⚑ **`3.66 × 10.6 = 38.8×`. Composed through the model: `1.46×`. The naive
> product overstates by 26.6×.** `compose()` refuses the mixed set rather than
> returning a number — the rig working exactly as intended, against its author.

⚠ **Two caveats on that `1.4554×`**: its phase shares are **laptop-derived and
pre-batching**, so it applies the LDE win to a share that win has already changed;
and re-deriving the shares on hbox with `-C target-cpu=native` is the next
measurement.

**Order matters by 1.68×**: the grind fix is worth **1.15× alone** and **1.94×
after the blowup drop**, because the drop takes grind's share from 15% to 56%.
⚠ *Those figures come from the contended-clock composition retained as history.*

**Amdahl ceilings, so a silicon argument starts from a number**
(`notes/phase-profile.md` §9): LDE share of prove is 21.2 / 25.1 / 28.2 / 28.6 /
31.9 / 30.2% at b=3..8 and **20.8% at the deployed point** ⇒ a *perfect* NTT
accelerator buys **1.26× at the deployed point** and never more than 1.47×
anywhere in range. The MLE-fold engine is smaller still (FRI fold is
0.03–0.18 ms, **under 0.1% of prove**).

**And the derived system rate, with its conditions stated**: **~17,700 Poseidon2
permutations proven/second** = 38,168 in-circuit ops per wrap ÷ a **2.16 s wrap**
— **on a contended box, at b=6, before four landed fixes**. That is 12.4× off
BinarySpartan's SHA-256 throughput and 4.6× off Flock per-core.
⚠ **The compounded figure was deliberately not quoted**, because the wins
reshuffle phase shares rather than multiplying — *which the hbox rig then
confirmed by refusing to produce it.* `docs/RESEARCH-STANCE.md`.

---

## 5. ⚠ NUMBERS WHOSE CONDITIONS I COULD NOT RECOVER

These are quoted somewhere in the tree and **should not be re-quoted without
re-deriving the condition.** Listed so the gap is findable.

1. **The whole of `notes/speedup-ledger.md` Bin 1** — 17 rows of third-party
   speedups (packed sumcheck 2.78×, FRI-M61 vs KZG-BN254 3.8–5.7×, zkCNN 33.2×,
   VerfCNN 10×, Sparrow 3.2–28.7×, …). Each names a source but **none carries the
   source's box, workload size, or thread count**, and they are in at least four
   incompatible units. One row already carries its own refutation (small-value
   sumcheck: 2–3× **on BN254**, and its ancestor measured it going *the wrong way*
   at BabyBear-deg4). **Treat the whole bin as a reading list, not a cost table.**
2. **"the sumcheck is 2–17% of prover time"** (`docs/VERDICTS.md` §4). The range
   is quoted without the two configurations that bracket it.
3. **"the base→extension boundary is a measured ~3× cliff"** — the underlying
   measurement is Plonky3's own sumcheck bench at 2^22, `base_ext` 11.99 ms vs
   `ext_ext_packed` 35.40 ms = 2.95× (`notes/fast-systems-recon.md`), but **the
   box and N are not recorded** and it is quoted elsewhere as a bare "3×".
4. **"1.5×–2.3× per standalone proof"** for the native-hash swap (§2.6's `m_leaf`
   row). The **class size is an entry-point count (18 files), not an audit
   result** — the note says so. Nobody has asked, proof by proof, whether a
   circuit consumes that proof's hash.
5. **"FRI verification is ~100% hashing"** (`notes/fast-systems-recon.md`), quoted
   in several downstream arguments. The one place it *was* decomposed gives
   **~73%** — and that 73% is itself **derived** (measured count × measured rate),
   not read off a span, because the verifier's internals carry no sub-spans at our
   rev. `notes/phase-profile.md` §8 flags it as the one figure it would want a
   second instrument on.
6. **`ρ_nat = 2.78`** is used as an input to the entire `R*` crossover. It is a
   contended-box clock ratio; the crossover note says so and argues it is the pair
   least corrupted by contention. **It has never been re-taken on hbox.**
7. **The `1.4554×` latency composition's phase shares** — laptop, pre-batching,
   named as the last laptop-derived input in the whole composition and explicitly
   queued for re-derivation.
8. **The `×2.430` calibration** transporting the geometric leaf-sponge law to
   counted totals in the tower. It is measured on the child where both numbers
   exist and **cancels in every ratio**, but any *absolute* tower figure inherits
   it.
9. **"KoalaBear α=3 beats every BabyBear configuration by 1.8–1.9×"** — this is
   *blowup-cells*, a derived unit (cols × LDE blowup), not a measured prove time.
   Sound as stated; frequently re-quoted without the unit.

---

## 6. Where the instruments are

| instrument | file | what it gives |
|---|---|---|
| phase spans + permutation counter | `breadstuffs/circuit/tests/ir2_phase_profile.rs` (§A–§F) | per-phase ms, exact perms, packed/scalar split, rate micro-bench |
| field-op counter | `breadstuffs/circuit/tests/ir2_field_op_counts.rs` (§G1–§G5) | exact DFT/extension/open counts, `Y`, working-set sweep |
| grind | `breadstuffs/circuit/tests/grind_phase_measure.rs` (§G1–§G5) | trial distribution, `crit` thread scaling, pow-vs-q ladder |
| tower census | `breadstuffs/circuit-prove/tests/recursion_tower_profile.rs` | in-circuit op census per layer, the 38,168 identity |
| in-circuit decomposition | `breadstuffs/circuit-prove/tests/leaf_vs_recursion_sweep.rs` | height/query/arity sweeps, the engine grid |
| **the rig** | `breadstuffs/circuit/tests/hbox_rig.rs` | two-arm counts/clock, `Conditions`, `Share`, `compose()`, the self-check |
| crossover arithmetic | `notes/hash-landscape-scripts/crossover.py` | `R*`, every input cited to a committed note |
| exchange rate (Lean) | `minidregg/Assurance/TwoRegimeQueryBudget.lean` §7 | grind-vs-query, two-sided, kernel-checked over ℚ |

**Running the rig on hbox** — four environment settings are load-bearing and none
is optional (`notes/hbox-rig.md` §7). ⚠ **Never build in `~/dev/breadstuffs` on
hbox**: that is a co-tenant's tree at a different SHA with ~1900 dirty files, and
**`/` is 100% full**. Use the detached clone on `/tank`, `CARGO_HOME` on `/tank`,
`RUSTFLAGS="-C target-cpu=native"` (**or you measure the scalar prover**), and
`swarm-build`. The clock arm needs **one process per thread count** — rayon's
global pool is set once.

⚠ **The agent harness stops backgrounded jobs at ~50 minutes and a killed test
reports as `1 failed`, not as unrunnable.** Read the per-test label — `SIGTERM` /
`TIMEOUT` / a panic — before reporting any failure. `swarm/PREFLIGHT.md`.

---

## ⚠ ADDENDUM (2026-08-16): two headline numbers of mine are UNCONDITIONED

The lane's §5 flags nine figures whose conditions could not be recovered.
**Two of them are claims I have repeated as headlines**, and a reader should
know:

- ⚑ **"The sumcheck is 2–17% of prover time."** I have used this to re-price
  an entire literature. Its conditions are not recorded. **The conclusion may
  well hold — the count-based decompositions point the same way — but it is
  currently an unconditioned number and should be re-derived on the rig before
  anyone leans on it again.**
- ⚑ **`ρ_nat = 2.78`** (Poseidon2 : Blake3 native Merkle cost) — the anchor of
  the whole "why Poseidon2" argument. Same problem. ⚠ Note the *separately
  measured* in-circuit side (30.6×–210×) and the crossover (`R* = 2.0–4.5×`)
  are far enough apart that the verdict survives a wide error bar on ρ_nat —
  **but say that, rather than quoting 2.78 as if it were pinned.**

Also from §5: the whole of `speedup-ledger.md` **Bin 1 is 17 third-party rows
with no box, no size, no thread count, in four incompatible units.** Treat it
as a bibliography, not as data.

⚠ And a detector caveat worth carrying: **`check-char2-vacuity.sh`'s
declaration count appears at THREE different values in our notes** (29,085 /
29,263 / 29,276). **Quote it with its run or not at all** — I have used 29,263
several times without one.
