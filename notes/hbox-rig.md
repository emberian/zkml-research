# The measurement rig on hbox — and what it found before it measured anything

2026-08-14. Ember: *"performance measurements should be conducted carefully on
`hbox` (which is quieter) right now, and we should be thinking about building up
our systems to be able to run these experiments."*

Every wall-clock number this project has published was taken on a laptop at load
16–95 with 36 login sessions, and `docs/COST-MODEL.md` had to retract a whole
composition model because of it. The discipline that came out of that retraction
is written down. **What was missing is a rig that makes the discipline
automatic**, because a rule in a markdown file is a rule a lane forgets at 3am.

The rig is `breadstuffs/circuit/tests/hbox_rig.rs` (`32c162142`, `8983bd9ca`). It runs on
hbox from a detached clone at a pinned SHA, and all four of its cells are green.

### What it found, in the order it found it

| # | finding | where |
|---|---|---|
| 1 | **hbox is a hybrid P/E CPU** and `swarm-build`'s `taskset -c 0-15` is exactly its 8 P-cores. "16 threads" means 8 physical cores with SMT. | §0 |
| 2 | ⚑ **Thread scaling turns over: T=16 is 1.54× WORSE than T=8** at b=6. The optimum is 4–8; the default is a pessimization. | §4 |
| 3 | ⛔ **hbox was running the SCALAR Poseidon2** — no `-C target-cpu=native`, so packing width 1 instead of 8. Counts unaffected, **every clock several-fold wrong on the hash side**. | §3 |
| 4 | ⚑ **The grind cell had stopped falsifying** — same transcript three times, printing `spread 1.00×`, the opposite of its purpose. Fixed: real spread is **6.00×**. | §3 |
| 5 | The count arm **reproduces the recorded permutation tables to the unit on different hardware**, at load 4 versus the laptop's 16–95. | §3 |
| 6 | ⚑ **The four "landed wins" compose to `1.0000×` in work and `1.4554×` in latency** — and the two columns may not be added. Naive multiplication says 38.8×. | §5 |
| 7 | The self-check **fired red in production** before it went green, naming a 36-permutation constant to the unit. | §3 |
| 8 | The "un-taken prize" (`ThreadPool::install`) is real but **~1.5× smaller than advertised**: 1.14–1.80×, not 2.2–2.5×. | §4 |

---

## ⚑ 0. What hbox actually is — measured, and it changes how to read every number

Before any measurement: the box is not the box the brief assumed, and two of its
properties are load-bearing.

```
12th Gen Intel(R) Core(TM) i9-12900 · 24 logical CPUs · 123 G RAM
```

**⚑ It is a hybrid P-core/E-core CPU**, read out of `/sys`:

| cpus | topology | max clock |
|---|---|---:|
| **0–15** | 8 **P-cores** × 2 SMT threads | 5.0–5.1 GHz |
| **16–23** | 8 **E-cores**, no SMT | 3.8 GHz |

`swarm-build` applies `taskset -c 0-15`. **That is exactly the P-cores** — so the
house rule, adopted for memory safety, turns out to also be the correct
measurement decision, by accident. Two consequences nobody has been recording:

- **"16 threads" on hbox is 8 physical cores with hyperthreading.** A thread
  sweep past T=8 measures SMT, not scaling. Every thread-count number from this
  box must say which side of 8 it sits on.
- A run **not** wrapped in `swarm-build` is free to land on the 3.8 GHz E-cores,
  and a cell that migrates across the P/E boundary mid-run produces a spread that
  looks like variance and is actually a different processor.

The rig records the affinity mask (`/proc/self/status` `Cpus_allowed_list`) on
every cell and flags a mask that spans the boundary.

**Second condition, also unrecorded until now:** the governor is `powersave`,
range **800 MHz – 5.1 GHz**. A cold first iteration is measured at a fraction of
the clock of a warm one. The rig takes an untimed warm-up before every timed
series — omitting it is one of the ways a false optimum gets manufactured at the
low end of a sweep.

### State of the box at the time of writing

| | |
|---|---|
| load average | **1.14** — genuinely quiet, unlike the laptop |
| co-tenant | codex's HOL build **not running** at this time; `ps` shows nothing over 210 M |
| memory | 123 G total, but **57 G is ZFS ARC** (reclaimable), so ~68 G is really free |
| ⚑ **root disk** | **`/` is 100% full — 401 MB free.** The PREFLIGHT disk hazard, live on hbox right now. |
| `/tank/dregg-build` | 1.8 T free — **the only place a build can go** |

⚠ **Anything built in `~/dev/breadstuffs` on hbox will fail or fill the boot
volume.** That checkout is also a co-tenant's: a different SHA (`fdfef4613`) with
**1901 dirty files**. The rig is built from a detached clone at a committed SHA
on `/tank`, with `CARGO_HOME` also moved to `/tank` so the build never writes to
the full root volume.

---

## 1. What the rig is

`circuit/tests/hbox_rig.rs`. Six sections; the four rules of `COST-MODEL.md`
each enforced by construction rather than by exhortation.

| rule | how the rig enforces it |
|---|---|
| counts PRIMARY, clock SECONDARY | **two separate arms.** `Counts` has no duration field; `Timing` has no count field. Neither can be made to return the other. |
| a result carries its conditions | `Conditions` is captured before *and after* every cell and printed with it. There is no path that emits a number without one. |
| a percentage needs its denominator | every share carries its phase-set string. |
| never compose work with latency | `Claim::Work` / `Claim::Latency` are distinct variants and `compose()` **returns an error** on a mixed set. |

### ⚑ Why counts and clock cannot share a run

This is a measurement fact, not a style choice, and it is why the two-arm split
is structural. `CountingPerm` bumps a relaxed `fetch_add` on a shared cache line
**once per permutation** — 217,114 atomics at b=6, landing in exactly the phase
being measured. A counting run's milliseconds are not "slightly high", they are
meaningless. So the count arm returns no duration at all.

The two instruments do compose with each other, which is the whole reason one
harness can carry both: the permutation counter rides in the Mmcs and the
Challenger, the DFT recorder rides in the `Dft` type parameter of
`TwoAdicFriPcs`. Different type parameters, no new impls:

```rust
type CPcs = TwoAdicFriPcs<P3BabyBear, RecordingDft, CValMmcs, CChallengeMmcs>;
type CountConfig = StarkConfig<CPcs, Ef, CChallenger /* over CountingPerm */>;
```

### The sweep dimensions are a struct, not a convention

```rust
pub struct Point { log_blowup, num_queries, pow_bits, effects, threads }
```

Rule 1 of `COST-MODEL.md` — *"a ratio without `(lb, q, pow, rows, N)` cannot be
composed"* — turned into a type. A cell cannot be recorded without saying where
it was taken.

### Statistics: min / p50 / p99, never a mean

A mean over a contended box is a number about the contention. The rig also
carries **spread** (max/min) per cell and prints `⚠ UNSTABLE — min only` above
1.3×, because a lane measuring GPU work found the same cell varying **2.1×
across three runs** and only caught it by looking.

---

## 2. ⚑ The self-check — and the law it is built on

The brief asked for a self-check that can go red, on the precedent of a pricer
that *"reproduces the measured Merkle column to a constant at all five rungs, and
refuses to print if it stops."*

Working back from the recorded permutation tables, the whole prover column is a
**two-parameter law**:

```
    P(b) = A · 2^b + C          A = 3381,  C = 766
```

and it is not a fit with slack — it reproduces every recorded rung **to the unit**,
and (§3) it then reproduced them again on hbox, on different hardware:

| b | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|
| `3381·2^b + 766` | 27,814 | 54,862 | 108,958 | 217,150 | 433,534 |
| measured on hbox | **27,814** | **54,862** | **108,958** | **217,150** | **433,534** |

It decomposes into named phases rather than being numerology — and each
sub-column has the same shape:

| phase | law | b=3 | b=6 | b=7 |
|---|---|---:|---:|---:|
| Merkle-commit | `3312·2^b − 3` | 26,493 | 211,965 | 423,933 |
| FRI-fold Merkle | `69·2^b − 3` | 549 | 4,413 | 8,829 |
| challenger | `736` (constant) | 736 | 736 | 736 |
| *three named phases* | `3381·2^b + 730` | 27,778 | 217,114 | 433,498 |
| **+ unspanned (FRI-commit-other 3, query/open 3, residual 30)** | **`3381·2^b + 766`** | **27,814** | **217,150** | **433,534** |

(`C = 736 − 3 − 3 + 36`: the challenger's sampling, less the two `2n−3` Merkle
roots, plus the 36 permutations the three named phases do not span.)
`pinned_law_decomposes_into_named_phases` asserts every cell of that table, both
conventions included.

### Three ways it goes red

1. **SHAPE** — the measured rungs are not affine in `2^b` at all.
2. **PREDICTION** — the law fitted on the two lowest rungs mispredicts a higher
   one. Catches a change confined to one blowup. Sensitive to **one permutation**.
3. **PIN** — a perfectly affine column with *different constants*. This is the
   case that matters most: the prover still works, the shape is intact, and the
   number has silently stopped being comparable to anything recorded. A new
   column, a widened chip, a changed query count all land here.

A companion census on the DFT side goes red if the `p3-fri` slow extrapolation
path is ever taken (it has been zero at every blowup in every recorded run — that
is what makes it a usable tripwire).

### ⚑ The pin I got wrong, caught before it shipped — and it is the instructive part

The first pin I wrote was `c = 730`, and it would have made the rig **fire red on a
correct prover.** There are **two recorded "prover permutation" columns** and they
differ by a constant **36**:

| convention | phase set | law | b=3 | b=6 |
|---|---|---|---:|---:|
| three NAMED phases | Merkle + FRI-fold + challenger | `3381·2^b + 730` | 27,778 | 217,114 |
| **prove − self-verify** ← what the rig measures | the above **+ FRI-commit-other (3) + query/open (3) + prove residual (30)** | **`3381·2^b + 766`** | **27,814** | **217,150** |

Both columns are in our notes, both are called "prover perms", and the `+36` is
constant in `b` — which is exactly why it hides: it never changes a *ratio*, only
an *absolute*, so every ratio anyone computed from either column was right.

This is the same disease as the "grind is 18% vs 23%" argument that cost half a
day: **two phase sets wearing one name.** The rig now carries both laws and a PIN
failure that lands on the sibling convention says so by name instead of printing a
mysterious 36.

### Red-capability is proved, not asserted

`self_check_is_red_capable` is a plain unit test — no prover, runs in CI — that
requires the checker to reject: a bent column, a **single-permutation** drift at
b=7, an affine-but-shifted column, a 2-rung input (a fit is not a check), a DFT
slow-path event, and a work/latency mixed compose. *A gate nobody has seen fail
is a gate nobody has tested.*

---

## 3. What it measured — the count arm, on hbox, reproducing the record exactly

`(lb variable, q 19, pow 0)`, workload `transferVmDescriptor2` · 1 Transfer · 64 columns ×
188 rows, threads 1, release @ `a31590c378c8`, rustc 1.98.0-nightly, hbox cpus 0-15,
governor powersave, nice 15, load 3.97 → 3.97, co-tenant `cargo(244M)`.

| b | prover perms | verify perms | prove+verify | proof bytes |
|---:|---:|---:|---:|---:|
| 3 | 27,814 | 3,698 | 31,512 | 301,904 |
| 4 | 54,862 | 3,812 | 58,674 | 311,918 |
| 5 | 108,958 | 3,926 | 112,884 | 321,428 |
| 6 | **217,150** | **4,040** | **221,190** | 331,386 |
| 7 | 433,534 | 4,154 | 437,688 | 341,212 |

⚑ **Every column reproduces the recorded tables to the unit — on different hardware.**
`prove+verify` matches `phase-profile.md` §7's total row (31,512 / 58,674 / 112,884 / 221,190
/ 437,688) exactly; the verifier column matches exactly; `prover` matches
`blowup-drop.md` §D2's 27,814 and 217,150 exactly. The M2 Max numbers were taken at load
16–95; these were taken on an Intel i9 at load 4. **That is what "contention-immune" means,
demonstrated rather than asserted** — and it is the argument for counts being the primary
instrument, made by the instrument itself.

Self-check: `P = 3381·2^b + 766 reproduces all 5 measured rungs to the unit, and matches the
pin`. DFT census: **9 calls, all `coset_lde_batch`** — down from the recorded 18 (6 + 12),
confirming `a31590c37`'s batching is live, with the slow extrapolation path not taken.

### ⚑ The self-check went red in production before it went green

The first hbox run fired **PIN**, printing `measured P = 3381·2^b + 766, pinned P = 3381·2^b
+ 730`. The cause was mundane — the binary was built from the pre-correction file — but the
behaviour is the whole point: **the rig measured the constant independently, on hardware, at
all five rungs, and named the discrepancy to the unit.** Red-capability is proved by a unit
test *and* was exercised for real on the first run.

### ⛔ A condition nobody was recording: hbox was running the SCALAR Poseidon2

`packing width = 1.00` at every blowup — zero packed permutation calls. `<BabyBear as
Field>::Packing` is selected by **target features**, not by the CPU that exists, so without
`-C target-cpu=native` an x86-64 build takes the scalar path even on a machine with AVX2. On
the M2 Max, NEON gave WIDTH=4 for free, which is why this never surfaced.

**This is the nastiest shape a defect can have**: the counts are *unaffected* (they are
scalar-equivalent by construction, and indeed they reproduced the record exactly), while
**every wall-clock number from such a build measures a different prover** — several times
too slow on precisely the hash side, which is the numerator of `hash/arith`. The primary
instrument stays correct and the secondary one silently lies.

The rig now prints a ⛔ banner when packing width is 1 and says the counts survive it. **Any
hbox timing taken without `RUSTFLAGS="-C target-cpu=native"` should be discarded.**

### ⚑ A defect in my own instrument: the grind cell stopped falsifying

§E3 exists to show that grind is a random draw. Its first version re-proved **the same
workload** three times and got `49,152` every time — reporting `spread 1.00×`, which reads as
*"grind is stable and safe to difference"*, the exact opposite of the finding it was written
to deliver. The grind searches a witness for **one transcript**; a fixed workload is a fixed
transcript, so it was one draw measured three times.

(The 49,152 is itself another exact reproduction — `blowup-drop.md` records 49,153 ground
perms at `(6,19,pow16)`.)

Fixed by varying the transfer amount per draw, which varies the trace, the commitment, the
challenge, and therefore the draw. This is the *falsifier that stopped falsifying* class,
found in a cell written specifically to guard against a measurement error — which is the
argument for never trusting an instrument you have not seen fail.

**After the fix**, six draws at `(lb 6, q 19, pow 16)`:

| amount | 50 | 51 | 52 | 53 | 54 | 55 |
|---|---:|---:|---:|---:|---:|---:|
| grind perms | 49,152 | 49,152 | 65,536 | 32,768 | 16,384 | 98,304 |

min 16,384 · max 98,304 · mean 51,883 · **spread 6.00×**.

> **Any "speedup" below 6× obtained by differencing two grind runs is noise.** That is the
> cell's whole job, and it can now do it.

⚑ **And an unplanned confirmation:** every draw is an exact multiple of **16,384 = 2^16 / 4**.
That is the landed grind schedule's window — `c = 1/4` from `11cff8852` — so the work is
quantised to one window. The rig independently re-derived the deployed grind parameter from
nothing but permutation counts, without being told it existed.

---

## 4. The clock arm — the first defensible timing this project has taken

`(lb, q 19, pow 0)` — **grind excluded, and named as excluded.** Workload
`transferVmDescriptor2` · 1 Transfer · 64 columns × 188 rows. Release @ `a31590c378c8`
with `-C target-cpu=native` (packing width 8.18), hbox cpus 0-15 (P-cores), governor
powersave, nice 15, **N=9 per cell after one untimed warm-up**, one process per thread
count. Values are **min ms**; every cell also carries p50/p99/max in the log.

### First, the reason to care about the box at all

**Spread (max/min) across all 40 cells: 1.01×–1.27×, and ≤1.10× in 33 of 40.** The
recorded laptop figure for the same kind of cell was **2.1× across three runs**. That
gap is the entire argument for moving measurement here, and it is now measured rather
than assumed.

### ⚑⚑ Thread scaling TURNS OVER at the physical-core boundary

b=6, min ms:

| threads | cold caller | vs T=1 | INSIDE pool | vs T=1 | pool/cold |
|---:|---:|---:|---:|---:|---:|
| 1 | 39.801 | 1.00× | 34.925 | 1.00× | 1.14× |
| 4 | 21.119 | 1.88× | 16.109 | 2.17× | 1.31× |
| **8** | **20.553** | **1.94×** | **15.512** | **2.25×** | 1.32× |
| 16 | 31.650 | **1.26×** | 19.067 | 1.83× | 1.66× |

b=7, min ms:

| threads | cold caller | vs T=1 | INSIDE pool | vs T=1 |
|---:|---:|---:|---:|---:|
| 1 | 74.213 | 1.00× | 64.175 | 1.00× |
| **4** | **34.854** | **2.13×** | 26.370 | 2.43× |
| 8 | 39.187 | 1.89× | **25.387** | **2.53×** |
| 16 | 54.748 | **1.36×** | 30.393 | 2.11× |

> ⚑ **T=16 is 1.54× WORSE than T=8 at b=6, and 1.57× worse than T=4 at b=7.**

This is the P/E topology from §0 arriving as a measurement. `swarm-build`'s
`taskset -c 0-15` is **8 physical P-cores × 2 SMT threads**, so a 16-thread pool puts two
workers on every physical core and they fight. **The optimum is 4–8 threads, and the
default is a pessimization.** Anyone who has been running this prover at default rayon
threads on this box has been paying up to 1.57× for the privilege.

⚠ And it is why "threads" had to be a recorded condition rather than a default: a
scaling curve taken only at 1 and "default" would have reported this prover as scaling
badly, when it scales ~2.2× to 8 threads and then falls off a topology cliff.

### The un-taken prize, measured independently on a quiet box

`notes/lde-layout.md` §G6f measured **2.2–2.5×** for running the whole prover inside
`ThreadPool::install`, on the contended laptop, and deliberately did not take it. Here:

| | T=1 | T=4 | T=8 | T=16 |
|---|---:|---:|---:|---:|
| pool/cold at b=6 | 1.14× | 1.31× | 1.32× | 1.66× |
| pool/cold at b=7 | 1.16× | 1.32× | 1.54× | 1.80× |

**Same sign, same direction, smaller magnitude — 1.14×–1.80× rather than 2.2–2.5×.** The
recommendation stands (it is still the largest single lever on the board and it grows
with thread count), but **the number it was sold on is ~1.5× optimistic**, which is
about what one expects from a ratio taken at load 16–95.

---

## 5. ⚑ The composed measurement — the answer is a refusal, and that is the result

The brief asked for the composition nobody has done honestly: what the four
landed wins give together, composed through the phase model rather than
multiplied. Doing it honestly produces a **finding rather than a number.**

| win | phase | unit | landed at HEAD? | factor |
|---|---|---|---|---:|
| LDE layout (`a31590c37`) | LDE | **LATENCY** | ✅ yes | 3.57–4.07× phase |
| grind schedule (`11cff8852`) | grind | **LATENCY** | ✅ yes | 10.6× mean (derived); 7.10× counted |
| blowup drop 6→2 | Merkle-commit | **WORK** | ❌ **not cut over** — `IR2_FRI_LOG_BLOWUP = 6` | 15.19× |
| `permEmissionNarrow` | Merkle-commit | **WORK** | ❌ **not cut over** — `CHIP_WIDTH = 386` | 1.076× per-batch |

> **The two that are LANDED are both LATENCY claims. The two that carry WORK
> claims are both NOT CUT OVER.**

So the honest composed answer:

- **In WORK — nothing.** Zero landed wins reduce the operation count. The grind
  schedule *raises* it by **+12.6%**, and raises grind's share of prover work
  from 23.2% to 25.4% at the deployed point. The LDE layout moves arithmetic by
  **−0.11%** and permutations by zero.
- **In LATENCY** — the two landed wins compose through the phase model, on phase
  shares measured on a contended laptop, pre-batching. **Shape, not magnitude.**

**The two columns cannot be added, and there is no configuration of this repo at
HEAD in which a user gets both.** `compose()` refuses the mixed set rather than
returning a number, which is the rule made mechanical.

### The numbers the rig printed

```
── composing all four ──
REFUSED — this set mixes 2 WORK claims with 2 LATENCY claims.

── the WORK column ──
phase set = prover Poseidon2 permutations at (lb 6, q 19, pow 0) = 217,114;
            Merkle-commit = 211,965 = 97.6%
SKIPPED  blowup drop 6→2      — the deployed config does not select it
SKIPPED  permEmissionNarrow   — the deployed config does not select it
── composed: 1.0000× ──

── the LATENCY column ──
phase set = prove wall clock at (lb 6, q 19, pow 16), phase-profile.md §2
            ⚠ CONTENDED LAPTOP, PRE-BATCHING. Shape only.
applied  LDE layout       phase 'LDE'   share 24.3% × 3.660×   ⇒ system 1.2141×
applied  grind schedule   phase 'grind' share 18.3% × 10.600×  ⇒ system 1.1987×
── composed: 1.4554× ──
```

⚑ **`3.66 × 10.6 = 38.8×`. Composed through the phase model: `1.46×`. The naive
product overstates by 26.6×.** That is `COST-MODEL.md`'s *"the wins do NOT multiply"*
shown rather than stated — and it is why "what do the four landed wins give together"
has never had an answer anyone could quote.

⚠ The `1.4554×` is **shape, not magnitude**: its phase shares come from
`phase-profile.md` §2, measured on the contended laptop *before* the LDE batching
landed — so it applies the LDE win to a share that win has already changed. Re-deriving
those shares on hbox with `-C target-cpu=native` is the next measurement, and the rig is
the thing that takes it.

⚠ This also corrects a framing in the brief itself: *"the blowup drop now that
the `p3-fri` bug is fixed"* — the **bug fix** is landed (`4e6089484`, and it is
what makes `lb = 2` feasible for all twelve descriptors, chip-bearing included).
The **config flip** to `(2, 57)` is not. Those are different objects and only the
second is the win.

---

## 6. Debt this pass recorded rather than paid

- **The permutation counter is now in its fourth copy.**
  `poseidon2_narrow_witness.rs`'s own header says *"if a third file wants one,
  that is the point to lift it into the library."* Lifting it touches three hot
  files in a swarm-shared tree and should not ride along inside a measurement
  rig; it is a clean separate change.
- **The rig carries DFT *shapes*, not field-op *counts*.** The counting-field
  newtype in `ir2_field_op_counts.rs` is ~600 lines and copying it would be a
  fifth twin. Instead the rig records the shape census live and cross-checks it;
  if the census moves, the recorded field-op table no longer describes this
  prover and the rig says so.
- **`/` on hbox is full.** Not this lane's to fix, but any lane that builds in
  `~/dev/breadstuffs` on hbox will hit it.

---

## 7. How to run it

The working rig lives at `/tank/dregg-build/hbox-rig/` on hbox: a detached clone at the
pinned SHA (`breadstuffs/`, zero dirty files), its own `CARGO_HOME` (`cargo/`), and the run
logs. **Four environment settings are load-bearing and none of them is optional:**

```bash
# on hbox, from the detached clone on /tank — NEVER from ~/dev/breadstuffs
# (that is a co-tenant's tree at a different SHA with ~1900 dirty files,
#  and / is 100% full so a build there fails anyway)
cd /tank/dregg-build/hbox-rig/breadstuffs

CARGO_HOME=/tank/dregg-build/hbox-rig/cargo \   # / is full; never write to it
DREGG_REQUIRE_LEAN=0 \                          # see below — safe HERE, not in general
RUSTFLAGS="-C target-cpu=native" \              # or you measure the SCALAR prover
SWARM_MEM_MAX=48G swarm-build \                 # cgroup cap + taskset 0-15 = P-cores
  cargo test -p dregg-circuit --release --test hbox_rig \
  -- --ignored --nocapture --test-threads=1 --skip e2_clock_sweep

# the clock arm needs ONE PROCESS PER THREAD COUNT (rayon's global pool is set once):
for T in 1 4 8 16; do RIG_THREADS=$T RIG_REPS=9 <same env> \
  cargo test … -- --ignored --nocapture --test-threads=1 --exact e2_clock_sweep; done
```

### ⚠ `DREGG_REQUIRE_LEAN=0` — why it is safe here and where it would not be

A release build of any `dregg-lean-ffi` consumer is **refused** unless a HEAD-matching
`libdregg_lean.a` seed is present, because a marshal-only build silently compiles out every
`#[cfg(dregg_*_present)]` module and reports the rest green. That gate is correct and it
fired on us. No seed is published for this closure key (`e712a26e70ecc437`), and the cold
`lake` bootstrap is hours.

Checked before working around it, rather than after: **`circuit/` contains zero
`dregg_*_present` cfgs, zero `lean_available()` calls, and zero `feature = "lean"` sites** —
the entire cfg inventory of `circuit/src/` is 97 `cfg(test)`, 18 `cfg(feature = "plonky3")`
(an always-on no-op) and 9 `cfg(debug_assertions)`. Descriptors are `include_str!` constants;
`circuit/` has no `build.rs`. The gate reaches us only through a **dev-dependency** edge
(`dregg-circuit [dev-deps] → dregg-bridge → dregg-lean-ffi`). So the prover measured is
byte-identical, and `cargo test -p dregg-circuit` loses no tests.

⚠ **Do not carry that conclusion to `-p dregg-lean-ffi`, `-p dregg-bridge`, `-p grain-verify`
or `--workspace`** — those genuinely go dark under a marshal-only build.

⚑ And the rig gives an independent check on exactly this: **the self-check reproducing
`3381·2^b + 766` at all five rungs is evidence that the marshal-only binary proves the same
thing the record was taken on.** That is what the self-check is for.

### A defect found in `scripts/fetch-lean-seed.sh`

When `origin` is not a GitHub remote (a clone from the local bare repo, which is exactly what
a detached build clone is), `REPO_SLUG` resolves to the local **path** and the script builds
`https://github.com//home/hbox/dev/breadstuffs/releases/download/...`, then reports a 404 as
*"no asset published for this platform"*. The real cause is a malformed URL. Setting the
remote to `git@github.com:emberian/dregg.git` gets a truthful answer (which was still "no
seed for this closure key", but for the right reason).

⚠ **The agent harness stops backgrounded jobs at ~50 minutes and a killed test
reports as `1 failed`, not as unrunnable.** Launch detached (`setsid`, which hbox
has and macOS does not) and **read the per-test label — `SIGTERM` / `TIMEOUT` /
a panic — before reporting any failure.** Every run in this note was launched
detached; the one `1 failed` we saw was a genuine panic at our own assertion, and
reading the label is what established that in one step.

---

## 8. What to measure next, with the rig that now exists

1. **Re-derive the phase shares on hbox.** §5's `1.4554×` uses shares from the
   contended laptop, *pre-batching* — it applies the LDE win to a share that win has
   already changed. The shares are the last laptop-derived input in the composition,
   and the rig can now replace them.
2. **Take the `ThreadPool::install` prize.** It is the largest single lever measured
   (1.14–1.80× here, growing with thread count), it is uncontaminated by the LDE
   batching, and the only thing between us and it is *where the `install` goes* — an
   ownership decision, not a measurement one.
3. **Set the thread default to 8.** Finding 2 is free money and nothing depends on
   the current default being right.
4. **Lift the permutation counter into a library.** Four copies now. The rig is the
   fourth consumer and the code's own comment asked for this at the third.
5. **Publish a Lean seed for the current closure key**, or the next lane repeats the
   same 40 minutes. `DREGG_REQUIRE_LEAN=0` is correct *here* and the note says why,
   but it is a workaround, not a fix.
6. **Fix `fetch-lean-seed.sh`'s `REPO_SLUG`** so a non-GitHub `origin` reports the
   real cause instead of a 404 that reads as "no seed published".
