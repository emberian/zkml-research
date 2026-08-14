# The measurement rig on hbox — and what it found before it measured anything

2026-08-14. Ember: *"performance measurements should be conducted carefully on
`hbox` (which is quieter) right now, and we should be thinking about building up
our systems to be able to run these experiments."*

Every wall-clock number this project has published was taken on a laptop at load
16–95 with 36 login sessions, and `docs/COST-MODEL.md` had to retract a whole
composition model because of it. The discipline that came out of that retraction
is written down. **What was missing is a rig that makes the discipline
automatic**, because a rule in a markdown file is a rule a lane forgets at 3am.

The rig is `breadstuffs/circuit/tests/hbox_rig.rs`.

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
    P(b) = A · 2^b + C          A = 3381,  C = 730
```

and it is not a fit with slack — it reproduces every recorded rung **to the
unit**:

| b | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|
| recorded (`phase-profile.md` §7, `field-op-counts.md` §5) | 27,778 | 54,826 | 108,922 | 217,114 | 433,498 |
| `3381·2^b + 730` | 27,778 | 54,826 | 108,922 | 217,114 | 433,498 |

It decomposes into named phases rather than being numerology — and each
sub-column has the same shape:

| phase | law | b=3 | b=6 | b=7 |
|---|---|---:|---:|---:|
| Merkle-commit | `3312·2^b − 3` | 26,493 | 211,965 | 423,933 |
| FRI-fold Merkle | `69·2^b − 3` | 549 | 4,413 | 8,829 |
| challenger | `736` (constant) | 736 | 736 | 736 |
| **total** | **`3381·2^b + 730`** | **27,778** | **217,114** | **433,498** |

(`C = 736 − 3 − 3`: the challenger's sampling, less the two `2n−3` Merkle roots.)
`pinned_law_decomposes_into_named_phases` asserts every cell of that table.

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

### Red-capability is proved, not asserted

`self_check_is_red_capable` is a plain unit test — no prover, runs in CI — that
requires the checker to reject: a bent column, a **single-permutation** drift at
b=7, an affine-but-shifted column, a 2-rung input (a fit is not a check), a DFT
slow-path event, and a work/latency mixed compose. *A gate nobody has seen fail
is a gate nobody has tested.*

---

## 3. ⚑ The composed measurement — the answer is a refusal, and that is the result

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

⚠ This also corrects a framing in the brief itself: *"the blowup drop now that
the `p3-fri` bug is fixed"* — the **bug fix** is landed (`4e6089484`, and it is
what makes `lb = 2` feasible for all twelve descriptors, chip-bearing included).
The **config flip** to `(2, 57)` is not. Those are different objects and only the
second is the win.

---

## 4. Debt this pass recorded rather than paid

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

## 5. How to run it

```bash
# on hbox, from the detached clone on /tank, never from ~/dev/breadstuffs
cd /tank/dregg-build/hbox-rig/breadstuffs
CARGO_HOME=/tank/dregg-build/hbox-rig/cargo \
SWARM_MEM_MAX=32G swarm-build \
  cargo test -p dregg-circuit --release --test hbox_rig \
  -- --ignored --nocapture --test-threads=1
```

⚠ **The agent harness stops backgrounded jobs at ~50 minutes and a killed test
reports as `1 failed`, not as unrunnable.** Launch detached (`setsid`, which hbox
has and macOS does not) and **read the per-test label — `SIGTERM` / `TIMEOUT` /
a panic — before reporting any failure.**
