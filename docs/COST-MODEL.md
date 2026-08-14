# One cost model everything checks into — and what building it exposed

2026-08-14. Ember asked what the lanes found and **how to synthesize more
intelligently.** The honest answer to the second is that I have been
**accumulating** — twenty facts appended to VERDICTS — not synthesizing. This
is the artifact that would have made the connections visible, plus the problem
that showed up the moment I tried to populate it.

## The model

Prover time is a small number of phases with different scaling laws. Every
measurement should update a share; every proposed win should name a phase.

| phase | scales with | kind |
|---|---|---|
| grind (PoW) | **nothing** | hash |
| LDE (coset NTT) | 2^b | arith |
| Merkle commit | 2^b | hash |
| sumcheck / fold | **nothing** | arith |
| query / opening | **query count** | hash |

*"Hash-bound" means the hash rows sum higher than the arith rows.* That is a
statement about a **mixture**, which is why two lanes could measure it
differently and both be right — they sat at different `b`.

## ⚑ What the model says that the list could not

Composing the two landed wins through the phase shares rather than
multiplying them:

- **The wins do NOT multiply.** 13.13× × 7.49× = 98× is **wrong**, and
  nothing in a flat list of wins says so.
- **Each win's value depends on the ORDER.** The grind fix is worth ~1.28× at
  the deployed point and ~1.46× *after* a blowup drop — because the blowup
  drop shrinks the phases the grind competes with, so **grind's share rises
  from 25% to ~36% and the same fix becomes worth more.**
- **A measured "13.13× faster" is a phase ratio, not a system ratio.** Grind
  alone (25%, blowup-independent) caps any blowup-only speedup at 4×.

## ⚑⚑ RETRACTION (2026-08-14, ember): THE CLOCK DATA IS NOT SOUND, AND I USED IT TO OVERTURN THE COUNTS

Every wall-clock figure below was taken on an **M2 Max at load average
16–95 with 36 login sessions**. The measuring lanes said so and labelled the
absolute ms as upper bounds. **I then built a composition model on them anyway
— and worse, used them to overturn an operation-count model**, writing *"the
exchange rate was in the wrong unit — counted multiplications where
nanoseconds bill."* **On a box that contended, counted operations are the MORE
reliable estimator, not the less.**

**And "the ratios are safe" is false**, which is the part I did not think
through: hash work (large-buffer traversal, memory-bound) and field arithmetic
(cache-resident, compute-bound) **degrade at different rates under
contention.** So `hash/arith` — *the central claim of two days* — is exactly
the quantity most corrupted by a busy machine.

### What we actually have, in exact counts (contention-immune)

| b | Merkle | FRI-fold | challenger | grind | total perms | grind share |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 26,493 | 549 | 736 | 47,917 | **75,695** | **63.3%** |
| 4 | 52,989 | 1,101 | 736 | 47,917 | 102,743 | 46.6% |
| 5 | 105,981 | 2,205 | 736 | 47,917 | 156,839 | 30.6% |
| **6** | **211,965** | **4,413** | **736** | **47,917** | **265,031** | **18.1%** |
| 7 | 423,933 | 8,829 | 736 | 47,917 | 481,415 | 10.0% |

**Blowup 6→3 is a 3.50× reduction in hash WORK** — exact, no clock. (The
contended-clock model said 3.61× on the system; close, but only the count
survives a busy box.)

### ⚑ Two structural errors the counts expose that the clock hid

1. **`hash/arith` rests on comparing an EXACT count against a CONTENDED
   clock.** We have exact permutation counts and **no field-multiplication
   counts at all** — the profiler had no hook. **That comparison is not
   sound**, and "hash-bound at every feasible blowup" must be demoted to
   *unproven* until an arithmetic op-count hook exists.
2. **The grind fix does not reduce operation count — it reduces CRITICAL
   PATH, and total work RISES** (a window gets scanned). **Work and latency
   are different quantities and cannot be composed in one unit.** "The grind
   fix is worth 1.94× after the blowup drop" was a **latency claim dressed as
   a throughput one, computed on a machine that cannot measure latency.**

### ⚑ RESOLVED 2026-08-14 — the arithmetic hook exists; the work claim holds and the premise above was backwards

Built: `breadstuffs/circuit/tests/ir2_field_op_counts.rs`. Full write-up:
**`notes/field-op-counts.md`**. Read that before quoting anything in this file.

Three corrections to what is written above.

1. **"Hash-bound at every feasible blowup" is PROVEN as a work claim, and the demotion can be
   lifted for that claim only.** It is now count-vs-count with one measured constant:
   *hash-bound iff `Y > X`*, where `X = (M + 0.803·A)/P` is exact and hardware-free and
   `Y = t_perm/t_mul` is the only quantity a clock touches. Measured `X` = **178** at b=3 falling
   to **124** at b=7; measured `Y` = **890** at a 16 MB working set, 898 at the primary estimator,
   1161 in cache. **Margin 5.0×–7.2×, no crossover in `b ∈ {3..7}`.** Every approximation in `X`
   points the same way (it over-states arithmetic).

2. ⚑ **"The ratios are safe is false" is right, but for the OPPOSITE reason to the one given
   above.** The premise was that hash work is memory-bound and field arithmetic cache-resident.
   Measured: the permutation count explains **80%** of the hash phase's measured time and **84%**
   of the open phase's, while the field-op count explains **25%** of LDE-commit's and **0.6%** of
   LDE-quotient-eval's. **The hash side behaves like its count; the LDE does not.** So the phase
   labelled "arith" in the table above is ~80% *not arithmetic* — and no clock can see that,
   because a clock cannot separate expensive arithmetic from cheap arithmetic wrapped in expensive
   movement. Also measured: `Y` moves only 1.3× across a 512× change in working set, so the
   cache-vs-DRAM hazard on the conversion constant is real but small and bounded.

3. **The `LDE (coset NTT) — 2^b — arith` row of the model is mis-typed, and one of its
   sub-phases is mis-diagnosed.** `get_evaluations_on_domain`'s slow path is *never taken* — zero
   `coset_idft_batch` and zero `coset_dft_batch` calls at every blowup. What the profiler labels
   "LDE quotient-eval" is the **twelve width-4 quotient-CHUNK LDE commits**, carrying **3.5% of
   the LDE's arithmetic and 63% of its measured time**; per call the two LDE phases cost 1.285 ms
   and 1.077 ms while their per-call work differs by 27×. **The cost is per-CALL and
   per-narrow-matrix, so the fix is a layout change (batch twelve width-4 commits into three of
   width 8/8/32), not an arithmetic one.** An arithmetic optimisation aimed at that phase buys
   essentially nothing.

**Rule 2 of this file needs a companion:** a proposed win must name its phase *and* its unit. A
phase whose milliseconds are 99% movement cannot be improved by a win denominated in
multiplications, and the model above has no column that would have caught that.

### ⚠ Denominator disclosure — answering a lane's challenge to my own figures

A lane reported that my relayed **"grind is 18% at b=6 / 63% at b=3"** does not
reproduce against `26b33a37a`, which says **23% at (lb 6, q 19)** and **82% at
(lb 2, q 57)**, and correctly asked whoever holds 18/63 to state its
denominator. **It is mine, and here it is:**

- **My denominator is HASH WORK ONLY** — the sum of Merkle-commit + FRI-fold
  Merkle + challenger + grind permutations from `notes/phase-profile.md`'s
  count table. It excludes field arithmetic entirely (which we cannot count
  yet). **A share of hash work is not a share of prove.**
- **My second point is b=3, not lb=2** — a different configuration from
  theirs, and at lb=2 the Merkle count roughly halves again, which accounts
  for most of 63% vs 82%.
- **The 23% vs 18% gap I cannot resolve from here** and do not average away.
  Both are permutation-count figures; the denominators differ by ~57,000
  perms, which is larger than any single phase I can name. **Whoever
  reconciles it should state the phase set on both sides.**

**Rule this produces: a percentage without its denominator is not a
measurement.** Every share in this file now names its phase set, and the two
above are the first to do so.

### The methodology that follows

- **Operation counts are the primary instrument.** They are exact,
  deterministic, contention-immune, and reproducible by anyone.
- **Wall clock is a secondary instrument** for the one thing counts cannot
  express — the *conversion rate* between op classes — and it requires a
  quiet machine, which we do not have.
- **Never compose a work claim with a latency claim.** Report them in separate
  columns.
- ~~**Build the arithmetic op-count hook.**~~ **DONE 2026-08-14** —
  `circuit/tests/ir2_field_op_counts.rs`, write-up `notes/field-op-counts.md`.
  See the RESOLVED block above: the work claim holds by 5–7×, and the phase
  taxonomy in the table at the top of this file needs a UNIT column.

*Everything below this line was computed from the contended clock and is
retained as history, not as evidence.*

## ~~POPULATED (2026-08-14)~~ — SUPERSEDED BY THE RETRACTION ABOVE

**Deployed point, b=6, pow=16, IR-v2 descriptor batch** (ms, min-of-21,
contended box — ratios are the deliverable):

| phase | ms | share | kind |
|---|---:|---:|---|
| **Merkle-commit** | **42.509** | **51.3%** | hash |
| LDE quotient-eval | 12.925 | 15.6% | arith |
| **grind (pow=16)** | **12.800** | **15.5%** | hash |
| LDE commit | 7.710 | 9.3% | arith |
| open arith | 3.545 | 4.3% | arith |
| everything else | 3.352 | 4.0% | — |
| **TOTAL** | **82.84** | | |

⚠ **My guessed share for grind was 25%; it is 15% at b=6** — and *b-dependent*,
because grind alone does not scale with blowup: **41% at b=4, 56% at b=3.**
The "~25%" in circulation was true at *some* b and quoted as if global.

### The composition, computed rather than guessed

| configuration | ms | vs deployed |
|---|---:|---:|
| deployed (b=6, pow=16) | 82.84 | — |
| blowup 6→3 only | 22.92 | **3.61×** |
| grind fix only (at b=6) | 71.75 | 1.15× |
| **both** | **11.83** | **7.00×** |

- **The prove-only part moves 6.92× but the system moves 3.61×**, because
  grind does not shrink. *A phase ratio is not a system ratio.*
- ⚑ **Order matters by 1.68×**: the grind fix is worth **1.15× alone** and
  **1.94× after the blowup drop**, because the drop takes grind's share from
  15% to **56%**.
- ⚑ **The query increase is nearly free** — `query/open` is **0.068 ms, 0.08%
  of prove.** Tripling queries to hold soundness at lower blowup costs
  essentially nothing. *That is why the blowup trade is good, and it is not
  visible anywhere in the soundness discussion.*
- ⚠ The separately-measured "13.13× at 4096 rows" is a **different workload**
  (trace height, not the descriptor batch) — do not compose the two without
  reconciling the shapes.

## ⚑ The model failing to populate at first — which is the real finding

**I could not fill in the phase shares from our own notes.** They record
*conclusions* ("hash-bound", "25% is grind", "13.13× faster at 4096 rows")
without the table the conclusion came from, without the configuration each
number was taken at, and without whether `pow` was on. The shares above are
**reconstructed from prose and are not trustworthy** — and the composition
arithmetic changes qualitatively depending on whether the 13.13× was measured
at pow=0 (likely, since that was the clean-comparison recommendation) or at
pow=16 (impossible, per the 4× cap above).

**That is the process defect.** A note that says "13.13× faster" is unusable
six hours later; a note that says "prove ms at (lb,q,pow) = (6,19,0): X, and
(2,57,0): Y, at 4096 rows, min-of-N, N=..." composes with everything else
forever.

## The rules that follow

1. **Every measurement records its CONFIGURATION and its RAW numbers**, not
   only its ratio. A ratio without `(lb, q, pow, rows, N)` cannot be composed.
2. **Every proposed win names the PHASE it touches.** A win that cannot name
   its phase has not been understood.
3. **Compose through the model, never by multiplying.** And state the order,
   because the order changes the value.
4. **A phase share is a claim like any other** — it gets a source and a date.
5. **When a new measurement contradicts a share, that is a finding**, not a
   discrepancy to average away. Two lanes disagreeing on "hash-bound" was the
   model telling us they were at different `b`; we treated it as a dispute for
   half a day.

## What to do next, in this order

- **Extract the profiler's actual per-phase table** into this file, with
  configurations. It exists — it was in a lane's output and only the summary
  reached the notes.
- **Re-state the blowup measurement** with its config, so the composition can
  be computed rather than guessed.
- **Then** compose the landed wins honestly and publish one number for "what
  ships if all four land," which nobody currently knows.
