# The grind's schedule, fixed — same witness, same bytes, 10.6× off the critical path

**Landed 2026-08-14.** Companion to `notes/grind-phase.md`, which found the defect: our own
determinism commit `90680ee7d` swapped upstream's `find_map_any` for **`find_map_first`**, and
`find_first` must prove no *lower* candidate exists, so the search stopped dividing —
**20,766 batches on the critical path at 1 thread and 20,766 at 12. Scale 1.00**, while total work
rose 5.9×.

This lane changed **the schedule and nothing else**. No security parameter moves: `pow` is still 16
at every config, `check_witness` is untouched, and the returned witness is bit-for-bit the one the
old path returned.

## What re-emits, what refuses to load

**Nothing, and that is the claim being defended.** No wire format, no descriptor, no VK, no
re-genesis. The grind's entire contribution to a proof is one field element, and that field element
is unchanged — measured, on a real deployed proof, against an integer recorded before the change
(§2). If anything here needed re-emitting, the fix would not be free and would not be worth doing.

| | critical path (the latency) | total work (the price) |
|---|---|---|
| **BabyBear leaf**, `pow=16`, T=12, 512 draws, derived | mean **10.6×**, p99 **11.8×** | **+12.6%** |
| **BN254 outer**, `pow=14`, T=12, **counted** | **9.49×** | **+13%** |
| **BN254 outer**, `pow=16` (deployed), derived | **11.0×** — **≈1.08 s → ≈98 ms** | +12.6% |

---

## 0. The five answers

1. **Correct.** The windowed parallel min returns the *globally minimal* valid witness, which is
   exactly what `find_map_first` computes, **for every window size**. Checked three ways over 128
   transcripts, plus end-to-end on real serialized proofs at three thread counts. §2.
2. **The critical path falls 10.6× on the mean and 11.8× on the p99**, at 12 threads, in exact
   batch counts. **Total work rises 1.126×.** Those are different units and never multiply. §3.
3. **The window is `c = 1/4`** — `2^pow / 4` candidates — picked from a measured sweep and a
   sensitivity analysis over the one constant the counts cannot see. §4.
4. ⚑ **A second, unlooked-for defect: rayon's `Range<u64>` producer is UNINDEXED**, so the window
   split only when a worker went idle and stole. On a loaded box the steal did not arrive and the
   fix delivered **2.47×** instead of ~10×. Forcing the split up front is what makes the schedule a
   schedule. §5.
5. ⚑ **The BN254 outer path is the bigger half.** Same defect (scale 0.97 across 12 threads), but a
   candidate there costs **16.5 µs** — a whole BN254 duplex, ~87× a packed BabyBear candidate — so
   at the deployed `bits=16` an apex/shrink proof's grind goes from **≈1.08 s to ≈98 ms**. §6.

⚠ **Box conditions:** Apple M2 Max, 12 cores, ~42 login sessions, **load average 21–62 across the
session**. Every count below (batches, calls, trials, windows, proof bytes) is exact and unaffected.
The two timed constants are stated where used; §4 explains why no whole-grind wall clock is quoted
as a result, and shows the run in which one reordered the parameter.

---

## 1. What landed, at all five sites

`vendor/plonky3-challenger-82cfad73/src/grinding_challenger.rs` gains one function and the five
grind sites call it:

```rust
pub fn windowed_find_map_first<T, S>(span: u64, window: u64, scan: S) -> Option<T>
```

> scan `0..span` in contiguous ascending windows; inside a window take the match with the **lowest
> unit index** — a complete scan, no early exit, split eagerly across the pool — and return on the
> first non-empty window.

| site | file | unit | window |
|---|---|---|---|
| `DuplexChallenger::grind` (the IR-v2 leaf) | `grinding_challenger.rs` | one SIMD batch (4 candidates) | `2^bits / 4` candidates |
| `MultiField32Challenger::grind` (BN254 outer/shrink) | `grinding_challenger.rs` | one candidate = one BN254 duplex | `2^bits / 4` |
| `grind_generic` (behind `grind_uniform`) | `grinding_challenger.rs` | one candidate | `2^bits / 4` |
| `SerializingChallenger32::grind` | `serializing_challenger.rs` | one candidate | `2^bits / 4` |
| `SerializingChallenger64::grind` | `serializing_challenger.rs` | one candidate | `2^bits / 4` |

Both `grind_with_window(bits, window)` methods are **public**, and that is deliberate: it lets the
tests sweep window sizes against the *deployed* function instead of against a paraphrase of it
sitting beside it in a test file.

### Why the answer cannot move — the argument, before the measurement

Windows are contiguous and ascending, so every unit before the first non-empty window returned
`None`. `find_map_first` returns the value of the lowest unit returning `Some`; that unit lies in
the first non-empty window; and reducing that window by **minimum unit index** returns exactly that
unit's value. Hence `windowed(span, w) == find_map_first(0..span)` for **every** `w ≥ 1`.

Note the reduction is by **unit index**, not by witness value. That makes the equality structural
rather than arithmetic: the window schedule is `find_map_first` with the early exit deleted, and an
early exit cannot change a first-match.

---

## 2. ⚑ The correctness obligation — byte-for-byte, four independent ways

This is the whole point of the lane, and none of it involves a clock.

### (a) Old path vs new path, 128 transcripts — `§G6`

`circuit/tests/grind_phase_measure.rs` keeps the pre-2026-08-14 body (`find_map_first` over the
whole range) as a **differential oracle** — the code that is no longer there — and asserts today's
`grind` returns the same field element.

| bits | transcripts | result |
|---:|---:|---|
| **16** (deployed) | 64 | identical on every one (largest witness seen 237,813) |
| 14 (`recursion-verify` default) | 64 | identical on every one (largest witness seen 58,476) |

### (b) Against the DEFINITION, not against the oracle — `§G6`

An oracle can drift into agreeing with the thing it checks, so the *contract* is verified
exhaustively: **every candidate strictly below the returned witness fails `check_witness`.** The
minimal valid witness is unique, so this pins `grind` to a specification rather than to another
program.

> **476,286 candidates checked below the returned witnesses** (392,061 at `bits=16`, 84,225 at
> `bits=14`, across 16 transcripts). Every one invalid.

### (c) Window invariance, including `window = 1` — `§G6`

Nine window sizes from **1 batch** (a literal sequential in-order scan, the specification in (b)
executed by the deployed code) to **2^24 batches** (one giant parallel window). All returned the
same witness, at both `bits`.

### (d) ⚑ Real serialized proofs, three thread counts — `§G7` (new, not `#[ignore]`d)

The deployed IR-v2 transfer at `(lb=6, q=19, pow=16)`, proved inside rayon pools of 1, 4 and 12
threads:

| threads | pow witness | proof bytes | blake3(proof)[..16] |
|---:|---:|---:|---|
| 1 | 47,912 | 138,224 | `3cad30a69901631b` |
| 4 | 47,912 | 138,224 | `3cad30a69901631b` |
| 12 | 47,912 | 138,224 | `3cad30a69901631b` |

Thread count is the axis that matters: a schedule reaches the answer exactly by making the answer
depend on how many workers looked at it. Under upstream's `find_map_any` this test was *measured*
to fail (2026-07-31: three rayon runs, three distinct proof lengths); it must not now.

**And `w = 47,912` is the integer `§G5` read off this same workload and config on 2026-08-13, on
the `find_map_first` path.** That is the old-path/new-path comparison carried out on a real proof.

Two guards make that reading honest:

* **A workload anchor.** The `pow = 0` rung of the same workload proves to **138,220 bytes**,
  exactly `§G4` arm 1's 2026-08-13 figure. `grind` returns `F::ZERO` before searching anything at
  `pow = 0`, so that number cannot be about the schedule — it says the descriptor, trace and FRI
  config have *not* moved underneath, which is what makes the witness match attributable.
* **The 4-byte delta is priced.** `pow=16` and `pow=0` differ by **4 bytes** — one varint field
  element, the entire wire cost of 16 soundness bits.

> ⚠ **A correction this lane made to itself.** The first version of `§G7` asserted the deployed
> proof was 138,220 bytes and went red at 138,224. **138,220 is `§G4`'s arm 1 — a `pow = 0` proof.**
> I had quoted a `pow = 0` figure as the deployed size. The fix was not to relax the assertion but
> to use the number for what it actually anchors; `grind-phase.md` §4 states the ≤8 B arm gap
> plainly and I read past it.

### (e) The work distribution is unchanged — `§G2`

Re-running the pre-fix instrument over 256 independent transcripts reproduces the 2026-08-13 table
*exactly* — mean 67,486 trials, p50 53,173, p90 149,417, p99 277,677, max 398,257. Identical
integers, because the witnesses are identical.

---

## 3. The measurement: critical path down, work up

⚑ **These are two different quantities in two different units and they move in opposite
directions.** The windowed min does **not** reduce operation count — a whole window is scanned
instead of stopping at the first hit, so total work *rises*. What falls is the critical path. A
"speedup" that multiplies the two is meaningless.

### (a) One fixed transcript, exact counts — `§G3` ①③

Witness 83,061 (a 1.27× draw), so the BEFORE path walks 20,766 batches. Every batch is exactly one
packed Poseidon2 permutation.

| threads | crit BEFORE | crit AFTER | **crit ×** | work BEFORE | work AFTER | work × (vs BEFORE@1) |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 20,766 | 24,576 | 0.84 | 20,766 | 24,576 | 1.18 |
| 2 | 20,870 | 12,288 | 1.70 | 41,636 | 24,576 | 1.18 |
| 4 | 20,766 | 6,358 | 3.27 | 81,742 | 24,576 | 1.18 |
| 8 | 20,766 | 3,511 | 5.91 | 140,864 | 24,576 | 1.18 |
| **12** | **20,766** | **2,923** | **7.10** | 81,029 | 24,576 | **1.18** |

**The BEFORE column is flat at 20,766 across every thread count — scale 1.00, the defect,
reproduced.** At one thread the fix is a 0.84× *regression* (it scans a whole window), which is the
honest shape of the trade and is why the work column exists.

⚠ **The work baseline is BEFORE at ONE thread, and saying so matters.** BEFORE's *total* work rises
with `T` (up to 140,864 at 8 threads — eleven workers scanning above the answer and losing the min),
so dividing AFTER's work by BEFORE's work *at the same `T`* would report this schedule change as a
work **reduction** of up to 6×. It is not. Against the least work the old path ever did, the price
is **+18% on this draw** and **+12.6% in expectation** (§4).

### (b) 512 independent draws, derived at T=12 — `§G3` ⑤

Normalised to the BEFORE path's own mean critical path (15,818 batches):

| | crit mean | crit p99 | crit max | work mean |
|---|---:|---:|---:|---:|
| **BEFORE** (`find_map_first`) | 1.000 | 4.089 | 6.646 | 1.000 |
| **AFTER** (`c = 1/4`, T=12) | **0.094** | **0.346** | **0.562** | **1.126** |
| ⇒ | **10.6×** | **11.8×** | **11.8×** | **+12.6% work** |

In absolute terms at the measured 643 ns/batch: mean critical path **10.17 ms → 0.96 ms**, p99
**41.6 ms → 3.52 ms**, worst of 512 **67.6 ms → 5.72 ms**, against a whole-prove budget of ~69 ms.

⚑ **What did NOT change is the relative spread.** `p99/mean` is 4.09 before and 3.68 after: the
draw is still geometric, now in whole windows rather than in candidates. The absolute p99 falls
11.8×; the *shape* does not flatten. `grind-phase.md` §6 offered `c = 8` as "the low-variance
option" — see §4 for why that reads better than it measures.

### (c) The derived model agrees with the counters — `§G3` ②

The windowed critical path is derivable with no instrument at all: the answer sits in batch
`w/lanes`, so the schedule consumes `n = w/(lanes·window) + 1` whole windows, each split across `T`.
Counted against derived, same transcript:

| threads | crit derived | crit counted |
|---:|---:|---:|
| 1 | 24,576 | 24,576 |
| 2 | 12,288 | 12,288 |
| 4 | 6,144 | 6,358 |
| 8 | 3,072 | 3,511 |
| 12 | 2,052 | 2,923 |

Exact at 1–2 threads, drifting to 1.42× at 12 — residual imbalance from a 12-worker pool on a
12-core box at load 35. **The derived column is the machine-independent statement; the counted one
is this box.** The 10.6× in (b) is derived; the 7.10× in (a) is counted. Both are stated.

---

## 4. Choosing the window

A window covering `c · 2^bits` candidates is empty with probability `e^(−c)`, so:

* expected **total work** = `c / (1 − e^(−c))` × the mean draw — the price;
* expected **barriers** = `1 / (1 − e^(−c))` — the thing that stops `c → 0`.

⚑ **Every exact column says smaller `c` is better, monotonically and without limit** — less work
*and* a shorter critical path. The only thing opposing `c → 0` is the per-window rayon join, and a
join is **invisible to an operation count**. So it was measured on its own — 96 tasks on 12 threads
with no work in them, min of 4096 — and the latency was then **derived** from the exact counts:

> measured constants: packed Poseidon2 **643 ns/batch**, one window barrier **7.1 µs**.

| `c` | batches | crit mean | crit p99 | work mean | E[windows] | barrier share | **est ms** |
|---:|---:|---:|---:|---:|---:|---:|---:|
| BEFORE | — | 1.000 | 4.089 | 1.000 | — | — | 10.18 |
| 1/16 | 1,024 | 0.087 | 0.348 | 1.032 | 15.95 | 11.5% | 0.99 |
| 1/8 | 2,048 | 0.089 | 0.346 | 1.063 | 8.21 | 6.1% | **0.96** |
| **1/4** | **4,096** | **0.094** | **0.346** | **1.126** | **4.35** | **3.1%** | **0.99** |
| 1/2 | 8,192 | 0.106 | 0.345 | 1.267 | 2.45 | 1.6% | 1.09 |
| 1 | 16,384 | 0.133 | 0.345 | 1.598 | 1.54 | 0.8% | 1.37 |
| 2 | 32,768 | 0.198 | 0.345 | 2.371 | 1.14 | 0.4% | 2.02 |
| 4 | 65,536 | 0.349 | 0.345 | 4.184 | 1.01 | 0.2% | 3.56 |
| 8 | 131,072 | 0.691 | 0.691 | 8.286 | 1.00 | 0.1% | 7.03 |

**The basin `1/16 … 1/4` is flat to 3%,** which is inside the model's own error. So `c` was chosen
by **sensitivity to the one constant that is measured rather than counted** — if the real barrier
is larger than the idle-pool 7.1 µs (it will be: a warm pool under memory pressure joins slower):

| if a barrier costs | best `c` | est ms at `c = 1/4` |
|---|---|---|
| 7.1 µs (measured, idle) | 1/8 | 0.99 |
| 21 µs (3×) | **1/4** | 1.05 |
| 71 µs (10×) | 1/4 – 1/2 | 1.26 |

**`c = 1/4` is the minimax choice across a 10× uncertainty in the barrier**, at 3.1% barrier share
and +12.6% work. `c = 1/8` wins by 3% at the measured constant and loses everywhere above 2×.

### ⚑ The `c = 8` "fixed-work" option is strictly worse, and should not be quoted as a low-variance win

`grind-phase.md` §6 measured that at `c = 8` the grind takes exactly one window over 64 draws and
called it "the low-variance option, ~8.3 ms, variance essentially zero". Measured here over 512
draws with the same instrument: `c = 8` costs **8.29× the work**, and its constant latency
(0.691 in the table = 7.03 ms) is **twice the p99 of `c = 1/4` (3.52 ms)**. Its mean is 7.3× worse.

So its only merit is that the *schedule* is deterministic — and the *answer* was already
deterministic, which is what anyone actually cares about here. A fixed-work grind is not a
soundness property and it buys nothing this system needs. **`c = 8` is refuted, not deferred.**

### The window is not `bits`-fragile

`default_grind_window(bits, candidates_per_unit)` floors at 64 units, which only binds below
`bits ≈ 10` where the entire grind is microseconds. The deployed `bits ∈ {14, 16}` are far above it,
and §2(c) sweeps the window independently at both.

---

## 5. ⚑ The defect inside the fix: rayon's `Range<u64>` is UNINDEXED

The first landed version was a straight windowed min, and it under-delivered:

| threads | crit counted (first version) | crit derived |
|---:|---:|---:|
| 4 | 9,928 | 6,144 |
| 8 | 5,704 | 3,072 |
| **12** | **9,942** | **2,052** |

One worker was doing **40% of a window** at 12 threads, and 12 threads was *worse* than 8 — the
signature of a split that is not happening.

**Cause, read not guessed:** rayon implements `IndexedParallelIterator` for ranges of
`u8/u16/u32/usize/i8/i16/i32/isize` and leaves `u64/i64/u128/i128` **unindexed**. An unindexed
producer halves **on demand** — only when a worker goes idle and steals. On a box at load 35 the
steal does not arrive promptly, so a "complete parallel scan" quietly becomes a mostly-serial one.
Every grind site in this crate ranges over `u64` or `u32`-widened-to-`u64`.

**Fix:** iterate the window as a `usize` range (a window fits trivially) so it is *indexed*, and
force the split up front with `with_max_len`, sized to `threads × 8` tasks per window. Same answer
— the window still cannot reach it — and the counted critical path went from 9,942 to 2,923 at 12
threads.

> **The class:** a parallel primitive that is *correct* and whose parallelism is *conditional on
> scheduling luck*. It cannot be caught by any correctness test, and on an idle box it would have
> measured fine. It was found only because the derived count and the counted count were both
> printed and disagreed — which is the argument for printing both.

---

## 6. The BN254 outer path

`MultiField32Challenger::grind` is the outer/shrink challenger, the one the apex, shrink and gnark
byte-parity gates ride on. `grind-phase.md` §0b flagged its pathology without measuring it: it is
**neither SIMD-packed nor batched**, so one candidate costs one whole **BN254 Poseidon2 duplex**
rather than a packed BabyBear permutation ÷ 4 lanes.

`circuit-prove/tests/outer_grind_schedule.rs` (new) carries the same obligations on that path.

### Correctness — same three checks, on the challenger the apex rides on

| check | result |
|---|---|
| old `find_first` vs new `grind`, 12 transcripts at `bits=12` | identical on every one |
| **one draw at the DEPLOYED `OUTER_FRI_QUERY_POW_BITS = 16`** | **identical: `w = 31,841`** |
| exhaustive minimality | all 2,857 candidates below the witness invalid |
| window invariance, 7 sizes from 1 to 2^20 | all returned 2,857 |

### ⚑ The per-candidate price, measured: 16.5 µs

> **One BN254 duplex = 16.5 µs**, against ~758 ns for a packed BabyBear batch covering **four**
> candidates. That is **~87× per candidate** — the outer grind is where the absolute milliseconds
> are, exactly as `grind-phase.md` §0b predicted without measuring it.

### The same pathology, and the same fix — `bits=14`, witness 28,953, counts in BN254 duplexes

| threads | crit BEFORE | crit AFTER | **crit ×** | work BEFORE | work AFTER | work × (vs BEFORE@1) |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 28,954 | 32,768 | 0.88 | 28,954 | 32,768 | 1.13 |
| 4 | 28,954 | 8,264 | 3.50 | 115,238 | 32,768 | 1.13 |
| **12** | **29,854** | **3,147** | **9.49** | 140,901 | 32,768 | **1.13** |

**BEFORE is flat — 28,954 at 1 thread, 29,854 at 12, scale 0.97** — the leaf's defect reproduced on
the outer path, while its total work rose 4.9×. AFTER is **9.49× on the critical path** for **+13%
work**, and it scales cleanly (3.97× at 4 threads, 10.41× at 12 by its own T=1 baseline).

### What that is worth at the deployed `bits = 16`

Derived from the exact counts and the measured 16.5 µs/candidate — an apex or shrink proof pays one
of these:

| | mean critical path | at 16.5 µs/candidate |
|---|---:|---:|
| BEFORE (`find_first`, any thread count) | 65,536 calls | **≈ 1.08 s** |
| AFTER (`c = 1/4`, T = 12) | 5,939 calls | **≈ 98 ms** |
| | | **11.0×** |

*(`5,939 = E[windows] 4.35 × window 16,384 ÷ 12`. The `E[windows]` is the leaf's 512-draw
measurement at `c = 1/4`; the draw is the same geometric process on both paths, only the
per-candidate price differs, so it transfers. The `T = 12` division is the derived one — the
outer path counted 10.41× of its own T=1 baseline at `bits = 14`, i.e. it splits better than the
leaf does, because a 16.5 µs unit of work dwarfs any stealing latency.)*

⚑ **About a second of wall clock per outer proof, and it was the same defect as the leaf's — just
87× more expensive per candidate and therefore never noticed as a *grind* problem.** In absolute
milliseconds it is the largest win in the lane.

### ⚠ But name the denominator: a second off a ~31-second shrink

A real BN254-native shrink, measured end-to-end through the fixed grind
(`apex_shrink_bn254_tooth`, 2026-08-14, load 68):

| | |
|---|---:|
| apex fold (BabyBear, inner) | 15.34 s |
| **shrink prove (BN254-native, outer)** | **30.85 s** |
| shrink verify | 131 ms |
| shrink proof | 459,805 B |

So the outer grind was **~1.08 s of a ~31.9 s shrink prove ≈ 3.4%**, and is now ~0.3%. That is a
real second and it is free, but **the outer grind was never the dominant term in a shrink** and this
figure must not be quoted as a 31 s → 1 s anything. The leaf is where the grind is a *large share*
of its prove (~25% per `phase-profile.md` §4); the outer path is where it is a large *number*.

That run is also the outer path's real-proof evidence: a full 2-turn apex fold, a BN254-native shrink
prove, a verify, and the tamper-rejection step, all green through the new schedule.

---

## 7. What this does NOT change

* **Not `pow`.** 16 stays. `grind-phase.md` §5's closed form puts `p* = 15.97` at the weighting this
  system uses; the fix moves `p*` *up*, and raising it is a soundness ledger move (`Bits 34 → 37` at
  UDR) to be argued on its own, not smuggled in as an optimisation.
* **Not the predicate.** `check_witness` is untouched at every site. The verifier does the same one
  permutation it always did.
* **Not the determinism delta.** `90680ee7d` is *preserved*, not reverted: the minimal witness is
  still what comes back, which is why §2 can compare against integers recorded before this change.
* **Not the position of the grind.** `grind-phase.md` §0 shows the grind cannot move off the
  critical path without weakening what the witness binds. Still true.

---

## 8. Reproduce

```bash
cd ~/dev/breadstuffs
# ⚠ never pipe cargo into head/grep -m: head exits, SIGPIPE kills the build, and the pipeline
# still reports success. Redirect and grep the file. (PREFLIGHT, 2026-08-14.)
# ⚠ and resolve the test binary AFTER the build — its hash changes when the source does.
cargo test -p dregg-circuit --release --test grind_phase_measure --no-run > /tmp/b.log 2>&1
B=$(ls -t target/release/deps/grind_phase_measure-* | grep -v '\.d$' | head -1)

$B g6_windowed_grind_returns_the_old_paths_witness           --nocapture --exact --test-threads=1
$B sweep::g7_proof_bytes_are_identical_under_the_windowed_schedule --nocapture --exact --test-threads=1
DREGG_GRIND_REPS=9 \
  $B g3_grind_thread_scaling                        --ignored --nocapture --exact --test-threads=1

cargo test -p dregg-circuit-prove --release --test outer_grind_schedule --no-run > /tmp/o.log 2>&1
O=$(ls -t target/release/deps/outer_grind_schedule-* | grep -v '\.d$' | head -1)
$O outer_windowed_grind_returns_the_old_paths_witness --nocapture --exact --test-threads=1
$O outer_grind_thread_scaling               --ignored --nocapture --exact --test-threads=1
```

Release only. §G6 and §G7 are ordinary gates (not `#[ignore]`d) and are the ones that must stay
green; §G3 and the outer scaling test are measurements.

Landed in `11cff8852` (the five grind sites + §G6/§G7) and `00b2cf2d5` (the BN254 measurement).

---

## 9. What is NOT covered, stated plainly

* **The outer path's proof BYTES are not pinned against a pre-fix golden.** The inner path is
  (§2(d): `w = 47,912` and a 138,220 B anchor, both recorded 2026-08-13). For the outer path there
  was no equivalent integer on record, so the evidence is the differential at the deployed
  `bits = 16` plus the structural argument — strong, but one rung below the inner path's.

### ⚑ And a found defect that is not mine: THE wrap capstone tooth has been red since 2026-08-08

Running `apex_shrink_bn254_tooth::real_apex_shrinks_bn254_native_and_verifies` as an outer-path
witness, it failed —

```
QueryProofCountMismatch { expected: 19, got: 38 }
```

— which a grind cannot cause (a PoW witness is one field element; it cannot change a *count*, and a
wrong witness fails as `InvalidPowWitness`, which §G5 demonstrates constructively). **Read, not
guessed:** the sibling `apex_shrink_gnark_fixture.rs:175-181` documents this exact error verbatim.
Since the **2026-08-08 mint split** a turn-chain leaf mints at `create_recursion_config`'s engine, so
every fold above it — the apex included — emits `(lb 3, q 38)`; reading the apex at the pre-split
`ir2_leaf_wrap_config()`'s `(lb 6, q 19)` is exactly the failure `config.rs` predicts. **The fix
landed in one of the two tests and not its twin**, and the twin's `#[ignore]` reason says `"SLOW"`
rather than `"broken"`, so nothing surfaced it for six days.

Fixed here — the same one-line rotation to `turn_chain_root_config()` the sibling already carries.
**It now passes**, in 46 s, and its numbers are §6's shrink table. This is the `documented ≠ detected`
class: an `#[ignore]`d test that cannot pass is indistinguishable from an `#[ignore]`d test nobody ran.

⚠ **I had to establish it was not my own regression before I could use the tool at all**, which is
the cost of a stale red in a shared tree: it makes every new change look guilty first.
* **`SerializingChallenger{32,64}::grind` and `grind_generic` have no consumer in this tree.**
  Grepped: nothing in `circuit`, `circuit-prove`, `recursion-verify` or `turn` constructs them.
  They were fixed because they are the same defect in the same vendored crate, but they are
  unexercised, so their fix rests on the shared `windowed_find_map_first` being right rather than on
  a test of their own.
* **Every ratio here is at `T ≤ 12` on one machine.** The derived columns extrapolate to any `T`;
  the counted ones do not, and the two already differ by 1.42× at `T = 12` on this box (§3(c)).
