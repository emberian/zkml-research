# One device, N pipelines — making the measured fusion win reachable in `fhegg-fhe`

*Lane note, written incrementally. 2026-08-13/14.*

## The job

`~/dev/zkml-research/notes/wgpu-fusion.md` measured the fusion thesis and found it real:
**1.30–4.92x end-to-end on a single hand-off, 2.7–7.1x at 2^20–2^22 on memory traffic alone**
(sync discounted), and — the structural result — **fused per-stage cost falls 3.8–5.3x across
K=1→16 batched hand-offs and is still falling, while unfused plateaus under 2x.**

That lane also found *why* the win had never been available: `Arena` owned exactly one
`wgpu::ComputePipeline`, and every other wgpu module in the crate stood up its **own
`wgpu::Device`**. Two wgpu devices cannot share a buffer. So a resident hand-off between the FHE
kernel and anything else was **unreachable by construction**, not unimplemented. It made `Arena`
multi-pipeline and added the MLE fold. The rest of the crate did not move. This lane moves it.

---

## 1. Inventory — every site in the crate that created its own `wgpu::Device`

Method: `grep -rn 'request_device' --include='*.rs'` across the workspace, then read each site.
The brief named three; there were **nine**, and two of them were in one file.

| # | site | kernel | had a device because | migrated |
| --- | --- | --- | --- | --- |
| 1 | `src/gpu_arena.rs:410` `arena()` | `bfv_fold` / `bfv_to_babybear` / `mle_fold` | the arena itself | ✅ |
| 2 | `src/bfv_gpu.rs:37` `ctx()` | one-shot BFV fold-add | own `OnceLock` | ✅ |
| 3 | `src/bfv_ntt_gpu.rs:1389` `GpuCtx::initialize` | BFV RNS-NTT (3-limb Montgomery, q < 2^48) | own `OnceLock` | ✅ |
| 4 | `src/private_book_bfv_wgpu.rs:85` `gpu_ctx()` | private-book signed dot | own `OnceLock` | ✅ |
| 5 | `src/tfhe_wgpu.rs:557` `init_gpu()` | torus negacyclic MAC | own `OnceLock` | ✅ |
| 6 | `src/tfhe_wgpu.rs:2090` `init_external_gpu()` | TFHE external product | **a second `OnceLock` in the same file** | ✅ |
| 7 | `src/tfhe_ntt_wgpu.rs:236` `GpuContext::initialize` | TFHE exact RNS-NTT batch | own `OnceLock` | ✅ |
| 8 | `src/tfhe_blind_rotation_wgpu.rs:175` | TFHE device-resident blind rotation | own `OnceLock` | ✅ |
| 9 | `src/tfhe_blind_rotation_ntt_wgpu.rs:232` | TFHE transform-resident PBS | own `OnceLock` | ✅ |

Two more in `src/bin/`, deliberately **not** migrated — see §6.

Outside `fhegg-fhe` and out of this lane's scope, but worth recording because the same wound is
there: `circuit-prove/src/gpu_backend.rs` (2 sites), `circuit-prove/src/gpu_hidingfri_fold.rs`,
`fhegg-solver/src/gpu.rs`, `vendor/bulletproofs-r1cs-wgpu/` (5 sites), plus five `circuit-prove/sketches/`
probes. **`circuit-prove` is the STARK prover** — the other half of the fusion thesis — so its two
devices are exactly where the next hand-off would want to land. Recorded, not touched.

### ⚑ The finding that made the migration safe

Every one of the nine sites requested its device with **byte-identical parameters**:

```rust
wgpu::DeviceDescriptor {
    label: /* the only thing that differed */,
    required_features: wgpu::Features::empty(),
    required_limits: adapter.limits(),
    memory_hints: Default::default(),
}
```

and selected its adapter with `PowerPreference::HighPerformance`, no surface, no fallback adapter.
So one shared device is not a negotiated compromise between nine different requests — it is
**literally the request each of them already made**. Nothing is widened, nothing is narrowed. That
is what reduces this from a rewrite to plumbing with a correctness obligation.

---

## 2. What was built

`fhegg-fhe/src/gpu_device.rs` — one `wgpu::Instance` / `Adapter` / `Device` / `Queue` behind a
process-wide `OnceLock`, plus the error-scope guard (§3).

```rust
pub fn shared_gpu() -> Result<&'static SharedGpu, SharedGpuUnavailable>;
```

`Result` rather than `Option` because callers already distinguish *no adapter* from *device
refused* in their own error enums (`TorusCpuFallbackReason::NoAdapter` vs `::DeviceRequestFailed`),
and collapsing them would have quietly coarsened a diagnostic.

**Pipelines stayed with their kernels.** The brief's phrase was "one device, one queue, one buffer
pool, N pipelines", and the tempting reading is that `Arena` should own all N. It should not: a
pipeline is kernel-local knowledge (bind-group layout, entry points, workgroup shape), and hoisting
`torus_pbs_transform_resident`'s twenty pipelines into `Arena` would make `gpu_arena.rs` depend on
every kernel in the crate. What has to be shared is the **device, the queue and the allocator** —
because that is what a buffer belongs to. Each module keeps `device.clone()` / `queue.clone()`
(both are `Arc`-backed handles in wgpu 24) in its existing context struct, so the diff at each site
is the initializer and nothing else.

Module-level **policy** was deliberately not centralized either. `tfhe_blind_rotation_ntt_wgpu`
refuses when `max_storage_buffers_per_shader_stage < 9` or the workgroup is too small — a statement
about what *that shader* needs. It now reads `shared.limits` and refuses identically.

---

## 3. ⚑ The one hazard consolidation introduces, and closing it

This is the part a "just share the device" change gets wrong.

**wgpu error scopes are a stack on the device, not a per-caller channel.** Nine devices meant nine
independent stacks. One device means one. And these modules do not push scopes only at init — they
push them in *hot paths*, 15 pairs across `src/`:

```
bfv_ntt_gpu            init + execute_batch
tfhe_wgpu              init_gpu + MAC run + init_external_gpu + external-product run
tfhe_ntt_wgpu          init + run
tfhe_blind_rotation_wgpu       init + run + prepare_extract_keyswitch + run_extract_keyswitch_prepared
tfhe_blind_rotation_ntt_wgpu   init + prepare + run_with_finalization + run_resident_gt_stages
```

Two threads in two different kernels now interleave `push`/`pop` on one stack. The failure is not
merely a false red: thread B can pop **A's** captured validation error, so the error is reported
against the wrong kernel *and* A's own pop returns `None` and A proceeds. **That is a weakened
check, introduced by a performance change** — precisely the thing that is never worth it.

`ValidationScope` closes it: an RAII handle that serializes the whole push..pop region against every
other holder in the process, **reentrant per thread** so a kernel that nests scopes (or calls
another kernel that opens one) cannot deadlock against itself. Nesting on one thread is properly
nested and is what the wgpu stack is *for*; interleaving across threads is what it cannot express.

Two things fall out that the raw calls did not have:

* **An early return can no longer leak a scope.** Every previous site pushed a scope and popped it
  up to *537 lines later* (`run_resident_gt_stages`, push :1222 → pop :1759) with `?`-returns in
  between. Each of those returns left an unbalanced scope on the device forever. `Drop` pops it now.
* **It was already unsound *within* a module.** Each module's device was a `OnceLock` static shared
  by all its callers, so two threads calling the same kernel already interleaved on one stack. This
  is a pre-existing bug the consolidation forced into view and fixed.

The cost is that concurrent GPU calls serialize across the push..pop region. They were never correct
concurrently, and the regions are dominated by device work one queue serializes anyway.

---

## 4. Tests — per kernel, and for the seam, and for the invariant itself

**Every migrated kernel keeps its existing teeth.** The suite that covers them is not the default
`cargo nextest run`: four of the nine sites are behind `#[cfg(feature = "tfhe-integer")]` and one
behind `amm-input-binding`, and several of the residency teeth are `#[ignore]`d behind
`DREGG_REQUIRE_WGPU=1`. A default run compiles none of the TFHE kernels and skips the GPU teeth —
i.e. **the obvious green says nothing about most of this change.** The run that means something is

```
DREGG_REQUIRE_WGPU=1 cargo nextest run -p fhegg-fhe --release --profile full \
  --features tfhe-integer,amm-input-binding --run-ignored all
```

Coverage per site, checked before migrating rather than after:

| site | teeth |
| --- | --- |
| `bfv_gpu` | 2 in-file, incl. GPU-vs-CPU fold bit-for-bit |
| `bfv_ntt_gpu` | 10 in-file + `bfv_odd_ntt_wgpu_required`, `bfv_ntt_wgpu_crossover`, `wgpu_correctness_matrix` |
| `private_book_bfv_wgpu` | 1 in-file + `private_book_bfv_wgpu_matrix` (incl. `require_real_wgpu_…_residency`) |
| `tfhe_wgpu` ×2 | 9 in-file + `tfhe_wgpu_parity`, `tfhe_wgpu_cmux`, `wgpu_correctness_matrix` |
| `tfhe_ntt_wgpu` | `tfhe_wgpu_ntt_crossover` |
| `tfhe_blind_rotation_wgpu` | `tfhe_wgpu_blind_rotation` |
| `tfhe_blind_rotation_ntt_wgpu` | `tfhe_wgpu_pbs_extract_keyswitch`, `tfhe_wgpu_pbs_deployed_envelope` |
| `gpu_arena` | 11 in-file + `wgpu_mle_fold` (7), `collective_gpu_additive`, `gpu_qualification_diagnostics` |

Three new test files, because three things were not covered by any of the above.

**`tests/wgpu_shared_device.rs` — the invariant, as a gate that can go red.**
The property that matters is not "the code was edited" but *"there is exactly one place in this
crate that opens a device"*, and that is a property a future edit breaks silently: a new kernel
written the way all nine were written compiles, passes its own tests, and is invisibly unfusable.
So `only_gpu_device_may_open_a_wgpu_device` walks `src/` and fails on any `.request_device(` outside
`gpu_device.rs`, with a two-entry **debt ledger** (`KNOWN_PRIVATE_DEVICES`) for the bench binaries
in §6 — spelled as an allow-list rather than "skip `src/bin/`" so a *new* device anywhere still goes
red, and with a downward ratchet so a fixed entry cannot linger as a lie. `two_arenas_share_one_device`
checks the same thing at runtime: two `arena()` calls used to hold two devices.

**`concurrent_kernels_on_one_device_neither_deadlock_nor_cross_talk`** is the tooth for §3. Eight
threads, two different modules' kernels, four rounds each, every answer checked against a CPU
oracle. It fails by *hanging* if `ValidationScope` is not reentrant and by *mismatching* if a pop
ever ate a sibling's error and let a bad result through.

**`tests/wgpu_ntt_fold_fusion.rs` — the seam, before anything measured over it.** A fusion benchmark
whose two arms compute different things measures nothing, and the way that happens silently is a
layout or bookkeeping mismatch exactly at the join. Bit-equality against **two** independent
references, because either alone is blind: the host round trip through the deployed
`forward_odd_batch`, and a pure CPU transform-then-fold. Plus `adopted_bounds_survive_the_fold…`
(the plaintext bound must still arm the wrap gate — a seam that dropped the bookkeeping would fold
correct residues and pass the first tooth) and `adopt_refuses_a_buffer_that_does_not_match_the_declared_shape`.

### ⚑ The gates went red first, and both reds were real

Not a formality — the first run of the three new files was **3 failed / 22 passed**, and neither
failure was a flaky:

* `only_gpu_device_may_open_a_wgpu_device` matched the *word* `request_device`, so it flagged
  `bfv_gpu.rs` — whose only occurrence is a **comment explaining what it used to do**. A gate that
  goes red for documenting its own history teaches people to delete the documentation. Fixed to
  match `.request_device(`.
* The seam tooth and the concurrency tooth both died on `Incompatible("poly count is not 2")`. A BFV
  ciphertext is a *pair* of polynomials and `bfv_lean::fold` refuses any other count — so my
  single-poly stand-in folded perfectly well on the GPU and **had no CPU oracle at all**. That is
  the failure mode these tests exist to prevent, found in the tests themselves. The batch is now
  always an even number of polynomials consumed two at a time; the buffer layout is unchanged
  because `[polynomial][rns row][coefficient]` is contiguous either way.

Final state: **48/48 green** on the default-feature GPU suite including all three new files, and
**8/8 green** on the featured TFHE/private-book teeth — every kernel in the inventory has at least
one passing tooth post-migration:
`private_book_bfv_wgpu_matrix` ×3 (incl. `require_real_wgpu_…_residency`), `tfhe_wgpu_blind_rotation`,
`tfhe_wgpu_cmux`, `tfhe_wgpu_ntt_crossover` ×2, `tfhe_wgpu_parity`.

### ⚠ `1 failed` that was my own kill, not an assertion

The featured run reported `9/10 tests run: 8 passed, 1 failed` and `error: test run failed`. There
was no failing assertion. The line above the summary reads

```
SIGTERM [3017.811s] (9/10) …tfhe_wgpu_pbs_deployed_envelope deployed_918_by_918_dense_pbs…
```

— I had killed the background job, and **nextest scores a killed test as a failure**, indistinguishable
in the summary line from a real one. I came within one command of reporting a regression in a module
whose diff is a pure initializer swap. This is the *"refusal renders as the expected verdict"* /
*"the wrapper answers for the work"* class: **read the per-test line, never the summary count.**
It happened **three times**, at 3017.8 s, 3137.0 s and 3106.0 s.

### ⚑ Three "failures" at the same wall-clock, and the wrapper that caused all three

Those three numbers are within **2% of each other**, on two different tests, across two sessions.
That is not slowness and it is not flakiness — it is a **limit, fired reproducibly**. Chasing it
found the limit is **not in the code and not in the test runner**:

* nextest's `full` profile sets `slow-timeout = { period = "60s", terminate-after = 60 }` — a 3600 s
  hard terminate. **3106 s never reached it**, and `grep -n 'pbs\|tfhe\|envelope' .config/nextest.toml`
  returns nothing, so no tighter per-test override applies either.
* The wrapper subshell's trailing `echo "EXIT=$?"` **never wrote a line** — so `cargo nextest` never
  returned at all. The clean `Summary` and `error: test run failed` in the log are nextest's SIGTERM
  handler reporting on its way down, not a verdict.

So the killer is **the agent harness stopping a backgrounded bash job at ~50 minutes**, and the test
simply takes longer than that. Every one of the three "1 failed" lines is that, wearing a verdict's
clothes.

⚠ **The lesson generalises past this repo:** a test longer than the harness's background-job lifetime
is *unrunnable* from a background job, and it does not report itself as unrunnable — it reports as
**failed**, at a plausible-looking duration, with a summary line that reads exactly like a real
assertion failure. Anything hour-scale must be launched **detached from the process group**
(`start_new_session=True` from Python; macOS has no `setsid`) or it can never pass, no matter how
correct the code is.

### What is confirmed, and the one thing that is not

Confirmed post-migration, every kernel in the inventory covered by at least one passing tooth:

| | |
| --- | --- |
| default features, incl. all 3 new files | **48/48** |
| featured TFHE / private-book | **9/9** — `private_book_bfv_wgpu_matrix` ×3, `tfhe_wgpu_blind_rotation`, `tfhe_wgpu_cmux`, `tfhe_wgpu_ntt_crossover` ×2, `tfhe_wgpu_parity`, **`tfhe_wgpu_pbs_extract_keyswitch` (1.43 s)** |

⚠ **Not confirmed: 5 `#[ignore]`-gated hour-scale tests** — 4 in `tfhe_high_level_wgpu`, 1 in
`tfhe_wgpu_pbs_deployed_envelope`. Each runs **>52 minutes** (all three SIGTERMs above landed at
~3100 s *inside a single test*), so the set is ~4.5 hours serialized. **They have never failed** —
one run died to ENOSPC and three to the ~50-minute background-job limit described above.

The module they cover, `tfhe_blind_rotation_ntt_wgpu`, **is** covered by a passing tooth —
`blind_rotate_extract_and_keyswitch_matches_tfhe_exactly`, which is a plain `#[test]` and passed in
1.43 s. So the gap is not "an unverified module"; it is "the deployed 918×918 envelope and the
high-level `FheUint32` path unverified at deployed scale." The one of the five that bears most
directly on this change is `deployed_918_by_918_dense_pbs_matches_tfhe_and_reuses_device_keys` —
**device-key reuse across calls is exactly the lifetime consolidation altered.**

Run detached, it survived past every previous kill point and then hit a **fourth** stopping
condition, a different one:

```
TIMEOUT [3600.150s] (1/1) …deployed_918_by_918_dense_pbs_matches_tfhe_and_reuses_device_keys
Summary [3600.155s] 1 test run: 0 passed, 1 timed out, 449 skipped
```

⚑ **That is nextest's own `slow-timeout` (`period = "60s" × terminate-after = 60` = 3600 s) in
`profile.full`, hit to the millisecond** — and note nextest labels it **`TIMEOUT`**, a *different
word* from the `SIGTERM` the harness kills produced. Three stopping conditions, three labels, one
summary line: **`1 failed` / `error: test run failed` means "harness killed it", "runner timed it
out", or "the code is wrong", and only the per-test label tells you which.**

And the cap was **my** mistake, not the test's: its own `#[ignore]` message documents the invocation
as `cargo test -p fhegg-fhe --test tfhe_wgpu_pbs_deployed_envelope -- --ignored`, which has **no
timeout at all**. I reached for `nextest --profile full` out of habit and imposed an hour cap on a
deliberately quadratic 918×918 baseline that was never written to run under one. It is relaunched
the documented way, detached, at `…/scratchpad/tfhe-918-cargotest.log`.

⚠ **The honest state of this lane: that test's result is not in evidence.** A `PASS` in that log
closes the gap; a real assertion failure reopens the TFHE half of this change. A `SIGTERM` or
`TIMEOUT` line is neither — read the label, not the count. What can be said without it is that the
change to this module is an initializer swap plus a mutex that is *uncontended* under
`--test-threads 1`, and that the module's behaviour is carried by
`blind_rotate_extract_and_keyswitch_matches_tfhe_exactly`, which passes in 1.43 s.

---

## 5. The measurement — what the consolidation unlocked

`src/bin/gpu_ntt_fold_fusion_bench.rs`, same shape as `gpu_fusion_bench`.

**Host:** Apple M2 Max, unified memory, wgpu 24 → Metal, `IntegratedGpu`.
Median of 11 reps, fused and unfused interleaved; both arms asserted equal every case.

⚠⚠ **READ THIS BEFORE QUOTING ANY NUMBER BELOW.** These were taken on a **contended box** — other
lanes were running `dregg-circuit` and `dregg-circuit-prove` test suites throughout, load average
6.5 and at times far higher, 46 login sessions. That is visible in the data: the same cell varies
**up to 2.1x across the three runs** (the 50 MB Pair A fused arm: 33.6 / 69.2 / 39.0 ms). Absolute
microseconds here are **not evidence of anything.**

And **"but I quote ratios, so contention cancels" is false** — it does not. The two arms are not the
same *kind* of work: the unfused arm's extra cost is a host readback and `RnsPoly` reassembly, which
is **memory-bound**, while the shared GPU work is compute-bound, and the two degrade at different
rates under load. A ratio of two differently-bound quantities on a loaded box is *itself* a moving
target, which is why the run-to-run spread below is reported cell by cell instead of averaged into
one flattering figure.

What survives contention is the **shape and the sign**: fusion wins in 36/36 cells across both pairs
and all three runs, the win grows with size, and the K-sweep's fused/unfused asymmetry is monotone in
every run. Those are the claims this section makes. It does **not** claim a calibrated speedup, and
any hardware argument wants a re-measure on a quiet box.

Two seams, chosen as the two kernels most likely to be composed in a real pipeline:

* **PAIR A — forward NTT batch → RNS fold-add.** The deployed BFV aggregation shape: transform,
  then aggregate. FUSED adopts the NTT's own output buffer; UNFUSED reads it back as `RnsPoly`s and
  uploads them again, which is what this crate did before today *because it had no other choice*.
* **PAIR B — NTT → fold → BabyBear bridge → MLE fold.** Three kernels from two modules, two seams,
  one device. Before the consolidation this needed two devices and was unreachable twice over.

⚑ **The sweep grows the BATCH, not the degree, past 4096.** Not a stylistic choice: the deployed
`FOLD_MODULI` admit a negacyclic NTT only up to the deployed `FOLD_DEGREE`. At 16384 `fhe-math`
refuses outright — *"Impossible to construct a Ntt operator"* — because q ≢ 1 mod 2N. Growing the
batch reaches the same byte counts through the shape a real aggregation actually has.

### PAIR A — NTT → fold (three runs)

```
#  degree batch     batch_B   fused_us   unfus_us   nttdl_us      raw  traffic
      256     8       49152     1601/2411/1656   2933/4124/3001   1.83/1.71/1.81x   — 
     1024     8      196608     2991/3934/3060   4433/5582/4483   1.48/1.42/1.47x   —
     4096     8      786432     4583/5632/4677   6151/7590/6281   1.34/1.35/1.34x   1.53/1.61/1.52x
     4096    32     3145728     7772/7432/7931  10466/10687/10573 1.35/1.44/1.33x   1.44/1.65/1.42x
     4096   128    12582912    13053/17204/13214 19758/29879/19988 1.51/1.74/1.51x  1.59/1.86/1.58x
     4096   512    50331648    33638/69213/38963 59881/99558/70054 1.78/1.44/1.80x  1.82/1.45/1.83x
```

**Fusion wins in all 18 cells: 1.33x–1.83x raw, 1.42x–1.86x traffic-only.**

The dominant unfused term is `nttdl_us` — the NTT's own readback and `RnsPoly` reassembly. At every
size it is *most of the fused pipeline's entire cost* (e.g. 46.4 ms of a 59.9 ms unfused run at
50 MB, against 33.6 ms fused). That term is exactly what adopting the buffer deletes.

### PAIR B — NTT → fold → bridge → MLE fold (three kernels)

```
#  degree batch   table_len          fused_us          unfus_us      raw            traffic
      256     8        4096   1702/3132/4441   4306/6199/9775   2.53/1.98/2.20x   — / — /2.88x
     1024     8       16384   1795/3266/3892   4466/7247/10191  2.49/2.22/2.62x   — / — /3.76x
     4096     8       65536   3315/6275/4098   6272/11014/9402  1.89/1.76/2.29x   2.78/2.23/3.13x
     4096    32       65536   3991/9841/8318   8081/15745/14798 2.02/1.60/1.78x   2.75/1.79/1.97x
     4096   128       65536  12797/19971/16539 20702/43808/28190 1.62/2.19/1.70x  1.71/2.36/1.78x
     4096   512       65536  33776/63308/46036 62729/98354/90781 1.86/1.55/1.97x  1.90/1.58/2.01x
```

**1.55x–2.62x raw, 1.58x–3.76x traffic-only, winning in all 18 cells.** Two seams beat one, which
is the expected shape and the reason it was worth building the three-kernel chain rather than
stopping at Pair A.

### The compounding result

```
#   K   fused/stage (us)      unfused/stage (us)         ratio
    1   3825 / 6869 / 4802    6252 / 9858 /  9807    1.63/1.44/2.04x
    2   2610 / 5912 / 4867    5657 / 9498 /  9055    2.17/1.61/1.86x
    4   2638 / 4547 / 3636    5728 /10138 /  8748    2.17/2.23/2.41x
    8   1954 / 4171 / 2860    5210 /10836 /  8019    2.67/2.60/2.80x
   16   1747 / 4159 / 2641    5219 /10784 /  8256    2.99/2.59/3.13x
fall K=1→16   2.19 / 1.65 / 1.82x        1.20 / 0.91 / 1.19x
```

**The prior lane's structural finding reproduces on this pair.** Fused per-stage cost falls
1.65x–2.19x across K=1→16 and is still falling at K=16; unfused is **flat** (0.91x–1.20x, i.e. no
fall at all in one run), because every unfused stage carries its own irreducible NTT readback. The
ratio grows monotonically in all three runs, from ~1.4–2.0x at K=1 to **2.6–3.1x at K=16**.

### ⚑ A defect in my own measurement, found and fixed rather than reported

The first K-sweep showed fused per-stage cost *rising* and the ratio *falling* — an apparent
refutation of the prior lane's headline. It was an artifact: my fused arm called `download` after
every stage, so it paid K synchronizations too and was not fused at all. The fused loop now reads
nothing back until the end; one device and one queue means the single final download waits on every
stage's work, which is exactly the property being measured.

Worth naming as a class, because the artifact was *plausible* and pointed the flattering way for a
skeptic: **a "fused" pipeline that synchronizes per stage measures the unfused one.**

### ⚠ And one about how the traffic column is allowed to print

An early run printed **1541x** traffic-only for a case whose raw speedup was 1.83x — the subtraction
of a ~1.7 ms floor from a ~1.7 ms measurement, i.e. noise over noise. The ratio is now printed only
when *both* arms clear the floor by 2x, and `—` otherwise. Quoting the flattering half of a pair is
how a nothing result reads as a triumph.

### Honest comparison to the prior lane

These wins (1.3x–2.6x raw, 1.4x–3.8x traffic) are **smaller than the fold→MLE seam's 2.7x–7.1x**,
and the reason is structural rather than disappointing: the NTT's own GPU work is a far larger share
of this pipeline than the MLE fold's was of that one, so the hand-off is a smaller fraction of the
total. The *shape* — win at every size, growing with size, compounding with pipeline depth, unfused
plateauing — is the same.

⚠ **Both caveats still apply and both still travel with these numbers.** Unified memory makes every
figure a **lower bound**: a "download" here is a copy inside one physical DRAM. And the ~1.6–2.4 ms
synchronization floor is wgpu's, not physics — carry the `traffic` column into any hardware
argument, never `raw`.

---

## 6. What did not migrate, and why

**Two bench binaries keep their own device, and both are in the ratchet's ledger so the decision is
visible rather than forgotten.**

* **`src/bin/gpu_saturate.rs`** — its device is labelled `attribution-scratch` and exists to measure
  what a **cold** device costs for one buffer create+upload. Handing it the warm shared device would
  change the quantity it exists to report. It hands no buffer to anything, so there is no fusion to
  unlock. *(Its separate adapter **probe** could read `shared_gpu().info` and would be slightly
  better for it; that is cosmetic and was left alone.)*
* **`src/bin/ntt_four_step_bench.rs`** — a standalone four-step-NTT-as-GEMM experiment with its own
  engine, handing no buffer to another kernel. ⚠ It was also **being edited by another live lane**
  while this work ran (`MM` in `git status` throughout), so touching it would have clobbered
  in-flight work. If that NTT graduates into a library kernel it must take the shared device with it.

**Out of scope, but the same wound, recorded because the next hand-off wants it:** `circuit-prove`
— *the STARK prover*, i.e. the other half of the vFHE fusion thesis — has **three** private devices
(`src/gpu_backend.rs` ×2, `src/gpu_hidingfri_fold.rs`), plus `fhegg-solver/src/gpu.rs` and five
`vendor/bulletproofs-r1cs-wgpu` sites. An FHE→prover hand-off across crates is unreachable by
construction for exactly the reason it was unreachable inside `fhegg-fhe` this morning.

**Nothing in `fhegg-fhe/src/` outside `bin/` failed to migrate.** All nine library sites moved.

---

## 7. Box note, not lane work

The machine's data volume hit **100% full (2.2 GiB free)** mid-run and killed a nextest run with
`ENOSPC`. Reclaimed `fhegg-fhe/target/` — a **9.6 GB private per-crate target dir with nothing
touched since July 19**, the exact "a private `CARGO_TARGET_DIR` is a TRAP" pattern already in the
memory index. There are **~300 GB more of the same** across the workspace (`wasm/target` 89 G,
`poa-curator` 25 G, `sdk-py` 20 G, `discord-bot` 19 G, `poa-solana-gate` 14 G, `dregg-tui` 12 G,
none touched in days). Not deleted — that is other lanes' state and not this lane's call.
