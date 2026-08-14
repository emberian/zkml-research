# The LDE's time is not its arithmetic — the quotient-chunk layout, measured

**Status: COMPLETE (2026-08-14).** Every number below is `[MEASURED]` on this box unless labelled
otherwise. One hypothesis was formed, tested and **refuted**; it is kept in §3 because the
refutation is the finding.

Predecessor: `field-op-counts.md` §G1 Finding 3 — *"twelve separate `coset_lde_batch` calls on
width-4 matrices … the cost is per-CALL and per-narrow-matrix, not per-operation … batching them
into three matrices of width 8/8/32 is the shape of the fix."* This lane confirms that diagnosis,
names the mechanism, does the batching, settles what the verifier sees — and finds that **the
mechanism has a second, larger consequence that the batching only partly collects.** §6.

Instruments: `breadstuffs/circuit/tests/ir2_field_op_counts.rs` §G6a–§G6f, §G7a–§G7c (new).
Change: `breadstuffs/vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs`, DREGG DELTA 3.

---

## 1. The diagnosis, re-measured `[MEASURED]`

Re-ran `§G1 field_op_counts_per_phase` from the committed harness, **unchanged and before touching
anything**, at `q = 19, pow = 0, b ∈ {3..7}` on the transfer workload. It reproduces exactly.

- **18 DFT calls per proof at every blowup**, and no others: 6 under `prove_batch`, 12 under
  `prove_batch>compute quotient`.
- **Zero `coset_idft_batch`, zero `coset_dft_batch`, zero `dft_batch`.** `get_evaluations_on_domain`'s
  slow path is never taken; `phase-profile.md`'s diagnosis of the phase stays refuted.
- **All twelve quotient calls are width 4**, in three height groups: `2 × (h=64)`, `8 × (h=8)`,
  `2 × (h=16)`. Stable at every blowup.
- Arithmetic share of the twelve: **3.48% → 3.53%** across b=3..7 (62,255 / 1,787,402 up to
  457,424 / 12,970,515).

Read from source (`p3-batch-stark/src/prover.rs:323–409`): the three groups are three **AIRs**.
Chunk height *is* trace height (`quotient_domain.size() = trace_size · n_chunks`, cut into
`n_chunks`), so the group sizes read directly as quotient degrees — 2, 8, 2. `get_quotient_ldes` is
called **once per AIR with that AIR's whole chunk list**, so "batch into 8/8/32" is exactly one
call per AIR. (The true widths are **8 / 32 / 8** in call order; the predecessor's `8/8/32` was the
right multiset in the wrong order.)

⚠ `p3-batch-stark` already commits all twelve chunk LDEs in **one** MMCS batch
(`pcs.commit_ldes(quotient_chunk_mats)`, one `quotient_commit`). "Twelve commits" is twelve
**`coset_lde_batch` calls**, not twelve Merkle commitments — which is what makes §4 answerable.

`§G6a` also checks the per-chunk LDE shifts through the prover's own domain API
(`natural_domain_for_degree → create_disjoint_domain(h·n) → split_domains(n)`, then
`GENERATOR / shift`): chunk `i` is LDE'd at `ω^-i`, `ω = two_adic_generator(log₂(h·n))`, chunk 0 at
`ONE`. Nothing in §5 rests on a hand-derived shift.

---

## 2. ⚑ The mechanism, first as a one-parameter model `[DERIVED FROM MEASURED]`

Before any experiment: `phase-profile.md` §A's own per-blowup table already discriminates a
**per-call** constant from a **per-coset-iteration** one, because both LDE rows scale ≈2× per rung
while a per-call constant would be flat in `b`. A `coset_lde_batch` with `added_bits = b` runs one
iDFT and then **`2^b` separate size-`h` coset DFTs**. So the model is

> `LDE_time(b) = C · (#calls) · 2^b + arith(b)`

with `arith(b)` from §G1's counts at §G3's rates (0.1805 ns/mul, 0.1450 ns/add). Fitting `C` on the
**pre-change** run of §A on this box (`RAYON_NUM_THREADS=1`, min of 5):

| b | LDE total ms (before) | arith ms | **C (µs/coset-iteration)** |
|---:|---:|---:|---:|
| 3 | 2.670 | 0.280 | **16.6** |
| 4 | 4.872 | 0.531 | **15.1** |
| 5 | 8.568 | 1.032 | **13.1** |
| 6 | 15.811 | 2.035 | **12.0** |
| 7 | 30.121 | 4.042 | **11.3** |

**One constant, 11–17 µs, across a 16× range of `b`.** It then *predicts* the post-change LDE time
from the call count alone (18 → 9 DFT calls), before that time was measured:

| b | predicted after ms | measured after ms | error |
|---:|---:|---:|---:|
| 3 | 1.475 | 1.382 | +6.7% |
| 4 | 2.701 | 2.334 | +15.7% |
| 5 | 4.799 | 4.805 | −0.1% |
| 6 | 8.924 | 9.281 | −3.8% |
| 7 | 17.08 | 18.58 | −8.1% |

A one-parameter model with no free knobs landing inside ±16% on a box at load 25–35 is the
mechanism being right, not a fit.

---

## 3. ⚑ What the constant IS — one hypothesis refuted, one confirmed `[MEASURED]`

### 3a. The hypothesis: coset-twiddle tables. **REFUTED.**

Each of the `2^b` coset DFTs calls `get_or_compute_coset_twiddles((log_h, g_big^j · shift))` — and
every term in that (a `Θ(h)` power ladder, `log₂ h` heap allocations, a `spin::RwLock` write, a
`BTreeMap` insert) is a function of `(h, b)` alone, with **width never appearing.** In counts
(`§G6b`, cold-memo minus warm-memo, `added_bits = 6`) that is exactly what happens:

| h | twiddle term (ops) at w = 4, 8, 16, 32, 64, 236 | share at w=4 | share at w=236 |
|---:|---|---:|---:|
| 8 | 836 / 836 / 836 / 836 / 836 / 836 | 7.76% | 0.15% |
| 16 | 1,736 (identical at every width) | 6.37% | 0.12% |
| 64 | 14,963 (identical at every width) | **9.06%** | **0.17%** |

Perfectly width-independent, share falling as `1/w`. It is also the wrong answer. `§G6c` measures
the *same* cold-vs-warm split on a clock, one `coset_lde_batch` per timing window in both arms:
the difference is **−12% to +18%, sign-random, at all 14 geometries.** The tables cost essentially
nothing in time. ⚑ **A counted term that is width-independent is not thereby the cost.** This is
the §G1 Finding 2 lesson recurring one level down.

*(Two instrument notes, both paid for. The first cut of §G6c timed `cold` against a window holding
**two** calls and subtracted — and printed negative twiddle costs at 11 of 14 geometries, because
the second call allocates its output while the first is still live. A min-of-mins over
differently-shaped windows is not a difference. And the §G6b h=64 rows are ~2.5× the closed form
`63 + 2·15 = 93`: `Powers::collect_n` takes a **parallel** path at `n ≥ 16`, so those cells are
thread-count dependent; h=8 and h=16 match 13 and 27 exactly.)*

### 3b. The confirmation: the cost tracks the COSET COUNT, not the work.

`§G6d`, `RAYON_NUM_THREADS=1`. Hold the **output** fixed at `h · 2^b = 4096` and slide the split.
Total butterfly work is `Θ(4096 · w · log h)` — it *falls* monotonically as `b` rises.

| h | +b | cosets | µs (w=4) | µs/coset | µs (w=64) | µs/coset | rel. work |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 0 | 1 | 165.5 | 165.5 | 1023.5 | 1023.5 | 1.00 |
| 512 | 3 | 8 | 177.5 | 22.2 | 505.4 | 63.2 | 0.75 |
| 64 | 6 | 64 | 779.5 | **12.2** | 977.0 | **15.3** | 0.50 |
| 16 | 8 | 256 | 2610.7 | **10.2** | 3164.6 | **12.4** | 0.33 |
| 8 | 9 | 512 | 5569.5 | **10.9** | 5811.6 | **11.4** | 0.25 |

**Work falls 4×; the clock rises 34×.** The per-coset constant settles at **~10–15 µs and depends
on neither the height nor the width** — a 16× change in `w` moves it by ~20%, a 64× change in `h`
by ~10%.

### 3c. ⚑⚑ What it is: rayon's cold hand-off.

The only thing inside `coset_dft_oop` with that shape is its `p3_maybe_rayon` dispatches
(`first_half_general_oop`, `second_half_general`, `reverse_matrix_index_bits`) on a matrix that at
`w = 4, h = 64` is 256 elements. Rayon's `par_*` **from a thread that is not itself a pool worker**
takes `Registry::in_worker_cold`: the caller parks on a latch while a worker picks the job up. A
cross-thread round trip, paid per dispatch, per coset, per call — and utterly independent of how
much work the job does.

`§G6e`: the identical workload (the real twelve quotient-chunk LDEs), run from the calling thread
and again inside `rayon::ThreadPool::install`.

| threads | b | from caller | inside pool | **ratio** |
|---:|---:|---:|---:|---:|
| 1 | 3 | 1.113 ms | 0.050 ms | **22.4×** |
| 1 | 6 | 9.632 ms | 0.359 ms | **26.8×** |
| 2 | 6 | 11.330 ms | 0.737 ms | 15.4× |
| 4 | 6 | 21.637 ms | 1.408 ms | 15.4× |
| 8 | 6 | 46.150 ms | 4.302 ms | 10.7× |
| default | 6 | 50.502 ms | 2.807 ms | 18.0× |

**The mechanism is named, and it is not arithmetic, not cache, not the sponge, and not the twiddle
tables. It is a scheduler hand-off charged 12 · 2^b times.** Note also that the caller-thread cost
*rises* with thread count — a busier pool is a more expensive hand-off — which is why the deployed
multi-threaded prover suffers from this more than a single-threaded one, not less.

**What the mechanism says about grouping:** the constant divides by the number of calls and is
blind to width, so batch **every chunk that shares a height**, and the gain is exactly the
call-count ratio. For IR-v2 that is one call per AIR — 12 → 3, predicted 4×, measured 3.6–4.1×.

---

## 4. ⚑ The verifier-semantics verdict: **(a) unchanged, and asserted** `[MEASURED]`

The obligation is real: the chunks are committed as separate matrices because the verifier opens
them separately, so a batch that changed *what those matrices are* would be a wire change and a VK
epoch. It does not, and the reason is algebraic.

Chunk `i` is evaluations of `q_i` over `s_i·H`, LDE'd at shift `t_i = g / s_i`. A coset DFT is a
coefficient scaling followed by a plain DFT — `coset_dft(c, t)[k] = Σ_j c_j t^j k^j`. So scaling
chunk `i`'s **coefficients** by `t_i^j` and then running a single shared LDE at shift `ONE`
reproduces each chunk's output exactly:

- the iDFT is column-independent and shift-free ⇒ batches verbatim;
- the scaling is column-block-local, `Θ(h·w)`, and lands in
  `coset_lde_batch_with_transform`'s transform hook — the point between the iDFT and the coset
  DFTs, which exists for precisely this;
- the forward coset DFTs are column-independent ⇒ batch verbatim;
- row order is unaffected: the map from `(coset_idx, h_idx)` to a storage slot does not depend on
  the shift at all.

Asserted, not argued: **`§G7a` checks `batched == per-chunk` element for element** at
`added_bits ∈ 3..=7` × all three real geometries, with the real `ω^-i` shifts, over deployed
`P3BabyBear`/`Radix2DitParallel`, with a distinct filler per chunk so it cannot pass by accident.

End-to-end corroboration, before/after binaries run back to back: **proof size is byte-identical at
every blowup** (119,522 / 124,198 / 128,872 / 133,544 / 138,220 / 142,894 / 147,566 B for b=2..8),
in-prove self-verify passes, standalone verify unchanged (4.0–4.6 ms).

> **No wire change. No VK rotation. No descriptor re-emit. No flag day.** The twelve matrices the
> MMCS commits, the opening rounds, and the verifier's `recompose_quotient_from_chunks` all see an
> identical object.

The alternative reading of the predecessor's phrase — actually *committing* three wide matrices
instead of twelve narrow ones — **would** be a wire change (opened-values shape, alpha-power
ordering) and buys only the split-back copy. It is not taken and should not be: the copy is ~229 KB
at b=6 against a saving of ~6 ms.

---

## 5. The change, and the counts `[MEASURED]`

`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs` — **DREGG DELTA 3**: `get_quotient_ldes` now
collects its chunks, checks the geometry is uniform (keeping the per-chunk loop as the fallback,
since the entry point is public), and calls the new `p3_fri::batched_chunk_ldes`. That function is
what §G6/§G7 measure — the tests call the deployed code, so instrument and prover cannot diverge.

**Reach is wider than IR-v2.** `Pcs::commit_quotient`'s default in `p3-commit` also routes through
`get_quotient_ldes`, so the **uni-stark** path gets this too — every carrier, light-client and Mina
AIR proved through `plonky3_prover.rs`. `HidingFriPcs` has its own `get_quotient_ldes` (it
randomises chunks against each other) and is untouched; that is a separate, harder batch.

### DFT calls and exact scalar-equivalent ops, from a real prove (`§G1`)

| b | calls before → after | quot-eval ops before | after | saved | DFT total before → after |
|---:|---|---:|---:|---:|---|
| 3 | 12 → 3 | 62,255 | 60,764 | 2.4% | 1,787,402 → 1,785,911 |
| 4 | 12 → 3 | 118,502 | 115,344 | 2.7% | 3,384,681 → 3,381,523 |
| 5 | 12 → 3 | 231,284 | 224,576 | 2.9% | 6,579,671 → 6,572,963 |
| 6 | 12 → 3 | 457,424 | 443,184 | 3.1% | 12,970,515 → 12,956,275 |
| 7 | 12 → 3 | 910,856 | 880,688 | 3.3% | 25,753,931 → 25,723,763 |

**The arithmetic barely moves: 0.11% of the DFT total at b=6.** That is the predecessor's point
landing — the obvious (arithmetic) optimisation was worth nothing here, and the counts say so
exactly. The saving is `n−1` iDFTs plus duplicated twiddle tables, minus the prescale.

The six trace/preprocessed/permutation commits are untouched: widths 236, 386, 2, 72, 12, 4 at the
same counts to the digit.

### Wall clock, before/after binaries, same box, back to back `[MEASURED, UPPER BOUNDS]`

⚠ Load 25–35 throughout; min-of-5 per phase, so every absolute is an upper bound. Both arms paid
the same contention, so ratios are the durable quantity.

`RAYON_NUM_THREADS=1`, `phase_profile_blowup_sweep_fixed_queries`:

| b | LDE quotient-eval before → after | **phase speedup** | prove_batch before → after | whole-prover |
|---:|---|---:|---|---:|
| 3 | 1.552 → 0.405 ms | **3.83×** | 11.36 → 9.80 ms | 1.16× |
| 4 | 2.839 → 0.697 ms | **4.07×** | 18.36 → 15.73 ms | 1.17× |
| 5 | 5.029 → 1.323 ms | **3.80×** | 32.22 → 27.64 ms | 1.17× |
| 6 | 9.312 → 2.545 ms | **3.66×** | 58.71 → 52.15 ms | 1.13× |
| 7 | 17.723 → 4.968 ms | **3.57×** | 115.47 → 100.44 ms | 1.15× |
| 8 | 39.180 → 9.716 ms | **4.03×** | 228.06 → 193.84 ms | 1.18× |

Default (multi-threaded) rayon, same sweep — **the win is larger**, because a busier pool makes
each hand-off dearer:

| b | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| prove_batch before (ms) | 17.19 | 20.80 | 36.18 | 58.03 | 99.19 | 175.92 | 373.24 |
| prove_batch after (ms) | 14.44 | 16.11 | 22.98 | 35.05 | 63.14 | 100.79 | 224.60 |
| **speedup** | 1.19× | 1.29× | **1.57×** | **1.66×** | **1.57×** | **1.75×** | **1.66×** |

Standalone kernel cross-check (`§G7c`, no tracing subscriber, `RAYON_NUM_THREADS=1`): the twelve
narrow calls measure **9.625 ms** at b=6 against the profiler's in-prover **9.312 ms** — 3.4%
apart. ⚑ Two consequences. The standalone kernel *does* reproduce the phase, so **§G5's failure was
rayon dispatch under load, and `RAYON_NUM_THREADS=1` is the fix §G5 asked for**; and the profiler's
own span machinery is *not* inflating the phase, a hypothesis worth testing given that it fires
once per coset.

### The crossover moves `[MEASURED]` — an update to `phase-profile.md` §3

`hash/arith` from the same before/after pair (`RAYON_NUM_THREADS=1`):

| b | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| before | 0.612 | 0.902 | 1.241 | 1.577 | 1.847 | 2.042 | 1.934 |
| **after** | 0.769 | **1.224** | 1.834 | 2.270 | 2.760 | 3.048 | 3.337 |

`phase-profile.md` §3 put the crossover at `b ≈ 2.9`, *just under* the feasibility floor, and called
b=3 "at parity". **It is no longer at parity: at b=3 the prover is hash-bound by 1.22× where it was
arithmetic-bound by 1.11×, and the crossover moves to `b ≈ 2.5`.** `field-op-counts.md` §5's
count-based verdict (hash-bound at every feasible blowup, margin 5.0–7.2×) is unaffected in kind
and strengthened: the arithmetic side lost 3% of its ops and 33% of its time.

---

## 6. ⚑⚑ The bigger finding, and why this section is not a footnote `[MEASURED]`

The mechanism in §3c is not specific to quotient chunks. It is charged to **every**
`p3_maybe_rayon` dispatch made by a prover whose caller is not a rayon worker. `§G6f` asks the
whole-prover version — same workload, same config, deployed `Radix2DitParallel`, the only
difference being whether the calling thread is inside `ThreadPool::install`:

| threads | b | from caller | inside pool | **speedup** |
|---:|---:|---:|---:|---:|
| 1 | 3 | 14.795 ms | 12.641 ms | 1.17× |
| 1 | 6 | 59.905 ms | 48.026 ms | 1.25× |
| 8 | 3 | 21.312 ms | 11.658 ms | **1.83×** |
| 8 | 6 | 60.463 ms | 24.210 ms | **2.50×** |
| default | 6 | 64.739 ms | 29.238 ms | **2.21×** |

**2.2–2.5× on the whole prover, for one `install` at the entry point.**

And the two do not compose. `§G6e` runs both layouts at both call sites (`RAYON_NUM_THREADS=1`):

| b | 12× caller | 3× caller | 12× pool | 3× pool | batch gain (caller) | batch gain (pool) |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 0.925 ms | 0.279 ms | 0.048 ms | 0.031 ms | 3.31× | 1.55× |
| 6 | 8.446 ms | 2.397 ms | 0.344 ms | 0.207 ms | 3.52× | 1.66× |

> ⚑ **Say it plainly: the batching's absolute gain is ~98% a cold-hand-off artifact.** At b=6 it
> saves **6.05 ms** from the caller thread and **0.137 ms** from inside the pool. Both optimisations
> attack the same constant — the batch divides how many times it is paid, the pool makes each one
> cheap — and the pool attacks it ~25× harder.

The batching still earns its place: it is landed, correct, verifier-invisible, worth 1.6× on the
phase even after the pool fix, and it is the only one of the two that needs no decision about
prover entry points. But a reader deciding where to spend the next hour should spend it on §6, not
on more layout work. **The prize was never the layout; the layout was the visible corner of it.**

⚑ **NOT TAKEN by this lane, deliberately.** It touches prover entry points across the tree (the
node's `prove_vm_descriptor2`, `plonky3_prover.rs`, the carrier and light-client provers, the GPU
lanes), and *where* the `install` goes — one at each entry, or one at the process boundary — is a
real design choice about who owns the pool, with its own before/after. `§G6f` is the instrument;
the number is the reason.

---

## 7. What is now reusable

| section | test | what it gives |
|---|---|---|
| §G6a | `quotient_chunk_shifts_are_omega_powers` | chunk LDE shifts checked through the prover's own domain API; the after-shape asserted |
| §G6b | `narrow_call_overhead_mechanism` | the width-independent term in exact counts (and why a count is not a cost) |
| §G6c | `per_coset_constant_wallclock` | the same split on a clock — the twiddle hypothesis, refuted |
| §G6d | `cost_tracks_coset_count_not_work` | fixed output size, sliding split: work falls 4×, clock rises 34× |
| §G6e | `per_coset_constant_is_a_cold_rayon_handoff` | 2×2 of layout × call site; the constant identified |
| §G6f | `whole_prove_inside_the_rayon_pool` | the whole-prover price of the same mechanism |
| §G7a | `batched_chunk_ldes_are_bit_identical` | **the correctness tooth** — element-wise equality at every blowup and geometry |
| §G7b | `batched_chunk_ldes_op_counts` | per-chunk vs batched in exact counts, prescale included |
| §G7c | `batched_chunk_ldes_wallclock` | the phase on a clock, both layouts, labelled upper bounds |

⚠ Run the timing sections with `RAYON_NUM_THREADS=1`. Without it, `§G6e`'s sub-millisecond
in-pool cells on a load-30 box are not reliable (at 8 threads one of them inverts).

**Gates run green after the change:** `fri_extrapolation_row_order` (3), `fri_blowup_global_knob_survey`
(3), `ir2_denotational_differential` (17), `effect_vm_ir2_validate` (1), `cap_open_self_verify` (4),
`state_constraint_air_teeth` (16), `mina_wrap_closing_air_proves` (38), plus 7 blowups × 5 proves ×
self-verify through the phase profiler.
