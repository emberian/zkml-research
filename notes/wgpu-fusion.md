# wgpu fusion measurement — does the prover's MLE table want to BE the FHE intermediate?

*Lane note, written incrementally. 2026-08-13.*

## The thesis under test

> A vFHE prover's multilinear (MLE) evaluation tables ARE the FHE evaluation's intermediates, so a
> fused pipeline pays the memory traffic once instead of twice.

Corollary that makes this worth a day: **if fusion does not win at toy scale on a GPU it will not
win on an FPGA.** An FPGA's whole argument is on-chip dataflow; a thesis that cannot show a delta
where the memory hierarchy is *shallowest* has nothing to deepen.

## Ground truth, verified at source before writing anything

Two of the brief's pointers were right and one was not.

| brief said | reality |
| --- | --- |
| `fhegg-fhe/src/gpu_arena.rs` holds an `Arena` with one device/queue + `ResidentHandle` ciphertexts that stay on device until `download()` | **CONFIRMED.** `upload` :750, `fold_resident` :818, `download` :944 (pre-edit line numbers), and the docblock's residency claim is real — `fold_resident` submits without waiting, `download` is the one `Maintain::Wait`. |
| `Arena` holds a *single* `pipeline: wgpu::ComputePipeline` (~:107) and other wgpu modules own their own `Queue` | **CONFIRMED**, and it is the load-bearing fact. See "what was structurally impossible" below. |
| `minidregg/prover/src/mle_kernels.rs` has `fold_mle_table` | **DOES NOT EXIST.** No `minidregg` directory in the repo; `fold_mle_table` appears nowhere. There was no CPU MLE reference to test against, so I wrote one and — more importantly — got an *independent* oracle instead (below). |

`fhegg-fhe/src/bfv_ntt_gpu.rs` and `shaders/bfv_ntt.wgsl` are real and do carry three-limb
radix-2^16 Montgomery over q < 2^48. Its `mont_mul` is **not reusable** for BabyBear: it is a
64-bit-carried `vec2<u32>` routine for a 48-bit modulus, ~9x the inner work a 31-bit prime needs.
The BabyBear kernel here uses a `mul_hi` + REDC with R = 2^32 instead — the right shape for the
field, not the shared one.

`PREFLIGHT.md` does not exist either; `preflight/` is a crate. Used `AGENTS.md` + `CLAUDE.md`.

## ⚑ What was structurally impossible, not merely unimplemented

`Arena` owned exactly one pipeline (`bfv_fold.wgsl`). Every other wgpu module in the crate
(`bfv_ntt_gpu`, `tfhe_*_wgpu`, `private_book_bfv_wgpu`) stands up its **own** `wgpu::Device` and
`Queue`.

Two wgpu devices cannot share a buffer. So "hand the FHE kernel's resident output to the prover's
kernel" was not a missing feature — it was **unreachable**, and the fusion thesis was untestable in
this codebase by construction. Making `Arena` multi-pipeline is therefore the first real work, not
plumbing.

Now: one `Device`, one `Queue`, one buffer pool, **three** pipelines —
`bfv_fold.wgsl` / `bfv_to_babybear.wgsl` / `mle_fold.wgsl` — and a `ResidentHandle` written by the
first is bound directly by the second.

## What was built

* **`fhegg-fhe/src/shaders/mle_fold.wgsl`** — the sumcheck fold round over BabyBear
  (p = 2013265921), `f'(x) = f(x,0) + r·(f(x,1) − f(x,0))`, folded variable as the HIGH index bit.
* **`fhegg-fhe/src/shaders/bfv_to_babybear.wgsl`** — the fusion seam. One RNS residue (< 2^37) into
  two base-2^30 BabyBear limbs, zero-padded to a power of two.
* **`fhegg-fhe/src/mle_gpu.rs`** — CPU reference, host-side mirror of the bridge encoding, and the
  `Arena` methods (`upload_table` / `bridge_to_babybear` / `mle_fold_rounds` / `download_table`).
* **`fhegg-fhe/src/gpu_arena.rs`** — `Arena` made multi-pipeline.
* **`fhegg-fhe/tests/wgpu_mle_fold.rs`** — 7 correctness teeth.
* **`fhegg-fhe/src/bin/gpu_fusion_bench.rs`** — the measurement.

### Two kernel facts worth keeping

**1. The fold is race-free IN PLACE.** Invocation `i` reads exactly `table[i]` and
`table[i+half]` and writes exactly `table[i]`. Index `i` is read by no *other* invocation
(invocation `i-half` does not exist), and `i+half` is written by nobody. So input and output can be
the same allocation: the table shrinks in place, zero ping-pong buffers, zero copies between
rounds. A whole n-round sumcheck fold is `n` dispatches in **one compute pass, one submission,
against one buffer**. (Dispatch ordering inside a pass is guaranteed by WebGPU and by Metal's
default `MTLDispatchTypeSerial`.)

**2. The table never needs a representation pass.** The table stays *canonical*; only the round
challenge is uploaded in Montgomery form (`r·2^32 mod p`). `mont_mul(r_mont, d) = r·d` exactly, so
there is no convert-in / convert-out sweep over the data — which would have been two extra full
passes over memory per fold, in a measurement whose entire subject is passes over memory.

### The bridge encoding, stated honestly

A deployed `FOLD_MODULI` residue is < 2^37 and does **not** fit one BabyBear element. `x mod p`
would be non-injective — two distinct residues sharing a committed lane, which is exactly the
pigeonhole wound this repo already carries elsewhere. So: `limb0 = x mod 2^30`, `limb1 = x >> 30`,
both < p, injective on [0, 2^37), asserted by round-tripping every lane in the test.

This is **a** faithful encoding, not **the** encoding a specific vFHE relation would fix — the
relation chooses the limb base. What is fixed and what the measurement depends on is the *shape*:
2 BabyBear elements per RNS lane, i.e. **the table is the same byte count as the ciphertext**.

## Correctness

Three independent checks, because each is blind to the others' failure.

1. **Arithmetic** — the WGSL Montgomery multiply on hostile operands (0, 1, 2, p−1, p−2, 2^15,
   2^16, 2^27±, 2^30−1, 2^31 mod p), through the fold with `f0 = 0` so a round *is* a multiply.
2. **Semantics** — one GPU round equals **Plonky3's own `Poly::fix_prefix_var`** at the workspace's
   pinned rev (82cfad73), which is literally `r*(a1-a0)+a0` over the split-at-half table and is what
   a `VariableOrder::Prefix` sumcheck folds. This is the check that matters: my CPU reference and my
   kernel could share a wrong idea of "the fold" and agree with each other forever. An oracle
   written by someone else settles it.
3. **The seam** — a real `fold_resident` output bridged on-device equals the host encoding of the
   same downloaded ciphertext, bit for bit, and fused/unfused fold to the same field element. If
   those disagreed, the benchmark would be timing two different computations and its delta would
   mean nothing.

```
running 7 tests
test montgomery_constants_do_not_drift ... ok
test one_arena_serves_three_pipelines_without_a_host_round_trip ... ok
test device_bridge_equals_host_encoding_of_the_same_fold ... ok
test fused_and_unfused_pipelines_agree ... ok
test one_round_matches_plonky3_and_cpu_reference ... ok
test montgomery_multiply_is_exact_on_hostile_operands ... ok
test full_fold_to_a_constant_matches_cpu ... ok
test result: ok. 7 passed; 0 failed
```

### The gate can go red

A green suite proves nothing about the suite. Two constructive mutations of the kernel, each
rebuilt and rerun:

| mutation | result |
| --- | --- |
| `submod(f1, f0)` → `submod(f0, f1)` (fold orientation) | **4 of 7 RED**, including the Plonky3 oracle |
| `carry = select(0u,1u,lo != 0u)` → `carry = 0u` (Montgomery REDC carry) | **4 of 7 RED** |

Kernel restored, suite green again.

---
# The measurement

`cargo run -p fhegg-fhe --release --bin gpu_fusion_bench`

**Host:** Apple M2 Max, 38 GPU cores, 96 GB **unified** memory. wgpu 24 → Metal.
`max_storage_buffer_binding_size = 4294967295`, `max_buffer_size = 62620631040`.

**No wgpu/Metal limit was hit.** Workgroup size 256 (Metal allows 1024); at most 3 buffer bindings
per group; largest single allocation 16 MB against a 58 GB ceiling. Nothing here is a workaround.

Both paths run identical kernels over identical data and their equality is **asserted every case**,
against each other *and* against the pure-CPU fold — so the delta is the round trip and nothing
else. Median of 11 reps, fused and unfused **interleaved rep by rep**.

## ⚠ First: the box was contended, so read ratios, not microseconds

Three runs, taken at 1-minute load averages of roughly 40, 79 and 70 on a 12-core laptop shared with
several other lanes' builds. Absolute times move **30–100%** between runs. The interleaving means
contention hits both arms of each comparison together, so *ratios* and *shapes* survive it and
*microseconds do not.* Every run is reported; none is discarded.

### Single hand-off — one BFV fold consumed by one MLE fold

```
run 1 (load ~40)
#  degree   ct_bytes  table_len   fused_us unfused_us     dl_us  encup_us cpu_mle_us speedup
      256      12288       4096     1485.0     2732.4    1277.2      35.8       10.6   1.84x
     1024      49152      16384     1505.2     2824.5    1284.3      62.6       38.1   1.88x
     4096     196608      65536     1479.5     2881.2    1281.0     152.3      141.2   1.95x
    16384     786432     262144     1527.2     3289.5    1330.2     545.5      562.2   2.15x
    65536    3145728    1048576     1661.3     5280.8    1676.9    2181.4     2274.7   3.18x
   262144   12582912    4194304     3062.1    12825.9    2823.1    9744.4    11099.8   4.19x

run 2 (load ~79)                                                    run 3 (load ~70)
      256     1981.0     3317.8 ... 1.67x                                 2146.2  4681.4 ... 2.18x
     1024     2155.3     3695.9 ... 1.71x                                 2333.3  4209.7 ... 1.80x
     4096     2139.9     3591.5 ... 1.68x                                 3408.7  4435.8 ... 1.30x
    16384     2145.2     4562.6 ... 2.13x                                 2256.5  4308.5 ... 1.91x
    65536     2087.1     6960.2 ... 3.33x                                 3596.9  8701.1 ... 2.42x
   262144     4386.3    21573.8 ... 4.92x                                 6233.9 23666.0 ... 3.80x
```

`dl_us` = ciphertext down to the host (staging copy + map + wait + `LeanCiphertext` reassembly).
`encup_us` = host limb encoding + the table's upload. `cpu_mle_us` = the whole fold on the CPU.

Fusion wins in all 18 cells, **1.30x–4.92x**, and the win grows with table size in all three runs.

## ⚑ Then: the fixed cost, which is most of the small-size story

```
#   idle wait_idle():                            0.1–0.2 us
#   minimal pipeline (2 elems, 1 round):     1394 / 1768 / 2482 us   <- per-synchronization floor
```

**A device synchronization costs ~1.3–2.5 ms on this stack regardless of how many bytes cross.**
(`dl_us` at the smallest size — 1277 / 1374 / 1446 µs — is essentially one bare sync.) That
dominates every row below ~2^20 elements. Taking the raw `speedup` column at face value there would
credit *bandwidth* for what is mostly *one fewer stall*.

Subtract it — fused pays one sync, unfused pays two:

| table | run 1 | run 2 | run 3 |
| ---: | ---: | ---: | ---: |
| 2^12 | 0.86x | 0.94x | 2.56x |
| 2^16 | 1.63x | 1.10x | 0.53x |
| 2^18 | 2.91x | 2.44x | 2.20x |
| 2^20 | **7.10x** | **5.91x** | **2.70x** |
| 2^22 | **5.75x** | **6.25x** | **4.34x** |

⚠ The 2^12–2^16 entries are differences of two large noisy numbers (subtracting ~2.8 ms from a
~3 ms measurement) and are **not reliable** — that is why they disagree in sign across runs. The
2^20 and 2^22 entries subtract the same 2.8 ms from a 5–24 ms measurement and are reliable.

**Traffic alone, no synchronization advantage at all: 2.7x–7.1x at 2^20–2^22, in all three runs.**
At and below 2^16 the sync-corrected result is consistent with *no win*, which is the expected
answer — a bridge dispatch is a whole extra kernel and there are not enough bytes to pay for it.

## The robust result: the win compounds, and the shape needs no subtraction

One hand-off is a constant. A real vFHE pipeline absorbs a *batch* of FHE outputs. Fused, K stages
are K sets of dispatches and **one** synchronization; unfused, K host round trips and **K+1**.

Per-stage cost at degree 4096 (65536-element tables), all three runs:

| K | fused/stage (µs) | unfused/stage (µs) |
| ---: | --- | --- |
| 1 | 1569 / 2589 / 3523 | 2937 / 4830 / 4533 |
| 2 | 882 / 1485 / 2331 | 2843 / 3028 / 3941 |
| 4 | 559 / 856 / 990 | 2238 / 2483 / 2825 |
| 8 | 402 / 855 / 727 | 1924 / 3118 / 2893 |
| 16 | **328 / 673 / 668** | 1835 / 2399 / 2614 |
| **fall, K=1→16** | **4.8x / 3.8x / 5.3x** | **1.6x / 2.0x / 1.7x** |

**This is the finding.** Fused per-stage cost falls 3.8x–5.3x across the sweep and is *still
falling* at K=16; unfused per-stage falls under 2x and *plateaus*, because every unfused stage
carries its own irreducible synchronization and its own host encode. The asymmetry reproduces in
all three runs, at three different contention levels, and it requires subtracting nothing. End-to-end
K=16 speedups were 5.60x / 3.56x / 3.91x.

## Is the WGSL fold worth anything on its own?

Against the scalar CPU reference at matched sizes, the GPU fold's marginal cost crosses over around
**2^17–2^18 elements** and reaches ~6x by 2^22. Below that the CPU wins outright — at 2^12 it is
10 µs against a >1 ms stall. ⚠ The CPU reference is single-threaded and scalar; a rayon + NEON fold
would push the crossover up by roughly the core count, so this is against a soft baseline and is
**not** a GPU-vs-CPU result. It is here only to confirm the fused pipeline's GPU leg does real work.

# Verdict on the fusion thesis at toy scale

**The thesis holds, and for the reason it claims — above a size floor, with one large caveat about
the silicon and one about the abstraction.**

1. **It wins, in every cell measured.** 1.30x–4.92x end to end across 18 size/run combinations.
2. **It wins for the stated reason at scale.** With the synchronization advantage discounted
   entirely, fusion still wins **2.7x–7.1x** at 2^20–2^22 purely on memory traffic. The dominant
   unfused term there is `encup_us` — host encode + re-upload — which *is* "paying the traffic
   twice". At 2^22 that single term (9.7–16.1 ms) exceeds the **entire** fused pipeline (3.1–6.2 ms).
3. **It compounds, and that is the structural result.** Fused per-stage cost falls 3.8x–5.3x over
   K=1→16 and is still falling; unfused plateaus under 2x. Reproduced in all three runs.
4. **It does NOT win below ~2^16 elements.** With the sync removed, small-table fusion is
   neutral-to-negative. A pipeline of small tensors gains nothing and pays for a bridge dispatch.
   Fusion is a claim about *large resident intermediates*, and it should be stated that way.
5. **⚠ Unified memory makes every number a LOWER BOUND.** The M2 Max reports `IntegratedGpu`; a
   "download" here is a copy inside one physical DRAM with no bus crossing. A discrete GPU pays a
   real transfer each way, and an FPGA spilling an intermediate to off-chip DRAM pays worse. The
   thesis's target hardware is where this understates the most.
6. **⚠ The ~1.3–2.5 ms sync floor is wgpu's, not physics.** Fresh staging buffer, `map_async`,
   `Maintain::Wait` — a tuned Metal/CUDA path with persistent staging and event waits would be far
   below it. **Do not carry the raw `speedup` column into an FPGA argument.** Carry the traffic-only
   2.7x–7.1x and the per-stage curve, both of which survive deleting the sync advantage.

## So: does it survive to an FPGA?

The brief's test was *"if fusion does not win at toy scale on a GPU it will not win on an FPGA."*
It wins. Two of the three mechanisms transfer cleanly — **avoided off-chip traffic** (worse on an
FPGA, so better for fusion) and **amortized handoff latency** (an FPGA↔host DMA has its own fixed
cost). The third, the wgpu synchronization floor, does **not** transfer and must be discounted, which
this measurement does explicitly rather than by assertion.

The measurement does **not** license "fusion wins on an FPGA". It licenses: *the mechanism the
thesis names is real and dominant at 2^20+, it compounds with pipeline depth, and it is absent below
2^16.* Those are the conditions to design against.

## What this does NOT show

* **Nothing is committed and no round polynomial is evaluated.** This is the fold, not a prover. A
  real sumcheck also evaluates `h(0)`/`h(inf)` per round and eventually feeds a PCS — more arithmetic
  per byte, which *lowers* the crossover (good for fusion) but is unmeasured here.
* **The fold is over the base field.** A real sumcheck folds over `EF4` after round 1: ~9x the
  arithmetic, 4x the bytes per lane. Both scale together so the traffic ratio should hold, but the
  crossover point would move and is not measured.
* **The bridge encoding is not a relation.** It is an injective 2-limb split chosen for the right
  *byte shape*. A real vFHE relation fixes the limb base, changing table sizes but not the structure.
* **`fold_resident` is outside the comparison** — both paths start from the same handle. What is
  measured is the hand-off, which is the thesis.
* **The box was contended.** Absolute microseconds here should not be quoted.

## Cost of the claim, in this repo

The BFV fold-add and the MLE fold now share a device, a queue and a buffer pool. That enabling change
is small (one struct, three pipelines, a `build_pipeline` helper). The debt it makes **visible** is
larger: `bfv_ntt_gpu`, `tfhe_*_wgpu` and `private_book_bfv_wgpu` each still stand up their own
`wgpu::Device`, so none of them can hand a resident buffer to anything. Every one is a site where the
measured 2.7x–7.1x is unavailable *by construction*. If this result is to be acted on, that is the
next work: one arena, all kernels.

## Cross-reference

A sibling lane is pricing the *CPU* fold from the other direction —
`sumcheck-toy/tests/folding_price.rs`, nanoseconds per value per layer through `p3-sumcheck` for the
committed-vs-virtualized exchange rate. Complementary, not duplicative: that measures a real
degree-2 product sumcheck over `EF4` including round-message evaluation; this measures a bare
base-field fold and the *hand-off around it*. For a rough bridge, the `cpu_mle_us` column here works
out to ~2.6 ns per fold operation at 2^22 and the fused GPU leg to ~0.4 ns — but the two are folding
different objects and the numbers should not be equated without saying so.

Landed: `c67b17b7c` — `gpu: make Arena multi-pipeline and measure the FHE/prover fusion thesis`.
