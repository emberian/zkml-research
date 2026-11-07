# The Tower256 leaf prover on one GPU, end to end: schedule, prediction, measurement

2026-11-07, lane w2-tower (initiative 17). This follows ember's direction: hardware time runs the real
software, scheduled to fill the machine, and no more rate probes.

- Code: minidregg `lane/accel-tower256-gpu`: `prover/cuda/tower256_fri.cu` and
  `prover/cuda/tower256_gpu.py` (`prove_steps`, `prove_batches`).
- Model: `tower256_schedule_model.py` (`python3 -I`), which prints the tables in §4.
- Script: `runbook/tower256.sh --e2e`.
- Run: `runs/accel-tower-e2e-01`.

## 1. Measured inputs (nothing below comes from a datasheet unless marked [A])

| quantity | T4 | H100 | source |
|---|---:|---:|---|
| Tower256 multiply, log/exp table kernel | 2.9e8-5.4e8/s (session-to-session) | 1.2e9-2.2e9/s [A: T4 x 4.11, INT32 SIMT lanes x clock] | TOWER256.md §4, §8; `accel-towermul-vs-table-01` (1.85 ns) |
| Keccak-f[1600], batched Merkle build | 4.35e8-6.9e8/s | 1.8e9-2.8e9/s [A: same scaling] | `accel-tower-dryrun-04`, `accel-tower-tune-03` |
| device copy (read + write bytes/s) | 234 GB/s | 3.03 TB/s | `accel-mma-t4-runbook-03`; `paid-h100-mma-03` |
| kernel launch from the Python host | ~12 µs [A: cupy RawKernel] | ~8 µs [A] | |
| host cSHAKE (pycryptodome) | ~6 µs/KB [A: 3 µs/KB on a loaded M2] | ~3 µs/KB [A] | |

## 2. Per-stage work (per proof; production shape lb 2, m = ell - 4, q 148)

At ell 20: n = 2^20, L = 2^18 input coefficients, 18 FFT depths, 16 folds.

| stage | work | bytes moved | binding resource | fused / scheduled as |
|---|---|---:|---|---|
| upload | the word, 32 B x L | 8.4 MB over PCIe | PCIe (~6 GB/s pageable) | one copy per batch |
| encode (Gao-Mateer) | 14.7M multiplies (per depth: L scale and n/2 butterflies) | 3.9 GB; 2.0 GB of it inside the multiply kernels | **the table multiply** (shared-memory log/exp lookups) | per depth: scale, then log2(bsz) - 1 Taylor XOR passes, then deinterleave; then n/2 butterflies per depth. The depth parameters are statement setup (cached) |
| Merkle | 4.19M Keccak-f (one per leaf and per node, every tree) | 0.34 GB | INT32 ALU (Keccak) | leaves, then one launch per level; stored levels serve the openings |
| folds | 1.05M multiplies | 0.13 GB | the table multiply | one kernel per round: the shared span S_j (setup) plus a per-proof d_b = alpha_b / pivot |
| final | per proof, Gauss-Jordan on at most 16 points, 16 evaluations | ~0 | latency | one thread per proof, batched |
| seeds | about 45 + 2 x 148 Keccak-f | ~0 | latency | `cshake_absorb` (prefix, one thread per proof), then `query_seeds` (B x q threads) |
| openings | about 45k digests encoded base 255 | ~1 MB out | latency | `open_lengths`, a cupy prefix sum, then `open_write`: the receipt's opening bytes, written in place |
| host | m challenges (~5 KB of cSHAKE each), receipt header framing | | the host CPU | the only per-round host work; it overlaps the device under two streams |

**The shape of the cost.**
- The encode is about 80% of device work, and it is bound by the multiply, not by bytes: its
  2.0 GB of multiply-kernel traffic takes 8.4 ms at 234 GB/s, against 27-51 ms of multiplies.
- The Taylor and deinterleave passes are pure memory: 1.9 GB, 8.3 ms on T4.
- The Merkle is a fifth of the encode.
- The host work per proof is about 2 ms. It must not sit on the critical path at ell 18, where a
  T4 proof is about 12-19 ms.

## 3. What overlaps, and what the batch is for

- **Batch over leaves.** B leaves of one shape share the domain, so each kernel launch covers all B
  words: B x 2^ell threads per FFT layer and B trees per Merkle level. Batching amortizes the
  launch chain over B. Per batch that is about 600-800 launches (~8-10 ms on T4), or 0.1-0.5 ms per
  proof at the chosen B. It also fills the machine at small ell. The domain-constant setup (FFT
  depth parameters, round maps, fold spans) is built once per shape.
- **Two streams.** The batch splits into two halves, each on its own CUDA stream; the host drives
  them in turn (`prove_batches`). While one half waits on the host (challenge hashing, receipt
  framing, reading roots back), the other half's kernels run, so the host work and every per-round
  sync come off the critical path.
- **Why not hash and encode concurrently.** Within one proof they cannot overlap: the round-0
  Merkle needs the encoded word, and every fold needs the previous root. Across proofs they can,
  and the two streams provide it.
  - The gain is bounded by the smaller of the two: at ell 20 the Merkle is 6-10 ms against 35-59
    ms of encode, so overlap buys at most about 15%.
  - Both are INT32/shared-memory bound, so they compete for the same SM resources and the real
    gain is smaller.
- **Why not one persistent kernel.** It would also remove the launch chain. The launch chain is
  already under 1% of the time at these batch sizes, and a persistent kernel would need grid-wide
  barriers between FFT layers (cooperative launch) for no measurable gain.
- **Batch sizes, by memory.** About 230 MB per proof at ell 20 (words, stored trees, encode
  scratch).
  - T4 (15 GB): ell 18 x 64, ell 20 x 16, ell 22 x 4, each about 4 GB.
  - H100 (80 GB): 4x those, 18 x 256, 20 x 64, 22 x 16, each about 15 GB, leaving room for two
    batches in flight.

## 4. Prediction (`tower256_schedule_model.py`; the range is the measured multiply and Keccak range)

Per proof, ms, amortized over the batch. "Device bound" is encode + Merkle + folds + upload; "one
stream" adds launches and host time.

| target | ell | batch | encode | Merkle | folds | device bound | one stream |
|---|---:|---:|---:|---:|---:|---:|---:|
| T4 | 18 | 64 | 7.7-13.0 | 1.5-2.4 | 0.5-0.9 | **10.1-16.6** | 12.2-18.7 |
| T4 | 20 | 16 | 35.5-58.9 | 6.1-9.6 | 1.9-3.6 | **44.9-73.6** | 47.4-76.1 |
| T4 | 22 | 4 | 161-265 | 24-39 | 8-15 | **198-323** | 203-328 |
| H100 [A] | 18 | 256 | 1.6-2.9 | 0.4-0.6 | 0.1-0.2 | **2.2-3.8** | 3.2-4.8 |
| H100 [A] | 20 | 64 | 7.3-13.0 | 1.5-2.3 | 0.5-0.9 | **9.6-16.6** | 10.8-17.7 |
| H100 [A] | 22 | 16 | 32-58 | 5.9-9.4 | 1.9-3.5 | **42-72** | 43-74 |

Against the CPU prover:
- One proof at ell 20 takes 1,782 ms on the Kaggle Xeon with 4 threads (`accel-tower-dryrun-04`).
- The predicted T4 per-proof cost at ell 20 is 24-38x below that.
- The fair comparison is the CPU's own best batch schedule, one proof per core. The run measures
  that on the same box.

## 5. The fused 1-bit tensor multiply inside the encode: not on T4

- **On sm_75 it cannot pay.** The T4 has only `.b1 xor.popc`. AND-parity then needs
  `popc(a) + popc(b) - popc(a^b)` mod 4, so each output bit needs operand popcounts and a second
  count in the epilogue.
- **Unfused, the route measured 11.6x slower than the table** (ROTATION §2(b)). The fused
  prediction, 0.40 ns per multiply (4.6x the table), applies only where a twiddle is shared by
  at least 64 butterflies.
- **Batching does help the eligibility.** It makes every twiddle shared B-fold, so at B >= 64
  every FFT layer would qualify.
- **The ceiling is low.** ROTATION's own end-to-end prediction for T4 at ell 20 is 43 → 19 ms
  (2.3x). That is a prediction for a kernel nobody has built, and the folds stay on the table:
  their factors are per element, with no fixed operand.
- **Decision:** the end-to-end run uses the table multiply. The fused kernel belongs on Hopper,
  where `and.popc` gives parity directly and the accumulators live in registers for the epilogue.
  If the H100 table run below holds, that kernel is the next lever, and the plan in §7 states where
  it would go.

## 6. Measured (`accel-tower-e2e-01`, Kaggle T4, one run, 564 s, rc 0)

**How the run was built.** It used the paid-box bundle, built the way the box builds it:
- `tower256-bundle.sh` from minidregg b73bb1dda, with the pruned lock;
- `tower256.sh --shrink --e2e`, online: `accel_venv` with pinned pip, rustup 1.89.0, and
  `cargo build --locked` of the bundle's prover;
- the CPU expectations computed on the same box.

**Byte identity: every receipt is byte-identical** to the CPU prover's.
- That covers 64 + 16 + 4 batched proofs at ell 18 / 20 / 22, each in four runs: synchronized
  phases, single-proof latency, one stream, two streams.
- Also identical: the five Lean vectors (through the same batch path at B = 1), the request
  bytes, and the conformance kernel at ell 8 and 10 on the box.
- `all_bit_exact` is true.

**Per proof, amortized over the batch (ms).** The device bound "at the session's rates" uses the
multiply rate inferred from the encode phase: 3.2e8/s at all three ells, 3.0-3.2e8 individually,
inside the measured 2.9-5.4e8 range. Keccak is 5.9e8/s, from the Merkle phase.

| ell | batch | predicted device bound (range, §4) | at the session's rates | measured, 1 stream | measured, 2 streams | measured / bound at session rates | single proof (latency) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 18 | 64 | 10.1-16.6 | 14.9 | 18.4 | **16.9** | 1.13 | 23.1 |
| 20 | 16 | 44.9-73.6 | 65.9 | 74.1 | **67.0** | 1.02 | 83.8 |
| 22 | 4 | 198-323 | 290.7 | 322.4 | **303.5** | 1.04 | 341.1 |

**Phases at ell 20** (synchronized per stage, ms per proof): upload 8.2, encode 53.6, Merkle 7.1,
folds 2.7, final 0.08, seeds 0.05, openings 0.7, host 1.7, readback 0.4.
- The encode is 80% of the device time, as predicted.
- The openings and seeds are now negligible (the Python host spent 110-220 ms per proof on the
  openings before).
- **The model missed the upload:** 8.2 ms per proof against 1.4. The upload is the host
  assembling the padded word in numpy plus a pageable copy, about 1 GB/s on the Kaggle host.
  Two streams hide most of it and the host time (74.1 → 67.0 ms).
- At ell 18 the synchronized row shows openings at 6.4 ms per proof. That is cupy compiling its
  prefix-sum kernels on first use (the first e2e row of the run); the warm rows have no such
  term.

**Against the CPU prover** (Kaggle Xeon @ 2.0 GHz, 4 vCPU). This session's CPU ran about 1.6x
slower than in `accel-tower-dryrun-04`: one ell-20 proof took 5,670 ms on 1 thread and 2,595 ms
on 4.

| ell | GPU per proof (2 streams) | CPU per proof, best batch schedule (4 cores, one proof each), same box | GPU speedup on the same box | against the 1,782 ms CPU figure (dryrun-04, ell 20, 4 threads) |
|---:|---:|---:|---:|---:|
| 18 | 16.9 ms | 603 ms | **35.6x** | |
| 20 | 67.0 ms | 2,371 ms | **35.4x** | **26.6x** |
| 22 | 303.5 ms | 9,980 ms | **32.9x** | |

**What the measurement settles.**
- The model holds. Per proof, the device time is the encode's multiply count over the table
  multiply's rate, plus the Taylor/deinterleave bytes over copy bandwidth, plus Keccak count
  over Keccak rate. It agrees within 1.02-1.13x once the session's rate is known.
- The remaining spread is the T4's own session-to-session multiply rate.
- The hashing is 11% of the device time. The prover is multiply-bound on SIMT, as ROTATION §2(c)
  says.

## 7. The one-hour H100 plan (the real prover; the parent decides on any rental)

- **Box:** 1x H100 SXM 80 GB, at least 32 host cores (so the same-box CPU comparison means
  something, and the host is never the bottleneck), at least 128 GB RAM, Ubuntu 22.04/24.04,
  CUDA driver 12.4+, internet.
- **Run:** on the Mac, `runbook/tower256-bundle.sh <minidregg checkout at b73bb1dda or later on
  lane/accel-tower256-gpu>`. On the box: `tar xzf tower256-bundle.tar.gz`, then
  `bash tower256/tower256.sh --e2e` (full mode: ell 18 x 256, 20 x 64, 22 x 16 leaves, about
  15 GB of device memory per batch; one and two streams; CPU one proof per core).
  `tower256.sh` already has this mode; it is the code that ran on the T4 with bigger batches and
  `--sku H100`.
- **Expected wall:**
  - about 4 min of setup (venv, pip, rustup, cargo);
  - about 10 min of CPU expectations: 1 thread over every batch, about 3 min per ell on a modern
    core, plus all cores;
  - about 2 min on the GPU.
  - About 16-20 min in all. The script's limits are 3,000 s wall and 600 s without output.
- **Cost:** H100 SXM on demand about $2-3/h [A: public on-demand prices, not checked this
  session], so under $1.50.
- **Prediction to accept against** (§4, H100 rates scaled from the T4 [A]): per proof at ell 20,
  device bound 9.6-16.6 ms. Host work (the upload as measured on T4, about 4 ms on a 2x faster
  host, plus 1-2 ms of challenges and framing) overlaps under two streams.
  - **Acceptance:** two-stream per proof within 1.5x of the device bound at the box's own rates,
    every receipt byte-identical.
  - ell 18: 2.2-3.8 ms. ell 22: 42-72 ms.
- **What each result decides:**
  - **H100 per proof against the same box's all-cores CPU.** On T4 the GPU leads 4 slow cores
    33-36x. A 32-64 core server is roughly 8-16x those 4 cores [A], and the H100 is predicted
    about 4-5x the T4, so the expected H100 lead over its own host is about 10-20x. That number
    decides whether the leaf prover is carried on GPUs at all.
  - **Whether H100 is host-bound.** If the two-stream per proof exceeds the device bound by more
    than the host's measured upload plus host time, then pinned uploads and a Rust host are the
    next work, not kernels.
  - **The encode share on Hopper.** If it stays near 80%, then the fused 1-bit multiply (§5; on
    Hopper `and.popc` gives the parity directly, and the epilogue repack stays in registers) is
    the one kernel worth building. ROTATION predicts 3.2x per proof for it. If the share has
    dropped (Hopper's multiply rate scaling better than INT32 lanes), the table stays.
