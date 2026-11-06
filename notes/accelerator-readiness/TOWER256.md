# Workload 2: the Tower256 additive-FRI prover (minidregg work 9104) on CPU and GPU

2026-11-06, lane w2-tower (initiative 17). Code: minidregg branch `lane/accel-tower256-gpu`
(367f9370d, from `lane/tower256-prover-exe` 6fd5d4f63). Runs: `runs/accel-tower-*`. Script:
`runbook/tower256.sh` (+ `common.sh`, `tower256-bundle.sh`; Kaggle entry `runbook/tower256_kaggle_entry.py`, run with the bundle plus a prebuilt `bin/tower256_fri_fast_bench`).

**Verdict.**
- At ell 14-16 a fixed CPU prover takes 55 ms and 210 ms per proof on one 2.0 GHz Kaggle Xeon
  core. Ell 14 is a 4 KiB record.
- On a T4, encode plus commit at ell 14 costs 0.82 ms per word when words are batched, about 57
  such cores.
- A single proof does not need a GPU. A GPU pays only for batches: many leaves or columns of one
  shape, or ell 20-22.
- This workload does not need a paid box to decide anything now. The T4 has measured both
  primitives, and the next lever (a bit-sliced multiply) can be measured on the T4 too.
- If ember wants H100 numbers anyway: one H100 SXM for about 10 minutes, under $1 [A] (§6).

## 1. What was built

1. **A fast CPU prover**, `prover/src/tower256_fri_fast.rs` (a new file, one `mod` line in
   lib.rs, proposed as `patches/minidregg-tower256-fri-fast-mod.patch`). Its receipts match the
   conformance kernel byte for byte. It replaces the kernel's three super-linear loops:
   - **Encode: Gao-Mateer additive FFT** of the monomial word on `offset + span(beta)`, for an
     arbitrary basis. Each depth normalizes beta_0 to one (`h(z) = f(beta_0 z)`), Taylor-expands
     at `z^2 + z` with XOR only, and recurses on `span(gamma_i^2 + gamma_i)` with offset
     `t^2 + t`. Every subproblem at one depth shares the basis and the offset, so a depth costs
     one inversion, `L` scalings and `n/2` butterflies.
     - The recursion stops once the polynomial is constant (depth `log2 L = ell - lb`). The
       rate-1/4 cosets therefore cost nothing extra: `(ell-lb) n/2 + (ell-lb) L` multiplies
       (14.2M at ell 20), against `n L` (2.7e11) for Horner.
     - Why not Lin-Chung-Han: it evaluates in the novel polynomial basis. The input here is
       monomial, and for an arbitrary (non-Cantor) basis the monomial-to-novel conversion costs
       about `n log^2 n`. Gao-Mateer takes monomial input directly; the price is one scaling
       pass per depth.
     - A dependent basis (a zero normalizer) falls back to Horner, so even degenerate requests
       give the conformance kernel's output.
   - **Merkle:** every level of every committed tree is stored once. An opening reads its
     siblings `L_{d+1}[(k mod 2^(d+1)) xor 2^d]`.
   - **Domains:** the round map `y -> y^2 + p y` is GF(2)-linear, so a domain is the XOR span of
     `ell+1` images. The fold factor `(dom_k + alpha)/p` is the span of the images, scaled once.
     That leaves one multiply per folded point.
   - **Arithmetic:** a polynomial basis `GF(2)[x]/p(x)`, reached by the field isomorphism
     `y(x) -> y(omega)`.
     - `omega` is a fixed SplitMix element of degree 256, and `p` is its minimal polynomial,
       computed at first use from the reference multiplication.
     - Products are PMULL or PCLMULQDQ with Barrett reduction: 36 64-bit carry-less multiplies,
       22.9 ns on the Kaggle Xeon, against 41,194 ns for the reference recursion.
     - Every byte that leaves the prover is converted back to Fan-Paar coordinates.
   - **Hashes:** raw Keccak-f[1600] from the cSHAKE customization midstate. It is half the cost
     of a `sha3`-crate call, and is checked against that crate.
2. **CUDA** (`prover/cuda/tower256_fri.cu`, 28 kernels) and **a cupy host**
   (`prover/cuda/tower256_gpu.py`). The host owns the transcript, the codecs and the receipt;
   the device owns the encode, the Merkle trees, the folds and the final interpolation.
   - Leaf and node hashing: one Keccak-f each, with 64-bit lanes rotated by two
     `__funnelshift_l`.
   - Tower256 multiply in Fan-Paar coordinates: Karatsuba down to GF(2^8), with log/exp tables
     in shared memory built on the device from the bit-level recursion.
   - Inversion by the tower norm `N(a0 + a1 y) = a0^2 + a0 a1 g + a1^2`.
   - The FFT pieces (scale, Taylor step, deinterleave, butterfly), all batch-capable: many words
     side by side in one launch set.
   - The same `.cu` also builds as host C++ (`-DHOST_EMU`). That emulation build tested the
     whole host on the Mac before any T4 time was spent, and the Kaggle runs then passed first
     time.

## 2. Bit-exact checks (all pass; none compares a thing with itself)

| check | against | where |
|---|---|---|
| fast CPU receipts, the 5 Lean vectors (1 and 4 threads) | Lean `proveRequest` bytes | `tests/tower256_fri_fast_conformance.rs` (Mac) |
| 30 random requests: random and unit bases, offsets, m in 0..ell, q 0..5, words longer than the domain, empty words, a dependent basis (zero pivot; Horner fallback) | conformance kernel `tower256_fri_prove.rs` | same |
| production shape (lb 2, m = ell-4, q 148) at ell 8, 10 | conformance kernel (ell 10: 12.2 s for the reference, 5.8 ms for the fast prover) | same, and inside every T4 run on the Kaggle CPU |
| fast prover on aarch64 (PMULL) and x86_64 (PCLMUL) | each other: identical receipt SHA3 at every ell | Mac, hbox, Kaggle |
| additive FFT, k 0..10, 7 lengths each | Horner at every point | conformance test |
| polynomial-basis isomorphism; raw Keccak hashers | `Tower256::mul`; the `sha3` crate | unit tests |
| T4 Keccak leaves and nodes (1,024 sampled) | pycryptodome `cSHAKE256` | every run |
| T4 Tower256 products (1,024) and inverses (16) | `binary_tower_256.rs` (`mul_check.bin`) | every run |
| T4-assisted receipts, the 5 Lean vectors | Lean bytes | every run |
| T4-assisted receipts and all roots, ell 10..20 (request regenerated in Python from the Rust SplitMix stream; request SHA3 checked too) | fast CPU prover on the same box | every run |
| batched words (64 at ell 14): roots of words 0, 32, 63 | the single-word path | every run |

## 3. CPU numbers (Kaggle Xeon @ 2.0 GHz, 4 vCPU, quiet; `accel-tower-dryrun-04` `rust_cpu`)

Production shape: lb 2, m = ell - 4, q 148, final degree 4. Times in ms, 1 thread / 4 threads.

| ell | total | encode | Merkle | folds | openings | Keccak-f | encode mults | receipt |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 14 | 54.7 / 55.8 | 7.6 | 41.0 | 0.5 | 4.8 | 65,493 | 147k | 515 KB |
| 16 | 209 / 155 | 35 | 164 | 2.1 | 6.4 | 262,099 | 688k | 677 KB |
| 18 | 841 / 475 | 158 | 664 | 9.2 | 8.1 | 1.05M | 3.1M | 859 KB |
| 20 | 3,390 / 1,782 | 724 | 2,616 | 38 | 10.2 | 4.19M | 14.2M | 1.06 MB |

- **The prover is Merkle-bound, as the counts doc says.** That is about 78% of the time, at
  536 ns per Keccak-f on this core. On the loaded M2 Max (load ~120) one core does 280-300 ns,
  so a modern core is about 2x this one.
- **4 threads help only from ell 16 up.** At ell 14 the per-call scoped threads cost more than
  they save. For many leaves, parallelize across words (embarrassingly parallel), not within one.
- The conformance kernel at ell 10 takes 12.2 s against 5.8 ms (2,100x). At ell 20 its encode
  alone would be about 2.7e11 reference multiplies, around 3 hours.

## 4. T4 numbers (`accel-tower-dryrun-04`, final code; tuning in `accel-tower-tune-02/-03`)

**Per proof, device phases (ms) and the Python host's openings.**

| ell | encode | Merkle | folds | device sum | host openings (Python) | wall |
|---:|---:|---:|---:|---:|---:|---:|
| 14 | 5.2 | 2.8 | 2.0 | 10.0 | 112 | 135 |
| 16 | 8.1 | 4.3 | 2.6 | 15.0 | 145 | 174 |
| 18 | 33.3 | 9.1 | 4.4 | 46.8 | 182 | 250 |
| 20 | 86.8 | 14.1 | 6.9 | 108 | 223 | 362 |

- At ell 14-16 the device time is launch-bound: about 300 small launches.
- The host openings are a Python artifact: digest base-255 encoding and byte assembly. The Rust
  prover's openings take 5-10 ms. A production host is the Rust prover with these kernels
  behind it.

**Batch (encode + commit, 64 words at ell 14):** 0.82 ms per word, against about 48.6 ms on one
Xeon core (7.6 encode + 41.0 Merkle). One T4 is about 59 such cores.

**Primitive rates** (`keccak_f_per_s` for lane w3-mma):

| primitive | measured | int32-op equivalents (T4: 40 SM x 64 lanes x 1.59 GHz) | F3-MODEL assumption |
|---|---:|---:|---:|
| Keccak-f[1600] (batched Merkle build, funnel-shift rotations) | **4.35e8/s** (dryrun-04); 6.9e8/s (tune-03) | 9,350; 5,900 | 4,320 [D] |
| Keccak-f, standalone dependent-chain probe (every variant) | 3.15-3.18e8/s | ~12,900 | |
| Tower256 multiply, log/exp GF(2^8) tables | **2.87e8/s** | ~14,200 | 718 (bit-sliced) [A] |
| Tower256 multiply, 64 KiB product table in dynamic smem | 3.4e7/s | ~120,000 | |

Tuning results:
- Funnel-shift rotations gave the batched Merkle build 1.9x over plain 64-bit shifts (3.7e8 in
  dryrun-01 against 6.9e8 in tune-03, same harness). The 4.35e8 in dryrun-04 is the same kernel
  on a different T4 session: small timed windows (5 ms), and the T4's 70 W cap moves clocks. Cite
  the range.
- Unrolling the rounds by 2 changes nothing. A full unroll does not launch at 256 threads.
- The full product table is 8.5x slower than log/exp. Log/exp stays the default.
- On the Keccak side, the T4 measures 1.4-2.2x above the model's 4,320 ops.
- On the multiply side the gap is 20x: table Karatsuba is about 4,350 instructions plus
  bank-conflicted shared loads. The F3 assumption of 718 for bit-sliced is the unbuilt kernel.
  It decides whether the GPU encode (80% of the device time at ell 20) can drop toward the hash
  cost.

## 5. Predictions (model: SIMT int32 throughput scales the measured T4 rates)

These kernels are integer-SIMT plus shared memory; no tensor cores are involved. H100 SXM has
132 SMs x 64 INT32 lanes x 1.98 GHz = 1.67e13 lane-ops/s, which is 4.1x the T4 at its listed
clock [A: not measured]. B200 is taken as about 1.3x H100 on INT32 SIMT [A].

| | T4 measured | H100 SXM predicted | B200 predicted [A] |
|---|---:|---:|---:|
| Keccak-f/s | 4.4-6.9e8 | 1.8-2.8e9 | 2.3-3.7e9 |
| Tower256 mult/s (tables) | 2.9e8 | 1.2e9 | 1.5e9 |
| ell 14 batch, words/s (encode + commit) | 1,220 | ~5,000 | ~6,500 |
| ell 20 per proof, device | 108 ms | ~26 ms | ~20 ms |

A CPU comparison on the same box: a 64-core host at about 2x the Kaggle core does about
64 x 2 / 48.6 ms = 2,600 ell-14 words/s. That is within 2x of an H100 on this workload until the
multiply kernel improves.

## 6. Paid box (only if ember wants H100 numbers; not needed for any current decision)

- **Ask for:** 1x H100 SXM 80 GB (any CUDA 12.4+ driver; Ubuntu 22.04/24.04), at least 16 host
  cores, 64 GB RAM, internet.
- **Run:**
  `runbook/tower256-bundle.sh <minidregg checkout of lane/accel-tower256-gpu>`,
  scp the tarball, `tar xzf`, then `bash tower256/tower256.sh` (venv with pinned
  numpy 2.1.3, pycryptodome 3.23.0, cupy-cuda12x 13.6.0 / cupy-cuda13x 14.0.1 (pins checked on
  PyPI); rustup 1.89.0; `target-cpu=native`).
- **Expected wall:** about 10 minutes. The T4 shrink took 118 s; the full mode adds ell 22, a
  512-word batch at ell 14 and a 64-word batch at ell 18. The script's own limit is 3,000 s.
- **Cost:** H100 SXM on demand about $2-3/h [A: not checked this session], so under $1.

**What each paid result decides for the Tower256 lane:**
- **H100 words/s at ell 14** (batch 512) against the same box's `rust_cpu` across all cores:
  whether a GPU is worth carrying for the leaf prover at all. If it is below 3x the box's CPU,
  stay on CPU.
- **H100 Keccak-f/s:** whether F3-MODEL's 3.9e9 holds (the model's Keccak share of a proof).
- **Device ell 22 per proof:** the largest single leaf on one GPU.

## 7. What is left (owned here unless noted)

- **The GPU multiply is still the encode's lever** (80% of device time at ell 20). The
  per-thread bit-sliced kernel did not move it (§8). The design to try next is warp-cooperative
  (below).
- **A Rust host for the device kernels,** to remove the Python openings (100-220 ms).
- **Tower256 lane's call** whether `tower256_fri_fast` (or its pieces: the Gao-Mateer encode, the
  stored trees, the polynomial-basis multiply) replaces the conformance kernel behind
  `tower256_additive_fri_prove_bytes`. Its receipts are byte-identical, and the conformance
  kernel stays as the pinned reference.
- The `lib.rs` line is in `patches/minidregg-tower256-fri-fast-mod.patch`.

## 8. The bit-sliced Tower256 multiply on the T4 (`accel-tower-bitslice-01`, 2 versions)

This tests the ~718 SIMT ops per multiply that F3-MODEL and ROTATION compare against.
Runs: `runs/accel-tower-bitslice-01-v1`, `runs/accel-tower-bitslice-01-v2`. Each version is the
whole shrunk script with `TOWER256_GPU_ARGS="--mul bs --bitslice-bench"`.

**The kernels** (`prover/cuda/tower256_fri.cu`, after `transpose32`):
- One thread multiplies a group of 32 products held as 256 bit planes (plane p, bit l = bit p
  of element l).
- The arithmetic is the Fan-Paar Karatsuba recursion on planes: AND at T_0, and the generator
  map `y_{K-1}` as XORs.
- `t256_mul_bs` works on resident sliced data: plane p of group g at `p*G + g`, coalesced.
- `t256_mul_bsx` and `ntt_scale_bsx` / `ntt_butterfly_bsx` / `fri_fold_bsx` are fused: they
  gather 32 elements, transpose 32x32 with five SWAR stages, multiply, and transpose back.
  They replace the bulk kernels under `--mul bs`.
- v1 cut the tree at T_5 (27 leaves in registers) and recombined through a flat table of 166
  terms into a 256-word accumulator, generated symbolically by the lane's
  `bs/gen_tables.py` (scratch, not committed).
- v2 cuts at T_4 (81 leaves in registers) and combines depth-first through 720 words of
  scratch. Levels 5-8 are out-of-line calls.

**Bit-exact, both versions:**
- 1,024 products against `binary_tower_256.rs` (`mul_check.bin`), through both the resident
  path (to_sliced, mul, from_sliced) and the fused path.
- 2^20 random products against the table kernel.
- With `--mul bs` in the encode and folds: the five Lean receipts and the ell 10..20 receipts
  and roots against the CPU prover.

**Rates** (2^20 products, warm, synchronized; int32-op equivalents = 40 SM x 64 x 1.59 GHz /
rate):

| kernel | v1 (T_5 leaves, table recombination) | v2 (T_4 leaves, depth-first) |
|---|---:|---:|
| bit-sliced, resident planes | 7.96e7/s = 51,100 ops | 7.72e7/s = **52,700 ops** |
| bit-sliced, fused with transposes | 3.22e7/s = 126,500 ops | 5.69e7/s = 71,500 ops |
| log/exp table kernel, same session | 3.40e8/s = 12,000 ops | 2.33e8/s = 17,400 ops |
| to_sliced / from_sliced (elements/s) | 4.4e8 / 1.07e8 | 4.3e8 / 1.06e8 |
| ptxas, `t256_mul_bs` | 255 regs, 6.5 KB spill | 248 regs, no spill |

`tower256_mul_per_s` (7.72e7) and `ops_per_mul` (52,700) are in v2's `results.json`.

**Per proof at ell 20 with `--mul bs`** (v2): encode 236 ms, folds 26 ms. With the tables
(dryrun-04) they are 87 ms and 7 ms. The bit-sliced kernel loses, so the tables stay the GPU
path.

**What this says about 718:**
- The arithmetic count of this formula is fixed: 3^8 = 6,561 ANDs and 34,550 XORs per 32
  products, from the recursion `X(K) = 3 X(K-1) + 3·2^K - 1`. That is 1,284 two-input ops per
  product, or about 860 if every XOR pair fused into a three-input LOP3.
- So 718 sits below even the ideal instruction count of Karatsuba-to-bits. It is not a
  measured or attainable SIMT figure for this multiply.
- The measured 52,700 is about 40x that count. What costs is data movement, not arithmetic:
  - 256 planes per operand cannot live in 255 registers, so the tree runs through per-thread
    local memory (L1/L2);
  - at 248 registers only 8 warps fit per SM, too few to hide that traffic.
- The table kernel (12,000-17,400 ops-equivalent, also latency-bound on bank-conflicted shared
  loads) stays 3-4x ahead on sm_75.

**For F3-MODEL and ROTATION:** use about 12,000-17,000 measured int32-op equivalents per
Tower256 multiply on SIMT (T4, tables), not 718. With that, the multiply rather than the hash
dominates the GPU prover. F3 item 6's "at 4x that multiply cost" branch is the one that holds,
and the real factor is about 20x.

**The next design**, if the multiply's GPU rate matters to a decision: warp-cooperative bit
slicing. Each lane owns one leaf product in registers, the 32 lanes of a warp share one group's
planes in shared memory (padded to stride 33 against bank conflicts), and the evaluation and
recombination trees are spread across lanes. Estimate: about 1,700 lane-ops per product,
around 7-10x the tables, if shared-memory traffic hides at moderate occupancy. It can be
measured on the free T4.
