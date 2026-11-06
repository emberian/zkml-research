# Workload 1: dark-learning BFV on accelerators (initiative 17, lane w1-bfv)

2026-11-06. Device port, tuning and paid-box script for the he_outer / he_matvec return pipeline in
`research/dark_learning_2026_11_06/`. The science belongs to the dark-learning lane. This file covers what was
built, every bit-exact check, the measurements, the model that predicts H100/B200, and what a paid run decides.

## 0. Verdict

- **The pipeline is exact on a GPU.** On a Kaggle T4, every word matches the owning lane's code: NTT spectra,
  the returned ciphertext residues, and the decryption.
- **One d = 4096 step is GPU-sized and short.** A single T4, doing all three custodians' HE work, measured
  2.8 s (N = 8192, L = 3) to 4.0 s (N = 16384, L = 4), extrapolated from measured per-return times with the
  lane's own counts (section 4).
- **H100 model: 0.25 to 0.4 s per step.**
- **Paid hardware: one H100 hour is worth it, B200 is not.** The H100 run turns a 2x-uncertain model into a
  measurement for about $3 [A]. B200 is predicted at only about 1.1 to 1.3x H100, because the NTT is bound by
  INT32 multiply throughput, not bandwidth.
- **The fork verdict does not need paid hardware.** It needs the T4 numbers below. At these rates the HE
  outer product is not the bottleneck of a training step.
- **TPU is a design plus a CPU-exact deliverable for now** (section 5). The MXU four-step path is exact on CPU.
  The one TPU measurement job is staged and waits on TPU-LOCK.

## 1. What was built (all new files; no existing file edited)

| file | what |
|---|---|
| `accel_rns_ref.py` | exact reference (Python ints, numpy object arrays): convention, tables, forward/inverse, RNS product, mask encoding, HPS decryption, the he_outer return in RNS form, checks |
| `accel_rns_ntt.cu` | CUDA (NVRTC via cupy). Batched two-phase NTT; Shoup or Montgomery (`__umul64hi`); plain radix-2 and register radix-2^G (G = 2..4) variants. Return kernels: `ret_mac` (sum over K blocks of P^ C^ + K U^), `ret_finalize` (e + round(QM/t) from M alone + flood), `pmul_fixed`, `hps_decrypt`, `gen_random`, fixed-operand prep |
| `accel_bench_cuda.py` | `Ctx` (tables, kernels, shapes); NTT check; tuning sweep |
| `accel_he_bench.py` | return pipeline (`Pipe`), check against the owning lane's code, bench, per-step extrapolation |
| `accel_bfv_run.py` | one entry: sweep -> best exact shape per (N, L) -> check + bench + extrapolation. `--shrink` = T4 |
| `accel_rns_jax.py` | TPU paths: VPU (u32 Montgomery), x64 baseline, MXU four-step (int8 dots), with checks and benches |
| `runbook/bfv.sh`, `runbook/bfv_kaggle_entry.py` | paid-box script (uses the parent's `common.sh`), and the Kaggle wrapper that ran it |

## 2. Convention (fixed once, `accel_rns_ref.py` docstring)

- **Primes.** L = 3: `ntt_primes(61, 3, 2N)`. L = 4: the first five of `ntt_primes(61, 5, 2N)`, minus t.
  t = `ntt_primes(61, 4, 2N)[3]` (the SPDZ field, as in run_he_outer) in both cases.
- **Root.** psi is the smallest primitive 2N-th root.
- **Forward.** Cooley-Tukey with psi_brv twiddles: natural-order input, bit-reversed output,
  A[k] = a(psi^(2 brv(k) + 1)).
- **Inverse.** Gentleman-Sande with ipsi_brv twiddles. Devices fold N^-1 into the last stage; the words are
  identical because every value is a canonical residue.
- **MXU four-step.** It produces X = A[brv] natively and is compared after that documented permutation.
- **Prime structure.** Every prime used is 2^61 - delta with delta < 2^22.

## 3. Bit-exact checks (all pass)

| check | where | result |
|---|---|---|
| forward = direct evaluation a(psi^(2 brv(k)+1)) at sampled k; inverse(forward) = id | ref, Mac, N 8192/16384, every prime of L 3 and 4 | pass |
| RNS NTT product, CRT mod Q = `bfv_ref.negacyclic_mul` mod Q: random full-size, and sparse D_a (coefficients 64 r, centered mod t) x uniform | ref, Mac, N 8192/16384, L 3/4 | pass |
| RNS return pipeline (`return_rns`) = `he_outer.HEOuter._return` ciphertext (rng replayed) and `bfv_ref` decryption; HPS ambiguity count 0 | ref, Mac, N 8192/16384, L 3/4 | pass |
| CUDA kernel index arithmetic, emulated in Python (all splits, column widths, G = 1..4), equals the ref | Mac (scratch emulators) | pass |
| device forward = ref words on sampled rows; inverse(forward) = input on every row; every swept shape (Shoup/Montgomery, E, threads, G) word-identical to the first | T4, every (N, L) | pass (20 shapes each) |
| device NTT-domain words of P and ct0 = ref; device c0, c1 residues = bfv_ref's ciphertext mod every prime, every coefficient; device decryption = `bfv_ref.decrypt`, every coefficient; HPS ambiguity 0 | T4, 2 returns per (N, L) drawn from `he_outer._return` | pass |
| JAX VPU / x64 forward = ref words, round trip; MXU forward = ref words after brv, round trip, MXU product = `negacyclic_mul` mod p | JAX CPU, N 8192/16384, all primes of L 3/4 | pass |

Dry run 02 found one real bug: the device HPS ambiguity counter overflowed when the 64-bit fraction was exactly 0
(it computed abs(INT64_MIN)). At L = 4 the fraction is about t * noise / Q ~ 2^-64, so fr = 0 happens often.
The decryption itself was already correct. Fixed with an unsigned distance; all later runs show 0.

## 4. CUDA: T4 measurements, roofline, H100/B200 prediction

Runs (harvested under `runs/`):
- `accel-bfv-dry-t4-03`: `accel_bfv_run.py --shrink`, all exact.
- `accel-bfv-dry-t4-04`: **`runbook/bfv.sh --shrink` itself**, all exact, rc 0, 198 s wall.

Run 04 warms the clocks first. Run 03 timed short bursts after an idle CPU-bound check, at 585-795 MHz.
Run 04 is sustained at the T4's 70 W power cap (1.2-1.4 GHz). Run 04's numbers are the honest ones and are used below.

**NTT microbench, T4, sustained (best shape per (N, L) from the 20-shape quick sweep):**

| N, L | best shape | fwd / inv us per NTT | effective HBM |
|---|---|---|---|
| 8192, 3 | Shoup, one pass (E = N), 256 thr, radix-8 | 1.77 / 2.20 | ~66 GB/s |
| 16384, 3 | Shoup, two pass (E = 1024), 128 thr, radix-8 | 3.78 / 4.28 | ~130 GB/s |
| 8192, 4 | Shoup, one pass, 256 thr, radix-8 | 1.81 / 2.24 | |
| 16384, 4 | Shoup, two pass, 128 thr, radix-8 | 4.53 / 4.61 | |

In unthrottled bursts (run 03), two-pass Montgomery radix-2 at E = 1024 reached 1.35 us at N = 8192. That is
61% of the two-pass HBM floor.

**Per return (us, T4 sustained, he_outer, K = 1):**

| N, L | gen | NTT(u) | MAC | INTT(acc) | finalize | decrypt (j) | total | sender |
|---|---|---|---|---|---|---|---|---|
| 8192, 3 | 2.9 | 5.3 | 4.4 | 13.3 | 4.9 | 17.2 | **49.5** | 30.9 |
| 16384, 3 | 5.9 | 11.8 | 13.4 | 26.3 | 9.8 | 34.7 | **100.8** | 67.2 |
| 8192, 4 | 4.1 | 7.4 | 6.9 | 18.2 | 6.4 | 24.0 | **68.1** | 43.1 |
| 16384, 4 | 8.4 | 17.0 | 22.6 | 37.8 | 12.8 | 48.8 | **145.5** | 98.6 |

**Per step at d = 4096, n = 3, one T4 doing every custodian's HE work.**
- Measured: per-return times for he_outer (K = 1) and he_matvec (K = 1 and K = 64).
- Extrapolated: return counts from `he_outer.counts` / `he_matvec.counts`; matvec MAC cost linear in K;
  amortized NTTs at the measured NTT rate (receiver NTT of each sent ct, 2L each; plaintext spectra, L each).

| N, L | outer returns | outer s | matvec s | **step s** | per custodian s |
|---|---|---|---|---|---|
| 8192, 3 | 49,152 | 2.45 | 0.32 | **2.77** | 0.92 |
| 16384, 3 | 24,576 | 2.50 | 0.34 | **2.84** | 0.95 |
| 8192, 4 | 49,152 | 3.36 | 0.39 | **3.75** | 1.25 |
| 16384, 4 | 24,576 | 3.60 | 0.43 | **4.03** | 1.34 |

N = 16384 halves the outer returns but doubles each one, so the two N cost about the same. L = 4 costs about 1.35x L = 3.

**Roofline (per NTT).**
- Work: N/2 log2 N butterflies, 53,248 at N = 8192 and 114,688 at N = 16384.
- 64-bit multiplies per butterfly: Montgomery 2 lo + 2 hi (213k per NTT at N = 8192); Shoup 2 lo + 1 hi (160k).
- Instruction count per butterfly: about 16 IMAD-equivalents plus 12 other int ops [A].
  sm_70+ has no 64-bit IMAD: mul.lo64 is about 3 IMAD, `__umul64hi` about 4-5.
- HBM per NTT: 2 x 8 N bytes per pass, i.e. 131 KB in one pass and 262 KB in two (N = 8192).
- INT32 throughput assumed [A]: 64 lanes/SM/clk at boost clock.
  - T4: 40 SM at 1.59 GHz = 4.1 Tops
  - H100 SXM: 132 SM at 1.98 GHz = 16.7 Tops
  - B200: 148 SM at 1.965 GHz = 18.6 Tops

| N = 8192 floors (us) | INT32 compute | HBM, one pass | HBM, two pass |
|---|---|---|---|
| T4 (320 GB/s) | 0.37 | 0.41 | 0.82 |
| H100 SXM (3.35 TB/s) | 0.089 | 0.039 | 0.078 |
| B200 (8 TB/s) | 0.080 | 0.016 | 0.033 |

N = 16384 doubles every entry (plus one stage).
- **On T4** the measured 1.35-2.0 us is HBM- and latency-bound, at 25-61% of the binding floor.
- **On H100 and B200** the INT32 floor is above the HBM floor. That is why B200 buys little for the NTT.

**Prediction.**
- NTT, efficiency 0.25-0.5 against the INT32 floor (T4 sustained 0.25, burst 0.5):
  - H100: 0.18-0.36 us per NTT at N = 8192
  - B200: 0.16-0.32 us
- The elementwise stages (gen, MAC, finalize, decrypt copy and HPS; about 17 us per return on the T4)
  are HBM-bound and scale by bandwidth: about 1.6 us on H100 and 0.7 us on B200.
- Per return at N = 8192, L = 3 (15 NTTs plus elementwise): **H100 4.3-7.0 us, B200 3.1-5.5 us**.
- Per step (all custodians, one GPU): **H100 0.25-0.4 s, B200 0.18-0.3 s**, against 2.8 s measured on the T4.
- With one GPU per custodian: about 0.1 s per step on H100.

**Tuning not done (next on a paid box, each checked word for word against the ref):**
1. Fuse the MAC into the inverse NTT's first-phase load, and the finalize into its last store. This removes
   two full passes over Acc (about 5 us of 49.5 on the T4).
2. Fuse the decryption's pointwise product into its inverse NTT.
3. Lazy (Harvey) reduction in [0, 4p): p < 2^61 leaves room.
4. Protocol-level, for the owning lane to decide: Enc_pk_j(0) is data-independent, so it can be precomputed
   offline. That removes L of the 5L NTTs per return from the online step.
5. A real CSPRNG (ChaCha20/AES-CTR) instead of splitmix64 in `gen_random`. Gen is 6% of a return now, and a
   ChaCha block per 64 bytes of randomness should stay under 10%.

## 5. TPU (JAX)
TPU v5e has no 64-bit integer multiply. Residues are canonical and stored as u32 pairs (lo, hi), with hi < 2^29.
Three paths are in `accel_rns_jax.py`, and all three are bit-exact on JAX CPU at N = 8192 and 16384 for every
prime of L = 3 and L = 4, against `accel_rns_ref.fwd` (forward words), the round trip, and (for MXU) a full
product against `bfv_ref.negacyclic_mul`.

**(a) VPU path.** This is the reference transform word for word: CT/GS radix-2 stages written as
reshape (m, 2, t), with psi_brv twiddles. The modular multiply is a four-limb radix-2^16 Montgomery product
with R = 2^64. It is the breadstuffs `bfv_ntt.wgsl` technique (three limbs, q < 2^48) extended by one limb.
Instead of carrying row by row, every 16x16 -> 32 product is split into 16-bit halves and added into 10
column accumulators. Each column holds at most 8 product halves, 8 reduction halves and the passed carries,
so every column stays < 2^22. The REDC rounds take m_i from the exact low 16 bits of column i, then pass the
carry from column i to column i + 1. Cost per modmul is 36 u32 multiplies (16 product, 4 m_i, 16 m*p), about
180 VPU ops in all. Twiddles are held in Montgomery form, so the outputs stay canonical.

**(x) X64 baseline.** The same transform on `jnp.uint64` with `jax_enable_x64`. mulhi64 is built from four
32x32 -> 64 products. On TPU, u64 is emulated, and this path measures what that emulation costs.

**(b) MXU path (CROSS/MORPH style).** A four-step decomposition N = N1 N2, with j = j1 + N1 j2 and
k = N2 k1 + k2. The forward exponent factors as psi^(j (1 + 2 k2)), which folds the psi twist and the
four-step middle twiddle into the first stage's per-j1 matrices:
  B[j1, k2] = sum_j2 a[j] psi^(j (1 + 2 k2))           (N1 matrices of N2 x N2)
  X[N2 k1 + k2] = sum_j1 psi^(2 N2 j1 k1) B[j1, k2]    (one N1 x N1 matrix)
So X[k] = a(psi^(2k+1)) in natural order, and the reference's bit-reversed spectrum is A = X[brv]. Pointwise
products are order-agnostic, so the pipeline never permutes. The inverse mirrors this with psi^-1, and
N^-1 is folded into the per-j1 matrices. There is no VPU twiddle pass at all.

Each stage computes Y = Z W mod p as an int8 x int8 -> int32 dot:
- Z (canonical) is cut into 8 balanced bytes z_i in [-128, 127].
- For each i, W 2^(8i) mod p is cut into 8 balanced bytes.
- i goes into the K dimension and l into the output dimension, so Y_l = sum_(i,j) z_i[j] byte_l(W[j] 2^(8i)),
  and sum_l Y_l 2^(8l) = Z W (mod p).

*int32 no-overflow bound:* K = 8 n <= 8 * 128 = 1024 terms, each |z w| <= 128 * 128 = 2^14, so
|Y_l| <= 2^24 < 2^31 (the K x 128^2 < 2^31 condition, with 2^7 of margin).

*Reduce (VPU):* the carry chain s_l = Y_l + c, d_l = s_l mod 256, c = floor(s_l / 256) gives V = D + c 2^64.
Here D < 2^64 and |c| < 2^17. Every prime here is p = 2^61 - delta with delta < 2^22 (asserted).
Then D = h 2^61 + r gives V = r + (h + 8c) delta (mod p), with |(h + 8c) delta| < 2^43.
r + e delta lies in (-2^43, 2^61 + 2^43), so one conditional add or subtract of p makes it canonical.

Matrix bytes per prime (forward + inverse): 134.7 MB at N = 8192 (N1 = 64; 69 MB with N1 = 128) and
270.5 MB at N = 16384. That is 1.1 GB for L = 4, inside v5e's 16 GB HBM.
int8 MACs per NTT: N1 (8 N2)^2 + (8 N1)^2 N2 = 1.0e8 at N = 8192 and 2.7e8 at N = 16384.
At the v5e peak of 394 int8 TOPS [A, public spec], that is 0.5 and 1.4 us per NTT.

**CPU timings** (Mac, JAX 0.12 CPU, P = 8, under load; for scale only). VPU 1040 / 350 us, MXU 966 / 1093 us,
x64 184 / 1046 us per NTT at N = 8192. CPU int8 dots reach 0.1-0.2 TOPS. These numbers mean nothing for the TPU.

**TPU measurement: one bounded job, staged as `accel-bfv-tpu-01` (not yet run).**
- `accel_rns_jax.py --check --checkL 3 --bench --N 8192 16384 --P 128 512 --N1 0 128 --pointwise --multi 256`
- It runs checks on device for every L = 3 prime at both N.
- Single device first: VPU / MXU / x64 at P = 128 and 512, the MXU with N1 = default and 128, and the VPU
  pointwise modmul rate.
- Then all 8 devices (pmap, MXU, P = 256 per device).
- Platform timeout 1200 s.
- TPU-LOCK has been held since 20:56 UTC by the parent's env probe, which is still QUEUED on Kaggle. Per the
  parent, if the queue stays hours-long, the TPU half stands as design plus CPU-exact.

**What would make the TPU competitive.**
- A d = 4096 step at N = 8192, L = 3 needs about 0.74 M NTTs (5L per return) plus about 4L pointwise modmuls
  per return.
- To match the T4 (2.8 s per step), a v5e chip must reach about 3.8 us per NTT including the pointwise share.
- To match the predicted H100 (0.3 s), it must reach about 0.4 us.
- The MXU path's int8 work alone is 0.5 us at peak, so even at full MXU efficiency a v5e chip lands near an
  H100, not above it. Eight chips would be about 8x one.
- Paid TPU is not on ember's offer. TPU stays Kaggle-only (free, queue-bound), and I see no case for arguing
  otherwise.

## 6. Paid box: what to ask for, wall, cost

- **Box:** one H100 SXM 80 GB (PCIe also fine: same INT32 count, lower clock and bandwidth), Ubuntu 22.04/24.04,
  NVIDIA driver with CUDA 12.x or 13.x, python3 with venv, internet. No CUDA toolkit needed.
  One GPU suffices: the script uses device 0.
- **Command:** `bash notes/accelerator-readiness/runbook/bfv.sh --sku H100` from a zkml-research checkout.
  `--shrink` reproduces the T4 dry run exactly.
- **Pins:** `cupy-cuda13x[ctk]==14.0.1` (or `cupy-cuda12x[ctk]==14.0.1` on a CUDA-12 driver), `numpy==2.1.3`.
  The `[ctk]` extra installs NVRTC and headers from PyPI [A: checked on Kaggle only with cupy-cuda13x 14.0.1 and
  a system toolkit present; the env smoke test fails loudly if NVRTC is missing].
- **Wall:** setup about 2 min. The full sweep is 124 shapes per (N, L) at N = 8192 and 152 at N = 16384 (single pass up to
  E = 16384 fits H100's 227 KB of shared memory), each with a word-for-word compare against the first. Checks are 3 returns per (N, L), CPU-bound: about 3 min at N = 16384, L = 4 on Kaggle's
  CPU. Benches use 512-return batches at N = 8192, L = 3 (scaled by 1/(N L)). Expect 20-35 min; the internal watchdog is 3000 s (stall 600 s).
- **Cost:** an H100 SXM on demand is about $2-3/h [A: public list prices, vast.ai/Lambda ranges, not checked
  today], so **about $1-3** for this run.
- **B200:** not recommended. The model says 1.1-1.3x H100 for about 2x the price [A]. Run it only if ember
  already has one up.

## 7. What each paid result decides (for the dark-learning lane)

- **H100 step time T_H.**
  - If T_H <= 0.5 s (all custodians on one GPU), the HE outer-product exchange costs under 1 s per step at
    d = 4096. The MPC fork's HE route is then compute-cheap, and its cost is wire: 49,152 returned ciphertexts
    of 2NL words per step.
  - If T_H > 1 s, the lane should take the Enc(0)-offline and fusion items in section 4 before pricing.
- **N = 8192 against N = 16384.** Equal device time (measured on the T4), so the choice is decided by wire and
  security, not compute.
- **L = 3 against L = 4.** A measured 1.35x on the T4. The paid run confirms whether the ratio holds when
  compute-bound.
- **Shoup against Montgomery.**
  - Shoup wins sustained on the T4 (fewer mulhi).
  - Montgomery wins in bursts.
  - H100's answer picks the default for production code.
