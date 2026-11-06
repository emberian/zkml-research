# Accelerator readiness (initiative 17): grounding

2026-11-06. What exists before this lane writes a kernel, what it reuses, and the bar. Three workloads; their
science belongs to other lanes, the device port, tuning and runbook belong here.

## 0. The bar

1. Every device kernel is checked **bit-exactly** against a CPU reference that is itself checked against the
   owning lane's reference (Python big-int BFV, the Lean-pinned Tower256 receipts, PTX semantics).
2. Tuning happens on CPU first: JAX on CPU for TPU code paths (XLA compiles the same program), `nvcc`
   compile checks where a toolkit exists, roofline models from the hardware lane's counts.
3. Then Kaggle (T4 x2, TPU v5e-8, account `emberian64`) through `harness/kaggle_job.py` only, logged in
   `KAGGLE-LEDGER.md`. TPU serialized by `TPU-LOCK`.
4. Then one script per workload for a fresh H100/H200/B200 box (ember provides it), under an hour wall,
   whose shrunk-parameter dry run passed on the T4 first. RUNBOOK.md says what box to ask for and what
   each result decides.

## 1. Machines (checked 2026-11-06)

| box | role here | CUDA toolkit | notes |
|---|---|---|---|
| Mac | references, JAX CPU (venv: jax 0.12.0.1, numpy 2.5.4, pycryptodome 4.3.0) | none | 171 GiB free at start |
| hbox | Rust builds if needed (`swarm-build`) | **none** (`/usr/local/cuda*` absent, no `nvcc`) | AMD RX 6750 XT (ROCm/Julia route documented in intmat); not our target |
| dregg-forge | compile checks under `/srv/lanes/accel-ready/` | **none** | nice -n 15, MemoryMax=12G, pause 10:00-11:00 UTC |
| Kaggle T4 | the first real CUDA compile and run | image toolkit (probe `accel-env-probe-t4-01`) | Oct: two 15 GiB T4s visible, sm_75 |
| Kaggle TPU v5e-8 | the JAX TPU path | n/a | Oct: JAX 0.11.0, 8 devices |

No local `nvcc` means the first real compile of each `.cu` file is on Kaggle. A pip `nvidia-cuda-nvcc` wheel on
forge is a possible compile-only check; not set up.

## 2. Workload 1: dark-learning BFV (zkml-research `research/dark_learning_2026_11_06/`)

- `bfv_ref.py`: exact textbook BFV on Python ints. Negacyclic products by Kronecker substitution
  (`negacyclic_mul`, exact over Z), `ntt_primes(61, k, 2N)` gives the NTT-friendly primes. **No NTT exists
  anywhere in the experiment**: every product is a big-int multiply. This is the oracle for the RNS NTT.
- `he_matvec.py`, `he_outer.py`: pairwise plaintext x ciphertext products under each custodian's own key.
  Per return: `ptxct` (two negacyclic products mod Q), `enc_zero_pk` (two), `decrypt` (one), masks and flood.
  Counts at d = 4096 (from their own `counts()`), n = 3:

  | N | L | matvec cts sent / returned | outer cts sent / returned |
  |---:|---:|---:|---:|
  | 8192 | 3 or 4 | 960 / 768 | 768 / **49,152** |
  | 16384 | 3 or 4 | 864 / 576 | 768 / **24,576** |

  The outer product's returns dominate: about 5 negacyclic products per return, each L forward plus L
  inverse NTTs in RNS, so ~10^5..10^6 NTTs of size N per step. That is GPU-sized work; a CPU at
  ~0.1 ms per 64-bit NTT needs tens of seconds per step.
- `spdz.py`: the SPDZ engine over the ~61-bit field (Python ints); not an accelerator target.
- Decision record: `docs/DARK-LEARNING-SCHEME-DECISION.md` (N = 8192, Q = three ~61-bit primes, t a fourth;
  "counts only" for experiment 1).
- **Reuse:** breadstuffs `fhegg-fhe/src/shaders/bfv_ntt.wgsl` and `src/bfv_ntt_gpu.rs`: an exact negacyclic
  RNS NTT in WGSL with u32-only arithmetic, three-limb radix-2^16 Montgomery for q < 2^48. Its limb
  Montgomery is the template for the TPU VPU path (extended to four 16-bit limbs for 61-bit primes);
  `ntt_four_step.wgsl` is the four-step layout. fhegg's own BFV (3x36-bit, N = 4096) is the rejected legacy
  engine, so the shaders are reused as technique, not as the engine.
- TPU facts the limb design rests on (CPU-checked; TPU result from `accel-env-probe-tpu-01`): u32 multiply
  low word exact; int8 x int8 -> int32 `jnp.dot` exact at K = 1024; u64 multiply under `jax_enable_x64`
  (emulated on TPU; cost to be measured).
- Prior art to price against (docs/HARDWARE.md): CROSS (HPCA'26) / MORPH run FHE NTT as INT8 GEMMs on TPU
  (v6e beats WarpDrive-on-A100 by 1.43x). That is the MXU path for a TPU NTT.

## 3. Workload 2: Tower256 FRI leaf prover (minidregg)

- Spec in counts: `docs/TOWER256-FRI-PROVER-WORK.md` (on `lane/tower256-prover-exe` and later lane branches,
  not on minidregg `main`). Prover ~4·2^ell Keccak-f (Merkle; leaves 66 B, nodes 131 B, one Keccak-f each
  from a cached customization midstate) plus an encode of size n·ell.
- The native kernel: `prover/src/tower256_fri_prove.rs` on `lane/tower256-prover-exe` (d88a8fb35), with
  `prover/src/binary_tower_256.rs` (Fan-Paar coordinates, limbs `[u64; 4]`), `prover/src/hash_kernels.rs`
  (`cshake256_xof`, the `sha3` crate). Byte-exact oracle: `prover/testdata/tower256_fri_vectors.json`, five
  Lean-produced request/response pairs (ell 2..8).
- **Read of the current kernel (this lane, 2026-11-06):** it is a conformance kernel, not a fast one, and
  three of its loops are asymptotically above the counts doc:
  1. encode is Horner at every domain point: n·deg multiplies (ell = 20, lb = 2: 2^20·2^18 = 2.7e11), where
     the counts doc assumes an additive NTT (n·ell);
  2. `Merkle::path` recomputes the subtree for every sibling: about 2·2^(ell-j) hashes per query per round,
     so ~q·4·2^ell in total (q = 148: ~150x the 4·2^ell of the commitment), where a stored tree costs 0;
  3. `Tower::domain` re-applies all pivots per point per level, though y -> y^2 + p·y is GF(2)-linear, so a
     level's domain is an XOR span of ell images.
  A GPU port of this code would accelerate the wrong loops. The order is: an algorithmically fixed CPU
  prover, byte-identical on the five vectors (proposed to the Tower256 lane as a patch, never edited in
  place), then the GPU Keccak Merkle layer and additive NTT against it.
- `native/mini-kernels` (minidregg main): cSHAKE256/KMAC256 via the `sha3` crate; no hand-written Keccak,
  no GPU code. Python oracle here: pycryptodome `cSHAKE256`.
- Hardware lane's verdict (`notes/tensor-core-holography/F3-MODEL.md` §1.5-6): no tensor-core mapping for
  binary fields without a 1-bit MMA; bit-sliced SIMT; Keccak-f ~4,320 int32 ops with LOP3, model 3.9e9/s on H100.

## 4. Workload 3: tensor-core exactness probe (degg-research `experiments/mma-accumulator-probe/`)

- `probe.cu` (uncompiled), `Makefile` (`ARCH ?= sm_90`), `README.md` (the one-hour, seven-step protocol).
- Its two kernels need `mma.sync m16n8k32` u8 (sm_80+) and e4m3 (sm_89+). **Neither runs on a T4 (sm_75).**
  The T4 subset has to use Turing's shapes: `mma.sync.aligned.m8n8k16.row.col.s32.u8.u8.s32` (sm_75) for
  the u8 wrap facts, `m8n8k128 .b1 xor.popc` (sm_75; `and.popc` is sm_80+) for the 1-bit path, plus steps 4
  (copy bandwidth), 5 (cuBLAS INT8 GEMM `cublasGemmEx` CUDA_R_8I -> CUDA_R_32I) and 7 (Keccak-f rate).
- Lean premise it measures: minidregg `lane/mma-exact` `Theory/MmaAccumulatorExact.lean`. Counts model:
  `notes/construction-search/mma_counts.py`.

## 5. Kaggle facts carried in (swarm/kaggle.md, intmat/docs/accelerators.md)

- CLI: `uvx --from kaggle --with six kaggle` (2.2.5). Script kernels upload one `code_file`; bundles ride
  inside `run.py` as a base64 tar (intmat's pattern; `harness/kaggle_job.py` does this).
- Oct T4 job: two T4s visible, one used. Oct TPU job: JAX 0.11.0, eight devices, ran; the failure was in its
  own host reference. Several historical "GPU" requests ran on CPU: the harness checks hardware first and
  exits 3 if it is wrong.
- No other lane has an `accel-*` or init-8 kernel on the account as of 20:55 UTC.

## 6. Out of bounds

nanodregg*, /Users/ember/hellas, pug, renting or signing up for anything, `vast` without ember's word,
editing another lane's file in place.
