# The phases are bound differently — which dissolves the contradiction and decides the TPU question

2026-08-13, ember: *"there are probably different phases of the process that
are bound differently right?"* Yes, and it is the answer.

## 1. "Is the prover hash-bound?" is the wrong question

The two lanes did not contradict each other so much as **aggregate different
mixtures**. The prover has four phases with **structurally different**
bottlenecks:

| phase | work | scales with | bound by |
|---|---|---|---|
| **Commit — LDE** | coset NTT over the trace | `(2^b+1)·log₂h/2` mults/felt | **field arithmetic** (butterflies) |
| **Commit — Merkle** | hash the codeword | `2^b·(1/8 + 2/w)` perms/felt | **hashing** |
| **Sumcheck / folding** | round polys, MLE folds | `(d−1)·k·10` mults — **independent of blowup** | **field arithmetic** |
| **Query / opening** | Merkle paths | **query count**, not blowup | **hashing** |
| **Verification** | paths + a little arithmetic | queries | **hashing (~100%, both lanes agree)** |

So the mix is a function of `(b, w, q)` — and the two measurements sit at
different points: **the derived 94% is at lb=6 (blowup 64), the measured
19–40% is at ρ=1/2 (blowup 2).** The hash term scales with `2^b`; the LDE term
scales with `2^b·log h`. **At high blowup the hash share rises; at low blowup
the LDE dominates.** Both lanes may be right about their own point.

⚑ **Therefore the profiling run must report PER PHASE, not a single ratio** —
and the useful output is not "hash-bound: yes/no" but **the crossover in `b`**.

⚑ **And this changes the lb=6 finding.** `lb=6` being 2.9× off the measured
optimum (20 ms at lb=4 vs 58 ms) is *the same fact seen from the other side*:
high blowup buys UD bits per query and pays in both LDE and hashing. **The
blowup knob is the single control that moves the phase mixture, the soundness
regime, and the hardware target simultaneously.**

## 2. What that means for silicon — and it is not one engine

- **LDE-bound ⇒ a butterfly/NTT engine**, and it is **GEMM-shaped**.
- **Hash-bound ⇒ a Poseidon2 engine**, which is **not** GEMM-shaped
  (sequential rounds, S-boxes, no contraction to exploit).
- **Sumcheck-bound ⇒ an MLE-fold engine** — strided reductions and small
  contractions, **also GEMM-shaped**.

**So two of the three phases are tensor-core work and one is not.** That is
the whole TPU/tensor question in one line.

## 3. Our own tensor-core code — what it would actually be

**The precedent**: CROSS (HPCA'26) + MORPH (DAC'26) run **both FHE and ZK as
INT8 GEMMs on TPUs** — TPU v6e beats WarpDrive-on-A100 NTT by 1.43×, **451×
perf/W vs OpenFHE**. MoMA (CGO'25) emits both FHE and ZKP kernels from one
rewrite system. **They are doing our fusion thesis on rented AI silicon with
no RTL.**

**The mechanism, so we are not cargo-culting**: an NTT is *not* naively a GEMM
(a DFT matrix is O(n²) against O(n log n)), **but the four-step/six-step
decomposition turns a length-n transform into `√n` sub-transforms of length
`√n` plus a twiddle multiply — and each sub-transform IS a small dense
matrix multiply.** At N=4096 that is 64 GEMMs of 64×64 plus a pointwise pass:
O(n^1.5) in GEMM primitives against O(n log n) in scalar ones — **a worse
asymptotic bought at a hardware rate that is 2–3 orders better.** That trade
is exactly why it wins, and it is the same trade for MLE folding, which is a
strided reduction and natively a contraction.

**What we already have to build on**: `fhegg-fhe/src/bfv_ntt_gpu.rs` — a wgpu
negacyclic NTT **over our exact moduli** (three-limb radix-2¹⁶ Montgomery,
refuses composite/non-NTT-friendly moduli) — and `gpu_arena.rs`, whose
`ResidentHandle` keeps ciphertexts **on device and never downloads until
asked**. The fusion toy is "make `Arena` multi-pipeline and add a WGSL MLE
fold," which is the same kernel shape as the TPU work.

**And the honest caveat**: our field is a **31-bit prime**, not INT8. A
BabyBear multiply is a 32×32→64 widening product plus a Montgomery reduce;
tensor cores want INT8 accumulating in INT32. So the transfer needs either
**limb decomposition into INT8 lanes** (3–4 lanes per felt, with the
cross-limb products a GEMM and the reduction a separate pass) or the **BF16/
FP32 tensor path** with exactness argued rather than assumed. **CROSS/MORPH
solved this for their parameters and we should read how before writing a
kernel.** That is the first task, not the kernel.

## 4. The order this implies

1. **Profile per phase** at lb=4 and lb=6 — output the crossover in `b`, not a
   ratio. Unblocks the field decision, the blowup decision, and the silicon
   target at once.
2. **Read CROSS/MORPH's field mapping** — specifically how they get a prime
   field onto INT8 tensor units without losing exactness. Cheap, and it gates
   everything below.
3. **The wgpu fusion toy**, now aimed correctly: an MLE fold as a batched
   contraction next to the BFV NTT on one queue, measuring with and without
   the download.
4. **Then** the four-step NTT as GEMM, on whichever accelerator the profile
   says matters.
5. **Only then** the board — and if the profile says LDE/sumcheck-bound,
   **renting TPUs may dominate an FPGA entirely**, which is the cheaper
   version of our own thesis and the F2 plan was made without it on the table.
