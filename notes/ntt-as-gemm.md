# NTT as GEMM — how CROSS/MORPH get a prime field onto INT8 tensor units, and whether it pays for us

2026-08-13, GPU/TENSOR BUILD lane. Written incrementally; §1–2 are the read,
§3+ are our own kernel and measurements.

---

## 1. The field mapping, answered: **BAT — Basis Aligned Transformation**

Source: **CROSS**, eprint 2026/160 (HPCA'26), §IV-A "Basis Aligned
Transformation", Eqs. (1)–(7), Alg. 2, Figs. 7–8. PDF locally at
`~/paperbin/hw-cross-he-on-tpuv6e-mit-hpca26-2026-160.pdf`.

**They do not lose exactness because nothing is ever approximated.** There is
no float anywhere in the path, no error term to argue about, and no rounding.
The entire trick is a *byte-radix change of basis on one operand, performed
offline*, which turns a high-precision modular multiply into an exact
small-integer matrix product whose accumulator provably cannot overflow.

### 1.1 The derivation, in their notation

For `a × b mod q` where **`a` is preknown** (twiddle factors, evaluation keys,
basis-switch constants) and `b` is runtime data, both `K` bytes wide:

```
a·b mod q =  ( Σ_{i<K}  a · (b_i · 2^{8i}) ) mod q            (1)  split b into bytes
          =  ( Σ_{i<K}  (a·2^{8i} mod q) · b_i ) mod q        (2)  push the shift onto a
          =  ( Σ_{i<K}  a_i · b_i ) mod q                     (3)  a_i := a·2^{8i} mod q, OFFLINE
          =  ( Σ_i ( Σ_j a_{j,i} 2^{8j} ) · b_i ) mod q       (4)  byte-decompose each a_i
          =  ( Σ_j ( Σ_i a_{j,i} · b_i ) · 2^{8j} ) mod q     (5)  swap: inner sum is an 8-bit MATMUL
          =  ( Σ_j psum_j · 2^{8j} ) mod q                    (7)  psum_j is 16 + log2(K) bits
```

Eq. (6) is the punchline in matrix form: **one scalar modular multiply becomes
a `K×K` byte matrix times a `K×1` byte vector.** The `K×K` matrix
`[a_{j,i}]` is *entirely offline* — it is byte `j` of `(a·2^{8i} mod q)`.

Quoting the paper directly on the offline half (Eq. 2 annotation):

> `calculated offline as a_i (K bytes)`

and on the shape:

> "BAT offline applies modular reduction to preknown K-byte parameter `a` in
> Eq. (1), converting it into Eq. (3). BAT then schedules post converted
> computation as a low-precision matrix multiplication with a carry
> propagation. This conversion takes O(N) time for converting a matrix with
> O(N) elements."

### 1.2 The exactness/overflow argument — this is the whole safety case

- Every entry of the `K×K` matrix and the `K×1` vector is a **byte**, `< 2^8`.
- Every product is `< 2^16`. **INT8 × INT8 → exact in INT16.**
- The accumulator sums over the expanded reduction dimension. CROSS states the
  bound in Fig. 8 as the output element width:

  > "The resulting element has `2·bp + log2(KV)` bits, accounting for precision
  > expansion during reduction (Alg. 2)."

  with `bp` = MXU bit precision (8) and `KV` the expanded reduction dimension.
  For the scalar case (Eq. 7) that is `16 + log2(K)` bits.
- **So the INT32 accumulator is safe with ~14 bits to spare at any reduction
  dimension a TPU tile will ever have.** For `bp=8` you would need
  `KV > 2^15 = 32768` before an INT32 accumulator could overflow.

There is no exactness *argument* to make because there is no approximation.
The BF16/FP32 path our own doc floated as the alternative is **not what they
do** — see §3.2 for the measured reason: FP32 gives a 256-element contraction
limit where INT32 gives 32768, and the failure is silent.

### 1.3 What it costs — the number that decides everything

`K = ⌈log2(q) / bp⌉`. CROSS runs `log2 q = 28`, `bp = 8`, so **`K = 4`**.

A high-precision `(H, V, W)`-ModMatMul becomes an 8-bit `(KH, KV, W)`-ModMatMul
(Alg. 2 / Fig. 8). Preknown operand expands in **both** dimensions
(`H→KH`, `V→KV`); runtime operand expands in **one** (`V→KV`). So:

> **BAT costs `K²` times the MACs, and buys them at the INT8 rate instead of
> the INT32 rate.**

At `K=4` that is **16× the multiply-accumulates**. CROSS reports the resulting
end-to-end win as **"≤ 7.16× speedup on one tensor core"** — which is exactly
`~100× rate ÷ 16× work`, and confirms the model.

⚠ **The asymmetry is load-bearing: one operand must be preknown.** Eq. (2)→(3)
only works because `a_i = a·2^{8i} mod q` is precomputed. A GEMM where *both*
operands are runtime data does not get this treatment — you would need the
`2^{8i}` reduction at runtime, which is the thing you were trying to avoid.
**For an NTT this is free: the twiddle matrix is the preknown operand.** For a
sumcheck/MLE fold, where both operands are witness data, **it is not free, and
this is the first place our own port would break.**

### 1.4 Where the reduction happens

**Outside the GEMM, on the vector unit.** Fig. 10 row 3 is explicit — the
pipeline is `uint8 MatMul (MXU) → uint32 Montgomery Reduction (VPU) → uint32
elementwise twiddle (VPU) → uint8 MatMul (MXU) → uint32 reduction (VPU)`.

They benchmarked the choice (§ Fig. 13): Barrett, Montgomery, Shoup, and
"BAT Lazy". Verdict quoted:

> "Our results indicate that Montgomery reduction is..." [best] — with
> **"VecModMul: Montgomery reduction achieves a 1.42×"** improvement.

Their Alg. 1 is an **optimized 64→32-bit Montgomery REDC built from 16-bit
primitives** — `q_lo = q mod 2^16`, `q_hi = ⌊q/2^16⌋`, four 16-bit partial
products, output in `[0, 2q)`. **That is structurally the same object as our
existing `mont_mul` in `fhegg-fhe/src/shaders/bfv_ntt.wgsl`** (three-limb
radix-2^16, `R = 2^48`, output reduced by one conditional subtraction). Our
kernel already made the same call for the same reason.

### 1.5 The NTT decomposition they actually use — **three-step, not four-step**

CROSS §IV "layout-invariant 3-step negacyclic NTT" (Fig. 10). The conventional
four-step has an explicit transpose and a bit-reverse; CROSS's second
contribution, **MAT (Memory Aligned Transformation)**, kills both by folding
the permutation into the *preknown twiddle matrices at compile time*:

> "MAT leverages the insight that any reordering operation on a one-dimensional
> vector can be represented as multiplication with a 'permutation matrix'…
> By applying [it offline] … Compute Only!"

Their stated formula:

```
( (P_π(R) @ TF_R×R) @ a_R×C ) · (P_π(R) @ TF^R_R×C) @ (TF^C_C×C @ P_π(C))
  \____ offline row perm ___/    \___ offline row perm ___/  \__ offline col perm __/
```

`@` = matmul, `·` = elementwise, `P` = bit-reversal permutation matrix.
**Steps 1 and 3 are the MXU matmuls; step 2 (the twiddle) is the VPU.** When
`R = C` only one twiddle matrix is needed.

Complexity, in their words:

> "The resulting algorithm achieves an effective computational complexity of
> `O(N√N)` … Although this complexity is higher than the radix-2 Cooley-Tukey
> NTT (`O(N log N)`), the dramatic throughput advantage of MXU results in
> superior overall NTT throughput and energy efficiency, making TPUs the SoTA
> throughput engine for NTT."

### 1.6 Their parameters, and the one that matters for us

| | CROSS |
|---|---|
| modulus | `log2 q = 28`, RNS limbs of a 1728-bit `Q` (Set D: `log2 Q = 1904`, `L = 51`) |
| `N` | `2^16` default (Sets A–D: `2^12`–`2^16`) |
| `(R, C)` | `{(128,512), (256,256), (512,128)}` — **not `√N`**; `R=128` is forced by the MXU lane count |
| storage | "Each 28-bit coefficient is stored in a 32-bit integer, and decomposed into four 8-bit chunks to match MXU operand precision" |
| `K` | 4 |
| verified against | "verified against OpenFHE's leveled ckksrns, achieving the same accuracy and generality" |

⚠ **Why `log2 q < 32`, stated as a hardware constraint, not a security one:**

> "Given TPU's micro-architecture is mainly designed for optimizing performance
> of low-precision integer (up-to 32 bits) and it implements 32-bit registers,
> we choose the security parameter with `log2 q < 32` for better performance.
> For security parameters requiring moduli precision exceeding 32 bits, we
> employ double rescaling to discard two sub-moduli (`log2 q < 32`) per level,
> doubling the number of constituent moduli."

**They redesigned the FHE parameter set around the accelerator's word size.**
That is the real lesson and it is not a kernel detail.

### 1.7 ⚑ The direct read for our field

**BabyBear is 31 bits ⇒ `K = ⌈31/8⌉ = 4` — the same `K` CROSS runs at.** The
arithmetic transfers with no modification at all: `a_i = a·2^{8i} mod p` for
`i<4`, a `4×4` byte matrix per preknown scalar, `psum` at `16 + log2(KV)` bits,
INT32-safe to `KV = 32768`.

Our deployed FHE moduli are wider — `FOLD_MODULI = [0xffffee001, 0xffffc4001,
0x1ffffe0001]` = 36, 36, 37 bits (`fhegg-core/src/bfv_lean.rs:72`) — giving
**`K = 5`, hence `K² = 25×` the MACs.** CROSS would tell us to re-plan the RNS
basis to `q < 2^32` before targeting a tensor unit. That is a real, cheap,
greenfield change and it is the single highest-leverage parameter decision on
this thread.

---

*§2 (MORPH/MoMA) and §3+ (our kernel and measurements) follow.*

---

## 2. MORPH and MoMA — one confirms, one is a premise error

### 2.1 MoMA (CGO'25, arXiv 2501.07535) — **does not use tensor units at all**

Correcting the brief: "Tensor Core" appears in MoMA only inside GPU product
names and one bibliography entry. Its compute units are scalar integer ALUs; it
says so about its own competitor — *"GZKP exploits all the floating-point
processing units on GPU. However, MoMA outperforms GZKP on smaller sizes, even
when using only integer processing units"* (§5.3) — and tensor units are listed
as future work (§7): *"we plan to investigate whether MoMA can work effectively
on AI/ML-specialized hardware."*

What MoMA actually is: a SPIRAL rewrite system that recursively splits wide
integers into **machine words at radix 2^64** (512 → 2×256 → 4×128 → 8×64),
with **Barrett reduction inside every butterfly** and a **plain radix-2
Cooley-Tukey NTT** — no four-step. Its exactness margin is a modulus of `k−4`
bits in a `k`-bit word (so 60/124/252/380/764-bit moduli). Smallest
configuration shown is a 60-bit single-word modulus, which is ordinary scalar
Barrett. **Nothing here transfers to a 31-bit prime on a matrix engine**, and it
should be dropped from the tensor thread. Code: `~/dev/zkml-research/vendor/moma`.

### 2.2 MORPH (DAC'26, arXiv 2604.17808) — same group, and the **GEMM is the reduction**

MORPH is the ZK sibling of CROSS and inherits BAT and the 3-step NTT from it by
citation. Its own contribution is a *different* mapping, because ZK moduli are
**256/377/753 bits** (§2.3.1), not 28:

1. Embed the prime field in a **non-prime RNS ring** `F_Q` with `Q > M²`
   (§3.2.2) so *"the product of their RNS vectors never overflows Q, avoiding a
   true reduction by Q. Hence, the multiplication is fully decomposed into
   independent 32-bit limb multiplications."*
2. The **multiply is elementwise 32-bit Montgomery on the vector unit**, not a
   GEMM.
3. The **INT8 GEMM is the base conversion** `F_Q → mod M → F_P`, with CRT
   reconstruction, the mod-M reduction and the output re-decomposition all
   folded offline into a precomputed 4-D uint8 tensor `E`, contracted by one
   einsum over both the residue index and the byte index. Exact quotient
   correction is Simon's reduction (Langowski–Devadas, eprint 2025/1068).
   *"It also removes all carry-propagation from the critical path."*

Accumulator: **uint32**, verified in their code
(`finite_field_context.py:724`, `number_theory_transform_context.py:139` both
pass `preferred_element_type=jnp.uint32`), with the same headroom argument —
`2·bp + log2(KV)` bits, so `KV ≤ 2^16` terms.

⚑ **The direct read: MORPH's layer-1 embedding is pointless for us.** It exists
because a 753-bit prime does not fit a machine word. **BabyBear already fits one
32-bit word**, so we skip straight to CROSS's BAT — one word, four unsigned
bytes, uint8 GEMM against BAT-folded twiddles, uint32 accumulate, Montgomery
epilogue. Neither paper says anything about 31-bit primes; CROSS at `log2 q = 28`
is the closest published point and it is structurally identical to ours.

**MORPH's real gift to us is the 5-step NTT** (§3.3.2, Eq. 1): *"replaces the
row-wise R-degree NTT with a 3-step NTT over (R₁,R₂,C), where R = R₁·R₂"*,
cutting the MXU span by `N^{1/4}`. See §5 — this is the single most important
structural fact on the whole thread. Code:
`~/dev/zkml-research/vendor/morph` (`NTT3Step`, `NTT5Step`, `NTT7Step`,
`basis_aligned_transformation`, `matmul_bat_einsum`).

---

## 3. What we built

Two files, both new, both in the shared tree:

- `breadstuffs/fhegg-fhe/src/shaders/ntt_four_step.wgsl`
- `breadstuffs/fhegg-fhe/src/bin/ntt_four_step_bench.rs`

A four-step negacyclic NTT at `N = R·C`, in **two arithmetic dialects over one
set of tables and one boundary**:

- **`mont`** — one three-limb radix-2^16 Montgomery modmul per MAC. This is
  literally the `mont_mul` from the deployed `shaders/bfv_ntt.wgsl`, so the
  comparison isolates the *decomposition* from the *arithmetic*.
- **`bat`** — CROSS's Basis Aligned Transformation, as derived in §1.

Residues are kept **plain**; every twiddle table is uploaded in Montgomery form,
so `mont_mul(plain, mont) = plain·w` exactly and BAT's contraction yields
`a·w_mont mod q`, closed by one bare `redc`. Two implementation notes worth
keeping:

- ⚑ **The runtime operand needs no byte-decomposition at all.** A residue stored
  as `(lo, hi)` *is* its own little-endian byte packing: bytes 0–3 are `lo`, byte
  4 is `hi & 0xff`. So the `K`-byte split that CROSS draws as a preprocessing
  step is free on any 32-bit lane machine.
- **Table layout is worth ~2×.** The obvious entry-major packing (all `K·KW`
  words of one twiddle contiguous) strides GPU lanes by `K·KW`. Plane-major —
  `bat[((j·KW + w)·D + i₁)·D + i₂]` — makes lanes that differ only in the fast
  output index read adjacent words. Measured 30.98 → 20.58 ms at batch 128.

### 3.1 Correctness — bit-exact, four independent ways

```
== CPU: the decomposition itself ==
  N=   64  (R,C)=(8,8)    four-step == naive O(N^2) DFT   OK
  N=  256  (R,C)=(16,16)  four-step == naive O(N^2) DFT   OK
  N=  256  (R,C)=(8,32)   four-step == naive O(N^2) DFT   OK
  N=  256  (R,C)=(32,8)   four-step == naive O(N^2) DFT   OK

== GPU: N=4096, (R,C)=(64,64), deployed FOLD_MODULI, Apple M2 Max (Metal) ==
  K = 5 limbs (q up to 37 bits), k_words = 2
  mont: negacyclic product == schoolbook, all 3 moduli, N=4096   OK
  mont: bit-exact vs deployed `multiply_rns_cpu`                 OK
  mont: bit-exact vs deployed radix-2 GPU NTT                    OK
  bat : negacyclic product == schoolbook, all 3 moduli, N=4096   OK
  bat : bit-exact vs deployed `multiply_rns_cpu`                 OK
  bat : bit-exact vs deployed radix-2 GPU NTT                    OK

== GPU: BabyBear (the prover field, 31 bits, K=4) ==
  mont: negacyclic product == schoolbook, N=4096   OK
  bat : negacyclic product == schoolbook, N=4096   OK
```

The chain is: schoolbook `O(N²)` negacyclic product → deployed
`multiply_rns_cpu` → deployed radix-2 wgpu kernel → our four-step, in both
dialects, over both the deployed FHE moduli and BabyBear. Nothing is compared
only against itself.

### 3.2 ⚑ The FP32 exactness boundary — and it is razor thin

An FP32 (or BF16-accumulating-in-FP32) tensor path is exact only while every
partial sum stays an integer `< 2^24`. Computed, not assumed:

| field | K | contraction C | max partial sum | verdict |
|---|---|---|---|---|
| BabyBear (31b) | 4 | **64** | 16,646,400 | **< 2^24 — EXACT** (0.78% margin) |
| BabyBear (31b) | 4 | 128 | 33,292,800 | ≥ 2^24 — UNSOUND |
| BabyBear (31b) | 4 | 256 | 66,585,600 | ≥ 2^24 — UNSOUND |
| FOLD q2 (37b) | 5 | 64 | 20,808,000 | ≥ 2^24 — **UNSOUND** |

**BabyBear at exactly `(R,C) = (64,64)` — i.e. `√N` at `N = 4096` — is the
largest exact FP32 BAT tile there is, with 0.78% of headroom.** One step up in
`C` and the accumulator silently rounds. Our deployed 37-bit FHE moduli are
already outside the budget at any useful tile.

This is why CROSS uses INT8→INT32 and not floats: **INT32 gives `KV ≤ 2^16`
terms of headroom where FP32 gives `KV ≤ 256`.** Anyone reaching for a BF16/FP32
tensor path here inherits a 256-element contraction limit, and the failure is
silent.

### 3.3 Measured — Apple M2 Max, N=4096, 3 RNS rows, best of 5

```
 batch |    up+down | radix-2 GPU |  4step mont |   4step BAT |   mont/BAT
     8 |     1.55ms |      4.62ms |      7.50ms |      2.58ms |      2.90x
    32 |     2.35ms |      4.43ms |     15.15ms |      4.84ms |      3.13x
   128 |     5.49ms |     12.90ms |     57.09ms |     18.69ms |      3.05x
   512 |    43.31ms |     51.45ms |    265.51ms |    290.75ms |      0.91x
```

`radix-2 GPU` is the deployed `RnsNttEngine::forward_odd_batch`, whose API is
host-in/host-out and therefore includes a round trip; the `up+down` column
measures that round trip alone so the reader can subtract it. The two four-step
columns are device-resident.

**Three readings, in order of importance:**

1. ⚑ **BAT beats three-limb Montgomery by 3.0× while issuing 40 byte-MACs per
   modmul — on hardware with no INT8 unit whatsoever.** That inverts to: **one
   Montgomery modmul in WGSL costs ~122 byte-MACs**, where the instruction count
   says 21 u32 multiplies. The remaining **~5.8× is the emulation tax** —
   carry chains, a 7-limb scratch array, register pressure. The tax is the
   thing a matrix engine is being asked to beat, and it is much larger than the
   multiply count suggests.

2. **The four-step is competitive on pass count, not on MACs.** Our four-step is
   4 dispatches (twist, GEMM, twiddle, GEMM); the radix-2 kernel is 14 (twist,
   bit-reverse, 12 stages), each a full read-modify-write of the array. At batch
   128, radix-2 costs 12.90 ms of which ~5.5 ms is the round trip, so ~7.4 ms of
   compute against BAT's 18.69 ms — **2.5× slower while doing 853× the
   arithmetic.** That 340× discrepancy is exactly CROSS's MAT argument showing up
   in our own numbers: **the radix-2 GPU NTT is bandwidth-bound and the four-step
   is compute-bound**, so the four-step gets most of the way back on memory
   traffic before any matrix engine is involved.

3. **Batch 512 falls off a cliff** (18.69 → 290.75 ms for 4× the data). Working
   set is 50 MB of data plus 50 MB of scratch against the M2 Max's 48 MB
   system-level cache. The four-step needs its full `R×C` tile plus a scratch
   copy resident; radix-2 degrades gracefully (51.45 ms). **A blocked/tiled
   four-step that keeps one tile in threadgroup memory is the obvious next
   kernel and we did not write it** — the numbers above are for an untiled,
   one-thread-per-output GEMM, and understate the four-step accordingly.

### 3.4 The only real matrix engine on this box: AMX

The M2 Max GPU has **no matrix unit and no DP4a**. Checked at source rather
than assumed: `dot4I8Packed` does not exist in naga 24 (which `fhegg-fhe` pins)
at all, and in naga 26/27 the **Metal backend lowers it to four separate
`packed_char4` element products summed** (`naga-26.0.0/src/back/msl/writer.rs:2318`)
— a source-level polyfill, not an instruction. So the hand-rolled `dot4u8` in our
shader is what this hardware would run either way; nothing was left on the table.

What *is* reachable is **AMX**, the M-series matrix coprocessor, through
Accelerate's `cblas_sgemm`. Using the FP32-exact budget of §3.2:

```
BabyBear (31b): (64 x 256) @ (256 x 256) = 4.19 MMAC -> 142 GMAC/s  [exact, 16646400 < 2^24]
FOLD q2 (37b):  (64 x 320) @ (320 x 320) = 6.55 MMAC -> 145 GMAC/s  [NOT EXACT in fp32]
AMX peak probe  256^3:  142 GMAC/s
AMX peak probe 1024^3:  487 GMAC/s
```

against our BAT kernel on the GPU at batch 128: 384 transforms × 20.97 M
byte-MACs / 18.69 ms = **431 GMAC/s**.

⚑ **AMX's peak (487 GMAC/s) is within 13% of what the GPU already achieves by
hand, and at the tile size BAT actually wants it delivers 142 — 3.4× below its
own peak and 3× below the GPU.** The BAT tile (`64 × KC`) is too small and too
skinny to saturate a matrix unit. **On this box the matrix engine is not a
different rate tier; it is the same tier with a worse aspect ratio.** That is a
hardware limit and it is why the verdict below is derived rather than measured
end-to-end.

---

## 4. ⚑ The structural fact: four-step vs radix-2 is not a binary, it is a knob

This reframes the whole question and it is the most useful thing the lane found
after the BAT derivation.

Split `N` into `m` factors of `N^{1/m}` each. The transform becomes `m` rounds of
dense `N^{1/m} × N^{1/m}` GEMMs plus `m−1` twiddle passes, costing
`m · N^{1+1/m}` modular multiplies:

| `m` | name | tile | MACs | that is |
|---|---|---|---|---|
| 2 | four-step / CROSS 3-step | `√N` | `2N^{1.5}` | the brief's `O(n^1.5)` |
| 3 | **MORPH 5-step** | `N^{1/3}` | `3N^{4/3}` | |
| 4 | **MORPH 7-step** | `N^{1/4}` | `4N^{1.25}` | |
| … | … | … | … | |
| `log₂N` | radix-2 Cooley-Tukey | 2 | `N log N` | the classical NTT |

**Radix-2 is the `m = log₂N` member of the same family.** The four-step is not a
different algorithm; it is the *coarsest* member, chosen because a large dense
tile is what a systolic array can saturate. **`m` is a dial trading arithmetic
against tile size, and you set it to the largest tile your matrix engine
saturates and no larger.**

Computed requirement — the INT8-MAC-to-modmul rate ratio a matrix engine must
clear for BAT to win, for BabyBear (`K=4`, 16 byte-MACs per modmul):

| | `m=2` (tile `√N`) | `m=3` | `m=4` |
|---|---|---|---|
| `N=2^12` | **341×** (tile 64) | 128× (tile 16) | 85× (tile 8) |
| `N=2^16` | **1024×** (tile 256) | 242× (tile 40) | 128× (tile 16) |
| `N=2^20` | **3277×** (tile 1024) | 488× (tile 102) | 205× (tile 32) |

(Against a *dedicated* modmul datapath — one modmul per slot. Against an
*emulated* modmul, divide by ~21, the u32-multiply count of a three-limb REDC;
our own measurement in §3.3 says the effective divisor on a GPU is ~122, not 21.
The formula assumes dense tiles and degrades below tile ≈ 8, where most twiddles
become trivial.)

⚑ **Two things fall out immediately.**

1. **The requirement grows as `√N / log N` at `m=2`.** The four-step's case gets
   *worse* with size, and `N = 2^16` — CROSS's own operating point — already
   needs 1024×. Our LDE sizes are `2^20`+, where `m=2` needs 3277×. **The
   four-step alone does not survive to our transform sizes; MORPH's 5-step is
   not a refinement, it is the thing that makes the approach viable at scale.**
2. **TPU v6e's MXU is 256×256, and `√N` at `N=2^16` is exactly 256.** The MXU
   width and CROSS's `(R,C)` choice are the same number for the same reason.
   Read the other way: **the tile a given accelerator can saturate *determines*
   `m`, which determines the MAC count, which determines whether you win.**

---

## 5. Verdict: are tensor units worth targeting for our field?

### 5.1 The field mapping — settled, and it transfers with no modification

**BabyBear is 31 bits, so `K = ⌈31/8⌉ = 4` — the same `K` CROSS runs at
`log2 q = 28`.** One 32-bit word, four unsigned bytes, `KW = 1` so the packing is
perfect with **zero wasted lanes**, uint8 GEMM against BAT-folded twiddles,
uint32 accumulate with 2^15 terms of headroom, one Montgomery epilogue. We
implemented it and it is bit-exact. **There is no research risk left in the
arithmetic.** MORPH's `F_Q` embedding is for 256–753-bit primes and is
irrelevant to us; MoMA is not a tensor-unit paper at all.

⚠ **But our deployed FHE moduli are the wrong shape.** `FOLD_MODULI` is 36/36/37
bits, giving `K=5`, `KW=2` — **25× the MACs with 38% of the issued byte-lanes
wasted on padding, and no exact FP32 path at any tile.** CROSS hit this and
their answer was to *change the parameters*: *"we choose the security parameter
with `log2 q < 32` for better performance … we employ double rescaling to
discard two sub-moduli per level, doubling the number of constituent moduli."*
**Re-planning the RNS basis to `q < 2^32` is the single highest-leverage
parameter change on this thread**, it is greenfield, and it costs a re-emit.

### 5.2 Whether it pays — the honest answer is conditional, and here is the condition

**Not on anything we own.** Measured: the M2 Max GPU has no matrix unit and no
DP4a (`dot4I8Packed` is a four-multiply polyfill in naga's Metal backend, and
absent entirely from the wgpu 24 this crate pins); AMX's *peak* is 487 GMAC/s
against 431 GMAC/s our hand-rolled BAT kernel already gets on the GPU, and at
the tile BAT actually wants AMX delivers 142. **On this box the matrix engine is
the same rate tier with a worse aspect ratio.** No NVIDIA hardware was reachable
(hbox: RX 6700 XT, persvati: Radeon 890M, `vast` refused the connection), so the
WMMA/DP4a numbers below are derived, not measured, and are labelled as such.

The condition, stated as a break-even rather than a guess:

> **BAT on a matrix engine beats a radix-2 NTT on a dedicated modmul datapath
> iff `rate_int8 / rate_modmul > m · N^{1/m} · K² · 2 / log₂N`.**

Plugging in the published numbers, and flagging each input:

| target | INT8-vs-scalar ratio | needed at `N=2^16` | verdict |
|---|---|---|---|
| TPU v6e MXU vs its own VPU | ~100× *(CROSS, "∼O(100) times higher throughput than its VPU")* | 49× at `m=2` (emulated framing) | **wins, ~2×** — consistent with CROSS's measured "≤7.16×" on the wider BConv |
| GPU with DP4a (RDNA2, SM61+) | 4× *(one instruction, four MACs — derived)* | 49× | **loses decisively** |
| GPU with INT8 WMMA (RDNA3, Ampere+) | ~8–32× *(derived from published INT8-vs-INT32 tiers)* | 49× | **loses at `m=2`; marginal at `m=3` (11.5×)** |
| Apple M2 Max | **1×, measured** | 49× | **loses; no INT8 tier exists** |

### 5.3 TPU-rental versus an FPGA — the number that actually decides it

This is what the pillar wanted priced. Take a TPU v6e-8 at ~500 T INT8-MAC/s
(CROSS Table III lists TPU INT8 at `O(1000)` TOPS). Then a rented TPU beats a
board **iff the board's dedicated modmul rate is below `500 T / requirement`**:

| | `m=2` | `m=3` (MORPH 5-step) |
|---|---|---|
| `N=2^16` | FPGA must exceed **0.49 T modmul/s** | FPGA must exceed **2.1 T modmul/s** |
| `N=2^20` | FPGA must exceed **0.15 T modmul/s** | FPGA must exceed **1.0 T modmul/s** |

A VU47P-class part has ~9k DSP58s; a 31-bit Montgomery modmul is ~2–4 DSPs, so
**~2–4k modmul units at ~300 MHz ≈ 0.6–1.2 T modmul/s.** Against that:

- **At `m=2`, `N=2^20` (our LDE size): the FPGA wins outright** — it needs only
  0.15 T and delivers ~1 T. The four-step's `√N` penalty has eaten the TPU's
  entire rate advantage.
- **At `m=3`, `N=2^20`: it is a coin flip** — the board needs ~1.0 T and lands at
  0.6–1.2 T. **The decision is inside the error bars of the DSP-per-modmul
  estimate**, which is a real, cheap thing to nail down and nobody has.
- **At `N=2^16` and below, the TPU wins comfortably at either `m`.**

⚠ So the pillar's framing — *"renting TPUs at 451× perf/W with no RTL may
dominate a $9.5k board"* — **holds at CROSS's transform sizes and does not
obviously survive to ours.** The 451×/1.43× figures are FHE numbers at `N=2^16`
with `log2 q=28`; **quoting them at `N=2^20` is quoting the flattering member of
a pair.** Perf/**watt** is a separate axis and the TPU very likely still wins it;
perf/**second** at `N=2^20` is where the FPGA is live.

### 5.4 The one place this breaks that nobody has flagged

⚑ **BAT requires one operand to be preknown.** That is free for an NTT (twiddles
are compile-time) and it is **not free for the other two GEMM-shaped phases in
our prover.** An MLE fold and a sumcheck round contract *two runtime witness
tensors*; `a_i = a·2^{8i} mod q` cannot be precomputed for either. So:

- **The LDE/NTT phase ports to a tensor unit by BAT with no new mathematics.**
- **The sumcheck/MLE-fold phase does not**, even though `PHASES-AND-TENSOR.md`
  §2 groups it with the NTT as "also GEMM-shaped". It is GEMM-shaped and it is
  *not BAT-shaped*, and those are different claims. Getting a two-runtime-operand
  modular GEMM onto INT8 exactly is an open problem in both papers we read —
  MORPH's answer for its own multiply is to *not* use the GEMM (elementwise
  Montgomery on the VPU) and put only the *reduction* on the MXU.

**Recommended next step, cheapest-first, in the order the numbers imply:**

1. **Re-plan the RNS basis to `q < 2^32`.** `K` 5→4, MACs 25×→16×, lane waste
   38%→0%, and the FP32 path becomes available at `C=64`. Greenfield, costs a
   re-emit, and it is a precondition for everything else here.
2. **Implement `m=3` (MORPH's 5-step) before benchmarking anything on rented
   silicon.** At `N=2^20` it is a 6.7× MAC reduction and it is the difference
   between "the FPGA wins outright" and "it is a coin flip."
3. **Nail the DSP-per-modmul figure for a 31-bit Montgomery multiplier on a
   VU47P.** One synthesis run decides §5.3, and the whole board-versus-rental
   question currently rests on a range.
4. **Tile the four-step kernel** (threadgroup-resident `R×C` block). Our batch-512
   cliff is a cache artifact, and the numbers in §3.3 understate the four-step by
   an unknown factor until it is fixed.
5. **Do not port the MLE fold by analogy.** §5.4 — it is not BAT-shaped, and
   assuming it is would be the expensive mistake here.
