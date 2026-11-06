# gptoss-int v0: an integer gpt-oss-20b, recomputed bit for bit

Initiative 8 (redirected); grounding in `notes/exact-recompute/GROUNDING.md`.

- `weights.py`: reads the shards with no framework, checks them against the registry's full-mode
  commitment (G0: all three `file_hash` equal), decodes MXFP4 to E2M1x2 integers and E8M0 exponents.
- `census_bf16.py` / `census_bf16.json`: per-row aligned significand width of the BF16 matrices
  (attention, router: p50 22-24 bits, max 34; lm_head max 39; embedding max 50). All enter exactly
  as int64 rows with one exponent each.
- `tables.py`: the pinned tables (YaRN rotary, softmax exp, the clamped-SwiGLU gate), built once in
  float64, digestable.
- `model.py`: the integer primitives (`rq`, the two-limb `rq2`, integer Newton `isqrt`), the exact
  weight rows, and the reference kernel `ExactF64`: float64 BLAS on 20-bit limbs, exact because every
  partial sum is an integer below 2^53. `InexactF32` is the falsifier.
- `jaxint.py`: the second kernel: int8 x int8 -> int32 dots (MXFP4 rows block by block), recombined
  in int64. This is the path a TPU MXU or a GPU's integer units execute.
- `layer.py`: a float64 gpt-oss layer (transformers semantics; fits the fixed points and measures
  fidelity) and the integer layer.
- `g1.py`: layer 0 on a real prompt (12 tokens of o200k_harmony).

## G1, 2026-11-06 (Mac, M-series CPU)

| kernel | a | q | k | v | o | x1 | m | router logits | x2 |
|---|---|---|---|---|---|---|---|---|---|
| numpy float64-BLAS limbs | = | = | = | = | = | = | = | = | = |
| JAX int8 limbs, XLA:CPU | = | = | = | = | = | = | = | = | = |
| numpy float32 BLAS (falsifier) | = | ≠ | ≠ | ≠ | ≠ | ≠ | ≠ | ≠ | ≠ |

"=" is the same SHA-256 over every int64 of that intermediate (`g1-*.json`). The two exact kernels
agree on all nine; the float32 kernel agrees only before the first matmul. Fidelity of the integer
layer against float64 (max relative error over the tensor): normed input 3.4e-5, stream after
attention 6.7e-4, after the MoE 5.5e-3. The elementwise integer code (`layer.py`) is shared by both
backends; what differs is the matmul route and the array library executing the integer ops.

Run: `uv run --no-project --with numpy --with tokenizers python g1.py numpy`, then
`... --with "jax[cpu]" python g1.py jax`.

## G2: the same integers on other silicon

| machine | kernel | all nine layer-0 digests equal to the Mac numpy reference |
|---|---|---|
| Mac (arm64), numpy float64 BLAS limbs | reference | (itself) |
| Mac, JAX 0.12.0.1 XLA:CPU, int8 limbs | `jaxint.Int8Mxu` | yes |
| bb2 (x86), numpy OpenBLAS limbs | `model.ExactF64` | yes |
| Kaggle Tesla T4, JAX 0.11.1 (cublasLt s8 x s8 -> s32), `runs/er-g2-layer0-t4-01` | `jaxint.Int8Mxu` | yes |
| the same T4, float32 dots (falsifier) | `jaxint.F32Dot` | no: `a`, `q`, `k` equal, from `v` on different |
| **G2-TPU**: GCP spot TPU v5e ("TPU v5 lite"), JAX 0.11.1, int8 dot as an s8 convolution on the MXU; run by the TPU-perf lane from this README at `1e10efb9`, result `notes/tpu-perf/results/gcp/tpuperf-s3/g2-tpu.json` (dev `38b1eb44`) | `jaxint.Int8Mxu` | yes; the int64 elementwise path raised nothing; fetch 477 MB in 11.5 s, kernel 66 s |
| the same TPU, float32 dots (falsifier) | `jaxint.F32Dot` | no: only `a` equal, from `q` on different |

Since G1 the attention dots also run as int8 limbs (q.k as 2 x 2 limbs, e.v as 3 x 2 because the exp
table reaches 2^15), so every product in the layer is an INT8-unit operation.

### G2 on a fresh machine (TPU VM, GPU box or CPU)

Needs Python 3.10+, network access to huggingface.co, about 1 GB of disk under `$GPTOSS_DIR`.

    python3 -m venv /tmp/er && . /tmp/er/bin/activate
    pip install "jax[tpu]==0.11.1" numpy        # GPU: "jax[cuda13]==0.11.1"; CPU: "jax[cpu]==0.11.1"
    cd research/exact_recompute_2026_11_06
    GPTOSS_DIR=/tmp/gptoss python3 g2_entry.py tpu      # or gpu, cpu: the backend it must find

It fetches layer 0's 31 byte ranges (477 MB) from `openai/gpt-oss-20b` at revision `6cee5e81…`,
refuses any range whose SHA-256 differs from `plan-layer0.json` (computed from shards whose file
hashes equal the registry's full-mode commitment), runs layer 0 with the int8-limb kernel and the
float32 falsifier, and writes `g2-<backend>.json`: `bit_identical`, per-intermediate equality with
`g1-numpy.json`, the compiled HLO of an int8 dot, timings. Nothing in the checkout is written.
JAX 0.11.1 is the version of the T4 and TPU v5e runs; a clean copy also ran it to
`bit_identical: true` on XLA:CPU.
