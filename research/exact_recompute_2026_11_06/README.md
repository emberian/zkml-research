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
