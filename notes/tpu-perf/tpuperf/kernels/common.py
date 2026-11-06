import functools

import jax
import jax.numpy as jnp
from jax.experimental import pallas as pl
from jax.experimental.pallas import tpu as pltpu


def _mm_kernel(x_ref, w_ref, o_ref, acc_ref, *, nk):
    @pl.when(pl.program_id(2) == 0)
    def _():
        acc_ref[...] = jnp.zeros_like(acc_ref)

    acc_ref[...] += jnp.dot(x_ref[...], w_ref[...], preferred_element_type=jnp.int32)

    @pl.when(pl.program_id(2) == nk - 1)
    def _():
        o_ref[...] = acc_ref[...]


def mm_i8(x, w, bm=256, bn=256, bk=None, interpret=False):
    """Exact int8 x int8 -> int32 matmul on the MXU as a Pallas kernel. Grid (M/bm, N/bn, K/bk), K innermost
    and 'arbitrary', accumulator in VMEM scratch, output written once per (i, j) tile."""
    M, K = x.shape
    _, N = w.shape
    bk = bk or K
    bm, bn = min(bm, M), min(bn, N)
    assert M % bm == 0 and N % bn == 0 and K % bk == 0, (M, N, K, bm, bn, bk)
    nk = K // bk
    return pl.pallas_call(
        functools.partial(_mm_kernel, nk=nk),
        out_shape=jax.ShapeDtypeStruct((M, N), jnp.int32),
        grid=(M // bm, N // bn, nk),
        in_specs=[pl.BlockSpec((bm, bk), lambda i, j, k: (i, k)), pl.BlockSpec((bk, bn), lambda i, j, k: (k, j))],
        out_specs=pl.BlockSpec((bm, bn), lambda i, j, k: (i, j)),
        scratch_shapes=[pltpu.VMEM((bm, bn), jnp.int32)],
        compiler_params=pltpu.CompilerParams(dimension_semantics=("parallel", "parallel", "arbitrary")),
        interpret=interpret,
    )(x, w)


def carry(limbs):
    """Base-256 carry propagation on int32 limbs (arithmetic shift, so negative carries are right)."""
    out, c = [], 0
    for l in limbs:
        t = l + c
        out.append(t & 255)
        c = t >> 8
    return out, c


def reduce_limbs(z, mod):
    """z: list of nl int32 arrays, value V = sum_c 256^c z_c with |z_c| < 2^25 and |V| / mod < 2^22.
    Returns nl uint8-valued int32 limbs of V mod `mod` (canonical). VPU only, no 64-bit type:
    carry, float32 quotient estimate from the top three limbs and the carry (error <= 1), subtract qhat*mod
    limbwise, carry, then one conditional +mod and one conditional -mod."""
    import numpy as np
    nl = len(z)
    mb = list(mod.to_bytes(nl, "little"))
    L, h = carry(z)
    f32 = jnp.float32
    vf = h.astype(f32) * np.float32(2.0 ** (8 * nl))
    for c in (nl - 1, nl - 2, nl - 3):
        vf = vf + L[c].astype(f32) * np.float32(2.0 ** (8 * c))
    qhat = jnp.floor(vf * np.float32(1.0 / mod)).astype(jnp.int32)
    L, h2 = carry([L[c] - qhat * mb[c] for c in range(nl)] + [h])
    L, h = L[:nl], L[nl] + (h2 << 8)
    neg = h < 0
    A, _ = carry([L[c] + mb[c] for c in range(nl)])
    L = [jnp.where(neg, A[c], L[c]) for c in range(nl)]
    S, hs = carry([L[c] - mb[c] for c in range(nl)])
    ge = hs >= 0
    return [jnp.where(ge, S[c], L[c]) for c in range(nl)]
