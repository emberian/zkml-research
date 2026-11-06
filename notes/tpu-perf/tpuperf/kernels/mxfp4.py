"""Workload 1: the exact MXFP4 expert matmul of gpt-oss-20b (W4A8) on the int8 MXU.

Math (docs/mx-formats.md; initiative 8 GROUNDING): weight row n has E2M1 codes over K and one E8M0 exponent
e[n, b] per 32-block. Doubled E2M1 values w2 are integers in [-12, 12]. With emin[n] = min_b e[n, b] and
s = e - emin in [0, 8] (gpt-oss: p50 2, p99 3, max 8), the dot product is exactly
    y[t, n] * 2^(emin[n] - 128),   Y[t, n] = sum_k x[t, k] * (w2[n, k] << s[n, k/32])
with x the int8 fixed-point activation. Y is what this kernel computes, bit-exactly.

Prefold (offline, once per weight load): Wp = w2 << s. A column with spread <= 3 has |Wp| <= 96 and is one
int8 limb. A wide column (spread 4..8, ~0.08% of gpt-oss rows) is Wp = 128*hi + lo with lo in [-64, 63],
hi in [-24, 24]. Wide columns are permuted to the end; the main matmul uses lo for them, and one extra
[K, 128] matmul adds 128*hi to the last 128 output columns. Output columns stay in the permuted order
(the inverse permutation folds into the next layer's K order for free). Exactness: |Y| <= 128*3072*2880 <
2^31 and every partial sum is below that.
"""
import functools

import jax
import jax.numpy as jnp
import numpy as np

from .common import mm_i8

E2M1_X2 = np.array([0, 1, 2, 3, 4, 6, 8, 12, 0, -1, -2, -3, -4, -6, -8, -12], np.int64)


def synth_weights(rng, N, K, n_wide_min=1):
    codes = rng.integers(0, 16, (N, K)).astype(np.uint8)
    u = rng.random(N)
    spread = np.where(u < 0.9463, rng.integers(0, 3, N), np.where(u < 0.9992, 3, rng.integers(4, 9, N)))
    spread[:n_wide_min] = 8
    base = rng.integers(115, 125, N)
    nb = K // 32
    e = base[:, None] + (rng.random((N, nb)) * (spread[:, None] + 1)).astype(np.int64)
    e[:, 0] = base
    e[np.arange(N), rng.integers(1, nb, N)] = base + spread
    return codes, e.astype(np.int64)


def prefold(codes, e):
    N, K = codes.shape
    w2 = E2M1_X2[codes]
    s = e - e.min(axis=1, keepdims=True)
    wp = w2 * (np.int64(1) << np.repeat(s, 32, axis=1))
    wide = s.max(axis=1) > 3
    nw = int(wide.sum())
    assert nw <= 128 and N % 128 == 0 and N >= 128, (nw, N)
    order = np.concatenate([np.flatnonzero(~wide), np.flatnonzero(wide)])
    wpp = wp[order]                                   # [N, K] permuted, wide last
    lo = ((wpp + 64) % 128) - 64
    hi = (wpp - lo) // 128
    is_wide = np.zeros(N, bool)
    is_wide[N - nw:] = True
    w_main = np.where(is_wide[:, None], lo, wpp)
    hi = np.where(is_wide[:, None], hi, 0)
    assert np.abs(w_main).max() <= 127 and np.abs(hi).max() <= 24
    W1 = np.ascontiguousarray(w_main.T).astype(np.int8)          # [K, N]
    Whi = np.ascontiguousarray(hi[N - 128:].T).astype(np.int8)   # [K, 128], last 128 output columns
    return W1, Whi, order, w2, s


def inputs(rng, T, K, N):
    codes, e = synth_weights(rng, N, K)
    W1, Whi, order, w2, s = prefold(codes, e)
    x = rng.integers(-128, 128, (T, K)).astype(np.int8)
    return (x, W1, Whi), dict(x=x, w2=w2, s=s, order=order)


def ref(rd, T, K, N):
    wp = rd["w2"] * (np.int64(1) << np.repeat(rd["s"], 32, axis=1))       # exact, int64
    Y = rd["x"].astype(np.int64) @ wp.T                                      # [T, N] original order
    return Y[:, rd["order"]]


def impl(T, K, N, bm=None, bn=None, interpret=False, backend="pallas"):
    bm = bm or min(T, 512)
    bn = bn or (512 if N % 512 == 0 else 128)

    def f(x, W1, Whi):
        if backend == "xla":
            y = jnp.dot(x, W1, preferred_element_type=jnp.int32)
            z = jnp.dot(x, Whi, preferred_element_type=jnp.int32)
        else:
            y = mm_i8(x, W1, bm=bm, bn=bn, interpret=interpret)
            z = mm_i8(x, Whi, bm=bm, bn=128, interpret=interpret)
        return y.at[:, N - 128:].add(z * 128)
    return f


def count(T, K, N):
    """The ideal: one int8 MAC per (t, n, k), one byte per prefolded weight, int32 out."""
    def f(x, W1):
        return jnp.dot(x, W1, preferred_element_type=jnp.int32)
    return f, [((T, K), jnp.int8), ((K, N), jnp.int8)]


def arg_specs(T, K, N):
    return [((T, K), jnp.int8), ((K, N), jnp.int8), ((K, 128), jnp.int8)]


KERNELS = [dict(
    name="mxfp4_w4a8",
    module=__name__,
    cfgs={
        "mac": dict(T=128, K=2880, N=768),                     # Mac exactness (interpret mode)
        "gateup_T256": dict(T=256, K=2880, N=5760),             # gpt-oss-20b MLP1, ~256 tokens per expert
        "gateup_T2048": dict(T=2048, K=2880, N=5760),
        "down_T2048": dict(T=2048, K=2880, N=2944),             # MLP2, N padded 2880 -> 23*128
    },
    inputs=inputs, ref=ref, impl=impl, count=count, arg_specs=arg_specs,
)]


# ---------------------------------------------------------------------------------------------------------
# Packed variant for small T (HBM-bound on weights): the narrow columns stay as E2M1 nibbles (two output
# columns per byte: low nibble = even, high nibble = odd of each 2-column pair, so the output column order is
# a fixed permutation, folded downstream) plus one int8 shift per (32-block, column). The kernel decodes the
# tile on the VPU once per grid step and feeds the MXU int8. The last 128 columns (all wide ones, padded) stay
# prefolded as in the dense kernel. Weight bytes: 0.5 + 1/32 per weight instead of 1.
# ---------------------------------------------------------------------------------------------------------
import functools as _ft

from jax.experimental import pallas as pl
from jax.experimental.pallas import tpu as pltpu


def _decode(code, sh):
    """code int32 nibble [K, n], sh int32 [K, n] -> int32 doubled E2M1 value << sh (|.| <= 96)."""
    e = (code >> 1) & 3
    m = code & 1
    mag = jnp.where(e == 0, m, (2 + m) << jnp.maximum(e - 1, 0))
    mag = mag << sh
    return jnp.where((code & 8) != 0, -mag, mag)


def _packed_kernel(x_ref, p_ref, s_ref, o_ref):
    p = p_ref[...].astype(jnp.int32) & 255                      # [K, bn/2] bytes
    K = p.shape[0]
    sh = s_ref[...].astype(jnp.int32)                           # [K/32, bn/2, 2] -> per nibble plane below
    s_lo = jnp.broadcast_to(sh[:, None, :, 0], (K // 32, 32, sh.shape[1])).reshape(K, sh.shape[1])
    s_hi = jnp.broadcast_to(sh[:, None, :, 1], (K // 32, 32, sh.shape[1])).reshape(K, sh.shape[1])
    w_lo = _decode(p & 15, s_lo).astype(jnp.int8)
    w_hi = _decode(p >> 4, s_hi).astype(jnp.int8)
    x = x_ref[...]
    half = p.shape[1]
    o_ref[:, :half] = jnp.dot(x, w_lo, preferred_element_type=jnp.int32)
    o_ref[:, half:] = jnp.dot(x, w_hi, preferred_element_type=jnp.int32)


def pack_narrow(codes, e, order, n_narrow_cols):
    """From the permuted codes/exponents: columns [0, n_narrow_cols) -> nibble bytes [K, n/2] and shifts
    [K/32, n/2, 2]; within each bn-tile the even/odd split is per 2-column pair (cols 2i, 2i+1)."""
    cp = codes[order][:n_narrow_cols]                           # [n, K]
    s = (e - e.min(axis=1, keepdims=True))[order][:n_narrow_cols]   # [n, K/32]
    assert s.max() <= 3
    lo, hi = cp[0::2], cp[1::2]
    packed = (lo | (hi << 4)).T.astype(np.uint8)                # [K, n/2]
    sh = np.stack([s[0::2].T, s[1::2].T], axis=-1).astype(np.int8)   # [K/32, n/2, 2]
    return packed, sh


def packed_out_order(n, bn):
    """Output column position -> permuted-column index produced by the packed kernel (per bn tile:
    first half = even columns of the tile's pairs, second half = odd)."""
    idx = []
    for t0 in range(0, n, bn):
        cols = np.arange(t0, t0 + bn)
        idx += list(cols[0::2]) + list(cols[1::2])
    return np.array(idx)


def _tail_kernel(y_ref, x_ref, wt_ref, wh_ref, o_ref):
    x = x_ref[...]
    o_ref[...] = (jnp.dot(x, wt_ref[...], preferred_element_type=jnp.int32)
                  + 128 * jnp.dot(x, wh_ref[...], preferred_element_type=jnp.int32))


def impl_packed(T, K, N, bn=512, interpret=False):
    nn = N - 128
    assert nn % bn == 0

    def f(x, packed, sh, W1_tail, Whi):
        """Writes the whole [T, N] output in place: the packed kernel fills [0, N-128), a second kernel aliased
        to the same buffer fills the wide tail (no concatenate, so no extra pass over the output)."""
        y = pl.pallas_call(
            _packed_kernel, out_shape=jax.ShapeDtypeStruct((T, N), jnp.int32), grid=(nn // bn,),
            in_specs=[pl.BlockSpec((T, K), lambda j: (0, 0)), pl.BlockSpec((K, bn // 2), lambda j: (0, j)),
                      pl.BlockSpec((K // 32, bn // 2, 2), lambda j: (0, j, 0))],
            out_specs=pl.BlockSpec((T, bn), lambda j: (0, j)),
            compiler_params=pltpu.CompilerParams(dimension_semantics=("parallel",), vmem_limit_bytes=64 * 2**20),
            interpret=interpret)(x, packed, sh)
        return pl.pallas_call(
            _tail_kernel, out_shape=jax.ShapeDtypeStruct((T, N), jnp.int32), grid=(1,),
            in_specs=[pl.BlockSpec(memory_space=pl.ANY), pl.BlockSpec((T, K), lambda j: (0, 0)),
                      pl.BlockSpec((K, 128), lambda j: (0, 0)), pl.BlockSpec((K, 128), lambda j: (0, 0))],
            out_specs=pl.BlockSpec((T, 128), lambda j: (0, nn // 128)),
            input_output_aliases={0: 0}, interpret=interpret)(y, x, W1_tail, Whi)
    return f


def prepare(rng, T, K, N, packed=False, check_rows=64):
    """(device args, check(out) -> bool) for the profiler: exact on the first check_rows rows vs int64."""
    codes, e = synth_weights(rng, N, K)
    W1, Whi, order, w2, s = prefold(codes, e)
    x = rng.integers(-128, 128, (T, K)).astype(np.int8)
    exp = ref(dict(x=x[:check_rows], w2=w2, s=s, order=order), check_rows, K, N)
    if packed:
        bn = 512
        pk, sh = pack_narrow(codes, e, order, N - 128)
        pos = np.concatenate([packed_out_order(N - 128, bn), np.arange(N - 128, N)])
        exp = exp[:, pos]
        args = (x, pk, sh, np.ascontiguousarray(W1[:, N - 128:]), Whi)
    else:
        args = (x, W1, Whi)
    return args, lambda o: bool((np.asarray(o)[:check_rows].astype(np.int64) == exp).all())


def impl_any(T, K, N, packed=False, **kw):
    return impl_packed(T, K, N, **kw) if packed else impl(T, K, N, **kw)


def arg_specs_any(T, K, N, packed=False):
    if packed:
        return [((T, K), jnp.int8), ((K, (N - 128) // 2), jnp.uint8), ((K // 32, (N - 128) // 2, 2), jnp.int8),
                ((K, 128), jnp.int8), ((K, 128), jnp.int8)]
    return arg_specs(T, K, N)


def count_any(T, K, N, packed=False):
    """Ideal for the packed variant: one MAC per (t, n, k); 0.5 B per narrow weight + 1/32 B shift."""
    if not packed:
        return count(T, K, N)

    def f(x, pk, sh, wt, wh):
        # MACs: T*N*K (+ the wide tail's hi limb); reads every argument once via a cheap reduction of each
        w = jnp.concatenate([pk.astype(jnp.int8), pk.astype(jnp.int8)], axis=1)[:, :N - 128]
        w = jnp.concatenate([w, wt], axis=1)
        y = jnp.dot(x, w, preferred_element_type=jnp.int32)
        return y + (sh.sum() + wh.sum()).astype(jnp.int32)
    return f, arg_specs_any(T, K, N, True)


KERNELS[0].update(impl=impl_any, arg_specs=arg_specs_any, count=count_any, prepare=prepare)
KERNELS[0]["cfgs"]["gateup_T256_packed"] = dict(T=256, K=2880, N=5760, packed=True)
