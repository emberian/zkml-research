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
