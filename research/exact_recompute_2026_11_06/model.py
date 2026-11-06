"""gptoss-int v0: an integer gpt-oss-20b. SPEC.md is the prose; this file is the reference.

Every quantity is an integer. Weights enter exactly: an MXFP4 expert row is q << (e_blk - e_min)
with row exponent e_min - 128; a BF16 row is m << (e - e_min) with row exponent e_min. A product
x @ W is defined as the exact integer sum, carried as two limbs D = Dh * 2^20 + Dl with
Dh = x @ (W >> 20), Dl = x @ (W & (2^20 - 1)), then requantized by rq2. Any order of summation
gives the same integers. Two kernels compute the limbs: `ExactF64` (float64 BLAS, exact because
every partial sum is an integer below 2^53) and, in jaxint.py, int8 limbs on an INT8 matrix unit
with int32 accumulation.
"""
import numpy as np

import tables as T
from weights import Shards, bf16_to_int

L20 = 20
ACLAMP_LO, ACLAMP_HI = -32640, 32639   # every matmul input: two balanced int8 limbs


# ---------------------------------------------------------------- integer primitives (xp = numpy | jax.numpy)
def rq(xp, a, k):
    """floor((a + 2^(k-1)) / 2^k) for k >= 1, elementwise, k an int or array."""
    k = xp.asarray(k, dtype=xp.int64)
    return xp.right_shift(a + xp.left_shift(xp.int64(1), k - 1), k)


def rq2(xp, dh, dl, s):
    """rq(dh * 2^20 + dl, s) exactly for s >= 1, and (dh * 2^20 + dl) * 2^-s for s <= 0
    (s per column), with dh, dl int64."""
    s = xp.asarray(s, dtype=xp.int64)
    c = xp.left_shift(xp.int64(1), xp.maximum(s, 1) - 1)
    big = s >= L20
    sb = xp.where(big, s, L20)
    a = dh + xp.right_shift(dl + c, L20)
    hi = xp.right_shift(a, sb - L20)
    ss = xp.where(big, 1, xp.maximum(s, 1))
    lo = xp.left_shift(dh, L20 - ss) + xp.right_shift(dl + c, ss)
    up = xp.maximum(-s, 0)                       # s <= 0: an exact left shift, no rounding
    exact = xp.left_shift(dh, L20 + up) + xp.left_shift(dl, up)
    return xp.where(s <= 0, exact, xp.where(big, hi, lo))


def clamp(xp, a, lo, hi):
    return xp.minimum(xp.maximum(a, lo), hi)


def isqrt(xp, n):
    """floor(sqrt(n)) for int64 0 <= n < 2^62, by integer Newton from 2^31 (no floating point)."""
    r = xp.full(n.shape, 1 << 31, dtype=xp.int64)
    for _ in range(40):
        nr = xp.right_shift(r + n // xp.maximum(r, 1), 1)
        r = xp.where(nr < r, nr, r)
    return r


def to_scale(xp, m, e, f):
    """The dyadic m * 2^e at fixed point 2^-f: exact shift up, or rq down."""
    sh = e + f
    up = xp.left_shift(m.astype(xp.int64), xp.maximum(sh, 0))
    down = rq(xp, m.astype(xp.int64), xp.maximum(-sh, 1))
    return xp.where(sh >= 0, up, down)


# ---------------------------------------------------------------- weights as integers
class IntMatrix:
    """W[out, in] = Wint[out, in] * 2^rowexp[out], exactly. Wint as (Wh, Wl) 20-bit limbs."""

    def __init__(self, wint, rowexp):
        self.wh = wint >> L20
        self.wl = wint & ((1 << L20) - 1)
        self.rowexp = rowexp.astype(np.int64)
        self.width = int(np.ceil(np.log2(np.abs(wint).max() + 1))) + 1

    @staticmethod
    def from_bf16(bits):
        m, e = bf16_to_int(bits)
        nz = m != 0
        emin = np.where(nz, e, 10 ** 6).min(axis=1)
        emin = np.where(emin == 10 ** 6, 0, emin)
        sh = np.where(nz, e - emin[:, None], 0)
        assert sh.max() <= 50, "BF16 row spread beyond the v0 window"
        return IntMatrix(m.astype(np.int64) << sh, emin)

    @staticmethod
    def from_mxfp4(q, e):
        """q int8 [out, nblk, 32], e int32 [out, nblk] -> row-aligned integers."""
        emin = e.min(axis=1)
        sh = (e - emin[:, None]).astype(np.int64)
        assert sh.max() <= 24, "MXFP4 row spread beyond the v0 window"
        wint = (q.astype(np.int64) << sh[:, :, None]).reshape(q.shape[0], -1)
        im = IntMatrix(wint, emin - 128)
        im.q, im.e, im.emin = q, e, emin  # kept for the block-wise MXU kernel
        return im


class ExactF64:
    """Limbs by float64 BLAS. Exact: |x| < 2^15, |Wl| < 2^20, |Wh| < 2^30, K <= 2^12 keep every
    partial sum an integer below 2^53 in magnitude, so any summation order gives the same value."""
    name = "numpy-f64blas"

    def limbs(self, x, W):
        assert x.min() >= ACLAMP_LO and x.max() <= ACLAMP_HI and x.shape[1] <= 4096
        assert W.width <= 50
        xf = x.astype(np.float64)
        dh = (xf @ W.wh.T.astype(np.float64)).astype(np.int64)
        dl = (xf @ W.wl.T.astype(np.float64)).astype(np.int64)
        return dh, dl


class InexactF32(ExactF64):
    """The falsifier: the same limbs through float32 BLAS. Partial sums exceed 2^24, so the
    result depends on the library's summation order and rounding; G1 shows its digests differ."""
    name = "numpy-f32blas-FALSIFIER"

    def limbs(self, x, W):
        xf = x.astype(np.float32)
        dh = (xf @ W.wh.T.astype(np.float32)).astype(np.int64)
        dl = (xf @ W.wl.T.astype(np.float32)).astype(np.int64)
        return dh, dl


def linear(xp, kern, x, xf, W, bias_bits, fo):
    """x at 2^-xf, W exact, bias BF16; result at 2^-fo, int64."""
    dh, dl = kern.limbs(x, W)
    s = xf - W.rowexp - fo
    if np.any(np.asarray(s) < -16):
        raise ValueError("output scale too fine for v0")
    y = rq2(xp, dh, dl, xp.asarray(s)[None, :])
    if bias_bits is not None:
        bm, be = bf16_to_int(bias_bits)
        y = y + to_scale(xp, xp.asarray(bm), xp.asarray(be), fo)[None, :]
    return y
