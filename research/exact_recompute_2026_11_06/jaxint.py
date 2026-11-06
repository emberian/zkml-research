"""The second kernel for gptoss-int v0: the exact limbs (Dh, Dl) of x @ W computed from int8 x int8
products with int32 accumulation (an INT8 matrix unit's native operation: TPU MXU, a GPU's dp4a /
IMMA, XLA:CPU's integer dot), recombined in int64. MXFP4 expert rows are done block by block:
each block-32 dot of an activation limb with the E2M1 integers is one int8 x int8 -> int32 dot,
then shifted by its block's exponent offset. Nothing here rounds; the integers equal the float64
BLAS kernel's by construction, which is what G1/G2 test."""
import jax
import jax.numpy as jnp
import numpy as np

import model as M


def low8(a):
    return ((a + 128) % 256) - 128


def split_act(x):
    """x in [-32640, 32639] -> (hi, lo) int8 with x = 256 hi + lo."""
    lo = low8(x)
    hi = (x - lo) // 256
    return hi.astype(jnp.int8), lo.astype(jnp.int8)


def split_w(w, n):
    """int64 w -> n balanced int8 limbs, w = sum_i limb_i * 256^i (asserted)."""
    limbs, r = [], np.asarray(w, dtype=np.int64)
    for _ in range(n):
        l = ((r + 128) % 256) - 128
        limbs.append(l.astype(np.int8))
        r = (r - l) // 256
    assert not np.any(r), "weight wider than its limbs"
    return limbs


def dot8(a, b):
    """int8 [t, k] x int8 [o, k] -> int32 [t, o], exact."""
    return jax.lax.dot_general(a, b, (((1,), (1,)), ((), ())), preferred_element_type=jnp.int32)


def act_limbs(x, n):
    """int64 x -> n balanced int8 limbs (jnp), x = sum_i limb_i * 256^i; the caller bounds |x|."""
    limbs, r = [], x
    for _ in range(n):
        l = low8(r)
        limbs.append(l.astype(jnp.int8))
        r = (r - l) // 256
    return limbs


def limb_einsum(spec, a, b, na, nb):
    """Exact int64 einsum from int8 x int8 -> int32 einsums. a, b are int64 with
    |a| < 128 * 256^(na-1) * 2 (balanced limbs), likewise b; each int32 partial is a sum of
    at most 2^16 products of magnitude <= 2^14, so it cannot overflow."""
    A, B = act_limbs(a, na), act_limbs(b, nb)
    out = None
    for i, ai in enumerate(A):
        for j, bj in enumerate(B):
            d = jnp.einsum(spec, ai, bj, preferred_element_type=jnp.int32).astype(jnp.int64)
            d = jnp.left_shift(d, 8 * (i + j))
            out = d if out is None else out + d
    return out


class Int8Mxu:
    name = "jax-int8-limbs"

    def __init__(self):
        self.backend = jax.default_backend()
        self.name = f"jax-int8-limbs-{self.backend}"
        self._cache = {}

    def _wlimbs(self, W, which):
        key = (id(W), which)
        if key not in self._cache:
            arr = W.wh if which == "h" else W.wl
            width = int(np.ceil(np.log2(np.abs(arr).max() + 1))) + 2 if np.any(arr) else 1
            n = max(1, -(-width // 8))
            self._cache[key] = [jnp.asarray(l) for l in split_w(arr, n)]
        return self._cache[key]

    def _limb_dot(self, xs, wl):
        acc = jnp.zeros((xs[0].shape[0], wl[0].shape[0]), dtype=jnp.int64)
        for i, xa in enumerate((xs[1], xs[0])):          # lo is 256^0, hi is 256^1
            for j, wb in enumerate(wl):
                acc = acc + jnp.left_shift(dot8(xa, wb).astype(jnp.int64), 8 * (i + j))
        return acc

    def einsum(self, spec, a, b, na, nb):
        """The attention dots: q.k (2 x 2 limbs) and e.v (3 x 2 limbs; the exp table reaches 2^15)."""
        def fits(z, n):
            hi = sum(127 << (8 * i) for i in range(n))
            return int(jnp.min(z)) >= -hi - n and int(jnp.max(z)) <= hi
        assert fits(jnp.asarray(a), na) and fits(jnp.asarray(b), nb) and a.shape[0] < (1 << 16)
        return limb_einsum(spec, jnp.asarray(a), jnp.asarray(b), na, nb)

    def limbs(self, x, W):
        x = jnp.asarray(x, dtype=jnp.int64)
        assert int(x.min()) >= M.ACLAMP_LO and int(x.max()) <= M.ACLAMP_HI
        xs = split_act(x)
        if hasattr(W, "q") and not np.any(W.wh):
            return jnp.zeros((x.shape[0], W.wl.shape[0]), dtype=jnp.int64), self._mxfp4(xs, W)
        return self._limb_dot(xs, self._wlimbs(W, "h")), self._limb_dot(xs, self._wlimbs(W, "l"))

    def _mxfp4(self, xs, W):
        key = (id(W), "q")
        if key not in self._cache:
            self._cache[key] = (jnp.asarray(W.q), jnp.asarray((W.e - W.emin[:, None]).astype(np.int64)))
        q, sh = self._cache[key]                         # q [o, nb, 32] int8, sh [o, nb]
        t = xs[0].shape[0]
        nb = q.shape[1]
        total = jnp.zeros((t, q.shape[0]), dtype=jnp.int64)
        for i, xa in enumerate((xs[1], xs[0])):
            xb = xa.reshape(t, nb, 32)
            blk = jax.lax.dot_general(xb, q, (((2,), (2,)), ((1,), (1,))), preferred_element_type=jnp.int32)  # [nb, t, o]
            blk = jnp.transpose(blk, (1, 2, 0)).astype(jnp.int64)                                            # [t, o, nb]
            total = total + jnp.left_shift(jnp.sum(jnp.left_shift(blk, sh[None]), axis=2), 8 * i)
        return total


class F32Dot(Int8Mxu):
    """The falsifier on the device: the same integer operands through float32 dots (cuBLAS / MXU f32
    path). Partial sums exceed 2^24, so values depend on the device's summation; expected to diverge."""

    def __init__(self):
        super().__init__()
        self.name = f"jax-f32-FALSIFIER-{self.backend}"

    def einsum(self, spec, a, b, na, nb):
        f = jnp.einsum(spec, jnp.asarray(a).astype(jnp.float32), jnp.asarray(b).astype(jnp.float32))
        return f.astype(jnp.int64)

    def limbs(self, x, W):
        xf = jnp.asarray(x).astype(jnp.float32)
        dh = (xf @ jnp.asarray(W.wh.T, dtype=jnp.float32)).astype(jnp.int64)
        dl = (xf @ jnp.asarray(W.wl.T, dtype=jnp.float32)).astype(jnp.int64)
        return dh, dl
