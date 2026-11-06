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
