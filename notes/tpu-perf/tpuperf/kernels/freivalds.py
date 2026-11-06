"""Workload 3b: Freivalds check of an exact int8 matmul Y = X @ W (int32), over BabyBear, on the int8 MXU.

Check  X (W r) == Y r  (mod P)  for s random vectors r in F_P^N (soundness error <= P^-s per wrong Y).
All three products are int8 matmuls over byte digits:
  W r  : W [K, N] @ R [N, 4s]      R = balanced base-256 digits of r (host, free); |acc| <= N 2^14
  X v  : X [T, K] @ V [K, 4s]      V = balanced digits of (W r mod P), computed on the VPU
  Y r  : sum_a 256^a  y'_a [T, N] @ R,  y'_a = byte a of Y as offset int8 (top byte signed), plus the
         constant 128 * colsum(R) for the three offset bytes.
This is the cheap verifier for workload 1's output: HBM-bound by reading Y (4 bytes per element).
"""
import jax
import jax.numpy as jnp
import numpy as np

P = 2**31 - 2**27 + 1


def bal_digits(v, n=4):
    d = []
    for _ in range(n):
        x = v % 256
        if x >= 128:
            x -= 256
        d.append(x)
        v = (v - x) // 256
    assert v == 0
    return d


def modp_from_digits(z, nl):
    """z: int32 [..., nl, s] digit sums (value sum_c 256^c z_c) -> int32 [..., s] canonical mod P.
    |z| < 2^28 assumed; done with float32-free exact steps: carry to bytes, then fold 2^32 = 2^28 - 2 (mod P)."""
    from .common import reduce_limbs
    L = reduce_limbs([z[..., c, :] for c in range(nl)], P)
    return L[0] | (L[1] << 8) | (L[2] << 16) | (L[3] << 24)


def digits_of(v):
    """int32 canonical [..., s] -> int8 balanced digits [..., 4, s] (VPU)."""
    out, c = [], 0
    for a in range(4):
        b = ((v >> (8 * a)) & 255) + c
        d = jnp.where(b >= 128, b - 256, b)
        c = (b - d) >> 8
        out.append(d)
    return jnp.stack(out, axis=-2).astype(jnp.int8)


NCH = 2048   # Y r contraction chunk: |z_c| <= 4 * 2048 * 2^14 = 2^27, inside reduce_limbs' exact range


def _addmod(x, y):
    t = x - (P - y)
    return jnp.where(t < 0, t + P, t)


def make(T, K, N, s):
    def f(X, W, Y, R, RA, Kc):
        """R int8 [N, 4*s] digits of r (columns (c, j)); RA int8 [4 a, N, 4*s] digits of 256^a r mod P;
        Kc int32 [s] = 128 * sum_(a<3, n) (256^a r_n mod P) mod P, the offset-byte constant."""
        wr = jnp.dot(W, R, preferred_element_type=jnp.int32).reshape(K, 4, s)        # [K, c, j]
        V = digits_of(modp_from_digits(wr, 4)).reshape(K, 4 * s)                     # [K, (c, j)]
        lhs = modp_from_digits(jnp.dot(X, V, preferred_element_type=jnp.int32).reshape(T, 4, s), 4)
        ys = [((Y >> (8 * a)) if a == 3 else (((Y >> (8 * a)) & 255) - 128)).astype(jnp.int8) for a in range(4)]
        rhs = None
        for c0 in range(0, N, NCH):
            z = sum(jnp.dot(ys[a][:, c0:c0 + NCH], RA[a, c0:c0 + NCH], preferred_element_type=jnp.int32)
                    for a in range(4)).reshape(T, 4, s)
            part = modp_from_digits(z, 4)
            rhs = part if rhs is None else _addmod(rhs, part)
        return lhs, _addmod(rhs, Kc[None, :])
    return f


def inputs(rng, T, K, N, s):
    X = rng.integers(-128, 128, (T, K)).astype(np.int8)
    W = rng.integers(-128, 128, (K, N)).astype(np.int8)
    Y = X.astype(np.int64) @ W.astype(np.int64)
    Y[0, 0] += 1                                               # one wrong entry: row 0 must fail
    Y = Y.astype(np.int32)
    r = rng.integers(0, P, (N, s), dtype=np.int64)
    dig = lambda M: np.ascontiguousarray(np.array([[bal_digits(int(M[n, j])) for j in range(s)] for n in range(N)],
                                                  np.int8).transpose(0, 2, 1).reshape(N, 4 * s))
    R = dig(r)
    ra = [(r * pow(256, a, P)) % P for a in range(4)]
    RA = np.stack([dig(x) for x in ra])
    Kc = np.array([128 * sum(int(ra[a][n, j]) for a in range(3) for n in range(N)) % P for j in range(s)], np.int32)
    return (X, W, Y, R, pad128(RA), Kc), dict(X=X, W=W, Y=Y, r=r)


def ref(rd, T, K, N, s):
    r = rd["r"] % P
    wr = (rd["W"].astype(np.int64) @ r) % P                     # |W| r < 2^7 * 2^31 * N < 2^52
    lhs = np.zeros((T, s), np.int64)
    X = rd["X"].astype(np.int64)
    for j in range(s):                                          # chunked to stay inside int64
        lhs[:, j] = (X @ wr[:, j]) % P
    Y = rd["Y"].astype(np.int64) % P
    rhs = np.zeros((T, s), np.int64)
    for j in range(s):
        acc = np.zeros(T, np.int64)
        for c0 in range(0, N, 1024):
            acc = (acc + (Y[:, c0:c0 + 1024] * r[c0:c0 + 1024, j][None, :] % P).sum(1)) % P
        rhs[:, j] = acc
    return lhs, rhs


def impl(T, K, N, s, interpret=False, **kw):
    return make_pallas(T, K, N, s, interpret=interpret)


def count(T, K, N, s):
    return make(T, K, N, s), count_specs(T, K, N, s)


def arg_specs(T, K, N, s):
    return [((T, K), jnp.int8), ((K, N), jnp.int8), ((T, N), jnp.int32), ((N, 4 * s), jnp.int8),
            ((4, N, 128), jnp.int8), ((s,), jnp.int32)]


def count_specs(T, K, N, s):
    return [((T, K), jnp.int8), ((K, N), jnp.int8), ((T, N), jnp.int32), ((N, 4 * s), jnp.int8),
            ((4, N, 4 * s), jnp.int8), ((s,), jnp.int32)]


KERNELS = [dict(
    name="freivalds_bb",
    module=__name__,
    cfgs={"mac": dict(T=256, K=2880, N=3840, s=2), "gateup_T2048": dict(T=2048, K=2880, N=5760, s=2)},
    inputs=inputs, ref=ref, impl=impl, count=count, arg_specs=arg_specs,
)]


# Pallas Y r: one pass over Y. Y tile (bt, nb) int32 -> 4 offset/signed byte planes (VPU) -> 4 int8 dots
# against RA[a] padded to 128 lanes (columns (c, j), 4*s used), accumulated in the resident output block.
# |acc| <= 4 N 2^14 = 2^28.5 at N = 5760: int32-exact, and V / P < 2^22 so reduce_limbs' estimate holds.
import functools

from jax.experimental import pallas as pl
from jax.experimental.pallas import tpu as pltpu


def _yr_kernel(y_ref, ra_ref, o_ref):
    @pl.when(pl.program_id(1) == 0)
    def _():
        o_ref[...] = jnp.zeros_like(o_ref)
    y = y_ref[...]
    acc = o_ref[...]
    for a in range(4):
        ya = (y >> 24) if a == 3 else (((y >> (8 * a)) & 255) - 128)
        acc = acc + jnp.dot(ya.astype(jnp.int8), ra_ref[a], preferred_element_type=jnp.int32)
    o_ref[...] = acc


def make_pallas(T, K, N, s, bt=512, nb=1920, interpret=False):
    assert 4 * N * 2**14 < 2**31 and N % nb == 0
    bt = min(bt, T)

    def f(X, W, Y, R, RA128, Kc):
        wr = jnp.dot(W, R, preferred_element_type=jnp.int32).reshape(K, 4, s)
        V = digits_of(modp_from_digits(wr, 4)).reshape(K, 4 * s)
        lhs = modp_from_digits(jnp.dot(X, V, preferred_element_type=jnp.int32).reshape(T, 4, s), 4)
        z = pl.pallas_call(
            _yr_kernel, out_shape=jax.ShapeDtypeStruct((T, 128), jnp.int32), grid=(T // bt, N // nb),
            in_specs=[pl.BlockSpec((bt, nb), lambda i, k: (i, k)), pl.BlockSpec((4, nb, 128), lambda i, k: (0, k, 0))],
            out_specs=pl.BlockSpec((bt, 128), lambda i, k: (i, 0)),
            compiler_params=pltpu.CompilerParams(dimension_semantics=("parallel", "arbitrary")),
            interpret=interpret)(Y, RA128)
        rhs = modp_from_digits(z[:, :4 * s].reshape(T, 4, s), 4)
        return lhs, _addmod(rhs, Kc[None, :])
    return f


def pad128(RA):
    out = np.zeros(RA.shape[:-1] + (128,), np.int8)
    out[..., :RA.shape[-1]] = RA
    return out


def prepare(rng, T, K, N, s):
    args, rd = inputs(rng, T, K, N, s)
    sub = dict(rd, X=rd["X"][:64], Y=rd["Y"][:64])
    el, er = ref(sub, 64, K, N, s)

    def check(o):
        lhs, rhs = (np.asarray(v)[:64] for v in o)
        return bool((lhs == el).all() and (rhs == er).all() and (lhs[0] != rhs[0]).all() and (lhs[1:] == rhs[1:]).all())
    return args, check


KERNELS[0]["prepare"] = prepare
