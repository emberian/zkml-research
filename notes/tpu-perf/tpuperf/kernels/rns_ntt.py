"""Workload 2: negacyclic NTT mod a 61-bit RNS prime, as int8 MXU matmuls over byte limbs (dark-learning BFV,
N = 8192; research/dark_learning_2026_11_06, docs/DARK-LEARNING-SCHEME-DECISION.md).

Layout and math. q < 2^61, q = 1 mod 2N, psi a primitive 2N-th root. Output Xhat[k] = sum_j x_j psi^(j(2k+1)).
Four-step with N = N1*N2, j = N2*j1 + j2, k = k1 + N1*k2:
  stage 1 (per j2):  A[k1, j2] = sum_j1 x[j1, j2] psi^(N2 j1 (2 k1 + 1))
  stage 2 (per k1):  Xhat[k1 + N1 k2] = sum_j2 A[k1, j2] psi^(j2 (2k + 1))
Output is stored [k1, k2] (k1-major), i.e. a fixed permutation of natural order; pointwise products don't care.

Limbs. A residue is 8 little-endian bytes u_a (the bytes of its u64). The MXU sees u_a - 128 (int8). A constant
matrix entry m (mod q) enters as  m * 2^(8a) mod q  written in 8 balanced base-256 digits d_c in [-128, 127]:
  sum_(j,a) m_j 2^(8a) u_ja  =  sum_c 256^c z_c  +  128 * sum_(j,a) (m_j 2^(8a) mod q),
  z_c = sum_(j,a) d_c[(j,a)] (u_ja - 128)   (one int8 matmul, K = 8*N1 or 8*N2, |z_c| < 2^24: exact in int32).
The constant term is precomputed. Reduction to canonical bytes is VPU int32 work: carry-propagate, a float32
quotient estimate qhat (error <= 1), subtract qhat*q limbwise, carry-propagate, two conditional corrections.
No 64-bit type anywhere (Mosaic rejects u64; XLA would emulate it).
"""
import jax
import jax.numpy as jnp
import numpy as np

from .common import reduce_limbs


def _is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def ntt_prime(bits, two_n):
    """Largest prime below 2^bits with p = 1 mod 2N (same rule as bfv_ref.ntt_primes)."""
    p = ((1 << bits) - 1) // two_n * two_n + 1
    while not _is_prime(p):
        p -= two_n
    return p


def root_2n(q, two_n):
    for g in range(2, 1000):
        psi = pow(g, (q - 1) // two_n, q)
        if pow(psi, two_n // 2, q) == q - 1:
            return psi
    raise ValueError


def bal_digits(m):
    d = []
    for _ in range(8):
        r = m % 256
        if r >= 128:
            r -= 256
        d.append(r)
        m = (m - r) // 256
    assert m == 0
    return d


class Plan:
    def __init__(self, N, N1, bits=61):
        self.N, self.N1, self.N2 = N, N1, N // N1
        q = ntt_prime(bits, 2 * N)
        self.q, self.psi = q, root_2n(q, 2 * N)
        pw = [pow(self.psi, e, q) for e in range(2 * N)]
        # D[e, a, c] = digit c of psi^e * 2^(8a) mod q ;  S[e, a] = psi^e 2^(8a) mod q
        D = np.zeros((2 * N, 8, 8), np.int8)
        S = [[0] * 8 for _ in range(2 * N)]
        for e in range(2 * N):
            for a in range(8):
                v = pw[e] * pow(2, 8 * a, q) % q
                S[e][a] = v
                D[e, a] = bal_digits(v)
        N1, N2 = self.N1, self.N2
        j1, k1 = np.arange(N1)[:, None], np.arange(N1)[None, :]
        e1 = (N2 * j1 * (2 * k1 + 1)) % (2 * N)                              # [j1, k1]
        # T1 [(k1, c), (a, j1)]
        self.T1 = np.ascontiguousarray(D[e1].transpose(1, 3, 2, 0).reshape(N1 * 8, 8 * N1))
        j2 = np.arange(N2)[None, :, None]
        kk = np.arange(N1)[:, None, None] + N1 * np.arange(N2)[None, None, :]  # [k1, 1, k2]
        e2 = (j2 * (2 * kk + 1)) % (2 * N)                                    # [k1, j2, k2]
        # T2 [k1, (a, j2), (c, k2)]   from D[e2] = [k1, j2, k2, a, c]
        self.T2 = np.ascontiguousarray(D[e2].transpose(0, 3, 1, 4, 2).reshape(N1, 8 * N2, 8 * N2))
        sa = [sum(S[e]) for e in range(2 * N)]                                # sum_a S[e, a]
        c1 = [128 * sum(sa[int(e1[j, k])] for j in range(N1)) % q for k in range(N1)]
        c2 = np.zeros((N1, N2, 8), np.int32)
        for a in range(N1):
            for b in range(N2):
                c2[a, b] = list((128 * sum(sa[int(e2[a, j, b])] for j in range(N2)) % q).to_bytes(8, "little"))
        self.C1 = np.array([list(v.to_bytes(8, "little")) for v in c1], np.int32)   # [k1, 8]
        self.C2 = c2                                                                  # [k1, k2, 8]
        self.qb = np.array(list(q.to_bytes(8, "little")), np.int32)


def reduce_q(z, qb, q):  # limb axis last; kept for the reduction stress test
    """z: int32 [..., 8] limb sums -> uint8 [..., 8] canonical mod q (common.reduce_limbs)."""
    return jnp.stack(reduce_limbs([z[..., c] for c in range(8)], q), axis=-1).astype(jnp.uint8)


def make_ntt(plan):
    """Planar layout: byte (limb) axes are MAJOR, the batch x data axes are the minor (lane) axes, so every
    limb is its own plane: the VPU reduction is lane-parallel and no limb axis is ever 8-of-128 lanes.
      input   xp  uint8 [8 a, N1 j1, B, N2 j2]       (x_j = sum_a 256^a xp[a, j1, b, j2], j = N2 j1 + j2)
      stage 1 z1 = T1 [(k1, c), (a, j1)] @ xp [(a, j1), (b, j2)]                      one 2D int8 matmul
      stage 2 per k1: z2[k1, c, b, k2] = sum_(a, j2) A[k1, a, b, j2] T2[k1, (a, j2), (c, k2)]   batched matmul
      output  uint8 [N1 k1, 8 c, B, N2 k2] = byte c of Xhat[k1 + N1 k2] of polynomial b."""
    N1, N2, q = plan.N1, plan.N2, plan.q
    C1 = jnp.asarray(plan.C1[:, :, None])                                            # [k1, c, 1]
    C2 = jnp.asarray(plan.C2.transpose(0, 2, 1))                                       # [k1, c, k2]

    def red(z, axis):
        L = reduce_limbs([jnp.take(z, c, axis=axis) for c in range(8)], q)
        return jnp.stack(L, axis=axis).astype(jnp.uint8)

    def ntt(xp, T1, T2):
        B = xp.shape[2]
        u = (xp ^ jnp.uint8(128)).view(jnp.int8).reshape(8 * N1, B * N2)
        z1 = jnp.dot(T1, u, preferred_element_type=jnp.int32).reshape(N1, 8, B, N2)
        A = red(z1 + C1[:, :, :, None], axis=1)                                         # [k1, a, B, j2]
        u2 = (A ^ jnp.uint8(128)).view(jnp.int8)
        z2 = jnp.einsum("kabt,katcx->kcbx", u2, T2.reshape(N1, 8, N2, 8, N2), preferred_element_type=jnp.int32)
        return red(z2 + C2[:, :, None, :], axis=1)                                      # [k1, c, B, k2]
    return ntt, None


_PLANS = {}


def plan_for(N, N1):
    if (N, N1) not in _PLANS:
        _PLANS[(N, N1)] = Plan(N, N1)
    return _PLANS[(N, N1)]


def inputs(rng, B, N, N1):
    p = plan_for(N, N1)
    x = [[int(v) % p.q for v in rng.integers(0, 2**62, N, dtype=np.int64)] for _ in range(B)]
    xb = np.array([[list(v.to_bytes(8, "little")) for v in row] for row in x], np.uint8)   # [B, N, 8]
    xp = np.ascontiguousarray(xb.reshape(B, N1, N // N1, 8).transpose(3, 1, 0, 2))      # [8, N1, B, N2]
    return (xp, p.T1, p.T2), dict(x=x)


def ntt_ref_poly(x, q, psi):
    """Negacyclic NTT, natural order: Xhat[k] = sum_j x_j psi^(j(2k+1)), O(N log N) on Python ints."""
    N = len(x)
    a = [x[j] * pow(psi, j, q) % q for j in range(N)]
    w = psi * psi % q
    j = 0
    for i in range(1, N):                      # bit reversal
        bit = N >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j |= bit
        if i < j:
            a[i], a[j] = a[j], a[i]
    m = 2
    while m <= N:
        wm = pow(w, N // m, q)
        for s in range(0, N, m):
            t = 1
            for k in range(m // 2):
                u, v = a[s + k], a[s + k + m // 2] * t % q
                a[s + k], a[s + k + m // 2] = (u + v) % q, (u - v) % q
                t = t * wm % q
        m *= 2
    return a


def ref(rd, B, N, N1):
    p = plan_for(N, N1)
    N2 = N // N1
    out = np.zeros((N1, 8, B, N2), np.uint8)
    for b, x in enumerate(rd["x"]):
        X = ntt_ref_poly(x, p.q, p.psi)
        for k1 in range(N1):
            for k2 in range(N2):
                out[k1, :, b, k2] = list(X[k1 + N1 * k2].to_bytes(8, "little"))
    return out


def impl(B, N, N1, **kw):
    f, _ = make_ntt(plan_for(N, N1))
    return f


def count(B, N, N1):
    f = impl(B, N, N1)
    return f, arg_specs(B, N, N1)


def arg_specs(B, N, N1):
    N2 = N // N1
    return [((8, N1, B, N2), jnp.uint8), ((N1 * 8, 8 * N1), jnp.int8), ((N1, 8 * N2, 8 * N2), jnp.int8)]


KERNELS = [dict(
    name="rns_ntt61",
    module=__name__,
    cfgs={
        "mac": dict(B=2, N=8192, N1=64),
        "N8192_B1024": dict(B=1024, N=8192, N1=64),
    },
    inputs=inputs, ref=ref, impl=impl, count=count, arg_specs=arg_specs,
)]


def selfcheck_small():
    """Naive O(N^2) definition vs the radix-2 reference at N = 64."""
    q, N = ntt_prime(61, 128), 64
    psi = root_2n(q, 128)
    x = list(range(3, 3 + N))
    nv = [sum(x[j] * pow(psi, j * (2 * k + 1), q) for j in range(N)) % q for k in range(N)]
    return nv == ntt_ref_poly(x, q, psi)
