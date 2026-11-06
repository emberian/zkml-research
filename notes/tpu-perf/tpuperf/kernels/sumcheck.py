"""Workload 3: one fused degree-2 sumcheck round over BabyBear^4 (p = 2^31 - 2^27 + 1, X^4 = 11), the
TensorZKP-style mapping of notes/tensor-core-holography/F3-MODEL.md onto the TPU's int8 MXU.

The prover's round i+1 begins with the fold by r_i, and its round polynomial is computed from the folded
tables, so one pass fuses them: read f, g [4 coords, 2 (b_i), 2 (b_i+1), H] (u32, coordinate-major so H is
the 128-lane axis), write f' = f_0 + r (f_1 - f_0) and g' likewise [4, 2, H], and return the round's sums
s(t) = sum_h f'_t(h) g'_t(h), t in {0, 1, 2}, f'_2 = 2 f'_1 - f'_0.

MXU mapping (both are int8 x int8 -> int32 over byte limbs offset by -128):
- fold: r * d is a fixed F_p-linear map on the 4 coordinates. In limbs it is a [16, 16] matrix; 8 copies on
  the block diagonal make it [128, 128] so the MXU is full: Z = W @ D, D = [(g, j, a), H/8].
- sums: sum_h f_j(h) g_l(h) over limbs is the Gram matrix A B^T of the packed [(g, j, a), H/8] limb tables,
  computed in chunks of 2^17 columns so int32 cannot overflow (|product| <= 2^14). Only the diagonal
  (g, g) blocks are used; the column sums for the -128 offset are VPU sums. A 16x16 host combine finishes s.
"""
import jax
import jax.numpy as jnp
import numpy as np

from .common import reduce_limbs

P = 2**31 - 2**27 + 1
W = 11
G = 8              # lane groups packed onto the MXU
CHUNK = 2**17      # columns per exact int32 Gram chunk


def ext_mul(a, b):
    c = [0] * 7
    for i in range(4):
        for j in range(4):
            c[i + j] += a[i] * b[j]
    return [(c[m] + W * (c[m + 4] if m + 4 < 7 else 0)) % P for m in range(4)]


def rmat(r):
    """R[m][j]: (r * d)_m = sum_j R[m][j] d_j."""
    return [[r[m - j] if m >= j else W * r[m - j + 4] % P for j in range(4)] for m in range(4)]


def bal4(v):
    d = []
    for _ in range(4):
        x = v % 256
        if x >= 128:
            x -= 256
        d.append(x)
        v = (v - x) // 256
    assert v == 0
    return d


def fold_consts(r):
    R = rmat(r)
    Wm = np.zeros((16, 16), np.int8)          # [(m, c), (j, a)]
    C = []
    for m in range(4):
        tot = 0
        for j in range(4):
            for a in range(4):
                v = R[m][j] * pow(2, 8 * a, P) % P
                tot += v
                for c, dg in enumerate(bal4(v)):
                    Wm[m * 4 + c, j * 4 + a] = dg
        C.append(list((128 * tot % P).to_bytes(4, "little")))
    Wb = np.kron(np.eye(G, dtype=np.int8), Wm)  # [128, 128] block diagonal
    return Wb, np.array(C, np.int32)            # C: [m, c]


def to_limbs(x):
    """u32 [4, H] canonical -> int8 [(j, a)=16, H] offset limbs (byte - 128)."""
    b = [((x >> (8 * a)) & 255) for a in range(4)]
    return (jnp.stack(b, axis=1).reshape(16, -1).astype(jnp.uint8) ^ jnp.uint8(128)).view(jnp.int8)


def pack(d16):
    """[16, H] -> [(g, 16), H/8]: column h of group g is original column g*(H/8) + h."""
    H = d16.shape[1]
    return d16.reshape(16, G, H // G).transpose(1, 0, 2).reshape(G * 16, H // G)


def unpack(z):
    H8 = z.shape[1]
    return z.reshape(G, 16, H8).transpose(1, 0, 2).reshape(16, G * H8)


def submod(a, b):
    d = a - b
    return jnp.where(a >= b, d, d + jnp.uint32(P))


def fold(x0, x1, Wb, C):
    """x0, x1: u32 [4, H]; returns x0 + r (x1 - x0) mod P, u32 [4, H]."""
    d = to_limbs(submod(x1, x0))
    z = unpack(jnp.dot(Wb, pack(d), preferred_element_type=jnp.int32))     # [(m, c), H]
    z = z.reshape(4, 4, -1) + C[:, :, None]
    L = reduce_limbs([z[:, c] for c in range(4)], P)
    rd = (L[0] | (L[1] << 8) | (L[2] << 16) | (L[3] << 24)).astype(jnp.uint32)
    s = x0 + rd
    return jnp.where(s >= jnp.uint32(P), s - jnp.uint32(P), s)


def gram(a, b):
    """a, b: u32 [4, H]. Returns int32 Gram chunks [n, 128, 128] and offset-limb column sums [n, 2, 128]."""
    A, B = pack(to_limbs(a)), pack(to_limbs(b))                              # [128, H/8]
    H8 = A.shape[1]
    ck = min(CHUNK, H8)
    n = H8 // ck
    A3, B3 = A.reshape(128, n, ck).transpose(1, 0, 2), B.reshape(128, n, ck).transpose(1, 0, 2)
    Gm = jnp.einsum("nik,njk->nij", A3, B3, preferred_element_type=jnp.int32)
    S = jnp.stack([A3.astype(jnp.int32).sum(-1), B3.astype(jnp.int32).sum(-1)], axis=1)
    return Gm, S


def round_fn(f, g, Wb, C):
    f0, f1 = fold(f[:, 0, 0], f[:, 1, 0], Wb, C), fold(f[:, 0, 1], f[:, 1, 1], Wb, C)
    g0, g1 = fold(g[:, 0, 0], g[:, 1, 0], Wb, C), fold(g[:, 0, 1], g[:, 1, 1], Wb, C)

    def two_minus(x1, x0):
        t = x1 + x1
        t = jnp.where(t >= jnp.uint32(P), t - jnp.uint32(P), t)
        return submod(t, x0)
    f2, g2 = two_minus(f1, f0), two_minus(g1, g0)
    grams = [gram(f0, g0), gram(f1, g1), gram(f2, g2)]
    fp, gp = jnp.stack([f0, f1], 1), jnp.stack([g0, g1], 1)
    return fp, gp, jnp.stack([x[0] for x in grams]), jnp.stack([x[1] for x in grams])


def combine(Gm, S, H):
    """Host side: Gram chunks + column sums -> s(t) in BabyBear^4 (Python ints, exact)."""
    Gm, S = np.asarray(Gm).astype(np.int64), np.asarray(S).astype(np.int64)
    out = []
    for t in range(3):
        Gt = Gm[t].sum(0)                       # [128, 128] exact in int64 (n chunks)
        Sa, Sb = S[t][:, 0].sum(0), S[t][:, 1].sum(0)
        acc = [0] * 7
        for gi in range(G):
            for j in range(4):
                for a in range(4):
                    for l in range(4):
                        for b in range(4):
                            ia, ib = gi * 16 + j * 4 + a, gi * 16 + l * 4 + b
                            v = int(Gt[ia, ib]) + 128 * int(Sb[ib]) + 128 * int(Sa[ia]) + 128 * 128 * (H // G)
                            acc[j + l] += v << (8 * (a + b))
        out.append([(acc[m] + W * (acc[m + 4] if m + 4 < 7 else 0)) % P for m in range(4)])
    return out


def inputs(rng, H):
    f = rng.integers(0, P, (4, 2, 2, H), dtype=np.int64).astype(np.uint32)
    g = rng.integers(0, P, (4, 2, 2, H), dtype=np.int64).astype(np.uint32)
    r = [int(v) for v in rng.integers(0, P, 4)]
    Wb, C = fold_consts(r)
    return (f, g, Wb, C), dict(f=f, g=g, r=r)


def ref(rd, H, sample=None):
    """Exact: folded tables (numpy object math on a column sample, all of H for small H) and s(t) on Python ints."""
    f, g, r = rd["f"].astype(object), rd["g"].astype(object), rd["r"]
    cols = range(H) if sample is None else sample
    fp = np.zeros((4, 2, len(cols)), object)
    gp = np.zeros((4, 2, len(cols)), object)
    s = [[0] * 4 for _ in range(3)]
    for ci, h in enumerate(cols):
        vals = {}
        for name, x, outp in (("f", f, fp), ("g", g, gp)):
            for b in range(2):
                x0, x1 = [int(v) for v in x[:, 0, b, h]], [int(v) for v in x[:, 1, b, h]]
                y = [(a + c) % P for a, c in zip(x0, ext_mul(r, [(q - p_) % P for p_, q in zip(x0, x1)]))]
                outp[:, b, ci] = y
                vals[(name, b)] = y
        for t in range(3):
            ft = [((1 - t) * a + t * b) % P for a, b in zip(vals[("f", 0)], vals[("f", 1)])]
            gt = [((1 - t) * a + t * b) % P for a, b in zip(vals[("g", 0)], vals[("g", 1)])]
            s[t] = [(u + v) % P for u, v in zip(s[t], ext_mul(ft, gt))]
    return fp, gp, s


def impl(H, **kw):
    return round_fn


def count(H):
    return round_fn, arg_specs(H)


def arg_specs(H):
    return [((4, 2, 2, H), jnp.uint32), ((4, 2, 2, H), jnp.uint32), ((128, 128), jnp.int8), ((4, 4), jnp.int32)]


KERNELS = [dict(
    name="sumcheck_bb4_round",
    module=__name__,
    cfgs={
        "mac": dict(H=2**14),
        "H2p22": dict(H=2**22),     # 2^24 evaluations per table: 1 GiB read, 0.5 GiB written per round
    },
    inputs=inputs, ref=ref, impl=impl, count=count, arg_specs=arg_specs,
)]
