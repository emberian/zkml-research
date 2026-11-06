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


def impl(H, interpret=False, **kw):
    return round_pallas(interpret=interpret)


def count(H):
    """Counts from the XLA formulation (same algorithm, same packing factor)."""
    return round_fn, [((4, 2, 2, H), jnp.uint32), ((4, 2, 2, H), jnp.uint32), ((128, 128), jnp.int8),
                      ((4, 4), jnp.int32)]


def arg_specs(H):
    return [((4, 2, 2, H // LW, LW), jnp.uint32), ((4, 2, 2, H // LW, LW), jnp.uint32), ((128, 128), jnp.int8),
            ((4, 4 * G, 1), jnp.int32)]


def inputs_pallas(rng, H):
    (f, g, _, _), rd = inputs(rng, H)
    Wp, C = fold_consts_pallas(rd["r"])
    return (f.reshape(4, 2, 2, H // LW, LW), g.reshape(4, 2, 2, H // LW, LW), Wp, C), rd


def check_pallas(out, rd, H, sample_cols=4096):
    """f', g' on a column sample plus the full round sums, all against the Python-int reference."""
    fo, go, glo, ghi, S = out
    rng = np.random.default_rng(0)
    cols = sorted(rng.choice(H, min(H, sample_cols), replace=False).tolist()) if H > sample_cols else list(range(H))
    efp, egp, _ = ref(rd, H, sample=cols)
    fo, go = np.asarray(fo).reshape(4, 2, H)[:, :, cols], np.asarray(go).reshape(4, 2, H)[:, :, cols]
    ok_f = (fo.astype(object) == efp).all() and (go.astype(object) == egp).all()
    return bool(ok_f), combine_pallas(glo, ghi, S, H)


KERNELS = [dict(
    name="sumcheck_bb4_round",
    module=__name__,
    cfgs={
        "mac": dict(H=2**14),       # 16 rows of LW = 1024: two grid steps
        "H2p22": dict(H=2**22),     # 2^24 evaluations per table: 1 GiB read, 0.5 GiB written per round
    },
    inputs=None, ref=ref, impl=impl, count=count, arg_specs=arg_specs,
)]
KERNELS[0]["inputs"] = lambda rng, **p: inputs_pallas(rng, **p)


# ---------------------------------------------------------------------------------------------------------
# Pallas version. Storage: tables as [4 coord, 2 b_i, 2 b_i+1, R, LW] u32 with H = R * LW (column h = r*LW + l):
# the column axis is split into rows of LW lanes, so 8 consecutive rows ARE the 8 MXU packing groups and the
# packing is a merge of major dims into sublanes (free). One grid step = 8 rows = 8*LW columns.
#   limbs  D[(j, a, g), l] int8 offset bytes                          [128, LW]
#   fold   Z = Wp @ D, Wp[(c, m, g'), (j, a, g)] = Wm[(m, c), (j, a)] d(g, g')   -> limb c is Z[c] : [32 (m, g), LW]
#   sums   Gram A @ B^T [128, 128] per step, accumulated as (G & 0xffff, G >> 16) so int32 never overflows
# ---------------------------------------------------------------------------------------------------------
import functools

from jax.experimental import pallas as pl
from jax.experimental.pallas import tpu as pltpu

LW = 1024


def fold_consts_pallas(r):
    R = rmat(r)
    Wp = np.zeros((4, 4, G, 4, 4, G), np.int8)     # [c, m, g', j, a, g]
    C = np.zeros((4, 4 * G, 1), np.int32)          # [c, (m, g), 1]
    for m in range(4):
        tot = 0
        for j in range(4):
            for a in range(4):
                v = R[m][j] * pow(2, 8 * a, P) % P
                tot += v
                for c, dg in enumerate(bal4(v)):
                    for g in range(G):
                        Wp[c, m, g, j, a, g] = dg
        for c, byte in enumerate((128 * tot % P).to_bytes(4, "little")):
            C[c, m * G:(m + 1) * G, 0] = byte
    return Wp.reshape(128, 128), C


def _limbs_packed(x):
    """u32 [4 j, 8 g, LW] -> int8 [(j, a, g) = 128, LW] offset bytes."""
    xi = x.astype(jnp.int32)  # values < 2^31 (canonical mod P), so the signed view is exact
    planes = [(((xi >> (8 * a)) & 255) - 128) for a in range(4)]      # each [4, 8, LW]
    return jnp.stack(planes, axis=1).reshape(128, x.shape[-1]).astype(jnp.int8)


def _submod(a, b):
    d = a - b
    return jnp.where(d < 0, d + P, d)


def _fold_tile(x0, x1, w, cc):
    """x0, x1 int32 [4, 8, LW] canonical -> x0 + r (x1 - x0) mod P, int32 [4, 8, LW]."""
    d = _limbs_packed(_submod(x1, x0))
    z = jnp.dot(w, d, preferred_element_type=jnp.int32).reshape(4, 4 * G, x0.shape[-1])
    L = reduce_limbs([z[c] + cc[c] for c in range(4)], P)
    rd = (L[0] | (L[1] << 8) | (L[2] << 16) | (L[3] << 24)).reshape(4, G, x0.shape[-1])
    s = x0 - (P - rd)                     # int32: x0 + rd would overflow (2P > 2^31)
    return jnp.where(s < 0, s + P, s)


def _round_kernel(f_ref, g_ref, w_ref, c_ref, fo_ref, go_ref, glo_ref, ghi_ref, s_ref):
    @pl.when(pl.program_id(0) == 0)
    def _():
        glo_ref[...] = jnp.zeros_like(glo_ref)
        ghi_ref[...] = jnp.zeros_like(ghi_ref)
        s_ref[...] = jnp.zeros_like(s_ref)

    w = w_ref[...]
    cc = c_ref[...]
    f = f_ref[...].astype(jnp.int32)
    g = g_ref[...].astype(jnp.int32)
    f0, f1 = _fold_tile(f[:, 0, 0], f[:, 1, 0], w, cc), _fold_tile(f[:, 0, 1], f[:, 1, 1], w, cc)
    g0, g1 = _fold_tile(g[:, 0, 0], g[:, 1, 0], w, cc), _fold_tile(g[:, 0, 1], g[:, 1, 1], w, cc)
    fo_ref[:, 0] = f0.astype(jnp.uint32)
    fo_ref[:, 1] = f1.astype(jnp.uint32)
    go_ref[:, 0] = g0.astype(jnp.uint32)
    go_ref[:, 1] = g1.astype(jnp.uint32)

    def two_minus(x1, x0):
        t = x1 - (P - x1)                 # 2 x1 mod P without leaving int32
        t = jnp.where(t < 0, t + P, t)
        return _submod(t, x0)
    for t, (a, b) in enumerate(((f0, g0), (f1, g1), (two_minus(f1, f0), two_minus(g1, g0)))):
        A, B = _limbs_packed(a), _limbs_packed(b)
        Gm = jax.lax.dot_general(A, B, (((1,), (1,)), ((), ())), preferred_element_type=jnp.int32)
        glo_ref[t] += Gm & 0xFFFF
        ghi_ref[t] += Gm >> 16
        s_ref[t, 0] += A.astype(jnp.int32).sum(axis=1, keepdims=True)
        s_ref[t, 1] += B.astype(jnp.int32).sum(axis=1, keepdims=True)


def round_pallas(interpret=False):
    def f(fz, gz, Wp, C):
        """fz, gz u32 [4, 2, 2, R, LW]; returns f', g' u32 [4, 2, R, LW], Gram lo/hi int32 [3, 128, 128],
        column sums int32 [3, 2, 128, 1]."""
        R, lw = fz.shape[3], fz.shape[4]
        tab = lambda: pl.BlockSpec((4, 2, 2, G, lw), lambda i: (0, 0, 0, i, 0))
        out = lambda: pl.BlockSpec((4, 2, G, lw), lambda i: (0, 0, i, 0))
        acc = lambda shp: pl.BlockSpec(shp, lambda i: (0,) * len(shp))
        return pl.pallas_call(
            _round_kernel,
            out_shape=(jax.ShapeDtypeStruct((4, 2, R, lw), jnp.uint32), jax.ShapeDtypeStruct((4, 2, R, lw), jnp.uint32),
                       jax.ShapeDtypeStruct((3, 128, 128), jnp.int32), jax.ShapeDtypeStruct((3, 128, 128), jnp.int32),
                       jax.ShapeDtypeStruct((3, 2, 128, 1), jnp.int32)),
            grid=(R // G,),
            in_specs=[tab(), tab(), acc((128, 128)), acc((4, 4 * G, 1))],
            out_specs=(out(), out(), acc((3, 128, 128)), acc((3, 128, 128)), acc((3, 2, 128, 1))),
            compiler_params=pltpu.CompilerParams(dimension_semantics=("arbitrary",), vmem_limit_bytes=96 * 2**20),
            interpret=interpret,
        )(fz, gz, Wp, C)
    return f


def combine_pallas(glo, ghi, S, H):
    """Host: Gram (lo, hi) + column sums -> s(t) in BabyBear^4, exact (Python ints). Rows (j, a, g)."""
    glo, ghi, S = (np.asarray(x).astype(np.int64) for x in (glo, ghi, S))
    out = []
    for t in range(3):
        Gt = glo[t] + (ghi[t] << 16)
        Sa, Sb = S[t, 0, :, 0], S[t, 1, :, 0]
        acc = [0] * 7
        for j in range(4):
            for a in range(4):
                for l in range(4):
                    for b in range(4):
                        tot = 0
                        for g in range(G):
                            ia, ib = (j * 4 + a) * G + g, (l * 4 + b) * G + g
                            tot += int(Gt[ia, ib]) + 128 * int(Sb[ib]) + 128 * int(Sa[ia])
                        tot += 128 * 128 * H
                        acc[j + l] += tot << (8 * (a + b))
        out.append([(acc[m] + W * (acc[m + 4] if m + 4 < 7 else 0)) % P for m in range(4)])
    return out


def sums_numpy(rd, H):
    """Exact round sums, vectorized int64 (products of residues < 2^62, reduced before summing)."""
    f, g, r = rd["f"].astype(np.int64), rd["g"].astype(np.int64), rd["r"]

    def emul(a, b):
        c = [np.zeros(a.shape[1], np.int64) for _ in range(7)]
        for i in range(4):
            for j in range(4):
                c[i + j] = (c[i + j] + a[i] * b[j] % P) % P
        return np.stack([(c[m] + W * c[m + 4] % P) % P if m + 4 < 7 else c[m] for m in range(4)])
    rr = np.array(r, np.int64)[:, None] * np.ones((1, H), np.int64)

    def fold(x0, x1):
        return (x0 + emul(rr, (x1 - x0) % P)) % P
    f0, f1 = fold(f[:, 0, 0], f[:, 1, 0]), fold(f[:, 0, 1], f[:, 1, 1])
    g0, g1 = fold(g[:, 0, 0], g[:, 1, 0]), fold(g[:, 0, 1], g[:, 1, 1])
    out = []
    for ft, gt in ((f0, g0), (f1, g1), ((2 * f1 - f0) % P, (2 * g1 - g0) % P)):
        out.append([int(v) for v in emul(ft, gt).sum(axis=1) % P])
    return out


def prepare(rng, H):
    args, rd = inputs_pallas(rng, H)
    es = sums_numpy(rd, H)

    def check(o):
        okf, s = check_pallas(o, rd, H, sample_cols=2048)
        return bool(okf and s == es)
    return args, check


KERNELS[0]["prepare"] = prepare
