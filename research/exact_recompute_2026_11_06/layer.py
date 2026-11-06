"""One gpt-oss decoder layer, twice: a float64 reference (semantics of transformers'
modeling_gpt_oss.py, used to fit the fixed-point scales and to measure fidelity) and gptoss-int v0.
"""
import math

import numpy as np

import model as M
import tables as T
from weights import Shards, bf16_to_int

D, H, KV, HD, NE, TOPK = 2880, 64, 8, 64, 32, 4
EPS = 1e-5
FDT = np.float64     # the float reference's dtype; float32 gives a second honest float backend


class LayerWeights:
    def __init__(self, S: Shards, l: int):
        p = f"model.layers.{l}."
        self.l = l
        self.sliding = (l % 2 == 0)
        self.bits = {n: S.bf16_bits(p + n) for n in (
            "input_layernorm.weight", "post_attention_layernorm.weight",
            "self_attn.q_proj.weight", "self_attn.q_proj.bias", "self_attn.k_proj.weight", "self_attn.k_proj.bias",
            "self_attn.v_proj.weight", "self_attn.v_proj.bias", "self_attn.o_proj.weight", "self_attn.o_proj.bias",
            "self_attn.sinks", "mlp.router.weight", "mlp.router.bias",
            "mlp.experts.gate_up_proj_bias", "mlp.experts.down_proj_bias")}
        self.S, self.p = S, p
        self._mx = {}

    def f(self, n):
        return (self.bits[n].astype(np.uint32) << 16).view(np.float32).astype(FDT)

    def expert(self, which, e):
        key = (which, e)
        if key not in self._mx:
            q, ex = self.S.mxfp4(self.p + f"mlp.experts.{which}", e)
            self._mx[key] = M.IntMatrix.from_mxfp4(np.asarray(q), np.asarray(ex))
        return self._mx[key]

    def drop_experts(self):
        self._mx = {k: v for k, v in self._mx.items() if k[0] == "bf16"}

    def int_matrix(self, n):
        key = ("bf16", n)
        if key not in self._mx:
            self._mx[key] = M.IntMatrix.from_bf16(self.bits[n])
        return self._mx[key]


def expert_float(W: M.IntMatrix):
    return ((W.wh * float(1 << M.L20) + W.wl) * np.exp2(W.rowexp.astype(np.float64))[:, None]).astype(FDT)


# ---------------------------------------------------------------- float64 reference
def rope_f_at(x, pos0):
    inv, att = T.yarn_inv_freq()
    ang = np.arange(pos0, pos0 + x.shape[0])[:, None] * inv[None, :]
    c, s = (np.cos(ang) * att).astype(FDT), (np.sin(ang) * att).astype(FDT)
    a, b = x[..., :HD // 2], x[..., HD // 2:]
    return np.concatenate([a * c[:, None] - b * s[:, None], b * c[:, None] + a * s[:, None]], axis=-1)


def rope_f(x, T_):
    inv, att = T.yarn_inv_freq()
    ang = np.arange(T_)[:, None] * inv[None, :]
    c, s = np.cos(ang) * att, np.sin(ang) * att
    a, b = x[..., :HD // 2], x[..., HD // 2:]
    return np.concatenate([a * c[:, None] - b * s[:, None], b * c[:, None] + a * s[:, None]], axis=-1)


class KVCache:
    """Keys (after rotary) and values of the positions seen so far, per layer."""
    def __init__(self):
        self.k = None
        self.v = None

    def extend(self, xp, k, v):
        self.k = k if self.k is None else xp.concatenate([self.k, k], axis=0)
        self.v = v if self.v is None else xp.concatenate([self.v, v], axis=0)
        return self.k, self.v


def causal_mask(pos0, t, n, sliding):
    i = np.arange(pos0, pos0 + t)[:, None]
    j = np.arange(n)[None, :]
    return (j <= i) & ((i - j < 128) if sliding else True)


def route(lg_row):
    """Top-4 experts of one row of router logits (ties to the lower index)."""
    return sorted(range(NE), key=lambda e_: (-lg_row[e_], e_))[:TOPK]


def layer_float(Wt: LayerWeights, x, trace=None, cache=None, pos0=0):
    x = x.astype(FDT)
    t = x.shape[0]
    def norm(v, g):
        return v / np.sqrt((v * v).mean(-1, keepdims=True) + EPS) * g
    a = norm(x, Wt.f("input_layernorm.weight"))
    q = a @ Wt.f("self_attn.q_proj.weight").T + Wt.f("self_attn.q_proj.bias")
    k = a @ Wt.f("self_attn.k_proj.weight").T + Wt.f("self_attn.k_proj.bias")
    v = a @ Wt.f("self_attn.v_proj.weight").T + Wt.f("self_attn.v_proj.bias")
    q = rope_f_at(q.reshape(t, H, HD), pos0)
    k = rope_f_at(k.reshape(t, KV, HD), pos0)
    v = v.reshape(t, KV, HD)
    if cache is not None:
        k, v = cache.extend(np, k, v)
    n = k.shape[0]
    sinks = Wt.f("self_attn.sinks")
    o = np.zeros((t, H, HD), dtype=FDT)
    mask = causal_mask(pos0, t, n, Wt.sliding)
    for h in range(H):
        g = h // (H // KV)
        sc = (q[:, h] @ k[:, g].T) / 8.0
        sc = np.where(mask, sc, -np.inf)
        comb = np.concatenate([sc, np.full((t, 1), sinks[h])], axis=1)
        comb = comb - comb.max(1, keepdims=True)
        pr = np.exp(comb)
        pr = pr / pr.sum(1, keepdims=True)
        o[:, h] = pr[:, :-1] @ v[:, g]
    attn = o.reshape(t, H * HD) @ Wt.f("self_attn.o_proj.weight").T + Wt.f("self_attn.o_proj.bias")
    x1 = x + attn
    m = norm(x1, Wt.f("post_attention_layernorm.weight"))
    logits = m @ Wt.f("mlp.router.weight").T + Wt.f("mlp.router.bias")
    out = np.zeros_like(x1)
    gub, db = Wt.f("mlp.experts.gate_up_proj_bias"), Wt.f("mlp.experts.down_proj_bias")
    by = {}
    for i in range(t):
        top = np.argsort(-logits[i], kind="stable")[:TOPK]
        w = np.exp(logits[i, top] - logits[i, top].max()); w /= w.sum()
        for e, we in zip(top, w):
            by.setdefault(int(e), []).append((i, we))
    for e in sorted(by):
        rows = np.array([r for r, _ in by[e]]); ws = np.array([w_ for _, w_ in by[e]])
        gu = m[rows] @ expert_float(Wt.expert("gate_up_proj", e)).T + gub[e]
        gate, up = np.minimum(gu[:, 0::2], 7.0), np.clip(gu[:, 1::2], -7.0, 7.0)
        h_ = (up + 1.0) * gate / (1.0 + np.exp(-1.702 * gate))
        np.add.at(out, rows, (ws[:, None] * (h_ @ expert_float(Wt.expert("down_proj", e)).T + db[e])).astype(FDT))
    if trace is not None:
        trace.update(a=a, q=q, k=k, v=v, o=o, x1=x1, m=m, logits=logits, x2=x1 + out)
    return x1 + out


# ---------------------------------------------------------------- gptoss-int v0
FS = 16          # residual stream fixed point
GS = 16          # norm gain constant: rha(g * sqrt(D) * 2^GS)
RM = 48          # norm reciprocal: Rc = floor((2^RM + sigma/2) / sigma)
FR = 16          # router logits
FG = 12          # gate and up
FW = 16          # routing weights
CL = M.ACLAMP_HI


def gain_const(g_bits):
    m, e = bf16_to_int(g_bits)
    g = m.astype(np.float64) * np.exp2(e.astype(np.float64))
    return T.rha(g * math.sqrt(D) * 2.0 ** GS)


NB = 25          # the norm's sum of squares runs on values below 2^NB (2880 * 2^50 < 2^62)


def rq0(xp, a, k):
    """rq for k >= 0 (k = 0 is the identity), k per row."""
    return xp.where(k == 0, a, M.rq(xp, a, xp.maximum(k, 1)))


def norm_int(xp, x, gs, fa):
    """Integer RMS norm. gpt-oss's residual carries massive activations (|x| up to ~42,000 between
    layers 6 and 16), so the sum of squares runs on x shifted right by s per row, s the number of
    k in 0..13 with max|x_row| >= 2^(NB+k); rows below 2^NB have s = 0 and are unchanged. The
    numerator keeps every bit of x: t = rq(x * Rc', RM - 24 + s), Rc' = 2^RM / sigma'."""
    mx = xp.max(xp.abs(x), axis=-1, keepdims=True)
    assert int(xp.max(mx)) < (1 << (NB + 14)), "residual beyond the v0 norm window"
    s = sum((mx >= (1 << (NB + k))).astype(xp.int64) for k in range(14))
    xs = rq0(xp, x, s)
    V = xp.sum(xs * xs, axis=-1, keepdims=True)
    E = int(round(EPS * D * 2.0 ** (2 * FS)))
    sigma = M.isqrt(xp, V + rq0(xp, xp.full(V.shape, E, dtype=xp.int64), 2 * s))
    Rc = (xp.left_shift(xp.int64(1), RM) + xp.right_shift(sigma, 1)) // sigma
    t = M.rq(xp, x * Rc, RM - 24 + s)
    return M.clamp(xp, M.rq(xp, t * gs[None, :], 24 + GS - fa), M.ACLAMP_LO, CL)


def rope_int(xp, x, C, S):
    a, b = x[..., : HD // 2], x[..., HD // 2:]
    c, s = C[:, None, :], S[:, None, :]
    return xp.concatenate([M.rq(xp, c * a - s * b, T.CS), M.rq(xp, c * b + s * a, T.CS)], axis=-1)


def layer_int(xp, kern, Wt: LayerWeights, x, P, trace=None, cache=None, pos0=0):
    """x: int64 [t, D] at 2^-FS. P: fitted exponents {fa, fqk, fv, fm, fh}."""
    t = x.shape[0]
    fa, fqk, fv, fm, fh = P["fa"], P["fqk"], P["fv"], P["fm"], P["fh"]
    a = norm_int(xp, x, xp.asarray(gain_const(Wt.bits["input_layernorm.weight"])), fa)
    lin = lambda inp, f_in, n, fo: M.linear(xp, kern, inp, f_in, Wt.int_matrix(n + ".weight"), Wt.bits[n + ".bias"], fo)
    q = M.clamp(xp, lin(a, fa, "self_attn.q_proj", fqk), M.ACLAMP_LO, CL).reshape(t, H, HD)
    k = M.clamp(xp, lin(a, fa, "self_attn.k_proj", fqk), M.ACLAMP_LO, CL).reshape(t, KV, HD)
    v = M.clamp(xp, lin(a, fa, "self_attn.v_proj", fv), M.ACLAMP_LO, CL).reshape(t, KV, HD)
    C, S = (xp.asarray(z[pos0:]) for z in T.rope_tables(pos0 + t))
    q = M.clamp(xp, rope_int(xp, q, C, S), M.ACLAMP_LO, CL)
    k = M.clamp(xp, rope_int(xp, k, C, S), M.ACLAMP_LO, CL)
    EX = xp.asarray(T.exp_table())
    u0 = EX.shape[0]
    fsc = 2 * fqk + 3                       # score fixed point: q.k / 8
    sm, se = bf16_to_int(Wt.bits["self_attn.sinks"])
    sink = M.to_scale(xp, xp.asarray(sm), xp.asarray(se), fsc)
    if cache is not None:
        k, v = cache.extend(xp, k, v)
    mask = xp.asarray(causal_mask(pos0, t, k.shape[0], Wt.sliding))
    rep = H // KV
    kk = xp.repeat(k, rep, axis=1)          # [t, H, HD]
    vv = xp.repeat(v, rep, axis=1)
    sc = kern.einsum("ihc,jhc->hij", q, kk, 2, 2)   # exact int64, at 2^-(2 fqk); the 1/8 is in fsc
    sc = xp.where(mask[None], sc, xp.iinfo(xp.int64).min // 4)
    mx = xp.maximum(sc.max(axis=2), sink[:, None])                      # [H, t]
    def ex(z):
        u = xp.right_shift(mx[..., None] - z, fsc - T.RX) if z.ndim == 3 else xp.right_shift(mx - z, fsc - T.RX)
        return xp.where(u < u0, EX[xp.minimum(u, u0 - 1)], 0)
    e = xp.where(mask[None], ex(sc), 0)                                  # [H, t, t]
    es = ex(xp.broadcast_to(sink[:, None], mx.shape))                    # [H, t]
    Z = e.sum(axis=2) + es
    acc = kern.einsum("hij,jhc->ihc", e, vv, 3, 2)                             # [t, H, HD]
    Zt = xp.transpose(Z)[:, :, None]
    o = (2 * acc + Zt) // (2 * Zt)
    o = M.clamp(xp, o, M.ACLAMP_LO, CL).reshape(t, H * HD)
    x1 = x + lin(o, fv, "self_attn.o_proj", FS)
    m = norm_int(xp, x1, xp.asarray(gain_const(Wt.bits["post_attention_layernorm.weight"])), fm)
    logits = lin(m, fm, "mlp.router", FR)                                # [t, NE]
    out = xp.zeros_like(x1)
    gubm, gube = bf16_to_int(Wt.bits["mlp.experts.gate_up_proj_bias"])
    dbm, dbe = bf16_to_int(Wt.bits["mlp.experts.down_proj_bias"])
    G = xp.asarray(T.glu_table())
    lg = np.asarray(logits)
    EXn = np.asarray(EX)
    by = {}
    for i in range(t):
        top = route([int(z) for z in lg[i]])
        lt = lg[i, top].astype(np.int64)
        u = (lt.max() - lt) >> (FR - T.RX)
        ee = np.where(u < u0, EXn[np.minimum(u, u0 - 1)], 0)
        Zr = int(ee.sum())
        wts = (2 * ee * (1 << FW) + Zr) // (2 * Zr)
        for e_, w_ in zip(top, wts):
            by.setdefault(e_, []).append((i, int(w_)))
    # every row's MoE output is the sum over its four experts of rq(w * down(...)); integer sums
    # commute, so grouping the rows by expert gives the same integers as the per-row loop
    moe = xp.zeros((t, D), dtype=xp.int64)
    for e_ in sorted(by):
        rows = np.array([r for r, _ in by[e_]])
        ws = xp.asarray(np.array([w_ for _, w_ in by[e_]], dtype=np.int64))
        W1 = Wt.expert("gate_up_proj", e_)
        gu = M.linear(xp, kern, m[rows], fm, W1, None, FG)
        gu = gu + M.to_scale(xp, xp.asarray(gubm[e_]), xp.asarray(gube[e_]), FG)[None, :]
        gate = xp.minimum(gu[:, 0::2], 7 << FG)
        up = M.clamp(xp, gu[:, 1::2], -(7 << FG), 7 << FG)
        key = M.clamp(xp, M.rq(xp, gate, FG - T.GK), T.GLO << T.GK, T.GHI << T.GK)
        glu = G[key - (T.GLO << T.GK)]
        h_ = M.clamp(xp, M.rq(xp, (up + (1 << FG)) * glu, FG + T.FT - fh), M.ACLAMP_LO, CL)
        W2 = Wt.expert("down_proj", e_)
        dn = M.linear(xp, kern, h_, fh, W2, None, FS)
        dn = dn + M.to_scale(xp, xp.asarray(dbm[e_]), xp.asarray(dbe[e_]), FS)[None, :]
        contrib = M.rq(xp, ws[:, None] * dn, FW)
        if xp is np:
            np.add.at(moe, rows, contrib)
        else:
            moe = moe.at[xp.asarray(rows)].add(contrib)
    x2 = x1 + moe
    if trace is not None:
        trace.update(a=a, q=q, k=k, v=v, o=o, x1=x1, m=m, logits=logits, x2=x2)
    return x2


def fit_exponents(tr, headroom=1.25):
    """Power-of-two fixed points from a float64 trace: the finest f with max|v| * 2^f * headroom <= 32639."""
    def f(v):
        return int(math.floor(math.log2(M.ACLAMP_HI / (headroom * float(np.abs(v).max())))))
    return {"fa": f(tr["a"]), "fqk": min(f(tr["q"]), f(tr["k"])), "fv": f(tr["v"]), "fm": f(tr["m"]), "fh": 9}
