#!/usr/bin/env python3
"""
einsum_turbo_pricing.py -- Deterministic BabyBear + Ext4 simulation, constructive
falsifier verification, and exact operation-count pricing for Lane 1 (`einsum-turbo`):
Next-generation `EinSumcheck` speedups on `gptoss-int v0` (`gpt-oss-20b`).

Covers all four concrete speedups:
  1. Gruen `eq`-Factored `EinSumcheck` (`ePrint 2024/108` §3.2 + `2025/1117` §5.1):
     - Mode 1: Wire-transparent Setty-Thaler cubic reconstruction (`s_u(X) = l_u(X)*q_u(X)`,
       zero verifier diff against `AirSumcheckCubic`, deterministic `l_u(1) == 0` fallback).
     - Mode 2: Gruen direct-`q_u` degree-`m_u` wire (`2` Ext4 evals `{0, inf}` per round for
       `m_u = 2`, zero prover inversions, `2/|F|` per-round soundness on `F_{>=2}`).
     - End-to-end prover + verifier + falsifiers on un-repeated GQA (`tgrd,ngd -> tgrn`,
       `tgrn,ngd -> tgrd`) and native MXFP4 (`ikb,jkb,jk -> ij`, where 18/25 `gate_up`
       rounds become quadratic degree-2!).
  2. Optimal Elimination Order + `SVO` (`ePrint 2025/1117`) for Native MXFP4 (`ikb,jkb,jk -> ij`):
     - Exact simulation and closed-form pricing of all 6 variable-block schedules
       (`j->k->b`, `j->b->k`, `k->j->b`, `k->b->j`, `b->j->k`, `b->k->j`) on `gpt-oss-20b`'s
       real shapes (`gate_up`: 5760x2880, `down`: 2880x2880, `q_proj`: 4096x2880).
     - Generic Toom-Cook `SVO` (`l_0 in {1,2,3}`) vs Tensor-Factored Block-Bind (`l_0 = 5`)
       + E2M1 4-bit-plane Horner addition chain (`0` multiplications on `Q[j,k,b]`!).
  3. Block-Banded Sliding-Window `EinSumcheck` (`W = 128` on 12/24 `gpt-oss-20b` layers)
     + Causal Block-Triangular Pruning on the 12 odd full-attention layers:
     - Bit-exact integer verification against `gptoss-int v0`'s `layer_int` (`layer.py:211-227`)
       using the exact `EXP_TAB` (`u0 = 2840`), `sinks`, and Euclidean `(2*acc + Zt)//(2*Zt)`.
     - End-to-end BabyBear + Ext4 prover & verifier for Block-Windowed GQA (`bugrd,bwgd -> bgruw`
       and `bgruw,bwgd -> bugrd`) + zero-extra-commitment `step_beta` carry-chain MLE reduction
       to committed `K[b,v,g,d]` and `V[b,v,g,d]`.
  4. Active-4 Sparse MoE `EinSumcheck` + 24-Layer Uniform Folding:
     - End-to-end BabyBear + Ext4 verification of bucketed Active-4 MoE + multi-layer uniform
       folding with zero-padded dummy-layer skipping.
     - Exact analytical + Monte Carlo pricing across `T in {1, 8, 32, 128, 512, 2048, 4096, 16384}`
       exposing the coupon-collector weight-scan saturation (`4 -> 32` active experts), dyadic
       bucket-padding overhead vs Jagged-PCS flatline, and `192-1536 -> 2` sumcheck collapse.

Usage:
  python3 research/speedup_wave_2026_11_21/experiments/einsum_turbo_pricing.py
"""

import math
from typing import Dict, List, Tuple, Any
import numpy as np

# ---------------------------------------------------------------------------
# Constants: BabyBear + Ext4 = F_p[X]/(X^4 - 11), and gpt-oss-20b architecture
# ---------------------------------------------------------------------------
P = (1 << 31) - (1 << 27) + 1   # BabyBear: 2013265921 = 15 * 2^27 + 1
W_BINOM = 11                    # Ext4 = F_p[X] / (X^4 - 11)

D_MODEL = 2880
H_Q = 64
H_KV = 8
GQA_REP = H_Q // H_KV           # 8
HD = 64
N_LAYERS = 24
N_SLIDING_LAYERS = 12           # l % 2 == 0 in layer.py:21
N_FULL_LAYERS = 12              # l % 2 == 1
W_SLIDE = 128
N_EXPERTS = 32
TOP_K = 4

E2M1_X2_VALS = np.array([-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12], dtype=np.int64)

# Cost weights matching research/zktransformer_2026_11_20/experiments/{einsum_gqa_counts,exp_pricing}.py
BB_MULS_PER_EXT_BASE = 4
BB_MULS_PER_EXT_EXT_KAR = 9
BB_MULS_PER_EXT_EXT_SB = 16
BYTES_PER_EXT4 = 16             # 4 x u32 BabyBear felts


# ---------------------------------------------------------------------------
# 1. BabyBear & Ext4 Vectorized Arithmetic + Exact Operation Counter
# ---------------------------------------------------------------------------
class OpCounter:
    def __init__(self):
        self.base_muls = 0
        self.ext_base_muls = 0
        self.ext_ext_muls = 0
        self.ext_adds = 0
        self.ext_invs = 0
        self.peak_ext4_bytes = 0

    def note_buf(self, n_ext4_elems: int):
        b = int(n_ext4_elems) * BYTES_PER_EXT4
        if b > self.peak_ext4_bytes:
            self.peak_ext4_bytes = b

    def bb_equiv_kar(self) -> int:
        return self.base_muls + BB_MULS_PER_EXT_BASE * self.ext_base_muls + BB_MULS_PER_EXT_EXT_KAR * self.ext_ext_muls


def ext_from_int(v: int) -> np.ndarray:
    return np.array([v % P, 0, 0, 0], dtype=np.int64)


def ext_zero() -> np.ndarray:
    return np.zeros(4, dtype=np.int64)


def ext_one() -> np.ndarray:
    return np.array([1, 0, 0, 0], dtype=np.int64)


def ext_add(a: np.ndarray, b: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    if ctr is not None:
        ctr.ext_adds += math.prod(np.broadcast_shapes(a.shape[:-1], b.shape[:-1]))
    return (a + b) % P


def ext_sub(a: np.ndarray, b: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    if ctr is not None:
        ctr.ext_adds += math.prod(np.broadcast_shapes(a.shape[:-1], b.shape[:-1]))
    return (a - b) % P


def ext_mul_base(e: np.ndarray, s: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """Multiply Ext4 array `e` (..., 4) by base-field array `s` (...)."""
    if ctr is not None:
        ctr.ext_base_muls += math.prod(np.broadcast_shapes(e.shape[:-1], s.shape))
    return (e * (s % P)[..., None]) % P


def ext_mul(a: np.ndarray, b: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """Multiply two Ext4 arrays (..., 4) in F_p[X]/(X^4 - 11)."""
    out_shape = np.broadcast_shapes(a.shape[:-1], b.shape[:-1])
    if ctr is not None:
        ctr.ext_ext_muls += math.prod(out_shape)
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    t_hi0 = ((a1 * b3) % P + (a2 * b2) % P + (a3 * b1) % P) % P
    t_hi1 = ((a2 * b3) % P + (a3 * b2) % P) % P
    c0 = ((a0 * b0) % P + W_BINOM * t_hi0) % P
    c1 = ((a0 * b1) % P + (a1 * b0) % P + W_BINOM * t_hi1) % P
    c2 = ((a0 * b2) % P + (a1 * b1) % P + (a2 * b0) % P + W_BINOM * ((a3 * b3) % P)) % P
    c3 = ((a0 * b3) % P + (a1 * b2) % P + (a2 * b1) % P + (a3 * b0) % P) % P
    return np.stack([c0, c1, c2, c3], axis=-1)


def ext_inv(a: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """Invert nonzero `a` in Ext4 = F_p[X]/(X^4 - 11) via quadratic tower norm over F_p[Y]/(Y^2 - 11):
    Write a = (a0 + a2*Y) + X*(a1 + a3*Y) = U + X*V with X^2 = Y, Y^2 = 11.
    Norm to F_p[Y]/(Y^2 - 11): N = U^2 - Y*V^2 = n0 + n1*Y.
    Norm to F_p: M = n0^2 - 11*n1^2 in F_p^*. Invert M in F_p, then lift back."""
    assert not np.array_equal(a % P, ext_zero()), "Division by zero in Ext4!"
    if ctr is not None:
        ctr.ext_invs += 1
    a0, a1, a2, a3 = [int(x) % P for x in a]
    # U = a0 + a2*Y => U^2 = (a0^2 + 11*a2^2) + (2*a0*a2)*Y
    u2_0 = (a0 * a0 + W_BINOM * a2 * a2) % P
    u2_1 = (2 * a0 * a2) % P
    # V = a1 + a3*Y => V^2 = (a1^2 + 11*a3^2) + (2*a1*a3)*Y => Y*V^2 = 11*v2_1 + v2_0*Y
    v2_0 = (a1 * a1 + W_BINOM * a3 * a3) % P
    v2_1 = (2 * a1 * a3) % P
    n0 = (u2_0 - W_BINOM * v2_1) % P
    n1 = (u2_1 - v2_0) % P
    m_fp = (n0 * n0 - W_BINOM * n1 * n1) % P
    m_inv = pow(m_fp, P - 2, P)
    # N^{-1} = (n0 - n1*Y) * m_inv = i0 + i1*Y
    i0 = (n0 * m_inv) % P
    i1 = ((-n1) * m_inv) % P
    # a^{-1} = (U - X*V) * (i0 + i1*Y)
    # even part U * N^{-1} = (a0 + a2*Y)(i0 + i1*Y) = (a0*i0 + 11*a2*i1) + (a0*i1 + a2*i0)*Y
    r0 = (a0 * i0 + W_BINOM * a2 * i1) % P
    r2 = (a0 * i1 + a2 * i0) % P
    # odd part -V * N^{-1} = -(a1 + a3*Y)(i0 + i1*Y)
    r1 = (-(a1 * i0 + W_BINOM * a3 * i1)) % P
    r3 = (-(a1 * i1 + a3 * i0)) % P
    res = np.array([r0, r1, r2, r3], dtype=np.int64)
    assert np.array_equal(ext_mul(a, res), ext_one())
    return res


def ext_sum_axis(arr: np.ndarray, axis: int) -> np.ndarray:
    """Exact modular sum along `axis` without int64 overflow (P < 2^31 => chunk <= 4B)."""
    # arr elements are in [0, P), P < 2^31, so up to 2^32 terms fit in int64 before overflow!
    return arr.sum(axis=axis) % P


def build_eq_table(r: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """LSB-first eq(r, x) table of shape (2^k, 4) in max(0, 2^k - 2) Ext4 muls."""
    k = r.shape[0]
    if k == 0:
        return ext_one()[None, :]
    one = ext_one()
    tbl = np.stack([ext_sub(one, r[0]), r[0]], axis=0)
    for i in range(1, k):
        hi = ext_mul(tbl, r[i], ctr)
        lo = ext_sub(tbl, hi)
        tbl = np.concatenate([lo, hi], axis=0)
    return tbl


def build_eq_suffix_tables(r: np.ndarray, ctr: OpCounter = None) -> List[np.ndarray]:
    """
    For Gruen LSB-first elimination of `r[0..ell-1]`:
    Returns `suf` of length `ell` where `suf[m]` (m = 0..ell-1) has shape `(2^m, 4)`
    representing `eq(r[ell-m : ell], x_rest)` with `r[ell-m]` at stride 1 (LSB).
    Round `idx` (0..ell-1) uses `suf[ell - 1 - idx]`.
    Exact Ext4 muls = max(0, 2^(ell - 1) - 2) (`r[0]` is NEVER multiplied into any table!).
    """
    ell = r.shape[0]
    if ell == 0:
        return []
    one = ext_one()
    suf: List[np.ndarray] = [one[None, :]]  # m = 0: shape (1, 4)
    if ell >= 2:
        # m = 1: variable r[ell - 1], 0 muls
        suf.append(np.stack([ext_sub(one, r[ell - 1]), r[ell - 1]], axis=0))
        for m in range(2, ell):
            # Prepend r[ell - m] at stride 1 (LSB) beneath existing (m-1) MSB vars:
            prev = suf[m - 1]                       # shape (2^(m-1), 4)
            hi = ext_mul(prev, r[ell - m], ctr)     # 2^(m-1) Ext4 muls
            lo = ext_sub(prev, hi)
            cur = np.stack([lo, hi], axis=1).reshape(-1, 4)
            suf.append(cur)
    return suf


def eval_eq_point(r: np.ndarray, z: np.ndarray) -> np.ndarray:
    one = ext_one()
    acc = one.copy()
    for i in range(r.shape[0]):
        rz = ext_mul(r[i], z[i])
        term = ext_add(ext_sub(ext_sub(one, r[i]), z[i]), ext_add(rz, rz))
        acc = ext_mul(acc, term)
    return acc


def mle_eval_base_tensor(tensor_flat: np.ndarray, point: np.ndarray) -> np.ndarray:
    eq = build_eq_table(point)
    return ((eq * ((tensor_flat % P)[:, None])) % P).sum(axis=0) % P


def partial_eval_f1_base(base_matrix: np.ndarray, r_f1: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    eq_f1 = build_eq_table(r_f1, ctr)
    f1_len, rem_len = base_matrix.shape
    if ctr is not None:
        ctr.ext_base_muls += f1_len * rem_len
    out = np.zeros((rem_len, 4), dtype=np.int64)
    b_mod = base_matrix % P
    for row in range(f1_len):
        out = (out + ((eq_f1[row][None, :] * b_mod[row, :, None]) % P)) % P
    return out


def eval_quad_from_0_1_inf(q0: np.ndarray, q1: np.ndarray, q_inf: np.ndarray, x: np.ndarray) -> np.ndarray:
    """Evaluate quadratic q(X) = q0 + c1*X + q_inf*X^2 at X = x, where c1 = q1 - q0 - q_inf."""
    c1 = ext_sub(ext_sub(q1, q0), q_inf)
    x2 = ext_mul(x, x)
    return ext_add(q0, ext_add(ext_mul(c1, x), ext_mul(q_inf, x2)))


def eval_cubic_from_0_1_2_inf(p0: np.ndarray, p1: np.ndarray, p2: np.ndarray, c3: np.ndarray, x: np.ndarray) -> np.ndarray:
    """Evaluate cubic p(X) = c0 + c1*X + c2*X^2 + c3*X^3 at X = x."""
    inv2 = pow(2, P - 2, P)
    six_c3 = (6 * c3) % P
    two_c2 = ext_sub(ext_add(ext_sub(p2, ext_add(p1, p1)), p0), six_c3)
    c2 = (two_c2 * inv2) % P
    c1 = ext_sub(ext_sub(ext_sub(p1, p0), c2), c3)
    x2 = ext_mul(x, x)
    x3 = ext_mul(x2, x)
    return ext_add(ext_add(p0, ext_mul(c1, x)), ext_add(ext_mul(c2, x2), ext_mul(c3, x3)))


# ---------------------------------------------------------------------------
# 2. SUBPROBLEM 1: Gruen `eq`-Factored `EinSumcheck` (Mode 1 & Mode 2)
# ---------------------------------------------------------------------------
def prove_gruen_2op_mode2_direct(
    r_f2: np.ndarray,
    T1_rem: np.ndarray,
    T2_rem: np.ndarray,
    challenges: np.ndarray,
    ctr: OpCounter = None,
) -> Tuple[List[Tuple[np.ndarray, ...]], np.ndarray, np.ndarray]:
    """
    Gruen `eq`-factored 2-operand `EinSumcheck` (Mode 2: direct degree-2 `q_u(X)` messages).
    In every round `u in F_{>=2}`:
      q_u(X) = sum_{x_rest} eq(r_{>u}, x_rest) sum_y T1(X, x_rest, y) * T2(X, x_rest, y)
    has degree `m_u = 2`! Prover computes ONLY `{q_u(0), q_u(inf)}` (`2` inner-product muls
    per pair instead of 4 in `{0,1,2,3}` or 3 in `{0,1,inf}`) and ZERO prover inversions
    (unless `r_f2[u] == 0`, in which `2^-124` fallback case prover also sends `q_u(1)`).
    In every round `v in S`:
      q_v(X) = sum_{y_rest} T1_y(X, y_rest) * T2_y(X, y_rest)
    also has degree 2, evaluated at `{0, inf}` (`2` inner-product muls + `2` fold muls = `4` muls/pair).
    """
    ell = r_f2.shape[0]
    S_len = T1_rem.shape[1]
    mu_s = int(round(math.log2(S_len)))
    suf_tables = build_eq_suffix_tables(r_f2, ctr)

    A = T1_rem.copy()
    B = T2_rem.copy()
    if ctr is not None:
        ctr.note_buf(A.shape[0] * A.shape[1] + B.shape[0] * B.shape[1])

    msgs: List[Tuple[np.ndarray, ...]] = []
    for r in range(ell):
        ch = challenges[r]
        A0, A1 = A[0::2], A[1::2]
        B0, B1 = B[0::2], B[1::2]
        dA = ext_sub(A1, A0, ctr)
        dB = ext_sub(B1, B0, ctr)

        Q0 = ext_sum_axis(ext_mul(A0, B0, ctr), axis=1)
        q_inf = ext_sum_axis(ext_mul(dA, dB, ctr), axis=1)

        if r < ell - 1:
            suf = suf_tables[ell - 1 - r]
            qu0 = ext_sum_axis(ext_mul(suf, Q0, ctr), axis=0)
            qu_inf = ext_sum_axis(ext_mul(suf, q_inf, ctr), axis=0)
        else:
            qu0 = Q0[0]
            qu_inf = q_inf[0]

        if np.array_equal(r_f2[r] % P, ext_zero()):
            # Deterministic completeness fallback when r_u == 0 (prob ~ 2^-124):
            Q1 = ext_sum_axis(ext_mul(A1, B1, ctr), axis=1)
            qu1 = ext_sum_axis(ext_mul(suf_tables[ell - 1 - r], Q1, ctr), axis=0) if r < ell - 1 else Q1[0]
            msgs.append((qu0, qu_inf, qu1))
        else:
            msgs.append((qu0, qu_inf))

        A = ext_add(A0, ext_mul(dA, ch, ctr), ctr)
        B = ext_add(B0, ext_mul(dB, ch, ctr), ctr)

    A_y = A[0]
    B_y = B[0]
    for r in range(mu_s):
        ch = challenges[ell + r]
        A0, A1 = A_y[0::2], A_y[1::2]
        B0, B1 = B_y[0::2], B_y[1::2]
        dA = ext_sub(A1, A0, ctr)
        dB = ext_sub(B1, B0, ctr)

        qv0 = ext_sum_axis(ext_mul(A0, B0, ctr), axis=0)
        qv_inf = ext_sum_axis(ext_mul(dA, dB, ctr), axis=0)
        msgs.append((qv0, qv_inf))

        A_y = ext_add(A0, ext_mul(dA, ch, ctr), ctr)
        B_y = ext_add(B0, ext_mul(dB, ch, ctr), ctr)

    return msgs, A_y[0], B_y[0]


def verify_gruen_2op_mode2_direct(
    claimed_H: np.ndarray,
    r_f2: np.ndarray,
    msgs: List[Tuple[np.ndarray, ...]],
    challenges: np.ndarray,
    final_T1_eval: np.ndarray,
    final_T2_eval: np.ndarray,
) -> bool:
    """
    Mode 2 Verifier (`ePrint 2024/108` §3.3 & App. A.3):
      - Rounds `0..ell-1`: solves `q_u(1) = r_u^{-1} * (sigma' - (1 - r_u)*q_u(0))`
        (or checks `(1 - r_u)*q_u(0) == sigma'` when `r_u == 0`), then updates `sigma' = q_u(ch_u)`.
        Notice `sigma'_ell` MUST connect directly into Phase 2 without disconnecting
        the `F_{>=2} -> S` bridge (`audit-blog-zksecurity-jolt-uniskip.txt` guard!).
      - Rounds `ell..ell+mu_s-1`: solves `q_v(1) = sigma' - q_v(0)`, updates `sigma' = q_v(ch_v)`.
      - Terminal check: `sigma' == final_T1_eval * final_T2_eval` (`eq` already stripped!).
    """
    ell = r_f2.shape[0]
    if len(msgs) != challenges.shape[0]:
        return False
    one = ext_one()
    sigma = claimed_H.copy()
    for r, msg in enumerate(msgs):
        if r < ell:
            ru = r_f2[r]
            if np.array_equal(ru % P, ext_zero()):
                if len(msg) != 3:
                    return False
                qu0, qu_inf, qu1 = msg
                if not np.array_equal(qu0 % P, sigma % P):
                    return False
            else:
                if len(msg) != 2:
                    return False
                qu0, qu_inf = msg
                lhs0 = ext_mul(ext_sub(one, ru), qu0)
                qu1 = ext_mul(ext_inv(ru), ext_sub(sigma, lhs0))
            sigma = eval_quad_from_0_1_inf(qu0, qu1, qu_inf, challenges[r])
        else:
            if len(msg) != 2:
                return False
            qv0, qv_inf = msg
            qv1 = ext_sub(sigma, qv0)
            sigma = eval_quad_from_0_1_inf(qv0, qv1, qv_inf, challenges[r])

    expected = ext_mul(final_T1_eval, final_T2_eval)
    return np.array_equal(sigma % P, expected % P)


def prove_gruen_2op_mode1_wire_transparent(
    claimed_H: np.ndarray,
    r_f2: np.ndarray,
    T1_rem: np.ndarray,
    T2_rem: np.ndarray,
    challenges: np.ndarray,
    ctr: OpCounter = None,
) -> Tuple[List[Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]], np.ndarray, np.ndarray]:
    """
    Setty-Thaler (`2025/105` / `2025/1117` Procedure 8) Wire-Transparent Gruen Prover:
    Performs the EXACT same 2-point `{0, inf}` array scans as Mode 2, reconstructs
    `s_u(X) = l_u(X) * q_u(X)` in O(1) scalar ops per round, and emits standard cubic
    messages `(p0, p1, p2, c3)` accepted by an UNMODIFIED `AirSumcheckCubic` verifier!
    Includes exact fallback when `l_u(1) == 0` (`r_u == 0` or `eq_prefix == 0`).
    """
    ell = r_f2.shape[0]
    S_len = T1_rem.shape[1]
    mu_s = int(round(math.log2(S_len)))
    suf_tables = build_eq_suffix_tables(r_f2, ctr)

    A = T1_rem.copy()
    B = T2_rem.copy()
    one = ext_one()
    two = ext_from_int(2)
    eq_prefix = one.copy()
    sigma = claimed_H.copy()
    cubic_msgs = []

    for r in range(ell):
        ch = challenges[r]
        ru = r_f2[r]
        A0, A1 = A[0::2], A[1::2]
        B0, B1 = B[0::2], B[1::2]
        dA = ext_sub(A1, A0, ctr)
        dB = ext_sub(B1, B0, ctr)

        Q0 = ext_sum_axis(ext_mul(A0, B0, ctr), axis=1)
        q_inf = ext_sum_axis(ext_mul(dA, dB, ctr), axis=1)
        if r < ell - 1:
            suf = suf_tables[ell - 1 - r]
            qu0 = ext_sum_axis(ext_mul(suf, Q0, ctr), axis=0)
            qu_inf = ext_sum_axis(ext_mul(suf, q_inf, ctr), axis=0)
        else:
            qu0 = Q0[0]
            qu_inf = q_inf[0]

        l0 = ext_mul(eq_prefix, ext_sub(one, ru), ctr)
        l1 = ext_mul(eq_prefix, ru, ctr)
        dl = ext_sub(l1, l0, ctr)
        l2 = ext_add(l1, dl, ctr)

        p0 = ext_mul(l0, qu0, ctr)
        if np.array_equal(l1 % P, ext_zero()):
            # Fallback when l1 == 0: compute qu1 directly, p1 = 0
            Q1 = ext_sum_axis(ext_mul(A1, B1, ctr), axis=1)
            qu1 = ext_sum_axis(ext_mul(suf_tables[ell - 1 - r], Q1, ctr), axis=0) if r < ell - 1 else Q1[0]
            p1 = ext_zero()
        else:
            p1 = ext_sub(sigma, p0, ctr)
            qu1 = ext_mul(ext_inv(l1, ctr), p1, ctr)

        # q_u(2) = 2*qu1 - qu0 + 2*qu_inf (0 muls!)
        qu2 = ext_add(ext_sub(ext_add(qu1, qu1, ctr), qu0, ctr), ext_add(qu_inf, qu_inf, ctr), ctr)
        p2 = ext_mul(l2, qu2, ctr)
        c3 = ext_mul(dl, qu_inf, ctr)
        cubic_msgs.append((p0, p1, p2, c3))

        # Update running claim & eq_prefix in O(1) ops:
        qu_ch = eval_quad_from_0_1_inf(qu0, qu1, qu_inf, ch)
        l_ch = ext_add(l0, ext_mul(dl, ch, ctr), ctr)
        sigma = ext_mul(l_ch, qu_ch, ctr)
        eq_prefix = l_ch

        A = ext_add(A0, ext_mul(dA, ch, ctr), ctr)
        B = ext_add(B0, ext_mul(dB, ch, ctr), ctr)

    A_y = A[0]
    B_y = B[0]
    for r in range(mu_s):
        ch = challenges[ell + r]
        A0, A1 = A_y[0::2], A_y[1::2]
        B0, B1 = B_y[0::2], B_y[1::2]
        dA = ext_sub(A1, A0, ctr)
        dB = ext_sub(B1, B0, ctr)

        qv0 = ext_sum_axis(ext_mul(A0, B0, ctr), axis=0)
        qv_inf = ext_sum_axis(ext_mul(dA, dB, ctr), axis=0)
        p0 = ext_mul(eq_prefix, qv0, ctr)
        p1 = ext_sub(sigma, p0, ctr)
        c2_scaled = ext_mul(eq_prefix, qv_inf, ctr)
        # For quadratic s(X) with s(0)=p0, s(1)=p1, s''/2 = c2_scaled: s(2) = 2*p1 - p0 + 2*c2_scaled
        p2 = ext_add(ext_sub(ext_add(p1, p1, ctr), p0, ctr), ext_add(c2_scaled, c2_scaled, ctr), ctr)
        cubic_msgs.append((p0, p1, p2, ext_zero()))

        sigma = eval_quad_from_0_1_inf(p0, p1, c2_scaled, ch)
        A_y = ext_add(A0, ext_mul(dA, ch, ctr), ctr)
        B_y = ext_add(B0, ext_mul(dB, ch, ctr), ctr)

    return cubic_msgs, A_y[0], B_y[0]


def verify_standard_cubic_einsumcheck(
    claimed_H: np.ndarray,
    r_f2: np.ndarray,
    cubic_msgs: List[Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]],
    challenges: np.ndarray,
    final_T1_eval: np.ndarray,
    final_T2_eval: np.ndarray,
) -> bool:
    """Unmodified standard cubic `EinSumcheck` verifier (`ZkmlEinSumcheck.lean`)."""
    running = claimed_H.copy()
    for r, (p0, p1, p2, c3) in enumerate(cubic_msgs):
        if not np.array_equal(ext_add(p0, p1) % P, running % P):
            return False
        running = eval_cubic_from_0_1_2_inf(p0, p1, p2, c3, challenges[r])
    ell = r_f2.shape[0]
    eq_eval = eval_eq_point(r_f2, challenges[:ell])
    expected = ext_mul(eq_eval, ext_mul(final_T1_eval, final_T2_eval))
    return np.array_equal(running % P, expected % P)


def closed_form_gruen_mode2_counts(f1_vars_1: int, f1_vars_2: int, ell_f2: int, mu_s: int) -> Dict[str, int]:
    """Exact closed-form counts matching `partial_eval_f1_base` + `prove_gruen_2op_mode2_direct` TO THE UNIT."""
    rem = 1 << (ell_f2 + mu_s)
    pe_eq = (max(0, (1 << f1_vars_1) - 2) if f1_vars_1 >= 1 else 0) + \
            (max(0, (1 << f1_vars_2) - 2) if f1_vars_2 >= 1 else 0)
    pe_ext_base = ((1 << f1_vars_1) + (1 << f1_vars_2)) * rem

    eq_suf = max(0, (1 << (ell_f2 - 1)) - 2) if ell_f2 >= 2 else 0
    ph1 = ((1 << ell_f2) - 1) * 4 * (1 << mu_s) + 2 * max(0, (1 << ell_f2) - 2)
    ph2 = 4 * ((1 << mu_s) - 1)
    sc_ext_ext = eq_suf + ph1 + ph2
    tot_ext_ext = pe_eq + sc_ext_ext
    return {
        "rounds": ell_f2 + mu_s,
        "transcript_ext4": 2 * (ell_f2 + mu_s) + 2,
        "pe_ext_base": pe_ext_base,
        "pe_ext_ext": pe_eq,
        "sc_ext_ext": sc_ext_ext,
        "total_ext_ext": tot_ext_ext,
        "bb_muls_kar": BB_MULS_PER_EXT_BASE * pe_ext_base + BB_MULS_PER_EXT_EXT_KAR * tot_ext_ext,
    }


def closed_form_prev_canonical_counts(f1_vars_1: int, f1_vars_2: int, ell_f2: int, mu_s: int) -> Dict[str, int]:
    """Closed-form counts of yesterday's canonical `{0,1,inf}` prover (`einsum_gqa_counts.py`)."""
    rem = 1 << (ell_f2 + mu_s)
    pe_eq = (max(0, (1 << f1_vars_1) - 2) if f1_vars_1 >= 1 else 0) + \
            (max(0, (1 << f1_vars_2) - 2) if f1_vars_2 >= 1 else 0)
    pe_ext_base = ((1 << f1_vars_1) + (1 << f1_vars_2)) * rem
    eq_f2 = max(0, (1 << ell_f2) - 2) if ell_f2 >= 1 else 0
    ph1 = ((1 << ell_f2) - 1) * (5 * (1 << mu_s) + 5)
    ph2 = 5 * ((1 << mu_s) - 1) + 3 * mu_s
    sc_ext_ext = eq_f2 + ph1 + ph2
    tot_ext_ext = pe_eq + sc_ext_ext
    return {
        "rounds": ell_f2 + mu_s,
        "transcript_ext4": 3 * ell_f2 + 2 * mu_s + 2,  # omitting p(1)
        "pe_ext_base": pe_ext_base,
        "sc_ext_ext": sc_ext_ext,
        "bb_muls_kar": BB_MULS_PER_EXT_BASE * pe_ext_base + BB_MULS_PER_EXT_EXT_KAR * tot_ext_ext,
    }


# ---------------------------------------------------------------------------
# 3. SUBPROBLEM 2: MXFP4 (`ikb,jkb,jk -> ij`) All 6 Schedules + SVO + Horner
# ---------------------------------------------------------------------------
def run_mxfp4_schedule_sim(
    order: Tuple[str, str, str],
    X_ri: np.ndarray,          # Ext4 (K, B, 4)
    Q_int: np.ndarray,         # int64 (J, K, B) in E2M1_X2_VALS
    S_int: np.ndarray,         # int64 (J, K)
    r_j: np.ndarray,           # Ext4 (log_j, 4)
    chals: Dict[str, np.ndarray],
) -> Tuple[List[Tuple[str, int, Tuple[np.ndarray, ...]]], Tuple[np.ndarray, np.ndarray, np.ndarray], OpCounter]:
    """
    Executes ANY of the 6 variable-block elimination orders `order` in Perm('j', 'k', 'b')
    under standard Algorithm 1 + Gruen Mode 2 on `j` (`m_j = 2` -> deg 2!) + `{0, inf}` on `b`
    (deg 2!) + `{0, 2, inf}` on `k` (deg 3!).
    Tracks exact `ext_base_muls`, `ext_ext_muls`, `ext_adds`, and `peak_ext4_bytes`!
    """
    ctr = OpCounter()
    J, K, B = Q_int.shape
    dims = {"j": J, "k": K, "b": B}
    logs = {ax: int(round(math.log2(dims[ax]))) for ax in ("j", "k", "b")}

    # State representation: each tensor tracks `(arr, axes_list, is_ext4)`
    X_st = [X_ri.copy(), ["k", "b"], True]
    Q_st = [Q_int.copy(), ["j", "k", "b"], False]
    S_st = [S_int.copy(), ["j", "k"], False]

    j_pos_in_order = order.index("j")
    suf_j = build_eq_suffix_tables(r_j, ctr)
    # If `j` is NOT eliminated first, we need full `eq_j_tab` during earlier blocks (`k` or `b`)!
    eq_j_full = build_eq_table(r_j, ctr) if j_pos_in_order > 0 else None

    def update_peak():
        elems = 0
        for arr, _, is_ext in (X_st, Q_st, S_st):
            if is_ext:
                elems += math.prod(arr.shape[:-1])
        if eq_j_full is not None and j_pos_in_order > 0:
            elems += eq_j_full.shape[0]
        ctr.note_buf(elems)

    update_peak()
    msgs: List[Tuple[str, int, Tuple[np.ndarray, ...]]] = []

    def move_axis_front(st, ax: str):
        arr, axes, is_ext = st
        idx = axes.index(ax)
        if idx != 0:
            perm = [idx] + [i for i in range(len(axes)) if i != idx]
            if is_ext:
                perm = perm + [len(axes)]
            arr = arr.transpose(perm)
            axes = [ax] + [a for a in axes if a != ax]
        return [arr, axes, is_ext]

    def fold_state(st, ch: np.ndarray):
        arr, axes, is_ext = st
        a0, a1 = arr[0::2], arr[1::2]
        if is_ext:
            da = ext_sub(a1, a0, ctr)
            folded = ext_add(a0, ext_mul(da, ch, ctr), ctr)
        else:
            da_base = (a1 - a0) % P
            folded = ext_mul_base(ch, da_base, ctr)
            folded[..., 0] = (folded[..., 0] + (a0 % P)) % P
        new_axes = axes if folded.shape[0] > 1 else axes[1:]
        if folded.shape[0] == 1:
            folded = folded[0]
        return [folded, new_axes, True]

    # Helper to evaluate full inner sum at a slice `(X_sl, Q_sl, S_sl)` over active remaining axes
    def eval_contraction_slice(
        X_sl: Tuple[np.ndarray, List[str], bool],
        Q_sl: Tuple[np.ndarray, List[str], bool],
        S_sl: Tuple[np.ndarray, List[str], bool],
        j_weight: np.ndarray = None,   # shape (J_rem, 4) in Ext4 if j still active
    ) -> np.ndarray:
        """Parenthesizes optimally across remaining active axes among {'j', 'k', 'b'}."""
        x_arr, x_ax, x_ext = X_sl
        q_arr, q_ax, q_ext = Q_sl
        s_arr, s_ax, s_ext = S_sl

        # Align axes to canonical subset of ['j', 'k', 'b']
        def align(arr, ax_list, is_ext, target):
            perm = [ax_list.index(a) for a in target]
            if is_ext:
                perm.append(len(ax_list))
            return arr.transpose(perm)

        rem_q = [a for a in ("j", "k", "b") if a in q_ax]
        q_a = align(q_arr, q_ax, q_ext, rem_q)
        rem_x = [a for a in ("k", "b") if a in x_ax]
        x_a = align(x_arr, x_ax, x_ext, rem_x)
        rem_s = [a for a in ("j", "k") if a in s_ax]
        s_a = align(s_arr, s_ax, s_ext, rem_s)

        def mul_any(u, u_ext: bool, v, v_ext: bool):
            if u_ext and v_ext:
                return ext_mul(u, v, ctr), True
            elif u_ext and not v_ext:
                return ext_mul_base(u, v, ctr), True
            elif not u_ext and v_ext:
                return ext_mul_base(v, u, ctr), True
            else:
                ctr.base_muls += math.prod(np.broadcast_shapes(u.shape, v.shape))
                return (u * v) % P, False

        # Step 1: If `b` is in `rem_q`, contract `X * Q` over `b` first!
        if "b" in rem_q:
            # Broadcast X onto Q's axes (`[j?], [k?], b`)
            x_bcast = x_a
            if "j" in rem_q:
                x_bcast = x_bcast[None, ...]
            prod_xq, xq_ext = mul_any(x_bcast, x_ext, q_a, q_ext)
            b_axis = rem_q.index("b")
            xq_sum = ext_sum_axis(prod_xq, axis=b_axis)  # axes: subset of ['j', 'k']
            cur_arr, cur_ax, cur_ext = xq_sum, [a for a in rem_q if a != "b"], xq_ext
        else:
            cur_arr, cur_ax, cur_ext = q_a, rem_q[:], q_ext
            # Multiply by X (which now only has `k` or is scalar Ext4)
            x_bcast = x_a
            if "j" in cur_ax and "k" in rem_x:
                x_bcast = x_bcast[None, ...]
            elif "j" in cur_ax and len(rem_x) == 0:
                pass
            cur_arr, cur_ext = mul_any(cur_arr, cur_ext, x_bcast, x_ext)

        # Step 2: Multiply by S (axes subset of ['j', 'k'])
        s_bcast = s_a
        if cur_ax == ["j"] and rem_s == []:
            pass
        elif cur_ax == ["k"] and rem_s == []:
            pass
        cur_arr, cur_ext = mul_any(cur_arr, cur_ext, s_bcast, s_ext)

        # Step 3: Sum over `k` if present
        if "k" in cur_ax:
            k_axis = cur_ax.index("k")
            cur_arr = ext_sum_axis(cur_arr, axis=k_axis) if cur_ext else (cur_arr.sum(axis=k_axis) % P)
            cur_ax = [a for a in cur_ax if a != "k"]

        # Step 4: Weight by `j_weight` and sum over `j` if present
        if "j" in cur_ax:
            if j_weight is not None:
                cur_arr, cur_ext = mul_any(j_weight, True, cur_arr, cur_ext)
            cur_arr = ext_sum_axis(cur_arr, axis=0) if cur_ext else (cur_arr.sum(axis=0) % P)
            cur_ax = []
        else:
            if j_weight is not None:
                # j_weight is length 1 scalar
                cur_arr, cur_ext = mul_any(j_weight[0], True, cur_arr, cur_ext)

        assert cur_ext
        return cur_arr

    def slice_point(st, ax: str, pt: str):
        """Slice tensor `st` along `ax` (already moved to axis 0) at pt in {'0', '2', 'inf'}."""
        arr, axes, is_ext = st
        a0, a1 = arr[0::2], arr[1::2]
        rem_axes = axes if a0.shape[0] > 1 else axes[1:]
        if pt == "0":
            out = a0[0] if a0.shape[0] == 1 else a0
            return (out, rem_axes, is_ext)
        d = ext_sub(a1, a0, ctr) if is_ext else ((a1 - a0) % P)
        if pt == "inf":
            out = d[0] if d.shape[0] == 1 else d
            return (out, rem_axes, is_ext)
        if pt == "2":
            a2 = ext_add(a1, d, ctr) if is_ext else ((a1 + d) % P)
            out = a2[0] if a2.shape[0] == 1 else a2
            return (out, rem_axes, is_ext)
        raise ValueError(pt)

    for blk_idx, ax in enumerate(order):
        n_rounds = logs[ax]
        for r in range(n_rounds):
            ch = chals[ax][r]
            if ax == "b":
                # Degree 2 (`X`, `Q` depend on `b`; `S` untouched!)
                X_st = move_axis_front(X_st, "b")
                Q_st = move_axis_front(Q_st, "b")
                jw = eq_j_full if ("j" in Q_st[1]) else None
                q0 = eval_contraction_slice(slice_point(X_st, "b", "0"), slice_point(Q_st, "b", "0"), tuple(S_st), jw)
                q_inf = eval_contraction_slice(slice_point(X_st, "b", "inf"), slice_point(Q_st, "b", "inf"), tuple(S_st), jw)
                msgs.append(("b", 2, (q0, q_inf)))
                X_st = fold_state(X_st, ch)
                Q_st = fold_state(Q_st, ch)
                update_peak()

            elif ax == "k":
                # Degree 3 (`X`, `Q`, `S` all depend on `k`) -> evaluate at {0, 2, inf}
                X_st = move_axis_front(X_st, "k")
                Q_st = move_axis_front(Q_st, "k")
                S_st = move_axis_front(S_st, "k")
                jw = eq_j_full if ("j" in Q_st[1]) else None
                p0 = eval_contraction_slice(slice_point(X_st, "k", "0"), slice_point(Q_st, "k", "0"), slice_point(S_st, "k", "0"), jw)
                p2 = eval_contraction_slice(slice_point(X_st, "k", "2"), slice_point(Q_st, "k", "2"), slice_point(S_st, "k", "2"), jw)
                c3 = eval_contraction_slice(slice_point(X_st, "k", "inf"), slice_point(Q_st, "k", "inf"), slice_point(S_st, "k", "inf"), jw)
                msgs.append(("k", 3, (p0, p2, c3)))
                X_st = fold_state(X_st, ch)
                Q_st = fold_state(Q_st, ch)
                S_st = fold_state(S_st, ch)
                update_peak()

            elif ax == "j":
                # Gruen Mode 2 on `j in F_{>=2}` (`Q`, `S` depend on `j`, `m_j = 2` -> DEGREE 2 `{0, inf}`!)
                Q_st = move_axis_front(Q_st, "j")
                S_st = move_axis_front(S_st, "j")
                jw = suf_j[n_rounds - 1 - r] if r < n_rounds - 1 else None
                qu0 = eval_contraction_slice(tuple(X_st), slice_point(Q_st, "j", "0"), slice_point(S_st, "j", "0"), jw)
                qu_inf = eval_contraction_slice(tuple(X_st), slice_point(Q_st, "j", "inf"), slice_point(S_st, "j", "inf"), jw)
                msgs.append(("j", 2, (qu0, qu_inf)))
                Q_st = fold_state(Q_st, ch)
                S_st = fold_state(S_st, ch)
                update_peak()
        if ax == "j":
            eq_j_full = None  # `j` eliminated and `eq(r_j, ch_j)` stripped by Gruen Mode 2!

    return msgs, (X_st[0], Q_st[0], S_st[0]), ctr


def verify_mxfp4_schedule_msgs(
    claimed_D: np.ndarray,
    order: Tuple[str, str, str],
    r_j: np.ndarray,
    msgs: List[Tuple[str, int, Tuple[np.ndarray, ...]]],
    chals: Dict[str, np.ndarray],
    finals: Tuple[np.ndarray, np.ndarray, np.ndarray],
) -> bool:
    """Unified verifier for any MXFP4 `(b, k, j)` schedule using Gruen Mode 2 on `j`."""
    one = ext_one()
    sigma = claimed_D.copy()
    cursors = {"j": 0, "k": 0, "b": 0}
    j_seen = False

    for ax, deg, m in msgs:
        idx = cursors[ax]
        cursors[ax] += 1
        ch = chals[ax][idx]
        if ax == "j":
            j_seen = True
            ru = r_j[idx]
            qu0, qu_inf = m
            lhs0 = ext_mul(ext_sub(one, ru), qu0)
            qu1 = ext_mul(ext_inv(ru), ext_sub(sigma, lhs0))
            sigma = eval_quad_from_0_1_inf(qu0, qu1, qu_inf, ch)
        elif deg == 2:
            q0, q_inf = m
            q1 = ext_sub(sigma, q0)
            sigma = eval_quad_from_0_1_inf(q0, q1, q_inf, ch)
        elif deg == 3:
            p0, p2, c3 = m
            p1 = ext_sub(sigma, p0)
            sigma = eval_cubic_from_0_1_2_inf(p0, p1, p2, c3, ch)
        else:
            return False

    assert j_seen
    x_fin, q_fin, s_fin = finals
    expected = ext_mul(x_fin, ext_mul(q_fin, s_fin))
    return np.array_equal(sigma % P, expected % P)


def e2m1_horner_dot_ext4(q_block_32: np.ndarray, vec_ext4_32: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """
    Zero-multiplication inner product `sum_{b=0}^{31} q_block_32[b] * vec_ext4_32[b]`
    for E2M1 doubled integers `q in {0, +-1, +-2, +-3, +-4, +-6, +-8, +-12}`!
    Exploits that every E2M1 integer has binary Hamming weight <= 2:
      12 = 8+4, 8 = 8, 6 = 4+2, 4 = 4, 3 = 2+1, 2 = 2, 1 = 1.
    Accumulates 7 magnitude buckets by pure `Ext4` add/sub, then combines via 4 bit-planes
    and 3 Horner doublings -> **0 multiplications**!
    """
    buckets = {m: np.zeros(4, dtype=np.int64) for m in (1, 2, 3, 4, 6, 8, 12)}
    for b in range(32):
        qv = int(q_block_32[b])
        if qv > 0:
            buckets[qv] = ext_add(buckets[qv], vec_ext4_32[b], ctr)
        elif qv < 0:
            buckets[-qv] = ext_sub(buckets[-qv], vec_ext4_32[b], ctr)

    c8 = ext_add(buckets[8], buckets[12], ctr)
    c4 = ext_add(ext_add(buckets[4], buckets[6], ctr), buckets[12], ctr)
    c2 = ext_add(ext_add(buckets[2], buckets[3], ctr), buckets[6], ctr)
    c1 = ext_add(buckets[1], buckets[3], ctr)

    # (((2 * c8 + c4) * 2 + c2) * 2 + c1)
    acc = ext_add(ext_add(c8, c8, ctr), c4, ctr)
    acc = ext_add(ext_add(acc, acc, ctr), c2, ctr)
    acc = ext_add(ext_add(acc, acc, ctr), c1, ctr)
    return acc


def prove_mxfp4_tensor_factored_horner_bjk(
    X_ri: np.ndarray,          # Ext4 (K, 32, 4)
    Q_int: np.ndarray,         # int64 (J, K, 32)
    S_int: np.ndarray,         # int64 (J, K)
    r_j: np.ndarray,           # Ext4 (log_j, 4)
    chals: Dict[str, np.ndarray],
) -> Tuple[List[Tuple[str, int, Tuple[np.ndarray, ...]]], Tuple[np.ndarray, np.ndarray, np.ndarray], OpCounter]:
    """
    Tensor-Factored Delayed Block-Bind (`l_0 = 5`) + E2M1 Bit-Plane Horner (`b -> j -> k`):
      1. `E_jk[j, k] = eq_j[j] * S[j, k]` (`J * K` `base * Ext4` muls; `S` is 32x smaller than `Q`!).
      2. Collapse `M[k, b] = sum_j E_jk[j, k] * Q[j, k, b]` via 7-bucket E2M1 Horner (`0` muls!).
      3. Run all 5 `b`-rounds on tiny `(K, 32)` arrays `X_ri` and `M` (`4 * (32*K - K)` Ext4 muls!).
      4. Build `eq_b[0..31] = eq(chals['b'], .)` (`30` Ext4 muls) and bind `Q^{(5)}[j, k]` directly
         from `int4` `Q` into a `(J, K)` Ext4 buffer via E2M1 Horner (`0` muls on `Q`, **16x smaller**
         peak Ext4 buffer than Algorithm 1!).
      5. Run Gruen `j`-rounds on `(J, K)` (where round `j_0` still has `S` in base field!) + 7 `k`-rounds on `(K,)`.
      Produces **bit-identical** sumcheck messages to `run_mxfp4_schedule_sim(('b', 'j', 'k'), ...)`!
    """
    ctr = OpCounter()
    J, K, B = Q_int.shape
    assert B == 32
    log_j = int(round(math.log2(J)))
    log_k = int(round(math.log2(K)))

    eq_j_tab = build_eq_table(r_j, ctr)
    E_jk = ext_mul_base(eq_j_tab[:, None, :], S_int, ctr)   # (J, K, 4): J*K base*Ext4 muls
    ctr.note_buf(J * K + K * B)

    # Step 2: M[k, b] via 7-bucket E2M1 Horner across j (0 multiplications!)
    M = np.zeros((K, B, 4), dtype=np.int64)
    for k in range(K):
        for b in range(B):
            buckets = {m: np.zeros(4, dtype=np.int64) for m in (1, 2, 3, 4, 6, 8, 12)}
            for j in range(J):
                qv = int(Q_int[j, k, b])
                if qv > 0:
                    buckets[qv] = ext_add(buckets[qv], E_jk[j, k], ctr)
                elif qv < 0:
                    buckets[-qv] = ext_sub(buckets[-qv], E_jk[j, k], ctr)
            c8 = ext_add(buckets[8], buckets[12], ctr)
            c4 = ext_add(ext_add(buckets[4], buckets[6], ctr), buckets[12], ctr)
            c2 = ext_add(ext_add(buckets[2], buckets[3], ctr), buckets[6], ctr)
            c1 = ext_add(buckets[1], buckets[3], ctr)
            acc = ext_add(ext_add(c8, c8, ctr), c4, ctr)
            acc = ext_add(ext_add(acc, acc, ctr), c2, ctr)
            M[k, b] = ext_add(ext_add(acc, acc, ctr), c1, ctr)

    del E_jk  # Free `(J, K)` buffer before allocating `Q5` -> peak stays `J * K`!

    # Step 3: 5 `b`-rounds on tiny `(K, 32)` arrays `X_cur` and `M_cur`
    msgs: List[Tuple[str, int, Tuple[np.ndarray, ...]]] = []
    X_cur = X_ri.transpose(1, 0, 2)  # (32, K, 4)
    M_cur = M.transpose(1, 0, 2)     # (32, K, 4)
    for r in range(5):
        ch = chals["b"][r]
        x0, x1 = X_cur[0::2], X_cur[1::2]
        m0, m1 = M_cur[0::2], M_cur[1::2]
        dx = ext_sub(x1, x0, ctr)
        dm = ext_sub(m1, m0, ctr)
        q0 = ext_sum_axis(ext_sum_axis(ext_mul(x0, m0, ctr), axis=1), axis=0)
        q_inf = ext_sum_axis(ext_sum_axis(ext_mul(dx, dm, ctr), axis=1), axis=0)
        msgs.append(("b", 2, (q0, q_inf)))
        X_cur = ext_add(x0, ext_mul(dx, ch, ctr), ctr)
        M_cur = ext_add(m0, ext_mul(dm, ch, ctr), ctr)
    X5 = X_cur[0]  # (K, 4)

    # Step 4: Bind Q^{(5)}[j, k] = sum_{b=0..31} eq_b[b] * Q[j, k, b] via E2M1 Horner (0 muls!)
    eq_b = build_eq_table(chals["b"], ctr)  # (32, 4): 30 Ext4 muls
    Q5 = np.zeros((J, K, 4), dtype=np.int64)
    ctr.note_buf(J * K + K + 32)
    for j in range(J):
        for k in range(K):
            Q5[j, k] = e2m1_horner_dot_ext4(Q_int[j, k], eq_b, ctr)

    # Step 5: Gruen `j`-rounds on `(J, K)` (`S_int` starts in base field!)
    suf_j = build_eq_suffix_tables(r_j, ctr)
    Q_j = Q5
    S_j = S_int.copy()
    s_is_ext = False
    for r in range(log_j):
        ch = chals["j"][r]
        q0, q1 = Q_j[0::2], Q_j[1::2]
        s0, s1 = S_j[0::2], S_j[1::2]
        dq = ext_sub(q1, q0, ctr)
        if not s_is_ext:
            ds_base = (s1 - s0) % P
            # Multiply Q*S (`base*Ext4`), then contract over `k` against `X5[k]`!
            qs0 = ext_mul_base(q0, s0, ctr)
            qsinf = ext_mul_base(dq, ds_base, ctr)
            S_j = ext_mul_base(ch, ds_base, ctr)
            S_j[..., 0] = (S_j[..., 0] + (s0 % P)) % P
            s_is_ext = True
            ctr.note_buf(Q_j.shape[0] // 2 * K + S_j.shape[0] * K)
        else:
            ds = ext_sub(s1, s0, ctr)
            qs0 = ext_mul(q0, s0, ctr)
            qsinf = ext_mul(dq, ds, ctr)
            S_j = ext_add(s0, ext_mul(ds, ch, ctr), ctr)

        # Contract over `k` with `X5[k]` (`2 * (J_rem) * K` Ext4 muls)
        c0_j = ext_sum_axis(ext_mul(qs0, X5[None, :, :], ctr), axis=1)
        cinf_j = ext_sum_axis(ext_mul(qsinf, X5[None, :, :], ctr), axis=1)
        if r < log_j - 1:
            jw = suf_j[log_j - 1 - r]
            qu0 = ext_sum_axis(ext_mul(jw, c0_j, ctr), axis=0)
            qu_inf = ext_sum_axis(ext_mul(jw, cinf_j, ctr), axis=0)
        else:
            qu0, qu_inf = c0_j[0], cinf_j[0]
        msgs.append(("j", 2, (qu0, qu_inf)))
        Q_j = ext_add(q0, ext_mul(dq, ch, ctr), ctr)

    # Step 6: 7 `k`-rounds on tiny vectors `X5`, `Q_j[0]`, `S_j[0]` of length `K`!
    Xk = X5
    Qk = Q_j[0]
    Sk = S_j[0]
    for r in range(log_k):
        ch = chals["k"][r]
        x0, x1 = Xk[0::2], Xk[1::2]
        q0, q1 = Qk[0::2], Qk[1::2]
        s0, s1 = Sk[0::2], Sk[1::2]
        dx = ext_sub(x1, x0, ctr)
        dq = ext_sub(q1, q0, ctr)
        ds = ext_sub(s1, s0, ctr)
        x2 = ext_add(x1, dx, ctr)
        q2 = ext_add(q1, dq, ctr)
        s2 = ext_add(s1, ds, ctr)

        p0 = ext_sum_axis(ext_mul(x0, ext_mul(q0, s0, ctr), ctr), axis=0)
        p2 = ext_sum_axis(ext_mul(x2, ext_mul(q2, s2, ctr), ctr), axis=0)
        c3 = ext_sum_axis(ext_mul(dx, ext_mul(dq, ds, ctr), ctr), axis=0)
        msgs.append(("k", 3, (p0, p2, c3)))

        Xk = ext_add(x0, ext_mul(dx, ch, ctr), ctr)
        Qk = ext_add(q0, ext_mul(dq, ch, ctr), ctr)
        Sk = ext_add(s0, ext_mul(ds, ch, ctr), ctr)

    return msgs, (Xk[0], Qk[0], Sk[0]), ctr


def price_mxfp4_real_shapes_exact(N_real: int, K_real: int) -> Dict[str, Dict[str, Any]]:
    """
    Exact closed-form operation & memory formulas for ALL 6 variable-block schedules +
    Generic Toom-Cook `SVO` (`l_0 in {1,2,3}`) + Tensor-Factored Block-Bind (`l_0 = 5`,
    both plain `base*Ext4` and E2M1 0-mul Horner) on real `gpt-oss-20b` shapes!
    Validated against `run_mxfp4_schedule_sim` and `prove_mxfp4_tensor_factored_horner_bjk`
    to ZERO discrepancy on synthetic power-of-2 shapes!
    """
    B = 32
    K_blk = K_real // 32
    J = 1 << int(math.ceil(math.log2(N_real)))
    K = 1 << int(math.ceil(math.log2(K_blk)))
    lj = int(round(math.log2(J)))
    lk = int(round(math.log2(K)))

    eq_j_build = max(0, J - 2)
    suf_j_build = max(0, (J // 2) - 2)

    out: Dict[str, Dict[str, Any]] = {}

    # 1. `j -> k -> b` (Algorithm 1 + Gruen on j):
    # j_0: Q is base (2*(J/2)*K*B eval + (J/2)*K*B fold = 1.5*J*K*B ext*base), S is base (1.5*J*K ext*base),
    #      X*Q sum * S + suf: (J/2)*K ext*base? Wait: match `run_mxfp4_schedule_sim` exact counts!
    # Let's compute exact formulas matching `run_mxfp4_schedule_sim` and check 0-diff in unit test!
    # Round j_0 (half_j = J/2):
    #   eval(0) & eval(inf): X*Q -> 2*(J/2)*K*B ext_base; * S -> 2*(J/2)*K ext_base; * suf -> 2*(J/2) ext_ext
    #   fold Q -> (J/2)*K*B ext_base; fold S -> (J/2)*K ext_base; Peak Ext4 buf = (J/2)*K*B + (J/2)*K + K*B
    # Rounds j_1..j_{lj-1} (sum half_j = J/2 - 1, sum_{r<lj-1} half_j = J/2 - 2):
    #   eval(0) & eval(inf): X*Q -> 2*(J/2-1)*K*B ext_ext; * S -> 2*(J/2-1)*K ext_ext; * suf -> 2*(J/2-2) ext_ext
    #   fold Q -> (J/2-1)*K*B ext_ext; fold S -> (J/2-1)*K ext_ext
    # k-rounds (sum half_k = K - 1):
    #   eval(0,2,inf): 3*(K-1)*B (X*Q) + 3*(K-1) (*S) ext_ext; fold X,Q,S: (2*(K-1)*B + (K-1)) ext_ext
    # b-rounds (sum half_b = B - 1):
    #   eval(0,inf): 2*(B-1) (X*Q) + 2*(B-1)? Wait: S is scalar -> + 2*lk_done = 2*5 = 10 ext_ext; fold X,Q: 2*(B-1)
    jkb_eb = 3 * (J // 2) * K * B + 3 * (J // 2) * K
    jkb_ee = (
        suf_j_build
        + 2 * (J // 2)
        + 3 * (J // 2 - 1) * K * B + 3 * (J // 2 - 1) * K + 2 * max(0, J // 2 - 2)
        + (5 * B + 4) * (K - 1)
        + 4 * (B - 1) + 2 * 5
    )
    out["1. j -> k -> b (Alg1+Gruen)"] = {
        "ext_base": jkb_eb,
        "ext_ext": jkb_ee,
        "peak_mb": ((J // 2) * K * B + (J // 2) * K + K * B) * BYTES_PER_EXT4 / 1e6,
    }

    # 2. `j -> b -> k`:
    # Same j-rounds! Then b-rounds on (K, B): eval(0,inf) does 2*K*half_b (X*Q) + 2*K (*S[k]); fold X,Q: 2*K*half_b
    # Then k-rounds on (K,): eval(0,2,inf) does 3*half_k (Q*X) + 3*half_k (*S); fold X,Q,S: 3*half_k -> 9*(K-1)!
    jbk_eb = jkb_eb
    jbk_ee = (
        suf_j_build
        + 2 * (J // 2)
        + 3 * (J // 2 - 1) * K * B + 3 * (J // 2 - 1) * K + 2 * max(0, J // 2 - 2)
        + 4 * K * (B - 1) + 2 * 5 * K
        + 9 * (K - 1)
    )
    out["2. j -> b -> k (Alg1+Gruen)"] = {
        "ext_base": jbk_eb,
        "ext_ext": jbk_ee,
        "peak_mb": ((J // 2) * K * B + (J // 2) * K + K * B) * BYTES_PER_EXT4 / 1e6,
    }

    # 3. `k -> j -> b`:
    # k_0 (half_k = K/2): X*Q -> 3*J*(K/2)*B ext_base; *S -> 3*J*(K/2) ext_base; *eq_j -> 3*J ext_ext;
    #   fold Q -> J*(K/2)*B ext_base, fold S -> J*(K/2) ext_base, fold X -> (K/2)*B ext_ext.
    # k_1..k_{lk-1} (sum = K/2 - 1): 3*J*(K/2-1)*B + 3*J*(K/2-1) + 3*J*(lk-1) (eval)
    #   + J*(K/2-1)*B + J*(K/2-1) + (K/2-1)*B (fold)
    # j-rounds on (J, B): eval(0,inf) does 2*half_j*B (X*Q) + 2*half_j (*S) + 2*half_j (*suf for r<lj-1); fold Q,S: half_j*B + half_j
    # b-rounds on (B,): 4*(B-1) + 10
    kjb_eb = 4 * J * (K // 2) * B + 4 * J * (K // 2)
    kjb_ee = (
        suf_j_build + eq_j_build
        + 3 * J + (K // 2) * B
        + 4 * J * (K // 2 - 1) * B + 4 * J * (K // 2 - 1) + 3 * J * (lk - 1) + (K // 2 - 1) * B
        + 3 * (J - 1) * B + 3 * (J - 1) + 2 * max(0, J - 2)
        + 4 * (B - 1) + 10
    )
    out["3. k -> j -> b (Alg1+Gruen)"] = {
        "ext_base": kjb_eb,
        "ext_ext": kjb_ee,
        "peak_mb": (J * (K // 2) * B + J * (K // 2) + (K // 2) * B + J) * BYTES_PER_EXT4 / 1e6,
    }

    # 4. `k -> b -> j`:
    kbj_eb = kjb_eb
    kbj_ee = (
        suf_j_build + eq_j_build
        + 3 * J + (K // 2) * B
        + 4 * J * (K // 2 - 1) * B + 4 * J * (K // 2 - 1) + 3 * J * (lk - 1) + (K // 2 - 1) * B
        + 3 * J * (B - 1) + (B - 1) + 2 * 5 * J   # wait: S is base? No, S became Ext4 in k_0! So *S is 2*5*J + *eq_j is 2*5*J -> 4*5*J!
        + 9 * (J - 1) - 3 * (J - 1) + 2 * max(0, J - 2)  # j-rounds on (J,) where X is scalar: Q*X (2*half_j) + *S (2*half_j) + *suf + fold Q,S (2*half_j) = 6*(J-1) + 2*max(0, J-2)!
    )
    # Fix exact b-round S+eq_j term in k->b->j: in each of 5 b-rounds, cur_arr (J,4) * S (J,4) -> J, then * eq_j (J,4) -> J => 2*J per eval * 2 evals = 4*J per round * 5 rounds = 20*J!
    kbj_ee = (
        suf_j_build + eq_j_build
        + 3 * J + (K // 2) * B
        + 4 * J * (K // 2 - 1) * B + 4 * J * (K // 2 - 1) + 3 * J * (lk - 1) + (K // 2 - 1) * B
        + 3 * J * (B - 1) + (B - 1) + 20 * J
        + 6 * (J - 1) + 2 * max(0, J - 2)
    )
    out["4. k -> b -> j (Alg1+Gruen)"] = {
        "ext_base": kbj_eb,
        "ext_ext": kbj_ee,
        "peak_mb": (J * (K // 2) * B + J * (K // 2) + (K // 2) * B + J) * BYTES_PER_EXT4 / 1e6,
    }

    # 5. `b -> j -> k` (Alg1 + Gruen):
    # b_0 (half_b = 16): X*Q -> 2*J*K*16 ext_base; *S (base!) -> 2*J*K ext_base; *eq_j -> 2*J ext_ext;
    #   fold Q -> J*K*16 ext_base, fold X -> K*16 ext_ext. (S UNTOUCHED!)
    # b_1..b_4 (sum half_b = 15): X*Q -> 2*J*K*15 ext_ext; *S (STILL BASE!) -> 2*4*J*K ext_base!!
    #   *eq_j -> 2*4*J ext_ext; fold Q -> J*K*15 ext_ext, fold X -> K*15 ext_ext.
    # j_0 (half_j = J/2): Q*X -> 2*(J/2)*K ext_ext; *S (STILL BASE!) -> 2*(J/2)*K ext_base; *suf -> 2*(J/2) ext_ext;
    #   fold Q -> (J/2)*K ext_ext, fold S -> (J/2)*K ext_base!
    # j_1..j_{lj-1} (sum = J/2 - 1): Q*X (2) + *S (2) + fold Q,S (2) = 6*(J/2-1)*K + 2*max(0, J/2-2) ext_ext
    # k-rounds on (K,): 9*(K - 1) ext_ext
    bjk_eb = 3 * J * K * 16 + 10 * J * K + 3 * (J // 2) * K
    bjk_ee = (
        suf_j_build + eq_j_build
        + 10 * J + K * (B - 1) + 3 * J * K * 15
        + 3 * (J // 2) * K + 2 * (J // 2)
        + 6 * (J // 2 - 1) * K + 2 * max(0, J // 2 - 2)
        + 9 * (K - 1)
    )
    out["5. b -> j -> k (Alg1+Gruen)"] = {
        "ext_base": bjk_eb,
        "ext_ext": bjk_ee,
        "peak_mb": (J * K * 16 + K * 16 + J) * BYTES_PER_EXT4 / 1e6,
    }

    # 6. `b -> k -> j` (Alg1 + Gruen):
    # Same 5 b-rounds! Then k_0 (half_k = K/2): Q*X -> 3*J*(K/2) ext_ext; *S (BASE!) -> 3*J*(K/2) ext_base;
    #   *eq_j -> 3*J ext_ext; fold Q -> J*(K/2) ext_ext, fold S -> J*(K/2) ext_base, fold X -> (K/2) ext_ext.
    # k_1..k_{lk-1} (sum = K/2 - 1): 3*J*(K/2-1) (Q*X) + 3*J*(K/2-1) (*S) + 3*J*(lk-1) (*eq_j) + 2*J*(K/2-1) (fold Q,S) + (K/2-1) (fold X)
    # j-rounds on (J,): 6*(J - 1) + 2*max(0, J - 2)
    bkj_eb = 3 * J * K * 16 + 10 * J * K + 4 * J * (K // 2)
    bkj_ee = (
        suf_j_build + eq_j_build
        + 10 * J + K * (B - 1) + 3 * J * K * 15
        + 4 * J * (K // 2) + 3 * J + (K // 2)
        + 8 * J * (K // 2 - 1) + 3 * J * (lk - 1) + (K // 2 - 1)
        + 6 * (J - 1) + 2 * max(0, J - 2)
    )
    out["6. b -> k -> j (Alg1+Gruen)"] = {
        "ext_base": bkj_eb,
        "ext_ext": bkj_ee,
        "peak_mb": (J * K * 16 + K * 16 + J) * BYTES_PER_EXT4 / 1e6,
    }

    # 7. Generic Toom-Cook `SVO` (`2025/1117` Thm 6.1) on `b -> j -> k` for `l_0 in {1, 2, 3}`:
    for l0 in (1, 2, 3):
        # First l0 rounds of `b` use Toom-Cook accumulators (`((3/2)^l0 + 1)*J*K*B` ext_base muls),
        # shrinking first materialized `Q` Ext4 buffer to `J * K * (32 / 2^(l0+1))` after round l0+1!
        rem_pairs = (B >> (l0 + 1)) - 1  # remaining Ext4 pairs in b after switching back at round l0+1
        svo_eb = round(((1.5 ** l0) + 1.5 / (1 << l0)) * J * K * B) + 2 * (5 - l0) * J * K + 3 * (J // 2) * K
        svo_ee = (
            suf_j_build + eq_j_build
            + 10 * J + K * (B - 1) + 3 * J * K * rem_pairs
            + 3 * (J // 2) * K + 2 * (J // 2)
            + 6 * (J // 2 - 1) * K + 2 * max(0, J // 2 - 2)
            + 9 * (K - 1)
        )
        buf_q = J * K * (B >> (l0 + 1))
        out[f"7{chr(96+l0)}. b->j->k + Generic SVO (l0={l0})"] = {
            "ext_base": svo_eb,
            "ext_ext": svo_ee,
            "peak_mb": (buf_q + K * B + J) * BYTES_PER_EXT4 / 1e6,
        }

    # 8a. Tensor-Factored Delayed Block-Bind (`l_0 = 5`, plain `base*Ext4` muls on Q):
    tf_ee = (
        eq_j_build + suf_j_build
        + 4 * K * (B - 1) + 30                  # 5 b-rounds on (K, 32) + eq_b build!
        + 2 * (J // 2) * K + 2 * (J // 2) + (J // 2) * K
        + 6 * (J // 2 - 1) * K + 2 * max(0, J // 2 - 2)
        + 9 * (K - 1)
    )
    tf_eb_plain = J * K + 2 * J * K * B + 3 * (J // 2) * K
    out["8a. b->j->k Tensor-Factored (l0=5, mul)"] = {
        "ext_base": tf_eb_plain,
        "ext_ext": tf_ee,
        "peak_mb": (J * K + K * B) * BYTES_PER_EXT4 / 1e6,
    }

    # 8b. Tensor-Factored (`l_0 = 5`) + E2M1 4-Bit-Plane Horner (`0` muls on `Q[j,k,b]`!)
    tf_eb_horner = J * K + 3 * (J // 2) * K
    out["8b. b->j->k Tensor-Factored + E2M1 Horner"] = {
        "ext_base": tf_eb_horner,
        "ext_ext": tf_ee,
        "peak_mb": (J * K + K * B) * BYTES_PER_EXT4 / 1e6,
    }

    # 8c. Active-support (`N_real x K_blk`, skipping zero-padded rows/blocks in C1..C4 + j_0!):
    tf_eb_horner_active = N_real * K_blk + 3 * (J // 2) * K_blk
    out["8c. b->j->k TF + Horner + ActiveSupport"] = {
        "ext_base": tf_eb_horner_active,
        "ext_ext": (
            eq_j_build + suf_j_build
            + 4 * K * (B - 1) + 30
            + 3 * (J // 2) * K_blk + 2 * (J // 2)
            + 6 * (J // 2 - 1) * K_blk + 2 * max(0, J // 2 - 2)
            + 9 * (K - 1)
        ),
        "peak_mb": (N_real * K_blk + K * B) * BYTES_PER_EXT4 / 1e6,
    }

    for v in out.values():
        v["bb_muls_kar"] = BB_MULS_PER_EXT_BASE * v["ext_base"] + BB_MULS_PER_EXT_EXT_KAR * v["ext_ext"]
    return out


# ---------------------------------------------------------------------------
# 4. SUBPROBLEM 3: Block-Banded Sliding-Window `EinSumcheck` (`W = 128`)
# ---------------------------------------------------------------------------
def build_gptoss_exp_table() -> np.ndarray:
    """Exact `EXP_TAB` from `research/exact_recompute_2026_11_06/tables.py:42-51` (`u0 = 2840`)."""
    ex = []
    u = 0
    while True:
        v = int(np.rint((2.0 ** 15) * math.exp(-u / 256.0)))
        if v == 0:
            break
        ex.append(v)
        u += 1
    return np.array(ex, dtype=np.int64)


def dense_layer_int_sliding_attn(
    q: np.ndarray,       # int64 [T, 64, 64]
    k: np.ndarray,       # int64 [T, 8, 64]
    v: np.ndarray,       # int64 [T, 8, 64]
    sink: np.ndarray,    # int64 [64] at scale fsc
    fsc: int,
    exp_tab: np.ndarray,
) -> np.ndarray:
    """Verbatim integer sliding-window GQA from `layer.py:211-226` (`pos0 = 0, sliding = True`)."""
    T_len = q.shape[0]
    u0 = exp_tab.shape[0]
    i_idx = np.arange(T_len)[:, None]
    j_idx = np.arange(T_len)[None, :]
    mask = (j_idx <= i_idx) & (i_idx - j_idx < W_SLIDE)

    kk = np.repeat(k, GQA_REP, axis=1)
    vv = np.repeat(v, GQA_REP, axis=1)
    sc = np.einsum("ihc,jhc->hij", q, kk)
    sc = np.where(mask[None], sc, np.iinfo(np.int64).min // 4)
    mx = np.maximum(sc.max(axis=2), sink[:, None])

    def ex(z):
        sh = fsc - 8
        u = np.right_shift(mx[..., None] - z, sh) if z.ndim == 3 else np.right_shift(mx - z, sh)
        return np.where(u < u0, exp_tab[np.minimum(u, u0 - 1)], 0)

    e = np.where(mask[None], ex(sc), 0)
    es = ex(np.broadcast_to(sink[:, None], mx.shape))
    Z = e.sum(axis=2) + es
    acc = np.einsum("hij,jhc->ihc", e, vv)
    Zt = Z.T[:, :, None]
    o = (2 * acc + Zt) // (2 * Zt)
    return o


def block_windowed_gqa_sliding_attn(
    q: np.ndarray,       # int64 [T, 64, 64]
    k: np.ndarray,       # int64 [T, 8, 64]
    v: np.ndarray,       # int64 [T, 8, 64]
    sink: np.ndarray,    # int64 [64]
    fsc: int,
    exp_tab: np.ndarray,
) -> np.ndarray:
    """
    Block-Windowed GQA (`W = 128`, ZERO KV head repeat, `[B_blk, 256]` window):
      - Reshapes `q` as `[B_blk, 128, 8, 8, 64]` (`b in [T/128], u in [128]`).
      - Builds virtual 256-token window `K_win[b, w, g, d]` (`w = 128*s + v in [256]`):
          `s = 0` -> block `b - 1` (`0` when `b == 0`), `s = 1` -> block `b`.
      - Contracts `sc_win = einsum("bugrd,bwgd->bgruw", q_blk, K_win)` (`[B_blk, 8, 8, 128, 256]`).
      - Local causal-128 window mask: `(s == 1 and v <= u) or (s == 0 and b >= 1 and v > u)`.
      - Contracts `acc_blk = einsum("bgruw,bwgd->bugrd", e_win, V_win)` and divides exactly!
    """
    T_len = q.shape[0]
    assert T_len % W_SLIDE == 0
    B_blk = T_len // W_SLIDE
    u0 = exp_tab.shape[0]

    q_blk = q.reshape(B_blk, W_SLIDE, H_KV, GQA_REP, HD)
    k_blk = k.reshape(B_blk, W_SLIDE, H_KV, HD)
    v_blk = v.reshape(B_blk, W_SLIDE, H_KV, HD)

    k_prev = np.concatenate([np.zeros((1, W_SLIDE, H_KV, HD), dtype=np.int64), k_blk[:-1]], axis=0)
    v_prev = np.concatenate([np.zeros((1, W_SLIDE, H_KV, HD), dtype=np.int64), v_blk[:-1]], axis=0)
    K_win = np.concatenate([k_prev, k_blk], axis=1)   # [B_blk, 256, 8, 64]
    V_win = np.concatenate([v_prev, v_blk], axis=1)   # [B_blk, 256, 8, 64]

    sc_win = np.einsum("bugrd,bwgd->bgruw", q_blk, K_win)  # [B_blk, 8, 8, 128, 256]

    u_idx = np.arange(W_SLIDE)[None, :, None]         # [1, 128, 1]
    v_idx = np.arange(W_SLIDE)[None, None, :]         # [1, 1, 128]
    b_pos = (np.arange(B_blk) >= 1)[:, None, None]    # [B_blk, 1, 1]
    mask_s0 = b_pos & (v_idx > u_idx)                 # [B_blk, 128, 128]
    mask_s1 = np.broadcast_to(v_idx <= u_idx, (B_blk, W_SLIDE, W_SLIDE))
    mask_win = np.concatenate([mask_s0, mask_s1], axis=2)  # [B_blk, 128, 256]

    sink_gr = sink.reshape(H_KV, GQA_REP)
    sc_masked = np.where(mask_win[:, None, None, :, :], sc_win, np.iinfo(np.int64).min // 4)
    mx = np.maximum(sc_masked.max(axis=-1), sink_gr[None, :, :, None])  # [B_blk, 8, 8, 128]

    sh = fsc - 8
    u_off = np.right_shift(mx[..., None] - sc_masked, sh)
    e_win = np.where(mask_win[:, None, None, :, :], np.where(u_off < u0, exp_tab[np.minimum(u_off, u0 - 1)], 0), 0)

    u_sink = np.right_shift(mx - sink_gr[None, :, :, None], sh)
    es = np.where(u_sink < u0, exp_tab[np.minimum(u_sink, u0 - 1)], 0)
    Z = e_win.sum(axis=-1) + es                       # [B_blk, 8, 8, 128]

    acc_blk = np.einsum("bgruw,bwgd->bugrd", e_win, V_win)  # [B_blk, 128, 8, 8, 64]
    Zt = Z.transpose(0, 3, 1, 2)[..., None]                 # [B_blk, 128, 8, 8, 1]
    o_blk = (2 * acc_blk + Zt) // (2 * Zt)
    return o_blk.reshape(T_len, H_Q, HD)


def eval_step_mle(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """
    Exact O(beta) verifier evaluation of the multilinear successor polynomial `step_beta(x, y)`,
    which equals `1[x == y + 1 and y < 2^beta - 1]` on `{0, 1}^beta x {0, 1}^beta` (LSB-first):
      step_beta(x, y) = sum_{c=0}^{beta - 1} (prod_{tau < c} (1 - x_tau)*y_tau)
                        * x_c*(1 - y_c) * (prod_{tau > c} eq_1(x_tau, y_tau)).
    """
    beta = x.shape[0]
    assert y.shape[0] == beta
    one = ext_one()
    # Suffix products of eq_1(x_tau, y_tau)
    eq_terms = []
    for tau in range(beta):
        xy = ext_mul(x[tau], y[tau])
        eq_terms.append(ext_add(ext_sub(ext_sub(one, x[tau]), y[tau]), ext_add(xy, xy)))
    suf_eq = [one.copy() for _ in range(beta + 1)]
    for tau in range(beta - 1, -1, -1):
        suf_eq[tau] = ext_mul(eq_terms[tau], suf_eq[tau + 1])

    total = ext_zero()
    pref_carry = one.copy()
    for c in range(beta):
        stop = ext_mul(x[c], ext_sub(one, y[c]))
        term = ext_mul(pref_carry, ext_mul(stop, suf_eq[c + 1]))
        total = ext_add(total, term)
        pref_carry = ext_mul(pref_carry, ext_mul(ext_sub(one, x[c]), y[c]))
    return total


def build_window_selector_table(r_b: np.ndarray, r_s: np.ndarray) -> np.ndarray:
    """
    Builds `W_beta[b'] = (1 - r_s)*step_beta(r_b, b') + r_s*eq(r_b, b')` for `b' in [2^beta]`,
    reducing `K_win(r_b, r_s, r_v, r_g, r_d)` to a beta-round quadratic sumcheck against
    ALREADY-COMMITTED `K(b', r_v, r_g, r_d)` -> ZERO extra KV commitments!
    """
    beta = r_b.shape[0]
    B_blk = 1 << beta
    one = ext_one()
    eq_rb = build_eq_table(r_b)  # eq_rb[b] = eq(r_b, b) for b in [B_blk]
    # Note: on Boolean b' in [B_blk], step_beta(r_b, b') = eq(r_b, b' + 1) for b' < B_blk - 1, and 0 for b' == B_blk - 1!
    step_rb = np.zeros((B_blk, 4), dtype=np.int64)
    step_rb[:-1] = eq_rb[1:]
    return ext_add(ext_mul(ext_sub(one, r_s), step_rb), ext_mul(r_s, eq_rb))


def verify_sliding_window_einsumcheck_end_to_end() -> None:
    """
    Verifies:
      1. Bit-exact integer match (`max_abs_diff == 0`) between `dense_layer_int_sliding_attn`
         and `block_windowed_gqa_sliding_attn` on random `gptoss-int v0` tensors at `T = 512`!
      2. Exact multilinear identity of `eval_step_mle` on ALL `2^(2*beta)` Boolean corners AND
         random `Ext4` challenges!
      3. End-to-end BabyBear + Ext4 Gruen Mode 2 `EinSumcheck` for Block-Windowed GQA
         (`bugrd,bwgd -> bgruw` and `bgruw,bwgd -> bugrd`) + zero-commitment `W_beta` reduction
         to committed `K[b,v,g,d]` and `V[b,v,g,d]` (+ tampered falsifiers)!
    """
    rng = np.random.default_rng(20261121)
    exp_tab = build_gptoss_exp_table()
    assert exp_tab.shape[0] == 2840, f"Expected EXP_TAB length 2840, got {exp_tab.shape[0]}"

    # 1. Bit-exact integer test at T = 512 (4 blocks of 128)
    T_test = 512
    fqk = 8
    fsc = 2 * fqk + 3
    q_int = rng.integers(-32640, 32640, size=(T_test, H_Q, HD), dtype=np.int64)
    k_int = rng.integers(-32640, 32640, size=(T_test, H_KV, HD), dtype=np.int64)
    v_int = rng.integers(-32640, 32640, size=(T_test, H_KV, HD), dtype=np.int64)
    sink_int = rng.integers(-(1 << (fsc + 2)), 1 << (fsc + 2), size=(H_Q,), dtype=np.int64)

    o_dense = dense_layer_int_sliding_attn(q_int, k_int, v_int, sink_int, fsc, exp_tab)
    o_win = block_windowed_gqa_sliding_attn(q_int, k_int, v_int, sink_int, fsc, exp_tab)
    assert np.array_equal(o_dense, o_win), "Sliding-window integer mismatch against layer_int!"

    # 2. Verify `eval_step_mle` on all 2^(2*beta) corners for beta = 3 (8 blocks) + random Ext4 point
    beta = 3
    B_blk = 1 << beta
    step_truth = np.zeros((B_blk, B_blk), dtype=np.int64)
    for x in range(B_blk):
        for y in range(B_blk):
            if x == y + 1 and y < B_blk - 1:
                step_truth[x, y] = 1
            xb = np.array([ext_from_int((x >> t) & 1) for t in range(beta)])
            yb = np.array([ext_from_int((y >> t) & 1) for t in range(beta)])
            assert np.array_equal(eval_step_mle(xb, yb), ext_from_int(step_truth[x, y]))

    rx = rng.integers(1, P, size=(beta, 4), dtype=np.int64)
    ry = rng.integers(1, P, size=(beta, 4), dtype=np.int64)
    # C-order (x, y) has y in low bits and x in high bits:
    mle_direct = mle_eval_base_tensor(step_truth.reshape(-1), np.concatenate([ry, rx], axis=0))
    assert np.array_equal(eval_step_mle(rx, ry), mle_direct), "step_beta Ext4 MLE mismatch!"

    # 3. End-to-end Block-Windowed GQA EinSumcheck + zero-commitment `K_win -> K` reduction
    # Use compact window `W_sim = 8` (`u in [8], w in [16]`, `B_blk = 4` -> `T = 32`) so direct MLE reference is instantaneous
    W_sim = 8
    B_sim = 4
    beta_sim = 2
    Q_f = rng.integers(0, P, size=(B_sim, W_sim, H_KV, GQA_REP, HD), dtype=np.int64)
    K_f = rng.integers(0, P, size=(B_sim, W_sim, H_KV, HD), dtype=np.int64)
    K_prev = np.concatenate([np.zeros((1, W_sim, H_KV, HD), dtype=np.int64), K_f[:-1]], axis=0)
    K_win = np.concatenate([K_prev, K_f], axis=1)  # [B_sim, 2*W_sim, 8, 64]

    Z_win = np.zeros((B_sim, H_KV, GQA_REP, W_sim, 2 * W_sim), dtype=np.int64)
    for d in range(HD):
        Z_win = (Z_win + Q_f[:, :, :, :, d].transpose(0, 2, 3, 1)[..., None] * K_win[:, :, :, d].transpose(0, 2, 1)[:, :, None, None, :]) % P

    r_b = rng.integers(1, P, size=(beta_sim, 4), dtype=np.int64)
    r_g = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_r = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_u = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_v = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_s = rng.integers(1, P, size=(1, 4), dtype=np.int64)
    r_w = np.concatenate([r_v, r_s], axis=0)  # w = 8*s + v => LSB: r_v (3b), MSB: r_s (1b)

    pt_Z = np.concatenate([r_w, r_u, r_r, r_g, r_b], axis=0)
    Z_claim = mle_eval_base_tensor(Z_win.reshape(-1), pt_Z)

    # F_1 partial eval: `(u, r)` on `Q_f` (`[B_sim, u, g, r, d] -> rows=(u, r), cols=(b, g, d)`)
    Q_ur_bgd = Q_f.transpose(1, 3, 0, 2, 4).reshape(W_sim * GQA_REP, (B_sim * H_KV) * HD)
    Q_pe = partial_eval_f1_base(Q_ur_bgd, np.concatenate([r_r, r_u], axis=0)).reshape(B_sim * H_KV, HD, 4)

    # `w` on `K_win` (`[B_sim, w, g, d] -> rows=w, cols=(b, g, d)`)
    Kw_w_bgd = K_win.transpose(1, 0, 2, 3).reshape(2 * W_sim, (B_sim * H_KV) * HD)
    Kw_pe = partial_eval_f1_base(Kw_w_bgd, r_w).reshape(B_sim * H_KV, HD, 4)

    # F_{>=2} = `(b, g)` => C-order `b * 8 + g` has `g` in low 3 bits and `b` in high `beta_sim` bits!
    r_bg = np.concatenate([r_g, r_b], axis=0)
    ch_sc = rng.integers(1, P, size=(beta_sim + 3 + 6, 4), dtype=np.int64)
    msgs_win, q_fin, kw_fin = prove_gruen_2op_mode2_direct(r_bg, Q_pe, Kw_pe, ch_sc)
    assert verify_gruen_2op_mode2_direct(Z_claim, r_bg, msgs_win, ch_sc, q_fin, kw_fin)
    # Falsifier:
    assert not verify_gruen_2op_mode2_direct(ext_add(Z_claim, ext_one()), r_bg, msgs_win, ch_sc, q_fin, kw_fin)

    # Now verify ZERO-COMMITMENT reduction of `kw_fin = K_win~(ch_b, r_s, r_v, ch_g, ch_d)` to `K~`!
    ch_g = ch_sc[:3]
    ch_b = ch_sc[3:3 + beta_sim]
    ch_d = ch_sc[3 + beta_sim:]
    W_sel = build_window_selector_table(ch_b, r_s[0])  # shape (B_sim, 4)
    # Partially evaluate committed `K_f[b', v, g, d]` at `(r_v, ch_g, ch_d)` -> vector of length `B_sim`:
    K_b_vgd = K_f.reshape(B_sim, W_sim * H_KV * HD)
    pt_vgd = np.concatenate([ch_d, ch_g, r_v], axis=0)
    K_vec = partial_eval_f1_base(K_b_vgd.T, pt_vgd)     # shape (B_sim, 4)
    # Run `beta_sim`-round quadratic sumcheck on `sum_{b'} W_sel[b'] * K_vec[b'] == kw_fin`:
    ch_bprime = rng.integers(1, P, size=(beta_sim, 4), dtype=np.int64)
    msgs_bridge, w_term, k_term = prove_gruen_2op_mode2_direct(
        np.zeros((0, 4), dtype=np.int64), W_sel[None, :, :], K_vec[None, :, :], ch_bprime
    )
    assert verify_gruen_2op_mode2_direct(kw_fin, np.zeros((0, 4), dtype=np.int64), msgs_bridge, ch_bprime, w_term, k_term)
    # Verifier computes `w_term` ITSELF in O(beta) ops via `eval_step_mle` + `eval_eq_point`!
    one = ext_one()
    w_verif = ext_add(
        ext_mul(ext_sub(one, r_s[0]), eval_step_mle(ch_b, ch_bprime)),
        ext_mul(r_s[0], eval_eq_point(ch_b, ch_bprime)),
    )
    assert np.array_equal(w_term % P, w_verif % P), "Verifier O(beta) window-selector check failed!"
    # And `k_term` equals ONE opening of the ALREADY-COMMITTED tensor `K_f` at `(ch_bprime, r_v, ch_g, ch_d)`!
    k_true = mle_eval_base_tensor(K_f.reshape(-1), np.concatenate([ch_d, ch_g, r_v, ch_bprime], axis=0))
    assert np.array_equal(k_term % P, k_true % P), "Committed K terminal opening mismatch!"


def price_sliding_and_causal_attention(T_len: int) -> Dict[str, Any]:
    """
    Exact 24-layer `gpt-oss-20b` attention pricing at sequence length `T_len`:
      - Arm A (`layer_int` Dense Repeated `[H, T, T]` across all 24 layers)
      - Arm B (Un-repeated GQA Dense `[8, 8, T, T]` across all 24 layers + Gruen)
      - Arm C (12 Sliding-128 Block-Windowed Even Layers + 12 Causal-Pruned Odd Layers + Gruen):
          * Even layers (`l % 2 == 0`, 12 layers): `W = 128`, `B_blk = T / 128` (`beta = log2(B_blk)`).
            - `EXP_TAB` lookups: ONLY active causal-128 cells `64 * (128*T - 8128) + 64*T`!
            - Committed `E` cells: `64 * 256 * T` (direct 256-window, 0 extra bridge) OR
              `64 * 128 * T` (128-packed active slot, +7-round `lt_7` bridge).
            - `Q.K_win^T` (`bugrd,bwgd->bgruw`): `u(7b), r(3b) in F_1(Q)`; `w(8b) in F_1(K_win)`;
              `(b, g)` (`beta + 3` bits) in `F_{>=2}`; `d(6b)` in `S`! Plus `beta`-round `K_win -> K` bridge (`4*(B_blk-1)` Ext4 muls!).
            - `E_win.V_win` (`bgruw,bwgd->bugrd`): `u(7b), r(3b) in F_1(E_win)`; `d(6b) in F_1(V_win)`;
              `(b, g)` (`beta + 3` bits) in `F_{>=2}`; `w(8b)` in `S`!
          * Odd layers (`l % 2 == 1`, 12 layers): Full causal `0 <= j <= i`.
            - `EXP_TAB` lookups & Jagged-PCS committed `E` cells: exact `64 * T*(T+1)//2` (`2.00x` pruning!).
            - `E.V` `F_1` partial eval skips upper-triangular `j > i` zeros (`50%` fewer `base*Ext4` muls!).
    """
    lt = int(round(math.log2(T_len)))
    B_blk = T_len // W_SLIDE
    beta = int(round(math.log2(B_blk)))

    # Helper: WHIR rho=1/4 PCS base-mul cost per committed base cell (from exp_pricing.py)
    def whir_muls(cells: int) -> int:
        if cells <= 0:
            return 0
        lh = max(1, int(math.ceil(math.log2(cells))))
        return round(cells * (2.5 * lh + 2.0))

    # Helper: D1b Helper-Free LogUp-GKR cost for `m` lookups into `EXP_TAB` (`N = 4096`, `b = 12`)
    def logup_gkr_d1b_bb_muls(m_queries: int) -> int:
        N_tab = 4096
        tot = m_queries + N_tab
        # Witness gen: 2*(m+N)*9 + (m+2N)*4; PIOP: 19*(m+N)*9 + 2*(m+N)*4; PCS on `m+N` cells:
        piop = (21 * tot) * BB_MULS_PER_EXT_EXT_KAR + (3 * m_queries + 4 * N_tab) * BB_MULS_PER_EXT_BASE
        return piop + whir_muls(tot)

    # --- Arm A: 24L Dense Repeated `[H, T, T]` (zkTransformer / layer.py baseline) ---
    exp_q_A_1L = H_Q * T_len * T_len + H_Q * T_len
    e_cells_A_1L = H_Q * T_len * T_len   # committed unnormalized exp weights `e[h,i,j]`
    kv_cells_A_1L = 2 * H_Q * HD * T_len
    qk_A = closed_form_prev_canonical_counts(lt, lt, 6, 6)
    ev_A = closed_form_prev_canonical_counts(lt, 6, 6, lt)

    # --- Arm B: 24L Un-repeated GQA Dense `[8, 8, T, T]` + Gruen ---
    exp_q_B_1L = exp_q_A_1L
    e_cells_B_1L = e_cells_A_1L
    kv_cells_B_1L = 2 * H_KV * HD * T_len
    qk_B = closed_form_gruen_mode2_counts(lt + 3, lt, 3, 6)
    ev_B = closed_form_gruen_mode2_counts(lt + 3, 6, 3, lt)

    # --- Arm C1: 1 Sliding-128 Even Layer (Block-Windowed GQA + Gruen + Zero-Commit `step_beta`) ---
    active_sliding_per_head = W_SLIDE * T_len - (W_SLIDE * (W_SLIDE - 1)) // 2  # 128*T - 8128
    exp_q_slide_1L = H_Q * active_sliding_per_head + H_Q * T_len
    e_cells_slide_256_1L = H_Q * (2 * W_SLIDE) * T_len   # 16,384 * T
    e_cells_slide_128_1L = H_Q * W_SLIDE * T_len         # 8,192 * T (packed active window)

    # QK sliding (`bugrd,bwgd -> bgruw`): F1_1 = u(7)+r(3)=10, F1_2 = w(8), F2 = b(beta)+g(3), S = d(6)
    # Note: K_win[b=0, s=0] is zero, and in EV `E_win` has 50% zeros in 256-window (`128*T - 8128` nonzeros)!
    qk_slide = closed_form_gruen_mode2_counts(10, 8, beta + 3, 6)
    ev_slide_full256 = closed_form_gruen_mode2_counts(10, 6, beta + 3, 8)
    # Skipping the known-masked 50% zeros of `E_win` during `partial_eval_f1_base`:
    e_win_zero_saved_eb = H_Q * (2 * W_SLIDE * T_len - active_sliding_per_head)
    ev_slide_pruned_eb = ev_slide_full256["pe_ext_base"] - e_win_zero_saved_eb
    bridge_sc_ee = 2 * 4 * max(0, B_blk - 1)  # `K_win -> K` and `V_win -> V` `beta`-round bridges!

    slide_sc_ee_1L = qk_slide["sc_ext_ext"] + ev_slide_full256["sc_ext_ext"] + bridge_sc_ee
    slide_pe_eb_1L = qk_slide["pe_ext_base"] + ev_slide_pruned_eb

    # --- Arm C2: 1 Odd Full-Attention Layer (Causal Pruning + Un-repeated GQA + Gruen) ---
    causal_pairs = T_len * (T_len + 1) // 2
    exp_q_odd_1L = H_Q * causal_pairs + H_Q * T_len
    e_cells_odd_1L = H_Q * causal_pairs
    qk_odd = qk_B
    ev_odd_pe_eb = (H_Q * causal_pairs) + (HD * H_KV * T_len)  # skips j > i zeros in E!
    odd_sc_ee_1L = qk_odd["sc_ext_ext"] + ev_B["sc_ext_ext"]
    odd_pe_eb_1L = qk_odd["pe_ext_base"] + ev_odd_pe_eb

    # --- 24-Layer Totals ---
    exp_24_dense = 24 * exp_q_A_1L
    exp_24_hybrid = 12 * exp_q_slide_1L + 12 * exp_q_odd_1L

    ecells_24_dense = 24 * e_cells_A_1L
    ecells_24_hybrid_256 = 12 * e_cells_slide_256_1L + 12 * e_cells_odd_1L
    ecells_24_hybrid_128 = 12 * e_cells_slide_128_1L + 12 * e_cells_odd_1L

    sc_ee_1L_gqa_dense = qk_B["sc_ext_ext"] + ev_B["sc_ext_ext"]
    pe_eb_1L_gqa_dense = qk_B["pe_ext_base"] + ev_B["pe_ext_base"]

    # Total 24L Attention Prover BB Muls (Contraction PE+SC + `EXP_TAB` D1b LogUp-GKR + `E` & `KV` WHIR PCS):
    tot_bb_dense_rep_24L = (
        24 * (qk_A["bb_muls_kar"] + ev_A["bb_muls_kar"] + whir_muls(kv_cells_A_1L))
        + logup_gkr_d1b_bb_muls(exp_24_dense)
    )
    tot_bb_gqa_dense_24L = (
        24 * (qk_B["bb_muls_kar"] + ev_B["bb_muls_kar"] + whir_muls(kv_cells_B_1L))
        + logup_gkr_d1b_bb_muls(exp_24_dense)
    )
    hybrid_einsum_bb_24L = (
        12 * (BB_MULS_PER_EXT_BASE * slide_pe_eb_1L + BB_MULS_PER_EXT_EXT_KAR * slide_sc_ee_1L)
        + 12 * (BB_MULS_PER_EXT_BASE * odd_pe_eb_1L + BB_MULS_PER_EXT_EXT_KAR * odd_sc_ee_1L)
        + 24 * whir_muls(kv_cells_B_1L)
    )
    tot_bb_hybrid_24L = hybrid_einsum_bb_24L + logup_gkr_d1b_bb_muls(exp_24_hybrid)

    tot_bb_1L_gqa = (
        qk_B["bb_muls_kar"] + ev_B["bb_muls_kar"] + whir_muls(kv_cells_B_1L)
        + logup_gkr_d1b_bb_muls(exp_q_B_1L)
    )
    tot_bb_1L_slide = (
        BB_MULS_PER_EXT_BASE * slide_pe_eb_1L + BB_MULS_PER_EXT_EXT_KAR * slide_sc_ee_1L
        + whir_muls(kv_cells_B_1L) + logup_gkr_d1b_bb_muls(exp_q_slide_1L)
    )

    return {
        "T": T_len,
        "slide_1L_exp_dense": exp_q_A_1L,
        "slide_1L_exp_win": exp_q_slide_1L,
        "slide_1L_exp_x": exp_q_A_1L / exp_q_slide_1L,
        "slide_1L_ecells_256": e_cells_slide_256_1L,
        "slide_1L_ecells_128": e_cells_slide_128_1L,
        "slide_1L_pe_x": pe_eb_1L_gqa_dense / slide_pe_eb_1L,
        "slide_1L_sc_ee_dense_gqa": sc_ee_1L_gqa_dense,
        "slide_1L_sc_ee_win": slide_sc_ee_1L,
        "slide_1L_sc_x": sc_ee_1L_gqa_dense / slide_sc_ee_1L,
        "slide_1L_tot_x": tot_bb_1L_gqa / tot_bb_1L_slide,
        "exp_24L_dense": exp_24_dense,
        "exp_24L_hybrid": exp_24_hybrid,
        "exp_24L_x": exp_24_dense / exp_24_hybrid,
        "ecells_24L_dense": ecells_24_dense,
        "ecells_24L_hybrid_128": ecells_24_hybrid_128,
        "ecells_24L_x": ecells_24_dense / ecells_24_hybrid_128,
        "tot_bb_24L_rep": tot_bb_dense_rep_24L,
        "tot_bb_24L_gqa": tot_bb_gqa_dense_24L,
        "tot_bb_24L_hybrid": tot_bb_hybrid_24L,
        "tot_24L_vs_rep_x": tot_bb_dense_rep_24L / tot_bb_hybrid_24L,
        "tot_24L_vs_gqa_x": tot_bb_gqa_dense_24L / tot_bb_hybrid_24L,
    }


# ---------------------------------------------------------------------------
# 5. SUBPROBLEM 4: Active-4 Sparse MoE `EinSumcheck` + 24-Layer Uniform Folding
# ---------------------------------------------------------------------------
def verify_active4_moe_and_layer_fold() -> None:
    """
    End-to-end BabyBear + Ext4 verification of:
      1. Active-4 Bucketed MoE `EinSumcheck`: proves ONLY the `M_act <= 32` experts with
         `T_e > 0` (`0` work & `0` openings on unrouted experts!) against per-expert
         commitments `R_{l, e}` (`moe-router-binding.md` §5.3 Decisions D4-D5).
      2. Multi-Layer Uniform Folded `EinSumcheck` (`L_real = 6` padded to `8`, analogous to
         `24 -> 32`): proves all `L_real` layers in ONE Gruen `EinSumcheck` while skipping
         zero-padded dummy layers `l >= L_real`!
    """
    rng = np.random.default_rng(20261122)

    # Part 1: Single-token (`T = 2`, `NE = 8`, `TOPK = 2`) bucketed MoE vs dense masked MoE
    T_tok, NE_sim, K_top, N_out, K_blk, B = 2, 8, 2, 4, 2, 32
    m_in = rng.integers(-100, 100, size=(T_tok, K_blk, B), dtype=np.int64)
    Q_bank = rng.choice(E2M1_X2_VALS, size=(NE_sim, N_out, K_blk, B))
    S_bank = (1 << rng.integers(0, 4, size=(NE_sim, N_out, K_blk))).astype(np.int64)
    logits = rng.integers(-1000, 1000, size=(T_tok, NE_sim), dtype=np.int64)

    # Canonical tie-break top-k (`layer.py:90-92`: `(-lg[e], e)`)
    routed = [sorted(range(NE_sim), key=lambda e_: (-int(logits[t, e_]), e_))[:K_top] for t in range(T_tok)]
    buckets: Dict[int, List[int]] = {}
    for t in range(T_tok):
        for slot, e_ in enumerate(routed[t]):
            buckets.setdefault(e_, []).append(t)

    # Only `len(buckets) <= 4` of `8` experts fire! Verify each active bucket via Horner MXFP4 EinSumcheck:
    assert len(buckets) <= T_tok * K_top < NE_sim
    for e_, tok_rows in buckets.items():
        Te = len(tok_rows)
        Te_pad = 1 << max(0, int(math.ceil(math.log2(max(Te, 1)))))
        X_bucket = np.zeros((Te_pad, K_blk, B), dtype=np.int64)
        X_bucket[:Te] = m_in[tok_rows]
        D_bucket = np.einsum("ikb,jkb,jk->ij", X_bucket, Q_bank[e_], S_bank[e_]) % P

        log_i = int(round(math.log2(Te_pad)))
        r_i = rng.integers(1, P, size=(log_i, 4), dtype=np.int64)
        r_j = rng.integers(1, P, size=(2, 4), dtype=np.int64)
        D_claim = mle_eval_base_tensor(D_bucket.reshape(-1), np.concatenate([r_j, r_i], axis=0))

        X_ri = partial_eval_f1_base(X_bucket.reshape(Te_pad, K_blk * B), r_i).reshape(K_blk, B, 4) if log_i > 0 else \
               np.stack([(X_bucket[0] % P), np.zeros_like(X_bucket[0]), np.zeros_like(X_bucket[0]), np.zeros_like(X_bucket[0])], axis=-1)
        chals = {
            "b": rng.integers(1, P, size=(5, 4), dtype=np.int64),
            "j": rng.integers(1, P, size=(2, 4), dtype=np.int64),
            "k": rng.integers(1, P, size=(1, 4), dtype=np.int64),
        }
        msgs, fins, _ = prove_mxfp4_tensor_factored_horner_bjk(X_ri, Q_bank[e_], S_bank[e_], r_j, chals)
        assert verify_mxfp4_schedule_msgs(D_claim, ("b", "j", "k"), r_j, msgs, chals, fins)

    # Part 2: Multi-Layer Uniform Folding (`L_real = 6` padded to `L_pad = 8`, zero-layer skipping!)
    L_real, L_pad = 6, 8
    I_len, J_len, D_in = 4, 4, 8
    X_layers = np.zeros((L_pad, I_len, D_in), dtype=np.int64)
    W_layers = np.zeros((L_pad, J_len, D_in), dtype=np.int64)
    X_layers[:L_real] = rng.integers(0, P, size=(L_real, I_len, D_in), dtype=np.int64)
    W_layers[:L_real] = rng.integers(0, P, size=(L_real, J_len, D_in), dtype=np.int64)
    Y_layers = np.zeros((L_pad, I_len, J_len), dtype=np.int64)
    for d in range(D_in):
        Y_layers = (Y_layers + (X_layers[:, :, d, None] * W_layers[:, None, :, d]) % P) % P

    r_l = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_i = rng.integers(1, P, size=(2, 4), dtype=np.int64)
    r_j = rng.integers(1, P, size=(2, 4), dtype=np.int64)
    Y_claim = mle_eval_base_tensor(Y_layers.reshape(-1), np.concatenate([r_j, r_i, r_l], axis=0))

    # Partial eval `F_1` (`i` on X, `j` on W) SKIPPING dummy layers `l in {6, 7}` (`25%` saved!):
    X_pe = np.zeros((L_pad, D_in, 4), dtype=np.int64)
    W_pe = np.zeros((L_pad, D_in, 4), dtype=np.int64)
    X_pe[:L_real] = partial_eval_f1_base(
        X_layers[:L_real].transpose(1, 0, 2).reshape(I_len, L_real * D_in), r_i
    ).reshape(L_real, D_in, 4)
    W_pe[:L_real] = partial_eval_f1_base(
        W_layers[:L_real].transpose(1, 0, 2).reshape(J_len, L_real * D_in), r_j
    ).reshape(L_real, D_in, 4)

    ch_fold = rng.integers(1, P, size=(3 + 3, 4), dtype=np.int64)
    msgs_f, xf, wf = prove_gruen_2op_mode2_direct(r_l, X_pe, W_pe, ch_fold)
    assert verify_gruen_2op_mode2_direct(Y_claim, r_l, msgs_f, ch_fold, xf, wf)
    assert not verify_gruen_2op_mode2_direct(ext_add(Y_claim, ext_one()), r_l, msgs_f, ch_fold, xf, wf)


def price_active4_moe_and_24layer_folding() -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Deterministic pricing of:
      (A) Active-4 Bucketed MoE vs Dense-32 MoE across `T in {1, 8, 32, 128, 512, 2048, 4096, 16384}`
          (Monte Carlo 128-trial deterministic seed for exact dyadic bucket padding + closed-form
          `32*(1 - (28/32)^T)` active-expert expectation, including router binding `moe-router-binding.md`
          variant (b) + `GLU_TAB` & `rq2` nonlinearities + WHIR PCS!).
      (B) 24-Layer Uniform Folding across all `gpt-oss-20b` operator classes (`q_proj`, `k/v_proj`,
          `o_proj`, `router`, `sliding_attn`, `full_attn`, `moe_gate_up`, `moe_down`) at `T = 2048`.
    """
    rng = np.random.default_rng(20261121)

    # Single-expert MXFP4 `(b, k, j)` weight-side sumcheck cost (`8c. TF + Horner + ActiveSupport`):
    gu_w = price_mxfp4_real_shapes_exact(5760, 2880)["8c. b->j->k TF + Horner + ActiveSupport"]["bb_muls_kar"]
    dn_w = price_mxfp4_real_shapes_exact(2880, 2880)["8c. b->j->k TF + Horner + ActiveSupport"]["bb_muls_kar"]
    w_sc_per_expert = gu_w + dn_w

    def whir_muls(cells: int) -> int:
        if cells <= 0:
            return 0
        lh = max(1, int(math.ceil(math.log2(cells))))
        return round(cells * (2.5 * lh + 2.0))

    def logup_d1b_per_query_muls(m_q: int, N_tab: int) -> int:
        tot = m_q + N_tab
        return (21 * tot) * BB_MULS_PER_EXT_EXT_KAR + (3 * m_q + 4 * N_tab) * BB_MULS_PER_EXT_BASE + whir_muls(tot)

    moe_rows: List[Dict[str, Any]] = []
    for T_len in (1, 8, 32, 128, 512, 2048, 4096, 16384):
        # Simulate 128 layers of uniform top-4-of-32 routing to get exact bucket padding stats:
        n_trials = 128
        act_cnts = []
        pad_sums = []
        for _ in range(n_trials):
            # Sample 4 distinct experts per token:
            scores = rng.random((T_len, N_EXPERTS))
            top4 = np.argpartition(scores, -TOP_K, axis=1)[:, -TOP_K:]
            counts = np.bincount(top4.reshape(-1), minlength=N_EXPERTS)
            nz = counts[counts > 0]
            act_cnts.append(len(nz))
            pad_sums.append(int(sum(1 << int(math.ceil(math.log2(int(c)))) for c in nz)))

        mean_act_exp = float(np.mean(act_cnts))
        exact_act_exp = N_EXPERTS * (1.0 - (28.0 / 32.0) ** T_len)
        mean_pad_rows = float(np.mean(pad_sums))
        active_rows = TOP_K * T_len
        dense_rows = N_EXPERTS * T_len
        pad_overhead = mean_pad_rows / active_rows

        # Per-expert-token-row costs (`layer.py:253-265`):
        # 1. Activation `F_1` partial eval (2-limb int8 X): `2 * 2880` (`gate_up` input `m`) + `2 * 2880` (`down` input `h_`)
        #    -> Note `m[t]` can be gathered per bucket (`pad_rows * 2880` or `active_rows * 2880` under Jagged PCS);
        #       `h_` has `pad_rows * 2880` (`dyadic`) or `active_rows * 2880` (`Jagged PCS`).
        # 2. Committed expert intermediates per active expert-token row (`gu` 5760 + `glu` 2880 + `h_` 2880 + `dn` 2880 = 14,400 cells)
        # 3. Lookups per active expert-token row: `GLU_TAB` (`18,433` entries -> `2^15`) = `2880` lookups;
        #    requant `rq2`/`rq` (`5760 + 2880 + 2880 + 2880 = 14,400` 16-bit range checks = `14,400` lookups).
        # 4. Router binding (`moe-router-binding.md` §2.3 variant (b) on `gpt-oss` `NE=32, TOPK=4`):
        #    Per token per layer: `32` logits + `32` `{0,1}` indicators + `1` `tau` + `4` `exp` + `4` weights = `73` cells,
        #    `33 * 2 = 66` 16-bit range lookups + `4` `EXP_TAB` lookups = `70` lookups!

        # Across 24 layers:
        w_sc_24_dense = 24 * N_EXPERTS * w_sc_per_expert
        w_sc_24_act = round(24 * exact_act_exp * w_sc_per_expert)

        pe_24_dense = 24 * dense_rows * (2 * 2880) * BB_MULS_PER_EXT_BASE
        pe_24_dyadic = round(24 * mean_pad_rows * (2 * 2880) * BB_MULS_PER_EXT_BASE)
        pe_24_jagged = 24 * active_rows * (2 * 2880) * BB_MULS_PER_EXT_BASE

        cells_24_dense = 24 * (dense_rows * 14400 + T_len * 32)
        cells_24_jagged = 24 * (active_rows * 14400 + T_len * 73)
        cells_24_dyadic = round(24 * (mean_pad_rows * 14400 + T_len * 73))

        glu_q_dense = 24 * dense_rows * 2880
        glu_q_act = 24 * active_rows * 2880
        rc_q_dense = 24 * dense_rows * 14400
        rc_q_act = 24 * (active_rows * 14400 + T_len * 70)

        nonlin_24_dense = whir_muls(cells_24_dense) + logup_d1b_per_query_muls(glu_q_dense, 32768) + logup_d1b_per_query_muls(rc_q_dense, 65536)
        nonlin_24_jagged = whir_muls(cells_24_jagged) + logup_d1b_per_query_muls(glu_q_act, 32768) + logup_d1b_per_query_muls(rc_q_act, 65536)
        nonlin_24_dyadic = whir_muls(cells_24_dyadic) + logup_d1b_per_query_muls(glu_q_act, 32768) + logup_d1b_per_query_muls(rc_q_act, 65536)

        router_only_cells_24 = 24 * T_len * 73
        router_share_pct = 100.0 * router_only_cells_24 / cells_24_jagged

        tot_dense = w_sc_24_dense + pe_24_dense + nonlin_24_dense
        tot_dyadic = w_sc_24_act + pe_24_dyadic + nonlin_24_dyadic
        tot_jagged = w_sc_24_act + pe_24_jagged + nonlin_24_jagged

        moe_rows.append({
            "T": T_len,
            "active_experts_of_32": exact_act_exp,
            "active_rows_1L": active_rows,
            "dyadic_pad_rows_1L": mean_pad_rows,
            "pad_factor": pad_overhead,
            "weight_sc_speedup": w_sc_24_dense / w_sc_24_act,
            "einsum_only_jagged_x": (w_sc_24_dense + pe_24_dense) / (w_sc_24_act + pe_24_jagged),
            "tot_moe_dyadic_bb": tot_dyadic,
            "tot_moe_jagged_bb": tot_jagged,
            "tot_moe_dense_bb": tot_dense,
            "tot_moe_dyadic_x": tot_dense / tot_dyadic,
            "tot_moe_jagged_x": tot_dense / tot_jagged,
            "router_cell_share_pct": router_share_pct,
        })

    # Part B: 24-Layer (+ 32-Expert) Uniform Folding Summary across Operator Types at T = 2048
    # Format: (op_name, unf_instances, rounds_per_unf, fold_instances, rounds_per_fold, openings_unf, openings_fold, naive_pad_overhead_pct)
    fold_ops = [
        ("q_proj (BF16/MXFP4 4096x2880)", 24, 24, 1, 29, 48, 2, 33.3),
        ("k_proj + v_proj (2 x 512x2880)", 48, 21, 2, 26, 96, 4, 33.3),
        ("o_proj (2880x4096)", 24, 24, 1, 29, 48, 2, 33.3),
        ("Sliding-128 GQA QK+EV (12 even L)", 24, 14, 2, 18, 48, 4, 33.3),
        ("Full Causal GQA QK+EV (12 odd L)", 24, 12, 2, 16, 48, 4, 33.3),
        ("MoE Router (32x2880)", 24, 17, 1, 22, 48, 2, 33.3),
        ("MoE Active-4 gate_up (768 buckets)", 768, 25, 1, 35, 1536, 3, 33.3),
        ("MoE Active-4 down (768 buckets)", 768, 24, 1, 34, 1536, 3, 33.3),
    ]
    fold_rows = []
    for name, u_inst, u_rnd, f_inst, f_rnd, u_op, f_op, pad_pct in fold_ops:
        u_tot_rnds = u_inst * u_rnd
        f_tot_rnds = f_inst * f_rnd
        # Mode 2 transcript: ~2.3 Ext4 elems/round + 2-3 terminal claims per instance
        u_kb = (u_tot_rnds * 2 + u_inst * 3) * BYTES_PER_EXT4 / 1024.0
        f_kb = (f_tot_rnds * 2 + f_inst * 3) * BYTES_PER_EXT4 / 1024.0
        fold_rows.append({
            "operator": name,
            "unfolded_inst": u_inst,
            "folded_inst": f_inst,
            "unfolded_rounds": u_tot_rnds,
            "folded_rounds": f_tot_rnds,
            "round_reduction_x": u_tot_rnds / f_tot_rnds,
            "unfolded_openings": u_op,
            "folded_openings": f_op,
            "transcript_kb_unf": u_kb,
            "transcript_kb_fold": f_kb,
            "zero_skip_prover_overhead": "0.0% (vs +33.3% naive)",
        })

    return moe_rows, fold_rows


# ---------------------------------------------------------------------------
# 6. Master End-to-End Verification Suite & Markdown Table Printer
# ---------------------------------------------------------------------------
def run_all_verifications() -> None:
    rng = np.random.default_rng(20261121)

    # ---- Verification 1: Gruen Mode 1 & Mode 2 on Un-repeated GQA (`t = 32`) + `r_u = 0` & Jolt-splice falsifiers ----
    t = 32
    lt = 5
    Q = rng.integers(0, P, size=(t, H_KV, GQA_REP, HD), dtype=np.int64)
    K = rng.integers(0, P, size=(t, H_KV, HD), dtype=np.int64)
    Z = np.zeros((H_KV, GQA_REP, t, t), dtype=np.int64)
    for d in range(HD):
        Z = (Z + Q[:, :, :, d].transpose(1, 2, 0)[:, :, :, None] * K[:, :, d].transpose(1, 0)[:, None, None, :]) % P

    r_g = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_r = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    r_i = rng.integers(1, P, size=(lt, 4), dtype=np.int64)
    r_j = rng.integers(1, P, size=(lt, 4), dtype=np.int64)
    Z_claim = mle_eval_base_tensor(Z.reshape(-1), np.concatenate([r_j, r_i, r_r, r_g], axis=0))

    ctr_m2 = OpCounter()
    Q_pe = partial_eval_f1_base(Q.transpose(0, 2, 1, 3).reshape(t * GQA_REP, H_KV * HD), np.concatenate([r_r, r_i], axis=0), ctr_m2).reshape(H_KV, HD, 4)
    K_pe = partial_eval_f1_base(K.reshape(t, H_KV * HD), r_j, ctr_m2).reshape(H_KV, HD, 4)
    ch_9 = rng.integers(1, P, size=(9, 4), dtype=np.int64)

    msgs_m2, qf2, kf2 = prove_gruen_2op_mode2_direct(r_g, Q_pe, K_pe, ch_9, ctr_m2)
    assert verify_gruen_2op_mode2_direct(Z_claim, r_g, msgs_m2, ch_9, qf2, kf2), "Gruen Mode 2 GQA failed!"
    cf_m2 = closed_form_gruen_mode2_counts(lt + 3, lt, 3, 6)
    assert ctr_m2.ext_base_muls == cf_m2["pe_ext_base"], (ctr_m2.ext_base_muls, cf_m2)
    assert ctr_m2.ext_ext_muls == cf_m2["total_ext_ext"], (ctr_m2.ext_ext_muls, cf_m2)
    assert ctr_m2.ext_invs == 0, "Gruen Mode 2 prover should perform ZERO inversions!"

    # Mode 1 (Wire-Transparent Setty-Thaler) verified by UNMODIFIED cubic verifier:
    msgs_m1, qf1, kf1 = prove_gruen_2op_mode1_wire_transparent(Z_claim, r_g, Q_pe, K_pe, ch_9)
    assert verify_standard_cubic_einsumcheck(Z_claim, r_g, msgs_m1, ch_9, qf1, kf1), "Gruen Mode 1 wire-transparent failed!"

    # Edge-case tooth: force `r_g[1] = 0` (`l_u(1) == 0`) and verify BOTH Mode 1 and Mode 2 pass!
    r_g_zero = r_g.copy()
    r_g_zero[1] = ext_zero()
    Z_claim_z = mle_eval_base_tensor(Z.reshape(-1), np.concatenate([r_j, r_i, r_r, r_g_zero], axis=0))
    msgs_z2, qfz2, kfz2 = prove_gruen_2op_mode2_direct(r_g_zero, Q_pe, K_pe, ch_9)
    assert verify_gruen_2op_mode2_direct(Z_claim_z, r_g_zero, msgs_z2, ch_9, qfz2, kfz2), "r_u=0 fallback failed in Mode 2!"
    msgs_z1, qfz1, kfz1 = prove_gruen_2op_mode1_wire_transparent(Z_claim_z, r_g_zero, Q_pe, K_pe, ch_9)
    assert verify_standard_cubic_einsumcheck(Z_claim_z, r_g_zero, msgs_z1, ch_9, qfz1, kfz1), "r_u=0 fallback failed in Mode 1!"

    # Falsifiers: tampered claim AND Jolt-PR-#1474 boundary splice between `F_{>=2}` (round 2) and `S` (round 3)!
    assert not verify_gruen_2op_mode2_direct(ext_add(Z_claim, ext_one()), r_g, msgs_m2, ch_9, qf2, kf2)
    spliced_msgs = list(msgs_m2)
    spliced_msgs[2] = (spliced_msgs[2][0], ext_add(spliced_msgs[2][1], ext_one()))
    assert not verify_gruen_2op_mode2_direct(Z_claim, r_g, spliced_msgs, ch_9, qf2, kf2), "Boundary splice accepted!"

    # ---- Verification 2: All 6 MXFP4 Schedules + Tensor-Factored E2M1 Horner + Closed-Form 0-Discrepancy ----
    I_s, J_s, K_s, B_s = 4, 8, 4, 32
    X_s = rng.integers(-128, 128, size=(I_s, K_s, B_s), dtype=np.int64)
    Q_s = rng.choice(E2M1_X2_VALS, size=(J_s, K_s, B_s))
    S_s = (1 << rng.integers(0, 5, size=(J_s, K_s))).astype(np.int64)
    D_s = np.einsum("ikb,jkb,jk->ij", X_s, Q_s, S_s) % P

    r_is = rng.integers(1, P, size=(2, 4), dtype=np.int64)
    r_js = rng.integers(1, P, size=(3, 4), dtype=np.int64)
    D_s_claim = mle_eval_base_tensor(D_s.reshape(-1), np.concatenate([r_js, r_is], axis=0))
    X_s_ri = partial_eval_f1_base(X_s.reshape(I_s, K_s * B_s), r_is).reshape(K_s, B_s, 4)
    ch_s = {
        "j": rng.integers(1, P, size=(3, 4), dtype=np.int64),
        "k": rng.integers(1, P, size=(2, 4), dtype=np.int64),
        "b": rng.integers(1, P, size=(5, 4), dtype=np.int64),
    }

    cf_synth = price_mxfp4_real_shapes_exact(J_s, K_s * 32)
    schedule_map = [
        (("j", "k", "b"), "1. j -> k -> b (Alg1+Gruen)"),
        (("j", "b", "k"), "2. j -> b -> k (Alg1+Gruen)"),
        (("k", "j", "b"), "3. k -> j -> b (Alg1+Gruen)"),
        (("k", "b", "j"), "4. k -> b -> j (Alg1+Gruen)"),
        (("b", "j", "k"), "5. b -> j -> k (Alg1+Gruen)"),
        (("b", "k", "j"), "6. b -> k -> j (Alg1+Gruen)"),
    ]
    bjk_ref_msgs = None
    for ord_tup, label in schedule_map:
        msgs_o, fins_o, ctr_o = run_mxfp4_schedule_sim(ord_tup, X_s_ri, Q_s, S_s, r_js, ch_s)
        assert verify_mxfp4_schedule_msgs(D_s_claim, ord_tup, r_js, msgs_o, ch_s, fins_o), f"Schedule {ord_tup} failed!"
        # Check degree profile: `b` (5 rounds) deg 2 AND `j` (3 rounds) deg 2, ONLY `k` (2 rounds) deg 3!
        deg_counts = {2: sum(1 for _, d, _ in msgs_o if d == 2), 3: sum(1 for _, d, _ in msgs_o if d == 3)}
        assert deg_counts == {2: 8, 3: 2}, f"Unexpected round degrees: {deg_counts}"
        # Check ZERO discrepancy between runtime `OpCounter` and closed-form pricing formulas!
        assert ctr_o.ext_base_muls == cf_synth[label]["ext_base"], (label, ctr_o.ext_base_muls, cf_synth[label]["ext_base"])
        assert ctr_o.ext_ext_muls == cf_synth[label]["ext_ext"], (label, ctr_o.ext_ext_muls, cf_synth[label]["ext_ext"])
        if ord_tup == ("b", "j", "k"):
            bjk_ref_msgs = msgs_o

    # Verify Tensor-Factored (`l_0 = 5`) + E2M1 4-Bit-Plane Horner produces BIT-IDENTICAL messages to `b -> j -> k`!
    msgs_tf, fins_tf, ctr_tf = prove_mxfp4_tensor_factored_horner_bjk(X_s_ri, Q_s, S_s, r_js, ch_s)
    assert verify_mxfp4_schedule_msgs(D_s_claim, ("b", "j", "k"), r_js, msgs_tf, ch_s, fins_tf)
    for (ax1, d1, m1), (ax2, d2, m2) in zip(bjk_ref_msgs, msgs_tf):
        assert ax1 == ax2 and d1 == d2
        for e1, e2 in zip(m1, m2):
            assert np.array_equal(e1 % P, e2 % P), "Tensor-Factored Horner message differed from standard b->j->k!"
    cf_horner = cf_synth["8b. b->j->k Tensor-Factored + E2M1 Horner"]
    assert ctr_tf.ext_base_muls == cf_horner["ext_base"], (ctr_tf.ext_base_muls, cf_horner["ext_base"])
    assert ctr_tf.ext_ext_muls == cf_horner["ext_ext"], (ctr_tf.ext_ext_muls, cf_horner["ext_ext"])

    # ---- Verification 3: Sliding-Window `W = 128` Integer Parity + `step_beta` Zero-Commitment Bridge ----
    verify_sliding_window_einsumcheck_end_to_end()

    # ---- Verification 4: Active-4 Bucketed MoE + Multi-Layer Uniform Folding ----
    verify_active4_moe_and_layer_fold()


def print_markdown_report() -> None:
    print("# `einsum-turbo` Deterministic Verification & Pricing Output (`BabyBear + Ext4`)\n")
    print("- `[EXECUTED]` All 4 end-to-end finite-field prover/verifier suites, `r_u = 0` fallback checks, Jolt-style boundary-splice falsifiers, 6-schedule `OpCounter` closed-form cross-checks (`0` op discrepancy), and `gptoss-int v0` (`W = 128`, `u0 = 2840`) sliding-window integer equivalence tests **PASSED**.\n")

    # ---- Table 1: Subproblem 1 (Gruen `eq`-Factored EinSumcheck on GQA & MXFP4) ----
    print("## 1. Gruen `eq`-Factored `EinSumcheck` (`ePrint 2024/108` §3.2) on Un-Repeated GQA\n")
    print("| Context $T$ | `zkT` Naive Rep SC `Ext4` | `zkT` Naive GQA SC `Ext4` | Prev Canonical (`{0,1,inf}`) SC `Ext4` | **Gruen Mode 2 (`{0,inf}`)** SC `Ext4` | SC Gain vs `zkT` GQA / Prev | Transcript `Ext4` (`Prev -> Gruen`) |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for T_len in (128, 512, 2048, 4096, 16384):
        lt = int(round(math.log2(T_len)))
        zkt_rep = 19 * ((64 * 64 - 1) + (64 * T_len - 1)) + 62 + 62
        zkt_gqa = 19 * ((8 * 64 - 1) + (8 * T_len - 1)) + 6 + 6
        prev_c = closed_form_prev_canonical_counts(lt + 3, lt, 3, 6)
        prev_v = closed_form_prev_canonical_counts(lt + 3, 6, 3, lt)
        gr_c = closed_form_gruen_mode2_counts(lt + 3, lt, 3, 6)
        gr_v = closed_form_gruen_mode2_counts(lt + 3, 6, 3, lt)
        sc_prev = prev_c["sc_ext_ext"] + prev_v["sc_ext_ext"]
        sc_gr = gr_c["sc_ext_ext"] + gr_v["sc_ext_ext"]
        tr_prev = prev_c["transcript_ext4"] + prev_v["transcript_ext4"]
        tr_gr = gr_c["transcript_ext4"] + gr_v["transcript_ext4"]
        print(
            f"| {T_len:,} | {zkt_rep:,} | {zkt_gqa:,} | {sc_prev:,} | **{sc_gr:,}** | "
            f"**{zkt_gqa/sc_gr:.2f}x** / **{sc_prev/sc_gr:.2f}x** | `{tr_prev} -> {tr_gr}` (**{tr_prev/tr_gr:.2f}x**) |"
        )

    # ---- Table 2: Subproblem 2 (All 6 MXFP4 Elimination Orders + SVO + Tensor-Factored E2M1 Horner) ----
    print("\n## 2. Native MXFP4 (`ikb,jkb,jk -> ij`) Schedule & `SVO` Comparison on `gpt-oss-20b` Shapes\n")
    for shape_name, (Nr, Kr) in [
        ("`gate_up` ($5760 \\times 2880$, padded $8192 \\times 128 \\times 32 = 33.55\\text{M}$)", (5760, 2880)),
        ("`down` ($2880 \\times 2880$, padded $4096 \\times 128 \\times 32 = 16.78\\text{M}$)", (2880, 2880)),
        ("`q_proj` ($4096 \\times 2880$, padded $4096 \\times 128 \\times 32 = 16.78\\text{M}$)", (4096, 2880)),
    ]:
        res = price_mxfp4_real_shapes_exact(Nr, Kr)
        base_bb = res["1. j -> k -> b (Alg1+Gruen)"]["bb_muls_kar"]
        base_ee = res["1. j -> k -> b (Alg1+Gruen)"]["ext_ext"]
        print(f"### Shape: {shape_name}\n")
        print("| Schedule / Prover Variant | `base x Ext4` Muls | `Ext4 x Ext4` Muls | Total BB Mul-Equiv (Kar) | Peak `Ext4` Buf (MB) | `Ext4` Mul Gain vs `j->k->b` | Total BB Gain |")
        print("|---|---:|---:|---:|---:|---:|---:|")
        for k_lbl, v in res.items():
            print(
                f"| {k_lbl} | {v['ext_base']:,} | {v['ext_ext']:,} | {v['bb_muls_kar']:,} | "
                f"{v['peak_mb']:.2f} MB | {base_ee / v['ext_ext']:.2f}x | **{base_bb / v['bb_muls_kar']:.2f}x** |"
            )
        print()

    # ---- Table 3: Subproblem 3 (Block-Banded Sliding-Window W=128 + Causal Odd Layers) ----
    print("## 3. Block-Banded Sliding-Window (`W = 128`, 12 Even Layers) + Causal-Pruned Odd Layers (`gpt-oss-20b`)\n")
    print("| $T$ | 1L Sliding `EXP_TAB` (`Dense -> Win128`) | 1L Sliding PE `x` / SC `Ext4` (`GQA -> Win128`) | **1L Sliding Tot `x`** | 24L `EXP_TAB` (`Dense -> Hybrid`) | 24L Total Attn+PCS BB Muls (`Rep -> GQA -> Hybrid`) | **24L Speedup vs Rep / GQA** |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for T_len in (512, 2048, 4096, 16384):
        r = price_sliding_and_causal_attention(T_len)
        print(
            f"| {T_len:,} | `{r['slide_1L_exp_dense']/1e6:.2f}M -> {r['slide_1L_exp_win']/1e6:.2f}M` (**{r['slide_1L_exp_x']:.1f}x**) | "
            f"**{r['slide_1L_pe_x']:.1f}x** PE / `{r['slide_1L_sc_ee_dense_gqa']:,}->{r['slide_1L_sc_ee_win']:,}` SC | "
            f"**{r['slide_1L_tot_x']:.1f}x** | "
            f"`{r['exp_24L_dense']/1e9:.2f}B -> {r['exp_24L_hybrid']/1e9:.2f}B` (**{r['exp_24L_x']:.2f}x**) | "
            f"`{r['tot_bb_24L_rep']/1e9:.2f}B -> {r['tot_bb_24L_gqa']/1e9:.2f}B -> {r['tot_bb_24L_hybrid']/1e9:.2f}B` | "
            f"**{r['tot_24L_vs_rep_x']:.2f}x** / **{r['tot_24L_vs_gqa_x']:.2f}x** |"
        )

    # ---- Table 4: Subproblem 4 (Active-4 Sparse MoE + 24-Layer Uniform Folding) ----
    moe_rows, fold_rows = price_active4_moe_and_24layer_folding()
    print("\n## 4A. Active-4 Bucketed MoE (`NE=32, TOPK=4`) Across Sequence Length $T$ (`24` Layers)\n")
    print("| $T$ | Active Experts `/ 32` | Active `4T` vs Dyadic-Pad Rows (`Pad x`) | Pure Weight-SC Gain | `EinSumcheck` Only Gain (Jagged) | Total 24L MoE BB Muls (`Dense -> Dyadic -> Jagged`) | **Total MoE Gain (Dyadic / Jagged)** | Router Cell Share |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|")
    for r in moe_rows:
        print(
            f"| {r['T']:,} | `{r['active_experts_of_32']:.2f}` | `{r['active_rows_1L']:,} -> {r['dyadic_pad_rows_1L']:.1f}` (`{r['pad_factor']:.2f}x`) | "
            f"`{r['weight_sc_speedup']:.2f}x` | `{r['einsum_only_jagged_x']:.2f}x` | "
            f"`{r['tot_moe_dense_bb']/1e9:.2f}B -> {r['tot_moe_dyadic_bb']/1e9:.2f}B -> {r['tot_moe_jagged_bb']/1e9:.2f}B` | "
            f"**{r['tot_moe_dyadic_x']:.2f}x** / **{r['tot_moe_jagged_x']:.2f}x** | `{r['router_cell_share_pct']:.2f}%` |"
        )

    print("\n## 4B. 24-Layer (+ 32-Expert) Uniform `EinSumcheck` Folding Summary (`gpt-oss-20b`)\n")
    print("| Operator Family (`24` Layers) | Sumcheck Instances (`Unf -> Fold`) | Total Sumcheck Rounds (`Unf -> Fold`) | Round Reduction | PCS Openings (`Unf -> Fold`) | Sumcheck Transcript (`Unf -> Fold`) | Prover Mul Overhead (Zero-Layer Skip) |")
    print("|---|---:|---:|---:|---:|---:|---|")
    tot_u_inst = sum(x["unfolded_inst"] for x in fold_rows)
    tot_f_inst = sum(x["folded_inst"] for x in fold_rows)
    tot_u_rnd = sum(x["unfolded_rounds"] for x in fold_rows)
    tot_f_rnd = sum(x["folded_rounds"] for x in fold_rows)
    tot_u_op = sum(x["unfolded_openings"] for x in fold_rows)
    tot_f_op = sum(x["folded_openings"] for x in fold_rows)
    tot_u_kb = sum(x["transcript_kb_unf"] for x in fold_rows)
    tot_f_kb = sum(x["transcript_kb_fold"] for x in fold_rows)
    for x in fold_rows:
        print(
            f"| {x['operator']} | `{x['unfolded_inst']} -> {x['folded_inst']}` | "
            f"`{x['unfolded_rounds']:,} -> {x['folded_rounds']}` | **{x['round_reduction_x']:.1f}x** | "
            f"`{x['unfolded_openings']} -> {x['folded_openings']}` | "
            f"`{x['transcript_kb_unf']:.1f} KB -> {x['transcript_kb_fold']:.2f} KB` | {x['zero_skip_prover_overhead']} |"
        )
    print(
        f"| **TOTAL (Full 24-Layer Model)** | **`{tot_u_inst:,} -> {tot_f_inst}` ({tot_u_inst/tot_f_inst:.0f}x)** | "
        f"**`{tot_u_rnd:,} -> {tot_f_rnd}` ({tot_u_rnd/tot_f_rnd:.1f}x)** | **{tot_u_rnd/tot_f_rnd:.1f}x** | "
        f"**`{tot_u_op:,} -> {tot_f_op}` ({tot_u_op/tot_f_op:.0f}x)** | "
        f"**`{tot_u_kb:.1f} KB -> {tot_f_kb:.2f} KB` ({tot_u_kb/tot_f_kb:.0f}x)** | **0.0% (exact active-layer parity)** |"
    )


if __name__ == "__main__":
    run_all_verifications()
    print_markdown_report()
