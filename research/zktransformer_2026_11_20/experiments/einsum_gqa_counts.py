#!/usr/bin/env python3
"""
einsum_gqa_counts.py -- Exact BabyBear + Ext4 verification and prover operation-count
pricing for Grouped-Query Attention (GQA) EinSumcheck in `gpt-oss-20b` (`H=64, KV=8, rep=8, HD=64`).

Compares:
  1. Score contraction `Q . K^T`:
     - Repeated KV (`layer.py:213-215`): `kk = repeat(k, 8)` [t, 64, 64], `einsum("ihc,jhc->hij", q, kk)`
       (i, j in F_1; h in F_>=2 [6 vars]; c in S [6 vars] => 12 degree-3 sumcheck rounds)
     - Native GQA EinSumcheck: `einsum("igrc,jgc->grij", q, k)`
       (i, r in F_1 on Q; j in F_1 on K; g in F_>=2 [3 vars]; c in S [6 vars] => 9 degree-3 sumcheck rounds!)
  2. Value contraction `E . V`:
     - Repeated KV (`layer.py:214,224`): `vv = repeat(v, 8)` [t, 64, 64], `einsum("hij,jhc->ihc", e, vv)`
       (i in F_1 on E; c in F_1 on VV; h in F_>=2 [6 vars]; j in S [log2(t) vars] => 6+log2(t) rounds, size 64*t)
     - Native GQA EinSumcheck: `einsum("grij,jgc->igrc", e, v)`
       (i, r in F_1 on E; c in F_1 on V; g in F_>=2 [3 vars]; j in S [log2(t) vars] => 3+log2(t) rounds, size 8*t!)

Includes:
  - Genuine BabyBear (p = 2013265921) and quartic extension Ext4 = F_p[X]/(X^4 - 11) implementation
  - Algebraic check that X^4 - 11 is irreducible over BabyBear
  - End-to-end execution of EinSumcheck canonical prover & verifier on random BabyBear tensors (t = 32),
    checking exact equality of Z_mle(r_g, r_r, r_i, r_j) and O_mle(r_i, r_g, r_r, r_c),
    verifier acceptance, tampered-prover rejection (falsifier!), and 0-discrepancy match between
    instrumented runtime op counters and closed-form count formulas!
"""

import csv
import json
import math
import os
from typing import Tuple, List, Dict, Any
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))

P = (1 << 31) - (1 << 27) + 1  # BabyBear: 2013265921
W_BINOM = 11                   # Ext4 = F_p[X] / (X^4 - 11)

H, KV, REP, HD = 64, 8, 8, 64
LAYERS_GPTOSS = 24


# ---------------------------------------------------------------------------
# 1. BabyBear & Ext4 = F_p[X]/(X^4 - 11) Vectorized Arithmetic + Op Counter
# ---------------------------------------------------------------------------
def check_x4_minus_11_irreducible():
    """Over F_p, X^4 - 11 is irreducible iff 11 is not a quadratic residue (since 4 | p-1)
    Wait: p - 1 = 15 * 2^27, so 4 | p - 1! By Serret's theorem, X^4 - a is irreducible over F_p
    (when 4 | p - 1) iff a is NOT a square in F_p (and -4a is not a 4th power, automatic if a is non-square!).
    Let's verify both Euler's criterion AND that X^{(p^2-1)} mod (X^4 - 11) != 1 and gcd(X^{p^2}-X, X^4-11) == 1!"""
    leg = pow(W_BINOM, (P - 1) // 2, P)
    assert leg == P - 1, f"11 must be a quadratic non-residue mod P, got {leg}"
    # Also check X^(p^2) != X mod (X^4 - 11): in F_p[X]/(X^4 - 11), X^p = 11^((p-1)/4) * X,
    # so X^(p^2) = 11^((p-1)/4 * (p+1)) * X = (11^((p-1)/2))^((p+1)/2) * X = (-1)^((p+1)/2) * X.
    # Since 8 | p - 1, p + 1 == 2 mod 8, so (p + 1)/2 is ODD => (-1)^((p+1)/2) = -1 != 1!
    c_p = pow(W_BINOM, (P - 1) // 4, P)
    c_p2 = pow(c_p, P + 1, P)
    assert c_p2 == P - 1, f"Expected X^(p^2) = -X, got {c_p2}*X"
    return True


class OpCounter:
    def __init__(self):
        self.ext_base_muls = 0  # Ext4 * F_p (4 base muls each)
        self.ext_ext_muls = 0   # Ext4 * Ext4 (9 Karatsuba / 16 schoolbook base muls each)

    def reset(self):
        self.ext_base_muls = 0
        self.ext_ext_muls = 0


def ext_add(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (a + b) % P


def ext_sub(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (a - b) % P


def ext_mul_base(e: np.ndarray, s: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """Multiply Ext4 array `e` (..., 4) by base-field array `s` (...)."""
    if ctr is not None:
        ctr.ext_base_muls += math.prod(np.broadcast_shapes(e.shape[:-1], s.shape))
    return (e * s[..., None]) % P


def ext_mul(a: np.ndarray, b: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """Multiply two Ext4 arrays (..., 4) modulo X^4 - 11."""
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


def ext_from_int(v: int) -> np.ndarray:
    return np.array([v % P, 0, 0, 0], dtype=np.int64)


def ext_one() -> np.ndarray:
    return ext_from_int(1)


def ext_zero() -> np.ndarray:
    return ext_from_int(0)


# ---------------------------------------------------------------------------
# 2. Multilinear & EinSumcheck Canonical Prover + Verifier (LSB-first per axis)
# ---------------------------------------------------------------------------
def build_eq_table(r: np.ndarray, ctr: OpCounter = None) -> np.ndarray:
    """
    Given challenge vector `r` of shape (k, 4) in Ext4, build the Lagrange basis table
    `eq(r, x)` of shape (2^k, 4) in exact `2^k - 1` Ext4 multiplications (VSBW13):
      step 0 (1 var): [1 - r_0, r_0] -> 0 muls!
      step i (i >= 1): right = prev * r_i (2^i muls), left = prev - right (0 muls).
      Total Ext4 muls = 2 + 4 + ... + 2^(k-1) = 2^k - 2 (for k >= 1)!
      Wait: let's check! Step 0 needs 0 muls (`1 - r_0` and `r_0`)!
      Steps i = 1 .. k-1 do `2^i` muls each => sum_{i=1}^{k-1} 2^i = 2^k - 2 Ext4 muls!
    """
    k = r.shape[0]
    if k == 0:
        return ext_one()[None, :]
    one = ext_one()
    tbl = np.stack([ext_sub(one, r[0]), r[0]], axis=0)  # shape (2, 4), 0 muls!
    for i in range(1, k):
        hi = ext_mul(tbl, r[i], ctr)                    # 2^i Ext4 muls
        lo = ext_sub(tbl, hi)                           # (1 - r_i) * tbl = tbl - r_i * tbl, 0 muls!
        tbl = np.concatenate([lo, hi], axis=0)          # bit i has stride 2^i (LSB-first)
    return tbl


def eval_eq_point(r: np.ndarray, z: np.ndarray) -> np.ndarray:
    """Verifier O(k) evaluation of eq(r, z) = prod_i (r_i z_i + (1 - r_i)(1 - z_i))."""
    one = ext_one()
    acc = one.copy()
    for i in range(r.shape[0]):
        # r_i * z_i + (1 - r_i)*(1 - z_i) = 1 - r_i - z_i + 2 * r_i * z_i
        rz = ext_mul(r[i], z[i])
        term = ext_add(ext_sub(ext_sub(one, r[i]), z[i]), ext_add(rz, rz))
        acc = ext_mul(acc, term)
    return acc


def mle_eval_base_tensor(tensor_flat: np.ndarray, point: np.ndarray) -> np.ndarray:
    """Direct reference MLE evaluation of a base-field flat array (length 2^v) at `point` (v, 4)."""
    eq = build_eq_table(point)
    # sum_b eq[b] * tensor_flat[b]
    return (eq * tensor_flat[:, None] % P).sum(axis=0) % P


def mle_eval_ext_tensor(tensor_ext: np.ndarray, point: np.ndarray) -> np.ndarray:
    """Direct reference MLE evaluation of an Ext4 flat array (2^v, 4) at `point` (v, 4)."""
    eq = build_eq_table(point)
    return ext_mul(eq, tensor_ext).sum(axis=0) % P


def partial_eval_f1_base(
    base_matrix: np.ndarray,
    r_f1: np.ndarray,
    ctr: OpCounter,
) -> np.ndarray:
    """
    Partially evaluate a base-field tensor reshaped as `(2^f1_vars, 2^rem_vars)` on its
    degree-1 free indices `r_f1` (`f1_vars` challenges in Ext4):
      1. Build `eq_f1 = build_eq_table(r_f1)`: `2^f1_vars - 2` Ext4*Ext4 muls (for f1_vars >= 1)
      2. Compute `out[col] = sum_{row} eq_f1[row] * base_matrix[row, col]`:
         `2^f1_vars * 2^rem_vars` (= full tensor size!) Ext4 * Base muls!
    Returns Ext4 array of shape `(2^rem_vars, 4)`.
    """
    eq_f1 = build_eq_table(r_f1, ctr)  # (F1_len, 4)
    f1_len, rem_len = base_matrix.shape
    ctr.ext_base_muls += f1_len * rem_len
    # Exact modular inner product over int64 in chunks so numpy int64 never overflows (< 2^62):
    # P < 2^31, so P * P < 2^62; chunk size 1 on sum of P*P would overflow if > 2 terms!
    # Wait: eq_f1 < 2^31 and base_matrix < 2^31, so product < 2^62! Adding > 2 products in int64 overflows 2^63-1!
    # Reduce mod P every pair or use Python object / limb split!
    out = np.zeros((rem_len, 4), dtype=np.int64)
    for row in range(f1_len):
        out = (out + eq_f1[row][None, :] * base_matrix[row, :, None]) % P
    return out


def partial_eval_f1_ext(
    ext_matrix: np.ndarray,
    r_f1: np.ndarray,
    ctr: OpCounter,
) -> np.ndarray:
    """Partially evaluate an Ext4 tensor `(2^f1_vars, 2^rem_vars, 4)` (or base if softmax E is in base!).
    Note: in `gptoss-int v0` (`layer.py:224`), `e` (`E[g, r, i, j]`) IS AN INTEGER / BASE-FIELD TENSOR!
    So BOTH Q, K AND E, V are base-field tensors! This helper is only if an input were in Ext4."""
    eq_f1 = build_eq_table(r_f1, ctr)
    f1_len, rem_len, _ = ext_matrix.shape
    out = np.zeros((rem_len, 4), dtype=np.int64)
    for row in range(f1_len):
        out = ext_add(out, ext_mul(eq_f1[row][None, :], ext_matrix[row], ctr))
    return out


def run_canonical_einsumcheck_prover(
    r_f2: np.ndarray,          # shape (ell, 4): challenges for F_>=2 (shared free indices)
    T1_rem: np.ndarray,        # shape (2^ell, 2^mu_s, 4): operand 1 after F_1 partial eval, axes (F_>=2, S)
    T2_rem: np.ndarray,        # shape (2^ell, 2^mu_s, 4): operand 2 after F_1 partial eval, axes (F_>=2, S)
    challenges: np.ndarray,    # shape (ell + mu_s, 4): verifier sumcheck challenges
    ctr: OpCounter,
) -> Tuple[List[Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]], np.ndarray, np.ndarray]:
    """
    Canonical linear-time EinSumcheck prover (zkTransformer App. F Eq. 10, optimized factored-eq):
      H = sum_{x in {0,1}^ell, y in {0,1}^mu_s} eq(r_f2, x) * T1(x, y) * T2(x, y)

    Eliminates `x` (the `ell` shared-free variables in F_>=2) FIRST, then `y` (the `mu_s` summation variables in S)!
    Look at why eliminating `x` first is doubly clean:
      1. During the first `ell` rounds (eliminating `x_0 .. x_{ell-1}`), `eq` has ONLY `2^{ell - r}` entries
         (does NOT depend on `y`!), so at each `x_rest` we FIRST sum `T1 * T2` over `y` (at t in {0, 1, 2, inf}:
         actually quadratic in t before multiplying by eq(t)! Even simpler: `S(t, x_rest) = sum_y T1(t, x_rest, y) * T2(t, x_rest, y)`
         has degree 2 in `t`, taking ONLY 3 muls per `(x_rest, y)` pair [t=0, t=1, t=inf, then t=2 by linear comb of 0,1,inf!],
         and multiplying `eq(t, x_rest) * S(t, x_rest)` at t in {0, 1, 2, inf} takes ONLY `4 * 2^{ell - 1 - r}` muls!!).
         WAIT A SECOND! Check that algebraic identity:
           For quadratic Q(t) = q_0 + q_1 t + q_2 t^2:
             Q(0) = A_0 * B_0 (1 mul), Q(1) = A_1 * B_1 (1 mul), q_2 = Q(inf) = dA * dB (1 mul),
             and Q(2) = 2*Q(1) - Q(0) + 2*q_2 (ZERO muls!! Because q_0 + 2 q_1 + 4 q_2 = 2(q_0+q_1+q_2) - q_0 + 2 q_2!!)!
           Check: 2(q_0 + q_1 + q_2) - q_0 + 2 q_2 = q_0 + 2 q_1 + 4 q_2 == Q(2)!! IDENTICAL!!
           So per `(x_rest, y)` pair in the first `ell` rounds, computing `S` takes ONLY **3** F_ext muls (not 8!),
           plus folding T1 and T2 takes **2** F_ext muls => **5 F_ext muls per (x_rest, y) pair**, plus **5 F_ext muls per x_rest** for `eq`!
      2. After the `ell` rounds on `x`, `eq(r_f2, x)` is completely bound to a SINGLE scalar `eq_scalar = eq(r_f2, ch_x)`!
         In the remaining `mu_s` rounds (eliminating `y_0 .. y_{mu_s-1}`), the summand is `eq_scalar * T1(ch_x, y) * T2(ch_x, y)`,
         which has DEGREE 2 in `y_r` (cubic message has c_3 = 0):
           Q(0), Q(1), q_2 = dA*dB take 3 muls per `y_rest` pair + 2 muls to fold T1, T2 = **5 F_ext muls per pair**,
           plus 3 muls ONCE per round to multiply `(Q(0), Q(1), Q(2))` by `eq_scalar`!
    Returns `(round_msgs, final_T1_eval, final_T2_eval)` where each round_msg is `(p(0), p(1), p(2), p_lead_c3)`.
    """
    ell = r_f2.shape[0]
    S_len = T1_rem.shape[1]
    mu_s = int(round(math.log2(S_len)))
    assert T1_rem.shape == (1 << ell, S_len, 4)
    assert T2_rem.shape == (1 << ell, S_len, 4)

    eq_arr = build_eq_table(r_f2, ctr)  # (2^ell, 4): 2^ell - 2 muls
    A = T1_rem.copy()
    B = T2_rem.copy()

    round_msgs = []

    # Phase 1: `ell` rounds over shared free variables x (LSB-first)
    for r in range(ell):
        ch = challenges[r]
        half_x = 1 << (ell - 1 - r)
        # Split LSB of x: x = 2 * x_rest + bit => indices 0::2 (bit=0) and 1::2 (bit=1)
        A0, A1 = A[0::2], A[1::2]        # (half_x, S_len, 4)
        B0, B1 = B[0::2], B[1::2]
        dA = ext_sub(A1, A0)
        dB = ext_sub(B1, B0)

        # 3 muls per (x_rest, y) pair:
        Q0 = ext_mul(A0, B0, ctr).sum(axis=1) % P     # (half_x, 4)
        Q1 = ext_mul(A1, B1, ctr).sum(axis=1) % P     # (half_x, 4)
        q2 = ext_mul(dA, dB, ctr).sum(axis=1) % P     # (half_x, 4)
        # Q(2) = 2*Q(1) - Q(0) + 2*q2 (0 muls!)
        two_Q1 = ext_add(Q1, Q1)
        two_q2 = ext_add(q2, q2)
        Q2 = ext_add(ext_sub(two_Q1, Q0), two_q2)

        eq0, eq1 = eq_arr[0::2], eq_arr[1::2]         # (half_x, 4)
        deq = ext_sub(eq1, eq0)
        eq2 = ext_sub(ext_add(eq1, eq1), eq0)         # 2*eq1 - eq0 (0 muls)

        # 4 muls per x_rest:
        p0 = ext_mul(eq0, Q0, ctr).sum(axis=0) % P
        p1 = ext_mul(eq1, Q1, ctr).sum(axis=0) % P
        p2 = ext_mul(eq2, Q2, ctr).sum(axis=0) % P
        c3 = ext_mul(deq, q2, ctr).sum(axis=0) % P    # leading cubic coeff!
        round_msgs.append((p0, p1, p2, c3))

        # Fold A, B (2 * half_x * S_len muls) and eq_arr (half_x muls):
        A = ext_add(A0, ext_mul(dA, ch, ctr))
        B = ext_add(B0, ext_mul(dB, ch, ctr))
        eq_arr = ext_add(eq0, ext_mul(deq, ch, ctr))

    eq_scalar = eq_arr[0]  # shape (4,)
    A_y = A[0]             # shape (S_len, 4)
    B_y = B[0]             # shape (S_len, 4)

    # Phase 2: `mu_s` rounds over summation variables y (LSB-first)
    for r in range(mu_s):
        ch = challenges[ell + r]
        A0, A1 = A_y[0::2], A_y[1::2]
        B0, B1 = B_y[0::2], B_y[1::2]
        dA = ext_sub(A1, A0)
        dB = ext_sub(B1, B0)

        Q0 = ext_mul(A0, B0, ctr).sum(axis=0) % P
        Q1 = ext_mul(A1, B1, ctr).sum(axis=0) % P
        q2 = ext_mul(dA, dB, ctr).sum(axis=0) % P
        Q2 = ext_add(ext_sub(ext_add(Q1, Q1), Q0), ext_add(q2, q2))

        p0 = ext_mul(eq_scalar, Q0, ctr)
        p1 = ext_mul(eq_scalar, Q1, ctr)
        p2 = ext_mul(eq_scalar, Q2, ctr)
        c3 = ext_zero()
        round_msgs.append((p0, p1, p2, c3))

        A_y = ext_add(A0, ext_mul(dA, ch, ctr))
        B_y = ext_add(B0, ext_mul(dB, ch, ctr))

    return round_msgs, A_y[0], B_y[0]


def verify_einsumcheck(
    claimed_H: np.ndarray,
    r_f2: np.ndarray,
    round_msgs: List[Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]],
    challenges: np.ndarray,
    final_T1_eval: np.ndarray,
    final_T2_eval: np.ndarray,
) -> bool:
    """
    Verifier reconstructs cubic p(t) = c0 + c1*t + c2*t^2 + c3*t^3 from (p0, p1, p2, c3):
      c0 = p0
      p1 - p0 = c1 + c2 + c3
      p2 - 2*p1 + p0 = 2*c2 + 6*c3  =>  c2 = (p2 - 2*p1 + p0 - 6*c3) * 2^{-1}
      c1 = (p1 - p0) - c2 - c3
    Checks p(0) + p(1) == running_sum in every round, updates running_sum = p(ch_r),
    and at the end checks running_sum == eq(r_f2, ch_f2) * final_T1_eval * final_T2_eval!
    """
    inv2 = pow(2, P - 2, P)
    running = claimed_H.copy()
    for r, (p0, p1, p2, c3) in enumerate(round_msgs):
        if not np.array_equal(ext_add(p0, p1), running):
            return False
        c0 = p0
        six_c3 = (6 * c3) % P
        two_c2 = ext_sub(ext_add(ext_sub(p2, ext_add(p1, p1)), p0), six_c3)
        c2 = (two_c2 * inv2) % P
        c1 = ext_sub(ext_sub(ext_sub(p1, p0), c2), c3)

        t = challenges[r]
        t2 = ext_mul(t, t)
        t3 = ext_mul(t2, t)
        running = ext_add(
            ext_add(c0, ext_mul(c1, t)),
            ext_add(ext_mul(c2, t2), ext_mul(c3, t3)),
        )

    ell = r_f2.shape[0]
    eq_eval = eval_eq_point(r_f2, challenges[:ell])
    expected = ext_mul(eq_eval, ext_mul(final_T1_eval, final_T2_eval))
    return np.array_equal(running, expected)


# ---------------------------------------------------------------------------
# 3. Closed-Form Exact Operation Count Formulas
# ---------------------------------------------------------------------------
def closed_form_counts_einsum(
    f1_vars_1: int,
    f1_vars_2: int,
    ell_f2: int,
    mu_s: int,
) -> Dict[str, int]:
    """
    Exact closed-form counts matching `partial_eval_f1_base` + `run_canonical_einsumcheck_prover` TO THE UNIT:
      1. Partial eval operand 1 (shape 2^f1_1 x 2^(ell + mu_s)):
         - eq table: (2^f1_1 - 2) if f1_1 >= 1 else 0 Ext4 muls
         - matrix inner product: 2^(f1_1 + ell + mu_s) Ext x Base muls
      2. Partial eval operand 2 (shape 2^f1_2 x 2^(ell + mu_s)):
         - eq table: (2^f1_2 - 2) if f1_2 >= 1 else 0 Ext4 muls
         - matrix inner product: 2^(f1_2 + ell + mu_s) Ext x Base muls
      3. Sumcheck over ell_f2 + mu_s rounds:
         - eq_f2 build: (2^ell - 2) if ell >= 1 else 0 Ext4 muls
         - Phase 1 (`ell` rounds, half_x = 2^{ell-1}, ..., 1 => sum half_x = 2^ell - 1):
             per round: 5 * half_x * 2^mu_s (Q0,Q1,q2 + fold A,B) + 5 * half_x (p0,p1,p2,c3 + fold eq)
             total Phase 1 = (2^ell - 1) * (5 * 2^mu_s + 5) Ext4 muls
         - Phase 2 (`mu_s` rounds, half_y = 2^{mu_s-1}, ..., 1 => sum half_y = 2^mu_s - 1):
             per round: 5 * half_y (Q0,Q1,q2 + fold A_y,B_y) + 3 (p0,p1,p2 * eq_scalar)
             total Phase 2 = 5 * (2^mu_s - 1) + 3 * mu_s Ext4 muls
    """
    rem = 1 << (ell_f2 + mu_s)
    eq1 = ((1 << f1_vars_1) - 2) if f1_vars_1 >= 1 else 0
    eq2 = ((1 << f1_vars_2) - 2) if f1_vars_2 >= 1 else 0
    ext_base_1 = (1 << f1_vars_1) * rem
    ext_base_2 = (1 << f1_vars_2) * rem

    eq_f2 = ((1 << ell_f2) - 2) if ell_f2 >= 1 else 0
    ph1 = ((1 << ell_f2) - 1) * (5 * (1 << mu_s) + 5)
    ph2 = 5 * ((1 << mu_s) - 1) + 3 * mu_s

    pe_ext_ext = eq1 + eq2
    sc_ext_ext = eq_f2 + ph1 + ph2
    tot_ext_base = ext_base_1 + ext_base_2
    tot_ext_ext = pe_ext_ext + sc_ext_ext

    return {
        "sumcheck_rounds": ell_f2 + mu_s,
        "transcript_ext4_elems": 4 * ell_f2 + 3 * mu_s + 2,  # 4 elems in cubic rounds, 3 in quadratic rounds + 2 terminal claims
        "pe_ext_base_muls": tot_ext_base,
        "pe_ext_ext_muls": pe_ext_ext,
        "sc_ext_ext_muls": sc_ext_ext,
        "total_ext_base_muls": tot_ext_base,
        "total_ext_ext_muls": tot_ext_ext,
        "total_base_mul_equiv_kar": tot_ext_base * 4 + tot_ext_ext * 9,
        "total_base_mul_equiv_sb": tot_ext_base * 4 + tot_ext_ext * 16,
    }


def zktransformer_unoptimized_sumcheck_counts(
    f1_vars_1: int,
    f1_vars_2: int,
    ell_f2: int,
    mu_s: int,
) -> Dict[str, int]:
    """
    For comparison, also price zkTransformer's `Einsum::prove` as implemented in `src/basicblock/einsum.rs`
    (which broadcasts `eq` across all `2^mu_s` summation entries and runs `LinearSumcheckProver` over {0,1,2,3}
    for all `ell + mu_s` rounds at 19 Ext4 muls per pair!).
    """
    rem = 1 << (ell_f2 + mu_s)
    ext_base = ((1 << f1_vars_1) + (1 << f1_vars_2)) * rem
    eq_muls = (((1 << f1_vars_1) - 2) if f1_vars_1 >= 1 else 0) + \
              (((1 << f1_vars_2) - 2) if f1_vars_2 >= 1 else 0) + \
              (((1 << ell_f2) - 2) if ell_f2 >= 1 else 0)
    sc_muls = 19 * (rem - 1)
    tot_ext_ext = eq_muls + sc_muls
    return {
        "sc_ext_ext_muls_zkt_linear_prover": sc_muls,
        "total_base_mul_equiv_kar_zkt_linear_prover": ext_base * 4 + tot_ext_ext * 9,
    }


# ---------------------------------------------------------------------------
# 4. End-to-End Numerical Verification over BabyBear (t = 32)
# ---------------------------------------------------------------------------
def verify_on_random_babybear_tensors(t: int = 32) -> Dict[str, Any]:
    rng = np.random.default_rng(20261120)
    log_t = int(round(math.log2(t)))

    # Random Q [t, 8, 8, 64], K [t, 8, 64], V [t, 8, 64], E [8, 8, t, t] over BabyBear
    Q = rng.integers(0, P, size=(t, KV, REP, HD), dtype=np.int64)
    K = rng.integers(0, P, size=(t, KV, HD), dtype=np.int64)
    V = rng.integers(0, P, size=(t, KV, HD), dtype=np.int64)
    E = rng.integers(0, P, size=(KV, REP, t, t), dtype=np.int64)

    # Repeated tensors (matching layer.py:213-214): h = 8*g + r => in LSB-first bit order of h = (r_bits, g_bits)
    # Wait: let's be SUPER CAREFUL about bit ordering of `h = 8 * g + r`!
    # In `np.repeat(K, 8, axis=1)`, index `h = 8 * g + r` has `r` in the LOW 3 bits (`r = h & 7`)
    # and `g` in the HIGH 3 bits (`g = h >> 3`)!
    # And in numpy C-order flattening of `(g, r)` (shape `(8, 8)`), `g * 8 + r` ALSO puts `r` in the
    # LOW 3 bits (`stride 1`) and `g` in the HIGH 3 bits (`stride 8`)!!
    # Let's verify that `KK.reshape(t, 64, 64)` and `Q.reshape(t, 64, 64)` match bit-for-bit!
    Q_rep = Q.reshape(t, H, HD)
    KK = np.repeat(K, REP, axis=1)  # KK[j, 8*g + r, c] == K[j, g, c]
    VV = np.repeat(V, REP, axis=1)
    E_rep = E.reshape(H, t, t)

    # Exact contractions mod P (computed in 2 chunks of 32 or loop so int64 never overflows 2^63-1):
    Z_gqa = np.zeros((KV, REP, t, t), dtype=np.int64)
    for c_idx in range(HD):
        Z_gqa = (Z_gqa + Q[:, :, :, c_idx].transpose(1, 2, 0)[:, :, :, None] * K[:, :, c_idx].transpose(1, 0)[:, None, None, :]) % P
    Z_rep = np.zeros((H, t, t), dtype=np.int64)
    for c_idx in range(HD):
        Z_rep = (Z_rep + Q_rep[:, :, c_idx].transpose(1, 0)[:, :, None] * KK[:, :, c_idx].transpose(1, 0)[:, None, :]) % P
    assert np.array_equal(Z_gqa.reshape(H, t, t), Z_rep), "Integer contraction mismatch!"

    O_gqa = np.zeros((t, KV, REP, HD), dtype=np.int64)
    for j_idx in range(t):
        O_gqa = (O_gqa + E[:, :, :, j_idx].transpose(2, 0, 1)[:, :, :, None] * V[j_idx, :, None, :]) % P
    O_rep = np.zeros((t, H, HD), dtype=np.int64)
    for j_idx in range(t):
        O_rep = (O_rep + E_rep[:, :, j_idx].transpose(1, 0)[:, :, None] * VV[j_idx, :, :]) % P
    assert np.array_equal(O_gqa.reshape(t, H, HD), O_rep), "Value contraction mismatch!"

    # Sample verifier challenges in Ext4:
    # Note LSB-first bit convention: when flattening C-order `(A, B)` of sizes `(2^a, 2^b)`,
    # flat index is `idx = idx_A * 2^b + idx_B`, so `B` occupies the LOW `b` bits `[0..b)`
    # and `A` occupies the HIGH `a` bits `[b..b+a)`!
    r_g = rng.integers(0, P, size=(3, 4), dtype=np.int64)      # 3 bits for g in [0, 8)
    r_r = rng.integers(0, P, size=(3, 4), dtype=np.int64)      # 3 bits for r in [0, 8)
    r_i = rng.integers(0, P, size=(log_t, 4), dtype=np.int64)  # log_t bits for i
    r_j = rng.integers(0, P, size=(log_t, 4), dtype=np.int64)  # log_t bits for j
    r_c = rng.integers(0, P, size=(6, 4), dtype=np.int64)      # 6 bits for c in [0, 64)

    # ---- Test 1: Score Contraction Z[g, r, i, j] ----
    # C-order flat index of Z[g, r, i, j] has LSB->MSB variable order: (r_j, r_i, r_r, r_g)!
    pt_Z = np.concatenate([r_j, r_i, r_r, r_g], axis=0)
    Z_eval_direct = mle_eval_base_tensor(Z_gqa.reshape(-1), pt_Z)
    # Note h = 8*g + r => LSB->MSB bits of h are (r_r, r_g), so Z_rep[h, i, j] has exact same flat order!
    Z_rep_eval_direct = mle_eval_base_tensor(Z_rep.reshape(-1), pt_Z)
    assert np.array_equal(Z_eval_direct, Z_rep_eval_direct)

    # 1a. Run UN-REPEATED GQA EinSumcheck ("igrc,jgc->grij", 9 rounds):
    # Reorder Q[i, g, r, c] -> rows=(i, r) [LSB: r_r then r_i], cols=(g, c) [LSB: c then g -> Wait:
    # run_canonical_einsumcheck_prover expects axis 0 = F_>=2 (g, LSB-first) and axis 1 = S (c, LSB-first)!]
    ctr_qk_gqa = OpCounter()
    Q_ir_gc = Q.transpose(0, 2, 1, 3).reshape(t * REP, KV * HD)  # row = i*8 + r => LSB: (r_r, r_i)
    r_ir = np.concatenate([r_r, r_i], axis=0)
    Q_pe = partial_eval_f1_base(Q_ir_gc, r_ir, ctr_qk_gqa).reshape(KV, HD, 4)

    K_j_gc = K.reshape(t, KV * HD)                               # row = j => LSB: r_j
    K_pe = partial_eval_f1_base(K_j_gc, r_j, ctr_qk_gqa).reshape(KV, HD, 4)

    ch_qk_9 = rng.integers(0, P, size=(9, 4), dtype=np.int64)
    msgs_qk_gqa, q_fin_gqa, k_fin_gqa = run_canonical_einsumcheck_prover(r_g, Q_pe, K_pe, ch_qk_9, ctr_qk_gqa)
    ok_qk_gqa = verify_einsumcheck(Z_eval_direct, r_g, msgs_qk_gqa, ch_qk_9, q_fin_gqa, k_fin_gqa)
    assert ok_qk_gqa, "GQA 9-round EinSumcheck failed verification!"

    # Falsifier check: tamper claimed Z_eval_direct by +1 and confirm verifier REJECTS!
    bad_Z = ext_add(Z_eval_direct, ext_one())
    assert not verify_einsumcheck(bad_Z, r_g, msgs_qk_gqa, ch_qk_9, q_fin_gqa, k_fin_gqa), "Falsifier accepted!"

    #Also check terminal claims q_fin_gqa, k_fin_gqa match true MLE evaluations of Q and K!
    # Q[i, g, r, c] C-order flat has LSB->MSB: (ch_c, r_r, ch_g, r_i)
    q_true_term = mle_eval_base_tensor(Q.reshape(-1), np.concatenate([ch_qk_9[3:], r_r, ch_qk_9[:3], r_i], axis=0))
    k_true_term = mle_eval_base_tensor(K.reshape(-1), np.concatenate([ch_qk_9[3:], ch_qk_9[:3], r_j], axis=0))
    assert np.array_equal(q_fin_gqa, q_true_term), "Terminal Q MLE mismatch!"
    assert np.array_equal(k_fin_gqa, k_true_term), "Terminal K MLE mismatch!"

    # Verify exact 0-discrepancy with closed-form op counter!
    cf_qk_gqa = closed_form_counts_einsum(log_t + 3, log_t, 3, 6)
    assert ctr_qk_gqa.ext_base_muls == cf_qk_gqa["total_ext_base_muls"], (ctr_qk_gqa.ext_base_muls, cf_qk_gqa)
    assert ctr_qk_gqa.ext_ext_muls == cf_qk_gqa["total_ext_ext_muls"], (ctr_qk_gqa.ext_ext_muls, cf_qk_gqa)

    # 1b. Run REPEATED KV EinSumcheck ("ihc,jhc->hij", 12 rounds):
    ctr_qk_rep = OpCounter()
    r_h = np.concatenate([r_r, r_g], axis=0)  # 6 vars for h = 8*g + r
    Q_pe_rep = partial_eval_f1_base(Q_rep.reshape(t, H * HD), r_i, ctr_qk_rep).reshape(H, HD, 4)
    KK_pe_rep = partial_eval_f1_base(KK.reshape(t, H * HD), r_j, ctr_qk_rep).reshape(H, HD, 4)
    ch_qk_12 = rng.integers(0, P, size=(12, 4), dtype=np.int64)
    msgs_qk_rep, q_fin_rep, kk_fin_rep = run_canonical_einsumcheck_prover(r_h, Q_pe_rep, KK_pe_rep, ch_qk_12, ctr_qk_rep)
    ok_qk_rep = verify_einsumcheck(Z_rep_eval_direct, r_h, msgs_qk_rep, ch_qk_12, q_fin_rep, kk_fin_rep)
    assert ok_qk_rep, "Repeated 12-round EinSumcheck failed verification!"
    cf_qk_rep = closed_form_counts_einsum(log_t, log_t, 6, 6)
    assert ctr_qk_rep.ext_base_muls == cf_qk_rep["total_ext_base_muls"]
    assert ctr_qk_rep.ext_ext_muls == cf_qk_rep["total_ext_ext_muls"]

    # ---- Test 2: Value Contraction O[i, g, r, c] = sum_j E[g, r, i, j] * V[j, g, c] ----
    pt_O = np.concatenate([r_c, r_r, r_g, r_i], axis=0)
    O_eval_direct = mle_eval_base_tensor(O_gqa.reshape(-1), pt_O)
    O_rep_eval_direct = mle_eval_base_tensor(O_rep.reshape(-1), pt_O)
    assert np.array_equal(O_eval_direct, O_rep_eval_direct)

    # 2a. Un-repeated ("grij,jgc->igrc", 3 + log_t rounds):
    ctr_ev_gqa = OpCounter()
    # E[g, r, i, j] -> rows=(i, r) [LSB: r_r, r_i], cols=(g, j)
    E_ir_gj = E.transpose(2, 1, 0, 3).reshape(t * REP, KV * t)
    E_pe = partial_eval_f1_base(E_ir_gj, r_ir, ctr_ev_gqa).reshape(KV, t, 4)
    # V[j, g, c] -> rows=(c), cols=(g, j)
    V_c_gj = V.transpose(2, 1, 0).reshape(HD, KV * t)
    V_pe = partial_eval_f1_base(V_c_gj, r_c, ctr_ev_gqa).reshape(KV, t, 4)

    ch_ev_gqa = rng.integers(0, P, size=(3 + log_t, 4), dtype=np.int64)
    msgs_ev_gqa, e_fin_gqa, v_fin_gqa = run_canonical_einsumcheck_prover(r_g, E_pe, V_pe, ch_ev_gqa, ctr_ev_gqa)
    assert verify_einsumcheck(O_eval_direct, r_g, msgs_ev_gqa, ch_ev_gqa, e_fin_gqa, v_fin_gqa)
    cf_ev_gqa = closed_form_counts_einsum(log_t + 3, 6, 3, log_t)
    assert ctr_ev_gqa.ext_base_muls == cf_ev_gqa["total_ext_base_muls"]
    assert ctr_ev_gqa.ext_ext_muls == cf_ev_gqa["total_ext_ext_muls"]

    # 2b. Repeated ("hij,jhc->ihc", 6 + log_t rounds):
    ctr_ev_rep = OpCounter()
    E_rep_i_hj = E_rep.transpose(1, 0, 2).reshape(t, H * t)
    E_pe_rep = partial_eval_f1_base(E_rep_i_hj, r_i, ctr_ev_rep).reshape(H, t, 4)
    VV_c_hj = VV.transpose(2, 1, 0).reshape(HD, H * t)
    VV_pe_rep = partial_eval_f1_base(VV_c_hj, r_c, ctr_ev_rep).reshape(H, t, 4)

    ch_ev_rep = rng.integers(0, P, size=(6 + log_t, 4), dtype=np.int64)
    msgs_ev_rep, e_fin_rep, vv_fin_rep = run_canonical_einsumcheck_prover(r_h, E_pe_rep, VV_pe_rep, ch_ev_rep, ctr_ev_rep)
    assert verify_einsumcheck(O_rep_eval_direct, r_h, msgs_ev_rep, ch_ev_rep, e_fin_rep, vv_fin_rep)
    cf_ev_rep = closed_form_counts_einsum(log_t, 6, 6, log_t)
    assert ctr_ev_rep.ext_base_muls == cf_ev_rep["total_ext_base_muls"]
    assert ctr_ev_rep.ext_ext_muls == cf_ev_rep["total_ext_ext_muls"]

    return {
        "t": t,
        "x4_minus_11_irreducible": True,
        "Z_mle_eval_ext4": Z_eval_direct.tolist(),
        "O_mle_eval_ext4": O_eval_direct.tolist(),
        "qk_gqa_9round_verified": True,
        "qk_rep_12round_verified": True,
        "ev_gqa_verified": True,
        "ev_rep_verified": True,
        "falsifier_rejected": True,
        "terminal_claims_verified": True,
        "instrumented_equals_closed_form": True,
    }


def main():
    check_x4_minus_11_irreducible()
    verif = verify_on_random_babybear_tensors(t=32)

    ts = [32, 128, 512, 2048, 4096]
    table_rows: List[Dict[str, Any]] = []

    for t in ts:
        lt = int(round(math.log2(t)))

        # Q.K^T: repeated ("ihc,jhc->hij") vs un-repeated ("igrc,jgc->grij")
        qk_rep = closed_form_counts_einsum(lt, lt, 6, 6)
        qk_gqa = closed_form_counts_einsum(lt + 3, lt, 3, 6)
        qk_rep_zkt = zktransformer_unoptimized_sumcheck_counts(lt, lt, 6, 6)
        qk_gqa_zkt = zktransformer_unoptimized_sumcheck_counts(lt + 3, lt, 3, 6)

        # E.V: repeated ("hij,jhc->ihc") vs un-repeated ("grij,jgc->igrc")
        ev_rep = closed_form_counts_einsum(lt, 6, 6, lt)
        ev_gqa = closed_form_counts_einsum(lt + 3, 6, 3, lt)

        # Committed KV cells per layer and across 24 layers:
        # Repeated materializes kk [t, 64, 64] + vv [t, 64, 64] = 8192 * t cells/layer
        # Un-repeated keeps only k [t, 8, 64] + v [t, 8, 64] = 1024 * t cells/layer
        kv_cells_rep_1L = 2 * H * HD * t
        kv_cells_gqa_1L = 2 * KV * HD * t
        kv_cells_saved_1L = kv_cells_rep_1L - kv_cells_gqa_1L
        kv_cells_saved_24L = LAYERS_GPTOSS * kv_cells_saved_1L

        # PCS commitment savings on those saved KV cells (WHIR rho=1/4, blake2s, from exp_pricing):
        blow = 4.0
        log_kv = max(1, int(math.ceil(math.log2(kv_cells_rep_1L))))
        whir_muls_per_cell = (blow + 1.0) * log_kv / 2.0 + 2.0
        pcs_muls_saved_1L = round(kv_cells_saved_1L * whir_muls_saved_factor(log_kv))

        both_rep_kar = qk_rep["total_base_mul_equiv_kar"] + ev_rep["total_base_mul_equiv_kar"]
        both_gqa_kar = qk_gqa["total_base_mul_equiv_kar"] + ev_gqa["total_base_mul_equiv_kar"]

        table_rows.append({
            "t": t,
            "log2_t": lt,
            # QK counts
            "qk_rep_rounds": qk_rep["sumcheck_rounds"],
            "qk_gqa_rounds": qk_gqa["sumcheck_rounds"],
            "qk_rep_pe_ext_base_muls": qk_rep["pe_ext_base_muls"],
            "qk_gqa_pe_ext_base_muls": qk_gqa["pe_ext_base_muls"],
            "qk_rep_sc_ext_ext_muls": qk_rep["sc_ext_ext_muls"],
            "qk_gqa_sc_ext_ext_muls": qk_gqa["sc_ext_ext_muls"],
            "qk_sc_speedup": round(qk_rep["sc_ext_ext_muls"] / qk_gqa["sc_ext_ext_muls"], 2),
            "qk_rep_total_bb_muls_kar": qk_rep["total_base_mul_equiv_kar"],
            "qk_gqa_total_bb_muls_kar": qk_gqa["total_base_mul_equiv_kar"],
            "qk_total_speedup_kar": round(qk_rep["total_base_mul_equiv_kar"] / qk_gqa["total_base_mul_equiv_kar"], 3),
            "qk_rep_zkt_sc_ext_muls": qk_rep_zkt["sc_ext_ext_muls_zkt_linear_prover"],
            "qk_gqa_zkt_sc_ext_muls": qk_gqa_zkt["sc_ext_ext_muls_zkt_linear_prover"],
            # EV counts
            "ev_rep_rounds": ev_rep["sumcheck_rounds"],
            "ev_gqa_rounds": ev_gqa["sumcheck_rounds"],
            "ev_rep_pe_ext_base_muls": ev_rep["pe_ext_base_muls"],
            "ev_gqa_pe_ext_base_muls": ev_gqa["pe_ext_base_muls"],
            "ev_rep_sc_ext_ext_muls": ev_rep["sc_ext_ext_muls"],
            "ev_gqa_sc_ext_ext_muls": ev_gqa["sc_ext_ext_muls"],
            "ev_sc_speedup": round(ev_rep["sc_ext_ext_muls"] / ev_gqa["sc_ext_ext_muls"], 2),
            "ev_rep_total_bb_muls_kar": ev_rep["total_base_mul_equiv_kar"],
            "ev_gqa_total_bb_muls_kar": ev_gqa["total_base_mul_equiv_kar"],
            "ev_total_speedup_kar": round(ev_rep["total_base_mul_equiv_kar"] / ev_gqa["total_base_mul_equiv_kar"], 3),
            # Combined QK + EV per layer
            "attn_einsum_rep_bb_muls_1L": both_rep_kar,
            "attn_einsum_gqa_bb_muls_1L": both_gqa_kar,
            "attn_einsum_speedup_1L": round(both_rep_kar / both_gqa_kar, 3),
            # Committed KV cells
            "kv_cells_rep_1L": kv_cells_rep_1L,
            "kv_cells_gqa_1L": kv_cells_gqa_1L,
            "kv_cells_saved_1L": kv_cells_saved_1L,
            "kv_cells_saved_24L": kv_cells_saved_24L,
            "pcs_bb_muls_saved_1L": pcs_muls_saved_1L,
            "pcs_bb_muls_saved_24L": pcs_muls_saved_1L * LAYERS_GPTOSS,
            "total_1L_rep_incl_kv_pcs": both_rep_kar + round(kv_cells_rep_1L * whir_muls_per_cell),
            "total_1L_gqa_incl_kv_pcs": both_gqa_kar + round(kv_cells_gqa_1L * whir_muls_per_cell),
            "total_1L_speedup_incl_kv_pcs": round(
                (both_rep_kar + kv_cells_rep_1L * whir_muls_per_cell) /
                (both_gqa_kar + kv_cells_gqa_1L * whir_muls_per_cell), 3
            ),
        })

    out_json = os.path.join(HERE, "einsum_gqa_results.json")
    with open(out_json, "w") as f:
        json.dump({"verification_t32": verif, "counts_by_t": table_rows}, f, indent=2)

    out_csv = os.path.join(HERE, "einsum_gqa_counts.csv")
    with open(out_csv, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(table_rows[0].keys()))
        w.writeheader()
        w.writerows(table_rows)

    print("=== GQA EINSUMCHECK VERIFICATION OVER BABYBEAR EXT4 ===")
    print(json.dumps(verif, indent=2))
    print("\n=== GQA EINSUMCHECK PROVER COUNTS (1 Layer & 24-Layer KV Savings, BabyBear+Ext4) ===")
    hdr = (f"{'t':>5} | {'QK PE rep->gqa':>21} {'QK SC rep->gqa':>17} {'QK x':>6} | "
           f"{'EV SC rep->gqa':>19} {'EV x':>6} | {'KV Saved (24L)':>14} {'Tot+PCS x':>9}")
    print(hdr)
    print("-" * len(hdr))
    for r in table_rows:
        print(f"{r['t']:5d} | "
              f"{r['qk_rep_pe_ext_base_muls']:9,d}->{r['qk_gqa_pe_ext_base_muls']:9,d} "
              f"{r['qk_rep_sc_ext_ext_muls']:7,d}->{r['qk_gqa_sc_ext_ext_muls']:6,d} {r['qk_total_speedup_kar']:5.2f}x | "
              f"{r['ev_rep_sc_ext_ext_muls']:8,d}->{r['ev_gqa_sc_ext_ext_muls']:7,d} {r['ev_total_speedup_kar']:5.2f}x | "
              f"{r['kv_cells_saved_24L']:14,d} {r['total_1L_speedup_incl_kv_pcs']:8.2f}x")


def whir_muls_saved_factor(log_h: int) -> float:
    return (4.0 + 1.0) * max(1, log_h) / 2.0 + 2.0


if __name__ == "__main__":
    main()
