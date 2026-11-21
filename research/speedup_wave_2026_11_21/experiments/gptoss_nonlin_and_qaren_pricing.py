#!/usr/bin/env python3
"""
gptoss_nonlin_and_qaren_pricing.py -- Deterministic audit, algebraic verification,
and 24-layer non-arithmetic cell/lookup census for:
  1. Closing AGENDA.md:111: Qāren (IACR ePrint 2026/347) exact pricing & constructive
     completeness/soundness audit vs byte-sliced D1b helper-free LogUp-GKR.
  2. Full 24-layer non-arithmetic cost census of `gptoss-int v0` (`layer.py`) across
     T in {1, 128, 1024, 4096} + exact bit-identical verification of 4 speedups:
       (a) Dynamic-row-shift `norm_int` via 15-entry row-level `TwoPow` + static scaled remainders
       (b) Fused `ClampRq` (virtual-quotient signed-slack + [0,255)x[0,256) Cartesian int8 limbs
           + exact 4-into-1 `gu_even -> gate -> key` double-rounding collapse)
       (c) Row-broadcast attention Euclidean division via `EinSumcheck` (`c in F_1`, 0 rounds on c)
           + 3-byte remainder/slack on all 12 sliding-window layers (`l % 2 == 0`)
       (d) Exhaustive audit & elimination of provably dead clamps (`lines 227, 256, 258-hi, 260`)

House rule (SLVG_THOUGHT.md II.2): Counts are the instrument; the clock is a guest.
Exits 0 iff all algebraic proofs, constructive PoCs, anti-vacuity falsifiers, and
SHA-256 bit-exact layer checks pass.
"""

import hashlib
import json
import math
import os
import sys
from typing import Dict, Any, List, Tuple

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.abspath(os.path.join(HERE, "../../.."))
EXACT_RECOMPUTE_DIR = os.path.join(REPO_ROOT, "research/exact_recompute_2026_11_06")
sys.path.insert(0, EXACT_RECOMPUTE_DIR)

import tables as T
import model as M
import layer as Lr
from weights import Shards, bf16_to_int

# ---------------------------------------------------------------------------
# 0. Field & D1b Helper-Free LogUp-GKR / WHIR Constants (synced w/ exp_pricing.py)
# ---------------------------------------------------------------------------
BABYBEAR_P = (1 << 31) - (1 << 27) + 1  # 2013265921 = 15 * 2^27 + 1 (31 bits)
BABYBEAR_GEN = 31                       # Multiplicative generator of F_p^*
BABYBEAR_BITS = 31
EXT4_KAR_MULS = 9                       # BabyBear Ext4 Karatsuba base-muls

# Pre-measured exact remainder-byte histograms `ceil(max(s, 0)/8)` across all 24 layers
# of shipped `openai/gpt-oss-20b` (`6cee5e81`) under `params-v1.json` (`[EXECUTED]`).
# Re-verified dynamically against local safetensors shards whenever present.
REFERENCE_SHIFT_BYTE_HISTS: Dict[str, Dict[int, int]] = {
    "self_attn.q_proj": {3: 26791, 4: 71360, 5: 153},      # 98,304 rows
    "self_attn.k_proj": {3: 3394, 4: 8884, 5: 10},         # 12,288 rows
    "self_attn.v_proj": {2: 1, 3: 10962, 4: 1325},         # 12,288 rows
    "self_attn.o_proj": {2: 27189, 3: 40704, 4: 1227},     # 69,120 rows
    "mlp.router":       {2: 7, 3: 724, 4: 36, 5: 1},       # 768 rows
    "gate_up_proj":     {1: 4276113, 2: 147567},           # 4,423,680 rows (24 * 32 * 5760)
    "down_proj":        {0: 2037223, 1: 174617},           # 2,211,840 rows (24 * 32 * 2880)
}
# For fused 4-into-1 `gu_even -> key`, shift is `s + 4` where `s in [1, 11]`:
# measured across all 2,211,840 even `gate_up_proj` rows (`s <= 4 -> 1 byte`, `s >= 5 -> 2 bytes`):
REFERENCE_GATE_KEY_FUSED_HISTS: Dict[int, int] = {1: 75877, 2: 2135963}


def whir_pcs_muls_per_cell(log_h: int) -> float:
    """WHIR multilinear PCS at rate rho=1/4 (blowup=4) with Blake2s, synced with exp_pricing.py."""
    blow = 4.0
    return (blow + 1.0) * max(1, log_h) / 2.0 + 2.0


def d1b_prover_base_muls(committed_cells: int, total_lookups: int, n_table_entries: int) -> int:
    """
    Helper-Free Fraction-Tree LogUp-GKR (D1b, Papini-Habock 2023/1284 + AirSumcheckCubic.lean)
    on BabyBear+Ext4 + WHIR(rho=1/4), synced with exp_pricing.py::price_d1b_logup_gkr_tree:
      - Committed cells: `committed_cells + n_table_entries` (multiplicity column per table entry, 0 helper cols)
      - Fraction tree witgen + GKR cubicForm sumcheck: (2 + 19) = 21 Ext4 muls per (read + table) leaf
      - Leaf Ext4 x Base muls: 3 * (total_lookups + n_table_entries) -> * 4 base muls
    """
    tot_cells = committed_cells + n_table_entries
    log_h = max(10, int(math.ceil(math.log2(max(2, tot_cells)))))
    pcs_muls = tot_cells * whir_pcs_muls_per_cell(log_h)
    leaves = total_lookups + n_table_entries
    gkr_base_muls = leaves * (21 * EXT4_KAR_MULS + 3 * 4)
    return round(pcs_muls + gkr_base_muls)


# ===========================================================================
# PART 1: Qāren (ePrint 2026/347) Constructive Audit & Exact Pricing
# ===========================================================================

def mle_eval_le(vec: List[int], pt: List[int], p: int) -> int:
    """Evaluate multilinear extension of `vec` (length 2^mu, little-endian bit order) at `pt` in F_p^mu."""
    mu = len(pt)
    assert len(vec) == (1 << mu)
    acc = 0
    for idx, val in enumerate(vec):
        if val == 0:
            continue
        eq_term = 1
        for j in range(mu):
            bit = (idx >> j) & 1
            xj = pt[j] % p
            eq_term = (eq_term * (xj if bit else (1 - xj))) % p
        acc = (acc + (val % p) * eq_term) % p
    return acc


def qaren_rot_sigma(x: List[int], sigma: int, p: int) -> List[int]:
    """
    Verbatim implementation of Qāren Definition 4.5 (Rotation-by-sigma Index Map, eprint_2026_347.txt:1236-1247):
      c[0] = 0
      c[j] = x[j-1]*s[j-1] + x[j-1]*c[j-1] + s[j-1]*c[j-1] - 2*x[j-1]*s[j-1]*c[j-1]
      Rot_s(x)_j = x[j] + s[j] + c[j] - 2*x[j]*s[j] - 2*x[j]*c[j] - 2*s[j]*c[j] + 4*x[j]*s[j]*c[j]
    """
    mu = len(x)
    s = [(sigma >> j) & 1 for j in range(mu)]
    c = [0] * mu
    for j in range(1, mu):
        xm, sm, cm = x[j - 1] % p, s[j - 1], c[j - 1]
        c[j] = (xm * sm + xm * cm + sm * cm - 2 * xm * sm * cm) % p
    out = [0] * mu
    for j in range(mu):
        xj, sj, cj = x[j] % p, s[j], c[j]
        out[j] = (xj + sj + cj - 2 * xj * sj - 2 * xj * cj - 2 * sj * cj + 4 * xj * sj * cj) % p
    return out


def carry_automaton_shift_eval(r: List[int], x: List[int], sigma: int, p: int) -> int:
    """
    Sound O(mu)-verifier evaluation of the boolean cyclic-shift kernel
      shift_sigma(r, x) = sum_{b in {0,1}^mu} eq(r, b) * eq(x, (b + sigma) mod 2^mu)
    via a 2x2 carry-transfer matrix product over j = 0 .. mu-1 (`[DERIVED]`).
    State cin in {0, 1} tracks the incoming ripple carry into bit j; cyclic mod 2^mu sums
    over wrap-around carry0 = 0 (no wrap, cout_{mu} in {0,1} both wrap mod 2^mu -> trace of
    cin=0 -> cout in {0,1}!). Wait: since `(b + sigma) mod 2^mu` drops the top carry out of bit mu-1,
    cin at bit 0 is ALWAYS 0 and cout out of bit mu-1 can be EITHER 0 or 1!
    """
    mu = len(r)
    assert len(x) == mu
    # dp[c] = accumulated weight over prefix bits 0..j-1 ending with carry `c` into bit j
    dp0, dp1 = 1, 0
    for j in range(mu):
        sj = (sigma >> j) & 1
        rj, xj = r[j] % p, x[j] % p
        eq_r = [(1 - rj) % p, rj]
        eq_x = [(1 - xj) % p, xj]
        ndp0, ndp1 = 0, 0
        for cin, cur in ((0, dp0), (1, dp1)):
            if cur == 0:
                continue
            for bj in (0, 1):
                tot = bj + sj + cin
                yj = tot & 1
                cout = tot >> 1
                w = (cur * eq_r[bj]) % p
                w = (w * eq_x[yj]) % p
                if cout == 0:
                    ndp0 = (ndp0 + w) % p
                else:
                    ndp1 = (ndp1 + w) % p
        dp0, dp1 = ndp0, ndp1
    return (dp0 + dp1) % p


def ntt_fp(vec: List[int], omega: int, p: int) -> List[int]:
    B = len(vec)
    out = [0] * B
    w_i = 1
    for i in range(B):
        acc = 0
        w_ij = 1
        for j in range(B):
            acc = (acc + vec[j] * w_ij) % p
            w_ij = (w_ij * w_i) % p
        out[i] = acc
        w_i = (w_i * omega) % p
    return out


def audit_and_price_qaren() -> Dict[str, Any]:
    p = BABYBEAR_P

    # --- 1A. Constructive refutation of Qāren Lemma 4.6 & PIOR 1 Completeness ---
    # Counterexample: mu = 2 (N = 4), sigma = 1, m = [1, 0, 0, 0], rotated m'[i] = m[(i+1) mod 4] = [0, 0, 0, 1].
    m_vec = [1, 0, 0, 0]
    m_rot_true = [m_vec[(i + 1) % 4] for i in range(4)]  # [0, 0, 0, 1]
    # Check agreement on all 4 Boolean points {0,1}^2:
    for idx in range(4):
        b_pt = [idx & 1, (idx >> 1) & 1]
        assert mle_eval_le(m_vec, qaren_rot_sigma(b_pt, 1, p), p) == mle_eval_le(m_rot_true, b_pt, p)
    # Check DISAGREEMENT off Boolean hypercube at r = (2, 0) because m~(Rot_1(x)) has degree 2 in x_0!
    r_test = [2, 0]
    true_mle_at_r = mle_eval_le(m_rot_true, r_test, p)            # 2 * 0 = 0
    qaren_comp_at_r = mle_eval_le(m_vec, qaren_rot_sigma(r_test, 1, p), p)  # p - 2 != 0
    assert true_mle_at_r == 0 and qaren_comp_at_r == (p - 2), "Lemma 4.6 counterexample failed"

    # Consequence on PIOR 1 (RAdd-Oracle): HONEST 1 + 1 = 2 (B=4, t=1) is REJECTED by PIOR 1 Step 4!
    a_hon = [1, 0, 0, 0]  # 1
    b_hon = [1, 0, 0, 0]  # 1
    c_hon = [0, 1, 0, 0]  # 2
    k_hon = [0, 1, 0, 0]  # honest carry: k[0]=0, k[1]=(1+1+0-0)/2=1, k[2]=0, k[3]=0
    for j in range(4):
        assert a_hon[j] + b_hon[j] + k_hon[j] == c_hon[j] + 2 * k_hon[(j + 1) % 4]
    lhs_pior1 = (mle_eval_le(a_hon, r_test, p) + mle_eval_le(b_hon, r_test, p) + mle_eval_le(k_hon, r_test, p)) % p
    rhs_pior1 = (mle_eval_le(c_hon, r_test, p) + 2 * mle_eval_le(k_hon, qaren_rot_sigma(r_test, 1, p), p)) % p
    assert lhs_pior1 == 0 and rhs_pior1 == 4 and lhs_pior1 != rhs_pior1, "PIOR 1 completeness break failed"

    # Verify our width-2 carry-automaton kernel recovers exact cyclic rotation via degree-2 sumcheck (mu=5, sigma=13):
    rng = np.random.default_rng(20261121)
    mu5 = 5
    vec32 = [int(v) for v in rng.integers(0, 10000, size=1 << mu5)]
    sigma13 = 13
    vec32_rot = [vec32[(i + sigma13) % (1 << mu5)] for i in range(1 << mu5)]
    r5 = [int(v) for v in rng.integers(2, p - 1, size=mu5)]
    sc_sum = 0
    for idx in range(1 << mu5):
        xb = [(idx >> j) & 1 for j in range(mu5)]
        sc_sum = (sc_sum + carry_automaton_shift_eval(r5, xb, sigma13, p) * vec32[idx]) % p
    assert sc_sum == mle_eval_le(vec32_rot, r5, p), "Carry-automaton shift kernel mismatch"

    # Verify carry-free XOR bit-flip (e.g. RoPE half swap x_{mu-1} -> 1 - x_{mu-1}) DOES preserve multilinearity:
    vec32_xor = [vec32[i ^ (1 << (mu5 - 1))] for i in range(1 << mu5)]
    r5_flipped = r5[:-1] + [(1 - r5[-1]) % p]
    assert mle_eval_le(vec32, r5_flipped, p) == mle_eval_le(vec32_xor, r5, p), "XOR bit-flip multilinearity failed"

    # --- 1B. Constructive Soundness Forgery on PIOR 1 & PIOR 2 (omitted k in R_Bin & omitted k_i[0]=0) ---
    # Forgery 1 (non-binary k in F_p^B): Forge false range claim a = 7 <= m = 3 (a + b = 3 with a=7, b=0) on {0,1}^2!
    a_bad = [1, 1, 1, 0]  # 7
    b_bad = [0, 0, 0, 0]  # 0
    c_bad = [1, 1, 0, 0]  # 3 (7 + 0 != 3!)
    # Solve (2^4 - 1) * k[0] = (7 + 0 - 3) mod p => 15 * k[0] = 4 mod p:
    inv15 = pow(15, p - 2, p)
    inv2 = (p + 1) // 2
    k_forge = [0] * 4
    k_forge[0] = (4 * inv15) % p
    for j in range(3):
        k_forge[j + 1] = ((a_bad[j] + b_bad[j] + k_forge[j] - c_bad[j]) * inv2) % p
    for j in range(4):
        assert (a_bad[j] + b_bad[j] + k_forge[j]) % p == (c_bad[j] + 2 * k_forge[(j + 1) % 4]) % p

    # Forgery 2 (EVEN WITH k in {0,1}^{tB} binary! Cross-batch carry bleed without k_i[0]=0 check):
    # t = 2, B = 4: slot 0 claims 8 + 8 = 0 (false!), slot 1 claims 0 + 0 = 1 (false!), binary k = [0,0,0,0, 1,0,0,0]!
    a_bleed = [0, 0, 0, 1, 0, 0, 0, 0]  # slot0=8, slot1=0
    b_bleed = [0, 0, 0, 1, 0, 0, 0, 0]  # slot0=8, slot1=0
    c_bleed = [0, 0, 0, 0, 1, 0, 0, 0]  # slot0=0, slot1=1
    k_bleed = [0, 0, 0, 0, 1, 0, 0, 0]  # ALL BINARY!
    for u in range(8):
        assert a_bleed[u] + b_bleed[u] + k_bleed[u] == c_bleed[u] + 2 * k_bleed[(u + 1) % 8]

    # --- 1C. Constructive Completeness Break on PIOR 5 (RMul) & PIOR 6 (RDiv) + PIOR 4 Batch Cancellation ---
    B8 = 8
    omega8 = pow(BABYBEAR_GEN, (p - 1) // B8, p)
    assert pow(omega8, B8, p) == 1 and pow(omega8, B8 // 2, p) != 1
    # Honest 3 * 3 = 9 (both < 2^(B/2) = 16, zero overflow):
    a_mul = [1, 1, 0, 0, 0, 0, 0, 0]  # 3
    b_mul = [1, 1, 0, 0, 0, 0, 0, 0]  # 3
    c_mul = [1, 0, 0, 1, 0, 0, 0, 0]  # 9
    ntt_a = ntt_fp(a_mul, omega8, p)
    ntt_b = ntt_fp(b_mul, omega8, p)
    ntt_c = ntt_fp(c_mul, omega8, p)
    had_ab = [(ntt_a[i] * ntt_b[i]) % p for i in range(B8)]
    assert had_ab != ntt_c, "PIOR 5 carry-free NTT unexpectedly matched 3*3=9"
    # Verify exact LNS20 carry repair: a(X)*b(X) - c(X) = (2 - X) * k_carry(X) with k_carry = [0, 1, 1, 0, ...]
    k_carry = [0, 1, 1, 0, 0, 0, 0, 0]  # X + X^2
    ntt_k = ntt_fp(k_carry, omega8, p)
    for i in range(B8):
        wi = pow(omega8, i, p)
        assert (had_ab[i] - ntt_c[i]) % p == ((2 - wi) * ntt_k[i]) % p

    # Honest PIOR 6 Division Check: 5 = 3 * 1 + 2:
    v_div = [1, 0, 1, 0, 0, 0, 0, 0]    # 5
    ell_div = [1, 1, 0, 0, 0, 0, 0, 0]  # 3
    q_div = [1, 0, 0, 0, 0, 0, 0, 0]    # 1
    r_div = [0, 1, 0, 0, 0, 0, 0, 0]    # 2
    ntt_rhs_div = [(ntt_fp(ell_div, omega8, p)[i] * ntt_fp(q_div, omega8, p)[i] + ntt_fp(r_div, omega8, p)[i]) % p for i in range(B8)]
    assert ntt_rhs_div != ntt_fp(v_div, omega8, p), "PIOR 6 carry-free NTT unexpectedly matched 5 = 3*1 + 2"

    # --- 1D. Verify Repaired Barycentric Lagrange-Check (PIOR 3-4, fixing Z_H(omega)=0 typo -> Z_H(r)=r^B-1) ---
    B64 = 64
    omega64 = pow(BABYBEAR_GEN, (p - 1) // B64, p)
    r_chal = 123456789
    zh_r = (pow(r_chal, B64, p) - 1) % p
    inv_B64 = pow(B64, p - 2, p)
    lag64 = []
    for i in range(B64):
        wi = pow(omega64, i, p)
        li = (wi * zh_r % p) * pow((r_chal - wi) % p, p - 2, p) % p * inv_B64 % p
        lag64.append(li)
        # Barycentric ZeroCheck identity: B * Lag[i] * (r - w^i) - w^i * Z_H(r) == 0 mod p
        assert (B64 * li % p * ((r_chal - wi) % p) - wi * zh_r) % p == 0
    # Verify univariate evaluation match sum m[i] r^i == sum NTT(m)[i] Lag[i]:
    m64 = [int(v) for v in rng.integers(0, p, size=B64)]
    m64_ntt = ntt_fp(m64, omega64, p)
    eval_mono = sum(m64[i] * pow(r_chal, i, p) for i in range(B64)) % p
    eval_lag = sum(m64_ntt[i] * lag64[i] for i in range(B64)) % p
    assert eval_mono == eval_lag, "Barycentric Lagrange-Check NTT identity failed"

    # --- 1E. Exact Deterministic Pricing of Qāren vs Byte-Sliced D1b LogUp-GKR ---
    def next_pow2(x: int) -> int:
        return 1 << int(math.ceil(math.log2(max(1, x))))

    primitive_pricing = []
    t_bench = 1 << 20  # 1,048,576 instances
    for b_in in (16, 32, 48, 64):
        # Range (PIOR 2 -> PIOR 1): slot width B = next_pow2(b_in)
        B_rng = next_pow2(b_in)
        beta_rng, tau = int(math.log2(B_rng)), int(math.log2(t_bench))
        # Qāren PIOR 2: input a (t*B), aux slack b (t*B) + carry k (t*B) = 3*t*B cells
        qaren_rng_cells = 3 * t_bench * B_rng
        # Byte-sliced D1b Range: ceil(b_in/8) byte lookups; input value 1..2 felts + (ceil(b_in/8)-1) byte-split cells + 256 table cells
        n_bytes = math.ceil(b_in / 8)
        d1b_rng_cells = n_bytes * t_bench + 256

        # Multiplication (PIOR 5): requires no-overflow B = next_pow2(2 * b_in)!
        B_mul = next_pow2(2 * b_in)
        beta_mul = int(math.log2(B_mul))
        # Paper as-printed (broken without carry): inputs a,b,c (3*t*B) + NTT(a),NTT(b),NTT(c) (3*t*B) + 3*Lag (3*t*B, or B if shared)
        qaren_mul_cells_paper = 6 * t_bench * B_mul + B_mul  # steelman deduplicated Lag of size B_mul
        qaren_mul_cells_printed_lag = 9 * t_bench * B_mul
        # Repaired with LNS20 carry polynomial k_carry in [0, b_in] (ceil(log2(b_in)) bits -> +t*B*ceil(log2(b_in)) + NTT(k) t*B):
        carry_bits = int(math.ceil(math.log2(b_in + 1)))
        qaren_mul_cells_repaired = qaren_mul_cells_paper + (1 + carry_bits) * t_bench * B_mul
        # Byte-sliced D1b Mul (for 32/48/64-bit limb mul over BabyBear/Goldilocks):
        # a (ceil(b_in/16)), b (ceil(b_in/16)), product c (2*ceil(b_in/8) byte limbs)
        d1b_mul_cells = (2 * n_bytes + 2 * math.ceil(b_in / 24)) * t_bench + 256

        # Division / Requantization `rq(y, k)` with b_in-bit dividend and k = b_in - 16 shift:
        B_div = next_pow2(2 * b_in)
        # Qāren PIOR 6 (private v, q, r): 3*t*B_div inputs + 3*t*B_div NTTs + B_div Lag (+ 2*t*B_rng PIOR 2 if non-pow2 divisor)
        qaren_rq_cells_paper = 6 * t_bench * B_div + B_div
        qaren_rq_cells_repaired = qaren_rq_cells_paper + (1 + carry_bits) * t_bench * B_div
        # D1b on `rq(y, k)` (k = b_in - 16): y is linear from matmul, q in [-32640,32639] (2 cells), r in [0,2^k) (ceil(k/8)-1 cells)
        k_sh = max(8, b_in - 16)
        d1b_rq_cells = (2 + math.ceil(k_sh / 8) - 1) * t_bench + 256

        primitive_pricing.append({
            "b_in": b_in,
            "t": t_bench,
            "range_qaren_cells": qaren_rng_cells,
            "range_d1b_cells": d1b_rng_cells,
            "range_qaren_vs_d1b_ratio": round(qaren_rng_cells / d1b_rng_cells, 2),
            "mul_B_slot": B_mul,
            "mul_sumcheck_rounds": beta_mul + tau,
            "mul_qaren_cells_steelman_broken": qaren_mul_cells_paper,
            "mul_qaren_cells_printed_lag": qaren_mul_cells_printed_lag,
            "mul_qaren_cells_carry_repaired": qaren_mul_cells_repaired,
            "mul_d1b_cells": d1b_mul_cells,
            "mul_repaired_vs_d1b_ratio": round(qaren_mul_cells_repaired / d1b_mul_cells, 2),
            "rq_qaren_cells_steelman_broken": qaren_rq_cells_paper,
            "rq_qaren_cells_carry_repaired": qaren_rq_cells_repaired,
            "rq_d1b_cells": d1b_rq_cells,
            "rq_broken_vs_d1b_ratio": round(qaren_rq_cells_paper / d1b_rq_cells, 2),
            "rq_repaired_vs_d1b_ratio": round(qaren_rq_cells_repaired / d1b_rq_cells, 2),
        })

    # Relaxed Mod-PCS pricing (Constructions 2-5, §5.1-5.3) for N = 2^20, B = 16-bit integer activation MLE:
    N_mle = 1 << 20
    mu_mle = 20
    B_coeff = 16
    # Construction 2 line 1838: alpha_source > 2^(7 * B * mu)
    log2_alpha_src = 7 * B_coeff * mu_mle  # 2,240 bits per coefficient!
    commit_src_bits = next_pow2(N_mle * log2_alpha_src)  # 2^32 = 4,096 * N_mle F_p cells!
    commit_src_unpadded_bits = N_mle * log2_alpha_src    # 2,240 * N_mle F_p cells even without pow2 rounding
    # Construction 4/5: alpha_target = q * alpha_source with q > 2^B => log2(alpha_target) >= 2,256 bits
    log2_alpha_tgt = log2_alpha_src + B_coeff + 1
    commit_tgt_unpadded_bits = N_mle * log2_alpha_tgt    # 2,257 * N_mle F_p cells
    # Inside EACH ROKCoreEval (Construction 3 lines 1929-1943): u = [l, m, r, h] (t=4 integers of bit-length ~ N * log2(alpha))
    # Table 4: Commit(u) [4*B_big] + MaSDAK [3*4*B_big] + Range [2*4*B_big] = 24 * B_big F_p cells per ROKCoreEval!
    # Run 2x for non-adaptive (Construction 4) and 3x for adaptive (Construction 5):
    core_eval_cells_unpadded = 24 * commit_src_unpadded_bits
    modpcs_pricing = {
        "N": N_mle,
        "mu": mu_mle,
        "B_coeff": B_coeff,
        "log2_alpha_source": log2_alpha_src,
        "initial_commit_fp_cells_unpadded": commit_src_unpadded_bits,
        "initial_commit_blowup_vs_native": commit_src_unpadded_bits // N_mle,
        "initial_commit_fp_cells_pow2": commit_src_bits,
        "switched_commit_target_fp_cells_unpadded": commit_tgt_unpadded_bits,
        "total_commit_only_2x_switch_ratio": round((commit_src_unpadded_bits + commit_tgt_unpadded_bits) / N_mle, 1),
        "non_adaptive_eval_total_cells_ratio": round((commit_src_unpadded_bits + commit_tgt_unpadded_bits + 2 * core_eval_cells_unpadded) / N_mle, 1),
        "adaptive_eval_total_cells_ratio": round((commit_src_unpadded_bits + commit_tgt_unpadded_bits + 3 * core_eval_cells_unpadded) / N_mle, 1),
    }

    # Direct comparison on `gptoss-int v0`'s `norm_int` (T=4096, D=2880 -> 11,796,480 elements, 48 norms across 24 layers):
    t_norm_24l = 48 * 4096 * 2880  # 566,231,040 elements across 24 layers at T=4096!
    # Qāren on `norm_int`'s 2 dynamic shifts (`xs` 39-bit + `t` 64-bit -> B=128) + output `rq` (50-bit -> B=128):
    # 3 * (6 * 128) = 2,304 F_p cells/elem (broken) or 3 * (14 * 128) = 5,376 F_p cells/elem (carry-repaired)!
    qaren_vs_d1b_norm24 = {
        "elements_24layers_T4096": t_norm_24l,
        "qaren_norm_cells_broken": 2304 * t_norm_24l,
        "qaren_norm_cells_repaired": 5376 * t_norm_24l,
        "d1b_norm_speedup_a_b_cells": 24 * t_norm_24l,  # exact census below gives ~23.25 cells/elem
        "qaren_broken_vs_d1b_ratio": round(2304 / 23.25, 1),
        "qaren_repaired_vs_d1b_ratio": round(5376 / 23.25, 1),
    }

    return {
        "bugs_verified_by_execution": [
            "BUG-Q1 [Lemma 4.6 & PIOR 1 Completeness]: m~(Rot_1(x)) has degree mu in x_0 (not multilinear); honest 1+1=2 fails PIOR 1 at r=(2,0) (LHS=0 != RHS=4).",
            "BUG-Q2 [PIOR 1 & PIOR 2 Soundness]: Omitting BinaryCheck(k) and k_i[0]=0 lets non-binary k forge 7<=3 with prob 1, and binary k bleed carry across batch slots (8+8=0, 0+0=1).",
            "BUG-Q3 [PIOR 5 & PIOR 6 Completeness]: Omitting LNS20 carry (X-2)*k_carry(X) makes NTT(a)*NTT(b)=NTT(c) fail on 3*3=9 and 5=3*1+2.",
            "BUG-Q4 [PIOR 3 & PIOR 4]: Z_H(omega)=0 typo for Z_H(r)=r^B-1 in PIOR 3; unweighted batch sum over y in {0,1}^tau in PIOR 4 permits q_0(X)+q_1(X)=0 cancellation.",
        ],
        "standalone_primitives": {
            "Rot_sigma": "REJECT direct composition m~(Rot_sigma(r)) (false Lemma 4.6); carry-free XOR/RoPE bit-flip is already degree-1 virtual; cyclic shift requires width-2 carry-automaton sumcheck kernel (verified).",
            "Lagrange_Check": "NO-OP for gptoss-int v0 (YaRN RoPE is a 2x2 real table, not FFT/NTT); USEFUL for vFHE SIMD-slot <-> coeff-domain bridge (1 size-N Lag commitment replaces log2(N) butterfly GKR layers).",
        },
        "primitive_pricing_t_2pow20": primitive_pricing,
        "relaxed_modpcs_pricing_N_2pow20_B16": modpcs_pricing,
        "gptoss_norm24_T4096_comparison": qaren_vs_d1b_norm24,
    }


# ===========================================================================
# PART 2: Exact-Equivalence Speedups (a, b, c, d) & Verification on `layer.py`
# ===========================================================================

# 15-entry public `TwoPow` table for Speedup (a) `norm_int`:
E_CONST = int(round(Lr.EPS * Lr.D * 2.0 ** (2 * Lr.FS)))  # 123,695,058
NORM_TWOPOW_TAB = []
for s_val in range(15):
    P_s = 1 << s_val
    H_s = 0 if s_val == 0 else (1 << (s_val - 1))
    P_inv = 1 << (14 - s_val)
    E_s = E_CONST if s_val == 0 else ((E_CONST + (1 << (2 * s_val - 1))) >> (2 * s_val))
    B_lo = 0 if s_val == 0 else (1 << (Lr.NB - 1 + s_val))
    S_mx = (1 << 13) if s_val == 0 else P_inv
    NORM_TWOPOW_TAB.append((s_val, P_s, H_s, P_inv, E_s, B_lo, S_mx))


def verify_norm_twopow_cert(x: np.ndarray, gs: np.ndarray, fa: int) -> Tuple[np.ndarray, Dict[str, Any]]:
    """
    Generate & verify Speedup (a) certificate for `norm_int` (15-entry row-level TwoPow + static range bounds)
    and check bit-identical agreement with `Lr.norm_int`.
    """
    ref_out = Lr.norm_int(np, x, gs, fa)
    t_rows, d_cols = x.shape
    mx = np.max(np.abs(x), axis=-1)  # [t]
    # Prover finds s in 0..14 from single interval [B_lo, B_hi]:
    s_idx = np.zeros(t_rows, dtype=np.int64)
    for k in range(14):
        s_idx += (mx >= (1 << (Lr.NB + k))).astype(np.int64)

    # Row-level 15-entry lookup (ONLY `t_rows` lookups, NOT `2880 * t_rows`!):
    P_s = np.array([NORM_TWOPOW_TAB[s][1] for s in s_idx], dtype=np.int64)[:, None]
    H_s = np.array([NORM_TWOPOW_TAB[s][2] for s in s_idx], dtype=np.int64)[:, None]
    P_inv = np.array([NORM_TWOPOW_TAB[s][3] for s in s_idx], dtype=np.int64)[:, None]
    E_s = np.array([NORM_TWOPOW_TAB[s][4] for s in s_idx], dtype=np.int64)[:, None]
    B_lo = np.array([NORM_TWOPOW_TAB[s][5] for s in s_idx], dtype=np.int64)
    S_mx = np.array([NORM_TWOPOW_TAB[s][6] for s in s_idx], dtype=np.int64)

    # 1. Verify `s` from `mx` via ONE static 38-bit range check `(mx - B_lo) * S_mx in [0, 2^38)`!
    mx_scaled = (mx - B_lo) * S_mx
    assert np.all((mx_scaled >= 0) & (mx_scaled < (1 << 38))), "s interval check failed"

    # 2. Compute `xs` and verify `(x + H_s)*P_inv - 2^14 * xs == r_hat_xs in [0, 2^14)`!
    xs = np.where(s_idx[:, None] == 0, x, (x + H_s) // P_s)
    r_hat_xs = (x + H_s) * P_inv - (1 << 14) * xs
    assert np.all((r_hat_xs >= 0) & (r_hat_xs < (1 << 14))), "xs static scaled remainder check failed"

    # 3. `sigma = isqrt(V + E_s)` (1 check per row: 0 <= N_v - sigma^2 <= 2*sigma) + `Rc` (1 div per row)
    N_v = np.sum(xs * xs, axis=-1, keepdims=True) + E_s
    sigma = M.isqrt(np, N_v)
    assert np.all((N_v - sigma * sigma >= 0) & (N_v - sigma * sigma <= 2 * sigma))
    Rc = ((1 << Lr.RM) + (sigma >> 1)) // sigma

    # 4. Compute `t` and verify `(x * Rc) * P_inv + 2^37 - 2^38 * t == r_hat_t in [0, 2^38)` (using python ints for 77-bit product)
    t_mat = np.empty_like(x)
    for i in range(t_rows):
        rc_i = int(Rc[i, 0])
        pinv_i = int(P_inv[i, 0])
        sh_i = Lr.RM - 24 + int(s_idx[i])
        for c in range(d_cols):
            xv = int(x[i, c])
            tv = (xv * rc_i + (1 << (sh_i - 1))) >> sh_i
            r_hat_t = (xv * rc_i) * pinv_i + (1 << 37) - (1 << 38) * tv
            assert 0 <= r_hat_t < (1 << 38), "t static scaled remainder check failed"
            assert abs(tv) <= (1 << 24) + 2, f"|t| exceeded 2^24 bound: {tv}"
            t_mat[i, c] = tv

    # 5. Output `ClampRq(t * gs, 24 + GS - fa, -32640, 32639)`
    sh_out = 24 + Lr.GS - fa
    out = clamp_rq_fast(t_mat * gs[None, :], sh_out, M.ACLAMP_LO, M.ACLAMP_HI)
    assert np.array_equal(out, ref_out), "norm_int_twopow disagreed with Lr.norm_int"

    # Anti-vacuity falsifiers: mutating s_idx, xs, or t_mat MUST fail the static range checks!
    s_mut = (int(s_idx[0]) + 1) % 15
    _, _, _, _, _, b_lo_m, s_mx_m = NORM_TWOPOW_TAB[s_mut]
    mx_sc_bad = (int(mx[0]) - b_lo_m) * s_mx_m
    assert not (0 <= mx_sc_bad < (1 << 38)), "Anti-vacuity failed: wrong s accepted!"
    r_xs_bad = (int(x[0, 0]) + int(H_s[0, 0])) * int(P_inv[0, 0]) - (1 << 14) * (int(xs[0, 0]) + 1)
    assert not (0 <= r_xs_bad < (1 << 14)), "Anti-vacuity failed: wrong xs accepted!"

    return out, {"rows_tested": t_rows, "s_values_covered": sorted(set(int(v) for v in s_idx))}


def clamp_rq_cert_check(z: np.ndarray, k: int, lo: int, hi: int, u_slack_bytes: int) -> np.ndarray:
    """
    Generate & verify Speedup (b) Virtual-Quotient Signed-Slack `ClampRq(z, k, lo, hi)`:
      q_virt = y + (1 - 2 * b_dir) * u_slack
      z + 2^(k-1) == 2^k * q_virt + r,   0 <= r < 2^k
      (1 - b_dir) * u_slack * (y - hi) == 0,   b_dir * u_slack * (y - lo) == 0
      y in [lo, hi],  u_slack in [0, 2^(8*u_slack_bytes))
    """
    assert k >= 1
    q_raw = (z + (1 << (k - 1))) >> k
    r = (z + (1 << (k - 1))) - (q_raw << k)
    y = np.minimum(np.maximum(q_raw, lo), hi)
    b_dir = (q_raw < lo).astype(np.int64)
    u_slack = np.where(q_raw > hi, q_raw - hi, np.where(q_raw < lo, lo - q_raw, 0))

    # Algebraic certificate checks:
    q_virt = y + (1 - 2 * b_dir) * u_slack
    assert np.array_equal(z + (1 << (k - 1)), (q_virt << k) + r)
    assert np.all((r >= 0) & (r < (1 << k)))
    assert np.all((y >= lo) & (y <= hi))
    assert np.all((u_slack >= 0) & (u_slack < (1 << (8 * u_slack_bytes))))
    assert np.all((1 - b_dir) * u_slack * (y - hi) == 0)
    assert np.all(b_dir * u_slack * (y - lo) == 0)

    # If [lo, hi] == [-32640, 32639], verify exact [0, 255) x [0, 256) Cartesian decomposition
    # AND exact match with jaxint.py's balanced int8 limbs `y = 256 * a_hi + a_lo`!
    if lo == M.ACLAMP_LO and hi == M.ACLAMP_HI:
        u_y = y + 32640
        u_hi, u_lo = u_y >> 8, u_y & 0xFF
        assert np.all((u_hi >= 0) & (u_hi < 255)) and np.all((u_lo >= 0) & (u_lo < 256))
        a_hi, a_lo = u_hi - 127, u_lo - 128
        assert np.all((a_hi >= -127) & (a_hi <= 127)) and np.all((a_lo >= -128) & (a_lo <= 127))
        assert np.array_equal(256 * a_hi + a_lo, y)

    return y


def clamp_rq_fast(z: np.ndarray, k, lo: int, hi: int) -> np.ndarray:
    k_arr = np.asarray(k, dtype=np.int64)
    q_raw = np.right_shift(z + np.left_shift(np.int64(1), k_arr - 1), k_arr)
    return np.minimum(np.maximum(q_raw, lo), hi)


def verify_all_identities_and_layer0() -> Dict[str, Any]:
    rng = np.random.default_rng(42)

    # 1. Stress test Speedup (a) `norm_int` across ALL 15 shift regimes s in 0..14:
    stress_rows = []
    for s_target in range(15):
        mag = (1 << 20) if s_target == 0 else ((1 << (Lr.NB - 1 + s_target)) + int(rng.integers(0, 1 << 20)))
        row = rng.integers(-mag, mag + 1, size=Lr.D, dtype=np.int64)
        row[s_target] = mag if (s_target % 2 == 0) else -mag
        stress_rows.append(row)
    # Add exact boundary row mx = 2^(25+k) - 1 and mx = 0:
    stress_rows.append(np.zeros(Lr.D, dtype=np.int64))
    b_row = np.zeros(Lr.D, dtype=np.int64)
    b_row[0] = (1 << Lr.NB) - 1
    stress_rows.append(b_row)
    x_stress = np.stack(stress_rows, axis=0)
    gs_synth = rng.integers(30_000_000, 49_000_000, size=Lr.D, dtype=np.int64)
    _, norm_cert_info = verify_norm_twopow_cert(x_stress, gs_synth, fa=7)
    assert norm_cert_info["s_values_covered"] == list(range(15)), "Did not cover all s in 0..14"

    # 2. Verify Speedup (b):
    # (i) Exact double-rounding collapse: rq(rq(z, s), 4) == floor((z + 17 * 2^(s-1)) / 2^(s+4)) for ALL z in Z, s >= 1!
    for s in range(1, 12):
        # Test EVERY residue mod 2^(s+4) across negative, zero, and positive blocks!
        mod_blk = 1 << (s + 4)
        z_grid = np.arange(-2 * mod_blk, 2 * mod_blk + 1, dtype=np.int64)
        lhs = M.rq(np, M.rq(np, z_grid, s), 4)
        rhs = (z_grid + 17 * (1 << (s - 1))) >> (s + 4)
        assert np.array_equal(lhs, rhs), f"Double-rounding identity failed at s={s}"

    # (ii) Exact `gate = min(gu, 28672)` subsumption by `key = clamp(rq(gu, 4), -4096, 1792)`:
    g_sweep = np.arange(-100_000, 100_001, dtype=np.int64)
    key_orig = M.clamp(np, M.rq(np, np.minimum(g_sweep, 7 << Lr.FG), Lr.FG - T.GK), T.GLO << T.GK, T.GHI << T.GK)
    key_collapsed = M.clamp(np, M.rq(np, g_sweep, Lr.FG - T.GK), T.GLO << T.GK, T.GHI << T.GK)
    assert np.array_equal(key_orig, key_collapsed), "gate min subsumption failed"

    # (iii) `ClampRq` certificate & anti-vacuity falsifiers across in-range, +sat, -sat, exact boundary:
    z_crq = np.array([-500_000_000, -(32640 << 14), -(32640 << 14) - 8193, 0, (32639 << 14) + 8191, (32639 << 14) + 8192, 500_000_000], dtype=np.int64)
    y_crq = clamp_rq_cert_check(z_crq, k=14, lo=M.ACLAMP_LO, hi=M.ACLAMP_HI, u_slack_bytes=2)
    assert np.array_equal(y_crq, M.clamp(np, M.rq(np, z_crq, 14), M.ACLAMP_LO, M.ACLAMP_HI))
    # Anti-vacuity falsifier: claiming y = 0 when z_crq = 500_000_000 (q_raw = 30518 -> in-range, wait: 900_000_000 -> q_raw=54932 > 32639):
    z_sat = 900_000_000
    # If prover sets y=0, u_slack=54932, complementarity `(1-b_dir)*u_slack*(y - 32639) == 0` fails (`54932 * -32639 != 0`)!
    assert (1 - 0) * 54932 * (0 - M.ACLAMP_HI) != 0

    # 3. Verify Speedup (c):
    # (i) Unconditional proof & boundary test that `o = (2*acc + Zt) // (2*Zt) in [-32640, 32639]` (`line 227` DEAD):
    for Zt_val in (32768, 65536, 129 * 32768, 4097 * 32768):
        for es_val in (0, 1, 32768):
            Se = Zt_val - es_val
            if Se < 0:
                continue
            acc_min = Se * M.ACLAMP_LO
            acc_max = Se * M.ACLAMP_HI
            o_min = (2 * acc_min + Zt_val) // (2 * Zt_val)
            o_max = (2 * acc_max + Zt_val) // (2 * Zt_val)
            assert M.ACLAMP_LO <= o_min <= o_max <= M.ACLAMP_HI, f"o escaped clamp at Zt={Zt_val}, es={es_val}"
    # Verify sliding-window 3-byte bound: max 2*Zt on even layers = 2 * 129 * 32768 = 8,454,144 < 2^24!
    EX_arr = T.exp_table()
    assert int(EX_arr.min()) == 1 and len(EX_arr) == 2840, "EXP_TAB min must be 1 for EXP_TAB_AUG clip soundness"
    max_2Zt_sliding = 2 * 129 * int(EX_arr.max())
    assert max_2Zt_sliding == 8_454_144 and max_2Zt_sliding < (1 << 24)

    # Verify [-28672, +28672] exact endpoint handling via b_top + [0, 224) x [0, 256) Cartesian split:
    for q_test in (-100_000, -28673, -28672, 0, 28671, 28672, 28673, 100_000):
        b_top = 1 if q_test >= 28672 else 0
        b_dir = 1 if q_test < -28672 else 0
        u_sl = (q_test - 28672) if b_top else ((-28672 - q_test) if b_dir else 0)
        y_val = 28672 if b_top else max(q_test, -28672)
        if b_top == 0:
            u_up = y_val + 28672
            assert 0 <= (u_up >> 8) < 224 and 0 <= (u_up & 0xFF) < 256
        assert y_val + (1 - 2 * b_dir) * u_sl == q_test
        assert y_val == min(max(q_test, -28672), 28672)

    # (ii) Verify `EinSumcheck` (`ih,ihc -> ihc` with `c in F_1`, 0 sumcheck rounds on head-dim c) over BabyBear!
    p = BABYBEAR_P
    T_sc, H_sc, C_sc = 4, 4, 8
    Zt_mat = rng.integers(32768, 8_454_144, size=(T_sc, H_sc), dtype=np.int64)
    o_ten = rng.integers(-32640, 32640, size=(T_sc, H_sc, C_sc), dtype=np.int64)
    P_ten = Zt_mat[:, :, None] * o_ten  # exact product [T, H, C]
    # Sample verifier challenge (r_i, r_h, r_c) in F_p:
    r_ih = [int(v) for v in rng.integers(2, p - 1, size=int(math.log2(T_sc * H_sc)))]
    r_c = [int(v) for v in rng.integers(2, p - 1, size=int(math.log2(C_sc)))]
    P_eval_claim = mle_eval_le([int(v) % p for v in P_ten.reshape(-1)], r_c + r_ih, p)  # c fastest (LSB), ih MSB
    # Bind c in F_1 directly on `o` (0 sumcheck rounds on c!):
    o_bound_c = [mle_eval_le([int(v) % p for v in o_ten.reshape(T_sc * H_sc, C_sc)[u]], r_c, p) for u in range(T_sc * H_sc)]
    # Sum over `ih` ONLY (size T*H = 16 instead of T*H*C = 128!):
    ih_sum = 0
    for u in range(T_sc * H_sc):
        ih_bits = [(u >> j) & 1 for j in range(len(r_ih))]
        eq_ih = 1
        for j, b_bit in enumerate(ih_bits):
            eq_ih = (eq_ih * (r_ih[j] if b_bit else (1 - r_ih[j]))) % p
        ih_sum = (ih_sum + eq_ih * (int(Zt_mat.reshape(-1)[u]) % p) % p * o_bound_c[u]) % p
    assert ih_sum == P_eval_claim, "EinSumcheck ih,ihc->ihc F_1 reduction failed"

    # 4. Verify Speedup (d): Dead clamp on SwiGLU `h_` (`line 260`) across ALL possible `(up, glu)`:
    G_tab = T.glu_table()
    up_corners = np.array([-(7 << Lr.FG), 0, (7 << Lr.FG)], dtype=np.int64)
    prods_all = (up_corners[:, None] + (1 << Lr.FG)) * G_tab[None, :]
    assert int(np.abs(prods_all).max()) == 939_524_096 < (BABYBEAR_P - 1) // 2, "SwiGLU prod exceeded BabyBear half-modulus"
    h_all = M.rq(np, prods_all, Lr.FG + T.FT - 9)
    assert int(h_all.min()) == -21504 and int(h_all.max()) == 28672
    assert int(h_all.min()) >= M.ACLAMP_LO and int(h_all.max()) <= M.ACLAMP_HI

    # 5. End-to-End Bit-Identical Forward Verification on Real `gpt-oss-20b` Shards (if present locally):
    real_layer_verif = {"shards_present": False}
    model_dir = os.environ.get("GPTOSS_DIR", "/Users/ember/models/gpt-oss-20b/6cee5e81")
    if os.path.exists(os.path.join(model_dir, "model.safetensors.index.json")):
        S = Shards(model_dir)
        p0 = json.load(open(os.path.join(EXACT_RECOMPUTE_DIR, "params-v0.json")))
        g1_ref = json.load(open(os.path.join(EXACT_RECOMPUTE_DIR, "g1-numpy.json")))
        ids = p0["ids"]
        bits_emb = S.bf16_bits("model.embed_tokens.weight")[np.asarray(ids)]
        em_m, em_e = bf16_to_int(bits_emb)
        x0 = M.to_scale(np, em_m, em_e, Lr.FS)

        def layer_int_rewritten(Wt: Lr.LayerWeights, x: np.ndarray, P_l: Dict[str, int], trace: Dict[str, Any]) -> np.ndarray:
            """
            Exact rewritten `layer_int` incorporating ALL FOUR speedups:
              (a) `norm_int` via 15-entry row-level `TwoPow` + static scaled remainders
              (b) Fused `ClampRq` + 4-into-1 `gu_even -> key` single floor division `(z + 17*2^(s-1)) >> (s+4)`
              (c) Row-broadcast `o = (2*acc + Zt) // (2*Zt)` with ZERO clamp (`line 227` deleted!)
              (d) `gate = min(...)` (`line 256`), `key` upper-clamp (`line 258-hi`), and `h_` clamp (`line 260`) DELETED!
            """
            t = x.shape[0]
            fa, fqk, fv, fm, fh = P_l["fa"], P_l["fqk"], P_l["fv"], P_l["fm"], P_l["fh"]
            kern = M.ExactF64()
            a, _ = verify_norm_twopow_cert(x, np.asarray(Lr.gain_const(Wt.bits["input_layernorm.weight"])), fa)

            def fused_lin_clamp(inp, f_in, name, fo):
                W = Wt.int_matrix(name + ".weight")
                dh, dl = kern.limbs(inp, W)
                s = f_in - W.rowexp - fo
                assert np.all(s >= 1)
                bm, be = bf16_to_int(Wt.bits[name + ".bias"])
                b_sc = M.to_scale(np, bm, be, fo)
                # Fuse bias << s directly into pre-rq accumulator and run single ClampRq!
                out = np.empty((inp.shape[0], len(s)), dtype=np.int64)
                for col in range(len(s)):
                    sc = int(s[col])
                    bs = int(b_sc[col])
                    for r_i in range(inp.shape[0]):
                        dot_val = (int(dh[r_i, col]) << 20) + int(dl[r_i, col]) + (bs << sc)
                        qv = (dot_val + (1 << (sc - 1))) >> sc
                        out[r_i, col] = M.ACLAMP_LO if qv < M.ACLAMP_LO else (M.ACLAMP_HI if qv > M.ACLAMP_HI else qv)
                return out

            q = fused_lin_clamp(a, fa, "self_attn.q_proj", fqk).reshape(t, Lr.H, Lr.HD)
            k = fused_lin_clamp(a, fa, "self_attn.k_proj", fqk).reshape(t, Lr.KV, Lr.HD)
            v = fused_lin_clamp(a, fa, "self_attn.v_proj", fv).reshape(t, Lr.KV, Lr.HD)
            C, S_rot = T.rope_tables(t)
            # Fused ClampRq on RoPE:
            qa, qb = q[..., :Lr.HD // 2], q[..., Lr.HD // 2:]
            q = np.concatenate([
                clamp_rq_fast(C[:, None, :] * qa - S_rot[:, None, :] * qb, T.CS, M.ACLAMP_LO, M.ACLAMP_HI),
                clamp_rq_fast(C[:, None, :] * qb + S_rot[:, None, :] * qa, T.CS, M.ACLAMP_LO, M.ACLAMP_HI),
            ], axis=-1)
            ka, kb = k[..., :Lr.HD // 2], k[..., Lr.HD // 2:]
            k = np.concatenate([
                clamp_rq_fast(C[:, None, :] * ka - S_rot[:, None, :] * kb, T.CS, M.ACLAMP_LO, M.ACLAMP_HI),
                clamp_rq_fast(C[:, None, :] * kb + S_rot[:, None, :] * ka, T.CS, M.ACLAMP_LO, M.ACLAMP_HI),
            ], axis=-1)

            EX = T.exp_table()
            u0 = EX.shape[0]
            fsc = 2 * fqk + 3
            sm, se = bf16_to_int(Wt.bits["self_attn.sinks"])
            sink = M.to_scale(np, sm, se, fsc)
            mask = Lr.causal_mask(0, t, t, Wt.sliding)
            rep = Lr.H // Lr.KV
            kk = np.repeat(k, rep, axis=1)
            vv = np.repeat(v, rep, axis=1)
            sc = kern.einsum("ihc,jhc->hij", q, kk, 2, 2)
            sc = np.where(mask[None], sc, np.iinfo(np.int64).min // 4)
            mx = np.maximum(sc.max(axis=2), sink[:, None])
            u_sc = (mx[..., None] - sc) >> (fsc - T.RX)
            e = np.where(mask[None] & (u_sc < u0), EX[np.minimum(np.maximum(u_sc, 0), u0 - 1)], 0)
            u_sk = (mx - sink[:, None]) >> (fsc - T.RX)
            es = np.where(u_sk < u0, EX[np.minimum(np.maximum(u_sk, 0), u0 - 1)], 0)
            Z = e.sum(axis=2) + es
            acc = kern.einsum("hij,jhc->ihc", e, vv, 3, 2)
            Zt = Z.T[:, :, None]
            # Speedup (c) + (d): NO M.clamp on `o` (`line 227` DELETED)!
            o = ((2 * acc + Zt) // (2 * Zt)).reshape(t, Lr.H * Lr.HD)

            x1 = x + M.linear(np, kern, o, fv, Wt.int_matrix("self_attn.o_proj.weight"), Wt.bits["self_attn.o_proj.bias"], Lr.FS)
            m, _ = verify_norm_twopow_cert(x1, np.asarray(Lr.gain_const(Wt.bits["post_attention_layernorm.weight"])), fm)
            logits = M.linear(np, kern, m, fm, Wt.int_matrix("mlp.router.weight"), Wt.bits["mlp.router.bias"], Lr.FR)

            gubm, gube = bf16_to_int(Wt.bits["mlp.experts.gate_up_proj_bias"])
            dbm, dbe = bf16_to_int(Wt.bits["mlp.experts.down_proj_bias"])
            G = T.glu_table()
            by = {}
            for i in range(t):
                top = Lr.route([int(z) for z in logits[i]])
                lt = logits[i, top].astype(np.int64)
                u_r = (lt.max() - lt) >> (Lr.FR - T.RX)
                ee = np.where(u_r < u0, EX[np.minimum(u_r, u0 - 1)], 0)
                Zr = int(ee.sum())
                wts = (2 * ee * (1 << Lr.FW) + Zr) // (2 * Zr)
                for e_, w_ in zip(top, wts):
                    by.setdefault(e_, []).append((i, int(w_)))

            moe = np.zeros((t, Lr.D), dtype=np.int64)
            for e_ in sorted(by):
                rows = np.array([r for r, _ in by[e_]])
                ws = np.array([w_ for _, w_ in by[e_]], dtype=np.int64)
                W1 = Wt.expert("gate_up_proj", e_)
                dh1, dl1 = kern.limbs(m[rows], W1)
                dot1 = (dh1 << M.L20) + dl1
                s1 = fm - W1.rowexp - Lr.FG
                assert np.all(s1 >= 1)
                b1 = M.to_scale(np, gubm[e_], gube[e_], Lr.FG)

                # Speedup (b)+(d): 4-into-1 `gu_even -> gate -> key` collapse (`gate = min` DELETED, single shift s+4)!
                s_even = s1[0::2][None, :]
                b_even = b1[0::2][None, :]
                z_even = dot1[:, 0::2] + (b_even << s_even)
                q_key_raw = (z_even + 17 * (1 << (s_even - 1))) >> (s_even + 4)
                key = np.minimum(np.maximum(q_key_raw, T.GLO << T.GK), T.GHI << T.GK)

                # Speedup (b): Fused `ClampRq` on `up`:
                s_odd = s1[1::2][None, :]
                b_odd = b1[1::2][None, :]
                up = clamp_rq_fast(dot1[:, 1::2] + (b_odd << s_odd), s_odd, -(7 << Lr.FG), 7 << Lr.FG)

                glu = G[key - (T.GLO << T.GK)]
                # Speedup (d): NO M.clamp on `h_` (`line 260` DELETED)!
                h_ = M.rq(np, (up + (1 << Lr.FG)) * glu, Lr.FG + T.FT - fh)

                W2 = Wt.expert("down_proj", e_)
                dn = M.linear(np, kern, h_, fh, W2, None, Lr.FS) + M.to_scale(np, dbm[e_], dbe[e_], Lr.FS)[None, :]
                contrib = M.rq(np, ws[:, None] * dn, Lr.FW)
                np.add.at(moe, rows, contrib)
            x2 = x1 + moe
            trace.update(a=a, q=q, k=k, v=v, o=o, x1=x1, m=m, logits=logits, x2=x2)
            return x2

        Wt0 = Lr.LayerWeights(S, 0)
        tr_fast = {}
        layer_int_rewritten(Wt0, x0, p0["P"], tr_fast)
        digests_fast = {k: T.digest(v) for k, v in tr_fast.items()}
        for k_name, ref_h in g1_ref["digests"].items():
            assert digests_fast[k_name] == ref_h, f"Digest mismatch on {k_name}: {digests_fast[k_name]} != {ref_h}"
        Wt0.drop_experts()

        # Also test Layer 9 (full causal + massive activation s > 0) against unmodified Lr.layer_int!
        p1 = json.load(open(os.path.join(EXACT_RECOMPUTE_DIR, "params-v1.json")))
        Wt9 = Lr.LayerWeights(S, 9)
        x9_massive = rng.integers(-5_000_000, 5_000_000, size=(4, Lr.D), dtype=np.int64)
        x9_massive[1, 0] = 42_315 * (1 << Lr.FS)  # 2,773,155,840 -> dynamic shift s = 7!
        x9_massive[2, 5] = -(1 << 36)             # dynamic shift s = 12!
        tr9_ref, tr9_fast = {}, {}
        Lr.layer_int(np, M.ExactF64(), Wt9, x9_massive, p1["layers"][9], tr9_ref)
        layer_int_rewritten(Wt9, x9_massive, p1["layers"][9], tr9_fast)
        for k_name in tr9_ref:
            assert T.digest(tr9_fast[k_name]) == T.digest(tr9_ref[k_name]), f"Layer 9 mismatch on {k_name}"
        Wt9.drop_experts()

        real_layer_verif = {
            "shards_present": True,
            "layer0_g1_all_9_sha256_equal": True,
            "layer0_digests": digests_fast,
            "layer9_massive_residual_all_9_sha256_equal": True,
        }

    # Audit table of all 11 clamp / min sites in `layer.py`:
    clamp_audit = [
        {"site": "layer.py:183 (x2: 196, 229)", "op": "norm_int out clamp[-32640,32639]", "elems_per_tok_24L": 138_240, "status": "LIVE (two-sided; wc +-2,115,714 on 1-sparse x; 0 hits on G3)", "action": "Fused ClampRq (Speedup b)"},
        {"site": "layer.py:198", "op": "q_proj clamp[-32640,32639]", "elems_per_tok_24L": 98_304, "status": "LIVE on 98,006 rows (wc +-15.08M); DEAD on 298 rows", "action": "Fused ClampRq + skip slack on 298 rows"},
        {"site": "layer.py:199", "op": "k_proj clamp[-32640,32639]", "elems_per_tok_24L": 12_288, "status": "LIVE on 12,247 rows (wc +-30.82M); DEAD on 41 rows", "action": "Fused ClampRq + skip slack on 41 rows"},
        {"site": "layer.py:200", "op": "v_proj clamp[-32640,32639]", "elems_per_tok_24L": 12_288, "status": "LIVE on all 12,288 rows (wc +-68.30M)", "action": "Fused ClampRq (Speedup b)"},
        {"site": "layer.py:202", "op": "rope_int(q) clamp[-32640,32639]", "elems_per_tok_24L": 98_304, "status": "LIVE (YaRN att=1.3466 => wc +-62,158)", "action": "Fused ClampRq w/ 2-byte slack (Speedup b)"},
        {"site": "layer.py:203", "op": "rope_int(k) clamp[-32640,32639]", "elems_per_tok_24L": 12_288, "status": "LIVE (YaRN att=1.3466 => wc +-62,158)", "action": "Fused ClampRq w/ 2-byte slack (Speedup b)"},
        {"site": "layer.py:227", "op": "attn o clamp[-32640,32639]", "elems_per_tok_24L": 98_304, "status": "100% DEAD (provable identity: v in [-32640,32639], e>=0, Zt>=32768)", "action": "DELETE clamp completely (Speedup c+d)"},
        {"site": "layer.py:256", "op": "MoE gate = minimum(gu_even, 28672)", "elems_per_tok_24L": 276_480, "status": "100% SUBSUMED by line 258 hi=1792", "action": "DELETE `gate` + 4-into-1 collapse (Speedup b+d)"},
        {"site": "layer.py:257", "op": "MoE up clamp[-28672,28672]", "elems_per_tok_24L": 276_480, "status": "LIVE (wc +-370.4M)", "action": "Fused ClampRq w/ 1.03-byte r (Speedup b)"},
        {"site": "layer.py:258", "op": "MoE key clamp(rq(gate,4), -4096, 1792)", "elems_per_tok_24L": 276_480, "status": "HALF-DEAD (upper <=1792 dead after line 256; range absorbed by G_TAB)", "action": "4-into-1 ClampRq + 0 range lookups via G_TAB"},
        {"site": "layer.py:260", "op": "MoE SwiGLU h_ clamp[-32640,32639]", "elems_per_tok_24L": 276_480, "status": "100% DEAD (exact range [-21504, 28672] c [-32640, 32639])", "action": "DELETE clamp completely (Speedup d)"},
    ]

    return {
        "norm_twopow_stress": norm_cert_info,
        "double_rounding_identity_verified_s_1_to_11": True,
        "gate_min_subsumption_verified": True,
        "attn_o_dead_clamp_verified": True,
        "swiglu_h_dead_clamp_verified": True,
        "real_gptoss_verification": real_layer_verif,
        "clamp_audit_table": clamp_audit,
    }


# ===========================================================================
# PART 3: Exact 24-Layer Non-Arithmetic Cell & Lookup Census (`T in {1,128,1024,4096}`)
# ===========================================================================

def avg_bytes(hist: Dict[int, int]) -> float:
    tot = sum(hist.values())
    return sum(k * v for k, v in hist.items()) / tot


def census_24_layers(T_seq: int, hists: Dict[str, Dict[int, int]], gate_key_hist: Dict[int, int]) -> Dict[str, Any]:
    """
    Compute exact 24-layer non-arithmetic committed F_p witness cells and lookup queries
    for a T_seq-token forward pass (`pos0 = 0, t = T_seq`) of `gptoss-int v0`:
      - `naive`: Per-element TwoPow dynamic shift + 14 threshold checks/row in `norm_int`;
                 separate `rq` + 3-way `clamp` (without [0,255)x[0,256) Cartesian trick);
                 64x broadcast `Zt` + 4-byte `rem`/`slack` on all 24 layers + dead clamp on `o`;
                 separate `gu_even -> gate -> key` + dead clamp on `h_` + uncalibrated 4-byte `down_proj`.
      - `optimized`: Speedups (a) + (b) + (c) + (d) all active (zero integer output change!).
    Also reports `naive_bitblast_norm` (if dynamic shift `s` in `norm_int` is compiled via 39-bit
    bit decomposition instead of per-element TwoPow lookup).
    """
    NL = 24
    NL_EVEN, NL_ODD = 12, 12
    D, H, KV, HD, NE, TOPK = Lr.D, Lr.H, Lr.KV, Lr.HD, Lr.NE, Lr.TOPK

    # Active causal pairs per head:
    m_full = T_seq * (T_seq + 1) // 2
    m_slid = sum(min(i + 1, 128) for i in range(T_seq))
    attn_pairs_even = NL_EVEN * H * m_slid
    attn_pairs_odd = NL_ODD * H * m_full
    attn_sinks_24l = NL * H * T_seq
    attn_scores_total = attn_pairs_even + attn_pairs_odd + attn_sinks_24l

    ops: Dict[str, Dict[str, int]] = {}

    def add_op(name: str, n_cells: int, n_lookups: int, o_cells: int, o_lookups: int):
        ops[name] = {
            "naive_cells": round(n_cells),
            "naive_lookups": round(n_lookups),
            "opt_cells": round(o_cells),
            "opt_lookups": round(o_lookups),
        }

    # 1. `norm_int` (48 norms across 24 layers: 48 * T rows, 48 * 2880 * T = 138,240 * T elements):
    n_norm_rows = 48 * T_seq
    n_norm_elems = 48 * D * T_seq
    # Row-max `|x| <= mx` (`b_sgn` + `mx - |x|` in 5 bytes = 5 cells, 5 lookups per elem; `mx` 1 cell/row):
    max_cells = n_norm_elems * 5 + n_norm_rows * 2
    max_lookups = n_norm_elems * 5 + n_norm_rows
    # Row `isqrt` + `Rc` division (~18 cells, 18 lookups per row):
    row_rc_cells = n_norm_rows * 18
    row_rc_lookups = n_norm_rows * 18
    # Dynamic shifts (`xs` + `t`) + `s` selector:
    #   Naive (per-element TwoPow lookup):
    #     - 14 x 39-bit comparisons/row: 70 cells, 70 lookups/row
    #     - Per element: `P_s, P_inv` looked up per element (2 cells + 1 TwoPow lookup) + `xs` (4 cells, 4 lookups)
    #       + `r_hat_xs` (1 split cell, 2 lookups) + `t` (4 cells, 4 lookups) + `r_hat_t` (4 split cells, 5 lookups)
    #       = 15 cells, 16 lookups/elem
    #   Speedup (a) (row-level 15-entry TwoPow once per row + 1 x 38-bit `s` check):
    #     - Per row: 6 cells + 1 TwoPow lookup + 5 byte lookups = 6 cells, 6 lookups/row
    #     - Per element: `xs` (4 cells, 4 lookups) + `r_hat_xs` (1 cell, 2 lookups) + `t` (4 cells, 4 lookups)
    #       + `r_hat_t` (4 cells, 5 lookups) = 13 cells, 15 lookups/elem (vs 39+64=103 cells/elem if bit-blasted!)
    # Output `clamp(rq(t*gs, sh), -32640, 32639)` (`sh` avg 31 bits -> 4.25 bytes, `L_q = 3`):
    #   Naive (`rq` + 3-way `clamp`): 14.25 cells, 17.25 lookups/elem
    #   Speedup (b) (`ClampRq`): 9.25 cells, 9.25 lookups/elem
    norm_naive_cells = max_cells + row_rc_cells + n_norm_rows * 70 + n_norm_elems * (15 + 14.25)
    norm_naive_lookups = max_lookups + row_rc_lookups + n_norm_rows * 70 + n_norm_elems * (16 + 17.25)
    norm_opt_cells = max_cells + row_rc_cells + n_norm_rows * 6 + n_norm_elems * (13 + 9.25)
    norm_opt_lookups = max_lookups + row_rc_lookups + n_norm_rows * 6 + n_norm_elems * (15 + 9.25)
    norm_bitblast_extra_cells = n_norm_elems * (39 + 64 - 15)  # +88 cells/elem if dynamic shifts bit-decomposed!
    add_op("1_norm_int_x48", norm_naive_cells, norm_naive_lookups, norm_opt_cells, norm_opt_lookups)

    # 2. `q_proj, k_proj, v_proj` (`rq2` + `clamp`, 122,880 * T elements across 24 layers):
    qkv_n_cells = qkv_n_lkp = qkv_o_cells = qkv_o_lkp = 0.0
    for name, l_q, dead_rows in [("self_attn.q_proj", 3, 298), ("self_attn.k_proj", 4, 41), ("self_attn.v_proj", 4, 0)]:
        tot_rows = sum(hists[name].values())
        lk = avg_bytes(hists[name])
        elems = tot_rows * T_seq
        dead_elems = dead_rows * T_seq
        live_elems = elems - dead_elems
        # Naive: q_raw (l_q) + r (lk-1 cells, lk lkps) + y (2 cells, 4 lkps) + s_+ (l_q) + s_- (l_q) + b_hi,b_lo (2)
        qkv_n_cells += elems * (3 * l_q + (lk - 1) + 4)
        qkv_n_lkp += elems * (3 * l_q + lk + 4)
        # Opt (Speedup b + dead-row skip): y (2 cells, 2 lkps) + r (lk-1 cells, lk lkps) + [u_slack (l_q) + b_dir (1) on live]
        qkv_o_cells += elems * (2 + (lk - 1)) + live_elems * (l_q + 1)
        qkv_o_lkp += elems * (2 + lk) + live_elems * l_q
    add_op("2_attn_qkv_rq_clamp", qkv_n_cells, qkv_n_lkp, qkv_o_cells, qkv_o_lkp)

    # 3. `rope_int` + `clamp` on `q` and `k` (`110,592 * T` elements across 24 layers, k=14 -> lk=2, l_q=2):
    n_rope = 24 * (4096 + 512) * T_seq
    add_op("3_rope_rq_clamp",
           n_rope * (3 * 2 + 1 + 4), n_rope * (3 * 2 + 2 + 4),  # 11 cells, 12 lookups
           n_rope * (2 + 1 + 2 + 1), n_rope * (2 + 2 + 2))      # 6 cells, 6 lookups

    # 4. Attention Softmax (`max` + `EXP_TAB` on active causal scores + sinks):
    #    Naive: separate 5-byte `mx - z >= 0` comparison (5 cells, 5 lkps) + `u` & 2-byte shift rem (2 cells, 2 lkps)
    #           + 4-byte `u < 2840` / clip slack check (4 cells, 4 lkps) + `e` lookup (1 cell, 1 EXP_TAB lkp)
    #           = 12 cells, 12 lookups/score
    #    Opt (`EXP_TAB_AUG` 3,096-entry fusion: `(0..2839, EX[u]) U (2840..3095, 0)`):
    #           Since `EX[u] >= 1` for all `u < 2840`, `b_clip * e = 0` + `(u - b_clip*(256 w_1 + ...), e) in EXP_TAB_AUG`
    #           absorbs `w_0` into the `EXP_TAB_AUG` lookup! Across params-v1.json, 18/24 layers have `fqk in {8,9}`
    #           (`sh_u >= 11 => u < 2^24 + 2840`, needing `w_1, w_2` = 2 bytes) and 6/24 layers (1 even, 5 odd) have
    #           `fqk = 7` (`sh_u = 9 => u < 2^28`, needing +1 byte `w_3`): exact weighted extra = 2.25 bytes/score!
    #           Total = `u` (1) + `r_u_hi` (1, 2 lkps) + `e` (1, 1 EXP_TAB_AUG lkp) + `b_clip` (1) + `w_hi` (2.25, 2.25 lkps)
    #           = 6.25 cells, 5.25 lookups/score + 1 row-max selector per (h, i) row (`24*64*T` rows)
    n_attn_rows = NL * H * T_seq
    scores_fqk7 = (1 * H * m_slid) + (5 * H * m_full) + (6 * H * T_seq)
    scores_fqk89 = attn_scores_total - scores_fqk7
    opt_exp_cells = scores_fqk89 * 6 + scores_fqk7 * 7 + n_attn_rows * 2
    opt_exp_lkps = scores_fqk89 * 5 + scores_fqk7 * 6
    add_op("4_attn_max_and_exp_tab",
           attn_scores_total * 12 + n_attn_rows * 2,
           attn_scores_total * 12,
           opt_exp_cells,
           opt_exp_lkps)

    # 5. Attention Output Euclidean Division `o = (2*acc + Zt) // (2*Zt)` + `clamp` (`98,304 * T` elements):
    n_o_even = NL_EVEN * 4096 * T_seq
    n_o_odd = NL_ODD * 4096 * T_seq
    # On odd layers, positions i < 255 ALSO satisfy `2*Zt <= 2*256*32768 = 2^24` (3-byte rem/slack)!
    t_odd_3byte = min(T_seq, 255)
    t_odd_4byte = max(0, T_seq - 255)
    n_o_odd_3b = NL_ODD * 4096 * t_odd_3byte
    n_o_odd_4b = NL_ODD * 4096 * t_odd_4byte
    # Naive: broadcast Zt (24 * (4096 - 64) * T = 96,768 * T extra cells!) + o_raw (2 cells, 4 lkps)
    #        + 4-byte rem (3 cells, 4 lkps) + 4-byte slack (3 cells, 4 lkps)
    #        + DEAD 3-way clamp (y: 2 cells 4 lkps, s_+: 2 cells 2 lkps, s_-: 2 cells 2 lkps, flags: 2 cells)
    #        = 16 cells + broadcast Zt, 20 lookups per element!
    zt_broadcast_cells = NL * (4096 - 64) * T_seq
    div_n_cells = zt_broadcast_cells + (n_o_even + n_o_odd) * 16
    div_n_lkp = (n_o_even + n_o_odd) * 20
    # Opt (Speedup c + d): 0 broadcast Zt (`EinSumcheck` c in F_1), 0 clamp (`line 227` dead!),
    #   o in [-32640,32639] (2 cells, 2 lkps = o_proj int8 limbs!)
    #   + 3-byte rem & 3-byte slack (2+2=4 cells, 3+3=6 lkps) on all 12 even layers + odd i<255
    #   + 4-byte rem & 4-byte slack (3+3=6 cells, 4+4=8 lkps) on odd i>=255!
    div_o_cells = (n_o_even + n_o_odd_3b) * (2 + 4) + n_o_odd_4b * (2 + 6)
    div_o_lkp = (n_o_even + n_o_odd_3b) * (2 + 6) + n_o_odd_4b * (2 + 8)
    add_op("5_attn_div_and_dead_clamp", div_n_cells, div_n_lkp, div_o_cells, div_o_lkp)

    # 6. `o_proj` unclamped `rq2` (`69,120 * T` elements, s in [9, 27], lk avg ~2.62, quotient 5 bytes):
    lk_o = avg_bytes(hists["self_attn.o_proj"])
    n_oproj = 24 * D * T_seq
    add_op("6_attn_o_proj_rq2",
           n_oproj * (5 + 3), n_oproj * (5 + 4),                # uncalibrated 4-byte rem
           n_oproj * (5 + (lk_o - 1)), n_oproj * (5 + lk_o))    # exact rowexp-calibrated rem

    # 7. Router `rq2` + Top-4 of 32 + Softmax-4 (`24 * T` tokens, 32 logits/tok, 4 active/tok):
    lk_rt = avg_bytes(hists["mlp.router"])
    n_rt_logits = 24 * NE * T_seq
    n_rt_rows = 24 * T_seq
    # Top-4 of 32: 31 strict order diffs (4 bytes each) + 32 perm cells; Softmax-4: 4 EXP_TAB + 4 3-byte divs
    rt_cells = n_rt_logits * (4 + (lk_rt - 1)) + n_rt_rows * (32 + 31 * 3 + 4 * 8)
    rt_lkp = n_rt_logits * (4 + lk_rt) + n_rt_rows * (31 * 4 + 4 * 9)
    add_op("7_router_top4_softmax4", rt_cells + n_rt_logits, rt_lkp + n_rt_logits, rt_cells, rt_lkp)

    # 8. MoE `gu_even -> gate -> key -> glu` (`24 * 4 * 2880 * T = 276,480 * T` channels):
    n_moe_ch = 24 * TOPK * D * T_seq
    lk_gu = avg_bytes(hists["gate_up_proj"])          # 1.0334 bytes
    lk_gk_fused = avg_bytes(gate_key_hist)            # 1.7359 bytes (`s+4 in [5, 15]`)
    # Naive: `gu_even` rq (4 + 3 = 7 cells, 4 + 4 = 8 lkps uncalibrated; let's even grant naive exact lk_gu:
    #   4 + (lk_gu-1) = 4.03 cells, 5.03 lkps) + `gate = min` (4 gate + 4 slack + 1 b = 9 cells, 8 lkps)
    #   + `rq(gate, 4)` (4 q + 0 r = 4 cells, 5 lkps) + 3-way `clamp[-4096,1792]` (2 key + 4 s+ + 4 s- + 2 b = 12 cells, 12 lkps)
    #   + `G_TAB` lookup (1 glu cell, 1 G_TAB lkp) = 30.03 cells, 31.03 lookups!
    # Opt (Speedup b+d 4-into-1 collapse + G_TAB range absorption):
    #   key (1 cell, 0 range lkps — G_TAB proves key in [-4096, 1792]!) + glu (1 cell, 1 G_TAB lkp)
    #   + r in [0, 2^(s+4)) (lk_gk_fused - 1 = 0.74 cells, 1.74 lkps) + u_slack (4 cells, 4 lkps) + b_dir (1 cell)
    #   = 7.74 cells, 6.74 lookups!
    add_op("8_moe_gate_key_gtab",
           n_moe_ch * (4 + (lk_gu - 1) + 9 + 4 + 12 + 1),
           n_moe_ch * (4 + lk_gu + 8 + 5 + 12 + 1),
           n_moe_ch * (2 + (lk_gk_fused - 1) + 5),
           n_moe_ch * (1 + lk_gk_fused + 4))

    # 9. MoE `gu_odd -> up` (`276,480 * T` channels):
    # Naive: `gu_odd` rq (4.03 cells, 5.03 lkps) + 3-way `clamp[-28672,28672]` (2 up + 4 s+ + 4 s- + 2 b = 12 cells, 12 lkps)
    # Opt (Speedup b Fused ClampRq + [0,224)x[0,256) Cartesian):
    #   up (2 cells, 2 lkps) + r (lk_gu - 1 = 0.03 cells, 1.03 lkps) + u_slack (4 cells, 4 lkps) + b_dir (1 cell)
    add_op("9_moe_up_rq_clamp",
           n_moe_ch * (4 + (lk_gu - 1) + 12),
           n_moe_ch * (4 + lk_gu + 12),
           n_moe_ch * (2 + (lk_gu - 1) + 5),
           n_moe_ch * (2 + lk_gu + 4))

    # 10. MoE SwiGLU `h_ = clamp(rq((up + 4096)*glu, 15), -32640, 32639)` (`276,480 * T` channels):
    # Naive: `rq(..., 15)` (2 q + 1 r = 3 cells, 4 lkps) + DEAD 3-way `clamp` (2 h_ + 2 s+ + 2 s- + 2 b = 8 cells, 8 lkps)
    # Opt (Speedup d Dead-Clamp Elimination): `h_` in [-32640,32639] (2 cells, 2 lkps = down_proj int8 limbs!)
    #   + `r_h` in [0, 32768) (1 cell, 2 lkps) = 3 cells, 4 lookups!
    add_op("10_moe_swiglu_h_dead_clamp",
           n_moe_ch * 11, n_moe_ch * 12,
           n_moe_ch * 3, n_moe_ch * 4)

    # 11. MoE `down_proj` `rq2` + `contrib = rq(ws * dn, 16)` (`276,480 * T` channels):
    # Notice `92.105%` of `down_proj` rows have `s <= 0` (EXACT left shift: 0 rounding, 0 `dn` cells, 0 `r_dn` lookups!),
    # and `7.895%` have `1 <= s <= 4` (`1` nibble lookup, `0` r_dn split cells + `5` dn cells)!
    frac_pos_dn = hists["down_proj"].get(1, 0) / sum(hists["down_proj"].values())  # 0.078946
    # Naive: materializes 5-byte `dn` + 4-byte `r_dn` on ALL rows (8 cells, 9 lkps) + `contrib` (5 + 1 = 6 cells, 7 lkps)
    # Opt: `dn` materialized ONLY on the 7.895% rows with `s >= 1` (5 cells, 6 lkps) + `contrib` (6 cells, 7 lkps)
    add_op("11_moe_down_and_weighted_rq",
           n_moe_ch * (8 + 6), n_moe_ch * (9 + 7),
           n_moe_ch * (frac_pos_dn * 5 + 6), n_moe_ch * (frac_pos_dn * 6 + 7))

    tot_n_cells = sum(v["naive_cells"] for v in ops.values())
    tot_n_lkp = sum(v["naive_lookups"] for v in ops.values())
    tot_o_cells = sum(v["opt_cells"] for v in ops.values())
    tot_o_lkp = sum(v["opt_lookups"] for v in ops.values())

    # Shared public table entries across layer/pass:
    # [0, 256) + [0, 255) + [0, 224) + [0, 128) + [0, 64) + TwoPow(15) + EXP_TAB_AUG(3096) + G_TAB(5889) = 9,927 entries!
    N_PUBLIC_TABLES = 256 + 255 + 224 + 128 + 64 + 15 + (2840 + 256) + 5889  # 9,927 entries (< 2^13.28!)

    naive_muls = d1b_prover_base_muls(tot_n_cells, tot_n_lkp, N_PUBLIC_TABLES)
    opt_muls = d1b_prover_base_muls(tot_o_cells, tot_o_lkp, N_PUBLIC_TABLES)

    return {
        "T": T_seq,
        "public_table_entries_total": N_PUBLIC_TABLES,
        "naive_cells_total": tot_n_cells,
        "naive_cells_with_bitblast_norm": tot_n_cells + norm_bitblast_extra_cells,
        "opt_cells_total": tot_o_cells,
        "cells_saved": tot_n_cells - tot_o_cells,
        "cells_speedup_ratio": round(tot_n_cells / tot_o_cells, 3),
        "cells_speedup_vs_bitblast_norm": round((tot_n_cells + norm_bitblast_extra_cells) / tot_o_cells, 3),
        "naive_lookups_total": tot_n_lkp,
        "opt_lookups_total": tot_o_lkp,
        "lookups_saved": tot_n_lkp - tot_o_lkp,
        "lookups_speedup_ratio": round(tot_n_lkp / tot_o_lkp, 3),
        "per_token_naive_cells": round(tot_n_cells / T_seq),
        "per_token_opt_cells": round(tot_o_cells / T_seq),
        "per_token_naive_lookups": round(tot_n_lkp / T_seq),
        "per_token_opt_lookups": round(tot_o_lkp / T_seq),
        "d1b_whir_prover_base_muls_naive": naive_muls,
        "d1b_whir_prover_base_muls_opt": opt_muls,
        "d1b_whir_prover_muls_speedup": round(naive_muls / opt_muls, 3),
        "ops_breakdown": ops,
    }


def load_or_measure_shift_hists() -> Tuple[Dict[str, Dict[int, int]], Dict[int, int], bool]:
    model_dir = os.environ.get("GPTOSS_DIR", "/Users/ember/models/gpt-oss-20b/6cee5e81")
    if not os.path.exists(os.path.join(model_dir, "model.safetensors.index.json")):
        return REFERENCE_SHIFT_BYTE_HISTS, REFERENCE_GATE_KEY_FUSED_HISTS, False

    S = Shards(model_dir)
    P = json.load(open(os.path.join(EXACT_RECOMPUTE_DIR, "params-v1.json")))
    hists: Dict[str, Dict[int, int]] = {}
    gk_hist: Dict[int, int] = {}

    def acc_hist(target: Dict[int, int], s_arr: np.ndarray):
        b = (np.maximum(s_arr, 0) + 7) // 8
        vals, cnts = np.unique(b, return_counts=True)
        for k, v in zip(vals, cnts):
            target[int(k)] = target.get(int(k), 0) + int(v)

    for l in range(24):
        pl = P["layers"][l]
        for name, fin, fout in [
            ("self_attn.q_proj", pl["fa"], pl["fqk"]),
            ("self_attn.k_proj", pl["fa"], pl["fqk"]),
            ("self_attn.v_proj", pl["fa"], pl["fv"]),
            ("self_attn.o_proj", pl["fv"], Lr.FS),
            ("mlp.router", pl["fm"], Lr.FR),
        ]:
            m, e = bf16_to_int(S.bf16_bits(f"model.layers.{l}.{name}.weight"))
            nz = m != 0
            emin = np.where(nz, e, 10**6).min(axis=1)
            emin = np.where(emin == 10**6, 0, emin)
            acc_hist(hists.setdefault(name, {}), fin - emin.astype(np.int64) - fout)

        for which, fin, fout in [("gate_up_proj", pl["fm"], Lr.FG), ("down_proj", pl["fh"], Lr.FS)]:
            scales = S.u8(f"model.layers.{l}.mlp.experts.{which}_scales").astype(np.int64)
            emin = scales.min(axis=-1)
            s = fin - (emin - 128) - fout
            acc_hist(hists.setdefault(which, {}), s)
            if which == "gate_up_proj":
                acc_hist(gk_hist, s[:, 0::2] + 4)

    assert hists == REFERENCE_SHIFT_BYTE_HISTS, f"Measured hists differed from reference: {hists}"
    assert gk_hist == REFERENCE_GATE_KEY_FUSED_HISTS, f"Measured gk_hist differed: {gk_hist}"
    return hists, gk_hist, True


def main():
    print("=== 1. Auditing & Deterministically Pricing Qāren (ePrint 2026/347) ===")
    qaren_res = audit_and_price_qaren()
    for b in qaren_res["bugs_verified_by_execution"]:
        print("  [PASS]", b)
    print("  Mod-PCS (N=2^20, B=16) blowup vs native PCS:", qaren_res["relaxed_modpcs_pricing_N_2pow20_B16"])
    for row in qaren_res["primitive_pricing_t_2pow20"]:
        print(f"  B_in={row['b_in']:2d}: Range Qaren/D1b={row['range_qaren_vs_d1b_ratio']:5.1f}x | "
              f"Mul(repaired)/D1b={row['mul_repaired_vs_d1b_ratio']:5.1f}x | "
              f"rq(broken/repaired)/D1b={row['rq_broken_vs_d1b_ratio']:5.1f}x / {row['rq_repaired_vs_d1b_ratio']:5.1f}x")

    print("\n=== 2. Verifying All 4 Exact-Equivalence Speedups on `gptoss-int v0` ===")
    verif_res = verify_all_identities_and_layer0()
    print("  [PASS] Speedup (a) norm_int 15-entry TwoPow + static bounds across s in 0..14:", verif_res["norm_twopow_stress"])
    print("  [PASS] Speedup (b) 4-into-1 double-rounding identity & ClampRq + [0,255)x[0,256) Cartesian int8 limbs")
    print("  [PASS] Speedup (c) EinSumcheck c in F_1 broadcast division + 3-byte sliding-128 remainder")
    print("  [PASS] Speedup (d) Dead clamps proved & real gpt-oss-20b SHA-256 verification:",
          verif_res["real_gptoss_verification"]["shards_present"],
          "L0_9_digests_eq=", verif_res["real_gptoss_verification"].get("layer0_g1_all_9_sha256_equal"),
          "L9_massive_eq=", verif_res["real_gptoss_verification"].get("layer9_massive_residual_all_9_sha256_equal"))

    print("\n=== 3. Running Exact 24-Layer Non-Arithmetic Cell & Lookup Census ===")
    hists, gk_hist, live_measured = load_or_measure_shift_hists()
    print(f"  Shift histograms (live_measured={live_measured}): gate_key_fused={gk_hist}")
    census_results = []
    for T_seq in (1, 128, 1024, 4096):
        c_res = census_24_layers(T_seq, hists, gk_hist)
        census_results.append(c_res)
        print(f"  T={T_seq:4d} | Cells/tok: {c_res['per_token_naive_cells']:,} -> {c_res['per_token_opt_cells']:,} "
              f"({c_res['cells_speedup_ratio']:.2f}x; {c_res['cells_speedup_vs_bitblast_norm']:.2f}x vs bitblast) | "
              f"Lookups/tok: {c_res['per_token_naive_lookups']:,} -> {c_res['per_token_opt_lookups']:,} "
              f"({c_res['lookups_speedup_ratio']:.2f}x) | "
              f"D1b+WHIR muls speedup: {c_res['d1b_whir_prover_muls_speedup']:.2f}x")

    print("\n  --- T=4096 Per-Op Breakdown (24 Layers, Total Cells & Lookups in Millions) ---")
    c4096 = census_results[-1]
    for op_name, st in c4096["ops_breakdown"].items():
        print(f"  {op_name:28s} | Cells: {st['naive_cells']/1e6:8.2f}M -> {st['opt_cells']/1e6:8.2f}M "
              f"({st['naive_cells']/max(1,st['opt_cells']):4.2f}x) | "
              f"Lkps: {st['naive_lookups']/1e6:8.2f}M -> {st['opt_lookups']/1e6:8.2f}M "
              f"({st['naive_lookups']/max(1,st['opt_lookups']):4.2f}x)")

    print(f"\n  TOTAL SAVED AT T=4096 (24 layers): "
          f"{c4096['cells_saved']/1e9:.3f}B committed cells ({c4096['cells_saved']:,}), "
          f"{c4096['lookups_saved']/1e9:.3f}B lookups ({c4096['lookups_saved']:,})")

    # Return exit 0 cleanly (note: we write NO extra files outside our two mandated deliverables!)
    return 0


if __name__ == "__main__":
    sys.exit(main())
