#!/usr/bin/env python3
"""
rank1_prod_exp.py -- Algebraic rank verification, overflow/hardware boundary falsification,
synthetic Softmax sweep (up to context L=4096), and real 24-layer `gpt-oss-20b` fidelity
evaluation of Zero-Rescale Rank-1 Product `exp` (`Rank1ProdExp`) vs. `gptoss-int v0` exact
table vs. `zkTransformer`'s cubic Taylor `StructuredExp`.
"""

import csv
import json
import math
import os
import sys
import time
from typing import Dict, Any, Tuple, List
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXACT_RECOMP_DIR = os.path.abspath(os.path.join(HERE, "../../exact_recompute_2026_11_06"))
PHASE0_DIR = os.path.abspath(os.path.join(HERE, "../../../phase0"))
sys.path.insert(0, EXACT_RECOMP_DIR)

import tables as T  # gptoss-int v0 pinned tables (RX=8, EXPS=15)

BABYBEAR_P = (1 << 31) - (1 << 27) + 1  # 2013265921
GOLDILOCKS_P = (1 << 64) - (1 << 32) + 1


# ---------------------------------------------------------------------------
# 1. Exact Rank over F_p (same Gaussian elimination as phase0/bf16_tables.py)
# ---------------------------------------------------------------------------
def rank_mod_p(M: np.ndarray, p: int = BABYBEAR_P) -> int:
    A = (np.asarray(M, dtype=np.int64) % p).copy()
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + int(nz[0])
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        below = np.nonzero(A[r + 1:, c])[0]
        if below.size:
            idx = r + 1 + below
            factors = A[idx, c].reshape(-1, 1)
            A[idx] = (A[idx] - factors * A[r].reshape(1, -1)) % p
        r += 1
    return r


def find_first_nonzero_2x2_minor(M: np.ndarray, p: int = BABYBEAR_P):
    A = np.asarray(M, dtype=np.int64)
    rows, cols = A.shape
    for i in range(min(rows, 32)):
        for j in range(i + 1, min(rows, 32)):
            for a in range(min(cols, 64)):
                for b in range(a + 1, min(cols, 64)):
                    det_z = int(A[i, a]) * int(A[j, b]) - int(A[i, b]) * int(A[j, a])
                    det_p = det_z % p
                    if det_p != 0:
                        return {"rows": [i, j], "cols": [a, b], "minor_Z": det_z, "minor_mod_p": det_p}
    return None


# ---------------------------------------------------------------------------
# 2. Nonlinearity Constructions on Non-Negative Offset u in [0, 65536) (step 2^-8)
# ---------------------------------------------------------------------------
def build_exact_q15_64k(rx: int = 8, exps: int = 15) -> np.ndarray:
    """Exact rounded Q15 exp table over u in [0, 65536): round(2^15 * exp(-u / 2^8)).
    Matches T.exp_table() identically on its support u < 2839 and is 0 on u >= 2839."""
    u = np.arange(65536, dtype=np.float64)
    tab = np.rint((2.0 ** exps) * np.exp(-u / (2.0 ** rx))).astype(np.int64)
    ex_v0 = T.exp_table()
    assert np.array_equal(tab[:len(ex_v0)], ex_v0)
    assert np.all(tab[len(ex_v0):] == 0)
    return tab


def build_rank1_subtables(s1: int, s2: int, rx: int = 8) -> Tuple[np.ndarray, np.ndarray]:
    """Two 256-entry public integer tables:
      T_hi[u_hi] = rint(2^s1 * exp(-u_hi * 256 / 2^rx))
      T_lo[u_lo] = rint(2^s2 * exp(-u_lo / 2^rx))
    Uses round-half-to-even (`np.rint`) matching `tables.py:46`."""
    u_hi = np.arange(256, dtype=np.float64)
    u_lo = np.arange(256, dtype=np.float64)
    t_hi = np.rint((2.0 ** s1) * np.exp(-u_hi * 256.0 / (2.0 ** rx))).astype(np.int64)
    t_lo = np.rint((2.0 ** s2) * np.exp(-u_lo / (2.0 ** rx))).astype(np.int64)
    return t_hi, t_lo


def eval_rank1_prod_exp(u: np.ndarray, t_hi: np.ndarray, t_lo: np.ndarray, rescale_bits: int = 0) -> np.ndarray:
    """Evaluate Rank1ProdExp on arbitrary non-negative integer array `u` (0 for u >= 65536)."""
    u_clamped = np.clip(u, 0, 65535)
    u_hi = u_clamped >> 8
    u_lo = u_clamped & 0xFF
    prod = t_hi[u_hi] * t_lo[u_lo]
    if rescale_bits > 0:
        prod = (prod + (1 << (rescale_bits - 1))) >> rescale_bits
    return np.where((u >= 0) & (u < 65536), prod, 0)


def build_structured_exp_64k(k_bits: int = 4, sf_log: int = 15, rx: int = 8) -> np.ndarray:
    """
    Exact bit-faithful integer replication of zkTransformer's `DagBuilder::exp`
    (`src/dag/builder.rs:127-130, 332-399`, `src/basicblock/exp.rs:33-56`, `src/basicblock/scale.rs:41-43`)
    at scale `s = 15`:
      - Input offset `u` at 2^-8 corresponds to Q15 negative input `x_q15 = -u * 2^(15 - 8) = -128 * u <= 0`.
      - ClampLower: `c_val = ((1 << k_bits) - 2) * ln2_sf` (at k_bits=4: `14 * 22713 = 317982`, corresponding to
        `u <= 2484.2`, i.e., clamping `exp` to `2^-14` instead of `0`! Wait: notice that in `builder.rs:129`,
        clamping at `-14 * ln 2 ≈ -9.70` leaves a NON-ZERO floor `exp(-9.70) = 2^-14 = 2` in Q15 on ALL masked/tail
        positions!! We test BOTH `builder.rs` with ClampLower AND unclamped `k_bits=8` where large k -> 0!).
      - ExpHelper: `ln2_sf = round(ln(2) * 2^15) = 22713`; `k = round(-x / ln2_sf)`; `r = x + k * ln2_sf`.
      - TwoPow: `two_pow = 2^(15 - k)` if `k <= 15` else `0`.
      - Cubic Taylor with ScaleDown(30 -> 15) (`rq(a, 15) = (a + 16384) >> 15`):
          r_sq = rq(r * r, 15)
          r_sixth = rq(r * 5461, 15)       # 5461 = floor(2^15 / 6) in builder.rs:363
          deg23 = rq((r_sixth + 16384) * r_sq, 15)
          exp_r = deg23 + r + 32768
          exp_x = rq(two_pow * exp_r, 15)
    """
    u = np.arange(65536, dtype=np.int64)
    x = -u * (1 << (sf_log - rx))  # exact Q15 integer <= 0
    ln2_sf = int(round(math.log(2.0) * (1 << sf_log)))  # 22713 at sf_log=15

    if k_bits == 4:
        # Exact builder.rs:129 ClampLower: y = max(x, -14 * ln2_sf)
        c_val = 14 * ln2_sf
        y = np.maximum(x, -c_val)
    else:
        y = x

    k = np.rint((-y.astype(np.float64)) / float(ln2_sf)).astype(np.int64)
    r = y + k * ln2_sf

    def rq15(v):
        return (v + (1 << 14)) >> 15

    two_pow = np.where((k >= 0) & (k <= 15), 1 << np.clip(15 - k, 0, 15), 0)
    r_sq = rq15(r * r)
    r_sixth = rq15(r * 5461)
    deg23 = rq15((r_sixth + 16384) * r_sq)
    exp_r = deg23 + r + 32768
    exp_x = rq15(two_pow * exp_r)
    return exp_x.astype(np.int64)


# ---------------------------------------------------------------------------
# 3. Part 1: Algebraic Rank & DecomposableTable Verification
# ---------------------------------------------------------------------------
def run_algebraic_rank_tests() -> Dict[str, Any]:
    # 1a. Reproduce Phase 0 control ([-88, 0] fixed-point exp rounded to bf16 -> rank 253 of 256)
    sys.path.insert(0, PHASE0_DIR)
    import bf16_tables as P0
    p0_ctrl_bf16 = P0.f64_to_bf16(P0.fixedpoint_exp_control()).astype(np.int64).reshape(256, 256)
    p0_rank = rank_mod_p(p0_ctrl_bf16, BABYBEAR_P)
    p0_minor_01_018 = int(p0_ctrl_bf16[0, 0]) * int(p0_ctrl_bf16[1, 18]) - int(p0_ctrl_bf16[0, 18]) * int(p0_ctrl_bf16[1, 0])

    # 1b. Exact rounded Q15 exp table `T_exact[u] = round(2^15 * exp(-u/256))` reshaped to 256 x 256
    t_exact = build_exact_q15_64k()
    M_exact = t_exact.reshape(256, 256)
    rank_exact_q15 = rank_mod_p(M_exact, BABYBEAR_P)
    minor_exact_q15 = find_first_nonzero_2x2_minor(M_exact, BABYBEAR_P)
    # Note: rows u_hi >= 12 are all zeros in M_exact (only 12 nonzero rows: u_hi = 0..11!), so max possible rank is 12!
    # Wait: LOOK AT THAT! On u in [0, 65536) with RX=8, EXPS=15, rows u_hi = 12..255 are IDENTICALLY ZERO,
    # so there are ONLY 12 NONZERO ROWS (u_hi = 0..11), and ALL 12 NONZERO ROWS ARE LINEARLY INDEPENDENT (rank 12 of 12)!
    nonzero_rows_q15 = int(np.sum(np.any(M_exact != 0, axis=1)))

    # Also check Q15 exact table when scaled to span all 256 rows (e.g. step so exp spans [-10.4, 0] across 65536 entries,
    # as in zkTransformer s=15 where u in [0, 65536) at step 2^-12 -> [-16, 0]):
    u_wide = np.arange(65536, dtype=np.float64)
    M_exact_wide = np.rint(32768.0 * np.exp(-u_wide / 4096.0)).astype(np.int64).reshape(256, 256)
    rank_exact_wide = rank_mod_p(M_exact_wide, BABYBEAR_P)
    nonzero_rows_wide = int(np.sum(np.any(M_exact_wide != 0, axis=1)))

    # 1c. Test Rank1ProdExp for (s1, s2) in {(8,8), (10,10), (15,15), (18,12)} + 1-rescale (15,15)->15
    rank1_checks = {}
    for name, s1, s2, rs in [
        ("Rank1_8_8_0rs", 8, 8, 0),
        ("Rank1_10_10_0rs", 10, 10, 0),
        ("Rank1_15_15_0rs", 15, 15, 0),
        ("Rank1_18_12_0rs", 18, 12, 0),
        ("Rank1_15_15_to_15_1rs", 15, 15, 15),
    ]:
        t_hi, t_lo = build_rank1_subtables(s1, s2)
        vals = eval_rank1_prod_exp(np.arange(65536, dtype=np.int64), t_hi, t_lo, rescale_bits=rs)
        M = vals.reshape(256, 256)
        rk = rank_mod_p(M, BABYBEAR_P)
        max_entry = int(vals.max())
        no_mod_p_wrap = max_entry < BABYBEAR_P
        outer_exact_mod_p = bool(np.array_equal(M % BABYBEAR_P, np.outer(t_hi % BABYBEAR_P, t_lo % BABYBEAR_P) % BABYBEAR_P))
        minor = find_first_nonzero_2x2_minor(M, BABYBEAR_P)
        if rs == 0:
            assert rk == 1, f"Expected rank 1 for {name}, got {rk}"
            assert outer_exact_mod_p and minor is None
            assert no_mod_p_wrap, f"Overflowed BabyBear: {max_entry} >= {BABYBEAR_P}"
        rank1_checks[name] = {
            "s1": s1,
            "s2": s2,
            "rescale_bits": rs,
            "exact_rank_mod_babybear": rk,
            "nonzero_rows": int(np.sum(np.any(M != 0, axis=1))),
            "max_entry": max_entry,
            "fits_unwrapped_in_babybear": no_mod_p_wrap,
            "is_exact_decomposable_c2_w8_alpha2_prodTable": outer_exact_mod_p,
            "first_nonzero_minor": minor,
        }

    return {
        "phase0_bf16_fixedpoint_control": {
            "exact_rank_mod_babybear": p0_rank,
            "minor_r01_c0_18": p0_minor_01_018,
        },
        "gptoss_q15_rx8_exact_64k": {
            "exact_rank_mod_babybear": rank_exact_q15,
            "nonzero_rows_of_256": nonzero_rows_q15,
            "note": "All 12 nonzero rows (u_hi=0..11) are linearly independent (full row rank 12/12) due to rounding carries!",
            "first_nonzero_minor": minor_exact_q15,
        },
        "q15_rx12_wide_exact_64k": {
            "exact_rank_mod_babybear": rank_exact_wide,
            "nonzero_rows_of_256": nonzero_rows_wide,
        },
        "rank1_prod_variants": rank1_checks,
    }


# ---------------------------------------------------------------------------
# 4. Part 2: Overflow & INT8-Limb Hardware Boundary Audit
# ---------------------------------------------------------------------------
def run_overflow_and_limb_audit() -> Dict[str, Any]:
    """Check Softmax denominator Z = sum_{j=0}^{L-1} E(u_j) and value dot `acc = sum_j E(u_j) * V_j`
    (|V_j| <= 32,639 in gptoss-int v0) across context lengths L in {32, 128, 512, 2048, 4096}."""
    v_max = 32639
    audit = {}
    for name, max_e in [
        ("Exact_Q15_or_1Rescale", 1 << 15),
        ("Rank1_8_8_0rs", 1 << 16),
        ("Rank1_9_9_0rs", 1 << 18),
        ("Rank1_10_10_0rs", 1 << 20),
        ("Rank1_15_15_0rs", 1 << 30),
    ]:
        # Number of signed/balanced int8 limbs needed to represent E in [0, max_e] on INT8 tensor/MXU units:
        # In jaxint.py, 2^15 uses 3 balanced int8 limbs (since 2^15 = 32768 <= 127*(2^16 + 2^8 + 1) ~ 2^23, wait:
        # unsigned/balanced radix-256 limbs for max_e: ceil(log2(max_e + 1) / 7.99) -> 2^15 takes 3 signed int8 limbs
        # because 32768 = 0*65536 + 128*256 + 0 exceeds signed int8 max 127 in 2 limbs [-32640, 32639]!).
        # Specifically, k balanced int8 limbs cover max |x| <= 127 * (256^k - 1) / 255:
        #   k=2: 32,639 (< 32,768 -> 2^15 needs 3 limbs!)
        #   k=3: 8,355,711 (covers 2^16 = 65,536, 2^18 = 262,144, AND 2^20 = 1,048,576 in the SAME 3 limbs as Q15!!)
        #   k=4: 2,139,062,143 (covers 2^30 = 1,073,741,824 -> needs 4 limbs, i.e., 4x2 = 8 INT8 GEMMs instead of 3x2 = 6!)
        k_limbs = 1
        while 127 * ((256 ** k_limbs - 1) // 255) < max_e:
            k_limbs += 1

        by_L = {}
        for L in (2, 32, 128, 512, 2048, 4096):
            z_worst = L * max_e
            acc_worst = L * max_e * v_max
            # Numerator of rounded division `(2 * acc + Z)` in layer.py:226:
            div_num_worst = 2 * acc_worst + z_worst
            by_L[str(L)] = {
                "Z_worst": z_worst,
                "Z_fits_babybear_unsigned": z_worst < BABYBEAR_P,
                "acc_fits_babybear_signed": acc_worst < (BABYBEAR_P // 2),
                "acc_fits_f64_exact_2_53": acc_worst < (1 << 53),
                "div_num_fits_goldilocks_signed": div_num_worst < (GOLDILOCKS_P // 2),
                "div_num_fits_int64": div_num_worst < ((1 << 63) - 1),
            }
        audit[name] = {
            "max_E": max_e,
            "balanced_int8_limbs_for_E": k_limbs,
            "int8_gemms_for_EV": k_limbs * 2,  # V has 2 limbs
            "by_context_L": by_L,
        }
    return audit


# ---------------------------------------------------------------------------
# 5. Part 3: Pointwise & Synthetic Softmax Fidelity (up to L = 4096)
# ---------------------------------------------------------------------------
def run_pointwise_and_synthetic_fidelity() -> Dict[str, Any]:
    u = np.arange(65536, dtype=np.int64)
    true_f64 = np.exp(-u.astype(np.float64) / 256.0)
    t_exact = build_exact_q15_64k()

    t_hi_8, t_lo_8 = build_rank1_subtables(8, 8)
    t_hi_10, t_lo_10 = build_rank1_subtables(10, 10)
    t_hi_15, t_lo_15 = build_rank1_subtables(15, 15)
    t_hi_18_12, t_lo_18_12 = build_rank1_subtables(18, 12)

    candidates = {
        "gptoss_exact_q15": (t_exact, float(1 << 15)),
        "Rank1_8_8_0rs": (eval_rank1_prod_exp(u, t_hi_8, t_lo_8, 0), float(1 << 16)),
        "Rank1_10_10_0rs": (eval_rank1_prod_exp(u, t_hi_10, t_lo_10, 0), float(1 << 20)),
        "Rank1_15_15_0rs": (eval_rank1_prod_exp(u, t_hi_15, t_lo_15, 0), float(1 << 30)),
        "Rank1_18_12_0rs": (eval_rank1_prod_exp(u, t_hi_18_12, t_lo_18_12, 0), float(1 << 30)),
        "Rank1_15_15_1rs": (eval_rank1_prod_exp(u, t_hi_15, t_lo_15, 15), float(1 << 15)),
        "StructuredExp_k4_clamped": (build_structured_exp_64k(k_bits=4), float(1 << 15)),
        "StructuredExp_unclamped": (build_structured_exp_64k(k_bits=8), float(1 << 15)),
    }

    # Pointwise accuracy on:
    #   (A) Significant Softmax band `x in [-6.0, 0]` (`u in [0, 1536]`, where exp >= 0.0025)
    #   (B) Full Q15 support `u in [0, 2838]` (`x in [-11.09, 0]`)
    #   (C) Full 64k domain `u in [0, 65536)` (catches StructuredExp ClampLower's non-zero tail floor!)
    pointwise = {}
    mask_sig = u <= 1536
    mask_sup = u <= 2838
    for name, (arr, scale) in candidates.items():
        norm = arr.astype(np.float64) / scale
        abs_err_q15 = np.abs(norm - true_f64) * 32768.0  # normalized to Q15 ULPs!
        rel_sig = np.abs(norm[mask_sig] - true_f64[mask_sig]) / true_f64[mask_sig]
        rel_sup = np.abs(norm[mask_sup] - true_f64[mask_sup]) / true_f64[mask_sup]
        # Equivalent Q15 integer comparison against gptoss_exact_q15:
        q15_equiv = np.rint(norm * 32768.0).astype(np.int64)
        ulp_vs_exact_sup = np.abs(q15_equiv[mask_sup] - t_exact[mask_sup])
        ulp_vs_exact_all = np.abs(q15_equiv - t_exact)
        pointwise[name] = {
            "scale": scale,
            "max_abs_err_in_q15_ulps_all64k": round(float(abs_err_q15.max()), 4),
            "mean_abs_err_in_q15_ulps_sup": round(float(abs_err_q15[mask_sup].mean()), 4),
            "max_rel_err_band_neg6_to_0": round(float(rel_sig.max()), 6),
            "mean_rel_err_band_neg6_to_0": round(float(rel_sig.mean()), 6),
            "max_rel_err_q15_support": round(float(rel_sup.max()), 6),
            "max_q15_ulp_diff_vs_gptoss_sup": int(ulp_vs_exact_sup.max()),
            "max_q15_ulp_diff_vs_gptoss_all64k": int(ulp_vs_exact_all.max()),
            "tail_floor_at_u_8000_q15_ulps": round(float(norm[8000] * 32768.0), 4),
            "nonzero_entries_of_64k": int(np.sum(arr > 0)),
        }

    # Synthetic Softmax + Value-Projection Sweep across L in {32, 128, 512, 2048, 4096}
    rng = np.random.default_rng(42)
    n_trials = 200
    hd = 64
    softmax_sweep = {}

    for L in (32, 128, 512, 2048, 4096):
        # Mix realistic sharp attention (sigma=3.5) and diffuse attention (sigma=1.2)
        logits_real = np.concatenate([
            rng.normal(0.0, 3.5, size=(n_trials // 2, L)),
            rng.normal(0.0, 1.2, size=(n_trials // 2, L)),
        ], axis=0)
        # Quantize scores to 2^-19 (`fsc = 2*8 + 3 = 19` as in gptoss-int Layer 0!)
        fsc = 19
        sc_int = np.rint(logits_real * (1 << fsc)).astype(np.int64)
        mx = sc_int.max(axis=1, keepdims=True)
        u_mat = (mx - sc_int) >> (fsc - 8)  # [n_trials, L]
        u_clamped = np.clip(u_mat, 0, 65535)

        V_int = rng.integers(-16000, 16000, size=(n_trials, L, hd), dtype=np.int64)
        # Random downstream projection W_o [hd, 128] to test logit argmax stability!
        W_proj = rng.integers(-500, 500, size=(hd, 128), dtype=np.int64)

        # Float64 ground truth on same quantized scores:
        diff_f64 = (sc_int - mx).astype(np.float64) / float(1 << fsc)
        e_f64 = np.exp(diff_f64)
        Z_f64 = e_f64.sum(axis=1)
        o_f64 = (e_f64[:, :, None] * V_int.astype(np.float64)).sum(axis=1) / Z_f64[:, None]

        # gptoss-int v0 reference output:
        e_ref = candidates["gptoss_exact_q15"][0][u_clamped]
        e_ref = np.where(u_mat < 65536, e_ref, 0)
        Z_ref = e_ref.sum(axis=1, keepdims=True)
        acc_ref = np.einsum("ti,tic->tc", e_ref, V_int)
        o_ref = (2 * acc_ref + Z_ref) // (2 * Z_ref)
        proj_ref_argmax = (o_ref @ W_proj).argmax(axis=1)

        res_L = {}
        for name, (tab, scale) in candidates.items():
            e_c = tab[u_clamped]
            if "k4_clamped" not in name:
                e_c = np.where(u_mat < 65536, e_c, 0)
            # Safe exact integer accumulation even when scale = 2^30 (split hi/lo 15 bits so int64 never overflows!):
            Z_c = e_c.sum(axis=1, keepdims=True)
            e_hi = e_c >> 15
            e_lo = e_c & 0x7FFF
            acc_hi = np.einsum("ti,tic->tc", e_hi, V_int)
            acc_lo = np.einsum("ti,tic->tc", e_lo, V_int)
            # Exact division `(2 * (acc_hi * 2^15 + acc_lo) + Z_c) // (2 * Z_c)` using Python bigints per scalar
            o_c = np.empty_like(o_ref)
            for ti in range(n_trials):
                zc = int(Z_c[ti, 0])
                two_zc = 2 * zc
                for ci in range(hd):
                    acc_val = (int(acc_hi[ti, ci]) << 15) + int(acc_lo[ti, ci])
                    o_c[ti, ci] = (2 * acc_val + zc) // two_zc

            Z_norm = Z_c[:, 0].astype(np.float64) / scale
            rel_Z_err = np.abs(Z_norm - Z_f64) / Z_f64
            ulp_vs_ref = np.abs(o_c - o_ref)
            err_vs_f64 = np.abs(o_c.astype(np.float64) - o_f64)
            proj_argmax = (o_c @ W_proj).argmax(axis=1)
            flips_vs_ref = int(np.sum(proj_argmax != proj_ref_argmax))

            res_L[name] = {
                "max_rel_denom_err": round(float(rel_Z_err.max()), 6),
                "mean_rel_denom_err": round(float(rel_Z_err.mean()), 6),
                "max_output_ulp_vs_gptoss_v0": int(ulp_vs_ref.max()),
                "mean_output_ulp_vs_gptoss_v0": round(float(ulp_vs_ref.mean()), 4),
                "exact_output_match_frac_vs_gptoss_v0": round(float(np.mean(ulp_vs_ref == 0)), 4),
                "max_abs_err_vs_f64": round(float(err_vs_f64.max()), 4),
                "proj_argmax_flips_of_200_vs_gptoss_v0": flips_vs_ref,
            }
        softmax_sweep[f"L={L}"] = res_L

    return {"pointwise": pointwise, "synthetic_softmax_by_L": softmax_sweep}


# ---------------------------------------------------------------------------
# 6. Part 4: Real `gpt-oss-20b` Layer-0 & Full 24-Layer End-to-End Evaluation!
# ---------------------------------------------------------------------------
def custom_layer_int_step(
    Wt,
    x: np.ndarray,
    P_layer: Dict[str, int],
    exp_tab_64k: np.ndarray,
    clamp_k4_bug: bool = False,
) -> Tuple[np.ndarray, Dict[str, Any]]:
    """
    Exact replica of `research/exact_recompute_2026_11_06/layer.py::layer_int`, parameterized ONLY
    by the 65,536-entry integer `exp` table `exp_tab_64k` (with bigint-safe `(2*acc + Z)//(2*Z)` so
    30-bit `Rank1(15,15)` never overflows int64!).
    When `exp_tab_64k` is `build_exact_q15_64k()`, we assert SHA-256 bit-identity with `gptoss-int v0`!
    """
    import layer as Lr
    import model as M
    from weights import bf16_to_int

    xp = np
    kern = M.ExactF64()
    t = x.shape[0]
    fa, fqk, fv, fm, fh = P_layer["fa"], P_layer["fqk"], P_layer["fv"], P_layer["fm"], P_layer["fh"]
    a = Lr.norm_int(xp, x, xp.asarray(Lr.gain_const(Wt.bits["input_layernorm.weight"])), fa)
    lin = lambda inp, f_in, n, fo: M.linear(xp, kern, inp, f_in, Wt.int_matrix(n + ".weight"), Wt.bits[n + ".bias"], fo)
    q = M.clamp(xp, lin(a, fa, "self_attn.q_proj", fqk), M.ACLAMP_LO, Lr.CL).reshape(t, Lr.H, Lr.HD)
    k = M.clamp(xp, lin(a, fa, "self_attn.k_proj", fqk), M.ACLAMP_LO, Lr.CL).reshape(t, Lr.KV, Lr.HD)
    v = M.clamp(xp, lin(a, fa, "self_attn.v_proj", fv), M.ACLAMP_LO, Lr.CL).reshape(t, Lr.KV, Lr.HD)
    C, S = (xp.asarray(z[:t]) for z in T.rope_tables(t))
    q = M.clamp(xp, Lr.rope_int(xp, q, C, S), M.ACLAMP_LO, Lr.CL)
    k = M.clamp(xp, Lr.rope_int(xp, k, C, S), M.ACLAMP_LO, Lr.CL)

    fsc = 2 * fqk + 3
    sm, se = bf16_to_int(Wt.bits["self_attn.sinks"])
    sink = M.to_scale(xp, xp.asarray(sm), xp.asarray(se), fsc)
    mask = xp.asarray(Lr.causal_mask(0, t, t, Wt.sliding))
    rep = Lr.H // Lr.KV
    kk = xp.repeat(k, rep, axis=1)
    vv = xp.repeat(v, rep, axis=1)
    sc = kern.einsum("ihc,jhc->hij", q, kk, 2, 2)

    # Measure empirical unmasked u distribution!
    sc_masked = xp.where(mask[None], sc, xp.iinfo(xp.int64).min // 4)
    mx = xp.maximum(sc_masked.max(axis=2), sink[:, None])  # [H, t]
    u_unmasked = (mx[:, :, None] - sc) >> (fsc - T.RX)
    u_valid = u_unmasked[np.broadcast_to(mask[None], u_unmasked.shape)]
    u_sink = (mx - sink[:, None]) >> (fsc - T.RX)

    def ex_lookup(z):
        u_val = (mx[..., None] - z) >> (fsc - T.RX) if z.ndim == 3 else (mx - z) >> (fsc - T.RX)
        if clamp_k4_bug:
            return exp_tab_64k[np.clip(u_val, 0, 65535)]
        return np.where(u_val < 65536, exp_tab_64k[np.clip(u_val, 0, 65535)], 0)

    e = np.where(mask[None], ex_lookup(sc_masked), 0)  # [H, t, t]
    es = ex_lookup(np.broadcast_to(sink[:, None], mx.shape))  # [H, t]
    Z = e.sum(axis=2) + es  # [H, t]

    # Bigint-safe contraction for acc [t, H, HD] so 30-bit E never overflows int64:
    e_hi, e_lo = e >> 15, e & 0x7FFF
    acc_hi = np.einsum("hij,jhc->ihc", e_hi, vv)
    acc_lo = np.einsum("hij,jhc->ihc", e_lo, vv)
    o = np.empty((t, Lr.H, Lr.HD), dtype=np.int64)
    for hi_idx in range(Lr.H):
        for ti in range(t):
            zc = int(Z[hi_idx, ti])
            two_zc = 2 * zc
            for ci in range(Lr.HD):
                acc_val = (int(acc_hi[ti, hi_idx, ci]) << 15) + int(acc_lo[ti, hi_idx, ci])
                o[ti, hi_idx, ci] = (2 * acc_val + zc) // two_zc

    o_flat = M.clamp(xp, o, M.ACLAMP_LO, Lr.CL).reshape(t, Lr.H * Lr.HD)
    x1 = x + lin(o_flat, fv, "self_attn.o_proj", Lr.FS)
    m = Lr.norm_int(xp, x1, xp.asarray(Lr.gain_const(Wt.bits["post_attention_layernorm.weight"])), fm)
    logits = lin(m, fm, "mlp.router", Lr.FR)

    gubm, gube = bf16_to_int(Wt.bits["mlp.experts.gate_up_proj_bias"])
    dbm, dbe = bf16_to_int(Wt.bits["mlp.experts.down_proj_bias"])
    G = xp.asarray(T.glu_table())
    lg = np.asarray(logits)
    by = {}
    for i in range(t):
        top = Lr.route([int(z) for z in lg[i]])
        lt = lg[i, top].astype(np.int64)
        u_r = (lt.max() - lt) >> (Lr.FR - T.RX)
        ee = np.where(u_r < 65536, exp_tab_64k[np.clip(u_r, 0, 65535)], 0)
        Zr = int(ee.sum())
        wts = [((2 * int(ee_k) * (1 << Lr.FW) + Zr) // (2 * Zr)) for ee_k in ee]
        for e_, w_ in zip(top, wts):
            by.setdefault(e_, []).append((i, int(w_)))

    moe = xp.zeros((t, Lr.D), dtype=xp.int64)
    for e_ in sorted(by):
        rows = np.array([r_ for r_, _ in by[e_]])
        ws = xp.asarray(np.array([w_ for _, w_ in by[e_]], dtype=xp.int64))
        W1 = Wt.expert("gate_up_proj", e_)
        gu = M.linear(xp, kern, m[rows], fm, W1, None, Lr.FG)
        gu = gu + M.to_scale(xp, xp.asarray(gubm[e_]), xp.asarray(gube[e_]), Lr.FG)[None, :]
        gate = xp.minimum(gu[:, 0::2], 7 << Lr.FG)
        up = M.clamp(xp, gu[:, 1::2], -(7 << Lr.FG), 7 << Lr.FG)
        key = M.clamp(xp, M.rq(xp, gate, Lr.FG - T.GK), T.GLO << T.GK, T.GHI << T.GK)
        glu = G[key - (T.GLO << T.GK)]
        h_ = M.clamp(xp, M.rq(xp, (up + (1 << Lr.FG)) * glu, Lr.FG + T.FT - fh), M.ACLAMP_LO, Lr.CL)
        W2 = Wt.expert("down_proj", e_)
        dn = M.linear(xp, kern, h_, fh, W2, None, Lr.FS)
        dn = dn + M.to_scale(xp, xp.asarray(dbm[e_]), xp.asarray(dbe[e_]), Lr.FS)[None, :]
        contrib = M.rq(xp, ws[:, None] * dn, Lr.FW)
        np.add.at(moe, rows, contrib)

    x2 = x1 + moe
    stats = {
        "u_unmasked_max": int(u_valid.max()),
        "u_unmasked_p99": int(np.percentile(u_valid, 99)),
        "u_sink_max": int(u_sink.max()),
        "o_attn": o,
    }
    return x2, stats


def run_real_gptoss_evaluation() -> Dict[str, Any]:
    model_dir = os.environ.get("GPTOSS_DIR", "/Users/ember/models/gpt-oss-20b/6cee5e81")
    if not os.path.exists(os.path.join(model_dir, "model.safetensors.index.json")):
        return {"available": False}

    import hashlib
    import forward as Fw
    import layer as Lr
    import model as M
    from weights import Shards

    S = Shards(model_dir)
    t_exact = build_exact_q15_64k()
    t_hi_8, t_lo_8 = build_rank1_subtables(8, 8)
    t_hi_10, t_lo_10 = build_rank1_subtables(10, 10)
    t_hi_15, t_lo_15 = build_rank1_subtables(15, 15)
    t_hi_18, t_lo_18 = build_rank1_subtables(18, 12)
    u64k = np.arange(65536, dtype=np.int64)

    variants = {
        "gptoss_exact_q15": (t_exact, False),
        "Rank1_8_8_0rs": (eval_rank1_prod_exp(u64k, t_hi_8, t_lo_8, 0), False),
        "Rank1_10_10_0rs": (eval_rank1_prod_exp(u64k, t_hi_10, t_lo_10, 0), False),
        "Rank1_15_15_0rs": (eval_rank1_prod_exp(u64k, t_hi_15, t_lo_15, 0), False),
        "Rank1_18_12_0rs": (eval_rank1_prod_exp(u64k, t_hi_18, t_lo_18, 0), False),
        "Rank1_15_15_1rs": (eval_rank1_prod_exp(u64k, t_hi_15, t_lo_15, 15), False),
        "StructuredExp_k4_clamped": (build_structured_exp_64k(k_bits=4), True),
    }

    # --- A. Layer 0 exact check against pinned `g1-numpy.json` (12 tokens) ---
    p0_cfg = json.load(open(os.path.join(EXACT_RECOMP_DIR, "params-v0.json")))
    g1_ref = json.load(open(os.path.join(EXACT_RECOMP_DIR, "g1-numpy.json")))
    ids_g1 = p0_cfg["ids"]
    x0_g1, _ = Fw.embed(S, ids_g1)
    Wt0 = Lr.LayerWeights(S, 0)
    layer0_res = {}
    o_ref_l0 = None
    x2_ref_l0 = None

    for vname, (vtab, cbug) in variants.items():
        x2_v, st_v = custom_layer_int_step(Wt0, x0_g1, p0_cfg["P"], vtab, clamp_k4_bug=cbug)
        if vname == "gptoss_exact_q15":
            dig_x2 = hashlib.sha256(np.ascontiguousarray(x2_v, dtype="<i8").tobytes()).hexdigest()
            assert dig_x2 == g1_ref["digests"]["x2"], f"SHA-256 mismatch with g1-numpy.json! {dig_x2}"
            o_ref_l0 = st_v["o_attn"]
            x2_ref_l0 = x2_v
        o_diff = np.abs(st_v["o_attn"] - o_ref_l0)
        x2_diff = np.abs(x2_v - x2_ref_l0)
        layer0_res[vname] = {
            "attn_o_max_ulp_diff_vs_gptoss_v0": int(o_diff.max()),
            "attn_o_exact_match_frac": round(float(np.mean(o_diff == 0)), 5),
            "layer0_x2_max_ulp_diff": int(x2_diff.max()),
            "u_unmasked_max": st_v["u_unmasked_max"],
        }
    del Wt0

    # --- B. Full 24-Layer + lm_head End-to-End Evaluation on Held-Out Passage 0 (32 tokens)! ---
    # Also cross-checked against `g3-numpy.json` passage 0 SHA-256 digest!
    P_v1 = json.load(open(os.path.join(EXACT_RECOMP_DIR, "params-v1.json")))
    g3_ref = json.load(open(os.path.join(EXACT_RECOMP_DIR, "g3-numpy.json")))["passages"][0]
    passages = json.load(open(os.path.join(EXACT_RECOMP_DIR, "passages.json")))
    # Tokenize passage 0 without requiring external `tokenizers` package if not in default python3:
    try:
        tok = Fw.tok()
        ids_p0 = tok.encode(passages["eval"][0]).ids
    except ImportError:
        # Fallback: check if `uv` or tokenizer JSON BPE is needed, or use g1's 12 tokens
        ids_p0 = ids_g1

    t0_24l = time.time()
    xi_init, xf_init = Fw.embed(S, ids_p0)
    states = {vname: xi_init.copy() for vname in variants}
    xf = xf_init.copy()
    max_u_across_24_layers = 0
    max_u_sink_across_24_layers = 0

    for l in range(24):
        Wt = Lr.LayerWeights(S, l)
        # Step float64 reference once
        xf = Lr.layer_float(Wt, xf)
        # Step all integer variants while Wt's decoded experts are hot in cache!
        for vname, (vtab, cbug) in variants.items():
            states[vname], st_l = custom_layer_int_step(Wt, states[vname], P_v1["layers"][l], vtab, clamp_k4_bug=cbug)
            if vname == "gptoss_exact_q15":
                max_u_across_24_layers = max(max_u_across_24_layers, st_l["u_unmasked_max"])
                max_u_sink_across_24_layers = max(max_u_sink_across_24_layers, st_l["u_sink_max"])
        del Wt

    # Final RMSNorm + chunked 201,088-vocab lm_head for all variants in ONE pass over lm_head.weight!
    af = Fw.final_norm_float(S, xf)
    normed_states = {vname: Fw.final_norm_int(np, S, states[vname], P_v1["fa_final"]) for vname in variants}

    bits_lm = S.bf16_bits("lm_head.weight")
    kern = M.ExactF64()
    logits_variants = {vname: [] for vname in variants}
    logits_f64_chunks = []
    for c0 in range(0, bits_lm.shape[0], Fw.VOCAB_CHUNK):
        W_chunk = M.IntMatrix.from_bf16(np.asarray(bits_lm[c0:c0 + Fw.VOCAB_CHUNK]))
        logits_f64_chunks.append(af @ Lr.expert_float(W_chunk).T)
        for vname in variants:
            logits_variants[vname].append(np.asarray(M.linear(np, kern, normed_states[vname], P_v1["fa_final"], W_chunk, None, Fw.FL)))
        del W_chunk

    lf = np.concatenate(logits_f64_chunks, axis=1)
    argmax_f64 = lf.argmax(axis=1)
    logits_int_map = {vname: np.concatenate(chunks, axis=1) for vname, chunks in logits_variants.items()}

    li_exact = logits_int_map["gptoss_exact_q15"]
    if len(ids_p0) == 32:
        dig_logits = hashlib.sha256(np.ascontiguousarray(li_exact, dtype="<i8").tobytes()).hexdigest()
        assert dig_logits == g3_ref["digests"]["logits"], f"24-layer logits SHA-256 mismatch! {dig_logits}"
    argmax_exact = li_exact.argmax(axis=1)

    full_24l_summary = {}
    for vname, li in logits_int_map.items():
        ai = li.argmax(axis=1)
        logit_diff_vs_v0 = np.abs(li - li_exact).astype(np.float64) / (2.0 ** Fw.FL)
        logit_diff_vs_f64 = np.abs(li.astype(np.float64) / (2.0 ** Fw.FL) - lf)
        full_24l_summary[vname] = {
            "positions": int(len(ids_p0)),
            "argmax_agree_with_gptoss_v0": int(np.sum(ai == argmax_exact)),
            "argmax_flips_vs_gptoss_v0": int(np.sum(ai != argmax_exact)),
            "argmax_agree_with_float64": int(np.sum(ai == argmax_f64)),
            "max_abs_logit_diff_vs_gptoss_v0": round(float(logit_diff_vs_v0.max()), 5),
            "median_pos_max_logit_diff_vs_gptoss_v0": round(float(np.median(logit_diff_vs_v0.max(axis=1))), 5),
            "max_abs_logit_diff_vs_float64": round(float(logit_diff_vs_f64.max()), 4),
        }

    return {
        "available": True,
        "tokens_evaluated_24l": len(ids_p0),
        "verified_g1_layer0_sha256": True,
        "verified_g3_24layer_logits_sha256": len(ids_p0) == 32,
        "max_unmasked_u_across_24_layers": max_u_across_24_layers,
        "max_sink_u_across_24_layers": max_u_sink_across_24_layers,
        "all_unmasked_u_fit_in_16bits_65536": max_u_across_24_layers < 65536,
        "elapsed_seconds_secondary": round(time.time() - t0_24l, 2),
        "layer0_12tok": layer0_res,
        "full_24layer_end_to_end": full_24l_summary,
    }


def main():
    print("1. Running algebraic rank & DecomposableTable tests over BabyBear...")
    alg = run_algebraic_rank_tests()
    print(f"   Phase 0 bf16 control rank = {alg['phase0_bf16_fixedpoint_control']['exact_rank_mod_babybear']}, "
          f"minor(0,1;0,18) = {alg['phase0_bf16_fixedpoint_control']['minor_r01_c0_18']}")
    print(f"   Q15 wide exact table rank = {alg['q15_rx12_wide_exact_64k']['exact_rank_mod_babybear']} / "
          f"{alg['q15_rx12_wide_exact_64k']['nonzero_rows_of_256']} nonzero rows")
    for k, v in alg["rank1_prod_variants"].items():
        print(f"   {k:24s}: rank = {v['exact_rank_mod_babybear']:3d}, max_entry = {v['max_entry']:11,d}, "
              f"fits_BB = {v['fits_unwrapped_in_babybear']}, SOS_exact = {v['is_exact_decomposable_c2_w8_alpha2_prodTable']}")

    print("\n2. Running overflow & INT8-limb hardware boundary audit...")
    ovf = run_overflow_and_limb_audit()

    print("\n3. Running pointwise & synthetic Softmax fidelity up to L=4096...")
    fid = run_pointwise_and_synthetic_fidelity()
    for k, v in fid["pointwise"].items():
        print(f"   {k:26s}: max_rel[-6,0]={v['max_rel_err_band_neg6_to_0']:.6f}, "
              f"max_q15_ulp_sup={v['max_q15_ulp_diff_vs_gptoss_sup']}, "
              f"L=4096 max_rel_Z={fid['synthetic_softmax_by_L']['L=4096'][k]['max_rel_denom_err']:.6f}, "
              f"L=4096 max_out_ulp={fid['synthetic_softmax_by_L']['L=4096'][k]['max_output_ulp_vs_gptoss_v0']}")

    print("\n4. Running real `gpt-oss-20b` Layer-0 and Full 24-Layer + lm_head evaluation...")
    real_res = run_real_gptoss_evaluation()
    if real_res.get("available"):
        print(f"   24-layer tokens={real_res['tokens_evaluated_24l']}, "
              f"g3_sha256_verified={real_res['verified_g3_24layer_logits_sha256']}, "
              f"max_unmasked_u={real_res['max_unmasked_u_across_24_layers']} (<65536: {real_res['all_unmasked_u_fit_in_16bits_65536']})")
        for k, v in real_res["full_24layer_end_to_end"].items():
            print(f"   {k:26s}: argmax_agree_v0={v['argmax_agree_with_gptoss_v0']}/{v['positions']}, "
                  f"argmax_agree_f64={v['argmax_agree_with_float64']}/{v['positions']}, "
                  f"max_|dlogit|_vs_v0={v['max_abs_logit_diff_vs_gptoss_v0']:.5f}, "
                  f"max_|dlogit|_vs_f64={v['max_abs_logit_diff_vs_float64']:.4f}")

    out_json = os.path.join(HERE, "rank1_prod_exp_results.json")
    with open(out_json, "w") as f:
        json.dump({
            "algebraic_rank": alg,
            "overflow_and_limb_audit": ovf,
            "fidelity": fid,
            "real_gptoss_20b": real_res,
        }, f, indent=2)

    # Summary CSV across candidates
    summary_rows = []
    for k, pw in fid["pointwise"].items():
        l4096 = fid["synthetic_softmax_by_L"]["L=4096"][k]
        r24 = real_res.get("full_24layer_end_to_end", {}).get(k, {})
        summary_rows.append({
            "variant": k,
            "scale": int(pw["scale"]),
            "max_rel_err_band_neg6_0": pw["max_rel_err_band_neg6_to_0"],
            "max_q15_ulp_diff_sup": pw["max_q15_ulp_diff_vs_gptoss_sup"],
            "L4096_max_rel_denom_err": l4096["max_rel_denom_err"],
            "L4096_max_out_ulp_vs_v0": l4096["max_output_ulp_vs_gptoss_v0"],
            "L4096_proj_argmax_flips_of_200": l4096["proj_argmax_flips_of_200_vs_gptoss_v0"],
            "gptoss20b_24L_argmax_agree_v0": r24.get("argmax_agree_with_gptoss_v0"),
            "gptoss20b_24L_argmax_agree_f64": r24.get("argmax_agree_with_float64"),
            "gptoss20b_24L_pos": r24.get("positions"),
            "gptoss20b_24L_max_dlogit_vs_v0": r24.get("max_abs_logit_diff_vs_gptoss_v0"),
            "gptoss20b_24L_max_dlogit_vs_f64": r24.get("max_abs_logit_diff_vs_float64"),
        })

    out_csv = os.path.join(HERE, "rank1_prod_exp_summary.csv")
    with open(out_csv, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)


if __name__ == "__main__":
    main()
