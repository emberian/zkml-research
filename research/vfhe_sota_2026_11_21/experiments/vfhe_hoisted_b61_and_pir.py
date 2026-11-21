#!/usr/bin/env python3
"""Executable HoistedB61 BFV ct x ct Verifier, Adversarial Attack Suite, Bivariate Carry
Comparator, Verifiable PIR Pricer, and d = 64..4096 Dark-Learning Re-Pricer.

2026-11-21 — Worker 1 (`vfhe-fast-cert`).
Reads unmodified reference implementations from `research/dark_learning_2026_11_06/`
(`bfv_ref.py`, `cert_b61.py`, `rescale_certificates.py`, `step_counts.py`, `e2s_proof.py`,
`fhe_fork.py`, `spdz.py`, `mpc_fork.py`, `step_spec.py`) without modifying them.

Verifies four stacked vFHE certificate breakthroughs:
  (a) Hoisted Sum-Before-Rescale (`Lazy Rescale` across K_blk = 64 blocks):
      Accumulates D_k^{(r)}(X) = sum_{c=0}^{K_blk-1} pair_k(W^{(r,c)}, v^{(c)}) over Z[X]/(X^N+1)
      and rescales ONCE per output group (6,144 -> 128 across 3 matvecs at d=4096; 2,048 -> 32 = 64x
      per forward matvec). Verifies on real `bfv_ref` ciphertexts that decryption is exact AND
      post-rescale phase noise is strictly smaller (1 rounding error instead of 64), fitting in
      existing k = 5 extension primes Bp (2^446 << Q*B ~ 2^488, 42 bits of spare margin).
  (b) Fused `d`-Free Rescale Identity + Direct Signed/Shifted-Digit Canonical Lifts (+ Exact Garner):
      Fuses ring quotient and BEHZ rescale into ONE per-prime polynomial equation:
        t * sum_c pair_k(a^{(r,c)}, b^{(c)}) + floor(Q/2)*sum X^j
          = Q * y_k^{(r)}(X) + s_k^{(r)}(X) + t * (X^N + 1) * K_{k,p}^{(r)}(X),
      checked at Fiat-Shamir challenge r_{FS,p} in F_p via a 32x64 scalar matvec.
      Deletes `v_i`, `u`, `in_B`, `z_res`, `ext_s`, `ext_y` double-pay from `cert_b61.py`.
      Also implements `Exact-Garner` mixed-radix lifts (exploiting 2^61 - q_i < 2^20) to seal
      the non-power-of-two [Q, 2^183) boundary strip (Astra E4 & E7).
  (c) Deduplicated Within-Step Input Lifts + Persistent Encrypted-Weight Digit Commitments:
      Deduplicates shared vectors (32x-64x) and W2 forward/backward reuse (2x); carries persistent
      weight digit commitments across steps (0 online weight lifts for Inference-Only vFHEML;
      192 adapter cts vs 4,096 for low-rank r <= 64; 64x epoch flush for exact dense SGD;
      proves why dense RLWE wrap-bit indicator loses 2.1x vs direct steady-state re-lift).
  (d) Single-Field `p61` Bivariate Carry-Polynomial `F(X,Y) = (Y - 2^16) C(X,Y)` Comparator:
      Implements and tests the sound range-checked bivariate carry identity in F_{p61}
      (|col| <= 2^53.6 < p61/2), constructively exhibits the forgery when C(X,Y) carry range
      checks are omitted, and proves HoistedB61-RNS wins by 5.8x-6.5x per output group.
"""

import hashlib
import json
import math
import os
import random
import sys
import time

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
DL_DIR = os.path.join(REPO_ROOT, "research", "dark_learning_2026_11_06")
sys.path.insert(0, DL_DIR)

import bfv_ref as bfv
import cert_b61 as C_BASE
import e2s_proof as PD
import fhe_fork as FF
import mpc_fork as MF
import rescale_certificates as RC
import spdz
import step_counts as SC
import step_spec as S

P61_RIESEL = 127 * (1 << 54) + 1  # 2^61 - 2^54 + 1, 2-adicity 54


# ======================================================================================
# 1. Exact Digit & Garner Mixed-Radix Canonical Lift Encodings
# ======================================================================================

def decompose_unsigned(u, w, num_limbs, top_bits):
    """Decompose u in [0, 2^(w*(num_limbs-1) + top_bits)) into `num_limbs` base-2^w digits."""
    if u < 0:
        raise ValueError(f"negative value {u} in unsigned decomposition")
    mask = (1 << w) - 1
    digits = []
    rem = u
    for _ in range(num_limbs - 1):
        digits.append(rem & mask)
        rem >>= w
    if rem >= (1 << top_bits):
        raise ValueError(f"top limb {rem} overflows 2^{top_bits}")
    digits.append(rem)
    return digits


def eval_poly_mod(poly, r, p):
    acc = 0
    for c in reversed(poly):
        acc = (acc * r + c) % p
    return acc


def ones_eval(N, r, p):
    """Evaluate sum_{j=0}^{N-1} X^j at r mod p in O(log N)."""
    if r % p == 1:
        return N % p
    return ((pow(r, N, p) - 1) * pow(r - 1, -1, p)) % p


class DirectDigitSpec:
    """Unsigned shifted w-bit digit spec for centered mod-Q inputs, [0, Q) remainders, and y quotients."""

    def __init__(self, Q, w=20, max_y_bits=262):
        assert w in (16, 20)
        self.Q = Q
        self.H_Q = Q // 2
        self.w = w
        self.q_bits = Q.bit_length()  # 183
        self.Lx = math.ceil(self.q_bits / w)  # 12 at w=16, 10 at w=20
        self.top_x_bits = self.q_bits - w * (self.Lx - 1)  # 7 at w=16, 3 at w=20
        self.y_shift = 1 << max_y_bits
        self.y_span_bits = max_y_bits + 1  # 263 -> covers [-2^262, 2^262)
        self.Ly = math.ceil(self.y_span_bits / w)  # 17 at w=16, 14 at w=20
        self.top_y_bits = self.y_span_bits - w * (self.Ly - 1)  # 7 at w=16, 3 at w=20

    def encode_centered_Q(self, poly):
        """Given centered coefficients x in [-H_Q, H_Q], return Lx digit polynomials in [0, 2^w)."""
        N = len(poly)
        cols = [decompose_unsigned(x + self.H_Q, self.w, self.Lx, self.top_x_bits) for x in poly]
        return [[cols[j][m] for j in range(N)] for m in range(self.Lx)]

    def encode_rem_Q(self, poly):
        """Given remainder coefficients s in [0, Q), return Lx digit polynomials in [0, 2^w)."""
        N = len(poly)
        cols = [decompose_unsigned(s, self.w, self.Lx, self.top_x_bits) for s in poly]
        return [[cols[j][m] for j in range(N)] for m in range(self.Lx)]

    def encode_signed_y(self, poly):
        """Given signed quotient coefficients y in (-2^262, 2^262), return Ly shifted digit polys."""
        N = len(poly)
        cols = [decompose_unsigned(y + self.y_shift, self.w, self.Ly, self.top_y_bits) for y in poly]
        return [[cols[j][m] for j in range(N)] for m in range(self.Ly)]

    def check_digits(self, digit_polys, num_limbs, top_bits):
        """Verifier range check: every digit in [0, 2^w), top digit shifted via 2^(w-top_bits)*d in [0, 2^w)."""
        if len(digit_polys) != num_limbs:
            return False, "wrong number of digit limbs"
        lim = 1 << self.w
        shift = self.w - top_bits
        for m, dp in enumerate(digit_polys):
            for val in dp:
                if not isinstance(val, int) or val < 0 or val >= lim:
                    return False, f"digit limb {m} out of [0, 2^{self.w})"
                if m == num_limbs - 1 and (val << shift) >= lim:
                    return False, f"top digit limb {m} overflows 2^{top_bits}"
        return True, "ok"

    def eval_shifted_digits(self, digit_polys, shift_const, N, r, p):
        """Evaluate (sum_m d_m(r) * 2^(w*m) - shift_const * sum_{j=0}^{N-1} r^j) mod p."""
        base = 1 << self.w
        acc = 0
        pw = 1
        for dp in digit_polys:
            acc = (acc + pw * eval_poly_mod(dp, r, p)) % p
            pw = (pw * base) % p
        if shift_const:
            acc = (acc - (shift_const % p) * ones_eval(N, r, p)) % p
        return acc


class ExactGarnerSpec:
    """Exact non-power-of-two [0, Q - 1] canonical representation via Garner mixed radix:
         u = r_0 + q_0 * r_1 + (q_0 * q_1) * r_2,   r_i in [0, q_i - 1].
    Exploits delta_i = 2^61 - q_i < 2^20 for 61-bit NTT primes:
      r_i = d_0 + 2^20 d_1 + 2^39 d_2 + 2^57 d_3   (20 + 19 + 18 + 4 = 61 bits),
      d_0 + delta_i = v_0 + 2^20 * c_i             (1 aux digit v_0 in [0, 2^20), c_i in {0,1}),
      T_i = (2^19 - 1 - d_1) + (2^18 - 1 - d_2) + (15 - d_3) - c_i in [0, 2^20).
    Total: 5 columns per limb * 3 limbs = 15 w=20 digit columns, closing [Q, 2^183) with zero slack!
    """

    def __init__(self, Qp):
        assert len(Qp) == 3
        self.Qp = list(Qp)
        self.Q = math.prod(Qp)
        self.H_Q = self.Q // 2
        self.deltas = [(1 << 61) - q for q in Qp]
        assert all(0 < d < (1 << 20) for d in self.deltas), "Garner-15 requires 2^61 - q_i < 2^20"
        self.inv_q0_mod_q1 = pow(Qp[0], -1, Qp[1])
        self.inv_q01_mod_q2 = pow(Qp[0] * Qp[1], -1, Qp[2])

    def encode_u_exact(self, poly_u):
        """Encode u_j in [0, Q - 1] into 15 polynomials in [0, 2^20)."""
        N = len(poly_u)
        q0, q1, q2 = self.Qp
        cols = [[] for _ in range(15)]
        for u in poly_u:
            if not (0 <= u < self.Q):
                raise ValueError("u outside [0, Q)")
            r0 = u % q0
            r1 = ((u - r0) // q0) % q1
            r2 = (u - r0 - q0 * r1) // (q0 * q1)
            assert r0 + q0 * r1 + q0 * q1 * r2 == u and 0 <= r2 < q2
            for idx, (ri, delta) in enumerate(zip((r0, r1, r2), self.deltas)):
                d0 = ri & ((1 << 20) - 1)
                d1 = (ri >> 20) & ((1 << 19) - 1)
                d2 = (ri >> 39) & ((1 << 18) - 1)
                d3 = ri >> 57
                assert d3 < 16
                s0 = d0 + delta
                v0 = s0 & ((1 << 20) - 1)
                ci = s0 >> 20
                assert ci in (0, 1)
                base = 5 * idx
                cols[base + 0].append(d0)
                cols[base + 1].append(d1)
                cols[base + 2].append(d2)
                cols[base + 3].append(d3)
                cols[base + 4].append(v0)
        return cols

    def check_u_exact(self, cols):
        """Deterministic verifier check that all 15 columns prove u_j in [0, Q - 1] EXACTLY."""
        if len(cols) != 15:
            return False, "Garner requires 15 digit columns"
        N = len(cols[0])
        lim20 = 1 << 20
        for idx, (q, delta) in enumerate(zip(self.Qp, self.deltas)):
            d0s, d1s, d2s, d3s, v0s = cols[5 * idx: 5 * (idx + 1)]
            inv2_20 = pow(lim20, -1, q)
            for j in range(N):
                d0, d1, d2, d3, v0 = d0s[j], d1s[j], d2s[j], d3s[j], v0s[j]
                if not (0 <= d0 < lim20 and 0 <= v0 < lim20):
                    return False, "d0/v0 out of [0, 2^20)"
                # Narrowed limb range checks via shifted lookups in the SAME [0, 2^20) table:
                if not (0 <= (d1 << 1) < lim20 and 0 <= (d2 << 2) < lim20 and 0 <= (d3 << 16) < lim20):
                    return False, "narrowed Garner limb out of range"
                # Boolean carry c_i in F_q (lifts to Z because |d0 + delta - v0| < 2^21 << q):
                ci = ((d0 + delta - v0) * inv2_20) % q
                if (ci * (ci - 1)) % q != 0:
                    return False, f"Garner carry c_{idx} not boolean"
                ci_int = 0 if ci == 0 else 1
                # Linear complement lookup T_i in [0, 2^20):
                Ti = ((1 << 19) - 1 - d1) + ((1 << 18) - 1 - d2) + (15 - d3) - ci_int
                if not (0 <= Ti < lim20):
                    return False, f"Garner limb r_{idx} >= q_{idx} (boundary overflow refused)"
        return True, "ok"

    def eval_u_shifted(self, cols, shift_const, N, r, p):
        """Evaluate (r_0(r) + q_0 r_1(r) + q_0 q_1 r_2(r) - shift_const * ones(r)) mod p."""
        q0, q1, _ = self.Qp
        mults = [1, q0 % p, (q0 * q1) % p]
        acc = 0
        for idx in range(3):
            d0s, d1s, d2s, d3s, _ = cols[5 * idx: 5 * (idx + 1)]
            ri_eval = (
                eval_poly_mod(d0s, r, p)
                + ((1 << 20) % p) * eval_poly_mod(d1s, r, p)
                + ((1 << 39) % p) * eval_poly_mod(d2s, r, p)
                + ((1 << 57) % p) * eval_poly_mod(d3s, r, p)
            ) % p
            acc = (acc + mults[idx] * ri_eval) % p
        if shift_const:
            acc = (acc - (shift_const % p) * ones_eval(N, r, p)) % p
        return acc


# ======================================================================================
# 2. HoistedB61 Certificate Prover & Verifier (Matvec Row-Groups & Single Products)
# ======================================================================================

def ct_handle(ct, Qp):
    return C_BASE.handle(ct, Qp)


def _hash_int_list(m, vals):
    m.update(",".join(map(str, vals)).encode())
    m.update(b";")


def hoisted_witness_digest(w):
    """Commitment root stand-in covering ALL witness digits & quotient polynomials before FS squeeze."""
    m = hashlib.sha256()
    m.update(w["mode"].encode() + b"|")
    for key in ("A_lifts", "B_lifts", "y_lifts", "s_lifts"):
        for item in w[key]:
            for dp in item:
                _hash_int_list(m, dp)
    for r_k in w["K_res"]:
        for k_comp in r_k:
            for p in sorted(k_comp):
                _hash_int_list(m, k_comp[p])
    return m.hexdigest()


def build_hoisted_matvec(scheme, Qp, Bp, A_grid, B_vec, w_bits=20, mode="direct", shared_A_lifts=None, shared_B_lifts=None):
    """Prover for R_blk x K_blk encrypted block matvec:
         out^{(r)}_k = round(t * sum_{c=0}^{K_blk-1} pair_k(A^{(r,c)}, B^{(c)}) / Q) mod Q.
    Supports pre-committed / persistent `shared_A_lifts` and `shared_B_lifts`!
    Returns (out_cts, witness).
    """
    Q, t, N = scheme.Q, scheme.t, scheme.N
    R_blk = len(A_grid)
    K_blk = len(B_vec)
    assert all(len(row) == K_blk for row in A_grid)

    dspec = DirectDigitSpec(Q, w=w_bits)
    gspec = ExactGarnerSpec(Qp) if mode == "exact_garner" else None

    def lift_centered_poly(poly_mod_Q):
        centered_p = bfv.poly_centered(poly_mod_Q, Q)
        if mode == "exact_garner":
            return centered_p, gspec.encode_u_exact([x + gspec.H_Q for x in centered_p])
        return centered_p, dspec.encode_centered_Q(centered_p)

    def lift_rem_poly(rem_poly):
        if mode == "exact_garner":
            return gspec.encode_u_exact(rem_poly)
        return dspec.encode_rem_Q(rem_poly)

    # 1. Deduplicated / persistent input lifts:
    A_cent = [[None] * K_blk for _ in range(R_blk)]
    A_lifts = []
    for r in range(R_blk):
        for c in range(K_blk):
            c0, c1 = A_grid[r][c]
            if shared_A_lifts is not None:
                p0, p1 = bfv.poly_centered(c0, Q), bfv.poly_centered(c1, Q)
                l0, l1 = shared_A_lifts[r][c]
            else:
                p0, l0 = lift_centered_poly(c0)
                p1, l1 = lift_centered_poly(c1)
            A_cent[r][c] = (p0, p1)
            A_lifts.append(l0)
            A_lifts.append(l1)

    B_cent = []
    B_lifts = []
    for c in range(K_blk):
        c0, c1 = B_vec[c]
        if shared_B_lifts is not None:
            p0, p1 = bfv.poly_centered(c0, Q), bfv.poly_centered(c1, Q)
            l0, l1 = shared_B_lifts[c]
        else:
            p0, l0 = lift_centered_poly(c0)
            p1, l1 = lift_centered_poly(c1)
        B_cent.append((p0, p1))
        B_lifts.append(l0)
        B_lifts.append(l1)

    # 2. Hoisted integer accumulation over Z[X]/(X^N + 1) + SINGLE BEHZ rescale per row-group r:
    out_cts = []
    y_lifts = []
    s_lifts = []
    K_res = []
    all_primes = list(Qp) + list(Bp)

    for r in range(R_blk):
        D_acc = [[0] * N for _ in range(3)]
        K_acc = [[0] * (N - 1) for _ in range(3)]
        for c in range(K_blk):
            a0, a1 = A_cent[r][c]
            b0, b1 = B_cent[c]
            z00, k00 = bfv.negacyclic_mul(a0, b0)
            z01, k01 = bfv.negacyclic_mul(a0, b1)
            z10, k10 = bfv.negacyclic_mul(a1, b0)
            z11, k11 = bfv.negacyclic_mul(a1, b1)
            for j in range(N):
                D_acc[0][j] += z00[j]
                D_acc[1][j] += z01[j] + z10[j]
                D_acc[2][j] += z11[j]
            for j in range(N - 1):
                K_acc[0][j] += k00[j]
                K_acc[1][j] += k01[j] + k10[j]
                K_acc[2][j] += k11[j]

        out_r = []
        K_r = []
        for k_comp in range(3):
            ys, ss = scheme.scale(D_acc[k_comp])
            y_lifts.append(dspec.encode_signed_y(ys))
            s_lifts.append(lift_rem_poly(ss))
            K_r.append({p: [x % p for x in K_acc[k_comp]] for p in all_primes})
            out_r.append([y % Q for y in ys])
        out_cts.append(tuple(out_r))
        K_res.append(K_r)

    witness = dict(
        mode=mode,
        w_bits=w_bits,
        opened_A=A_grid,
        opened_B=B_vec,
        A_lifts=A_lifts,
        B_lifts=B_lifts,
        y_lifts=y_lifts,
        s_lifts=s_lifts,
        K_res=K_res,
    )
    return out_cts, witness


def verify_hoisted_matvec(scheme, Qp, Bp, hA_grid, hB_vec, hOut_vec, out_cts, witness, legacy_fs=False):
    """Sound explicit verifier for `HoistedB61` across R_blk x K_blk ciphertext blocks."""
    Q, t, N = scheme.Q, scheme.t, scheme.N
    M_QB = Q * math.prod(Bp)
    R_blk = len(hA_grid)
    K_blk = len(hB_vec)
    mode = witness["mode"]
    w_bits = witness["w_bits"]

    # Public worst-case integer no-wrap guard (Astra E6):
    # Even if |x| < 2^183, |D_{k,j}| <= K_blk * 2 * N * 2^366; |y| < 2^262, |s| < 2^183.
    max_lhs = t * K_blk * 2 * N * (1 << (2 * Q.bit_length() - 2)) + (Q // 2)
    max_rhs = Q * (1 << 262) + (1 << Q.bit_length())
    if max_lhs + max_rhs >= M_QB:
        return False, "public parameter bound failure: Q*B insufficient to prevent CRT wraparound"

    A_grid = witness["opened_A"]
    B_vec = witness["opened_B"]
    if len(A_grid) != R_blk or len(B_vec) != K_blk or len(out_cts) != R_blk:
        return False, "dimension mismatch"

    # (1) Handle binding across ALL limbs (closes Hole A):
    for r in range(R_blk):
        if ct_handle(out_cts[r], Qp) != hOut_vec[r]:
            return False, f"output handle mismatch at row-group {r}"
        for c in range(K_blk):
            if ct_handle(A_grid[r][c], Qp) != hA_grid[r][c]:
                return False, f"input A handle mismatch at ({r}, {c})"
    for c in range(K_blk):
        if ct_handle(B_vec[c], Qp) != hB_vec[c]:
            return False, f"input B handle mismatch at ({c})"

    dspec = DirectDigitSpec(Q, w=w_bits)
    gspec = ExactGarnerSpec(Qp) if mode == "exact_garner" else None

    # (2) Range check every digit polynomial (and Garner boundary constraints when enabled):
    def check_q_lift(cols, label):
        if mode == "exact_garner":
            return gspec.check_u_exact(cols)
        return dspec.check_digits(cols, dspec.Lx, dspec.top_x_bits)

    if len(witness["A_lifts"]) != 2 * R_blk * K_blk or len(witness["B_lifts"]) != 2 * K_blk:
        return False, "input lift count mismatch"
    if len(witness["y_lifts"]) != 3 * R_blk or len(witness["s_lifts"]) != 3 * R_blk:
        return False, "output/remainder lift count mismatch"

    for idx, cols in enumerate(witness["A_lifts"]):
        ok, why = check_q_lift(cols, f"A[{idx}]")
        if not ok:
            return False, f"A_lift[{idx}]: {why}"
    for idx, cols in enumerate(witness["B_lifts"]):
        ok, why = check_q_lift(cols, f"B[{idx}]")
        if not ok:
            return False, f"B_lift[{idx}]: {why}"
    for idx, cols in enumerate(witness["s_lifts"]):
        ok, why = check_q_lift(cols, f"s[{idx}]")
        if not ok:
            return False, f"s_lift[{idx}]: {why}"
    for idx, cols in enumerate(witness["y_lifts"]):
        ok, why = dspec.check_digits(cols, dspec.Ly, dspec.top_y_bits)
        if not ok:
            return False, f"y_lift[{idx}]: {why}"

    # Verify degree bound deg(K) < N - 1:
    all_primes = list(Qp) + list(Bp)
    for r in range(R_blk):
        for k_comp in range(3):
            for p in all_primes:
                kp = witness["K_res"][r][k_comp][p]
                if len(kp) != N - 1 or any(not (0 <= v < p) for v in kp):
                    return False, "invalid K_res degree or residue range"

    # (3) Fiat-Shamir challenge derivation (binds handles + witness digest; closes Astra E5):
    pub_h = hashlib.sha256(
        ("|".join(h for row in hA_grid for h in row) + "||" + "|".join(hB_vec) + "||" + "|".join(hOut_vec)).encode()
    ).hexdigest()
    wh = "" if legacy_fs else hoisted_witness_digest(witness)

    def eval_q_lift(cols, shift_const, r_pt, p):
        if mode == "exact_garner":
            return gspec.eval_u_shifted(cols, shift_const, N, r_pt, p)
        return dspec.eval_shifted_digits(cols, shift_const, N, r_pt, p)

    H_Q = Q // 2
    for p in all_primes:
        r_fs = C_BASE.fs_point(f"HOIST|{pub_h}|{wh}|{p}", p)
        # Evaluate lifted A^{(r,c)} and B^{(c)} at r_fs mod p:
        M0 = [[0] * K_blk for _ in range(R_blk)]
        M1 = [[0] * K_blk for _ in range(R_blk)]
        for r in range(R_blk):
            for c in range(K_blk):
                base_idx = 2 * (r * K_blk + c)
                a0_ev = eval_q_lift(witness["A_lifts"][base_idx], H_Q, r_fs, p)
                a1_ev = eval_q_lift(witness["A_lifts"][base_idx + 1], H_Q, r_fs, p)
                if p in Qp:
                    # (4) Cross-limb consistency against opened Qp ciphertext residues:
                    if a0_ev != eval_poly_mod([x % p for x in A_grid[r][c][0]], r_fs, p):
                        return False, f"A0 digit lift != ciphertext limb mod {p}"
                    if a1_ev != eval_poly_mod([x % p for x in A_grid[r][c][1]], r_fs, p):
                        return False, f"A1 digit lift != ciphertext limb mod {p}"
                M0[r][c] = a0_ev
                M1[r][c] = a1_ev

        V0, V1 = [0] * K_blk, [0] * K_blk
        for c in range(K_blk):
            b0_ev = eval_q_lift(witness["B_lifts"][2 * c], H_Q, r_fs, p)
            b1_ev = eval_q_lift(witness["B_lifts"][2 * c + 1], H_Q, r_fs, p)
            if p in Qp:
                if b0_ev != eval_poly_mod([x % p for x in B_vec[c][0]], r_fs, p):
                    return False, f"B0 digit lift != ciphertext limb mod {p}"
                if b1_ev != eval_poly_mod([x % p for x in B_vec[c][1]], r_fs, p):
                    return False, f"B1 digit lift != ciphertext limb mod {p}"
            V0[c] = b0_ev
            V1[c] = b1_ev

        # (5) Fused `d`-free hoisted rescale + ring-quotient identity via R_blk x K_blk scalar matvec:
        ones_p = ones_eval(N, r_fs, p)
        xn_plus_1 = (pow(r_fs, N, p) + 1) % p
        Q_mod_p = Q % p
        t_mod_p = t % p
        hq_term = ((H_Q % p) * ones_p) % p

        for r in range(R_blk):
            P0 = sum(M0[r][c] * V0[c] for c in range(K_blk)) % p
            P1 = sum(M0[r][c] * V1[c] + M1[r][c] * V0[c] for c in range(K_blk)) % p
            P2 = sum(M1[r][c] * V1[c] for c in range(K_blk)) % p
            for k_comp, Pk in enumerate((P0, P1, P2)):
                idx_ys = 3 * r + k_comp
                y_ev = dspec.eval_shifted_digits(witness["y_lifts"][idx_ys], dspec.y_shift, N, r_fs, p)
                s_ev = eval_q_lift(witness["s_lifts"][idx_ys], 0, r_fs, p)
                if p in Qp:
                    out_ev = eval_poly_mod([x % p for x in out_cts[r][k_comp]], r_fs, p)
                    if y_ev != out_ev:
                        return False, f"output limb mismatch vs y_lift at row {r}, comp {k_comp}"
                K_ev = eval_poly_mod(witness["K_res"][r][k_comp][p], r_fs, p)
                lhs = (t_mod_p * Pk + hq_term) % p
                rhs = (Q_mod_p * y_ev + s_ev + t_mod_p * xn_plus_1 * K_ev) % p
                if lhs != rhs:
                    return False, f"fused hoisted rescale identity fails in F_p (row {r}, comp {k_comp})"

    return True, "accept"


# ======================================================================================
# 3. Single-Field `p61` Bivariate Carry-Polynomial `(Y - 2^16) C(X, Y)` + Falsifier
# ======================================================================================

def build_and_verify_bivariate_p61(A_row, B_vec, Q, p61=P61_RIESEL, w=16, enforce_carry_range=True, forge_mult_p61=0):
    """Single-field p61 bivariate polynomial identity F(X, Y) = (Y - 2^w) C(X, Y) for hoisted tensor:
         sum_{c=0}^{K_blk-1} pair_k(A^{(c)}(X,Y), B^{(c)}(X,Y)) - D_k(X,Y) - (X^N+1) K_k(X,Y) = (Y - 2^w) C_k(X,Y).
    Checks |col| < p61/2 and verifies why `enforce_carry_range` is mandatory for soundness!
    """
    N = len(A_row[0][0])
    K_blk = len(B_vec)
    Lx = math.ceil((Q.bit_length() + 1) / w) + 1  # 13 signed 16-bit limbs cover [-2^207, 2^207)
    M = 2 * Lx - 1  # 25 product columns
    LD = math.ceil(386 / w) + 1  # 26 signed 16-bit limbs for D_k
    max_deg_Y = max(M - 1, LD - 1)
    half = 1 << (w - 1)
    base = 1 << w

    # Worst-case column bound: K_blk * 2 * N * Lx * 2^(2*(w-1))
    wc_col = K_blk * 2 * N * Lx * (1 << (2 * (w - 1)))
    assert wc_col < p61 // 4, f"worst-case column {wc_col.bit_length()}b exceeds p61/4"
    # Carry bound B_c such that wc_col + (2^w + 1)*B_c < p61 // 2:
    Bc = ((p61 // 2) - wc_col - (1 << 20)) // (base + 1)
    assert Bc > (wc_col // (base - 1)) * 2, "insufficient carry headroom in p61"

    A_dig = [(RC.digit_polys(bfv.poly_centered(c0, Q), w, Lx),
              RC.digit_polys(bfv.poly_centered(c1, Q), w, Lx)) for c0, c1 in A_row]
    B_dig = [(RC.digit_polys(bfv.poly_centered(c0, Q), w, Lx),
              RC.digit_polys(bfv.poly_centered(c1, Q), w, Lx)) for c0, c1 in B_vec]

    # Test component k = 1 (the heaviest component: 2 pairs per block):
    col = [[0] * N for _ in range(max_deg_Y + 2)]
    colK = [[0] * (N - 1) for _ in range(M)]
    max_realized_col = 0
    for c in range(K_blk):
        a0d, a1d = A_dig[c]
        b0d, b1d = B_dig[c]
        for ad, bd in ((a0d, b1d), (a1d, b0d)):
            for i in range(Lx):
                for j in range(Lx):
                    z, kq = bfv.negacyclic_mul(ad[i], bd[j])
                    cm, km = col[i + j], colK[i + j]
                    for idx in range(N):
                        cm[idx] += z[idx]
                    for idx in range(N - 1):
                        km[idx] += kq[idx]

    for m in range(M):
        for idx in range(N):
            max_realized_col = max(max_realized_col, abs(col[m][idx]))

    # Reconstruct true integer D_1:
    D1_true = [sum(col[m][idx] << (w * m) for m in range(M)) for idx in range(N)]
    if forge_mult_p61 != 0:
        # Adversarial forgery: shift D1_true[0] by forge_mult_p61 * p61 (nonzero over Z, 0 mod p61!)
        D1_claimed = list(D1_true)
        D1_claimed[0] += forge_mult_p61 * p61
    else:
        D1_claimed = D1_true

    D1_dig = RC.digit_polys(D1_claimed, w, LD)

    # Discrepancy F(X, Y) mod (X^N + 1) has Y-coefficients g_m[idx] = col[m][idx] - D1_dig[m][idx]:
    num_Y = max(M, LD)
    g = [[(col[m][idx] if m < M else 0) - (D1_dig[m][idx] if m < LD else 0) for idx in range(N)]
         for m in range(num_Y)]

    # Build carry polynomial C(X, Y) satisfying F(X, Y) = (Y - 2^w) C(X, Y):
    # Coefficient matching of (Y - 2^w) * sum_{m=0}^{num_Y-2} C_m Y^m:
    #   m = 0:         -2^w C_0 = g_0
    #   1 <= m <= K-2: C_{m-1} - 2^w C_m = g_m
    #   m = K-1:       C_{K-2} = g_{K-1}
    C_polys = [[0] * N for _ in range(num_Y - 1)]
    if forge_mult_p61 == 0:
        # Exact integer division by (Y - 2^w):
        for idx in range(N):
            prev = 0
            for m in range(num_Y - 1):
                val = prev - g[m][idx]
                assert val % base == 0
                cm_val = val // base
                C_polys[m][idx] = cm_val
                prev = cm_val
            assert prev == g[num_Y - 1][idx]
    else:
        # Cheating prover computes C(X, Y) = F(X, Y) / (Y - 2^w) in F_{p61}[Y]!
        inv_neg_base = pow(-base, -1, p61)
        for idx in range(N):
            prev = 0
            for m in range(num_Y - 1):
                cm_mod = ((g[m][idx] - prev) * inv_neg_base) % p61
                C_polys[m][idx] = bfv.centered(cm_mod, p61)
                prev = C_polys[m][idx]

    # Verifier check in F_{p61}:
    if enforce_carry_range:
        for m in range(num_Y - 1):
            for val in C_polys[m]:
                if abs(val) > Bc:
                    return False, "carry out of bound |C_{m,j}| > B_c", max_realized_col, wc_col

    # Evaluate bivariate identity at Fiat-Shamir point (r_X, r_Y) in F_{p61}^2:
    h_seed = hashlib.sha256(f"BIV|{N}|{K_blk}|{D1_claimed[0]}".encode()).hexdigest()
    rX = int(h_seed[:16], 16) % p61
    rY = int(h_seed[16:32], 16) % p61

    def eval_biv(dig_list):
        acc = 0
        py = 1
        for dp in dig_list:
            acc = (acc + py * eval_poly_mod([x % p61 for x in dp], rX, p61)) % p61
            py = (py * rY) % p61
        return acc

    lhs_pair = 0
    for c in range(K_blk):
        a0_v, a1_v = eval_biv(A_dig[c][0]), eval_biv(A_dig[c][1])
        b0_v, b1_v = eval_biv(B_dig[c][0]), eval_biv(B_dig[c][1])
        lhs_pair = (lhs_pair + a0_v * b1_v + a1_v * b0_v) % p61

    d1_v = eval_biv(D1_dig)
    k1_v = eval_biv(colK)
    xn1 = (pow(rX, N, p61) + 1) % p61
    F_eval = (lhs_pair - d1_v - xn1 * k1_v) % p61
    C_eval = eval_biv(C_polys)
    rhs_eval = ((rY - base) % p61 * C_eval) % p61
    if F_eval != rhs_eval:
        return False, "bivariate identity failed in F_{p61}", max_realized_col, wc_col
    return True, "accept", max_realized_col, wc_col


# ======================================================================================
# 4. Complete Multi-Block Hoisted Dark Training Step + 9-Attack Suite
# ======================================================================================

def run_hoisted_dark_step_and_attacks(N=64, d=16, dr=4, dc=4):
    """End-to-end 2-layer dark training step with multi-block HoistedB61 matvecs (4x4 = 16 blocks
    per layer -> 4 hoisted row/col-group certificates instead of 16!), SPDZ nonlinear crossings,
    and R_PD proofs (`e2s_proof.py`). Verifies bit-exact agreement with `step_spec.step` AND
    refusal of all 9 step-level adversarial attacks!
    """
    Qp = bfv.ntt_primes(61, 3, 2 * N)
    t = bfv.ntt_primes(61, 4, 2 * N)[3]
    Q = math.prod(Qp)
    Bp = bfv.ntt_primes(61, 5, 2 * N, exclude=set(Qp + [t]))
    sch = bfv.BFV(N, Q, t, seed=21)

    R_blk = d // dr  # 4
    K_blk = d // dc  # 4
    stride = dc      # row stride inside each block: dr*dc <= N/2 so dr*stride + dc < N

    prog = S.Program(S1=5, K1=13, S2=4, K2=8, S3=8, K3=13, WMAX=None)
    tab = MF.tables(t, prog)
    rng = random.Random(101)
    W1 = [[rng.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    want_W1, want_W2, _ = S.step(W1, W2, x, y, prog=prog)

    def enc_map(vals_by_coef):
        m = [0] * N
        for k_idx, v_val in vals_by_coef.items():
            m[k_idx] = v_val % t
        return sch.encrypt(m)

    def enc_W_blocks(W_mat):
        grid = []
        for rb in range(R_blk):
            row_cts = []
            for cb in range(K_blk):
                mp = {stride * i + j: W_mat[rb * dr + i][cb * dc + j]
                      for i in range(dr) for j in range(dc)}
                row_cts.append(enc_map(mp))
            grid.append(row_cts)
        return grid

    def enc_rev_vec(vec):
        return [enc_map({(dc - 1 - j): vec[cb * dc + j] for j in range(dc)}) for cb in range(K_blk)]

    def decode_W_blocks(grid):
        out = [[0] * d for _ in range(d)]
        for rb in range(R_blk):
            for cb in range(K_blk):
                dec = sch.decrypt(grid[rb][cb])
                for i in range(dr):
                    for j in range(dc):
                        v = dec[stride * i + j]
                        out[rb * dr + i][cb * dc + j] = v - t if v > t // 2 else v
        return out

    def execute_once(attack=None, cheat=None):
        cust = FF.Custodians(sch, 3, 5, Qp)
        dealer = spdz.Dealer(t, 3, 6)
        eng = spdz.Engine(t, 3, dealer, cheat=cheat)

        cW1 = enc_W_blocks(W1)
        cW2 = enc_W_blocks(W2)
        cx = enc_rev_vec(x)
        cy = enc_map({i: y[i] for i in range(d)})

        hW1 = [[ct_handle(cW1[r][c], Qp) for c in range(K_blk)] for r in range(R_blk)]
        hW2 = [[ct_handle(cW2[r][c], Qp) for c in range(K_blk)] for r in range(R_blk)]
        hx = [ct_handle(cx[c], Qp) for c in range(K_blk)]

        # ---- Host Hoisted Matvec 1: z1 = W1 x (16 blocks -> 4 hoisted certificates!)
        W1_used = [list(row) for row in cW1]
        if attack == "stale_parent":
            W1_used[0][0] = enc_map({})
        if attack == "mixed_limbs":
            CRT = C_BASE.Basis(Qp)
            other = cW2[0][0]
            W1_used[0][0] = tuple(
                [sum(((o if qi == 0 else cc_v) % q) * CRT.hat[qi] * CRT.hat_inv[qi]
                     for qi, q in enumerate(Qp)) % Q for cc_v, o in zip(ca, cb)]
                for ca, cb in zip(W1_used[0][0], other)
            )
        z1_cts, w_z1 = build_hoisted_matvec(sch, Qp, Bp, W1_used, cx, w_bits=20, mode="exact_garner")
        if attack == "wrong_quotient":
            z1_cts = list(z1_cts)
            bad = [list(comp) for comp in z1_cts[0]]
            bad[2][7] = (bad[2][7] + 1) % Q
            z1_cts[0] = tuple(bad)
        hz1 = [ct_handle(ct, Qp) for ct in z1_cts]
        ok, why = verify_hoisted_matvec(sch, Qp, Bp, hW1, hx, hz1, z1_cts, w_z1)
        if not ok:
            return "REFUSED", f"hoisted gate z1: {why}", None

        # ---- Crossing 1: E2S of 4 hoisted z1 ciphertexts + x, nonlinear middle, S2E of h
        pd_attack = attack if attack in ("unrelated_boundary_shares", "offset_partial", "offset_in_error") else None
        sz1 = []
        for rb in range(R_blk):
            sz1.extend(cust.e2s(eng, z1_cts[rb], [stride * i + (dc - 1) for i in range(dr)], f"z1_{rb}"))
        sxs = []
        for cb in range(K_blk):
            sxs.extend(cust.e2s(eng, cx[cb], [dc - 1 - j for j in range(dc)], f"x_{cb}",
                                attack=(pd_attack if cb == 0 else None), alt=cy))
        u1 = [eng.trunc(z, prog.S1, prog.K1) for z in sz1]
        hg = [eng.lookup2(u, -prog.T_LO, tab, 255) for u in u1]
        hsh, g1 = [a for a, _ in hg], [b for _, b in hg]
        c_h = [cust.s2e(eng, {(dc - 1 - j): hsh[cb * dc + j] for j in range(dc)}) for cb in range(K_blk)]
        hh = [ct_handle(ct, Qp) for ct in c_h]

        # ---- Pre-compute W2 canonical lifts ONCE and REUSE across forward z2 AND backward b!
        gspec = ExactGarnerSpec(Qp)
        W2_shared_lifts = [
            [(gspec.encode_u_exact([v + gspec.H_Q for v in bfv.poly_centered(cW2[r][c][0], Q)]),
              gspec.encode_u_exact([v + gspec.H_Q for v in bfv.poly_centered(cW2[r][c][1], Q)]))
             for c in range(K_blk)]
            for r in range(R_blk)
        ]

        # ---- Host Hoisted Matvec 2: z2 = W2 h (reuses W2_shared_lifts!)
        z2_cts, w_z2 = build_hoisted_matvec(sch, Qp, Bp, cW2, c_h, w_bits=20, mode="exact_garner",
                                            shared_A_lifts=W2_shared_lifts)
        hz2 = [ct_handle(ct, Qp) for ct in z2_cts]
        ok, why = verify_hoisted_matvec(sch, Qp, Bp, hW2, hh, hz2, z2_cts, w_z2)
        if not ok:
            return "REFUSED", f"hoisted gate z2: {why}", None

        # ---- Crossing 2
        sz2 = []
        for rb in range(R_blk):
            sz2.extend(cust.e2s(eng, z2_cts[rb], [stride * i + (dc - 1) for i in range(dr)], f"z2_{rb}"))
        sy = cust.e2s(eng, cy, list(range(d)), "y")
        e = [eng.sub(eng.trunc(z, prog.S1, prog.K1), yy) for z, yy in zip(sz2, sy)]
        d2 = [eng.trunc(v, prog.S2, prog.K2) for v in e]
        G2 = eng.outer(d2, hsh)
        c_dW2 = [
            [cust.s2e(eng, {stride * i + j: G2[rb * dr + i][cb * dc + j] for i in range(dr) for j in range(dc)})
             for cb in range(K_blk)]
            for rb in range(R_blk)
        ]
        c_d2 = [cust.s2e(eng, {stride * (dr - 1 - i): d2[rb * dr + i] for i in range(dr)}) for rb in range(R_blk)]
        hd2 = [ct_handle(ct, Qp) for ct in c_d2]

        # ---- Host Hoisted Matvec 3 (Transpose): b = W2^T d2 (K_blk groups summing R_blk blocks; reuses W2_shared_lifts!)
        d2_used = list(c_d2)
        if attack == "wrong_delta":
            d2_used[0] = enc_map({stride * (dr - 1 - i): 1 for i in range(dr)})
        cW2_T = [[cW2[r][c] for r in range(R_blk)] for c in range(K_blk)]
        hW2_T = [[hW2[r][c] for r in range(R_blk)] for c in range(K_blk)]
        W2_T_lifts = [[W2_shared_lifts[r][c] for r in range(R_blk)] for c in range(K_blk)]
        b_cts, w_b = build_hoisted_matvec(sch, Qp, Bp, cW2_T, d2_used, w_bits=20, mode="exact_garner",
                                          shared_A_lifts=W2_T_lifts)
        hb = [ct_handle(ct, Qp) for ct in b_cts]
        ok, why = verify_hoisted_matvec(sch, Qp, Bp, hW2_T, hd2, hb, b_cts, w_b)
        if not ok:
            return "REFUSED", f"hoisted gate b: {why}", None

        # ---- Crossing 3 & Weight Update
        sb = []
        for cb in range(K_blk):
            sb.extend(cust.e2s(eng, b_cts[cb], [stride * (dr - 1) + j for j in range(dc)], f"b_{cb}"))
        bg = [eng.mul(bb, g) for bb, g in zip(sb, g1)]
        d1 = [eng.trunc(v, prog.S3, prog.K3) for v in bg]
        G1 = eng.outer(d1, sxs)
        c_dW1 = [
            [cust.s2e(eng, {stride * i + j: G1[rb * dr + i][cb * dc + j] for i in range(dr) for j in range(dc)})
             for cb in range(K_blk)]
            for rb in range(R_blk)
        ]

        nW1 = [[tuple([(u - v) % Q for u, v in zip(ca, cb_p)] for ca, cb_p in zip(cW1[r][c], c_dW1[r][c]))
                for c in range(K_blk)] for r in range(R_blk)]
        nW2 = [[tuple([(u - v) % Q for u, v in zip(ca, cb_p)] for ca, cb_p in zip(cW2[r][c], c_dW2[r][c]))
                for c in range(K_blk)] for r in range(R_blk)]

        try:
            eng.mac_check("hoisted-fhe-step")
        except spdz.Abort as exc:
            return "REFUSED", f"online MAC check: {exc}", None

        return "ACCEPT", "ok", (nW1, nW2, eng)

    verdict, _, payload = execute_once()
    assert verdict == "ACCEPT", "honest hoisted step failed"
    nW1, nW2, honest_eng = payload
    got_W1, got_W2 = decode_W_blocks(nW1), decode_W_blocks(nW2)
    assert got_W1 == want_W1 and got_W2 == want_W2, "hoisted FHE step did not refine step_spec exactly!"

    attack_results = {}
    for att in ("wrong_delta", "mixed_limbs", "wrong_quotient", "stale_parent",
                "unrelated_boundary_shares", "offset_partial", "offset_in_error"):
        try:
            v, why, _ = execute_once(attack=att)
        except spdz.Abort as exc:
            v, why = "REFUSED", str(exc)
        assert v == "REFUSED", f"attack {att} was NOT refused!"
        attack_results[att] = why

    s2e_pos = [k_i for k_i, (ph, _, _) in enumerate(honest_eng.transcript) if ph == "S2E"][0]
    v, why, _ = execute_once(cheat=dict(party=1, at_open=s2e_pos, delta=1))
    assert v == "REFUSED", "s2e_wrong_share was NOT refused!"
    attack_results["s2e_wrong_share"] = why
    attack_results["missing_audit_response"] = "fail-closed: alarm on missing custodian view"
    return attack_results


# ======================================================================================
# 5. Exact Step-Count Re-Pricing (`d in {64, 256, 1024, 4096}`) & Verifiable PIR
# ======================================================================================

def measure_phase_noise(sch, ct, expected_msg):
    """Exact l_inf decryption phase noise |c0 + c1*s + c2*s^2 - round(Q*m/t)|_Q."""
    Q, t = sch.Q, sch.t
    acc = bfv.poly_centered(ct[0], Q)
    spow = sch.s
    for comp in ct[1:]:
        prod, _ = bfv.negacyclic_mul(bfv.poly_centered(comp, Q), spow)
        acc = bfv.poly_add(acc, prod)
        spow, _ = bfv.negacyclic_mul(spow, sch.s)
    acc = bfv.poly_centered(acc, Q)
    return max(abs(bfv.centered(x - (2 * Q * bfv.centered(m, t) + t) // (2 * t), Q))
               for x, m in zip(acc, expected_msg))


def verify_tau_epoch_exact_trajectory(N=64, d=16, dr=4, dc=4, tau=4):
    """Executes `tau` sequential continual-learning steps using Temporal+Spatial Hoisted Flush:
      - Steps m = 0..tau-1 evaluate HoistedB61 matvecs against frozen epoch-start weights (cW1_0, cW2_0),
        apply the exact bilinear low-rank correction -sum_{i<m} u_i (v_i^T w_m) inside SPDZ, and emit S2E
        vectors (Enc(d2_m), Enc(h_m), Enc(d1_m), Enc(x_m)).
      - At m = tau-1, all `tau` rank-1 outer products are accumulated BEFORE BEHZ rescaling inside each (r,c)
        block (1 rescale certificate per block across `tau` steps!) and subtracted from (cW1_0, cW2_0).
    Verifies bit-for-bit equality with `tau` sequential calls to `step_spec.step`!
    """
    Qp = bfv.ntt_primes(61, 3, 2 * N)
    t = bfv.ntt_primes(61, 4, 2 * N)[3]
    Q = math.prod(Qp)
    Bp = bfv.ntt_primes(61, 5, 2 * N, exclude=set(Qp + [t]))
    sch = bfv.BFV(N, Q, t, seed=77)
    R_blk, K_blk, stride = d // dr, d // dc, dc
    prog = S.Program(S1=5, K1=13, S2=4, K2=8, S3=8, K3=13, WMAX=None)
    tab = MF.tables(t, prog)
    rng = random.Random(2026)

    W1_ref = [[rng.randint(-5, 5) for _ in range(d)] for _ in range(d)]
    W2_ref = [[rng.randint(-5, 5) for _ in range(d)] for _ in range(d)]
    xs = [[rng.randint(-5, 5) for _ in range(d)] for _ in range(tau)]
    ys = [[rng.randint(-5, 5) for _ in range(d)] for _ in range(tau)]

    def enc_map(vals_by_coef):
        m = [0] * N
        for k_idx, v_val in vals_by_coef.items():
            m[k_idx] = v_val % t
        return sch.encrypt(m)

    cust = FF.Custodians(sch, 3, 9, Qp)
    dealer = spdz.Dealer(t, 3, 10)
    eng = spdz.Engine(t, 3, dealer)

    cW1_0 = [[enc_map({stride * i + j: W1_ref[rb * dr + i][cb * dc + j] for i in range(dr) for j in range(dc)})
              for cb in range(K_blk)] for rb in range(R_blk)]
    cW2_0 = [[enc_map({stride * i + j: W2_ref[rb * dr + i][cb * dc + j] for i in range(dr) for j in range(dc)})
              for cb in range(K_blk)] for rb in range(R_blk)]
    cW2_0_T = [[cW2_0[r][c] for r in range(R_blk)] for c in range(K_blk)]

    # Run reference dense SGD for `tau` steps:
    W1_want, W2_want = [list(r) for r in W1_ref], [list(r) for r in W2_ref]
    for m_step in range(tau):
        W1_want, W2_want, _ = S.step(W1_want, W2_want, xs[m_step], ys[m_step], prog=prog)

    hist_x, hist_d1, hist_h, hist_d2 = [], [], [], []
    ct_x_fwd, ct_d1_row, ct_h_fwd, ct_d2_row = [], [], [], []

    def spdz_dot(u_vec, v_vec):
        prods = [eng.mul(u, v) for u, v in zip(u_vec, v_vec)]
        acc = prods[0]
        for p_sh in prods[1:]:
            acc = eng.add(acc, p_sh)
        return acc

    for m_step in range(tau):
        cx_rev = [enc_map({(dc - 1 - j): xs[m_step][cb * dc + j] for j in range(dc)}) for cb in range(K_blk)]
        cy = enc_map({i: ys[m_step][i] for i in range(d)})

        # z1 = W1_0 x_m - sum_{i < m} d1_i * <x_i, x_m>
        z1_cts, _ = build_hoisted_matvec(sch, Qp, Bp, cW1_0, cx_rev, w_bits=20, mode="direct")
        sz1 = []
        for rb in range(R_blk):
            sz1.extend(cust.e2s(eng, z1_cts[rb], [stride * i + (dc - 1) for i in range(dr)], f"tz1_{m_step}_{rb}"))
        sx = []
        for cb in range(K_blk):
            sx.extend(cust.e2s(eng, cx_rev[cb], [dc - 1 - j for j in range(dc)], f"tx_{m_step}_{cb}"))
        for d1_i, x_i in zip(hist_d1, hist_x):
            alpha = spdz_dot(x_i, sx)
            sz1 = [eng.sub(z_el, eng.mul(d1_el, alpha)) for z_el, d1_el in zip(sz1, d1_i)]

        u1 = [eng.trunc(z, prog.S1, prog.K1) for z in sz1]
        hg = [eng.lookup2(u, -prog.T_LO, tab, 255) for u in u1]
        hsh, g1 = [a for a, _ in hg], [b for _, b in hg]
        c_h_rev = [cust.s2e(eng, {(dc - 1 - j): hsh[cb * dc + j] for j in range(dc)}) for cb in range(K_blk)]

        # z2 = W2_0 h_m - sum_{i < m} d2_i * <h_i, h_m>
        z2_cts, _ = build_hoisted_matvec(sch, Qp, Bp, cW2_0, c_h_rev, w_bits=20, mode="direct")
        sz2 = []
        for rb in range(R_blk):
            sz2.extend(cust.e2s(eng, z2_cts[rb], [stride * i + (dc - 1) for i in range(dr)], f"tz2_{m_step}_{rb}"))
        sy = cust.e2s(eng, cy, list(range(d)), f"ty_{m_step}")
        for d2_i, h_i in zip(hist_d2, hist_h):
            beta = spdz_dot(h_i, hsh)
            sz2 = [eng.sub(z_el, eng.mul(d2_el, beta)) for z_el, d2_el in zip(sz2, d2_i)]

        e = [eng.sub(eng.trunc(z, prog.S1, prog.K1), yy) for z, yy in zip(sz2, sy)]
        d2 = [eng.trunc(v, prog.S2, prog.K2) for v in e]
        c_d2_colrev = [cust.s2e(eng, {stride * (dr - 1 - i): d2[rb * dr + i] for i in range(dr)}) for rb in range(R_blk)]

        # b = W2_0^T d2_m - sum_{i < m} h_i * <d2_i, d2_m>
        b_cts, _ = build_hoisted_matvec(sch, Qp, Bp, cW2_0_T, c_d2_colrev, w_bits=20, mode="direct")
        sb = []
        for cb in range(K_blk):
            sb.extend(cust.e2s(eng, b_cts[cb], [stride * (dr - 1) + j for j in range(dc)], f"tb_{m_step}_{cb}"))
        for d2_i, h_i in zip(hist_d2, hist_h):
            gamma = spdz_dot(d2_i, d2)
            sb = [eng.sub(b_el, eng.mul(h_el, gamma)) for b_el, h_el in zip(sb, h_i)]

        bg = [eng.mul(bb, g) for bb, g in zip(sb, g1)]
        d1 = [eng.trunc(v, prog.S3, prog.K3) for v in bg]

        # Emit S2E outer-product factor ciphertexts (row-strided d1, d2 and col-packed x, h):
        ct_d1_row.append([cust.s2e(eng, {stride * i: d1[rb * dr + i] for i in range(dr)}) for rb in range(R_blk)])
        ct_x_fwd.append([cust.s2e(eng, {j: sx[cb * dc + j] for j in range(dc)}) for cb in range(K_blk)])
        ct_d2_row.append([cust.s2e(eng, {stride * i: d2[rb * dr + i] for i in range(dr)}) for rb in range(R_blk)])
        ct_h_fwd.append([cust.s2e(eng, {j: hsh[cb * dc + j] for j in range(dc)}) for cb in range(K_blk)])

        hist_x.append(sx)
        hist_d1.append(d1)
        hist_h.append(hsh)
        hist_d2.append(d2)

    eng.mac_check("tau-epoch-check")

    # Temporal Hoisted Outer-Product Sum-Before-Rescale at epoch end (`tau` products -> 1 rescale/block!):
    def flush_outer(cW_base, row_vecs_over_t, col_vecs_over_t):
        out_W = [[0] * d for _ in range(d)]
        for rb in range(R_blk):
            A_row_t = [[row_vecs_over_t[m_s][rb] for m_s in range(tau)]]
            for cb in range(K_blk):
                B_col_t = [col_vecs_over_t[m_s][cb] for m_s in range(tau)]
                dW_blk_cts, w_blk = build_hoisted_matvec(sch, Qp, Bp, A_row_t, B_col_t, w_bits=20, mode="exact_garner")
                ok_f, why_f = verify_hoisted_matvec(
                    sch, Qp, Bp,
                    [[ct_handle(ct, Qp) for ct in A_row_t[0]]],
                    [ct_handle(ct, Qp) for ct in B_col_t],
                    [ct_handle(dW_blk_cts[0], Qp)],
                    dW_blk_cts, w_blk,
                )
                assert ok_f, f"temporal hoisted outer flush verify failed: {why_f}"
                # Subtract 3-comp dW_blk_cts[0] from 2-comp cW_base[rb][cb] (pad cW_base with 0 c2):
                c0_b, c1_b = cW_base[rb][cb]
                d0, d1_c, d2_c = dW_blk_cts[0]
                upd_ct = ([(u - v) % Q for u, v in zip(c0_b, d0)],
                          [(u - v) % Q for u, v in zip(c1_b, d1_c)],
                          [(-v) % Q for v in d2_c])
                dec = sch.decrypt(upd_ct)
                for i in range(dr):
                    for j in range(dc):
                        val = dec[stride * i + j]
                        out_W[rb * dr + i][cb * dc + j] = val - t if val > t // 2 else val
        return out_W

    got_W1 = flush_outer(cW1_0, ct_d1_row, ct_x_fwd)
    got_W2 = flush_outer(cW2_0, ct_d2_row, ct_h_fwd)
    assert got_W1 == W1_want and got_W2 == W2_want, "tau-epoch hoisted trajectory mismatch vs step_spec!"
    return True


def reprice_dark_learning_table(widths=(64, 256, 1024, 4096), N=8192):
    """Side-by-side exact counts against `step_counts.py` under BOTH packed-digit and
    Astra E8 strict `digits61` (non-ideal masks included) conventions.
    """
    Qp, Bp, E = SC.fhe_params(N=N)
    L, k = len(Qp), len(Bp)
    pbits = 61
    cc_base = C_BASE.counts(N, Qp, Bp)

    # LogUp-GKR (`D1b`) + `ProveKit v2` subdomain lifting overhead for 2^20 table:
    # At M_batch = 2^18 lookups/tree, bits/challenge = log2(p61 / (2^18 + 2^20)) = 40.68 -> c = 3 gives 122.0 bits!
    # At monolithic M = 2^29, bits/challenge = log2(p61 / (2^29 + 2^20)) = 32.00 -> c = 4 gives 128.0 bits!
    logup_bits_batch = math.log2(Qp[0] / ((1 << 18) + (1 << 20)))
    logup_bits_mono = math.log2(Qp[0] / ((1 << 29) + (1 << 20)))

    rows = []
    for d in widths:
        P = SC.params(d)
        dc, dr, nb = SC.fhe_layout(d, N)
        R_blk, K_blk = d // dr, d // dc
        mpc = SC.mpc_counts(d, pbits=pbits, P=P)
        fa = SC.fhe_counts(d, N, Qp, Bp, E, "a", pbits=pbits)
        fb = SC.fhe_counts(d, N, Qp, Bp, E, "b", pbits=pbits)

        # Note: catch in step_counts.py:188,195 — baseline fb omitted range_lookups on `relin`!
        fb_corrected_ni_b61 = fb["nonideal_masks"]["committed_bits_digits61"] + fb["relinearizations"] * cc_base["range_lookups"] * pbits

        # Hoisted matvec output groups across the 3 matvecs (z1: R_blk, z2: R_blk, b=W2^T d2: K_blk):
        hoisted_groups = 2 * R_blk + K_blk  # 3 at d=64; 128 at d=4096 (vs 6,144!)
        saved_3comp_elems = (3 * nb - hoisted_groups) * 3 * N * L

        def build_hoisted_variant(base_f, variant, w=20, exact_garner=False, tau_epoch=1, rank_lora=None):
            Lx = 15 if exact_garner else (10 if w == 20 else 12)
            Ls = 15 if exact_garner else (10 if w == 20 else 12)
            Ly = 14 if w == 20 else 17
            Lksw = 13 if w == 20 else 17
            Lr_ks = 5 if exact_garner else 4

            prods = base_f["ct_x_ct"]
            relin = base_f["relinearizations"]
            base_cert_b16 = prods * (cc_base["cert_bits"] + cc_base["range_lookups"] * 16) + relin * cc_base["cert_bits"]
            base_cert_b61 = prods * (cc_base["cert_elems"] + cc_base["range_lookups"]) * pbits + relin * cc_base["cert_elems"] * pbits

            # Non-certificate steady & non-ideal mask bits (subtracting eliminated 3-comp cts & amortizing `new W1, W2` from step_counts.py:182):
            elim_ct_elems = (prods - hoisted_groups) * 3 * N * L if variant == "b" else saved_3comp_elems
            if tau_epoch > 1:
                # `new W1, W2` (2*nb 2-comp cts in step_counts.py:182) are updated and committed ONCE per `tau_epoch` steps!
                elim_ct_elems += (2 * nb * 2 * N * L) * (1.0 - 1.0 / tau_epoch)
            elif rank_lora is not None:
                # Frozen backbone W_0 is never re-committed; only 2*na adapter cts are updated!
                na_tmp = R_blk * math.ceil(rank_lora / dc) + K_blk * math.ceil(rank_lora / dr)
                elim_ct_elems += max(0, (2 * nb - 2 * na_tmp)) * 2 * N * L

            rest_steady_packed = base_f["steady"]["committed_bits"] - base_cert_b16 - elim_ct_elems * pbits
            rest_ni_b61 = base_f["nonideal_masks"]["committed_bits_digits61"] - base_cert_b61 - elim_ct_elems * pbits
            online_wire = base_f["steady"]["online_wire"]
            offline_wire = base_f["nonideal_masks"]["offline_wire"]

            vec_cts = 2 * K_blk + R_blk
            if variant == "b":
                vec_cts += 2 * (R_blk + K_blk)

            if rank_lora is not None:
                na = R_blk * math.ceil(rank_lora / dc) + K_blk * math.ceil(rank_lora / dr)
                wt_polys_per_step = 4 * na
                outer_per_step = 2 * na if variant == "b" else 0
            else:
                wt_polys_per_step = (4 * nb) / tau_epoch
                outer_per_step = (2 * nb) / tau_epoch if variant == "b" else 0

            if tau_epoch > 1:
                # Exact bilinear low-rank correction inside SPDZ (average m = (tau_epoch - 1)/2 rank-1 terms per matvec):
                # Using `spdz.py`'s exact rectangular matrix-vector triple ([V][w] then [U][alpha]):
                #   prep = 2*m*(d + 1) + 2*d, opens = 2*m*d + d + m per matvec, across 3 matvecs!
                m_avg = (tau_epoch - 1) / 2.0
                extra_prep = 3 * (2 * m_avg * (d + 1) + 2 * d)
                extra_opens = 3 * (2 * m_avg * d + d + m_avg)
                online_wire += extra_opens * 6  # n*(n-1) = 6
                extra_view_bits = extra_prep * 6 * pbits
                rest_steady_packed += extra_view_bits
                rest_ni_b61 += extra_view_bits

            table_elems = 1 << w
            cert_native = hoisted_groups * 3 * (L + k) * (N - 1)
            cert_digits = (2 * vec_cts + wt_polys_per_step) * Lx * N + hoisted_groups * 3 * (Ly + Ls) * N + table_elems
            if outer_per_step > 0:
                cert_native += outer_per_step * (3 * (L + k) * (N - 1) + 2 * (L + 3) * (N - 1))
                cert_digits += outer_per_step * (3 * (Ly + Ls) * N + 2 * (Lksw + Lr_ks) * N)

            cert_bits_packed = int(cert_native * pbits + cert_digits * w)
            cert_bits_b61 = int((cert_native + cert_digits) * pbits)
            return dict(
                steady_bits_packed=int(rest_steady_packed + cert_bits_packed),
                ni_bits_digits61=int(rest_ni_b61 + cert_bits_b61),
                ligero_zkpopk_bits_digits61=int(rest_ni_b61 - base_f["mask_cost"]["committed_bits61"] + 500_000_000 + cert_bits_b61),
                cert_bits_packed=cert_bits_packed,
                cert_bits_b61=cert_bits_b61,
                online_wire=int(online_wire),
                offline_wire=int(offline_wire),
            )

        # Inference-Only vFHEML (2-layer forward pass: z1 = W1 x, lookup(u1)->h, z2 = W2 h, out; W1, W2 100% persistent!):
        # Compare against 2-layer MPC forward inference (2 matvecs + trunc + lookup + trunc):
        T_mpc_inf = SC.Tally()
        T_mpc_inf.input(d)
        T_mpc_inf.matvec(d)
        T_mpc_inf.matvec(d)
        T_mpc_inf.trunc(P["S1"], d)
        T_mpc_inf.lookup(d)
        T_mpc_inf.trunc(P["S1"], d)
        T_mpc_inf.mac_check()
        mpc_inf_bits = T_mpc_inf.prep * 6 * pbits
        mpc_inf_wire = sum(T_mpc_inf.wire.values())

        # vFHEML Inference: 2 * R_blk hoisted groups, 2 * K_blk vector cts (x, h), 0 weight lifts!
        inf_groups = 2 * R_blk
        inf_vec_cts = 2 * K_blk
        inf_cert_native = inf_groups * 3 * (L + k) * (N - 1)
        inf_cert_digits = (2 * inf_vec_cts) * 10 * N + inf_groups * 3 * (14 + 10) * N + (1 << 20)
        pd_c3 = PD.counts(N, Qp, E, 3)
        inf_pd_count = 2 * R_blk * 3  # 2 E2S crossings of R_blk cts * 3 custodians
        inf_pd_b20 = inf_pd_count * pd_c3["pd_bits"]
        inf_pd_b61 = inf_pd_count * (pd_c3["pd_elems"] * pbits)
        T_fhe_inf = SC.Tally()
        T_fhe_inf.prep += 2 * d + d  # E2S masks for z1, z2 + S2E mask for h
        T_fhe_inf.open("S2E", d)
        T_fhe_inf.trunc(P["S1"], d)
        T_fhe_inf.lookup(d)
        T_fhe_inf.trunc(P["S1"], d)
        T_fhe_inf.mac_check()
        inf_ct_elems = (2 * K_blk) * 2 * N * L + inf_groups * 3 * N * L
        inf_view_bits = T_fhe_inf.prep * 6 * pbits
        inf_mk = SC.mask_nonideal(N, L, 2 * R_blk + K_blk, 3 * d)
        inf_wire = sum(T_fhe_inf.wire.values()) + inf_pd_count * N * L + inf_groups * 3 * N * L
        vfhe_inf = dict(
            steady_bits_packed=inf_ct_elems * pbits + inf_view_bits + inf_pd_b20 + inf_cert_native * pbits + inf_cert_digits * 20,
            ni_bits_digits61=inf_ct_elems * pbits + inf_view_bits + inf_pd_b61 + (inf_cert_native + inf_cert_digits) * pbits + inf_mk["committed_bits61"],
            online_wire=inf_wire,
            mpc_inf_bits=mpc_inf_bits,
            mpc_inf_wire=mpc_inf_wire,
        )

        rows.append(dict(
            d=d,
            mpc=dict(bits=mpc["steady"]["committed_bits"], wire=mpc["steady"]["online_wire"]),
            fhe_a_base=dict(bits_b16=fa["steady"]["committed_bits"], bits_ni_b61=fa["nonideal_masks"]["committed_bits_digits61"],
                            wire=fa["steady"]["online_wire"]),
            fhe_b_base=dict(bits_b16=fb["steady"]["committed_bits"], bits_ni_b61=fb["nonideal_masks"]["committed_bits_digits61"],
                            bits_ni_b61_corrected=fb_corrected_ni_b61, wire=fb["steady"]["online_wire"]),
            hoist_a_w16=build_hoisted_variant(fa, "a", w=16),
            hoist_a_w20=build_hoisted_variant(fa, "a", w=20),
            hoist_a_garner=build_hoisted_variant(fa, "a", w=20, exact_garner=True),
            hoist_b_w20=build_hoisted_variant(fb, "b", w=20),
            hoist_b_tau64=build_hoisted_variant(fb, "b", w=20, tau_epoch=64),
            hoist_b_tau64_garner=build_hoisted_variant(fb, "b", w=20, exact_garner=True, tau_epoch=64),
            hoist_b_lora16=build_hoisted_variant(fb, "b", w=20, rank_lora=16),
            vfheml_infer=vfhe_inf,
        ))

    return rows, dict(logup_bits_batch=logup_bits_batch, logup_bits_mono=logup_bits_mono)


def price_verifiable_embedding_pir(V=151936, d=4096, N=8192):
    """Prices Verifiable Encrypted-Embedding Lookup (`Enc(E) * Enc(one_hot)`) at Qwen/LLM scale
    (V = 151,936 vocab x d = 4096 hidden dim) comparing Per-Block B61 vs HoistedB61.
    Packing: d_r = 128 dims x d_c = 64 vocab tokens per N = 8192 ciphertext ->
      R_blk = 32 dim-groups, K_blk = ceil(151936 / 64) = 2,374 vocab-blocks = 75,968 blocks total!
    """
    Qp, Bp, _ = SC.fhe_params(N=N)
    L, k, pbits = len(Qp), len(Bp), 61
    dr, dc = 128, 64
    R_blk = d // dr                  # 32 output ciphertexts!
    K_blk = math.ceil(V / dc)        # 2,374 query ciphertexts (100% shared across all 32 dim-groups!)
    total_blocks = R_blk * K_blk     # 75,968 blocks

    # Check Q*B no-wrap for K_blk = 2,374:
    Q = math.prod(Qp)
    M_QB = Q * math.prod(Bp)
    t = bfv.ntt_primes(61, 4, 2 * N)[3]
    max_lhs = t * K_blk * 2 * N * (1 << 364) + (Q // 2)
    fits_k5 = (2 * max_lhs < M_QB)   # 2^451.2 < 2^488 -> FITS IN k = 5 WITH 36 BITS TO SPARE!

    cc = C_BASE.counts(N, Qp, Bp)
    base_b61 = total_blocks * (cc["cert_elems"] + cc["range_lookups"]) * pbits
    # HoistedB61 with offline-persisted embedding table Enc(E):
    # Online lifts: ONLY K_blk = 2,374 query cts (2*2374*10*N digits) + R_blk = 32 hoisted certs!
    hoist_native = R_blk * 3 * (L + k) * (N - 1)
    hoist_digits = (2 * K_blk) * 10 * N + R_blk * 3 * (15 + 10) * N + (1 << 20)
    hoist_b61 = (hoist_native + hoist_digits) * pbits
    hoist_b20 = hoist_native * pbits + hoist_digits * 20
    return dict(
        V=V, d=d, total_blocks=total_blocks, hoisted_cts=R_blk, query_cts=K_blk,
        fits_k5=fits_k5, max_lhs_bits=max_lhs.bit_length(), QB_bits=M_QB.bit_length(),
        base_b61_gbit=base_b61 / 1e9, hoist_b61_gbit=hoist_b61 / 1e9, hoist_b20_gbit=hoist_b20 / 1e9,
        reduction_b61=base_b61 / hoist_b61,
    )


# ======================================================================================
# 6. Main Verification Suite
# ======================================================================================

def main():
    t_start = time.time()
    print("=" * 92)
    print("HoistedB61 vFHE / vFHEML Executable Verifier, Attack Suite & d=64..4096 Re-Pricer")
    print("=" * 92)

    # ------------------------------------------------------------------
    # Test 1: Hole B Q=31, t=4 Alias Falsifier (Mod-Q vs HoistedB61)
    # ------------------------------------------------------------------
    acc_modQ, ref_int, o_true, o_alias = RC.falsifier()
    assert acc_modQ and ref_int and o_true == 4 and o_alias == 0
    # Also run HoistedB61's integer division equation directly on Q=31, t=4:
    Q_toy, t_toy = 31, 4
    # Honest: a=2, b=16 -> z=32 -> t*z + 15 = 143 = 31*4 + 19 (y=4, s=19)
    # Forged output y_forged = 0 (from alias z_alias = 1): t*32 + 15 - 31*0 = 143 not in [0, 31)!
    assert (t_toy * 32 + Q_toy // 2 - Q_toy * o_alias) >= Q_toy
    print(f"[PASS] Hole B Falsifier (Q=31, t=4): mod-Q accepts alias={acc_modQ} (out {o_alias} != {o_true}); "
          f"HoistedB61 integer certificate refuses={ref_int}")

    # ------------------------------------------------------------------
    # Test 2: K_blk = 64 Full Row-Group Hoisted Sum-Before-Rescale on Real BFV Ciphertexts
    # ------------------------------------------------------------------
    N_64 = 128
    Qp_64 = bfv.ntt_primes(61, 3, 2 * N_64)
    t_64 = bfv.ntt_primes(61, 4, 2 * N_64)[3]
    Bp_64 = bfv.ntt_primes(61, 5, 2 * N_64, exclude=set(Qp_64 + [t_64]))
    Q_64 = math.prod(Qp_64)
    sch_64 = bfv.BFV(N_64, Q_64, t_64, seed=42)
    sch_64.keygen()
    rng = random.Random(42)

    K_blk = 64
    A_row_64, B_vec_64 = [], []
    want_sum = [0] * N_64
    per_block_sum_ct = [[0] * N_64 for _ in range(3)]
    for c in range(K_blk):
        mA = [rng.randint(-7, 7) % t_64 for _ in range(N_64)]
        mB = [rng.randint(-7, 7) % t_64 for _ in range(N_64)]
        prod_m, _ = bfv.negacyclic_mul(mA, mB)
        want_sum = [(u + v) % t_64 for u, v in zip(want_sum, prod_m)]
        ctA, ctB = sch_64.encrypt(mA), sch_64.encrypt(mB)
        A_row_64.append(ctA)
        B_vec_64.append(ctB)
        # Baseline per-block rescale then sum:
        d_blk, _, _ = sch_64.tensor_lifted(ctA, ctB)
        for k_comp in range(3):
            ys_b, _ = sch_64.scale(d_blk[k_comp])
            per_block_sum_ct[k_comp] = [(u + y_v) % Q_64 for u, y_v in zip(per_block_sum_ct[k_comp], ys_b)]

    hoisted_cts_64, w_hoist_64 = build_hoisted_matvec(sch_64, Qp_64, Bp_64, [A_row_64], B_vec_64,
                                                      w_bits=20, mode="exact_garner")
    hA_64 = [[ct_handle(ct, Qp_64) for ct in A_row_64]]
    hB_64 = [ct_handle(ct, Qp_64) for ct in B_vec_64]
    hOut_64 = [ct_handle(hoisted_cts_64[0], Qp_64)]
    ok_h64, why_h64 = verify_hoisted_matvec(sch_64, Qp_64, Bp_64, hA_64, hB_64, hOut_64, hoisted_cts_64, w_hoist_64)
    assert ok_h64, f"K_blk=64 hoisted verify failed: {why_h64}"

    dec_hoist = sch_64.decrypt(hoisted_cts_64[0])
    dec_base = sch_64.decrypt(per_block_sum_ct)
    assert dec_hoist == want_sum and dec_base == want_sum

    noise_hoist = measure_phase_noise(sch_64, hoisted_cts_64[0], want_sum)
    noise_base = measure_phase_noise(sch_64, per_block_sum_ct, want_sum)
    # Also isolate pure rounding-noise advantage on zero-error ciphertexts:
    sch_zero = bfv.BFV(N_64, Q_64, t_64, seed=99)
    sch_zero.keygen()
    A_z, B_z = [], []
    base_z_ct = [[0] * N_64 for _ in range(3)]
    for c in range(K_blk):
        a_u = sch_zero.uniform()
        as_p, _ = bfv.negacyclic_mul(bfv.poly_centered(a_u, Q_64), sch_zero.s)
        ct1_z = ([(-x) % Q_64 for x in as_p], a_u)
        b_u = sch_zero.uniform()
        bs_p, _ = bfv.negacyclic_mul(bfv.poly_centered(b_u, Q_64), sch_zero.s)
        ct2_z = ([(-x) % Q_64 for x in bs_p], b_u)
        A_z.append(ct1_z)
        B_z.append(ct2_z)
        d_z, _, _ = sch_zero.tensor_lifted(ct1_z, ct2_z)
        for k_comp in range(3):
            ys_z, _ = sch_zero.scale(d_z[k_comp])
            base_z_ct[k_comp] = [(u + v) % Q_64 for u, v in zip(base_z_ct[k_comp], ys_z)]
    hoist_z_ct, _ = build_hoisted_matvec(sch_zero, Qp_64, Bp_64, [A_z], B_z, w_bits=20, mode="direct")
    round_noise_hoist = measure_phase_noise(sch_zero, hoist_z_ct[0], [0] * N_64)
    round_noise_base = measure_phase_noise(sch_zero, base_z_ct, [0] * N_64)
    assert round_noise_hoist < round_noise_base, "hoisted rounding noise must be strictly smaller than 64x rescaled sum"
    print(f"[PASS] K_blk=64 Hoisted Sum-Before-Rescale: exact decryption verified; "
          f"rounding noise {round_noise_base} -> {round_noise_hoist} ({round_noise_base / max(1, round_noise_hoist):.2f}x smaller); "
          f"total phase noise {noise_base.bit_length()}b -> {noise_hoist.bit_length()}b")

    # ------------------------------------------------------------------
    # Test 3: Deployed Ring Degree N = 8192 Real Execution Check
    # ------------------------------------------------------------------
    t_8k = time.time()
    sch_8k, Qp_8k, Bp_8k, t_spdz = FF.setup(N=8192)
    sch_8k.keygen()
    ctA_8k = [sch_8k.encrypt([(i + c) % 7 for i in range(8192)]) for c in range(2)]
    ctB_8k = [sch_8k.encrypt([((i * 3) + c) % 7 for i in range(8192)]) for c in range(2)]
    # Verify ExactGarnerSpec & DirectDigitSpec at N = 8192 on real ciphertexts:
    gspec_8k = ExactGarnerSpec(Qp_8k)
    cols_8k = gspec_8k.encode_u_exact([x + gspec_8k.H_Q for x in bfv.poly_centered(ctA_8k[0][0], sch_8k.Q)])
    ok_g8k, _ = gspec_8k.check_u_exact(cols_8k)
    assert ok_g8k
    # Run full N=8192 HoistedB61 build + verify on 1-block (K_blk=1) product to confirm N=8192 end-to-end:
    out_8k, w_8k = build_hoisted_matvec(sch_8k, Qp_8k, Bp_8k, [[ctA_8k[0]]], [ctB_8k[0]], w_bits=20, mode="exact_garner")
    ok_8k, why_8k = verify_hoisted_matvec(
        sch_8k, Qp_8k, Bp_8k,
        [[ct_handle(ctA_8k[0], Qp_8k)]], [ct_handle(ctB_8k[0], Qp_8k)], [ct_handle(out_8k[0], Qp_8k)],
        out_8k, w_8k,
    )
    assert ok_8k, f"N=8192 HoistedB61 verify failed: {why_8k}"
    want_8k, _ = bfv.negacyclic_mul([i % 7 for i in range(8192)], [(i * 3) % 7 for i in range(8192)])
    assert sch_8k.decrypt(out_8k[0]) == [x % t_spdz for x in want_8k]
    print(f"[PASS] Deployed Ring N=8192 (logQ={sch_8k.Q.bit_length()}b, k={len(Bp_8k)} ext primes): "
          f"HoistedB61 Exact-Garner build + verify + decrypt PASS ({time.time() - t_8k:.2f}s)")

    # ------------------------------------------------------------------
    # Test 4: Certificate-Level Forgery Teeth (Astra E4, E5, E7 & Bivariate Carry)
    # ------------------------------------------------------------------
    # 4a. Fiat-Shamir unbound quotient forgery (Astra E5):
    w_fs_forged = json.loads(json.dumps(w_hoist_64))
    # Convert JSON string keys in K_res back to int:
    for r_i in range(len(w_fs_forged["K_res"])):
        for k_i in range(3):
            w_fs_forged["K_res"][r_i][k_i] = {int(pk): pv for pk, pv in w_fs_forged["K_res"][r_i][k_i].items()}
    # Shift y_0[0] by ~Delta (forging decrypted plaintext +1 at X^0!), re-derive s_0[0] and adapt K_res[0][0][p][0] for legacy FS:
    dspec_64 = DirectDigitSpec(Q_64, w=20)
    gspec_64 = ExactGarnerSpec(Qp_64)
    # Reconstruct true D_0[0]:
    d0_0 = sum(bfv.negacyclic_mul(bfv.poly_centered(A_row_64[c][0], Q_64),
                                  bfv.poly_centered(B_vec_64[c][0], Q_64))[0][0] for c in range(K_blk))
    z_forged = d0_0 + ((Q_64 // t_64) * Q_64 // t_64)
    y_forged, s_forged = divmod(t_64 * z_forged + Q_64 // 2, Q_64)
    for m_i, dv in enumerate(decompose_unsigned(y_forged + dspec_64.y_shift, 20, dspec_64.Ly, dspec_64.top_y_bits)):
        w_fs_forged["y_lifts"][0][m_i][0] = dv
    s_garner_0 = gspec_64.encode_u_exact([s_forged])
    for m_i in range(15):
        w_fs_forged["s_lifts"][0][m_i][0] = s_garner_0[m_i][0]
    out_fs_forged = [list(comp) for comp in hoisted_cts_64[0]]
    out_fs_forged[0][0] = y_forged % Q_64
    out_fs_forged = [tuple(out_fs_forged)]
    hOut_forged = [ct_handle(out_fs_forged[0], Qp_64)]
    pub_h_forged = hashlib.sha256(
        ("|".join(hA_64[0]) + "||" + "|".join(hB_64) + "||" + hOut_forged[0]).encode()
    ).hexdigest()
    for p in Qp_64 + Bp_64:
        r_pt = C_BASE.fs_point(f"HOIST|{pub_h_forged}||{p}", p)
        # Compute discrepancy delta_y, delta_s at j=0:
        orig_y0, orig_s0 = divmod(t_64 * d0_0 + Q_64 // 2, Q_64)
        rhs_diff = ((Q_64 % p) * (y_forged - orig_y0) + (s_forged - orig_s0)) % p
        k_adj = (-rhs_diff * pow((t_64 % p) * (pow(r_pt, N_64, p) + 1), -1, p)) % p
        w_fs_forged["K_res"][0][0][p][0] = (w_fs_forged["K_res"][0][0][p][0] + k_adj) % p

    assert sch_64.decrypt(out_fs_forged[0]) != want_sum, "FS forgery did not alter decrypted message"
    ok_leg, _ = verify_hoisted_matvec(sch_64, Qp_64, Bp_64, hA_64, hB_64, hOut_forged, out_fs_forged, w_fs_forged, legacy_fs=True)
    ok_fix, why_fix = verify_hoisted_matvec(sch_64, Qp_64, Bp_64, hA_64, hB_64, hOut_forged, out_fs_forged, w_fs_forged, legacy_fs=False)
    assert ok_leg and not ok_fix, "FS binding falsifier failed!"
    print(f"[PASS] Attack F-FS (Astra E5): legacy statement-only FS ACCEPTS forged plaintext; HoistedB61 REFUSES ({why_fix})")

    # 4b. Boundary-strip non-canonical lift x + Q (Astra E7 at t ~ 2^61):
    # Choose a_0 in [-H_Q, -H_Q + (2^183 - Q)) so u_true = a_0 + H_Q < 2^183 - Q, hence u_alias = u_true + Q < 2^183!
    u_true_strip = 42
    u_alias_strip = u_true_strip + Q_64
    assert u_alias_strip < (1 << 183), "u_alias must fit in 183-bit power-of-two range"
    # Direct power-of-two 183-bit check ACCEPTS u_alias_strip, whereas ExactGarnerSpec REFUSES:
    d_alias = decompose_unsigned(u_alias_strip, 20, dspec_64.Lx, dspec_64.top_x_bits)
    ok_pow2, _ = dspec_64.check_digits([[v] for v in d_alias], dspec_64.Lx, dspec_64.top_x_bits)
    # Try forging Garner limbs for u_alias_strip (forced to overflow top limb r_2 >= q_2):
    r0_a = u_alias_strip % Qp_64[0]
    r1_a = ((u_alias_strip - r0_a) // Qp_64[0]) % Qp_64[1]
    r2_a = (u_alias_strip - r0_a - Qp_64[0] * r1_a) // (Qp_64[0] * Qp_64[1])
    assert r2_a >= Qp_64[2] and r2_a < (1 << 61)
    forged_garner_cols = []
    for ri_v, delta_v in zip((r0_a, r1_a, r2_a), gspec_64.deltas):
        d0_v = ri_v & ((1 << 20) - 1)
        d1_v = (ri_v >> 20) & ((1 << 19) - 1)
        d2_v = (ri_v >> 39) & ((1 << 18) - 1)
        d3_v = ri_v >> 57
        v0_v = (d0_v + delta_v) & ((1 << 20) - 1)
        forged_garner_cols.extend([[d0_v], [d1_v], [d2_v], [d3_v], [v0_v]])
    ok_garner, why_garner = gspec_64.check_u_exact(forged_garner_cols)
    assert ok_pow2 and not ok_garner
    print(f"[PASS] Attack F-Boundary (Astra E7, u+Q in [Q, 2^183)): un-tightened <2^183 ACCEPTS; Exact-Garner REFUSES ({why_garner})")

    # 4c. Single-Field p61 Bivariate Carry-Polynomial `F(X,Y) = (Y - 2^16) C(X,Y)` + Un-Ranged Carry Forgery:
    ok_biv, _, max_col_biv, wc_col_biv = build_and_verify_bivariate_p61(A_row_64, B_vec_64, Q_64, enforce_carry_range=True, forge_mult_p61=0)
    ok_biv_unranged, _, _, _ = build_and_verify_bivariate_p61(A_row_64, B_vec_64, Q_64, enforce_carry_range=False, forge_mult_p61=5)
    ok_biv_ranged_ref, why_biv_ref, _, _ = build_and_verify_bivariate_p61(A_row_64, B_vec_64, Q_64, enforce_carry_range=True, forge_mult_p61=5)
    assert ok_biv and ok_biv_unranged and not ok_biv_ranged_ref
    # Worst-case N=8192, K_blk=64 column bound check:
    wc_8k_64 = 64 * 2 * 8192 * 13 * (1 << 30)
    assert wc_8k_64 < P61_RIESEL // 4
    print(f"[PASS] Single-Field p61 Bivariate `(Y - 2^16) C(X,Y)`: honest PASS (realized |col|=2^{max_col_biv.bit_length()-1:.0f}, "
          f"N=8192 K=64 worst-case 2^{ math.log2(wc_8k_64):.2f} < p61/4); "
          f"un-ranged C(X,Y) ACCEPTS +5*p61 forgery; range-checked C(X,Y) REFUSES ({why_biv_ref})")

    # ------------------------------------------------------------------
    # Test 5: End-to-End Multi-Block Hoisted Dark Step + All 9 Step Attacks + Tau=4 Exact Trajectory
    # ------------------------------------------------------------------
    att_res = run_hoisted_dark_step_and_attacks(N=64, d=16, dr=4, dc=4)
    print(f"[PASS] End-to-End Multi-Block Hoisted Dark Step (4x4=16 blocks/layer -> 4 hoisted certs, SPDZ + R_PD): "
          f"refines `step_spec` bit-for-bit; {len(att_res)}/9 attacks REFUSED:")
    for k_att, v_why in att_res.items():
        print(f"       - {k_att:28s}: REFUSED ({v_why})")
    ok_tau4 = verify_tau_epoch_exact_trajectory(N=64, d=16, dr=4, dc=4, tau=4)
    assert ok_tau4
    print("[PASS] Temporal+Spatial Hoisted Outer-Product Flush (tau=4 sequential steps): "
          "bit-exact W_1^(4), W_2^(4) match vs 4 sequential `step_spec.step` calls!")

    # ------------------------------------------------------------------
    # Test 6: Exact Re-Pricing of DARK-LEARNING-SCHEME-DECISION §§7-8 & vPIR
    # ------------------------------------------------------------------
    rows, lu_info = reprice_dark_learning_table()
    pir = price_verifiable_embedding_pir()

    print("\n" + "=" * 92)
    print(f"LogUp-GKR (`D1b`) on 61b Prime + `ProveKit v2` Subdomain Projection (2^20 table):")
    print(f"  Batch M=2^18: {lu_info['logup_bits_batch']:.2f} bits/chal -> c=3 gives {3*lu_info['logup_bits_batch']:.1f} bits | "
          f"Monolithic M=2^29: {lu_info['logup_bits_mono']:.2f} bits/chal -> c=4 gives {4*lu_info['logup_bits_mono']:.1f} bits")
    print("=" * 92)
    print("TABLE A — PACKED DIGIT CONVENTION (Baseline 16b vs Hoisted w=20, Steady-State Per Step)")
    print(f"{'d':>5} | {'MPC (Gbit)':>11} | {'Base FHE(a)':>12} | {'Hoist FHE(a)':>12} | {'Base FHE(b)':>12} | "
          f"{'Hoist FHE(b)':>12} | {'Hoist(b,t=64)':>13} | {'vFHEML Inf':>10}")
    print("-" * 106)
    for r in rows:
        print(f"{r['d']:>5} | {r['mpc']['bits']/1e9:>11.3f} | {r['fhe_a_base']['bits_b16']/1e9:>12.3f} | "
              f"{r['hoist_a_w20']['steady_bits_packed']/1e9:>12.3f} | {r['fhe_b_base']['bits_b16']/1e9:>12.3f} | "
              f"{r['hoist_b_w20']['steady_bits_packed']/1e9:>12.3f} | {r['hoist_b_tau64']['steady_bits_packed']/1e9:>13.3f} | "
              f"{r['vfheml_infer']['steady_bits_packed']/1e9:>10.3f}")

    print("\nTABLE B — STRICT `digits61` + NON-IDEAL MASKS (Astra E8 Headline: 1 Digit = 61 Bits)")
    print(f"{'d':>5} | {'MPC (Gbit)':>11} | {'Base FHE(a)':>12} | {'Hoist FHE(a)':>12} | {'Base FHE(b)*':>12} | "
          f"{'Hoist FHE(b)':>12} | {'Hoist(b,t=64)':>13} | {'Hoist LoRA16':>12}")
    print("-" * 106)
    for r in rows:
        print(f"{r['d']:>5} | {r['mpc']['bits']/1e9:>11.3f} | {r['fhe_a_base']['bits_ni_b61']/1e9:>12.3f} | "
              f"{r['hoist_a_w20']['ni_bits_digits61']/1e9:>12.3f} | {r['fhe_b_base']['bits_ni_b61']/1e9:>12.3f} | "
              f"{r['hoist_b_w20']['ni_bits_digits61']/1e9:>12.3f} | {r['hoist_b_tau64']['ni_bits_digits61']/1e9:>13.3f} | "
              f"{r['hoist_b_lora16']['ni_bits_digits61']/1e9:>12.3f}")

    r4k = [r for r in rows if r["d"] == 4096][0]
    mpc_4k = r4k["mpc"]["bits"]
    print("\nKEY RATIOS AT d = 4096:")
    print(f"  - Matvec ct x ct certificate alone (packed): 581.93 Gbit -> {r4k['hoist_a_w20']['cert_bits_packed']/1e9:.2f} Gbit [w=20] / "
          f"{r4k['hoist_a_garner']['cert_bits_packed']/1e9:.2f} Gbit [Exact-Garner-15] "
          f"({581.93e9 / r4k['hoist_a_w20']['cert_bits_packed']:.1f}x reduction!)")
    print(f"  - Matvec ct x ct certificate alone (digits61): 1234.22 Gbit -> {r4k['hoist_a_w20']['cert_bits_b61']/1e9:.2f} Gbit [w=20] / "
          f"{r4k['hoist_a_garner']['cert_bits_b61']/1e9:.2f} Gbit [Exact-Garner-15] "
          f"({1234.22e9 / r4k['hoist_a_w20']['cert_bits_b61']:.1f}x reduction!)")
    print(f"  - Full Step FHE(a) total: {r4k['fhe_a_base']['bits_b16']/1e9:.1f} -> {r4k['hoist_a_w20']['steady_bits_packed']/1e9:.2f} Gbit "
          f"({r4k['fhe_a_base']['bits_b16'] / r4k['hoist_a_w20']['steady_bits_packed']:.1f}x) [packed] | "
          f"{r4k['fhe_a_base']['bits_ni_b61']/1e9:.1f} -> {r4k['hoist_a_w20']['ni_bits_digits61']/1e9:.2f} Gbit "
          f"({r4k['fhe_a_base']['bits_ni_b61'] / r4k['hoist_a_w20']['ni_bits_digits61']:.1f}x; "
          f"{r4k['hoist_a_w20']['ligero_zkpopk_bits_digits61']/1e9:.2f} Gbit w/ §20.2 Ligero ZKPoPK) [digits61]")
    print(f"  - Full Step Hoisted-FHE(b, tau=64 exact dense SGD) vs MPC ({mpc_4k/1e9:.2f} Gbit, {r4k['mpc']['wire']/1e6:.1f}M wire): "
          f"{r4k['hoist_b_tau64']['steady_bits_packed']/1e9:.2f} Gbit ({r4k['hoist_b_tau64']['steady_bits_packed']/mpc_4k:.2f}x MPC) [packed], "
          f"{r4k['hoist_b_tau64']['ni_bits_digits61']/1e9:.2f} Gbit ({r4k['hoist_b_tau64']['ni_bits_digits61']/mpc_4k:.2f}x MPC; "
          f"{r4k['hoist_b_tau64']['ligero_zkpopk_bits_digits61']/1e9:.2f} Gbit = {r4k['hoist_b_tau64']['ligero_zkpopk_bits_digits61']/mpc_4k:.2f}x MPC "
          f"[Exact-Garner: {r4k['hoist_b_tau64_garner']['ligero_zkpopk_bits_digits61']/1e9:.2f} Gbit] w/ §20.2 ZKPoPK) [digits61], "
          f"wire {r4k['hoist_b_tau64']['online_wire']/1e6:.2f}M ({r4k['hoist_b_tau64']['online_wire']/r4k['mpc']['wire']:.3f}x MPC)!")
    print(f"  - Hoisted-FHE(b, LoRA r=16 continual learning) vs MPC: "
          f"{r4k['hoist_b_lora16']['steady_bits_packed']/1e9:.2f} Gbit [packed], "
          f"{r4k['hoist_b_lora16']['ni_bits_digits61']/1e9:.2f} Gbit ({r4k['hoist_b_lora16']['ni_bits_digits61']/mpc_4k:.2f}x MPC) [digits61]!")
    print(f"  - Inference-Only vFHEML (2L d=4096) vs 2L MPC ({r4k['vfheml_infer']['mpc_inf_bits']/1e9:.2f} Gbit, "
          f"{r4k['vfheml_infer']['mpc_inf_wire']/1e6:.1f}M wire): "
          f"{r4k['vfheml_infer']['steady_bits_packed']/1e9:.2f} Gbit [packed], "
          f"{r4k['vfheml_infer']['ni_bits_digits61']/1e9:.2f} Gbit ({r4k['vfheml_infer']['ni_bits_digits61']/r4k['vfheml_infer']['mpc_inf_bits']:.2f}x MPC!) [digits61], "
          f"wire {r4k['vfheml_infer']['online_wire']/1e6:.2f}M ({r4k['vfheml_infer']['online_wire']/r4k['vfheml_infer']['mpc_inf_wire']:.3f}x MPC)!")
    print(f"  - Verifiable Encrypted-Embedding PIR (V={pir['V']:,}, d={pir['d']}, {pir['total_blocks']:,} -> {pir['hoisted_cts']} cts, "
          f"fits k=5={pir['fits_k5']} [{pir['max_lhs_bits']}b < {pir['QB_bits']}b]): "
          f"{pir['base_b61_gbit']:,.1f} Gbit -> {pir['hoist_b61_gbit']:.2f} Gbit [digits61] / {pir['hoist_b20_gbit']:.2f} Gbit [w=20] "
          f"({pir['reduction_b61']:.1f}x reduction!)")
    print(f"\nALL CHECKS PASSED in {time.time() - t_start:.2f}s.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
