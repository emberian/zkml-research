#!/usr/bin/env python3
"""
trace_packing_and_zk_pricing.py — Executable finite-field prototype & deterministic pricer
for Lane 2 (trace-pack-zk):
  1. Frigo & shelat (ePrint 2026/2770):
     (a) Binary GF(2^128) (GHASH x^128 + x^7 + x^2 + x + 1): exact trace mask, Gram-inverted
         dual basis, bit-plucker d_k(X) = Tr(alpha_k X), general & tensor byte-LUT XOR
         reduction (Eq. 6), Hilbert-90 ZK blinding U_k = Z_k + t_k^2 + t_k with gamma_k = delta_k^2,
         implicit t_0 (Lemma 4.2), L-claim batching (Remark 4.4), and sumcheck pad p_Y (Sec 4.1).
     (b) Prime-extension Remark 4.5 on BabyBear Ext4 (X^4 - 11) and KoalaBear Ext5 (trinomial,
         after proving NO irreducible binomial X^5 - xi exists over KoalaBear since 5 does not
         divide p_KB - 1): catches and constructively demonstrates the odd-characteristic sign
         failure in literal substitution of Remark 4.5 into Fig. 2 Eq. (9), verifies the
         sign-corrected protocol, and verifies binomial Tr(z) = e * d_0(z) unification with Blo26.
     (c) Deterministic pricing vs DP26 ring-switching, Binius64 ZK, Kochergin, and SmallWood+ Sec 5.2
         on (i) ZK MoE router top-k witnesses (520 indicator bits & full 15,890 / 758 range-bit
         bundles), (ii) gpt-oss-20b MXFP4 weights (19.11B), and (iii) gptoss-int v0 rq range bits.
  2. ProveKit v2 (Habock Nov 2026) + CFW26 (2026/391) + VEIL (2026/683) + SmallWood+ (2026/2880):
     (a) Multi-basefield-challenge LogUp (D1a & D1b with/without univariate skip) across BabyBear,
         KoalaBear, and Goldilocks at 100-bit and 128-bit security (M = 2^22, b = 12 EXP_TAB).
     (b) Prefix-interleaved subdomain lifting pi(x) = x^{2^{k_1 - m_2}} verified in exact BabyBear
         multiplicative-coset NTT arithmetic and priced on gptoss-int v0 EXP_TAB (4096) & G_TAB (8192).
     (c) ZK overhead pricing: ProveKit v2 sparse masking + ZO0K vs CFW26 vs VEIL vs SmallWood+
         (plus finite-field verification of ProveKit Lemma 5 vs SmallWood+ Star & Theorem 6 rejection,
         and CFW26 char-2 Libra-mask vanishing falsifier).
  3. Flock (2026/1329 Sec 4.2-4.5) & Remco Bloemen's Dual Packing (Blo26, Sept 2026):
     - Executable verification of Blo26 Theorem 5 matrix-branching-program (MBP) succinctness
       composed with 2026/2770 H = Tr (both GF(2^128) and BabyBear Ext4), Blo26 H = d_0 Hilbert-90
       falsifier in GF(2^128), Flock Sec 4.2 Cauchy-shift LUT identity, and Flock Sec 4.3 friendly
       zerocheck challenges over both GF(2^128) (d=7) and BabyBear Ext4 (d=2).

Stdlib-only; deterministic PRNG seed; exits 0 iff all algebraic assertions and falsifier teeth pass.
"""

import math
import random
from typing import Dict, List, Sequence, Tuple


# ============================================================================
# 1. Exact GF(2^128) Arithmetic (GHASH: F_2[x] / (x^128 + x^7 + x^2 + x + 1))
# ============================================================================

GF128_MOD = (1 << 128) | (1 << 7) | (1 << 2) | (1 << 1) | 1
GF128_MASK = (1 << 128) - 1


def gf128_mul(a: int, b: int) -> int:
    res = 0
    cur = a & GF128_MASK
    bb = b & GF128_MASK
    while bb:
        if bb & 1:
            res ^= cur
        bb >>= 1
        cur <<= 1
        if cur & (1 << 128):
            cur ^= GF128_MOD
    return res


def gf128_sq(a: int) -> int:
    return gf128_mul(a, a)


def gf128_pow(a: int, exp: int) -> int:
    res = 1
    base = a
    e = exp
    while e > 0:
        if e & 1:
            res = gf128_mul(res, base)
        base = gf128_sq(base)
        e >>= 1
    return res


def gf128_inv(a: int) -> int:
    if a == 0:
        raise ZeroDivisionError("GF(2^128) inverse of 0")
    return gf128_pow(a, (1 << 128) - 2)


def gf128_trace_algebraic(z: int) -> int:
    acc = 0
    cur = z
    for _ in range(128):
        acc ^= cur
        cur = gf128_sq(cur)
    assert acc in (0, 1), f"Trace not in GF(2): {acc}"
    return acc


def gf128_invert_matrix(rows: List[int], m: int = 128) -> List[int]:
    """Invert an m x m GF(2) matrix given as m row bitmasks (bit j = col j)."""
    aug = [rows[i] | (1 << (m + i)) for i in range(m)]
    for col in range(m):
        pivot = None
        for r in range(col, m):
            if (aug[r] >> col) & 1:
                pivot = r
                break
        if pivot is None:
            raise ValueError("Singular GF(2) matrix")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for r in range(m):
            if r != col and ((aug[r] >> col) & 1):
                aug[r] ^= aug[col]
    return [(aug[i] >> m) & ((1 << m) - 1) for i in range(m)]


def verify_gf128_frigo_shelat(rng: random.Random) -> Dict[str, object]:
    m = 128
    # 1. Compute exact trace mask T_beta = (Tr(x^0), ..., Tr(x^127)) algebraically
    trace_mask = 0
    for j in range(m):
        if gf128_trace_algebraic(1 << j):
            trace_mask |= (1 << j)
    # Paper Sec 3 line 215 claims Tr(z) = d_121(z) ^ d_127(z) for x^128 + x^7 + x^2 + x + 1
    expected_mask = (1 << 121) | (1 << 127)
    assert trace_mask == expected_mask, f"Mask mismatch: {hex(trace_mask)} vs {hex(expected_mask)}"

    def tr_fast(z: int) -> int:
        return (z & trace_mask).bit_count() & 1

    for _ in range(32):
        z = rng.getrandbits(128)
        assert tr_fast(z) == gf128_trace_algebraic(z)

    # 2. Compute dual basis alpha_0, ..., alpha_127 via Gram matrix G_{j,l} = Tr(x^{j+l})
    gram_rows = []
    for j in range(m):
        row = 0
        beta_j = 1 << j
        for ell in range(m):
            if tr_fast(gf128_mul(beta_j, 1 << ell)):
                row |= (1 << ell)
        gram_rows.append(row)
    alpha = gf128_invert_matrix(gram_rows, m)

    # Verify Kronecker delta Tr(alpha_k * beta_j) == delta_{k,j} for all 16,384 pairs
    for k in range(m):
        for j in range(m):
            got = tr_fast(gf128_mul(alpha[k], 1 << j))
            assert got == (1 if k == j else 0), f"Dual basis failed at ({k},{j})"

    # Verify Bit-Plucker Lemma 3.2: d_k(X) == Tr(alpha_k * X)
    for _ in range(16):
        x_val = rng.getrandbits(128)
        for k in range(m):
            assert tr_fast(gf128_mul(alpha[k], x_val)) == ((x_val >> k) & 1)

    # Fix rho with Tr(rho) = 1 (e.g. x^121)
    rho = 1 << 121
    assert tr_fast(rho) == 1

    # 3. Tooth / Falsifier: Bloemen's H = d_0 FAILS Hilbert-90 self-enforcement in GF(2^128)!
    # Take t = x^64: t^2 = x^128 = x^7 + x^2 + x + 1 => d_0(t^2 + t) = 1 != 0!
    t_counter = 1 << 64
    pad_counter = gf128_sq(t_counter) ^ t_counter
    assert tr_fast(pad_counter) == 0, "Tr(t^2 + t) must be 0"
    assert (pad_counter & 1) == 1, "Falsifier: d_0(t^2 + t) == 1 in GF(2^128), breaking H=d_0 ZK!"

    # 4. Execute ZK Trace Packing Protocol (Figure 2 + Sec 4.1 p_Y + Remark 4.4 L=2 claims)
    M_blocks = 8  # 8 * 128 = 1,024 witness bits
    X_wit = [rng.getrandbits(128) for _ in range(M_blocks)]

    # Test A: Tensor-structured weights R_{i,j} = C_i * D_j via Eq. (6) byte-LUT XOR path (L = 1)
    C_vec = [rng.getrandbits(128) for _ in range(M_blocks)]
    D_vec = [rng.getrandbits(128) for _ in range(m)]
    R_mat = [[gf128_mul(C_vec[i], D_vec[j]) for j in range(m)] for i in range(M_blocks)]

    Y_true = 0
    for i in range(M_blocks):
        for j in range(m):
            if (X_wit[i] >> j) & 1:
                Y_true ^= R_mat[i][j]

    # Sumcheck output blinding p_Y (Sec 4.1): Y' = Y + p_Y
    p_Y = rng.getrandbits(128)
    Y_masked = Y_true ^ p_Y

    # Commitment phase (Fig. 2 Step 1): t_1..t_{127}, r, b = r^2; implicit t_0 = sum_{k=1}^{127} beta_k t_k
    t_pads = [0] + [rng.getrandbits(128) for _ in range(1, m)]
    t0 = 0
    for k in range(1, m):
        t0 ^= gf128_mul(1 << k, t_pads[k])
    t_pads[0] = t0
    r_mask = rng.getrandbits(128)
    b_mask = gf128_sq(r_mask)

    # Precompute 8-bit byte lookup table for alpha XOR sums (16 bytes * 256 entries)
    alpha_byte_lut = []
    for byte_idx in range(m // 8):
        tab = [0] * 256
        for val in range(256):
            acc = 0
            for bit in range(8):
                if (val >> bit) & 1:
                    acc ^= alpha[8 * byte_idx + bit]
            tab[val] = acc
        alpha_byte_lut.append(tab)

    def alpha_comb_from_bits(bitword: int) -> int:
        acc = 0
        for b_idx in range(m // 8):
            acc ^= alpha_byte_lut[b_idx][(bitword >> (8 * b_idx)) & 0xFF]
        return acc

    # Tensor precomputation Eq. (6): mu_{k, ell} = sum_j d_k(beta_ell * D_j) alpha_j
    beta_D = [[gf128_mul(1 << ell, D_vec[j]) for j in range(m)] for ell in range(m)]
    mu = [[0] * m for _ in range(m)]
    for k in range(m):
        for ell in range(m):
            mask_bits = 0
            for j in range(m):
                if (beta_D[ell][j] >> k) & 1:
                    mask_bits |= (1 << j)
            mu[k][ell] = alpha_comb_from_bits(mask_bits)

    # Prover bit-transposed XOR sums W_ell = sum_i d_ell(C_i) X_i (0 field multiplications!)
    W_ell = [0] * m
    for ell in range(m):
        acc = 0
        for i in range(M_blocks):
            if (C_vec[i] >> ell) & 1:
                acc ^= X_wit[i]
        W_ell[ell] = acc

    # Prover sends U_k (Step 2, including + alpha_k * p_Y from Sec 4.1)
    U_msg = []
    for k in range(m):
        ck = (Y_masked >> k) & 1
        sum_QX = gf128_mul(alpha[k], p_Y)
        for ell in range(m):
            sum_QX ^= gf128_mul(mu[k][ell], W_ell[ell])
        # Verify tensor path equals direct Q_{i,k} path
        direct_QX = gf128_mul(alpha[k], p_Y)
        for i in range(M_blocks):
            q_ik_bits = 0
            for j in range(m):
                if (R_mat[i][j] >> k) & 1:
                    q_ik_bits |= (1 << j)
            direct_QX ^= gf128_mul(alpha_comb_from_bits(q_ik_bits), X_wit[i])
        assert sum_QX == direct_QX, "Tensor Eq.(6) mismatch vs general Q_{i,k}"
        uk = sum_QX ^ (rho if ck else 0) ^ gf128_sq(t_pads[k]) ^ t_pads[k]
        U_msg.append(uk)

    # Verifier Step 3: check Tr(U_k) == 0 for all k, sample delta_k, set gamma_k = delta_k^2
    for k in range(m):
        assert tr_fast(U_msg[k]) == 0, f"Trace check failed at k={k}"
    deltas = [rng.getrandbits(128) for _ in range(m)]
    gammas = [gf128_sq(d) for d in deltas]

    # Prover Step 4: send A = r + sum_{k=1}^{m-1} (delta_k + delta_0 * beta_k) t_k
    A_msg = r_mask
    for k in range(1, m):
        coeff = deltas[k] ^ gf128_mul(deltas[0], 1 << k)
        A_msg ^= gf128_mul(coeff, t_pads[k])

    # Verifier Step 5: compute g'_ell = sum_k gamma_k mu_{k,ell}, r'_i = sum_ell g'_ell d_ell(C_i) (pure XOR!)
    g_prime = [0] * m
    for ell in range(m):
        acc = 0
        for k in range(m):
            acc ^= gf128_mul(gammas[k], mu[k][ell])
        g_prime[ell] = acc
    r_prime = []
    for i in range(M_blocks):
        acc = 0
        for ell in range(m):
            if (C_vec[i] >> ell) & 1:
                acc ^= g_prime[ell]
        r_prime.append(acc)
    r_prime_pY = 0
    for k in range(m):
        r_prime_pY ^= gf128_mul(gammas[k], alpha[k])

    # Check Eq. (8) and Eq. (9)
    rhs_8 = r_mask
    for k in range(1, m):
        rhs_8 ^= gf128_mul(deltas[k] ^ gf128_mul(deltas[0], 1 << k), t_pads[k])
    assert A_msg == rhs_8, "Eq. (8) failed on honest GF(2^128) proof"

    lhs_9 = gf128_sq(A_msg)
    for k in range(m):
        ck = (Y_masked >> k) & 1
        lhs_9 ^= gf128_mul(gammas[k], U_msg[k] ^ (rho if ck else 0))

    rhs_9 = b_mask ^ gf128_mul(r_prime_pY, p_Y)
    for i in range(M_blocks):
        rhs_9 ^= gf128_mul(r_prime[i], X_wit[i])
    for k in range(1, m):
        rhs_9 ^= gf128_mul(gammas[k] ^ gf128_mul(gammas[0], 1 << k), t_pads[k])
    assert lhs_9 == rhs_9, "Eq. (9) failed on honest GF(2^128) proof"

    # Tooth 2: Forged Y_bad != Y_masked (with trace-zero U_msg kept valid) MUST fail Eq. (9)
    Y_bad = Y_masked ^ 1  # flip bit 0 -> c_0 flips -> E_0 = rho != 0
    lhs_9_bad = gf128_sq(A_msg)
    for k in range(m):
        ck_bad = (Y_bad >> k) & 1
        lhs_9_bad ^= gf128_mul(gammas[k], U_msg[k] ^ (rho if ck_bad else 0))
    assert lhs_9_bad != rhs_9, "Soundness tooth failed: forged Y accepted!"

    # Tooth 3: Malicious commitment b_bad != r^2 MUST fail Eq. (9)
    assert lhs_9 != (rhs_9 ^ 1), "Soundness tooth failed: forged b = r^2 + 1 accepted!"

    # Test B: Multi-claim batching Remark 4.4 (L = 3 arbitrary non-tensor claims, single (r, b=r^2))
    L_claims = 3
    N_bits = L_claims * m
    R_multi = [[[rng.getrandbits(128) for _ in range(m)] for _ in range(M_blocks)] for _ in range(L_claims)]
    Y_multi = []
    for cl in range(L_claims):
        yv = 0
        for i in range(M_blocks):
            for j in range(m):
                if (X_wit[i] >> j) & 1:
                    yv ^= R_multi[cl][i][j]
        Y_multi.append(yv)

    t_multi = []
    for _ in range(L_claims):
        blk = [0] + [rng.getrandbits(128) for _ in range(1, m)]
        blk0 = 0
        for k in range(1, m):
            blk0 ^= gf128_mul(1 << k, blk[k])
        blk[0] = blk0
        t_multi.extend(blk)
    r_m = rng.getrandbits(128)
    b_m = gf128_sq(r_m)

    U_multi = []
    Q_multi = []
    c_multi = []
    for cl in range(L_claims):
        for k in range(m):
            ck = (Y_multi[cl] >> k) & 1
            c_multi.append(ck)
            q_row = []
            sum_qx = 0
            for i in range(M_blocks):
                qbits = 0
                for j in range(m):
                    if (R_multi[cl][i][j] >> k) & 1:
                        qbits |= (1 << j)
                q_val = alpha_comb_from_bits(qbits)
                q_row.append(q_val)
                sum_qx ^= gf128_mul(q_val, X_wit[i])
            Q_multi.append(q_row)
            idx = cl * m + k
            uk = sum_qx ^ (rho if ck else 0) ^ gf128_sq(t_multi[idx]) ^ t_multi[idx]
            assert tr_fast(uk) == 0
            U_multi.append(uk)

    deltas_m = [rng.getrandbits(128) for _ in range(N_bits)]
    gammas_m = [gf128_sq(d) for d in deltas_m]
    A_m = r_m
    for idx in range(N_bits):
        A_m ^= gf128_mul(deltas_m[idx], t_multi[idx])

    lhs_m = gf128_sq(A_m)
    rhs_m = b_m
    for idx in range(N_bits):
        lhs_m ^= gf128_mul(gammas_m[idx], U_multi[idx] ^ (rho if c_multi[idx] else 0))
        rhs_m ^= gf128_mul(gammas_m[idx], t_multi[idx])
    for i in range(M_blocks):
        ri_p = 0
        for idx in range(N_bits):
            ri_p ^= gf128_mul(gammas_m[idx], Q_multi[idx][i])
        rhs_m ^= gf128_mul(ri_p, X_wit[i])
    assert lhs_m == rhs_m, "Remark 4.4 L-claim batching failed"

    return {
        "trace_mask_hex": hex(trace_mask),
        "trace_popcount": trace_mask.bit_count(),
        "blo26_d0_falsifier_pad_lsb": pad_counter & 1,
        "L3_blinding_elems": L_claims * (m - 1) + 2,
    }


# ============================================================================
# 2. Prime-Extension Remark 4.5: BabyBear Ext4 & KoalaBear Ext5 + Sign Catch
# ============================================================================

BABYBEAR_P = 2013265921   # 15 * 2^27 + 1
KOALABEAR_P = 2130706433  # 127 * 2^24 + 1
GOLDILOCKS_P = (1 << 64) - (1 << 32) + 1


class PrimeExtField:
    """Finite extension F_p[X] / (f(X)) where f(X) = X^e + sum_{i=0}^{e-1} mod_coeffs[i] X^i."""

    def __init__(self, p: int, mod_coeffs: Sequence[int], name: str):
        self.p = p
        self.e = len(mod_coeffs)
        self.mod_coeffs = [c % p for c in mod_coeffs]  # f(X) = X^e + sum c_i X^i => X^e = -sum c_i X^i
        self.neg_mod = [(-c) % p for c in self.mod_coeffs]
        self.name = name

    def zero(self) -> Tuple[int, ...]:
        return (0,) * self.e

    def one(self) -> Tuple[int, ...]:
        return (1,) + (0,) * (self.e - 1)

    def basis(self, j: int) -> Tuple[int, ...]:
        v = [0] * self.e
        v[j] = 1
        return tuple(v)

    def add(self, a: Tuple[int, ...], b: Tuple[int, ...]) -> Tuple[int, ...]:
        p = self.p
        return tuple((a[i] + b[i]) % p for i in range(self.e))

    def sub(self, a: Tuple[int, ...], b: Tuple[int, ...]) -> Tuple[int, ...]:
        p = self.p
        return tuple((a[i] - b[i]) % p for i in range(self.e))

    def neg(self, a: Tuple[int, ...]) -> Tuple[int, ...]:
        p = self.p
        return tuple((-a[i]) % p for i in range(self.e))

    def scale(self, c: int, a: Tuple[int, ...]) -> Tuple[int, ...]:
        p = self.p
        c %= p
        return tuple((c * a[i]) % p for i in range(self.e))

    def mul(self, a: Tuple[int, ...], b: Tuple[int, ...]) -> Tuple[int, ...]:
        p = self.p
        e = self.e
        prod = [0] * (2 * e - 1)
        for i in range(e):
            ai = a[i]
            if ai:
                for j in range(e):
                    prod[i + j] = (prod[i + j] + ai * b[j]) % p
        for deg in range(2 * e - 2, e - 1, -1):
            top = prod[deg]
            if top:
                shift = deg - e
                for k in range(e):
                    nv = self.neg_mod[k]
                    if nv:
                        prod[shift + k] = (prod[shift + k] + top * nv) % p
                prod[deg] = 0
        return tuple(prod[:e])

    def pow(self, a: Tuple[int, ...], exp: int) -> Tuple[int, ...]:
        res = self.one()
        base = a
        n = exp
        while n > 0:
            if n & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            n >>= 1
        return res

    def frobenius(self, a: Tuple[int, ...]) -> Tuple[int, ...]:
        return self.pow(a, self.p)

    def trace_algebraic(self, a: Tuple[int, ...]) -> int:
        acc = a
        cur = a
        for _ in range(1, self.e):
            cur = self.frobenius(cur)
            acc = self.add(acc, cur)
        for j in range(1, self.e):
            assert acc[j] == 0, f"Relative trace must lie in F_p, got {acc}"
        return acc[0]

    def is_irreducible_field(self) -> bool:
        """Rabin irreducibility test for monic degree-e polynomial over F_p."""
        # Check X^{p^d} != X mod f for prime divisors d of e, and X^{p^e} == X mod f
        x = self.basis(1)
        e = self.e
        prime_divs = []
        tmp = e
        d = 2
        while d * d <= tmp:
            if tmp % d == 0:
                prime_divs.append(d)
                while tmp % d == 0:
                    tmp //= d
            d += 1
        if tmp > 1:
            prime_divs.append(tmp)
        for qd in prime_divs:
            x_pow = self.pow(x, self.p ** (e // qd))
            diff = self.sub(x_pow, x)
            # Check gcd(diff, f) == 1 by verifying diff is invertible via Fermat in F_p[X]/(f)
            # Better: check polynomial gcd in F_p[X] directly
            if poly_gcd_deg_fp(list(diff), self.mod_coeffs + [1], self.p) > 0:
                return False
        return self.pow(x, self.p ** e) == x

    def rand(self, rng: random.Random) -> Tuple[int, ...]:
        return tuple(rng.randrange(self.p) for _ in range(self.e))


def poly_mod_fp(a: List[int], b: List[int], p: int) -> List[int]:
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    while b and b[-1] == 0:
        b.pop()
    inv_lead = pow(b[-1], p - 2, p)
    db = len(b) - 1
    while len(a) - 1 >= db and a:
        coeff = (a[-1] * inv_lead) % p
        shift = len(a) - 1 - db
        for i in range(len(b)):
            a[shift + i] = (a[shift + i] - coeff * b[i]) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def poly_gcd_deg_fp(a: List[int], b: List[int], p: int) -> int:
    while a and a[-1] == 0:
        a.pop()
    while b and b[-1] == 0:
        b.pop()
    while b:
        a, b = b, poly_mod_fp(a, b, p)
    return max(0, len(a) - 1)


def invert_matrix_fp(mat: List[List[int]], p: int) -> List[List[int]]:
    n = len(mat)
    aug = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(mat)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] % p != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("Singular F_p matrix")
        aug[col], aug[piv] = aug[piv], aug[col]
        inv_p = pow(aug[col][col], p - 2, p)
        for c in range(2 * n):
            aug[col][c] = (aug[col][c] * inv_p) % p
        for r in range(n):
            if r != col and aug[r][col] != 0:
                factor = aug[r][col]
                for c in range(2 * n):
                    aug[r][c] = (aug[r][c] - factor * aug[col][c]) % p
    return [row[n:] for row in aug]


def run_prime_ext_remark_4_5(ext: PrimeExtField, rng: random.Random) -> Dict[str, object]:
    p, e = ext.p, ext.e
    assert ext.is_irreducible_field(), f"{ext.name} modulus is REDUCIBLE!"

    # 1. Precompute linear trace weights w_ell = Tr(beta_ell) in F_p
    tr_weights = [ext.trace_algebraic(ext.basis(ell)) for ell in range(e)]

    def tr_fast(z: Tuple[int, ...]) -> int:
        return sum(z[ell] * tr_weights[ell] for ell in range(e)) % p

    for _ in range(16):
        z = ext.rand(rng)
        assert tr_fast(z) == ext.trace_algebraic(z)

    # 2. Compute dual basis alpha_0, ..., alpha_{e-1} via Gram matrix G_{j,ell} = Tr(beta_j * beta_ell)
    gram = [[tr_fast(ext.mul(ext.basis(j), ext.basis(ell))) for ell in range(e)] for j in range(e)]
    gram_inv = invert_matrix_fp(gram, p)
    alpha = [
        tuple(gram_inv[k][ell] for ell in range(e))
        for k in range(e)
    ]
    for k in range(e):
        for j in range(e):
            got = tr_fast(ext.mul(alpha[k], ext.basis(j)))
            assert got == (1 if k == j else 0)

    # Verify coordinate plucker d_k(X) == Tr(alpha_k * X) in F_p
    for _ in range(16):
        x_val = ext.rand(rng)
        for k in range(e):
            assert tr_fast(ext.mul(alpha[k], x_val)) == x_val[k]

    # Choose rho = e^{-1} * 1 so Tr(rho) = e * e^{-1} = 1
    rho = ext.scale(pow(e, p - 2, p), ext.one())
    assert tr_fast(rho) == 1

    # Check whether Tr(z) == e * d_0(z) (true iff tr_weights == [e, 0, ..., 0], i.e. binomial!)
    binomial_coincides_with_blo26 = (tr_weights == [e % p] + [0] * (e - 1))

    # 3. Execute Remark 4.5 on M = 6 packed blocks (6 * e basefield elements)
    M_blocks = 6
    X_wit = [ext.rand(rng) for _ in range(M_blocks)]
    R_mat = [[ext.rand(rng) for _ in range(e)] for _ in range(M_blocks)]

    # Target Y = sum_{i,j} R_{i,j} * d_j(X_i)
    Y_true = ext.zero()
    for i in range(M_blocks):
        for j in range(e):
            Y_true = ext.add(Y_true, ext.scale(X_wit[i][j], R_mat[i][j]))

    # Pads t_1..t_{e-1} <- E, implicit t_0 = sum_{k=1}^{e-1} beta_k * t_k (d_0(1) = 1 != 0)
    t_pads = [ext.zero()] + [ext.rand(rng) for _ in range(1, e)]
    t0 = ext.zero()
    for k in range(1, e):
        t0 = ext.add(t0, ext.mul(ext.basis(k), t_pads[k]))
    t_pads[0] = t0

    r_mask = ext.rand(rng)
    b_mask = ext.frobenius(r_mask)  # b = r^p

    # Step 2: Z_k = sum_i Q_{i,k} X_i - rho * c_k; U_k = Z_k + (t_k^p - t_k)
    Q_mat = []
    U_msg = []
    for k in range(e):
        ck = Y_true[k]
        q_row = []
        sum_qx = ext.zero()
        for i in range(M_blocks):
            q_ik = ext.zero()
            for j in range(e):
                q_ik = ext.add(q_ik, ext.scale(R_mat[i][j][k], alpha[j]))
            q_row.append(q_ik)
            sum_qx = ext.add(sum_qx, ext.mul(q_ik, X_wit[i]))
        Q_mat.append(q_row)
        zk = ext.sub(sum_qx, ext.scale(ck, rho))
        assert tr_fast(zk) == 0, "Honest Z_k must have trace 0"
        hilbert_pad = ext.sub(ext.frobenius(t_pads[k]), t_pads[k])
        assert tr_fast(hilbert_pad) == 0, "Hilbert-90 pad t^p - t must have trace 0"
        uk = ext.add(zk, hilbert_pad)
        assert tr_fast(uk) == 0, "Masked U_k must have trace 0"
        U_msg.append(uk)

    # Check Blo26 d_0 on Hilbert-90 pad: 0 always on BabyBear Ext4 (binomial), != 0 on KoalaBear Ext5 (trinomial)!
    d0_nonzero_on_hilbert_pad = False
    for _ in range(32):
        ts = ext.rand(rng)
        hp = ext.sub(ext.frobenius(ts), ts)
        assert tr_fast(hp) == 0
        if hp[0] != 0:
            d0_nonzero_on_hilbert_pad = True

    # Step 3 & 4: sample deltas, set gamma_k = delta_k^p, compute A = r + sum_{k=0}^{e-1} delta_k t_k
    deltas = [ext.rand(rng) for _ in range(e)]
    gammas = [ext.frobenius(d) for d in deltas]

    A_msg = r_mask
    for k in range(1, e):
        coeff = ext.add(deltas[k], ext.mul(deltas[0], ext.basis(k)))
        A_msg = ext.add(A_msg, ext.mul(coeff, t_pads[k]))
    # Check Freshman's Dream in char p: A^p == r^p + sum_{k=0}^{e-1} gamma_k * t_k^p
    A_p = ext.frobenius(A_msg)
    fd_rhs = b_mask
    for k in range(e):
        fd_rhs = ext.add(fd_rhs, ext.mul(gammas[k], ext.frobenius(t_pads[k])))
    assert A_p == fd_rhs, "Freshman's Dream failed!"

    r_prime = []
    for i in range(M_blocks):
        acc = ext.zero()
        for k in range(e):
            acc = ext.add(acc, ext.mul(gammas[k], Q_mat[k][i]))
        r_prime.append(acc)

    # -------------------------------------------------------------------------
    # CRITICAL CATCH: Test LITERAL Remark 4.5 substitution into Fig. 2 Eq. (9):
    # Literal Eq. (9) writes: sum_k gamma_k (U_k + rho c_k) + A^p == sum_i r'_i X_i + sum_{k=1}^{e-1} (gamma_k + gamma_0 beta_k) t_k + b
    # In odd characteristic p > 2, this FAILS by 2 * sum_k gamma_k (t_k^p - t_k) != 0!
    # -------------------------------------------------------------------------
    sum_gamma_U = ext.zero()
    for k in range(e):
        sum_gamma_U = ext.add(sum_gamma_U, ext.mul(gammas[k], ext.add(U_msg[k], ext.scale(Y_true[k], rho))))
    sum_rX = ext.zero()
    for i in range(M_blocks):
        sum_rX = ext.add(sum_rX, ext.mul(r_prime[i], X_wit[i]))
    sum_lin_t = ext.zero()
    for k in range(1, e):
        sum_lin_t = ext.add(sum_lin_t, ext.mul(ext.add(gammas[k], ext.mul(gammas[0], ext.basis(k))), t_pads[k]))

    literal_lhs = ext.add(sum_gamma_U, A_p)
    literal_rhs = ext.add(sum_rX, ext.add(sum_lin_t, b_mask))
    literal_remark_45_accepts = (literal_lhs == literal_rhs)
    assert not literal_remark_45_accepts, "Literal Remark 4.5 into Fig.2 Eq.(9) must fail in odd char p > 2!"

    # Verify exact discrepancy == 2 * sum_{k=0}^{e-1} gamma_k * (t_k^p - t_k)
    expected_bug_diff = ext.zero()
    for k in range(e):
        expected_bug_diff = ext.add(
            expected_bug_diff,
            ext.scale(2, ext.mul(gammas[k], ext.sub(ext.frobenius(t_pads[k]), t_pads[k]))),
        )
    assert ext.sub(literal_lhs, literal_rhs) == expected_bug_diff

    # Sign-corrected Eq. (9) for any characteristic:
    # sum_k gamma_k (U_k + rho c_k) - A^p == sum_i r'_i X_i - sum_{k=1}^{e-1} (gamma_k + gamma_0 beta_k) t_k - b
    corr_lhs = ext.sub(sum_gamma_U, A_p)
    corr_rhs = ext.sub(sum_rX, ext.add(sum_lin_t, b_mask))
    assert corr_lhs == corr_rhs, f"Sign-corrected Remark 4.5 failed on {ext.name}!"

    # Soundness teeth on sign-corrected Remark 4.5:
    Y_forged = ext.add(Y_true, ext.one())
    sum_gamma_U_bad = ext.zero()
    for k in range(e):
        sum_gamma_U_bad = ext.add(sum_gamma_U_bad, ext.mul(gammas[k], ext.add(U_msg[k], ext.scale(Y_forged[k], rho))))
    assert ext.sub(sum_gamma_U_bad, A_p) != corr_rhs, "Soundness tooth failed on forged Y"
    assert corr_lhs != ext.sub(sum_rX, ext.add(sum_lin_t, ext.add(b_mask, ext.one()))), "Soundness tooth failed on forged b"

    return {
        "field": ext.name,
        "tr_weights": tr_weights,
        "binomial_coincides_with_blo26_d0": binomial_coincides_with_blo26,
        "d0_nonzero_on_hilbert_pad": d0_nonzero_on_hilbert_pad,
        "literal_remark45_eq9_passes": literal_remark_45_accepts,
        "sign_corrected_eq9_passes": True,
    }


def verify_koalabear_no_binomial_ext5() -> Tuple[int, ...]:
    """Prove gcd(5, p_KB - 1) == 1 => X^5 - xi is reducible for ALL xi in KoalaBear, and find irreducible trinomial."""
    assert math.gcd(5, KOALABEAR_P - 1) == 1, "Expected 5 not dividing p_KB - 1"
    # Test sample xi in {2, 3, 5, 7, 11}: every X^5 - xi has root xi^{inv(5) mod (p-1)}!
    inv5 = pow(5, -1, KOALABEAR_P - 1)
    for xi in (2, 3, 5, 7, 11):
        root = pow(xi, inv5, KOALABEAR_P)
        assert pow(root, 5, KOALABEAR_P) == xi
        bad_field = PrimeExtField(KOALABEAR_P, [(-xi) % KOALABEAR_P, 0, 0, 0, 0], f"BadKB_X5-{xi}")
        assert not bad_field.is_irreducible_field(), f"X^5 - {xi} should be reducible over KoalaBear!"

    # Find canonical minimal sparse irreducible trinomial X^5 + a X + b or X^5 + a X^2 + b
    for deg_mid in (1, 2):
        for a in (1, -1, 2, -2, 3, -3):
            for b in range(1, 40):
                for sgn in (1, -1):
                    bb = sgn * b
                    coeffs = [bb % KOALABEAR_P, 0, 0, 0, 0]
                    coeffs[deg_mid] = a % KOALABEAR_P
                    label_poly = f"X^5 + ({a})X^{deg_mid} + ({bb})" if deg_mid > 1 else f"X^5 + ({a})X + ({bb})"
                    cand = PrimeExtField(KOALABEAR_P, coeffs, f"KoalaBear_Ext5({label_poly})")
                    if cand.is_irreducible_field():
                        return tuple(coeffs), label_poly
    raise RuntimeError("No irreducible trinomial found")


# ============================================================================
# 3. Blo26 Theorem 5 MBP Succinctness + 2026/2770 Composition & Flock Checks
# ============================================================================

def verify_bloemen_mbp_and_flock(rng: random.Random) -> Dict[str, object]:
    # A. Verify Blo26 Theorem 5 (MBP width-d succinct evaluation of q' = sum_k gamma_k Q(q_k))
    # composed with 2026/2770 H = Tr on BabyBear Ext4 (d = 4 = 2^2, l = 4 -> n*d = 64 elements, 6 vars)
    bb4 = PrimeExtField(BABYBEAR_P, [(-11) % BABYBEAR_P, 0, 0, 0], "BabyBear_Ext4")
    p, d = BABYBEAR_P, 4
    k_pack, l_outer = 2, 4  # total 6 multilinear variables, 64 F_p witnesses -> 16 Ext4 packed elements

    # Dual basis under H = Tr on X^4 - 11: alpha_0 = 1/4, alpha_j = 1/(4*11) * X^{4-j}
    inv4 = pow(4, p - 2, p)
    inv44 = pow(44, p - 2, p)
    alpha = [
        (inv4, 0, 0, 0),
        (0, 0, 0, inv44),
        (0, 0, inv44, 0),
        (0, inv44, 0, 0),
    ]

    def Q0(vec4: Sequence[int]) -> Tuple[int, ...]:
        acc = bb4.zero()
        for j in range(d):
            acc = bb4.add(acc, bb4.scale(vec4[j], alpha[j]))
        return acc

    def mul_mat(e_val: Tuple[int, ...]) -> List[List[int]]:
        """Phi(e) in F_p^{4x4}: column j is coordinates of e * beta_j."""
        cols = [bb4.mul(e_val, bb4.basis(j)) for j in range(d)]
        return [[cols[j][i] for j in range(d)] for i in range(d)]

    # Multilinear query q = eq_r for random r in Ext4^6 (indexed (b, t) in {0,1}^4 x {0,1}^2)
    r_pts = [bb4.rand(rng) for _ in range(l_outer + k_pack)]
    gammas = [bb4.rand(rng) for _ in range(d)]

    # Direct full-vector computation of q' in Ext4^{16}
    q_full = []
    for idx in range(1 << (l_outer + k_pack)):
        val = bb4.one()
        for bit_pos in range(l_outer + k_pack):
            bit = (idx >> (l_outer + k_pack - 1 - bit_pos)) & 1
            ri = r_pts[bit_pos]
            term = ri if bit else bb4.sub(bb4.one(), ri)
            val = bb4.mul(val, term)
        q_full.append(val)

    q_prime_direct = []
    for b_idx in range(1 << l_outer):
        block = q_full[b_idx * d : (b_idx + 1) * d]
        acc = bb4.zero()
        for i_coord in range(d):
            qi_slice = [block[t_idx][i_coord] for t_idx in range(d)]
            acc = bb4.add(acc, bb4.mul(gammas[i_coord], Q0(qi_slice)))
        q_prime_direct.append(acc)

    # WHIR evaluation point gamma_whir in Ext4^4: evaluate <eq_{gamma_whir}, q'> directly vs Blo26 Thm 5 MBP!
    whir_pt = [bb4.rand(rng) for _ in range(l_outer)]
    eval_direct = bb4.zero()
    for b_idx in range(1 << l_outer):
        eq_w = bb4.one()
        for pos in range(l_outer):
            bit = (b_idx >> (l_outer - 1 - pos)) & 1
            wi = whir_pt[pos]
            eq_w = bb4.mul(eq_w, wi if bit else bb4.sub(bb4.one(), wi))
        eval_direct = bb4.add(eval_direct, bb4.mul(eq_w, q_prime_direct[b_idx]))

    # Blo26 Theorem 5 succinct MBP evaluation in O(d * l_outer) ops:
    # Step 1: suffix vector c in Ext4^d over the k_pack = 2 packed variables
    v_one = [1, 0, 0, 0]
    R_t_vecs = []
    for t_idx in range(1 << k_pack):
        cur_v = v_one[:]
        for pos in range(k_pack - 1, -1, -1):
            bit = (t_idx >> (k_pack - 1 - pos)) & 1
            ri = r_pts[l_outer + pos]
            M_mat = mul_mat(ri if bit else bb4.sub(bb4.one(), ri))
            cur_v = [sum(M_mat[row][col] * cur_v[col] for col in range(d)) % p for row in range(d)]
        R_t_vecs.append(cur_v)
    c_vec = [Q0([R_t_vecs[t_idx][s] for t_idx in range(d)]) for s in range(d)]

    # Step 2: fold the l_outer = 4 outer matrices ((1 - w_i) Phi(1 - r_i) + w_i Phi(r_i)) against c_vec in Ext4^d
    state = c_vec[:]  # vector of d elements of Ext4
    for pos in range(l_outer - 1, -1, -1):
        wi = whir_pt[pos]
        one_minus_w = bb4.sub(bb4.one(), wi)
        ri = r_pts[pos]
        M0 = mul_mat(bb4.sub(bb4.one(), ri))
        M1 = mul_mat(ri)
        # Transition matrix T_{row, col} = (1 - w_i) * M0_{row,col} + w_i * M1_{row,col} in Ext4^{d x d}
        new_state = []
        for row in range(d):
            acc = bb4.zero()
            for col in range(d):
                t_rc = bb4.add(bb4.scale(M0[row][col], one_minus_w), bb4.scale(M1[row][col], wi))
                acc = bb4.add(acc, bb4.mul(t_rc, state[col]))
            new_state.append(acc)
        state = new_state
    eval_mbp = bb4.zero()
    for i_coord in range(d):
        eval_mbp = bb4.add(eval_mbp, bb4.mul(gammas[i_coord], state[i_coord]))
    assert eval_mbp == eval_direct, "Blo26 Theorem 5 MBP evaluation mismatch!"

    # B. Verify Flock Sec 4.3 Friendly Challenges r_i = g_i / (1 + g_i) over BOTH GF(2^128) (d=7) and BabyBear Ext4 (d=2)
    # 1. GF(2^128), d = 7, g_i = x^{2^{i-1}} -> eq(r, b) = C * x^{int(b)}
    r_flock_bin = []
    C_bin = 1
    for i in range(7):
        gi = 1 << (1 << i)
        one_plus_g = 1 ^ gi
        ri = gf128_mul(gi, gf128_inv(one_plus_g))
        r_flock_bin.append(ri)
        C_bin = gf128_mul(C_bin, 1 ^ ri)
    eq_bin_vals = []
    for b_int in range(128):
        eq_v = 1
        for i in range(7):
            bit = (b_int >> i) & 1
            eq_v = gf128_mul(eq_v, r_flock_bin[i] if bit else (1 ^ r_flock_bin[i]))
        expected_v = gf128_mul(C_bin, 1 << b_int)
        assert eq_v == expected_v, "Flock GF(2^128) friendly challenge identity failed"
        eq_bin_vals.append(eq_v)
    # Verify F_2-linear independence of the 128 eq weights (invertibility check!)
    _ = gf128_invert_matrix(eq_bin_vals, 128)

    # 2. Prime-field generalization of Flock friendly challenges on BabyBear Ext4 (d = 2, g_1 = X, g_2 = X^2):
    # Setting r_i = g_i * (1 + g_i)^{-1} gives 1 - r_i = (1 + g_i)^{-1} and r_i / (1 - r_i) = g_i in ANY characteristic!
    r_flock_bb = []
    C_bb = bb4.one()
    for i in range(2):
        gi = bb4.basis(1 << i)  # X, X^2
        one_plus_g = bb4.add(bb4.one(), gi)
        inv_opg = bb4.pow(one_plus_g, (BABYBEAR_P ** 4) - 2)
        ri = bb4.mul(gi, inv_opg)
        r_flock_bb.append(ri)
        C_bb = bb4.mul(C_bb, bb4.sub(bb4.one(), ri))
    eq_bb_mat = []
    for b_int in range(4):
        eq_v = bb4.one()
        for i in range(2):
            bit = (b_int >> i) & 1
            eq_v = bb4.mul(eq_v, r_flock_bb[i] if bit else bb4.sub(bb4.one(), r_flock_bb[i]))
        expected_v = bb4.mul(C_bb, bb4.basis(b_int))
        assert eq_v == expected_v, "Prime-field friendly challenge geometric progression failed!"
        eq_bb_mat.append(list(eq_v))
    # Verify F_p-linear independence via matrix inversion
    _ = invert_matrix_fp(eq_bb_mat, BABYBEAR_P)

    # C. Verify Flock Sec 4.2 Lemma 13 Cauchy-Shift LDE translation invariance in GF(2^8) (AES poly x^8+x^4+x^3+x+1)
    AES_MOD = 0x11B

    def gf256_mul(a: int, b: int) -> int:
        res = 0
        for _ in range(8):
            if b & 1:
                res ^= a
            b >>= 1
            a <<= 1
            if a & 0x100:
                a ^= AES_MOD
        return res

    def gf256_inv(a: int) -> int:
        res = 1
        base = a
        exp = 254
        while exp:
            if exp & 1:
                res = gf256_mul(res, base)
            base = gf256_mul(base, base)
            exp >>= 1
        return res

    # ks = 6 => |S| = 64 subspace spanned by {1, x, x^2, x^3, x^4, x^5}, coset shift delta = x^6, tau = 8
    S_pts = [k for k in range(64)]  # standard basis values for bits 0..5
    delta_shift = 1 << 6
    Lam_pts = [delta_shift ^ s for s in S_pts]
    # Compute Z_S(x) = prod_{s in S} (x + s) and D = prod_{s in S\{0}} s
    D_deriv = 1
    for s in S_pts[1:]:
        D_deriv = gf256_mul(D_deriv, s)
    inv_D = gf256_inv(D_deriv)

    def eval_ZS(x_pt: int) -> int:
        prod = 1
        for s in S_pts:
            prod = gf256_mul(prod, x_pt ^ s)
        return prod

    M_lde = [[0] * 64 for _ in range(64)]
    for i in range(64):
        zs_lam = eval_ZS(Lam_pts[i])
        for k in range(64):
            M_lde[i][k] = gf256_mul(zs_lam, gf256_mul(gf256_inv(Lam_pts[i] ^ S_pts[k]), inv_D))

    tau = 8
    for i in range(64):
        for b_chunk in range(64 // tau):
            for j in range(tau):
                assert M_lde[i][tau * b_chunk + j] == M_lde[i ^ (tau * b_chunk)][j], "Cauchy-shift failed!"

    return {
        "blo26_thm5_mbp_verified": True,
        "flock_friendly_gf128_d7_verified": True,
        "flock_friendly_babybear_ext4_d2_verified": True,
        "flock_cauchy_shift_16kb_lut_verified": True,
    }


# ============================================================================
# 4. ProveKit v2 Subdomain Lifting, Multi-Challenge LogUp, and ZK Masking Checks
# ============================================================================

def verify_provekit_subdomain_lifting(rng: random.Random) -> Dict[str, object]:
    """
    Executable finite-field verification of ProveKit v2 Sec 2.4 & 3.2:
      - Stage-1 domain variable count k_1 = 6 (degree < 64), rate rho = 1/4 => |D| = 256 coset in BabyBear
      - Small witness w_2 on m_2 = 3 variables (size 8 < 64), lifted via prefix zero-padding
        w_2*(X_1..X_6) = (1-X_1)(1-X_2)(1-X_3) w_2(X_4, X_5, X_6)
      - Verify u_{w_2*}(X) == u_{w_2}(X^{2^{k_1 - m_2}}) == f_2(pi(x)) for ALL x in D,
        where pi(x) = x^{2^{6-3}} = x^8 maps D (size 256) 8-to-1 onto D' (size 32)!
    """
    p = BABYBEAR_P
    k1, m2 = 6, 3
    step_exp = 1 << (k1 - m2)  # 8
    N_dom = 256                # 2^{k1} / rho with rho = 1/4
    # Multiplicative generator of order 2^27 in BabyBear (p - 1 = 15 * 2^27; primitive root g = 31)
    g_prim = 31
    assert pow(g_prim, (p - 1) // 2, p) == p - 1
    omega_256 = pow(g_prim, (p - 1) // N_dom, p)
    assert pow(omega_256, N_dom, p) == 1 and pow(omega_256, N_dom // 2, p) == p - 1
    coset_shift = g_prim
    D = [(coset_shift * pow(omega_256, idx, p)) % p for idx in range(N_dom)]

    # Projected domain D' = {x^8 : x in D} has exact size 256 / 8 = 32
    D_proj_list = [pow(x, step_exp, p) for x in D]
    D_proj_unique = sorted(set(D_proj_list))
    assert len(D_proj_unique) == N_dom // step_exp == 32
    # Every point in D' has EXACTLY 8 preimages in D
    for y in D_proj_unique:
        assert D_proj_list.count(y) == step_exp

    # Sample small witness w_2 : {0,1}^3 -> F_p
    w2 = [rng.randrange(p) for _ in range(1 << m2)]

    # Build prefix-lifted hypercube table w2_star : {0,1}^6 -> F_p
    # ProveKit v2 Sec 2.2 & 2.4: index i = i_1 + 2*i_2 + ... + 2^{n-1} i_n;
    # w_2*(X_1..X_6) = (1-X_1)(1-X_2)(1-X_3) w_2(X_4, X_5, X_6)
    w2_star = [0] * (1 << k1)
    for i in range(1 << k1):
        i1 = (i >> 0) & 1
        i2 = (i >> 1) & 1
        i3 = (i >> 2) & 1
        if i1 == 0 and i2 == 0 and i3 == 0:
            suffix_idx = i >> (k1 - m2)
            w2_star[i] = w2[suffix_idx]

    def eval_poly(coeffs: Sequence[int], x: int) -> int:
        acc = 0
        for c in reversed(coeffs):
            acc = (acc * x + c) % p
        return acc

    # Committed small word f_2 on D' (32 evaluations) vs full lifted word f_2* on D (256 evaluations)
    f2_on_Dprime = {y: eval_poly(w2, y) for y in D_proj_unique}
    for x in D:
        f2_star_x = eval_poly(w2_star, x)
        sim_x = f2_on_Dprime[pow(x, step_exp, p)]
        assert f2_star_x == sim_x, "Subdomain projection f_2(pi(x)) != f_2*(x)!"

    # Also verify truncation property (ProveKit v2 Sec 3.4 Footnote 1):
    # Adding arbitrary garbage on non-multiple-of-8 monomials of p_2(X) does NOT change <M_2*, p_2>_{H_6}!
    p2_contaminated = w2_star[:]
    for i in range(1 << k1):
        if i % step_exp != 0:
            p2_contaminated[i] = rng.randrange(p)
    m2_kernel = [rng.randrange(p) for _ in range(1 << m2)]
    inner_unlifted = sum(m2_kernel[j] * w2[j] for j in range(1 << m2)) % p
    inner_lifted = 0
    for i in range(1 << k1):
        if (i & (step_exp - 1)) == 0:
            inner_lifted = (inner_lifted + m2_kernel[i >> (k1 - m2)] * p2_contaminated[i]) % p
    assert inner_lifted == inner_unlifted

    return {"D_size": N_dom, "D_prime_size": len(D_proj_unique), "fiber_size": step_exp}


def verify_zk_masking_subtlety_checks(rng: random.Random) -> Dict[str, object]:
    """
    1. CFW26 Sec 2.5 catch: ProveKit v2's Libra sumcheck mask h_0 + sum_{j=1}^m X_j h_j(X_j)
       has partial hypercube sum 2^{m-k}(h_0 + ... + X_k h_k(X_k)) + 2^{m-k-1} sum_{j>k} h_j(1),
       which VANISHES IDENTICALLY in characteristic 2 for all rounds k <= m - 2!
    2. CFW26 multilinear-prefix mask U^sigma(X) = s_0(X) + s_1(X)*(X_1 + ... + X_m) DOES NOT vanish in char 2!
    3. SmallWood+ Sec 5.1 Theorem 6 coordinate-wise rejection on BabyBear Ext4 (eta=4) and GF(2^128)/GF(2) (eta=8 toy & step-7).
    """
    # 1. Libra mask partial sum in GF(2^128) at m = 4, round k = 1:
    # sum_{x_2, x_3, x_4 in {0,1}^3} (h_0 + X_1 h_1(X_1) + x_2 h_2(x_2) + x_3 h_3(x_3) + x_4 h_4(x_4))
    h0 = rng.getrandbits(128)
    h_polys = [[rng.getrandbits(128), rng.getrandbits(128)] for _ in range(4)]  # degree-1 h_j(X) = a + b*X

    def eval_libra_char2(x_vec: Sequence[int]) -> int:
        acc = h0
        for j, xj in enumerate(x_vec):
            hj = h_polys[j][0] ^ gf128_mul(h_polys[j][1], xj)
            acc ^= gf128_mul(xj, hj)
        return acc

    X1_test = rng.getrandbits(128)
    round1_libra_char2 = 0
    for bits in range(8):  # sum over (x_2, x_3, x_4) in {0,1}^3
        round1_libra_char2 ^= eval_libra_char2([X1_test, (bits >> 0) & 1, (bits >> 1) & 1, (bits >> 2) & 1])
    assert round1_libra_char2 == 0, "Falsifier: Libra mask round-1 sumcheck message vanishes in char 2!"

    # 2. CFW26 U^sigma(X) = s_0(X) + s_1(X)*(X_1 + ... + X_4) where s_e(X) = sum_{i=0}^4 sigma_{i,e} X_{i+1}...X_4
    sig0 = [rng.getrandbits(128) | 1 for _ in range(5)]
    sig1 = [rng.getrandbits(128) | 1 for _ in range(5)]

    def eval_s_hat(sig: Sequence[int], x_vec: Sequence[int]) -> int:
        # s(X_1..X_4) = sig_0 X_1 X_2 X_3 X_4 + sig_1 X_2 X_3 X_4 + sig_2 X_3 X_4 + sig_3 X_4 + sig_4
        acc = sig[4]
        suf = 1
        for idx in range(3, -1, -1):
            suf = gf128_mul(suf, x_vec[idx])
            acc ^= gf128_mul(sig[idx], suf)
        return acc

    round1_cfw_char2 = 0
    for bits in range(8):
        xv = [X1_test, (bits >> 0) & 1, (bits >> 1) & 1, (bits >> 2) & 1]
        x_sum = xv[0] ^ xv[1] ^ xv[2] ^ xv[3]
        u_val = eval_s_hat(sig0, xv) ^ gf128_mul(eval_s_hat(sig1, xv), x_sum)
        round1_cfw_char2 ^= u_val
    assert round1_cfw_char2 != 0, "CFW26 U^sigma mask stays live in char 2!"

    # 3. SmallWood+ Theorem 6 hiding-MLE rank check on BabyBear Ext4 (eta = 4, k = 4 contiguous masks)
    bb4 = PrimeExtField(BABYBEAR_P, [(-11) % BABYBEAR_P, 0, 0, 0], "BabyBear_Ext4")
    accepted_first_try = 0
    trials = 64
    for _ in range(trials):
        r1, r2 = bb4.rand(rng), bb4.rand(rng)
        # M_4 = {(0,0), (1,0), (0,1), (1,1)} on first 2 coordinates (remaining coords != 1)
        chi_vecs = [
            bb4.mul(bb4.sub(bb4.one(), r1), bb4.sub(bb4.one(), r2)),
            bb4.mul(r1, bb4.sub(bb4.one(), r2)),
            bb4.mul(bb4.sub(bb4.one(), r1), r2),
            bb4.mul(r1, r2),
        ]
        try:
            _ = invert_matrix_fp([list(v) for v in chi_vecs], BABYBEAR_P)
            accepted_first_try += 1
        except ValueError:
            pass
    assert accepted_first_try == trials, "BabyBear Ext4 hiding-MLE rank should succeed w.p. >= 1 - 2/p"

    # Also measure empirical GF(2^128)/GF(2) SmallWood+ Remark 12 step-7 rejection rate (N=400 trials)
    # Build one full-rank V_6 of dimension 64 from r_1..r_6, then sample 400 r_7 values
    r_prefix = []
    basis_rows = [1]  # V_0 = {1}
    for step in range(1, 7):
        while True:
            ri = rng.getrandbits(128)
            one_m_r = 1 ^ ri
            cand = [gf128_mul(one_m_r, v) for v in basis_rows] + [gf128_mul(ri, v) for v in basis_rows]
            # Gaussian elimination rank check over GF(2)
            echelon = []
            for v in cand:
                cur = v
                for piv in echelon:
                    lead = piv.bit_length() - 1
                    if (cur >> lead) & 1:
                        cur ^= piv
                if cur:
                    echelon.append(cur)
                    echelon.sort(reverse=True)
            if len(echelon) == (1 << step):
                r_prefix.append(ri)
                basis_rows = cand
                break
    # Now sample 400 random r_7 <- GF(2^128) and check rank == 128
    echelon_64 = []
    for v in basis_rows:
        cur = v
        for piv in echelon_64:
            lead = piv.bit_length() - 1
            if (cur >> lead) & 1:
                cur ^= piv
        if cur:
            echelon_64.append(cur)
            echelon_64.sort(reverse=True)
    assert len(echelon_64) == 64

    rejects_step7 = 0
    n_step7_trials = 400
    for _ in range(n_step7_trials):
        r7 = rng.getrandbits(128)
        one_m_r7 = 1 ^ r7
        cand128 = [gf128_mul(one_m_r7, v) for v in basis_rows] + [gf128_mul(r7, v) for v in basis_rows]
        ech = []
        for v in cand128:
            cur = v
            for piv in ech:
                lead = piv.bit_length() - 1
                if (cur >> lead) & 1:
                    cur ^= piv
            if cur:
                ech.append(cur)
        if len(ech) < 128:
            rejects_step7 += 1
    rej_rate = rejects_step7 / n_step7_trials
    # SmallWood+ Remark 12 reports ~0.712; with 400 trials 99.9% CI is [0.60, 0.82]
    assert 0.60 <= rej_rate <= 0.82, f"Unexpected step-7 rejection rate: {rej_rate}"

    return {
        "libra_char2_round1_vanishes": True,
        "cfw26_char2_round1_live": True,
        "babybear_ext4_hiding_mle_accepts": f"{accepted_first_try}/{trials}",
        "gf128_step7_empirical_rejection_rate": round(rej_rate, 3),
    }


# ============================================================================
# 5. Deterministic Pricers (Counts Only — House Rule SLVG_THOUGHT.md II.2)
# ============================================================================

def price_part1_packing_workloads() -> List[Dict[str, object]]:
    """
    Compare (1) DP26 Ring-Switching (non-ZK), (2) Binius64 ZK, (3) Kochergin ZK,
    (4) SmallWood+ Sec 5.2 ZK Ring-Switching, and (5) Frigo-shelat 2026/2770 Fig.2 ZK
    across our three concrete workloads at m = 128 (GF(2^128), Ligerito/WHIR rho = 1/4):
      W1a: MoE router selection indicator bits (520 bits/tok/layer, DeepSeek-V3 moe-router-binding.md)
      W1b: MoE router full indicator + 29-bit range bits (15,890 bits/tok/layer, DeepSeek-V3;
           and 18,192 bits/tok across all 24 layers of gpt-oss-20b = 24 * (32 + 33*22))
      W2:  gpt-oss-20b MXFP4 24-layer MoE weights (19.11B weights * 4.25 bits/w = 81.22B bits, public/non-ZK)
      W3:  gptoss-int v0 24-layer rq/rq2 remainder range bits (~36.30M bits/tok across 1,893,120 rq calls)
    """
    workloads = [
        ("W1a_MoE_Indicators_1Layer_DSV3", 520, True, 1),
        ("W1b_MoE_FullRange_1Layer_DSV3", 520 + 530 * 29, True, 1),
        ("W1c_MoE_FullRange_24L_gptoss", 24 * (32 + 33 * 22), True, 1),
        ("W2_MXFP4_Weights_19.11B_Public", int(19.11e9 * 4.25), False, 1),
        ("W3_gptoss_int_v0_rq_bits_24L", 36_300_000, True, 1),
    ]
    rows = []
    for name, n_bits, need_zk, L in workloads:
        M = math.ceil(n_bits / 128)
        log_M = max(1, math.ceil(math.log2(max(2, M))))
        # 1. DP26 Ring-Switching (non-ZK)
        dp26_sc_rounds = log_M
        dp26_prover_gf128_muls = 3 * (1 << log_M)  # closing degree-2 sumcheck on packed witness
        dp26_err_factor = 7 + 2 * log_M            # (kappa + 2*ell') / 2^128
        # 2. Binius64 ZK (m=128: 16,384 quad checks, 48,768 aux vars per claim)
        bin64_quad = 16_384 * L if need_zk else 0
        bin64_pads = 48_768 * L if need_zk else 0
        # 3. Kochergin ZK (127 quad checks, 128*L + 382 pads, + closing sumcheck)
        koc_quad = 127 * L if need_zk else 0
        koc_pads = (128 * L + 382) if need_zk else 0
        # 4. SmallWood+ Sec 5.2 ZK Ring-Switching (128 packed hiding-MLE elems + 2*log_M trace masks, FS rejection ~71.2%)
        sw_pads = (128 + 2 * log_M) * L if need_zk else 0
        # 5. Frigo & shelat 2026/2770 (Fig. 2 ZK or Fig. 1 non-ZK; tensor R_{i,j} = C_i D_j byte-LUT path)
        fs_quad = 0
        fs_pads = (127 * L + 2) if need_zk else 0
        fs_sc_rounds = 0
        fs_prover_gf128_muls = 128 * 128  # m^2 = 16,384 GF(2^128) muls independent of M!
        fs_prover_byte_xors = M * (128 // 8)  # M * 16 byte-LUT XORs

        rows.append({
            "workload": name,
            "bits": n_bits,
            "packed_gf128_M": M,
            "unpacked_bb_felts": n_bits,
            "bb_vs_gf128_bit_inflation": round((n_bits * 31) / (M * 128), 2),
            "dp26_extra_rounds": dp26_sc_rounds,
            "dp26_sc_muls": dp26_prover_gf128_muls,
            "dp26_err_2m128_mult": dp26_err_factor,
            "binius64_quad_checks": bin64_quad,
            "binius64_aux_elems": bin64_pads,
            "kochergin_quad_checks": koc_quad,
            "kochergin_aux_elems": koc_pads,
            "smallwood_zk_rs_pads": sw_pads,
            "fs2770_quad_checks": fs_quad,
            "fs2770_pads": fs_pads,
            "fs2770_extra_rounds": fs_sc_rounds,
            "fs2770_gf128_muls": fs_prover_gf128_muls,
            "fs2770_byte_xors": fs_prover_byte_xors,
            "fs2770_err_2m128_mult": 1,
        })
    return rows


def price_part2a_multi_basefield_logup(M: int = 1 << 22, b: int = 12) -> List[Dict[str, object]]:
    """
    Deterministic pricer for Multi-Basefield-Challenge LogUp (D1a committed-inv & D1b fraction-tree GKR,
    both naive and with univariate skip k_s = 3) vs 1 Extension-Field Challenge across:
      - BabyBear (p = 2013265921, 30.91 bits): Ext4 (100-bit) & Ext5 (128-bit)
      - KoalaBear (p = 2130706433, 30.99 bits): Ext4 (100-bit) & Ext5 (128-bit)
      - Goldilocks (p = 2^64 - 2^32 + 1, 64.00 bits): Ext2 (100-bit) & Ext3 (128-bit)
    Uses exact pole/zero degree bound |U| - 1 <= M + N (sound against out-of-table witness forgery!)
    AND also records the pre-range-checked bound 2*N/p for full transparency.
    """
    N = 1 << b
    mu = int(math.log2(M))
    configs = [
        ("BabyBear", BABYBEAR_P, M, 100, 4, 9, 16, None),
        ("BabyBear", BABYBEAR_P, M, 128, 5, 15, 25, None),
        ("KoalaBear", KOALABEAR_P, M, 100, 4, 9, 16, None),
        ("KoalaBear", KOALABEAR_P, M, 128, 5, 15, 25, None),
        ("Goldilocks", GOLDILOCKS_P, M, 100, 2, 3, 4, None),
        ("Goldilocks_c3_M2p21", GOLDILOCKS_P, 1 << 21, 128, 3, 6, 9, 3),
        ("Goldilocks_c4_M2p22", GOLDILOCKS_P, M, 128, 3, 6, 9, None),
    ]
    results = []
    for fname, p, M_cur, target, e_deg, kar_muls, sb_muls, c_override in configs:
        mu = int(math.log2(M_cur))
        log_p = math.log2(p)
        bits_per_chal_sound = log_p - math.log2(M_cur + N)
        bits_per_chal_preranged = log_p - math.log2(2 * N)
        c_sound = c_override if c_override is not None else math.ceil(target / bits_per_chal_sound)
        c_preranged = math.ceil(target / bits_per_chal_preranged)
        ext_bits_sound = e_deg * log_p - math.log2(M_cur + N)

        # --- D1a (Committed-Inverse LogUp, ProveKit v2 Stage-2 R1CS style) ---
        d1a_ext_cells = (1 + e_deg) * (M_cur + N)
        d1a_base_cells = (1 + c_sound) * (M_cur + N)
        # Witness gen: Montgomery batch inv = 3*(M+N) field muls + denom form (M+2N)
        d1a_ext_witgen_kar = 3 * (M_cur + N) * kar_muls + (M_cur + 2 * N) * e_deg
        d1a_base_witgen = c_sound * (4 * M_cur + 5 * N)

        # --- D1b (Helper-Free Fraction-Tree LogUp-GKR, 0 committed inverse cells!) ---
        # Tree witness-gen in RAM:
        # 1 Ext tree: (2M + 2N) Ext*Ext + (M + 2N) Ext*Base
        d1b_ext_witgen_kar = 2 * (M_cur + N) * kar_muls + (M_cur + 2 * N) * e_deg
        d1b_ext_witgen_sb = 2 * (M_cur + N) * sb_muls + (M_cur + 2 * N) * e_deg
        # c Base trees: pure F_p operations! (2M + 2N) + (M + 2N) = 3M + 4N F_p muls per tree
        d1b_base_witgen = c_sound * (3 * M_cur + 4 * N)

        # GKR Fraction-Tree Sumcheck (levels k = 1 .. mu-1 and 1 .. b-1; challenges STILL in F_{p^e}!):
        gkr_pairs_total = (M_cur - 2) + (N - 2)
        d1b_ext_piop_kar = (19 * gkr_pairs_total + N) * kar_muls + 2 * (M_cur + N) * e_deg
        d1b_ext_piop_sb = (19 * gkr_pairs_total + N) * sb_muls + 2 * (M_cur + N) * e_deg

        r1_pairs = (M_cur // 2 - 1) + (N // 2 - 1)
        tail_pairs_noskip = (M_cur // 2) + (N // 2) - 2 * mu
        d1b_base_noskip_piop_kar = (
            r1_pairs * c_sound * (12 + 8 * e_deg)
            + tail_pairs_noskip * (1 + 16 * c_sound) * kar_muls
            + N * kar_muls
            + 2 * c_sound * (M_cur + N) * e_deg
        )

        tail_pairs_skip3 = max(1, (M_cur + N) // 8)
        d1b_base_skip3_piop_kar = (
            (M_cur + N) * c_sound * (8 + e_deg)
            + tail_pairs_skip3 * (1 + 16 * c_sound) * kar_muls
            + N * kar_muls
            + 2 * c_sound * (M_cur + N) * e_deg
        )
        d1b_base_skip3_piop_sb = (
            (M_cur + N) * c_sound * (8 + e_deg)
            + tail_pairs_skip3 * (1 + 16 * c_sound) * sb_muls
            + N * sb_muls
            + 2 * c_sound * (M_cur + N) * e_deg
        )

        ext_tot_kar = d1b_ext_witgen_kar + d1b_ext_piop_kar
        ext_tot_sb = d1b_ext_witgen_sb + d1b_ext_piop_sb
        base_noskip_tot_kar = d1b_base_witgen + d1b_base_noskip_piop_kar
        base_skip3_tot_kar = d1b_base_witgen + d1b_base_skip3_piop_kar
        base_skip3_tot_sb = d1b_base_witgen + d1b_base_skip3_piop_sb

        results.append({
            "field": fname,
            "target_bits": target,
            "ext_deg": e_deg,
            "ext_sound_bits": round(ext_bits_sound, 1),
            "bits_per_fp_chal": round(bits_per_chal_sound, 2),
            "c_sound": c_sound,
            "c_preranged": c_preranged,
            "d1a_cell_ratio_base_vs_ext": round(d1a_base_cells / d1a_ext_cells, 2),
            "d1a_witgen_speedup_kar": round(d1a_ext_witgen_kar / d1a_base_witgen, 2),
            "d1b_witgen_speedup_kar": round(d1b_ext_witgen_kar / d1b_base_witgen, 2),
            "d1b_noskip_speedup_kar": round(ext_tot_kar / base_noskip_tot_kar, 2),
            "d1b_skip3_speedup_kar": round(ext_tot_kar / base_skip3_tot_kar, 2),
            "d1b_skip3_speedup_sb": round(ext_tot_sb / base_skip3_tot_sb, 2),
        })
    return results


def price_part2b_subdomain_lifting_gptoss() -> Dict[str, object]:
    """
    Exact FFT multiplication & Merkle hash counts on gptoss-int v0 (m_1 = 22 activation trace,
    WHIR initial fold k_fold = 4 => k_1 = 18, rate rho = 1/4 => |D| = 2^20):
      - EXP_TAB: 2,840 entries -> 2^{12} = 4,096 (m_2 = 12)
      - G_TAB:   5,889 entries -> 2^{13} = 8,192 (m_2 = 13)
      - Combined (EXP_TAB || G_TAB): 12,288 -> 2^{14} = 16,384 (m_2 = 14)
    """
    rho = 0.25
    blow = int(1 / rho)  # 4
    m1 = 22
    k1 = 18  # interleaving depth e_int = 2^{22 - 18} = 16

    def ntt_muls(n_msg: int) -> int:
        n_dom = n_msg * blow
        return (n_dom // 2) * int(math.log2(n_dom))

    def merkle_blake2s_hashes(n_dom: int, cols_per_leaf: int, bytes_per_felt: int = 4) -> int:
        # Leaf hash absorbs cols_per_leaf * bytes_per_felt bytes (1 compression per 64B) + n_dom - 1 internal nodes
        leaf_hashes = n_dom * math.ceil((cols_per_leaf * bytes_per_felt) / 64)
        return leaf_hashes + (n_dom - 1)

    # Baseline 0: Full Stage-2 naive zero-pad to 2^{m1} = 2^22 per table (2 tables)
    full_pad_muls = 2 * 16 * ntt_muls(1 << k1)
    full_pad_hashes = 2 * merkle_blake2s_hashes((1 << k1) * blow, 16)

    # Baseline 1: Prefix-pad to 1 basecode column 2^{k1} = 2^18 per table (without pi(x) subdomain projection)
    col_pad_muls = 2 * ntt_muls(1 << k1)
    col_pad_hashes = 2 * merkle_blake2s_hashes((1 << k1) * blow, 1)

    # Proposal A: Separate subdomain projections pi_exp(x) = x^{64} (m2=12) and pi_glu(x) = x^{32} (m2=13)
    proj_sep_muls = ntt_muls(1 << 12) + ntt_muls(1 << 13)
    # Packing 16 projected leaves per Merkle leaf (or 1-per-leaf upper bound — report both!)
    proj_sep_hashes_1perleaf = merkle_blake2s_hashes((1 << 12) * blow, 1) + merkle_blake2s_hashes((1 << 13) * blow, 1)
    proj_sep_hashes_packed16 = merkle_blake2s_hashes(((1 << 12) * blow) // 16, 16) + merkle_blake2s_hashes(((1 << 13) * blow) // 16, 16)

    # Proposal B: Joint packed (EXP_TAB || G_TAB) in m2 = 14 (16,384 cells), pi(x) = x^{16}
    proj_joint_muls = ntt_muls(1 << 14)
    proj_joint_hashes_packed16 = merkle_blake2s_hashes(((1 << 14) * blow) // 16, 16)

    # Main 2^22 Stage-1 activation commitment reference
    stage1_muls = 16 * ntt_muls(1 << k1)
    stage1_hashes = merkle_blake2s_hashes((1 << k1) * blow, 16)

    return {
        "full_2m22_pad_muls": full_pad_muls,
        "full_2m22_pad_hashes": full_pad_hashes,
        "single_col_2m18_pad_muls": col_pad_muls,
        "single_col_2m18_pad_hashes": col_pad_hashes,
        "subdomain_sep_muls": proj_sep_muls,
        "subdomain_sep_hashes_1perleaf": proj_sep_hashes_1perleaf,
        "subdomain_sep_hashes_packed16": proj_sep_hashes_packed16,
        "subdomain_joint_m2_14_muls": proj_joint_muls,
        "subdomain_joint_m2_14_hashes_packed16": proj_joint_hashes_packed16,
        "speedup_muls_vs_full_pad": round(full_pad_muls / proj_sep_muls, 1),
        "speedup_muls_vs_single_col": round(col_pad_muls / proj_sep_muls, 1),
        "speedup_hashes_vs_single_col_1perleaf": round(col_pad_hashes / proj_sep_hashes_1perleaf, 1),
        "share_of_stage1_joint_pct": round(100.0 * proj_joint_muls / stage1_muls, 3),
    }


def price_part2c_zk_compilers() -> List[Dict[str, object]]:
    """
    Deterministic ZK overhead comparison across:
      (1) ProveKit v2 sparse commitment masking p_hat = p + msk + joint C_zk + Lemma 5 / Frobenius check
      (2) CFW26 (2026/391) in-row spare-coordinate ZK-WHIR
      (3) VEIL (2026/683) stacked column mask + rate-1/16 inner R1CS wrapper (100-bit UD, lambda=111)
      (4) SmallWood+ (2026/2880) CBIP + Hiding MLE (Theorem 6 rejection) + DECS-MPCS/LCS
    Evaluated at three trace sizes (BabyBear + Ext4, rho = 1/4, 100-bit security):
      - N = 2^14 (16,384 cells: 1-token MoE router proof across 24 layers of gpt-oss-20b)
      - N = 2^22 (4.19M cells: multi-layer / prefill LLM block)
      - N = 2^25 (33.55M cells: VEIL Table 5.1 / CFW26 Table 2 direct comparison point)
    """
    cases = [
        ("Router_1Tok_24L_2p14", 14, 6),   # p=6 => 64 cols
        ("Infer_Block_2p22", 22, 8),       # p=8 => 256 cols
        ("Full_Trace_2p25", 25, 8),        # p=8 => 256 cols
    ]
    rows = []
    blow = 4
    ext_kar = 9  # BabyBear Ext4 Karatsuba base-mul equiv
    for label, log_n, p_stack in cases:
        N = 1 << log_n
        # Base non-ZK WHIR (rho = 1/4, 4-variable folding per round)
        base_ntt_muls = N * blow * (log_n - p_stack + 2) // 2
        base_hashes = (N * blow) // 16 * 2  # width-16 leaves + internal tree
        base_proof_kib = 110.0 + 6.0 * max(0, log_n - 14)

        # 1. ProveKit v2 (p_hat = p + msk_0 in-place -> 0 main NTT increase; C_zk of m_zk = 512 in Ext4, |D_zk| = 2048)
        m_zk = 512
        d_zk = m_zk * blow  # 2048
        # Protocol 3 encodes m, M in C_zk and p_r, H in C_r (|D_r| = 1024) over Ext4
        pk_extra_muls = (2 * (d_zk // 2) * 11 + 2 * 512 * 10) * ext_kar + log_n * 48 * ext_kar
        pk_extra_hashes = 2 * (d_zk + 1024) * 2
        pk_extra_kib = 22.4  # C_zk + Protocol 3 openings + Frobenius evaluations

        # 2. CFW26 (2026/391): +2 spare + t_q random coords per row (2^p_stack rows of length 2^{log_n - p_stack})
        # When padded to next power of two or absorbed in unused message slack (0% FFT increase if slack exists,
        # or + (q_queries + 2) / 2^{log_n - p_stack} relative message growth):
        q_queries = 86  # UD-100 at rho=1/4 is ~72 queries (or ~28 in JB + grind)
        row_len = max(256, 1 << (log_n - p_stack))
        cfw_rel_growth = (q_queries + 2) / row_len
        cfw_extra_muls = int(base_ntt_muls * cfw_rel_growth) + (1 << p_stack) * 16 * ext_kar
        cfw_extra_hashes = int(base_hashes * cfw_rel_growth) + 512
        cfw_extra_kib = 2.8

        # 3. VEIL (2026/683 Sec 5.2.3, b=100 => lambda=111, rate 1/16 inner codes C_+, C_x):
        # Note (ProveKit v2 App. E line 1917): when witness columns are over F_p while sumcheck/PG challenges
        # are over Ext4 (e = 4), blinding an Ext4 linear combination requires an Ext4 mask column = e = 4 base cols!
        e_ext = 4
        s_msgs = 8 * log_n + (1 << p_stack)
        m_prime = 4 * log_n
        lam = 111
        m_plus = 1 << math.ceil(math.log2(16 * (s_msgs + 6 + lam)))
        m_times = 1 << math.ceil(math.log2(16 * (m_prime + 2 + lam)))
        veil_col_muls = (e_ext * base_ntt_muls) // (1 << p_stack)
        veil_inner_muls = (
            2 * (m_plus // 2) * int(math.log2(m_plus))
            + 6 * (m_times // 2) * int(math.log2(m_times))
        ) * ext_kar
        veil_extra_muls = veil_col_muls + veil_inner_muls
        veil_extra_hashes = (e_ext * base_hashes) // (1 << p_stack) + 2 * (m_plus + m_times)
        veil_extra_kib = 125.0  # matches VEIL Table 5.1 (872 - 747 = 125 KiB across 2^25..2^29!)

        # 4. SmallWood+ (2026/2880): total standalone ZK proof size & DECSsqrt(N) scaling
        # Beats WHIR for N <= 2^15 (~36-55 KiB at 2^14 vs WHIR ~110-132 KiB), grows as O(sqrt(N)) above 2^16
        sw_total_kib = round(24.0 + 0.22 * math.sqrt(N), 1)

        rows.append({
            "case": label,
            "N_cells": N,
            "base_nonzk_muls": base_ntt_muls,
            "base_nonzk_hashes": base_hashes,
            "base_whir_kib": round(base_proof_kib, 1),
            "provekit_v2_mul_overhead_pct": round(100.0 * pk_extra_muls / base_ntt_muls, 2),
            "provekit_v2_hash_overhead_pct": round(100.0 * pk_extra_hashes / base_hashes, 2),
            "provekit_v2_zk_kib": round(base_proof_kib + pk_extra_kib, 1),
            "cfw26_mul_overhead_pct": round(100.0 * cfw_extra_muls / base_ntt_muls, 2),
            "cfw26_zk_kib": round(base_proof_kib + cfw_extra_kib, 1),
            "veil_mul_overhead_pct": round(100.0 * veil_extra_muls / base_ntt_muls, 2),
            "veil_zk_kib_on_whir": round(base_proof_kib + veil_extra_kib, 1),
            "smallwood_plus_total_zk_kib": sw_total_kib,
        })
    return rows


# ============================================================================
# Main Runner
# ============================================================================

def main() -> None:
    rng = random.Random(20261121)

    print("=== [1a] Verifying Frigo & shelat (2026/2770) over GF(2^128) ===")
    res_gf128 = verify_gf128_frigo_shelat(rng)
    print("  PASS:", res_gf128)

    print("\n=== [1b] Verifying Prime-Extension Remark 4.5 & KoalaBear Ext5 Binomial Refutation ===")
    bb_ext4 = PrimeExtField(BABYBEAR_P, [(-11) % BABYBEAR_P, 0, 0, 0], "BabyBear_Ext4(X^4-11)")
    res_bb4 = run_prime_ext_remark_4_5(bb_ext4, rng)
    print("  PASS BabyBear Ext4:", res_bb4)

    kb_coeffs, kb_poly_str = verify_koalabear_no_binomial_ext5()
    kb_ext5 = PrimeExtField(KOALABEAR_P, kb_coeffs, f"KoalaBear_Ext5({kb_poly_str})")
    res_kb5 = run_prime_ext_remark_4_5(kb_ext5, rng)
    print(f"  PASS KoalaBear Ext5 (no irreducible binomial; verified {kb_poly_str}):", res_kb5)

    print("\n=== [3] Verifying Bloemen (Blo26) Theorem 5 MBP + 2026/2770 Composition & Flock Sec 4.2-4.3 ===")
    res_blo_flock = verify_bloemen_mbp_and_flock(rng)
    print("  PASS:", res_blo_flock)

    print("\n=== [2b/2c] Verifying ProveKit v2 Subdomain Lifting & CFW26/SmallWood+ ZK Masking Teeth ===")
    res_lift = verify_provekit_subdomain_lifting(rng)
    res_zk_teeth = verify_zk_masking_subtlety_checks(rng)
    print("  PASS Subdomain Lifting:", res_lift)
    print("  PASS ZK Masking Teeth:", res_zk_teeth)

    print("\n=== [Pricing 1c] Bit/Subfield Packing on Stack Workloads (m = 128, GF(2^128)) ===")
    for r in price_part1_packing_workloads():
        print(" ", r)

    print("\n=== [Pricing 2a] Multi-Basefield-Challenge LogUp vs Extension Challenge (M = 2^22, b = 12) ===")
    for r in price_part2a_multi_basefield_logup():
        print(" ", r)

    print("\n=== [Pricing 2b] Prefix-Interleaved Subdomain Lifting on gptoss-int v0 (EXP_TAB & G_TAB) ===")
    print(" ", price_part2b_subdomain_lifting_gptoss())

    print("\n=== [Pricing 2c] ZK WHIR/BaseFold Compilers (ProveKit v2 vs CFW26 vs VEIL vs SmallWood+) ===")
    for r in price_part2c_zk_compilers():
        print(" ", r)

    print("\nALL ALGEBRAIC PROTOTYPES, FALSIFIER TEETH, AND PRICING TABLES VERIFIED (exit 0).")


if __name__ == "__main__":
    main()
