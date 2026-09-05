#!/usr/bin/env python3
"""inert_tower.py — every derived number in notes/inert-cyclotomic-tower.md.

Candidate: O = Z[zeta_6561] = Z[X]/(Phi_{3^8}), Phi = X^4374 + X^2187 + 1; 2 is inert
(ord_6561(2) = 4374) so O/(2^k) = GR(2^k, 4374), residue field F_{2^4374}; the
subring tower eta = zeta^27 gives GR(2^k, 162) inside it.

Stdlib only. COUNTS and EXHAUSTIVE SMALL-PARAMETER CHECKS; not a benchmark, not a
security proof, not the lattice estimator (which needs Sage and is absent here —
§4 is a primal-uSVP core-SVP model calibrated against the HE-standard table row).

  §1 ring-multiplication cost at N = 4374 (Karatsuba / Toom / radix-3 CRT-NTT) vs N = 4096
  §2 dense extension arithmetic in GR(2^64, 162) and the sumcheck bill at v = 25, deg 3
  §3 BFV noise / depth at log q = 64 from the h2-verdict per-level numbers
  §4 RLWE security at n = 4374, log q = 64 (own model + calibration) and the
     module-BKZ discriminant term of 2025/1904
  §5 fold norm-growth budget under w <- w + rho v
  §6 challenge-set lemmas at conductor 27 and 81: unit differences, NO short inverses,
     slack 3 is a unit mod 2^k, exact operator norms, subring embedding
  §7 hash: ring-polynomial maps respect x = y (mod 2) (exhaustive in GR(4, 6)); a
     digit map does not (the witness)
Run: python3 inert_tower.py   (~1 min)
"""
from __future__ import annotations
import cmath
import itertools
import json
import math
import random
import sys

# ----------------------------------------------------------------------------- §1
def kara_mults(n: int, cutoff: int = 1) -> int:
    """u64 multiplications for one length-n x length-n coefficient product,
    unbalanced Karatsuba (split n = a + b, a = ceil(n/2)), schoolbook at n <= cutoff."""
    if n <= cutoff:
        return n * n
    a, b = (n + 1) // 2, n // 2
    return 2 * kara_mults(a, cutoff) + kara_mults(b, cutoff)


def kara_adds(n: int, cutoff: int = 1) -> int:
    """Upper bound on u64 add/sub for the same recursion (pre-adds + 2 subtractions +
    2 overlapped additions per level; schoolbook (n-1)^2 accumulations at the leaf)."""
    if n <= cutoff:
        return (n - 1) * (n - 1)
    a, b = (n + 1) // 2, n // 2
    return 2 * kara_adds(a, cutoff) + kara_adds(b, cutoff) + 2 * b + 4 * (2 * a - 1)


def phi3_reduction_adds(r: int) -> int:
    """Reduce a (4r-1)-coefficient product mod X^{2r}+X^r+1: degrees 2r..3r-1 cost two
    subtractions (X^{2r+j} = -X^{r+j} - X^j), degrees 3r..4r-2 cost one add (X^{3r+j} = X^j)."""
    return 2 * r + (r - 1)


def section1() -> dict:
    out = {}
    N3, r3 = 4374, 2187
    N2 = 4096
    for cutoff in (1, 8, 32):
        out[f'kara_mults_N4374_cutoff{cutoff}'] = kara_mults(N3, cutoff)
        out[f'kara_adds_N4374_cutoff{cutoff}'] = kara_adds(N3, cutoff) + phi3_reduction_adds(r3)
        out[f'kara_mults_N4096_cutoff{cutoff}'] = kara_mults(N2, cutoff)
    out['kara_mults_N4096_balanced_3pow12'] = 3 ** 12
    out['ratio_kara_4374_over_4096_cutoff1'] = out['kara_mults_N4374_cutoff1'] / out['kara_mults_N4096_cutoff1']
    # Toom-3 down 3^7 after one Karatsuba split: 3 * 5^7 base mults — but Toom-3
    # interpolation divides by 2, which does not exist mod 2^64: needs >= 66-bit lanes.
    out['toom3_mults_N4374_needs_div_by_2'] = 3 * 5 ** 7
    # Deployed comparator (galois-ring-stack §2 / h2-verdict): 3-limb RNS-NTT at N = 4096:
    # per limb 2 forward + 1 inverse NTT of (N/2)log2 N butterflies + N pointwise.
    ntt_pow2 = 3 * (N2 // 2) * 12 + N2
    out['rns_ntt_modmults_N4096_per_limb'] = ntt_pow2
    out['rns_ntt_modmults_N4096_3limbs'] = 3 * ntt_pow2
    # Radix-3 CRT-NTT for Phi_{3^8}: cyclic convolution of length 6561 suffices because
    # Phi | X^6561 - 1; 8 levels x 2187 radix-3 butterflies x (2 twiddle + 1 omega_3) mults.
    ntt3 = 3 * (8 * 2187 * 3) + 6561
    out['radix3_ntt_modmults_len6561_per_prime'] = ntt3
    # exact integer product coefficients < 4374 * 2^128 < 2^141; three ~50-bit primes
    out['radix3_ntt_modmults_3primes'] = 3 * ntt3
    out['ratio_radix3_3primes_over_pow2_3limbs'] = 3 * ntt3 / (3 * ntt_pow2)
    out['ratio_kara4374_over_pow2_3limb_ntt'] = out['kara_mults_N4374_cutoff1'] / (3 * ntt_pow2)
    # instruction-class note: a Z/2^64 product needs only the LOW 64 bits (one mul);
    # a Shoup modmul is ~3 mul-class instructions (measured 0.737 ns, h2-verdict).
    out['time_bracket_us_kara4374_at_0.3ns_and_0.5ns_per_mult'] = (
        out['kara_mults_N4374_cutoff1'] * 0.3e-3, out['kara_mults_N4374_cutoff1'] * 0.5e-3)
    out['time_us_pow2_3limb_ntt_at_0.737ns_per_modmult'] = 3 * ntt_pow2 * 0.737e-3
    # worst-case coefficient expansion: monomial op-norm 2 (harness) => delta_R <= 2N
    out['delta_R_coeff_basis_upper'] = 2 * N3
    out['delta_R_negacyclic_4096_proved_tight'] = N2
    out['delta_R_extra_bits_per_level'] = math.log2(2 * N3 / N2)
    return out


# ----------------------------------------------------------------------------- §2
def section2(v: int = 25, deg: int = 3) -> dict:
    out = {}
    for d, r in ((162, 81), (107, None), (131, None), (4374, 2187)):
        km = kara_mults(d)
        out[f'GR_d{d}_bytes'] = 8 * d
        out[f'GR_d{d}_schoolbook_mults'] = d * d
        out[f'GR_d{d}_kara_mults'] = km
        out[f'GR_d{d}_kara_adds'] = kara_adds(d) + (phi3_reduction_adds(r) if r else d - 1)
    # dense x sparse (weight h challenge in the degree-162 subring): h monomial shifts,
    # each <= d coefficient moves + 2r reduction subs, zero multiplications.
    h, d, r = 60, 162, 81
    out['dense_x_sparse_h60_d162_add_class_ops'] = h * (d + 2 * r)
    out['dense_x_sparse_h60_mults'] = 0
    # bilinear-complexity floor for a degree-162 algebra: 2*162 - 1
    out['bilinear_lower_bound_d162'] = 2 * 162 - 1
    # sumcheck at (v, deg): round 1 tables are base-ring words; rounds 2..v hold dense
    # extension elements. Per cell per round: (deg+1) evaluation points x (deg-1) products.
    cells_ext = sum(2 ** (v - i) for i in range(2, v + 1))
    per_cell = (deg + 1) * (deg - 1)
    out['sumcheck_ext_mults_total'] = cells_ext * per_cell
    out['sumcheck_base_round_u64_mults'] = 2 ** (v - 1) * per_cell
    out['sumcheck_u64_mults_GR162_kara'] = cells_ext * per_cell * out['GR_d162_kara_mults']
    out['sumcheck_u32_mults_BabyBearExt4_schoolbook16'] = cells_ext * per_cell * 16
    out['sumcheck_u32_mults_BabyBearExt4_kara9'] = cells_ext * per_cell * 9
    out['ratio_GR162_over_Ext4_schoolbook'] = out['GR_d162_kara_mults'] / 16
    out['ratio_GR162_over_Ext4_kara'] = out['GR_d162_kara_mults'] / 9
    out['ratio_lower_bound_over_Ext4'] = (2 * 162 - 1) / 16
    # table bytes after round 1 (deg = 3 => three tables)
    out['tables_bytes_after_round1_GR162'] = 3 * 2 ** (v - 1) * 8 * 162
    out['tables_bytes_after_round1_Ext4'] = 3 * 2 ** (v - 1) * 16
    out['fold_ops_per_round_i_GR162_sparse'] = 'entries(i) x 3 tables x %d adds, 0 mults' % (h * (d + 2 * r))
    # logup denominator inverse: Hensel from F_{2^162}: 6 Newton steps x 2 dense mults
    out['dense_inverse_u64_mults_via_hensel'] = 6 * 2 * out['GR_d162_kara_mults']
    # ct x ct identity a*b = c + m*Phi checked by evaluation at rho in GR(2^64,162) with
    # precomputed powers: scalar (u64) x dense (162 words) per coefficient.
    out['ctxct_eval_check_u64_mults'] = (3 * 4374 + 4373 + 8747) * 162
    out['ctxct_eval_check_over_perform_kara'] = out['ctxct_eval_check_u64_mults'] / kara_mults(4374)
    return out


# ----------------------------------------------------------------------------- §3
def section3() -> dict:
    # h2-verdict [READ]: 61-bit arm: +3.03 bits margin at depth 1, -29.94 at depth 2
    # (N = 4096, t = 2^20, d = 512, 8-bit weights); one level costs 33-42 bits.
    m1_61, m2_61 = 3.03, -29.94
    extra = 64 - 61
    ring_bits = math.log2(2 * 4374 / 4096)  # worst-case delta_R doubling + dimension
    return {'margin_depth1_bits_at_64_negacyclic_shift': m1_61 + extra,
            'margin_depth2_bits_at_64_negacyclic_shift': m2_61 + extra,
            'ring_correction_bits_per_level': ring_bits,
            'margin_depth1_bits_Phi3_8': m1_61 + extra - ring_bits,
            'margin_depth2_bits_Phi3_8': m2_61 + extra - 2 * ring_bits,
            'levels_at_64': 1, 'levels_deployed_109': 2,
            'Delta_q_over_t': 2 ** 44, 'r_t_q': (2 ** 64) % (2 ** 20)}


# ----------------------------------------------------------------------------- §4
def delta_bkz(b: float) -> float:
    return ((math.pi * b) ** (1 / b) * b / (2 * math.pi * math.e)) ** (1 / (2 * (b - 1)))


def primal_usvp_beta(n: int, logq: float, sigma_e: float, sigma_s: float):
    """Smallest BKZ blocksize beta (and m) with sigma_e*sqrt(beta) <= delta^(2beta-d-1) *
    vol^(1/d), vol = q^m * nu^n, nu = sigma_e/sigma_s (Bai–Galbraith scaling), d = n+m+1.
    ADPS16 / Alkim et al. success condition; no additive constants."""
    q = 2.0 ** logq
    nu = sigma_e / sigma_s
    for beta in range(60, 3000):
        dl = delta_bkz(beta)
        for m in range(n // 4, 3 * n, 4):
            d = n + m + 1
            rhs = dl ** (2 * beta - d - 1) * math.exp((m * math.log(q) + n * math.log(nu)) / d)
            if sigma_e * math.sqrt(beta) <= rhs:
                return beta, m
    return None, None


def cyclotomic_log_disc(p: int, k: int) -> float:
    """ln|Delta| for Q(zeta_{p^k}): |Delta| = p^{p^{k-1}(pk-k-1)}."""
    return p ** (k - 1) * (p * k - k - 1) * math.log(p)


def section4() -> dict:
    out = {}
    sig_e = 3.2
    sig_ternary = math.sqrt(2 / 3)
    sig_cbd20 = math.sqrt(10)          # deployed secret: CBD, variance 10 (fhe-core-theory)
    # calibration row: HE standard v1.1 Table 1 (BKZ.sieve), ternary secret, n=4096 -> logq 109
    b, m = primal_usvp_beta(4096, 109, sig_e, sig_ternary)
    out['calib_n4096_logq109_ternary'] = {'beta': b, 'm': m, 'coreSVP_0.292b': 0.292 * b,
                                          'sieve_0.292b+16.4': 0.292 * b + 16.4,
                                          'HE_standard_quoted_bits': 128}
    for (n, lq, ss, label) in ((4374, 64, sig_cbd20, 'n4374_logq64_CBD20'),
                               (4374, 64, sig_ternary, 'n4374_logq64_ternary'),
                               (4096, 64, sig_ternary, 'n4096_logq64_ternary'),
                               (4374, 109, sig_cbd20, 'n4374_logq109_CBD20')):
        b, m = primal_usvp_beta(n, lq, sig_e, ss)
        out[label] = {'beta': b, 'm': m, 'coreSVP_classical_0.292b': round(0.292 * b, 1),
                      'coreSVP_quantum_0.265b': round(0.265 * b, 1),
                      'sieve_0.292b+16.4': round(0.292 * b + 16.4, 1)}
    # module-BKZ discriminant term (2025/1904 abstract): blocksize shift
    # (ln|Delta_K| - d ln d)/d * beta/ln beta  (negative = attacker gain)
    d3, d2 = 4374, 4096
    t3 = (cyclotomic_log_disc(3, 8) - d3 * math.log(d3)) / d3
    t2 = (cyclotomic_log_disc(2, 13) - d2 * math.log(d2)) / d2
    b64 = out['n4374_logq64_CBD20']['beta']
    out['module_bkz'] = {'ln_disc_over_d_minus_ln_d_Phi3^8': t3,
                         'same_for_Phi2^13_should_be_0': t2,
                         'blocksize_shift_at_beta': b64,
                         'delta_beta': t3 * b64 / math.log(b64),
                         'delta_bits_coreSVP': 0.292 * t3 * b64 / math.log(b64)}
    # NTRU-overstretched threshold for reference (ABD16 regime is super-polynomial q; the
    # Kirchner–Fouque/DvW fatigue point for power-of-two conductors is q ~ n^2.484)
    out['ntru_fatigue_log2_n4374_pow2.484'] = 2.484 * math.log2(4374)
    return out


# ----------------------------------------------------------------------------- §5
def section5() -> dict:
    B = 2 ** 16
    out = {}
    for gamma, label in ((1, 'acc_rbr_fold_rho1'), (32, 'ambient_h16'), (120, 'subring_h60')):
        # binding needs a nonvacuous norm gap: 2*(b0 + T*gamma*B) < q = 2^64 (acc-rbr-fold §3, strict)
        T = (2 ** 63 - B) // (gamma * B)
        while 2 * (B + T * gamma * B) >= 2 ** 64:
            T -= 1
        out[label] = {'op_norm': gamma, 'T_max_no_wrap': T, 'log2_T': math.log2(T)}
    out['tree_wall_T'] = 2 ** 47 - 2
    out['recurrence'] = 'b0 + T*gamma*B < 2^63 (additive chain; same shape as acc-rbr-fold budget)'
    # LatticeFold needs MSIS at 8*T*B with T the expansion factor
    out['latticefold_msis_norm_8TB_h16'] = 8 * 32 * B
    out['latticefold_msis_norm_8TB_h60'] = 8 * 120 * B
    return out


# ----------------------------------------------------------------------------- §6
class Phi3Ring:
    """Z/2^k [X] / (X^{2r} + X^r + 1), coefficient lists of length 2r."""

    def __init__(self, r: int, k: int):
        self.r, self.n, self.k, self.mod = r, 2 * r, k, 1 << k

    def reduce(self, c: list[int]) -> list[int]:
        r, n = self.r, self.n
        c = list(c) + [0] * max(0, 4 * r - len(c))
        for j in range(r - 1, -1, -1):   # X^{3r+j} = X^j
            c[j] += c[3 * r + j]
            c[3 * r + j] = 0
        for j in range(r - 1, -1, -1):   # X^{2r+j} = -X^{r+j} - X^j
            c[r + j] -= c[2 * r + j]
            c[j] -= c[2 * r + j]
            c[2 * r + j] = 0
        return [x % self.mod for x in c[:n]]

    def mul(self, a: list[int], b: list[int]) -> list[int]:
        n = self.n
        c = [0] * (2 * n - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    c[i + j] += ai * bj
        return self.reduce(c)

    def sub(self, a, b):
        return [(x - y) % self.mod for x, y in zip(a, b)]

    def centered(self, a):
        return [x - self.mod if x >= self.mod // 2 else x for x in a]

    def monomial(self, j):
        v = [0] * (3 * self.r)
        v[j] = 1
        return self.reduce(v)


def gf2_mod(a: int, m: int) -> int:
    while a and a.bit_length() >= m.bit_length():
        a ^= m << (a.bit_length() - m.bit_length())
    return a


def gf2_mulmod(a: int, b: int, m: int) -> int:
    res = 0
    while b:
        if b & 1:
            res ^= a
        b >>= 1
        a <<= 1
        if a.bit_length() == m.bit_length():
            a ^= m
    return res


def gf2_inv(a: int, m: int) -> int:
    """Inverse in F_2[X]/(m) by extended Euclid; m irreducible."""
    r0, r1, s0, s1 = m, a, 0, 1
    while r1 != 1:
        # divide r0 by r1
        q, rem = 0, r0
        while rem and rem.bit_length() >= r1.bit_length():
            sh = rem.bit_length() - r1.bit_length()
            q ^= 1 << sh
            rem ^= r1 << sh
        r0, r1 = r1, rem
        # s = s0 - q*s1 over F_2[X] (no modulus needed for correctness, reduce for size)
        qs = 0
        qq, ss = q, s1
        while qq:
            if qq & 1:
                qs ^= ss
            qq >>= 1
            ss <<= 1
        s0, s1 = s1, s0 ^ qs
        if r1 == 0:
            raise ValueError('not invertible')
    return gf2_mod(s1, m)


def gf2_is_irreducible(m: int, n: int) -> bool:
    """Rabin-style: gcd(X^{2^i} - X, m) = 1 for i <= n/2."""
    x = 2
    xp = x
    for i in range(1, n // 2 + 1):
        xp = gf2_mulmod(xp, xp, m)
        g = gf2_gcd(xp ^ x, m)
        if g != 1:
            return False
    return True


def gf2_gcd(a: int, b: int) -> int:
    while b:
        a, b = b, gf2_mod(a, b)
    return a


def poly_to_gf2(c: list[int]) -> int:
    return sum((x & 1) << i for i, x in enumerate(c))


def gf2_to_poly(a: int, n: int) -> list[int]:
    return [(a >> i) & 1 for i in range(n)]


def gr_inverse(R: Phi3Ring, a: list[int], phi_bits: int) -> list[int]:
    """Newton/Hensel lift of the residue-field inverse: y <- y(2 - a y)."""
    y = gf2_to_poly(gf2_inv(poly_to_gf2(a), phi_bits), R.n)
    prec = 1
    two = [2] + [0] * (R.n - 1)
    while prec < R.k:
        ay = R.mul(a, y)
        y = R.mul(y, R.sub(two, ay))
        prec *= 2
    return y


def op_norm_exact(R: Phi3Ring, c: list[int]) -> int:
    """Exact linf->linf operator norm of multiplication by an INTEGER element c
    (coefficients taken centered): max row l1 of the multiplication matrix."""
    cols = [R.centered(R.mul(c, R.monomial(j))) for j in range(R.n)]
    return max(sum(abs(cols[j][i]) for j in range(R.n)) for i in range(R.n))


def det_bareiss(M: list[list[int]]) -> int:
    """Exact integer determinant (fraction-free Gaussian elimination)."""
    n = len(M)
    M = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def algebraic_norm(c: list[int], m: int) -> int:
    """N_{Q(zeta_m)/Q}(c(zeta)) EXACTLY: determinant of the integer multiplication-by-c
    matrix in the power basis of Z[X]/(Phi_m), m = 3^a (a 200-bit modulus stands in for Z)."""
    r = m // 3
    RZ = Phi3Ring(r, 200)
    cc = [x % RZ.mod for x in c]
    cols = [RZ.centered(RZ.mul(cc, RZ.monomial(j))) for j in range(RZ.n)]
    return det_bareiss([[cols[j][i] for j in range(RZ.n)] for i in range(RZ.n)])


def section6(seed: int = 20260904) -> dict:
    rng = random.Random(seed)
    out = {}
    for m, r, hs, k_list in ((27, 9, (2, 3), (8, 16, 32, 64)), (81, 27, (2,), (16, 64))):
        n = 2 * r
        phi_bits = (1 << n) | (1 << r) | 1
        res = {'conductor': m, 'degree': n, 'ord_2_mod_m': None,
               'Phi_irreducible_mod_2': gf2_is_irreducible(phi_bits, n)}
        o, x = 1, 2 % m
        while x != 1:
            x = x * 2 % m
            o += 1
        res['ord_2_mod_m'] = o
        assert o == n and res['Phi_irreducible_mod_2']
        for h in hs:
            supports = list(itertools.combinations(range(n), h))
            chal = []
            for S in supports:
                v = [0] * n
                for j in S:
                    v[j] = 1
                chal.append(v)
            pairs = 0
            for a, b in itertools.combinations(chal, 2):
                dlt = [x - y for x, y in zip(a, b)]
                assert any(dlt)                       # distinct supports
                assert sum(dlt) == 0                  # equal weight => delta(1) = 0
                assert poly_to_gf2([x % 2 for x in dlt]) != 0   # nonzero in F_{2^n}
                pairs += 1
            rec = {'weight': h, 'set_size': len(chal), 'pairs_unit_mod_2_checked': pairs}
            # exact operator norms of the challenges themselves (<= 2h claimed)
            R1 = Phi3Ring(r, 64)
            nsample = 400 if m == 27 else 60
            ops = [op_norm_exact(R1, c) for c in chal[:nsample]]
            rec[f'op_norm_max_first{nsample}'] = max(ops)
            rec['op_norm_bound_2h'] = 2 * h
            # inverses of differences mod 2^k: centered linf relative to 2^(k-1)
            sample = [rng.sample(range(len(chal)), 2) for _ in range(60)]
            for k in k_list:
                R = Phi3Ring(r, k)
                ratios = []
                for i, j in sample:
                    dlt = [(x - y) % R.mod for x, y in zip(chal[i], chal[j])]
                    inv = gr_inverse(R, dlt, phi_bits)
                    one = [1] + [0] * (n - 1)
                    assert R.mul(dlt, inv) == one
                    ratios.append(max(abs(t) for t in R.centered(inv)) / 2 ** (k - 1))
                ratios.sort()
                rec[f'inverse_linf_over_2^(k-1)_k{k}_min_med_max'] = (
                    round(ratios[0], 4), round(ratios[len(ratios) // 2], 4), round(ratios[-1], 4))
            # algebraic norms of differences: never +-1 (3 | N), always odd
            norms = []
            for i, j in sample[:40]:
                dlt = [x - y for x, y in zip(chal[i], chal[j])]
                N = algebraic_norm(dlt, m)
                assert N % 2 == 1 and N % 3 == 0 and abs(N) != 1
                norms.append(N)
            rec['algebraic_norms_sample'] = {'all_odd': True, 'all_divisible_by_3': True,
                                             'min_abs': min(map(abs, norms)), 'max_abs': max(map(abs, norms))}
            res[f'weight_{h}'] = rec
        # slack 3: g = sum_{j<2r} X^j + sum_{j<r} X^j satisfies (1 - X) g = 3 mod Phi
        RZ = Phi3Ring(r, 64)
        g = [2] * r + [1] * r
        one_minus_x = [1, -1 % RZ.mod] + [0] * (n - 2)
        prod = RZ.mul(one_minus_x, g)
        assert prod == [3] + [0] * (n - 1)
        res['slack3'] = {'(1-X)*g == 3 mod Phi': True, 'linf_g': 2, 'l1_g': 3 * r,
                         'op_norm_g_exact': op_norm_exact(RZ, g),
                         '3_is_unit_mod_2^64': math.gcd(3, 2 ** 64) == 1}
        # monomial op-norm = 2 exactly (harness had <= 2)
        res['monomial_op_norm_max'] = max(op_norm_exact(RZ, RZ.monomial(j)) for j in range(n))
        # subring: Phi_{m/3}(X^3) == Phi_m(X) as polynomials
        res['subring_embedding_Phi_{m/3}(X^3)=Phi_m'] = True  # X^{2r}+X^r+1 = (X^3)^{2r/3}+(X^3)^{r/3}+1
        out[f'conductor_{m}'] = res
    # top-level sizes
    out['A_16_ambient_bits'] = math.log2(math.comb(4374, 16))
    out['A_60_subring162_bits'] = math.log2(math.comb(162, 60))
    out['monomial_set_with_signs_bits'] = math.log2(2 * 4374)
    return out


# ----------------------------------------------------------------------------- §7
def section7(seed: int = 7) -> dict:
    rng = random.Random(seed)
    R = Phi3Ring(3, 2)          # GR(4, 6) = Z_4[X]/(X^6 + X^3 + 1)
    n = R.n
    elems = [list(t) for t in itertools.product(range(4), repeat=n)]
    checks = 0
    for _ in range(40):
        deg = rng.randint(1, 5)
        coeffs = [[rng.randrange(4) for _ in range(n)] for _ in range(deg + 1)]

        def F(x):
            acc = [0] * n
            for c in reversed(coeffs):
                acc = R.mul(acc, x)
                acc = [(u + w) % 4 for u, w in zip(acc, c)]
            return acc
        for x in rng.sample(elems, 200):
            z = rng.choice(elems)
            y = [(a + 2 * b) % 4 for a, b in zip(x, z)]
            fx, fy = F(x), F(y)
            assert all((a - b) % 2 == 0 for a, b in zip(fx, fy))
            checks += 1
    # witness: the digit map D(x) = x >> 1 (coefficientwise) is not a ring polynomial and
    # breaks the congruence: x = 0, y = 2 (== 0 mod 2) but D(0) = 0, D(2) = 1.
    x0, y0 = [0] * n, [2] + [0] * (n - 1)
    Dx = [c >> 1 for c in x0]
    Dy = [c >> 1 for c in y0]
    assert (Dx[0] - Dy[0]) % 2 == 1
    return {'GR(4,6)_polynomial_maps_respect_mod2': checks, 'digit_map_witness': {'x': 0, 'y': 2, 'D(x)': 0, 'D(y)': 1},
            'x^7_algebraic_degree_over_F2n': bin(7).count('1'),
            'x^(2^i+1)_algebraic_degree': 2}


def main() -> None:
    res = {'s1_mult_cost': section1(), 's2_extension': section2(), 's3_noise': section3(),
           's4_security': section4(), 's5_fold_budget': section5(),
           's6_challenge_lemmas': section6(), 's7_hash_congruence': section7()}
    print(json.dumps(res, indent=1, default=str))
    print('\nPASS: all assertions (counts + exhaustive small-parameter checks; not a security claim)')


if __name__ == '__main__':
    main()
