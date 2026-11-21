#!/usr/bin/env python3
"""
Deterministic algebraic & numerical verification for SEAM_AND_PRIOR_ART.md:
1. zkGPT Eq. (8) completeness failure on batched matmul (shared free batch index b without eq).
2. zkLLM proof.cu (993311e) hadamard_product_sumcheck (Fr_hp_sc) completeness failure.
3. Native MXFP4 3-operand EinSumcheck (ikb,jkb,jk -> ij):
   - Exact MLE identity over BabyBear (p = 2013265921) and Goldilocks (p = 2^64 - 2^32 + 1).
   - Round-by-round univariate degree verification under elimination order j -> k -> b:
     * j-rounds: exact degree 3 (4th finite difference == 0)
     * k-rounds: exact degree 3 (4th finite difference == 0)
     * b-rounds (intra-block 32): exact degree 2 (3rd finite difference == 0)
4. Exact gpt-oss-20b MXFP4 overflow bounds & commitment bit/felt accounting.
"""

import random

P_BB = 2013265921  # BabyBear: 15 * 2^27 + 1
P_GL = (1 << 64) - (1 << 32) + 1  # Goldilocks
P_61 = (1 << 61) - 1  # Mersenne-61


def eq_bit(r: int, b: int, p: int) -> int:
    return (r * b + (1 - r) * (1 - b)) % p


def eq_vec(r_vec: list[int], b_int: int, p: int) -> int:
    """MSB-first eq polynomial on {0,1}^d."""
    d = len(r_vec)
    acc = 1
    for idx, r in enumerate(r_vec):
        bit = (b_int >> (d - 1 - idx)) & 1
        acc = (acc * eq_bit(r, bit, p)) % p
    return acc


def mle_eval_msb(table: list[int], r_vec: list[int], p: int) -> int:
    d = len(r_vec)
    assert len(table) == (1 << d)
    acc = 0
    for i, val in enumerate(table):
        acc = (acc + (val % p) * eq_vec(r_vec, i, p)) % p
    return acc


def verify_zkgpt_eq8(p: int = P_BB) -> None:
    rng = random.Random(20261120)
    A = [rng.randrange(1, 100) for _ in range(8)]
    B = [rng.randrange(1, 100) for _ in range(8)]
    V1 = [0] * 8
    for b in range(2):
        for x in range(2):
            for y in range(2):
                s = 0
                for c in range(2):
                    s += A[(b << 2) | (x << 1) | c] * B[(b << 2) | (c << 1) | y]
                V1[(b << 2) | (x << 1) | y] = s % p

    r1 = [rng.randrange(2, p - 1) for _ in range(3)]
    r2 = [rng.randrange(2, p - 1) for _ in range(3)]
    alpha, beta = rng.randrange(2, p - 1), rng.randrange(2, p - 1)

    lhs = (alpha * mle_eval_msb(V1, r1, p) + beta * mle_eval_msb(V1, r2, p)) % p

    rhs_zkgpt = 0
    for c in (0, 1):
        t1 = mle_eval_msb(A, [r1[0], r1[1], c], p) * mle_eval_msb(B, [r1[0], c, r1[2]], p)
        t2 = mle_eval_msb(A, [r2[0], r2[1], c], p) * mle_eval_msb(B, [r2[0], c, r2[2]], p)
        rhs_zkgpt = (rhs_zkgpt + alpha * t1 + beta * t2) % p

    rhs_fixed = 0
    for b in (0, 1):
        for c in (0, 1):
            t1 = (
                eq_bit(r1[0], b, p)
                * mle_eval_msb(A, [b, r1[1], c], p)
                * mle_eval_msb(B, [b, c, r1[2]], p)
            )
            t2 = (
                eq_bit(r2[0], b, p)
                * mle_eval_msb(A, [b, r2[1], c], p)
                * mle_eval_msb(B, [b, c, r2[2]], p)
            )
            rhs_fixed = (rhs_fixed + alpha * t1 + beta * t2) % p

    assert lhs != rhs_zkgpt, "zkGPT Eq. (8) unexpectedly matched!"
    assert lhs == rhs_fixed, "Fixed EinSumcheck batched matmul failed!"
    print(f"[PASS] zkGPT Eq. (8) completeness failure reproduced: LHS={lhs} != RHS_zkGPT={rhs_zkgpt}, RHS_EinSumcheck={rhs_fixed}")


def mle_eval_lsb(table: list[int], u_vec: list[int], p: int) -> int:
    """zkLLM Fr_me convention (fr-tensor.cu:589-609): u[0] folds LSB."""
    cur = [x % p for x in table]
    for x in u_vec:
        nxt = []
        for gid in range((len(cur) + 1) // 2):
            a0 = cur[2 * gid]
            a1 = cur[2 * gid + 1] if (2 * gid + 1) < len(cur) else 0
            nxt.append((a0 + x * (a1 - a0)) % p)
        cur = nxt
    assert len(cur) == 1
    return cur[0]


def verify_zkllm_proof_cu(p: int = P_BB) -> None:
    rng = random.Random(20261121)
    d = 3
    N = 1 << d
    a = [rng.randrange(1, 100) for _ in range(N)]
    b = [rng.randrange(1, 100) for _ in range(N)]
    y = [(a[i] * b[i]) % p for i in range(N)]
    u = [rng.randrange(2, p - 1) for _ in range(d)]
    v = [rng.randrange(2, p - 1) for _ in range(d)]

    claim_y = mle_eval_lsb(y, u, p)

    cur_a, cur_b = a[:], b[:]
    hp_rounds = []
    for r_idx in range(d):
        out_size = len(cur_a) // 2
        out0, out1, out2 = [], [], []
        for gid in range(out_size):
            a0, a1 = cur_a[2 * gid], cur_a[2 * gid + 1]
            b0, b1 = cur_b[2 * gid], cur_b[2 * gid + 1]
            out0.append((a0 * b0) % p)
            out1.append((a0 * (b1 - b0) + b0 * (a1 - a0)) % p)
            out2.append(((a1 - a0) * (b1 - b0)) % p)
        u_rem = u[r_idx + 1 :]
        c0 = mle_eval_lsb(out0, u_rem, p)
        c1 = mle_eval_lsb(out1, u_rem, p)
        c2 = mle_eval_lsb(out2, u_rem, p)
        hp_rounds.append((c0, c1, c2))
        vr = v[r_idx]
        cur_a = [(cur_a[2 * g] + vr * (cur_a[2 * g + 1] - cur_a[2 * g])) % p for g in range(out_size)]
        cur_b = [(cur_b[2 * g] + vr * (cur_b[2 * g + 1] - cur_b[2 * g])) % p for g in range(out_size)]

    c0, c1, c2 = hp_rounds[0]
    g1_0 = c0
    g1_1 = (c0 + c1 + c2) % p
    assert (g1_0 + g1_1) % p != claim_y, "Fr_hp_sc round 1 unexpectedly matched!"
    assert ((1 - u[0]) * g1_0 + u[0] * g1_1) % p == claim_y
    print(f"[PASS] zkLLM Fr_hp_sc (proof.cu:67-107, called in rmsnorm.cu:47) fails round-1 check: g1(0)+g1(1)={(g1_0+g1_1)%p} != Y(u)={claim_y}")


def finite_diffs(vals: list[int], p: int) -> list[list[int]]:
    diffs = [vals]
    cur = vals
    while len(cur) > 1:
        cur = [(cur[i + 1] - cur[i]) % p for i in range(len(cur) - 1)]
        diffs.append(cur)
    return diffs


def verify_mxfp4_3op_einsumcheck(p: int, name: str) -> None:
    rng = random.Random(20261122)
    log_i, log_j, log_k, log_b = 2, 2, 2, 5
    I, J, K, B = 1 << log_i, 1 << log_j, 1 << log_b - 3, 1 << log_b
    K = 1 << log_k

    e2m1_x2 = [-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12]
    X = [rng.randint(-200, 200) for _ in range(I * K * B)]
    Q = [rng.choice(e2m1_x2) for _ in range(J * K * B)]
    S = [1 << rng.randint(0, 3) for _ in range(J * K)]

    D = [0] * (I * J)
    for i in range(I):
        for j in range(J):
            acc = 0
            for k in range(K):
                s_jk = S[j * K + k]
                base_x = (i * K + k) * B
                base_q = (j * K + k) * B
                blk = 0
                for b in range(B):
                    blk += X[base_x + b] * Q[base_q + b]
                acc += blk * s_jk
            D[i * J + j] = acc % p

    r_i = [rng.randrange(2, p - 1) for _ in range(log_i)]
    r_j = [rng.randrange(2, p - 1) for _ in range(log_j)]

    lhs = mle_eval_msb(D, r_i + r_j, p)

    X_ri = [0] * (K * B)
    for k in range(K):
        for b in range(B):
            col = [X[(i * K + k) * B + b] for i in range(I)]
            X_ri[k * B + b] = mle_eval_msb(col, r_i, p)

    eq_tab = [eq_vec(r_j, j, p) for j in range(J)]
    X_tab = X_ri[:]
    Q_tab = [q % p for q in Q]
    S_tab = [s % p for s in S]

    def fold_msb(tab: list[int], t_val: int) -> list[int]:
        half = len(tab) // 2
        return [(tab[idx] + t_val * (tab[idx + half] - tab[idx])) % p for idx in range(half)]

    cur_claim = lhs
    j_degrees, k_degrees, b_degrees = [], [], []

    cur_J = J
    for _ in range(log_j):
        evals = []
        for t in range(5):
            eq_t = fold_msb(eq_tab, t)
            Q_t = fold_msb(Q_tab, t)
            S_t = fold_msb(S_tab, t)
            s_val = 0
            for j2 in range(cur_J // 2):
                eq_v = eq_t[j2]
                for k in range(K):
                    s_jk = (eq_v * S_t[j2 * K + k]) % p
                    base_x = k * B
                    base_q = (j2 * K + k) * B
                    for b in range(B):
                        s_val = (s_val + s_jk * X_tab[base_x + b] * Q_t[base_q + b]) % p
            evals.append(s_val)
        assert (evals[0] + evals[1]) % p == cur_claim
        diffs = finite_diffs(evals, p)
        assert diffs[4][0] == 0
        deg = max(d_idx for d_idx in range(len(diffs)) if any(x != 0 for x in diffs[d_idx]))
        j_degrees.append(deg)

        chal = rng.randrange(2, p - 1)
        c2 = (chal * (chal - 1) * pow(2, p - 2, p)) % p
        c3 = (c2 * (chal - 2) * pow(3, p - 2, p)) % p
        cur_claim = (diffs[0][0] + chal * diffs[1][0] + c2 * diffs[2][0] + c3 * diffs[3][0]) % p
        eq_tab = fold_msb(eq_tab, chal)
        Q_tab = fold_msb(Q_tab, chal)
        S_tab = fold_msb(S_tab, chal)
        cur_J //= 2

    eq_scalar = eq_tab[0]

    cur_K = K
    for _ in range(log_k):
        evals = []
        for t in range(5):
            X_t = fold_msb(X_tab, t)
            Q_t = fold_msb(Q_tab, t)
            S_t = fold_msb(S_tab, t)
            s_val = 0
            for k2 in range(cur_K // 2):
                s_k = (eq_scalar * S_t[k2]) % p
                base = k2 * B
                for b in range(B):
                    s_val = (s_val + s_k * X_t[base + b] * Q_t[base + b]) % p
            evals.append(s_val)
        assert (evals[0] + evals[1]) % p == cur_claim
        diffs = finite_diffs(evals, p)
        assert diffs[4][0] == 0
        deg = max(d_idx for d_idx in range(len(diffs)) if any(x != 0 for x in diffs[d_idx]))
        k_degrees.append(deg)

        chal = rng.randrange(2, p - 1)
        c2 = (chal * (chal - 1) * pow(2, p - 2, p)) % p
        c3 = (c2 * (chal - 2) * pow(3, p - 2, p)) % p
        cur_claim = (diffs[0][0] + chal * diffs[1][0] + c2 * diffs[2][0] + c3 * diffs[3][0]) % p
        X_tab = fold_msb(X_tab, chal)
        Q_tab = fold_msb(Q_tab, chal)
        S_tab = fold_msb(S_tab, chal)
        cur_K //= 2

    s_scalar = (eq_scalar * S_tab[0]) % p

    cur_B = B
    for _ in range(log_b):
        evals = []
        for t in range(4):
            X_t = fold_msb(X_tab, t)
            Q_t = fold_msb(Q_tab, t)
            s_val = 0
            for b2 in range(cur_B // 2):
                s_val = (s_val + s_scalar * X_t[b2] * Q_t[b2]) % p
            evals.append(s_val)
        assert (evals[0] + evals[1]) % p == cur_claim
        diffs = finite_diffs(evals, p)
        assert diffs[3][0] == 0
        deg = max(d_idx for d_idx in range(len(diffs)) if any(x != 0 for x in diffs[d_idx]))
        b_degrees.append(deg)

        chal = rng.randrange(2, p - 1)
        c2 = (chal * (chal - 1) * pow(2, p - 2, p)) % p
        cur_claim = (diffs[0][0] + chal * diffs[1][0] + c2 * diffs[2][0]) % p
        X_tab = fold_msb(X_tab, chal)
        Q_tab = fold_msb(Q_tab, chal)
        cur_B //= 2

    final_rhs = (s_scalar * X_tab[0] * Q_tab[0]) % p
    assert cur_claim == final_rhs
    print(f"[PASS] MXFP4 3-op EinSumcheck ({name}): exact match; degrees j={j_degrees}, k={k_degrees}, b={b_degrees}")


def compute_gptoss_mxfp4_numbers() -> None:
    D = 2880
    max_x = 32768
    max_q = 12
    for sh in [2, 3, 6, 7, 8]:
        max_D = D * max_x * max_q * (1 << sh)
        fits_61 = (2 * max_D) < P_61
        fits_gl = (2 * max_D) < P_GL
        fits_bb = (2 * max_D) < P_BB
        max_D_xsplit = D * 128 * max_q * (1 << sh)
        fits_bb_xsplit = (2 * max_D_xsplit) < P_BB
        print(
            f"  spread sh={sh}: |D|_max={max_D:.3e} (2|D| < p61:{fits_61}, GL:{fits_gl}, BB:{fits_bb}); "
            f"with int8 X-split: |D_limb|_max={max_D_xsplit:.3e} (2|D_limb| < BB:{fits_bb_xsplit}, ratio={2*max_D_xsplit/P_BB:.3f})"
        )

    w_per_layer = 32 * 5760 * 2880 + 32 * 2880 * 2880
    w_total_24 = 24 * w_per_layer
    s_per_layer = w_per_layer // 32
    s_total_24 = 24 * s_per_layer

    bits_native_4 = 4 * w_total_24 + 8 * s_total_24
    bits_native_5 = 5 * w_total_24 + 9 * s_total_24
    bits_deq_29 = 29 * w_total_24
    felts_native = w_total_24 + s_total_24
    felts_2limb = 2 * w_total_24

    print(f"  gpt-oss-20b MoE weights: {w_per_layer:,}/layer, {w_total_24:,} across 24 layers ({s_total_24:,} blocks)")
    print(
        f"  Bits/weight: native-4b = {bits_native_4/w_total_24:.3f} b/w ({bits_native_4/8/1e9:.3f} GB), "
        f"native-5b = {bits_native_5/w_total_24:.3f} b/w, dequant-29b = 29.000 b/w ({bits_deq_29/8/1e9:.3f} GB)"
    )
    print(f"  Bit savings: {bits_deq_29/bits_native_4:.2f}x (4b) / {bits_deq_29/bits_native_5:.2f}x (5b)")
    print(
        f"  Felt commitments (24L MoE): native = {felts_native:,} (1.03125 felts/w) vs "
        f"2-limb = {felts_2limb:,} (2.0 felts/w) -> {felts_2limb/felts_native:.4f}x reduction"
    )


if __name__ == "__main__":
    verify_zkgpt_eq8()
    verify_zkllm_proof_cu()
    verify_mxfp4_3op_einsumcheck(P_BB, "BabyBear")
    verify_mxfp4_3op_einsumcheck(P_GL, "Goldilocks")
    compute_gptoss_mxfp4_numbers()
