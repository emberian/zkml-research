#!/usr/bin/env python3
"""hensel_preimage.py -- the kill test for a polynomial ("Poseidon-shaped") hash over Z/2^k.

Claim [INFERRED, ours; the mechanism is Klimov-Shamir T-function bit-slicing, CHES 2002,
recalled not read]: any map built from Z/2^k-polynomial S-boxes and Z/2^k-linear layers is a
T-function, and for i >= 1

    F(x + 2^i b) = F(x) + 2^i * J_F(x) * b   (mod 2^{i+1}),    b in {0,1}^n,

so bit-plane i of the output is AFFINE over F_2 in bit-plane i of the input given the lower
planes (Taylor: second-order terms carry 2^{2i}, which vanish mod 2^{i+1} once i >= 1).
Plane 0 is F mod 2, which is affine because x^n = x on F_2 for every n >= 1.
Hence a preimage is found by k successive F_2 linear solves (plus backtracking where the
mod-2 Jacobian drops rank).  The Jacobian is obtained by finite differences, so the attack
needs only black-box evaluations of F: it never reads the design.

Two S-boxes: 'rivest' x(2x+1) (a permutation polynomial mod 2^w, Rivest 2001; derivative
4x+1 = 1 mod 2, so J never drops rank) and 'cube' x^3 (not a permutation; derivative 3x^2 =
x mod 2, so J drops rank at even S-box inputs and the search backtracks).

Hash model: state t words of k bits, c capacity words fixed to 0, message t-c words,
R rounds of (add constants, S-box each word, multiply by a matrix invertible mod 2);
digest = first c words.  Preimage: given digest y, find m with H(m) = y.
"""
import random, sys, time

def make_params(k, t, R, seed):
    rng = random.Random(seed)
    mask = (1 << k) - 1
    while True:
        M = [[rng.randrange(1 << k) for _ in range(t)] for _ in range(t)]
        if gf2_rank([[x & 1 for x in row] for row in M]) == t:
            break
    RC = [[rng.randrange(1 << k) for _ in range(t)] for _ in range(R)]
    return M, RC, mask

def gf2_rank(rows):
    rows = [int("".join(map(str, r)), 2) if isinstance(r, list) else r for r in rows]
    rank = 0
    for bit in reversed(range(max(1, max(r.bit_length() for r in rows) if rows else 1))):
        piv = next((i for i, r in enumerate(rows) if (r >> bit) & 1), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and (rows[i] >> bit) & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank

def sbox(x, kind, mask):
    if kind == "rivest":
        return (x * (2 * x + 1)) & mask
    if kind == "cube":
        return (x * x * x) & mask
    raise ValueError(kind)

def permute(state, M, RC, mask, kind):
    t = len(state)
    s = list(state)
    for rc in RC:
        s = [sbox((x + a) & mask, kind, mask) for x, a in zip(s, rc)]
        s = [sum(M[i][j] * s[j] for j in range(t)) & mask for i in range(t)]
    return s

def H(msg, c, M, RC, mask, kind):
    t = len(M)
    return permute(list(msg) + [0] * c, M, RC, mask, kind)[:c]

def gf2_solve_all(A_rows, rhs, n):
    """All b in {0,1}^n with A b = rhs over F_2.  A_rows: list of n-bit ints (row i), rhs: bits."""
    # Gaussian elimination on augmented rows (bit n = rhs)
    rows = [(r << 1) | y for r, y in zip(A_rows, rhs)]
    pivots = []
    rank = 0
    for col in reversed(range(n)):
        piv = next((i for i in range(rank, len(rows)) if (rows[i] >> (col + 1)) & 1), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and (rows[i] >> (col + 1)) & 1:
                rows[i] ^= rows[rank]
        pivots.append(col)
        rank += 1
    for r in rows[rank:]:
        if r & 1:
            return []  # inconsistent
    free = [c for c in range(n) if c not in pivots]
    sols = []
    for fv in range(1 << len(free)):
        b = 0
        for idx, col in enumerate(free):
            if (fv >> idx) & 1:
                b |= 1 << col
        for i, col in enumerate(pivots):
            # row i: pivot col + free cols ; solve pivot bit
            val = rows[i] & 1
            for idx, fc in enumerate(free):
                if (rows[i] >> (fc + 1)) & 1 and (b >> fc) & 1:
                    val ^= 1
            if val:
                b |= 1 << col
        sols.append(b)
    return sols

def preimage(y, k, c, M, RC, mask, kind, budget=200000):
    """Bit-plane lifting.  Returns (msg, evaluations, backtracks) or (None, ...)."""
    t = len(M)
    n = t - c
    evals = 0
    backtracks = 0
    def F(m):
        nonlocal evals
        evals += 1
        return H(m, c, M, RC, mask, kind)

    def rec(i, m):
        nonlocal backtracks
        if i == k:
            return m
        base = F(m)
        if i == 0:
            # F mod 2 is affine: columns = F(e_j) - F(0) mod 2, rhs = y - F(0) mod 2
            cols = []
            for j in range(n):
                e = list(m); e[j] |= 1
                fe = F(e)
                cols.append([(fe[r] ^ base[r]) & 1 for r in range(c)])
        else:
            cols = []
            for j in range(n):
                e = list(m); e[j] |= 1 << i
                fe = F(e)
                cols.append([((fe[r] - base[r]) >> i) & 1 for r in range(c)])
        A_rows = []
        for r in range(c):
            row = 0
            for j in range(n):
                if cols[j][r]:
                    row |= 1 << j
            A_rows.append(row)
        rhs = [((y[r] - base[r]) >> i) & 1 for r in range(c)]
        sols = gf2_solve_all(A_rows, rhs, n)
        if not sols:
            backtracks += 1
            return None
        random.shuffle(sols)
        for b in sols:
            if evals > budget:
                return None
            m2 = [m[j] | (((b >> j) & 1) << i) for j in range(n)]
            got = rec(i + 1, m2)
            if got is not None:
                return got
            backtracks += 1
        return None

    m = rec(0, [0] * n)
    return m, evals, backtracks

def main():
    k, t, c, R = 32, 6, 2, 8
    print(f"hash over Z/2^{k}: t={t} words, capacity c={c} words (digest {c*k} bits), R={R} rounds")
    for kind in ("rivest", "cube"):
        M, RC, mask = make_params(k, t, R, seed=1)
        ok = 0; tot_e = 0; tot_b = 0; t0 = time.time()
        trials = 10
        for trial in range(trials):
            rng = random.Random(100 + trial)
            m_true = [rng.randrange(1 << k) for _ in range(t - c)]
            y = H(m_true, c, M, RC, mask, kind)
            m, e, b = preimage(y, k, c, M, RC, mask, kind)
            found = m is not None and H(m, c, M, RC, mask, kind) == y
            ok += found; tot_e += e; tot_b += b
        dt = time.time() - t0
        print(f"  S-box {kind:6s}: preimages found {ok}/{trials}; mean evaluations {tot_e/trials:.0f}"
              f" (brute force ~2^{c*k}); mean backtracks {tot_b/trials:.1f}; {dt/trials*1000:.0f} ms each")
    # the free distinguisher: bit-plane 0 of the digest depends only on bit-plane 0 of the message
    M, RC, mask = make_params(k, t, R, seed=1)
    rng = random.Random(7)
    same = 0
    for _ in range(200):
        m1 = [rng.randrange(1 << k) for _ in range(t - c)]
        m2 = [x ^ (rng.randrange(1 << (k - 1)) << 1) for x in m1]  # flip only bits >= 1
        y1 = H(m1, c, M, RC, mask, "rivest"); y2 = H(m2, c, M, RC, mask, "rivest")
        same += all((a & 1) == (b & 1) for a, b in zip(y1, y2))
    print(f"  T-function distinguisher: digest LSBs unchanged when only message bits >= 1 change: {same}/200")

if __name__ == "__main__":
    main()
