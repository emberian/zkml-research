"""Exact public NTT matvec producing both ring outputs and polynomial quotients.

No keys, encryption, random oracle, verifier or cryptographic parameter claim.
NTT order is natural frequency order, with a bit-reversed input permutation.
"""
from collections import Counter
from dataclasses import dataclass

P = 2013265921


def prime_by_trial_division(p):
    if p < 2 or (p % 2 == 0 and p != 2):
        return False
    d = 3
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def power_two_root(order, p):
    assert order > 0 and order & (order - 1) == 0
    assert (p - 1) % order == 0
    if order == 1:
        return 1
    for candidate in range(2, p):
        root = pow(candidate, (p - 1) // order, p)
        if pow(root, order // 2, p) == p - 1:
            return root
    raise ValueError('No root found')


class Plan:
    def __init__(self, n, negacyclic=False, p=P):
        assert n > 0 and n & (n - 1) == 0
        self.n, self.p, self.negacyclic = n, p, negacyclic
        self.psi = power_two_root(2 * n, p) if negacyclic else 1
        self.omega = self.psi * self.psi % p if negacyclic else power_two_root(n, p)
        width = n.bit_length() - 1
        self.reverse = [int(f'{i:0{width}b}'[::-1], 2) if width else 0 for i in range(n)]
        self.stage_tables = []
        self.inverse_tables = []
        length = 2
        while length <= n:
            w = pow(self.omega, n // length, p)
            self.stage_tables.append([pow(w, j, p) for j in range(length // 2)])
            iw = pow(w, p - 2, p)
            self.inverse_tables.append([pow(iw, j, p) for j in range(length // 2)])
            length *= 2
        self.twist = [pow(self.psi, j, p) for j in range(n)]
        self.untwist_normalize = [pow(n, p - 2, p) * pow(self.psi, -j, p) % p for j in range(n)]
        self.counts = Counter()

    def transform(self, values, inverse=False):
        assert len(values) == self.n
        p = self.p
        a = [x % p for x in values]
        if self.negacyclic and not inverse:
            a = [x * t % p for x, t in zip(a, self.twist)]
            self.counts['twist_multiplications'] += self.n
        a = [a[j] for j in self.reverse]
        length = 2
        for table in self.inverse_tables if inverse else self.stage_tables:
            for block in range(0, self.n, length):
                for j, w in enumerate(table):
                    u = a[block + j]
                    v = a[block + j + length // 2] * w % p
                    a[block + j] = (u + v) % p
                    a[block + j + length // 2] = (u - v) % p
            length *= 2
        butterflies = self.n * (self.n.bit_length() - 1) // 2
        self.counts['butterfly_multiplications'] += butterflies
        self.counts['butterfly_additions'] += 2 * butterflies
        if inverse:
            a = [x * t % p for x, t in zip(a, self.untwist_normalize)]
            self.counts['normalization_multiplications'] += self.n
        self.counts[('inverse_' if inverse else 'forward_') + str(self.n)] += 1
        return a


def shape(A, C):
    r, m, k, n = len(A), len(C), len(C[0]), len(A[0][0])
    assert r and m and k and n
    assert all(len(row) == m for row in A)
    assert all(len(row) == k for row in C)
    assert all(len(v) == n for row in A for v in row)
    assert all(len(v) == n for row in C for v in row)
    return r, m, k, n


def spectral_matmul(Ahat, Chat, p, counts):
    r, m, k, n = len(Ahat), len(Chat), len(Chat[0]), len(Ahat[0][0])
    out = []
    for i in range(r):
        outrow = []
        for c in range(k):
            v = [0] * n
            for j in range(m):
                v = [(x + a * b) % p for x, a, b in zip(v, Ahat[i][j], Chat[j][c])]
            outrow.append(v)
        out.append(outrow)
    counts['hadamard_multiplications'] += r * m * k * n
    counts['spectral_accumulation_additions'] += r * m * k * n
    return out


@dataclass
class Cache:
    mode: str
    n: int
    p: int
    plans: list
    spectra: list
    preprocessing_counts: dict


def preprocess(A, mode='split', p=P):
    n = len(A[0][0])
    assert mode in ('split', 'long')
    plans = [Plan(n, False, p), Plan(n, True, p)] if mode == 'split' else [Plan(2 * n, False, p)]
    spectra = []
    counts = Counter()
    for plan in plans:
        spectra.append([[plan.transform(a if mode == 'split' else a + [0] * n) for a in row] for row in A])
        counts.update(plan.counts)
        plan.counts.clear()
    return Cache(mode, n, p, plans, spectra, dict(counts))


def evaluate(cache, C):
    n, p, mode = cache.n, cache.p, cache.mode
    r = len(cache.spectra[0])
    m = len(cache.spectra[0][0])
    assert len(C) == m and all(len(c) == n for row in C for c in row)
    k = len(C[0])
    assert all(len(row) == k for row in C)
    counts, blocks = Counter(), []
    for plan, Ahat in zip(cache.plans, cache.spectra):
        Chat = [[plan.transform(c if mode == 'split' else c + [0] * n) for c in row] for row in C]
        outputhat = spectral_matmul(Ahat, Chat, p, counts)
        blocks.append([[plan.transform(v, True) for v in row] for row in outputhat])
        counts.update(plan.counts)
        plan.counts.clear()
    if mode == 'long':
        Q = [[v[n:] for v in row] for row in blocks[0]]
        Y = [[[(lo - hi) % p for lo, hi in zip(v[:n], v[n:])] for v in row] for row in blocks[0]]
    else:
        D, Y = blocks
        inv2 = (p + 1) // 2
        Q = [[[(d - y) * inv2 % p for d, y in zip(D[i][c], Y[i][c])] for c in range(k)] for i in range(r)]
        counts['quotient_recombination_multiplications'] += r * k * n
    counts['quotient_recombination_additions'] += r * k * n
    assert all(v[-1] == 0 for row in Q for v in row), 'Degree below N-1 is required'
    return Y, Q, dict(counts)


def duplicate_baseline(A, C, p=P, plans=None):
    """Own model of the named source's duplicate per-product NTT arithmetic.

    Includes no crypto, Rust execution, PCS work or source transplant.
    """
    r, m, k, n = shape(A, C)
    short, long = plans if plans is not None else (Plan(n, True, p), Plan(2 * n, True, p))
    assert short.n == n and long.n == 2 * n and short.p == long.p == p
    assert short.negacyclic and long.negacyclic
    short.counts.clear()
    long.counts.clear()
    counts = Counter()
    Y = [[[0] * n for _ in range(k)] for _ in range(r)]
    S = [[[0] * (2 * n) for _ in range(k)] for _ in range(r)]
    for i in range(r):
        for j in range(m):
            for c in range(k):
                for plan, out, length in ((short, Y, n), (long, S, 2 * n)):
                    aa = A[i][j] + [0] * (length - n)
                    cc = C[j][c] + [0] * (length - n)
                    ah, ch = plan.transform(aa), plan.transform(cc)
                    values = plan.transform([a * b % p for a, b in zip(ah, ch)], True)
                    out[i][c] = [(x + v) % p for x, v in zip(out[i][c], values)]
                    counts['hadamard_multiplications'] += length
                    counts['coefficient_accumulation_additions'] += length
    Q = [[v[n:] for v in row] for row in S]
    from_remainders = [[[(lo - hi) % p for lo, hi in zip(v[:n], v[n:])] for v in row] for row in S]
    assert from_remainders == Y
    counts['quotient_recombination_additions'] += r * k * n
    counts.update(short.counts)
    counts.update(long.counts)
    return Y, Q, dict(counts)


def schoolbook(A, C, p=P):
    r, m, k, n = shape(A, C)
    S = [[[0] * (2 * n) for _ in range(k)] for _ in range(r)]
    for i in range(r):
        for c in range(k):
            for j in range(m):
                for a in range(n):
                    for b in range(n):
                        S[i][c][a + b] = (S[i][c][a + b] + A[i][j][a] * C[j][c][b]) % p
    return ([[[(v[t] - v[t + n]) % p for t in range(n)] for v in row] for row in S],
            [[v[n:] for v in row] for row in S])


def evaluate_poly(coeffs, x, p=P):
    result = 0
    for c in reversed(coeffs):
        result = (result * x + c) % p
    return result
