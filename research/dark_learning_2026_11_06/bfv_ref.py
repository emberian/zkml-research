"""Minimal exact BFV reference over Python integers, for COUNTING certificates, not for security.

2026-11-06. Pure Python 3, no dependencies. Polynomials are lists of ints of length N in
Z[X]/(X^N+1). Negacyclic products use Kronecker substitution on Python big ints (exact).
Textbook BFV: Delta = floor(Q/t), ternary secret (the deployed secret is CBD(20); the
certificate sizes below depend on coefficient BOUNDS, which are stated, not on the
distribution). Nothing here is constant-time or secure; it exists so the certificate
witnesses are computed on a real ciphertext product and checked.
"""
import random

def is_probable_prime(n, rounds=40):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    rng = random.Random(n)
    for _ in range(rounds):
        a = rng.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def ntt_primes(bits, count, two_n, exclude=()):
    """Largest primes below 2^bits with p = 1 mod 2N (NTT-friendly for X^N+1)."""
    out = []
    p = ((1 << bits) - 1) // two_n * two_n + 1
    while len(out) < count:
        if p not in exclude and is_probable_prime(p):
            out.append(p)
        p -= two_n
    return out

def centered(x, m):
    x %= m
    return x - m if x > m // 2 else x

def poly_centered(a, m):
    return [centered(x, m) for x in a]

def _pack(p, wb):
    """Nonnegative coefficients -> one big int, wb bytes per slot, little-endian (linear time)."""
    return int.from_bytes(b"".join(c.to_bytes(wb, "little") for c in p), "little")

def _unpack(v, wb, n):
    raw = v.to_bytes(wb * n, "little")
    return [int.from_bytes(raw[i * wb:(i + 1) * wb], "little") for i in range(n)]

def negacyclic_mul(a, b):
    """Exact product in Z[X]/(X^N+1) via Kronecker substitution on byte-packed nonnegative parts
    (a = a+ - a-), linear-time packing. Returns (z, k) with a(X) b(X) = z(X) + (X^N + 1) k(X) over Z,
    deg z < N, deg k < N - 1."""
    N = len(a)
    ap = [x if x > 0 else 0 for x in a]
    an = [-x if x < 0 else 0 for x in a]
    bp = [x if x > 0 else 0 for x in b]
    bn = [-x if x < 0 else 0 for x in b]
    ma = max(1, max(abs(x) for x in a))
    mb = max(1, max(abs(x) for x in b))
    bound = N * ma * mb
    wb = (bound.bit_length() + 8) // 8 + 1
    Pa, Na, Pb, Nb = (_pack(x, wb) for x in (ap, an, bp, bn))
    pos = _unpack(Pa * Pb + Na * Nb, wb, 2 * N)
    neg = _unpack(Pa * Nb + Na * Pb, wb, 2 * N)
    full = [u - v for u, v in zip(pos, neg)][: 2 * N - 1]
    low = full[:N]
    high = full[N:] + [0]
    z = [low[i] - high[i] for i in range(N)]
    k = high[: N - 1]
    return z, k

def poly_add(a, b):
    return [x + y for x, y in zip(a, b)]

def poly_sub(a, b):
    return [x - y for x, y in zip(a, b)]

def poly_mod(a, m):
    return [x % m for x in a]

class BFV:
    def __init__(self, N, Q, t, seed=1):
        self.N, self.Q, self.t = N, Q, t
        self.delta = Q // t
        self.rng = random.Random(seed)

    def ternary(self):
        return [self.rng.choice((-1, 0, 1)) for _ in range(self.N)]

    def small_error(self, bound=8):
        return [self.rng.randint(-bound, bound) for _ in range(self.N)]

    def uniform(self):
        return [self.rng.randrange(self.Q) for _ in range(self.N)]

    def mul_mod(self, a, b):
        z, _ = negacyclic_mul(poly_centered(a, self.Q), poly_centered(b, self.Q))
        return poly_mod(z, self.Q)

    def keygen(self):
        self.s = self.ternary()
        return self.s

    def encrypt(self, m):
        """Secret-key encryption: (c0, c1) = (Delta m - a s - e, a)."""
        a = self.uniform()
        e = self.small_error()
        as_, _ = negacyclic_mul(poly_centered(a, self.Q), self.s)
        # centered message representative: with textbook Delta = floor(Q/t), encoding m near t leaves a
        # term r = Q mod t that a later ct x ct multiplies by the lift quotient (~N^2 |s|): fatal at t ~ 2^61
        c0 = [(self.delta * centered(mi, self.t) - x - ei) % self.Q for mi, x, ei in zip(m, as_, e)]
        return (c0, a)

    def decrypt(self, ct):
        """Decrypt a 2- or 3-component ciphertext with (1, s, s^2)."""
        acc = poly_centered(ct[0], self.Q)
        spow = self.s
        for comp in ct[1:]:
            prod, _ = negacyclic_mul(poly_centered(comp, self.Q), spow)
            acc = poly_add(acc, prod)
            spow, _ = negacyclic_mul(spow, self.s)
        acc = poly_centered(acc, self.Q)
        return [((self.t * x * 2 + self.Q) // (2 * self.Q)) % self.t for x in acc]

    def tensor_lifted(self, ct1, ct2):
        """Integer tensor of centered lifts: d0 = a0 b0, d1 = a0 b1 + a1 b0, d2 = a1 b1 over Z[X]/(X^N+1)."""
        a0, a1 = (poly_centered(c, self.Q) for c in ct1)
        b0, b1 = (poly_centered(c, self.Q) for c in ct2)
        z00, k00 = negacyclic_mul(a0, b0)
        z01, k01 = negacyclic_mul(a0, b1)
        z10, k10 = negacyclic_mul(a1, b0)
        z11, k11 = negacyclic_mul(a1, b1)
        d = [z00, poly_add(z01, z10), z11]
        ks = [k00, poly_add(k01, k10), k11]
        return d, ks, (a0, a1, b0, b1)

    def scale(self, d):
        """out = round(t d / Q) mod Q, nearest with ties up: t d + floor(Q/2) = Q y + s, 0 <= s < Q."""
        Q, t = self.Q, self.t
        ys, ss = [], []
        for x in d:
            num = t * x + Q // 2
            y, s = divmod(num, Q)
            ys.append(y)
            ss.append(s)
        return ys, ss
