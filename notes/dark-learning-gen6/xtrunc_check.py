"""Exhaustive check of the XT mask test on toy primes, and of perfect hiding + no-wrap of the public rule."""
import itertools, random
def plan(p, nb):
    T = 0
    while T < nb and (p >> (nb - 1 - T)) & 1: T += 1
    L = nb - T
    P = p & ((1 << L) - 1)
    return T, L, P
def y_of(r, p, nb):
    T, L, P = plan(p, nb)
    b = [(r >> i) & 1 for i in range(nb)]
    a = T - sum(b[L:])
    E = [None] * (L + 1); E[L] = 1
    m = min([i for i in range(L) if (P >> i) & 1], default=L)
    mults = 0
    for i in range(L - 1, m - 1, -1):
        e = b[i] if (P >> i) & 1 else 1 - b[i]
        E[i] = E[i + 1] * e
        if i < L - 1: mults += 1
    lt = sum(E[i + 1] - E[i] for i in range(L) if (P >> i) & 1)
    assert lt == (1 if (r & ((1 << L) - 1)) < P else 0)
    return a + lt, mults + 1
for nb in range(3, 11):
    for p in range(2 ** (nb - 1) + 1, 2 ** nb, 2):
        if any(p % q == 0 for q in range(3, int(p ** .5) + 1, 2)): continue
        for r in range(2 ** nb):
            y, _ = y_of(r, p, nb)
            assert (y == 0) == (r >= p), (p, r)
print("mask test: y == 0 iff r >= p, every odd prime of 3..10 bits, every r")
# perfect hiding + no wrap under the public rule c >= 2^(K+1), toy field
for p, K in [(1021, 3), (2039, 4), (4093, 5)]:
    for x in range(-(1 << K), 1 << K):
        xp = x + (1 << K)
        acc = {}
        for r in range(p):
            c = (xp + r) % p
            if c < 1 << (K + 1):
                continue
            assert xp + r < p                      # no wrap on an accepted opening
            acc[c] = acc.get(c, 0) + 1
        assert sorted(acc) == list(range(1 << (K + 1), p)) and set(acc.values()) == {1}
print("public rule: accepted c uniform on [2^(K+1), p) for every x; accepted => no wrap")
for name, p in [("N4096", 0x1ffffffffff92001), ("N8192", 0x1fffffffffec4001), ("N16384", 0x1fffffffffcf8001)]:
    T, L, P = plan(p, 61)
    _, mults = y_of(5, p, 61)
    for _ in range(20000):
        r = random.getrandbits(61) if random.random() < .5 else random.randrange(p - 4096, 1 << 61)
        y, _ = y_of(r, p, 61)
        assert (y == 0) == (r >= p)
    print(name, hex(p), "T", T, "L", L, "P", hex(P), "mults per mask (chain + rho y)", mults, "reject 2^%.2f" % __import__('math').log2(((1 << 61) - p) / 2 ** 61))
