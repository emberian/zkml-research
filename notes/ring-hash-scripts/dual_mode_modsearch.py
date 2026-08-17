# tau=2 joint-modulus search, mirroring design_tau_tradeoff.py's tau=4 search.
# Conditions: q prime just under 2^64 (gamma = 2^64 - q = B^K - q small, B=2^16 K=4);
# ord_32(q) = 2  (X^16+1 splits into 8 quadratics -> tau=2, ell=8 slots F_{q^2});
# gcd(7, q^2 - 1) = 1  (C1: alpha=7 legal at tau=2)  <=>  q mod 7 not in {1, 6}.
from sympy import isprime
from math import gcd, log2
hits = []
for gamma in range(1, 4000):
    q = 2**64 - gamma
    r32 = q % 32
    # order of q mod 32 == 2  <=> q^2 = 1 mod 32 and q != 1 mod 32
    if pow(r32, 2, 32) != 1 or r32 == 1:
        continue
    if q % 7 in (1, 6):
        continue
    if not isprime(q):
        continue
    assert gcd(7, q*q - 1) == 1
    hits.append((gamma, q, r32, q % 7))
    if len(hits) >= 5:
        break
for gamma, q, r32, r7 in hits:
    print(f"gamma={gamma:5d}  q={q}  q mod 32={r32:2d}  q mod 7={r7}  gamma/q=2^{log2(gamma/q):.1f}")
# control: the tau=4 joint modulus from the design note
q4 = 2**64 - 279
def ord32(x):
    o, y = 1, x % 32
    while y != 1:
        y = (y*x) % 32; o += 1
    return o
print("control 2^64-279: ord_32 =", ord32(q4), "(design note says tau=4) prime:", isprime(q4))
