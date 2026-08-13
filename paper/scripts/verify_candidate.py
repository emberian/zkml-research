#!/usr/bin/env python3
"""verify_candidate.py — computational checks behind the Rock-1 paper draft.

Every check here is a COMPUTED claim in paper/CLAIM-LEDGER.md. Pure Python 3,
no dependencies. Run: python3 verify_candidate.py

Primality: deterministic Miller-Rabin for n < 2^64 (12-base set, proven
exhaustive by Sorenson-Webster); 40 fixed bases above 2^64 (probabilistic,
error < 4^-40 per composite — flagged as such in output).
"""

import sys

DET_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
BIG_BASES = list(range(2, 179))  # first ~40 primes among these are used


def _mr_round(n, a):
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    x = pow(a, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(r - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


def is_prime(n):
    if n < 2:
        return False
    for p in DET_BASES:
        if n == p:
            return True
        if n % p == 0:
            return False
    bases = DET_BASES if n < 2**64 else [b for b in BIG_BASES if is_prime_small(b)][:40]
    return all(_mr_round(n, a) for a in bases)


def is_prime_small(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))


def v2(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def ord_mod(a, m):
    """Multiplicative order of a mod m (m small: brute force)."""
    if a % m == 0:
        return None
    x, k = a % m, 1
    while x != 1:
        x = x * a % m
        k += 1
        if k > m:
            return None
    return k


CHECKS = []


def check(name, cond):
    CHECKS.append((name, bool(cond)))
    print(f"[{'PASS' if cond else 'FAIL'}] {name}")


# ---------------------------------------------------------------- the candidate
P61 = 2**61 - 2**54 + 1
GOLDILOCKS = 2**64 - 2**32 + 1
BABYBEAR = 2**31 - 2**27 + 1
KOALABEAR = 2**31 - 2**24 + 1

print("== candidate p61 = 2^61 - 2^54 + 1 ==")
check("p61 == 2287828610704211969", P61 == 2287828610704211969)
check("p61 == 127*2^54 + 1 (family form, cofactor 127)", P61 == 127 * 2**54 + 1)
check("p61 is prime (deterministic MR < 2^64)", is_prime(P61))
check("2-adicity of p61-1 is exactly 54", v2(P61 - 1) == 54)
check("cofactor (p61-1)/2^54 == 127, prime", (P61 - 1) // 2**54 == 127 and is_prime(127))
check("KoalaBear == 127*2^24 + 1 == 2^31 - 2^24 + 1 (same Solinas shape)",
      KOALABEAR == 127 * 2**24 + 1)

# Solinas fold identity used by Goldilocks-class reduction: 2^61 = 2^54 - 1 (mod p)
check("fold identity: 2^61 ≡ 2^54 - 1 (mod p61)", pow(2, 61, P61) == (2**54 - 1) % P61)
check("3 lazy-reduction bits: p61 < 2^61 <= 2^64/8", P61 < 2**61)

# NTT legality: p-1 = 2^54 * 127, so the group has a 2^54 subgroup.
# Generator test needs only the prime factors {2, 127} of p-1.
g = next(a for a in range(2, 100)
         if pow(a, (P61 - 1) // 2, P61) != 1 and pow(a, (P61 - 1) // 127, P61) != 1)
omega = pow(g, (P61 - 1) // 2**54, P61)
check(f"omega = g^((p-1)/2^54) with g={g} has omega^(2^53) == -1 (order exactly 2^54; "
      "negacyclic NTT legal to N = 2^53)", pow(omega, 2**53, P61) == P61 - 1)

# ------------------------------------------------- 3-adic inertia (ord_9 criterion)
# Phi_{3^k} irreducible mod p for ALL k  <=>  p is a primitive root mod 9
# (ord_9(p) = 6; lifts to every 3^k since (Z/3^k)* is cyclic and p.r. mod 9 => mod 3^k).
print("\n== 3-adic inertia: ord_9 criterion ==")
check("ord_9(p61) == 6  (maximal inertia: Phi_{3^k} irreducible for all k)",
      ord_mod(P61, 9) == 6)
check("ord_9(Goldilocks) == 3  (FAILS maximal inertia)", ord_mod(GOLDILOCKS, 9) == 3)
check("ord_9(BabyBear) == 3  (FAILS maximal inertia)", ord_mod(BABYBEAR, 9) == 3)
check("ord_9(KoalaBear) == 6  (passes)", ord_mod(KOALABEAR, 9) == 6)
# direct check at higher conductors for p61: ord_{3^k}(p) == 2*3^(k-1) = phi(3^k)
direct = all(ord_mod(P61, 3**k) == 2 * 3**(k - 1) for k in range(2, 9))
check("direct: ord_{3^k}(p61) == phi(3^k) for k = 2..8", direct)

# ---------------------------------------------------------------- the family law
# For p = 127*2^n + 1 PRIME: maximal inertia <=> n ≡ 0 or 2 (mod 6).
# (n ≡ 1,3,5 mod 6 give 3 | p — never prime; n ≡ 4 mod 6 gives ord_9(p) = 2.)
print("\n== family law: p = 127*2^n + 1, n = 1..80 ==")
law_holds, family_primes = True, []
for n in range(1, 81):
    p = 127 * 2**n + 1
    if n % 2 == 1 or n % 6 == 3:
        if p % 3 != 0:
            law_holds = False
        continue
    if is_prime(p):
        inert = ord_mod(p, 9) == 6
        family_primes.append((n, inert))
        if inert != (n % 6 in (0, 2)):
            law_holds = False
check("n odd or n ≡ 3 (mod 6)  =>  3 | p (no primes there)", law_holds)
check("every family prime n=1..80: maximal inertia <=> n ≡ 0,2 (mod 6)", law_holds)
print("   family primes found:",
      ", ".join(f"n={n}({'inert' if i else 'NOT'})" for n, i in family_primes))
check("KoalaBear (n=24 ≡ 0) and p61 (n=54 ≡ 0) both instances, both inert",
      (24, True) in family_primes and (54, True) in family_primes)
# The law's failing branch, exhibited: first family prime with n ≡ 4 (mod 6)
# is n = 214 (search to 600), and it fails maximal inertia with ord_9 = 2.
p214 = 127 * 2**214 + 1
check("failing witness: 127*2^214 + 1 prime (probabilistic MR) with ord_9 == 2 (NOT inert)",
      is_prime(p214) and ord_mod(p214, 9) == 2)

# ---------------------------------------------------------------- known adicities
print("\n== reference adicities ==")
check("2-adicity(Goldilocks) == 32", v2(GOLDILOCKS - 1) == 32)
check("2-adicity(BabyBear) == 27", v2(BABYBEAR - 1) == 27)
check("2-adicity(KoalaBear) == 24", v2(KOALABEAR - 1) == 24)

# ------------------------------------------- Goldilocks cyclotomic triple identity
print("\n== Goldilocks barrel-shift structure (identities only; uniqueness scan is a lane) ==")
check("Goldilocks == Phi_6(2^32) == Phi_12(2^16) == Phi_24(2^8)",
      GOLDILOCKS == 2**64 - 2**32 + 1
      and (lambda x: x * x - x + 1)(2**32) == GOLDILOCKS
      and (lambda x: x**4 - x**2 + 1)(2**16) == GOLDILOCKS
      and (lambda x: x**8 - x**4 + 1)(2**8) == GOLDILOCKS)

# ---------------------------------------------------------- Crandall exclusion
# p = 2^k - c, c odd < 4096: 2-adicity(p-1) = v2(2^k - (c+1)) = v2(c+1) <= 12.
print("\n== Crandall primes 2^k - c, c < 4096: structural 2-adicity cap ==")
crandall_ok = all(v2(2**90 - c - 1) == v2(c + 1) for c in range(1, 4096, 2))
check("v2(2^k - c - 1) == v2(c+1) for all odd c < 4096 (k=90 witness)", crandall_ok)
check("max v2(c+1) over odd c < 4096 == 12 (so 2-adicity <= 12, structural)",
      max(v2(c + 1) for c in range(1, 4096, 2)) == 12)

# ---------------------------------------------------------------- Solinas census
print("\n== Solinas census: p = 2^a - 2^b + 1, a in [96,130] ==")
solinas = []
for a in range(96, 131):
    for b in range(1, a):
        p = 2**a - 2**b + 1
        if is_prime(p):
            solinas.append((a, b))  # 2-adicity of p-1 is exactly b
total = len(solinas)
deep = [(a, b) for a, b in solinas if b >= 20]
print(f"   primes found: {total}  |  with 2-adicity >= 20: {len(deep)}")
print(f"   (bases above 2^64 are probabilistic MR, 40 rounds)")
check("census note figure: 93 primes with 2-adicity >= 20 in a ∈ [96,130]",
      len(deep) == 93)
for a, b in [(108, 50), (109, 58), (109, 65), (113, 32)]:
    check(f"example 2^{a} - 2^{b} + 1 is prime with 2-adicity {b}", (a, b) in solinas)

# ---------------------------------------------------------------------- verdict
print()
fails = [n for n, ok in CHECKS if not ok]
if fails:
    print(f"RESULT: {len(fails)} FAILED of {len(CHECKS)}")
    sys.exit(1)
print(f"RESULT: all {len(CHECKS)} checks pass")
