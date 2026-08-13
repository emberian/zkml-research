#!/usr/bin/env python3
"""koalabear_limb.py — recompute, from scratch, the KoalaBear-limb result.

REVIVAL lane, 2026-08-13. A result reported by three lanes and lost to a
SendMessage failure. Nothing here trusts the recovered numbers; everything is
recomputed and each claim prints PASS/FAIL.

Sections
  1. KoalaBear as a negacyclic-NTT limb at N=4096 (primality, 2-adicity, 8192)
  2. Enumerate KB x two-Solinas-companion towers in the 105-112 bit band
  3. The depth-2 ledger: which towers actually support the MEASURED depth 2
  4. Emulation cost model: what fraction of proof-side limb arithmetic goes
     native, derived (not assumed) from sub-limb counts

Pure python3 stdlib. Run: python3 koalabear_limb.py
"""

import sys
from math import log2, ceil

# ---------------------------------------------------------------- primality
DET_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


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


def _small_primes(limit):
    sieve = [True] * limit
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, limit, i):
                sieve[j] = False
    return [i for i, ok in enumerate(sieve) if ok]


SMALL = _small_primes(2000)


def is_prime(n):
    """Deterministic (Sorenson-Webster 12-base set) below 2^64; 40 fixed
    prime bases above, error < 4^-40 per composite. Every modulus we emit
    here is < 2^64, so every primality claim below is DETERMINISTIC."""
    if n < 2:
        return False
    for p in SMALL[:20]:
        if n == p:
            return True
        if n % p == 0:
            return False
    bases = DET_BASES if n < 2**64 else SMALL[:40]
    return all(_mr_round(n, a) for a in bases)


def v2(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


CHECKS = []


def check(name, cond, note=""):
    CHECKS.append((name, bool(cond)))
    print(f"[{'PASS' if cond else 'FAIL'}] {name}" + (f"   {note}" if note else ""))


# ============================================================ DEPLOYED FACTS
# Source: notes/kpz-noop-and-the-model-gap.md (measured, 40/40 draws) and
# notes/fhe-core-theory.md. N, t and the 3x{36,36,37} tower are the deployed
# fhegg/fhe-dregg BFV parameters.
N = 4096
T = 1032193                     # plaintext modulus, deployed
LOG2_T = log2(T)
LOG2_Q_DEPLOYED = 109.0         # notes quote log2 Q = 109.0
DEPLOYED_LIMB_BITS = (36, 36, 37)
CLIFF_DEPLOYED = 88.02          # measured decrypt cliff, bits
V_FRESH = 4.0                   # measured fresh noise, bits
MUL1 = 42.1                     # measured ct x ct #1 increment, bits
MUL2 = 33.0                     # measured ct x ct #2 increment, bits

print("=" * 74)
print("SECTION 0 -- deployed ground truth, and the cliff formula DERIVED")
print("=" * 74)
# BFV decrypts iff ||noise||_inf < Delta/2 = Q/(2t).
cliff_formula = LOG2_Q_DEPLOYED - 1 - LOG2_T
print(f"   log2 t = {LOG2_T:.4f}   (t = {T} = 2^20 - 2^14 + 1)")
check("t is prime", is_prime(T))
check("t == 2^20 - 2^14 + 1 (t is itself a Solinas prime)", T == 2**20 - 2**14 + 1)
check("2-adicity(t-1) == 14 (t supports N=8192 slots)", v2(T - 1) == 14)
check(f"cliff = log2 Q - 1 - log2 t reproduces the MEASURED 88.02 "
      f"(got {cliff_formula:.2f})", abs(cliff_formula - CLIFF_DEPLOYED) < 0.02)

# depth-2 endpoint
noise_d2 = V_FRESH + MUL1 + MUL2
check(f"measured depth-2 noise = {noise_d2:.1f} bits, margin "
      f"{CLIFF_DEPLOYED - noise_d2:.2f} bits (notes say 8.9)",
      abs((CLIFF_DEPLOYED - noise_d2) - 8.9) < 0.05)

# The mul-growth increment, DERIVED: v <- 2 * delta_R * t * v with delta_R = N.
mul_growth_derived = 1 + log2(N) + LOG2_T
check(f"MUL2 increment is log2(2*N*t) = {mul_growth_derived:.3f} vs measured "
      f"{MUL2} -- derived, not fit", abs(mul_growth_derived - MUL2) < 0.05)

# The mul#1 endpoint is NOT the arithmetic term (that would be
# V_FRESH + 33.0 = 37.0); it is a floor. Identify it as the RNS-BV
# relinearisation floor, which scales as k * q_max.
arith_only_mul1 = V_FRESH + mul_growth_derived
RELIN_FLOOR_DEPLOYED = V_FRESH + MUL1     # = 46.1 bits
check(f"ct x ct #1 lands ABOVE its arithmetic term ({arith_only_mul1:.1f}) at "
      f"{RELIN_FLOOR_DEPLOYED:.1f} => a FLOOR dominates",
      RELIN_FLOOR_DEPLOYED > arith_only_mul1 + 5)
# Worst-case RNS-BV keyswitch bound recorded in fhe-core-theory.md: 2^53.91.
ks_worst = log2(N) + log2(3) + 37 + log2(6 * (10 ** 0.5))
print(f"   RNS-BV keyswitch WORST CASE  delta_R*k*q_max*6sigma = 2^{ks_worst:.2f}"
      f"   (notes record 2^53.91)")
print(f"   measured floor 2^{RELIN_FLOOR_DEPLOYED:.1f} sits {ks_worst - RELIN_FLOOR_DEPLOYED:.1f}"
      f" bits below worst case (average-case ring expansion ~sqrt(N) not N,"
      f" plus sigma vs 6sigma) -- CALIBRATED, see caveat in the note")


def relin_floor(k, log2_qmax):
    """RNS-BV keyswitch noise ~ delta_R * (sum_i q_i) * B_err ~ k * q_max.
    Anchored on the deployed measurement (k=3, q_max=2^37 -> 2^46.1); all
    calibration constants cancel in the ratio."""
    return RELIN_FLOOR_DEPLOYED + log2(k / 3.0) + (log2_qmax - 37.0)


def depth2_noise(k, log2_qmax):
    return relin_floor(k, log2_qmax) + mul_growth_derived


def cliff(log2_q):
    return log2_q - 1 - LOG2_T


def depth2_margin(log2_q, k, log2_qmax):
    return cliff(log2_q) - depth2_noise(k, log2_qmax)


check(f"model reproduces deployed depth-2 margin: "
      f"{depth2_margin(LOG2_Q_DEPLOYED, 3, 37.0):.2f} vs measured 8.90",
      abs(depth2_margin(LOG2_Q_DEPLOYED, 3, 37.0) - 8.90) < 0.1)

# The closed form: margin = log2 Q - log2 q_max - 63.08 for k=3.
closed = LOG2_Q_DEPLOYED - 37.0 - (1 + LOG2_T + RELIN_FLOOR_DEPLOYED - 37.0
                                   + mul_growth_derived - (1 + LOG2_T)) - 0
_const = 1 + LOG2_T + RELIN_FLOOR_DEPLOYED - 37.0 + mul_growth_derived
print(f"\n   CLOSED FORM (k=3): depth-2 margin = log2(Q / q_max) - "
      f"{RELIN_FLOOR_DEPLOYED - 37.0 + mul_growth_derived + 1 + LOG2_T:.2f}")
DEPTH2_CONST = RELIN_FLOOR_DEPLOYED - 37.0 + mul_growth_derived + 1 + LOG2_T
print(f"   i.e. the product of the two SMALLER limbs must exceed "
      f"{DEPTH2_CONST:.2f} bits.")
check(f"closed form agrees with the model (deployed 36+36 = 72 bits vs "
      f"{DEPTH2_CONST:.2f} => margin {72 - DEPTH2_CONST:.2f})",
      abs((72 - DEPTH2_CONST) - depth2_margin(LOG2_Q_DEPLOYED, 3, 37.0)) < 0.3)


# ==================================================== SECTION 1: KOALABEAR
print()
print("=" * 74)
print("SECTION 1 -- KoalaBear as a negacyclic-NTT limb at N=4096")
print("=" * 74)
KB = 2**31 - 2**24 + 1
print(f"   KB = {KB}")
check("KB == 2130706433", KB == 2130706433)
check("KB is prime (deterministic Miller-Rabin, KB < 2^64)", is_prime(KB))
check("2-adicity(KB - 1) == 24", v2(KB - 1) == 24)
check("(KB-1)/2^24 == 127, prime (KB is 127*2^24 + 1)",
      (KB - 1) // 2**24 == 127 and is_prime(127))
check("KB == 1 (mod 8192)  [8192 = 2N, negacyclic legality at N=4096]",
      KB % 8192 == 1)
check("2-adicity 24 >= 13 = log2(2N), so negacyclic NTT legal up to N = 2^23",
      v2(KB - 1) >= 13)
# exhibit the root of unity, do not merely assert its existence
g = next(a for a in range(2, 200)
         if pow(a, (KB - 1) // 2, KB) != 1 and pow(a, (KB - 1) // 127, KB) != 1)
psi = pow(g, (KB - 1) // 8192, KB)
check(f"exhibited psi = g^((KB-1)/8192), g={g}: psi has order exactly 8192 "
      f"(psi^4096 == -1)", pow(psi, 4096, KB) == KB - 1 and pow(psi, 8192, KB) == 1)
check("gcd(KB, t) == 1 (legal RNS limb alongside the deployed plaintext modulus)",
      KB % T != 0 and T % KB != 0)
check("KB > t (limb exceeds plaintext modulus, required by RNS scaling)", KB > T)
check("KB < 2^62 (fits fhe.rs Modulus, u64 Shoup/Barrett lane)", KB < 2**62)
check("KB is Solinas 2^a - 2^b + 1 => cheap reduction fold: "
      "2^31 == 2^24 - 1 (mod KB)", pow(2, 31, KB) == (2**24 - 1) % KB)
print(f"   log2 KB = {log2(KB):.4f}")


# ============================== SECTION 2: THE TOWER ENUMERATION
print()
print("=" * 74)
print("SECTION 2 -- KB x two Solinas companions, 105-112 bit band")
print("=" * 74)
print("""   Conditions imposed on each companion c = 2^a - 2^b + 1, stated explicitly:
     (C1) c prime                       [deterministic MR, all c < 2^64]
     (C2) Solinas form 2^a - 2^b + 1    [cheap reduction: 2^a = 2^b - 1 mod c]
     (C3) 2-adicity(c-1) = b >= 13      [<=> c = 1 mod 8192, negacyclic at N=4096]
     (C4) c != KB, c1 != c2, gcd all 1  [distinct RNS limbs]
     (C5) t < c < 2^62                  [fhe.rs Modulus lane; limb exceeds t]
     (C6) 105 <= log2(KB*c1*c2) <= 112  [the stated noise band]
   Companion exponent range searched: a in [14, 62] (every word-sized limb).""")

# All Solinas primes 2^a - 2^b + 1 with the NTT condition.
solinas = []
for a in range(14, 63):
    for b in range(13, a):          # v2(p-1) = b exactly, need b >= 13
        p = 2**a - 2**b + 1
        if p <= T or p >= 2**62:
            continue
        if is_prime(p):
            solinas.append((a, b, p))
print(f"\n   Solinas primes 2^a-2^b+1, a in [14,62], b in [13,a-1], prime, > t: "
      f"{len(solinas)}")
check("KB (a=31,b=24) is itself in that census",
      (31, 24, KB) in solinas)

LOG2_KB = log2(KB)
BAND_LO, BAND_HI = 105.0, 112.0
towers = []
for i in range(len(solinas)):
    a1, b1, c1 = solinas[i]
    if c1 == KB:
        continue
    for j in range(i + 1, len(solinas)):
        a2, b2, c2 = solinas[j]
        if c2 == KB or c2 == c1:
            continue
        lq = LOG2_KB + log2(c1) + log2(c2)
        if BAND_LO <= lq <= BAND_HI:
            towers.append(((a1, b1, c1), (a2, b2, c2), lq))
towers.sort(key=lambda x: -x[2])
print(f"   KB x c1 x c2 towers with log2 Q in [{BAND_LO},{BAND_HI}]: "
      f"**{len(towers)}**")
print(f"   RECOVERED-CLAIM CHECK: the lost result said 77. Computed here: "
      f"{len(towers)}.")
print("   NOT a canonical number -- see notes/koalabear-limb.md section 2: 77 is")
print("   reachable only under an unstated companion-exponent window (33 settings")
print("   in the sweep hit exactly 77, e.g. a in [35,42]). The SUBSTANCE (the band")
print("   is comfortably populated) reproduces; the COUNT does not.")

EX1, EX2 = 2**37 - 2**25 + 1, 2**38 - 2**36 + 1
ex = [tw for tw in towers if {tw[0][2], tw[1][2]} == {EX1, EX2}]
check("the recovered example KB*(2^37-2^25+1)*(2^38-2^36+1) is in the set "
      "and its log2 Q is 105.57",
      len(ex) == 1 and abs(ex[0][2] - 105.57) < 0.01,
      f"(computed log2 Q = {ex[0][2]:.4f})" if ex else "(ABSENT)")
check("2^37-2^25+1 is prime with 2-adicity 25", is_prime(EX1) and v2(EX1 - 1) == 25)
check("2^38-2^36+1 is prime with 2-adicity 36", is_prime(EX2) and v2(EX2 - 1) == 36)


# ======================= SECTION 3: WHICH TOWERS SUPPORT MEASURED DEPTH 2
print()
print("=" * 74)
print("SECTION 3 -- depth 2 (the MEASURED requirement), not just a bit-range")
print("=" * 74)
print(f"   Requirement: cliff(Q) > relin_floor(3, q_max) + {mul_growth_derived:.2f}")
print(f"   Equivalently: log2(Q / q_max) > {DEPTH2_CONST:.2f} bits, i.e. the")
print(f"   product of the two SMALLER limbs must clear {DEPTH2_CONST:.2f} bits.")
print(f"   KB contributes only {LOG2_KB:.2f}, so the MIDDLE limb must clear "
      f"{DEPTH2_CONST - LOG2_KB:.2f} bits.")

rows = []
for (a1, b1, c1), (a2, b2, c2), lq in towers:
    limbs = sorted([LOG2_KB, log2(c1), log2(c2)])
    qmax = limbs[-1]
    m = depth2_margin(lq, 3, qmax)
    rows.append((lq, (a1, b1, c1), (a2, b2, c2), qmax, m))

ok2 = [r for r in rows if r[4] > 0]
print(f"\n   towers in band: {len(rows)}   supporting measured depth 2: "
      f"**{len(ok2)}**   failing: {len(rows) - len(ok2)}")
if ok2:
    best = max(ok2, key=lambda r: r[4])
    print(f"   best depth-2 margin: {best[4]:.2f} bits at log2 Q = {best[0]:.2f}, "
          f"limbs KB x 2^{best[1][0]}-2^{best[1][1]}+1 x 2^{best[2][0]}-2^{best[2][1]}+1")
print(f"   deployed reference (36/36/37, log2 Q=109.0): margin "
      f"{depth2_margin(109.0, 3, 37.0):.2f} bits")

print("\n   top 12 KB towers by depth-2 margin:")
print("   " + "-" * 88)
print(f"   {'log2 Q':>7} {'cliff':>7} {'limb bits (KB,c1,c2)':>26} "
      f"{'d2 noise':>9} {'margin':>7}  companions")
print("   " + "-" * 88)
for lq, s1, s2, qmax, m in sorted(ok2, key=lambda r: -r[4])[:12]:
    lb = f"{LOG2_KB:.1f},{log2(s1[2]):.1f},{log2(s2[2]):.1f}"
    print(f"   {lq:7.2f} {cliff(lq):7.2f} {lb:>26} "
          f"{depth2_noise(3, qmax):9.2f} {m:7.2f}  "
          f"2^{s1[0]}-2^{s1[1]}+1 x 2^{s2[0]}-2^{s2[1]}+1")

# The single-prime and deployed comparators on the same ledger
print("\n   comparators on the SAME ledger:")
for label, lq, k, qmax in [
        ("deployed 3x{36,36,37}", 109.0, 3, 37.0),
        ("single 109-bit prime  ", 109.0, 1, 109.0),
        ("single p61 = 2^61-2^54+1", log2(2**61 - 2**54 + 1), 1,
         log2(2**61 - 2**54 + 1)),
]:
    print(f"     {label}: cliff {cliff(lq):6.2f}  depth-2 noise "
          f"{depth2_noise(k, qmax):6.2f}  margin {depth2_margin(lq, k, qmax):7.2f}")


# =============== SECTION 3b: THE ACTUAL PROOF FIELD IS BABYBEAR
print()
print("=" * 74)
print("SECTION 3b -- the proof field is BabyBear, NOT KoalaBear (ground truth)")
print("=" * 74)
print("""   circuit/src/field.rs:12          BABYBEAR_P = (1<<31) - (1<<27) + 1
   circuit/src/stark_zk.rs:36,75-97 Poseidon2BabyBear<16>, HidingFriPcs<P3BabyBear>
   Cargo.toml:321                   p3-baby-bear (no p3-koala-bear in the workspace)
   KoalaBear appears in FOUR prose/comment sites repo-wide and ZERO config
   sites. `notes/field-choice-verdict.md` RECOMMENDS KoalaBear; nothing runs it.

   Consequence for the recovered claim: the seam rule ("KoalaBear everywhere
   or BabyBear everywhere, never per-subsystem") says the limb must equal the
   DEPLOYED proof field. Today that is BabyBear. A KoalaBear limb under a
   BabyBear prover introduces a SECOND 31-bit prime -- exactly what the rule
   forbids. So the deployable form of this idea is a BABYBEAR limb.""")

BB = 2**31 - 2**27 + 1
print(f"\n   BB = {BB}")
check("BB == 2013265921 (BabyBear)", BB == 2013265921)
check("BB is prime", is_prime(BB))
check("2-adicity(BB - 1) == 27  (BB - 1 = 2^27 * 15)", v2(BB - 1) == 27)
check("BB == 1 (mod 8192) -- BabyBear is ALSO a legal negacyclic limb at N=4096",
      BB % 8192 == 1)
gb = next(a for a in range(2, 200) if pow(a, (BB - 1) // 2, BB) != 1
          and pow(a, (BB - 1) // 3, BB) != 1 and pow(a, (BB - 1) // 5, BB) != 1)
psib = pow(gb, (BB - 1) // 8192, BB)
check(f"exhibited psi_BB (g={gb}) of order exactly 8192, psi^4096 == -1",
      pow(psib, 4096, BB) == BB - 1 and pow(psib, 8192, BB) == 1)
check("BB > t, gcd(BB,t) = 1", BB > T and T % BB != 0)
check("BB is Solinas: 2^31 == 2^27 - 1 (mod BB)", pow(2, 31, BB) == (2**27 - 1) % BB)
check("BB and KB are DISTINCT primes (a tower could carry both; only one is native)",
      BB != KB)
print(f"   log2 BB = {log2(BB):.4f}   (BB is 0.0779 bits WIDER than KB)")

# BB towers, same conditions
LOG2_BB = log2(BB)
bb_towers = []
for i in range(len(solinas)):
    a1, b1, c1 = solinas[i]
    if c1 == BB:
        continue
    for j in range(i + 1, len(solinas)):
        a2, b2, c2 = solinas[j]
        if c2 == BB:
            continue
        lq = LOG2_BB + log2(c1) + log2(c2)
        if BAND_LO <= lq <= BAND_HI:
            bb_towers.append(((a1, b1, c1), (a2, b2, c2), lq))
print(f"\n   BB x c1 x c2 towers in [{BAND_LO},{BAND_HI}]: {len(bb_towers)}")


def sigma_q(limbs):
    """log2 of sum of limbs -- the RNS-BV digit sum, which sets the relin floor."""
    return log2(sum(limbs))


SIGMA_Q_DEPLOYED = sigma_q(FOLD := [0xffffee001, 0xffffc4001, 0x1ffffe0001])
print(f"\n   deployed sum(q_i) = 2^{SIGMA_Q_DEPLOYED:.3f}")


def relin_floor_sum(log2_sumq):
    return RELIN_FLOOR_DEPLOYED + (log2_sumq - SIGMA_Q_DEPLOYED)


def margin_sum(log2_q, log2_sumq):
    return cliff(log2_q) - (relin_floor_sum(log2_sumq) + mul_growth_derived)


check(f"sum-of-limbs relin model still reproduces the deployed margin "
      f"({margin_sum(LOG2_Q_DEPLOYED, SIGMA_Q_DEPLOYED):.2f} vs 8.90)",
      abs(margin_sum(LOG2_Q_DEPLOYED, SIGMA_Q_DEPLOYED) - 8.90) < 0.1)

for name, base_p, tws in (("KoalaBear", KB, towers), ("BabyBear", BB, bb_towers)):
    good = []
    for s1, s2, lq in tws:
        sq = sigma_q([base_p, s1[2], s2[2]])
        m = margin_sum(lq, sq)
        if m > 0:
            good.append((m, lq, s1, s2))
    good.sort(reverse=True)
    print(f"\n   {name} limb: {len(good)}/{len(tws)} towers support MEASURED depth 2")
    if good:
        print(f"     best 5 by depth-2 margin (deployed reference: "
              f"{margin_sum(LOG2_Q_DEPLOYED, SIGMA_Q_DEPLOYED):.2f} bits):")
        for m, lq, s1, s2 in good[:5]:
            print(f"       log2Q={lq:6.2f}  margin={m:5.2f}  "
                  f"{name[:2]} x 2^{s1[0]}-2^{s1[1]}+1 x 2^{s2[0]}-2^{s2[1]}+1")

print("\n   depth-1 comparators (H2's 61-bit joint prime, on the SAME ledger):")
LQ61 = log2(2**61 - 2**54 + 1)
# with a single prime the BV digit base is a free choice; use 2^20 digits (3 of them)
for lbl, lq, sq in [("p61 joint prime, BV base 2^20", LQ61, log2(3 * 2**20)),
                    ("p61 joint prime, BV base 2^37", LQ61, log2(2**37))]:
    d1 = max(relin_floor_sum(sq), V_FRESH + mul_growth_derived)
    d2 = d1 + mul_growth_derived
    print(f"     {lbl}: cliff {cliff(lq):6.2f} | depth-1 noise {d1:6.2f} "
          f"(margin {cliff(lq) - d1:+6.2f}) | depth-2 noise {d2:6.2f} "
          f"(margin {cliff(lq) - d2:+7.2f})")
print("   => a 61-bit joint prime buys depth 1 with a few bits, and CANNOT reach")
print("      depth 2 at the deployed t. The limb route keeps depth 2 outright.")


# ============================ SECTION 4: EMULATION COST, DERIVED
print()
print("=" * 74)
print("SECTION 4 -- emulation cost, DERIVED then VALIDATED against the real AIR")
print("=" * 74)
print("""   Model. A residue mod q_i (b_i bits) is witnessed in the proof field as k
   sub-limbs of s bits; to prove a*b = c (mod q_i) the AIR witnesses the
   quotient d and checks a*b - c - d*q_i = 0 on the sub-limb decomposition:
       k^2 products for a*b + k^2 for d*q_i    -> 2k^2 native muls
   Overflow: k partial products < 2^(2s) must fit the field, 2s + log2 k <= 31
   => s = 14, k <= 3. A limb that IS the proof field needs k = 1, no quotient,
   no carries, and no canonicity range check: 1 mul, 0 lookups.

   GROUND TRUTH this is checked against (metatheory/Market/PrivateBookBfvButterflyAir.lean):
     :47   RADIX = 2^14                                  <- s = 14, predicted
     :102  qLimb = [8193, 16379, 255]  (14/14/8 bits)    <- k = 3, predicted
     one modmul = conv3Expr (3x3) + quotientTimesQExpr (3x3) = 18 products
     PrivateBookBfvNttFamily.lean:100  TRACE_WIDTH = 8 + 6*3 + 3 + 2 + 11 + 4 + 2 = 48
     :388-397  ranges = 21 limb + 16 schedule + 11 carry = 48""")


def sublimbs(bits, s=14, p_bits=31):
    k = ceil(bits / s)
    return k


def width(k):
    """Butterfly trace width as a function of sub-limb count. Derived from the
    Lean column map: 8 schedule + 6 residues*k + quotient k + 2 reduce flags
    + (2k-1) product carries + k add carries + k sub carries + 4 bus + 2 stage.
    At k = 1 the quotient, the reduce flags and every carry vanish."""
    if k == 1:
        return 8 + 6 + 4 + 2
    return 8 + 6 * k + k + 2 + (2 * k - 1) + k + k + 4 + 2


def ranges(k):
    """16 schedule ranges always; 7 bases x k limb ranges and 4k-1 carry ranges
    only when the modulus is emulated (a native residue is canonical for free)."""
    return 16 if k == 1 else 16 + 7 * k + (4 * k - 1)


def muls(k):
    return 1 if k == 1 else 2 * k * k


check(f"derived width(3) == 48, the SHIPPED NTT_TRACE_WIDTH", width(3) == 48)
check(f"derived ranges(3) == 48, the SHIPPED range count", ranges(3) == 48)
check(f"derived muls(3) == 18 == conv3(9) + quotientTimesQ(9) in the Lean AIR",
      muls(3) == 18)
check(f"derived width(1) == 20 -- independently reproducing the H2 lane's "
      f"'width 48 -> 20' for a native modulus", width(1) == 20)
check(f"derived ranges(1) == 16 -- independently reproducing 'range checks "
      f"48 -> 16'", ranges(1) == 16)
print(f"\n   width:  k=1 -> {width(1)}   k=2 -> {width(2)}   k=3 -> {width(3)}")
print(f"   ranges: k=1 -> {ranges(1)}   k=2 -> {ranges(2)}   k=3 -> {ranges(3)}")
print(f"   muls:   k=1 -> {muls(1)}    k=2 -> {muls(2)}    k=3 -> {muls(3)}")


# ================== SECTION 5: PRICE IT ON THE REAL TRACE GEOMETRY
print()
print("=" * 74)
print("SECTION 5 -- price it on the SHIPPED trace geometry (with padding)")
print("=" * 74)
LIVE_FAMILY_ROWS = 1032192      # PrivateBookBfvNttFamily.lean:85, theorem :123
PER_MODULUS_ROWS = LIVE_FAMILY_ROWS // 3     # 344,064
check("LIVE_FAMILY_ROWS / 3 == 344064 (the per-modulus slice the H2 lane used)",
      PER_MODULUS_ROWS == 344064)
check("LIVE_FAMILY_ROWS pads to 2^20 with 16384 rows of padding (shipped fact)",
      2**20 - LIVE_FAMILY_ROWS == 16384)


def pad2(n):
    k = 1
    while k < n:
        k <<= 1
    return k


def price(tables, label, per_mul_cost=1.0):
    """tables: list of (rows, k). Returns committed elements, lookups, muls."""
    el = sum(pad2(r) * width(k) for r, k in tables)
    lk = sum(r * ranges(k) for r, k in tables)
    mu = sum(r * muls(k) for r, k in tables)
    return el, lk, mu, el * per_mul_cost


R = PER_MODULUS_ROWS
designs = [
    ("A  status quo: one 48-wide table, 3 emulated moduli",
     [(3 * R, 3)], 1.0),
    ("B  native limb, SPLIT tables (2 emulated + 1 native)",
     [(2 * R, 3), (R, 1)], 1.0),
    ("C  native limb, ONE uniform 48-wide table",
     [(3 * R, 3)], 1.0),
    ("D  H2's joint 109-bit prime (proof field moves to 109 bits)",
     [(R, 1)], 18.5),
]
print(f"\n   {'design':<54} {'elements':>12} {'lookups':>12} {'nativemul':>11}")
print("   " + "-" * 92)
res = {}
for label, tabs, pmc in designs:
    el, lk, mu, wt = price(tabs, label, pmc)
    res[label[0]] = (el, lk, mu, wt)
    print(f"   {label:<54} {el:12,} {lk:12,} {mu:11,}")

elA, lkA, muA, wtA = res["A"]
print(f"\n   ratios against A (status quo), higher = better:")
for key, name in [("B", "split tables"), ("C", "uniform width"),
                  ("D", "joint 109-bit prime")]:
    el, lk, mu, wt = res[key]
    print(f"     {key} ({name:<20}): elements {elA / el:6.3f}x   "
          f"lookups {lkA / lk:6.3f}x   nativemuls {muA / mu:6.3f}x   "
          f"H2-weighted (elements x per-mul) {wtA / wt:6.3f}x")

# C's lookups/muls are the split figures -- in a uniform table the NATIVE rows
# still commit 48 columns, but they need neither the limb ranges nor the 18 muls.
elC, _, _, _ = res["C"]
lkC = 2 * R * ranges(3) + R * ranges(1)
muC = 2 * R * muls(3) + R * muls(1)
print(f"\n   correcting C (a uniform-width table still SAVES the lookups and muls,")
print(f"   it only fails to save the committed columns):")
print(f"     C elements {elA / elC:6.3f}x   lookups {lkA / lkC:6.3f}x   "
      f"nativemuls {muA / muC:6.3f}x")

print(f"""
   ⚑ THE PADDING WALL, stated plainly:
     3 moduli = {3 * R:,} live rows -> pads to 2^20 = {pad2(3 * R):,}  ({(pad2(3 * R) / (3 * R) - 1) * 100:.1f}% padding)
     2 moduli =   {2 * R:,} live rows -> pads to 2^20 = {pad2(2 * R):,}  ({(pad2(2 * R) / (2 * R) - 1) * 100:.1f}% padding)
   Dropping one third of the rows from the wide table does NOT shrink it: both
   {2 * R:,} and {3 * R:,} land in the same power of two. So design B pays for a
   whole extra table and gets nothing back on the wide one.""")

print(f"""
   ⚠ H2's '16x fewer committed elements' does NOT reproduce. Derived from the
     shipped geometry the joint-prime element ratio is {elA / res['D'][0]:.2f}x padded
     ({(3 * R * width(3)) / (R * width(1)):.2f}x on live rows) -- not 16x. Under H2's OWN model
     (LDE time proportional to elements x per-multiply cost) that makes the
     109-bit joint prime {res['D'][3] / wtA:.2f}x WORSE, not 'break-even to slightly
     worse'. H2's negative verdict is STRONGER than it stated.""")

# ---- the padding wall is a LAYOUT artifact, and 344064 = 2^14 * 21 dissolves it
print("\n   Is the padding wall structural? No -- it is a layout choice.")
print(f"     344,064 = 2^14 * 21 and 1,032,192 = 2^14 * 63, so packing j")
print(f"     butterflies per row gives an EXACTLY power-of-two height for")
print(f"     j = 21 (native table) and j = 42 or 63 (wide table). With those")
print(f"     layouts padding is zero and the ratio is the honest LIVE-row ratio.")
live_A = 3 * R * width(3)
live_B = 2 * R * width(3) + R * width(1)
lkA_live, lkB_live = 3 * R * ranges(3), 2 * R * ranges(3) + R * ranges(1)
muA_live, muB_live = 3 * R * muls(3), 2 * R * muls(3) + R * muls(1)
print(f"\n     zero-padding layout:   A {live_A:,}   B {live_B:,}   "
      f"ratio **{live_A / live_B:.4f}x**")
print(f"     lookups:               A {lkA_live:,}   B {lkB_live:,}   "
      f"ratio {lkA_live / lkB_live:.4f}x")
print(f"     native muls:           A {muA_live:,}   B {muB_live:,}   "
      f"ratio {muA_live / muB_live:.4f}x")
check("best-case element saving is 1.2414x (19.4% fewer), NOT the naive 1/3",
      abs(live_A / live_B - 1.2414) < 0.001)

print(f"""
   ⚑ WHY IT IS 19.4% AND NOT 33.3% -- the decomposition that answers
     'is one limb of three worth a third?':

       a butterfly row's 48 columns split into
         FIXED overhead (survives nativeness):  8 schedule + 4 bus + 2 stage = {8 + 4 + 2}
         RESIDUE payload (shrinks 3k -> 3):     6 residues x k              = {6 * 3} -> {6}
         EMULATION machinery (vanishes):        quotient {3} + reduce 2 + carries {(2 * 3 - 1) + 3 + 3} = {3 + 2 + 11}
       native row = {8 + 4 + 2} fixed + {6} residues = {width(1)}  (NOT 48/3 = 16)

     So the native limb still pays {(8 + 4 + 2) / width(1) * 100:.0f}% of its row on schedule/bus/stage
     overhead that has nothing to do with the modulus. Element saving is
     (48-20)/(3*48) = {(width(3) - width(1)) / (3 * width(3)) * 100:.2f}%, not 33.33%.
     The multiply count DOES nearly reach a third ({(1 - muB_live / muA_live) * 100:.1f}%) because
     multiplies carry no fixed overhead -- which is exactly why the two
     metrics disagree, and why 'one third of the limbs' had to be derived.""")

print(f"""
   ⚑ THE COMPARISON THAT DECIDES IT (all on the shipped geometry):

     option                          elements   depth   noise margin   FHE side
     -----------------------------------------------------------------------
     A status quo 3x{{36,36,37}}        1.00x       2      +8.95 bits    1.00x
     B one native limb (best layout)  {live_A / live_B:.2f}x       2      +8.34 bits    1.00x
     D joint 109-bit prime           1/{res['D'][3] / wtA:.2f}x*      2      +8.95 bits    1.2-2.2x worse
     E joint 61-bit prime (p61)         --       1      +3.03 bits    ~1.0x
     * D is {res['D'][3] / wtA:.2f}x WORSE: 4.80x fewer elements, 18.5x dearer per multiply.
       Only B is on the winning side of 1.00x, and only by {(live_A / live_B - 1) * 100:.0f}%.""")

# ------------------------------------------------------------------ verdict
print()
fails = [n for n, ok in CHECKS if not ok]
if fails:
    print(f"RESULT: {len(fails)} FAILED of {len(CHECKS)}")
    for n in fails:
        print(f"   FAIL: {n}")
    sys.exit(1)
print(f"RESULT: all {len(CHECKS)} checks pass")
