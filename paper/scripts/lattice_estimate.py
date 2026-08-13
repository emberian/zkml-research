#!/usr/bin/env python3
"""lattice_estimate.py — primal-uSVP lattice estimate, VALIDATED FIRST.

REVIVAL lane, 2026-08-13. Written for the KoalaBear-limb question but usable
for any (n, q, sigma). Nothing is quoted about a candidate until the estimator
reproduces Kyber-768 (beta = 623) and Kyber-1024 (beta = 873).

Method: primal uSVP with the 2016 estimate (Alkim-Ducas-Poeppelmann-Schwabe),
GSA basis profile, normal-form LWE (secret and error from the same
distribution -- which is EXACTLY our case: fhe-dregg samples both from
sample_vec_cbd(., variance) with variance = 10).

Success condition for BKZ-beta on the Kannan embedding of dimension d = m+n+1
with volume q^m:

    sqrt(beta) * sigma  <=  delta(beta)^(2*beta - d - 1) * q^(m/d)

    delta(beta) = ( (pi*beta)^(1/beta) * beta / (2*pi*e) )^(1/(2*(beta-1)))

Cost models reported:
  core-SVP classical   2^(0.292 * beta)          [ADPS16, the conservative one]
  core-SVP quantum     2^(0.265 * beta)
  gate count           2^(0.292*beta + 16.4 + log2(8d))   [Albrecht et al.]
  MATZOV sieve         2^(0.29613*beta + 20.387)          [MATZOV 2022]

Pure python3 stdlib. Run: python3 lattice_estimate.py
"""

import sys
from math import log2, sqrt, pi, e, log

CHECKS = []


def check(name, cond, note=""):
    CHECKS.append((name, bool(cond)))
    print(f"[{'PASS' if cond else 'FAIL'}] {name}" + (f"   {note}" if note else ""))


def delta(beta):
    return ((pi * beta) ** (1.0 / beta) * beta / (2 * pi * e)) ** (1.0 / (2 * (beta - 1)))


def primal_usvp(n, log2_q, sigma, m_max=None, beta_hi=2000):
    """Smallest beta for which primal uSVP succeeds, optimising over m.

    Returns (beta, m, d). log2_q avoids overflow at 100+ bit moduli --
    everything is done in logs.
    """
    if m_max is None:
        m_max = 4 * n
    best = None
    lo, hi = 40, beta_hi
    # monotone in beta for fixed m, so bisect on "exists m that works"
    def works(beta):
        dl = log2(delta(beta))
        lhs = 0.5 * log2(beta) + log2(sigma)
        # scan m; the optimum is smooth, step coarse then refine
        step = max(1, n // 64)
        bm, bv = None, None
        m = max(1, n // 4)
        while m <= m_max:
            d = m + n + 1
            rhs = (2 * beta - d - 1) * dl + (m / d) * log2_q
            if bv is None or rhs > bv:
                bv, bm = rhs, m
            m += step
        # refine around bm
        for m in range(max(1, bm - step), min(m_max, bm + step) + 1):
            d = m + n + 1
            rhs = (2 * beta - d - 1) * dl + (m / d) * log2_q
            if rhs > bv:
                bv, bm = rhs, m
        return (lhs <= bv), bm

    if not works(hi)[0]:
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        ok, _ = works(mid)
        if ok:
            hi = mid
        else:
            lo = mid + 1
    _, m = works(lo)
    return lo, m, m + n + 1


def costs(beta, d):
    return {
        "core_svp_c": 0.292 * beta,
        "core_svp_q": 0.265 * beta,
        "gate": 0.292 * beta + 16.4 + log2(8 * d),
        "matzov": 0.29613 * beta + 20.387,
    }


def report(label, n, log2_q, sigma, m_max=None):
    r = primal_usvp(n, log2_q, sigma, m_max=m_max)
    if r is None:
        print(f"   {label:<34} NO beta below the cap (instance is very hard)")
        return None
    beta, m, d = r
    c = costs(beta, d)
    print(f"   {label:<34} beta={beta:5d}  m={m:5d}  d={d:5d}  "
          f"coreSVP-C={c['core_svp_c']:6.1f}  Q={c['core_svp_q']:6.1f}  "
          f"gate={c['gate']:6.1f}  MATZOV={c['matzov']:6.1f}")
    return beta, c


# ============================================================== VALIDATION
print("=" * 96)
print("VALIDATION -- the estimator must reproduce Kyber before it is used on anything")
print("=" * 96)
print("   Kyber: module-LWE, n = 256*k, q = 3329, secret and error CBD(eta),")
print("   sigma = sqrt(eta/2). Published round-3 core-SVP beta: 512->406, 768->623, 1024->873.")
print("   Samples available from the public key: m = n (k*256).\n")

kyber = {
    "Kyber-512  (k=2, eta=3)": (512, 3329, sqrt(3 / 2), 512, 406),
    "Kyber-768  (k=3, eta=2)": (768, 3329, sqrt(2 / 2), 768, 623),
    "Kyber-1024 (k=4, eta=2)": (1024, 3329, sqrt(2 / 2), 1024, 873),
}
val_ok = True
for label, (n, q, s, mm, target) in kyber.items():
    r = primal_usvp(n, log2(q), s, m_max=mm)
    beta, m, d = r
    dev = abs(beta - target)
    print(f"   {label:<26} computed beta = {beta:4d}   published {target:4d}   "
          f"delta {beta - target:+4d}   coreSVP-C = {0.292 * beta:6.1f}")
    if dev > 0.02 * target:
        val_ok = False

check("estimator reproduces all three published Kyber betas within 2%", val_ok)
check("Kyber-768 within 2% of 623",
      abs(primal_usvp(768, log2(3329), 1.0, m_max=768)[0] - 623) <= 13)
check("Kyber-1024 within 2% of 873",
      abs(primal_usvp(1024, log2(3329), 1.0, m_max=1024)[0] - 873) <= 18)

if not val_ok:
    print("\n   ESTIMATOR NOT VALIDATED -- refusing to quote candidate numbers.")
    sys.exit(1)

# ================================================== THE DEPLOYED INSTANCE
print()
print("=" * 96)
print("THE SHIPPED SECRET -- pinned at source, not relayed")
print("=" * 96)
print("""   vendor/fhe-dregg/src/bfv/parameters.rs:272   variance: 10   (the default,
     range-checked to [1,16] by fhe_util::sample_vec_cbd)
   vendor/fhe-dregg/src/bfv/keys/secret_key.rs:43   s <- sample_vec_cbd(N, variance)
   vendor/fhe-dregg/src/bfv/keys/secret_key.rs:125  e <- Poly::small(.., variance)
   fhe_util::sample_vec_cbd: number_bits = 4*variance; two 2*variance-bit
     popcounts differenced  =>  CBD(eta) with eta = 2*variance = 20,
     support +/-20, VARIANCE = 10, sigma = sqrt(10) = 3.1623.
   secret_key.rs:288 asserts |c_i| <= 2*variance = 20 -- the support, in a test.
   => BOTH secret and error are CBD(20). This is NORMAL-FORM LWE, and it is
      NOT ternary (support +/-1) and NOT CBD(10) (support +/-10). Both earlier
      labels in our notes were wrong.""")

SIGMA = sqrt(10.0)
NRING = 4096
print(f"\n   sigma = sqrt(10) = {SIGMA:.4f}   (HE-standard reference sigma is 3.19 -- "
      f"ours is {SIGMA:.4f}, essentially the same)")

print("\n" + "=" * 96)
print("CANDIDATE INSTANCES at N=4096, CBD(20) both sides, m unbounded (many ciphertexts)")
print("=" * 96)
FOLD = [0xffffee001, 0xffffc4001, 0x1ffffe0001]
LOG2Q_DEPLOYED = sum(log2(x) for x in FOLD)
print(f"   deployed FOLD_MODULI product: log2 Q = {LOG2Q_DEPLOYED:.6f}\n")

rows = []
rows.append(report(f"deployed  log2 Q = {LOG2Q_DEPLOYED:.2f}", NRING, LOG2Q_DEPLOYED, SIGMA))
for lq in [105.0, 105.57, 107.0, 109.0, 110.0, 112.0]:
    rows.append(report(f"KB tower  log2 Q = {lq:.2f}", NRING, lq, SIGMA))
print()
rows.append(report("p61 single log2 Q = 61.00", NRING, log2(2**61 - 2**54 + 1), SIGMA))
rows.append(report("ternary-secret control (sigma=0.816)", NRING, LOG2Q_DEPLOYED,
                   sqrt(2 / 3)))

print("\n   Sensitivity: security is monotone DECREASING in log2 Q at fixed N.")
print("   Every KB tower in the 105-112 band therefore brackets the deployed")
print("   instance; the 105.57 example is STRICTLY MORE SECURE than deployed.")

print()
fails = [n for n, ok in CHECKS if not ok]
if fails:
    print(f"RESULT: {len(fails)} FAILED of {len(CHECKS)}")
    sys.exit(1)
print(f"RESULT: all {len(CHECKS)} validation checks pass")
