"""
THE tau=1 vs tau=4 FORK, priced in one metric  --  revival lane, 2026-08-13.

The cryptanalysis lane's handoff says "keep tau=1 (load-bearing; tau>1 reopens
the extension-field S-box question)".  The design lane's branch-number closure
happens at tau=4.  Nobody had put the two on one axis.  This does the COST half;
the security half is prose (see notes/ring-hash-design.md Sec. 4).

Metric: rows in 2026/1127's R1CS-over-R_q-with-automorphisms accounting, per
ABSORBED RING ELEMENT, exactly as costmodel.py / design_mds_interleave.py (D).
Baseline to beat: 716.8 rows/elt, the paper's own App C.3 decompose-and-hash
(Poseidon over Z_q with ring elements split into d=16 coefficients).

  rows/perm = S_alpha*(RF*t + RP)  +  sum over rounds of (sigma rows/elt) * t
  rows/elt  = rows/perm / rate

The ONLY thing tau changes in this model is HOW MANY sigma rows buy slot-MDS:
  tau=1: ell = 16 slots, slot-MDS needs the dense group layer  = 8 rows/elt/round
  tau=4: ell =  4 slots, slot-MDS needs {1,5,-1,-5}           = 2 rows/elt/round
Element SIZE, S-box cost and round counts are tau-independent (x^7 is 4 R_q
mults either way), so this isolates the fork.

The sigma cost law (from Def. 9's two automorphism channels per row) is
    support s  costs  ceil((s-1)/2) rows/elt/round,
so at tau=1 full support d=16 costs 8, and at tau=4 full slot-support 4 costs 2.
"""
from math import ceil

RF, RP, ALPHA, S_ALPHA = 8, 22, 7, 4
T_RING, RATE = 9, 8
ROUNDS = RF + RP
BASELINE = 716.8
SBOX = S_ALPHA * (RF * T_RING + RP)

def cost(sigma_rows_full, sigma_rows_partial, n_full=RF, n_partial=RP):
    rows = SBOX + (sigma_rows_full * n_full + sigma_rows_partial * n_partial) * T_RING
    return rows, rows / RATE

def row(label, sf, sp, branch, nf=RF, np_=RP):
    r, pe = cost(sf, sp, nf, np_)
    print(f"  {label:<46} {r:>6}  {pe:>7.1f}  {BASELINE/pe:>6.1f}x   {branch}")

print("=" * 96)
print(f"S-box floor = S_a*(RF*t+RP) = {S_ALPHA}*({RF}*{T_RING}+{RP}) = {SBOX} rows/perm "
      f"= {SBOX/RATE:.1f}/elt  ({BASELINE/(SBOX/RATE):.1f}x baseline, sigma-free)")
print("=" * 96)
print(f"  {'schedule':<46} {'rows':>6}  {'per elt':>7}  {'vs 716.8':>7}   branch delivered")
print("-" * 96)
print("  tau=1  (ell=16 slots over F_q; well-studied prime-field S-box)")
row("support-3 every round        (1 row)", 1, 1, "4 of 17 -- the recorded #1 weakness")
row("support-9 in full, support-3 in partial", 4, 1, "10 of 17 in full rounds")
row("dense in 4 outer full rounds only", 8, 1, "17 in 4 rounds, 4 elsewhere", nf=4, np_=ROUNDS-4)
row("dense in ALL full rounds     (8 rows)", 8, 1, "17 = SLOT-MDS in every full round")
row("dense every round            (8 rows)", 8, 8, "17 = SLOT-MDS in every round")
print("-" * 96)
print("  tau=2  (ell=8 slots over F_q^2; slot-MDS needs full support 8 = ceil(7/2) = 4 rows)")
row("support-3 every round        (1 row)", 1, 1, "4 of 9")
row("slot-MDS in full, support-3 in partial", 4, 1, "9 = SLOT-MDS in every full round")
row("slot-MDS every round         (4 rows)", 4, 4, "9 = SLOT-MDS in every round")
print("-" * 96)
print("  tau=4  (ell=4 slots over F_q^4; DEPLOYED Frog ring; extension-field S-box)")
row("support-3 every round        (1 row)", 1, 1, "4 of 5")
row("slot-MDS in full, support-3 in partial", 2, 1, "5 = SLOT-MDS in every full round")
row("slot-MDS every round         (2 rows)", 2, 2, "5 = SLOT-MDS in every round")
print("-" * 96)

_, mds_all_1 = cost(8, 8)
_, mds_all_4 = cost(2, 2)
_, mds_full_1 = cost(8, 1)
_, mds_full_4 = cost(2, 1)
print(f"""
  THE FORK, in one number each way:
    slot-MDS in EVERY round     tau=1 {mds_all_1:.1f}/elt  vs  tau=4 {mds_all_4:.1f}/elt   -> tau=4 is {mds_all_1/mds_all_4:.2f}x cheaper
    slot-MDS in FULL rounds     tau=1 {mds_full_1:.1f}/elt  vs  tau=4 {mds_full_4:.1f}/elt   -> tau=4 is {mds_full_1/mds_full_4:.2f}x cheaper

  and the comparison that actually decides it -- what does the SAME BUDGET buy?
    at ~{mds_full_4:.0f} rows/elt:  tau=4 buys SLOT-MDS in every full round;
                       tau=1 buys support-3 only (branch 4 of 17), i.e. the
                       recorded #1 weakness, un-fixed.
    to reach slot-MDS at tau=1 you pay {mds_full_1:.1f}/elt, which is {mds_full_1/mds_full_4:.2f}x the tau=4
    price and lands at {BASELINE/mds_full_1:.1f}x the decompose-and-hash baseline instead of {BASELINE/mds_full_4:.1f}x.

  (the round-count caveat on these numbers is printed at the end)""")

# ---------------------------------------------------------------- C1 at tau > 1
# The S-box x^alpha permutes R_q iff it permutes each slot field F_(q^tau), i.e.
# iff gcd(alpha, q^tau - 1) = 1.  This is STRICTLY HARDER at tau=4 than tau=1 and
# nobody had checked it against the two moduli the two candidates want.
from math import gcd

print()
print("=" * 96)
print("C1 -- does the S-box still PERMUTE at tau>1?   gcd(alpha, q^tau - 1) = 1")
print("=" * 96)
Q_FROG = 15912092521325583641
Q_GF = (1 << 64) - 59          # the modulus the gadget-Feistel REQUIRES (tiny gamma)
for name, q in [("deployed Frog", Q_FROG), ("2^64-59 (gadget-friendly)", Q_GF)]:
    print(f"  {name}   (q mod 7 = {q % 7})")
    for tau in (1, 2, 4):
        n = q ** tau - 1
        legal = [a for a in range(3, 40, 2) if gcd(a, n) == 1]
        verdict = "OK" if gcd(ALPHA, n) == 1 else "** ILLEGAL **"
        print(f"    tau={tau}:  gcd(7, q^tau-1) = {gcd(ALPHA, n)}   alpha=7 {verdict:<14}"
              f" smallest legal alpha = {legal[0]:>2}  ({len(bin(legal[0]))-2 + bin(legal[0]).count('1')-2} mults)")

d1 = [r for r in range(1, 7) if (r - 1) % 7 == 0]
d4 = [r for r in range(1, 7) if (r ** 4 - 1) % 7 == 0]
print(f"""
  DENSITY: 7 | q^tau - 1  iff  ord_7(q) | tau.  (Z/7)^* is cyclic of order 6, so
    tau=1: q = 1 mod 7            -> {len(d1)}/6 = {len(d1)/6:.0%} of primes exclude alpha=7
    tau=4: q = 1 or 6 mod 7       -> {len(d4)}/6 = {len(d4)/6:.0%} of primes exclude alpha=7
  So C1 is twice as constraining at tau=4.  Not fatal -- but it is a real
  modulus-selection constraint, and it COLLIDES with the other candidate:

  ** THE TWO CANDIDATES WANT INCOMPATIBLE MODULI. **
    the gadget-Feistel REQUIRES tiny gamma = 2^64 - q, which 2^64-59 gives and
    Frog does not (Frog: gamma/q = 0.159, broken by default);
    but 2^64-59 = 6 mod 7, so 7 | q+1 | q^4-1, and alpha=7 is ILLEGAL there at
    tau=4 -- sigma-Poseidon would need alpha=13 (5 mults, +25% S-box cost).
    Meanwhile the deployed Frog modulus is 2 mod 7 and takes alpha=7 at every
    tau -- it is fine for sigma-Poseidon and fatal for the Feistel.
  Neither script had checked C1 against the OTHER candidate's modulus.  But the
  collision is a property of the two moduli NAMED so far, not of the design --
  so rather than file it, search for a modulus that serves both:""")

# ---------------------------------------------------------------- joint modulus
import sympy
TOP = 1 << 64
print("=" * 96)
print("JOINT MODULUS SEARCH: tiny gamma (Feistel) AND ord_32(q)=4 (tau=4) AND gcd(7,q^4-1)=1")
print("=" * 96)
found, g = [], 1
while len(found) < 5 and g < 200_000:
    q = TOP - g
    if q % 2 and sympy.isprime(q):
        o = next((k for k in range(1, 17) if pow(q, k, 32) == 1), None)
        if o == 4 and gcd(ALPHA, q ** 4 - 1) == 1:
            found.append((g, q))
    g += 1
from math import log2
for g, q in found:
    print(f"  gamma={g:>6}  q = {q}   q mod 32 = {q%32:>2}  q mod 7 = {q%7}"
          f"   gamma/q = 2^{log2(g/q):.1f}   E[ambiguous coeffs/elt] = {16*g/q:.2g}")
g0, q0 = found[0]
print(f"""
  ** THE COLLISION IS RESOLVABLE, and cheaply: q = 2^64 - {g0}. **
    ord_32 = 4, so X^16+1 splits into 4 quartics -> tau=4, ell=4 slots, the
      branch closure of Sec. 1.2 applies;
    q = {q0 % 7} mod 7, so gcd(7, q^4-1) = 1 -> alpha=7 stays legal (4 mults);
    gamma = {g0}, so gamma/q = 2^{log2(g0/q0):.1f} -> the Feistel's decomposition is
      unambiguous except with probability ~2^{log2(16*g0/q0):.0f} per element.
  Grinding one ambiguous coefficient costs ~2^{-log2(16*g0/q0):.0f} here against ~2^54 at 2^64-59
  -- the same regime, two bits worse, in exchange for tau=4 AND a legal alpha=7.
  ⚠ the exact ROM accounting for that residual is the folding scheme's to state,
    not settled here; what is settled is that no modulus TRADEOFF is forced.""")

print(f"""
  ROUND-COUNT CAVEAT on the cost table above -- what is NOT modelled: round
  counts are held at RF=8/RP=22 for both regimes, and
  those are BORROWED (a width-~12 prime-field Poseidon set), not derived for
  either regime.  If the extension-field S-box at tau=4 needs more rounds -- and
  nothing rules that out -- the advantage shrinks proportionally.  At tau=4 the
  break-even is RP = {((mds_full_1*RATE - SBOX)/T_RING - 2*RF) / 1:.0f} partial rounds against tau=1's 22, i.e. tau=4 stays
  ahead until it needs ~{(((mds_full_1*RATE - SBOX)/T_RING - 2*RF))/RP:.1f}x the partial rounds of tau=1.""")
