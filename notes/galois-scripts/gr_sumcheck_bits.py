#!/usr/bin/env python3
"""gr_sumcheck_bits.py -- the arithmetic behind notes/galois-ring-stack.md.

Everything here is [DERIVED] from named inputs, or a brute-force [MEASURED] exhibit
at toy size. No number in the note comes from anywhere else.

  1. Extension degree r of GR(2^64, r) needed so that sumcheck soundness v*deg/2^r
     clears the 100- and 124-bit bars (Rinocchio 2021/322 Lemma 2 + Prop 1:
     Lenstra constant of GR(p^k, d) is p^d; CCKP19 Thm 2 shape v*d/|A|).
  2. Element-size / challenge-multiplication table vs BabyBear-Ext4, Binius, Z_Q-Ext4.
  3. Tightness exhibit: sampling from the WHOLE ring buys nothing (f = 2^(k-1)*x).
  4. x^alpha is not a permutation of Z/2^k (units bijective for odd alpha; non-units collide).
  5. Z_{2^k}[X]/(X^N+1) is local with residue field F_2: every exceptional set has size <= 2
     (brute force at k=3, N=4), so no invertible-difference challenge set exists.
  6. Smooth part of 2^d - 1: the largest odd-radix FFT-friendly Teichmuller subgroup for an
     RS/BaseFold-style fold that avoids dividing by 2 (side remark in the note, section 2).
  7. Negacyclic 64-bit product at N=4096: Karatsuba vs 3-prime CRT-NTT multiplication counts.
"""
import math
from itertools import product

# ---------------------------------------------------------------------------
# 1. r needed for the soundness bars.   eps = v*deg / 2^r  <=  2^-bar
#    => r >= bar + log2(v*deg).  Inputs: bars from notes/two-regime-calculator.md
#    (~124-bit repo bar; 100 as the lower bar named in the brief); work points:
#    (v=25, deg=3) = notes/zq-sumcheck.md section 2 worked point;
#    (v=16, deg=7) = a 2^16-row AIR with the alpha=7 S-box;
#    (v=24, deg=2) = 4096x4096 matmul sumcheck (log2(4096^2) rounds, product of two MLEs).
# ---------------------------------------------------------------------------
BARS = [100, 124]
POINTS = [("zq-sumcheck worked point", 25, 3), ("AIR deg-7, 2^16 rows", 16, 7),
          ("4096^2 matmul", 24, 2)]

def r_needed(bar, v, deg):
    return math.ceil(bar + math.log2(v * deg))

print("== 1. extension degree r of GR(2^64, r) for eps = v*deg/2^r <= 2^-bar ==")
print(f"{'point':28s} {'v':>3s} {'deg':>3s} {'v*deg':>6s} " + " ".join(f"r@{b}" for b in BARS)
      + "   challenge bytes (8r) @bars")
for name, v, d in POINTS:
    rs = [r_needed(b, v, d) for b in BARS]
    print(f"{name:28s} {v:3d} {d:3d} {v*d:6d} " + " ".join(f"{r:5d}" for r in rs)
          + "   " + " / ".join(f"{8*r}" for r in rs))
print("  (per-round error deg/2^r, rounds ADD (union bound); PCS/opening error not included)")

# ---------------------------------------------------------------------------
# 2. element sizes and challenge-multiplication cost
#    GR(2^64, r): witness 8 B; challenge 8r B; one challenge x challenge mult =
#      r^2 u64 mults schoolbook, ~r^1.585 Karatsuba, plus reduction mod the degree-r binomial.
#    BabyBear Ext4: 4 B / 16 B / 16 u32 mults (9 Karatsuba).   [deployed; notes/zq-sumcheck.md]
#    Binius GF(2^128): tower elt 1 bit..16 B / 16 B / 1 GF(2^128) mult (~4 PCLMUL + reduction).
#    Z_Q Ext4 (notes/zq-sumcheck.md section 6): 3 limbs ~ 14 B / 4*14 = 55 B / 16 Z_Q-mults = 48 limb-mults.
# ---------------------------------------------------------------------------
print("\n== 2. element sizes (bytes) and cost of one challenge*challenge multiplication ==")
rows = [("BabyBear + Ext4 (deployed)", 4, 16, "16 u32 (9 Karatsuba)", 124 - 0.4),
        ("Binius GF(2^128) challenges", 16, 16, "1 GF(2^128) (~4 PCLMUL)", 128),
        ("Z_Q (109-bit) + shared Ext4", 14, 55, "48 limb-mults (36/37-bit)", 144)]
for name, w, c, cost, bits in rows:
    print(f"  {name:32s} witness {w:3d} B  challenge {c:5d} B  mult: {cost:28s} |A| ~ 2^{bits:g}")
for bar in BARS:
    r = r_needed(bar, 25, 3)
    print(f"  GR(2^64, {r}) @ {bar}-bit bar        witness   8 B  challenge {8*r:5d} B  "
          f"mult: {r*r} u64 schoolbook / ~{round(r**1.585)} Karatsuba |A| = 2^{r}")
print("  soundness bits per challenge BIT: field 1.0; GR(2^64, r): r/(64 r) = 1/64 = 0.0156")

# ---------------------------------------------------------------------------
# 3. tightness: sampling from the whole ring GR(2^k,1) = Z/2^k, f(x) = 2^(k-1) x, deg 1,
#    vanishes on exactly half the ring = deg / 2^r with r = 1.  [MEASURED at k=8..12]
# ---------------------------------------------------------------------------
print("\n== 3. whole-ring sampling is no better: zeros of f(x) = 2^(k-1)*x over Z/2^k ==")
for k in (8, 10, 12):
    q = 1 << k
    zeros = sum(1 for x in range(q) if ((1 << (k - 1)) * x) % q == 0)
    print(f"  k={k:2d}: {zeros}/{q} = {zeros/q:.3f}  (deg/2^r with r=1 predicts 0.500)")

# ---------------------------------------------------------------------------
# 4. x^alpha on Z/2^k: image sizes on units and on the whole ring.  [MEASURED]
# ---------------------------------------------------------------------------
print("\n== 4. x -> x^alpha on Z/2^k: is it a permutation? ==")
for k in (8, 12):
    q = 1 << k
    units = [x for x in range(q) if x & 1]
    for a in (3, 5, 7):
        img_all = len({pow(x, a, q) for x in range(q)})
        img_units = len({pow(x, a, q) for x in units})
        print(f"  k={k:2d} alpha={a}: |image on units| = {img_units}/{len(units)}"
              f"  |image on ring| = {img_all}/{q}  -> permutation? {img_all == q}")
print("  (Rivest 2001: p(x) is a permutation polynomial mod 2^w iff a1 odd, a2+a4+... even, a3+a5+... even;"
      " e.g. x(2x+1) is one -- and every polynomial map on Z/2^k is a T-function; see hensel_preimage.py)")

# ---------------------------------------------------------------------------
# 5. Z_{2^k}[X]/(X^N+1) is LOCAL with residue field F_2 (X^N+1 = (X+1)^N mod 2):
#    u is a unit  <=>  u(1) is odd.  So any exceptional set injects into F_2: size <= 2.
#    Brute force at k=3, N=4 (4096 elements).  [MEASURED]
# ---------------------------------------------------------------------------
def negacyclic_mul(a, b, q, N):
    out = [0] * N
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            s = i + j
            if s < N:
                out[s] = (out[s] + ai * bj) % q
            else:
                out[s - N] = (out[s - N] - ai * bj) % q
    return out

print("\n== 5. Z_{2^k}[X]/(X^N+1): units and the exceptional-set bound (k=3, N=4) ==")
k, N = 3, 4
q = 1 << k
elts = list(product(range(q), repeat=N))
prods = {}
one = tuple([1] + [0] * (N - 1))
unit = set()
for a in elts:
    for b in elts:
        if tuple(negacyclic_mul(a, b, q, N)) == one:
            unit.add(a)
            break
pred = {a for a in elts if sum(a) % 2 == 1}
print(f"  |ring| = {len(elts)}, |units| = {len(unit)}, predicted by 'u(1) odd' = {len(pred)},"
      f" sets equal: {unit == pred}")
# any 3 elements: two share the parity of u(1); their difference is a non-unit.
bad = 0
for a, b, c in [(elts[0], elts[1], elts[5]), (elts[7], elts[100], elts[4095]), (elts[3], elts[9], elts[27])]:
    diffs = [tuple((x - y) % q for x, y in zip(u, v)) for u, v in ((a, b), (a, c), (b, c))]
    if all(d in unit for d in diffs):
        bad += 1
print(f"  3-element sets with all pairwise differences units, among samples: {bad} (pigeonhole on u(1) mod 2 forbids any)")
print("  => Lenstra constant of Z_{2^k}[X]/(X^N+1) is 2. Compare GR(2^k, r): 2^r (Rinocchio Prop 1);"
      " prime q splitting X^N+1 into tau factors: |F_q^{N/tau}| per factor (LaBRADOR/Greyhound [LS18]).")

# ---------------------------------------------------------------------------
# 6. Smooth part of 2^d - 1 (odd-radix fold domains inside the Teichmuller group of GR(2^k, d)).
# ---------------------------------------------------------------------------
print("\n== 6. smooth part of 2^d - 1 (radix <= 64): odd-radix FFT-friendly Teichmuller subgroup ==")
try:
    from sympy import factorint
    for d in (32, 36, 40, 48, 60, 64):
        f = factorint((1 << d) - 1)
        smooth = 1
        for p, e in f.items():
            if p <= 64:
                smooth *= p ** e
        print(f"  d={d:2d}: 2^d-1 = {' * '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in f.items())}"
              f"  smooth(<=64) part = {smooth} ~ 2^{math.log2(smooth):.1f}")
except ImportError:
    print("  sympy unavailable; skipped")

# ---------------------------------------------------------------------------
# 7. 64-bit negacyclic product at N = 4096: multiplication counts.
#    Karatsuba to depth 12: 3^12 word mults (64x64->128).  CRT-NTT over 3 primes (~50 bits,
#    covering 128 + 12 bits of product magnitude): per prime 3 NTTs of N/2 log2 N butterflies
#    + N pointwise.  Saber 2018/230 and 2021/995 for the measured N=256 ratio.
# ---------------------------------------------------------------------------
print("\n== 7. negacyclic 64-bit product, N=4096: multiplication counts ==")
Nn = 4096
kar = 3 ** 12
ntt = 3 * (3 * (Nn // 2) * 12 + Nn)
print(f"  Karatsuba (full depth): {kar:,} 64x64->128 mults;  3-prime CRT-NTT: {ntt:,} ~50-bit modmults"
      f"  ratio {kar/ntt:.2f}x (plus Karatsuba's ~6.5*3^12 = {round(6.5*kar):,} 128-bit adds)")
g = 16 ** 0.585 / 1.5
print(f"  measured anchor [READ] eprint 2021/995 abstract: NTT-based Saber is 33%-41% faster than Toom-Cook at N=256, 13-bit;"
      f" the gap grows as N^0.585/log N, i.e. x(16^0.585/1.5) = {g:.1f} at N=4096 => ~{1.33*g:.1f}x-{1.41*g:.1f}x")
