#!/usr/bin/env python3
"""GSR (eprint 2026/1692) complexity calculator, reproduced against the paper's
Table 1 then instantiated at our BabyBear Poseidon2 parameters."""
from math import log2

def lg(x):
    return log2(x)

def gsr(t, alpha, p_bits, k, Rf0, Rp, Rf1, label=""):
    """Return (rounds_attacked, skipped_partial, d_opt, time_bits, mem_bits)."""
    # GSR absorbs Rf0=1 full round + min(Rp, t-2k) partial rounds.
    skip = min(Rp, t - 2*k)
    if skip < 0:
        skip = 0
    unskipped_partial = Rp - skip
    # degree growth activates over unskipped partial + final full rounds
    growth_rounds = unskipped_partial + Rf1
    d = alpha ** growth_rounds
    # SyCZ: nest Sylvester resultants k-1 times -> degree d^(2^(k-1));
    # Cantor-Zassenhaus root find: time O(D^2 log p), mem O(D log p) with D = d^(2^(k-1))
    D = d ** (2 ** (k - 1))
    time_bits = 2 * lg(D) + lg(p_bits)
    mem_bits = lg(D) + lg(p_bits)
    rounds = Rf0 + Rp + Rf1
    return dict(label=label, t=t, alpha=alpha, k=k, rounds=rounds,
                skip=skip, unskipped=unskipped_partial, growth=growth_rounds,
                d=d, d_bits=lg(d), D_bits=lg(D),
                time=time_bits, mem=mem_bits, brute=p_bits_bits(p_bits)*k)

def p_bits_bits(p_bits):
    return p_bits

print("=" * 78)
print("VALIDATION against paper Table 1 (KoalaBear p=2130706433~2^31, t=24, a=3)")
print("=" * 78)
KB = 31
for (k, Rf0, Rp, Rf1, exp_t, exp_m) in [
    (1, 1, 23, 4, 20.8, 12.9),
    (2, 1, 23, 4, 49.3, 27.1),
    (2, 1, 20, 4, 30.3, 17.6),
    (3, 1, 18, 4, 55.7, 30.3),
    (4, 1, 16, 4, 106.4, 55.7),
]:
    r = gsr(24, 3, KB, k, Rf0, Rp, Rf1)
    print(f"  CICO-{k} ({Rf0},{Rp},{Rf1})={r['rounds']:>2}r  skip={r['skip']:>2} "
          f"unskipped={r['unskipped']} growth={r['growth']}  d=3^{r['growth']}={r['d']}  "
          f"time=2^{r['time']:.1f} (paper 2^{exp_t})  mem=2^{r['mem']:.1f} (paper 2^{exp_m})")

print()
print("=" * 78)
print("OUR INSTANCE: BabyBear p=2013265921~2^31, Poseidon2, t=16, alpha=7")
print("=" * 78)
BB = 31
for RP in [13, 20, 21, 22]:
    print(f"\n--- hypothesis RP = {RP} (RF=8 => total rounds = {8+RP}) ---")
    for k in [1, 2, 3]:
        # full-spec Rf1 = 4
        r = gsr(16, 7, BB, k, 1, RP, 4)
        brute = 31 * k
        verdict = "FEASIBLE" if r['time'] < brute else "no gain"
        print(f"  CICO-{k}: GSR reaches (1,{RP},4) = {r['rounds']} of {8+RP} rounds | "
              f"skip {r['skip']}/{RP} partial | residual growth {r['growth']} rounds | "
              f"d=7^{r['growth']}=2^{r['d_bits']:.1f} | time=2^{r['time']:.1f} "
              f"mem=2^{r['mem']:.1f} | brute=2^{brute} -> {verdict}")
        # attacker may also reduce Rp to lower d (round-reduced target)
        best = None
        for Rp2 in range(0, RP + 1):
            rr = gsr(16, 7, BB, k, 1, Rp2, 4)
            if rr['time'] < brute:
                if best is None or rr['rounds'] > best['rounds']:
                    best = rr
        if best:
            print(f"           deepest round-reduced target beaten: "
                  f"(1,{best['rounds']-5},4) = {best['rounds']} rounds at 2^{best['time']:.1f}")
