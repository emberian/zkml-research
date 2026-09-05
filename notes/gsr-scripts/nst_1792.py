#!/usr/bin/env python3
"""eprint 2026/1792 (Li-Liu-Wang, "Beyond Linear Subspace Trails") cost model,
reproduced against the paper's Table C.1 / C.2 first, then evaluated at our
deployed BabyBear Poseidon2 (t=16, alpha=7, R_F=8, R_P=13 and 20) for
  * the Merkle internal node  TruncatedPermutation<Perm16,2,8,16>  (compression, c=0, d=8)
  * the leaf sponge           PaddingFreeSponge<Perm16,16,8,8>     (sponge, c=8, d=8)

Everything is the paper's own formulas (Sect. 2.3, 4.1, 4.2; Tables C.1, C.2):
  Macaulay bound   d_reg = 1 + sum(delta_i - 1)
  C_GB   = binom(sum(delta_i) + 1, n)^omega           omega = 2 in all their tables
  C_FGLM = n * D_I^omega, D_I <= prod(delta_i)         omega = 3 in Table C.1
  C_Graeffe(delta) = delta log delta (log p - log delta + 1) log log delta   (d = 1)
  digest-side degrees are capped at p - 2 (their Sect. 4.1 (6), following GKR25)
  round number = min r_P (>= the model's trail floor) with cost >= 2^128.
No dependency on anything else in the campaign.  Run:  python3 nst_1792.py
"""
from math import comb, log2, ceil, log

KAPPA = 128


def lg(x):
    return log2(x)


def cap(deg, p):
    """Sect. 4.1 (6): 'if the digest side equations reach degree p-2 ... estimate their degree as p-2'."""
    return min(deg, p - 2)


def gb_bits(sum_deg, n, omega):
    """log2 of binom(sum_deg + 1, n)^omega  (= binom(d_reg + n, n)^omega)."""
    return omega * lg(comb(sum_deg + 1, n))


def fglm_bits(logD, n, omega=3):
    return lg(n) + omega * logD


def graeffe_bits(delta, p):
    ld = lg(delta)
    return ld + lg(ld) + lg(lg(p) - ld + 1) + lg(lg(ld))


def res_bits(dx, dy):
    """C_RES(dx,dy) = dy * M(dx dy) log(dx dy), M(D) = D log D loglog D."""
    D = dx * dy
    return lg(dy) + lg(D) + lg(lg(D)) + lg(lg(lg(D))) + lg(lg(D))


# --------------------------------------------------------------------------
# The five Poseidon/Poseidon2 models of Sect. 4.1.  All return a dict with the
# bits and every intermediate.  Sponge: r = t - c, Ec = t - c - d.  Compression
# is the same formulas with c = 0 (Sect. 4.1: "In compression mode, Ec = t - d").
# --------------------------------------------------------------------------
def model1_basic(t, c, d, alpha, rF, rP, p, omega=2):
    """(1) Basic attack: d equations of degree alpha^(rF+rP); r variables, of which
    r - d are fixed so the system is square (their Table C.2 'basic attack' rows
    only reproduce with n = d)."""
    n = d
    deg = cap(alpha ** (rF + rP), p)
    if d == 1:
        bits = graeffe_bits(deg, p)
        how = "Graeffe"
    elif d == 2:
        bits = res_bits(deg, deg)
        how = "resultant"
    else:
        bits = gb_bits(d * deg, n, omega)
        how = "GB"
    return dict(model="1 basic", n=n, deg_digest=deg, sum_deg=d * deg,
                logD=d * lg(deg), bits=bits, how=how, tau=None, Ec_used=0,
                unabsorbed=rP, capped=(alpha ** (rF + rP) > p - 2))


def _trail_exponent(rf2, rP, tau, Ec_used, factor):
    """Digest-side exponent after a trail using Ec_used constraints.
    factor = 1 (linear trail, covers Ec_used rounds, degree 1 at its end)
    factor = 2 (nonlinear trail, covers 2*Ec_used+1 rounds, degree alpha at its end).
    Returns (exponent, unabsorbed partial rounds)."""
    if Ec_used == 0:
        return rf2 + (rP - tau), rP - tau
    if factor == 1:
        rem = rP - tau - Ec_used
        return rf2 + max(rem, 0), max(rem, 0)
    rem = rP - tau - 2 * Ec_used          # paper: alpha^(rf' + rP - tau - 2Ec), valid for rem >= 1
    return rf2 + max(rem, 1), max(rem - 1, 0)


def model3_sub(t, c, d, alpha, rf, rf2, rP, p, omega=2, nonlinear=True,
               literal=True, fglm_omega=3):
    """(2)/(3) Forward + substitution + linear/nonlinear subspace.
    literal=True : the paper's formula, full Ec, tau in [0, rP - floor]; if rP is
                   below the floor the tau range is EMPTY and we report the flat
                   extension at tau = 0 (flagged 'below_floor').
    literal=False: attacker-optimal within the family -- Ec' <= Ec constraints,
                   the unused Ec - Ec' degrees of freedom fixed (fewer variables)."""
    Ec = t - c - d
    factor = 2 if nonlinear else 1
    floor = (2 * Ec + 1) if nonlinear else Ec
    best = None
    Ec_choices = [Ec] if literal else range(0, Ec + 1)
    for Ecu in Ec_choices:
        if literal:
            taus = range(0, max(rP - floor, 0) + 1) if rP >= floor else [0]
        else:
            taus = range(0, rP + 1)
        n = (t + d + Ec) - (Ec - Ecu) if nonlinear else (t + d)
        # nonlinear: variables r + t = 2t - c, equations t + Ec + d; linear: t + d
        if not nonlinear and not literal:
            n = t + d
        for tau in taus:
            e_dig, unab = _trail_exponent(rf2, rP, tau, Ecu, factor)
            deg_sub = alpha ** (rf + tau)
            deg_dig = cap(alpha ** e_dig, p)
            sum_deg = t * deg_sub + d * deg_dig + (Ecu * alpha if nonlinear else 0)
            logD = t * lg(deg_sub) + d * lg(deg_dig) + (Ecu * lg(alpha) if nonlinear else 0)
            bits = gb_bits(sum_deg, n, omega)
            r = dict(model=("3 sub+nonlin" if nonlinear else "2 sub+lin"), n=n, tau=tau,
                     Ec=Ec, Ec_used=Ecu, floor=floor, below_floor=(rP < floor),
                     deg_sub=deg_sub, deg_dig=deg_dig, e_dig=e_dig, unabsorbed=unab,
                     sum_deg=sum_deg, dreg=sum_deg - n + 1, logD=logD, bits=bits,
                     fglm=fglm_bits(logD, n, fglm_omega), capped=(alpha ** e_dig > p - 2))
            if best is None or bits < best["bits"]:
                best = r
    return best


def model5_nonsub(t, c, d, alpha, rf, rf2, rP, p, omega=2, nonlinear=True, literal=True,
                  fglm_omega=3):
    """(4)/(5) Forward + no substitution + linear/nonlinear subspace, tau = 0.
    Variables r = t - c; equations Ec (degree alpha^rf, or alpha^(rf+1) nonlinear) + d."""
    Ec = t - c - d
    rF = rf + rf2
    factor = 2 if nonlinear else 1
    floor = (2 * Ec + 1) if nonlinear else Ec
    best = None
    for Ecu in ([Ec] if literal else range(0, Ec + 1)):
        n = (t - c) - (Ec - Ecu)
        e_dig, unab = _trail_exponent(rf2, rP, 0, Ecu, factor)
        e_dig += rf                                   # no substitution: the rf front rounds stay in
        deg_con = alpha ** (rf + 1) if nonlinear else alpha ** rf
        deg_dig = cap(alpha ** e_dig, p)
        sum_deg = Ecu * deg_con + d * deg_dig
        logD = Ecu * lg(deg_con) + d * lg(deg_dig)
        bits = gb_bits(sum_deg, n, omega)
        r = dict(model=("5 nonsub+nonlin" if nonlinear else "4 nonsub+lin"), n=n, tau=0,
                 Ec=Ec, Ec_used=Ecu, floor=floor, below_floor=(rP < floor), deg_con=deg_con,
                 deg_dig=deg_dig, e_dig=e_dig, unabsorbed=unab, sum_deg=sum_deg,
                 dreg=sum_deg - n + 1, logD=logD, bits=bits, fglm=fglm_bits(logD, n, fglm_omega),
                 capped=(alpha ** e_dig > p - 2))
        if best is None or bits < best["bits"]:
            best = r
    return best


def round_number(cost_fn, floor, rP_max=200, bar=KAPPA):
    """min rP >= floor with cost_fn(rP) >= 2^bar  (the paper's 'round number')."""
    for rP in range(max(floor, 0), rP_max):
        if cost_fn(rP) >= bar:
            return rP
    return None


def designers_rP(p_bits, t, alpha, rF, kappa=KAPPA):
    """Poseidon designers' interpolation term (Sect. 2.1); the r_GB term is not
    binding in any Table C.2 row.  Margin = ceil(1.075 * rP)."""
    base = 1 + ceil(min(kappa, p_bits) / lg(alpha)) + ceil(log(t, alpha)) - rF
    return base, ceil(1.075 * base)


# ==========================================================================
print("=" * 96)
print("REPRODUCTION 1: Table C.1 (Poseidon2 sponge, rF=6 -> rf=rf'=3, no margin;")
print("  entries C_GB(omega=2)/C_FGLM(omega=3): min rP >= 2Ec+1 with cost >= 2^128)")
print("=" * 96)
rows = [  # label, p_bits, c=d, alpha, t-range, printed entries (GB, FGLM)
    ("a", 64, 4, 3, range(12, 25, 2), {12: (9, 9), 14: (13, 13), 16: (17, 17), 18: (21, 21), 20: (25, 25), 22: (29, 29), 24: (33, 33)}),
    ("b", 96, 3, 3, range(8, 25, 2), {8: (5, 5), 10: (9, 9), 12: (13, 13), 14: (17, 17), 16: (21, 21), 18: (25, 25), 20: (29, 29), 22: (33, 33), 24: (37, 37)}),
    ("c", 128, 2, 3, range(8, 25, 2), {8: (9, 9), 10: (13, 13), 12: (17, 17), 14: (21, 21), 16: (25, 25), 18: (29, 29), 20: (33, 33), 22: (37, 37), 24: (41, 41)}),
    ("d", 256, 1, 3, range(4, 25, 2), {4: (10, 9), 6: (10, 10), 8: (13, 13), 10: (17, 17), 12: (21, 21), 14: (25, 25), 16: (29, 29), 18: (33, 33), 20: (37, 37), 22: (41, 41), 24: (45, 45)}),
    ("e", 256, 1, 5, range(4, 25, 2), {4: (6, 5), 6: (9, 9), 8: (13, 13), 10: (17, 17), 12: (21, 21), 14: (25, 25), 16: (29, 29), 18: (33, 33), 20: (37, 37), 22: (41, 41), 24: (45, 45)}),
    ("f", 256, 1, 7, range(4, 25, 2), {4: (5, 5), 6: (9, 9), 8: (13, 13), 10: (17, 17), 12: (21, 21), 14: (25, 25), 16: (29, 29), 18: (33, 33), 20: (37, 37), 22: (41, 41), 24: (45, 45)}),
]
ok = tot = 0
for label, pb, cd, alpha, ts, printed in rows:
    p = 2 ** pb
    line = f"  {label}: p~2^{pb:<3} c=d={cd} a={alpha} |"
    for t in ts:
        Ec = t - 2 * cd
        floor = 2 * Ec + 1
        gb = round_number(lambda rP: model3_sub(t, cd, cd, alpha, 3, 3, rP, p)["bits"], floor)
        fg = round_number(lambda rP: model3_sub(t, cd, cd, alpha, 3, 3, rP, p)["fglm"], floor)
        pg, pf = printed[t]
        mark = "" if (gb, fg) == (pg, pf) else " <-- MISMATCH"
        ok += (gb, fg) == (pg, pf)
        tot += 1
        line += f" t{t}:{gb}/{fg}(paper {pg}/{pf}){mark}"
    print(line)
print(f"  Table C.1 cells reproduced: {ok}/{tot}")

# how far above 2^128 the cost sits at the trail floor, per cell (the floor binds iff >= 128)
floor_costs = []
for label, pb, cd, alpha, ts, printed in rows:
    for t in ts:
        Ec = t - 2 * cd
        r = model3_sub(t, cd, cd, alpha, 3, 3, 2 * Ec + 1, 2 ** pb)
        floor_costs.append((r["bits"], label, t))
floor_costs.sort()
print("  Cost AT the trail floor rP = 2Ec+1, lowest six cells:",
      ", ".join(f"{l}/t{t}: 2^{b:.1f}" for b, l, t in floor_costs[:6]))
print(f"  Cells whose floor cost is already >= 2^128: {sum(b >= KAPPA for b, _, _ in floor_costs)}/{len(floor_costs)}; "
      f"lowest floor cost among t >= 8 cells: 2^{min(b for b, _, t in floor_costs if t >= 8):.1f}")

# show the three non-floor cells with their intermediates (the actual calibration)
print("\n  Calibration cells (where the cost, not the trail floor, decides):")
for label, pb, alpha, t in [("d", 256, 3, 4), ("d", 256, 3, 6), ("e", 256, 5, 4), ("f", 256, 7, 4)]:
    p = 2 ** pb
    Ec = t - 2
    for rP in range(2 * Ec + 1, 2 * Ec + 7):
        r = model3_sub(t, 1, 1, alpha, 3, 3, rP, p)
        print(f"    {label} t={t} a={alpha} Ec={Ec} rP={rP:2}: tau*={r['tau']} n={r['n']} "
              f"deg_sub={r['deg_sub']} deg_dig={r['deg_dig']} sum={r['sum_deg']} dreg={r['dreg']} "
              f"GB=2^{r['bits']:.1f} FGLM=2^{r['fglm']:.1f}")
        if r["bits"] >= KAPPA and r["fglm"] >= KAPPA:
            break

# ==========================================================================
print("\n" + "=" * 96)
print("REPRODUCTION 2: Table C.2 (compression mode, c=0, rF=6, all seven rows per instance)")
print("=" * 96)
c2 = [  # p_bits, t, d, alpha, printed (baseline, margin, basic, sub+lin, sub+nonlin, nonsub+lin, nonsub+nonlin)
    (64, 24, 4, 3, (39, 42, 4, 20, 41, 20, 41)),
    (256, 22, 1, 7, (43, 47, 34, 21, 43, 21, 43)),
    (256, 24, 1, 7, (43, 47, 34, 23, 47, 23, 47)),
]
ok = tot = 0
for pb, t, d, alpha, printed in c2:
    p = 2 ** pb
    Ec = t - d
    base, marg = designers_rP(pb, t, alpha, 6)
    basic = round_number(lambda rP: model1_basic(t, 0, d, alpha, 6, rP, p)["bits"], 0)
    sl = round_number(lambda rP: model3_sub(t, 0, d, alpha, 3, 3, rP, p, nonlinear=False)["bits"], Ec)
    sn = round_number(lambda rP: model3_sub(t, 0, d, alpha, 3, 3, rP, p, nonlinear=True)["bits"], 2 * Ec + 1)
    nl = round_number(lambda rP: model5_nonsub(t, 0, d, alpha, 3, 3, rP, p, nonlinear=False)["bits"], Ec)
    nn = round_number(lambda rP: model5_nonsub(t, 0, d, alpha, 3, 3, rP, p, nonlinear=True)["bits"], 2 * Ec + 1)
    got = (base, marg, basic, sl, sn, nl, nn)
    for g, pr in zip(got, printed):
        ok += g == pr
        tot += 1
    print(f"  p~2^{pb} t={t} c=0 d={d} a={alpha} Ec={Ec}: baseline {base} (paper {printed[0]})  margin {marg} ({printed[1]})  "
          f"basic {basic} ({printed[2]})  sub+lin {sl} ({printed[3]})  sub+nonlin {sn} ({printed[4]})  "
          f"nonsub+lin {nl} ({printed[5]})  nonsub+nonlin {nn} ({printed[6]})")
    # basic-attack crossing detail
    for rP in (basic - 1, basic):
        r = model1_basic(t, 0, d, alpha, 6, rP, p)
        print(f"      basic rP={rP}: n={r['n']} deg={r['deg_digest']} ({r['how']}) -> 2^{r['bits']:.1f}")
print(f"  Table C.2 entries reproduced: {ok}/{tot}")

# ==========================================================================
print("\n" + "=" * 96)
print("OUR POINT: BabyBear p=2013265921 (~2^30.9), Poseidon2 t=16, alpha=7, R_F=8 (rf=rf'=4)")
print("=" * 96)
P = 2013265921
T, ALPHA, RF, RF2 = 16, 7, 4, 4
BARS = [("2^128 (paper's bar)", 128), ("2^124 (VERDICTS collision claim, 8 elems)", 124),
        ("2^100 (VERDICTS S1 Ext4 realized soundness)", 100), ("2^248 (generic preimage, 8 elems)", 248)]

objects = [
    ("MERKLE NODE  TruncatedPermutation<Perm16,2,8,16>  compression c=0 d=8", 0, 8),
    ("LEAF SPONGE  PaddingFreeSponge<Perm16,16,8,8>      sponge c=8 d=8", 8, 8),
]
for RP in (13, 20):
    for name, c, d in objects:
        Ec = T - c - d
        print(f"\n--- R_P = {RP} | {name} | Ec = t-c-d = {Ec}, nonlinear trail 2Ec+1 = {2*Ec+1}, "
              f"linear trail Ec = {Ec}; partial rounds absorbed by nonlinear trail = min(R_P, 2Ec+1) = {min(RP, 2*Ec+1)}")
        results = []
        for omega in (2, 2.37):
            m1 = model1_basic(T, c, d, ALPHA, RF + RF2, RP, P, omega)
            m2 = model3_sub(T, c, d, ALPHA, RF, RF2, RP, P, omega, nonlinear=False)
            m3 = model3_sub(T, c, d, ALPHA, RF, RF2, RP, P, omega, nonlinear=True)
            m3g = model3_sub(T, c, d, ALPHA, RF, RF2, RP, P, omega, nonlinear=True, literal=False)
            m4 = model5_nonsub(T, c, d, ALPHA, RF, RF2, RP, P, omega, nonlinear=False)
            m5 = model5_nonsub(T, c, d, ALPHA, RF, RF2, RP, P, omega, nonlinear=True)
            m5g = model5_nonsub(T, c, d, ALPHA, RF, RF2, RP, P, omega, nonlinear=True, literal=False)
            print(f"  omega = {omega}")
            print(f"    model 1 basic        : n={m1['n']:2} deg_dig=7^{RF+RF2+RP}{' CAPPED to p-2='+str(m1['deg_digest']) if m1['capped'] else '='+str(m1['deg_digest'])} "
                  f"sum={m1['sum_deg']} -> {m1['how']} 2^{m1['bits']:.1f}")
            for m in (m2, m3, m4, m5):
                flag = " [R_P < trail floor %d: tau-range empty; flat extension at tau=0]" % m['floor'] if m['below_floor'] else ""
                dsub = f"deg_sub=7^{RF}+tau={m['deg_sub']}" if 'deg_sub' in m else f"deg_con={m['deg_con']}"
                print(f"    model {m['model']:<15}: n={m['n']:2} Ec_used={m['Ec_used']} tau*={m['tau']} {dsub} "
                      f"deg_dig=7^{m['e_dig']}={m['deg_dig']}{' (capped)' if m['capped'] else ''} unabsorbed_partial={m['unabsorbed']} "
                      f"sum={m['sum_deg']} dreg={m['dreg']} -> GB 2^{m['bits']:.1f}  FGLM(w=3) 2^{m['fglm']:.1f}{flag}")
            for m in (m3g, m5g):
                print(f"    model {m['model']:<15} attacker-optimal (Ec'<=Ec, DoF fixed): n={m['n']:2} Ec_used={m['Ec_used']} tau*={m['tau']} "
                      f"deg_dig=7^{m['e_dig']} unabsorbed={m['unabsorbed']} sum={m['sum_deg']} -> GB 2^{m['bits']:.1f}")
            results.append((omega, min(x['bits'] for x in (m1, m2, m3, m3g, m4, m5, m5g)),
                            min((m1, m2, m3, m3g, m4, m5, m5g), key=lambda x: x['bits'])['model']))
        for omega, best, which in results:
            print(f"  CHEAPEST in 1792's model family at omega={omega}: 2^{best:.1f} ({which})")
            for bname, b in BARS:
                print(f"      vs {bname:<46}: {best - b:+.1f} bits")

# ==========================================================================
print("\n" + "=" * 96)
print("CONTEXT: CICO-d sweep on the compression node at R_P = 13 (d output constraints, 16 free inputs)")
print("  (only d = 8 is the Merkle claim; smaller d is not a break of the tree)")
print("=" * 96)
for d in range(1, 9):
    Ec = T - d
    m1 = model1_basic(T, 0, d, ALPHA, 8, 13, P)
    m3 = model3_sub(T, 0, d, ALPHA, 4, 4, 13, P, nonlinear=True, literal=False)
    m5 = model5_nonsub(T, 0, d, ALPHA, 4, 4, 13, P, nonlinear=True, literal=False)
    best = min((m1, m3, m5), key=lambda x: x['bits'])
    print(f"  d={d}: Ec={Ec:2} 2Ec+1={2*Ec+1:2} | basic({m1['how']}, n={m1['n']}) 2^{m1['bits']:.1f} | "
          f"sub+nonlin(n={m3['n']},Ec'={m3['Ec_used']}) 2^{m3['bits']:.1f} | nonsub+nonlin(n={m5['n']},Ec'={m5['Ec_used']}) 2^{m5['bits']:.1f} "
          f"| cheapest 2^{best['bits']:.1f} vs generic 2^{31*d}")
