"""
IDEAL-QUOTIENT GATE -- does either full-mode round function respect a CRT ideal?

HAZARD (elementary; needs no Groebner basis).  Let R be a finite commutative ring,
I a nonzero proper ideal, pi : R -> R/I.  Any map F : R^w -> R^w assembled from ring
operations (ring +, ring * by constants or variables, R-linear mixing, x^alpha) satisfies
    x = y (mod I)  =>  F(x) = F(y) (mod I)   componentwise,
because pi is a ring homomorphism.  For an ideal permutation the same event has
probability |R/I|^(-w).  So a ring-polynomial F is distinguished with one query pair,
and worse: over R = prod_i R/I_i it is |R/I|-many independent maps.  This is
2026/1127 Sec. D's slot-locality observation, and eprint 2023/822 Lemma 1
(F(x) mod u = F(x mod u)) in ideal-theoretic clothing.

OUR RING.  R_q = Z_q[X]/(X^16+1), q = 2^64 - 257 (prime, q = -1 mod 32), so X^16+1
splits into EIGHT irreducible quadratics f_k = X^2 - c_k X + 1, c_k = zeta^k + zeta^-k,
zeta a primitive 32nd root of unity in F_{q^2} = F_q[i], k in {1,3,5,7,9,11,13,15}.
R_q = prod_k F_{q^2}  (tau = 2, ell = 8).  The eight ideals I_k = (f_k) are the ideals
to test.  Everything below runs at the REAL modulus -- no toy instance is needed,
because the statistic is exact (agreement is 0/1 per trial and the random baseline
is q^-2 = 2^-128 per element).

WHAT IS TESTED, at the ground-truth definitions imported from the sibling scripts:
  (A) sigma-Poseidon  (sigma_poseidon.py, frog_like() at q = 2^64-257): each layer
      alone, each of the 30 rounds alone, 1 / 2 / 30 rounds, and the sigma-OFF control.
  (B) gadget-Feistel  (design_gadget_feistel.py Feistel at q = 2^64-257): G^-1 alone,
      the plane-linear map alone on UNdecomposed input (control), F at P=0 and P=2,
      1 / 2 / 16 rounds.
  (C) linear mode  C = A . G^-1(v + a0): as a map of v, and as a map of the planes Y.
  (D) the sigma cost law at tau=2: how many chain rows reach full slot-support 8,
      per choice of the second automorphism sigma~ in Def. 9's pp.

RATE 1 = the hazard (F respects I_k).  RATE 0 = the escape (baseline 2^-128 per elt).
"""
import os, sys, random, time
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sigma_poseidon as SP                      # __main__-guarded: safe to import

# ------------------------------------------------------------ Feistel: load defs only
# design_gadget_feistel.py runs its experiments at module level; exec only the
# definitions (everything before its first experiment banner), verbatim.
_src = open(os.path.join(HERE, "design_gadget_feistel.py")).read()
_cut = _src.index("# ================================================== (1)")
GF = {}
exec(compile(_src[:_cut], "design_gadget_feistel.py[defs]", "exec"), GF)
Feistel, gadget, ring_ops = GF["Feistel"], GF["gadget"], GF["ring_ops"]

# ------------------------------------------------------------ parameters
Q = 2**64 - 257
D = 16
assert Q % 32 == 31 and Q % 4 == 3            # tau = 2; -1 is a non-residue -> F_q[i]
add, sub, mul = ring_ops(Q)                    # negacyclic ring ops, from the Feistel file
Rq = SP.Rq(Q, D)
assert Rq.tau == 2 and Rq.ell == 8

# ------------------------------------------------------------ F_{q^2} = F_q[i]/(i^2+1)
def f2mul(u, v):
    a, b = u; c, d = v
    return ((a*c - b*d) % Q, (a*d + b*c) % Q)
def f2pow(u, e):
    r, b = (1, 0), u
    while e:
        if e & 1: r = f2mul(r, b)
        b = f2mul(b, b); e >>= 1
    return r
def f2add(u, v): return ((u[0]+v[0]) % Q, (u[1]+v[1]) % Q)

rng = random.Random(2026)
while True:                                     # primitive 32nd root of unity
    z = (rng.randrange(Q), rng.randrange(Q))
    zeta = f2pow(z, (Q*Q - 1)//32)
    if f2pow(zeta, 16) == (Q-1, 0): break
SLOTS = [1, 3, 5, 7, 9, 11, 13, 15]             # coset reps of <q> = {1,31} in (Z/32)^*
ZK = {k: f2pow(zeta, k) for k in SLOTS}
FK = {}                                         # f_k = X^2 - c_k X + 1 as a ring element
for k in SLOTS:
    ck = f2add(f2pow(zeta, k), f2pow(zeta, 32-k))
    assert ck[1] == 0, "c_k must lie in F_q"
    c = ck[0]
    assert pow((c*c - 4) % Q, (Q-1)//2, Q) == Q-1, "f_k must be irreducible (disc non-residue)"
    FK[k] = [1, (-c) % Q, 1] + [0]*(D-3)
# premise-inhabitation: prod_k f_k = X^16 + 1 in Z_q[X] (NO reduction)
prod = [1]
for k in SLOTS:
    f = FK[k][:3]; new = [0]*(len(prod)+2)
    for i, a in enumerate(prod):
        for j, b in enumerate(f): new[i+j] = (new[i+j] + a*b) % Q
    prod = new
assert prod == [1] + [0]*15 + [1], "the eight quadratics must multiply to X^16+1"

def ev(x, k):
    """x(zeta^k) in F_{q^2}: x = y mod I_k  <=>  ev(x,k) == ev(y,k)."""
    v = (0, 0)
    for c in reversed(x): v = f2add(f2mul(v, ZK[k]), (c % Q, 0))
    return v
def congr(x, y, k): return ev(x, k) == ev(y, k)
def rem_fk(x, k):
    """remainder of x mod f_k by long division -- independent congruence check."""
    c = (-FK[k][1]) % Q; r = list(x)
    for i in range(D-1, 1, -1):
        t = r[i]
        if t:
            r[i] = 0; r[i-1] = (r[i-1] + t*c) % Q; r[i-2] = (r[i-2] - t) % Q
    return r[:2]

def rand_elt(): return [rng.randrange(Q) for _ in range(D)]
def pair(k, w):
    """x, y in R_q^w with x = y (mod I_k) componentwise, y uniform in that coset."""
    x = [rand_elt() for _ in range(w)]
    y = [add(xi, mul(FK[k], rand_elt())) for xi in x]
    assert all(congr(a, b, k) for a, b in zip(x, y))
    assert all(rem_fk(sub(a, b), k) == [0, 0] for a, b in zip(x, y))
    return x, y

def rate(fn, w, N=3, slots=SLOTS):
    """per slot k: (whole-state agreements / N, mean per-element agreement fraction)."""
    out = {}
    for k in slots:
        whole = 0; elts = 0
        for _ in range(N):
            x, y = pair(k, w)
            fx, fy = fn(x), fn(y)
            ag = sum(1 for a, b in zip(fx, fy) if congr(a, b, k))
            elts += ag; whole += (ag == len(fx))
        out[k] = (whole / N, elts / (N*len(fx)))
    return out

def show(label, res):
    ws = " ".join(f"{res[k][0]:.2f}" for k in SLOTS)
    pe = sum(res[k][1] for k in SLOTS) / len(SLOTS)
    tag = "HAZARD (rate 1)" if all(res[k][0] == 1 for k in SLOTS) else \
          ("escape" if all(res[k][0] == 0 for k in SLOTS) else "MIXED")
    print(f"  {label:<44} slots k=1..15: {ws}   per-elt {pe:.3f}   {tag}")

print("=" * 100)
print(f"IDEAL-QUOTIENT GATE at q = 2^64-257 (prime, q mod 32 = 31), d=16, tau=2, ell=8 slots F_(q^2)")
print(f"  c_k (k=1,3,5): {[(-FK[k][1]) % Q for k in (1,3,5)]}  ...  prod_k f_k == X^16+1: verified")
print(f"  random baseline Pr[agree in one slot] = q^-2 = 2^-128 per element; N trials per cell")
print("=" * 100)

# ============================================================ (A) sigma-Poseidon
print("\n(A) sigma-POSEIDON, frog_like(q=2^64-257): t=9, RF=8, RP=22, alpha=7, sigma every round")
P = SP.frog_like(q=Q)
assert P.R.tau == 2 and P.R.ell == 8
for name, ok, note in P.validate():
    print(f"    [{'PASS' if ok else 'FAIL'}] {name:<42} {note}")
T = P.t

def sp_rounds(P, state, r_lo, r_hi):
    """rounds r_lo..r_hi-1 of SP.permutation, loop body copied verbatim (guarded below)."""
    R, t = P.R, P.t
    s = list(state); nrounds = P.RF + P.RP; half = P.RF // 2
    for rd in range(r_lo, r_hi):
        s = [R.add(x, P.rc[rd][i]) for i, x in enumerate(s)]
        full = rd < half or rd >= nrounds - half
        if full: s = [R.pow(x, P.alpha) for x in s]
        else:    s = [R.pow(s[0], P.alpha)] + s[1:]
        s = [SP._mds_row(R, P.mds, s, i, t) for i in range(t)]
        if rd in P.sigma_rounds:
            k = P.sigma_exps[rd]
            s = [R.add(x, R.mul(P.sc[rd][i], R.sigma(x, k))) for i, x in enumerate(s)]
    return s
for _ in range(2):                              # guard: the copy IS the ground truth
    st = [rand_elt() for _ in range(T)]
    assert sp_rounds(P, st, 0, P.RF+P.RP) == SP.permutation(P, st)
# at tau=2, sigma_{-1} = sigma_31 = sigma_q IS the power map x -> x^q on R_q (ring-polynomial):
for x in ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], [Q-1, 0, 5] + [0]*12 + [7]):
    assert P.R.pow(x, Q) == P.R.sigma(x, 31) and P.R.pow(x, Q*Q) == x
print("  sigma_31(x) == x^q in R_q (verified on fixed inputs): the tau=2 'sigma_-1' is a POWER MAP")

t0 = time.time()
print("  layers alone (round-0 tables):")
show("round constants  s + rc",           rate(lambda s: [P.R.add(x, P.rc[0][i]) for i, x in enumerate(s)], T))
show("S-box  x^7",                        rate(lambda s: [P.R.pow(x, 7) for x in s], T))
show("R_q-MDS",                           rate(lambda s: [SP._mds_row(P.R, P.mds, s, i, T) for i in range(T)], T))
for k in (1, 31, 5, 25, 17):
    lab = {1: "identity", 31: "= sigma_q, Frobenius", 5: "8-cycle on slots", 25: "two 4-cycles", 17: "four 2-cycles"}[k]
    show(f"sigma-layer  x + c*sigma_{k}(x)   [{lab}]",
         rate(lambda s, k=k: [P.R.add(x, P.R.mul(P.sc[0][i], P.R.sigma(x, k))) for i, x in enumerate(s)], T))

print("  single rounds r (sigma exponent in brackets):")
local = []
for r in range(P.RF + P.RP):
    res = rate(lambda s, r=r: sp_rounds(P, s, r, r+1), T, N=2)
    h = all(res[k][0] == 1 for k in SLOTS)
    if h: local.append(r)
    if r < 12 or h:
        show(f"round {r:>2}  [sigma_{P.sigma_exps[r]}]", res)
print(f"  ==> slot-respecting rounds: {local}  = {len(local)}/{P.RF+P.RP}"
      f"   (exp in <q> = {{1,31}} mod 32; matches ring-hash-attacks-2-3-4.md sec 3b: 14/30, run 8-11)")
NR = P.RF + P.RP
show("rounds 0-0 (1 round)",   rate(lambda s: sp_rounds(P, s, 0, 1), T))
show("rounds 0-1 (2 rounds)",  rate(lambda s: sp_rounds(P, s, 0, 2), T))
show("rounds 8-11 (the slot-diagonal window)", rate(lambda s: sp_rounds(P, s, 8, 12), T))
show(f"full permutation ({NR} rounds)", rate(lambda s: SP.permutation(P, s), T))
P0 = SP.frog_like(q=Q); P0.sigma_rounds = set()          # sigma OFF: 2026/1127 Sec. D's object
show(f"CONTROL sigma OFF, {NR} rounds (ring-Poseidon)", rate(lambda s: SP.permutation(P0, s), T))
P5 = SP.frog_like(q=Q); P5.sigma_exps = [5]*NR           # every round slot-moving
show(f"sigma_5 every round, {NR} rounds", rate(lambda s: SP.permutation(P5, s), T))
print(f"  [A took {time.time()-t0:.0f}s]")

# ============================================================ (B) gadget-Feistel
print("\n(B) GADGET-FEISTEL, Feistel(q=2^64-257): w=4 per branch (state 8), B=2^16, K=4, P=2, NR=16")
Fe = Feistel(Q, seed=2026)                       # P=2
Fe0 = Feistel(Q, seed=2026, p=0)                 # P=0: linear in planes
W = Fe.w
def planes_map(s):                               # G^-1 alone: all K planes of each element
    return [pl for x in s for pl in gadget(add(x, Fe.a[0][0]), Q, Fe.base, Fe.k)]
def plane_linear_undecomposed(s):                # CONTROL: the same dense R_q-linear map on x itself
    out = []
    for i in range(W):
        acc = [0]*D
        for i2 in range(W):
            for j in range(Fe.k): acc = add(acc, mul(Fe.g[0][i][i2][j], s[i2]))
        out.append(acc)
    return out
def feistel_rounds(nr):
    return lambda s: (lambda LR: LR[0] + LR[1])(Fe.perm(s[:W], s[W:], rounds=nr))
show("G^-1 alone  (planes Y_j, all 4)",        rate(planes_map, W))
show("plane-linear map on UNdecomposed x (ctl)", rate(plane_linear_undecomposed, W))
show("F_0 at P=0  (G^-1 then linear)",         rate(lambda s: Fe0.F(s, 0), W))
show("F_0 at P=2  (G^-1, products, linear)",   rate(lambda s: Fe.F(s, 0), W))
show("1 round  (R passes through: 4/8 agree)", rate(feistel_rounds(1), 2*W))
show("2 rounds",                               rate(feistel_rounds(2), 2*W))
show("full permutation (16 rounds)",           rate(feistel_rounds(16), 2*W))

# ============================================================ (C) linear mode
print("\n(C) LINEAR MODE  C = A . G^-1(v + a0), kappa=2 rows for the test (A uniform, ring-linear in planes)")
KAPPA = 2
A = [[rand_elt() for _ in range(Fe.k * W)] for _ in range(KAPPA)]
a0 = [rand_elt() for _ in range(W)]
def commit_v(v):
    Y = [pl for i in range(W) for pl in gadget(add(v[i], a0[i]), Q, Fe.base, Fe.k)]
    return [sum_(mul(A[r][j], Y[j]) for j in range(len(Y))) for r in range(KAPPA)]
def sum_(it):
    acc = [0]*D
    for e in it: acc = add(acc, e)
    return acc
def commit_Y(Y): return [sum_(mul(A[r][j], Y[j]) for j in range(len(Y))) for r in range(KAPPA)]
show("as a map of the payload v  (G^-1 inside)", rate(commit_v, W))
show("as a map of the planes Y   (R_q-linear)",  rate(commit_Y, Fe.k * W))

# ============================================================ (D) sigma cost law at tau=2
print("\n(D) SIGMA COST LAW AT tau=2: chain rows to reach full slot-support 8, per Def.9 pp=(sigma_5, sigma~)")
print("    model: each row materialises ONE new witness = sigma or sigma~ of an existing one;")
print("    the final combine reaches classes(E u 5E u s~E) with independent coefficients.")
def cls(e): return min(e % 32, (-e) % 32)       # slot class of exponent e at tau=2: {e,-e}
from itertools import product as iprod
for st in (31, 25, 17, 9, 3):
    best = None
    for c in range(0, 8):
        # enumerate chain-built E of size c+1 containing 1 (each step: 5* or st* an existing exp)
        frontier = [{1}]
        for _ in range(c):
            nxt = []
            for E in frontier:
                for e in E:
                    for g in (5, st):
                        E2 = E | {(e*g) % 32}
                        if len(E2) == len(E)+1: nxt.append(E2)
            frontier = nxt
        for E in frontier:
            reach = {cls(e) for e in E} | {cls(5*e) for e in E} | {cls(st*e) for e in E}
            if len(reach) == 8: best = c; break
        if best is not None: break
    note = {31: "= sigma_q (Frobenius): buys NO new slot class", 25: "= 5^2", 17: "= 5^4", 9: "= 5^6", 3: "not a power of 5 mod 32 (3 = -29 = -5^3)"}[st]
    print(f"    sigma~ = sigma_{st:<2} ({note:<48}) -> min chain rows for support 8: {best}")
print("    the design note's tau=2 figure (design_tau_tradeoff.py) is ceil((8-1)/2) = 4 rows, the tau=1 law.")

print("\nDONE.")
