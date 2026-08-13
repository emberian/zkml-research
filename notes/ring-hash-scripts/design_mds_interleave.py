"""
HOW FEW DENSE (SLOT-MDS) ROUNDS SUFFICE?  Schedules, measured.

design_branch_frontier.py established the per-round menu at tau=1, d=16:
    support-3  {1,5,-1}          1 row/elt/round   slot-branch 4
    support-9  {5^0..5^4,-5^0..-5^3}  4 rows      slot-branch 10 (law)
    dense G, Cauchy-programmed   8 rows           slot-branch 17 = slot-MDS, by theorem

This script measures what SCHEDULES buy, on two axes the attack surface cares
about (Sec. D's distinguisher and invariant-subspace structure both live in the
slot basis):

  (A) COMPOSITE SUPPORT of the linear skeleton: after r rounds of layer support
      K per round, the composite layer's slot-support is the product set
      K^r -- measured as boolean matrix products (exact, structural).
      Full support = every output slot reads every input slot.

  (B) COMPOSITE MDS-ness (sampled): fraction of random n/2 x n/2 submatrices of
      the composite that are singular, plus exact-to-cap MDS check at d=8.

  (C) SLOT DIFFUSION of the real nonlinear permutation (S-box included),
      slot-basis differential as in slot_diffusion.py, per schedule.

  (D) the COST of each schedule per absorbed ring element, at the proposal
      geometry (t=9, rate 8, RF=8, RP=22, alpha=7, S_alpha=4).

The Poseidon2 precedent frames the answer: Poseidon2's INTERNAL rounds use
I + diag(v) -- a layer with branch 2, far weaker than our support-3 -- and put
the strong MDS only in EXTERNAL rounds.  The measured tables below say whether
the analogous schedule (dense in full rounds, support-3 in partial rounds)
keeps the composite skeleton saturated here.  Preview of the verdict: it does.
"""
import itertools, random
from math import gcd

def units(n): return [k for k in range(1, n) if gcd(k, n) == 1]

def slot_perms(q, d):
    roots = sorted(w for w in range(1, q) if pow(w, d, q) == q - 1)
    assert len(roots) == d
    idx = {w: j for j, w in enumerate(roots)}
    return {k: [idx[pow(w, k, q)] for w in roots] for k in units(2 * d)}, roots

# ---------------------------------------------------------------- (A) support growth
print("=" * 78)
print("(A) composite slot-support of the linear skeleton, d=16 (exact, structural)")
print("=" * 78)
d = 16
N = 2 * d
G = units(N)

def pattern(K):
    """boolean slot pattern of a support-K layer (translation action of G on itself)."""
    P = [[False] * d for _ in range(d)]
    Gl = sorted(G)
    gi = {g: i for i, g in enumerate(Gl)}
    for k in K:
        for i, g in enumerate(Gl):
            P[i][gi[g * k % N]] = True
    return P

def bmul(A, B):
    n = len(A)
    return [[any(A[i][k] and B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

def minsupp(P):
    return min(sum(row) for row in P)

K3 = [1, 5, N - 1]
K9 = sorted(set([pow(5, j, N) for j in range(5)] + [(-pow(5, j, N)) % N for j in range(4)]))
KD = G
SCHEDULES = {
    "support-3 every round (1 row/elt)":        lambda r: K3,
    "support-9 every round (4 rows/elt)":       lambda r: K9,
    "dense every round (8 rows/elt)":           lambda r: KD,
    "dense every 4th, support-3 else":          lambda r: KD if r % 4 == 3 else K3,
    "dense every 8th, support-3 else":          lambda r: KD if r % 8 == 7 else K3,
}
print(f"  {'schedule':<38} min row-support of composite after round r = 1..10")
for name, sched in SCHEDULES.items():
    P = None
    out = []
    for r in range(10):
        Q = pattern(sched(r))
        P = Q if P is None else bmul(Q, P)
        out.append(minsupp(P))
    print(f"  {name:<38} {out}")
print(f"""
  ^ support-3 alone saturates all {d} slots after 8 rounds (product sets
    {{±5^j}} grow by one exponent per round); interleaving one dense round
    collapses the wait to that round's position.  Support saturation is
    NECESSARY for RO-likeness, nowhere near sufficient.""")

# ---------------------------------------------------------------- (B) composite MDS
print("=" * 78)
print("(B) composite MDS-ness, d=8, t=1, q=65537 (exact to cap + sampled)")
print("=" * 78)
q8, d8 = 65537, 8
perms8, roots8 = slot_perms(q8, d8)
G8 = units(16)
rng = random.Random(7)

def sigma_layer(q, d, K, rng, perms, cauchy=False):
    if cauchy:
        xs = list(range(1, d + 1)); ys = list(range(d + 1, 2 * d + 1))
        return [[pow(xs[i] + ys[j], q - 2, q) for j in range(d)] for i in range(d)]
    M = [[0] * d for _ in range(d)]
    for k in K:
        D = [rng.randrange(1, q) for _ in range(d)]
        pk = perms[k]
        for s in range(d):
            M[s][pk[s]] = (M[s][pk[s]] + D[s]) % q
    return M

def matmul(A, B, p):
    n = len(A)
    return [[sum(A[i][x] * B[x][j] for x in range(n)) % p for j in range(n)] for i in range(n)]

def rank_mod(M, p):
    M = [row[:] for row in M]; rows = len(M); cols = len(M[0]); r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [v * inv % p for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(M[i][k] - f * M[r][k]) % p for k in range(cols)]
        r += 1
    return r

def is_mds_exact(M, p):
    n = len(M)
    for k in range(1, n + 1):
        for rows in itertools.combinations(range(n), k):
            for cols in itertools.combinations(range(n), k):
                sub = [[M[i][j] for j in cols] for i in rows]
                if rank_mod(sub, p) < k: return False
    return True

K3_8 = [1, 5, 15]
SCHED8 = {
    "support-3 every round":       lambda r: (K3_8, False),
    "dense Cauchy every round":    lambda r: (None, True),
    "dense every 4th, s-3 else":   lambda r: (None, True) if r % 4 == 3 else (K3_8, False),
}
print(f"  {'schedule':<32} composite MDS after round r = 1..6")
for name, sched in SCHED8.items():
    P = None
    out = []
    for r in range(6):
        K, cau = sched(r)
        Q = sigma_layer(q8, d8, K, rng, perms8, cauchy=cau)
        P = Q if P is None else matmul(Q, P, q8)
        out.append("Y" if is_mds_exact(P, q8) else "n")
    print(f"  {name:<32} {' '.join(out)}")
print("""
  ^ a single dense (Cauchy) round makes the COMPOSITE skeleton MDS at once,
    and further support-3 rounds do not destroy it (generic composition
    preserves MDS w.h.p. at large q).  Support-3 alone becomes MDS only when
    its product set saturates.""")

# ---------------------------------------------------------------- (C) real diffusion
print("=" * 78)
print("(C) slot diffusion of the REAL permutation (S-box on), d=16, tau=1 toy")
print("=" * 78)
qs, ds, t = 12289, 16, 4
permsS, rootsS = slot_perms(qs, ds)
ALPHA = 7
assert gcd(ALPHA, qs - 1) == 1

class R:
    @staticmethod
    def add(a, b): return [(x + y) % qs for x, y in zip(a, b)]
    @staticmethod
    def mul(a, b):
        r = [0] * ds
        for i, x in enumerate(a):
            if not x: continue
            for j, y in enumerate(b):
                e = i + j
                if e < ds: r[e] = (r[e] + x * y) % qs
                else: r[e - ds] = (r[e - ds] - x * y) % qs
        return r
    @staticmethod
    def pow(a, n):
        r = [1] + [0] * (ds - 1); b = a[:]
        while n:
            if n & 1: r = R.mul(r, b)
            b = R.mul(b, b); n >>= 1
        return r
    @staticmethod
    def sigma(a, k):
        r = [0] * ds
        for j, c in enumerate(a):
            e = (j * k) % (2 * ds); s = 1
            if e >= ds: e -= ds; s = -1
            r[e] = (r[e] + s * c) % qs
        return r

def slots(a):
    out = []
    for w in rootsS:
        v = 0
        for c in reversed(a): v = (v * w + c) % qs
        out.append(v)
    return out

def unslot(sl):
    A = [[pow(w, i, qs) for i in range(ds)] + [sl[j]] for j, w in enumerate(rootsS)]
    for c in range(ds):
        p_ = next(r for r in range(c, ds) if A[r][c] % qs)
        A[c], A[p_] = A[p_], A[c]
        inv = pow(A[c][c], qs - 2, qs); A[c] = [v * inv % qs for v in A[c]]
        for r in range(ds):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [(A[r][k] - f * A[c][k]) % qs for k in range(ds + 1)]
    return [A[i][ds] for i in range(ds)]

rng2 = random.Random(31)
MDSr = [[[rng2.randrange(qs) for _ in range(ds)] for _ in range(t)] for _ in range(t)]

def apply_sigma_K(x, K, coefs):
    acc = x[:] if 1 in K else [0] * ds
    for k in K:
        if k == 1: continue
        acc = R.add(acc, R.mul(coefs[k], R.sigma(x, k)))
    return acc

K3_16 = [1, 5, 31]
KD_16 = units(32)

def perm_rounds(state, nrounds, sched, rngc):
    s = state
    for rd in range(nrounds):
        s = [R.pow(x, ALPHA) for x in s]
        ns = []
        for i in range(t):
            acc = [0] * ds
            for j in range(t):
                acc = R.add(acc, R.mul(MDSr[i][j], s[j]))
            ns.append(acc)
        s = ns
        K = sched(rd)
        coefs = {k: [rngc.randrange(qs) for _ in range(ds)] for k in K}
        s = [apply_sigma_K(x, K, coefs) for x in s]
    return s

SCHEDC = {
    "support-3 every round":     lambda r: K3_16,
    "dense every round":         lambda r: KD_16,
    "dense rd 0 only, s-3 else": lambda r: KD_16 if r == 0 else K3_16,
}
for name, sched in SCHEDC.items():
    row = []
    for nr in range(1, 7):
        tot = 0; trials = 10
        for _ in range(trials):
            x = [[rng2.randrange(qs) for _ in range(ds)] for _ in range(t)]
            sx = [slots(e) for e in x]
            j = rng2.randrange(ds)
            sy = [r_[:] for r_ in sx]; sy[0][j] = (sy[0][j] + 1) % qs
            y = [unslot(r_) for r_ in sy]
            a = perm_rounds(x, nr, sched, random.Random(99))
            b = perm_rounds(y, nr, sched, random.Random(99))
            da = [slots(e) for e in a]; db = [slots(e) for e in b]
            tot += sum(1 for i in range(t) for jj in range(ds) if da[i][jj] != db[i][jj])
        row.append(f"{tot/trials:5.1f}")
    print(f"  {name:<28} active slots (of {t*ds}) after r=1..6: {' '.join(row)}")

# ---------------------------------------------------------------- (D) schedule costs
print()
print("=" * 78)
print("(D) cost per absorbed ring element at proposal geometry (t=9, r=8, RF=8, RP=22)")
print("=" * 78)
S_ALPHA, RF, RP, T, RATE = 4, 8, 22, 9, 8
NR = RF + RP
sbox = S_ALPHA * (RF * T + RP)
print(f"  {'sigma schedule':<52} {'rows/perm':>9} {'per elt':>8} {'vs 716.8':>8}")
for name, cost_by_round in [
    ("support-3 every round  [prior lane's headline]",   [1] * NR),
    ("dense every round",                                [8] * NR),
    ("dense in FULL rounds, support-3 in partial",       [8] * RF + [1] * RP),
    ("dense in 4 outer full rounds, support-3 else",     [8, 8] + [1] * (NR - 4) + [8, 8]),
    ("support-9 in full rounds, support-3 in partial",   [4] * RF + [1] * RP),
    ("dense every 4th round, support-3 else",            [8 if r % 4 == 3 else 1 for r in range(NR)]),
]:
    sig = sum(cost_by_round) * T
    per = (sbox + sig) / RATE
    print(f"  {name:<52} {sbox + sig:>9} {per:>8.1f} {716.8 / per:>7.1f}x")
print("""
  ^ dense-in-full-rounds (the Poseidon2-shaped schedule) buys slot-MDS branch
    in every full round for ~5x vs the field baseline; the 4-outer-round
    variant recovers ~6.4x.  Against these, support-3-everywhere (8.9x) keeps
    only branch 4.  The winner depends on how much the STRUCTURED-attack
    margin is worth; the proposal takes dense-in-full-rounds and says why.""")
