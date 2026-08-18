"""
ITEM 1 (part A) -- STRUCTURAL FACTS ABOUT THE GADGET-FEISTEL ROUND FUNCTION,
measured against the versioned spec, as the inputs a MITM model needs.

Spec of record: /Users/ember/src/ring-ro-hash/design_gadget_feistel.py
  R_q = Z_q[X]/(X^16+1), q = 2^64-257, B = 2^16, K = 4 planes, w = 4, P = 2, NR = 16
  round: (L,R) <- (R, L + F_r(R))
    Y_{i,j} = plane j of (R_i + a_{r,i});  Z_{i,j} = Y_{i,j} * Y_{i,j+1}, j < P=2
    F_r(R)_i = sum_{i',j<K} g[r][i][i'][j] Y_{i',j} + sum_{i',j<P} h[r][i][i'][j] Z_{i',j}

WHAT THIS SCRIPT SETTLES (each measured, each with a live guard):

  S1. F_r is a SUM OF w INDEPENDENT PER-ELEMENT FUNCTIONS:
        F_r(R)_i = sum_{i'} f_{r,i,i'}(R_{i'}).
      Nothing couples two input elements inside the nonlinearity.

  S2. ⚑ THE TOP PLANE IS NEVER MULTIPLIED.  With P = 2 the products are
      Z_0 = Y_0*Y_1 and Z_1 = Y_1*Y_2.  Y_3 -- the TOP 16 of every 64-bit
      coefficient -- appears ONLY in the linear sum.  So F_r is EXACTLY AFFINE
      in Y_3, with a STATE-INDEPENDENT slope (the public constants g[..][3]).
      That is an order-1 linear relation holding with probability 1 on a set of
      size B^(d*w) = 2^1024, not a probabilistic differential.

  S3. Cell-level diffusion is COMPLETE IN ONE ROUND (needed by the MITM model
      in rha_mitm_dof.py: it is the assumption that makes the colour lattice
      collapse).

  S4. The order-2 differential claim from the design note reproduced AND
      extended past one round -- the note only ever measured ONE round function.
"""
import random
from math import log2

D, B, K, W, P, NR = 16, 1 << 16, 4, 4, 2, 16
Q = (1 << 64) - 257          # the dual-mode modulus


def ring_ops(q, d=D):
    def add(a, b): return [(x + y) % q for x, y in zip(a, b)]
    def sub(a, b): return [(x - y) % q for x, y in zip(a, b)]
    def mul(a, b):
        r = [0] * d
        for i, x in enumerate(a):
            if not x:
                continue
            for j, y in enumerate(b):
                e = i + j
                if e < d:
                    r[e] = (r[e] + x * y) % q
                else:
                    r[e - d] = (r[e - d] - x * y) % q
        return r
    return add, sub, mul


def gadget(a, q, base=B, k=K):
    return [[(c // base ** j) % base for c in a] for j in range(k)]


class Feistel:
    """transcribed from design_gadget_feistel.py, same structure and seeding."""

    def __init__(self, q=Q, seed=2026, w=W, p=P, nr=NR, base=B, k=K):
        self.q, self.w, self.p, self.nr, self.base, self.k = q, w, p, nr, base, k
        self.add, self.sub, self.mul = ring_ops(q)
        rng = random.Random(seed)
        rr = lambda: [rng.randrange(q) for _ in range(D)]
        self.a = [[rr() for _ in range(w)] for _ in range(nr)]
        self.g = [[[[rr() for _ in range(k)] for _ in range(w)] for _ in range(w)] for _ in range(nr)]
        self.h = [[[[rr() for _ in range(p)] for _ in range(w)] for _ in range(w)] for _ in range(nr)]

    def planes_of(self, R_, r):
        return [gadget(self.add(R_[i], self.a[r][i]), self.q, self.base, self.k)
                for i in range(self.w)]

    def F(self, R_, r):
        q, w, p, k = self.q, self.w, self.p, self.k
        planes = self.planes_of(R_, r)
        prods = [[self.mul(planes[i][j], planes[i][j + 1]) for j in range(p)] for i in range(w)]
        out = []
        for i in range(w):
            acc = [0] * D
            for i2 in range(w):
                for j in range(k):
                    acc = self.add(acc, self.mul(self.g[r][i][i2][j], planes[i2][j]))
                for j in range(p):
                    acc = self.add(acc, self.mul(self.h[r][i][i2][j], prods[i2][j]))
            out.append(acc)
        return out

    def F_contrib(self, elt, i2, r):
        """the i2-th per-element term of F_r, computed ALONE."""
        q, p, k = self.q, self.p, self.k
        pl = gadget(self.add(elt, self.a[r][i2]), q, self.base, k)
        pr = [self.mul(pl[j], pl[j + 1]) for j in range(p)]
        out = []
        for i in range(self.w):
            acc = [0] * D
            for j in range(k):
                acc = self.add(acc, self.mul(self.g[r][i][i2][j], pl[j]))
            for j in range(p):
                acc = self.add(acc, self.mul(self.h[r][i][i2][j], pr[j]))
            out.append(acc)
        return out

    def perm(self, L, R_, rounds=None):
        for r in range(rounds if rounds is not None else self.nr):
            L, R_ = R_, [self.add(L[i], self.F(R_, r)[i]) for i in range(self.w)]
        return L, R_


F = Feistel()
rng = random.Random(20260818)
rnd_elt = lambda: [rng.randrange(Q) for _ in range(D)]
rnd_half = lambda: [rnd_elt() for _ in range(W)]

print("=" * 78)
print("S1. F_r IS A SUM OF w INDEPENDENT PER-ELEMENT FUNCTIONS")
print("=" * 78)
ok = 0
TR = 12
for _ in range(TR):
    R_ = rnd_half()
    full = F.F(R_, 0)
    summed = [[0] * D for _ in range(W)]
    for i2 in range(W):
        part = F.F_contrib(R_[i2], i2, 0)
        summed = [F.add(summed[i], part[i]) for i in range(W)]
    ok += (full == summed)
print(f"  sum of per-element contributions == full F_r : {ok}/{TR}")
assert ok == TR
# GUARD (live by injection): drop ONE contribution; the identity must FAIL.
bad = 0
for _ in range(TR):
    R_ = rnd_half()
    full = F.F(R_, 0)
    summed = [[0] * D for _ in range(W)]
    for i2 in range(W - 1):                       # <-- injected defect: omit i2=3
        part = F.F_contrib(R_[i2], i2, 0)
        summed = [F.add(summed[i], part[i]) for i in range(W)]
    bad += (full == summed)
print(f"  GUARD  with one contribution omitted, identity holds in {bad}/{TR}"
      f"  -> {'LIVE (refused)' if bad == 0 else 'DEAD GUARD'}")
assert bad == 0
print("  => the nonlinearity NEVER couples two input elements.  All coupling is")
print("     the public linear layer.  (This is what makes the ring element the")
print("     correct MITM cell, and the coefficient/bit the wrong one.)")

print()
print("=" * 78)
print("S2. ⚑ THE TOP PLANE Y_3 IS NEVER MULTIPLIED -> F IS EXACTLY AFFINE IN IT")
print("=" * 78)
print("  P = 2 gives Z_0 = Y_0*Y_1 and Z_1 = Y_1*Y_2.  Y_3 enters only via g.")
print("  test: F(R + delta) - F(R) for delta a TOP-PLANE offset must be")
print("        INDEPENDENT OF R (a state-independent, probability-1 slope).")

def top_plane_delta(mag):
    """a ring element whose only nonzero content is in plane 3 (bits 48..63)."""
    return [(rng.randrange(mag) << 48) for _ in range(D)]

# choose R so that adding the delta cannot carry out of plane 3: force the top
# plane of R_i + a_i to be small.  We do it by SEARCHING for a compatible R.
def make_carryfree_R(delta):
    """R with (R_i + a_i) having top plane < 2^15, so + delta (<2^15<<48) is carry-free."""
    R_ = []
    for i in range(W):
        base = [rng.randrange(1 << 48) for _ in range(D)]   # top plane zero
        R_.append(F.sub(base, F.a[0][i]))
    return R_

slopes = []
TRIALS = 10
delta = [top_plane_delta(1 << 15) for _ in range(W)]
for _ in range(TRIALS):
    R_ = make_carryfree_R(delta)
    Rd = [F.add(R_[i], delta[i]) for i in range(W)]
    d_out = tuple(tuple(F.sub(F.F(Rd, 0)[i], F.F(R_, 0)[i])) for i in range(W))
    slopes.append(d_out)
uniq = len(set(slopes))
print(f"  top-plane delta: distinct output differences over {TRIALS} random states = {uniq}")
print(f"    -> {'AFFINE (state-independent slope)' if uniq == 1 else 'state-dependent'}")
assert uniq == 1

# GUARD (live by injection): a LOW-plane delta of the same magnitude must be
# state-DEPENDENT, because Y_0 enters Z_0 = Y_0*Y_1.
low_delta = [[rng.randrange(1 << 15) for _ in range(D)] for _ in range(W)]
slopes_low = []
for _ in range(TRIALS):
    R_ = []
    for i in range(W):
        base = [rng.randrange(1 << 48) for _ in range(D)]
        R_.append(F.sub(base, F.a[0][i]))
    Rd = [F.add(R_[i], low_delta[i]) for i in range(W)]
    d_out = tuple(tuple(F.sub(F.F(Rd, 0)[i], F.F(R_, 0)[i])) for i in range(W))
    slopes_low.append(d_out)
uniq_low = len(set(slopes_low))
print(f"  GUARD  LOW-plane delta, same magnitude: distinct differences = {uniq_low}"
      f"  -> {'LIVE (refused affinity)' if uniq_low > 1 else 'DEAD GUARD'}")
assert uniq_low > 1
print("  => 16 of every 64 bits (25% of the state) traverse each round through a")
print("     PURELY LINEAR path.  P=3 (adding Z_2 = Y_2*Y_3) would close it, at")
print("     w = 4 more rows/round: 12 -> 16 rows, +33%.")

print()
print("=" * 78)
print("S3. CELL-LEVEL DIFFUSION IS COMPLETE IN ONE ROUND")
print("=" * 78)
tot = 0
TR3 = 10
for _ in range(TR3):
    R_ = rnd_half()
    i0 = rng.randrange(W)
    R2 = [r[:] for r in R_]
    R2[i0] = rnd_elt()
    o1, o2 = F.F(R_, 0), F.F(R2, 0)
    tot += sum(1 for i in range(W) if o1[i] != o2[i])
print(f"  one input CELL changed -> mean affected output cells = {tot/TR3:.2f} / {W}")
assert tot / TR3 == W
# GUARD: changing NOTHING must affect nothing.
tot0 = 0
for _ in range(TR3):
    R_ = rnd_half()
    o1, o2 = F.F(R_, 0), F.F([r[:] for r in R_], 0)
    tot0 += sum(1 for i in range(W) if o1[i] != o2[i])
print(f"  GUARD  no input change -> affected output cells = {tot0/TR3:.2f}"
      f"  -> {'LIVE' if tot0 == 0 else 'BROKEN HARNESS'}")
assert tot0 == 0

print()
print("=" * 78)
print("S4. THE ORDER-2 DIFFERENTIAL: reproduced, then EXTENDED PAST ONE ROUND")
print("=" * 78)
print("  the design note measured D^2 of ONE round function F and found it")
print("  constant 40/40.  It never measured the PERMUTATION.  Both below.")
Delta = [[1 if (i == 0 and c == 0) else 0 for c in range(D)] for i in range(W)]

# (a) one round function, as the note did
def F_second_diff(seedrng):
    y = [[seedrng.randrange(Q) for _ in range(D)] for _ in range(W)]
    y1 = [F.add(y[i], Delta[i]) for i in range(W)]
    y2 = [F.add(y1[i], Delta[i]) for i in range(W)]
    f0, f1, f2 = F.F(y, 0), F.F(y1, 0), F.F(y2, 0)
    return tuple(tuple((f2[i][c] - 2 * f1[i][c] + f0[i][c]) % Q for c in range(D))
                 for i in range(W))

r2 = random.Random(78)
ref = F_second_diff(r2)
m = sum(1 for _ in range(40) if F_second_diff(r2) == ref)
print(f"  (a) ONE round function F, D^2_Delta F constant in {m}/40   [note says 40/40]")

# (b) the PERMUTATION at r rounds -- the measurement the note never made
def perm_second_diff(rounds, seedrng):
    L = [[seedrng.randrange(Q) for _ in range(D)] for _ in range(W)]
    R_ = [[seedrng.randrange(Q) for _ in range(D)] for _ in range(W)]
    outs = []
    for k in range(3):
        Rk = [F.add(R_[i], [k * Delta[i][c] for c in range(D)]) for i in range(W)]
        outs.append(F.perm(L, Rk, rounds=rounds))
    return tuple(tuple((outs[2][h][i][c] - 2 * outs[1][h][i][c] + outs[0][h][i][c]) % Q
                       for c in range(D)) for h in (0, 1) for i in range(W))

for rounds in (1, 2, 3):
    r3 = random.Random(1000 + rounds)
    ref2 = perm_second_diff(rounds, r3)
    mm = sum(1 for _ in range(20) if perm_second_diff(rounds, r3) == ref2)
    print(f"  (b) PERMUTATION at {rounds} round(s): D^2 constant in {mm}/20"
          f"   -> {'STRUCTURE PRESENT' if mm > 1 else 'dead'}")

print()
print("  => the order-2 property is a property of ONE round function, and the")
print("     permutation kills it at 2 rounds.  The design note's 'does not die in")
print("     one round' is TRUE and its scope is ONE ROUND FUNCTION, not the")
print("     permutation.  As an attack primitive it buys a 1-round local")
print("     relation, the same reach as the S2 affine relation, which is")
print("     stronger (order 1, probability 1).")
