"""The reference integer learner both forks must refine (F15's "single executable specification").

2026-11-06. Two dense layers, d = 64, batch 1, exact integer semantics, no floats anywhere.

    z1 = W1 x                       (|W| <= 7, |x| <= 7: |z1| <= 64*49 = 3136)
    u1 = floor(z1 / 2^S1)           (S1 = 5: |u1| <= 98, a table index)
    h  = SIG[u1], g1 = DSIG[u1]     (one table, two columns keyed on the INPUT code: F2)
    z2 = W2 h                       (|h| <= 7)
    e  = floor(z2 / 2^S1) - y       (|e| <= 98 + 7)
    d2 = floor(e / 2^S2)            (S2 = 4: |d2| <= 7)
    b  = W2^T d2                    (old W2)
    d1 = floor((b * g1) / 2^S3)     (S3 = 8: |b g1| <= 64*7*7 = 3136, so |d1| <= 13)
    W2 <- W2 - d2 (x) h,  W1 <- W1 - d1 (x) x      (factor-quantized integer update: exact)

Bounds are asserted on every call so a refinement claim can name them. The weights are not clipped:
one step from |W| <= 7 stays bounded by the stated sum; long runs need F1's wrap ledger.
"""
D = 64
S1, S2, S3 = 5, 4, 8

def sig(u):
    """Integer hard-sigmoid-like activation on the requantized code u in [-128, 128)."""
    return max(-7, min(7, u // 4))

def dsig(u):
    return 1 if -28 <= u < 32 else 0

SIG = {u: sig(u) for u in range(-128, 128)}
DSIG = {u: dsig(u) for u in range(-128, 128)}


class Program:
    """The step program as parameters (genesis pins one). The defaults are the harness's program above, and
    step(W1, W2, x, y) with the default is the function it always was (same assertions, same outputs).

    S1, K1   z1 and z2 truncated by 2^S1; the MPC's statistical truncation needs |v| < 2^K1
    S2, K2   e truncated by 2^S2, |e| < 2^K2
    S3, K3   b * g1 + R3 truncated by 2^S3, |b * g1 + R3| < 2^K3
    R3       public constant added to b * g1 before its truncation (2^(S3-1): round half up; 0: floor)
    T_LO     the table's domain is [T_LO, T_LO + 256); u1 must land in it (the lookup interpolates there)
    XMAX     |x| <= XMAX asserted
    WMAX     |W| <= WMAX asserted at entry; None: weights unbounded (a training run), and every truncation's
             input bound above is asserted instead (CHECK_K is then forced on)
    CHECK_K  assert the truncation input bounds (off in the harness default, whose assertions predate them)
    """
    FIELDS = ("S1", "K1", "S2", "K2", "S3", "K3", "R3", "T_LO", "XMAX", "WMAX", "CHECK_K")

    def __init__(self, S1=S1, K1=13, S2=S2, K2=8, S3=S3, K3=13, R3=0, T_LO=-128, XMAX=7, WMAX=7, CHECK_K=False):
        self.S1, self.K1, self.S2, self.K2, self.S3, self.K3, self.R3 = S1, K1, S2, K2, S3, K3, R3
        self.T_LO, self.XMAX, self.WMAX, self.CHECK_K = T_LO, XMAX, WMAX, CHECK_K or WMAX is None
        self.SIG = {u: sig(u) for u in range(T_LO, T_LO + 256)}
        self.DSIG = {u: dsig(u) for u in range(T_LO, T_LO + 256)}

    def intervals(self):
        """Each truncation input's interval [a, a + 2^B) as {name: (a, B)}: the MPC's statistical truncation needs
        -2^K <= v < 2^K; z1's is also cut to the table's domain (u1 = z1 >> S1 in [T_LO, T_LO + 256)). The proof
        proves these and the ledger refuses a step outside them."""
        lo = max(-(1 << self.K1), self.T_LO << self.S1)
        hi = min(1 << self.K1, (self.T_LO + 256) << self.S1)
        B = (hi - lo).bit_length() - 1
        assert hi - lo == 1 << B, "z1's interval must have power-of-two width"
        return {"z1": (lo, B), "z2": (-(1 << self.K1), self.K1 + 1), "e": (-(1 << self.K2), self.K2 + 1),
                "bg": (-(1 << self.K3), self.K3 + 1)}

    def as_dict(self):
        return {k: getattr(self, k) for k in self.FIELDS}

    def __eq__(self, o):
        return isinstance(o, Program) and self.as_dict() == o.as_dict()

    def __repr__(self):
        return "Program(%s)" % ", ".join("%s=%r" % kv for kv in self.as_dict().items())


HARNESS = Program()
# Gen 6's pinned program at d = 4096 (notes/dark-learning-gen6/train.md; genesis train_genesis_gen6.json):
# z1, z2 >> 11 with |.| < 2^19, e >> 7 with |e| < 2^8, round(b g1 / 2^8) with |b g1 + 2^7| < 2^19, weights unbounded.
GEN6 = Program(S1=11, K1=19, S2=7, K2=8, S3=8, K3=19, R3=1 << 7, WMAX=None)


class Init:
    """Seeded initial weights: r = random.Random(seed); W1[j][k] = r.randint(-a1, a1) for j < hid, k < nin
    (row-major), then W2[i][j] = r.randint(-a2, a2) for i < nout, j < hid; every other entry 0; a = 0 draws nothing.
    The zero rows and columns stay zero under the step (a hidden unit with a zero W1 row and W2 column has h = 0 and
    b = 0; an output row with zero weights and target 0 has d2 = 0)."""

    def __init__(self, seed, a1, a2, nin, hid, nout):
        self.seed, self.a1, self.a2, self.nin, self.hid, self.nout = seed, a1, a2, nin, hid, nout

    def weights(self, d):
        import random
        r = random.Random(self.seed)
        W1 = [[0] * d for _ in range(d)]
        W2 = [[0] * d for _ in range(d)]
        if self.a1 > 0:
            for j in range(self.hid):
                row = W1[j]
                for k in range(self.nin):
                    row[k] = r.randint(-self.a1, self.a1)
        if self.a2 > 0:
            for i in range(self.nout):
                row = W2[i]
                for j in range(self.hid):
                    row[j] = r.randint(-self.a2, self.a2)
        return W1, W2


def matvec(W, v):
    return [sum(W[i][j] * v[j] for j in range(len(v))) for i in range(len(W))]

def matTvec(W, v):
    return [sum(W[i][j] * v[i] for i in range(len(W))) for j in range(len(W[0]))]

def outer(a, b):
    return [[ai * bj for bj in b] for ai in a]

def fdiv(x, s):
    return x >> s          # Python >> is floor division by 2^s for negative ints too

def step(W1, W2, x, y, prog=HARNESS):
    P = prog
    assert all(abs(v) <= P.XMAX for v in x)
    if P.WMAX is not None:
        assert all(abs(w) <= P.WMAX for r in W1 + W2 for w in r)
    z1 = matvec(W1, x)
    u1 = [fdiv(z, P.S1) for z in z1]
    assert all(P.T_LO <= u < P.T_LO + 256 for u in u1)
    h = [P.SIG[u] for u in u1]
    g1 = [P.DSIG[u] for u in u1]
    z2 = matvec(W2, h)
    e = [fdiv(z, P.S1) - yy for z, yy in zip(z2, y)]
    d2 = [fdiv(v, P.S2) for v in e]
    b = matTvec(W2, d2)
    bg = [bb * g + P.R3 for bb, g in zip(b, g1)]
    if P.CHECK_K:
        iv = P.intervals()
        inside = lambda vs, k: all(iv[k][0] <= v < iv[k][0] + (1 << iv[k][1]) for v in vs)
        assert inside(z1, "z1") and inside(z2, "z2"), "z1/z2 outside the truncation bound [-2^K1, 2^K1)"
        assert inside(e, "e"), "e outside [-2^K2, 2^K2)"
        assert inside(bg, "bg"), "b*g1 + R3 outside [-2^K3, 2^K3)"
    d1 = [fdiv(v, P.S3) for v in bg]
    G2 = outer(d2, h)
    G1 = outer(d1, x)
    W2n = [[W2[i][j] - G2[i][j] for j in range(len(W2[0]))] for i in range(len(W2))]
    W1n = [[W1[i][j] - G1[i][j] for j in range(len(W1[0]))] for i in range(len(W1))]
    trace = dict(z1=z1, u1=u1, h=h, g1=g1, z2=z2, e=e, d2=d2, b=b, d1=d1)
    return W1n, W2n, trace
