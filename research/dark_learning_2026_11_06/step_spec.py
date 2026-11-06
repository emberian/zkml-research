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

def matvec(W, v):
    return [sum(W[i][j] * v[j] for j in range(len(v))) for i in range(len(W))]

def matTvec(W, v):
    return [sum(W[i][j] * v[i] for i in range(len(W))) for j in range(len(W[0]))]

def outer(a, b):
    return [[ai * bj for bj in b] for ai in a]

def fdiv(x, s):
    return x >> s          # Python >> is floor division by 2^s for negative ints too

def step(W1, W2, x, y):
    assert all(abs(v) <= 7 for v in x) and all(abs(w) <= 7 for r in W1 + W2 for w in r)
    z1 = matvec(W1, x)
    u1 = [fdiv(z, S1) for z in z1]
    assert all(-128 <= u < 128 for u in u1)
    h = [SIG[u] for u in u1]
    g1 = [DSIG[u] for u in u1]
    z2 = matvec(W2, h)
    e = [fdiv(z, S1) - yy for z, yy in zip(z2, y)]
    d2 = [fdiv(v, S2) for v in e]
    b = matTvec(W2, d2)
    d1 = [fdiv(bb * g, S3) for bb, g in zip(b, g1)]
    G2 = outer(d2, h)
    G1 = outer(d1, x)
    W2n = [[W2[i][j] - G2[i][j] for j in range(len(W2[0]))] for i in range(len(W2))]
    W1n = [[W1[i][j] - G1[i][j] for j in range(len(W1[0]))] for i in range(len(W1))]
    trace = dict(z1=z1, u1=u1, h=h, g1=g1, z2=z2, e=e, d2=d2, b=b, d1=d1)
    return W1n, W2n, trace
