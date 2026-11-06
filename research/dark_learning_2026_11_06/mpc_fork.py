"""MPC fork of the d = 64 dark training step: SPDZ shares among n custodians, the whole step in MPC.

2026-11-06. Custodians hold authenticated shares of W1, W2; the data owner inputs x, y as shares. The host
holds only commitments (per-party view hashes) and the public transcript of masked openings: it never holds
an evaluation object for the mind (P3, scheme decision §3). Every step ends with the batched MAC check
(the envelope: every step, not sampled). The audit opens n-1 of n committed views and re-executes them
against the public transcript (MPC-in-the-head over the real MPC).
"""
import random

import spdz
import step_spec as S

def tables(p):
    sig = [S.SIG[u - 128] % p for u in range(256)]
    dsig = [S.DSIG[u - 128] % p for u in range(256)]
    return spdz.interpolate(sig, p), spdz.interpolate(dsig, p)

def centered(v, p):
    return v - p if v > p // 2 else v

def run_step(eng, W1, W2, x, y, tab, owner_seed, tamper=None):
    """The protocol, identical in live and audit mode. W1, W2, x, y are PLAIN values for the owner's input
    (ignored in audit mode, which reads the owner's broadcasts from the transcript)."""
    d = len(x)
    orng = random.Random(owner_seed)
    flat = lambda M: [v for r in M for v in r]
    sW1 = eng.input(flat(W1) if W1 else [0] * d * d, orng, "input")
    sW2 = eng.input(flat(W2) if W2 else [0] * d * d, orng, "input")
    sx = eng.input(x if x else [0] * d, orng, "input")
    sy = eng.input(y if y else [0] * d, orng, "input")
    eng.parent = [hash_shares(sW1 + sW2, i) for i in eng.active]
    M1 = [sW1[i * d:(i + 1) * d] for i in range(d)]
    M2 = [sW2[i * d:(i + 1) * d] for i in range(d)]
    z1 = eng.matvec(M1, sx)
    u1 = [eng.trunc(z, S.S1, 13) for z in z1]
    hg = [eng.lookup2(u, 128, tab, 255) for u in u1]
    h = [a for a, _ in hg]
    g1 = [b for _, b in hg]
    if tamper == "swap_share" and not eng.audit:
        # custodian 2 substitutes its (share, MAC share) of h[0] with those of an unrelated sharing (h[1])
        h[0] = dict(h[0]); h[0][2] = h[1][2]
    z2 = eng.matvec(M2, h)
    e = [eng.sub(eng.trunc(z, S.S1, 13), yy) for z, yy in zip(z2, sy)]
    d2 = [eng.trunc(v, S.S2, 8) for v in e]
    b = eng.matvec(M2, d2, transpose=True)
    bg = [eng.mul(bb, g) for bb, g in zip(b, g1)]
    d1 = [eng.trunc(v, S.S3, 13) for v in bg]
    G2 = eng.outer(d2, h)
    G1 = eng.outer(d1, sx)
    W2n = [[eng.sub(M2[i][j], G2[i][j]) for j in range(d)] for i in range(d)]
    W1n = [[eng.sub(M1[i][j], G1[i][j]) for j in range(d)] for i in range(d)]
    return W1n, W2n, dict(h=h, d2=d2, d1=d1, x=sx, y=sy, z1=z1, z2=z2, b=b, g1=g1, bg=bg, W1=M1, W2=M2)

def reveal(eng, X):
    """Test-only reconstruction (NOT part of the protocol): sum all parties' shares."""
    p = eng.p
    return centered(sum(X[i][0] for i in range(eng.n)) % p, p)

def hash_shares(xs, i):
    import hashlib
    m = hashlib.sha256()
    for x in xs:
        m.update(repr(x[i]).encode())
    return m.hexdigest()
