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

def tables(p, prog=S.HARNESS):
    """SIG and DSIG interpolated at 0..255 = the input code u - T_LO (prog's table domain)."""
    sig = [prog.SIG[u + prog.T_LO] % p for u in range(256)]
    dsig = [prog.DSIG[u + prog.T_LO] % p for u in range(256)]
    return spdz.interpolate(sig, p), spdz.interpolate(dsig, p)

def centered(v, p):
    return v - p if v > p // 2 else v

def run_step(eng, W1, W2, x, y, tab, owner_seed, tamper=None, mv=None, ou=None, prog=S.HARNESS):
    """The protocol, identical in live and audit mode. W1, W2, x, y are PLAIN values for the owner's input
    (ignored in audit mode, which reads the owner's broadcasts from the transcript). prog: the step program
    (step_spec.Program; tab must be tables(p, prog)); the default is the harness's program, unchanged."""
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
    matvec = mv or eng.matvec        # mv: HE-assisted matvec (he_matvec.HEMatvec), same interface
    z1 = matvec(M1, sx)
    ri = getattr(eng, "rec_in", None)          # cosnark_gates.RecEngine: the middle's IO for its proof
    ro = getattr(eng, "rec_out", None)
    if ri:
        z1 = ri("z1", z1)
    u1 = [eng.trunc(z, prog.S1, prog.K1) for z in z1]
    hg = [eng.lookup2(u, -prog.T_LO, tab, 255) for u in u1]
    h = [a for a, _ in hg]
    g1 = [b for _, b in hg]
    if ro:
        ro("h", h)
        ro("g1", g1)
    if tamper == "swap_share" and not eng.audit:
        # custodian 2 substitutes its (share, MAC share) of h[0] with those of an unrelated sharing (h[1])
        h[0] = dict(h[0]); h[0][2] = h[1][2]
    z2 = matvec(M2, h)
    if ri:
        z2 = ri("z2", z2)
        sy = ri("y", sy)
    e = [eng.sub(eng.trunc(z, prog.S1, prog.K1), yy) for z, yy in zip(z2, sy)]
    d2 = [eng.trunc(v, prog.S2, prog.K2) for v in e]
    if ro:
        ro("d2", d2)
    b = matvec(M2, d2, transpose=True)
    if ri:
        b = ri("b", b)
    bg = [eng.mul(bb, g) for bb, g in zip(b, g1)]
    if ro:
        ro("bg", bg)
    bgr = [eng.cadd(prog.R3, v) for v in bg] if prog.R3 else bg     # public rounding constant (0: floor)
    d1 = [eng.trunc(v, prog.S3, prog.K3) for v in bgr]
    if ro:
        ro("d1", d1)
    outer = ou or eng.outer          # ou: HE-assisted outer product (he_outer.HEOuter), same interface
    G2 = outer(d2, h)
    G1 = outer(d1, sx)
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
