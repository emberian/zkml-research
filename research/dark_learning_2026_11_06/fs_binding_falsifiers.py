"""Falsifiers for the Fiat-Shamir binding of the two explicit verifiers (Astra experiment-1 audit, E5).

Before this fix, the identity checks in cert_b61.verify (tensor identity (3)) and e2s_proof.verify
(R_PD) evaluated at a point derived from PUBLIC data only. The quotient polynomial is a free witness,
so a prover who computes the point first can pick the quotient afterwards and pass a FALSE statement:
  F-cert  a wrong ct x ct output (component 0 at one coefficient shifted by about Delta, so the product
          DECRYPTS to a different message; z, s, y re-derived consistently);
  F-pd    a partial decryption with an offset of 5 Delta.
Each must be ACCEPTED by the legacy verifier (the hole is real) and REFUSED by the fixed one, whose point
also depends on a hash of the witness (the commitment roots in the succinct form). N = 256, seconds.
"""
import math
import random
import sys

import bfv_ref as bfv
import cert_b61 as C
import e2s_proof as P
import fhe_fork as FF

def forge_cert(sch, Qp, Bp, ct1, ct2):
    Q, t, N = sch.Q, sch.t, sch.N
    out, w = C.build(sch, Qp, Bp, ct1, ct2)
    QB, BB = C.Basis(Qp), C.Basis(Bp)
    k, j = 0, 7
    d, _, _ = sch.tensor_lifted(ct1, ct2)
    z = d[k][j]
    z2 = z + -(-(Q // t) * Q // t)                  # y' = y + about Delta: one plaintext unit at X^j
    y2, s2 = divmod(t * z2 + Q // 2, Q)
    for p in Qp + Bp:
        w["z_res"][k][p][j] = z2 % p
    w["ext_s"][k][j] = QB.extend_witness(s2, centered=False)
    w["ext_y"][k][j] = BB.extend_witness(y2)
    out = [list(c) for c in out]
    out[k][j] = y2 % Q
    h1, h2, ho = C.handle(ct1, Qp), C.handle(ct2, Qp), C.handle(out, Qp)
    # adapt K's constant coefficient so identity (3) holds at the point the LEGACY verifier will use
    ins = [bfv.poly_centered(c, Q) for c in (ct1[0], ct1[1], ct2[0], ct2[1])]
    pairs = [[(0, 2)], [(0, 3), (1, 2)], [(1, 3)]][k]   # (a0 b0), (a0 b1 + a1 b0), (a1 b1)
    for p in Qp + Bp:
        r = C.fs_point(f"{h1}{h2}{ho}{k}{p}", p)
        res = lambda i: [c % p for c in ins[i]] if p in Qp else [
            (sum(vi * (hh % p) for vi, hh in zip(v, QB.hat)) - u * (QB.M % p)) % p for v, u in w["ext_in"][i]]
        lhs = sum(C.evalp(res(a), r, p) * C.evalp(res(b), r, p) for a, b in pairs) % p
        rhs = (C.evalp(w["z_res"][k][p], r, p) + (pow(r, N, p) + 1) * C.evalp(w["K_res"][k][p], r, p)) % p
        w["K_res"][k][p][0] = (w["K_res"][k][p][0] + (lhs - rhs) * pow(pow(r, N, p) + 1, -1, p)) % p
    return h1, h2, ho, out, w

def forge_pd(sch, Qp, cust, ct, tag):
    Q, N = sch.Q, sch.N
    e = [0] * N
    p, w = P.prove(sch, Qp, cust.s_sh[1], cust.s2_sh[1], ct, e)
    p[3] = (p[3] + sch.delta * 5) % Q
    h = P.ct_handle(ct, Q)
    for q in Qp:
        r = P.pd_point(tag, h, None, q, legacy_fs=True)
        lhs = C.evalp([x % q for x in p], r, q)
        rhs = (C.evalp([x % q for x in w["s"]], r, q) * C.evalp([x % q for x in ct[1]], r, q)
               + C.evalp([x % q for x in w["e"]], r, q) - (pow(r, N, q) + 1) * C.evalp(w["k"][q], r, q))
        w["k"][q][0] = (w["k"][q][0] - (lhs - rhs) * pow(pow(r, N, q) + 1, -1, q)) % q
    return p, w

def main(N=256):
    sch, Qp, Bp, t = FF.setup(N=N)
    cust = FF.Custodians(sch, 3, 5, Qp)
    rng = random.Random(1)
    m1 = [rng.randint(-7, 7) % t for _ in range(N)]
    m2 = [rng.randint(-7, 7) % t for _ in range(N)]
    c1, c2 = sch.encrypt(m1), sch.encrypt(m2)
    ok = True
    h1, h2, ho, out, w = forge_cert(sch, Qp, Bp, c1, c2)
    legacy = C.verify(sch, Qp, Bp, h1, h2, ho, out, w, legacy_fs=True)
    fixed = C.verify(sch, Qp, Bp, h1, h2, ho, out, w)
    wrong = sch.decrypt(out) != sch.decrypt(C.build(sch, Qp, Bp, c1, c2)[0])
    print(f"F-cert  output wrong: {wrong}; legacy verifier: {legacy}; fixed verifier: {fixed}")
    ok &= wrong and legacy[0] and not fixed[0]
    p, w = forge_pd(sch, Qp, cust, c1, "x")
    legacy = P.verify(sch, Qp, c1, p, cust.K[1], w, cust.E, "x", legacy_fs=True)
    fixed = P.verify(sch, Qp, c1, p, cust.K[1], w, cust.E, "x")
    print(f"F-pd    offset 5 Delta; legacy verifier: {legacy}; fixed verifier: {fixed}")
    ok &= legacy[0] and not fixed[0]
    print("FS BINDING FALSIFIERS", "PASS" if ok else "FAIL")
    return ok

if __name__ == "__main__":
    sys.exit(0 if main() else 1)
