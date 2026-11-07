"""HE-assisted outer product for the MPC fork (scheme decision §14): replaces SPDZ's outer-product tuples
([u], [w], [u w^T], d^2 correlated products each) by pairwise plaintext x ciphertext products under each
custodian's OWN BFV key, as he_matvec does for the matvec.

2026-11-06. For [G] = [a] (x) [x], with a = sum_i a^(i), x = sum_j x^(j) and MAC shares m^(i)(a), sum_i m^(i)(a) =
alpha a:
    G        = sum_i a^(i) x^(i)T     (local)  +  sum_{i != j} a^(i) x^(j)T     (cross terms, by HE)
    alpha G  = sum_i m^(i)(a) x^(i)T  (local)  +  sum_{i != j} m^(i)(a) x^(j)T  (the same exchange)
So the MAC shares of G come out of the SAME exchange, run on i's MAC shares of a: no auth_plain of the d^2
outputs. Under MASCOT that would cost d^2 jointly hidden masks (about 0.76 Tbit at d = 4096).

Packing (coefficient encoding; one block is dr rows x dc columns, dc = min(d2, 64), dr = min(d1, N / 64)):
  j sends    Enc_j(H_b),  H_b(X) = sum_c x^(j)_{b dc + c} X^c           (one ciphertext per column block)
  i returns  D_a(X) * Enc_j(H_b) and D'_a(X) * Enc_j(H_b), with D_a(X) = sum_r a^(i)_{a dr + r} X^(64 r)
             and D' the same with i's MAC shares; coefficient 64 r + c holds a_r x_c with no wrap
  Each return adds round(Q M / t) for a uniform mask M on all N coefficients, a fresh Enc_pk_j(0) and flooding
  noise (the he_matvec recipe). j keeps the decryption, and i keeps -M.

Integrity: each custodian broadcasts a hash of its (G, MAC) share matrices. Then, with coins (rho1, rho2)
drawn from the transcript, ONE SPDZ check opens rho1^T [G] rho2 - [rho1 . a] [x . rho2]; it must be 0. That is
one Beaver product, and the opening is MAC-checked. Refused:
  - j encrypts x' != x^(j):  the check value is (rho1 . a)((x' - x^(j)) . rho2), nonzero unless a = 0 (then G = 0
    is correct anyway);
  - i returns a wrong G cross term E:  rho1^T E rho2 != 0, except with probability 2/p;
  - i returns a wrong MAC cross term only:  the check value is 0, but its MAC is off by rho1^T E' rho2, so the
    batched MAC check fails;
  - a custodian shifts its share before committing:  as for a wrong G term.
Full collusion (all n, alpha known) passes every one of these checks by construction. That case is the
collaborative proof's job: the spine's zero-round rank-1 check is on W' = W - d (x) h over the committed vectors,
whatever produced G (run_he_outer.py shows it).

Not built: the ZKPoPK on each sent ciphertext (a privacy leg for i, priced as in he_matvec), and
whole-ciphertext circuit privacy. The Astra scholar refuted the first-component flood for he_matvec, and it
applies here unchanged.
"""
import hashlib
import random

import bfv_ref as bfv
import he_matvec as HM
import spdz

def layout(d1, d2, N):
    return min(d2, 64), min(d1, N // 64)

class HEOuter:
    """Drop-in for eng.outer(a, x) on an spdz.Engine (live mode)."""
    def __init__(self, eng, keys, N, Q, seed=13, flood_bits=40, attack=None, context=("model", 0, 0),
                 per_return_rng=False):
        self.eng, self.keys, self.N, self.Q = eng, keys, N, Q
        self.p = eng.p
        self.seed = seed
        self.rng = random.Random(seed)
        self.per_return_rng = per_return_rng   # as he_matvec.HEMatvec: one stream per return, for distributed custodians
        self.flood_bits = flood_bits
        self.attack = attack           # (kind, party)
        self.context = context
        self.wire = {"he_send": 0, "he_return": 0, "commit": 0}
        self.cts_sent = self.cts_returned = self.calls = 0

    def _return(self, kj, P, ct, j_mask, key=None):
        """i's reply: P * ct + round(Q M / t) + Enc_pk_j(0) + flood; returns (ciphertext, M). key = (i, j, ab, b, kind)
        names the return's own stream in per_return_rng mode."""
        Q, N, p = self.Q, self.N, self.p
        rg = (random.Random("ho|%d|%d|%d|%d|%d|%d|%s" % ((self.seed, self.calls) + tuple(key)))
              if self.per_return_rng else self.rng)
        acc = HM.ptxct(P, ct, Q)
        M = [rg.randrange(p) for _ in range(N)]
        z0 = kj.enc_zero_pk(rg)
        F = 1 << ((N * (p // 2) * 16 * 2).bit_length() + self.flood_bits)
        c0 = [(x + y + (2 * Q * bfv.centered(mm, p) + p) // (2 * p) + rg.randint(-F, F)) % Q
              for x, y, mm in zip(acc[0], z0[0], M)]
        c1 = [(x + y) % Q for x, y in zip(acc[1], z0[1])]
        self.wire["he_return"] += 2 * N * 3
        self.cts_returned += 1
        return (c0, c1), M

    def __call__(self, a, x):
        eng, p, N, n = self.eng, self.p, self.N, self.eng.n
        d1, d2 = len(a), len(x)
        dc, dr = layout(d1, d2, N)
        cen = lambda v: v - p if v > p // 2 else v
        A = [[cen(v[i][0]) for v in a] for i in range(n)]          # value shares of a, per party
        Am = [[cen(v[i][1]) for v in a] for i in range(n)]         # MAC shares of a
        X = [[cen(v[j][0]) for v in x] for j in range(n)]
        self.calls += 1
        G = [[[A[i][r] * X[i][c] % p for c in range(d2)] for r in range(d1)] for i in range(n)]
        Gm = [[[Am[i][r] * X[i][c] % p for c in range(d2)] for r in range(d1)] for i in range(n)]
        for j in range(n):
            kj = self.keys[j]
            xj = list(X[j])
            if self.attack == ("wrong_vector", j):
                xj[0] += 1
            sent = {}
            for b in range(d2 // dc):
                m = [0] * N
                for c in range(dc):
                    m[c] = xj[b * dc + c] % p
                sent[b] = kj.sch.encrypt_exact(m)
            for i in range(n):
                if i == j:
                    continue
                self.wire["he_send"] += len(sent) * 2 * N * 3
                self.cts_sent += len(sent)
                for ab in range(d1 // dr):
                    D = [0] * N
                    Dm = [0] * N
                    for r in range(dr):
                        D[64 * r] = A[i][ab * dr + r]
                        Dm[64 * r] = Am[i][ab * dr + r]
                    for b in range(d2 // dc):
                        for P, tgt, kind in ((D, G, "val"), (Dm, Gm, "mac")):
                            ct, M = self._return(kj, P, sent[b], None, key=(i, j, ab, b, kind))
                            dec = kj.sch.decrypt(ct)
                            for r in range(dr):
                                for c in range(dc):
                                    k = 64 * r + c
                                    R, C = ab * dr + r, b * dc + c
                                    tgt[j][R][C] = (tgt[j][R][C] + dec[k]) % p
                                    tgt[i][R][C] = (tgt[i][R][C] - M[k]) % p
                            if self.attack == ("wrong_return", i) and kind == "val":
                                tgt[i][ab * dr][b * dc] = (tgt[i][ab * dr][b * dc] + 1) % p
                            if self.attack == ("wrong_mac_return", i) and kind == "mac":
                                tgt[i][ab * dr][b * dc] = (tgt[i][ab * dr][b * dc] + 1) % p
        if self.attack and self.attack[0] == "shift_share":
            k = self.attack[1]
            G[k][0][0] = (G[k][0][0] + 1) % p
        if self.attack and self.attack[0] == "collude":
            # all n custodians agree on G[0][0] + 1, with the consistent MAC (they know alpha)
            G[0][0][0] = (G[0][0][0] + 1) % p
            Gm[0][0][0] = (Gm[0][0][0] + eng.dealer.alpha) % p
        out = [[{i: (G[i][r][c], Gm[i][r][c]) for i in range(n)} for c in range(d2)] for r in range(d1)]
        # commit, then coins from the transcript (which now holds every custodian's commitment)
        com = {i: hashlib.sha256(repr((G[i], Gm[i])).encode()).hexdigest() for i in range(n)}
        eng.transcript.append(("he_outer_commit", com, 0))
        self.wire["commit"] += n * (n - 1) * 5          # a 256-bit hash is 5 field elements of wire
        h = hashlib.sha256(repr(("he_outer", self.context, self.calls, d1, d2, eng.transcript)).encode()).hexdigest()
        rr = random.Random(int(h, 16))
        r1 = [rr.randrange(p) for _ in range(d1)]
        r2 = [rr.randrange(p) for _ in range(d2)]
        lhs = eng.lin([(r1[r] * r2[c] % p, out[r][c]) for r in range(d1) for c in range(d2)])
        ra = eng.lin([(r1[r], a[r]) for r in range(d1)])
        xr = eng.lin([(r2[c], x[c]) for c in range(d2)])
        chk = eng.sub(lhs, eng.mul(ra, xr))
        if self.attack and self.attack[0] == "collude":
            # the colluders also broadcast a consistent forged opening: shift the value and its MAC to read 0
            v = sum(chk[i][0] for i in range(n)) % p
            chk = dict(chk); s, mm = chk[0]
            chk[0] = ((s - v) % p, (mm - eng.dealer.alpha * v) % p)
        if eng.open(chk, "he_outer_check") != 0:
            raise spdz.Abort("HE outer: Freivalds check failed (a custodian's vector, product or share is wrong)")
        return out

def counts(d, N=8192, L=3, n=3, outers=2):
    """Per step: HE wire (send + value and MAC returns), commitment and check wire, preprocessing, ZKPoPKs."""
    dc, dr = layout(d, d, N)
    ct = 2 * N * L
    send = outers * n * (n - 1) * (d // dc)
    ret = outers * n * (n - 1) * 2 * (d // dr) * (d // dc)
    commit = outers * n * (n - 1) * 5
    check = outers * 3 * n * (n - 1)                      # one Beaver product (2 openings) + the check opening
    return dict(cts_sent=send, cts_returned=ret, he_send_wire=send * ct, he_return_wire=ret * ct,
                he_wire=(send + ret) * ct, commit_wire=commit, check_wire=check,
                spdz_wire=commit + check, prep_auth_values=outers * 3,
                replaces_spdz_outer_wire=outers * 2 * d * n * (n - 1),
                replaces_prep_auth_values=outers * (2 * d + d * d),
                zkpopk_proofs=send, zkpopk_bits=send * (2 * L * (N - 1) * 61 + 7 * N * 61))
