"""HE-assisted matvec for the MPC fork (decision §10): replaces SPDZ's matrix-triple matvec, which opens
W - A (d^2 values) every time, by pairwise plaintext x ciphertext products under each custodian's OWN key.

2026-11-06. For [z] = [W][v] with additive shares W = sum_i W^(i), v = sum_j v^(j):
    z = sum_i W^(i) v^(i)  (local)  +  sum_{i != j} W^(i) v^(j)  (cross terms, by HE).
For each ordered pair (i, j), i != j:
  1. j sends Enc_j(v^(j)) in the block layout, with EXACT scaling round(Q v / t). With textbook Delta v,
     the plaintext product by a full-size share W^(i) (coefficients ~2^60) multiplies the rounding error
     (Q mod t) v / t past the margin: the F2 phenomenon again.
  2. i computes sum_blocks W^(i)_block * Enc_j(v_block). That is plaintext x ciphertext only: no
     relinearization, no evaluation key, and j's key never leaves j.
     i adds round(Q M / t) for a uniform mask M on ALL N coefficients, a fresh Enc_pk_j(0) (otherwise
     W^(i) * a_j would let j divide out W^(i)), and flooding noise. It returns the result.
  3. j decrypts and keeps (W^(i) v^(j))_k + M_k at the layout's output coefficients; i keeps -M_k.
The plain shares of z are authenticated with auth_plain. Then ONE Freivalds check in SPDZ: with rho drawn
after the shares are fixed, open rho^T [z] - <rho^T [W], [v]>; it must be 0 (rho^T [W] is local,
the inner product costs d Beaver products, and the opening is MAC-checked). This catches:
  - j encrypting a vector other than its share (z = W v' while the check uses the true [v]);
  - i returning a wrong product;
  - any custodian shifting its share at authentication.
In each case the check fails unless W (v' - v) = 0, i.e. unless the result is correct anyway.
Not built: the ZKPoPK on each sent ciphertext (bounded noise and plaintext range). It protects i's share
against a malformed ciphertext from j, so it is a privacy leg, not an integrity leg. It is priced in
counts().

Block layout (as in step_counts): d_c = min(d, 64) columns by d_r = min(d, N / 64) rows per plaintext,
coefficient 64 i + j. Forward: block x rev(v-block) -> row i at 64 i + 63, summed over column blocks.
Transpose: block x colrev(e-block) -> column j at 64 (d_r - 1) + j, summed over row blocks.
"""
import math
import random

import wire_round as WR

import bfv_ref as bfv

class OwnKey:
    def __init__(self, N, Q, t, seed):
        self.sch = bfv.BFV(N, Q, t, seed=seed)
        self.sch.keygen()
        sch = self.sch
        a = sch.uniform()
        e = sch.small_error()
        as_, _ = bfv.negacyclic_mul(bfv.poly_centered(a, Q), sch.s)
        self.pk = ([(-x - ee) % Q for x, ee in zip(as_, e)], a)

    def enc_zero_pk(self, rng):
        """Fresh public-key encryption of 0 under this custodian's key (used by OTHER custodians)."""
        sch = self.sch
        Q, N = sch.Q, sch.N
        u = [rng.choice((-1, 0, 1)) for _ in range(N)]
        c0, _ = bfv.negacyclic_mul(bfv.poly_centered(self.pk[0], Q), u)
        c1, _ = bfv.negacyclic_mul(bfv.poly_centered(self.pk[1], Q), u)
        return ([(x + rng.randint(-8, 8)) % Q for x in c0], [(x + rng.randint(-8, 8)) % Q for x in c1])

def layout(d, N):
    dc = min(d, 64)
    dr = min(d, N // 64)
    return dc, dr

def ptxct(P, ct, Q):
    a, _ = bfv.negacyclic_mul(P, bfv.poly_centered(ct[0], Q))
    b, _ = bfv.negacyclic_mul(P, bfv.poly_centered(ct[1], Q))
    return [x % Q for x in a], [x % Q for x in b]

class HEMatvec:
    """Drop-in for eng.matvec(W, v, transpose) on an spdz.Engine (live mode)."""
    def __init__(self, eng, keys, N, Q, seed=11, flood_bits=40, attack=None, context=("model", 0, 0),
                 per_return_rng=False, wire=None):
        self.eng, self.keys, self.N, self.Q = eng, keys, N, Q
        self.p = eng.p
        self.seed = seed
        self.rng = random.Random(seed)
        # per_return_rng: each return's randomness (mask M, Enc_pk_j(0), flood) comes from its own stream, keyed by
        # (seed, call, transpose, returner i, recipient j, output block o). A distributed custodian draws only its own
        # returns' randomness, so it cannot share one sequential stream with the others; the native custodians
        # (native/darkstep) use this mode, and so does the bit-exact reference (native_ref.py). The default keeps the
        # single shared stream every recorded result was produced with.
        self.per_return_rng = per_return_rng
        # wire = (primes, b0, b1): returns switched to two primes and noise-rounded (wire_round.py); outputs unchanged
        self.wire_mode = wire
        self.flood_bits = flood_bits
        self.attack = attack           # (kind, party) for falsifiers
        self.context = context
        self.wire = {"he_send": 0, "he_return": 0}
        self.cts_sent = 0
        self.cts_returned = 0
        self.calls = 0

    def __call__(self, W, v, transpose=False):
        eng, p, N, Q, n = self.eng, self.p, self.N, self.Q, self.eng.n
        d = len(v)
        dc, dr = layout(d, N)
        cen = lambda x: x - p if x > p // 2 else x
        Wsh = [[[cen(W[r][c][i][0]) for c in range(d)] for r in range(d)] for i in range(n)]
        vsh = [[cen(x[i][0]) for x in v] for i in range(n)]
        self.calls += 1
        # local diagonal terms
        z = [[0] * d for _ in range(n)]
        for i in range(n):
            for r in range(d):
                if not transpose:
                    z[i][r] = sum(Wsh[i][r][c] * vsh[i][c] for c in range(d)) % p
                else:
                    z[i][r] = sum(Wsh[i][c][r] * vsh[i][c] for c in range(d)) % p
        nrb, ncb = d // dr, d // dc
        for j in range(n):
            kj = self.keys[j]
            vj = list(vsh[j])
            if self.attack == ("wrong_vector", j):
                vj[0] += 1                               # j encrypts a vector that is not its share
            # j's ciphertexts: forward one per column block (rev layout), transpose one per row block
            sent = {}
            if not transpose:
                for b in range(ncb):
                    m = [0] * N
                    for c in range(dc):
                        m[63 - c] = vj[b * dc + c] % p
                    sent[b] = kj.sch.encrypt_exact(m)
            else:
                for a in range(nrb):
                    m = [0] * N
                    for r in range(dr):
                        m[64 * (dr - 1 - r)] = vj[a * dr + r] % p
                    sent[a] = kj.sch.encrypt_exact(m)
            for i in range(n):
                if i == j:
                    continue
                self.wire["he_send"] += len(sent) * 2 * N * 3
                self.cts_sent += len(sent)
                outs = range(nrb) if not transpose else range(ncb)
                for o in outs:
                    acc = None
                    blocks = [(o, b) for b in range(ncb)] if not transpose else [(a, o) for a in range(nrb)]
                    for a, b in blocks:
                        P = [0] * N
                        for r in range(dr):
                            for c in range(dc):
                                P[64 * r + c] = Wsh[i][a * dr + r][b * dc + c]
                        prod = ptxct(P, sent[b] if not transpose else sent[a], Q)
                        acc = prod if acc is None else ([(x + y) % Q for x, y in zip(acc[0], prod[0])],
                                                        [(x + y) % Q for x, y in zip(acc[1], prod[1])])
                    rg = (random.Random(f"hm|{self.seed}|{self.calls}|{int(transpose)}|{i}|{j}|{o}")
                          if self.per_return_rng else self.rng)
                    M = [rg.randrange(p) for _ in range(N)]
                    z0 = kj.enc_zero_pk(rg)
                    F = 1 << (self.noise_bits(dr, dc) + self.flood_bits)
                    c0 = [(x + y + (2 * Q * bfv.centered(mm, p) + p) // (2 * p) + rg.randint(-F, F)) % Q
                          for x, y, mm in zip(acc[0], z0[0], M)]
                    c1 = [(x + y) % Q for x, y in zip(acc[1], z0[1])]
                    self.wire["he_return"] += 2 * N * 3
                    self.cts_returned += 1
                    dec = (WR.decrypt_wire(kj.sch, (c0, c1), *self.wire_mode) if self.wire_mode else kj.sch.decrypt((c0, c1)))
                    idx = [(64 * r + 63, o * dr + r) for r in range(dr)] if not transpose else \
                          [(64 * (dr - 1) + c, o * dc + c) for c in range(dc)]
                    for coef, out in idx:
                        z[j][out] = (z[j][out] + dec[coef]) % p
                        z[i][out] = (z[i][out] - M[coef]) % p
                        if self.attack == ("wrong_return", i) and out == 0:
                            z[i][out] = (z[i][out] + 1) % p
        # authenticate the plain shares
        zs = []
        for r in range(d):
            plain = {k: z[k][r] for k in range(n)}
            if self.attack and self.attack[0] == "shift_share" and r == 0:
                plain[self.attack[1]] = (plain[self.attack[1]] + 1) % p
            zs.append(eng.auth_plain(plain, "he_auth"))
        # Freivalds: rho after the shares are fixed (Fiat-Shamir on the transcript so far)
        rho = self.coins(d, transpose)
        lhs = eng.lin([(rho[r], zs[r]) for r in range(d)])
        if not transpose:
            u = [eng.lin([(rho[r], W[r][c]) for r in range(d)]) for c in range(d)]
        else:
            u = [eng.lin([(rho[c], W[r][c]) for c in range(d)]) for r in range(d)]
        ip = None
        for a, b in zip(u, v):
            t = eng.mul(a, b)
            ip = t if ip is None else eng.add(ip, t)
        chk = eng.open(eng.sub(lhs, ip), "freivalds")
        if chk != 0:
            import spdz
            raise spdz.Abort("HE matvec: Freivalds check failed (a custodian's vector, product or share is wrong)")
        return zs

    def noise_bits(self, dr, dc):
        # |P|_inf <= p/2, product noise ~ N * (p/2) * e: a public bound
        return (self.N * (self.p // 2) * 16 * 2).bit_length()

    def coins(self, d, transpose=False):
        """Freivalds coins bound to the WHOLE transcript so far (not a suffix), the invocation index, the
        shape and the transpose flag, plus the caller's context (model, epoch, step). Astra scholar: the
        suffix-only seed omitted context, so an older prefix could be changed without moving rho."""
        import hashlib
        h = hashlib.sha256(repr(("freivalds", self.context, self.calls, d, transpose,
                                 self.eng.transcript)).encode()).hexdigest()
        r = random.Random(int(h, 16))
        return [r.randrange(self.p) for _ in range(d)]

def counts(d, N=8192, L=3, n=3, matvecs=(False, False, True)):
    """Per step: HE wire, SPDZ wire for authentication + Freivalds, priced ZKPoPKs on sent ciphertexts."""
    dc, dr = layout(d, N)
    ct = 2 * N * L
    send = ret = 0
    for tr in matvecs:
        s, r = (d // dc, d // dr) if not tr else (d // dr, d // dc)
        send += n * (n - 1) * s
        ret += n * (n - 1) * r
    auth = len(matvecs) * d * n * (n - 1)
    frei = len(matvecs) * (2 * d + 1) * n * (n - 1)
    zk = n * (n - 1) * 0 + send            # one ZKPoPK per sent ciphertext (a broadcast could share them)
    return dict(he_send_wire=send * ct, he_return_wire=ret * ct, auth_wire=auth, freivalds_wire=frei,
                he_wire=(send + ret) * ct, spdz_wire=auth + frei, cts_sent=send, cts_returned=ret,
                zkpopk_proofs=zk, zkpopk_bits=zk * (2 * L * (N - 1) * 61 + 7 * N * 61),
                prep_auth_values=len(matvecs) * (d + 3 * d))
