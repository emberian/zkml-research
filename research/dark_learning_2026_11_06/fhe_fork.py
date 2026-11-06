"""FHE fork of the d = 64 dark training step (scheme decision §2): host computes matvecs on ciphertexts and
proves each ct x ct with the B61 certificate; custodians gate every partial decryption on that proof, run
the nonlinearity / requantization / rank-1 update on SPDZ shares (same engine as the MPC fork), and return
fresh ciphertexts.

Parameters: N = 8192; Q = three ~61-bit NTT-friendly primes; plaintext modulus t = the SPDZ field prime
(a fourth ~61-bit prime), so encryption-to-shares lands directly in F_t = the MPC field; extension basis B
sized from the bounds. Layouts (coefficient encoding, d = 64, no negacyclic wrap since 64*63+63+63 < N):
  W row-major: W(X) = sum W[i][j] X^(64 i + j)
  forward:  W(X) * rev(v)(X),   rev(v) = sum v_j X^(63 - j)        ->  (W v)_i at coefficient 64 i + 63
  backward: W(X) * colrev(e)(X), colrev(e) = sum e_i X^(64 (63 - i)) ->  (W^T e)_j at coefficient 4032 + j
No relinearization: every ct x ct output (3 components) goes straight into a crossing, a masked public
decryption with shares of (1, s, s^2) and a proof per custodian that its partial decryption is well formed
(e2s_proof.py). Shares-to-encryption is a masked public encryption opened through SPDZ. The rank-1 update is computed by the custodians on shares and re-encrypted
(the alternative, a homomorphic outer product, would need relinearization and its own certificate).
"""
import hashlib
import math
import random

import bfv_ref as bfv
import cert_b61 as C
import e2s_proof as P
import spdz
import step_spec as S

D = 64

def setup(N=8192, seed=21):
    Qp = bfv.ntt_primes(61, 3, 2 * N)
    t = bfv.ntt_primes(61, 4, 2 * N)[3]
    Q = math.prod(Qp)
    zb = 2 * Q.bit_length() + N.bit_length() + 2
    yb = zb + t.bit_length() - Q.bit_length() + 2
    Bp = bfv.ntt_primes(61, math.ceil(max(yb, zb - Q.bit_length() + 1) / 60), 2 * N, exclude=set(Qp + [t]))
    sch = bfv.BFV(N, Q, t, seed=seed)
    return sch, Qp, Bp, t

def enc_layout(sch, vals_by_coef):
    m = [0] * sch.N
    for k, v in vals_by_coef.items():
        m[k] = v % sch.t
    return sch.encrypt(m)

def row_major(W):
    return {64 * i + j: W[i][j] for i in range(D) for j in range(D)}

def rev(v):
    return {63 - j: v[j] for j in range(D)}

def colrev(e):
    return {64 * (63 - i): e[i] for i in range(D)}

class Custodians:
    """n custodians holding additive shares s_i of the BFV secret and shares of s^2 (ideal keygen), with a
    long-term commitment K_i to (s_i, s2_i). Crossings are masked public decryption / encryption
    (`e2s_proof.py`): no custodian holds a private plain share at any point."""
    def __init__(self, sch, n, seed, Qp):
        self.sch, self.n, self.Qp = sch, n, Qp
        rng = random.Random(seed)
        self.s_sh = [sch.ternary() for _ in range(n)]
        sch.s = [sum(c) for c in zip(*self.s_sh)]
        s2, _ = bfv.negacyclic_mul(sch.s, sch.s)
        parts = [[rng.randrange(-(1 << 20), 1 << 20) for _ in range(sch.N)] for _ in range(n - 1)]
        parts.append([a - sum(c) for a, c in zip(s2, zip(*parts))])
        self.s2_sh = parts
        self.K = [P.key_commit(a, b) for a, b in zip(self.s_sh, self.s2_sh)]
        # public smudging bound: as wide as the decryption margin allows (Q / 2t shared by n smudges + noise)
        self.E = (sch.Q // (2 * sch.t)) // (8 * n)
        self.rng = rng
        self.wire = {}
        self.pd = dict(proofs=0, elems=0, bits=0, range_lookups=0, openings=0)
        self.prep_ct = 0           # preprocessing ciphertexts (mask pairs), in Z_q elements
        self.noise_bits = []       # measured noise of each designated ct before smudging (for the ratio)

    def count(self, phase, k):
        self.wire[phase] = self.wire.get(phase, 0) + k

    def _mask_pair(self, eng, coefs, full, tag):
        sch, t, N = self.sch, self.sch.t, self.sch.N
        R = [self.rng.randrange(t) for _ in range(N)] if full else [0] * N
        if not full:
            for k in coefs:
                R[k] = self.rng.randrange(t)
        sh = [eng.prep(tag, lambda v=R[k]: v) for k in coefs]
        self.prep_ct += 2 * N * len(self.Qp)
        return sch.encrypt_exact(R), sh

    def e2s(self, eng, ct, coefs, tag, attack=None, alt=None):
        """Masked public decryption of the DESIGNATED ct at `coefs`; returns authenticated SPDZ shares."""
        sch, Qp = self.sch, self.Qp
        Q, t, N, L = sch.Q, sch.t, sch.N, len(Qp)
        cR, Rsh = self._mask_pair(eng, coefs, True, "e2s-mask")
        def masked(c):
            out = [[(u - v) % Q for u, v in zip(c[0], cR[0])], [(u - v) % Q for u, v in zip(c[1], cR[1])]]
            return tuple(out + ([list(c[2])] if len(c) == 3 else []))
        ctm = masked(ct)
        acc = list(ctm[0])
        noiseless = list(ctm[0])
        for i in range(self.n):
            e = [self.rng.randrange(-self.E, self.E + 1) for _ in range(N)]
            src = masked(alt) if (attack == "unrelated_boundary_shares" and i == 1 and alt is not None) else ctm
            if attack == "offset_in_error" and i == 1:
                e[coefs[0]] += sch.delta * 5          # an offset of 5 in the plaintext, hidden in the error
            p, w = P.prove(sch, Qp, self.s_sh[i], self.s2_sh[i], src, e)
            if attack == "offset_partial" and i == 1:
                p[coefs[0]] = (p[coefs[0]] + sch.delta * 5) % Q
            c = P.counts(N, Qp, self.E, len(ct))
            self.pd["proofs"] += 1
            for k in ("elems", "bits", "range_lookups", "openings"):
                self.pd[k] += c["pd_" + k]
            self.count("E2S", N * L)
            ok, why = P.verify(sch, Qp, ctm, p, self.K[i], w, self.E, tag)
            if not ok:
                raise spdz.Abort(f"partial decryption of {tag} refused (custodian {i}): {why}")
            acc = [(u + v) % Q for u, v in zip(acc, p)]
            q0, _ = P.partial(sch, self.s_sh[i], self.s2_sh[i], ctm, [0] * N)
            noiseless = [(u + v) % Q for u, v in zip(noiseless, q0)]
        v = [((t * bfv.centered(x, Q) * 2 + Q) // (2 * Q)) % t for x in acc]
        v0 = [((t * bfv.centered(x, Q) * 2 + Q) // (2 * Q)) % t for x in noiseless]
        nz = max(abs(bfv.centered(x - (2 * Q * bfv.centered(m, t) + t) // (2 * t), Q)) for x, m in zip(noiseless, v0))
        self.noise_bits.append((tag, nz.bit_length()))
        return [eng.cadd(v[k], r) for k, r in zip(coefs, Rsh)]

    def s2e(self, eng, vals_by_coef):
        """Masked public encryption: open m - R' through SPDZ (MAC checked), add it to Enc_exact(R')."""
        sch = self.sch
        Q, t = sch.Q, sch.t
        coefs = list(vals_by_coef)
        cR, Rsh = self._mask_pair(eng, coefs, False, "s2e-mask")
        c0 = list(cR[0])
        for k, r in zip(coefs, Rsh):
            v = eng.open(eng.sub(vals_by_coef[k], r), "S2E")
            c0[k] = (c0[k] + (2 * Q * bfv.centered(v, t) + t) // (2 * t)) % Q
        return (c0, list(cR[1]))

def shares_at(shares, coefs):
    return [{i: shares[i][k] for i in range(len(shares))} for k in coefs]

def plain_of(eng, X):
    """Extract each party's plain share (drop MACs) for S2E."""
    return {i: X[i][0] for i in eng.active}

def head(prev, *handles):
    return hashlib.sha256((prev + "".join(handles)).encode()).hexdigest()

class Host:
    """Holds ciphertexts and handles only. `attack` names a deviation to inject."""
    def __init__(self, sch, Qp, Bp, attack=None):
        self.sch, self.Qp, self.Bp, self.attack = sch, Qp, Bp, attack
        self.stale = {}

    def prove_product(self, ct_a, ct_b):
        out, w = C.build(self.sch, self.Qp, self.Bp, ct_a, ct_b)
        return out, w

def run_step(sch, Qp, Bp, cust, eng, tab, W1, W2, x, y, attack=None, chain="genesis", dbg=None):
    """Returns dict with verdict, counts, and the new encrypted weights (for the reference check)."""
    N, L = sch.N, len(Qp)
    gate = []
    def gate_check(name, h_a, h_b, out, w):
        ok, why = C.verify(sch, Qp, Bp, h_a, h_b, C.handle(out, Qp), out, w)
        gate.append((name, ok, why))
        if not ok:
            raise spdz.Abort(f"decryption refused at {name}: {why}")
    owner = random.Random(77)
    # genesis / owner material (the owner encrypts its data in the layouts the step needs)
    cW1, cW2 = enc_layout(sch, row_major(W1)), enc_layout(sch, row_major(W2))
    cx, cy = enc_layout(sch, rev(x)), enc_layout(sch, {i: y[i] for i in range(D)})
    hW1, hW2, hx, hy = (C.handle(c, Qp) for c in (cW1, cW2, cx, cy))
    hd = head(chain, hW1, hW2)
    committed = {hW1, hW2, hx, hy}
    # ---- host: z1 = W1 x
    a_in = cW1
    if attack == "stale_parent":
        a_in = enc_layout(sch, row_major([[0] * D for _ in range(D)]))   # an older W1 the host kept
    z1, w1 = C.build(sch, Qp, Bp, a_in, cx)
    if attack == "mixed_limbs":
        # limb 0 of the W1 input taken from a different ciphertext: the opened residues no longer hash to hW1
        other = enc_layout(sch, row_major(W2))
        CRT = C.Basis(Qp)
        mixed = tuple([sum(((o if qi == 0 else c) % q) * CRT.hat[qi] * CRT.hat_inv[qi] for qi, q in enumerate(Qp)) % sch.Q
                       for c, o in zip(ca, cb)] for ca, cb in zip(a_in, other))
        z1, w1 = C.build(sch, Qp, Bp, mixed, cx)
    if attack == "wrong_quotient":
        k, j = 2, 4095
        z1 = [list(c) for c in z1]
        z1[k][j] = (z1[k][j] + 1) % sch.Q
    gate_check("z1 = W1 x", hW1, hx, z1, w1)
    # ---- crossing 1
    pd_attack = attack if attack in ("unrelated_boundary_shares", "offset_partial", "offset_in_error") else None
    sz1 = cust.e2s(eng, z1, [64 * i + 63 for i in range(D)], "z1")
    # attack hook: custodian 1 contributes a partial decryption of a DIFFERENT ciphertext (y's) to x's crossing
    sxs = cust.e2s(eng, cx, [63 - j for j in range(D)], "x", attack=pd_attack, alt=cy)
    u1 = [eng.trunc(z, S.S1, 13) for z in sz1]
    hg = [eng.lookup2(u, 128, tab, 255) for u in u1]
    hsh, g1 = [a for a, _ in hg], [b for _, b in hg]
    c_h = cust.s2e(eng, {63 - j: hsh[j] for j in range(D)})
    h_h = C.handle(c_h, Qp)
    committed.add(h_h)
    # ---- host: z2 = W2 h
    z2, w2 = C.build(sch, Qp, Bp, cW2, c_h)
    gate_check("z2 = W2 h", hW2, h_h, z2, w2)
    # ---- crossing 2
    sz2 = cust.e2s(eng, z2, [64 * i + 63 for i in range(D)], "z2")
    sy = cust.e2s(eng, cy, list(range(D)), "y")
    e = [eng.sub(eng.trunc(z, S.S1, 13), yy) for z, yy in zip(sz2, sy)]
    d2 = [eng.trunc(v, S.S2, 8) for v in e]
    G2 = eng.outer(d2, hsh)
    c_dW2 = cust.s2e(eng, {64 * r + c: G2[r][c] for r in range(D) for c in range(D)})
    c_d2 = cust.s2e(eng, {64 * (63 - r): d2[r] for r in range(D)})
    h_d2 = C.handle(c_d2, Qp)
    committed.update({C.handle(c_dW2, Qp), h_d2})
    # ---- host: b = W2^T d2 (old W2), then W2' = W2 - Enc(dW2)
    d2_in = c_d2
    if attack == "wrong_delta":
        d2_in = enc_layout(sch, colrev([1] * D))       # host substitutes its own error vector
    bct, wb = C.build(sch, Qp, Bp, cW2, d2_in)
    gate_check("b = W2^T d2", hW2, h_d2, bct, wb)
    nW2 = tuple([(u - v) % sch.Q for u, v in zip(cc, dd)] for cc, dd in zip(cW2, c_dW2))
    # ---- crossing 3
    sb = cust.e2s(eng, bct, [4032 + j for j in range(D)], "b")
    bg = [eng.mul(bb, g) for bb, g in zip(sb, g1)]
    d1 = [eng.trunc(v, S.S3, 13) for v in bg]
    G1 = eng.outer(d1, sxs)
    c_dW1 = cust.s2e(eng, {64 * r + c: G1[r][c] for r in range(D) for c in range(D)})
    nW1 = tuple([(u - v) % sch.Q for u, v in zip(cc, dd)] for cc, dd in zip(cW1, c_dW1))
    if dbg is not None:
        dbg.update(z1=z1, c_h=c_h, z2=z2, c_dW2=c_dW2, c_d2=c_d2, b=bct, c_dW1=c_dW1)
    eng.mac_check("fhe-step")
    new_head = head(hd, C.handle(nW1, Qp), C.handle(nW2, Qp))
    return dict(nW1=nW1, nW2=nW2, gate=gate, head=new_head)

def decode_W(sch, ct):
    m = sch.decrypt(ct)
    c = lambda v: v - sch.t if v > sch.t // 2 else v
    return [[c(m[64 * i + j]) for j in range(D)] for i in range(D)]
