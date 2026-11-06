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
No relinearization: every ct x ct output (3 components) goes straight into a crossing, which decrypts
with shares of (1, s, s^2). The rank-1 update is computed by the custodians on shares and re-encrypted
(the alternative, a homomorphic outer product, would need relinearization and its own certificate).
"""
import hashlib
import math
import random

import bfv_ref as bfv
import cert_b61 as C
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
    """n custodians holding additive shares s_i of the BFV secret and shares of s^2 (ideal keygen), plus the
    SPDZ engine. Their E2S/S2E messages are recorded per party (the view) for the audit."""
    def __init__(self, sch, n, seed):
        self.sch, self.n = sch, n
        rng = random.Random(seed)
        self.s_sh = [sch.ternary() for _ in range(n)]
        sch.s = [sum(c) for c in zip(*self.s_sh)]
        s2, _ = bfv.negacyclic_mul(sch.s, sch.s)
        parts = [[rng.randrange(-(1 << 20), 1 << 20) for _ in range(sch.N)] for _ in range(n - 1)]
        parts.append([a - sum(c) for a, c in zip(s2, zip(*parts))])
        self.s2_sh = parts
        self.rng = rng
        self.wire = {}
        self.views = [[] for _ in range(n)]

    def count(self, phase, k):
        self.wire[phase] = self.wire.get(phase, 0) + k

    def e2s(self, ct, L):
        """Encryption-to-shares; returns plain additive shares mod t of every coefficient."""
        sch = self.sch
        Q, t, N = sch.Q, sch.t, sch.N
        delta = Q // t
        comps = [bfv.poly_centered(c, Q) for c in ct]
        def part(i):
            acc, _ = bfv.negacyclic_mul(self.s_sh[i], comps[1])
            if len(comps) == 3:
                x2, _ = bfv.negacyclic_mul(self.s2_sh[i], comps[2])
                acc = bfv.poly_add(acc, x2)
            return acc
        shares, hs = [None] * self.n, []
        for i in range(1, self.n):
            Mi = [self.rng.randrange(t) for _ in range(N)]
            e = [self.rng.randrange(-(1 << 30), 1 << 30) for _ in range(N)]     # smudging (toy width)
            hi = [(x - delta * m + ee) % Q for x, m, ee in zip(part(i), Mi, e)]
            self.views[i].append(("e2s", Mi, e))
            self.count("E2S", N * L)
            hs.append(hi)
            shares[i] = Mi
        acc = [(c0 + x + sum(h[j] for h in hs)) % Q for j, (c0, x) in enumerate(zip(comps[0], part(0)))]
        shares[0] = [((t * bfv.centered(x, Q) * 2 + Q) // (2 * Q)) % t for x in acc]
        self.views[0].append(("e2s-decode", acc))
        return shares

    def s2e(self, plain_shares_by_coef, L):
        """Shares-to-encryption with a common reference polynomial; plain_shares_by_coef[i] = {coef: share}."""
        sch = self.sch
        Q, t, N = sch.Q, sch.t, sch.N
        delta = Q // t
        a = sch.uniform()
        total = [0] * N
        for i in range(self.n):
            Mi = [0] * N
            for k, v in plain_shares_by_coef[i].items():
                Mi[k] = v % t
            sa, _ = bfv.negacyclic_mul(self.s_sh[i], bfv.poly_centered(a, Q))
            e = [self.rng.randrange(-(1 << 30), 1 << 30) for _ in range(N)]
            # KPZ-exact encoding round(Q M / t), NOT Delta M: the shares sum to m + k t, and Delta (m + k t)
            # leaves a noise k (Q mod t) ~ 2^62 that the next ct x ct multiplies by t N |s| (fatal at t ~ 2^61);
            # with round(Q M_i / t) the k t part becomes k Q = 0 mod Q and the error is <= n/2.
            hi = [(-x + (Q * m * 2 + t) // (2 * t) + ee) % Q for x, m, ee in zip(sa, Mi, e)]
            self.views[i].append(("s2e", Mi, e))
            self.count("S2E", N * L)
            total = [(u + v) % Q for u, v in zip(total, hi)]
        return (total, a)

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
    conv_log = []           # (transcript position, source tag, coefficient, dealer stream index per party)
    e2s_out = {}
    def e2s(tag, ct):
        e2s_out[tag] = cust.e2s(ct, L)
        return e2s_out[tag]
    def conv(tag, coef, override=None):
        plain = {i: e2s_out[tag][i][coef] for i in range(cust.n)}
        if override:
            plain.update(override)
        pos = len(eng.transcript)
        x = eng.auth_plain(plain)
        conv_log.append((pos, tag, coef, {i: len(eng.dealer.streams[i]) - 1 for i in range(cust.n)}))
        return x
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
    e2s("z1", z1)
    e2s("x", cx)
    sz1 = [conv("z1", 64 * i + 63) for i in range(D)]
    if attack == "unrelated_boundary_shares":
        # custodian 1 authenticates a share from a DIFFERENT encryption-to-shares (here: y's ciphertext)
        e2s("y-alt", cy)
        sxs = [conv("x", 63, override={1: e2s_out["y-alt"][1][0]})] + [conv("x", 63 - j) for j in range(1, D)]
    else:
        sxs = [conv("x", 63 - j) for j in range(D)]
    u1 = [eng.trunc(z, S.S1, 13) for z in sz1]
    hg = [eng.lookup2(u, 128, tab, 255) for u in u1]
    hsh, g1 = [a for a, _ in hg], [b for _, b in hg]
    c_h = cust.s2e([{63 - j: hsh[j][i][0] for j in range(D)} for i in range(cust.n)], L)
    h_h = C.handle(c_h, Qp)
    committed.add(h_h)
    # ---- host: z2 = W2 h
    z2, w2 = C.build(sch, Qp, Bp, cW2, c_h)
    gate_check("z2 = W2 h", hW2, h_h, z2, w2)
    # ---- crossing 2
    e2s("z2", z2)
    e2s("y", cy)
    sz2 = [conv("z2", 64 * i + 63) for i in range(D)]
    sy = [conv("y", i) for i in range(D)]
    e = [eng.sub(eng.trunc(z, S.S1, 13), yy) for z, yy in zip(sz2, sy)]
    d2 = [eng.trunc(v, S.S2, 8) for v in e]
    G2 = eng.outer(d2, hsh)
    c_dW2 = cust.s2e([{64 * r + c: G2[r][c][i][0] for r in range(D) for c in range(D)} for i in range(cust.n)], L)
    c_d2 = cust.s2e([{64 * (63 - r): d2[r][i][0] for r in range(D)} for i in range(cust.n)], L)
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
    e2s("b", bct)
    sb = [conv("b", 4032 + j) for j in range(D)]
    bg = [eng.mul(bb, g) for bb, g in zip(sb, g1)]
    d1 = [eng.trunc(v, S.S3, 13) for v in bg]
    G1 = eng.outer(d1, sxs)
    c_dW1 = cust.s2e([{64 * r + c: G1[r][c][i][0] for r in range(D) for c in range(D)} for i in range(cust.n)], L)
    nW1 = tuple([(u - v) % sch.Q for u, v in zip(cc, dd)] for cc, dd in zip(cW1, c_dW1))
    if dbg is not None:
        dbg.update(z1=z1, c_h=c_h, z2=z2, c_dW2=c_dW2, c_d2=c_d2, b=bct, c_dW1=c_dW1)
    eng.mac_check("fhe-step")
    new_head = head(hd, C.handle(nW1, Qp), C.handle(nW2, Qp))
    return dict(nW1=nW1, nW2=nW2, gate=gate, head=new_head, conv_log=conv_log, e2s_out=e2s_out)

def conversion_audit(eng, res, opened, honest_tags=None):
    """Sampled audit of the encryption-to-shares -> authenticated-shares conversion (Codex's conversion
    relation): for each opened custodian, its broadcast at every authentication must equal its own E2S
    share of the PROTOCOL-DESIGNATED source ciphertext at the designated coefficient, minus its share of
    the dealer's mask. The auditor reads the custodian's E2S view (its share of each source) and its
    committed preprocessing stream."""
    p = eng.p
    for pos, tag, coef, sidx in res["conv_log"]:
        ph, bs, v = eng.transcript[pos]
        for i in opened:
            share = res["e2s_out"][tag][i][coef]
            r_i = eng.dealer.streams[i][sidx[i]][1][0]
            if bs[i] != (share - r_i) % p:
                return False, f"custodian {i} authenticated a value that is not its share of {tag}[{coef}]"
    return True, "accept"

def decode_W(sch, ct):
    m = sch.decrypt(ct)
    c = lambda v: v - sch.t if v > sch.t // 2 else v
    return [[c(m[64 * i + j]) for j in range(D)] for i in range(D)]
