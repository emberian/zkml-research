"""Collaborative zero-knowledge Ligero over additive shares (cosnark ZK layers 2-3; scheme decision §13).

2026-11-06. The custodians hold a hidden witness as additive shares, organised in ROWS of width k. A row is the
message of a polynomial f of degree < k + t: f(zeta_i) = message_i for i < k, and f(eta_l) = hiding randomness for
l < t, drawn locally by each party. Rows are committed in GROUPS, one Merkle tree per (group, party) over the
codeword f(1..npts), so a group can be committed before a Fiat-Shamir challenge it must precede (one group per
sumcheck round). Opening T <= t columns reveals uniform values.

Tests (Ames-Hazay-Ishai-Venkitasubramaniam 2017, rows of a single interleaved RS code; [READ from memory, the
masking forms are the standard ones]):
  proximity  w(X) = sum_rows gamma_r f_r(X) + mask_p(X)                  deg < k + t
  linear     A w = b: alpha = r^T A, R_row interpolates alpha_row on zeta;
             q(X) = sum_rows R_row(X) f_row(X) + mask_l(X), sum_{i<k} mask_l(zeta_i) = 0;
             verifier checks sum_{i<k} q(zeta_i) = r^T b                   deg < 2k + t - 1
  quadratic  x o y = z on row triples: p(X) = sum rho_q (f_x f_y - f_z)(X) + mask_q(X), mask_q vanishes on zeta;
             verifier checks p(zeta_i) = 0                                deg < 2(k + t) - 1
and, at T columns drawn after all messages, every message's consistency with the opened column sums.
Every mask is committed before the challenge it hides; a mask that is not low degree passes the column test only
with probability about (1 - delta)^T, and one whose zeta-sum or zeta-values are wrong passes only with
probability 1/p, because it was fixed before r or rho [INFERRED].

Collaborative execution: proximity and linear messages are LOCAL (sums of public polynomials times shared ones).
The quadratic message needs the product f_x f_y of two SHARED polynomials. It uses one POLYNOMIAL Beaver triple
(A, B, C = A B) from the dealer: open E = f_x - A and F = f_y - B (uniform coefficient vectors), then
f_x f_y = C + E B + F A + E F locally. Integrity of the product needs no MAC: the quadratic test checks it.
"""
import random

from cosnark import H, Transcript, Tree, distinct_cols, leaf_salts, verify_path
import cosnark_ext as X

def pmul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return out

def padd(a, b, p):
    n = max(len(a), len(b))
    a = a + [0] * (n - len(a)); b = b + [0] * (n - len(b))
    return [(x + y) % p for x, y in zip(a, b)]

def pscale(c, a, p):
    return [c * x % p for x in a]

def peval(a, x, p):
    acc = 0
    for c in reversed(a):
        acc = (acc * x + c) % p
    return acc

def lagrange_basis(nodes, p):
    """Coefficient vectors of the Lagrange basis polynomials on `nodes`."""
    M = [1]
    for z in nodes:
        M = pmul(M, [(-z) % p, 1], p)
    out = []
    for z in nodes:
        # M / (X - z) by synthetic division
        q, carry = [0] * (len(M) - 1), 0
        for i in range(len(M) - 1, 0, -1):
            carry = (M[i] + carry * z) % p
            q[i - 1] = carry
        den = peval(q, z, p)
        out.append(pscale(pow(den, -1, p), q, p))
    return out

class Params:
    def __init__(self, p, k=64, t=64, T=64, blow=4):
        assert T <= t
        self.p, self.k, self.t, self.T = p, k, t, T
        self.npts = blow * (k + t)
        self.zeta = [p - 1 - i for i in range(k)]
        self.eta = [p - 1 - k - l for l in range(t)]
        self.L = lagrange_basis(self.zeta + self.eta, p)      # message+hiding values -> coefficients
        self.Lz = lagrange_basis(self.zeta, p)                # alpha on zeta -> R_row
        V = [1]
        for z in self.zeta:
            V = pmul(V, [(-z) % p, 1], p)
        self.Vz = V                                           # vanishing polynomial of zeta

    def interp(self, vals):
        p = self.p
        out = [0] * len(self.L)
        for v, l in zip(vals, self.L):
            if v:
                for i, c in enumerate(l):
                    out[i] = (out[i] + v * c) % p
        return out

    def interp_z(self, alpha):
        p = self.p
        out = [0] * self.k
        for v, l in zip(alpha, self.Lz):
            if v:
                for i, c in enumerate(l):
                    out[i] = (out[i] + v * c) % p
        return out

    def code(self, poly):
        return [peval(poly, x, self.p) for x in range(1, self.npts + 1)]

def merkle(cols, det=None):
    salts = leaf_salts(len(cols), det)
    level = [H("leaf", s, c) for s, c in zip(salts, cols)]
    level += [H("pad", j) for j in range((1 << (len(level) - 1).bit_length()) - len(level))]
    tree = Tree([level])
    tree.salts = salts
    while len(level) > 1:
        level = [H(level[i], level[i + 1]) for i in range(0, len(level), 2)]
        tree.append(level)
    return tree

def path(tree, j):
    out, k = [tree.salts[j]], j
    for lvl in tree[:-1]:
        out.append(lvl[k ^ 1])
        k //= 2
    return out

class Prover:
    """The custodians' side. rows[r][i] = party i's share of row r's k message values."""
    def __init__(self, P, n, seed):
        self.P, self.n = P, n
        # hiding values and the dealer's triples come from secret randomness, never from public data
        import secrets
        from cosnark import det_rng
        self.det = det_rng("cozk", seed, "dealer") is not None      # TEST ONLY streams (cosnark.det_rng)
        if self.det:
            self.rng = [det_rng("cozk", seed, "party", i) for i in range(n)]
            self.dealer = det_rng("cozk", seed, "dealer")
        else:
            self.rng = [random.Random(secrets.randbits(256)) for i in range(n)]
            self.dealer = random.Random(secrets.randbits(256))
        self.rows, self.polys, self.groups = [], [], []
        self.pending = []
        self.wire = 0               # field elements sent between custodians (openings)
        self.poly_triples = 0       # polynomial Beaver triples (preprocessing)
        self.scalar_triples = 0     # scalar Beaver triples for the product rows' z values

    def add_row(self, shares):
        P = self.P
        assert len(shares) == self.n and all(len(s) <= P.k for s in shares)
        shares = [list(s) + [0] * (P.k - len(s)) for s in shares]
        self.rows.append(shares)
        self.polys.append([P.interp(shares[i] + [self.rng[i].randrange(P.p) for _ in range(P.t)])
                           for i in range(self.n)])
        self.pending.append(len(self.rows) - 1)
        return len(self.rows) - 1

    def _commit(self, polys_by_party):
        P = self.P
        codes = [[P.code(f) for f in fs] for fs in polys_by_party]
        trees = [merkle([[c[j] for c in codes[i]] for j in range(P.npts)], self.rng[i] if self.det else None)
                 for i in range(self.n)]
        return codes, trees

    def commit(self):
        """Commit the rows added since the last commit as one group; returns the per-party roots."""
        idx, self.pending = self.pending, []
        codes, trees = self._commit([[self.polys[r][i] for r in idx] for i in range(self.n)])
        self.groups.append(dict(rows=idx, codes=codes, trees=trees))
        return [t[-1][0] for t in trees]

    def commit_masks(self):
        """Per component k < EXT of the F_{p^EXT} test coefficients: mask_p (deg < k + t), mask_l (deg < 2k + t - 1,
        zero sum on zeta), mask_q (vanishing on zeta). Order: the EXT mask_p, the EXT mask_l, the EXT mask_q
        (EXT = 1: mask_p, mask_l, mask_q)."""
        P, p = self.P, self.P.p
        E = X.EXT
        ms = []
        for i in range(self.n):
            rg = self.rng[i]
            mps = [[rg.randrange(p) for _ in range(P.k + P.t)] for _ in range(E)]
            mls = []
            for _ in range(E):
                ml = [rg.randrange(p) for _ in range(2 * P.k + P.t - 1)]
                s = sum(peval(ml, z, p) for z in P.zeta) % p
                ml[0] = (ml[0] - s * pow(P.k, -1, p)) % p           # sum over zeta of the constant term is k * c0
                mls.append(ml)
            mqs = [pmul(P.Vz, [rg.randrange(p) for _ in range(P.k + 2 * P.t - 1)], p) for _ in range(E)]
            ms.append(mps + mls + mqs)
        self.masks = ms
        codes, trees = self._commit(ms)
        self.mask_group = dict(codes=codes, trees=trees)
        return [t[-1][0] for t in trees]

    def mul_plain(self, xs, ys):
        """Shares of x*y from plain additive shares with a dealer triple; no MAC is needed, because the
        quadratic test checks z = x y."""
        p, n = self.P.p, self.n
        a, b = self.dealer.randrange(p), self.dealer.randrange(p)
        A, B, C = (_share([v], n, p, self.dealer) for v in (a, b, a * b % p))
        self.scalar_triples += 1
        e = self.open_poly([[(xs[i] - A[i][0]) % p] for i in range(n)])[0]
        f = self.open_poly([[(ys[i] - B[i][0]) % p] for i in range(n)])[0]
        return [(C[i][0] + e * B[i][0] + f * A[i][0] + (e * f if i == 0 else 0)) % p for i in range(n)]

    def open_poly(self, shares):
        """Open a shared coefficient vector: every party sends its share to every other."""
        self.wire += len(shares[0]) * self.n * (self.n - 1)
        out = [0] * max(len(s) for s in shares)
        for s in shares:
            out = padd(out, s, self.P.p)
        return out

    def prove(self, tr, lin, quad):
        """lin: list of ({(row, pos): coef}, rhs). quad: list of (row_x, row_y, row_z). Returns the messages. The test
        coefficients are F_{p^EXT} elements; component k of each message uses component k of the coefficients and
        its own masks (EXT = 1: the base protocol, byte for byte)."""
        P, p, n = self.P, self.P.p, self.n
        E = X.EXT
        R = len(self.rows)
        # proximity
        gam = X.chal(tr, p, R)
        w = [self.open_poly([_lincomb([(g[k], self.polys[r][i]) for r, g in enumerate(gam) if k < len(g)] +
                                      [(1, self.masks[i][k])], p) for i in range(n)]) for k in range(E)]
        tr.absorb("lig-w", *w)
        # linear
        rr = X.chal(tr, p, len(lin))
        alpha = _alpha(lin, rr, R, P.k, p)
        q = []
        for k in range(E):
            Rp = [P.interp_z(a) if any(a) else None for a in alpha[k]]
            q.append(self.open_poly([_lincomb([(1, pmul(Rp[r], self.polys[r][i], p)) for r in range(R) if Rp[r]] +
                                              [(1, self.masks[i][E + k])], p) for i in range(n)]))
        tr.absorb("lig-q", *q)
        # quadratic, with one polynomial Beaver triple per row triple (the products are base polynomials: the
        # extension's components only weight them differently)
        rho = X.chal(tr, p, len(quad))
        acc = [[list(self.masks[i][2 * E + k]) for i in range(n)] for k in range(E)]
        for (rx, ry, rz), c in zip(quad, rho):
            deg = P.k + P.t
            A = [self.dealer.randrange(p) for _ in range(deg)]
            B = [self.dealer.randrange(p) for _ in range(deg)]
            C = pmul(A, B, p)
            sh = lambda v: _share(v, n, p, self.dealer)
            As, Bs, Cs = sh(A), sh(B), sh(C)
            self.poly_triples += 1
            Ep = self.open_poly([padd(self.polys[rx][i], pscale(p - 1, As[i], p), p) for i in range(n)])
            F = self.open_poly([padd(self.polys[ry][i], pscale(p - 1, Bs[i], p), p) for i in range(n)])
            EF = pmul(Ep, F, p)
            for i in range(n):
                prod = _lincomb([(1, Cs[i]), (1, pmul(Ep, Bs[i], p)), (1, pmul(F, As[i], p))] +
                                ([(1, EF)] if i == 0 else []), p)
                for k in range(E):
                    ck = c[k] if k < len(c) else 0
                    acc[k][i] = _lincomb([(1, acc[k][i]), (ck, prod), (p - ck, self.polys[rz][i])], p)
        pq = [self.open_poly(acc[k]) for k in range(E)]
        tr.absorb("lig-p", *pq)
        # columns
        J = distinct_cols(tr, p, P.T, P.npts)
        cols = []
        for g in self.groups + [self.mask_group]:
            cols.append([[([c[j] for c in g["codes"][i]], path(g["trees"][i], j)) for j in J] for i in range(n)])
        out = dict(w=w[0], q=q[0], pq=pq[0], J=J, cols=cols)
        for k in range(1, E):
            out.update({f"w{k}": w[k], f"q{k}": q[k], f"pq{k}": pq[k]})
        return out

def _alpha(lin, rr, R, k, p):
    """alpha[comp][row][pos] = sum_c rr_c[comp] * A_c[row][pos]."""
    alpha = [[[0] * k for _ in range(R)] for _ in range(X.EXT)]
    for (terms, _), c in zip(lin, rr):
        for kk, ck in enumerate(c):
            if not ck:
                continue
            al = alpha[kk]
            for (row, pos), a in terms.items():
                al[row][pos] = (al[row][pos] + ck * a) % p
    return alpha

def _lincomb(terms, p):
    out = [0]
    for c, a in terms:
        out = padd(out, pscale(c, a, p), p)
    return out

def _share(v, n, p, rng):
    xs = [[rng.randrange(p) for _ in v] for _ in range(n - 1)]
    last = [(x - sum(c)) % p for x, c in zip(v, zip(*xs))] if n > 1 else list(v)
    return xs + [last]

def verify(P, n, group_roots, group_sizes, mask_roots, lin, quad, msgs, tr):
    """group_roots[g] = per-party roots of group g (in commit order); group_sizes[g] = its row count; rows are
    numbered in commit order. Uses only public data."""
    p, k, t = P.p, P.k, P.t
    E = X.EXT
    R = sum(group_sizes)
    sfx = [""] + [str(c) for c in range(1, E)]
    try:
        w = [msgs["w" + s_] for s_ in sfx]
        q = [msgs["q" + s_] for s_ in sfx]
        pq = [msgs["pq" + s_] for s_ in sfx]
    except KeyError:
        return False, "Ligero: a message component is missing"
    cols = msgs["cols"]
    if any(len(w_) > k + t for w_ in w) or any(len(q_) > 2 * k + t - 1 for q_ in q) or any(len(x) > 2 * (k + t) - 1 for x in pq):
        return False, "Ligero: a message exceeds its degree bound"
    gam = X.chal(tr, p, R)
    tr.absorb("lig-w", *w)
    rr = X.chal(tr, p, len(lin))
    for kk in range(E):
        if sum(peval(q[kk], z, p) for z in P.zeta) % p != sum(c[kk] * b for (_, b), c in zip(lin, rr) if kk < len(c)) % p:
            return False, "Ligero linear test: the constraints do not hold"
    alpha = _alpha(lin, rr, R, k, p)
    Rp = [[P.interp_z(a) if any(a) else None for a in alpha[kk]] for kk in range(E)]
    tr.absorb("lig-q", *q)
    rho = X.chal(tr, p, len(quad))
    if any(peval(pq_, z, p) for pq_ in pq for z in P.zeta):
        return False, "Ligero quadratic test: a product gate does not hold"
    tr.absorb("lig-p", *pq)
    J = distinct_cols(tr, p, P.T, P.npts)
    if msgs.get("J") is not None and list(msgs["J"]) != J:
        return False, "Ligero column challenge mismatch"
    roots = list(group_roots) + [mask_roots]
    sizes = list(group_sizes) + [3 * E]
    if len(cols) != len(roots):
        return False, "Ligero: wrong number of column groups"
    for jj, j in enumerate(J):
        x = j + 1
        colsum, msum = [], None
        for g, (rts, sz) in enumerate(zip(roots, sizes)):
            s = [0] * sz
            for i in range(n):
                col, pth = cols[g][i][jj]
                if len(col) != sz or not verify_path(rts[i], col, j, pth):
                    return False, f"Ligero: Merkle opening fails (group {g}, custodian {i})"
                s = [(a + b) % p for a, b in zip(s, col)]
            if g < len(group_roots):
                colsum += s
            else:
                msum = s
        for kk in range(E):
            if peval(w[kk], x, p) != (sum(g_[kk] * c for g_, c in zip(gam, colsum)) + msum[kk]) % p:
                return False, "Ligero proximity test fails at an opened column"
            if peval(q[kk], x, p) != (sum(peval(Rp[kk][r], x, p) * colsum[r] for r in range(R) if Rp[kk][r]) + msum[E + kk]) % p:
                return False, "Ligero linear test fails at an opened column"
            if peval(pq[kk], x, p) != (sum(c[kk] * (colsum[a] * colsum[b] - colsum[z]) for (a, b, z), c in zip(quad, rho)) + msum[2 * E + kk]) % p:
                return False, "Ligero quadratic test fails at an opened column"
    return True, "accept"
