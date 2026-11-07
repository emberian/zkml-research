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
        """mask_p (deg < k + t), mask_l (deg < 2k + t - 1, zero sum on zeta), mask_q (vanishing on zeta)."""
        P, p = self.P, self.P.p
        ms = []
        for i in range(self.n):
            rg = self.rng[i]
            mp = [rg.randrange(p) for _ in range(P.k + P.t)]
            ml = [rg.randrange(p) for _ in range(2 * P.k + P.t - 1)]
            s = sum(peval(ml, z, p) for z in P.zeta) % p
            ml[0] = (ml[0] - s * pow(P.k, -1, p)) % p           # sum over zeta of the constant term is k * c0
            mq = pmul(P.Vz, [rg.randrange(p) for _ in range(P.k + 2 * P.t - 1)], p)
            ms.append([mp, ml, mq])
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
        """lin: list of ({(row, pos): coef}, rhs). quad: list of (row_x, row_y, row_z). Returns the messages."""
        P, p, n = self.P, self.P.p, self.n
        R = len(self.rows)
        # proximity
        gam = tr.chal(p, R)
        w = self.open_poly([_lincomb([(g, self.polys[r][i]) for r, g in enumerate(gam)] + [(1, self.masks[i][0])], p)
                            for i in range(n)])
        tr.absorb("lig-w", w)
        # linear
        rr = tr.chal(p, len(lin))
        alpha = [[0] * P.k for _ in range(R)]
        for (terms, _), c in zip(lin, rr):
            for (row, pos), a in terms.items():
                alpha[row][pos] = (alpha[row][pos] + c * a) % p
        Rp = [P.interp_z(a) if any(a) else None for a in alpha]
        q = self.open_poly([_lincomb([(1, pmul(Rp[r], self.polys[r][i], p)) for r in range(R) if Rp[r]] +
                                     [(1, self.masks[i][1])], p) for i in range(n)])
        tr.absorb("lig-q", q)
        # quadratic, with one polynomial Beaver triple per row triple
        rho = tr.chal(p, len(quad))
        acc = [list(self.masks[i][2]) for i in range(n)]
        for (rx, ry, rz), c in zip(quad, rho):
            deg = P.k + P.t
            A = [self.dealer.randrange(p) for _ in range(deg)]
            B = [self.dealer.randrange(p) for _ in range(deg)]
            C = pmul(A, B, p)
            sh = lambda v: _share(v, n, p, self.dealer)
            As, Bs, Cs = sh(A), sh(B), sh(C)
            self.poly_triples += 1
            E = self.open_poly([padd(self.polys[rx][i], pscale(p - 1, As[i], p), p) for i in range(n)])
            F = self.open_poly([padd(self.polys[ry][i], pscale(p - 1, Bs[i], p), p) for i in range(n)])
            EF = pmul(E, F, p)
            for i in range(n):
                prod = _lincomb([(1, Cs[i]), (1, pmul(E, Bs[i], p)), (1, pmul(F, As[i], p))] +
                                ([(1, EF)] if i == 0 else []), p)
                acc[i] = _lincomb([(1, acc[i]), (c, prod), (p - c, self.polys[rz][i])], p)
        pq = self.open_poly(acc)
        tr.absorb("lig-p", pq)
        # columns
        J = distinct_cols(tr, p, P.T, P.npts)
        cols = []
        for g in self.groups + [self.mask_group]:
            cols.append([[([c[j] for c in g["codes"][i]], path(g["trees"][i], j)) for j in J] for i in range(n)])
        return dict(w=w, q=q, pq=pq, cols=cols)

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
    R = sum(group_sizes)
    w, q, pq, cols = msgs["w"], msgs["q"], msgs["pq"], msgs["cols"]
    if len(w) > k + t or len(q) > 2 * k + t - 1 or len(pq) > 2 * (k + t) - 1:
        return False, "Ligero: a message exceeds its degree bound"
    gam = tr.chal(p, R)
    tr.absorb("lig-w", w)
    rr = tr.chal(p, len(lin))
    if sum(peval(q, z, p) for z in P.zeta) % p != sum(c * b for (_, b), c in zip(lin, rr)) % p:
        return False, "Ligero linear test: the constraints do not hold"
    alpha = [[0] * k for _ in range(R)]
    for (terms, _), c in zip(lin, rr):
        for (row, pos), a in terms.items():
            alpha[row][pos] = (alpha[row][pos] + c * a) % p
    Rp = [P.interp_z(a) if any(a) else None for a in alpha]
    tr.absorb("lig-q", q)
    rho = tr.chal(p, len(quad))
    if any(peval(pq, z, p) for z in P.zeta):
        return False, "Ligero quadratic test: a product gate does not hold"
    tr.absorb("lig-p", pq)
    J = distinct_cols(tr, p, P.T, P.npts)
    roots = list(group_roots) + [mask_roots]
    sizes = list(group_sizes) + [3]
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
        if peval(w, x, p) != (sum(g_ * c for g_, c in zip(gam, colsum)) + msum[0]) % p:
            return False, "Ligero proximity test fails at an opened column"
        if peval(q, x, p) != (sum(peval(Rp[r], x, p) * colsum[r] for r in range(R) if Rp[r]) + msum[1]) % p:
            return False, "Ligero linear test fails at an opened column"
        if peval(pq, x, p) != (sum(c * (colsum[a] * colsum[b] - colsum[z]) for (a, b, z), c in zip(quad, rho)) + msum[2]) % p:
            return False, "Ligero quadratic test fails at an opened column"
    return True, "accept"
