"""
gf_round.py -- the full gadget-Feistel round as a CLAASP component graph,
built on the exactly-verified mod-q primitives of gf_claasp.py (fct3).

The reference is the VERSIONED spec `~/src/ring-ro-hash/design_gadget_feistel.py`.
This file does not re-implement it; fct5 loads that file's `Feistel` class and
compares outputs.
"""
from gf_claasp import Builder, Wire


class RingFeistelEncoder:
    """q: odd prime < 2^n.  d: ring degree.  w: elements per branch.
       B = 2^b, K planes, K*b == n.  P plane products per element."""

    def __init__(self, cipher, n, q, d, w, K, b, P):
        assert K * b == n, "n must be K*b so digits are exact bit-slices"
        assert d * (1 << (2 * b)) < q, "d*B^2 < q keeps the Y*Y sums reduction-free"
        assert q < (1 << n)
        self.B = Builder(cipher)
        self.n, self.q, self.d, self.w, self.K, self.b, self.P = n, q, d, w, K, b, P
        self.free_digit_slices = 0

    # ---------------------------------------------------------- element helpers
    def zext(self, wire, width):
        """widen a wire to `width` bits with leading zeros."""
        k = len(wire)
        if k == width:
            return wire
        zw = self.B.const(width, 0)
        return self.B.xor([self.B.const(width - k, 0), wire, zw], width)

    def subq(self, a, b):
        """(a-b) mod q for a,b in [0,q).  Mirror of addq."""
        n, q = self.n, self.q
        z1 = self.B.const(1, 0)
        W = n + 1
        t = self.B.modsub([z1, a, z1, b], W)        # a-b mod 2^(n+1)
        m = self.B.broadcast_msb(t, W)              # all-ones iff a < b
        qc = self.B.const(W, q)
        qm = self.B.and_([m, qc], W)
        r = self.B.modadd([t, qm], W)
        return r.slice(1, W)

    def addq(self, a, b):
        return self.B.addq(a, b, self.n, self.q)

    # ------------------------------------------------------------ ring layer
    def ring_mul_const(self, g_coeffs, v):
        """g (public ring constant) * v (variable ring element), in
        R_q = Z_q[X]/(X^d+1).  Negacyclic: X^d = -1."""
        d = self.d
        out = []
        for e in range(d):
            pos, neg = None, None
            for i in range(d):
                j = e - i
                sign = 1
                if j < 0:
                    j += d
                    sign = -1
                g = g_coeffs[i] % self.q
                if g == 0:
                    continue
                term = self.B.mulq_const(v[j], g, self.n, self.q)
                if sign > 0:
                    pos = term if pos is None else self.addq(pos, term)
                else:
                    neg = term if neg is None else self.addq(neg, term)
            if pos is None:
                pos = self.B.const(self.n, 0)
            out.append(pos if neg is None else self.subq(pos, neg))
        return out

    def ring_mul_digits(self, a, b):
        """a*b in R_q where every coefficient of a and b is < B.  Then each
        partial sum is < d*B^2 < q, so the accumulation is EXACT in n-bit
        arithmetic and only ONE mod-q step (the negacyclic subtraction) is
        needed.  This is the layer that is genuinely classical: it is exactly
        CLAASP-MP's own modular-multiplication shape."""
        d, n = self.d, self.n
        out = []
        for e in range(d):
            pos, neg = None, None
            for i in range(d):
                j = e - i
                sign = 1
                if j < 0:
                    j += d
                    sign = -1
                term = self.B.mul_exact(a[i], b[j], n)
                if sign > 0:
                    pos = term if pos is None else self.B.modadd([pos, term], n)
                else:
                    neg = term if neg is None else self.B.modadd([neg, term], n)
            if pos is None:
                pos = self.B.const(n, 0)
            if neg is None:
                out.append(pos)
            else:
                out.append(self.subq(pos, neg))
        return out

    # ------------------------------------------------------------- the round
    def digits(self, coeff):
        """base-B decomposition = PURE BIT-SLICING, zero components.
        digit j (j=0 least significant) is MSB-indexed bits
        [n-(j+1)b, n-jb).  Counted, because it is the finding."""
        n, b, K = self.n, self.b, self.K
        out = []
        for j in range(K):
            self.free_digit_slices += 1
            out.append(Wire(coeff.cid, coeff.pos[n - (j + 1) * b: n - j * b]))
        return out

    def F(self, R, a_r, g_r, h_r):
        """R: list of w ring elements, each a list of d n-bit wires."""
        w, d, K, P = self.w, self.d, self.K, self.P
        planes, prods = [], []
        for i in range(w):
            shifted = [self.addq(R[i][c], self.B.const(self.n, a_r[i][c] % self.q))
                       for c in range(d)]
            # per-coefficient digits, regrouped into K ring elements Y_j
            per_coeff = [self.digits(sh) for sh in shifted]
            Y = [[self.zext(per_coeff[c][j], self.n) for c in range(d)]
                 for j in range(K)]
            planes.append(Y)
            prods.append([self.ring_mul_digits(Y[j], Y[j + 1]) for j in range(P)])

        out = []
        for i in range(w):
            acc = None
            for i2 in range(w):
                for j in range(K):
                    t = self.ring_mul_const(g_r[i][i2][j], planes[i2][j])
                    acc = t if acc is None else [self.addq(acc[c], t[c]) for c in range(d)]
                for j in range(P):
                    t = self.ring_mul_const(h_r[i][i2][j], prods[i2][j])
                    acc = t if acc is None else [self.addq(acc[c], t[c]) for c in range(d)]
            out.append(acc)
        return out

    def round(self, L, R, a_r, g_r, h_r):
        Fv = self.F(R, a_r, g_r, h_r)
        newR = [[self.addq(L[i][c], Fv[i][c]) for c in range(self.d)]
                for i in range(self.w)]
        return R, newR
