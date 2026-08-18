"""
gf_claasp.py -- express the gadget-decomposition Feistel ("MSIS-Feistel") as a
CLAASP component graph.

THE POINT OF THIS FILE is to settle, constructively, whether the primitive
CAN be handed to CLAASP / CLAASP-MP at all.  Spec:
`~/src/ring-ro-hash/design_gadget_feistel.py` (versioned) and
`notes/ring-hash-design.md` sec.3.

  R_q = Z_q[X]/(X^d+1), q an ODD PRIME (deployed: 2^64-257, tau=2)
  state (L,R) in R_q^w x R_q^w
  round: (1) R_i += a_{r,i}            -- ring add, mod q
         (2) Y = base-B digits of each coefficient      (B = 2^16, K = 4)
         (3) Z_{i,j} = Y_{i,j} * Y_{i,j+1}              -- ring mult, P of them
         (4) F_r = sum g*Y + sum h*Z   -- dense PUBLIC-CONSTANT ring combination
         (5) (L,R) <- (R, L + F_r(R))

CLAASP's arithmetic components are all mod 2^n (see fct2_modulus_trap.py: the
`modulus` field never reaches any constraint model).  So every mod-q operation
here is EMULATED from mod-2^n components.  The emulations are:

  addq(a,b), a,b in [0,q)
      s = MODADD_{2^(n+1)}(0||a, 0||b)          exact: a+b < 2q < 2^(n+1)
      t = MODSUB_{2^(n+1)}(s, q)                MSB(t)=1  <=>  s < q
      m = LINEAR_LAYER broadcast of MSB(t)      (bit-copy IS F_2-linear)
      r = t XOR (m AND (s XOR t))               select s if s<q else s-q
      -> 1 MODADD + 1 MODSUB + 1 LINEAR_LAYER + 2 XOR + 1 AND = 6 components

  mulq_const(a, g) = sum over set bits i of g of (a * 2^i mod q)
      a*2^i mod q by i repeated addq(x,x); accumulate with addq.
      -> at most 2n addq = 12n components.  NO Barrett, NO wide arithmetic.
      NOTE this is a *variable times public constant* multiply, which is all
      layer (4) needs.

  mul_exact(a,b) for operands < 2^(n/2): the product is < 2^n so mod-2^n
      arithmetic is EXACT and no reduction is needed.  This is what layer (3)
      needs, and it is precisely CLAASP-MP's own modular-multiplication shape
      (eprint 2026/735 sec.3.3.4, Algorithm 4).

Bit order: CLAASP indexes bit 0 = MSB throughout.
"""

BIT0_IS_MSB = True


class Wire:
    """A named slice of some component's output."""
    __slots__ = ("cid", "pos")

    def __init__(self, cid, pos):
        self.cid, self.pos = cid, list(pos)

    def __len__(self):
        return len(self.pos)

    def slice(self, lo, hi):
        return Wire(self.cid, self.pos[lo:hi])


class Builder:
    """Thin recording wrapper over a CLAASP Cipher; counts what it emits."""

    def __init__(self, cipher):
        self.c = cipher
        self.n_components = 0
        self.by_kind = {}
        self._const_cache = {}

    def _bump(self, kind, width):
        self.n_components += 1
        k = self.by_kind.setdefault(kind, [0, 0])
        k[0] += 1
        k[1] += width

    def const(self, width, value):
        key = (width, value)
        if key not in self._const_cache:
            comp = self.c.add_constant_component(width, value)
            self._bump("constant", width)
            self._const_cache[key] = Wire(comp.id, range(width))
        return self._const_cache[key]

    def _ids_pos(self, wires):
        return [w.cid for w in wires], [w.pos for w in wires]

    def modadd(self, wires, width):
        ids, pos = self._ids_pos(wires)
        comp = self.c.add_MODADD_component(ids, pos, width, None)
        self._bump("modadd", width)
        return Wire(comp.id, range(width))

    def modsub(self, wires, width):
        ids, pos = self._ids_pos(wires)
        comp = self.c.add_MODSUB_component(ids, pos, width, None)
        self._bump("modsub", width)
        return Wire(comp.id, range(width))

    def xor(self, wires, width):
        ids, pos = self._ids_pos(wires)
        comp = self.c.add_XOR_component(ids, pos, width)
        self._bump("xor", width)
        return Wire(comp.id, range(width))

    def and_(self, wires, width):
        ids, pos = self._ids_pos(wires)
        comp = self.c.add_AND_component(ids, pos, width)
        self._bump("and", width)
        return Wire(comp.id, range(width))

    def linear(self, wire, matrix, width):
        """matrix: list of `width` rows, each a list of len(wire) bits."""
        comp = self.c.add_linear_layer_component([wire.cid], [wire.pos], width, matrix)
        self._bump("linear_layer", width)
        return Wire(comp.id, range(width))

    def shift(self, wire, width, amount):
        comp = self.c.add_SHIFT_component([wire.cid], [wire.pos], width, amount)
        self._bump("shift", width)
        return Wire(comp.id, range(width))

    # ------------------------------------------------------------- mod-q layer
    def broadcast_msb(self, wire, width):
        """copy bit 0 (the MSB) of `wire` to all `width` output bits, for a
        SQUARE case (len(wire) == width).  matrix[i][j] = input i -> output j;
        see fct4_linear_layer_transpose.py, which measured this convention and
        confirmed the evaluator and the CLAASP-MP model agree on it.

        ⚠ CLAASP's evaluator (generic_functions.linear_layer) emits exactly
        `input.len` output bits, so LINEAR_LAYER CANNOT widen.  For a 1-bit
        source use broadcast_bit() instead."""
        n_in = len(wire)
        assert n_in == width, "LINEAR_LAYER cannot change width in CLAASP"
        matrix = [[1] * width if i == 0 else [0] * width for i in range(n_in)]
        return self.linear(wire, matrix, width)

    def broadcast_bit(self, bit, width):
        """0 or all-ones, from a 1-bit wire, using only MODSUB.  Width-safe and
        free of any matrix-orientation convention: -x mod 2^w is 0 when x=0 and
        2^w-1 when x=1."""
        assert len(bit) == 1
        zw = self.const(width, 0)
        if width > 1:
            x = self.xor([self.const(width - 1, 0), bit, zw], width)
        else:
            x = self.xor([bit, zw], width)
        return self.modsub([zw, x], width)

    def addq(self, a, b, n, q):
        """(a+b) mod q for a,b in [0,q), q odd, q < 2^n.  Returns an n-bit wire."""
        z1 = self.const(1, 0)
        w = n + 1
        s = self.modadd([z1, a, z1, b], w)
        qc = self.const(w, q)
        t = self.modsub([s, qc], w)
        m = self.broadcast_msb(t, w)
        u = self.xor([s, t], w)
        v = self.and_([m, u], w)
        r = self.xor([t, v], w)
        return r.slice(1, w)                      # drop the guard bit

    def dblq(self, a, n, q):
        return self.addq(a, a, n, q)

    def mulq_const(self, a, g, n, q):
        """(a*g) mod q with g a PUBLIC CONSTANT.  Double-and-add over addq."""
        g %= q
        if g == 0:
            return self.const(n, 0)
        acc = None
        cur = a
        i = 0
        while (g >> i) != 0:
            if (g >> i) & 1:
                acc = cur if acc is None else self.addq(acc, cur, n, q)
            i += 1
            if (g >> i) != 0:
                cur = self.dblq(cur, n, q)
        return acc

    def mul_exact(self, a, b, n):
        """a*b mod 2^n, exact when a*b < 2^n.  Shift-and-add, the shape of
        CLAASP-MP's Algorithm 4 (eprint 2026/735 sec.3.3.4)."""
        acc = self.const(n, 0)
        for j in range(n):                        # j-th bit of b, MSB-first index n-1-j
            bj = Wire(b.cid, [b.pos[n - 1 - j]])
            mask = self.broadcast_bit(bj, n)
            part = self.and_([mask, a], n)
            if j:
                part = self.shift(part, n, -j)    # negative parameter = LEFT shift
            acc = self.modadd([acc, part], n)
        return acc
