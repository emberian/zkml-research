"""Extension-field challenges for the collaborative proof (proof lane gen 5, 2026-11-07).

Every Fiat-Shamir challenge that a Schwartz-Zippel or random-combination argument rests on (sumcheck and zerocheck
rounds, the zerocheck's tau, the linear batch's gamma, the rank-1 and binding points, the PCS and Ligero proximity,
linear and quadratic test coefficients) is drawn from F_{p^E}, E = EXT in {1, 2}. E = 2 is F_p[u] / (u^2 - NR) with NR
the least quadratic non-residue >= 2 of p. Committed data, shares, MACs and column indices stay in F_p.

Representation. An element is a tuple of 1 or E ints. Its LENGTH IS STRUCTURAL: a length-1 tuple is "known to be in
F_p" (a share of committed data, a public base constant), a length-E tuple came from a challenge. Arithmetic keeps
the shortest length that the operands force, so a product of two shared F_p values costs one Beaver triple, an
F_{p^2} value times an F_p value two, and two F_{p^2} values three (Karatsuba): z0 = P1 + NR P2, z1 = P3 - P1 - P2
with P1 = x0 y0, P2 = x1 y1, P3 = (x0 + x1)(y0 + y1), in that triple order. Native darkproof::ext mirrors this
exactly (the triple order and the lengths are part of the tape and wire schema). With E = 1 every tuple has length 1
and every byte is the base-field protocol's.
"""
EXT = 1
_NR = {}

def nr(p):
    if p not in _NR:
        n = 2
        while pow(n, (p - 1) // 2, p) != p - 1:
            n += 1
        _NR[p] = n
    return _NR[p]

def lift(x):
    return (x,)

def zero():
    return (0,)

def one():
    return (1,)

def flat(v):
    """A list of elements as a flat int list, components in order (the transcript and wire form)."""
    return [c for x in v for c in x]

def add(a, b, p):
    if len(a) < len(b):
        a, b = b, a
    return tuple((a[i] + (b[i] if i < len(b) else 0)) % p for i in range(len(a)))

def neg(a, p):
    return tuple((-x) % p for x in a)

def sub(a, b, p):
    return add(a, neg(b, p), p)

def scal(c, a, p):
    """c (an int) times a."""
    return tuple(c * x % p for x in a)

def mul(a, b, p):
    if len(a) == 1:
        return tuple(a[0] * x % p for x in b)
    if len(b) == 1:
        return tuple(b[0] * x % p for x in a)
    (a0, a1), (b0, b1) = a, b
    return ((a0 * b0 + nr(p) * a1 * b1) % p, (a0 * b1 + a1 * b0) % p)

def inv(a, p):
    if len(a) == 1:
        return (pow(a[0], -1, p),)
    a0, a1 = a
    nrm = (a0 * a0 - nr(p) * a1 * a1) % p
    ni = pow(nrm, -1, p)
    return (a0 * ni % p, (-a1) * ni % p)

def one_minus(r, p):
    return sub(one(), r, p)

def dot(xs, ys, p):
    acc = zero()
    for x, y in zip(xs, ys):
        acc = add(acc, mul(x, y, p), p)
    return acc

def chal(tr, p, k):
    """k challenges of E components: ONE transcript call of E k draws, grouped consecutively (E = 1: tr.chal)."""
    v = tr.chal(p, EXT * k)
    return [tuple(v[EXT * i:EXT * (i + 1)]) for i in range(k)]

def chal1(tr, p):
    return chal(tr, p, 1)[0]

def eqv(r, p):
    """eq(r, idx) over [0, 2^len(r)) as elements; bit k of idx is paired with r[k] (cosnark.eqv)."""
    v = [one()]
    for rk in r:
        om = one_minus(rk, p)
        v = [mul(x, om, p) for x in v] + [mul(x, rk, p) for x in v]
    return v

def mle(vec, r, p):
    """vec: ints (F_p data) or elements."""
    e = eqv(r, p)
    acc = zero()
    for a, b in zip(vec, e):
        acc = add(acc, mul(a if isinstance(a, tuple) else (a,), b, p), p)
    return acc

def eq_at(a, b, p):
    """eq(a, b) = prod_k (a_k b_k + (1 - a_k)(1 - b_k)): the value of mle(eqv(a), b) without its 2^len(a) table."""
    acc = one()
    for x, y in zip(a, b):
        acc = mul(acc, add(mul(x, y, p), mul(one_minus(x, p), one_minus(y, p), p), p), p)
    return acc

def lagc(deg, r, p):
    """Lagrange coefficients of the nodes 0..deg at r (cosnark_zk.lagc)."""
    out = []
    for i in range(deg + 1):
        num, den = one(), 1
        for j in range(deg + 1):
            if j != i:
                num = mul(num, sub(r, lift(j), p), p)
                den = den * (i - j) % p
        out.append(scal(pow(den, -1, p), num, p))
    return out

def interp_at(vals, r, p):
    """The degree-len(vals)-1 polynomial through (j, vals[j]) evaluated at r."""
    return dot(lagc(len(vals) - 1, r, p), vals, p)

# ------------------------------------------------------------------------------- shared values (spdz.Engine)
def slin(eng, terms):
    """sum c_k x_k over shared elements: terms = [(element c, shared element x)], a shared element being a tuple
    of 1 or E engine values. Returns a shared element of the forced length."""
    p = eng.p
    L = max([1] + [max(len(c), len(x)) for c, x in terms])
    comp = [[] for _ in range(L)]
    n2 = nr(p)
    for c, x in terms:
        if len(c) == 1 and len(x) == 1:
            comp[0].append((c[0], x[0]))
        elif len(x) == 1:
            comp[0].append((c[0], x[0])); comp[1].append((c[1], x[0]))
        elif len(c) == 1:
            comp[0].append((c[0], x[0])); comp[1].append((c[0], x[1]))
        else:
            comp[0] += [(c[0], x[0]), (n2 * c[1] % p, x[1])]
            comp[1] += [(c[0], x[1]), (c[1], x[0])]
    return tuple(eng.lin(t) for t in comp)

def smul(eng, x, y):
    """A product of two shared elements by Beaver triples (1, 2 or 3 of them; order in the module docstring)."""
    p = eng.p
    if len(x) == 1 and len(y) == 1:
        return (eng.mul(x[0], y[0]),)
    if len(y) == 1:
        return (eng.mul(x[0], y[0]), eng.mul(x[1], y[0]))
    if len(x) == 1:
        return (eng.mul(x[0], y[0]), eng.mul(x[0], y[1]))
    P1 = eng.mul(x[0], y[0])
    P2 = eng.mul(x[1], y[1])
    P3 = eng.mul(eng.add(x[0], x[1]), eng.add(y[0], y[1]))
    return (eng.lin([(1, P1), (nr(p), P2)]), eng.lin([(1, P3), (-1, P1), (-1, P2)]))

def sadd(eng, x, y):
    return slin(eng, [(one(), x), (one(), y)])

def ssub(eng, x, y):
    return slin(eng, [(one(), x), (neg(one(), eng.p), y)])

def scmul(eng, c, x):
    return slin(eng, [(c, x)])

def shares(x, i):
    """Party i's plain shares of a shared element, as a tuple of ints."""
    return tuple(v[i][0] for v in x)

def soundness_bits(p):
    import math
    return EXT * math.log2(p)

def spad(eng, x):
    """A shared element padded to EXT components with zero (a round message always carries EXT components)."""
    if len(x) == EXT:
        return x
    z = {i: (0, 0) for i in eng.active}
    return tuple(x) + (z,) * (EXT - len(x))

def pad(a):
    """An element padded to EXT components (an opened value always carries EXT components)."""
    return tuple(a) + (0,) * (EXT - len(a))
