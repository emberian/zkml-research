"""The collaborative proof's spine with zero knowledge layers 2-3 (scheme decision §13, §16).

2026-11-06. Layer 1 (hiding PCS: random tails, one proximity mask per life) is cosnark.SharePCS. Layers 2-3:
  - every sumcheck round message stays SECRET-SHARED: it is a hidden row of a collaborative Ligero (cozk.py),
    committed as its own group before the round's challenge is drawn;
  - every PCS evaluation's row combination u_e stays hidden too. The evaluation-consistency check
    "encode(u_e) agrees with a_e . (opened column)" becomes Ligero LINEAR constraints on u_e, at the PCS's
    opened columns. So no evaluation mask rows are needed, and the evaluation VALUE Y_e = <u_e, b_e> is a
    hidden linear form;
  - the verifier's algebra (round sums, Lagrange steps, finals) is linear in the hidden values except six
    products: three matvec finals Y_W Y_v, the zerocheck's Y_b Y_g, and the two zero-round rank-1 checks
    Y_d Y_v. They go into three product rows (x, y, z) under Ligero's quadratic test. Construction (a) is
    unchanged: W'(r) = W(r) - d(r_row) v(r_col) is one product gate on exact (unmasked) MLE values.
What the verifier sees: Merkle roots, the PCS proximity combinations (each masked by its life's mask row),
opened PCS columns (uniform: tails >= opened columns per life), the Ligero roots, Ligero's three masked messages,
and opened Ligero columns (uniform: t >= T). It sees no round value and no evaluation.

prove_zk returns a proof object made only of ints, hex strings and lists. verify_zk(d, context, parent_roots,
chained, proof) uses public data only, and is what the untrusted-input verifier (proofwire.py) parses into.
"""
import cosnark as CS
import cozk as Z
import cosnark_ext as X
from cosnark import Transcript, eqv, mle

K_L, T_HIDE, T_OPEN = 64, 309, 309       # Ligero row width, hiding points (>= opened), opened columns (as the PCS: T_COLS)
NPROD = 6
ZKSC = "rows"     # how the sumchecks are hidden (profile "ZKSC"): "rows", every round message a hidden Ligero row in its
                  # own tree; "mask" (cut D, proof.md section 17), every round message OPENED, made uniform by a masking
                  # polynomial g = g_1(x_1) + ... + g_l(x_l) per sumcheck, all g of a proof hidden in ONE Ligero group

class GMask:
    """Cut D's masking polynomials for one proof. specs: [(name, l, deg)]. g_name's round j (0-based) polynomial is
    given by its values at t = 0..deg, each an F_{p^EXT} element; the cells of every g are packed, in spec order,
    into consecutive Ligero rows from row0: flat index off(name) + (j (deg + 1) + t) EXT + k."""
    def __init__(self, specs, row0=0):
        self.specs, self.row0, self.off, self.ld = list(specs), row0, {}, {}
        n = 0
        for name, l, deg in self.specs:
            self.off[name], self.ld[name] = n, (l, deg)
            n += l * (deg + 1) * X.EXT
        self.ncells = n
        self.nrows = -(-n // K_L)

    def idx(self, name, j, t, k):
        l, deg = self.ld[name]
        return self.off[name] + (j * (deg + 1) + t) * X.EXT + k

    def cell(self, name, j, t, k):
        i = self.idx(name, j, t, k)
        return (self.row0 + i // K_L, i % K_L)

    def form(self, p, name, j, t, coef):
        return evar(p, ecell([self.cell(name, j, t, k) for k in range(X.EXT)]), coef)

    def G_coef(self, p, name):
        """[(j, t, coefficient)] of G = sum over the cube of g = 2^(l-1) sum_j (g_j(0) + g_j(1))."""
        l, _ = self.ld[name]
        c = pow(2, l - 1, p)
        return [(j, t, c) for j in range(l) for t in (0, 1)]

    def at_coef(self, p, name, rs):
        """[(j, t, element)] of g(rs) = sum_j g_j(r_j)."""
        _, deg = self.ld[name]
        return [(j, t, lc) for j, r in enumerate(rs) for t, lc in enumerate(X.lagc(deg, r, p))]

    def round_coef(self, p, name, i, t, rs):
        """[(j, t', element)] of the round-i message's g part at X = t: the sum of g(r_<i, t, x_>i) over x_>i in
        {0, 1}^(l - 1 - i) = 2^(l-1-i) (sum_{j<i} g_j(r_j) + g_i(t)) + 2^(l-2-i) sum_{j>i} (g_j(0) + g_j(1))."""
        l, deg = self.ld[name]
        a = (pow(2, l - 1 - i, p),)
        out = [(j, tt, X.mul(a, lc, p)) for j in range(i) for tt, lc in enumerate(X.lagc(deg, rs[j], p))]
        out.append((i, t, a))
        if i < l - 1:
            b = pow(2, l - 2 - i, p)
            out += [(j, tt, (b,)) for j in range(i + 1, l) for tt in (0, 1)]
        return out

    def lin_form(self, p, name, coefs, scale):
        """The form scale * sum coef * g-cell value."""
        forms = [self.form(p, name, j, t, X.mul(scale, c if isinstance(c, tuple) else (c,), p)) for j, t, c in coefs]
        out = [dict() for _ in range(X.EXT)]
        for f_ in forms:
            for k in range(X.EXT):
                for key, v in f_[k].items():
                    out[k][key] = (out[k].get(key, 0) + v) % p
        return out

    def share_val(self, p, sh, name, coefs):
        """One party's share (an element) of sum coef * g-cell value, from its flat share list sh."""
        acc = X.zero()
        for j, t, c in coefs:
            v = tuple(sh[self.idx(name, j, t, k)] for k in range(X.EXT))
            acc = X.add(acc, X.mul(c if isinstance(c, tuple) else (c,), v, p), p)
        return acc

    def commit(self, L):
        """Prover: every party draws its g share (all cells, from its own Ligero stream), adds the rows, commits
        them as one group. Returns (per-party flat shares, roots)."""
        p = L.P.p
        shs = [[L.rng[i].randrange(p) for _ in range(self.ncells)] for i in range(L.n)]
        for r in range(self.nrows):
            L.add_row([sh[r * K_L:(r + 1) * K_L] for sh in shs])
        return shs, L.commit()

def open_sum(p, per_party):
    """The opened value of a list of per-party element shares (every custodian broadcasts its share)."""
    acc = X.zero()
    for v in per_party:
        acc = X.add(acc, v, p)
    return X.pad(acc)

class ZKPCS(CS.SharePCS):
    """Layer-1 PCS without evaluation masks: evaluation consistency is proved inside the Ligero."""
    def eval_weights(self, pt, e):
        return eqv(pt[self.mc:], self.p) + [0] * self.nmask

    def mask_corr(self, i, pt, e):
        return 0

    def eval_weights_e(self, pt):
        """The row weights of an evaluation at pt (elements): eq(pt_rows) on the data rows, 0 on the mask rows."""
        return X.eqv(pt[self.mc:], self.p) + [X.zero()] * self.nmask

class PubShape:
    """The public shape of a ZKPCS commitment to a vector of length 2^m (what the verifier may know)."""
    def __init__(self, p, m, hide, nmask, base, lives=None):
        self.p, self.m = p, m
        self.mr = CS.row_split(m, nmask, hide)
        self.mc = m - self.mr
        self.Rd, self.C = 1 << self.mr, 1 << self.mc
        self.nmask, self.hide = nmask, hide
        self.R = self.Rd + nmask
        self.lives = lives or CS.LIVES
        self.block = nmask // self.lives if nmask else 0
        self.base = base
        self.W = self.C + hide
        self.pts = CS.domain(p, CS.BLOW * self.W, self.W)
    eval_weights, eval_weights_e = ZKPCS.eval_weights, ZKPCS.eval_weights_e
    prox_row, prox_len, prox_weights = CS.SharePCS.prox_row, CS.SharePCS.prox_len, CS.SharePCS.prox_weights
    prox_rows_e, prox_len_e, prox_weights_e = CS.SharePCS.prox_rows_e, CS.SharePCS.prox_len_e, CS.SharePCS.prox_weights_e

VEC = ("x", "z1", "h", "z2", "d2", "b", "g1", "bg", "d1")
MAT = ("W1", "W2", "W1n", "W2n")

DEFER = False     # cut E (profile "DEFER", proof.md section 21): a step does not open its children W1n, W2n; it commits
                  # carries c1, c2 = W(r) - d(r_row) v(r_col), and the child's next opening (the next step, the release,
                  # the handover or a closing proof) discharges W_(k+1)(r_k) = c_k. Every W then has one life, hide T.
CARRY = ("c1", "c2")
CARRY_IN = ("c1p", "c2p")

def carry_m():
    """A carry holds the EXT components of one element: 2^m >= EXT entries."""
    return (X.EXT - 1).bit_length()

def w_shape(p, m):
    """A W matrix's shape: one life under DEFER (hide T, EXT proximity masks), else two."""
    if DEFER:
        return PubShape(p, m, CS.T_COLS, X.EXT, 0, lives=1)
    return None

def w_pcs(p, shares, label, **kw):
    """A W matrix's commitment (genesis, public genesis, a step's child): DEFER gives it one life, hide T."""
    if DEFER:
        return ZKPCS(p, shares, label, hide=CS.T_COLS, nmask=X.EXT, lives=1, **kw)
    return ZKPCS(p, shares, label, **kw)

def carry_shape(p, second):
    return PubShape(p, carry_m(), CS.LIVES * CS.T_COLS, CS.LIVES * X.EXT, X.EXT if second else 0, lives=CS.LIVES)

def shapes(p, d, chained, bind=False, deferred_in=False):
    """deferred_in (DEFER): the parent W's carry a pending claim, so the previous step's carries are carried in."""
    ld = d.bit_length() - 1
    sh = {}
    for k in VEC + MAT + (("xo",) if bind else ()):
        m = ld if k in VEC or k == "xo" else 2 * ld
        if DEFER and k in MAT:
            sh[k] = w_shape(p, m)
            continue
        sh[k] = PubShape(p, m, CS.HIDE, CS.NMASK, CS.NMASK // CS.LIVES if (chained and k in ("W1", "W2")) else 0)
    if DEFER:
        for k in CARRY:
            sh[k] = carry_shape(p, False)
        if deferred_in:
            for k in CARRY_IN:
                sh[k] = carry_shape(p, True)
    return sh

def opened(sh):
    """The commitments a step opens: under DEFER, not its children."""
    return {k: v for k, v in sh.items() if not (DEFER and k in ("W1n", "W2n"))}

def layout(d, ld):
    """The public schedule: (sumcheck name, kind, deg) and the evaluation list's commitment names."""
    sc = [("z1", "mv", 2), ("z2", "mv", 2), ("b", "mv", 2), ("bg", "zc", 3)]
    return sc

def lagc(deg, r, p):
    out = []
    for i in range(deg + 1):
        num = den = 1
        for j in range(deg + 1):
            if j != i:
                num = num * (r - j) % p
                den = den * (i - j) % p
        out.append(num * pow(den, -1, p) % p)
    return out

# ------------------------------------------------------------------------------------------------- shared
def specs(d):
    """Cut D's masking polynomials of the spine: (sumcheck, rounds, degree)."""
    ld = d.bit_length() - 1
    return [("z1", ld, 2), ("z2", ld, 2), ("b", ld, 2), ("bg", ld, 3)]

def schedule(tr, p, d, sh, round_roots_or_cb, bind=False, pre=None, deferred=None):
    """Replays the public part of the transcript up to the evaluation list. round_roots_or_cb(name, rnd) returns
    what the round puts in the transcript (ZKSC "rows": the round's Ligero roots, prover after committing, verifier
    from the proof; "mask": the opened round message, flat). pre(tr), if given, runs first (cut D: the g group's
    roots, the opened G values and rho). Returns the per-sumcheck challenges and the evaluation list. Every challenge
    is an F_{p^EXT} element (cosnark_ext)."""
    ld = d.bit_length() - 1
    if pre is not None:
        pre(tr)
    evals, scs, r1 = [], {}, {}
    for name, Wk, vk, zk, tp in (("z1", "W1", "x", "z1", False), ("z2", "W2", "h", "z2", False),
                                 ("b", "W2", "d2", "b", True)):
        tau = X.chal(tr, p, ld)
        rs = []
        for rnd in range(ld):
            tr.absorb("scr", round_roots_or_cb(name, rnd, tau, rs))
            rs.append(X.chal1(tr, p))
        scs[name] = (tau, rs)
        evals += [(zk, tau), (vk, rs), (Wk, (rs + tau) if not tp else (tau + rs))]
    tau = X.chal(tr, p, ld)
    rs = []
    for rnd in range(ld):
        tr.absorb("scr", round_roots_or_cb("bg", rnd, tau, rs))
        rs.append(X.chal1(tr, p))
    scs["bg"] = (tau, rs)
    evals += [("b", rs), ("g1", rs), ("bg", rs)]
    cpt = [X.zero()] * carry_m()
    for (Wn, Wo, dv, vv), cn in zip((("W1n", "W1", "d1", "x"), ("W2n", "W2", "d2", "h")), CARRY):
        rc, rr = X.chal(tr, p, ld), X.chal(tr, p, ld)
        r1[Wn] = (rc, rr)
        # DEFER: the child is not opened here; the carry c (its single row) stands for W(r) - d(r_row) v(r_col)
        evals += [(cn, cpt) if DEFER else (Wn, rc + rr), (Wo, rc + rr), (dv, rr), (vv, rc)]
    if bind:
        # signed-input binding: the owner's committed batch x and the custodians' x agree at a fresh point
        rb = X.chal(tr, p, ld)
        evals += [("xo", rb), ("x", rb)]
    if deferred is not None:
        # the parent's pending claims W(r_prev) = c_prev, at the previous step's points (from the ledger)
        for Wo, cn in (("W1", "c1p"), ("W2", "c2p")):
            evals += [(Wo, list(deferred[Wo])), (cn, cpt)]
    return scs, evals

def row_layout(d, sh, evals):
    """Hidden-row numbering, in commit order: rounds (z1, z2, b, bg; ld each; a round's value j, component k at
    position j EXT + k), then each evaluation's u rows (component-major: EXT blocks of ceil(W / K_L) rows), then the
    product rows x, y, z (EXT = 2: three cells per product, see constraints)."""
    ld = d.bit_length() - 1
    rows, nxt = {}, 0
    if ZKSC == "mask":
        rows["g"] = GMask(specs(d), 0)
        nxt = rows["g"].nrows
    else:
        for name in ("z1", "z2", "b", "bg"):
            rows[name] = list(range(nxt, nxt + ld)); nxt += ld
    urows = []
    for k, _ in evals:
        nr = -(-sh[k].W // K_L)
        urows.append(list(range(nxt, nxt + X.EXT * nr))); nxt += X.EXT * nr
    prod = (nxt, nxt + 1, nxt + 2)
    return rows, urows, prod, nxt + 3

# ---------------------------------------------------------------------- linear forms over F_{p^EXT} values
def evar(p, comps, coef):
    """The form coef * V, V a hidden value whose components are the linear forms comps (1 or EXT dicts {cell: c}),
    coef an element: EXT dicts, one per component of the product."""
    out = [dict() for _ in range(X.EXT)]
    def put(k, form, c):
        if c % p:
            o = out[k]
            for key, v in form.items():
                o[key] = (o.get(key, 0) + c * v) % p
    if len(comps) == 1:
        for k, ck in enumerate(coef):
            put(k, comps[0], ck)
    elif len(coef) == 1:
        for k in range(len(comps)):
            put(k, comps[k], coef[0])
    else:
        put(0, comps[0], coef[0]); put(0, comps[1], X.nr(p) * coef[1])
        put(1, comps[1], coef[0]); put(1, comps[0], coef[1])
    return out

def ecell(cells):
    """The component forms of a hidden value stored in the given cells."""
    return [{c: 1} for c in cells]

def eadder(p, lin, labels, cur):
    """add(*forms, rhs): sum E-forms, emit EXT F_p constraints (component order)."""
    def add(*forms, rhs=X.zero()):
        for k in range(X.EXT):
            t = {}
            for f in forms:
                for key, v in f[k].items():
                    t[key] = (t.get(key, 0) + v) % p
            lin.append(({kk: v for kk, v in t.items() if v}, (rhs[k] if k < len(rhs) else 0) % p))
            labels.append(cur[0])
    return add

def prod_forms(p, prod, q):
    Xr, Yr, Zr = prod
    if X.EXT == 1:
        return ecell([(Xr, q)]), ecell([(Yr, q)]), [{(Zr, q): 1}], []
    b = 3 * q
    m1 = p - 1
    xf = ecell([(Xr, b), (Xr, b + 1)])
    yf = ecell([(Yr, b), (Yr, b + 1)])
    zf = [{(Zr, b): 1, (Zr, b + 1): X.nr(p)}, {(Zr, b + 2): 1, (Zr, b): m1, (Zr, b + 1): m1}]
    aux = [{(Xr, b + 2): 1, (Xr, b): m1, (Xr, b + 1): m1}, {(Yr, b + 2): 1, (Yr, b): m1, (Yr, b + 1): m1}]
    return xf, yf, zf, aux

def prod_shares(L, xs, ys):
    """The product rows' shares from the operands' shares (xs[q], ys[q]: per party, tuples of EXT ints) by the
    Ligero's plain Beaver products (EXT = 2: P1, P2, P3 per gate, in that order)."""
    n, p = L.n, L.P.p
    if X.EXT == 1:
        zs = [L.mul_plain([x[i][0] for i in range(n)], [y[i][0] for i in range(n)]) for x, y in zip(xs, ys)]
        return ([[x[i][0] for x in xs] for i in range(n)], [[y[i][0] for y in ys] for i in range(n)],
                [[z[i] for z in zs] for i in range(n)])
    rx, ry, rz = [[] for _ in range(n)], [[] for _ in range(n)], [[] for _ in range(n)]
    for x, y in zip(xs, ys):
        xx = [[x[i][0], x[i][1], (x[i][0] + x[i][1]) % p] for i in range(n)]
        yy = [[y[i][0], y[i][1], (y[i][0] + y[i][1]) % p] for i in range(n)]
        zz = [L.mul_plain([xx[i][c] for i in range(n)], [yy[i][c] for i in range(n)]) for c in range(3)]
        for i in range(n):
            rx[i] += xx[i]; ry[i] += yy[i]; rz[i] += [zz[c][i] for c in range(3)]
    return rx, ry, rz

def check_rounds(p, name, msgs, rs, deg, claim0=None):
    """Cut D, the verifier's clear checks of one sumcheck's opened messages: shape, s_0(0) + s_0(1) = claim0 when it
    is public, and s_i(0) + s_i(1) = s_(i-1)(r_(i-1)). Returns None or the refusal."""
    if len(msgs) != len(rs) or any(len(m) != deg + 1 or any(len(v) != X.EXT for v in m) for m in msgs):
        return f"sumcheck {name}: round messages of the wrong shape"
    if claim0 is not None and X.add(msgs[0][0], msgs[0][1], p) != X.pad(claim0):
        return f"sumcheck {name}: first round sum differs from the public claim"
    for i in range(1, len(msgs)):
        if X.add(msgs[i][0], msgs[i][1], p) != X.pad(X.interp_at(msgs[i - 1], rs[i - 1], p)):
            return f"sumcheck {name}: round {i} sum differs from the previous round at r"
    return None

def unflat(v, deg):
    """A flat opened round message (EXT components per value) as deg + 1 elements."""
    E = X.EXT
    return [tuple(v[j * E:(j + 1) * E]) for j in range(deg + 1)]

def constraints(p, d, sh, scs, evals, cols, rows, urows, prod, mz=None, bind=False, deferred=False):
    """The verifier's checks as Ligero constraints on hidden values. cols[k] = (J, column sums at J). Every check
    is an identity over F_{p^EXT}, emitted as EXT F_p constraints (cosnark_ext; EXT = 1: the base system)."""
    lin, labels = [], []
    cur = ["?"]
    E = X.EXT
    add = eadder(p, lin, labels, cur)
    def U(e, c):
        nr = -(-sh[evals[e][0]].W // K_L)
        return ecell([(urows[e][k * nr + c // K_L], c % K_L) for k in range(E)])
    def Y(e, coef=X.one()):
        k, pt = evals[e]
        b = X.eqv(pt[:sh[k].mc], p)
        return fsum(*[evar(p, U(e, c), X.mul(coef, b[c], p)) for c in range(sh[k].C)])
    def fsum(*forms):
        out = [dict() for _ in range(E)]
        for f in forms:
            for k in range(E):
                for key, v in f[k].items():
                    out[k][key] = (out[k].get(key, 0) + v) % p
        return out
    def RC(r, j, coef=X.one()):
        return evar(p, ecell([(r, j * E + k) for k in range(E)]), coef)
    neg = lambda c: X.neg(c, p)
    # PCS evaluation consistency at the opened columns: component k of u_e against component k of a_e
    for e, (k, pt) in enumerate(evals):
        cur[0] = f"PCS evaluation consistency ({k})"
        s = sh[k]
        a = s.eval_weights_e(pt)
        J, csum = cols[k]
        for jj, j in enumerate(J):
            x = s.pts[j]
            xs, forms = 1, []
            for c in range(s.W):
                forms.append(evar(p, U(e, c), (xs,)))
                xs = xs * x % p
            add(*forms, rhs=X.dot(a, [(v,) for v in csum[jj]], p))
    pf = [prod_forms(p, prod, q) for q in range(NPROD)]
    def Zv(q, coef):
        return evar(p, pf[q][2], coef)
    def operands(q, ex, ey):
        cur[0] = f"product {q} operands"
        add(evar(p, pf[q][0], X.one()), Y(ex, neg(X.one())))      # x = W(..)
        add(evar(p, pf[q][1], X.one()), Y(ey, neg(X.one())))      # y = v(rs)
        for f_ in pf[q][3]:
            lin.append((f_, 0)); labels.append(f"product {q} operand sums")
    def sumcheck(name, deg, first, final_lin, q):
        """first: form for the initial claim (rows[0][0] + rows[0][1] = first); final_lin: the last claim's link."""
        tau, rs = scs[name]
        R = rows[name]
        cur[0] = f"sumcheck {name}: first round sum = claim"
        add(RC(R[0], 0), RC(R[0], 1), [{kk: (-v) % p for kk, v in f_.items()} for f_ in first])
        cur[0] = f"sumcheck {name}: round sums"
        for i in range(1, len(R)):
            lc = X.lagc(deg, rs[i - 1], p)
            add(RC(R[i], 0), RC(R[i], 1), *[RC(R[i - 1], j, neg(lc[j])) for j in range(deg + 1)])
        lc = X.lagc(deg, rs[-1], p)
        cur[0] = f"sumcheck {name}: final claim = product gate"
        add(*[RC(R[-1], j, lc[j]) for j in range(deg + 1)], final_lin)
    def sumcheck_mask(name, first, final):
        """Cut D: the g group's G constraint; first (a hidden claim's form, or None when the claim is public and
        checked in the clear): claim + rho G = s_0(0) + s_0(1); final: final + rho g(r) = s_l(r_l)."""
        gm, (tau, rs) = rows["g"], scs[name]
        msgs, G, rho = mz["msgs"][name], mz["G"][name], mz["rho"]
        cur[0] = f"sumcheck {name}: G = the sum of g over the cube"
        add(gm.lin_form(p, name, gm.G_coef(p, name), X.one()), rhs=G)
        if first is not None:
            cur[0] = f"sumcheck {name}: claim + rho G = first round sum"
            add(first, rhs=X.sub(X.add(msgs[0][0], msgs[0][1], p), X.mul(rho, G, p), p))
        cur[0] = f"sumcheck {name}: final + rho g(r) = last round at r"
        add(final, gm.lin_form(p, name, gm.at_coef(p, name, rs), rho), rhs=X.interp_at(msgs[-1], rs[-1], p))
    empty = [dict() for _ in range(E)]
    tau, rs = scs["bg"]
    eq = X.mle(X.eqv(tau, p), rs, p)
    for q, (name, idx) in enumerate((("z1", 0), ("z2", 3), ("b", 6))):
        if ZKSC == "mask":
            sumcheck_mask(name, Y(idx), Zv(q, X.one()))
        else:
            sumcheck(name, 2, Y(idx), Zv(q, neg(X.one())), q)
        operands(q, idx + 2, idx + 1)
    if ZKSC == "mask":
        sumcheck_mask("bg", None, fsum(Zv(3, eq), Y(11, neg(eq))))
    else:
        sumcheck("bg", 3, empty, fsum(Zv(3, neg(eq)), Y(11, eq)), 3)
    operands(3, 9, 10)
    def Cv(e, coef=X.one()):
        """A carry's value: its single u row's first EXT cells (component 0), as one element."""
        return evar(p, ecell([U(e, k)[0].popitem()[0] for k in range(E)]), coef)
    for q, base in ((4, 12), (5, 16)):          # W'(r) - W(r) + d(r_row) v(r_col) = 0
        if DEFER:
            cur[0] = f"rank-1 update {'W1n' if q == 4 else 'W2n'}: c = W(r) - d(r_row) v(r_col) (deferred)"
            add(Cv(base), Y(base + 1, neg(X.one())), Zv(q, X.one()))
        else:
            cur[0] = f"rank-1 update {'W1n' if q == 4 else 'W2n'}: W'(r) = W(r) - d(r_row) v(r_col)"
            add(Y(base), Y(base + 1, neg(X.one())), Zv(q, X.one()))
        operands(q, base + 2, base + 3)
    if bind or (not DEFER and len(evals) == 22):
        cur[0] = "signed input binding: the custodians' x = the owner's signed x"
        add(Y(20), Y(21, neg(X.one())))
    if deferred:
        e0 = 22 if bind else 20
        for i, nm in enumerate(("W1", "W2")):
            cur[0] = f"deferred claim of the parent {nm}: {nm}(r_prev) = c_prev"
            add(Y(e0 + 2 * i), Cv(e0 + 2 * i + 1, neg(X.one())))
    quad = [prod]
    return lin, quad, labels

# ------------------------------------------------------------------------------------------------- prover
def public_digest(public):
    """The public SPDZ transcript (the opened values), bound into Fiat-Shamir right after the context. Without
    it, colluding custodians could choose an opening value AFTER seeing the batch challenge (review3
    forge_public: a steered weight update accepted by the ledger)."""
    return CS.H("public-transcript", len(public), tuple(public))

def prove_zk(eng, wires, attack=None, carry=None, context=("model", 0, 0), seed=1, owner_x=None, public=(), deferred=None):
    """owner_x: the data owner's share-tuple commitment to x (dealt to the custodians with its opening), whose
    roots the owner signed; when given, the proof binds the custodians' x to it. deferred (DEFER): the previous
    step's stats["deferred"] (its points and carries), whose claims this step discharges."""
    p, n = eng.p, eng.n
    d = len(wires["x"])
    ld = d.bit_length() - 1
    flat = lambda M: [v for r in M for v in r]
    P = CS.Prover(eng, wires, attack)
    data = {k: wires[k] for k in VEC}
    data.update({k: flat(wires[k]) for k in MAT})
    com = {}
    wire0, open0 = dict(eng.wire), eng.nopen
    for k in VEC + MAT:
        shs = P.shares_of(data[k])
        if attack in ("forge_W1n", "lie_in_u") and k == "W1n":
            honest = [list(x) for x in shs]
            shs[0] = list(shs[0]); shs[0][5] = (shs[0][5] + 1) % p
            honest_W1n = honest
        if attack in ("forge_z1", "forge_sumcheck") and k == "z1":
            shs[0] = list(shs[0]); shs[0][3] = (shs[0][3] + 1) % p
        if carry and k in carry:
            com[k] = carry[k]
            if not DEFER:
                com[k].base = com[k].block
            continue
        if DEFER and k in MAT:
            com[k] = w_pcs(p, shs, k)
            continue
        com[k] = ZKPCS(p, shs, k)
    if owner_x is not None:
        com["xo"] = owner_x
    if deferred is not None:
        for k in CARRY_IN:
            com[k] = deferred["carries"][k]
            com[k].base = com[k].block            # the carry's second life
    L = Z.Prover(Z.Params(p, K_L, T_HIDE, T_OPEN), n, (seed, context))
    tr = Transcript("step-zk")
    tr.absorb("ctx", context)
    tr.absorb("public", public_digest(public))
    for k in sorted(com):
        tr.absorb(k, com[k].roots)
    state = {}
    tables = {"z1": ("W1", "x", False), "z2": ("W2", "h", False), "b": ("W2", "d2", True)}
    round_roots = {}
    def cb(name, rnd, tau, rs):
        """Compute round rnd of sumcheck `name` on shares, hide it as a Ligero row, commit, return the roots. Tables
        hold shared elements (cosnark_ext: tuples of engine values; a product costs 1, 2 or 3 Beaver triples)."""
        one = X.one()
        B = lambda v: (v,)
        if rnd == 0:
            if name == "bg":
                state[name] = dict(f=[B(v) for v in wires["b"]], g=[B(v) for v in wires["g1"]],
                                   sub=[B(v) for v in wires["bg"]], eq=X.eqv(tau, p), deg=3, claim=X.zero())
            else:
                Wk, vk, tp = tables[name]
                W, et = wires[Wk], X.eqv(tau, p)
                f = ([X.slin(eng, [(et[i], B(W[i][j])) for i in range(d)]) for j in range(d)] if not tp else
                     [X.slin(eng, [(et[j], B(W[i][j])) for j in range(d)]) for i in range(d)])
                claim = None
                if attack == "forge_sumcheck" and name == "z1":
                    zsum = [sum(com["z1"].rows[i][r][c] for i in range(n)) % p for r in range(com["z1"].Rd)
                            for c in range(com["z1"].C)]
                    claim = X.mle(zsum, tau, p)
                state[name] = dict(f=f, g=[B(v) for v in wires[vk]], sub=None, eq=None, deg=2, claim=claim)
        else:
            st = state[name]
            r = rs[-1]
            om = X.one_minus(r, p)
            fold = lambda T: [X.slin(eng, [(om, T[2 * k]), (r, T[2 * k + 1])]) for k in range(len(T) // 2)]
            st["f"], st["g"] = fold(st["f"]), fold(st["g"])
            if st["sub"] is not None:
                st["sub"] = fold(st["sub"])
            if st["eq"] is not None:
                st["eq"] = [X.add(X.mul(st["eq"][2 * k], om, p), X.mul(st["eq"][2 * k + 1], r, p), p)
                            for k in range(len(st["eq"]) // 2)]
            if st["claim"] is not None:
                st["claim"] = X.interp_at(st["last"], r, p)
        st = state[name]
        f, g, sub, eqt, deg = st["f"], st["g"], st["sub"], st["eq"], st["deg"]
        half = len(f) // 2
        vals = []
        for Xv in range(deg + 1):
            c0, c1 = ((1 - Xv) % p,), (Xv,)
            acc = None
            for k in range(half):
                lo, hi = 2 * k, 2 * k + 1
                term = X.smul(eng, X.slin(eng, [(c0, f[lo]), (c1, f[hi])]), X.slin(eng, [(c0, g[lo]), (c1, g[hi])]))
                if sub is not None:
                    term = X.ssub(eng, term, X.slin(eng, [(c0, sub[lo]), (c1, sub[hi])]))
                if eqt is not None:
                    term = X.scmul(eng, X.add(X.mul(eqt[lo], c0, p), X.mul(eqt[hi], c1, p), p), term)
                acc = term if acc is None else X.sadd(eng, acc, term)
            vals.append(X.spad(eng, acc))
        if ZKSC == "mask":
            return open_round(name, rnd, rs, vals, st, deg)
        shares = [[c for v in vals for c in X.shares(v, i)] for i in range(n)]
        if st["claim"] is not None:
            # colluders: make the hidden round sum match the (forged) claim
            E = X.EXT
            plain = [tuple(sum(sh_[j * E + kk] for sh_ in shares) % p for kk in range(E)) for j in range(deg + 1)]
            fix = X.scal(pow(2, -1, p), X.sub(st["claim"], X.add(plain[0], plain[1], p), p), p)
            fix = fix + (0,) * (E - len(fix))
            shares[0] = [(v + fix[pos % E]) % p for pos, v in enumerate(shares[0])]
            st["last"] = [X.add(v, fix, p) for v in plain]
        L.add_row(shares)
        roots = L.commit()
        round_roots.setdefault(name, []).append(roots)
        return roots
    mz = dict(msgs={}, G={}, rho=None)
    def pre(tr_):
        """Cut D: commit every g of the spine as one group, open the G values, draw rho."""
        gm = GMask(specs(d), 0)
        mz["gsh"], mz["g_roots"] = gm.commit(L)
        mz["gm"] = gm
        for name, _, _ in gm.specs:
            Gs = [gm.share_val(p, mz["gsh"][i], name, gm.G_coef(p, name)) for i in range(n)]
            if attack == "forge_G" and name == "z2":
                Gs[0] = X.add(Gs[0], X.one(), p)
            mz["G"][name] = open_sum(p, Gs)
        tr_.absorb("zkg", mz["g_roots"])
        tr_.absorb("G", X.flat([mz["G"][nm] for nm, _, _ in gm.specs]))
        mz["rho"] = X.chal1(tr_, p)
    def open_round(name, rnd, rs, vals, st, deg):
        """Cut D: every custodian broadcasts its share of s_rnd = f-part + rho g-part; the opened values go in the
        transcript and the bundle."""
        gm, rho = mz["gm"], mz["rho"]
        if rnd == 0 and st.get("claim") is not None:
            st["claim"] = X.add(st["claim"], X.mul(rho, mz["G"][name], p), p)
        plain = []
        for t in range(deg + 1):
            cf = gm.round_coef(p, name, rnd, t, rs)
            per = [X.add(X.shares(vals[t], i), X.mul(rho, gm.share_val(p, mz["gsh"][i], name, cf), p), p)
                   for i in range(n)]
            if attack == "bad_share" and name == "b" and rnd == 0 and t == 0:
                per[0] = X.add(per[0], X.one(), p)
            plain.append(open_sum(p, per))
        if st.get("claim") is not None:
            # colluders: shift the opened message so its sum matches the (forged) claim
            fix = X.pad(X.scal(pow(2, -1, p), X.sub(st["claim"], X.add(plain[0], plain[1], p), p), p))
            plain = [X.add(v, fix, p) for v in plain]
        if attack == "forge_round" and name == "z2" and rnd == 1:
            # a forged message whose own sum is kept: +c at X = 0, -c at X = 1; later rounds follow its value at r
            plain[0] = X.add(plain[0], (5,), p)
            plain[1] = X.sub(plain[1], (5,), p)
            st["claim"] = X.zero()
        st["last"] = plain
        mz["msgs"].setdefault(name, []).append(plain)
        return X.flat(plain)
    dpts = deferred["points"] if deferred is not None else None
    sh_pub = shapes(p, d, True, owner_x is not None, deferred is not None) if DEFER else None
    scs, evals = schedule(tr, p, d, {**com, **({k: sh_pub[k] for k in CARRY} if DEFER else {})}, cb,
                          bind=owner_x is not None, pre=pre if ZKSC == "mask" else None, deferred=dpts)
    pairs = [(2, 1), (5, 4), (8, 7), (9, 10), (14, 15), (18, 19)]       # (x, y) evaluation indices per product
    if DEFER:
        # the products first (none involves a carry), then the carries c = W(r) - d(r_row) v(r_col), committed and
        # absorbed after every schedule challenge and before the evaluation rows
        ys0 = {}
        for e in sorted({a for pr in pairs for a in pr} | {13, 17}):
            k, pt = evals[e]
            c = com[k]
            a = c.eval_weights_e(pt)
            u = [c.row_combo_e(i, a) for i in range(n)]
            b = X.eqv(pt[:c.mc], p)
            ys0[e] = [X.dot([tuple(u[i][kk][cc] for kk in range(X.EXT)) for cc in range(c.C)], b, p) for i in range(n)]
        rx, ry, rz = prod_shares(L, [ys0[a] for a, _ in pairs], [ys0[b] for _, b in pairs])
        def zval(i, q):
            if X.EXT == 1:
                return (rz[i][q],)
            P1, P2, P3 = rz[i][3 * q:3 * q + 3]
            return ((P1 + X.nr(p) * P2) % p, (P3 - P1 - P2) % p)
        cshares = {}
        for q, wi, cn in ((4, 13, "c1"), (5, 17, "c2")):
            dl = [X.pad(X.sub(ys0[wi][i], zval(i, q), p)) for i in range(n)]
            cshares[cn] = [list(v) + [0] * ((1 << carry_m()) - X.EXT) for v in dl]
            com[cn] = ZKPCS(p, cshares[cn], cn, hide=CS.LIVES * CS.T_COLS, nmask=CS.LIVES * X.EXT, lives=CS.LIVES)
        tr.absorb("carry", com["c1"].roots, com["c2"].roots)
    rows, urows, prod, nrows = row_layout(d, com, evals)
    # hidden evaluation row combinations u_e (no masks; EXT components) and the evaluation values' shares
    ushares, yshares = [], []
    for e, (k, pt) in enumerate(evals):
        c = com[k]
        a = c.eval_weights_e(pt)
        u = [c.row_combo_e(i, a) for i in range(n)]
        if attack == "lie_in_u" and k == "W1n":
            hon = [list(honest_W1n[0][r * c.C:(r + 1) * c.C]) + c.ext[0][r][c.C:] for r in range(c.Rd)] + c.ext[0][c.Rd:]
            u[0] = [[sum(a[r][kk] * hon[r][cc] for r in range(c.R) if kk < len(a[r])) % p for cc in range(c.W)]
                    for kk in range(X.EXT)]
        b = X.eqv(pt[:c.mc], p)
        ushares.append(u)
        yshares.append([X.dot([tuple(u[i][kk][cc] for kk in range(X.EXT)) for cc in range(c.C)], b, p) for i in range(n)])
        for kk in range(X.EXT):
            for s0 in range(0, c.W, K_L):
                L.add_row([u[i][kk][s0:s0 + K_L] for i in range(n)])
    if not DEFER:
        rx, ry, rz = prod_shares(L, [yshares[a] for a, _ in pairs], [yshares[b] for _, b in pairs])
    L.add_row(rx)
    L.add_row(ry)
    L.add_row(rz)
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    _, prox, pcols = CS.pcs_prove(opened(com), [], tr, n, p)
    cols = {k: (pcols[k][0], [[sum(pcols[k][1][i][jj][0][r] for i in range(n)) % p for r in range(com[k].R)]
                              for jj in range(len(pcols[k][0]))]) for k in opened(com)}
    lin, quad, labels = constraints(p, d, com, scs, evals, cols, rows, urows, prod, mz=mz, bind=owner_x is not None,
                                    deferred=deferred is not None)
    lig = L.prove(tr, lin, quad)
    eng.mac_check("cosnark-zk")
    proof = dict(roots={k: com[k].roots for k in sorted(com)}, eval_roots=eval_roots,
                 mask_roots=mask_roots, prox={k: prox[k][1] for k in sorted(prox)},
                 pcs_cols={k: pcols[k] for k in sorted(pcols)}, ligero=lig)
    if ZKSC == "mask":
        proof.update(g_roots=mz["g_roots"], G=X.flat([mz["G"][nm] for nm, _, _ in specs(d)]),
                     rounds={nm: [X.flat(m) for m in mz["msgs"][nm]] for nm, _, _ in specs(d)})
    else:
        proof["round_roots"] = round_roots
    stats = dict(hidden_rows=nrows, hidden_values=nrows * K_L, lin_constraints=len(lin), products=NPROD,
                 ligero_wire=L.wire, ligero_beaver_scalar=L.scalar_triples, ligero_poly_triples=L.poly_triples,
                 spdz_wire={ph: v - wire0.get(ph, 0) for ph, v in eng.wire.items() if v != wire0.get(ph, 0)},
                 spdz_openings=eng.nopen - open0,
                 child={"W1": com["W1n"], "W2": com["W2n"]}, coms=com,
                 deferred=dict(points={"W1": evals[13][1], "W2": evals[17][1]},
                               carries={"c1p": com["c1"], "c2p": com["c2"]}) if DEFER else None,
                 first_violated=first_violated(p, L.rows, lin, quad, labels))
    return proof, stats

# ------------------------------------------------------------------------------------------------- verifier
def verify_zk(p, n, d, context, parent_roots, chained, proof, bind=False, public=(), deferred=None, out=None):
    """Public data only. parent_roots: the previous step's child roots for W1, W2 (None at genesis). bind: the
    proof must carry the owner's commitment "xo" and the binding constraint (its roots are checked against the
    owner's signature by the caller). DEFER: deferred = the parent's pending claims from the LEDGER (dict points
    {"W1", "W2"} and carry roots {"c1p", "c2p"}), None when the parent is final (public genesis); out, if given,
    receives this step's own pending claims (points and carry roots) for the ledger."""
    ld = d.bit_length() - 1
    sh = shapes(p, d, chained, bind, deferred is not None)
    roots = proof["roots"]
    want = VEC + MAT + (("xo",) if bind else ()) + ((CARRY + (CARRY_IN if deferred is not None else ())) if DEFER else ())
    if sorted(roots) != sorted(want):
        return False, "proof names the wrong commitments"
    if parent_roots is not None and (roots["W1"] != parent_roots["W1"] or roots["W2"] != parent_roots["W2"]):
        return False, "parent commitment is not the previous step's child commitment"
    if deferred is not None and any(roots[k] != deferred["carry_roots"][k] for k in CARRY_IN):
        return False, "the parent's carry commitments are not the previous step's"
    tr = Transcript("step-zk")
    tr.absorb("ctx", context)
    tr.absorb("public", public_digest(public))
    for k in sorted(roots):
        if DEFER and k in CARRY:
            continue                     # committed after r_k: absorbed below ("carry")
        tr.absorb(k, roots[k])
    E = X.EXT
    mz = None
    if ZKSC == "mask":
        rd = proof.get("rounds")
        sp = specs(d)
        if rd is None or sorted(rd) != ["b", "bg", "z1", "z2"] or any(len(rd[k]) != ld for k in rd) or \
                len(proof.get("G", ())) != E * len(sp) or len(proof.get("g_roots", ())) != n:
            return False, "wrong number of sumcheck rounds"
        degs = {nm: dg for nm, _, dg in sp}
        mz = dict(G={nm: tuple(proof["G"][E * i:E * (i + 1)]) for i, (nm, _, _) in enumerate(sp)},
                  msgs={nm: [unflat(v, degs[nm]) for v in rd[nm]] for nm in rd}, rho=None)
        def pre(tr_):
            tr_.absorb("zkg", proof["g_roots"])
            tr_.absorb("G", list(proof["G"]))
            mz["rho"] = X.chal1(tr_, p)
        if any(len(v) != E * (degs[nm] + 1) for nm in rd for v in rd[nm]):
            return False, "sumcheck round messages of the wrong shape"
        scs, evals = schedule(tr, p, d, sh, lambda name, rnd, tau, rs: rd[name][rnd], bind=bind, pre=pre,
                              deferred=deferred["points"] if deferred is not None else None)
        for nm, _, dg in sp:
            why = check_rounds(p, nm, mz["msgs"][nm], scs[nm][1], dg,
                               X.mul(mz["rho"], mz["G"][nm], p) if nm == "bg" else None)
            if why:
                return False, why
    else:
        rr = proof["round_roots"]
        if sorted(rr) != ["b", "bg", "z1", "z2"] or any(len(rr[k]) != ld for k in rr):
            return False, "wrong number of sumcheck rounds"
        scs, evals = schedule(tr, p, d, sh, lambda name, rnd, tau, rs: rr[name][rnd], bind=bind,
                              deferred=deferred["points"] if deferred is not None else None)
    if DEFER:
        tr.absorb("carry", roots["c1"], roots["c2"])
        if out is not None:
            out.update(points={"W1": evals[13][1], "W2": evals[17][1]},
                       carry_roots={"c1p": roots["c1"], "c2p": roots["c2"]})
    rows, urows, prod, nrows = row_layout(d, sh, evals)
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    osh = opened(sh)
    ok, why = CS.pcs_verify(osh, {k: roots[k] for k in osh}, [], [], {k: (None, proof["prox"][k]) for k in osh},
                            proof["pcs_cols"], tr, n, p)
    if not ok:
        return ok, why
    pc = proof["pcs_cols"]
    cols = {k: (pc[k][0], [[sum(pc[k][1][i][jj][0][r] for i in range(n)) % p for r in range(sh[k].R)]
                           for jj in range(len(pc[k][0]))]) for k in osh}
    lin, quad, _ = constraints(p, d, sh, scs, evals, cols, rows, urows, prod, mz=mz, bind=bind,
                               deferred=deferred is not None)
    if ZKSC == "mask":
        ng = rows["g"].nrows
        group_roots, sizes = [proof["g_roots"], proof["eval_roots"]], [ng, nrows - ng]
    else:
        group_roots = [rr[nm][i] for nm in ("z1", "z2", "b", "bg") for i in range(ld)] + [proof["eval_roots"]]
        sizes = [1] * (4 * ld) + [nrows - 4 * ld]
    return Z.verify(Z.Params(p, K_L, T_HIDE, T_OPEN), n, group_roots, sizes, proof["mask_roots"], lin, quad,
                    proof["ligero"], tr)

def first_violated(p, rows, lin, quad, labels):
    """DIAGNOSTIC ONLY (prover side, plaintext): the first constraint the hidden witness violates, so a harness
    can say WHICH check refused a forgery. The verifier never runs this; it only sees the Ligero tests fail."""
    val = lambda r, pos: sum(sh[pos] for sh in rows[r]) % p
    for (terms, rhs), lab in zip(lin, labels):
        if sum(c * val(r, pos) for (r, pos), c in terms.items()) % p != rhs:
            return lab
    for x, y, z in quad:
        for pos in range(len(rows[x][0])):
            if val(x, pos) * val(y, pos) % p != val(z, pos):
                return f"product gate {pos}"
    return None

# ------------------------------------------------------------------------------------------------- counts
def measure(proof, n):
    """Sizes read off a proof object (field elements, 256-bit hashes, column indices)."""
    fe = hs = idx = 0
    for k, (J, cols) in proof["pcs_cols"].items():
        idx += len(J)
        for i in range(n):
            for col, path in cols[i]:
                fe += len(col); hs += len(path)
    fe += sum(len(u) for v in proof["prox"].values() for u in v)
    hs += sum(len(v) for v in proof["roots"].values())
    hs += sum(len(r) for v in proof["round_roots"].values() for r in v) + len(proof["eval_roots"]) + len(proof["mask_roots"])
    lg = proof["ligero"]
    fe += len(lg["w"]) + len(lg["q"]) + len(lg["pq"])
    for g in lg["cols"]:
        for i in range(n):
            for col, path in g[i]:
                fe += len(col); hs += len(path)
    return dict(field_elems=fe, hashes=hs, indices=idx, bits=61 * fe + 256 * hs)

def counts_formula(d, n=3, hide=None, nmask=None, k=None, t=None, T=None):
    # read at call time: defaults bound at def time ignored a pinned T (proofwire.pin_params)
    k, t, T = k or K_L, t or T_HIDE, T or T_OPEN
    hide = CS.HIDE if hide is None else hide
    nmask = CS.NMASK if nmask is None else nmask
    ld = d.bit_length() - 1
    vec, mat = CS.shape(ld), CS.shape(2 * ld)
    coms = [vec] * 9 + [mat] * 4
    evals = [vec, vec, mat] * 3 + [vec] * 3 + [mat, mat, vec, vec] * 2
    W = lambda C: C + hide
    lgp = lambda C: (CS.BLOW * W(C) - 1).bit_length() + 1       # + the leaf salt
    rows = 4 * ld + sum(-(-W(C) // k) for _, C in evals) + 3
    groups = 4 * ld + 1
    npts = 4 * (k + t)
    lgL = (npts - 1).bit_length() + 1
    lin = len(evals) * CS.T_COLS + 4 * (ld + 1) + 2 * NPROD + 2
    muls = 9 * (d - 1) + 4 * (d - 1)
    pcs_fe = sum(n * W(C) for _, C in coms) + sum(n * CS.T_COLS * (R + nmask) for R, _ in coms)
    pcs_h = sum(n * CS.T_COLS * lgp(C) for _, C in coms) + n * 13
    lig_fe = (k + t) + (2 * k + t - 1) + (2 * (k + t) - 1) + n * T * (rows + 3)
    lig_h = n * T * lgL * (groups + 1) + n * (groups + 1)
    fe, hs = pcs_fe + lig_fe, pcs_h + lig_h
    return dict(hidden_rows=rows, hidden_values=rows * k, lin_constraints=lin, products=NPROD,
                ligero_wire=n * (n - 1) * (3 * (k + t) + (2 * k + t - 1) + (2 * (k + t) - 1) + 2 * NPROD),
                ligero_beaver_scalar=NPROD, ligero_poly_triples=1,
                spdz_wire={"mul": muls * 2 * n * (n - 1), "mac_check": 2 * n * (n - 1)}, spdz_openings=2 * muls,
                proof=dict(field_elems=fe, hashes=hs, indices=13 * CS.T_COLS, bits=61 * fe + 256 * hs),
                pcs_part_bits=61 * pcs_fe + 256 * pcs_h, ligero_part_bits=61 * lig_fe + 256 * lig_h)

def measure_any(proof, n):
    """Field elements and hashes of any proof object: ints count as field elements, 64-hex strings as hashes
    (column indices are counted with the field elements here)."""
    fe = hs = 0
    stack = [proof]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            stack.extend(x.values())
        elif isinstance(x, (list, tuple)):
            stack.extend(x)
        elif isinstance(x, int):
            fe += 1
        elif isinstance(x, str):
            hs += 1
    return dict(field_elems=fe, hashes=hs, bits=61 * fe + 256 * hs)

def owner_commit(p, vec, label, n=3):
    """The data owner deals vec as n additive shares and commits the share tuple with secret tails (ZKPCS). It
    signs the roots; the custodians receive the commitment object (their shares and openings)."""
    import secrets
    det = CS.det_rng("owner-commit", label, CS.H(list(vec)))          # TEST ONLY (cosnark.det_rng)
    sh = [[det.randrange(p) if det else secrets.randbelow(p) for _ in vec] for _ in range(n - 1)]
    sh.append([(v - sum(c)) % p for v, c in zip(vec, zip(*sh))])
    return ZKPCS(p, sh, label)

# ------------------------------------------------------------------------------------------------- closing proof
def close_evals(deferred_points):
    cpt = [X.zero()] * carry_m()
    return [(k, list(deferred_points[k])) for k in ("W1", "W2")] + [(k, cpt) for k in CARRY_IN]

def close_constraints(p, sh, evals, cols, urows):
    """The closing proof's checks: PCS consistency of the four evaluations, and W(r_k) = c_k for both updates."""
    lin, labels, cur = [], [], ["?"]
    E = X.EXT
    add = eadder(p, lin, labels, cur)
    def U(e, c):
        nr = -(-sh[evals[e][0]].W // K_L)
        return ecell([(urows[e][k * nr + c // K_L], c % K_L) for k in range(E)])
    for e, (k, pt) in enumerate(evals):
        cur[0] = f"PCS evaluation consistency ({k})"
        s = sh[k]
        a = s.eval_weights_e(pt)
        J, csum = cols[k]
        for jj, j in enumerate(J):
            x, xs, forms = s.pts[j], 1, []
            for c in range(s.W):
                forms.append(evar(p, U(e, c), (xs,)))
                xs = xs * x % p
            add(*forms, rhs=X.dot(a, [(v,) for v in csum[jj]], p))
    for i, nm in enumerate(("W1", "W2")):
        k, pt = evals[i]
        b = X.eqv(pt[:sh[k].mc], p)
        Yf = [dict() for _ in range(E)]
        for c in range(sh[k].C):
            f_ = evar(p, U(i, c), b[c])
            for kk in range(E):
                for key, v in f_[kk].items():
                    Yf[kk][key] = (Yf[kk].get(key, 0) + v) % p
        Cf = evar(p, ecell([U(2 + i, k2)[0].popitem()[0] for k2 in range(E)]), X.neg(X.one(), p))
        cur[0] = f"closing: {nm}(r_k) = c_k"
        add(Yf, Cf)
    return lin, labels

def prove_close(p, n, coms, deferred, context, seed=3):
    """A halted run's standalone discharge (cut E): the head's W1, W2 (coms, their single life) opened at the last
    step's points, against its carries (deferred["carries"], second life). No MPC product is needed."""
    com = {"W1": coms["W1"], "W2": coms["W2"]}
    for k in CARRY_IN:
        com[k] = deferred["carries"][k]
        com[k].base = com[k].block
    L = Z.Prover(Z.Params(p, K_L, T_HIDE, T_OPEN), n, (seed, context))
    tr = Transcript("close-zk")
    tr.absorb("ctx", context)
    for k in sorted(com):
        tr.absorb(k, com[k].roots)
    evals = close_evals(deferred["points"])
    urows, nxt = [], 0
    for k, pt in evals:
        c = com[k]
        a = c.eval_weights_e(pt)
        u = [c.row_combo_e(i, a) for i in range(n)]
        nr = -(-c.W // K_L)
        urows.append(list(range(nxt, nxt + X.EXT * nr))); nxt += X.EXT * nr
        for kk in range(X.EXT):
            for s0 in range(0, c.W, K_L):
                L.add_row([u[i][kk][s0:s0 + K_L] for i in range(n)])
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    _, prox, pcols = CS.pcs_prove(com, [], tr, n, p)
    cols = {k: (pcols[k][0], [[sum(pcols[k][1][i][jj][0][r] for i in range(n)) % p for r in range(com[k].R)]
                              for jj in range(len(pcols[k][0]))]) for k in com}
    lin, labels = close_constraints(p, com, evals, cols, urows)
    lig = L.prove(tr, lin, [])
    proof = dict(roots={k: com[k].roots for k in sorted(com)}, eval_roots=eval_roots, mask_roots=mask_roots,
                 prox={k: prox[k][1] for k in sorted(prox)}, pcs_cols={k: pcols[k] for k in sorted(pcols)}, ligero=lig)
    return proof, dict(first_violated=first_violated(p, L.rows, lin, [], labels), hidden_rows=nxt)

def close_shapes(p, d):
    ld = d.bit_length() - 1
    sh = {k: w_shape(p, 2 * ld) for k in ("W1", "W2")}
    sh.update({k: carry_shape(p, True) for k in CARRY_IN})
    return sh

def verify_close(p, n, d, context, head_roots, deferred, proof):
    """Public data only: head_roots = the head's W1, W2 roots, deferred = its pending claims, both from the ledger."""
    sh = close_shapes(p, d)
    roots = proof["roots"]
    if sorted(roots) != sorted(sh):
        return False, "closing proof names the wrong commitments"
    if any(roots[k] != head_roots[k] for k in ("W1", "W2")) or any(roots[k] != deferred["carry_roots"][k] for k in CARRY_IN):
        return False, "closing proof is not over the head's commitments and carries"
    tr = Transcript("close-zk")
    tr.absorb("ctx", context)
    for k in sorted(roots):
        tr.absorb(k, roots[k])
    evals = close_evals(deferred["points"])
    urows, nxt = [], 0
    for k, _ in evals:
        nr = -(-sh[k].W // K_L)
        urows.append(list(range(nxt, nxt + X.EXT * nr))); nxt += X.EXT * nr
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    ok, why = CS.pcs_verify(sh, roots, [], [], {k: (None, proof["prox"][k]) for k in sh}, proof["pcs_cols"], tr, n, p)
    if not ok:
        return ok, why
    pc = proof["pcs_cols"]
    cols = {k: (pc[k][0], [[sum(pc[k][1][i][jj][0][r] for i in range(n)) % p for r in range(sh[k].R)]
                           for jj in range(len(pc[k][0]))]) for k in sh}
    lin, _ = close_constraints(p, sh, evals, cols, urows)
    return Z.verify(Z.Params(p, K_L, T_HIDE, T_OPEN), n, [proof["eval_roots"]], [nxt], proof["mask_roots"], lin, [],
                    proof["ligero"], tr)
