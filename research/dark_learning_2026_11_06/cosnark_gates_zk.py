"""ZK layers 2-3 for the collaborative proof's MIDDLE (cosnark_gates.py): SPDZ execution integrity of the
nonlinear gates, with no round value, claim or evaluation revealed. Same machinery as cosnark_zk.py.

2026-11-06. Hidden (collaborative Ligero, cozk.py):
  - the Hadamard zerocheck's round messages (one row per round, committed before its challenge);
  - the 13 claims c_X = <q_X, X> (one row, committed before the linear sumcheck starts);
  - the 13 linear sumchecks, run IN LOCKSTEP with shared challenges after zero-padding every X to the longest:
    one hidden row of 13 x 3 values per round. A padded vector's MLE is X~(r[:m]) * prod_{j >= m} (1 - r_j);
  - every PCS evaluation's row combination u_e (consistency at the opened columns as linear constraints).
Constraints: the batch identity sum_X c_X + const = 0, round sums and Lagrange steps, the linear finals
c-chain = mle(q_X)(r) * pad(r) * X~(r[:m]) (public coefficient, LINEAR), and the zerocheck final with ONE
product gate A~(rho) B~(rho).
A spine vector that the middle re-commits (z1, z2, b, h, g1, d2, bg, d1) is opened in two proofs, the spine's
and this one. The middle therefore uses its SECOND life, i.e. its second proximity mask row: reusing one mask
row in two proofs would reveal a difference of data combinations. Its tails cover 2 x T_COLS columns.
"""
import cosnark as CS
import cosnark_gates as G
import cosnark_zk as ZK
import cozk as Z
import cosnark_ext as X
import spdz
from cosnark import Transcript, eqv, mle

NAMES = ("z1", "z2", "b", "y", "h", "g1", "d2", "bg", "d1")
SPINE = ("z1", "z2", "b", "h", "g1", "d2", "bg", "d1")

class IO:
    """The middle's external vectors for a program other than the step (the release, cosnark_release): names, their
    lengths (powers of two), the CARRIED ones (an existing commitment, used at its second life) and their shapes, and
    the transcript label. None everywhere below means the step's (NAMES, SPINE, "middle-zk")."""
    def __init__(self, lens, carried, label, shapes=None):
        self.lens, self.carried, self.label, self.shapes = dict(lens), tuple(carried), label, dict(shapes or {})
        self.names = tuple(sorted(self.lens))

def build_q(p, sym, cons, had, prep, lens, gam):
    """gam: F_{p^EXT} elements; q's entries and const are elements (an untouched entry stays the base zero)."""
    pos = {a: k for k, a in enumerate(prep)}
    q = {k: [X.zero()] * L for k, L in lens.items()}
    const = X.zero()
    for g, (form, c0, val, _) in zip(gam, cons):
        for a, co in form.items():
            kind, tag = sym.atoms[a]
            if kind == "ext":
                nm, k = tag
                q[nm][k] = X.add(q[nm][k], X.scal(co, g, p), p)
            else:
                q["P"][pos[a]] = X.add(q["P"][pos[a]], X.scal(co, g, p), p)
        const = X.add(const, X.scal(c0 - val, g, p), p)
    g3 = gam[len(cons):]
    for k, (a, b, c) in enumerate(had):
        for j, (vn, at) in enumerate((("A", a), ("B", b), ("C", c))):
            g = g3[3 * k + j]
            q[vn][k] = X.add(q[vn][k], g, p)
            q["P"][pos[at]] = X.sub(q["P"][pos[at]], g, p)
    return q, const

def plen(x):
    n = 1
    while n < max(1, x):
        n *= 2
    return n

def public_shapes(p, prep, had, d, bind=False, io=None):
    """lens: the vectors in the linear batch. sh: every commitment's shape, including the owner's "yo"
    (committed and evaluated, but not in the batch)."""
    lens = dict(P=plen(len(prep)), A=plen(len(had)), B=plen(len(had)), C=plen(len(had)))
    lens.update({nm: plen(d) for nm in NAMES} if io is None else io.lens)
    carried = SPINE if io is None else io.carried
    sh = {k: ZK.PubShape(p, (L - 1).bit_length(), CS.HIDE, CS.NMASK,
                         CS.NMASK // CS.LIVES if k in carried else 0) for k, L in lens.items()}
    if io is not None:
        sh.update(io.shapes)
    if bind:
        sh["yo"] = ZK.PubShape(p, (plen(d) - 1).bit_length(), CS.HIDE, CS.NMASK, 0)
    return lens, sh

def specs(lens):
    """Cut D's masking polynomials of the middle: the zerocheck, then one per linear sumcheck (sorted names)."""
    lh = (lens["A"] - 1).bit_length()
    Lmax = max((L - 1).bit_length() for L in lens.values())
    return [("zc", lh, 3)] + [(f"l:{k}", Lmax, 2) for k in sorted(lens)]

def schedule(tr, p, lens, round_cb, claims_cb, lin_cb, pre=None):
    """Public schedule. Returns (zerocheck tau, zrs), (gam drawn by caller), batched rr, and the evaluation list.
    pre(tr): cut D's g group, G values and rho, before tau."""
    lh = (lens["A"] - 1).bit_length()
    if pre is not None:
        pre(tr)
    tau = X.chal(tr, p, lh)
    zrs = []
    for rnd in range(lh):
        tr.absorb("zc", round_cb(rnd, tau, zrs))
        zrs.append(X.chal1(tr, p))
    ks = sorted(lens)
    gam = tr.chal(p, -1) if False else None
    return tau, zrs, ks

def run_linear_schedule(tr, p, lens, ks, claims_root, lin_cb):
    tr.absorb("claims", claims_root)
    Lmax = max((lens[k] - 1).bit_length() for k in ks)
    rr = []
    for rnd in range(Lmax):
        tr.absorb("lsc", lin_cb(rnd, rr))
        rr.append(X.chal1(tr, p))
    return rr

def evaluations(lens, ks, zrs, rr, rb=None):
    ev = [("A", zrs), ("B", zrs), ("C", zrs)]
    for k in ks:
        m = (lens[k] - 1).bit_length()
        ev.append((k, rr[:m]))
    if rb is not None:
        ev += [("yo", rb), ("y", rb)]          # signed-input binding for y
    return ev

def row_layout(sh, ev, lh, Lmax, lens=None):
    """ZKSC "mask" (cut D): the g group's rows first (zrows is the GMask, lrows None), then the claims row."""
    nxt = 0
    if ZK.ZKSC == "mask":
        zrows = ZK.GMask(specs(lens), 0)
        nxt = zrows.nrows
        crow = nxt; nxt += 1
        lrows = None
    else:
        zrows = list(range(nxt, nxt + lh)); nxt += lh
        crow = nxt; nxt += 1
        lrows = list(range(nxt, nxt + Lmax)); nxt += Lmax
    urows = []
    for k, _ in ev:
        nr = -(-sh[k].W // ZK.K_L)
        urows.append(list(range(nxt, nxt + X.EXT * nr))); nxt += X.EXT * nr
    return zrows, crow, lrows, urows, (nxt, nxt + 1, nxt + 2), nxt + 3

def constraints(p, sh, lens, ks, ev, cols, layout, tau, zrs, rr, q, const, mz=None):
    """As cosnark_zk.constraints: identities over F_{p^EXT}, EXT F_p constraints each. A round's or the claims
    row's value j, component k, sits at position j EXT + k."""
    zrows, crow, lrows, urows, prod, _ = layout
    lin, labels, cur = [], [], ["?"]
    K, E = ZK.K_L, X.EXT
    add = ZK.eadder(p, lin, labels, cur)
    ev_, ecell = ZK.evar, ZK.ecell
    def U(e, c):
        nr = -(-sh[ev[e][0]].W // K)
        return ecell([(urows[e][kk * nr + c // K], c % K) for kk in range(E)])
    def fsum(*forms):
        out = [dict() for _ in range(E)]
        for f in forms:
            for kk in range(E):
                for key, v in f[kk].items():
                    out[kk][key] = (out[kk].get(key, 0) + v) % p
        return out
    def Y(e, coef=X.one()):
        k, pt = ev[e]
        b = X.eqv(pt[:sh[k].mc], p)
        return fsum(*[ev_(p, U(e, c), X.mul(coef, b[c], p)) for c in range(sh[k].C)])
    def RC(r, j, coef=X.one()):
        return ev_(p, ecell([(r, j * E + kk) for kk in range(E)]), coef)
    neg = lambda c: X.neg(c, p)
    m1 = neg(X.one())
    for e, (k, pt) in enumerate(ev):
        cur[0] = f"PCS evaluation consistency ({k})"
        s = sh[k]
        a = s.eval_weights_e(pt)
        J, csum = cols[k]
        for jj, j in enumerate(J):
            x, xs, forms = s.pts[j], 1, []
            for c in range(s.W):
                forms.append(ev_(p, U(e, c), (xs,)))
                xs = xs * x % p
            add(*forms, rhs=X.dot(a, [(v,) for v in csum[jj]], p))
    mask = ZK.ZKSC == "mask"
    def G_and_final(name, first, final, pts):
        """Cut D: G constraint; claim + rho G = s_0(0) + s_0(1) (first: hidden claim form, or None: public);
        final + rho g(r) = s_l(r_l)."""
        gm, msgs, G, rho = zrows, mz["msgs"][name], mz["G"][name], mz["rho"]
        cur[0] = f"sumcheck {name}: G = the sum of g over the cube"
        add(gm.lin_form(p, name, gm.G_coef(p, name), X.one()), rhs=G)
        if first is not None:
            cur[0] = f"sumcheck {name}: claim + rho G = first round sum"
            add(first, rhs=X.sub(X.add(msgs[0][0], msgs[0][1], p), X.mul(rho, G, p), p))
        cur[0] = f"sumcheck {name}: final + rho g(r) = last round at r"
        add(final, gm.lin_form(p, name, gm.at_coef(p, name, pts), rho), rhs=X.interp_at(msgs[-1], pts[-1], p))
    # zerocheck A * B - C = 0
    xf, yf, zf, aux = ZK.prod_forms(p, prod, 0)
    eq = X.mle(X.eqv(tau, p), zrs, p)
    if mask:
        G_and_final("zc", None, fsum(ev_(p, zf, eq), Y(2, neg(eq))), zrs)
    else:
        cur[0] = "Hadamard zerocheck: round sums"
        add(RC(zrows[0], 0), RC(zrows[0], 1))
        for i in range(1, len(zrows)):
            lc = X.lagc(3, zrs[i - 1], p)
            add(RC(zrows[i], 0), RC(zrows[i], 1), *[RC(zrows[i - 1], j, neg(lc[j])) for j in range(4)])
        lc = X.lagc(3, zrs[-1], p)
        cur[0] = "Hadamard zerocheck: final = eq (A B - C)"
        add(*[RC(zrows[-1], j, lc[j]) for j in range(4)], ev_(p, zf, neg(eq)), Y(2, eq))
    cur[0] = "product operands"
    add(ev_(p, xf, X.one()), Y(0, m1))
    add(ev_(p, yf, X.one()), Y(1, m1))
    for f_ in aux:
        lin.append((f_, 0)); labels.append("product operand sums")
    # the linear batch
    cur[0] = "linear batch: openings/IO/copy constraints"
    add(*[RC(crow, i) for i in range(len(ks))], rhs=neg(const))
    for i, k in enumerate(ks):
        m = (lens[k] - 1).bit_length()
        coef = X.mle(q[k] + [X.zero()] * ((1 << len(rr)) - len(q[k])), rr, p)
        for rj in rr[m:]:
            coef = X.mul(coef, X.one_minus(rj, p), p)
        if mask:
            G_and_final(f"l:{k}", RC(crow, i), Y(3 + i, coef), rr)
            continue
        cur[0] = f"linear sumcheck {k}"
        add(RC(lrows[0], 3 * i), RC(lrows[0], 3 * i + 1), RC(crow, i, m1))
        for r in range(1, len(lrows)):
            lc = X.lagc(2, rr[r - 1], p)
            add(RC(lrows[r], 3 * i), RC(lrows[r], 3 * i + 1), *[RC(lrows[r - 1], 3 * i + j, neg(lc[j])) for j in range(3)])
        lc = X.lagc(2, rr[-1], p)
        cur[0] = f"linear sumcheck {k}: final"
        add(*[RC(lrows[-1], 3 * i + j, lc[j]) for j in range(3)], Y(3 + i, neg(coef)))
    if len(ev) == 3 + len(ks) + 2:
        cur[0] = "signed input binding: the custodians' y = the owner's signed y"
        add(Y(len(ev) - 2), Y(len(ev) - 1, m1))
    return lin, [prod], labels

def prove_middle_zk(live, sym, wires, spine_coms, attack=None, context=("model", 0, 0), seed=2, owner_y=None, io=None,
                    ignore_range=False):
    p, n = live.p, live.n
    zero = {i: (0, 0) for i in range(n)}
    cons_l, had_l, prep_l, ext_l = G.middle(live)
    cons, had, prep, ext = G.middle(sym)
    if (len(cons_l), prep_l, ext_l) != (len(cons), prep, ext) or had_l != had:
        return None, dict(error="prover and verifier constraint systems differ")
    eng = spdz.Engine(p, n, live.dealer)
    bad = G.fill_range(live, eng)
    G.fill_lookup(live, eng)
    if bad and not ignore_range:
        return None, dict(error="proving refused: truncation input outside its proved bound: "
                          + ", ".join(f"{nm}[{k}]" for nm, k in bad[:4]) + (" ..." if len(bad) > 4 else ""))
    pos = {a: k for k, a in enumerate(prep)}
    Pv = G.pad([live.atom_sh[a] for a in prep], zero)
    if attack == "bad_triple":
        k = pos[had[0][2]]
        Pv[k] = dict(Pv[k]); Pv[k][0] = ((Pv[k][0][0] + 1) % p, Pv[k][0][1])
    if attack == "nonboolean_bit":
        k = pos[[t for t in had if t[0] == t[1] == t[2]][0][0]]
        Pv[k] = dict(Pv[k]); Pv[k][0] = ((Pv[k][0][0] + 2) % p, Pv[k][0][1])
    Av = G.pad([Pv[pos[a]] for a, _, _ in had], zero)
    Bv = G.pad([Pv[pos[b]] for _, b, _ in had], zero)
    Cv = G.pad([Pv[pos[c]] for _, _, c in had], zero)
    names, carried = (NAMES, SPINE) if io is None else (io.names, io.carried)
    vecs = dict(P=Pv, A=Av, B=Bv, C=Cv, **{nm: G.pad(wires[nm], zero) for nm in names})
    d = len(wires["x"]) if io is None else None
    lens, _ = public_shapes(p, prep, had, d, io=io)
    assert all(len(vecs[k]) == lens[k] for k in lens)
    sh_ = lambda V: [[x[i][0] for x in V] for i in range(n)]
    com = {}
    for k, V in vecs.items():
        if k in carried:
            com[k] = spine_coms[k]                             # the spine's commitment, carried: same root
            com[k].base = com[k].block                         # its second life (second proximity mask)
        else:
            com[k] = ZK.ZKPCS(p, sh_(V), k)
    if owner_y is not None:
        com["yo"] = owner_y
    L = Z.Prover(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n, (seed, context))
    tr = Transcript("middle-zk" if io is None else io.label)
    tr.absorb("ctx", context)
    tr.absorb("public", ZK.public_digest([v for _, _, v in live.transcript]))
    for k in sorted(com):
        tr.absorb(k, com[k].roots)
    st = {}
    def zround(rnd, tau, zrs):
        """One Beaver product per live pair per round (gen 6): the product f g is quadratic in X, so with its values
        at X = 0, 1 known it needs only X = 2 (X = 3 by interpolation). Round 0's X = 0, 1 products are the C atoms
        themselves (A B = C for the honest witness; a dishonest one fails the final check, whatever the prover
        computed); a later round's are the previous round's pair products at r, by interpolation. Pairs past the
        live length (zero padding) are zero. Tables hold shared elements (cosnark_ext): from round 1 on, the folds
        by F_{p^EXT} challenges make each product cost EXT = 2: three Beaver triples."""
        B = lambda v: (v,)
        if rnd == 0:
            st.update(f=[B(v) for v in Av], g=[B(v) for v in Bv], sub=[B(v) for v in Cv], eq=X.eqv(tau, p),
                      live=len(had), prev=[B(v) for v in Cv])
        else:
            r = zrs[-1]
            om = X.one_minus(r, p)
            fold = lambda T: [X.slin(eng, [(om, T[2 * k]), (r, T[2 * k + 1])]) for k in range(len(T) // 2)]
            st["f"], st["g"], st["sub"] = fold(st["f"]), fold(st["g"]), fold(st["sub"])
            st["eq"] = [X.add(X.mul(st["eq"][2 * k], om, p), X.mul(st["eq"][2 * k + 1], r, p), p)
                        for k in range(len(st["eq"]) // 2)]
            r1, r2 = X.sub(r, X.one(), p), X.sub(r, X.lift(2), p)
            l0 = X.scal(inv2, X.mul(r1, r2, p), p)
            l1 = X.neg(X.mul(r, r2, p), p)
            l2 = X.scal(inv2, X.mul(r, r1, p), p)
            st["prev"] = [X.slin(eng, [(l0, P0), (l1, P1), (l2, P2)]) for P0, P1, P2 in st["P"]]
            st["live"] = (st["live"] + 1) // 2
        f, g, sub, eqt, prev = st["f"], st["g"], st["sub"], st["eq"], st["prev"]
        half = len(f) // 2
        na = (st["live"] + 1) // 2
        mo, two = ((-1) % p,), (2,)
        P2 = [X.smul(eng, X.slin(eng, [(mo, f[2 * k]), (two, f[2 * k + 1])]), X.slin(eng, [(mo, g[2 * k]), (two, g[2 * k + 1])]))
              for k in range(na)]
        zz = (zero,)
        P = [(prev[2 * k], prev[2 * k + 1], P2[k] if k < na else zz) for k in range(half)]
        st["P"] = P
        vals = []
        for Xv in range(4):
            c0, c1 = ((1 - Xv) % p,), (Xv,)
            acc = None
            for k in range(half):
                lo, hi = 2 * k, 2 * k + 1
                P0, P1, P2k = P[k]
                prod = (P0, P1, P2k)[Xv] if Xv < 3 else X.slin(eng, [(X.one(), P0), (((-3) % p,), P1), ((3,), P2k)])
                term = X.ssub(eng, prod, X.slin(eng, [(c0, sub[lo]), (c1, sub[hi])]))
                term = X.scmul(eng, X.add(X.mul(eqt[lo], c0, p), X.mul(eqt[hi], c1, p), p), term)
                acc = term if acc is None else X.sadd(eng, acc, term)
            vals.append(X.spad(eng, acc))
        if mask:
            return open_round("zc", rnd, zrs, vals)
        L.add_row([[c for v in vals for c in X.shares(v, i)] for i in range(n)])
        return L.commit()
    inv2 = pow(2, p - 2, p)
    mask = ZK.ZKSC == "mask"
    mz = dict(msgs={}, G={}, rho=None)
    def pre(tr_):
        """Cut D: every g of the middle committed as one group, the G values opened, rho drawn."""
        gm = ZK.GMask(specs(lens), 0)
        mz["gsh"], mz["g_roots"] = gm.commit(L)
        mz["gm"] = gm
        for name, _, _ in gm.specs:
            mz["G"][name] = ZK.open_sum(p, [gm.share_val(p, mz["gsh"][i], name, gm.G_coef(p, name)) for i in range(n)])
        tr_.absorb("zkg", mz["g_roots"])
        tr_.absorb("G", X.flat([mz["G"][nm] for nm, _, _ in gm.specs]))
        mz["rho"] = X.chal1(tr_, p)
    def open_round(name, rnd, pts, vals):
        """Cut D: the opened round message s_rnd = f-part + rho g-part (every custodian broadcasts its share)."""
        gm, rho = mz["gm"], mz["rho"]
        plain = []
        for t in range(len(vals)):
            cf = gm.round_coef(p, name, rnd, t, pts)
            plain.append(ZK.open_sum(p, [X.add(X.shares(vals[t], i), X.mul(rho, gm.share_val(p, mz["gsh"][i], name, cf), p), p)
                                         for i in range(n)]))
        mz["msgs"].setdefault(name, []).append(plain)
        return plain
    tau, zrs, ks = schedule(tr, p, lens, lambda rnd, tau, zrs: X.flat(zround(rnd, tau, zrs)) if mask else zround(rnd, tau, zrs),
                            None, None, pre=pre if mask else None)
    gam = X.chal(tr, p, len(cons) + 3 * len(had))
    q, const = build_q(p, sym, cons, had, prep, lens, gam)
    nz = lambda c: any(c)
    claims = [X.spad(eng, X.slin(eng, [(q[k][i], (vecs[k][i],)) for i in range(lens[k]) if nz(q[k][i])]))
              for k in ks]
    L.add_row([[c for cl in claims for c in X.shares(cl, i)] for i in range(n)])
    croot = L.commit()
    Lmax = max((lens[k] - 1).bit_length() for k in ks)
    tabs = {k: (list(q[k]) + [X.zero()] * ((1 << Lmax) - lens[k]),
                [(v,) for v in vecs[k]] + [(zero,)] * ((1 << Lmax) - lens[k])) for k in ks}
    def lround(rnd, rr):
        if rnd:
            r = rr[-1]
            om = X.one_minus(r, p)
            for k in ks:
                qq, XX = tabs[k]
                tabs[k] = ([X.add(X.mul(qq[2 * j], om, p), X.mul(qq[2 * j + 1], r, p), p) for j in range(len(qq) // 2)],
                           [X.slin(eng, [(om, XX[2 * j]), (r, XX[2 * j + 1])]) for j in range(len(XX) // 2)])
        shares = [[] for _ in range(n)]
        opened = []
        for k in ks:
            qq, XX = tabs[k]
            vs = []
            for t in range(3):
                c0, c1 = ((1 - t) % p,), (t,)
                terms = []
                for j in range(len(XX) // 2):
                    qa = X.add(X.mul(qq[2 * j], c0, p), X.mul(qq[2 * j + 1], c1, p), p)
                    terms += [(X.mul(qa, c0, p), XX[2 * j]), (X.mul(qa, c1, p), XX[2 * j + 1])]
                v = X.spad(eng, X.slin(eng, [(c, x) for c, x in terms if nz(c)]))
                vs.append(v)
                for i in range(n):
                    shares[i] += list(X.shares(v, i))
            if mask:
                opened += X.flat(open_round(f"l:{k}", rnd, rr, vs))
        if mask:
            return opened
        L.add_row(shares)
        return L.commit()
    rr = run_linear_schedule(tr, p, lens, ks, croot, lround)
    rb = X.chal(tr, p, (plen(d) - 1).bit_length()) if owner_y is not None else None
    ev = evaluations(lens, ks, zrs, rr, rb)
    layout = row_layout(com, ev, len(zrs), Lmax, lens)
    ys = []
    for e, (k, pt) in enumerate(ev):
        c = com[k]
        a = c.eval_weights_e(pt)
        u = [c.row_combo_e(i, a) for i in range(n)]
        b = X.eqv(pt[:c.mc], p)
        ys.append([X.dot([tuple(u[i][kk][cc] for kk in range(X.EXT)) for cc in range(c.C)], b, p) for i in range(n)])
        for kk in range(X.EXT):
            for s0 in range(0, c.W, ZK.K_L):
                L.add_row([u[i][kk][s0:s0 + ZK.K_L] for i in range(n)])
    for row in ZK.prod_shares(L, [ys[0]], [ys[1]]):
        L.add_row(row)
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    _, prox, pcols = CS.pcs_prove(com, [], tr, n, p)
    cols = {k: (pcols[k][0], [[sum(pcols[k][1][i][jj][0][r] for i in range(n)) % p for r in range(com[k].R)]
                              for jj in range(len(pcols[k][0]))]) for k in com}
    lin, quad, labels = constraints(p, com, lens, ks, ev, cols, layout, tau, zrs, rr, q, const, mz=mz)
    lig = L.prove(tr, lin, quad)
    eng.mac_check("middle-zk")
    proof = dict(roots={k: com[k].roots for k in sorted(com)}, claims_root=croot,
                 eval_roots=eval_roots, mask_roots=mask_roots, prox={k: prox[k][1] for k in sorted(prox)},
                 pcs_cols={k: pcols[k] for k in sorted(pcols)}, ligero=lig)
    if mask:
        proof.update(g_roots=mz["g_roots"], G=X.flat([mz["G"][nm] for nm, _, _ in specs(lens)]),
                     zc=[X.flat(m) for m in mz["msgs"]["zc"]],
                     lsc=[[c for k in ks for c in X.flat(mz["msgs"][f"l:{k}"][r])] for r in range(Lmax)])
    else:
        ngz = len(zrs)
        proof["zc_roots"] = [[t[-1][0] for t in g["trees"]] for g in L.groups[:ngz]]
        proof["lsc_roots"] = [[t[-1][0] for t in g["trees"]] for g in L.groups[ngz + 1:ngz + 1 + Lmax]]
    stats = dict(hidden_rows=layout[-1], lin_constraints=len(lin), ligero_wire=L.wire,
                 spdz_wire=dict(eng.wire), spdz_openings=eng.nopen, atoms=len(prep), hadamard=len(had),
                 first_violated=ZK.first_violated(p, L.rows, lin, quad, labels))
    return proof, stats

def verify_middle_zk(p, n, sym, d, spine_roots, context, proof, bind=False, io=None):
    cons, had, prep, ext = G.middle(sym)
    lens, sh = public_shapes(p, prep, had, d, bind, io=io)
    roots = proof["roots"]
    if sorted(roots) != sorted(sh):
        return False, "proof names the wrong commitments"
    for nm in (SPINE if io is None else io.carried):
        if io is not None and roots[nm] != spine_roots[nm]:
            return False, f"the {nm} commitment is not the ledger head's"
        if nm in spine_roots and roots[nm] != spine_roots[nm]:
            return False, f"middle's {nm} is not the spine's committed {nm}"
    tr = Transcript("middle-zk" if io is None else io.label)
    tr.absorb("ctx", context)
    tr.absorb("public", ZK.public_digest([v for _, _, v in sym.transcript]))
    for k in sorted(roots):
        tr.absorb(k, roots[k])
    lh = (lens["A"] - 1).bit_length()
    Lmax = max((L - 1).bit_length() for L in lens.values())
    ks = sorted(lens)
    E = X.EXT
    mask = ZK.ZKSC == "mask"
    mz = None
    if mask:
        sp = specs(lens)
        if len(proof.get("zc", ())) != lh or any(len(v) != 4 * E for v in proof["zc"]):
            return False, "wrong number of zerocheck rounds"
        if len(proof.get("lsc", ())) != Lmax or any(len(v) != 3 * E * len(ks) for v in proof["lsc"]):
            return False, "wrong number of linear sumcheck rounds"
        if len(proof.get("G", ())) != E * len(sp) or len(proof.get("g_roots", ())) != n:
            return False, "masking polynomials of the wrong shape"
        msgs = {"zc": [ZK.unflat(v, 3) for v in proof["zc"]]}
        for i, k in enumerate(ks):
            msgs[f"l:{k}"] = [ZK.unflat(v[3 * E * i:3 * E * (i + 1)], 2) for v in proof["lsc"]]
        mz = dict(G={nm: tuple(proof["G"][E * i:E * (i + 1)]) for i, (nm, _, _) in enumerate(sp)}, msgs=msgs, rho=None)
        def pre(tr_):
            tr_.absorb("zkg", proof["g_roots"])
            tr_.absorb("G", list(proof["G"]))
            mz["rho"] = X.chal1(tr_, p)
        tau, zrs, _ = schedule(tr, p, lens, lambda rnd, tau, zrs: proof["zc"][rnd], None, None, pre=pre)
    else:
        if len(proof["zc_roots"]) != lh:
            return False, "wrong number of zerocheck rounds"
        tau, zrs, _ = schedule(tr, p, lens, lambda rnd, tau, zrs: proof["zc_roots"][rnd], None, None)
        if len(proof["lsc_roots"]) != Lmax:
            return False, "wrong number of linear sumcheck rounds"
    gam = X.chal(tr, p, len(cons) + 3 * len(had))
    q, const = build_q(p, sym, cons, had, prep, lens, gam)
    rr = run_linear_schedule(tr, p, lens, ks, proof["claims_root"],
                             (lambda rnd, rr_: proof["lsc"][rnd]) if mask else (lambda rnd, rr_: proof["lsc_roots"][rnd]))
    if mask:
        why = ZK.check_rounds(p, "zc", mz["msgs"]["zc"], zrs, 3, X.mul(mz["rho"], mz["G"]["zc"], p))
        for k in ks:
            why = why or ZK.check_rounds(p, f"l:{k}", mz["msgs"][f"l:{k}"], rr, 2)
        if why:
            return False, why
    rb = X.chal(tr, p, (plen(d) - 1).bit_length()) if bind else None
    ev = evaluations(lens, ks, zrs, rr, rb)
    layout = row_layout(sh, ev, lh, Lmax, lens)
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    ok, why = CS.pcs_verify(sh, roots, [], [], {k: (None, proof["prox"][k]) for k in sh}, proof["pcs_cols"], tr, n, p)
    if not ok:
        return ok, why
    pc = proof["pcs_cols"]
    cols = {k: (pc[k][0], [[sum(pc[k][1][i][jj][0][r] for i in range(n)) % p for r in range(sh[k].R)]
                           for jj in range(len(pc[k][0]))]) for k in sh}
    lin, quad, _ = constraints(p, sh, lens, ks, ev, cols, layout, tau, zrs, rr, q, const, mz=mz)
    if mask:
        ng = layout[0].nrows
        groups = [proof["g_roots"], proof["claims_root"], proof["eval_roots"]]
        sizes = [ng, 1, layout[-1] - ng - 1]
    else:
        groups = list(proof["zc_roots"]) + [proof["claims_root"]] + list(proof["lsc_roots"]) + [proof["eval_roots"]]
        sizes = [1] * lh + [1] + [1] * Lmax + [layout[-1] - lh - 1 - Lmax]
    return Z.verify(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n, groups, sizes, proof["mask_roots"], lin, quad,
                    proof["ligero"], tr)

def counts_formula(d, n=3, k=None, t=None, T=None, **gate_shifts):
    """The middle ZK proof's counts as a function of d (atoms and Hadamard counts from cosnark_gates.counts_formula,
    which run_cosnark_gates.py validates against execution)."""
    k, t, T = k or ZK.K_L, t or ZK.T_HIDE, T or ZK.T_OPEN
    g = G.counts_formula(d, **gate_shifts)
    lens = dict(P=plen(g["atoms"]), A=plen(g["hadamard"]), B=plen(g["hadamard"]), C=plen(g["hadamard"]))
    lens.update({nm: plen(d) for nm in NAMES})
    m = {kk: (L - 1).bit_length() for kk, L in lens.items()}
    C_ = {kk: 1 << (mm - CS.row_split(mm)) for kk, mm in m.items()}
    R_ = {kk: 1 << CS.row_split(mm) for kk, mm in m.items()}
    W = {kk: C_[kk] + CS.HIDE for kk in lens}
    lh, Lmax = m["A"], max(m.values())
    ev = ["A", "B", "C"] + sorted(lens)
    urows = sum(-(-W[kk] // k) for kk in ev)
    rows = lh + 1 + Lmax + urows + 3
    groups = lh + 1 + Lmax + 1
    lin = len(ev) * CS.T_COLS + (lh + 3) + 1 + len(lens) * (Lmax + 1)
    npts = 4 * (k + t)
    lgL = (npts - 1).bit_length() + 1                              # + the leaf salt
    lgp = lambda kk: (CS.BLOW * W[kk] - 1).bit_length() + 1
    pcs_fe = sum(n * W[kk] + n * CS.T_COLS * (R_[kk] + CS.NMASK) + CS.T_COLS for kk in lens)
    pcs_h = sum(n * CS.T_COLS * lgp(kk) + n for kk in lens)
    lig_fe = (k + t) + (2 * k + t - 1) + (2 * (k + t) - 1) + n * T * (rows + 3)
    lig_h = n * T * lgL * (groups + 1) + n * (groups + 1)
    muls = 4 * (lens["A"] - 1)
    fe, hs = pcs_fe + lig_fe, pcs_h + lig_h
    return dict(hidden_rows=rows, lin_constraints=lin,
                ligero_wire=n * (n - 1) * (3 * (k + t) + (2 * k + t - 1) + (2 * (k + t) - 1) + 2),
                spdz_wire={"mul": muls * 2 * n * (n - 1), "mac_check": 2 * n * (n - 1)}, spdz_openings=2 * muls,
                atoms=g["atoms"], hadamard=g["hadamard"],
                proof=dict(field_elems=fe, hashes=hs, bits=61 * fe + 256 * hs))
