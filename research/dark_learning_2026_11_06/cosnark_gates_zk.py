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
import spdz
from cosnark import Transcript, eqv, mle

NAMES = ("z1", "z2", "b", "y", "h", "g1", "d2", "bg", "d1")
SPINE = ("z1", "z2", "b", "h", "g1", "d2", "bg", "d1")

def build_q(p, sym, cons, had, prep, lens, gam):
    pos = {a: k for k, a in enumerate(prep)}
    q = {k: [0] * L for k, L in lens.items()}
    const = 0
    for g, (form, c0, val, _) in zip(gam, cons):
        for a, co in form.items():
            kind, tag = sym.atoms[a]
            if kind == "ext":
                nm, k = tag
                q[nm][k] = (q[nm][k] + g * co) % p
            else:
                q["P"][pos[a]] = (q["P"][pos[a]] + g * co) % p
        const = (const + g * (c0 - val)) % p
    g3 = gam[len(cons):]
    for k, (a, b, c) in enumerate(had):
        for j, (vn, at) in enumerate((("A", a), ("B", b), ("C", c))):
            g = g3[3 * k + j]
            q[vn][k] = (q[vn][k] + g) % p
            q["P"][pos[at]] = (q["P"][pos[at]] - g) % p
    return q, const

def plen(x):
    n = 1
    while n < max(1, x):
        n *= 2
    return n

def public_shapes(p, prep, had, d, bind=False):
    """lens: the vectors in the linear batch. sh: every commitment's shape, including the owner's "yo"
    (committed and evaluated, but not in the batch)."""
    lens = dict(P=plen(len(prep)), A=plen(len(had)), B=plen(len(had)), C=plen(len(had)))
    lens.update({nm: plen(d) for nm in NAMES})
    sh = {k: ZK.PubShape(p, (L - 1).bit_length(), CS.HIDE, CS.NMASK,
                         CS.NMASK // CS.LIVES if k in SPINE else 0) for k, L in lens.items()}
    if bind:
        sh["yo"] = ZK.PubShape(p, (plen(d) - 1).bit_length(), CS.HIDE, CS.NMASK, 0)
    return lens, sh

def schedule(tr, p, lens, round_cb, claims_cb, lin_cb):
    """Public schedule. Returns (zerocheck tau, zrs), (gam drawn by caller), batched rr, and the evaluation list."""
    lh = (lens["A"] - 1).bit_length()
    tau = tr.chal(p, lh)
    zrs = []
    for rnd in range(lh):
        tr.absorb("zc", round_cb(rnd, tau, zrs))
        zrs.append(tr.chal(p)[0])
    ks = sorted(lens)
    gam = tr.chal(p, -1) if False else None
    return tau, zrs, ks

def run_linear_schedule(tr, p, lens, ks, claims_root, lin_cb):
    tr.absorb("claims", claims_root)
    Lmax = max((lens[k] - 1).bit_length() for k in ks)
    rr = []
    for rnd in range(Lmax):
        tr.absorb("lsc", lin_cb(rnd, rr))
        rr.append(tr.chal(p)[0])
    return rr

def evaluations(lens, ks, zrs, rr, rb=None):
    ev = [("A", zrs), ("B", zrs), ("C", zrs)]
    for k in ks:
        m = (lens[k] - 1).bit_length()
        ev.append((k, rr[:m]))
    if rb is not None:
        ev += [("yo", rb), ("y", rb)]          # signed-input binding for y
    return ev

def row_layout(sh, ev, lh, Lmax):
    nxt = 0
    zrows = list(range(nxt, nxt + lh)); nxt += lh
    crow = nxt; nxt += 1
    lrows = list(range(nxt, nxt + Lmax)); nxt += Lmax
    urows = []
    for k, _ in ev:
        nr = -(-sh[k].W // ZK.K_L)
        urows.append(list(range(nxt, nxt + nr))); nxt += nr
    return zrows, crow, lrows, urows, (nxt, nxt + 1, nxt + 2), nxt + 3

def constraints(p, sh, lens, ks, ev, cols, layout, tau, zrs, rr, q, const):
    zrows, crow, lrows, urows, (X, Yr, Zr), _ = layout
    lin, labels, cur = [], [], ["?"]
    K = ZK.K_L
    def ucell(e, c):
        return (urows[e][c // K], c % K)
    def Y(e, coef=1):
        k, pt = ev[e]
        b = eqv(pt[:sh[k].mc], p)
        return {ucell(e, c): coef * b[c] % p for c in range(sh[k].C)}
    def add(*forms, rhs=0):
        t = {}
        for f in forms:
            for key, v in f.items():
                t[key] = (t.get(key, 0) + v) % p
        lin.append(({kk: v for kk, v in t.items() if v}, rhs % p))
        labels.append(cur[0])
    cell = lambda r, pos, c=1: {(r, pos): c % p}
    for e, (k, pt) in enumerate(ev):
        cur[0] = f"PCS evaluation consistency ({k})"
        s = sh[k]
        a = s.eval_weights(pt, e)
        J, csum = cols[k]
        for jj, j in enumerate(J):
            x, xs, f = s.pts[j], 1, {}
            for c in range(s.W):
                f[ucell(e, c)] = xs
                xs = xs * x % p
            add(f, rhs=sum(ai * v for ai, v in zip(a, csum[jj])))
    # zerocheck A * B - C = 0
    cur[0] = "Hadamard zerocheck: round sums"
    add(cell(zrows[0], 0), cell(zrows[0], 1))
    for i in range(1, len(zrows)):
        lc = ZK.lagc(3, zrs[i - 1], p)
        add(cell(zrows[i], 0), cell(zrows[i], 1), *[cell(zrows[i - 1], j, -lc[j]) for j in range(4)])
    lc = ZK.lagc(3, zrs[-1], p)
    eq = mle(eqv(tau, p), zrs, p)
    cur[0] = "Hadamard zerocheck: final = eq (A B - C)"
    add(*[cell(zrows[-1], j, lc[j]) for j in range(4)], cell(Zr, 0, -eq), Y(2, eq))
    cur[0] = "product operands"
    add(cell(X, 0), Y(0, -1))
    add(cell(Yr, 0), Y(1, -1))
    # the linear batch
    cur[0] = "linear batch: openings/IO/copy constraints"
    add(*[cell(crow, i) for i in range(len(ks))], rhs=-const)
    for i, k in enumerate(ks):
        cur[0] = f"linear sumcheck {k}"
        add(cell(lrows[0], 3 * i), cell(lrows[0], 3 * i + 1), cell(crow, i, -1))
        for r in range(1, len(lrows)):
            lc = ZK.lagc(2, rr[r - 1], p)
            add(cell(lrows[r], 3 * i), cell(lrows[r], 3 * i + 1), *[cell(lrows[r - 1], 3 * i + j, -lc[j]) for j in range(3)])
        lc = ZK.lagc(2, rr[-1], p)
        m = (lens[k] - 1).bit_length()
        coef = mle(q[k] + [0] * ((1 << len(rr)) - len(q[k])), rr, p)
        for rj in rr[m:]:
            coef = coef * (1 - rj) % p
        cur[0] = f"linear sumcheck {k}: final"
        add(*[cell(lrows[-1], 3 * i + j, lc[j]) for j in range(3)], Y(3 + i, -coef))
    if len(ev) == 3 + len(ks) + 2:
        cur[0] = "signed input binding: the custodians' y = the owner's signed y"
        add(Y(len(ev) - 2), Y(len(ev) - 1, -1))
    return lin, [(X, Yr, Zr)], labels

def prove_middle_zk(live, sym, wires, spine_coms, attack=None, context=("model", 0, 0), seed=2, owner_y=None):
    p, n = live.p, live.n
    zero = {i: (0, 0) for i in range(n)}
    cons_l, had_l, prep_l, ext_l = G.middle(live)
    cons, had, prep, ext = G.middle(sym)
    if (len(cons_l), prep_l, ext_l) != (len(cons), prep, ext) or had_l != had:
        return None, dict(error="prover and verifier constraint systems differ")
    eng = spdz.Engine(p, n, live.dealer)
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
    vecs = dict(P=Pv, A=Av, B=Bv, C=Cv, **{nm: G.pad(wires[nm], zero) for nm in NAMES})
    d = len(wires["x"])
    lens, _ = public_shapes(p, prep, had, d)
    assert all(len(vecs[k]) == lens[k] for k in lens)
    sh_ = lambda V: [[x[i][0] for x in V] for i in range(n)]
    com = {}
    for k, V in vecs.items():
        if k in SPINE:
            com[k] = spine_coms[k]                             # the spine's commitment, carried: same root
            com[k].base = com[k].block                         # its second life (second proximity mask)
        else:
            com[k] = ZK.ZKPCS(p, sh_(V), k)
    if owner_y is not None:
        com["yo"] = owner_y
    L = Z.Prover(Z.Params(p, ZK.K_L, ZK.T_HIDE, ZK.T_OPEN), n, (seed, context))
    tr = Transcript("middle-zk")
    tr.absorb("ctx", context)
    tr.absorb("public", ZK.public_digest([v for _, _, v in live.transcript]))
    for k in sorted(com):
        tr.absorb(k, com[k].roots)
    st = {}
    def zround(rnd, tau, zrs):
        if rnd == 0:
            st.update(f=list(Av), g=list(Bv), sub=list(Cv), eq=eqv(tau, p))
        else:
            r = zrs[-1]
            fold = lambda T: [eng.lin([(1 - r, T[2 * k]), (r, T[2 * k + 1])]) for k in range(len(T) // 2)]
            st["f"], st["g"], st["sub"] = fold(st["f"]), fold(st["g"]), fold(st["sub"])
            st["eq"] = [(st["eq"][2 * k] * (1 - r) + st["eq"][2 * k + 1] * r) % p for k in range(len(st["eq"]) // 2)]
        f, g, sub, eqt = st["f"], st["g"], st["sub"], st["eq"]
        vals = []
        for Xv in range(4):
            acc = None
            for k in range(len(f) // 2):
                lo, hi = 2 * k, 2 * k + 1
                term = eng.mul(eng.lin([(1 - Xv, f[lo]), (Xv, f[hi])]), eng.lin([(1 - Xv, g[lo]), (Xv, g[hi])]))
                term = eng.sub(term, eng.lin([(1 - Xv, sub[lo]), (Xv, sub[hi])]))
                term = eng.cmul((eqt[lo] * (1 - Xv) + eqt[hi] * Xv) % p, term)
                acc = term if acc is None else eng.add(acc, term)
            vals.append(acc)
        L.add_row([[v[i][0] for v in vals] for i in range(n)])
        return L.commit()
    tau, zrs, ks = schedule(tr, p, lens, zround, None, None)
    gam = tr.chal(p, len(cons) + 3 * len(had))
    q, const = build_q(p, sym, cons, had, prep, lens, gam)
    claims = [eng.lin([(q[k][i], vecs[k][i]) for i in range(lens[k]) if q[k][i]]) if any(q[k]) else zero for k in ks]
    L.add_row([[c[i][0] for c in claims] for i in range(n)])
    croot = L.commit()
    Lmax = max((lens[k] - 1).bit_length() for k in ks)
    tabs = {k: (list(q[k]) + [0] * ((1 << Lmax) - lens[k]), list(vecs[k]) + [zero] * ((1 << Lmax) - lens[k])) for k in ks}
    def lround(rnd, rr):
        if rnd:
            r = rr[-1]
            for k in ks:
                qq, XX = tabs[k]
                tabs[k] = ([(qq[2 * j] * (1 - r) + qq[2 * j + 1] * r) % p for j in range(len(qq) // 2)],
                           [eng.lin([(1 - r, XX[2 * j]), (r, XX[2 * j + 1])]) for j in range(len(XX) // 2)])
        shares = [[] for _ in range(n)]
        for k in ks:
            qq, XX = tabs[k]
            for t in range(3):
                terms = []
                for j in range(len(XX) // 2):
                    qa = (qq[2 * j] * (1 - t) + qq[2 * j + 1] * t) % p
                    terms += [(qa * (1 - t) % p, XX[2 * j]), (qa * t % p, XX[2 * j + 1])]
                v = eng.lin(terms) if any(c for c, _ in terms) else zero
                for i in range(n):
                    shares[i].append(v[i][0])
        L.add_row(shares)
        return L.commit()
    rr = run_linear_schedule(tr, p, lens, ks, croot, lround)
    rb = tr.chal(p, (plen(d) - 1).bit_length()) if owner_y is not None else None
    ev = evaluations(lens, ks, zrs, rr, rb)
    layout = row_layout(com, ev, len(zrs), Lmax)
    ys = []
    for e, (k, pt) in enumerate(ev):
        c = com[k]
        a = c.eval_weights(pt, e)
        u = [c.row_combo(i, a) for i in range(n)]
        b = eqv(pt[:c.mc], p)
        ys.append([sum(x * y for x, y in zip(u[i][:c.C], b)) % p for i in range(n)])
        for s0 in range(0, c.W, ZK.K_L):
            L.add_row([u[i][s0:s0 + ZK.K_L] for i in range(n)])
    zsh = L.mul_plain(ys[0], ys[1])
    for vec in (ys[0], ys[1], zsh):
        L.add_row([[vec[i]] for i in range(n)])
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    _, prox, pcols = CS.pcs_prove(com, [], tr, n, p)
    cols = {k: (pcols[k][0], [[sum(pcols[k][1][i][jj][0][r] for i in range(n)) % p for r in range(com[k].R)]
                              for jj in range(len(pcols[k][0]))]) for k in com}
    lin, quad, labels = constraints(p, com, lens, ks, ev, cols, layout, tau, zrs, rr, q, const)
    lig = L.prove(tr, lin, quad)
    eng.mac_check("middle-zk")
    proof = dict(roots={k: com[k].roots for k in sorted(com)}, zc_roots=None, claims_root=croot,
                 eval_roots=eval_roots, mask_roots=mask_roots, prox={k: prox[k][1] for k in sorted(prox)},
                 pcs_cols={k: pcols[k] for k in sorted(pcols)}, ligero=lig)
    ngz = len(zrs)
    proof["zc_roots"] = [[t[-1][0] for t in g["trees"]] for g in L.groups[:ngz]]
    proof["lsc_roots"] = [[t[-1][0] for t in g["trees"]] for g in L.groups[ngz + 1:ngz + 1 + Lmax]]
    stats = dict(hidden_rows=layout[-1], lin_constraints=len(lin), ligero_wire=L.wire,
                 spdz_wire=dict(eng.wire), spdz_openings=eng.nopen, atoms=len(prep), hadamard=len(had),
                 first_violated=ZK.first_violated(p, L.rows, lin, quad, labels))
    return proof, stats

def verify_middle_zk(p, n, sym, d, spine_roots, context, proof, bind=False):
    cons, had, prep, ext = G.middle(sym)
    lens, sh = public_shapes(p, prep, had, d, bind)
    roots = proof["roots"]
    if sorted(roots) != sorted(sh):
        return False, "proof names the wrong commitments"
    for nm in SPINE:
        if nm in spine_roots and roots[nm] != spine_roots[nm]:
            return False, f"middle's {nm} is not the spine's committed {nm}"
    tr = Transcript("middle-zk")
    tr.absorb("ctx", context)
    tr.absorb("public", ZK.public_digest([v for _, _, v in sym.transcript]))
    for k in sorted(roots):
        tr.absorb(k, roots[k])
    lh = (lens["A"] - 1).bit_length()
    if len(proof["zc_roots"]) != lh:
        return False, "wrong number of zerocheck rounds"
    tau, zrs, ks = schedule(tr, p, lens, lambda rnd, tau, zrs: proof["zc_roots"][rnd], None, None)
    gam = tr.chal(p, len(cons) + 3 * len(had))
    q, const = build_q(p, sym, cons, had, prep, lens, gam)
    Lmax = max((lens[k] - 1).bit_length() for k in ks)
    if len(proof["lsc_roots"]) != Lmax:
        return False, "wrong number of linear sumcheck rounds"
    rr = run_linear_schedule(tr, p, lens, ks, proof["claims_root"], lambda rnd, rr_: proof["lsc_roots"][rnd])
    rb = tr.chal(p, (plen(d) - 1).bit_length()) if bind else None
    ev = evaluations(lens, ks, zrs, rr, rb)
    layout = row_layout(sh, ev, lh, Lmax)
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    ok, why = CS.pcs_verify(sh, roots, [], [], {k: (None, proof["prox"][k]) for k in sh}, proof["pcs_cols"], tr, n, p)
    if not ok:
        return ok, why
    pc = proof["pcs_cols"]
    cols = {k: (pc[k][0], [[sum(pc[k][1][i][jj][0][r] for i in range(n)) % p for r in range(sh[k].R)]
                           for jj in range(len(pc[k][0]))]) for k in sh}
    lin, quad, _ = constraints(p, sh, lens, ks, ev, cols, layout, tau, zrs, rr, q, const)
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
    C_ = {kk: 1 << (mm - mm // 2) for kk, mm in m.items()}
    R_ = {kk: 1 << (mm // 2) for kk, mm in m.items()}
    W = {kk: C_[kk] + CS.HIDE for kk in lens}
    lh, Lmax = m["A"], max(m.values())
    ev = ["A", "B", "C"] + sorted(lens)
    urows = sum(-(-W[kk] // k) for kk in ev)
    rows = lh + 1 + Lmax + urows + 3
    groups = lh + 1 + Lmax + 1
    lin = len(ev) * CS.T_COLS + (lh + 3) + 1 + len(lens) * (Lmax + 1)
    npts = 4 * (k + t)
    lgL = (npts - 1).bit_length()
    lgp = lambda kk: (CS.BLOW * W[kk] - 1).bit_length()
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
