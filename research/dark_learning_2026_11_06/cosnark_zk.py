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
from cosnark import Transcript, eqv, mle

K_L, T_HIDE, T_OPEN = 64, 309, 309       # Ligero row width, hiding points (>= opened), opened columns (as the PCS: T_COLS)
NPROD = 6

class ZKPCS(CS.SharePCS):
    """Layer-1 PCS without evaluation masks: evaluation consistency is proved inside the Ligero."""
    def eval_weights(self, pt, e):
        return eqv(pt[self.mc:], self.p) + [0] * self.nmask

    def mask_corr(self, i, pt, e):
        return 0

class PubShape:
    """The public shape of a ZKPCS commitment to a vector of length 2^m (what the verifier may know)."""
    def __init__(self, p, m, hide, nmask, base):
        self.p, self.m = p, m
        self.mr, self.mc = m // 2, m - m // 2
        self.Rd, self.C = 1 << self.mr, 1 << self.mc
        self.nmask, self.hide = nmask, hide
        self.R = self.Rd + nmask
        self.block = nmask // CS.LIVES if nmask else 0
        self.base = base
        self.W = self.C + hide
        self.pts = list(range(1, CS.BLOW * self.W + 1))
    eval_weights = ZKPCS.eval_weights
    prox_row, prox_len, prox_weights = CS.SharePCS.prox_row, CS.SharePCS.prox_len, CS.SharePCS.prox_weights

VEC = ("x", "z1", "h", "z2", "d2", "b", "g1", "bg", "d1")
MAT = ("W1", "W2", "W1n", "W2n")

def shapes(p, d, chained, bind=False):
    ld = d.bit_length() - 1
    sh = {}
    for k in VEC + MAT + (("xo",) if bind else ()):
        m = ld if k in VEC or k == "xo" else 2 * ld
        sh[k] = PubShape(p, m, CS.HIDE, CS.NMASK, CS.NMASK // CS.LIVES if (chained and k in ("W1", "W2")) else 0)
    return sh

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
def schedule(tr, p, d, sh, round_roots_or_cb, bind=False):
    """Replays the public part of the transcript up to the evaluation list. round_roots_or_cb(name, rnd) returns
    the round's Ligero roots (prover: after committing; verifier: from the proof). Returns the per-sumcheck
    challenges and the evaluation list."""
    ld = d.bit_length() - 1
    evals, scs, r1 = [], {}, {}
    for name, Wk, vk, zk, tp in (("z1", "W1", "x", "z1", False), ("z2", "W2", "h", "z2", False),
                                 ("b", "W2", "d2", "b", True)):
        tau = tr.chal(p, ld)
        rs = []
        for rnd in range(ld):
            tr.absorb("scr", round_roots_or_cb(name, rnd, tau, rs))
            rs.append(tr.chal(p)[0])
        scs[name] = (tau, rs)
        evals += [(zk, tau), (vk, rs), (Wk, (rs + tau) if not tp else (tau + rs))]
    tau = tr.chal(p, ld)
    rs = []
    for rnd in range(ld):
        tr.absorb("scr", round_roots_or_cb("bg", rnd, tau, rs))
        rs.append(tr.chal(p)[0])
    scs["bg"] = (tau, rs)
    evals += [("b", rs), ("g1", rs), ("bg", rs)]
    for Wn, Wo, dv, vv in (("W1n", "W1", "d1", "x"), ("W2n", "W2", "d2", "h")):
        rc, rr = tr.chal(p, ld), tr.chal(p, ld)
        r1[Wn] = (rc, rr)
        evals += [(Wn, rc + rr), (Wo, rc + rr), (dv, rr), (vv, rc)]
    if bind:
        # signed-input binding: the owner's committed batch x and the custodians' x agree at a fresh point
        rb = tr.chal(p, ld)
        evals += [("xo", rb), ("x", rb)]
    return scs, evals

def row_layout(d, sh, evals):
    """Hidden-row numbering, in commit order: rounds (z1, z2, b, bg; ld each), then each evaluation's u rows,
    then the product rows x, y, z."""
    ld = d.bit_length() - 1
    rows, nxt = {}, 0
    for name in ("z1", "z2", "b", "bg"):
        rows[name] = list(range(nxt, nxt + ld)); nxt += ld
    urows = []
    for k, _ in evals:
        nr = -(-sh[k].W // K_L)
        urows.append(list(range(nxt, nxt + nr))); nxt += nr
    prod = (nxt, nxt + 1, nxt + 2)
    return rows, urows, prod, nxt + 3

def constraints(p, d, sh, scs, evals, cols, rows, urows, prod):
    """The verifier's checks as Ligero constraints on hidden values. cols[k] = (J, column sums at J)."""
    lin, labels = [], []
    cur = ["?"]
    def ucell(e, c):
        return (urows[e][c // K_L], c % K_L)
    def Y(e, coef=1):
        k, pt = evals[e]
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
    # PCS evaluation consistency at the opened columns
    for e, (k, pt) in enumerate(evals):
        cur[0] = f"PCS evaluation consistency ({k})"
        s = sh[k]
        a = s.eval_weights(pt, e)
        J, csum = cols[k]
        for jj, j in enumerate(J):
            x = s.pts[j]
            xs, f = 1, {}
            for c in range(s.W):
                f[ucell(e, c)] = xs
                xs = xs * x % p
            add(f, rhs=sum(ai * v for ai, v in zip(a, csum[jj])))
    X, Yr, Zr = prod
    def sumcheck(name, deg, first, final_lin, q):
        """first: form for the initial claim (rows[0][0] + rows[0][1] = first); final_lin: the last claim's link."""
        tau, rs = scs[name]
        R = rows[name]
        cur[0] = f"sumcheck {name}: first round sum = claim"
        add(cell(R[0], 0), cell(R[0], 1), {kk: (-v) % p for kk, v in first.items()})
        cur[0] = f"sumcheck {name}: round sums"
        for i in range(1, len(R)):
            lc = lagc(deg, rs[i - 1], p)
            add(cell(R[i], 0), cell(R[i], 1), *[cell(R[i - 1], j, -lc[j]) for j in range(deg + 1)])
        lc = lagc(deg, rs[-1], p)
        cur[0] = f"sumcheck {name}: final claim = product gate"
        add(*[cell(R[-1], j, lc[j]) for j in range(deg + 1)], final_lin)
    for q, (name, idx) in enumerate((("z1", 0), ("z2", 3), ("b", 6))):
        sumcheck(name, 2, Y(idx), cell(Zr, q, -1), q)
        cur[0] = f"product {q} operands"
        add(cell(X, q), Y(idx + 2, -1))        # x = W(..)
        add(cell(Yr, q), Y(idx + 1, -1))       # y = v(rs)
    tau, rs = scs["bg"]
    eq = mle(eqv(tau, p), rs, p)
    sumcheck("bg", 3, {}, {**cell(Zr, 3, -eq), **Y(11, eq)}, 3)
    cur[0] = "product 3 operands"
    add(cell(X, 3), Y(9, -1))
    add(cell(Yr, 3), Y(10, -1))
    for q, base in ((4, 12), (5, 16)):          # W'(r) - W(r) + d(r_row) v(r_col) = 0
        cur[0] = f"rank-1 update {'W1n' if q == 4 else 'W2n'}: W'(r) = W(r) - d(r_row) v(r_col)"
        add(Y(base), Y(base + 1, -1), cell(Zr, q))
        cur[0] = f"product {q} operands"
        add(cell(X, q), Y(base + 2, -1))
        add(cell(Yr, q), Y(base + 3, -1))
    if len(evals) == 22:
        cur[0] = "signed input binding: the custodians' x = the owner's signed x"
        add(Y(20), Y(21, -1))
    quad = [(X, Yr, Zr)]
    return lin, quad, labels

# ------------------------------------------------------------------------------------------------- prover
def public_digest(public):
    """The public SPDZ transcript (the opened values), bound into Fiat-Shamir right after the context. Without
    it, colluding custodians could choose an opening value AFTER seeing the batch challenge (review3
    forge_public: a steered weight update accepted by the ledger)."""
    return CS.H("public-transcript", len(public), tuple(public))

def prove_zk(eng, wires, attack=None, carry=None, context=("model", 0, 0), seed=1, owner_x=None, public=()):
    """owner_x: the data owner's share-tuple commitment to x (dealt to the custodians with its opening), whose
    roots the owner signed; when given, the proof binds the custodians' x to it."""
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
            com[k].base = com[k].block
            continue
        com[k] = ZKPCS(p, shs, k)
    if owner_x is not None:
        com["xo"] = owner_x
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
        """Compute round rnd of sumcheck `name` on shares, hide it as a Ligero row, commit, return the roots."""
        if rnd == 0:
            if name == "bg":
                state[name] = dict(f=list(wires["b"]), g=list(wires["g1"]), sub=list(wires["bg"]),
                                   eq=eqv(tau, p), deg=3, claim=0)
            else:
                Wk, vk, tp = tables[name]
                W, et = wires[Wk], eqv(tau, p)
                f = ([eng.lin([(et[i], W[i][j]) for i in range(d)]) for j in range(d)] if not tp else
                     [eng.lin([(et[j], W[i][j]) for j in range(d)]) for i in range(d)])
                claim = None
                if attack == "forge_sumcheck" and name == "z1":
                    zsum = [sum(com["z1"].rows[i][r][c] for i in range(n)) % p for r in range(com["z1"].Rd)
                            for c in range(com["z1"].C)]
                    claim = mle(zsum, tau, p)
                state[name] = dict(f=f, g=list(wires[vk]), sub=None, eq=None, deg=2, claim=claim)
        else:
            st = state[name]
            r = rs[-1]
            fold = lambda T: [eng.lin([(1 - r, T[2 * k]), (r, T[2 * k + 1])]) for k in range(len(T) // 2)]
            st["f"], st["g"] = fold(st["f"]), fold(st["g"])
            if st["sub"] is not None:
                st["sub"] = fold(st["sub"])
            if st["eq"] is not None:
                st["eq"] = [(st["eq"][2 * k] * (1 - r) + st["eq"][2 * k + 1] * r) % p for k in range(len(st["eq"]) // 2)]
            if st["claim"] is not None:
                st["claim"] = CS.lag3(st["last"], r, p)
        st = state[name]
        f, g, sub, eqt, deg = st["f"], st["g"], st["sub"], st["eq"], st["deg"]
        half = len(f) // 2
        vals = []
        for Xv in range(deg + 1):
            acc = None
            for k in range(half):
                lo, hi = 2 * k, 2 * k + 1
                term = eng.mul(eng.lin([(1 - Xv, f[lo]), (Xv, f[hi])]), eng.lin([(1 - Xv, g[lo]), (Xv, g[hi])]))
                if sub is not None:
                    term = eng.sub(term, eng.lin([(1 - Xv, sub[lo]), (Xv, sub[hi])]))
                if eqt is not None:
                    term = eng.cmul((eqt[lo] * (1 - Xv) + eqt[hi] * Xv) % p, term)
                acc = term if acc is None else eng.add(acc, term)
            vals.append(acc)
        shares = [[v[i][0] for v in vals] for i in range(n)]
        if st["claim"] is not None:
            # colluders: make the hidden round sum match the (forged) claim
            plain = [sum(sh_[x] for sh_ in shares) % p for x in range(deg + 1)]
            fix = (st["claim"] - plain[0] - plain[1]) * pow(2, -1, p) % p
            shares[0] = [(v + fix) % p for v in shares[0]]
            st["last"] = [(v + fix) % p for v in plain]
        L.add_row(shares)
        roots = L.commit()
        round_roots.setdefault(name, []).append(roots)
        return roots
    scs, evals = schedule(tr, p, d, com, cb, bind=owner_x is not None)
    rows, urows, prod, nrows = row_layout(d, com, evals)
    # hidden evaluation row combinations u_e (no masks) and the evaluation values' shares
    ushares, yshares = [], []
    for e, (k, pt) in enumerate(evals):
        c = com[k]
        a = c.eval_weights(pt, e)
        u = [c.row_combo(i, a) for i in range(n)]
        if attack == "lie_in_u" and k == "W1n":
            hon = [list(honest_W1n[0][r * c.C:(r + 1) * c.C]) + c.ext[0][r][c.C:] for r in range(c.Rd)] + c.ext[0][c.Rd:]
            u[0] = [sum(a[r] * hon[r][cc] for r in range(c.R)) % p for cc in range(c.W)]
        b = eqv(pt[:c.mc], p)
        ushares.append(u)
        yshares.append([sum(x * y for x, y in zip(u[i][:c.C], b)) % p for i in range(n)])
        for s0 in range(0, c.W, K_L):
            L.add_row([u[i][s0:s0 + K_L] for i in range(n)])
    pairs = [(2, 1), (5, 4), (8, 7), (9, 10), (14, 15), (18, 19)]       # (x, y) evaluation indices per product
    xs = [yshares[a] for a, _ in pairs]
    ys = [yshares[b] for _, b in pairs]
    zs = [L.mul_plain(x, y) for x, y in zip(xs, ys)]
    L.add_row([[x[i] for x in xs] for i in range(n)])
    L.add_row([[y[i] for y in ys] for i in range(n)])
    L.add_row([[z[i] for z in zs] for i in range(n)])
    eval_roots = L.commit()
    mask_roots = L.commit_masks()
    tr.absorb("lig-evals", eval_roots, mask_roots)
    _, prox, pcols = CS.pcs_prove(com, [], tr, n, p)
    cols = {k: (pcols[k][0], [[sum(pcols[k][1][i][jj][0][r] for i in range(n)) % p for r in range(com[k].R)]
                              for jj in range(len(pcols[k][0]))]) for k in com}
    lin, quad, labels = constraints(p, d, com, scs, evals, cols, rows, urows, prod)
    lig = L.prove(tr, lin, quad)
    eng.mac_check("cosnark-zk")
    proof = dict(roots={k: com[k].roots for k in sorted(com)}, round_roots=round_roots, eval_roots=eval_roots,
                 mask_roots=mask_roots, prox={k: prox[k][1] for k in sorted(prox)},
                 pcs_cols={k: pcols[k] for k in sorted(pcols)}, ligero=lig)
    stats = dict(hidden_rows=nrows, hidden_values=nrows * K_L, lin_constraints=len(lin), products=NPROD,
                 ligero_wire=L.wire, ligero_beaver_scalar=L.scalar_triples, ligero_poly_triples=L.poly_triples,
                 spdz_wire={ph: v - wire0.get(ph, 0) for ph, v in eng.wire.items() if v != wire0.get(ph, 0)},
                 spdz_openings=eng.nopen - open0,
                 child={"W1": com["W1n"], "W2": com["W2n"]}, coms=com,
                 first_violated=first_violated(p, L.rows, lin, quad, labels))
    return proof, stats

# ------------------------------------------------------------------------------------------------- verifier
def verify_zk(p, n, d, context, parent_roots, chained, proof, bind=False, public=()):
    """Public data only. parent_roots: the previous step's child roots for W1, W2 (None at genesis). bind: the
    proof must carry the owner's commitment "xo" and the binding constraint (its roots are checked against the
    owner's signature by the caller)."""
    ld = d.bit_length() - 1
    sh = shapes(p, d, chained, bind)
    roots = proof["roots"]
    if sorted(roots) != sorted(VEC + MAT + (("xo",) if bind else ())):
        return False, "proof names the wrong commitments"
    if parent_roots is not None and (roots["W1"] != parent_roots["W1"] or roots["W2"] != parent_roots["W2"]):
        return False, "parent commitment is not the previous step's child commitment"
    tr = Transcript("step-zk")
    tr.absorb("ctx", context)
    tr.absorb("public", public_digest(public))
    for k in sorted(roots):
        tr.absorb(k, roots[k])
    rr = proof["round_roots"]
    if sorted(rr) != ["b", "bg", "z1", "z2"] or any(len(rr[k]) != ld for k in rr):
        return False, "wrong number of sumcheck rounds"
    scs, evals = schedule(tr, p, d, sh, lambda name, rnd, tau, rs: rr[name][rnd], bind=bind)
    rows, urows, prod, nrows = row_layout(d, sh, evals)
    tr.absorb("lig-evals", proof["eval_roots"], proof["mask_roots"])
    ok, why = CS.pcs_verify(sh, roots, [], [], {k: (None, proof["prox"][k]) for k in sh}, proof["pcs_cols"],
                            tr, n, p)
    if not ok:
        return ok, why
    pc = proof["pcs_cols"]
    cols = {k: (pc[k][0], [[sum(pc[k][1][i][jj][0][r] for i in range(n)) % p for r in range(sh[k].R)]
                           for jj in range(len(pc[k][0]))]) for k in sh}
    lin, quad, _ = constraints(p, d, sh, scs, evals, cols, rows, urows, prod)
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
    sh = [[secrets.randbelow(p) for _ in vec] for _ in range(n - 1)]
    sh.append([(v - sum(c)) % p for v, c in zip(vec, zip(*sh))])
    return ZKPCS(p, sh, label)
