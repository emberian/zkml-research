"""A collaborative proof of the MPC fork's step: the custodians jointly prove the step over their SPDZ
shares, so integrity no longer rests on any custodian being honest. Prototype, counts and checks.

2026-11-06. The MPC fork's integrity used to come from SPDZ's MAC check (which holds only if at least one
custodian is honest) and from the MPC-in-the-head audit (which full collusion defeats with consistent fake
views). A collaborative SNARK (Ozdemir-Boneh, USENIX Sec 2022) closes this: the parties run a SNARK
prover inside the MPC; the verifier sees only commitments, prover messages and openings, and soundness
is the SNARK's, which holds against ALL provers at once.

Construction (choices made for our setting, each argued in docs/DARK-LEARNING-SCHEME-DECISION.md §9):
  * Field: the shared 61-bit prime p (= the FHE fork's t). No pairings exist here, so the PCS is
    hash-based. Prototype challenges are in F_p (soundness ~2^-60 per check); a deployment draws them from
    F_{p^2} or F_{p^3}.
  * PCS on additive shares with NO hashing inside the MPC: each custodian Reed-Solomon-encodes the
    rows of ITS OWN share matrix (rate 1/4) and Merkle-commits its own columns. The commitment to v is the
    n-tuple of roots. Encoding is linear, so the committed object is the sum matrix V = sum_i V_i, and the
    Ligero/Brakedown tests run on the sum: each party sends its row combinations (a^T V_i, gamma^T V_i), the
    verifier adds them, and at t opened columns checks each party's Merkle opening against the codeword of
    the summed combination. Binding, proximity and evaluation soundness are those of the single-prover
    scheme applied to V.
  * Statements: matvecs by sumcheck (log d rounds, degree 2) ending in ONE evaluation of W's MLE; the
    rank-1 updates W' = W - d (x) v by the zero-round check W'(r) = W(r) - d(r_row) v(r_col) (construction
    (a) of the program); Hadamard gates by a degree-3 zerocheck. Products of shared values inside the
    prover use SPDZ Beaver multiplication, so the prover messages come out of MAC-checked openings.
  * Chaining: the parent commitment of step t+1 is the W' commitment of step t, so a chain of verified
    steps binds the whole trajectory.

Built here: the linear-algebra spine of the step (3 matvecs, the Hadamard gate b * g1, both rank-1
updates, parent/child chaining) as one non-interactive proof (Fiat-Shamir). NOT built, priced in counts:
the elementwise gates (truncations, the table lookup, e = trunc(z2) - y), which re-prove the SPDZ
circuits' own multiplication gates with the same zerocheck; zero-knowledge masking (mask rows, masked
sumcheck), without which the opened row combinations leak linear functionals of W to the verifier.
"""
import hashlib
import math

import spdz

BLOW = 4          # RS rate 1/4
T_COLS = 97       # opened columns per commitment: (3/4)^97 = 2^-40.26 proximity error at rate 1/4 (gen 4; was 64, 2^-26.6)

def H(*parts):
    m = hashlib.sha256()
    for x in parts:
        m.update(repr(x).encode())
    return m.hexdigest()

class Transcript:
    def __init__(self, label):
        self.state = H("cosnark", label)

    def absorb(self, *x):
        self.state = H(self.state, *x)

    def chal(self, p, k=1):
        out = []
        for i in range(k):
            self.state = H(self.state, "c", i)
            out.append(int(self.state, 16) % p)
        return out

def distinct_cols(tr, p, T, npts):
    """T DISTINCT column indices from the transcript (sampling without replacement: a repeated index is drawn
    again). With replacement, 64 draws over a few hundred columns give about 60 distinct columns."""
    out, seen = [], set()
    while len(out) < min(T, npts):
        j = tr.chal(p)[0] % npts
        if j not in seen:
            seen.add(j)
            out.append(j)
    return out

class LifeExhausted(Exception):
    pass

def eqv(r, p):
    """eq(r, idx) for idx in [0, 2^len(r)), bit k of idx paired with r[k]."""
    v = [1]
    for rk in r:
        v = [x * (1 - rk) % p for x in v] + [x * rk % p for x in v]
    return v

def mle(vec, r, p):
    return sum(a * b for a, b in zip(vec, eqv(r, p))) % p

# ------------------------------------------------------------------------------------------- the PCS
HIDE = 0          # zero-knowledge PCS (cosnark ZK layer 1): random tail coefficients per row. A commitment that is
                  # opened in L proofs (a chained W: child of step t, parent of step t+1) reveals up to L*t columns,
                  # so it needs HIDE >= L * T_COLS
NMASK = 0         # random mask rows per commitment: per life, one per evaluation it serves plus one proximity mask
LIVES = 2         # a weight commitment lives twice (child, then parent); masks are split into LIVES blocks

class SharePCS:
    """Commitment to v (length 2^m) given as n additive share vectors; R x C layout, idx = row * C + col.
    Hiding mode (HIDE, NMASK > 0): every row is encoded with HIDE extra random coefficients, so any t <= HIDE
    opened columns are uniform whatever the data; and NMASK random mask rows are appended. Evaluation e adds mask
    row e with weight 1 (its revealed row combination is uniform; the custodians send m_e = <M_e, b> so the
    verifier can still subtract it). The proximity combination adds the LAST mask row with weight 1. Each
    custodian draws its own mask and tail shares locally: no communication."""
    def __init__(self, p, shares, label, hide=None, nmask=None, legacy_public_seed=False):
        import random as _r
        import secrets as _s
        self.p, self.label = p, label
        self.hide = HIDE if hide is None else hide
        self.nmask = NMASK if nmask is None else nmask
        m = (len(shares[0]) - 1).bit_length()
        self.m = m
        self.mr, self.mc = m // 2, m - m // 2
        self.Rd, self.C = 1 << self.mr, 1 << self.mc
        self.R = self.Rd + self.nmask
        self.base = 0                     # which block of mask rows this proof uses (0: first life)
        self.block = self.nmask // LIVES if self.nmask else 0
        self.W = self.C + self.hide
        self.pts = list(range(1, BLOW * self.W + 1))
        self.rows = [[s[r * self.C:(r + 1) * self.C] for r in range(self.Rd)] for s in shares]
        self.ext = []
        for i, rows in enumerate(self.rows):
            # Each custodian's tails and mask rows come from ITS OWN secret randomness. Until 2026-11-06 they were
            # seeded from public data (label, party, hide, nmask): anyone could recompute them and strip them from
            # the opened columns, so layer 1 did not hide (zk_seed_falsifier.py). legacy_public_seed keeps the old
            # behaviour for that falsifier only.
            rng = _r.Random(H("mask", label, i, self.hide, self.nmask)) if legacy_public_seed else \
                _r.Random(_s.randbits(256))
            ext = [list(r) + [rng.randrange(p) for _ in range(self.W - self.C)] for r in rows]
            ext += [[rng.randrange(p) for _ in range(self.W)] for _ in range(self.nmask)]
            self.ext.append(ext)
        self.enc = [[self.encode(row) for row in rows] for rows in self.ext]
        self.trees = [self.merkle(E) for E in self.enc]
        self.roots = [t[-1][0] for t in self.trees]

    def encode(self, row):
        p = self.p
        out = []
        for x in self.pts:
            acc = 0
            for c in reversed(row):
                acc = (acc * x + c) % p
            out.append(acc)
        return out

    def merkle(self, E):
        level = [H("leaf", [E[r][j] for r in range(len(E))]) for j in range(len(self.pts))]
        level += [H("pad", j) for j in range((1 << (len(level) - 1).bit_length()) - len(level))]
        tree = [level]
        while len(level) > 1:
            level = [H(level[i], level[i + 1]) for i in range(0, len(level), 2)]
            tree.append(level)
        return tree

    def open_col(self, i, j):
        path, k = [], j
        for lvl in self.trees[i][:-1]:
            path.append(lvl[k ^ 1])
            k //= 2
        return [self.enc[i][r][j] for r in range(self.R)], path

    def row_combo(self, i, a):
        p = self.p
        return [sum(a[r] * self.ext[i][r][c] for r in range(self.R)) % p for c in range(self.W)]

    def eval_weights(self, pt, e):
        a = eqv(pt[self.mc:], self.p) + [0] * self.nmask
        if self.nmask:
            assert e < self.block - 1, "each mask row serves exactly one evaluation (the block's last is the proximity mask)"
            a[self.Rd + self.base + e] = 1
        return a

    def mask_corr(self, i, pt, e):
        if not self.nmask:
            return 0
        b = eqv(pt[:self.mc], self.p)
        return sum(x * y for x, y in zip(self.ext[i][self.Rd + self.base + e][:self.C], b)) % self.p

    def prox_row(self):
        return self.Rd + self.base + self.block - 1

    def prox_len(self):
        return self.R - (1 if self.nmask else 0)

    def prox_weights(self, gam):
        """gamma on every row except this life's proximity mask, which gets weight 1 (so the revealed
        combination is uniform). Rows of the OTHER life are still tested (their weights are random)."""
        if not self.nmask:
            return list(gam)
        g = list(gam)
        g.insert(self.prox_row(), 1)
        return g

def pcs_prove(com, evals, tr, n, p, u_hook=None):
    """The custodians' PCS messages for every (commitment, point) in evals, then proximity, then columns."""
    msgs, used = [], {}
    for k, pt in evals:
        c = com[k]
        e = used.get(k, 0)
        used[k] = e + 1
        a = c.eval_weights(pt, e)
        u = [c.row_combo(i, a) for i in range(n)]
        if u_hook:
            u = u_hook(k, c, a, u)
        m = [c.mask_corr(i, pt, e) for i in range(n)]
        msgs.append((u, m))
        tr.absorb("u", k, u, m)
    prox = {}
    for k in sorted(com):
        c = com[k]
        gam = c.prox_weights(tr.chal(p, c.prox_len()))
        prox[k] = (gam, [c.row_combo(i, gam) for i in range(n)])
        tr.absorb("g", k, prox[k][1])
    cols = {}
    for k in sorted(com):
        c = com[k]
        # a hiding commitment may be opened in at most LIVES proofs: its tails cover LIVES * T_COLS columns. A third
        # opening (a retry, a refused bundle) would let anyone interpolate the data (review3 lives_leak). The
        # custodians keep this counter (durably, in a deployment) and refuse the opening.
        c.opened_lives = getattr(c, "opened_lives", 0) + 1
        if c.hide and c.opened_lives > getattr(c, "max_lives", LIVES):
            raise LifeExhausted(f"commitment {k} already opened in {LIVES} proofs; a further opening reveals it")
        J = distinct_cols(tr, p, T_COLS, len(c.pts))
        cols[k] = (J, [[c.open_col(i, j) for j in J] for i in range(n)])
    return msgs, prox, cols

def pcs_value(c, pt, msg, p):
    u, m = msg
    b = eqv(pt[:c.mc], p)
    return (sum(sum(ui[cc] for ui in u) * b[cc] for cc in range(c.C)) - sum(m)) % p

def pcs_verify(com, roots, evals, msgs, prox, cols, vt, n, p):
    """Replays the PCS part of the transcript and checks Merkle paths, proximity and evaluation consistency.
    Uses only shapes from com (R, C, W, mc, nmask), never the committed data."""
    for ie, (k, pt) in enumerate(evals):
        vt.absorb("u", k, msgs[ie][0], msgs[ie][1])
    gams = {}
    for k in sorted(com):
        c = com[k]
        gams[k] = c.prox_weights(vt.chal(p, c.prox_len()))
        if prox[k][0] is not None and gams[k] != prox[k][0]:
            return False, "proximity challenge mismatch"
        vt.absorb("g", k, prox[k][1])
    used = {}
    eweights = []
    for k, pt in evals:
        e = used.get(k, 0)
        used[k] = e + 1
        eweights.append(com[k].eval_weights(pt, e))
    for k in sorted(com):
        c = com[k]
        npts = len(c.pts)
        J = distinct_cols(vt, p, T_COLS, npts)
        if J != cols[k][0]:
            return False, "column challenge mismatch"
        gam, gs = gams[k], prox[k][1]
        gcode = encode_pub(p, [sum(g[cc] for g in gs) % p for cc in range(c.W)], npts)
        ucodes = [(eweights[ie], encode_pub(p, [sum(ui[cc] for ui in msgs[ie][0]) % p for cc in range(c.W)], npts))
                  for ie, (kk, pt) in enumerate(evals) if kk == k]
        for jj, j in enumerate(J):
            colsum = [0] * c.R
            for i in range(n):
                col, path = cols[k][1][i][jj]
                if not verify_path(roots[k][i], col, j, path):
                    return False, f"Merkle opening fails ({k}, custodian {i})"
                colsum = [(a + b) % p for a, b in zip(colsum, col)]
            if sum(g * x for g, x in zip(gam, colsum)) % p != gcode[j]:
                return False, f"proximity test fails ({k})"
            for a, ucode in ucodes:
                if sum(ai * x for ai, x in zip(a, colsum)) % p != ucode[j]:
                    return False, f"evaluation consistency fails at an opened column ({k})"
    return True, "accept"

def verify_path(root, col, j, path):
    h = H("leaf", col)
    k = j
    for sib in path:
        h = H(h, sib) if k % 2 == 0 else H(sib, h)
        k //= 2
    return h == root

def encode_pub(p, row, npts):
    out = []
    for x in range(1, npts + 1):
        acc = 0
        for c in reversed(row):
            acc = (acc * x + c) % p
        out.append(acc)
    return out

# ------------------------------------------------------------------------------------------- prover
def lag3(vals, x, p):
    """Interpolate the polynomial through (0..k-1, vals) and evaluate at x."""
    k = len(vals)
    acc = 0
    for i in range(k):
        num, den = 1, 1
        for j in range(k):
            if j != i:
                num = num * (x - j) % p
                den = den * (i - j) % p
        acc = (acc + vals[i] * num * pow(den, -1, p)) % p
    return acc

class Prover:
    """The custodians, jointly. `eng` is the SPDZ engine (products inside the prover are Beaver
    multiplications with MAC-checked openings). `wires` holds SPDZ-shared values {party: (share, mac)}."""
    def __init__(self, eng, wires, attack=None):
        self.eng, self.p, self.w, self.attack = eng, eng.p, wires, attack
        self.n = eng.n

    def plain(self, x):
        return [x[i][0] for i in range(self.n)]

    def shares_of(self, vec):
        return [[v[i][0] for v in vec] for i in range(self.n)]

    def sumcheck(self, tr, f, g, claim, deg, eqpub=None, sub=None):
        """Prove sum_k [eq_k] * f_k * g_k (- sub_k) = claim over shared tables f, g (lists of SPDZ values).
        deg = 2 (no eq) or 3 (zerocheck with public eq table and subtracted table `sub`)."""
        p, eng = self.p, self.eng
        msgs, rs = [], []
        f, g = list(f), list(g)
        sub = list(sub) if sub is not None else None
        eqt = list(eqpub) if eqpub is not None else None
        forge = self.attack == "forge_sumcheck"
        while len(f) > 1:
            half = len(f) // 2
            vals = []
            for X in range(deg + 1):
                acc = None
                for k in range(half):
                    lo, hi = 2 * k, 2 * k + 1
                    fx = eng.lin([(1 - X, f[lo]), (X, f[hi])])
                    gx = eng.lin([(1 - X, g[lo]), (X, g[hi])])
                    term = eng.mul(fx, gx)
                    if sub is not None:
                        term = eng.sub(term, eng.lin([(1 - X, sub[lo]), (X, sub[hi])]))
                    if eqt is not None:
                        term = eng.cmul((eqt[lo] * (1 - X) + eqt[hi] * X) % p, term)
                    acc = term if acc is None else eng.add(acc, term)
                vals.append(eng.open(acc, "cosnark"))
            if forge and claim is not None and (vals[0] + vals[1]) % p != claim:
                # colluding custodians shift the round polynomial so the sum check passes
                fix = (claim - vals[0] - vals[1]) * pow(2, -1, p) % p
                vals = [(v + fix) % p for v in vals]
            tr.absorb("sc", vals)
            r = tr.chal(p)[0]
            msgs.append(vals)
            rs.append(r)
            claim = lag3(vals, r, p)
            f = [eng.lin([(1 - r, f[2 * k]), (r, f[2 * k + 1])]) for k in range(half)]
            g = [eng.lin([(1 - r, g[2 * k]), (r, g[2 * k + 1])]) for k in range(half)]
            if sub is not None:
                sub = [eng.lin([(1 - r, sub[2 * k]), (r, sub[2 * k + 1])]) for k in range(half)]
            if eqt is not None:
                eqt = [(eqt[2 * k] * (1 - r) + eqt[2 * k + 1] * r) % p for k in range(half)]
        return msgs, rs

def prove_and_verify(eng, wires, parent=None, attack=None, carry=None, context=("model", 0, 0), expect=None):
    """context = (model id, epoch, step index) is bound into the transcript; the verifier checks the proof
    against `expect` (default: the same). A proof for step t cannot be accepted as step t + 1, so a valid
    edge (including a no-update edge whose child equals its parent) cannot be replayed (Astra scholar).
    Durable one-acceptance-per-counter is the acceptance ledger's job, outside this function."""
    """Runs the custodians' prover and the public verifier on one step. Returns (ok, why, counts).
    `wires`: x, z1, h, z2, d2, b, g1, bg, d1, W1, W2, W1n, W2n as SPDZ-shared values (matrices row-major)."""
    p, n = eng.p, eng.n
    P = Prover(eng, wires, attack)
    d = len(wires["x"])
    ld = d.bit_length() - 1
    flat = lambda M: [v for r in M for v in r]
    vecs = {k: wires[k] for k in ("x", "z1", "h", "z2", "d2", "b", "g1", "bg", "d1")}
    mats = {k: flat(wires[k]) for k in ("W1", "W2", "W1n", "W2n")}
    com = {}
    open0 = eng.nopen
    wire0 = dict(eng.wire)
    for k, v in list(vecs.items()) + list(mats.items()):
        sh = P.shares_of(v)
        honest_sh = [list(x) for x in sh]
        if attack in ("forge_W1n", "lie_in_u") and k == "W1n":
            sh[0] = list(sh[0]); sh[0][5] = (sh[0][5] + 1) % p           # all custodians agree on a wrong W1'
            honest_W1n = honest_sh
        if attack in ("forge_z1", "forge_sumcheck") and k == "z1":
            sh[0] = list(sh[0]); sh[0][3] = (sh[0][3] + 1) % p
        if carry and k in carry:
            # a chained, hiding commitment is NOT recomputed: the custodians carry its opening (shares, tails,
            # masks) from the previous step and use its second block of mask rows
            com[k] = carry[k]
            com[k].base = com[k].block
            continue
        com[k] = SharePCS(p, sh, k)
    if parent is not None:                      # the verifier's parent = the previous step's child roots
        parent_roots = parent
    else:
        parent_roots = {"W1": com["W1"].roots, "W2": com["W2"].roots}
    tr = Transcript("step")
    tr.absorb("ctx", context)
    for k in sorted(com):
        tr.absorb(k, com[k].roots)
    evals = []                                  # (commitment name, point) the verifier will need
    proof = dict(sumchecks={}, rank1={})
    # ---- matvecs: z = W v (row-major W, idx = row * d + col: low ld bits = col)
    def matvec(name, Wk, vk, zk, transpose=False):
        tau = tr.chal(p, ld)
        eqt = eqv(tau, p)
        W = wires[Wk]
        if not transpose:       # f_j = sum_i eq(tau, i) W[i][j]
            f = [eng.lin([(eqt[i], W[i][j]) for i in range(d)]) for j in range(d)]
        else:                   # f_i = sum_j eq(tau, j) W[i][j]
            f = [eng.lin([(eqt[j], W[i][j]) for j in range(d)]) for i in range(d)]
        # the honest prover never needs the claim (its round polynomials determine it); the colluding
        # forger targets the value the (forged) z commitment evaluates to
        claim_z = None
        if attack == "forge_sumcheck":
            zc = com[zk]
            zsum = [sum(zc.rows[i][r][c] for i in range(n)) % p for r in range(zc.Rd) for c in range(zc.C)]
            claim_z = mle(zsum, tau, p)
        msgs, rs = P.sumcheck(tr, f, wires[vk], claim_z, 2)
        proof["sumchecks"][name] = (tau, msgs, rs)
        evals.append((zk, tau))
        evals.append((vk, rs))
        evals.append((Wk, (rs + tau) if not transpose else (tau + rs)))
    matvec("z1", "W1", "x", "z1")
    matvec("z2", "W2", "h", "z2")
    matvec("b", "W2", "d2", "b", transpose=True)
    # ---- Hadamard bg = b * g1
    tau = tr.chal(p, ld)
    msgs, rs = P.sumcheck(tr, wires["b"], wires["g1"], 0, 3, eqpub=eqv(tau, p), sub=wires["bg"])
    proof["sumchecks"]["bg"] = (tau, msgs, rs)
    for k in ("b", "g1", "bg"):
        evals.append((k, rs))
    # ---- rank-1 updates, zero rounds
    for Wn, Wo, dv, vv in (("W1n", "W1", "d1", "x"), ("W2n", "W2", "d2", "h")):
        rc, rr = tr.chal(p, ld), tr.chal(p, ld)
        proof["rank1"][Wn] = (rc, rr)
        evals += [(Wn, rc + rr), (Wo, rc + rr), (dv, rr), (vv, rc)]
    # ---- PCS: row combinations per evaluation, one proximity combination per commitment, t columns
    def u_hook(k, c, a, u):
        if attack == "lie_in_u" and k == "W1n":
            # the forged W1' is committed, but custodian 0 reports the row combination of its HONEST share,
            # so every evaluation (and the rank-1 check) looks honest; only the opened columns can tell
            hon = [list(honest_W1n[0][r * c.C:(r + 1) * c.C]) + c.ext[0][r][c.C:] for r in range(c.Rd)] + c.ext[0][c.Rd:]
            u = list(u)
            u[0] = [sum(a[r] * hon[r][cc] for r in range(c.R)) % p for cc in range(c.W)]
        return u
    pcs_msgs, prox, cols = pcs_prove(com, evals, tr, n, p, u_hook)
    eng.mac_check("cosnark")
    proving_wire = {ph: v - wire0.get(ph, 0) for ph, v in eng.wire.items() if v != wire0.get(ph, 0)}
    proving_opens = eng.nopen - open0

    # =============================================================== VERIFIER (sees roots, messages, openings)
    def V():
        vt = Transcript("step")
        vt.absorb("ctx", expect if expect is not None else context)
        roots = {k: com[k].roots for k in com}
        if roots["W1"] != parent_roots["W1"] or roots["W2"] != parent_roots["W2"]:
            return False, "parent commitment is not the previous step's child commitment"
        for k in sorted(roots):
            vt.absorb(k, roots[k])
        def pcs_value_(i_eval):
            k, pt = evals[i_eval]
            return pcs_value(com[k], pt, pcs_msgs[i_eval], p)
        idx = 0
        sc_res = {}
        for name in ("z1", "z2", "b"):
            tau = vt.chal(p, ld)
            tau_p, msgs, rs = proof["sumchecks"][name]
            if tau != tau_p:
                return False, "transcript mismatch"
            claim = pcs_value_(idx)                      # z(tau) from the z commitment
            rr = []
            for vals in msgs:
                if (vals[0] + vals[1]) % p != claim:
                    return False, f"sumcheck {name}: round sum does not match the claim"
                vt.absorb("sc", vals)
                r = vt.chal(p)[0]
                rr.append(r)
                claim = lag3(vals, r, p)
            if claim != pcs_value_(idx + 1) * pcs_value_(idx + 2) % p:
                return False, f"sumcheck {name}: final check fails against the committed W and vector"
            idx += 3
        tau = vt.chal(p, ld)
        _, msgs, rs = proof["sumchecks"]["bg"]
        claim, rr = 0, []
        for vals in msgs:
            if (vals[0] + vals[1]) % p != claim:
                return False, "Hadamard zerocheck: round sum fails"
            vt.absorb("sc", vals)
            r = vt.chal(p)[0]
            rr.append(r)
            claim = lag3(vals, r, p)
        e = mle(eqv(tau, p), rr, p)
        if claim != e * (pcs_value_(idx) * pcs_value_(idx + 1) - pcs_value_(idx + 2)) % p:
            return False, "Hadamard zerocheck: final check fails (bg != b * g1)"
        idx += 3
        for Wn in ("W1n", "W2n"):
            rc, rr2 = vt.chal(p, ld), vt.chal(p, ld)
            wn, wo, dv, vv = (pcs_value_(idx + k) for k in range(4))
            if wn != (wo - dv * vv) % p:
                return False, f"rank-1 update {Wn}: W'(r) != W(r) - d(r_row) v(r_col)"
            idx += 4
        return pcs_verify(com, roots, evals, pcs_msgs, prox, cols, vt, n, p)
    ok, why = V()
    # ---- counts (the proof as the verifier receives it, and the custodians' proving cost)
    wit = sum(len(v) for v in vecs.values()) + sum(len(v) for v in mats.values())
    cw = sum(com[k].R * len(com[k].pts) for k in com)
    nev = len(evals)
    sc_elems = sum(len(m) * len(m[0]) for _, m, _ in proof["sumchecks"].values())
    u_elems = sum(n * com[k].W for k, _ in evals) + (n * nev if any(com[k].nmask for k in com) else 0)
    g_elems = sum(n * com[k].W for k in com)
    col_elems = sum(n * T_COLS * com[k].R for k in com)
    hashes = sum(n * T_COLS * (len(com[k].trees[0]) - 1) for k in com)   # path length = levels - 1
    counts = dict(witness_elems=wit, codeword_elems_per_party=cw, merkle_leaves_per_party=sum(len(com[k].pts) for k in com),
                  commitments=len(com), pcs_evaluations=len(evals),
                  proof_field_elems=sc_elems + u_elems + g_elems + col_elems + n * len(com),
                  proof_hashes=hashes + n * len(com), sumcheck_msg_elems=sc_elems, row_combo_elems=u_elems + g_elems,
                  opened_column_elems=col_elems, proving_openings=proving_opens, proving_wire=proving_wire,
                  child_roots={"W1": com["W1n"].roots, "W2": com["W2n"].roots},
                  carry={"W1": com["W1n"], "W2": com["W2n"]},
                  roots={k: com[k].roots for k in com}, coms=com)
    return ok, why, counts

# ------------------------------------------------------------------------------------------- counts at any d
def shape(m):
    return 1 << (m // 2), 1 << (m - m // 2)

def counts_formula(d, n=3, t=T_COLS, hide=0, nmask=0):
    """The built spine's counts as a function of d (validated against executed runs by run_cosnark.py,
    with and without the hiding PCS)."""
    ld = d.bit_length() - 1
    vec, mat = shape(ld), shape(2 * ld)
    coms = [vec] * 9 + [mat] * 4
    evals = [vec, vec, mat] * 3 + [vec] * 3 + [mat, mat, vec, vec] * 2
    lg = lambda C: (BLOW * (C + hide) - 1).bit_length()
    sc = 3 * ld * 3 + ld * 4
    u = sum(n * (C + hide) for _, C in evals) + (n * len(evals) if nmask else 0)
    g = sum(n * (C + hide) for _, C in coms)
    col = sum(n * t * (R + nmask) for R, _ in coms)
    opens = 3 * (6 * (d - 1) + 3 * ld) + 8 * (d - 1) + 4 * ld
    muls = 3 * 3 * (d - 1) + 4 * (d - 1)
    return dict(witness_elems=9 * d + 4 * d * d,
                codeword_elems_per_party=sum((R + nmask) * BLOW * (C + hide) for R, C in coms),
                merkle_leaves_per_party=sum(BLOW * (C + hide) for _, C in coms), commitments=13, pcs_evaluations=len(evals),
                proof_field_elems=sc + u + g + col + n * 13, proof_hashes=sum(n * t * lg(C) for _, C in coms) + n * 13,
                sumcheck_msg_elems=sc, row_combo_elems=u + g, opened_column_elems=col, proving_openings=opens,
                proving_wire={"mul": muls * 2 * n * (n - 1), "mac_check": 2 * n * (n - 1),
                              "cosnark": (opens - 2 * muls) * n * (n - 1)})

def unbuilt_formula(d, S1, S2, S3, n=3, deg=255):
    """MODEL: the elementwise gates re-proved as the SPDZ circuits' own multiplication gates, batched into
    one Hadamard zerocheck (operands linked to committed wires by one batched linear-functional check).
    Per truncation by s bits: s committed mask bits (booleanity) + 1 high part + 2(s-1) products.
    Per lookup: deg committed powers r^j, deg - 1 chain products, one public-coefficient linear check."""
    trunc = lambda s: (s + 1 + 2 * (s - 1), s + 2 * (s - 1))      # (committed, Hadamard constraints)
    parts = [trunc(S1), trunc(S1), trunc(S2), trunc(S3)]
    com = d * sum(c for c, _ in parts) + d * deg + 4 * d            # + u1, e, rem-free outputs, c's are public
    had = d * sum(h for _, h in parts) + d * (deg - 1)
    lh = max(1, (had - 1).bit_length())
    muls = 4 * had                                                 # degree-3 zerocheck: 4 points x len/2 x rounds
    opens = 2 * muls + 4 * lh
    return dict(committed_elems=com, hadamard_constraints=had, proving_openings=opens,
                proving_wire=opens * n * (n - 1))
