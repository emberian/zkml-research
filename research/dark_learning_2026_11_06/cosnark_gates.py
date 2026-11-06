"""The elementwise gates of the MPC fork's step, proved collaboratively: the custodians show that they
executed the SPDZ program for the nonlinear middle (truncations, the table lookup, e = trunc(z2) - y,
bg = b * g1) on the committed spine vectors. Integrity against full collusion, like cosnark.py.

2026-11-06. The construction rests on one observation. In SPDZ every shared value is a PUBLIC-linear
form in the preprocessed values (atoms) and the public openings. So "the custodians ran the program"
is exactly:
  (O) every opening equals its form evaluated on the atoms (a linear constraint, value public);
  (P) the preprocessing is well formed:
        Beaver triples ta * tb = tc                               (Hadamard);
        truncation mask bits trb are boolean                      (Hadamard b * b = b);
        tr = sum 2^i trb_i + 2^s trh                              (linear);
        trh in [0, 2^(K + kappa - s)) via its bits trhb, boolean  (Hadamard + linear). Without this
          range, rhi is a free field element and u = (c >> s) - rhi - borrow is no longer
          floor(z / 2^s): colluders could steer the lookup input;
        lookup powers pw_j = pw_1 * pw_(j-1)                      (Hadamard);
  (X) the middle's inputs and outputs are the spine's committed vectors (z1, z2, b, y in; h, g1, d2,
      bg, d1 out): linear constraints tying each form to an external atom.
The VERIFIER derives this constraint system itself, by replaying run_step symbolically against the
public transcript (RecEngine in symbolic mode: an opening reads its value from the transcript, a
preprocessing call makes a fresh atom). Nothing about the forms comes from the prover.

Proof (one Fiat-Shamir transcript, chained after cosnark's spine):
  * commit P (the middle's atoms, plus the dealer-provided bits of each trh, which is proof-only
    preprocessing) and the Hadamard operand vectors A, B, C (gathers of P), with the share-codeword PCS;
  * zerocheck A * B - C = 0 (degree 3; MPC Beaver products);
  * all linear constraints, the copy constraints A = P[ia], B = P[ib], C = P[ic], and the IO
    constraints are batched with random gammas into sum_X <q_X, X> = const. Each <q_X, X> is a sumcheck
    against a PUBLIC table q_X: its round polynomials are local on shares (no MPC multiplication). It ends in
    one PCS evaluation of X, and the verifier evaluates q_X's MLE itself.
Semantics proved: the SPDZ program's own (floor of the canonical representative). It equals step_spec
whenever the spec's input bounds hold. Those bounds are the C2 envelope's job, not this proof's.
"""
import spdz

KAPPA = spdz.KAPPA

class SV(dict):
    """A shared value plus its form: {atom: coeff} and a constant."""
    __slots__ = ("form", "const")

def mk(sh, form, const=0):
    v = SV(sh)
    v.form, v.const = form, const
    return v

class RecEngine(spdz.Engine):
    """Live (custodians: real shares) or symbolic (verifier: no shares, reads the public transcript)."""
    def __init__(self, p, n, dealer, symbolic=False, transcript=None, seed=1, cheat=None, attack=None):
        if symbolic:
            super().__init__(p, n, dealer, active=[], transcript=transcript)
        else:
            super().__init__(p, n, dealer, cheat=cheat)
        self.attack, self.attack_done = attack, False
        self.symbolic = symbolic
        self.atoms = []            # (kind, tag)
        self.atom_sh = []          # per atom: {party: share} (live only)
        self.ext = {}              # (name, k) -> atom id
        self.cons = []             # (form, const, value, kind)
        self.had = []              # (a, b, c) atom ids
        self.lp_run = []
        self.tctx = None
        self.last = []
        import random
        self.prng = random.Random(seed)

    # ------------------------------------------------------------ atoms
    def _atom(self, kind, tag, sh=None):
        self.atoms.append((kind, tag))
        self.atom_sh.append(sh)
        return len(self.atoms) - 1

    def _share(self, v):
        """Proof-only preprocessing (the trh bits): authenticated shares from the ideal dealer."""
        p, n = self.p, self.n
        xs = [self.prng.randrange(p) for _ in range(n - 1)]
        xs.append((v - sum(xs)) % p)
        ms = [self.prng.randrange(p) for _ in range(n - 1)]
        ms.append((self.dealer.alpha * v - sum(ms)) % p)
        self.proofprep = getattr(self, "proofprep", 0) + 1
        return {i: (xs[i], ms[i]) for i in range(n)}

    def prep(self, tag, value_fn):
        if self.symbolic:
            sh = {}
            vals = None
        else:
            # malformed preprocessing, as a fully colluding custodian set (who are also the dealer) can produce
            if not self.attack_done and (self.attack, tag) in (("bad_triple", "tc"), ("nonboolean_bit", "trb"),
                                                                ("mask_out_of_range", "tr")):
                f0 = value_fn
                bump = {"tc": 1, "trb": 2, "tr": 1 << 60}[tag]
                value_fn = lambda f0=f0, bump=bump: f0() + bump
                self.attack_done = True
            sh = super().prep(tag, value_fn)
            vals = dict(sh)
        a = self._atom("prep", tag, vals)
        p = self.p
        # well-formedness relations, recorded by tag (the same in live and symbolic mode)
        if tag == "tc":
            ta, tb = self.last[-2], self.last[-1]
            self.had.append((ta, tb, a))
        elif tag == "trb":
            self.had.append((a, a, a))
            self.tctx["bits"].append(a)
        elif tag == "tr":
            self.tctx["r"] = a
        elif tag == "trh":
            s, K = self.tctx["s"], self.tctx["K"]
            nb = K + KAPPA - s
            val = None if self.symbolic else sum(x[0] for x in vals.values()) % p
            bits = []
            for j in range(nb):
                bsh = None if self.symbolic else self._share((val >> j) & 1)
                b = self._atom("proofprep", "trhb", bsh)
                self.had.append((b, b, b))
                bits.append(b)
            form = {self.tctx["r"]: 1, a: (-(1 << s)) % p}
            for i, rb in enumerate(self.tctx["bits"]):
                form[rb] = (-(1 << i)) % p
            self.cons.append((form, 0, 0, "trunc-mask"))
            form = {a: 1}
            for j, b in enumerate(bits):
                form[b] = (-(1 << j)) % p
            self.cons.append((form, 0, 0, "trh-range"))
        elif tag == "lp":
            self.lp_run.append(a)
            if len(self.lp_run) >= 2:
                self.had.append((self.lp_run[0], self.lp_run[-2], a))
        self.last = (self.last + [a])[-2:]
        return mk(sh, {a: 1})

    # ------------------------------------------------------------ linear ops with forms
    def _comb(self, terms, const):
        p = self.p
        f = {}
        for c, x in terms:
            for k, v in x.form.items():
                f[k] = (f.get(k, 0) + c * v) % p
        return {k: v for k, v in f.items() if v}, const % p

    def add(self, x, y):
        f, c = self._comb([(1, x), (1, y)], x.const + y.const)
        return mk(super().add(x, y), f, c)

    def sub(self, x, y):
        f, c = self._comb([(1, x), (-1, y)], x.const - y.const)
        return mk(super().sub(x, y), f, c)

    def cmul(self, c0, x):
        f, c = self._comb([(c0, x)], c0 * x.const)
        return mk(super().cmul(c0, x), f, c)

    def cadd(self, c0, x):
        return mk(super().cadd(c0, x), dict(x.form), x.const + c0)

    def lin(self, terms, const=0):
        f, c = self._comb([(cc, x) for cc, x in terms if cc % self.p], const + sum(cc * x.const for cc, x in terms))
        sh = super().lin([(cc, x) for cc, x in terms], 0) if self.active else {}
        if not self.active:
            return mk({}, f, c)
        out = mk(sh, f, c)
        return mk(super().cadd(const, sh) if const else sh, f, c)

    def open(self, x, phase="open"):
        if self.symbolic:
            ph, bs, v = self.transcript[self.tpos]
            self.tpos += 1
            self.nopen += 1
            self.open_log.append(({}, v))
        else:
            v = super().open(x, phase)
        self.cons.append((dict(x.form), x.const, v, phase))
        return v

    # ------------------------------------------------------------ gadget context
    def trunc(self, x, s, K):
        self.tctx = dict(s=s, K=K, bits=[])
        out = super().trunc(x, s, K)
        self.tctx = None
        return out

    def lookup2(self, u, offset, tables_coeffs, deg):
        self.lp_run = []
        out = super().lookup2(u, offset, tables_coeffs, deg)
        self.lp_run = []
        return out

    # ------------------------------------------------------------ the middle's IO
    def rec_in(self, name, vec):
        out = []
        for k, x in enumerate(vec):
            a = self._atom("ext", (name, k), None)
            self.ext[(name, k)] = a
            out.append(mk(dict(x), {a: 1}))
        return out

    def rec_out(self, name, vec):
        p = self.p
        for k, x in enumerate(vec):
            a = self._atom("ext", (name, k), None)
            self.ext[(name, k)] = a
            f = dict(x.form)
            f[a] = (f.get(a, 0) - 1) % p
            self.cons.append((f, x.const, 0, "io"))


MIDDLE_PHASES = ("trunc", "lookup", "mul", "trunc-mask", "trh-range", "io")

def middle(rec):
    """Restrict the recorded system to the nonlinear middle: atoms referenced by middle constraints."""
    cons = [c for c in rec.cons if c[3] in MIDDLE_PHASES]
    used = set()
    for f, _, _, _ in cons:
        used.update(f)
    for t in rec.had:
        used.update(t)
    prep_atoms = sorted(a for a in used if rec.atoms[a][0] != "ext")
    ext_atoms = sorted(a for a in used if rec.atoms[a][0] == "ext")
    return cons, list(rec.had), prep_atoms, ext_atoms


# ============================================================================== prover + verifier
import cosnark as CS

def pad(xs, zero):
    n = 1
    while n < max(1, len(xs)):
        n *= 2
    return list(xs) + [zero] * (n - len(xs))

def sumcheck_pub(eng, tr, q, X, p):
    """Prove <q, X> for a PUBLIC table q and shared X: round polynomials are local linear combinations of
    shares (no Beaver products), opened. Returns (msgs, rs)."""
    q, X = list(q), list(X)
    msgs, rs = [], []
    while len(X) > 1:
        half = len(X) // 2
        vals = []
        for t in range(3):
            terms = []
            for k in range(half):
                qa = (q[2 * k] * (1 - t) + q[2 * k + 1] * t) % p
                terms.append((qa * (1 - t) % p, X[2 * k]))
                terms.append((qa * t % p, X[2 * k + 1]))
            vals.append(eng.open(eng.lin(terms), "cosnark-lin"))
        tr.absorb("scl", vals)
        r = tr.chal(p)[0]
        msgs.append(vals)
        rs.append(r)
        q = [(q[2 * k] * (1 - r) + q[2 * k + 1] * r) % p for k in range(half)]
        X = [eng.lin([(1 - r, X[2 * k]), (r, X[2 * k + 1])]) for k in range(half)]
    return msgs, rs

def prove_and_verify_middle(live, sym, wires, spine_roots, attack=None):
    """live: RecEngine run by the custodians (shares); sym: RecEngine replayed by the verifier from the
    public transcript. wires: spine SPDZ vectors (z1, z2, b, y, h, g1, d2, bg, d1)."""
    p, n = live.p, live.n
    zero = {i: (0, 0) for i in range(n)}
    cons_l, had_l, prep_l, ext_l = middle(live)
    cons, had, prep, ext = middle(sym)
    if (len(cons_l), len(had_l), prep_l, ext_l) != (len(cons), len(had), prep, ext) or had_l != had:
        return False, "prover and verifier constraint systems differ (program/transcript mismatch)", {}
    eng = spdz.Engine(p, n, live.dealer)                      # the proving MPC (same MAC key)
    pos = {a: k for k, a in enumerate(prep)}
    Pv = pad([live.atom_sh[a] for a in prep], zero)
    if attack == "bad_triple":
        # all custodians agree on a malformed Beaver triple (c != a b): the triple's c atom is shifted
        a_c = had[0][2]
        k = pos[a_c]
        Pv[k] = dict(Pv[k]); Pv[k][0] = ((Pv[k][0][0] + 1) % p, Pv[k][0][1])
    if attack == "nonboolean_bit":
        a_b = [t for t in had if t[0] == t[1] == t[2]][0][0]
        k = pos[a_b]
        Pv[k] = dict(Pv[k]); Pv[k][0] = ((Pv[k][0][0] + 2) % p, Pv[k][0][1])
    Av = pad([Pv[pos[a]] for a, _, _ in had], zero)
    Bv = pad([Pv[pos[b]] for _, b, _ in had], zero)
    Cv = pad([Pv[pos[c]] for _, _, c in had], zero)
    names = ("z1", "z2", "b", "y", "h", "g1", "d2", "bg", "d1")
    extv = {nm: pad(wires[nm], zero) for nm in names}
    if attack == "wrong_output":
        # the colluders commit an h that is NOT the lookup of u1 (one entry +1) and prove the spine on it
        extv["h"] = list(extv["h"]); extv["h"][0] = dict(extv["h"][0])
        extv["h"][0][0] = ((extv["h"][0][0][0] + 1) % p, extv["h"][0][0][1])
    vecs = dict(P=Pv, A=Av, B=Bv, C=Cv, **extv)
    sh = lambda V: [[x[i][0] for x in V] for i in range(n)]
    com = {k: CS.SharePCS(p, sh(V), k) for k, V in vecs.items()}
    tr = CS.Transcript("middle")
    for k in sorted(com):
        tr.absorb(k, com[k].roots)
    evals = []
    # ---- zerocheck A * B - C
    lh = (len(Av) - 1).bit_length()
    tau = tr.chal(p, lh)
    Pr = CS.Prover(eng, None)
    zmsgs, zrs = Pr.sumcheck(tr, Av, Bv, 0, 3, eqpub=CS.eqv(tau, p), sub=Cv)
    evals += [("A", zrs), ("B", zrs), ("C", zrs)]
    # ---- the linear batch
    def build_q(tr_):
        gam = tr_.chal(p, len(cons) + 3 * len(had))
        q = {k: [0] * len(V) for k, V in vecs.items() if k not in ("P", "A", "B", "C")}
        q.update(P=[0] * len(Pv), A=[0] * len(Av), B=[0] * len(Bv), C=[0] * len(Cv))
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
    q, const = build_q(tr)
    claimed = {}
    lsc = {}
    for k in sorted(vecs):
        v = eng.open(eng.lin([(q[k][i], vecs[k][i]) for i in range(len(q[k])) if q[k][i]]) if any(q[k]) else
                     eng.lin([(0, vecs[k][0])]), "cosnark-lin")
        claimed[k] = v
        tr.absorb("claim", k, v)
    for k in sorted(vecs):
        msgs, rs = sumcheck_pub(eng, tr, q[k], vecs[k], p)
        lsc[k] = (msgs, rs)
        evals.append((k, rs))
    # ---- PCS openings (shared routine with the spine; hiding mode follows CS.HIDE / CS.NMASK)
    pcs_msgs, prox, cols = CS.pcs_prove(com, evals, tr, n, p)
    eng.mac_check("middle")

    # ======================================================== VERIFIER
    def V():
        for nm in names:
            if nm in spine_roots and com[nm].roots != spine_roots[nm]:
                return False, f"middle's {nm} is not the spine's committed {nm}"
        vt = CS.Transcript("middle")
        roots = {k: com[k].roots for k in com}
        for k in sorted(roots):
            vt.absorb(k, roots[k])
        def pv(ie):
            k, pt = evals[ie]
            return CS.pcs_value(com[k], pt, pcs_msgs[ie], p)
        tau = vt.chal(p, lh)
        claim, rr = 0, []
        for vals in zmsgs:
            if (vals[0] + vals[1]) % p != claim:
                return False, "Hadamard zerocheck (preprocessing well-formedness): round sum fails"
            vt.absorb("sc", vals)
            r = vt.chal(p)[0]
            rr.append(r)
            claim = CS.lag3(vals, r, p)
        if claim != CS.mle(CS.eqv(tau, p), rr, p) * (pv(0) * pv(1) - pv(2)) % p:
            return False, "Hadamard zerocheck: a triple, bit or power is malformed"
        qv, constv = build_q(vt)
        for k in sorted(vecs):
            vt.absorb("claim", k, claimed[k])
        if (sum(claimed.values()) + constv) % p:
            return False, "linear batch: openings/IO/copy constraints do not hold"
        for ie, k in enumerate(sorted(vecs)):
            msgs, _ = lsc[k]
            claim, rr = claimed[k], []
            for vals in msgs:
                if (vals[0] + vals[1]) % p != claim:
                    return False, f"linear sumcheck {k}: round sum fails"
                vt.absorb("scl", vals)
                r = vt.chal(p)[0]
                rr.append(r)
                claim = CS.lag3(vals, r, p)
            if claim != CS.mle(qv[k], rr, p) * pv(3 + ie) % p:
                return False, f"linear sumcheck {k}: final check fails"
        return CS.pcs_verify(com, roots, evals, pcs_msgs, prox, cols, vt, n, p)
    ok, why = V()
    counts = dict(atoms=len(prep), proofprep_bits=getattr(live, "proofprep", 0), hadamard=len(had),
                  linear_constraints=len(cons), committed_elems=sum(len(V) for k, V in vecs.items()
                                                                     if k in ("P", "A", "B", "C")),
                  proving_openings=eng.nopen, proving_wire=dict(eng.wire),
                  proving_wire_total=sum(eng.wire.values()),
                  public_openings_in_constraints=sum(1 for c in cons if c[3] in ("trunc", "lookup", "mul")))
    return ok, why, counts

def counts_formula(d, S1=5, K1=13, S2=4, K2=8, S3=8, K3=13, deg=255, n=3):
    """The middle's counts as a function of d (checked against execution by run_cosnark_gates.py)."""
    def trunc(s, K):
        nb = K + KAPPA - s
        return dict(atoms=2 + s + 6 * (s - 1) + nb, pp=nb, had=s + nb + 2 * (s - 1), lin=1 + 4 * (s - 1) + 2)
    gates = [trunc(S1, K1), trunc(S1, K1), trunc(S2, K2), trunc(S3, K3),
             dict(atoms=deg, pp=0, had=deg - 1, lin=1), dict(atoms=3, pp=0, had=1, lin=2)]
    atoms = d * sum(g["atoms"] for g in gates)
    had = d * sum(g["had"] for g in gates)
    lin = d * sum(g["lin"] for g in gates) + 5 * d
    p2 = lambda x: 1 << max(0, (x - 1).bit_length())
    L, PL, dl = p2(had), p2(atoms), p2(d)
    lg = lambda x: x.bit_length() - 1
    zero_muls = 4 * (L - 1)
    opens = 2 * zero_muls + 4 * lg(L) + 3 * lg(PL) + 3 * 3 * lg(L) + 9 * 3 * lg(dl) + 13
    return dict(atoms=atoms, proofprep_bits=d * sum(g["pp"] for g in gates), hadamard=had, linear_constraints=lin,
                committed_elems=PL + 3 * L, proving_openings=opens,
                proving_wire_total=opens * n * (n - 1) + 2 * n * (n - 1))

def counts_optimized_MODEL(d, S1=5, K1=13, S2=4, K2=8, S3=8, K3=13, n=3):
    """MODEL, not built: the three levers the executed counts point to.
      1. the lookup by LogUp (about 2 Hadamard-type checks per element: the inverse and its product)
         instead of a 254-product power chain;
      2. rhi's range by three 16-bit LogUp chunks (about 2 checks each) instead of K + kappa - s bits;
      3. the zerocheck reuses the products the parties already hold at X = 0, 1, so only X = 2, 3 need new
         Beaver products (2 per pair per round instead of 4), with no power-of-two padding (chunked).
    The 16-bit range table and the LogUp multiplicities are public-size overheads, not counted per d."""
    def trunc(s, K):
        return 2 * (s - 1) + s + 3 * 2
    had = d * (trunc(S1, K1) * 2 + trunc(S2, K2) + trunc(S3, K3) + 2 + 1)
    muls = 2 * had
    opens = 2 * muls
    return dict(hadamard=had, proving_openings=opens, proving_wire_total=opens * n * (n - 1))

def counts_honest_majority_MODEL(d, n, S1=5, K1=13, S2=4, K2=8, S3=8, K3=13):
    """MODEL (IV-MPC's choice, ePrint 2026/2721 §5.2.1): Shamir shares with t < n/2, so every product in a
    sumcheck round is LOCAL (degree-2t shares) and only the round polynomials are opened. The proving wire
    of the middle and the spine is then the openings alone: each round polynomial of degree deg is deg + 1
    values, each value broadcast by every party (n (n - 1) elements)."""
    f = counts_formula(d, S1, K1, S2, K2, S3, K3)
    p2 = lambda x: 1 << max(0, (x - 1).bit_length())
    lg = lambda x: x.bit_length() - 1
    L, PL, dl = p2(f["hadamard"]), p2(f["atoms"]), p2(d)
    ld = lg(dl)
    middle_vals = 4 * lg(L) + 3 * lg(PL) + 3 * 3 * lg(L) + 9 * 3 * ld + 13
    spine_vals = 3 * 3 * ld + 4 * ld
    return dict(n=n, t=(n - 1) // 2, middle_proving_wire=middle_vals * n * (n - 1),
                spine_proving_wire=spine_vals * n * (n - 1))
