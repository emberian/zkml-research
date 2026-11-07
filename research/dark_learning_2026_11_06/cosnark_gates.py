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

def _form(x):
    """A value's form; a plain share dict (an HE outer product's output) has none."""
    return getattr(x, "form", {})

def _const(x):
    return getattr(x, "const", 0)

class RecEngine(spdz.Engine):
    """Live (custodians: real shares) or symbolic (verifier: no shares, reads the public transcript).
    he: True while an HE helper (he_matvec / he_outer, cosnark_he) runs. Its openings are recorded with kind
    "he:<phase>" and its Beaver triples add no Hadamard rows, so none of them enters the middle (MIDDLE_PHASES): they
    are bound by the public transcript's digest only, and matvec / outer correctness is the spine's (decision §22)."""
    he = False
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
        self.ranges = []           # truncations whose input bound the proof checks (trunc(..., rc=...))
        self.range_rows = []       # their rows, appended after the program (append_range)
        self.range_fail = []       # (name, index) whose PUBLIC c - lo is already outside [0, 2^L)
        self.lb = False            # the lookup proved by a bit circuit on z1's range bits (append_lookup; "LB": true)
        self.rs = False            # R1 + R2 (proof.md 23; "RS": true): range chains to bit B; K + 1 - s rhi bits
        self.quiet = False         # MPC work outside the proof (L's lookup by bits): no atoms, rows or constraints
        self.lb_req = []           # per lookup: dict(k, ext={column: ext atom}) (rec_out fills ext)
        self.lb_pend = {}          # id(output value) -> (lookup index, column), until rec_out binds it
        self.lb_rows = []          # the circuit's rows per lookup (append_lookup), filled at proof time (fill_lookup)

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
        if self.quiet:
            return mk({} if self.symbolic else super().prep(tag, value_fn), {})
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
        if tag == "tc" and not self.he:
            ta, tb = self.last[-2], self.last[-1]
            self.had.append((ta, tb, a))
        elif tag == "trb":
            self.had.append((a, a, a))
            self.tctx["bits"].append(a)
        elif tag == "tr":
            self.tctx["r"] = a
        elif tag == "trh":
            s, K = self.tctx["s"], self.tctx["K"]
            nb = K + 1 - s if self.rs else K + KAPPA - s
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
            if not self.rs:
                # under RS rhi has no bound row: every truncation's range (R1) makes the output exact without it
                form = {a: 1}
                for j, b in enumerate(bits):
                    form[b] = (-(1 << j)) % p
                self.cons.append((form, 0, 0, "trh-range"))
            self.tctx["hbits"] = bits
        elif tag == "lp" and not self.lb:
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
            for k, v in _form(x).items():
                f[k] = (f.get(k, 0) + c * v) % p
        return {k: v for k, v in f.items() if v}, const % p

    def add(self, x, y):
        f, c = self._comb([(1, x), (1, y)], _const(x) + _const(y))
        return mk(super().add(x, y), f, c)

    def sub(self, x, y):
        f, c = self._comb([(1, x), (-1, y)], _const(x) - _const(y))
        return mk(super().sub(x, y), f, c)

    def cmul(self, c0, x):
        f, c = self._comb([(c0, x)], c0 * _const(x))
        return mk(super().cmul(c0, x), f, c)

    def cadd(self, c0, x):
        return mk(super().cadd(c0, x), dict(_form(x)), _const(x) + c0)

    def lin(self, terms, const=0):
        f, c = self._comb([(cc, x) for cc, x in terms if cc % self.p], const + sum(cc * _const(x) for cc, x in terms))
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
        if self.quiet:
            return v
        kind = "he:" + phase if self.he else ("lookup-lb" if self.lb and phase == "lookup" else phase)
        self.cons.append((dict(_form(x)), _const(x), v, kind))
        if self.tctx is not None and phase == "trunc":
            self.tctx["c"] = v
        return v

    # ------------------------------------------------------------ gadget context
    def trunc(self, x, s, K, rc=None):
        """rc = (name, a, B): the proof also checks the input x in [a, a + 2^B) (append_range)."""
        if self.rs:
            # R2's soundness needs every truncation range-checked, a a multiple of 2^s, and s <= B <= K + 1
            if rc is None or rc[1] % (1 << s) or not s <= rc[2] <= K + 1:
                raise ValueError(f"RS: truncation (s={s}, K={K}) needs a range with 2^s | a and s <= B <= K + 1: {rc}")
        self.tctx = dict(s=s, K=K, bits=[])
        out = super().trunc(x, s, K)
        if rc is not None:
            name, a, B = rc
            self.ranges.append(dict(R=self.tctx["bits"] + self.tctx["hbits"], c=self.tctx["c"], K=K, s=s, a=a, B=B,
                                    name=name, k=sum(1 for r in self.ranges if r["name"] == name),
                                    r=self.tctx["r"], rs=self.rs))
        self.tctx = None
        return out

    def lookup_bits(self, t_lo, s1):
        """L (proof.md 23): the release MPC's h = SIG[u1] for every z1 truncation so far, by the LB circuit on shares
        instead of the masked powers. Outside the proof (quiet): z1's borrow chain c' - r to bit B = s1 + 8 (R_i the
        dealt trb and trhb bits, c' public after the truncation's opening; one Beaver product per bit from i = 1, all
        lookups per round), the difference bits v_j = diff_(s1 + j), then lookup_bits_ops' circuit level by level
        (products batched over every lookup in creation order). Opens only Beaver differences. Each output is bound
        to its external atom h[k] like lb's (rec_out), and append_lookup proves it."""
        p, B = self.p, s1 + 8
        Ds = [D for D in self.ranges if D["name"] == "z1"]
        if not Ds or any((D["a"], D["B"], D["s"]) != (t_lo << s1, B, s1) for D in Ds):
            raise ValueError("L: the lookup by bits needs RC with z1's interval the table's domain")
        sv = lambda a: mk({} if self.symbolic else dict(self.atom_sh[a]), {})
        self.quiet = True
        R = [[sv(D["R"][i]) for i in range(B)] for D in Ds]
        cb = []
        for D in Ds:
            L = D["K"] + KAPPA + 1
            cp = (D["c"] - (1 << D["K"]) - D["a"]) % (1 << L)
            cb.append([(cp >> i) & 1 for i in range(B)])
        n = len(Ds)
        beta = [[None] for _ in range(n)]          # beta[k][i] = beta_i
        for i in range(B):
            T = [self.mul(R[k][i], beta[k][i]) for k in range(n)] if i else [None] * n
            for k in range(n):
                if cb[k][i]:
                    nb = T[k] if i else self.lin([], 0)
                else:
                    nb = self.lin([(1, R[k][i])] + ([(1, beta[k][i]), (-1, T[k])] if i else []))
                beta[k].append(nb)
        vin = [[self.lin([(-1, R[k][s1 + j]), (-1, beta[k][s1 + j]), (2, beta[k][s1 + j + 1])], cb[k][s1 + j])
                for j in range(8)] for k in range(n)]
        ops, vph, hout = lookup_bits_ops(p, t_lo)
        lvl = {}
        for op in ops:
            lvl[op[1]] = max([lvl.get(x, 0) for x in op[2]] + [0]) if op[0] == "lin" else max(lvl.get(op[2], 0), lvl.get(op[3], 0)) + 1
        val = [dict(zip(vph, vin[k])) for k in range(n)]
        for Lv in range(max(lvl.values()) + 1):
            for k in range(n):
                for op in ops:
                    if op[0] == "lin" and lvl[op[1]] == Lv:
                        val[k][op[1]] = self.lin([(c, val[k][x]) for x, c in op[2].items()], op[3])
            for k in range(n):
                for op in ops:
                    if op[0] == "mul" and lvl[op[1]] == Lv + 1:
                        val[k][op[1]] = self.mul(val[k][op[2]], val[k][op[3]])
        hs = [self.lin([(c, val[k][x]) for x, c in hout[0].items()], hout[1]) for k in range(n)]
        self.quiet = False
        res = []
        for k, h in enumerate(hs):
            j = len(self.lb_req)
            self.lb_req.append(dict(k=j, ext={}))
            o = dict(h)
            if (self.attack, j, self.symbolic) == ("lb_h", 1, False):
                # a colluding custodian set shifts lookup 1's output by one, MAC-consistently (they hold alpha)
                s0, m0 = o[1]
                o[1] = ((s0 + 1) % self.p, (m0 + self.dealer.alpha) % self.p)
                self.attack_done = True
            v = mk(o, {})
            self.lb_pend[id(v)] = (j, 0)
            res.append(v)
        return res

    def lookup2(self, u, offset, tables_coeffs, deg):
        """With lb, the MPC is unchanged but the proof drops the masked-power relations: the opening is recorded as
        "lookup-lb" (outside the middle), so the power atoms enter no middle constraint, and each output is a value
        with the MPC's shares and no form yet. rec_out binds it to its external atom; append_lookup then proves that
        atom from z1's range bits."""
        self.lp_run = []
        out = super().lookup2(u, offset, tables_coeffs, deg)
        self.lp_run = []
        if not self.lb:
            return out
        k = len(self.lb_req)
        self.lb_req.append(dict(k=k, ext={}))
        res = []
        for col, o in enumerate(out):
            o = dict(o)
            if (self.attack, k, self.symbolic) in (("lb_h", 1, False), ("lb_g1", 1, False)) and col == (self.attack == "lb_g1"):
                # a colluding custodian set shifts lookup 1's output by one, MAC-consistently (they hold alpha)
                s0, m0 = o[1]
                o[1] = ((s0 + 1) % self.p, (m0 + self.dealer.alpha) % self.p)
                self.attack_done = True
            v = mk(o, {})
            self.lb_pend[id(v)] = (k, col)
            res.append(v)
        return res

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
            if id(x) in self.lb_pend:
                j, col = self.lb_pend.pop(id(x))
                self.lb_req[j]["ext"][col] = a
                x.form, x.const = {a: 1}, 0
                continue
            f = dict(x.form)
            f[a] = (f.get(a, 0) - 1) % p
            self.cons.append((f, x.const, 0, "io"))


MIDDLE_PHASES = ("trunc", "lookup", "mul", "trunc-mask", "trh-range", "io", "release", "range", "lookup-bits")


def append_range(eng):
    """The truncation input bound, proved (gen 6). For a truncation c = x + 2^K + r (c public; r = sum_i 2^i R_i, its
    bits R the committed trb and trhb atoms) with the declared interval x in [a, a + 2^B), B <= K + 1: with
    lo = 2^K + a and c' = c - lo (public), the rows prove that c' - r, as an INTEGER, lies in [0, 2^B). They are the
    borrow chain of c' - r over L = K + KAPPA + 1 bits: with c'_i public, beta_0 = 0,
        beta_(i+1) = c'_i ? t_i : R_i + beta_i - t_i,   t_i = R_i beta_i  (a Hadamard row)
    (beta boolean by induction), then beta_L = 0 (no borrow: c' >= r) and the difference's bits
    c'_i - R_i - beta_i + 2 beta_(i+1) = 0 for i >= B. Then x = c - 2^K - r = (c' - r) + a in the field and as an
    integer: no wrap mod p, and x in [a, a + 2^B). Honest c' < 2^B + 2^(K + KAPPA) <= 2^L. A public c' outside
    [0, 2^L) is recorded in range_fail (the verifier refuses it by name). Atoms t_i, beta_(i+1) are proof-only,
    computed by the custodians at proof time (fill_range); rows are appended after the program, in truncation order."""
    p = eng.p
    for D in eng.ranges:
        K, a, B = D["K"], D["a"], D["B"]
        L = K + KAPPA + 1
        lo = (1 << K) + a
        cp = D["c"] - lo
        if not 0 <= cp < 1 << L:
            eng.range_fail.append((D["name"], D["k"]))
        cb = [((cp % (1 << L)) >> i) & 1 for i in range(L)]
        R = D["R"]
        assert len(R) == (K + 1 if D["rs"] else K + KAPPA)
        if D["rs"]:
            # R1 (proof.md 23): the chain over i < B, then r - sum_(i<B) 2^i R_i + 2^B beta_B = 2^B floor(c' / 2^B)
            ts, bs = [], []
            beta = None
            for i in range(B):
                Ri = R[i]
                t = None
                if beta is not None:
                    t = eng._atom("proofrange", "rt", None)
                    eng.had.append((Ri, beta, t))
                nb = eng._atom("proofrange", "rb", None)
                f = {nb: 1}
                if cb[i]:
                    if t is not None:
                        f[t] = (f.get(t, 0) - 1) % p
                else:
                    for x, co in ((Ri, -1), (beta, -1), (t, 1)):
                        if x is not None:
                            f[x] = (f.get(x, 0) + co) % p
                eng.cons.append((f, 0, 0, "range"))
                ts.append(t)
                bs.append(nb)
                beta = nb
            chi = cp >> B
            g = {D["r"]: 1}
            for i in range(B):
                g[R[i]] = (g.get(R[i], 0) - (1 << i)) % p
            g[beta] = (g.get(beta, 0) + (1 << B)) % p
            eng.cons.append((g, -(chi << B) % p, 0, "range"))
            eng.range_rows.append(dict(D, L=B, cb=cb, t=ts, b=bs, chi=chi))
            continue
        assert len(R) == K + KAPPA
        ts, bs = [], []
        beta = None
        for i in range(L):
            Ri = R[i] if i < len(R) else None
            t = None
            if Ri is not None and beta is not None:
                t = eng._atom("proofrange", "rt", None)
                eng.had.append((Ri, beta, t))
            nb = eng._atom("proofrange", "rb", None)
            f = {nb: 1}
            if cb[i]:
                if t is not None:
                    f[t] = (f.get(t, 0) - 1) % p
            else:
                for x, co in ((Ri, -1), (beta, -1), (t, 1)):
                    if x is not None:
                        f[x] = (f.get(x, 0) + co) % p
            eng.cons.append((f, 0, 0, "range"))
            if i >= B:
                g = {nb: 2}
                for x in (Ri, beta):
                    if x is not None:
                        g[x] = (g.get(x, 0) - 1) % p
                eng.cons.append((g, cb[i], 0, "range"))
            ts.append(t)
            bs.append(nb)
            beta = nb
        eng.cons.append(({beta: 1}, 0, 0, "range"))
        eng.range_rows.append(dict(D, L=L, cb=cb, t=ts, b=bs))


def fill_range(live, eng):
    """The custodians' shares of the range rows' atoms (proof time, on the proving engine eng: its Beaver products
    run round by round over every truncation, round i over the truncations in order). Then each truncation's
    violation indicator beta_L + sum_(i >= B) diff_i (0 iff in bound) is opened: an honest run opens zeros. Returns
    the violated truncations as (name, index)."""
    rows = live.range_rows
    if not rows:
        return []
    n = live.n
    zero = {i: (0, 0) for i in range(n)}
    sh = lambda a: live.atom_sh[a]
    beta = [None] * len(rows)
    for i in range(max(D["L"] for D in rows)):
        idx = [k for k, D in enumerate(rows) if i < D["L"] and D["t"][i] is not None]
        prods = [eng.mul(sh(rows[k]["R"][i]), beta[k]) for k in idx]
        for k, t in zip(idx, prods):
            live.atom_sh[rows[k]["t"][i]] = t
        for k, D in enumerate(rows):
            if i >= D["L"]:
                continue
            Ri = sh(D["R"][i]) if i < len(D["R"]) else None
            bt = beta[k]
            t = live.atom_sh[D["t"][i]] if D["t"][i] is not None else None
            if D["cb"][i]:
                nb = t if t is not None else zero
            else:
                nb = eng.lin([(1, x) for x in (Ri, bt) if x is not None] + ([(-1, t)] if t is not None else []))
                nb = nb if (Ri is not None or bt is not None) else zero
            live.atom_sh[D["b"][i]] = dict(nb)
            beta[k] = nb
    if rows[0].get("rs"):
        # RS: one masked zero test over every truncation, so a refused run opens only whether some input left its
        # bound: S = sum_k g_k E_k (E_k the high row's value, g_k public coins keyed by every c), then rho S with rho a
        # fresh triple's a (uniform, authenticated) is opened: 0 iff S = 0, else uniform (proof.md 23)
        import hashlib, random
        p = eng.p
        hx = hashlib.sha256(b"dl-range-zero-test" + b"".join(D["c"].to_bytes(8, "little") for D in rows)).hexdigest()
        g = random.Random(int(hx, 16))
        terms, cst = [], 0
        for D in rows:
            B, gk = D["B"], g.randrange(p)
            terms += [(gk, sh(D["r"]))] + [(-gk * (1 << i) % p, sh(D["R"][i])) for i in range(B)]
            terms.append((gk * (1 << B) % p, sh(D["b"][B - 1])))
            cst -= gk * (D["chi"] << B)
        S = eng.lin(terms, cst % p)
        av, bv = eng.dealer.rng.randrange(p), eng.dealer.rng.randrange(p)
        rho = eng.prep("ta", lambda: av)
        eng.prep("tb", lambda: bv)
        eng.prep("tc", lambda: av * bv)
        v = eng.open(eng.mul(S, rho), "range-check")
        return [("some truncation (RS: one masked zero test)", None)] if v else []
    ind = []
    for D in rows:
        terms = [(1, sh(D["b"][-1]))]
        for i in range(D["B"], D["L"]):
            Ri = sh(D["R"][i]) if i < len(D["R"]) else None
            bt = sh(D["b"][i - 1]) if i > 0 else None
            terms += [(2, sh(D["b"][i]))] + [(-1, x) for x in (Ri, bt) if x is not None]
            terms.append((D["cb"][i], None))
        cst = sum(c for c, x in terms if x is None)
        ind.append(eng.lin([(c, x) for c, x in terms if x is not None], cst))
    vals = [eng.open(v, "range-check") for v in ind]
    return [(D["name"], D["k"]) for D, v in zip(rows, vals) if v]

class _Bits:
    """The bit circuit's builder for one lookup: atoms (kind "proofbits", made at proof time), linear definitions and
    products, in creation order. A value is a (form, const) pair, linear in the atoms."""

    def __init__(self, eng):
        self.eng, self.p = eng, eng.p
        self.ops = []                  # ("lin", atom, form, const) | ("mul", atom, x, y)

    def atom(self, form, const):
        """A fresh atom a with a = form + const (a linear row)."""
        a = self.eng._atom("proofbits", "lq", None)
        f = {a: 1}
        for x, c in form.items():
            f[x] = (f.get(x, 0) - c) % self.p
        self.eng.cons.append(({k: v for k, v in f.items() if v}, -const % self.p, 0, "lookup-bits"))
        self.ops.append(("lin", a, dict(form), const % self.p))
        return a

    def mul(self, b, v):
        """b * v for an atom b: a constant or single-atom v (alpha y + beta) costs one product b y; any other v is made
        an atom first."""
        p = self.p
        form, const = v
        if not form:
            return ({b: const % p} if const % p else {}), 0
        if len(form) > 1:
            y, al, be = self.atom(form, const), 1, 0
        else:
            ((y, al),) = form.items()
            be = const
        m = self.eng._atom("proofbits", "lm", None)
        self.eng.had.append((b, y, m))
        self.ops.append(("mul", m, b, y))
        out = {m: al % p}
        if be % p:
            out[b] = (out.get(b, 0) + be) % p
        return {k: v for k, v in out.items() if v}, 0

    def lt(self, bits, c):
        """[value < c] for the integer value sum 2^i bits[i] (boolean atoms) and a public c, LSB first:
        lt_(i+1) = c_i ? 1 - b_i + b_i lt_i : lt_i - b_i lt_i, constants folded."""
        p = self.p
        n = len(bits)
        if c <= 0:
            return {}, 0
        if c >= 1 << n:
            return {}, 1
        cur = ({}, 0)
        for i, b in enumerate(bits):
            m, mc = self.mul(b, cur)
            if (c >> i) & 1:
                f = dict(m)
                f[b] = (f.get(b, 0) - 1) % p
                cur = ({k: v for k, v in f.items() if v}, (1 + mc) % p)
            else:
                f = dict(cur[0])
                for k, v in m.items():
                    f[k] = (f.get(k, 0) - v) % p
                cur = ({k: v for k, v in f.items() if v}, (cur[1] - mc) % p)
        return cur


def _addf(*terms):
    """sum of coeff * (form, const) values, mod p (the caller's field via the last argument)."""
    p = terms[-1]
    f, c = {}, 0
    for co, (fm, cc) in terms[:-1]:
        for k, v in fm.items():
            f[k] = (f.get(k, 0) + co * v) % p
        c = (c + co * cc) % p
    return {k: v for k, v in f.items() if v}, c


def append_lookup(eng, t_lo, s1):
    """The lookup proved by a bit circuit (gen 6; program flag "LB", which needs "RC" and z1's default interval). With
    the range check, z1's rows prove the integer z1 - a in [0, 2^(s1 + 8)), a = t_lo 2^s1, through its difference
    bits diff_i = c'_i - R_i - beta_i + 2 beta_(i+1), each boolean (the borrow chain is integer subtraction). Its top
    8 bits are v = u1 - t_lo, the table index. Per lookup, after the range rows:
      bits  v_j = diff_(s1 + j), j < 8                       (8 atoms, linear rows)
      h     = w Bf - w lo + (q - 7) Bf - (q + 7) lo + 7    w = v >> 2 = sum 2^j v_(j+2) (an atom), q = t_lo / 4,
            lo = [w < -7 - q], Bf = [w < 8 - q]               so h = clamp(floor(u1 / 4), -7, 7) = SIG[u1]
      g1    = [v < 32 - t_lo] - [v < -28 - t_lo]            = DSIG[u1]   (step only: a lookup with a g1 column)
    The comparisons are bit chains on constants (_Bits.lt). Products are proof-time Beaver products (fill_lookup).
    The rows tie the circuit's h and g1 to the lookup's external atoms."""
    p = eng.p
    if t_lo % 4:
        raise ValueError("the bit lookup needs t_lo divisible by 4")
    q = t_lo // 4
    z1rows = {D["k"]: D for D in eng.range_rows if D["name"] == "z1"}
    for req in eng.lb_req:
        D = z1rows[req["k"]]
        if (D["a"], D["B"]) != (t_lo << s1, s1 + 8) or D["s"] != s1:
            raise ValueError("the bit lookup needs z1's interval to be the table's domain")
        bx = _Bits(eng)
        R, bs, cb = D["R"], D["b"], D["cb"]
        v = []
        for j in range(8):
            i = s1 + j
            f = {R[i]: 1, bs[i]: (-2) % p}
            if i > 0:
                f[bs[i - 1]] = (f.get(bs[i - 1], 0) + 1) % p
            # v_j - diff_i = v_j + R_i + beta_i - 2 beta_(i+1) - c'_i
            v.append(bx.atom({x: (-c) % p for x, c in f.items()}, cb[i]))
        lo = bx.lt(v[2:], -7 - q)
        Bf = bx.lt(v[2:], 8 - q)
        if lo[0] or Bf[0]:
            w = bx.atom({v[2 + j]: 1 << j for j in range(6)}, 0)
            wB = bx.mul(w, Bf)
            wl = bx.mul(w, lo)
        else:
            wf = ({v[2 + j]: 1 << j for j in range(6)}, 0)
            wB = (wf[0], 0) if Bf[1] else ({}, 0)
            wl = (wf[0], 0) if lo[1] else ({}, 0)
        h = _addf((1, wB), (-1, wl), (q - 7, Bf), (-(q + 7), lo), (7, ({}, 1)), p)
        outs = [h]
        if 1 in req["ext"]:
            outs.append(_addf((1, bx.lt(v, 32 - t_lo)), (-1, bx.lt(v, -28 - t_lo)), p))
        for col, (fm, c) in enumerate(outs):
            f = dict(fm)
            a = req["ext"][col]
            f[a] = (f.get(a, 0) - 1) % p
            eng.cons.append(({k: x for k, x in f.items() if x}, c, 0, "lookup-bits"))
        eng.lb_rows.append(bx.ops)


class _OpsEng:
    """A stand-in engine for _Bits that only numbers atoms (lookup_bits_ops)."""

    def __init__(self, p):
        self.p, self.n_atoms, self.cons, self.had = p, 0, [], []

    def _atom(self, kind, tag, sh=None):
        self.n_atoms += 1
        return self.n_atoms - 1


def lookup_bits_ops(p, t_lo):
    """The LB circuit for h alone (append_lookup's), as ops over 8 placeholder atoms v_j (atoms 0..7, set by the caller):
    returns (ops after the placeholders, the placeholder ids, h as (form, const)). The release MPC evaluates it on
    shares (RecEngine.lookup_bits); natively darkproof run::lookup_bits_ops."""
    q = t_lo // 4
    eng = _OpsEng(p)
    vph = [eng._atom("ph", "v") for _ in range(8)]
    bx = _Bits(eng)
    v = [bx.atom({vph[j]: 1}, 0) for j in range(8)]
    lo = bx.lt(v[2:], -7 - q)
    Bf = bx.lt(v[2:], 8 - q)
    if lo[0] or Bf[0]:
        w = bx.atom({v[2 + j]: 1 << j for j in range(6)}, 0)
        wB = bx.mul(w, Bf)
        wl = bx.mul(w, lo)
    else:
        wf = ({v[2 + j]: 1 << j for j in range(6)}, 0)
        wB = (wf[0], 0) if Bf[1] else ({}, 0)
        wl = (wf[0], 0) if lo[1] else ({}, 0)
    h = _addf((1, wB), (-1, wl), (q - 7, Bf), (-(q + 7), lo), (7, ({}, 1)), p)
    return bx.ops, vph, h


def fill_lookup(live, eng):
    """The custodians' shares of the bit circuit's atoms (proof time, after fill_range, on the proving engine eng). An
    atom's level: a linear atom the max of its form's, a product one more than its operands'. Level by level, the
    linear atoms of that level are evaluated (lookup by lookup, in creation order), then the products of the next
    level run as one batch over every lookup in creation order."""
    rows = live.lb_rows
    if not rows:
        return
    lvl = {}
    lev = lambda a: lvl.get(a, 0)
    for ops in rows:
        for op in ops:
            if op[0] == "lin":
                lvl[op[1]] = max([lev(x) for x in op[2]] + [0])
            else:
                lvl[op[1]] = max(lev(op[2]), lev(op[3])) + 1
    top = max(lvl.values())
    for L in range(top + 1):
        for ops in rows:
            for op in ops:
                if op[0] == "lin" and lvl[op[1]] == L:
                    _, a, form, const = op
                    live.atom_sh[a] = dict(eng.lin([(c, live.atom_sh[x]) for x, c in form.items()], const))
        batch = [op for ops in rows for op in ops if op[0] == "mul" and lvl[op[1]] == L + 1]
        for op in batch:
            live.atom_sh[op[1]] = dict(eng.mul(live.atom_sh[op[2]], live.atom_sh[op[3]]))


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

def prove_and_verify_middle(live, sym, wires, spine_roots, attack=None, spine_coms=None):
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
    # a vector the spine already committed is NOT recommitted: with secret tails a recomputed root would differ,
    # and the custodians hold the spine's commitment (opening) anyway
    com = {k: (spine_coms[k] if spine_coms and k in spine_coms and k != "y" else CS.SharePCS(p, sh(V), k))
           for k, V in vecs.items()}
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
