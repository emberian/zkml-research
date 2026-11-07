"""The collaborative proof of the step AS DEPLOYED: HE matvec + HE outer (he_matvec.HEMatvec, he_outer.HEOuter; decision
§22), the program native/darkstep runs. The reference the native prover (native/darkproof) is bit-exact with.

2026-11-07. The construction (agreed with the coordinator, gen 5):
  * the spine is unchanged: its sumchecks and rank-1 checks prove z1 = W1 x, z2 = W2 h, b = W2^T d2 and
    W' = W - d (x) v on the COMMITTED vectors, whatever the SPDZ-level helpers did;
  * the HE helpers' public entries (per matvec: d "he_auth" broadcasts, d Freivalds Beaver products, one "freivalds"
    opening; per outer: one "he_outer_commit" entry, one Beaver product, one "he_outer_check" opening) are bound by
    the public transcript's digest only. RecEngine records them with kind "he:<phase>" and adds no Hadamard rows
    for their triples (RecEngine.he), so they never enter the middle (MIDDLE_PHASES);
  * z1, z2, b enter the middle as before, as IO atoms bound to the spine's committed vectors (rec_in).
The middle's constraint system is therefore the plain step's (same atoms, Hadamard rows and constraints); only the
public transcript between them differs. The verifier's replay (SymMatvec, SymOuter) consumes the HE schedule's
entries without forms, and requires each he_outer_commit entry's value to be 0 (the commitment hashes are not field
elements and are not part of the bundle).

Steps: the genesis step inputs W1, W2, x, y from the data owner (2 d^2 + 2 d "input" entries). A CARRIED step takes
W1, W2 as the previous step's W1n, W2n shares and inputs only x, y (2 d entries), as native/darkstep's party loop
does. The program's truncation shifts are a parameter (Prog), pinned in the ledger's genesis record.
"""
import random

import cosnark_gates as G
import mpc_fork as MF


class ScheduleError(Exception):
    pass


class Prog:
    """The step program's proof-relevant parameters (step_spec.Program; its bounds XMAX, WMAX, CHECK_K are the C2
    envelope's, not the proof's): (s1, k1) for z1 and z2, (s2, k2) for e, (s3, k3) for b * g1 + r3; the table's domain
    [t_lo, t_lo + 256)."""
    KEYS = ("S1", "K1", "S2", "K2", "S3", "K3", "R3", "T_LO")

    def __init__(self, s1=5, k1=13, s2=4, k2=8, s3=8, k3=13, r3=0, t_lo=-128, rc=False, bounds=None, lb=False, rs=False,
                 xt=False):
        self.s1, self.k1, self.s2, self.k2, self.s3, self.k3 = s1, k1, s2, k2, s3, k3
        self.r3, self.t_lo = r3, t_lo
        self.rc = rc                   # the proof checks every truncation's input interval (append_range)
        self.over = dict(bounds or {})
        self.lb = lb                   # the lookup proved by a bit circuit on z1's range bits (append_lookup)
        if lb and not rc:
            raise ValueError("the bit lookup (LB) needs the range check (RC)")
        self.rs = rs                   # R1 + R2 (proof.md 23): range chains to bit B, rhi's bits below 2^(K + 1 - s) only
        if rs and not rc:
            raise ValueError("the short range (RS) needs the range check (RC) on every truncation")
        self.xt = xt                   # exact truncation (notes/dark-learning-gen6/xtrunc.md): r uniform in [0, p)
        if xt and not rs:
            raise ValueError("exact truncation (XT) needs the short range (RS): its rows hold for any r")

    @classmethod
    def of(cls, program):
        """From a ledger genesis "program" dict (R3, T_LO default to the harness's; "RC": true turns the proved bounds
        on; "BOUNDS": {name: [a, B]} overrides the default intervals; "LB": true proves the lookup by its bit circuit)."""
        dflt = dict(S1=5, K1=13, S2=4, K2=8, S3=8, K3=13, R3=0, T_LO=-128)
        return cls(*(program.get(k, dflt.get(k)) for k in cls.KEYS), rc=bool(program.get("RC")),
                   bounds={k: tuple(v) for k, v in program.get("BOUNDS", {}).items()}, lb=bool(program.get("LB")), rs=bool(program.get("RS")),
                   xt=bool(program.get("XT")))

    def bound(self, name, kc=10):
        """The proved input interval [a, a + 2^B) of truncation `name`: z1 (and the release's z1) the table's domain,
        every other its declared K (|x| < 2^K)."""
        if name in self.over:
            return self.over[name]
        dflt = dict(z1=(self.t_lo << self.s1, self.s1 + 8), z2=(-(1 << self.k1), self.k1 + 1),
                    e=(-(1 << self.k2), self.k2 + 1), bg=(-(1 << self.k3), self.k3 + 1),
                    score=(-(1 << self.k1), self.k1 + 1), compare=(-(1 << kc), kc + 1))
        return dflt[name]

    def rc_of(self, name, kc=10):
        return (name,) + tuple(self.bound(name, kc)) if self.rc else None

    def tables(self, p):
        """mpc_fork.tables(p) over [t_lo, t_lo + 256): SIG, DSIG interpolated at u - t_lo = 0..255."""
        import spdz
        import step_spec as S
        sig = [S.sig(u + self.t_lo) % p for u in range(256)]
        dsig = [S.dsig(u + self.t_lo) % p for u in range(256)]
        return spdz.interpolate(sig, p), spdz.interpolate(dsig, p)


class LiveHE:
    """An HE helper run by the custodians on a live RecEngine: its entries are recorded as HE entries; an outer
    product's output (plain share dicts) gets an empty form (W1n, W2n never enter the middle)."""

    def __init__(self, eng, inner, outer=False):
        self.eng, self.inner, self.outer = eng, inner, outer

    def __call__(self, *a, **k):
        self.eng.he = True
        try:
            out = self.inner(*a, **k)
        finally:
            self.eng.he = False
        if self.outer:
            out = [[G.mk(c, {}) for c in r] for r in out]
        return out


class SymMatvec:
    """The verifier's replay of one HE matvec: d he_auth entries (one "ar" atom each), d Beaver products, one
    Freivalds opening."""

    def __init__(self, eng):
        self.eng = eng

    def __call__(self, W, v, transpose=False):
        eng, d = self.eng, len(v)
        eng.he = True
        try:
            zs = [eng.auth_plain({}, "he_auth") for _ in range(d)]
            z = G.mk({}, {})
            for _ in range(d):
                eng.mul(z, z)
            eng.open(z, "freivalds")
        finally:
            eng.he = False
        return zs


class SymOuter:
    """The verifier's replay of one HE outer product: the commitment entry (value 0), one Beaver product, the check
    opening. It returns no matrix: the outer product feeds only the children, which the replay does not form."""

    def __init__(self, eng):
        self.eng = eng

    def __call__(self, a, x):
        eng = self.eng
        eng.he = True
        try:
            _, _, v = eng.transcript[eng.tpos]
            if v != 0:
                raise ScheduleError("he_outer_commit entry is not 0")
            eng.tpos += 1
            z = G.mk({}, {})
            eng.mul(z, z)
            eng.open(z, "he_outer_check")
        finally:
            eng.he = False
        return None


def run_step(eng, W1, W2, x, y, tab, owner_seed, mv, ou, prog=None, carried=None, children=True):
    """mpc_fork.run_step with the deployed helpers, a parameterized program and carried weights. carried = (M1, M2),
    the previous step's W1n, W2n shares (then only x, y are input). Returns (W1n, W2n, wires) as mpc_fork does.
    children=False (the verifier's replay): W1n, W2n are not formed (None). They are local subtractions that open
    nothing and never enter the middle, so the replay's constraint system is the same without their 2 d^2 forms."""
    pg = prog or Prog()
    d = len(x)
    eng.lb = pg.lb
    eng.rs = pg.rs
    eng.xt = getattr(pg, "xt", False)
    orng = random.Random(owner_seed)
    if carried is None:
        flat = lambda M: [v for r in M for v in r]
        sW1 = eng.input(flat(W1) if W1 else [0] * d * d, orng, "input")
        sW2 = eng.input(flat(W2) if W2 else [0] * d * d, orng, "input")
        M1 = [sW1[i * d:(i + 1) * d] for i in range(d)]
        M2 = [sW2[i * d:(i + 1) * d] for i in range(d)]
    else:
        M1, M2 = carried
    sx = eng.input(x if x else [0] * d, orng, "input")
    sy = eng.input(y if y else [0] * d, orng, "input")
    z1 = eng.rec_in("z1", mv(M1, sx))
    u1 = [eng.trunc(z, pg.s1, pg.k1, rc=pg.rc_of("z1")) for z in z1]
    hg = [eng.lookup2(u, -pg.t_lo, tab, 255) for u in u1]
    h = [a for a, _ in hg]
    g1 = [b for _, b in hg]
    eng.rec_out("h", h)
    eng.rec_out("g1", g1)
    z2 = eng.rec_in("z2", mv(M2, h))
    sy = eng.rec_in("y", sy)
    e = [eng.sub(eng.trunc(z, pg.s1, pg.k1, rc=pg.rc_of("z2")), yy) for z, yy in zip(z2, sy)]
    d2 = [eng.trunc(v, pg.s2, pg.k2, rc=pg.rc_of("e")) for v in e]
    eng.rec_out("d2", d2)
    b = eng.rec_in("b", mv(M2, d2, transpose=True))
    bg = [eng.mul(bb, g) for bb, g in zip(b, g1)]
    eng.rec_out("bg", bg)
    bgr = [eng.cadd(pg.r3 % eng.p, v) for v in bg] if pg.r3 else bg
    d1 = [eng.trunc(v, pg.s3, pg.k3, rc=pg.rc_of("bg")) for v in bgr]
    eng.rec_out("d1", d1)
    G2 = ou(d2, h)
    G1 = ou(d1, sx)
    W1n = W2n = None
    if children:
        W2n = [[eng.sub(M2[i][j], G2[i][j]) for j in range(d)] for i in range(d)]
        W1n = [[eng.sub(M1[i][j], G1[i][j]) for j in range(d)] for i in range(d)]
    if pg.rc:
        G.append_range(eng)
    if pg.lb:
        G.append_lookup(eng, pg.t_lo, pg.s1)
    return W1n, W2n, dict(h=h, d2=d2, d1=d1, x=sx, y=sy, z1=z1, z2=z2, b=b, g1=g1, bg=bg, W1=M1, W2=M2)


def replay(p, public, d, tab, prog=None, carried=False):
    """The verifier's symbolic replay of the deployed step against the public values. Returns the RecEngine (its
    tpos tells how many entries the program consumed); IndexError if the transcript is shorter than the program."""
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=[("open", {}, v) for v in public])
    # carried weights enter only the HE matvec (SymMatvec reads none of them) and the children, which are not formed
    run_step(sym, None, None, [0] * d, [0] * d, tab, 9, SymMatvec(sym), SymOuter(sym), prog=prog,
             carried=(None, None) if carried else None, children=False)
    return sym


def schedule_len(d, prog=None, carried=False):
    """Entries of the deployed step's public transcript (checked against replay by the vector script)."""
    pg = prog or Prog()
    inputs = (0 if carried else 2 * d * d) + 2 * d
    he_mv = 3 * (d + 2 * d + 1)
    he_ou = 2 * (1 + 2 + 1)

    def trunc(s):
        # c opening + (s - 1) borrow products and (s - 1) prefix products: 2 openings each
        return 1 + 2 * (2 * (s - 1))
    tr = d * (2 * trunc(pg.s1) + trunc(pg.s2) + trunc(pg.s3))
    look = d
    bg = 2 * d
    return inputs + he_mv + he_ou + tr + look + bg
