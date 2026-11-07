"""A minimal SPDZ-style engine: authenticated additive shares over F_p, dishonest majority, with abort.

2026-11-06. Written for the d = 64 dark training step (both forks use it: the MPC fork for the whole step,
the FHE fork for its crossings). It is a COUNTING and CHECKING implementation, not a deployable one:

* Preprocessing is an ideal dealer (F_prep). Its outputs to each party are committed (a hash per party)
  so an auditor can check an opened view against them. Every preprocessed element is counted.
* Parties are simulated in one process, but every party-local computation is a deterministic function of
  (that party's input shares, its preprocessing, the public transcript of openings). The SAME code re-runs
  for any subset of parties in audit mode, reading opened values from the transcript instead of
  reconstructing them: that is the MPC-in-the-head audit over the real MPC's views.
* Openings are broadcasts: each party sends its share to the n-1 others (n(n-1) wire elements).
* MACs: x is held as shares x_i and MAC shares m_i with sum m_i = alpha * x, alpha = sum alpha_i. The MAC
  check is batched with public random coefficients; it is run online at the end of the step (every step:
  an envelope, not a sample).

Exact deterministic semantics: truncation is floor division (bit-decomposed comparison of the low bits,
statistical masking of the high part with KAPPA = 40 bits), table lookups are exact polynomial
evaluation at a uniformly masked point.
"""
import hashlib
import random

KAPPA = 40

def h(*parts):
    m = hashlib.sha256()
    for p in parts:
        m.update(repr(p).encode())
    return m.hexdigest()

class Abort(Exception):
    pass

class Dealer:
    """Ideal preprocessing. Hands party i its shares; records per-party streams for the commitment."""
    def __init__(self, p, n, seed):
        self.p, self.n = p, n
        self.rng = random.Random(seed)
        self.alpha_sh = [self.rng.randrange(p) for _ in range(n)]
        self.alpha = sum(self.alpha_sh) % p
        self.streams = [[] for _ in range(n)]
        self.count = 0

    def _share(self, v):
        p, n = self.p, self.n
        xs = [self.rng.randrange(p) for _ in range(n - 1)]
        xs.append((v - sum(xs)) % p)
        ms = [self.rng.randrange(p) for _ in range(n - 1)]
        ms.append((self.alpha * v - sum(ms)) % p)
        return list(zip(xs, ms))

    def auth(self, v, tag):
        sh = self._share(v % self.p)
        for i in range(self.n):
            self.streams[i].append((tag, sh[i]))
        self.count += 1
        return sh

    def commitments(self):
        return [h(s) for s in self.streams]

class Party:
    def __init__(self, i, alpha_i):
        self.i, self.alpha_i = i, alpha_i

class Engine:
    """Shared values are dicts {party_index: (share, mac_share)} over the ACTIVE party set."""
    def __init__(self, p, n, dealer, active=None, transcript=None, cheat=None):
        self.p, self.n = p, n
        self.dealer = dealer
        self.active = list(range(n)) if active is None else list(active)
        self.audit = transcript is not None
        self.transcript = transcript if transcript is not None else []
        self.tpos = 0
        self.open_log = []           # (mac shares per party, opened value) for the MAC check
        self.wire = {}
        self.cheat = cheat or {}     # {"party": i, "at_open": transcript position, "delta": v}: a deviating party
        self.nopen = 0
        self.prep_stream_pos = {i: 0 for i in range(n)}

    # -------------------------------------------------- preprocessing access (audit reads the stream)
    def prep(self, tag, value_fn):
        """Get one authenticated preprocessed value. In live mode the dealer samples it; in audit mode
        each active party's share is read back from its committed stream, checking the tag."""
        if not self.audit:
            sh = self.dealer.auth(value_fn(), tag)
            return {i: sh[i] for i in self.active}
        out = {}
        for i in self.active:
            t, s = self.dealer.streams[i][self.prep_stream_pos[i]]
            if t != tag:
                raise Abort(f"audit: preprocessing tag mismatch for party {i}")
            self.prep_stream_pos[i] += 1
            out[i] = s
        return out

    def count(self, phase, k):
        self.wire[phase] = self.wire.get(phase, 0) + k

    # -------------------------------------------------- linear ops (local)
    def add(self, x, y):
        p = self.p
        return {i: ((x[i][0] + y[i][0]) % p, (x[i][1] + y[i][1]) % p) for i in self.active}

    def sub(self, x, y):
        p = self.p
        return {i: ((x[i][0] - y[i][0]) % p, (x[i][1] - y[i][1]) % p) for i in self.active}

    def cmul(self, c, x):
        p = self.p
        return {i: (c * x[i][0] % p, c * x[i][1] % p) for i in self.active}

    def cadd(self, c, x):
        """x + public c: party 0 adds c to its share; every party adds alpha_i c to its MAC share."""
        p = self.p
        return {i: (((x[i][0] + c) if i == 0 else x[i][0]) % p,
                    (x[i][1] + self.alpha_sh(i) * c) % p) for i in self.active}

    def alpha_sh(self, i):
        return self.dealer.alpha_sh[i]

    def lin(self, terms, const=0):
        """sum c_k x_k + const."""
        p = self.p
        out = {i: (0, 0) for i in self.active}
        for c, x in terms:
            if c % p == 0:
                continue
            out = {i: ((out[i][0] + c * x[i][0]) % p, (out[i][1] + c * x[i][1]) % p) for i in self.active}
        return self.cadd(const, out) if const else out

    # -------------------------------------------------- opening
    def open(self, x, phase="open"):
        """Broadcast shares. Live: reconstruct and append to the public transcript (all n shares are
        public broadcasts). Audit: the opened value and every party's broadcast share come from the
        transcript; the active parties' re-executed shares must EQUAL what they broadcast."""
        p = self.p
        k = self.nopen
        self.nopen += 1
        if not self.audit:
            shares = {i: x[i][0] for i in self.active}
            if self.cheat.get("at_open") == len(self.transcript):     # transcript position (inputs included)
                j = self.cheat["party"]
                shares[j] = (shares[j] + self.cheat["delta"]) % p
            v = sum(shares.values()) % p
            self.transcript.append((phase, dict(shares), v))
            self.count(phase, self.n * (self.n - 1))
        else:
            ph, bshares, v = self.transcript[self.tpos]
            self.tpos += 1
            for i in self.active:
                if bshares[i] != x[i][0]:
                    raise Abort(f"audit: party {i} broadcast at opening {k} differs from its re-executed share")
        self.open_log.append(({i: x[i][1] for i in self.active}, v))
        return v

    def open_vec(self, xs, phase="open"):
        return [self.open(x, phase) for x in xs]

    def mac_check(self, coin_seed, commit_sigma=True):
        """Batched MAC check: sigma_i = sum_k rho_k (m_{i,k} - alpha_i v_k); sum sigma_i must be 0.
        Coins come AFTER every broadcast is fixed: the seed hashes the label and the whole frozen transcript.
        With a caller-chosen seed alone the coins are predictable, and one party can shift two openings by
        (rho_1, -rho_0) so that its MAC errors cancel (Astra scholar, rederivation.md).
        Then every party COMMITS to sigma_i (hash with a fresh nonce) before any sigma is opened, and each
        opening must match its commitment. Without the commitment a rushing party that shifted an opening
        waits for the others' sigma_i and opens -sum of them, so the sum is 0 without knowing alpha
        (mac_timing_falsifier.py; commit_sigma=False keeps that legacy behaviour for the falsifier only).
        Wire: commitments n (n-1) (a hash counted as one element) + openings n (n-1) = 2 n (n-1)."""
        import secrets
        p = self.p
        rng = random.Random(h("mac-coins", coin_seed, self.open_log and [v for _, v in self.open_log],
                              [t for t in self.transcript]))
        rho = [rng.randrange(p) for _ in self.open_log]
        sig = {i: 0 for i in self.active}
        for r, (macs, v) in zip(rho, self.open_log):
            for i in self.active:
                sig[i] = (sig[i] + r * (macs[i] - self.alpha_sh(i) * v)) % p
        nonce = {i: secrets.token_hex(16) for i in self.active}
        com = {i: h("sigma", i, sig[i], nonce[i]) for i in self.active} if commit_sigma else None
        opened = dict(sig)
        rush = self.cheat.get("rush_sigma")
        if rush is not None and not self.audit:
            # the rushing party sees every other sigma first and opens the value that makes the sum vanish
            opened[rush] = (-sum(v for i, v in sig.items() if i != rush)) % p
        if commit_sigma:
            for i in self.active:
                if h("sigma", i, opened[i], nonce[i]) != com[i]:
                    raise Abort(f"MAC check: party {i}'s opened sigma does not match its commitment")
        self.count("mac_check", 2 * self.n * (self.n - 1))
        if not self.audit and sum(opened.values()) % p != 0:
            raise Abort("MAC check failed: an opened value is not the authenticated one")
        return sig

    # -------------------------------------------------- input
    def input(self, values, owner_rng, phase="input"):
        """Data owner inputs: dealer gives [r] (owner learns r), owner broadcasts c = v - r."""
        out = []
        for v in values:
            rv = owner_rng.randrange(self.p) if not self.audit else 0
            r = self.prep("in", lambda rv=rv: rv)
            if not self.audit:
                c = (v - rv) % self.p
                self.transcript.append((phase, {}, c))
                self.count(phase, self.n)
            else:
                ph, _, c = self.transcript[self.tpos]
                self.tpos += 1
            out.append(self.cadd(c, r))
        return out

    # -------------------------------------------------- multiplication
    def mul(self, x, y):
        if not self.audit:
            av, bv = self.dealer.rng.randrange(self.p), self.dealer.rng.randrange(self.p)
        else:
            av = bv = 0
        a = self.prep("ta", lambda: av)
        b = self.prep("tb", lambda: bv)
        c = self.prep("tc", lambda: av * bv)
        e = self.open(self.sub(x, a), "mul")
        f = self.open(self.sub(y, b), "mul")
        return self.lin([(1, c), (e, b), (f, a)], e * f % self.p)

    def auth_plain(self, plain, phase="auth"):
        """Authenticate unauthenticated additive shares {i: m_i} (e.g. from encryption-to-shares):
        dealer gives [r]; each party broadcasts m_i - r_i; [m] = [r] + (m - r). Audit mode checks the
        active parties' broadcasts against their re-executed m_i."""
        rv = self.dealer.rng.randrange(self.p) if not self.audit else 0
        r = self.prep("ar", lambda: rv)
        p = self.p
        if not self.audit:
            bs = {i: (plain[i] - r[i][0]) % p for i in self.active}
            v = sum(bs.values()) % p
            self.transcript.append((phase, bs, v))
            self.count(phase, self.n * (self.n - 1))
        else:
            ph, bs, v = self.transcript[self.tpos]
            self.tpos += 1
            for i in self.active:
                if bs[i] != (plain[i] - r[i][0]) % p:
                    raise Abort(f"audit: party {i} authenticated a share it did not hold")
        self.nopen += 1
        return self.cadd(v, r)

    def matvec(self, W, v, transpose=False):
        """[W] [v] with a matrix triple ([A], [b], [A b]): open W - A (d^2) and v - b (d)."""
        d = len(W)
        Av = [[self.dealer.rng.randrange(self.p) if not self.audit else 0 for _ in range(d)] for _ in range(d)]
        bv = [self.dealer.rng.randrange(self.p) if not self.audit else 0 for _ in range(d)]
        A = [[self.prep("mA", lambda i=i, j=j: Av[i][j]) for j in range(d)] for i in range(d)]
        b = [self.prep("mb", lambda j=j: bv[j]) for j in range(d)]
        def AB(i):
            if transpose:
                return sum(Av[r][i] * bv[r] for r in range(d))
            return sum(Av[i][r] * bv[r] for r in range(d))
        C = [self.prep("mC", lambda i=i: AB(i)) for i in range(d)]
        E = [[self.open(self.sub(W[i][j], A[i][j]), "matvec") for j in range(d)] for i in range(d)]
        f = [self.open(self.sub(v[j], b[j]), "matvec") for j in range(d)]
        out = []
        for i in range(d):
            if transpose:   # (W^T v)_i = sum_r W[r][i] v[r]
                terms = [(1, C[i])] + [(E[r][i], b[r]) for r in range(d)] + [(f[r], A[r][i]) for r in range(d)]
                const = sum(E[r][i] * f[r] for r in range(d))
            else:
                terms = [(1, C[i])] + [(E[i][r], b[r]) for r in range(d)] + [(f[r], A[i][r]) for r in range(d)]
                const = sum(E[i][r] * f[r] for r in range(d))
            out.append(self.lin(terms, const % self.p))
        return out

    def outer(self, a, x):
        """[a] (x) [x] with an outer triple ([u], [w], [u w^T]): open a - u and x - w (2d openings)."""
        d1, d2 = len(a), len(x)
        uv = [self.dealer.rng.randrange(self.p) if not self.audit else 0 for _ in range(d1)]
        wv = [self.dealer.rng.randrange(self.p) if not self.audit else 0 for _ in range(d2)]
        U = [self.prep("ou", lambda i=i: uv[i]) for i in range(d1)]
        Wm = [self.prep("ow", lambda j=j: wv[j]) for j in range(d2)]
        UW = [[self.prep("ouw", lambda i=i, j=j: uv[i] * wv[j]) for j in range(d2)] for i in range(d1)]
        e = [self.open(self.sub(a[i], U[i]), "outer") for i in range(d1)]
        f = [self.open(self.sub(x[j], Wm[j]), "outer") for j in range(d2)]
        return [[self.lin([(1, UW[i][j]), (e[i], Wm[j]), (f[j], U[i])], e[i] * f[j] % self.p)
                 for j in range(d2)] for i in range(d1)]

    # -------------------------------------------------- truncation: exact floor(x / 2^s), |x| < 2^K
    xt = False    # exact truncation (program flag "XT"; notes/dark-learning-gen6/xtrunc.md)

    def trunc(self, x, s, K):
        """Statistical (default): r uniform in [0, 2^(K+KAPPA)), so c = x + 2^K + r < p never wraps. XT: r uniform in
        [0, p), so c is uniform in F_p for every x (perfect), and an opening c < 2^(K+1) (a wrap is possible only there:
        a wrap gives c = x + 2^K + r - p < x + 2^K) aborts the step, which is redone with fresh preprocessing. Outside
        that zone c = x + 2^K + r over the integers, so the same formula is exact. Test hooks (live, XT): cheat
        {"xt_wrap": k} deals the k-th truncation the mask p - (x + 2^K), a wrap landing at c = 0; {"xt_ignore": True}
        continues past the zone (a deviating custodian set, for the proof's refusal rows)."""
        p = self.p
        k_tr = getattr(self, "n_trunc", 0)
        self.n_trunc = k_tr + 1
        if self.audit:
            rv = 0
        elif self.xt:
            rv = self.dealer.rng.randrange(p)
            if self.cheat.get("xt_wrap") == k_tr:
                xv = sum(x[i][0] for i in self.active) % p
                rv = (p - (xv + (1 << K))) % p
        else:
            rv = self.dealer.rng.randrange(1 << (K + KAPPA))
        r = self.prep("tr", lambda: rv)
        rbits = [self.prep("trb", lambda i=i: (rv >> i) & 1) for i in range(s)]
        rhi = self.prep("trh", lambda: rv >> s)
        c = self.open(self.add(self.cadd(1 << K, x), r), "trunc")     # c = x + 2^K + r < 2^{K+KAPPA+1} < p
        if self.xt and not self.audit and c < 1 << (K + 1) and not self.cheat.get("xt_ignore"):
            raise Abort("XT: truncation opening in the wrap zone (c < 2^(K+1); reveals nothing); redo the step")
        clow = c & ((1 << s) - 1)
        a = [(clow >> i) & 1 for i in range(s)]
        # borrow = [clow < rlow] = sum_i r_i (1 - a_i) prod_{j > i} (1 - (a_j xor r_j))
        eq = [self.lin([(1 - 2 * a[j], rbits[j])], a[j]) for j in range(s)]    # a xor r = a + r - 2 a r
        eq = [self.lin([(-1, e)], 1) for e in eq]                               # 1 - xor
        borrow = None
        prefix = None
        for i in reversed(range(s)):
            term = self.cmul(1 - a[i], rbits[i])
            if prefix is not None:
                term = self.mul(term, prefix)
            borrow = term if borrow is None else self.add(borrow, term)
            prefix = eq[i] if prefix is None else self.mul(prefix, eq[i])
        q = (c >> s) - (1 << (K - s))
        flip_sk = self.cheat.get("borrow_flip_sk")
        if flip_sk == (s, K) and not self.audit:
            self.cheat = dict(self.cheat, borrow_flip=k_tr, borrow_flip_sk=None)   # the first truncation of that class
        if self.cheat.get("borrow_flip") == k_tr and not self.audit:
            # TEST: a colluding custodian set outputs q - rhi - (1 - borrow), MAC-consistently (a wrong low-bit comparison)
            return self.lin([(-1, rhi), (1, borrow)], (q - 1) % p)
        return self.lin([(-1, rhi), (-1, borrow)], q % p)

    # -------------------------------------------------- exact table lookup at a masked point
    def lookup2(self, u, offset, tables_coeffs, deg):
        """u + offset in [0, deg]. Tables given as polynomial coefficient lists over F_p (interpolated
        once). Preprocessing [r^j], j = 1..deg; open c = (u + offset) - r; P(c + r) = sum_j tay_j(c) r^j."""
        p = self.p
        rv = self.dealer.rng.randrange(p) if not self.audit else 0
        pw = [self.prep("lp", lambda j=j: pow(rv, j, p)) for j in range(1, deg + 1)]
        c = self.open(self.sub(self.cadd(offset, u), pw[0]), "lookup")
        outs = []
        for coeffs in tables_coeffs:
            tay = taylor_shift(coeffs, c, p)
            outs.append(self.lin([(tay[j], pw[j - 1]) for j in range(1, len(tay))], tay[0]))
        return outs

def taylor_shift(coeffs, c, p):
    """Coefficients of P(X + c) for P = sum coeffs[k] X^k, mod p (Horner-style synthetic division)."""
    a = list(coeffs)
    n = len(a)
    for i in range(n):
        for k in range(n - 2, i - 1, -1):
            a[k] = (a[k] + c * a[k + 1]) % p
    return a

def interpolate(values, p):
    """Coefficients of the unique degree < n polynomial with P(k) = values[k], k = 0..n-1, mod p. O(n^2)."""
    n = len(values)
    M = [1]
    for j in range(n):                      # M(X) = prod (X - j)
        M = [(a - j * b) % p for a, b in zip([0] + M, M + [0])]
    coeffs = [0] * n
    for k in range(n):
        # Q_k = M / (X - k) by synthetic division; L_k = Q_k / Q_k(k)
        q = [0] * n
        acc = 0
        for i in range(n, 0, -1):
            acc = (M[i] + acc * k) % p if i == n else (M[i] + acc * k) % p
            q[i - 1] = acc
        qk = 0
        for c in reversed(q):
            qk = (qk * k + c) % p
        scale = values[k] * pow(qk, -1, p) % p
        for i in range(n):
            coeffs[i] = (coeffs[i] + scale * q[i]) % p
    return coeffs
