"""Batched zero-knowledge proof of plaintext knowledge for BFV ciphertexts: a hash-based Ligero argument over a
255-bit prime field (dark learning gen 4; notes/dark-learning-gen4/GROUNDING.md says why not a lattice proof).

2026-11-06. One proof per (sender, HE call) covers every ciphertext the sender sends in that call, and binds them
to the sender's REGISTERED key.

Relation, secret-key batch (the MPC fork's HE helpers). Public: registry (N, primes q_0..q_{L-1}, t, seed, b) with
a = public_a(seed) (Astra scholar, unchanged); ciphertexts (c0_j, c1_j) in R_Q; per ciphertext a public slot set S_j
(the layout: the plaintext may be nonzero only there); the context. Private: s in {-1,0,1}^N, e_pk in [-8,8]^N, and
per ciphertext e_j in [-8,8]^N and r_j in [-(t-1)/2,(t-1)/2]^{S_j}, such that for every prime q_i and
coefficient k
    b + a s + e_pk                    = 0                 (mod q_i)     the registered key
    t (c0_j + c1_j s + e_j) - r_j     = 0                 (mod q_i)     r_j = 0 off the slots
These say: c0_j + c1_j s = round(Q m_j / t) - e_j (mod Q) with m_j = -r_j Q^-1 mod t (exact scaling: Q is invertible
mod t, so t | Q m_j + r_j, u_j = (Q m_j + r_j)/t = round(Q m_j / t) since |r_j| <= (t-1)/2, and t u_j = r_j =
t (phase + e_j) mod Q), |e_j| <= 8, m_j zero off the layout, and the same integer s in every limb and in the key.
(The scholar's form also committed m_j and a mod-t equation; both are implied, and gen 4 dropped them.)

Public-key batch (FHE (b)'s mask ciphertexts, under the joint key (b, a)): per ciphertext u in {-1,0,1}^N,
e0, e1 in [-8,8]^N, r at the slots, with t (c0 - b u - e0) - r = 0 and c1 - a u - e1 = 0 (mod q_i). It bounds the
encryption randomness; the phase bound is the scholar's public-key envelope.

Proof. Every private integer is a sum of binary digits (top digit of adjusted weight, so [lo, hi] is covered
exactly). The digits are rows of one interleaved Reed-Solomon code over F_P; the Ligero tests (proximity, linear,
quadratic b^2 = b) run on them. Cross-limb: after the digits are committed, Fiat-Shamir draws, for each of F folds
and each prime q_i, weights rho in [0, q_i) for every coefficient equation; the prover then commits integer
quotients with sum rho * LHS_i = q_i K_{f,i} over Z, with |LHS - q K| <= 2B + q < P checked (a statement
that does not fit is refused), K range-proved. A coefficient equation that fails mod q_i survives one fold with probability
1/q_i < 2^-60 and F folds with 2^-60F; F = folds_for(T) keeps pace with the column test (3 at T = 309, 1 at 97),
because a prover can regrind root 1 against the fold as against the columns. Order: statement -> digit rows and all masks (root 1) -> rho -> quotient rows
(root 2) -> gamma, lambda, gamma' -> messages w, q, p -> T distinct columns. Every challenge follows the
commitments it must follow; `legacy=True` reproduces the hole (challenges from the statement only) for the
falsifier and is never used by a recipient.

Soundness, stated plainly [INFERRED, standard Ligero analysis as used in cozk.py]: column test about
(1 - delta)^T with delta = (1 - rate)/3 >= 1/4 here: the default T = 309 gives <= 2^-128.25 (the ledger
profile); T = 97 gives 2^-40.26, statistical only (demo profile; Fiat-Shamir grinding of 2^g tries gives 2^(g-40)). Fold: 2^-60 per fold. Field terms: rows/P, < 2^-200.
Zero knowledge [INFERRED]: each row has th >= T random coefficients times (X^k - 1), so T openings are uniform;
w, q, p are masked by fresh polynomials committed in root 1; leaves are salted. No QROM proof is claimed.
"""
import hashlib
import math
import secrets

import bfv_ref as bfv
from scholar_zkpopk import canonical, public_a

DOMAIN = b"dl-gen4-zkpopk-ligero-v1"
TWO_ADIC = 32
EB = 32                                     # bytes per field element / hash / salt on the wire
MIN_MODULUS = 1 << 60                       # and above 2^60: the fold's error is 1/q_i, and a prover can regrind root 1
                                            # (independent review, gen 4: a 17-bit limb let mixed limbs through in 28 tries)
MAX_MODULUS = 1 << 61                       # the profile: every ciphertext prime and t below 2^61 (Codex trace, gen 4:
                                            # a 256-bit prime with asserts stripped by -O let a false statement verify)


def _find_field(bits=255):
    c = ((1 << bits) - 1) >> TWO_ADIC
    while True:
        p = (c << TWO_ADIC) + 1
        if p.bit_length() == bits and bfv.is_probable_prime(p):
            return p
        c -= 1


P = _find_field()


def _root():
    for x in range(3, 10000):
        w = pow(x, (P - 1) >> TWO_ADIC, P)
        if pow(w, 1 << (TWO_ADIC - 1), P) != 1:
            return w


ROOT = _root()
SHIFT = next(x for x in range(3, 100) if pow(x, 1 << TWO_ADIC, P) != 1)   # coset off every 2-power subgroup


def root_of(n):
    assert n & (n - 1) == 0 and n <= 1 << TWO_ADIC
    return pow(ROOT, (1 << TWO_ADIC) // n, P)


_TW = {}


def ntt(a, w):
    """Evaluations a(w^i), i < len(a). Iterative radix 2."""
    a = list(a)
    n = len(a)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j |= bit
        if i < j:
            a[i], a[j] = a[j], a[i]
    m = 2
    while m <= n:
        key = (w, n, m)
        ws = _TW.get(key)
        if ws is None:
            wm = pow(w, n // m, P)
            ws = [1] * (m // 2)
            for i in range(1, m // 2):
                ws[i] = ws[i - 1] * wm % P
            _TW[key] = ws
        h = m // 2
        for s in range(0, n, m):
            lo = a[s:s + h]
            hi = [x * y % P for x, y in zip(a[s + h:s + m], ws)]
            a[s:s + h] = [(x + y) % P for x, y in zip(lo, hi)]
            a[s + h:s + m] = [(x - y) % P for x, y in zip(lo, hi)]
        m *= 2
    return a


def intt(v, w):
    n = len(v)
    inv = pow(n, P - 2, P)
    return [x * inv % P for x in ntt(v, pow(w, P - 2, P))]


def peval(c, x):
    acc = 0
    for a in reversed(c):
        acc = (acc * x + a) % P
    return acc


def batch_inv(xs):
    pre, acc = [], 1
    for x in xs:
        pre.append(acc)
        acc = acc * x % P
    inv = pow(acc, P - 2, P)
    out = [0] * len(xs)
    for i in range(len(xs) - 1, -1, -1):
        out[i] = pre[i] * inv % P
        inv = inv * xs[i] % P
    return out


class Code:
    """Messages of length k on the subgroup H = <w_k>; f = interp(msg) + (X^k - 1) * rand(X), deg rand < th;
    codewords on the coset D = SHIFT * <w_D>, |D| the least power of two >= 4 (k + th)."""

    def __init__(self, k, th):
        assert k & (k - 1) == 0 and th >= 1
        self.k, self.th = k, th
        self.nD = 1 << (4 * (k + th) - 1).bit_length()
        self.wk, self.wD = root_of(k), root_of(self.nD)
        self.lgD = self.nD.bit_length() - 1
        self.shpow = [1] * self.nD
        for i in range(1, self.nD):
            self.shpow[i] = self.shpow[i - 1] * SHIFT % P
        ishift = pow(SHIFT, P - 2, P)
        self.ishpow = [1] * self.nD
        for i in range(1, self.nD):
            self.ishpow[i] = self.ishpow[i - 1] * ishift % P
        self.pts = [SHIFT * x % P for x in self._powers(self.wD, self.nD)]

    @staticmethod
    def _powers(w, n):
        out = [1] * n
        for i in range(1, n):
            out[i] = out[i - 1] * w % P
        return out

    def rate(self):
        return (self.k + self.th) / self.nD

    def interp(self, msg):
        return intt(msg, self.wk)

    def evalD(self, coeffs):
        c = list(coeffs) + [0] * (self.nD - len(coeffs))
        return ntt([x * s % P for x, s in zip(c, self.shpow)], self.wD)

    def coeffsD(self, evals):
        return [x * s % P for x, s in zip(intt(evals, self.wD), self.ishpow)]

    def row_poly(self, msg, rng):
        c = self.interp(msg) + [0] * self.th
        for l in range(self.th):
            r = rng.randrange(P)
            c[l] = (c[l] - r) % P
            c[self.k + l] = (c[self.k + l] + r) % P
        return c


# ------------------------------------------------------------------------------------------- transcript
class Transcript:
    """SHA-256 state; challenges by SHAKE-256 expansion with rejection sampling. legacy=True drops every
    absorb of prover messages: the statement-only hole, reproduced for the falsifier."""

    def __init__(self, statement_digest, legacy=False):
        self.legacy = legacy
        self.state = hashlib.sha256(DOMAIN + b"|statement|" + statement_digest).digest()
        self.n = 0

    def absorb(self, label, data):
        if self.legacy:
            return
        self.state = hashlib.sha256(self.state + label.encode() + hashlib.sha256(data).digest()).digest()

    def ints(self, label, count, mod):
        nb = (mod.bit_length() + 7) // 8 + 8
        lim = (1 << (8 * nb)) // mod * mod
        out = []
        ctr = 0
        while len(out) < count:
            need = count - len(out)
            raw = hashlib.shake_256(self.state + label.encode() + ctr.to_bytes(8, "big")).digest(nb * need)
            ctr += 1
            for i in range(need):
                x = int.from_bytes(raw[i * nb:(i + 1) * nb], "big")
                if x < lim:
                    out.append(x % mod)
        self.n += 1
        self.state = hashlib.sha256(self.state + b"|drawn|" + label.encode()).digest()
        return out

    def distinct(self, label, T, n):
        out, seen, ctr = [], set(), 0
        while len(out) < T:
            for j in self.ints(f"{label}{ctr}", T, n):
                if j not in seen and len(out) < T:
                    seen.add(j)
                    out.append(j)
            ctr += 1
        return out


def H(*parts):
    h = hashlib.sha256()
    for x in parts:
        h.update(len(x).to_bytes(8, "big"))
        h.update(x)
    return h.digest()


def fe(x):
    return x.to_bytes(EB, "big")


# ------------------------------------------------------------------------------------------- statement
class KeyRegistry:
    """Pinned key record: a from the registry seed (scholar's public_a), b registered. For a secret-key batch
    the registry is the sender's own key; for a public-key batch it is the joint key."""

    def __init__(self, N, primes, t, seed, key_id, b):
        self.N, self.primes, self.t, self.seed, self.key_id = N, tuple(primes), t, seed, key_id
        self.Q = math.prod(self.primes)
        self.b = tuple(b)
        self.a = tuple(public_a(seed, N, self.Q))

    def valid(self):
        N, Q, t = self.N, self.Q, self.t
        return (N >= 2 and N & (N - 1) == 0 and len(self.primes) >= 1 and len(set(self.primes)) == len(self.primes)
                and all(type(q) is int and MIN_MODULUS < q < MAX_MODULUS and q % (2 * N) == 1 and bfv.is_probable_prime(q)
                        for q in self.primes)
                and type(t) is int and MIN_MODULUS < t < MAX_MODULUS and t % 2 == 1 and bfv.is_probable_prime(t)
                and t not in self.primes
                and self.Q > 17 * t        # decryption margin: |e| + 1/2 <= 8.5 < Q/(2t) (Codex review: one limb with
                                           # Q ~ t accepted a proof whose decryption left the layout)
                and len(self.b) == N and all(type(x) is int and 0 <= x < Q for x in self.b))

    def public(self):
        return canonical([self.N, list(self.primes), self.t, self.seed, self.key_id, list(self.b)])


def keygen(N, primes, t, seed, key_id="custodian", rng=None):
    rng = rng or secrets.SystemRandom()
    Q = math.prod(primes)
    s = [rng.choice((-1, 0, 1)) for _ in range(N)]
    e = [rng.randint(-8, 8) for _ in range(N)]
    a = public_a(seed, N, Q)
    as_, _ = bfv.negacyclic_mul(a, s)
    b = [(-x - y) % Q for x, y in zip(as_, e)]
    return KeyRegistry(N, primes, t, seed, key_id, b), s, e


def _round_scale(Q, t, m):
    u = (2 * Q * m + t) // (2 * t)
    return u, t * u - Q * m


def encrypt_sk(reg, s, m, slots, rng, e=None):
    """Secret-key BFV with exact scaling, the he_matvec layout: m nonzero only at `slots`. Returns (ct, witness)."""
    N, Q, t = reg.N, reg.Q, reg.t
    m = [x % t for x in m]
    assert all(m[k] == 0 for k in range(N) if k not in set(slots))
    a = [rng.randrange(Q) for _ in range(N)]
    e = e if e is not None else [rng.randint(-8, 8) for _ in range(N)]
    as_, _ = bfv.negacyclic_mul(a, s)
    us = [_round_scale(Q, t, x) for x in m]
    c0 = [(u - y - z) % Q for (u, _), y, z in zip(us, as_, e)]
    return (c0, a), dict(e=e, m=[m[k] for k in slots], r=[us[k][1] for k in slots])


def encrypt_pk(reg, m, slots, rng, e0=None):
    N, Q, t = reg.N, reg.Q, reg.t
    m = [x % t for x in m]
    assert all(m[k] == 0 for k in range(N) if k not in set(slots))
    u = [rng.choice((-1, 0, 1)) for _ in range(N)]
    e0 = e0 if e0 is not None else [rng.randint(-8, 8) for _ in range(N)]
    e1 = [rng.randint(-8, 8) for _ in range(N)]
    bu, _ = bfv.negacyclic_mul(list(reg.b), u)
    au, _ = bfv.negacyclic_mul(list(reg.a), u)
    us = [_round_scale(Q, t, x) for x in m]
    c0 = [(x + y + v) % Q for x, y, (v, _) in zip(bu, e0, us)]
    c1 = [(x + y) % Q for x, y in zip(au, e1)]
    return (c0, c1), dict(u=u, e0=e0, e1=e1, m=[m[k] for k in slots], r=[us[k][1] for k in slots])


class Statement:
    def __init__(self, reg, kind, cts, slots, context):
        if kind not in ("sk", "pk", "key"):
            raise ValueError("kind")
        self.reg, self.kind, self.context = reg, kind, context
        N, Q = reg.N, reg.Q
        self.cts = [tuple(tuple(c) for c in ct) for ct in cts]
        self.slots = [tuple(S) for S in slots]
        if (kind == "key") != (not self.cts) or len(self.slots) != len(self.cts):
            raise ValueError("batch shape")         # a key statement has no ciphertexts; a batch has at least one
        for (c0, c1), S in zip(self.cts, self.slots):
            if len(c0) != N or len(c1) != N:
                raise ValueError("ciphertext shape")
            if any(type(x) is not int or not 0 <= x < Q for x in c0 + c1):
                raise ValueError("noncanonical ciphertext")
            if list(S) != sorted(set(S)) or any(type(k) is not int or not 0 <= k < N for k in S):
                raise ValueError("slot layout")

    def digest(self):
        h = hashlib.sha256(DOMAIN)
        h.update(self.reg.public())
        h.update(canonical([self.kind, self.context, [list(S) for S in self.slots]]))
        wb = (self.reg.Q.bit_length() + 7) // 8
        for c0, c1 in self.cts:
            h.update(b"".join(x.to_bytes(wb, "big") for x in c0 + c1))
        return h.digest()


# ------------------------------------------------------------------------------------------- layout and bounds
def weights(U):
    w = U.bit_length()
    return [1 << j for j in range(w - 1)] + [U - (1 << (w - 1)) + 1]


def digits(z, U):
    ws = weights(U)
    assert 0 <= z <= U
    top = 0
    if len(ws) > 1 and z >= 1 << (len(ws) - 1):
        top, z = 1, z - ws[-1]
    elif len(ws) == 1:
        return [z]
    return [(z >> j) & 1 for j in range(len(ws) - 1)] + [top]


def folds_for(T):
    """Independent per-prime folds so that the fold keeps pace with the column test: each fold errs with 1/q_i < 2^-60,
    and a prover can regrind root 1, so the ledger profile (T = 309, 128 bits) needs 3 folds, the demo profile 1."""
    bits = T * math.log2(4 / 3)
    return max(1, math.ceil(bits / 60))


def quotient_bounds(st):
    """|F_i| <= B_i for any in-range witness and any rho; K in [-(B_i // q_i + 1), +]."""
    reg = st.reg
    N, t, M = reg.N, reg.t, len(st.cts)
    out = []
    for q in reg.primes:
        ring = (q - 1) * (N + 1) + 8
        ct0 = t * ring + (t - 1) // 2
        if st.kind in ("sk", "key"):
            B = (q - 1) * N * (ring + M * ct0)
        else:
            B = (q - 1) * N * M * (ct0 + ring)
        if not 2 * B + q < P:
            raise ValueError("field too small for this batch: the folded limb equation could wrap modulo P")
        out.append(B)
    return out


def layout(st, F=1):
    """Round-1 groups (name, length, lo, hi) in wire order, and round-2 (quotients, one per fold and prime).
    No plaintext digits: with Q invertible mod t, any r with |r| <= (t-1)/2 has the unique m = -r Q^-1 mod t, and
    t | Q m + r, so u = (Q m + r)/t = round(Q m / t) and t (phase + e) = r (mod Q) says phase + e = u (mod Q).
    (Gen 4 dropped the mod-t row and the m digits; the independent review showed them redundant.)"""
    reg = st.reg
    N, t = reg.N, reg.t
    E, R = (-8, 8), (-((t - 1) // 2), (t - 1) // 2)
    g1 = []
    if st.kind in ("sk", "key"):
        g1 += [("s", N, -1, 1), ("e_pk", N, -8, 8)]
        for j, S in enumerate(st.slots):
            g1 += [(f"e{j}", N) + E, (f"r{j}", len(S)) + R]
    else:
        for j, S in enumerate(st.slots):
            g1 += [(f"u{j}", N, -1, 1), (f"e0_{j}", N) + E, (f"e1_{j}", N) + E, (f"r{j}", len(S)) + R]
    Bs = quotient_bounds(st)
    g2 = [(f"K{f}_{i}", 1, -(B // q + 1), B // q + 1) for f in range(F) for i, (B, q) in enumerate(zip(Bs, reg.primes))]
    return g1, g2


def nbits(groups):
    return sum(n * len(weights(hi - lo)) for _, n, lo, hi in groups)


def adj(c):
    """c(X^-1) in Z[X]/(X^N+1): <rho, c*s> = <adj(c)*rho, s>."""
    return [c[0]] + [-x for x in reversed(c[1:])]


def draw_rho(tr, st, F=1):
    reg = st.reg
    N = reg.N
    rho = {}
    for f in range(F):
        for i, q in enumerate(reg.primes):
            if st.kind in ("sk", "key"):
                rho[(f, "key", i)] = tr.ints(f"rho-{f}-key-{i}", N, q)
                for j in range(len(st.cts)):
                    rho[(f, j, i)] = tr.ints(f"rho-{f}-ct-{j}-{i}", N, q)
            else:
                for j in range(len(st.cts)):
                    rho[(f, j, i, 0)] = tr.ints(f"rho-{f}-ct-{j}-{i}-0", N, q)
                    rho[(f, j, i, 1)] = tr.ints(f"rho-{f}-ct-{j}-{i}-1", N, q)
    return rho


def linear_system(st, rho, F=1):
    """One constraint per (fold, prime): coefficient vectors per group (exact integers), a constant, the modulus and
    the quotient's name, with sum_g <coef_g, value_g> + const - q K = 0 over Z for an honest witness."""
    reg = st.reg
    t = reg.t
    cons = []
    for f in range(F):
        for i, q in enumerate(reg.primes):
            co, const = {}, 0

            def addv(name, vec):
                co[name] = [x + y for x, y in zip(co[name], vec)] if name in co else list(vec)

            if st.kind in ("sk", "key"):
                rk = rho[(f, "key", i)]
                ai = [x % q for x in reg.a]
                sco, _ = bfv.negacyclic_mul(adj(ai), rk)
                const += sum(r * (x % q) for r, x in zip(rk, reg.b))
                addv("e_pk", rk)
                for j, ((c0, c1), S) in enumerate(zip(st.cts, st.slots)):
                    rc = rho[(f, j, i)]
                    p1, _ = bfv.negacyclic_mul(adj([x % q for x in c1]), rc)
                    sco = [x + t * y for x, y in zip(sco, p1)]
                    const += t * sum(r * (x % q) for r, x in zip(rc, c0))
                    addv(f"e{j}", [t * r for r in rc])
                    addv(f"r{j}", [-rc[k] for k in S])
                co["s"] = sco
            else:
                bi = adj([x % q for x in reg.b])
                ai = adj([x % q for x in reg.a])
                for j, ((c0, c1), S) in enumerate(zip(st.cts, st.slots)):
                    r0, r1 = rho[(f, j, i, 0)], rho[(f, j, i, 1)]
                    p0, _ = bfv.negacyclic_mul(bi, r0)
                    p1, _ = bfv.negacyclic_mul(ai, r1)
                    co[f"u{j}"] = [-t * x - y for x, y in zip(p0, p1)]
                    co[f"e0_{j}"] = [-t * r for r in r0]
                    co[f"e1_{j}"] = [-r for r in r1]
                    co[f"r{j}"] = [-r0[k] for k in S]
                    const += t * sum(r * (x % q) for r, x in zip(r0, c0)) + sum(r * (x % q) for r, x in zip(r1, c1))
            kn = f"K{f}_{i}"
            co[kn] = [-q]
            cons.append((co, const, q, kn))
    if len(cons) != F * len(reg.primes):
        raise ValueError("constraint count")
    return cons


def alpha_beta(groups, cons, lam):
    """alpha over the flat digit vector (rows 1 then rows 2) and beta with <alpha, digits> = beta."""
    alpha, beta = [], 0
    for c, (co, const, _, _) in zip(lam, cons):
        beta -= c * const
    for name, n, lo, hi in groups:
        ws = weights(hi - lo)
        comb = [0] * n
        for c, (co, _, _, _) in zip(lam, cons):
            if name in co:
                v = co[name]
                comb = [(x + c * y) % P for x, y in zip(comb, v)]
        beta -= lo * sum(comb)
        for x in comb:
            alpha.extend(x * w % P for w in ws)
    return alpha, beta % P


def values_to_digits(groups, vals, raw=False):
    """raw=True (forgers only): an out-of-range value is packed into its first digit as a field element."""
    out = []
    for name, n, lo, hi in groups:
        v = vals[name]
        if len(v) != n:
            raise ValueError(f"{name}: length")
        for x in v:
            if type(x) is not int or not lo <= x <= hi:
                if not raw:
                    raise ValueError(f"{name} outside its exact range")
                out.extend([(x - lo) % P] + [0] * (len(weights(hi - lo)) - 1))
                continue
            out.extend(digits(x - lo, hi - lo))
    return out


# ------------------------------------------------------------------------------------------- parameters
def proof_bytes(k, th, T, m1, m2):
    lgD = ((1 << (4 * (k + th) - 1).bit_length())).bit_length() - 1
    msgs = (k + th) + (2 * k + th - 1) + (2 * k + 2 * th - 1)
    per_col = (m1 + 3) + 1 + lgD + m2 + 1 + lgD
    return EB * (2 + msgs + T * per_col)


def shape(st, T=309, th=None):
    th = th or T
    F = folds_for(T)
    g1, g2 = layout(st, F)
    n1, n2 = nbits(g1), nbits(g2)
    best = None
    for lk in range(4, 20):
        k = 1 << lk
        m1, m2 = -(-n1 // k), -(-n2 // k)
        b = proof_bytes(k, th, T, m1, m2)
        if best is None or b < best[0]:
            best = (b, k, m1, m2)
    _, k, m1, m2 = best
    return dict(k=k, th=th, T=T, F=F, m1=m1, m2=m2, n1=n1, n2=n2, g1=g1, g2=g2)


# ------------------------------------------------------------------------------------------- Merkle
def merkle(cols_bytes, salts):
    lvl = [H(b"leaf", s, c) for s, c in zip(salts, cols_bytes)]
    tree = [lvl]
    while len(lvl) > 1:
        lvl = [H(lvl[i], lvl[i + 1]) for i in range(0, len(lvl), 2)]
        tree.append(lvl)
    return tree


def mpath(tree, j):
    out = []
    for lvl in tree[:-1]:
        out.append(lvl[j ^ 1])
        j //= 2
    return out


def mverify(root, colb, salt, j, path):
    h = H(b"leaf", salt, colb)
    for sib in path:
        h = H(h, sib) if j % 2 == 0 else H(sib, h)
        j //= 2
    return h == root


def colbytes(rows, j):
    return b"".join(fe(r[j]) for r in rows)


# ------------------------------------------------------------------------------------------- prover
def _rows(bits, k, m):
    bits = bits + [0] * (m * k - len(bits))
    return [bits[r * k:(r + 1) * k] for r in range(m)]


def prove(st, wit, context_check=None, T=309, rng=None, legacy=False, cheat=None):
    """wit: sk: dict(s, e_pk, cts=[dict(e, m, r)]) ; pk: dict(cts=[dict(u, e0, e1, m, r)]).
    cheat (falsifiers only): dict(digits1=..., K=...) overrides, skipping the prover's own checks."""
    rng = secrets.SystemRandom()          # hiding randomness, masks and salts: never the caller's (seedable) rng
    sh = shape(st, T)
    k, th, m1, m2 = sh["k"], sh["th"], sh["m1"], sh["m2"]
    code = Code(k, th)
    nD = code.nD
    vals = {}
    if st.kind in ("sk", "key"):
        vals["s"], vals["e_pk"] = wit["s"], wit["e_pk"]
        for j, w in enumerate(wit.get("cts", [])):
            vals[f"e{j}"], vals[f"r{j}"] = w["e"], w["r"]
    else:
        for j, w in enumerate(wit["cts"]):
            vals[f"u{j}"], vals[f"e0_{j}"], vals[f"e1_{j}"] = w["u"], w["e0"], w["e1"]
            vals[f"r{j}"] = w["r"]
    if cheat and "values1" in cheat:
        vals.update(cheat["values1"])
    d1 = (cheat or {}).get("digits1") or values_to_digits(sh["g1"], vals, raw=bool(cheat and cheat.get("raw")))
    tr = Transcript(st.digest(), legacy)
    # round 1: digit rows and every mask
    R1 = _rows(d1, k, m1)
    P1 = [code.row_poly(r, rng) for r in R1]
    mp = [rng.randrange(P) for _ in range(k + th)]
    ml = [rng.randrange(P) for _ in range(2 * k + th - 1)]
    ml[0] = (ml[0] - sum(ml[0::k])) % P                     # sum over H of ml = k * sum_{j = 0 mod k} ml_j = 0
    g = [rng.randrange(P) for _ in range(k + 2 * th - 1)]
    mq = [0] * (2 * k + 2 * th - 1)
    for i, x in enumerate(g):
        mq[i] = (mq[i] - x) % P
        mq[i + k] = (mq[i + k] + x) % P
    E1 = [code.evalD(c) for c in P1] + [code.evalD(mp), code.evalD(ml), code.evalD(mq)]
    salts1 = [secrets.token_bytes(32) for _ in range(nD)]
    T1 = merkle([colbytes(E1, j) for j in range(nD)], salts1)
    tr.absorb("root1", T1[-1][0])
    rho = draw_rho(tr, st, sh["F"])
    cons = linear_system(st, rho, sh["F"])
    # round 2: quotients
    Ks = {}
    for co, const, mod, kn in cons:
        tot = const + sum(sum(a * b for a, b in zip(co[nm], vals[nm])) for nm in co if not nm.startswith("K"))
        if tot % mod and not cheat:
            raise ValueError(f"witness does not satisfy constraint {kn}")
        Ks[kn] = [tot // mod]
    if cheat and "K" in cheat:
        Ks.update(cheat["K"])
    d2 = (cheat or {}).get("digits2") or values_to_digits(sh["g2"], Ks, raw=bool(cheat and cheat.get("raw")))
    R2 = _rows(d2, k, m2)
    P2 = [code.row_poly(r, rng) for r in R2]
    E2 = [code.evalD(c) for c in P2]
    salts2 = [secrets.token_bytes(32) for _ in range(nD)]
    T2 = merkle([colbytes(E2, j) for j in range(nD)], salts2)
    tr.absorb("root2", T2[-1][0])
    mrows = m1 + m2
    gam = tr.ints("gamma", mrows, P)
    lam = tr.ints("lambda", len(cons), P)
    gq = tr.ints("gamma-q", mrows, P)
    alpha, beta = alpha_beta(sh["g1"] + sh["g2"], cons, lam)
    alpha += [0] * (mrows * k - len(alpha))
    # alpha's first n1 entries index round-1 digits; round 2 starts at row m1
    a1 = alpha[:sh["n1"]] + [0] * (m1 * k - sh["n1"])
    a2 = alpha[sh["n1"]:sh["n1"] + sh["n2"]] + [0] * (m2 * k - sh["n2"])
    arows = _rows(a1, k, m1) + _rows(a2, k, m2)
    E = E1[:m1] + E2
    Mp, Ml, Mq = E1[m1], E1[m1 + 1], E1[m1 + 2]
    wD, qD, pD = list(Mp), list(Ml), list(Mq)
    for r in range(mrows):
        Er = E[r]
        RD = code.evalD(code.interp(arows[r]))
        gr, gqr = gam[r], gq[r]
        wD = [(x + gr * y) % P for x, y in zip(wD, Er)]
        qD = [(x + a * y) % P for x, a, y in zip(qD, RD, Er)]
        pD = [(x + gqr * (y * y - y)) % P for x, y in zip(pD, Er)]
    w, q, p = code.coeffsD(wD), code.coeffsD(qD), code.coeffsD(pD)
    if not cheat:
        assert not any(w[k + th:]) and not any(q[2 * k + th - 1:]) and not any(p[2 * k + 2 * th - 1:])
    w, q, p = w[:k + th], q[:2 * k + th - 1], p[:2 * k + 2 * th - 1]
    msg = b"".join(fe(x) for x in w + q + p)
    tr.absorb("msgs", msg)
    J = tr.distinct("cols", T, nD)
    out = bytearray(T1[-1][0] + T2[-1][0] + msg)
    for j in J:
        out += colbytes(E1, j) + salts1[j] + b"".join(mpath(T1, j))
        out += colbytes(E2, j) + salts2[j] + b"".join(mpath(T2, j))
    blob = bytes(out)
    assert len(blob) == proof_bytes(k, th, T, m1, m2)
    return blob


# ------------------------------------------------------------------------------------------- verifier
def verify(st, blob, T=309, legacy=False):
    """Untrusted bytes against a statement the recipient built from its OWN expected context and the pinned
    registry. Returns (ok, reason)."""
    try:
        reg = st.reg
        if not reg.valid():
            return False, "key registry invalid"
        if list(reg.a) != public_a(reg.seed, reg.N, reg.Q):
            return False, "key registry: a is not the pinned seed's"
        sh = shape(st, T)
        k, th, m1, m2 = sh["k"], sh["th"], sh["m1"], sh["m2"]
        if type(blob) is not bytes or len(blob) != proof_bytes(k, th, T, m1, m2):
            return False, "proof length"
        code = Code(k, th)
        nD, lgD = code.nD, code.lgD
        at = 0

        def take(n):
            nonlocal at
            x = blob[at:at + n]
            at += n
            return x

        def elems(n):
            out = []
            for _ in range(n):
                x = int.from_bytes(take(EB), "big")
                if x >= P:
                    raise ValueError("noncanonical field element")
                out.append(x)
            return out

        root1, root2 = take(32), take(32)
        mstart = at
        w = elems(k + th)
        q = elems(2 * k + th - 1)
        p = elems(2 * k + 2 * th - 1)
        msg = blob[mstart:at]
        tr = Transcript(st.digest(), legacy)
        tr.absorb("root1", root1)
        rho = draw_rho(tr, st, sh["F"])
        cons = linear_system(st, rho, sh["F"])
        tr.absorb("root2", root2)
        mrows = m1 + m2
        gam = tr.ints("gamma", mrows, P)
        lam = tr.ints("lambda", len(cons), P)
        gq = tr.ints("gamma-q", mrows, P)
        tr.absorb("msgs", msg)
        J = tr.distinct("cols", T, nD)
        alpha, beta = alpha_beta(sh["g1"] + sh["g2"], cons, lam)
        a1 = alpha[:sh["n1"]] + [0] * (m1 * k - sh["n1"])
        a2 = alpha[sh["n1"]:] + [0] * (m2 * k - sh["n2"])
        arows = _rows(a1, k, m1) + _rows(a2, k, m2)
        # linear: sum over H of q = beta; quadratic: (X^k - 1) | p
        if k * sum(q[0::k]) % P != beta:
            return False, "linear test: the folded limb equations do not hold"
        fold = [0] * k
        for i, x in enumerate(p):
            fold[i % k] = (fold[i % k] + x) % P
        if any(fold):
            return False, "quadratic test: a committed digit is not binary"
        Hk = Code._powers(code.wk, k)
        kinv = pow(k, P - 2, P)
        cols = []
        for j in J:
            c1 = elems(m1 + 3)
            s1 = take(32)
            p1 = [take(32) for _ in range(lgD)]
            c2 = elems(m2)
            s2 = take(32)
            p2 = [take(32) for _ in range(lgD)]
            if not mverify(root1, b"".join(fe(x) for x in c1), s1, j, p1):
                return False, "Merkle path (root 1)"
            if not mverify(root2, b"".join(fe(x) for x in c2), s2, j, p2):
                return False, "Merkle path (root 2)"
            cols.append((j, c1, c2))
        if at != len(blob):
            return False, "proof length"
        for j, c1, c2 in cols:
            x = code.pts[j]
            U = c1[:m1] + c2
            mp_, ml_, mq_ = c1[m1], c1[m1 + 1], c1[m1 + 2]
            if peval(w, x) != (mp_ + sum(g * u for g, u in zip(gam, U))) % P:
                return False, "proximity test (column)"
            Z = (pow(x, k, P) - 1) * kinv % P
            inv = batch_inv([(x - h) % P for h in Hk])
            Wb = [h * iv % P * Z % P for h, iv in zip(Hk, inv)]
            lin = ml_
            for ar, u in zip(arows, U):
                if u:
                    lin += u * (sum(a * b for a, b in zip(ar, Wb)) % P)
            if peval(q, x) != lin % P:
                return False, "linear test (column)"
            if peval(p, x) != (mq_ + sum(g * (u * u - u) for g, u in zip(gq, U))) % P:
                return False, "quadratic test (column)"
        return True, "accept"
    except (ValueError, IndexError, TypeError, AssertionError, OverflowError, KeyError, AttributeError) as ex:
        return False, f"malformed: {ex}"


# ------------------------------------------------------------------------------------------- simulator / falsifier
def simulate_legacy(st, T=309, rng=None):
    """Honest-verifier simulator run as an ATTACK: if every challenge is computable from the statement alone
    (legacy transcript), it fabricates an accepting proof for ANY statement, true or false, with no witness."""
    rng = rng or secrets.SystemRandom()
    sh = shape(st, T)
    k, th, m1, m2 = sh["k"], sh["th"], sh["m1"], sh["m2"]
    code = Code(k, th)
    nD = code.nD
    tr = Transcript(st.digest(), legacy=True)
    rho = draw_rho(tr, st, sh["F"])
    cons = linear_system(st, rho, sh["F"])
    mrows = m1 + m2
    gam = tr.ints("gamma", mrows, P)
    lam = tr.ints("lambda", len(cons), P)
    gq = tr.ints("gamma-q", mrows, P)
    J = tr.distinct("cols", T, nD)
    alpha, beta = alpha_beta(sh["g1"] + sh["g2"], cons, lam)
    a1 = alpha[:sh["n1"]] + [0] * (m1 * k - sh["n1"])
    a2 = alpha[sh["n1"]:] + [0] * (m2 * k - sh["n2"])
    arows = _rows(a1, k, m1) + _rows(a2, k, m2)
    w = [rng.randrange(P) for _ in range(k + th)]
    q = [rng.randrange(P) for _ in range(2 * k + th - 1)]
    q[0] = (q[0] + beta * pow(k, P - 2, P) - sum(q[0::k])) % P
    g = [rng.randrange(P) for _ in range(k + 2 * th - 1)]
    p = [0] * (2 * k + 2 * th - 1)
    for i, x in enumerate(g):
        p[i] = (p[i] - x) % P
        p[i + k] = (p[i + k] + x) % P
    E1 = [[rng.randrange(P) for _ in range(nD)] for _ in range(m1 + 3)]
    E2 = [[rng.randrange(P) for _ in range(nD)] for _ in range(m2)]
    Hk = Code._powers(code.wk, k)
    kinv = pow(k, P - 2, P)
    for j in J:
        x = code.pts[j]
        U = [E1[r][j] for r in range(m1)] + [E2[r][j] for r in range(m2)]
        Z = (pow(x, k, P) - 1) * kinv % P
        inv = batch_inv([(x - h) % P for h in Hk])
        Wb = [h * iv % P * Z % P for h, iv in zip(Hk, inv)]
        E1[m1][j] = (peval(w, x) - sum(a * u for a, u in zip(gam, U))) % P
        E1[m1 + 1][j] = (peval(q, x) - sum(u * (sum(a * b for a, b in zip(ar, Wb)) % P)
                                           for ar, u in zip(arows, U))) % P
        E1[m1 + 2][j] = (peval(p, x) - sum(a * (u * u - u) for a, u in zip(gq, U))) % P
    salts1 = [secrets.token_bytes(32) for _ in range(nD)]
    salts2 = [secrets.token_bytes(32) for _ in range(nD)]
    T1 = merkle([colbytes(E1, j) for j in range(nD)], salts1)
    T2 = merkle([colbytes(E2, j) for j in range(nD)], salts2)
    out = bytearray(T1[-1][0] + T2[-1][0] + b"".join(fe(x) for x in w + q + p))
    for j in J:
        out += colbytes(E1, j) + salts1[j] + b"".join(mpath(T1, j))
        out += colbytes(E2, j) + salts2[j] + b"".join(mpath(T2, j))
    return bytes(out)


# ------------------------------------------------------------------------------------------- per-step counts
class _Reg:
    def __init__(self, N, primes, t):
        self.N, self.primes, self.t = N, tuple(primes), t
        self.Q = math.prod(primes)


class ShapeOnly:
    """What the proof's size depends on: kind, ring, primes, t and the slot layout, no ciphertext data."""

    def __init__(self, kind, N, primes, t, slot_sizes):
        self.kind, self.reg = kind, _Reg(N, primes, t)
        self.slots = [tuple(range(n)) for n in slot_sizes]
        self.cts = [None] * len(slot_sizes)


def batch_proof_bits(kind, N, primes, t, slot_sizes, T=309):
    sh = shape(ShapeOnly(kind, N, primes, t, slot_sizes), T)
    return 8 * proof_bytes(sh["k"], sh["th"], T, sh["m1"], sh["m2"]), sh
