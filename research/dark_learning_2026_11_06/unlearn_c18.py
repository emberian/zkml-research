"""C18: the sufficient-statistics learner with certified exact deletion (initiative 16).

2026-11-06. Pure Python, no dependencies. Every number printed is a COUNT; nothing is timed.

The learner. A frozen, public, pinned feature map phi (C18's "frozen phi"; C19 is the same learner with phi
followed by a fixed public projection, see unlearn_c19.py). The state is the exact integer statistics
    A = sum phi(x) phi(x)^T,   B = sum phi(x) e_y^T      (one-hot labels, so B needs additions only)
over the LIVE multiset of records. The release solves (lam I + A) W = B exactly over Q and is published in the
canonical form W = N / delta (delta > 0, gcd of delta and every entry of N is 1). Prediction is argmax_c phi(x)^T N_c,
exact in integers (delta > 0 does not change the argmax).

The commitments.
  * The dataset LOG is an MMR (same peaks, bagging and domain separation as breadstuffs dregg-query/src/mmr.rs;
    SHA-256 for BLAKE3). A leaf value is the record's content key K(r) = H("rec", canonical bytes) while live and
    the tombstone T(j) = H("tomb", j) after deletion. Positions never move.
  * The statistics commitment hashes the canonical encoding of (A, B). The model commitment hashes
    (stats commitment, lam, delta, N).
  * A HEAD binds (genesis, parent head, seq, log root, log length, stats commitment, ACTIVE model commitment or none).

The certificates (each checked by a verifier that holds only the current head and, in this host-visible variant,
the public statistics; never the dataset):
  insert(r)   frontier of the old log (bagged = old root); the verifier appends K(r), recomputes A, B itself.
  delete(c)   the request is a CONTENT KEY c (every copy goes). The certificate carries the record bytes r with
              K(r) = c, the positions P, one sibling path per position (sequential updates c -> T(j)), and the
              whole post-deletion leaf list (the absence leg: rebuilt to the new root, Count(c) = 0). The verifier
              computes S' = S - |P| contrib(r) itself. The new head has NO active model (C20).
  release     (N, delta); the verifier checks canonical form and (lam I + A) N = delta B exactly over Z. lam > 0 is
              pinned at genesis, so lam I + A is positive definite and the release is THE solution (Lean:
              release_unique). Only now does the head's active model move (C20 proof-gated activation).
The ledger refuses any certificate whose parent is not its head (single timeline; stale parents) and any serve
request for a model that is not the active one.
"""
import copy
import hashlib
import json
import os
import urllib.request
from fractions import Fraction
from math import gcd, lcm

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
OPTDIGITS = {   # UCI "Optical Recognition of Handwritten Digits" (CC BY 4.0), fetched 2026-11-06
    "optdigits.tra": "e1b683cc211604fe8fd8c4417e6a69f31380e0c61d4af22e93cc21e9257ffedd",
    "optdigits.tes": "6ebb3d2fee246a4e99363262ddf8a00a3c41bee6014c373ed9d9216ba7f651b8",
}
UCI = "https://archive.ics.uci.edu/ml/machine-learning-databases/optdigits/"
NCLASS = 10

# ------------------------------------------------------------------------------------------------ counting
class Counts(dict):
    def add(self, k, v=1):
        self[k] = self.get(k, 0) + v

CNT = Counts()

def H(tag, *parts):
    """Domain-separated SHA-256; every part is length-prefixed."""
    CNT.add("hash")
    m = hashlib.sha256()
    t = ("unlearn-v1:" + tag).encode()
    m.update(len(t).to_bytes(2, "big") + t)
    for p in parts:
        if isinstance(p, int):
            p = p.to_bytes((p.bit_length() + 8) // 8 + 1, "big", signed=True)
        elif isinstance(p, str):
            p = p.encode()
        m.update(len(p).to_bytes(8, "big") + p)
    return m.digest()

# ------------------------------------------------------------------------------------------------ data
def load(name):
    path = os.path.join(DATA, name)
    if not os.path.exists(path):
        os.makedirs(DATA, exist_ok=True)
        with urllib.request.urlopen(UCI + name) as r:
            raw = r.read()
        with open(path, "wb") as f:
            f.write(raw)
    raw = open(path, "rb").read()
    got = hashlib.sha256(raw).hexdigest()
    if got != OPTDIGITS[name]:
        raise SystemExit(f"{name}: sha256 {got} is not the pinned {OPTDIGITS[name]}")
    rows = [tuple(map(int, l.split(b","))) for l in raw.splitlines() if l.strip()]
    assert all(len(r) == 65 and all(0 <= v <= 16 for v in r[:64]) and 0 <= r[64] <= 9 for r in rows)
    return rows

def valid_record(r):
    return (isinstance(r, tuple) and len(r) == 65 and all(type(v) is int for v in r)
            and all(0 <= v <= 16 for v in r[:64]) and 0 <= r[64] < NCLASS)

def rec_bytes(r):
    return b"optdigits-v1:" + bytes(r[:64]) + bytes([r[64]])

def content_key(r):
    return H("rec", rec_bytes(r))

def tomb(j):
    return H("tomb", j)

# ------------------------------------------------------------------------------------------------ feature maps
class Phi:
    """A pinned public feature map. ident: x -> (x, 1), D = 65. proj: x -> U^T (x, 1) with integer U (C19)."""
    def __init__(self, name, U=None):
        self.name, self.U = name, U
        self.D = 65 if U is None else len(U[0])
        self.id = H("phi", name, json.dumps(U) if U is not None else "")

    def __call__(self, r):
        x = list(r[:64]) + [1]
        if self.U is None:
            return x
        CNT.add("phi_mult", 65 * self.D)
        return [sum(x[i] * self.U[i][k] for i in range(65)) for k in range(self.D)]

# ------------------------------------------------------------------------------------------------ statistics
def zero_stats(D):
    return [[0] * D for _ in range(D)], [[0] * NCLASS for _ in range(D)]

def add_contrib(S, f, y, sign=1, mult=1, count=True):
    """S += sign * mult * contrib(f, y). Symmetric rank-1: D(D+1)/2 products; B is one-hot: additions only."""
    A, B = S
    D = len(f)
    s = sign * mult
    for i in range(D):
        fi = f[i]
        if fi:
            Ai = A[i]
            for j in range(i, D):
                v = s * fi * f[j]
                Ai[j] += v
                if j != i:
                    A[j][i] += v
            B[i][y] += s * fi
    if count:
        CNT.add("contrib_mult", D * (D + 1) // 2)

def copy_stats(S):
    return [r[:] for r in S[0]], [r[:] for r in S[1]]

def stats_commit(S):
    A, B = S
    return H("stats", len(A), NCLASS, json.dumps(A).encode(), json.dumps(B).encode())

def fold(rows, phi):
    S = zero_stats(phi.D)
    for r in rows:
        add_contrib(S, phi(r), r[64], count=False)
    return S

# ------------------------------------------------------------------------------------------------ release
def solve(S, lam):
    """Exact rational solve of (lam I + A) W = B; canonical (N, delta)."""
    A, B = S
    D = len(A)
    M = [[Fraction(A[i][j] + (lam if i == j else 0)) for j in range(D)] + [Fraction(v) for v in B[i]]
         for i in range(D)]
    for k in range(D):
        piv = next(i for i in range(k, D) if M[i][k] != 0)
        M[k], M[piv] = M[piv], M[k]
        pk = M[k][k]
        Mk = M[k] = [v / pk for v in M[k]]
        for i in range(D):
            if i != k and M[i][k]:
                fct = M[i][k]
                M[i] = [a - fct * b for a, b in zip(M[i], Mk)]
    W = [row[D:] for row in M]
    den = 1
    for row in W:
        for v in row:
            den = lcm(den, v.denominator)
    N = [[int(v * den) for v in row] for row in W]
    return canonical(N, den)

def canonical(N, den):
    g = den
    for row in N:
        for v in row:
            g = gcd(g, v)
    if den < 0:
        g = -g
    return [[v // g for v in row] for row in N], den // g

def model_commit(sc, lam, N, den):
    return H("model", sc, lam, den, json.dumps(N).encode())

def check_release(S, lam, N, den):
    """(lam I + A) N == den * B over Z, entrywise. Returns (ok, reason)."""
    A, B = S
    D = len(A)
    if not (isinstance(den, int) and den > 0):
        return False, "release: delta must be a positive integer"
    if not (isinstance(N, list) and len(N) == D and all(isinstance(row, list) and len(row) == NCLASS and
                                                        all(type(v) is int for v in row) for row in N)):
        return False, "release: N is not a D x 10 integer matrix"
    if canonical(N, den) != (N, den):
        return False, "release: (N, delta) not in canonical form"
    for i in range(D):
        Ai = A[i]
        for c in range(NCLASS):
            v = lam * N[i][c] + sum(Ai[j] * N[j][c] for j in range(D))
            if v != den * B[i][c]:
                CNT.add("release_bigmult", (i * NCLASS + c + 1) * D)
                return False, "release: (lam I + A) N != delta B"
    CNT.add("release_bigmult", D * D * NCLASS)
    return True, "ok"

def predict(N, f):
    s = [sum(f[i] * N[i][c] for i in range(len(f))) for c in range(NCLASS)]
    return max(range(NCLASS), key=lambda c: s[c])

def accuracy(N, phi, rows):
    return sum(predict(N, phi(r)) == r[64] for r in rows)

# ------------------------------------------------------------------------------------------------ MMR
def leaf_h(v):
    return H("mmr-leaf", v)

def node_h(l, r):
    return H("mmr-node", l, r)

def bag(peaks):
    acc = H("mmr-empty")
    for _, ph in peaks:                         # oldest first, as dregg-query bag_peaks
        acc = H("mmr-bag", ph, acc)
    return acc

def push(peaks, v):
    """Append one leaf value to a frontier (oldest first); merges equal heights."""
    peaks = list(peaks) + [(0, leaf_h(v))]
    while len(peaks) >= 2 and peaks[-1][0] == peaks[-2][0]:
        (hl, l), (_, r) = peaks[-2], peaks[-1]
        peaks[-2:] = [(hl + 1, node_h(l, r))]
    return peaks

def frontier_ok(peaks):
    hs = [h for h, _ in peaks]
    return all(0 <= h < 64 for h in hs) and all(a > b for a, b in zip(hs, hs[1:]))

def build_peaks(values):
    peaks = []
    for v in values:
        peaks = push(peaks, v)
    return peaks

def covering(n, pos):
    start = 0
    for k, hgt in enumerate([h for h in range(63, -1, -1) if n >> h & 1]):
        if pos < start + (1 << hgt):
            return k, start, hgt
        start += 1 << hgt
    raise IndexError(pos)

def path_of(values, pos):
    """Prover side: sibling path (bottom-up) of pos inside its covering peak."""
    k, start, hgt = covering(len(values), pos)
    level = [leaf_h(v) for v in values[start:start + (1 << hgt)]]
    off, path = pos - start, []
    for _ in range(hgt):
        path.append(level[off ^ 1])
        level = [node_h(level[i], level[i + 1]) for i in range(0, len(level), 2)]
        off >>= 1
    return path

def peak_from(v, off, path):
    x = leaf_h(v)
    for s in path:
        x = node_h(x, s) if off & 1 == 0 else node_h(s, x)
        off >>= 1
    return x

def update(root, peaks, n, pos, old, new, path):
    """Verifier side: the frontier must bag to root; pos must open to `old`; returns the frontier with `new`."""
    if not frontier_ok(peaks) or sum(1 << h for h, _ in peaks) != n or bag(peaks) != root:
        return None, "frontier does not bag to the committed root"
    k, start, hgt = covering(n, pos)
    if len(path) != hgt:
        return None, "path length != covering peak height"
    if peak_from(old, pos - start, path) != peaks[k][1]:
        return None, "position does not open to the claimed old value"
    peaks = list(peaks)
    peaks[k] = (hgt, peak_from(new, pos - start, path))
    return peaks, "ok"

def check_delete_log(root, n, cert):
    """The four log legs of a delete certificate (opened, tomb, frame by sequential path updates; absent by the
    whole-log Count). Returns (ok, reason, post-deletion root). Shared by the host-visible and custodied ledgers."""
    r, c, P = cert["record"], cert["key"], cert["positions"]
    if content_key(r) != c:
        return False, "delete: record bytes do not hash to the requested key", None
    if not P or len(set(P)) != len(P):
        return False, "delete: positions empty or repeated", None
    if len(cert["paths"]) != len(P):
        return False, "delete: one path per position", None
    peaks = cert["frontier"]
    for pos, path in zip(P, cert["paths"]):
        if not 0 <= pos < n:
            return False, "delete: position out of range", None
        peaks, why = update(root, peaks, n, pos, c, tomb(pos), path)
        if peaks is None:
            return False, "delete: " + why, None
        root = bag(peaks)
    L = cert["log_after"]
    if len(L) != n or bag(build_peaks(L)) != root:
        return False, "absence: whole-log values do not rebuild the post-deletion root", None
    cnt = sum(v == c for v in L)
    CNT.add("absence_compare", n)
    if cnt != 0:
        return False, f"absence: Count(key) = {cnt} != 0 after deletion", None
    return True, "ok", root

# ------------------------------------------------------------------------------------------------ heads & ledger
def head_hash(hd):
    return H("head", hd["genesis"], hd["parent"], hd["seq"], hd["log_root"], hd["log_len"], hd["stats"],
             hd["model"] or b"")

class Genesis:
    def __init__(self, phi, lam, source):
        assert isinstance(lam, int) and lam > 0, "lam > 0 is what makes the release unique (release_unique)"
        self.phi, self.lam = phi, lam
        self.source = json.dumps(source, sort_keys=True)          # frozen: a canonical string, never the caller's object
        self.id = H("genesis", phi.id, lam, NCLASS, self.source)

    def head0(self):
        S = zero_stats(self.phi.D)
        return dict(genesis=self.id, parent=b"", seq=0, log_root=bag([]), log_len=0, stats=stats_commit(S),
                    model=None), S

class Ledger:
    """The verifier. Holds the current head and (host-visible variant) the public statistics. Never the data."""
    def __init__(self, gen):
        self.gen = gen
        self.head, self.S = gen.head0()
        self.accepted = []

    def _next_ok(self, cert, new):
        if cert["parent"] != head_hash(self.head):
            return "parent is not the ledger head (stale or forked)"
        if not isinstance(new, dict) or new.get("genesis") != self.gen.id or new.get("parent") != cert["parent"] \
                or new.get("seq") != self.head["seq"] + 1:
            return "new head does not extend the ledger head"
        return None

    def accept(self, cert):
        CNT.add("certs_checked")
        new = cert["new_head"]
        err = self._next_ok(cert, new)
        if err:
            return False, err
        kind = cert["kind"]
        phi, hd = self.gen.phi, self.head
        if kind in ("insert", "delete") and not valid_record(cert["record"]):
            return False, f"{kind}: record is not a 64-feature optdigits record with a label"
        if kind == "insert":
            r = cert["record"]
            peaks = cert["frontier"]
            if not frontier_ok(peaks) or sum(1 << h for h, _ in peaks) != hd["log_len"] or bag(peaks) != hd["log_root"]:
                return False, "insert: frontier does not bag to the committed root"
            root = bag(push(peaks, content_key(r)))
            S = copy_stats(self.S)
            add_contrib(S, phi(r), r[64])
            want = dict(hd, parent=cert["parent"], seq=hd["seq"] + 1, log_root=root, log_len=hd["log_len"] + 1,
                        stats=stats_commit(S), model=None)
        elif kind == "delete":
            r, P = cert["record"], cert["positions"]
            ok, why, root = check_delete_log(hd["log_root"], hd["log_len"], cert)
            if not ok:
                return False, why
            n = hd["log_len"]
            S = copy_stats(self.S)
            add_contrib(S, phi(r), r[64], sign=-1, mult=len(P))
            want = dict(hd, parent=cert["parent"], seq=hd["seq"] + 1, log_root=root, log_len=n,
                        stats=stats_commit(S), model=None)
        elif kind == "release":
            S = self.S
            ok, why = check_release(S, self.gen.lam, cert["N"], cert["delta"])
            if not ok:
                return False, why
            want = dict(hd, parent=cert["parent"], seq=hd["seq"] + 1,
                        model=model_commit(hd["stats"], self.gen.lam, cert["N"], cert["delta"]))
        else:
            return False, "unknown certificate kind"
        if not isinstance(new, dict) or set(new) != set(want):
            return False, f"{kind}: claimed head has fields other than the ledger's (Codex round 2)"
        for k in ("log_root", "log_len", "stats", "model"):
            if new[k] != want[k]:
                return False, f"{kind}: claimed head field '{k}' is not the one the certificate determines"
        if new != want:
            return False, f"{kind}: claimed head differs from the one the certificate determines"
        self.head, self.S = want, S          # the ledger stores ITS head, never the prover's object (Codex r1, r2)
        self.accepted.append(kind)
        return True, "ok"

    def serve(self, mc):
        """C20: only the active model of the head is served."""
        if self.head["model"] is None:
            return False, "serve: no active model (a deletion invalidated it; awaiting a release certificate)"
        if mc != self.head["model"]:
            return False, "serve: model is not the active one (stale)"
        return True, "ok"

# ------------------------------------------------------------------------------------------------ the host (prover)
class Host:
    """Honest prover. Attacks are mutations of its certificates (run_unlearn.py)."""
    def __init__(self, gen):
        self.gen = gen
        self.head, self.S = gen.head0()
        self.values, self.peaks, self.records = [], [], {}

    def _new(self, **kw):
        new = dict(self.head, parent=head_hash(self.head), seq=self.head["seq"] + 1)
        new.update(kw)
        return new

    def insert(self, r):
        c = content_key(r)
        self.records[c] = r
        S = copy_stats(self.S)
        add_contrib(S, self.gen.phi(r), r[64], count=False)
        peaks = push(self.peaks, c)
        cert = dict(kind="insert", parent=head_hash(self.head), record=r, frontier=self.peaks,
                    new_head=self._new(log_root=bag(peaks), log_len=len(self.values) + 1, stats=stats_commit(S),
                                       model=None))
        return cert, (S, peaks, self.values + [c])

    def delete(self, c):
        P = [j for j, v in enumerate(self.values) if v == c]
        r = self.records[c]
        vals = list(self.values)
        paths = []
        for j in P:
            paths.append(path_of(vals, j))
            vals[j] = tomb(j)
        S = copy_stats(self.S)
        add_contrib(S, self.gen.phi(r), r[64], sign=-1, mult=len(P), count=False)
        peaks = build_peaks(vals)
        cert = dict(kind="delete", parent=head_hash(self.head), key=c, record=r, positions=P, paths=paths,
                    frontier=self.peaks, log_after=vals,
                    new_head=self._new(log_root=bag(peaks), stats=stats_commit(S), model=None))
        return cert, (S, peaks, vals)

    def release(self):
        N, den = solve(self.S, self.gen.lam)
        cert = dict(kind="release", parent=head_hash(self.head), N=N, delta=den,
                    new_head=self._new(model=model_commit(self.head["stats"], self.gen.lam, N, den)))
        return cert, (self.S, self.peaks, self.values)

    def commit(self, cert, state):
        self.head = cert["new_head"]
        self.S, self.peaks, self.values = state
