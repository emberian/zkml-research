"""The untrusted-input verifier for one dark-learning step (MPC fork, collaborative ZK proof): bytes in, verdict
out. Nothing is shared with the prover.

2026-11-06. Wire format of a STEP BUNDLE (all integers big-endian):
  header   magic b"DLSTEP01" | model id (u16 length, UTF-8, 1..64 bytes) | epoch u32 | step u64 | d u16 | n u8 |
           chained u8
  spine    the ZK spine proof (cosnark_zk), schema-driven: every length is a function of (d, n, parameters)
  public   the SPDZ public transcript: u32 count, then count field elements (the opened values)
  middle   the ZK middle proof (cosnark_gates_zk), schema-driven; its shapes come from the verifier's own
           symbolic replay of the step program against `public`
  owner    (when the ledger has a data owner) the owner's hash-based signature over (model, epoch, step,
           roots of its x and y commitments), leaf = step, OS.sig_len(OWNER_H) bytes. The spine binds the
           custodians' x to the owner's x, and the middle binds y the same way (signed-input binding).
Encoding: a field element is 8 bytes and must be < p (canonical). A hash is 32 bytes. A column index is u32 and
must be < its domain size. The proofs carry no length prefixes: the parser reads exactly what the public schema
says. Trailing bytes, truncation and non-canonical values are refused before any verification.

Acceptance is a separate, durable object (Ledger): the verifier is handed the EXPECTED binding
(model, epoch, step = last accepted + 1) and parent commitments (the last accepted child) by the ledger. Proof
bytes never choose them. A header that disagrees with the expectation is refused before parsing the rest. The
Fiat-Shamir transcript binds the same context, so a patched header fails verification.
"""
import fcntl
import hashlib
import json
import os
import struct

import cosnark as CS
import cosnark_gates as G
import cosnark_he as CH
import cosnark_gates_zk as GZ
import cosnark_zk as ZK
import cozk as Z
import mpc_fork as MF
import owner_sig as OS

MAGIC = b"DLSTEP01"
OWNER_H = 12                 # 2^12 one-time keys per owner tree

# The verifier's parameters, pinned here (not taken from whichever run script set module globals) and recorded in
# every ledger's genesis record (the profile name included, so a demo ledger and a production ledger never accept each
# other's steps). Two profiles (root decision, gen 4):
#   ledger (default): T = 309 distinct columns at rate 1/4, (3/4)^309 = 2^-128.25 per PCS and per Ligero, so
#                     grinding 2^g Fiat-Shamir transcripts still leaves about 2^(g-128);
#   demo:             T = 97, 2^-40.26, a STATISTICAL figure only: under Fiat-Shamir 2^g grinding gives about 2^(g-40).
# HE parameters travel with the profile (root decision, gen 4): the ledger profile's HE helpers run at N = 16384 with
# four 61-bit primes and a 2^175 flood, the only set measured to reach a million-step privacy bound (decision doc
# section 21); the demo profile keeps N = 8192, three primes, 2^118.
HE_LEDGER = dict(N=16384, L=4, F_BITS=175)
HE_DEMO = dict(N=8192, L=3, F_BITS=118)
PROFILES = {
    "ledger": dict(PROFILE="ledger", HE=HE_LEDGER, HIDE=618, NMASK=2, LIVES=2, T_COLS=309, BLOW=4, K_L=64, T_HIDE=309, T_OPEN=309,
                   OWNER_H=OWNER_H),
    "demo": dict(PROFILE="demo", HE=HE_DEMO, HIDE=194, NMASK=2, LIVES=2, T_COLS=97, BLOW=4, K_L=64, T_HIDE=97, T_OPEN=97,
                 OWNER_H=OWNER_H),
}
PARAMS = dict(PROFILES["ledger"])

def set_profile(name):
    """Select a profile explicitly (the demo profile is never a default)."""
    PARAMS.clear()
    PARAMS.update(PROFILES[name])
    pin_params()

def pin_params():
    CS.HIDE, CS.NMASK, CS.LIVES, CS.T_COLS, CS.BLOW = (PARAMS[k] for k in ("HIDE", "NMASK", "LIVES", "T_COLS", "BLOW"))
    ZK.K_L, ZK.T_HIDE, ZK.T_OPEN = PARAMS["K_L"], PARAMS["T_HIDE"], PARAMS["T_OPEN"]

pin_params()

class ParseError(Exception):
    pass

# ----------------------------------------------------------------------------------------------- codec
class W:
    def __init__(self, p):
        self.p, self.b = p, bytearray()

    def fe(self, x):
        if not (isinstance(x, int) and 0 <= x < self.p):
            raise ValueError("non-canonical field element")
        self.b += x.to_bytes(8, "big")

    def h(self, x):
        raw = bytes.fromhex(x)
        assert len(raw) == 32
        self.b += raw

    def idx(self, x, bound):
        assert 0 <= x < bound
        self.b += struct.pack(">I", x)

class R:
    def __init__(self, p, data):
        self.p, self.d, self.o = p, bytes(data), 0

    def take(self, k):
        if self.o + k > len(self.d):
            raise ParseError("truncated")
        out = self.d[self.o:self.o + k]
        self.o += k
        return out

    def fe(self):
        x = int.from_bytes(self.take(8), "big")
        if x >= self.p:
            raise ParseError("non-canonical field element")
        return x

    def h(self):
        return self.take(32).hex()

    def idx(self, bound):
        x = struct.unpack(">I", self.take(4))[0]
        if x >= bound:
            raise ParseError("column index out of range")
        return x

    def end(self):
        if self.o != len(self.d):
            raise ParseError("trailing bytes")

def walk(io, spec, obj=None):
    """spec: ("fe",) | ("h",) | ("idx", bound) | ("list", count, spec) | ("dict", [(key, spec)]) | ("tup", [spec]).
    Writer (io is W): walks obj. Reader (io is R): returns the object."""
    kind = spec[0]
    rd = isinstance(io, R)
    if kind == "fe":
        return io.fe() if rd else io.fe(obj)
    if kind == "h":
        return io.h() if rd else io.h(obj)
    if kind == "idx":
        return io.idx(spec[1]) if rd else io.idx(obj, spec[1])
    if kind == "list":
        if rd:
            return [walk(io, spec[2]) for _ in range(spec[1])]
        if len(obj) != spec[1]:
            raise ValueError(f"list length {len(obj)} != schema {spec[1]}")
        for x in obj:
            walk(io, spec[2], x)
        return None
    if kind == "dict":
        if rd:
            return {k: walk(io, s) for k, s in spec[1]}
        if sorted(obj) != sorted(k for k, _ in spec[1]):
            raise ValueError("dict keys differ from schema")
        for k, s in spec[1]:
            walk(io, s, obj[k])
        return None
    if kind == "tup":
        if rd:
            return tuple(walk(io, s) for s in spec[1])
        for x, s in zip(obj, spec[1]):
            walk(io, s, x)
        return None
    raise ValueError(kind)

L_ = lambda c, s: ("list", c, s)
FE, HH = ("fe",), ("h",)

def ligero_schema(n, group_sizes):
    P = Z.Params.__new__(Z.Params)
    k, t, T = ZK.K_L, ZK.T_HIDE, ZK.T_OPEN
    npts = 4 * (k + t)
    lg = (npts - 1).bit_length() + 1                    # salt + siblings
    cols = [L_(n, L_(T, ("tup", [L_(sz, FE), L_(lg, HH)]))) for sz in list(group_sizes) + [3]]
    return ("dict", [("w", L_(k + t, FE)), ("q", L_(2 * k + t - 1, FE)), ("pq", L_(2 * (k + t) - 1, FE)),
                     ("cols", ("tup", cols))])

def pcs_schema(n, sh):
    keys = sorted(sh)
    def cols(s):
        lg = (len(s.pts) - 1).bit_length() + 1
        return ("tup", [L_(CS.T_COLS, ("idx", len(s.pts))), L_(n, L_(CS.T_COLS, ("tup", [L_(s.R, FE), L_(lg, HH)])))])
    return (("dict", [(k, L_(n, HH)) for k in keys]),
            ("dict", [(k, L_(n, L_(sh[k].W, FE))) for k in keys]),
            ("dict", [(k, cols(sh[k])) for k in keys]))

def spine_schema(p, n, d, chained, bind=False):
    ld = d.bit_length() - 1
    sh = ZK.shapes(p, d, chained, bind)
    roots, prox, cols = pcs_schema(n, sh)
    evals = ZK.schedule(_NullTr(p), p, d, sh, lambda *a: None, bind=bind)[1]
    nrows = ZK.row_layout(d, sh, evals)[3]
    return ("dict", [("roots", roots),
                     ("round_roots", ("dict", [(nm, L_(ld, L_(n, HH))) for nm in ("z1", "z2", "b", "bg")])),
                     ("eval_roots", L_(n, HH)), ("mask_roots", L_(n, HH)), ("prox", prox), ("pcs_cols", cols),
                     ("ligero", ligero_schema(n, [1] * (4 * ld) + [nrows - 4 * ld]))])

def middle_schema(p, n, sym, d, bind=False, io=None):
    cons, had, prep, ext = G.middle(sym)
    lens, sh = GZ.public_shapes(p, prep, had, d, bind, io=io)
    roots, prox, cols = pcs_schema(n, sh)
    lh = (lens["A"] - 1).bit_length()
    Lmax = max((L - 1).bit_length() for L in lens.values())
    ks = sorted(lens)
    ev = GZ.evaluations(lens, ks, [0] * lh, [0] * Lmax, [0] * (d.bit_length() - 1) if bind else None)
    nrows = GZ.row_layout(sh, ev, lh, Lmax)[-1]
    return ("dict", [("roots", roots), ("zc_roots", L_(lh, L_(n, HH))), ("claims_root", L_(n, HH)),
                     ("lsc_roots", L_(Lmax, L_(n, HH))), ("eval_roots", L_(n, HH)), ("mask_roots", L_(n, HH)),
                     ("prox", prox), ("pcs_cols", cols),
                     ("ligero", ligero_schema(n, [1] * lh + [1] + [1] * Lmax + [nrows - lh - 1 - Lmax]))])

class _NullTr:
    """Shapes only: challenges are irrelevant to lengths."""
    def __init__(self, p):
        self.p = p
    def absorb(self, *x):
        pass
    def chal(self, p, k=1):
        return [0] * k

# ----------------------------------------------------------------------------------------------- bundle
def encode_step(p, ctx, d, n, chained, spine, public, middle, sym, owner_sig=None):
    model, epoch, step = ctx
    w = W(p)
    mb = model.encode()
    assert 1 <= len(mb) <= 64
    w.b += MAGIC + struct.pack(">H", len(mb)) + mb + struct.pack(">IQHBB", epoch, step, d, n, int(chained))
    bind = owner_sig is not None
    walk(w, spine_schema(p, n, d, chained, bind), _plain(spine))
    w.b += struct.pack(">I", len(public))
    for v in public:
        w.fe(v)
    walk(w, middle_schema(p, n, sym, d, bind), _plain(middle))
    if bind:
        assert len(owner_sig) == OS.sig_len(OWNER_H)
        w.b += owner_sig
    return bytes(w.b)

def _plain(obj):
    """Proof objects use tuples and lists interchangeably; the schema decides."""
    if isinstance(obj, dict):
        return {k: _plain(v) for k, v in obj.items()}
    if isinstance(obj, tuple):
        return tuple(_plain(x) for x in obj)
    if isinstance(obj, list):
        return [_plain(x) for x in obj]
    return obj

def he_field(params=None):
    """The deployed (HE) program's field: the HE profile's plaintext modulus t = ntt_primes(61, L + 1, 2N)[L]."""
    import bfv_ref as bfv
    he = (params or PARAMS)["HE"]
    return bfv.ntt_primes(61, he["L"] + 1, 2 * he["N"])[he["L"]]

def verify_step(p, blob, expect_ctx, parent_roots, tab, d_pinned, owner_pk=None, min_leaf=0, program=None):
    """The untrusted-input verifier. expect_ctx, parent_roots, d_pinned, owner_pk, min_leaf and program come from the
    ledger, never from the blob. program: None (the harness's plain-SPDZ step) or the genesis record's program dict;
    with "he": true it is the deployed step (cosnark_he: HE matvec and outer, the shifts S1..K3, carried weights from
    step 2 on), over the HE profile's field. Returns (ok, why, (child roots, owner leaf))."""
    pin_params()
    bind = owner_pk is not None
    try:
        r = R(p, blob)
        if r.take(8) != MAGIC:
            raise ParseError("bad magic")
        ml = struct.unpack(">H", r.take(2))[0]
        if not 1 <= ml <= 64:
            raise ParseError("bad model id length")
        model_b = r.take(ml)
        epoch, step, d, n, chained = struct.unpack(">IQHBB", r.take(16))
        if (model_b, epoch, step) != (expect_ctx[0].encode(), expect_ctx[1], expect_ctx[2]):
            shown = model_b.decode("utf-8", "replace")
            return False, f"binding mismatch: proof is for {(shown, epoch, step)}, expected {tuple(expect_ctx)}", None
        if d != d_pinned or n != 3 or chained != 1:
            raise ParseError("shape or chaining differs from the ledger's genesis record")
        spine = walk(r, spine_schema(p, n, d, True, bind))
        cnt = struct.unpack(">I", r.take(4))[0]
        if cnt > 1 << 24:
            raise ParseError("public transcript too long")
        public = [r.fe() for _ in range(cnt)]
        try:
            if program and program.get("he"):
                if p != he_field():
                    raise ParseError("the deployed program's field is the HE profile's plaintext modulus")
                prog = CH.Prog.of(program)
                sym = CH.replay(p, public, d, prog.tables(p), prog, carried=expect_ctx[2] > 1)
            elif program:
                raise ParseError("a plain-SPDZ program other than the harness's is not supported")
            else:
                sym = G.RecEngine(p, n, None, symbolic=True, transcript=[("open", {}, v) for v in public])
                MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
        except IndexError:
            raise ParseError("public transcript shorter than the step program")
        except CH.ScheduleError as e:
            raise ParseError(str(e))
        if sym.tpos != cnt:
            raise ParseError("public transcript longer than the step program")
        middle = walk(r, middle_schema(p, n, sym, d, bind))
        sig = r.take(OS.sig_len(OWNER_H)) if bind else None
        r.end()
    except ParseError as e:
        return False, f"parse: {e}", None
    except Exception as e:                       # anything else in parsing is a refusal, never a crash
        return False, f"parse: {type(e).__name__}", None
    ctx = tuple(expect_ctx)
    leaf = None
    if bind:
        if not OS.verify(owner_pk, OWNER_H, min_leaf,
                         OS.batch_message(ctx, spine["roots"]["xo"], middle["roots"]["yo"]), sig):
            return False, "owner signature does not verify over (context, x and y commitments), or its leaf was used", None
        leaf = OS.sig_leaf(sig)
    ok, why = ZK.verify_zk(p, n, d, ctx, parent_roots, True, spine, bind, public=public)
    if not ok:
        return False, f"spine: {why}", None
    ok, why = GZ.verify_middle_zk(p, n, sym, d, spine["roots"], ctx, middle, bind)
    if not ok:
        return False, f"middle: {why}", None
    return True, "accept", ({"W1": spine["roots"]["W1n"], "W2": spine["roots"]["W2n"]}, leaf)

# ----------------------------------------------------------------------------------------------- release
RMAGIC = b"DLRELS01"

def encode_release(p, ctx, d, n, M, ncls, public, middle, sym, io):
    """The release bundle: header (magic, model, epoch, head step, d, n, M, ncls), the public transcript (its last
    value is the released count C), the release proof (the ZK middle over the release program, io)."""
    model, epoch, step = ctx
    w = W(p)
    mb = model.encode()
    assert 1 <= len(mb) <= 64
    w.b += RMAGIC + struct.pack(">H", len(mb)) + mb + struct.pack(">IQHBHB", epoch, step, d, n, M, ncls)
    w.b += struct.pack(">I", len(public))
    for v in public:
        w.fe(v)
    walk(w, middle_schema(p, n, sym, d, False, io), _plain(middle))
    return bytes(w.b)

def verify_release(p, blob, expect_ctx, head_roots, X, labels, program, ncls, d_pinned, kc=10):
    """The untrusted-input verifier of a release. expect_ctx = (model, epoch, head step) and head_roots (the head's
    W1, W2 roots) come from the ledger; X, labels and the program are the published policy, never the blob.
    Returns (ok, why, (M, C))."""
    import cosnark_release as CR
    pin_params()
    M = len(labels)
    try:
        r = R(p, blob)
        if r.take(8) != RMAGIC:
            raise ParseError("bad magic")
        ml = struct.unpack(">H", r.take(2))[0]
        if not 1 <= ml <= 64:
            raise ParseError("bad model id length")
        model_b = r.take(ml)
        epoch, step, d, n, m_, nc = struct.unpack(">IQHBHB", r.take(18))
        if (model_b, epoch, step) != (expect_ctx[0].encode(), expect_ctx[1], expect_ctx[2]):
            shown = model_b.decode("utf-8", "replace")
            return False, f"binding mismatch: release is for {(shown, epoch, step)}, expected {tuple(expect_ctx)}", None
        if (d, n, m_, nc) != (d_pinned, 3, M, ncls) or len(X) != d or any(len(row) != M for row in X):
            raise ParseError("shape differs from the ledger's genesis record or the release policy")
        cnt = struct.unpack(">I", r.take(4))[0]
        if cnt > 1 << 26:
            raise ParseError("public transcript too long")
        public = [r.fe() for _ in range(cnt)]
        prog = CH.Prog.of(program or {})
        try:
            sym = CR.replay(p, public, X, labels, prog, ncls, kc)
        except IndexError:
            raise ParseError("public transcript shorter than the release program")
        if sym.tpos != cnt:
            raise ParseError("public transcript longer than the release program")
        io = CR.io_spec(p, d, M)
        middle = walk(r, middle_schema(p, n, sym, d, False, io))
        r.end()
    except ParseError as e:
        return False, f"parse: {e}", None
    except Exception as e:
        if os.environ.get("DP_DEBUG"):
            raise
        return False, f"parse: {type(e).__name__}", None
    C = public[-1]
    if C > M:
        return False, "released count exceeds M", None
    ok, why = GZ.verify_middle_zk(p, n, sym, d, head_roots, tuple(expect_ctx), middle, False, io=io)
    if not ok:
        return False, f"release: {why}", None
    return True, "accept", (M, C)

# ----------------------------------------------------------------------------------------------- ledger
class Ledger:
    """Durable acceptance: one append-only file per model, one JSON record per line, each fsync'd.
      genesis  pins model, d, the verifier PARAMS, the owner key (or an explicit "none"), the custodian set and the
               genesis weight commitment roots, so the first bundle cannot choose them
      step     (epoch, step, digest, child roots, owner leaf)
      rotate   (new epoch, new custodian set, the NEW committee's commitment roots of the current weights), accepted
               only with a handover proof's bytes (handover.encode, gen 5) showing the new roots commit the same weights
               as the head's roots; the record carries sha256 of those bytes.
    The head (expected context, parent roots, next owner leaf) is replayed from the file on open; a torn or
    out-of-order line fails closed. accept() holds an exclusive file lock, so two acceptors cannot both append
    step N."""
    def __init__(self, path, model, genesis=None):
        self.path, self.model = path, model
        self.recs = []
        if not os.path.exists(path):
            assert genesis is not None, "a new ledger needs its genesis record"
            g = dict(kind="genesis", model=model, d=genesis["d"], params=PARAMS,
                     owner_pk=genesis["owner_pk"].hex() if genesis.get("owner_pk") else "none",
                     custodians=genesis["custodians"], roots=genesis["roots"])
            if genesis.get("program"):
                g["program"] = genesis["program"]
            self._append(g, new=True)
        with open(path) as f:
            for no, line in enumerate(f):
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError:
                    raise RuntimeError(f"ledger {path}: line {no + 1} is not a complete record (fail closed)")
                self.recs.append(rec)
        g = self.recs[0]
        if g.get("kind") != "genesis" or g["model"] != model or g["params"] != PARAMS:
            raise RuntimeError("ledger genesis record missing, for another model, or with other parameters")
        self._replay()

    def _replay(self):
        g = self.recs[0]
        self.d = g["d"]
        self.program = g.get("program")
        self.owner_pk = None if g["owner_pk"] == "none" else bytes.fromhex(g["owner_pk"])
        self.epoch, self.step, self.parent, self.next_leaf, self.custodians = 0, 0, g["roots"], 0, g["custodians"]
        for no, rec in enumerate(self.recs[1:], 2):
            if rec["kind"] == "step":
                if (rec["epoch"], rec["step"]) != (self.epoch, self.step + 1):
                    raise RuntimeError(f"ledger line {no} breaks the sequence (fail closed)")
                self.step, self.parent = rec["step"], rec["child"]
                if rec.get("leaf") is not None:
                    self.next_leaf = rec["leaf"] + 1
            elif rec["kind"] == "rotate":
                if rec["epoch"] != self.epoch + 1:
                    raise RuntimeError(f"ledger line {no}: rotation out of order (fail closed)")
                self.epoch, self.custodians, self.parent = rec["epoch"], rec["custodians"], rec["roots"]
            else:
                raise RuntimeError(f"ledger line {no}: unknown record kind (fail closed)")

    def _append(self, rec, new=False):
        with open(self.path, "a") as f:
            f.write(json.dumps(rec) + "\n")
            f.flush()
            os.fsync(f.fileno())
        if new:                                   # make the new file's directory entry durable too
            fd = os.open(os.path.dirname(os.path.abspath(self.path)), os.O_RDONLY)
            try:
                os.fsync(fd)
            finally:
                os.close(fd)

    def head(self):
        return (self.model, self.epoch, self.step + 1), self.parent

    def handover_context(self, custodians):
        import handover as HO
        return HO.context_digest(self.model, self.epoch, self.epoch + 1, self.step, self.custodians, custodians)

    def rotate(self, p, custodians, new_roots, handover):
        """Custody rotation: a durable record, accepted only with the BYTES of a handover proof (handover.encode)
        that the new committee's roots commit the same weights as the head's. Proofs from the old committee, whose
        commitments are to the old share tuple, no longer match the parent. Returns (ok, why); fails closed on any
        error. The record carries sha256 of the proof bytes."""
        import handover as HO
        with open(self.path) as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            self.recs = [json.loads(l) for l in open(self.path)]
            self._replay()
            if not handover:
                return False, "rotation refused: no handover proof"
            try:
                ok, why, got = HO.verify_bytes(p, self.d, len(self.custodians), len(custodians),
                                               self.handover_context(custodians), self.parent, bytes(handover))
            except Exception as e:  # untrusted input: any failure is a refusal
                return False, f"rotation refused: malformed handover proof ({type(e).__name__})"
            if not ok:
                return False, f"rotation refused: {why}"
            if got != new_roots:
                return False, "rotation refused: the handover proof is for other new roots"
            rec = dict(kind="rotate", epoch=self.epoch + 1, custodians=custodians, roots=new_roots,
                       handover_proof=hashlib.sha256(bytes(handover)).hexdigest())
            self._append(rec)
            self.recs.append(rec)
            self._replay()
        return True, "accept"

    def accept(self, p, blob, tab):
        with open(self.path) as f:
            fcntl.flock(f, fcntl.LOCK_EX)          # one acceptor at a time; re-read the head under the lock
            self.recs = [json.loads(l) for l in open(self.path)]
            self._replay()
            ctx, parent = self.head()
            ok, why, out = verify_step(p, blob, ctx, parent, tab, self.d, owner_pk=self.owner_pk,
                                       min_leaf=self.next_leaf, program=self.program)
            if not ok:
                return False, why
            child, leaf = out
            rec = dict(kind="step", epoch=ctx[1], step=ctx[2], digest=hashlib.sha256(blob).hexdigest(),
                       child=child, leaf=leaf)
            self._append(rec)
            self.recs.append(rec)
            self._replay()
        return True, "accept"
