"""The bit-exact reference for the GATED native custodians (native/darkstep --gate T): native_ref.py's step, with the
custodians' HE keys from the key ceremony (keygen_ceremony.run_ceremony: a_j = public_a(seed/j), every key
registered with its key proof) and the recipient's ZKPoPK gate: one batched Ligero proof (zkpopk_ligero, kind "sk")
per (sender, HE call), verified by both recipients before any ptxct touches the batch. A refusal aborts the step.

    DL_DETERMINISTIC=<seed> python3 native_ref_gated.py N L F_bits d T [out_prefix] [--attack zk_off_layout:J]

The gate does not change the step's outputs (decryption is exact, the returners' masks do not depend on the key),
so the transcript, share and sigma digests equal native_ref.py's; what the gate adds, and what the native run must
equal, is the ceremony (seed, every b_j) and every batch proof (sha256 of its bytes, per sender and call).
Batch context: ["dl-he-batch", "model", 0, 0, kind ("mv" | "ou"), call number, transpose, sender]; slots: forward
matvec 64 - d_c .. 63, transpose 0, 64, .., 64 (d_r - 1), outer 0 .. d_c - 1 (the he_matvec / he_outer layouts).
Falsifier zk_off_layout:J: sender J's first matvec batch carries 12345 at the first coefficient off the layout, with
a forged proof (cheat path); both recipients refuse it before any product.
"""
import hashlib
import json
import math
import random
import sys
import time

import bfv_ref as bfv
import he_matvec as HM
import he_outer as HO
import keygen_ceremony as K
import mpc_fork as MF
import native_ref as NR
import spdz
import step_spec as S
import zkpopk_ligero as Z

CUR = {}
OWNER = {}          # id(ct) -> sender
PENDING = {}        # (label, sender) -> [(ct, m, e)]
GATED = set()
STATE = dict(regs=None, cust=None, T=309, attack=None, proofs={}, products=0, gate_seconds=0.0)
_ptxct = HM.ptxct


def lbl(kind, call, tr, j):
    return f"{kind}-{call}-{tr}-{j}"


def context(kind, call, tr, j):
    return ["dl-he-batch", "model", 0, 0, kind, call, tr, j]


def slots_now(N):
    if CUR["kind"] == "mv":
        d = CUR["d"]
        dc, dr = HM.layout(d, N)
        return list(range(64 - dc, 64)) if not CUR["tr"] else [64 * k for k in range(dr)]
    dc, _ = HO.layout(CUR["d1"], CUR["d2"], N)
    return list(range(dc))


def witness_r(Q, t, m):
    x = (-Q * m) % t
    return x - t if x > t // 2 else x


class GatedBFV(bfv.BFV):
    """bfv.BFV.encrypt_exact, draw for draw, recording (ct, m, e) for the sender's batch proof."""

    def __init__(self, N, Q, t, seed, s, owner):
        super().__init__(N, Q, t, seed=seed)
        self.s = list(s)
        self.owner = owner

    def encrypt_exact(self, m):
        a = self.uniform()
        e = self.small_error()
        as_, _ = bfv.negacyclic_mul(bfv.poly_centered(a, self.Q), self.s)
        Q, t = self.Q, self.t
        key = (lbl(CUR["kind"], CUR["call"], CUR["tr"], self.owner), self.owner)
        batch = PENDING.setdefault(key, [])
        m = list(m)
        if (STATE["attack"] == ("zk_off_layout", self.owner) and CUR["kind"] == "mv" and CUR["call"] == 1
                and not batch):
            sl = set(slots_now(self.N))
            m[next(k for k in range(self.N) if k not in sl)] = 12345
        c0 = [((2 * Q * bfv.centered(mi, t) + t) // (2 * t) - x - ei) % Q for mi, x, ei in zip(m, as_, e)]
        ct = (c0, a)
        batch.append((ct, m, e))
        OWNER[id(ct)] = self.owner
        return ct


def gate(j):
    kind, call, tr = CUR["kind"], CUR["call"], CUR["tr"]
    key = (lbl(kind, call, tr, j), j)
    batch = PENDING[key]
    reg = STATE["regs"][j]
    N, Q, t = reg.N, reg.Q, reg.t
    sl = slots_now(N)
    st = Z.Statement(reg, "sk", [ct for ct, _, _ in batch], [sl] * len(batch), context(kind, call, tr, j))
    cu = STATE["cust"][j]
    wit = dict(s=cu.s, e_pk=cu.e, cts=[dict(e=e, r=[witness_r(Q, t, m[k]) for k in sl]) for _, m, e in batch])
    forged = STATE["attack"] == ("zk_off_layout", j) and kind == "mv" and call == 1
    t0 = time.time()
    blob = Z.prove(st, wit, T=STATE["T"], cheat=dict(forge=True) if forged else None)
    STATE["proofs"].setdefault(j, []).append([key[0], hashlib.sha256(blob).hexdigest()])
    for i in range(3):
        if i == j:
            continue
        # recipient i builds the statement from ITS expected context and j's registered key
        sti = Z.Statement(STATE["regs"][j], "sk", [ct for ct, _, _ in batch], [sl] * len(batch), context(kind, call, tr, j))
        ok, why = Z.verify(sti, blob, T=STATE["T"])
        if not ok:
            raise spdz.Abort(f"ZKPoPK gate: custodian {i} refused custodian {j}'s batch ({kind} call {call}): {why}")
    STATE["gate_seconds"] += time.time() - t0
    GATED.add(key)


def gated_ptxct(P, ct, Q):
    j = OWNER.get(id(ct))
    if j is None:
        raise spdz.Abort("ZKPoPK gate: a ciphertext no sender's batch proof covers")
    if (lbl(CUR["kind"], CUR["call"], CUR["tr"], j), j) not in GATED:
        gate(j)
    STATE["products"] += 1
    return _ptxct(P, ct, Q)


class GMatvec(HM.HEMatvec):
    def __call__(self, W, v, transpose=False):
        CUR.clear()
        CUR.update(kind="mv", call=self.calls + 1, tr=int(transpose), d=len(v))
        return super().__call__(W, v, transpose)


class GOuter(HO.HEOuter):
    def __call__(self, a, x):
        CUR.clear()
        CUR.update(kind="ou", call=self.calls + 1, tr=0, d1=len(a), d2=len(x))
        return super().__call__(a, x)


def run(N, L, F_bits, d, T, attack=None):
    Qp, t, Q = NR.setup(N, L)
    STATE.update(T=T, attack=attack)
    t0 = time.time()
    cer, cs = K.run_ceremony(1, 3, N, Qp, t, T)
    cer_s = time.time() - t0
    STATE["regs"] = [cer.registry(j) for j in range(3)]
    STATE["cust"] = cs
    keys = []
    for j in range(3):
        k = K.CeremonyKey(N, Q, t, cs[j], seed=NR.KEY_SEED0 + j)
        k.sch = GatedBFV(N, Q, t, NR.KEY_SEED0 + j, cs[j].s, j)
        keys.append(k)
    HM.ptxct = gated_ptxct
    tab = MF.tables(t)
    rng = random.Random(d)
    wm = NR.wmax_for(d)
    W1 = [[rng.randint(-wm, wm) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-wm, wm) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    m = lambda M: [[v % t for v in r] for r in M]
    dealer = spdz.Dealer(t, 3, NR.DEALER_SEED)
    eng = spdz.Engine(t, 3, dealer)
    noise = (N * (t // 2) * 32).bit_length()
    mv = GMatvec(eng, keys, N, Q, seed=NR.MV_SEED, flood_bits=F_bits - noise, per_return_rng=True)
    ou = GOuter(eng, keys, N, Q, seed=NR.OU_SEED, flood_bits=F_bits - (N * (t // 2) * 16 * 2).bit_length(),
                per_return_rng=True)
    gate_info = lambda: dict(T=T, ceremony_seed=cer.seed, ceremony_seconds=round(cer_s, 1),
                             key_b_sha256=[hashlib.sha256(Z.canonical(list(r.b))).hexdigest() for r in STATE["regs"]],
                             proofs={str(j): v for j, v in sorted(STATE["proofs"].items())},
                             gate_seconds=round(STATE["gate_seconds"], 1), products=STATE["products"])
    t1 = time.time()
    try:
        W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % t for v in x], [v % t for v in y], tab, NR.OWNER_SEED,
                                  mv=mv, ou=ou)
        sig = eng.mac_check("he")
    except spdz.Abort as e:
        return dict(verdict="REFUSED", by=str(e), transcript_len=len(eng.transcript), gate=gate_info())
    secs = time.time() - t1
    e1, e2, _ = S.step(W1, W2, x, y)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    H = lambda o: hashlib.sha256(repr(o).encode()).hexdigest()
    return dict(verdict="ACCEPT", refines_spec=rev(W1n) == e1 and rev(W2n) == e2, N=N, L=L, F_bits=F_bits, d=d, t=t,
                Q_primes=Qp, seconds=round(secs, 1), transcript_len=len(eng.transcript), transcript=H(eng.transcript),
                parties={i: H(([[c[i] for c in r] for r in W1n], [[c[i] for c in r] for r in W2n])) for i in range(3)},
                sigma={i: sig[i] for i in range(3)}, wire=dict(sorted(eng.wire.items())), gate=gate_info())


def main():
    args = [a for a in sys.argv[1:]]
    attack = None
    if "--attack" in args:
        k = args.index("--attack")
        kind, who = args[k + 1].split(":")
        attack = (kind, int(who))
        del args[k:k + 2]
    N, L, F_bits, d, T = (int(a) for a in args[:5])
    prefix = args[5] if len(args) > 5 else f"native_ref_gated_N{N}_L{L}_F{F_bits}_d{d}_T{T}" + (f"_{attack[0]}{attack[1]}" if attack else "")
    out = run(N, L, F_bits, d, T, attack)
    json.dump(out, open(prefix + ".json", "w"), indent=1)
    print(json.dumps(out), flush=True)


if __name__ == "__main__":
    main()
