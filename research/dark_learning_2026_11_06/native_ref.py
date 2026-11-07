"""The bit-exact reference for the native custodians (native/darkstep): one MPC step (SPDZ online phase, HE matvec +
HE outer, MAC check) at a given HE profile, with seeded keys, an ideal dealer and per-return HE randomness
(he_matvec/he_outer per_return_rng=True, the mode a distributed custodian can run). Prints one JSON line of digests and
writes the public transcript, one repr per line, so a native run can be diffed entry by entry.

    python3 native_ref.py N L F_bits d [out_prefix] [--program GEN6]   # e.g. 4096 3 118 64; ledger: 16384 4 175 64
    (--program: a step_spec program by name; the inputs are then inputs_for(d, prog), darkstep step::inputs_for)

Digests (all sha256 hex of CPython repr):
  transcript   repr(eng.transcript)
  party_i      repr((W1n_i, W2n_i)), W*n_i = [[(share, mac), ...], ...] (party i's final authenticated shares)
  sigma        the MAC check's sigma_i per party
"""
import hashlib
import json
import math
import os
import random
import sys
import time

import bfv_ref as bfv
import he_matvec as HM
import he_outer as HO
import mpc_fork as MF
import spdz
import wire_round as WR
import step_spec as S

DEALER_SEED, OWNER_SEED, KEY_SEED0, MV_SEED, OU_SEED = 5, 9, 100, 11, 13


def setup(N, L):
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    Qp, t = pr[:L], pr[L]
    return Qp, t, math.prod(Qp)


def wmax_for(d):
    """Weights in [-wmax, wmax]: 7 up to d = 64; wider layers need smaller weights so u1 = z1 >> 5 stays inside the
    table's domain [-128, 128) (step_spec asserts it). Mirrors native/darkstep step::wmax_for."""
    return 7 if d <= 64 else 2 if d <= 256 else 1


def inputs_for(d, prog):
    """darkstep step::inputs_for: the harness inputs for HARNESS; otherwise weights scaled to the program, redrawn
    from random.Random(d + k) until step_spec accepts them and both layers update."""
    if prog == S.HARNESS:
        rng = random.Random(d)
        wm = wmax_for(d)
        W1 = [[rng.randint(-wm, wm) for _ in range(d)] for _ in range(d)]
        W2 = [[rng.randint(-wm, wm) for _ in range(d)] for _ in range(d)]
        x = [rng.randint(-7, 7) for _ in range(d)]
        y = [rng.randint(-7, 7) for _ in range(d)]
        return W1, W2, x, y
    sd = math.sqrt(d)
    a1 = int(max((16.0 * float(1 << prog.S1) * 1.732) / (4.3 * sd), 1.0))
    a2 = int(max((32.0 * float(1 << prog.S1) * 1.732) / (4.0 * sd), 1.0))
    for k in range(64):
        rng = random.Random(d + k)
        W1 = [[rng.randint(-a1, a1) for _ in range(d)] for _ in range(d)]
        W2 = [[rng.randint(-a2, a2) for _ in range(d)] for _ in range(d)]
        x = [rng.randint(-7, 7) for _ in range(d)]
        y = [rng.randint(-7, 7) for _ in range(d)]
        try:
            n1, n2, _ = S.step(W1, W2, x, y, prog)
        except AssertionError:
            continue
        if n1 != W1 and n2 != W2:
            return W1, W2, x, y
    raise ValueError("inputs_for: no in-bound inputs")


def run(N, L, F_bits, d, attack=None, prog=S.HARNESS):
    Qp, t, Q = setup(N, L)
    keys = [HM.OwnKey(N, Q, t, seed=KEY_SEED0 + i) for i in range(3)]
    tab = MF.tables(t, prog)
    W1, W2, x, y = inputs_for(d, prog)
    m = lambda M: [[v % t for v in r] for r in M]
    dealer = spdz.Dealer(t, 3, DEALER_SEED)
    eng = spdz.Engine(t, 3, dealer)
    noise = (N * (t // 2) * 32).bit_length()
    # DL_WIRE=round: the deploy lane's switched, noise-rounded returns (wire_round.py; outputs unchanged)
    wire = None
    if os.environ.get("DL_WIRE", "").startswith("round"):
        b0, b1 = WR.round_bits(Qp, N, t, F_bits)
        extra = os.environ["DL_WIRE"][len("round"):]
        if extra:
            b0, b1 = b0 + int(extra.split(",")[0]), b1 + int(extra.split(",")[1])
        wire = (Qp, b0, b1)
        print("wire", wire[1:], file=sys.stderr)
    mv = HM.HEMatvec(eng, keys, N, Q, seed=MV_SEED, flood_bits=F_bits - noise, per_return_rng=True, wire=wire,
                     attack=attack if attack and attack[0] == "mv_wrong_return" and False else None)
    ou = HO.HEOuter(eng, keys, N, Q, seed=OU_SEED, flood_bits=F_bits - (N * (t // 2) * 16 * 2).bit_length(),
                    per_return_rng=True, attack=attack, wire=wire)
    t0 = time.time()
    try:
        W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % t for v in x], [v % t for v in y], tab, OWNER_SEED,
                                  mv=mv, ou=ou, prog=prog)
        sig = eng.mac_check("he")
        verdict = "ACCEPT"
    except spdz.Abort as e:
        return dict(verdict="REFUSED", by=str(e), transcript_len=len(eng.transcript)), eng
    secs = time.time() - t0
    e1, e2, _ = S.step(W1, W2, x, y, prog)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    refines = rev(W1n) == e1 and rev(W2n) == e2
    H = lambda o: hashlib.sha256(repr(o).encode()).hexdigest()
    out = dict(verdict=verdict, refines_spec=refines, N=N, L=L, F_bits=F_bits, d=d, t=t, Q_primes=Qp,
               seconds=round(secs, 1), transcript_len=len(eng.transcript), transcript=H(eng.transcript),
               parties={i: H(([[c[i] for c in r] for r in W1n], [[c[i] for c in r] for r in W2n])) for i in range(3)},
               sigma={i: sig[i] for i in range(3)}, wire=dict(sorted(eng.wire.items())),
               he_wire=dict(mv=mv.wire, ou=ou.wire), cts=dict(mv_sent=mv.cts_sent, mv_ret=mv.cts_returned,
                                                             ou_sent=ou.cts_sent, ou_ret=ou.cts_returned))
    return out, eng


def main():
    args = sys.argv[1:]
    pname = None
    if "--program" in args:
        i = args.index("--program")
        pname = args[i + 1]
        del args[i:i + 2]
    prog = getattr(S, pname) if pname else S.HARNESS
    N, L, F_bits, d = (int(a) for a in args[:4])
    suffix = f"_{pname}" if pname else ""
    prefix = args[4] if len(args) > 4 else f"native_ref_N{N}_L{L}_F{F_bits}_d{d}{suffix}"
    out, eng = run(N, L, F_bits, d, prog=prog)
    if pname:
        out["program"] = prog.as_dict()
    with open(prefix + ".transcript.txt", "w") as f:
        for e in eng.transcript:
            f.write(repr(e) + "\n")
    json.dump(out, open(prefix + ".json", "w"), indent=1)
    print(json.dumps(out), flush=True)


if __name__ == "__main__":
    main()
