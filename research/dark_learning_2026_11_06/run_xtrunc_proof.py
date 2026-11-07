"""Exact truncation in the collaborative proof (program flag "XT"; notes/dark-learning-gen6/xtrunc.md): the refusal
rows. One deployed step (cosnark_he, HE matvec and outer) at d = 4 on a profile (default demo-x2de), program RC + LB +
RS + XT, under DL_DETERMINISTIC (cosnark.det_rng).

    DL_DETERMINISTIC=7 python3 run_xtrunc_proof.py [profile]

Rows:
  honest        XT step, proved, the verifier ACCEPTS
  xt_wrap       the first truncation's mask wraps (c = 0) and the custodians do not redo the step:
                (a) the custodians' masked range zero test refuses to prove;
                (b) the bundle forced past it: the verifier refuses by name (the public check c >= 2^(K+1));
                (c) the same bundle with the public check bypassed (in this process only): the Ligero test refuses
  borrow_flip   the first e truncation's low-bit comparison flipped (d2 off by one), MAC-consistently: the MAC check passes and the
                verifier refuses (Ligero linear test)
"""
import os
import sys

import cosnark_gates as G
import cosnark_gates_zk as GZ
import cosnark_he as CH
import cosnark_zk as ZK
import darkproof_vectors as DV
import he_matvec as HM
import he_outer as HO
import mpc_fork as MF
import native_ref as NR
import proofwire as PW
import run_proofwire as RP
import spdz

PROGRAM = dict(DV.HE_PROGRAM, RC=True, LB=True, RS=True, XT=True)


def one(attack, d=4, ignore_range=False, bypass_public=False):
    he = PW.PARAMS["HE"]
    N, L, F = he["N"], he["L"], he["F_BITS"]
    Qp, t, Q = NR.setup(N, L)
    p = t
    keys = [HM.OwnKey(N, Q, t, seed=NR.KEY_SEED0 + i) for i in range(3)]
    prog = CH.Prog.of(PROGRAM)
    tab = prog.tables(p)
    import random
    rng = random.Random(d)
    wm = NR.wmax_for(d)
    W1 = [[rng.randint(-wm, wm) % p for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-wm, wm) % p for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) % p for _ in range(d)]
    y = [rng.randint(-7, 7) % p for _ in range(d)]
    dealer = spdz.Dealer(p, 3, NR.DEALER_SEED)
    live = G.RecEngine(p, 3, dealer, attack=attack)
    noise = (N * (t // 2) * 32).bit_length()
    mv = CH.LiveHE(live, HM.HEMatvec(live, keys, N, Q, seed=NR.MV_SEED, flood_bits=F - noise, per_return_rng=True))
    ou = CH.LiveHE(live, HO.HEOuter(live, keys, N, Q, seed=NR.OU_SEED, flood_bits=F - (N * (t // 2) * 16 * 2).bit_length(),
                                    per_return_rng=True), outer=True)
    W1n, W2n, wires = CH.run_step(live, W1, W2, x, y, tab, NR.OWNER_SEED, mv, ou, prog=prog)
    live.mac_check("he")                      # every row below passes the MAC check
    wires.update(W1n=W1n, W2n=W2n)
    public = [v for _, _, v in live.transcript]
    carry = RP.genesis_commit(p, wires)
    parent = {k: carry[k].roots for k in ("W1", "W2")}
    ctx = ("mind-0", 0, 1)
    spine, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, carry=carry, context=ctx, public=public)
    sym = CH.replay(p, public, d, tab, prog)
    middle, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx, ignore_range=ignore_range)
    if middle is None:
        return "custodians refuse: " + mst["error"]
    blob = PW.encode_step(p, ctx, d, 3, True, spine, public, middle, sym)
    orig = G.append_range
    if bypass_public:
        def no_public(eng):
            orig(eng)
            eng.range_fail[:] = [f for f in eng.range_fail if "XT wrap zone" not in f[0]]
        G.append_range = no_public
    try:
        ok, why, _ = PW.verify_step(p, blob, ctx, parent, tab, d, program=PROGRAM)
    finally:
        G.append_range = orig
    return ("ACCEPT" if ok else "REFUSED: " + why), len(blob)


ROWS = {"honest": (None, {}), "xt_wrap_a": ("xt_wrap", {}), "xt_wrap_b": ("xt_wrap", dict(ignore_range=True)),
        "xt_wrap_c": ("xt_wrap", dict(ignore_range=True, bypass_public=True)), "borrow_flip": ("borrow_flip", {})}


def expect(name, res):
    r = res if isinstance(res, str) else res[0]
    if name == "honest":
        return r == "ACCEPT"
    if name == "xt_wrap_a":
        return r.startswith("custodians refuse: proving refused: truncation input outside its proved bound")
    if name == "xt_wrap_b":
        return r.startswith("REFUSED") and "XT wrap zone" in r
    return r.startswith("REFUSED") and "Ligero" in r


def main():
    """args: [profile] [row ...] (default: every row, in this process)."""
    assert os.environ.get("DL_DETERMINISTIC") is not None, "set DL_DETERMINISTIC"
    prof = sys.argv[1] if len(sys.argv) > 1 else "demo-x2de"
    names = sys.argv[2:] or list(ROWS)
    PW.set_profile(prof + DV.DOMAIN_SUFFIX)
    ok = True
    for name in names:
        attack, kw = ROWS[name]
        res = one(attack, **kw)
        good = expect(name, res)
        ok &= good
        print(f"{name:12s} {'AS EXPECTED' if good else 'UNEXPECTED'}  {res}", flush=True)
    print("ALL XT PROOF ROWS AS EXPECTED" if ok else "SOME XT PROOF ROW UNEXPECTED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
