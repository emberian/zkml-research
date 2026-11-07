"""The MPC fork's d = 64 step (both HE helpers) on REAL preprocessing tapes (native/darkprep: MASCOT over MP-SPDZ),
checked against step_spec, with the MAC check; negative controls on corrupted tapes.

    python3 run_tape_step.py TAPE_DIR [honest] [mac] [share] [tag]

  honest  the step on the tapes: must refine step_spec, pass every HE check and the MAC check, consume every entry
  mac     TAPE_DIR_mac:   one MAC share flipped (party 1, a "ta" of the first Freivalds product): MAC check aborts
  share   TAPE_DIR_share: one share flipped (party 2, the last "trh"): the value is wrong, only the MAC check sees it
  tag     TAPE_DIR_tag:   one tag changed: the tape refuses at that entry
HE profile = the ledger's: N = 16384, L = 4, p = ntt_primes(61, L + 1, 2N)[L] (the tapes' prime).
"""
import json
import math
import random
import sys
import time

import bfv_ref as bfv
import he_matvec as HM
import he_outer as HO
import mpc_fork as MF
import spdz
import step_spec as S
import tape_dealer as TD

N, L = 16384, 4

def setup():
    p = bfv.ntt_primes(61, L + 1, 2 * N)[L]
    Q = math.prod(bfv.ntt_primes(61, L, 2 * N))
    keys = [HM.OwnKey(N, Q, p, seed=100 + i) for i in range(3)]
    return p, Q, keys

def run(tape_dir, ctx, d=64, wmax=7):
    p, Q, keys = ctx
    dealer = TD.TapeDealer(tape_dir)
    assert dealer.p == p, (dealer.p, p)
    assert dealer.meta["d"] == d and dealer.meta["mode"] == 0, dealer.meta
    tab = MF.tables(p)
    rng = random.Random(d)
    W1 = [[rng.randint(-wmax, wmax) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-wmax, wmax) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    m = lambda M: [[v % p for v in r] for r in M]
    eng = TD.TapeEngine(p, 3, dealer)
    mv = HM.HEMatvec(eng, keys, N, Q)
    ou = HO.HEOuter(eng, keys, N, Q)
    t0 = time.time()
    try:
        W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % p for v in x], [v % p for v in y], tab, 9, mv=mv, ou=ou)
    except spdz.Abort as e:
        return dict(verdict="REFUSED", stage="online", by=str(e), consumed=dealer.pos, secs=round(time.time() - t0))
    e1, e2, _ = S.step(W1, W2, x, y)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    refines = rev(W1n) == e1 and rev(W2n) == e2
    try:
        eng.mac_check("tape")
    except spdz.Abort as e:
        return dict(verdict="REFUSED", stage="mac_check", by=str(e), refines_spec=refines, consumed=dealer.pos,
                    secs=round(time.time() - t0))
    return dict(verdict="ACCEPT" if refines else "ACCEPTED-WRONG", refines_spec=refines, consumed=dealer.pos,
                tape_entries=len(dealer.tapes[0]), exhausted=dealer.exhausted(), prep_auth_values=dealer.count,
                commitments=dealer.commitments(), secs=round(time.time() - t0))

def main():
    tape_dir = sys.argv[1]
    which = sys.argv[2:] or ["honest", "mac", "share", "tag"]
    ctx = setup()
    out = {}
    for w in which:
        r = run(tape_dir if w == "honest" else f"{tape_dir}_{w}", ctx)
        out[w] = r
        print(w, json.dumps(r), flush=True)
    json.dump(out, open(f"tape_step_results_{'_'.join(which)}.json", "w"), indent=1)

if __name__ == "__main__":
    main()
