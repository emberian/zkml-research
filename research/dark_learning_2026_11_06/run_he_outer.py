"""The MPC fork with BOTH HE helpers (he_matvec.py + he_outer.py): honest step at d = 64 and d = 128, refinement
of step_spec, the attack list, a full-collusion forgery handed to the collaborative proof's spine, and the count
formula checked against execution.

    python3 run_he_outer.py [64] [128] [attacks]      # build box: N = 8192 products
"""
import json
import math
import random
import sys

import bfv_ref as bfv
import cosnark as CS
import he_matvec as HM
import he_outer as HO
import mpc_fork as MF
import spdz
import step_counts as SC
import step_spec as S

N = 8192

def setup():
    p = bfv.ntt_primes(61, 4, 2 * N)[3]
    Q = math.prod(bfv.ntt_primes(61, 3, 2 * N))
    keys = [HM.OwnKey(N, Q, p, seed=100 + i) for i in range(3)]
    return p, Q, keys

def run(d, wmax, attack=None, he_mv=True, spine=False, ctx=None):
    p, Q, keys = ctx or setup()
    tab = MF.tables(p)
    rng = random.Random(d)
    W1 = [[rng.randint(-wmax, wmax) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-wmax, wmax) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    m = lambda M: [[v % p for v in r] for r in M]
    dealer = spdz.Dealer(p, 3, 5)
    eng = spdz.Engine(p, 3, dealer)
    mv = HM.HEMatvec(eng, keys, N, Q) if he_mv else None
    ou = HO.HEOuter(eng, keys, N, Q, attack=attack)
    try:
        W1n, W2n, wires = MF.run_step(eng, m(W1), m(W2), [v % p for v in x], [v % p for v in y], tab, 9, mv=mv, ou=ou)
        eng.mac_check("he")
    except spdz.Abort as e:
        return dict(verdict="REFUSED", by=str(e))
    e1, e2, _ = S.step(W1, W2, x, y)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    refines = rev(W1n) == e1 and rev(W2n) == e2
    out = dict(verdict="ACCEPT" if refines else "ACCEPTED-WRONG", refines_spec=refines)
    if spine:
        wires.update(W1n=W1n, W2n=W2n)
        ok, why, _ = CS.prove_and_verify(eng, wires)
        out["spine"] = dict(verdict="ACCEPT" if ok else "REFUSED", by=why)
    if not he_mv:
        return out
    base = SC.mpc_counts(d, P=dict(S1=S.S1, K1=13, S2=S.S2, K2=8, S3=S.S3, K3=13))
    hm, ho = HM.counts(d, N), HO.counts(d, N)
    wire = sum(eng.wire.values()) + sum(mv.wire.values()) + sum(ou.wire.values())
    want_wire = (base["online_wire"] - 3 * (d * d + d) * 6 + hm["he_wire"] + hm["spdz_wire"]
                 - ho["replaces_spdz_outer_wire"] + ho["he_wire"] + ho["spdz_wire"])
    want_prep = (base["preprocessing_auth_values"] - 3 * (d * d + 2 * d) + hm["prep_auth_values"]
                 - ho["replaces_prep_auth_values"] + ho["prep_auth_values"])
    got = dict(online_wire=wire, prep_auth_values=dealer.count, outer_cts_sent=ou.cts_sent,
               outer_cts_returned=ou.cts_returned, matvec_cts_sent=mv.cts_sent, matvec_cts_returned=mv.cts_returned)
    want = dict(online_wire=want_wire, prep_auth_values=want_prep, outer_cts_sent=ho["cts_sent"],
                outer_cts_returned=ho["cts_returned"], matvec_cts_sent=hm["cts_sent"],
                matvec_cts_returned=hm["cts_returned"])
    out.update(counts=got, formula=want, formula_exact=got == want)
    return out

def main():
    which = sys.argv[1:] or ["64", "128", "attacks"]
    ctx = setup()
    out = {}
    if "64" in which:
        out["d64"] = run(64, 7, ctx=ctx)
        print("d64", json.dumps(out["d64"]), flush=True)
    if "128" in which:
        out["d128"] = run(128, 2, ctx=ctx)
        print("d128", json.dumps(out["d128"]), flush=True)
    if "attacks" in which:
        # the outer product is what is under test; the matvec's own attacks are in run_he_matvec.py
        for att in (("wrong_vector", 1), ("wrong_return", 2), ("wrong_mac_return", 0), ("shift_share", 1),
                    ("collude", 0)):
            r = run(64, 7, attack=att, he_mv=False, spine=(att[0] == "collude"), ctx=ctx)
            out["attack_" + att[0]] = r
            print(att, json.dumps(r), flush=True)
    json.dump(out, open(f"he_outer_results_{'_'.join(which)}.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
