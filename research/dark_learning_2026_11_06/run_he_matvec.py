"""The MPC fork with the HE-assisted matvec (he_matvec.py): honest step at d = 64 and d = 128 (two column
blocks: exercises the block sums), refinement of step_spec, falsifiers, and counts checked against
he_matvec.counts + step_counts.mpc_counts.

    python3 run_he_matvec.py          # writes he_matvec_results.json (build box: N = 8192 products)
"""
import json
import math
import random
import sys

import bfv_ref as bfv
import he_matvec as HM
import mpc_fork as MF
import spdz
import step_counts as SC
import step_spec as S

N = 8192

def run(d, wmax, attack=None, seed=3):
    p = bfv.ntt_primes(61, 4, 2 * N)[3]
    Qp = bfv.ntt_primes(61, 3, 2 * N)
    Q = math.prod(Qp)
    tab = MF.tables(p)
    rng = random.Random(d)
    W1 = [[rng.randint(-wmax, wmax) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-wmax, wmax) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    m = lambda M: [[v % p for v in r] for r in M]
    keys = [HM.OwnKey(N, Q, p, seed=100 + i) for i in range(3)]
    dealer = spdz.Dealer(p, 3, 5)
    eng = spdz.Engine(p, 3, dealer)
    mv = HM.HEMatvec(eng, keys, N, Q, attack=attack)
    try:
        W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % p for v in x], [v % p for v in y], tab, 9, mv=mv)
        eng.mac_check("he")
    except spdz.Abort as e:
        return dict(verdict="REFUSED", by=str(e))
    e1, e2, _ = S.step(W1, W2, x, y)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    refines = rev(W1n) == e1 and rev(W2n) == e2
    # the executed step uses step_spec's fixed shifts (S1 = 5 ...), not the widened recipe of step_counts
    base = SC.mpc_counts(d, P=dict(S1=S.S1, K1=13, S2=S.S2, K2=8, S3=S.S3, K3=13))
    hc = HM.counts(d, N)
    wire = sum(eng.wire.values()) + mv.wire["he_send"] + mv.wire["he_return"]
    want_wire = base["online_wire"] - 3 * (d * d + d) * 6 + hc["he_wire"] + hc["spdz_wire"]
    want_prep = base["preprocessing_auth_values"] - 3 * (d * d + 2 * d) + hc["prep_auth_values"]
    return dict(verdict="ACCEPT" if refines else "FAIL", refines_spec=refines,
                counts=dict(online_wire=wire, he_send=mv.wire["he_send"], he_return=mv.wire["he_return"],
                            spdz_wire=sum(eng.wire.values()), prep_auth_values=dealer.count,
                            cts_sent=mv.cts_sent, cts_returned=mv.cts_returned),
                formula=dict(online_wire=want_wire, step_prep_auth_values=want_prep, **hc),
                formula_exact=(wire == want_wire and dealer.count == want_prep
                               and mv.cts_sent == hc["cts_sent"] and mv.cts_returned == hc["cts_returned"]),
                spdz_matvec_step_wire=base["online_wire"])

def main():
    out = {}
    which = sys.argv[1:] or ["64", "128", "attacks"]
    if "64" in which:
        out["d64"] = run(64, 7)
        print("d64", json.dumps(out["d64"]), flush=True)
    if "128" in which:
        out["d128"] = run(128, 2)
        print("d128", json.dumps(out["d128"]), flush=True)
    if "attacks" in which:
        for att in (("wrong_vector", 1), ("wrong_return", 2), ("shift_share", 0)):
            r = run(64, 7, attack=att)
            out["attack_" + att[0]] = dict(verdict=r["verdict"], by=r.get("by"))
            print(att, r["verdict"], r.get("by"), flush=True)
    d = 4096
    base = SC.mpc_counts(d)
    hc = HM.counts(d, N)
    st = base["steady"]["online_wire"] - 3 * (d * d + d) * 6 + hc["he_wire"] + hc["spdz_wire"]
    out["d4096_formula"] = dict(he=hc, mpc_steady_online_wire_spdz_matvec=base["steady"]["online_wire"],
                                mpc_steady_online_wire_he_matvec=st)
    print("d4096", st, hc, flush=True)
    json.dump(out, open("he_matvec_results.json" if len(which) == 3 else f"he_matvec_results_{'_'.join(which)}.json", "w"),
              indent=1, default=str)

if __name__ == "__main__":
    main()
