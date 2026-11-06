"""The MPC fork's collaborative proof (cosnark.py) on the d = 64 step: honest, full-collusion attacks, a
two-step chain with a stale parent, and the count formula checked against the executed runs.

    python3 run_cosnark.py        # writes cosnark_results.json
"""
import json
import random

import bfv_ref as bfv
import cosnark as CS
import mpc_fork as MF
import spdz
import step_spec as S

def step(p, tab, W1, W2, x, y, seed):
    eng = spdz.Engine(p, 3, spdz.Dealer(p, 3, seed))
    W1n, W2n, wires = MF.run_step(eng, W1, W2, x, y, tab, 9)
    eng.mac_check("s")
    wires.update(W1n=W1n, W2n=W2n)
    return eng, wires

def main():
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    out = dict(formula_check={}, rows={})
    for d in (16, 32, 64):
        rng = random.Random(d)
        M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
        W1, W2 = M(), M()
        x = [rng.randint(-7, 7) % p for _ in range(d)]
        y = [rng.randint(-7, 7) % p for _ in range(d)]
        eng, wires = step(p, tab, W1, W2, x, y, 5)
        ok, why, c = CS.prove_and_verify(eng, wires)
        f = CS.counts_formula(d)
        same = {k: c[k] == f[k] for k in f}
        out["formula_check"][d] = dict(honest=(ok, why), all_equal=all(same.values()),
                                      mismatches=[k for k, v in same.items() if not v])
        print(d, ok, why, "formula", "EXACT" if all(same.values()) else same, flush=True)
        if d != 64:
            continue
        out["counts_d64"] = {k: v for k, v in c.items() if k != "child_roots"}
        out["rows"]["honest"] = dict(verdict="ACCEPT" if ok else "FAIL", by=why)
        for att, what in (("forge_W1n", "all custodians commit a wrong W1' (one entry +1)"),
                          ("forge_z1", "all custodians commit a wrong z1 and prove honestly"),
                          ("forge_sumcheck", "wrong z1, and the colluders forge every sumcheck round"),
                          ("lie_in_u", "wrong W1' committed; custodian 0 reports its honest share's row combination")):
            e2, w2 = step(p, tab, W1, W2, x, y, 5)
            ok2, why2, _ = CS.prove_and_verify(e2, w2, attack=att)
            out["rows"][att] = dict(what=what, verdict="ACCEPT" if ok2 else "REFUSED", by=why2)
            print(att, ok2, why2, flush=True)
        # two-step chain: step 2 starts from step 1's new weights; its parent is step 1's child commitment
        dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
        W1b, W2b = dec(wires["W1n"]), dec(wires["W2n"])
        # The custodians carry their step-1 shares of W' into step 2 (same MAC key: same dealer seed), so the
        # step-2 commitment to W must equal step 1's child commitment. The step-2 protocol runs on a fresh
        # sharing of the same values, and the prover is handed the carried shares for W1, W2.
        e3, w3 = step(p, tab, W1b, W2b, x, y, 5)
        for k_old, k_new in (("W1n", "W1"), ("W2n", "W2")):
            w3[k_new] = wires[k_old]
        ok3, why3, _ = CS.prove_and_verify(e3, w3, parent=c["child_roots"])
        out["rows"]["chain_step2_parent_is_step1_child"] = dict(verdict="ACCEPT" if ok3 else "REFUSED", by=why3)
        stale = {"W1": out_parent_roots(p, wires, "W1"), "W2": out_parent_roots(p, wires, "W2")}
        ok4, why4, _ = CS.prove_and_verify(e3, w3, parent=stale)
        out["rows"]["stale_parent"] = dict(what="step 2 verified against step 1's PARENT (an older W)",
                                           verdict="ACCEPT" if ok4 else "REFUSED", by=why4)
        print("chain", ok3, why3, "| stale", ok4, why4, flush=True)
    out["formula_d4096"] = dict(spine=CS.counts_formula(4096), spine_t148=CS.counts_formula(4096, t=148),
                                elementwise_MODEL=CS.unbuilt_formula(4096, 11, 4, 14),
                                elementwise_MODEL_d64=CS.unbuilt_formula(64, S.S1, S.S2, S.S3))
    json.dump(out, open("cosnark_results.json", "w"), indent=1, default=str)

def out_parent_roots(p, wires, k):
    sh = [[v[i][0] for r in wires[k] for v in r] for i in range(3)]
    return CS.SharePCS(p, sh, k).roots

if __name__ == "__main__":
    main()
