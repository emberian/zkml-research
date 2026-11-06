"""ZK layers 2-3 for the collaborative proof's spine (cosnark_zk.py): honest steps at d = 16, 32, 64, the
full-collusion forgeries with the check each one violates, a two-step chain with carried commitments, a stale
parent, a replayed proof, and the count formula checked against the executed proofs.

    python3 run_cosnark_zk.py          # writes cosnark_zk_results.json (a few minutes)
"""
import json
import random

import bfv_ref as bfv
import cosnark as CS
import cosnark_zk as ZK
import mpc_fork as MF
import spdz

CS.HIDE, CS.NMASK = CS.LIVES * CS.T_COLS, CS.LIVES        # layer-1 tails; one proximity mask per life

def step(p, tab, W1, W2, x, y, seed=5):
    eng = spdz.Engine(p, 3, spdz.Dealer(p, 3, seed))
    W1n, W2n, w = MF.run_step(eng, W1, W2, x, y, tab, 9)
    eng.mac_check("s")
    w.update(W1n=W1n, W2n=W2n)
    return eng, w

def inputs(p, d):
    rng = random.Random(d)
    M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    return M(), M(), [rng.randint(-7, 7) % p for _ in range(d)], [rng.randint(-7, 7) % p for _ in range(d)]

def main():
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    ctx = ("model", 0, 1)
    out = dict(formula_check={}, rows={})
    for d in (16, 32, 64):
        W1, W2, x, y = inputs(p, d)
        eng, w = step(p, tab, W1, W2, x, y)
        proof, st = ZK.prove_zk(eng, w, context=ctx)
        ok, why = ZK.verify_zk(p, 3, d, ctx, None, False, proof)
        f = ZK.counts_formula(d)
        got = {kk: st[kk] for kk in f if kk in st}
        got["proof"] = ZK.measure(proof, 3)
        mism = [kk for kk in got if got[kk] != f[kk]]
        out["formula_check"][d] = dict(honest=(ok, why), exact=not mism, mismatches=mism, counts=got)
        print(d, ok, why, "formula", "EXACT" if not mism else mism, got["proof"], flush=True)
        if d != 64:
            continue
        for att in ("forge_W1n", "forge_z1", "forge_sumcheck", "lie_in_u"):
            e2, w2 = step(p, tab, W1, W2, x, y)
            pr2, st2 = ZK.prove_zk(e2, w2, attack=att, context=ctx)
            ok2, why2 = ZK.verify_zk(p, 3, d, ctx, None, False, pr2)
            out["rows"][att] = dict(verdict="ACCEPT" if ok2 else "REFUSED", by=why2, violates=st2["first_violated"])
            print(att, ok2, why2, "|", st2["first_violated"], flush=True)
        ok5, why5 = ZK.verify_zk(p, 3, d, ("model", 0, 2), None, False, proof)
        out["rows"]["replayed_as_next_step"] = dict(verdict="ACCEPT" if ok5 else "REFUSED", by=why5)
        print("replay", ok5, why5, flush=True)
    # two-step chain at d = 16: step 2's W commitments are step 1's child commitments, carried
    d = 16
    W1, W2, x, y = inputs(p, d)
    eng, w = step(p, tab, W1, W2, x, y)
    pr1, st1 = ZK.prove_zk(eng, w, context=("model", 0, 1))
    child = {k: st1["child"][k].roots for k in ("W1", "W2")}
    dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
    e3, w3 = step(p, tab, dec(w["W1n"]), dec(w["W2n"]), x, y)
    for k_old, k_new in (("W1n", "W1"), ("W2n", "W2")):
        w3[k_new] = w[k_old]
    pr3, _ = ZK.prove_zk(e3, w3, carry=st1["child"], context=("model", 0, 2))
    ok3, why3 = ZK.verify_zk(p, 3, d, ("model", 0, 2), child, True, pr3)
    stale = {k: pr1["roots"][k] for k in ("W1", "W2")}
    ok4, why4 = ZK.verify_zk(p, 3, d, ("model", 0, 2), stale, True, pr3)
    out["rows"]["chain_step2"] = dict(verdict="ACCEPT" if ok3 else "REFUSED", by=why3)
    out["rows"]["stale_parent"] = dict(verdict="ACCEPT" if ok4 else "REFUSED", by=why4)
    print("chain", ok3, why3, "| stale", ok4, why4, flush=True)
    # what ZK costs at width (formulas validated above); layer 1 alone for comparison
    out["d4096"] = dict(zk_layers_1_2_3=ZK.counts_formula(4096),
                        layer1_only=CS.counts_formula(4096, hide=CS.LIVES * CS.T_COLS, nmask=CS.LIVES * 4))
    json.dump(out, open("cosnark_zk_results.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
