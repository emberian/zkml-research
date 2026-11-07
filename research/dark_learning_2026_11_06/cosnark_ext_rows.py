"""Refusal rows for the F_{p^2} challenges (cosnark_ext), on the spine (cosnark_zk) at a small width.

    python3 cosnark_ext_rows.py [d]          (default d = 8; profiles demo and demo-x2)

Rows, for EXT = 1 (control) and EXT = 2: the honest proof accepted; the full-collusion forgeries of
run_cosnark_zk.py (forged W1n, z1, a sumcheck whose hidden round messages are shifted to match a forged claim, a lie
in an evaluation row) refused; and, for EXT = 2, tampering with a second component (a Ligero message's u-part, a
PCS proximity combination's u-part) refused, and an EXT = 2 proof verified under EXT = 1 parameters (and the
reverse) refused.
"""
import copy
import sys

import cosnark_ext as X
import cosnark_zk as ZK
import proofwire as PW
from run_cosnark_zk import inputs, step

def rows(d, prof):
    PW.set_profile(prof)
    p = PW.he_field()
    import mpc_fork as MF
    tab = MF.tables(p)
    ctx = ("model", 0, 1)
    W1, W2, x, y = inputs(p, d)
    out = []
    def rec(name, okwhy):
        ok, why = okwhy
        out.append((prof, name, "ACCEPT" if ok else "REFUSED", why))
        print(f"{prof:9s} {name:44s} {'ACCEPT' if ok else 'REFUSED':8s} {why}", flush=True)
    eng, w = step(p, tab, W1, W2, x, y)
    proof, st = ZK.prove_zk(eng, w, context=ctx)
    V = lambda pr: ZK.verify_zk(p, 3, d, ctx, None, False, pr)
    rec("honest", V(proof))
    for att in ("forge_W1n", "forge_z1", "forge_sumcheck", "lie_in_u"):
        e2, w2 = step(p, tab, W1, W2, x, y)
        pr2, st2 = ZK.prove_zk(e2, w2, attack=att, context=ctx)
        rec(f"{att} (violates: {st2['first_violated']})", V(pr2))
    if X.EXT == 2:
        t = copy.deepcopy(proof)
        t["ligero"]["w1"][3] = (t["ligero"]["w1"][3] + 1) % p
        rec("Ligero proximity message, u-part +1", V(t))
        t = copy.deepcopy(proof)
        t["ligero"]["q1"][0] = (t["ligero"]["q1"][0] + 1) % p
        rec("Ligero linear message, u-part +1", V(t))
        t = copy.deepcopy(proof)
        k0 = sorted(t["prox"])[0]
        W = len(t["prox"][k0][0]) // 2
        t["prox"][k0][0][W] = (t["prox"][k0][0][W] + 1) % p
        rec(f"PCS proximity {k0}, u-part +1", V(t))
        t = copy.deepcopy(proof)
        for kk in ("w1", "q1", "pq1"):
            del t["ligero"][kk]
        rec("u-parts dropped (an EXT = 1 shaped Ligero)", V(t))
    return proof

def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    pr1 = rows(d, "demo")
    pr2 = rows(d, "demo-x2")
    # cross-profile: each proof under the other's parameters
    p = PW.he_field()
    ctx = ("model", 0, 1)
    PW.set_profile("demo")
    try:
        ok, why = ZK.verify_zk(p, 3, d, ctx, None, False, pr2)
    except Exception as e:
        ok, why = False, f"{type(e).__name__}: {e}"
    print(f"{'cross':9s} {'EXT = 2 proof under EXT = 1':44s} {'ACCEPT' if ok else 'REFUSED':8s} {why}")
    PW.set_profile("demo-x2")
    try:
        ok, why = ZK.verify_zk(p, 3, d, ctx, None, False, pr1)
    except Exception as e:
        ok, why = False, f"{type(e).__name__}: {e}"
    print(f"{'cross':9s} {'EXT = 1 proof under EXT = 2':44s} {'ACCEPT' if ok else 'REFUSED':8s} {why}")

if __name__ == "__main__":
    main()
