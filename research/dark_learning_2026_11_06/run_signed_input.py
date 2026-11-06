"""Signed-input binding (ePrint 2026/2721's input authentication, adapted): the data owner commits each batch
(x, y) as a share tuple, signs (model, epoch, step, roots) with a hash-based one-time key (leaf = step), and the
step proof binds the custodians' x and y to those commitments. Fully colluding custodians cannot choose the data.

    python3 run_signed_input.py [d]      # default d = 4; writes signed_input_results_d{d}.json
"""
import json
import os
import random
import sys
import tempfile

import bfv_ref as bfv
import cosnark as CS
import cosnark_gates as G
import cosnark_gates_zk as GZ
import cosnark_zk as ZK
import mpc_fork as MF
import owner_sig as OS
import proofwire as PW
import run_proofwire as RP
import spdz

def bundle(p, tab, d, W1, W2, x_mpc, y_mpc, ctx, owner, x_signed, y_signed, carry=None, carry_wires=None,
           signer=None, sign_ctx=None):
    """The MPC runs on (x_mpc, y_mpc); the owner commits and signs (x_signed, y_signed); an honest run has them
    equal. signer: sign with another key; sign_ctx: sign for another context."""
    if sign_ctx is None:
        return RP.make_bundle(p, tab, d, W1, W2, x_mpc, y_mpc, ctx, carry=carry, carry_wires=carry_wires,
                              owner=signer or owner, signed=(x_signed, y_signed))
    # replay: an old signature (made for sign_ctx) attached to a proof for ctx
    old = RP.make_bundle(p, tab, d, W1, W2, x_mpc, y_mpc, sign_ctx, carry=carry, carry_wires=carry_wires,
                         owner=owner, signed=(x_signed, y_signed))
    new = RP.make_bundle(p, tab, d, W1, W2, x_mpc, y_mpc, ctx, carry=carry, carry_wires=carry_wires,
                         owner=OS.Owner(h=PW.OWNER_H), signed=(x_signed, y_signed))
    L = OS.sig_len(PW.OWNER_H)
    new["blob"] = new["blob"][:-L] + old["blob"][-L:]
    return new

def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    rng = random.Random(d)
    M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    W1, W2 = M(), M()
    batch = lambda: ([rng.randint(-7, 7) % p for _ in range(d)], [rng.randint(-7, 7) % p for _ in range(d)])
    x1, y1 = batch()
    x2, y2 = batch()
    owner = OS.Owner(h=PW.OWNER_H)
    mallory = OS.Owner(h=PW.OWNER_H)                     # the colluding custodians' own key
    model = "mind-0"
    dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
    rows, info = {}, {}
    def rec(name, r):
        rows[name] = dict(verdict="ACCEPT" if r[0] else "REFUSED", by=r[1])
        print(f"{name:58s} {rows[name]['verdict']:8s} {r[1]}", flush=True)
    ctx1, ctx2 = (model, 0, 1), (model, 0, 2)
    s1 = bundle(p, tab, d, W1, W2, x1, y1, ctx1, owner, x1, y1)
    gen = s1["genesis"]
    info["first_violated_honest"] = (s1["sst"]["first_violated"], s1["mst"]["first_violated"])
    s2 = bundle(p, tab, d, dec(s1["wires"]["W1n"]), dec(s1["wires"]["W2n"]), x2, y2, ctx2, owner, x2, y2,
                carry=s1["child"], carry_wires=(s1["wires"]["W1n"], s1["wires"]["W2n"]))
    # the attack bundles are made by COLLUDING custodians, who bypass their own life counters (they hold W anyway)
    for c in list(gen.values()) + list(s1["child"].values()):
        c.max_lives = 99
    twin = lambda: OS.Owner(h=PW.OWNER_H, seed=owner.seed)       # a fresh honest signature on the batch shown
    x_bad = list(x1); x_bad[0] = (x_bad[0] + 1) % p
    y_bad = list(y1); y_bad[1] = (y_bad[1] + 3) % p
    sa = bundle(p, tab, d, W1, W2, x_bad, y1, ctx1, twin(), x1, y1, carry=gen)
    sb = bundle(p, tab, d, W1, W2, x1, y_bad, ctx1, twin(), x1, y1, carry=gen)
    sc = bundle(p, tab, d, W1, W2, x_bad, y1, ctx1, owner, x_bad, y1, carry=gen, signer=mallory)
    sr = bundle(p, tab, d, dec(s1["wires"]["W1n"]), dec(s1["wires"]["W2n"]), x1, y1, ctx2, owner, x1, y1,
                carry=s1["child"], carry_wires=(s1["wires"]["W1n"], s1["wires"]["W2n"]), sign_ctx=ctx1)
    info["substitute_x_violates"] = sa["sst"]["first_violated"]
    info["substitute_y_violates"] = sb["mst"]["first_violated"]
    tmp = tempfile.mkdtemp(prefix="dl-ledger-")
    path = os.path.join(tmp, "mind-0.ledger")
    Lg = PW.Ledger(path, model, genesis=dict(d=d, owner_pk=owner.pk, custodians=["c0", "c1", "c2"],
                                             roots={k: gen[k].roots for k in ("W1", "W2")}))
    rec("custodians train on x' while presenting the owner's signed x", Lg.accept(p, sa["blob"], tab))
    rec("custodians train on y' while presenting the owner's signed y", Lg.accept(p, sb["blob"], tab))
    rec("custodians commit x' themselves and sign with their own key", Lg.accept(p, sc["blob"], tab))
    rec("step 1, honest, owner-signed", Lg.accept(p, s1["blob"], tab))
    rec("step 2 re-using the owner's step-1 signature (old batch, used leaf)", Lg.accept(p, sr["blob"], tab))
    rec("step 2, honest, owner-signed", Lg.accept(p, s2["blob"], tab))
    info["bytes_bound_step"] = len(s1["blob"])
    info["signature_bytes"] = OS.sig_len(PW.OWNER_H)
    info["spine_lin_constraints"] = s1["sst"]["lin_constraints"]
    info["middle_lin_constraints"] = s1["mst"]["lin_constraints"]
    print(json.dumps(info), flush=True)
    for f in os.listdir(tmp):
        os.remove(os.path.join(tmp, f))
    os.rmdir(tmp)
    json.dump(dict(d=d, rows=rows, info=info), open(f"signed_input_results_d{d}.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
