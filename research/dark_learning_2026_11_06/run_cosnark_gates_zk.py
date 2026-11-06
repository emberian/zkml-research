"""ZK layers 2-3 for the collaborative proof's middle (cosnark_gates_zk.py) next to the ZK spine: honest steps,
the five gate forgeries with the check each violates, and the hidden-row/constraint counts.

    python3 run_cosnark_gates_zk.py [d ...]      # default 4 16; writes cosnark_gates_zk_results.json
"""
import json
import random
import sys
import time

import bfv_ref as bfv
import cosnark as CS
import cosnark_gates as G
import cosnark_gates_zk as GZ
import cosnark_zk as ZK
import mpc_fork as MF
import spdz

CS.HIDE, CS.NMASK = CS.LIVES * CS.T_COLS, CS.LIVES

def run(d, attack=None, cheat_phase=None):
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    rng = random.Random(d)
    W1 = [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) % p for _ in range(d)]
    y = [rng.randint(-7, 7) % p for _ in range(d)]
    cheat = None
    if cheat_phase:
        dry = G.RecEngine(p, 3, spdz.Dealer(p, 3, 5))
        MF.run_step(dry, W1, W2, x, y, tab, 9)
        cheat = dict(party=1, at_open=[k for k, (ph, _, _) in enumerate(dry.transcript) if ph == cheat_phase][0], delta=1)
    dealer = spdz.Dealer(p, 3, 5)
    live = G.RecEngine(p, 3, dealer, cheat=cheat, attack=attack)
    W1n, W2n, wires = MF.run_step(live, W1, W2, x, y, tab, 9)
    if not cheat:
        live.mac_check("step")
    wires.update(W1n=W1n, W2n=W2n)
    ctx = ("model", 0, 1)
    t0 = time.time()
    sp, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, context=ctx)
    ok_s = ZK.verify_zk(p, 3, d, ctx, None, False, sp)
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=list(live.transcript))
    MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
    mp, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx)
    ok_m = GZ.verify_middle_zk(p, 3, sym, d, sp["roots"], ctx, mp)
    return dict(spine=ok_s, middle=ok_m, spine_violates=sst["first_violated"], middle_violates=mst["first_violated"],
                middle_counts={k: v for k, v in mst.items() if k != "first_violated"},
                spine_stats={k: v for k, v in sst.items() if k not in ("child", "coms", "first_violated")},
                middle_proof=ZK.measure_any(mp, 3), seconds=round(time.time() - t0, 1))

def main():
    ds = [int(a) for a in sys.argv[1:]] or [4, 16]
    out = {}
    for d in ds:
        r = run(d)
        f = GZ.counts_formula(d)
        got = dict(r["middle_counts"], proof=r["middle_proof"])
        r["formula"] = f
        r["formula_mismatches"] = [k for k in f if got.get(k) != f[k]]
        out[f"d{d}"] = r
        print(d, json.dumps(r), flush=True)
    d = ds[0]
    for name, kw in (("forged_trunc_opening", dict(cheat_phase="trunc")),
                     ("forged_lookup_opening", dict(cheat_phase="lookup")),
                     ("bad_triple", dict(attack="bad_triple")),
                     ("nonboolean_bit", dict(attack="nonboolean_bit")),
                     ("mask_out_of_range", dict(attack="mask_out_of_range"))):
        r = run(d, **kw)
        out[name] = {k: r[k] for k in ("spine", "middle", "middle_violates")}
        print(name, json.dumps(out[name]), flush=True)
    S = dict(S1=11, K1=19, S2=4, K2=8, S3=14, K3=19)
    out["d4096_formula"] = dict(middle_zk=GZ.counts_formula(4096, **S))
    json.dump(out, open("cosnark_gates_zk_results.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
