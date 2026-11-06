"""The MPC fork's step with BOTH halves of the collaborative proof: the spine (cosnark.py) and the
elementwise middle (cosnark_gates.py). Honest run, full-collusion attacks, counts vs the MODEL.

    python3 run_cosnark_gates.py [d ...]      # default 16 64; writes cosnark_gates_results.json
"""
import json
import random
import sys
import time

import bfv_ref as bfv
import cosnark as CS
import cosnark_gates as G
import mpc_fork as MF
import spdz
import step_spec as S

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
        # locate the first opening of the phase in an honest run, then forge a broadcast there
        dry = G.RecEngine(p, 3, spdz.Dealer(p, 3, 5))
        MF.run_step(dry, W1, W2, x, y, tab, 9)
        pos = [k for k, (ph, _, _) in enumerate(dry.transcript) if ph == cheat_phase][0]
        cheat = dict(party=1, at_open=pos, delta=1)
    dealer = spdz.Dealer(p, 3, 5)
    live = G.RecEngine(p, 3, dealer, cheat=cheat, attack=attack)
    W1n, W2n, wires = MF.run_step(live, W1, W2, x, y, tab, 9)
    if not cheat:
        live.mac_check("step")        # a full collusion (knowing alpha) would forge MACs: skipped for cheats
    wires.update(W1n=W1n, W2n=W2n)
    t0 = time.time()
    ok_s, why_s, cs = CS.prove_and_verify(spdz.Engine(p, 3, dealer), wires)
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=list(live.transcript))
    MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
    ok_m, why_m, cm = G.prove_and_verify_middle(live, sym, wires, cs["roots"])
    return dict(spine=(ok_s, why_s), middle=(ok_m, why_m), middle_counts=cm,
                spine_counts={k: v for k, v in cs.items() if k not in ("child_roots", "roots", "carry")},
                seconds=round(time.time() - t0, 1))

def main():
    import os
    zk = os.environ.get("ZK") == "1"
    if zk:                       # ZK layer 1: hiding PCS (tails >= t, mask rows)
        CS.HIDE, CS.NMASK = CS.LIVES * CS.T_COLS, CS.LIVES * 4
    ds = [int(a) for a in sys.argv[1:]] or [16, 64]
    out = {}
    for d in ds:
        r = run(d)
        f = G.counts_formula(d)
        r["formula"] = f
        r["formula_exact"] = all(r["middle_counts"][k] == v for k, v in f.items()
                                 if not (CS.HIDE and k == "committed_elems"))
        out[f"d{d}"] = r
        print(d, "spine", r["spine"], "middle", r["middle"], "formula exact", r["formula_exact"],
              r["middle_counts"], flush=True)
    d = ds[0]
    atts = {}
    for name, kw in (("forged_trunc_opening", dict(cheat_phase="trunc")),
                     ("forged_lookup_opening", dict(cheat_phase="lookup")),
                     ("bad_triple", dict(attack="bad_triple")),
                     ("nonboolean_bit", dict(attack="nonboolean_bit")),
                     ("mask_out_of_range", dict(attack="mask_out_of_range"))):
        r = run(d, **kw)
        atts[name] = dict(spine=r["spine"], middle=r["middle"])
        print(name, "spine", r["spine"], "middle", r["middle"], flush=True)
    out["attacks"] = atts
    for dd in (64, 4096):
        out[f"formula_d{dd}"] = G.counts_formula(dd) if dd == 64 else G.counts_formula(
            dd, S1=11, K1=19, S2=4, K2=8, S3=14, K3=19)
    out["zk_layer1_hiding_pcs"] = zk
    json.dump(out, open("cosnark_gates_results_zk.json" if zk else "cosnark_gates_results.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
