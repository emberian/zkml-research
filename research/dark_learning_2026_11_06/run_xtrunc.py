"""Exact truncation (program flag "XT"; notes/dark-learning-gen6/xtrunc.md): the online phase's tests, plain SPDZ.

    python3 run_xtrunc.py [d]          (default d = 8, the harness program)

Rows (each prints and asserts):
  1. XT steps refine step_spec: several dealer seeds; every truncation mask uniform in [0, p) (ranges seen);
  2. the wrap zone: a mask that wraps (cheat xt_wrap) makes the custodians abort with the XT reason before the MAC
     check; the redo on the SAME dealer (same MAC key alpha, the stream continued: fresh preprocessing) is accepted
     and refines the spec; the aborted step never yields an accepted output;
  3. control: the same wrap with the rule ignored (xt_ignore) passes the MAC check and does NOT refine the spec (so
     the rule is load-bearing, and the MAC check cannot see it);
  4. a wrong low-bit comparison (borrow_flip at d1[0], MAC-consistent) passes the MAC check and breaks the spec (the proof's
     low-bit rows are what refuse it: run_xtrunc_proof.py);
  5. the statistical default is untouched: masks below 2^(K+40).
"""
import random
import sys

import mpc_fork as MF
import spdz
import step_spec as S

P = 2305843009210515457          # the ledger profile's SPDZ field (N = 16384, L = 4)


def inputs(d, seed):
    rng = random.Random(seed)
    W1 = [[rng.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    return W1, W2, x, y


def step(dealer, d, seed, xt, cheat=None, owner_seed=9):
    eng = spdz.Engine(P, 3, dealer, cheat=cheat)
    eng.xt = xt
    masks = []
    orig = dealer.auth
    def auth(v, tag):
        if tag == "tr":
            masks.append(v)
        return orig(v, tag)
    dealer.auth = auth
    W1, W2, x, y = inputs(d, seed)
    m = lambda M: [[v % P for v in r] for r in M]
    try:
        W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % P for v in x], [v % P for v in y], MF.tables(P), owner_seed)
        eng.mac_check("xt")
    except spdz.Abort as e:
        return dict(verdict="ABORT", why=str(e), masks=masks, opened=len(eng.transcript))
    finally:
        dealer.auth = orig
    e1, e2, _ = S.step(W1, W2, x, y)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    return dict(verdict="ACCEPT", refines=rev(W1n) == e1 and rev(W2n) == e2, masks=masks)


def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    # 1. XT refines the spec
    top = 0
    for seed in range(4):
        dl = spdz.Dealer(P, 3, 100 + seed)
        out = step(dl, d, seed, xt=True)
        assert out["verdict"] == "ACCEPT" and out["refines"], out.get("why")
        top = max(top, max(out["masks"]))
    print(f"1. XT d = {d}: 4 seeds ACCEPT, refines_spec; {4 * 4 * d} masks, largest 2^{top.bit_length()} "
          f"(statistical masks stay below 2^{13 + 40})")
    assert top.bit_length() > 13 + 41
    # 2. the wrap zone, then the redo on the same MAC key
    dl = spdz.Dealer(P, 3, 7)
    alpha = dl.alpha
    out = step(dl, d, 1, xt=True, cheat=dict(xt_wrap=0))
    assert out["verdict"] == "ABORT" and out["why"].startswith("XT:"), out
    print(f"2a. wrap at truncation 0: ABORT before the MAC check: {out['why']}")
    out2 = step(dl, d, 1, xt=True, owner_seed=10)
    assert dl.alpha == alpha and out2["verdict"] == "ACCEPT" and out2["refines"]
    assert not set(out2["masks"]) & set(out["masks"])
    print("2b. redo, same dealer (alpha unchanged, the MAC key kept), fresh masks: ACCEPT, refines_spec")
    # 3. control: the rule ignored
    out3 = step(spdz.Dealer(P, 3, 7), d, 1, xt=True, cheat=dict(xt_wrap=0, xt_ignore=True))
    assert out3["verdict"] == "ACCEPT" and not out3["refines"], out3
    print("3. control: the same wrap with the rule ignored: MAC check passes, refines_spec FALSE (the rule is load-bearing)")
    # 4. wrong low-bit comparison
    out4 = step(spdz.Dealer(P, 3, 7), d, 1, xt=True, cheat=dict(borrow_flip=3 * d))   # the first d1 truncation
    assert out4["verdict"] == "ACCEPT" and not out4["refines"], out4
    print("4. borrow flipped at the first d1 truncation: MAC check passes, refines_spec FALSE (the proof's low-bit rows refuse it)")
    # 5. the default
    out5 = step(spdz.Dealer(P, 3, 7), d, 1, xt=False)
    assert out5["verdict"] == "ACCEPT" and out5["refines"] and max(out5["masks"]) < 1 << (13 + 40)
    print("5. statistical default: ACCEPT, refines_spec, masks < 2^53")
    print("ALL XT ONLINE ROWS PASS")


if __name__ == "__main__":
    main()
