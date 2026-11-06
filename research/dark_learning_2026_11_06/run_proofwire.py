"""The untrusted-input verifier (proofwire.py) and the durable ledger, attacked. Step bundles are produced by the
custodians (spine + middle ZK proofs, public SPDZ transcript), serialized to bytes, and handed to a Ledger whose
genesis record pins d, the parameters, the custodian set and the genesis weight commitment.

    python3 run_proofwire.py [d]       # default d = 4; writes proofwire_results_d{d}.json
"""
import json
import os
import random
import struct
import sys
import tempfile

import bfv_ref as bfv
import cosnark as CS
import cosnark_gates as G
import cosnark_gates_zk as GZ
import cosnark_zk as ZK
import mpc_fork as MF
import proofwire as PW
import spdz

def genesis_commit(p, wires):
    """At genesis the custodians commit their shares of W1, W2; the ledger's genesis record pins the roots."""
    sh = lambda M: [[v[i][0] for r in M for v in r] for i in range(3)]
    return {"W1": ZK.ZKPCS(p, sh(wires["W1"]), "W1"), "W2": ZK.ZKPCS(p, sh(wires["W2"]), "W2")}

def make_bundle(p, tab, d, W1, W2, x, y, ctx, carry=None, carry_wires=None, owner=None, signed=None):
    dealer = spdz.Dealer(p, 3, 5)
    live = G.RecEngine(p, 3, dealer)
    W1n, W2n, wires = MF.run_step(live, W1, W2, x, y, tab, 9)
    live.mac_check("step")
    wires.update(W1n=W1n, W2n=W2n)
    gen = None
    if carry is None:
        carry = gen = genesis_commit(p, wires)
    if carry_wires:
        wires["W1"], wires["W2"] = carry_wires
    public = [v for _, _, v in live.transcript]
    ox = oy = sig = None
    if owner is not None:
        xs, ys = signed or (x, y)
        import owner_sig as OS
        ox, oy = ZK.owner_commit(p, xs, "xo"), ZK.owner_commit(p, ys, "yo")
        sig = owner.sign(OS.batch_message(ctx, ox.roots, oy.roots))
    spine, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, carry=carry, context=ctx, owner_x=ox, public=public)
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=list(live.transcript))
    MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
    middle, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx, owner_y=oy)
    blob = PW.encode_step(p, ctx, d, 3, True, spine, public, middle, sym, owner_sig=sig)
    return dict(blob=blob, child=sst["child"], wires=wires, genesis=gen, sst=sst, mst=mst)

def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    rng = random.Random(d)
    M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    W1, W2 = M(), M()
    x = [rng.randint(-7, 7) % p for _ in range(d)]
    y = [rng.randint(-7, 7) % p for _ in range(d)]
    model = "mind-0"
    dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
    s1 = make_bundle(p, tab, d, W1, W2, x, y, (model, 0, 1))
    b1, child1, w1 = s1["blob"], s1["child"], s1["wires"]
    groots = {k: s1["genesis"][k].roots for k in ("W1", "W2")}
    cw = (w1["W1n"], w1["W2n"])
    nxt = lambda ctx, **kw: make_bundle(p, tab, d, dec(w1["W1n"]), dec(w1["W2n"]), x, y, ctx, carry=child1,
                                        carry_wires=cw, **kw)
    s2 = nxt((model, 0, 2))
    b2, child2, w2 = s2["blob"], s2["child"], s2["wires"]
    # Colluding custodians (who could publish W anyway) bypass their life counter to make more proofs from step 1's
    # child: a second proof of step 2 (equivocation) and a step-3 proof patched to look like step 2. Honest
    # custodians refuse a third opening (life_counter row below).
    for c in child1.values():
        c.max_lives = 99
    b2b = nxt((model, 0, 2))["blob"]
    b3 = nxt((model, 0, 3))["blob"]
    for c in child1.values():
        del c.max_lives
    hdr = 8 + 2 + len(model)
    b3_as_2 = b3[:hdr + 4] + struct.pack(">Q", 2) + b3[hdr + 12:]
    rows = {}
    def rec(name, ok_why):
        rows[name] = dict(verdict="ACCEPT" if ok_why[0] else "REFUSED", by=ok_why[1])
        print(f"{name:52s} {rows[name]['verdict']:8s} {ok_why[1]}", flush=True)
    # an honest custodian set refuses a third opening of step 1's child
    try:
        nxt((model, 0, 2))
        rec("honest custodians asked to open step 1's child a third time", (True, "opened"))
    except CS.LifeExhausted as e:
        rec("honest custodians asked to open step 1's child a third time", (False, f"LifeExhausted: {e}"))
    tmp = tempfile.mkdtemp(prefix="dl-ledger-")
    path = os.path.join(tmp, "mind-0.ledger")
    Lg = PW.Ledger(path, model, genesis=dict(d=d, owner_pk=None, custodians=["c0", "c1", "c2"], roots=groots))
    rec("step 1, honest (parent = genesis record)", Lg.accept(p, b1, tab))
    rec("step 1 replayed", Lg.accept(p, b1, tab))
    rec("step 2 truncated by one byte", Lg.accept(p, b2[:-1], tab))
    rec("step 2 with one trailing byte", Lg.accept(p, b2 + b"\x00", tab))
    ld = d.bit_length() - 1
    off = hdr + 16 + (13 + 4 * ld + 2) * 3 * 32   # header, then the commitment, round, eval and mask roots
    rec("step 2 with a non-canonical field element", Lg.accept(p, b2[:off] + p.to_bytes(8, "big") + b2[off + 8:], tab))
    flips = {"a byte in the header's model id": 10, "a byte in a commitment root": hdr + 16 + 5,
             "a byte in a field element (prox)": off + 7, "a byte in the middle of the blob": len(b2) // 2,
             "the last byte": len(b2) - 1}
    for what, pos in flips.items():
        bad = bytearray(b2); bad[pos] ^= 0x01
        rec(f"step 2 with {what} flipped", Lg.accept(p, bytes(bad), tab))
    rec("step 2 with a model id that is not UTF-8", Lg.accept(p, b2[:10] + b"\xff\xfe\xfd\xfc\xfb\xfa" + b2[16:], tab))
    rec("step 3's proof under a header patched to step 2", Lg.accept(p, b3_as_2, tab))
    other = b2[:8] + struct.pack(">H", 6) + b"mind-1" + b2[hdr:]
    rec("step 2 claiming another model id", Lg.accept(p, other, tab))
    rec("step 2, honest", Lg.accept(p, b2, tab))
    rec("a second valid proof of step 2 (equivocation)", Lg.accept(p, b2b, tab))
    Lg2 = PW.Ledger(path, model)
    rows["restart reconstructs the head"] = dict(verdict="OK" if Lg2.head() == Lg.head() else "FAIL", by=str(Lg2.head()[0]))
    print("restart head", Lg2.head()[0], Lg2.head() == Lg.head(), flush=True)
    # rotation: a new committee re-commits the current weights; the old committee's next proof no longer chains
    s3 = make_bundle(p, tab, d, dec(w2["W1n"]), dec(w2["W2n"]), x, y, (model, 1, 3), carry=child2,
                     carry_wires=(w2["W1n"], w2["W2n"]))
    newc = {k: ZK.owner_commit(p, [sum(v[i][0] for i in range(3)) % p for r in w2[k + "n"] for v in r], k).roots
            for k in ("W1", "W2")}
    Lg2.rotate(["c3", "c4", "c5"], newc)
    Lg3 = PW.Ledger(path, model)
    rows["restart after rotation keeps epoch 1 and the new committee's roots"] = dict(
        verdict="OK" if Lg3.head() == ((model, 1, 3), newc) else "FAIL", by=str(Lg3.head()[0]))
    print("restart after rotation", Lg3.head()[0], Lg3.head() == ((model, 1, 3), newc), flush=True)
    rec("after rotation: the OLD committee's step 3 (epoch 1 header)", Lg3.accept(p, s3["blob"], tab))
    sizes = dict(step1_bytes=len(b1), step2_bytes=len(b2))
    print("sizes", sizes)
    for f in os.listdir(tmp):
        os.remove(os.path.join(tmp, f))
    os.rmdir(tmp)
    json.dump(dict(d=d, rows=rows, sizes=sizes), open(f"proofwire_results_d{d}.json", "w"), indent=1)

if __name__ == "__main__":
    main()
