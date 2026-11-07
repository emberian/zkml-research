"""Custody handover (handover.py) end to end on the durable ledger: step 1 by the old committee, resharing to a new
committee, the handover proof, the rotation record, step 2 by the new committee chained to the new roots; and the
attacks.

    python3 run_handover.py [d] [profile]      # default d = 4, ledger profile; writes handover_results_d{d}_{profile}.json

Under a cut E profile (DEFER: demo-x2de, ledger-x2de) it runs main_defer: the handover discharges the pending head
and leaves the new head pending through the new committee's carries (handover.prove_defer).

The ledger takes the proof's BYTES (handover.encode). HANDOVER_DUMP=<dir> also writes, per rotation attempt, the
ledger file before it, the bytes, the arguments, Python's verdict and the ledger file after it (rotations.json), which
the native verifier replays (native/darkproof/tests/handover_vs_python.rs).
"""
import json
import os
import random
import sys
import tempfile
import time

import proofwire as PW
import bfv_ref as bfv
import cosnark as CS
import cosnark_ext as X
import cosnark_zk as ZK
import handover as HO
import mpc_fork as MF
import run_proofwire as RP
import spdz


def authenticate(p, plain_by_party, d):
    """The new committee authenticates its plain shares under its MAC key (auth_plain; the harness's step dealer uses
    seed 5, so the new committee's spine engine shares that alpha)."""
    eng = spdz.Engine(p, 3, spdz.Dealer(p, 3, 5))
    flat = [eng.auth_plain({i: plain_by_party[i][k] for i in range(3)}, "handover_auth") for k in range(d * d)]
    return [flat[r * d:(r + 1) * d] for r in range(d)]


def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    prof = sys.argv[2] if len(sys.argv) > 2 else "ledger"
    PW.set_profile(prof)
    if ZK.DEFER:
        return main_defer(d, prof)
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    rng = random.Random(d)
    M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    W1, W2 = M(), M()
    x = [rng.randint(-7, 7) % p for _ in range(d)]
    y = [rng.randint(-7, 7) % p for _ in range(d)]
    model = "mind-h"
    old_set, new_set = ["c0", "c1", "c2"], ["c3", "c4", "c5"]
    dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
    rows = {}
    dump = os.environ.get("HANDOVER_DUMP")
    rotations = []

    def rot(name, lg, custodians, roots, blob, expect):
        before = open(lg.path).read()
        t = time.time()
        res = lg.rotate(p, custodians, roots, blob)
        secs = time.time() - t
        rec(name, res, expect)
        rows[name]["verify_seconds"] = round(secs, 3)
        if dump:
            fn = f"rot{len(rotations):02d}.bin"
            if blob is not None:
                open(os.path.join(dump, fn), "wb").write(blob)
            rotations.append(dict(name=name, ledger_before=before, ledger_after=open(lg.path).read(),
                                  custodians=custodians, new_roots=roots, bytes=fn if blob is not None else None,
                                  ok=res[0], why=res[1]))

    def rec(name, res, expect):
        ok, why = res
        good = ok == expect
        rows[name] = dict(verdict="ACCEPT" if ok else "REFUSED", by=why, as_expected=good)
        print(("ok  " if good else "BAD ") + name, "->", "ACCEPT" if ok else "REFUSED", why if not ok else "", flush=True)

    tmp = tempfile.mkdtemp()
    path = os.path.join(tmp, "ledger.jsonl")
    t0 = time.time()
    s1 = RP.make_bundle(p, tab, d, W1, W2, x, y, (model, 0, 1))
    groots = {k: s1["genesis"][k].roots for k in ("W1", "W2")}
    Lg = PW.Ledger(path, model, genesis=dict(d=d, owner_pk=None, custodians=old_set, roots=groots))
    rec("step 1 by the old committee", Lg.accept(p, s1["blob"], tab), True)
    child1, w1 = s1["child"], s1["wires"]

    # ---------------------------------------------------------------- resharing and the new committee's commitment
    old = {k: [[v[i][0] for r in w1[k + "n"] for v in r] for i in range(3)] for k in ("W1", "W2")}
    rs = random.Random(1234)
    new = {}
    for k in ("W1", "W2"):
        _, new[k] = HO.reshare(old[k], 3, p, rs)
    new_coms = {k: ZK.ZKPCS(p, new[k], k) for k in ("W1", "W2")}
    new_roots = {k: new_coms[k].roots for k in ("W1", "W2")}
    hctx = Lg.handover_context(new_set)

    # attack: the new committee commits shifted weights (one share entry + 1); the old committee's child is used for
    # this attempt with the colluders' life bypass, so the honest proof below still has its life
    bad = {k: [list(s) for s in new[k]] for k in ("W1", "W2")}
    bad["W1"][0][1] = (bad["W1"][0][1] + 1) % p
    bad_coms = {k: ZK.ZKPCS(p, bad[k], k) for k in ("W1", "W2")}
    for c in child1.values():
        c.max_lives = 99
    bproof, bst = HO.prove(p, d, child1, bad_coms, hctx)
    rot("handover to a commitment of shifted weights", Lg, new_set, {k: bad_coms[k].roots for k in bad_coms},
        HO.encode(p, d, bproof), False)
    rows["handover to a commitment of shifted weights"]["violated"] = bst["first_violated"]
    # attack: resharing that drops one subshare (sum != share)
    _, dropped = HO.reshare(old["W2"], 3, p, random.Random(5))
    dropped[2] = [(v - 7) % p for v in dropped[2]]
    dcoms = {"W1": ZK.ZKPCS(p, new["W1"], "W1"), "W2": ZK.ZKPCS(p, dropped, "W2")}
    dproof, dst = HO.prove(p, d, child1, dcoms, hctx)
    rot("resharing whose subshares do not sum to the old shares", Lg, new_set, {k: dcoms[k].roots for k in dcoms},
        HO.encode(p, d, dproof), False)
    rows["resharing whose subshares do not sum to the old shares"]["violated"] = dst["first_violated"]
    for c in child1.values():
        c.opened_lives = 1          # the bypassed attempts above are the colluders' extra openings; reset for honesty
        del c.max_lives

    t1 = time.time()
    hproof, hst = HO.prove(p, d, child1, new_coms, hctx)
    prove_secs = time.time() - t1
    hb = HO.encode(p, d, hproof)
    assert HO.encode(p, d, HO.decode(p, hb, d, 3, 3)) == hb
    rows["handover proof stats"] = dict(hidden_rows=hst["hidden_rows"], lin_constraints=hst["lin_constraints"],
                                       ligero_wire=hst["ligero_wire"], bytes=len(hb),
                                       prove_seconds=round(prove_secs, 2))
    rot("honest proof, but recorded with other new roots", Lg, new_set, {k: bad_coms[k].roots for k in bad_coms}, hb,
        False)
    rot("honest proof for another new custodian set", Lg, ["c3", "c4", "c9"], new_roots, hb, False)
    rot("honest proof for a committee of four", Lg, ["c3", "c4", "c5", "c9"], new_roots, hb, False)
    rot("no handover proof", Lg, new_set, new_roots, None, False)
    tampered = HO.decode(p, hb, d, 3, 3)
    tampered["ligero"]["q"][0] = (tampered["ligero"]["q"][0] + 1) % p
    rot("a tampered handover proof (Ligero q[0] + 1, re-encoded)", Lg, new_set, new_roots, HO.encode(p, d, tampered),
        False)
    # the proximity row's u-part: under EXT = 2 a custodian's row is EXT * W long, component-major; + 1 on the last
    # component's first entry (EXT = 1: the row's first entry)
    tp = HO.decode(p, hb, d, 3, 3)
    W = new_coms["W1"].W
    tp["prox_new"]["W1"][0][(X.EXT - 1) * W] = (tp["prox_new"]["W1"][0][(X.EXT - 1) * W] + 1) % p
    rot(f"a tampered proximity row (new W1, custodian 0, component {X.EXT - 1} u-part + 1, re-encoded)", Lg, new_set,
        new_roots, HO.encode(p, d, tp), False)
    flip = bytearray(hb)
    flip[len(hb) // 2] ^= 0x01
    rot("the proof bytes with one byte flipped (middle)", Lg, new_set, new_roots, bytes(flip), False)
    rot("the proof bytes truncated by one byte", Lg, new_set, new_roots, hb[:-1], False)
    rot("the proof bytes with a trailing byte", Lg, new_set, new_roots, hb + b"\x00", False)
    off = 12 + 32 * (2 * 3 + 2 * 3 + 6 + 6)      # header, old/new roots, eval/mask roots: the first prox element
    rot("the proof bytes with a non-canonical field element", Lg, new_set, new_roots,
        hb[:off] + p.to_bytes(8, "big") + hb[off + 8:], False)
    rot("honest handover", Lg, new_set, new_roots, hb, True)
    rot("the same handover proof replayed (now epoch 1 -> 2)", Lg, ["c6", "c7", "c8"], new_roots, hb, False)
    try:
        HO.prove(p, d, child1, new_coms, hctx)
        rows["a third opening of the old child"] = dict(verdict="OPENED", as_expected=False)
    except CS.LifeExhausted as e:
        rows["a third opening of the old child"] = dict(verdict="REFUSED", by=str(e), as_expected=True)
    print("ok   a third opening of the old child -> REFUSED (life counter)", flush=True)
    Lg2 = PW.Ledger(path, model)
    rows["restart after rotation"] = dict(verdict="OK" if Lg2.head() == ((model, 1, 2), new_roots) else "FAIL",
                                          as_expected=Lg2.head() == ((model, 1, 2), new_roots))

    # ---------------------------------------------------------------- the next step by the new committee
    new_wires = (authenticate(p, new["W1"], d), authenticate(p, new["W2"], d))
    s2 = RP.make_bundle(p, tab, d, dec(w1["W1n"]), dec(w1["W2n"]), x, y, (model, 1, 2), carry=new_coms,
                        carry_wires=new_wires)
    # the old committee's step 2 (colluders bypass their counter; the ledger refuses it on the parent)
    for c in child1.values():
        c.max_lives = 99
    s2_old = RP.make_bundle(p, tab, d, dec(w1["W1n"]), dec(w1["W2n"]), x, y, (model, 1, 2), carry=child1,
                            carry_wires=(w1["W1n"], w1["W2n"]))
    rec("after rotation: the OLD committee's step 2", Lg2.accept(p, s2_old["blob"], tab), False)
    rec("step 2 by the new committee, chained to the handover's roots", Lg2.accept(p, s2["blob"], tab), True)
    secs = round(time.time() - t0, 1)
    for f in os.listdir(tmp):
        os.remove(os.path.join(tmp, f))
    os.rmdir(tmp)
    if dump:
        json.dump(dict(d=d, profile=prof, model=model, rotations=rotations), open(os.path.join(dump, "rotations.json"), "w"),
                  indent=1)
    allgood = all(r.get("as_expected", True) for r in rows.values())
    out = dict(d=d, profile=prof, seconds=secs, all_as_expected=allgood, rows=rows)
    json.dump(out, open(f"handover_results_d{d}_{prof}.json", "w"), indent=1)
    print("all as expected:", allgood, f"({secs} s)")
    sys.exit(0 if allgood else 1)


def bundle(p, tab, d, W1, W2, x, y, ctx, carry=None, carry_wires=None, deferred=None, attack=None):
    """run_proofwire.make_bundle with cut E's deferred claims and the spine's attack hook (forge_W1n)."""
    import cosnark_gates as G
    import cosnark_gates_zk as GZ
    dealer = spdz.Dealer(p, 3, 5)
    live = G.RecEngine(p, 3, dealer)
    W1n, W2n, wires = MF.run_step(live, W1, W2, x, y, tab, 9)
    live.mac_check("step")
    wires.update(W1n=W1n, W2n=W2n)
    gen = None
    if carry is None:
        carry = gen = RP.genesis_commit(p, wires)
    if carry_wires:
        wires["W1"], wires["W2"] = carry_wires
    public = [v for _, _, v in live.transcript]
    spine, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, attack, carry=carry, context=ctx, public=public,
                             deferred=deferred)
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=list(live.transcript))
    MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
    middle, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx)
    blob = PW.encode_step(p, ctx, d, 3, True, spine, public, middle, sym)
    return dict(blob=blob, child=sst["child"], wires=wires, genesis=gen, sst=sst, mst=mst)


def main_defer(d, prof):
    """Cut E: step 1 (pending), the handover discharging it and leaving the new head pending, step 2 by the new
    committee discharging that; the refusal rows (i)-(iv) of the proof lane's conditions, and the byte-level ones."""
    import copy
    import shutil
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    rng = random.Random(d)
    M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    W1, W2 = M(), M()
    x = [rng.randint(-7, 7) % p for _ in range(d)]
    y = [rng.randint(-7, 7) % p for _ in range(d)]
    model = "mind-h"
    old_set, new_set = ["c0", "c1", "c2"], ["c3", "c4", "c5"]
    dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
    rows = {}
    dump = os.environ.get("HANDOVER_DUMP")
    rotations = []
    tmp = tempfile.mkdtemp()
    status = lambda lg: {str(k): v for k, v in sorted(lg.status.items())}

    def rec(name, res, expect, **extra):
        ok, why = res
        good = ok == expect
        rows[name] = dict(verdict="ACCEPT" if ok else "REFUSED", by=why, as_expected=good, **extra)
        print(("ok  " if good else "BAD ") + name, "->", "ACCEPT" if ok else "REFUSED", why if not ok else "", flush=True)

    def rot(name, lg, custodians, roots, blob, expect):
        before = open(lg.path).read()
        t = time.time()
        res = lg.rotate(p, custodians, roots, blob)
        rec(name, res, expect, verify_seconds=round(time.time() - t, 3))
        if dump:
            fn = f"rot{len(rotations):02d}.bin"
            if blob is not None:
                open(os.path.join(dump, fn), "wb").write(blob)
            rotations.append(dict(name=name, ledger_before=before, ledger_after=open(lg.path).read(),
                                  custodians=custodians, new_roots=roots, bytes=fn if blob is not None else None,
                                  ok=res[0], why=res[1]))

    def fork(lg, name):
        """A copy of the ledger file, for a branch of the run."""
        q = os.path.join(tmp, name + ".jsonl")
        shutil.copyfile(lg.path, q)
        return PW.Ledger(q, model)

    t0 = time.time()
    s1 = bundle(p, tab, d, W1, W2, x, y, (model, 0, 1))
    groots = {k: s1["genesis"][k].roots for k in ("W1", "W2")}
    gen = dict(d=d, owner_pk=None, custodians=old_set, roots=groots)
    Lg = PW.Ledger(os.path.join(tmp, "ledger.jsonl"), model, genesis=gen)
    rec("step 1 by the old committee", Lg.accept(p, s1["blob"], tab), True, status=None)
    rows["step 1 by the old committee"]["status"] = status(Lg)
    assert status(Lg) == {"1": "pending"}
    child1, w1, dfr1 = s1["child"], s1["wires"], s1["sst"]["deferred"]

    # resharing and the new committee's commitment (one life under cut E: ZK.w_pcs)
    old = {k: [[v[i][0] for r in w1[k + "n"] for v in r] for i in range(3)] for k in ("W1", "W2")}
    new = {}
    for k in ("W1", "W2"):
        _, new[k] = HO.reshare(old[k], 3, p, random.Random(1234))
    new_coms = {k: ZK.w_pcs(p, new[k], k) for k in ("W1", "W2")}
    new_roots = {k: new_coms[k].roots for k in ("W1", "W2")}
    hctx = Lg.handover_context(new_set)
    fresh = lambda: (copy.deepcopy(child1), copy.deepcopy(dfr1), copy.deepcopy(new_coms))

    # a handover that does not discharge the pending head (made as for a final head): refused
    c1o, _, nc = fresh()
    nd, _ = HO.prove(p, d, c1o, nc, hctx, deferred=None)
    rot("a handover that does not discharge the pending head", Lg, new_set, new_roots, HO.encode(p, d, nd), False)

    # (ii) the old head's carry not satisfied: step 1 with a forged child (forge_W1n), accepted as pending; the handover
    # opening that child against step 1's carry is refused
    sb = bundle(p, tab, d, W1, W2, x, y, (model, 0, 1), attack="forge_W1n")
    Lb = PW.Ledger(os.path.join(tmp, "forged.jsonl"), model, genesis=dict(gen, roots={k: sb["genesis"][k].roots for k in ("W1", "W2")}))
    rec("(ii) step 1 with a forged child (forge_W1n)", Lb.accept(p, sb["blob"], tab), True)
    rows["(ii) step 1 with a forged child (forge_W1n)"]["status"] = status(Lb)
    # the old custodians' shares of the forged child (custodian 0's W1n entry 5 + 1), reshared faithfully: old W(r) =
    # new W(r) holds, only the discharge W1n(r_1) = c1p fails
    sh_b = {k: [[v[i][0] for r in sb["wires"][k + "n"] for v in r] for i in range(3)] for k in ("W1", "W2")}
    sh_b["W1"][0][5] = (sh_b["W1"][0][5] + 1) % p
    bnew = {}
    for k in ("W1", "W2"):
        _, bnew[k] = HO.reshare(sh_b[k], 3, p, random.Random(77))
    bcoms = {k: ZK.w_pcs(p, bnew[k], k) for k in ("W1", "W2")}
    bproof, bst = HO.prove(p, d, sb["child"], bcoms, Lb.handover_context(new_set), deferred=sb["sst"]["deferred"])
    rot("(ii) a handover of a head whose child does not satisfy its carry", Lb, new_set,
        {k: bcoms[k].roots for k in bcoms}, HO.encode(p, d, bproof), False)
    rows["(ii) a handover of a head whose child does not satisfy its carry"]["violated"] = bst["first_violated"]

    # the new committee commits shifted weights AND carries their evaluation: old W(r) != cN, refused
    bad = {k: [list(s) for s in new[k]] for k in ("W1", "W2")}
    bad["W1"][0][1] = (bad["W1"][0][1] + 1) % p
    c1o, dfo, _ = fresh()
    bad_coms = {k: ZK.w_pcs(p, bad[k], k) for k in ("W1", "W2")}
    sp_, sst_ = HO.prove(p, d, c1o, bad_coms, hctx, deferred=dfo)
    rot("handover to shifted weights, carries their evaluation", Lg, new_set, {k: bad_coms[k].roots for k in bad_coms},
        HO.encode(p, d, sp_), False)
    rows["handover to shifted weights, carries their evaluation"]["violated"] = sst_["first_violated"]

    # (i) shifted weights, but the carries are the honest evaluation (cN = old W(r) != new W(r)): the rotation is
    # accepted as pending; the next step's discharge refuses it
    Li = fork(Lg, "i")
    c1o, dfo, _ = fresh()
    bad_coms = {k: ZK.w_pcs(p, bad[k], k) for k in ("W1", "W2")}
    ip, ist = HO.prove(p, d, c1o, bad_coms, hctx, deferred=dfo, carry_src=copy.deepcopy(new_coms))
    rot("(i) handover to shifted weights with honest carries", Li, new_set, {k: bad_coms[k].roots for k in bad_coms},
        HO.encode(p, d, ip), True)
    rows["(i) handover to shifted weights with honest carries"]["status"] = status(Li)
    bw = (authenticate(p, bad["W1"], d), authenticate(p, bad["W2"], d))
    plain = lambda sh_: [[MF.centered(sum(sh_[i][r * d + c] for i in range(3)) % p, p) % p for c in range(d)] for r in range(d)]
    si = bundle(p, tab, d, plain(bad["W1"]), plain(bad["W2"]), x, y, (model, 1, 2), carry=bad_coms, carry_wires=bw,
                deferred=ist["deferred"])
    rec("(i) the next step over the shifted weights (the discharge)", Li.accept(p, si["blob"], tab), False,
        violated=si["sst"]["first_violated"])

    # the honest handover, and the byte-level refusals
    c1o, dfo, nc = fresh()
    t1 = time.time()
    hproof, hst = HO.prove(p, d, c1o, nc, hctx, deferred=dfo)
    prove_secs = time.time() - t1
    hb = HO.encode(p, d, hproof)
    assert HO.encode(p, d, HO.decode(p, hb, d, 3, 3, True)) == hb
    assert hst["first_violated"] is None, hst["first_violated"]
    rows["handover proof stats"] = dict(hidden_rows=hst["hidden_rows"], lin_constraints=hst["lin_constraints"],
                                       ligero_wire=hst["ligero_wire"], bytes=len(hb), prove_seconds=round(prove_secs, 2))
    rot("honest proof for another new custodian set", Lg, ["c3", "c4", "c9"], new_roots, hb, False)
    tampered = HO.decode(p, hb, d, 3, 3, True)
    tampered["ligero"]["q"][0] = (tampered["ligero"]["q"][0] + 1) % p
    rot("a tampered handover proof (Ligero q[0] + 1, re-encoded)", Lg, new_set, new_roots, HO.encode(p, d, tampered), False)
    tc = HO.decode(p, hb, d, 3, 3, True)
    tc["carry_roots"]["c1"][0] = bytes(32) if isinstance(tc["carry_roots"]["c1"][0], bytes) else "00" * 32
    rot("a new carry root replaced (re-encoded)", Lg, new_set, new_roots, HO.encode(p, d, tc), False)
    flip = bytearray(hb)
    flip[len(hb) // 2] ^= 0x01
    rot("the proof bytes with one byte flipped (middle)", Lg, new_set, new_roots, bytes(flip), False)
    rot("the proof bytes truncated by one byte", Lg, new_set, new_roots, hb[:-1], False)
    rot("honest handover", Lg, new_set, new_roots, hb, True)
    rows["honest handover"]["status"] = status(Lg)
    rows["honest handover"]["pending"] = Lg.pending is not None
    try:
        HO.prove(p, d, c1o, copy.deepcopy(new_coms), hctx, deferred=copy.deepcopy(dfr1))
        rows["a second opening of the old head"] = dict(verdict="OPENED", as_expected=False)
    except CS.LifeExhausted as e:
        rows["a second opening of the old head"] = dict(verdict="REFUSED", by=str(e), as_expected=True)
    print("ok   a second opening of the old head -> REFUSED (life counter)", flush=True)
    Lg2 = PW.Ledger(Lg.path, model)
    good = Lg2.head() == ((model, 1, 2), new_roots) and Lg2.pending is not None
    rows["restart after rotation: head and pending claims"] = dict(verdict="OK" if good else "FAIL", as_expected=good)

    # (iv) a closing proof right after the rotation discharges it
    Lc = fork(Lg, "iv")
    cproof, _ = ZK.prove_close(p, 3, copy.deepcopy(new_coms), copy.deepcopy(hst["deferred"]), (model, 1, 1, "close"))
    rec("(iv) a closing proof right after the rotation", Lc.close(p, PW.encode_close(p, (model, 1, 1), d, 3, cproof)), True)
    rows["(iv) a closing proof right after the rotation"]["status"] = status(Lc)

    # (iii) the next step by the new committee, over the pending rotated head: accepted, and the head is final after it
    new_wires = (authenticate(p, new["W1"], d), authenticate(p, new["W2"], d))
    s2 = bundle(p, tab, d, dec(w1["W1n"]), dec(w1["W2n"]), x, y, (model, 1, 2), carry=copy.deepcopy(new_coms),
                carry_wires=new_wires, deferred=copy.deepcopy(hst["deferred"]))
    c1x = copy.deepcopy(child1)
    for c in c1x.values():
        c.max_lives = 99
    s2_old = bundle(p, tab, d, dec(w1["W1n"]), dec(w1["W2n"]), x, y, (model, 1, 2), carry=c1x,
                    carry_wires=(w1["W1n"], w1["W2n"]), deferred=copy.deepcopy(dfr1))
    rec("after rotation: the OLD committee's step 2", Lg2.accept(p, s2_old["blob"], tab), False)
    rec("(iii) step 2 by the new committee, discharging the rotated head", Lg2.accept(p, s2["blob"], tab), True)
    rows["(iii) step 2 by the new committee, discharging the rotated head"]["status"] = status(Lg2)
    want = {"1": "final (step 2 opened its child)", "2": "pending"}
    rows["status after step 2"] = dict(got=status(Lg2), want=want, as_expected=status(Lg2) == want)
    secs = round(time.time() - t0, 1)
    shutil.rmtree(tmp)
    if dump:
        json.dump(dict(d=d, profile=prof, model=model, rotations=rotations), open(os.path.join(dump, "rotations.json"), "w"),
                  indent=1)
    allgood = all(r.get("as_expected", True) for r in rows.values())
    out = dict(d=d, profile=prof, seconds=secs, all_as_expected=allgood, rows=rows)
    json.dump(out, open(f"handover_results_d{d}_{prof}.json", "w"), indent=1)
    print("all as expected:", allgood, f"({secs} s)")
    sys.exit(0 if allgood else 1)


if __name__ == "__main__":
    main()
