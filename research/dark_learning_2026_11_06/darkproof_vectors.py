"""Test vectors for the native collaborative proof (native/darkproof): runs the harness step and the bundle flow of
run_proofwire.make_bundle under DL_DETERMINISTIC (cosnark.det_rng) and writes, per bundle, the step witness the native
prover consumes (wires with MAC shares, the middle's preprocessing atoms, the public transcript, the dealer's MT state
after the step) and the Python bundle bytes the native bytes must equal.

    DL_DETERMINISTIC=7 python3 darkproof_vectors.py OUTDIR d [profile] [flows...]
      flows: pw (run_proofwire's steps 1 and 2), si (owner-signed steps 1 and 2), check (assert this file's bundle
      flow is byte-identical to run_proofwire.make_bundle), he (the DEPLOYED step, cosnark_he: HE matvec and outer
      over the HE profile's field, native_ref's inputs; step 1 genesis, steps 2 and 3 carried)
"""
import json
import os
import random
import sys

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

VECS = ("x", "y", "z1", "h", "z2", "d2", "b", "g1", "bg", "d1")
MATS = ("W1", "W2", "W1n", "W2n")

def sv(v, n=3):
    return [[v[i][0], v[i][1]] for i in range(n)]

def witness(p, d, dealer, live, wires):
    flat = lambda M: [x for r in M for x in r]
    cons, had, prep, ext = G.middle(live)
    prep = [a for a in prep if live.atoms[a][0] not in ("proofrange", "proofbits")]   # made at proof time
    return dict(p=p, d=d, n=3, alpha_sh=list(dealer.alpha_sh), dealer_state=list(dealer.rng.getstate()[1]),
                wires={k: [sv(v) for v in (wires[k] if k in VECS else flat(wires[k]))] for k in VECS + MATS if k in wires},
                public=[v for _, _, v in live.transcript], phases=[ph for ph, _, _ in live.transcript],
                atoms=[sv(live.atom_sh[a]) for a in prep], atom_tags=[live.atoms[a][1] for a in prep])

def step_only(p, tab, d, W1, W2, x, y, dump, carry_wires=None, cheat_phase=None, attack=None):
    """The harness step alone (no proof), its witness written to `dump`; returns the wires (W1n, W2n included)."""
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
    if carry_wires:
        wires["W1"], wires["W2"] = carry_wires
    json.dump(witness(p, d, dealer, live, wires), open(dump, "w"))
    return wires

def make_bundle(p, tab, d, W1, W2, x, y, ctx, carry=None, carry_wires=None, owner=None, signed=None, dump=None):
    """run_proofwire.make_bundle, with the witness written to `dump` right after the step."""
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
    if dump:
        json.dump(witness(p, d, dealer, live, wires), open(dump, "w"))
    public = [v for _, _, v in live.transcript]
    ox = oy = sig = None
    if owner is not None:
        xs, ys = signed or (x, y)
        ox, oy = ZK.owner_commit(p, xs, "xo"), ZK.owner_commit(p, ys, "yo")
        sig = owner.sign(OS.batch_message(ctx, ox.roots, oy.roots))
    spine, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, carry=carry, context=ctx, owner_x=ox, public=public)
    sym = G.RecEngine(p, 3, None, symbolic=True, transcript=list(live.transcript))
    MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
    middle, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx, owner_y=oy)
    blob = PW.encode_step(p, ctx, d, 3, True, spine, public, middle, sym, owner_sig=sig)
    return dict(blob=blob, child=sst["child"], wires=wires, genesis=gen, sst=sst, mst=mst)

# DP_DOMAIN=int: the gen 5 evaluation points x_j = j + 1 (the "<profile>-int" twin; vectors made before the coset domain)
DOMAIN_SUFFIX = "-int" if os.environ.get("DP_DOMAIN") == "int" else ""

HE_PROGRAM = dict(S1=5, K1=13, S2=4, K2=8, S3=8, K3=13, he=True)

def he_flow(out, d, prof, steps=3):
    """The deployed step chained over `steps` steps: native_ref's keys, inputs, dealer (seed 5, ONE stream for the
    run: step 1, its proof's triples, step 2, ...) and per-return HE streams. Step k uses HE seeds MV_SEED + 100 (k - 1),
    OU_SEED + 100 (k - 1) and owner seed OWNER_SEED + 100 (k - 1), so step 1 is native_ref's step exactly."""
    import cosnark_he as CH
    import he_matvec as HM
    import he_outer as HO
    import native_ref as NR
    he = PW.PARAMS["HE"]
    N, L, F = he["N"], he["L"], he["F_BITS"]
    Qp, t, Q = NR.setup(N, L)
    p = t
    assert p == PW.he_field()
    keys = [HM.OwnKey(N, Q, t, seed=NR.KEY_SEED0 + i) for i in range(3)]
    tab = MF.tables(p)
    if os.environ.get("DP_INPUTS"):
        # a step_spec program's inputs (native_ref.inputs_for, darkstep step::inputs_for), e.g. DP_INPUTS=GEN6
        import step_spec as S
        W1, W2, x, y = NR.inputs_for(d, getattr(S, os.environ["DP_INPUTS"]))
        W1 = [[v % p for v in r] for r in W1]
        W2 = [[v % p for v in r] for r in W2]
        x = [v % p for v in x]
        y = [v % p for v in y]
    else:
        rng = random.Random(d)
        wm = NR.wmax_for(d)
        W1 = [[rng.randint(-wm, wm) % p for _ in range(d)] for _ in range(d)]
        W2 = [[rng.randint(-wm, wm) % p for _ in range(d)] for _ in range(d)]
        x = [rng.randint(-7, 7) % p for _ in range(d)]
        y = [rng.randint(-7, 7) % p for _ in range(d)]
    steps = int(os.environ.get("DP_STEPS", steps))
    program = dict(HE_PROGRAM, **json.loads(os.environ.get("DP_PROGRAM", "{}")))
    # PUBLIC GENESIS (DP_PG_CFG=<darktrain cfg json>): W = train_owner.init(cfg) enters custody as a public constant
    # committed with public coins (PW.public_genesis); every step, step 1 included, is the carried program
    pg_cfg = os.environ.get("DP_PG_CFG")
    if pg_cfg:
        import hashlib
        cfg_bytes = open(pg_cfg, "rb").read()
        program["PG"] = hashlib.sha256(cfg_bytes).hexdigest()
        dd, W1, W2 = PW.public_weights(cfg_bytes)
        assert dd == d, "the public genesis cfg's d"
    prog = CH.Prog.of(program)
    tab = prog.tables(p)
    dealer = spdz.Dealer(p, 3, NR.DEALER_SEED)
    tag = f"{prof}_d{d}" + os.environ.get("DP_TAGSUFFIX", "")
    meta = dict(d=d, profile=prof, seed=os.environ["DL_DETERMINISTIC"], p=p, program=program, he=dict(N=N, L=L, F=F),
                bundles={})
    model, carry, carried, parent = "mind-0", None, None, None
    if pg_cfg:
        carry, parent = PW.public_genesis(p, d, W1, W2)
        carried = (PW.public_genesis_shares(p, W1, dealer.alpha_sh), PW.public_genesis_shares(p, W2, dealer.alpha_sh))
        meta["genesis_roots"], meta["pg_cfg"] = parent, os.path.abspath(pg_cfg)
    for k in range(1, steps + 1):
        cr = k > 1 or bool(pg_cfg)
        attack = os.environ.get("DP_ATTACK") if k == 1 else None   # TEST: a malformed step 1 (refusal rows)
        live = G.RecEngine(p, 3, dealer, attack=attack)
        noise = (N * (t // 2) * 32).bit_length()
        mv = CH.LiveHE(live, HM.HEMatvec(live, keys, N, Q, seed=NR.MV_SEED + 100 * (k - 1), flood_bits=F - noise,
                                         per_return_rng=True))
        ou = CH.LiveHE(live, HO.HEOuter(live, keys, N, Q, seed=NR.OU_SEED + 100 * (k - 1),
                                        flood_bits=F - (N * (t // 2) * 16 * 2).bit_length(), per_return_rng=True),
                       outer=True)
        W1n, W2n, wires = CH.run_step(live, W1, W2, x, y, tab, NR.OWNER_SEED + 100 * (k - 1), mv, ou, prog=prog,
                                      carried=carried)
        live.mac_check("he")
        wires.update(W1n=W1n, W2n=W2n)
        public = [v for _, _, v in live.transcript]
        assert len(public) == CH.schedule_len(d, prog, carried=cr), (len(public), CH.schedule_len(d, prog, cr))
        gen = None
        if carry is None:
            carry = gen = RP.genesis_commit(p, wires)
            parent = {kk: gen[kk].roots for kk in ("W1", "W2")}
            meta["genesis_roots"] = parent
        name = f"he{k}"
        json.dump(witness(p, d, dealer, live, wires), open(os.path.join(out, f"{tag}_{name}.json"), "w"))
        ctx = (model, 0, k)
        spine, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, carry=carry, context=ctx, public=public)
        sym = CH.replay(p, public, d, tab, prog, carried=cr)
        assert sym.tpos == len(public)
        middle, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx)
        blob = PW.encode_step(p, ctx, d, 3, True, spine, public, middle, sym)
        ok, why, res = PW.verify_step(p, blob, ctx, parent, tab, d, program=program)
        if attack:
            print(f"attack {attack}: python verify: {ok} {why} | first violated row: {mst.get('first_violated')}", flush=True)
            open(os.path.join(out, f"{tag}_{name}.bin"), "wb").write(blob)
            meta["bundles"][name] = dict(ctx=list(ctx), witness=f"{tag}_{name}.json", blob=f"{tag}_{name}.bin",
                                         owner_pk=None, carried=cr, attack=attack, python_accepts=ok)
            break
        assert ok, why
        open(os.path.join(out, f"{tag}_{name}.bin"), "wb").write(blob)
        meta["bundles"][name] = dict(ctx=list(ctx), witness=f"{tag}_{name}.json", blob=f"{tag}_{name}.bin",
                                     owner_pk=None, carried=cr)
        print(name, len(blob), len(public), "python verify:", why, flush=True)
        parent, carry, carried = res[0], sst["child"], (W1n, W2n)
        W1 = W2 = None
    json.dump(meta, open(os.path.join(out, f"{tag}_he_meta.json"), "w"), indent=1)

def verify_native(out, tag):
    """Python's verifier on the native bundles (TAG_<name>.native.bin), with a one-byte-flip control each."""
    meta = json.load(open(os.path.join(out, f"{tag}_meta.json")))
    PW.set_profile(meta["profile"] + DOMAIN_SUFFIX)
    p, d = meta["p"], meta["d"]
    tab = MF.tables(p)
    ok_all = True
    for flow, gen in (("pw", "genesis_roots"), ("si", "si_genesis_roots"), ("he", "genesis_roots")):
        parent = meta.get(gen)
        for name in sorted(b for b in meta["bundles"] if b.startswith(flow)):
            path = os.path.join(out, f"{tag}_{name}.native.bin")
            if parent is None or not os.path.exists(path):
                continue
            bd = meta["bundles"][name]
            blob = open(path, "rb").read()
            pk = bytes.fromhex(bd["owner_pk"]) if bd["owner_pk"] else None
            prog = meta.get("program")
            ok, why, res = PW.verify_step(p, blob, tuple(bd["ctx"]), parent, tab, d, owner_pk=pk, program=prog)
            bad = bytearray(blob); bad[len(bad) // 2] ^= 1
            ok2, why2, _ = PW.verify_step(p, bytes(bad), tuple(bd["ctx"]), parent, tab, d, owner_pk=pk, program=prog)
            print(f"python verify {tag} {name} native: {ok} {why} | flipped byte: {ok2} {why2}", flush=True)
            ok_all &= ok and not ok2
            if ok:
                parent = res[0]
    if meta.get("pg_cfg"):
        ok_all &= pg_ledger_check(out, tag, meta, p, tab)
    rm = meta.get("release")
    path = os.path.join(out, f"{tag}_rel.native.bin")
    if rm and os.path.exists(path):
        wit = json.load(open(os.path.join(out, rm["witness"])))
        blob = open(path, "rb").read()
        prog_r = dict(meta.get("program") or {}, **({"RC": True} if rm.get("rc") else {}), **({"LB": True} if rm.get("lb") else {}))
        ok, why, res = PW.verify_release(p, blob, tuple(rm["ctx"]), rm["head_roots"], wit["X"], wit["labels"],
                                         prog_r, rm["ncls"], d)
        bad = bytearray(blob); bad[len(bad) // 2] ^= 1
        ok2, why2, _ = PW.verify_release(p, bytes(bad), tuple(rm["ctx"]), rm["head_roots"], wit["X"], wit["labels"],
                                         prog_r, rm["ncls"], d)
        print(f"python verify {tag} release native: {ok} {why} {res} | flipped byte: {ok2} {why2}", flush=True)
        ok_all &= ok and not ok2 and res[1] == rm["C"]
    print("PYVERIFY", "PASS" if ok_all else "FAIL")
    sys.exit(0 if ok_all else 1)

def pg_ledger_check(out, tag, meta, p, tab):
    """Public genesis through Python's Ledger, on the native bundles: refused before the cfg check, with another cfg,
    and with the roots of another W; accepted with the pinned cfg, then every native bundle in order. Control: the
    same first bundle against a genesis program without "PG" (step 1 then is not the carried program) is refused."""
    import tempfile
    cfg = open(meta["pg_cfg"], "rb").read()
    d = meta["d"]
    names = sorted(b for b in meta["bundles"] if b.startswith("he"))
    blobs = [open(os.path.join(out, f"{tag}_{n}.native.bin"), "rb").read() for n in names]
    tmp = tempfile.mkdtemp(prefix="pg-ledger-")
    gen = lambda roots, prog: dict(d=d, owner_pk=None, custodians=["c0", "c1", "c2"], roots=roots, program=prog)
    lg = PW.Ledger(os.path.join(tmp, "mind-0.ledger"), "mind-0", gen(meta["genesis_roots"], meta["program"]))
    r0 = lg.accept(p, blobs[0], tab)
    r1 = lg.check_public_genesis(cfg + b"\n")
    _, W1, W2 = PW.public_weights(cfg)
    W1b = [r[:] for r in W1]
    W1b[0][0] += 1
    _, forged = PW.public_genesis(p, d, W1b, W2)
    fl = PW.Ledger(os.path.join(tmp, "forged.ledger"), "mind-0", gen(forged, meta["program"]))
    r2 = fl.check_public_genesis(cfg)
    r3 = lg.check_public_genesis(cfg)
    acc = [lg.accept(p, b, tab) for b in blobs]
    nopg = {k: v for k, v in meta["program"].items() if k != "PG"}
    ctl = PW.Ledger(os.path.join(tmp, "nopg.ledger"), "mind-0", gen(meta["genesis_roots"], nopg))
    r4 = ctl.accept(p, blobs[0], tab)
    for nm, r in (("step 1 before the cfg check", r0), ("another cfg", r1), ("roots of another W", r2),
                  ("the pinned cfg", r3)):
        print(f"python ledger {tag} public genesis: {nm}: {r}", flush=True)
    for nm, r in zip(names, acc):
        print(f"python ledger {tag} accepts native {nm}: {r}", flush=True)
    print(f"python ledger {tag} control, the same step 1 under a genesis without PG: {r4}", flush=True)
    return (not r0[0]) and (not r1[0]) and (not r2[0]) and r3[0] and all(r[0] for r in acc) and not r4[0]

def main():
    if sys.argv[1] == "verify":
        return verify_native(sys.argv[2], sys.argv[3])
    assert os.environ.get("DL_DETERMINISTIC") is not None, "set DL_DETERMINISTIC"
    out, d = sys.argv[1], int(sys.argv[2])
    prof = sys.argv[3] if len(sys.argv) > 3 else "ledger"
    flows = sys.argv[4:] or ["pw"]
    PW.set_profile(prof + DOMAIN_SUFFIX)
    os.makedirs(out, exist_ok=True)
    if "he" in flows:
        return he_flow(out, d, prof)
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    rng = random.Random(d)
    M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
    W1, W2 = M(), M()
    x = [rng.randint(-7, 7) % p for _ in range(d)]
    y = [rng.randint(-7, 7) % p for _ in range(d)]
    model = "mind-0"
    dec = lambda X: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) % p for v in r] for r in X]
    tag = f"{prof}_d{d}"
    meta = dict(d=d, profile=prof, seed=os.environ["DL_DETERMINISTIC"], p=p, bundles={})
    def save(name, ctx, b, owner_pk=None):
        open(os.path.join(out, f"{tag}_{name}.bin"), "wb").write(b["blob"])
        meta["bundles"][name] = dict(ctx=list(ctx), witness=f"{tag}_{name}.json", blob=f"{tag}_{name}.bin",
                                     owner_pk=owner_pk.hex() if owner_pk else None)
    if "pw" in flows or "check" in flows:
        s1 = make_bundle(p, tab, d, W1, W2, x, y, (model, 0, 1), dump=os.path.join(out, f"{tag}_pw1.json"))
        save("pw1", (model, 0, 1), s1)
        meta["genesis_roots"] = {k: s1["genesis"][k].roots for k in ("W1", "W2")}
        cw = (s1["wires"]["W1n"], s1["wires"]["W2n"])
        s2 = make_bundle(p, tab, d, dec(s1["wires"]["W1n"]), dec(s1["wires"]["W2n"]), x, y, (model, 0, 2),
                         carry=s1["child"], carry_wires=cw, dump=os.path.join(out, f"{tag}_pw2.json"))
        save("pw2", (model, 0, 2), s2)
        print("pw", len(s1["blob"]), len(s2["blob"]), flush=True)
        if "check" in flows:
            r1 = RP.make_bundle(p, tab, d, W1, W2, x, y, (model, 0, 1))
            assert r1["blob"] == s1["blob"], "this file's flow differs from run_proofwire.make_bundle"
            print("check: identical to run_proofwire.make_bundle", flush=True)
    if "rel" in flows:
        # the release at the head of the pw chain (step 2's child): M public examples, the harness's program
        import cosnark_he as CH
        import cosnark_release as CR
        ncls = min(10, d)
        M = 4 if d <= 4 else 8
        rr = random.Random(1000 + d)
        xs = int(os.environ.get("DP_XSCALE", "1"))        # > 1: a release whose z1 leaves the table's domain
        X = [[rr.randint(0, 100) * xs for _ in range(M)] for _ in range(d)]
        prog = CH.Prog(rc=bool(os.environ.get("DP_RC")), lb=bool(os.environ.get("DP_LB")))
        rprog = dict(RC=True, **({"LB": True} if prog.lb else {})) if prog.rc else None
        head = s2["wires"]
        dec = lambda Mx: [[MF.centered(sum(v[i][0] for i in range(3)) % p, p) for v in r] for r in Mx]
        # half the labels are the plain model's strict argmax (so C > 0), the rest random
        osc = CR.plain_scores(dec(head["W1n"]), dec(head["W2n"]), X, prog, ncls)
        labels = [max(range(ncls), key=lambda c: osc[c][t]) if t % 2 == 0 else rr.randrange(ncls) for t in range(M)]
        flat = lambda Mx: [v for r in Mx for v in r]
        dealer = spdz.Dealer(p, 3, 5)
        live = G.RecEngine(p, 3, dealer)
        C, z1h = CR.run_release(live, head["W1n"], head["W2n"], X, labels, prog, ncls)
        live.mac_check("release")
        public = [v for _, _, v in live.transcript]
        sym = CR.replay(p, public, X, labels, prog, ncls)
        io = CR.io_spec(p, d, M)
        ctx = (model, 0, 2)
        hw = dict(W1=flat(head["W1n"]), W2=flat(head["W2n"]))
        wit = witness(p, d, dealer, live, dict(W1=head["W1n"], W2=head["W2n"]))
        wit.update(ext={k: [sv(v) for v in z1h[k]] for k in ("z1", "h")}, X=X, labels=labels, ncls=ncls, M=M)
        json.dump(wit, open(os.path.join(out, f"{tag}_rel.json"), "w"))
        rel, rst = CR.prove(live, sym, hw, z1h, s2["child"], ctx, io)
        if rel is None:
            print("rel: the custodians refuse to prove:", rst["error"], flush=True)
            import cosnark_gates_zk as GZ2
            live2 = G.RecEngine(p, 3, spdz.Dealer(p, 3, 5))
            CR.run_release(live2, head["W1n"], head["W2n"], X, labels, prog, ncls)
            sym2 = CR.replay(p, [v for _, _, v in live2.transcript], X, labels, prog, ncls)
            forced, _ = GZ2.prove_middle_zk(live2, sym2, dict(W1=hw["W1"], W2=hw["W2"], **{k: z1h[k] for k in ("z1", "h")}),
                                             s2["child"], context=ctx, io=io, ignore_range=True)
            fb = PW.encode_release(p, ctx, d, 3, M, ncls, [v for _, _, v in live2.transcript], forced, sym2, io)
            heads = {k: s2["child"][k].roots for k in ("W1", "W2")}
            print("rel: a forced bundle (the check ignored):", PW.verify_release(p, fb, ctx, heads, X, labels,
                  rprog, ncls, d)[:2], flush=True)
            return
        blob = PW.encode_release(p, ctx, d, 3, M, ncls, public, rel, sym, io)
        open(os.path.join(out, f"{tag}_rel.bin"), "wb").write(blob)
        heads = {k: s2["child"][k].roots for k in ("W1", "W2")}
        ok, why, res = PW.verify_release(p, blob, ctx, heads, X, labels, rprog, ncls, d)
        assert ok, why
        Cp = CR.plain_count(dec(head["W1n"]), dec(head["W2n"]), X, labels, prog, ncls)
        assert C == Cp, (C, Cp)
        meta["release"] = dict(blob=f"{tag}_rel.bin", witness=f"{tag}_rel.json", ctx=list(ctx), M=M, ncls=ncls, C=C,
                               head_roots=heads, rc=prog.rc, lb=prog.lb)
        print("rel", len(blob), "C =", C, "of M =", M, flush=True)
    if "si" in flows:
        rng2 = random.Random(d)
        Mm = lambda: [[rng2.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
        W1s, W2s = Mm(), Mm()
        x1 = [rng2.randint(-7, 7) % p for _ in range(d)]
        y1 = [rng2.randint(-7, 7) % p for _ in range(d)]
        owner = OS.Owner(h=PW.OWNER_H, seed=bytes(range(32)))
        t1 = make_bundle(p, tab, d, W1s, W2s, x1, y1, (model, 0, 1), owner=owner,
                         dump=os.path.join(out, f"{tag}_si1.json"))
        save("si1", (model, 0, 1), t1, owner.pk)
        meta["si_genesis_roots"] = {k: t1["genesis"][k].roots for k in ("W1", "W2")}
        meta["si_xy"] = dict(x=x1, y=y1)
        print("si", len(t1["blob"]), flush=True)
    if "rows" in flows:
        # step-only witnesses for the refusal rows (the native harness proves them itself)
        J = lambda nm: os.path.join(out, f"{tag}_{nm}.json")
        w1 = step_only(p, tab, d, W1, W2, x, y, J("r_pw1"))
        cw1 = (w1["W1n"], w1["W2n"])
        w2 = step_only(p, tab, d, dec(w1["W1n"]), dec(w1["W2n"]), x, y, J("r_pw2"), carry_wires=cw1)
        step_only(p, tab, d, dec(w2["W1n"]), dec(w2["W2n"]), x, y, J("r_pw3"), carry_wires=(w2["W1n"], w2["W2n"]))
        rng3 = random.Random(d)
        Mm = lambda: [[rng3.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
        W1s, W2s = Mm(), Mm()
        bt = lambda: ([rng3.randint(-7, 7) % p for _ in range(d)], [rng3.randint(-7, 7) % p for _ in range(d)])
        x1, y1 = bt()
        x2, y2 = bt()
        s1 = step_only(p, tab, d, W1s, W2s, x1, y1, J("r_si1"))
        cs = (s1["W1n"], s1["W2n"])
        step_only(p, tab, d, dec(s1["W1n"]), dec(s1["W2n"]), x2, y2, J("r_si2"), carry_wires=cs)
        x_bad = list(x1); x_bad[0] = (x_bad[0] + 1) % p
        y_bad = list(y1); y_bad[1] = (y_bad[1] + 3) % p
        step_only(p, tab, d, W1s, W2s, x_bad, y1, J("r_sa"))
        step_only(p, tab, d, W1s, W2s, x1, y_bad, J("r_sb"))
        step_only(p, tab, d, dec(s1["W1n"]), dec(s1["W2n"]), x1, y1, J("r_sr"), carry_wires=cs)
        meta["rows_xy"] = dict(x1=x1, y1=y1, x2=x2, y2=y2, x_bad=x_bad, y_bad=y_bad)
        for nm, kw in (("trunc", dict(cheat_phase="trunc")), ("lookup", dict(cheat_phase="lookup")),
                       ("bad_triple", dict(attack="bad_triple")), ("nonboolean_bit", dict(attack="nonboolean_bit")),
                       ("mask_out_of_range", dict(attack="mask_out_of_range"))):
            step_only(p, tab, d, W1, W2, x, y, J(f"r_g_{nm}"), **kw)
        print("rows witnesses written", flush=True)
    json.dump(meta, open(os.path.join(out, f"{tag}_meta.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
