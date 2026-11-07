"""Test vectors for the native handover prover (native/darkproof/tests/handover_prover_vs_python.rs): under the
TEST-ONLY deterministic hook, the old committee's carried child commitment (labels W1n / W2n, one life spent), the
resharing, the new committee's commitment and handover.prove; writes the shares the native parties commit and the
Python proof bytes the native bytes must equal.

    DL_DETERMINISTIC=7 python3 handover_vectors.py OUTDIR d [profile]

Under a cut E profile (demo-x2de, ledger-x2de) the old commitment is the pending head's W (one life, labels W1n /
W2n, unopened), and the head's pending claims are given too: points r_k (random, flat F_{p^EXT}) and the old
committee's carries c1p, c2p (labels c1 / c2, two lives, the first spent), committed to each old custodian's share
of W(r_k). The vector then also holds the new committee's carry shares (cN = new W(r)) that the proof commits.
"""
import cosnark as CS
import cosnark_ext as X
import json
import os
import random
import sys
import time

import cosnark_zk as ZK
import handover as HO
import proofwire as PW


def main():
    out, d = sys.argv[1], int(sys.argv[2])
    prof = sys.argv[3] if len(sys.argv) > 3 else "ledger"
    assert os.environ.get("DL_DETERMINISTIC") is not None, "vectors need the deterministic hook"
    PW.set_profile(prof)
    p = PW.he_field()                        # the profile's field (the deployed HE plaintext modulus)
    rng = random.Random(1000 + d)
    old = {k: [[rng.randrange(p) for _ in range(d * d)] for _ in range(3)] for k in HO.KINDS}
    deferred = dfr_json = None
    if ZK.DEFER:
        old_coms = {k: ZK.w_pcs(p, old[k], k + "n") for k in HO.KINDS}
        ld = d.bit_length() - 1
        pts = {k: [tuple(rng.randrange(p) for _ in range(X.EXT)) for _ in range(2 * ld)] for k in HO.KINDS}
        carries, cshares = {}, {}
        for q, k in enumerate(HO.KINDS):
            c = old_coms[k]
            a, b = c.eval_weights_e(pts[k]), X.eqv(pts[k][:c.mc], p)
            ys = [X.dot([tuple(u[kk][cc] for kk in range(X.EXT)) for cc in range(c.C)], b, p)
                  for u in (c.row_combo_e(i, a) for i in range(3))]
            cs = [list(X.pad(y)) + [0] * ((1 << ZK.carry_m()) - X.EXT) for y in ys]
            cn = ZK.CARRY[q]
            cc = ZK.ZKPCS(p, cs, cn, hide=CS.LIVES * CS.T_COLS, nmask=CS.LIVES * X.EXT, lives=CS.LIVES)
            cc.opened_lives = 1                # its first life: the step that defined it
            carries[ZK.CARRY_IN[q]], cshares[ZK.CARRY_IN[q]] = cc, cs
        deferred = dict(points=pts, carries=carries)
        dfr_json = dict(points={k: X.flat(v) for k, v in pts.items()}, carry_labels={"c1p": "c1", "c2p": "c2"},
                        carry_shares=cshares, carry_lives_spent=1)
    else:
        old_coms = {k: ZK.ZKPCS(p, old[k], k + "n") for k in HO.KINDS}
        for c in old_coms.values():
            c.opened_lives = 1                 # the child's first life: its step's opening
    rs = random.Random(1234)
    new = {k: HO.reshare(old[k], 3, p, rs)[1] for k in HO.KINDS}
    new_coms = {k: (ZK.w_pcs if ZK.DEFER else ZK.ZKPCS)(p, new[k], k) for k in HO.KINDS}
    model, old_set, new_set = "mind-h", ["c0", "c1", "c2"], ["c3", "c4", "c5"]
    ctx = HO.context_digest(model, 0, 1, 1, old_set, new_set)
    t = time.time()
    proof, st = HO.prove(p, d, old_coms, new_coms, ctx, deferred=deferred)
    secs = time.time() - t
    blob = HO.encode(p, d, proof)
    ldfr = PW.deferred_of(dict(points=dfr_json["points"], carry_roots={c: deferred["carries"][c].roots for c in ZK.CARRY_IN})) if deferred else None
    out_p = {}
    ok, why, _ = HO.verify_bytes(p, d, 3, 3, ctx, proof["old_roots"], blob, deferred=ldfr, out=out_p)
    assert ok, why
    if deferred:
        dfr_json["new_carry_shares"] = {c: [list(r[0][:1 << ZK.carry_m()]) for r in st["deferred"]["carries"][c].ext] for c in ZK.CARRY_IN}
        dfr_json["new_pending"] = PW.pending_json(out_p)
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, f"handover_d{d}_{prof}.bin"), "wb").write(blob)
    json.dump(dict(p=p, d=d, profile=prof, domain=PW.PARAMS["DOMAIN"], model=model, epoch_old=0, epoch_new=1, after_step=1, old_set=old_set,
                   new_set=new_set, old_labels={k: k + "n" for k in HO.KINDS}, old_lives_spent=0 if ZK.DEFER else 1,
                   old=old, new=new, bytes=f"handover_d{d}_{prof}.bin", python_prove_seconds=round(secs, 2),
                   first_violated=st["first_violated"], deferred=dfr_json),
              open(os.path.join(out, f"handover_d{d}_{prof}.json"), "w"))
    print(f"d = {d} {prof}: {len(blob)} bytes, Python prove {secs:.2f} s, verify {why}")


if __name__ == "__main__":
    main()
