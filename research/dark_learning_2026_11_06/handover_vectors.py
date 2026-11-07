"""Test vectors for the native handover prover (native/darkproof/tests/handover_prover_vs_python.rs): under the
TEST-ONLY deterministic hook, the old committee's carried child commitment (labels W1n / W2n, one life spent), the
resharing, the new committee's commitment and handover.prove; writes the shares the native parties commit and the
Python proof bytes the native bytes must equal.

    DL_DETERMINISTIC=7 python3 handover_vectors.py OUTDIR d [profile]
"""
import json
import os
import random
import sys
import time

import bfv_ref as bfv
import cosnark_zk as ZK
import handover as HO
import proofwire as PW


def main():
    out, d = sys.argv[1], int(sys.argv[2])
    prof = sys.argv[3] if len(sys.argv) > 3 else "ledger"
    assert os.environ.get("DL_DETERMINISTIC") is not None, "vectors need the deterministic hook"
    PW.set_profile(prof)
    p = bfv.ntt_primes(61, 4, 16384)[3]
    rng = random.Random(1000 + d)
    old = {k: [[rng.randrange(p) for _ in range(d * d)] for _ in range(3)] for k in HO.KINDS}
    old_coms = {k: ZK.ZKPCS(p, old[k], k + "n") for k in HO.KINDS}
    for c in old_coms.values():
        c.opened_lives = 1                     # the child's first life: its step's opening
    rs = random.Random(1234)
    new = {k: HO.reshare(old[k], 3, p, rs)[1] for k in HO.KINDS}
    new_coms = {k: ZK.ZKPCS(p, new[k], k) for k in HO.KINDS}
    model, old_set, new_set = "mind-h", ["c0", "c1", "c2"], ["c3", "c4", "c5"]
    ctx = HO.context_digest(model, 0, 1, 1, old_set, new_set)
    t = time.time()
    proof, st = HO.prove(p, d, old_coms, new_coms, ctx)
    secs = time.time() - t
    blob = HO.encode(p, d, proof)
    ok, why, _ = HO.verify_bytes(p, d, 3, 3, ctx, proof["old_roots"], blob)
    assert ok, why
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, f"handover_d{d}_{prof}.bin"), "wb").write(blob)
    json.dump(dict(d=d, profile=prof, model=model, epoch_old=0, epoch_new=1, after_step=1, old_set=old_set,
                   new_set=new_set, old_labels={k: k + "n" for k in HO.KINDS}, old_lives_spent=1,
                   old=old, new=new, bytes=f"handover_d{d}_{prof}.bin", python_prove_seconds=round(secs, 2),
                   first_violated=st["first_violated"]),
              open(os.path.join(out, f"handover_d{d}_{prof}.json"), "w"))
    print(f"d = {d} {prof}: {len(blob)} bytes, Python prove {secs:.2f} s, verify {why}")


if __name__ == "__main__":
    main()
