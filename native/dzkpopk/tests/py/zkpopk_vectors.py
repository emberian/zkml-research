"""Bit-exact vectors for native/dzkpopk against the harness (zkpopk_ligero.py, keygen_ceremony.py).

    DL_DETERMINISTIC=<seed> python3 zkpopk_vectors.py gen N L M T OUTDIR       # prove sk, pk, key; write py_<kind>.bin
    python3 zkpopk_vectors.py verify N L M T KIND PROOF                         # verify a proof (native's) -> ACCEPT/REFUSED
    DL_DETERMINISTIC=<seed> python3 zkpopk_vectors.py ceremony N L T            # the 3-custodian ceremony, digests

The instances are the harness's own: run_zkpopk_ligero.sk_batch with random.Random(N * 1000 + M), then a joint key
and max(1, M - 1) public-key ciphertexts from the same rng, and a key statement for the sk registry. The native
CLI (`dzkpopk vectors`) builds the same instances draw for draw; the statement digests printed by both must match.
"""
import hashlib
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.normpath(os.path.join(HERE, "../../../../research/dark_learning_2026_11_06"))
sys.path.insert(0, HARNESS)

import bfv_ref as bfv  # noqa: E402
import zkpopk_ligero as Z  # noqa: E402
from run_zkpopk_ligero import sk_batch  # noqa: E402

CTX = ("mind-0", 0, 7, "matvec-fwd-0", "custodian-1", ("custodian-0", "custodian-2"))
KEY_CTX = ["dl-keygen-key", 1, 1, "vectors"]


def instances(N, L, M):
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    Qp, t = pr[:L], pr[L]
    rng = random.Random(N * 1000 + M)
    reg, wit, cts, slots = sk_batch(N, Qp, t, M, rng)
    st_sk = Z.Statement(reg, "sk", cts, slots, CTX)
    regj, _, _ = Z.keygen(N, Qp, t, "joint-seed-0", "joint", rng)
    pcts, pws, psl = [], [], []
    for _ in range(max(1, M - 1)):
        Sx = list(range(min(N, 8)))
        m = [0] * N
        for kk in Sx:
            m[kk] = rng.randrange(t)
        ct, w = Z.encrypt_pk(regj, m, Sx, rng)
        pcts.append(ct); pws.append(w); psl.append(Sx)
    st_pk = Z.Statement(regj, "pk", pcts, psl, CTX)
    st_key = Z.Statement(reg, "key", [], [], KEY_CTX)
    return {"sk": (st_sk, wit), "pk": (st_pk, dict(cts=pws)), "key": (st_key, dict(s=wit["s"], e_pk=wit["e_pk"]))}


def main():
    mode = sys.argv[1]
    if mode == "gen":
        N, L, M, T = (int(x) for x in sys.argv[2:6])
        out = sys.argv[6]
        kinds = sys.argv[7].split(",") if len(sys.argv) > 7 else ["sk", "pk", "key"]
        res = {}
        for kind, (st, wit) in instances(N, L, M).items():
            if kind not in kinds:
                continue
            t0 = time.time()
            blob = Z.prove(st, wit, T=T)
            tp = time.time() - t0
            sh = Z.shape(st, T)
            open(os.path.join(out, f"py_{kind}.bin"), "wb").write(blob)
            res[kind] = dict(digest=st.digest().hex(), sha256=hashlib.sha256(blob).hexdigest(), bytes=len(blob),
                             formula=Z.proof_bytes(sh["k"], sh["th"], T, sh["m1"], sh["m2"]), prove_s=round(tp, 2))
        print(json.dumps(res, indent=1))
    elif mode == "verify":
        N, L, M, T = (int(x) for x in sys.argv[2:6])
        kind, path = sys.argv[6], sys.argv[7]
        st, _ = instances(N, L, M)[kind]
        t0 = time.time()
        ok, why = Z.verify(st, open(path, "rb").read(), T=T)
        print(json.dumps(dict(kind=kind, ok=ok, why=why, verify_s=round(time.time() - t0, 2))))
    elif mode == "ceremony":
        import keygen_ceremony as K
        N, L, T = (int(x) for x in sys.argv[2:5])
        pr = bfv.ntt_primes(61, L + 1, 2 * N)
        cer, cs = K.run_ceremony(1, 3, N, pr[:L], pr[L], T)
        print(json.dumps(dict(seed=cer.seed, transcript=cer.transcript(),
                              commits=[cer.commits[i] for i in range(3)],
                              proofs=[cer.keys[i]["proof_digest"] for i in range(3)],
                              b_digest=[hashlib.sha256(Z.canonical(list(cer.keys[i]["registry"].b))).hexdigest() for i in range(3)]),
                         indent=1))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
