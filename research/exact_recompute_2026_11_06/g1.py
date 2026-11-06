"""G1: layer 0 of gptoss-int v0 on a real prompt. Writes the integer trace digests (g1-<backend>.json)
and, for the reference backend, the fitted exponents (params-v0.json) and fidelity against float64."""
import hashlib
import json
import os
import sys
import time

import numpy as np

import layer as Lr
import model as M
from weights import Shards, bf16_to_int

PROMPT = "The capital of France is Paris. The capital of Japan is"
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.environ.get("G1_OUT", HERE)          # where results go; params are always read from HERE


def tokens():
    if os.environ.get("GPTOSS_IDS_FROM_PARAMS") == "1":     # remote jobs: ids pinned in params-v0.json
        return json.load(open(os.path.join(HERE, "params-v0.json")))["ids"]
    from tokenizers import Tokenizer
    tok = Tokenizer.from_file(os.path.join(os.environ.get("GPTOSS_DIR", "/Users/ember/models/gpt-oss-20b/6cee5e81"), "tokenizer.json"))
    return tok.encode(PROMPT).ids


def embed_int(xp, S, ids):
    bits = S.bf16_bits("model.embed_tokens.weight")[np.asarray(ids)]
    m, e = bf16_to_int(bits)
    return M.to_scale(xp, xp.asarray(m), xp.asarray(e), Lr.FS)


def digests(tr):
    return {k: hashlib.sha256(np.ascontiguousarray(np.asarray(v), dtype="<i8").tobytes()).hexdigest() for k, v in tr.items()}


def main(backend="numpy"):
    S = Shards()
    ids = tokens()
    Wt = Lr.LayerWeights(S, 0)
    if backend == "numpy-f32":
        xp, kern = np, M.InexactF32()
        P = json.load(open(os.path.join(HERE, "params-v0.json")))["P"]
        x0 = embed_int(np, S, ids)
    elif backend == "numpy":
        xp, kern = np, M.ExactF64()
        x0 = embed_int(np, S, ids)
        ftr = {}
        Lr.layer_float(Wt, x0.astype(np.float64) / 2.0 ** Lr.FS, ftr)
        P = Lr.fit_exponents(ftr)
        json.dump({"ids": ids, "P": P}, open(os.path.join(OUT, "params-v0.json"), "w"))
    else:
        import jax
        jax.config.update("jax_enable_x64", True)
        import jax.numpy as jnp
        import jaxint
        xp, kern = jnp, (jaxint.F32Dot() if backend == "jax-f32" else jaxint.Int8Mxu())
        cfg = json.load(open(os.path.join(HERE, "params-v0.json")))
        assert cfg["ids"] == ids
        P = cfg["P"]
        x0 = embed_int(jnp, S, ids)
    t0 = time.time()
    tr = {}
    Lr.layer_int(xp, kern, Wt, x0, P, tr)
    secs = time.time() - t0
    rec = {"backend": kern.name, "ids": ids, "P": P, "digests": digests(tr), "seconds": round(secs, 2)}
    if backend == "numpy":
        def rel(k, f):
            a = np.asarray(tr[k], dtype=np.float64) / 2.0 ** f
            b = ftr[k] if k not in ("q", "k") else None
            return None if b is None else float(np.abs(a - b).max() / np.abs(b).max())
        rec["fidelity_max_rel_err"] = {"a": rel("a", P["fa"]), "x1": rel("x1", Lr.FS), "m": rel("m", P["fm"]), "x2": rel("x2", Lr.FS)}
        np.savez_compressed(os.path.join(OUT, "g1-numpy-trace.npz"), **{k: np.asarray(v) for k, v in tr.items()})
    json.dump(rec, open(os.path.join(OUT, f"g1-{backend}.json"), "w"), indent=1)
    print(json.dumps(rec, indent=1))


if __name__ == "__main__":
    main(*sys.argv[1:])
