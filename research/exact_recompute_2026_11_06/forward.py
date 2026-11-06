"""G3: gptoss-int v0, all 24 layers, teacher-forced. The integer model and the float64 reference run in
one pass over a token sequence (they share each decoded expert); the integer model's output is its
logits at every position, which is what an auditor recomputing a committed transcript needs.

    python forward.py fit                 -> params-v1.json (fixed points per layer, from calib)
    python forward.py eval [N]            -> g3-numpy.json  (digests, argmax agreement, margins)
"""
import hashlib
import json
import os
import sys
import time

import numpy as np

import layer as Lr
import model as M
from weights import Shards, bf16_to_int

HERE = os.path.dirname(os.path.abspath(__file__))
NL = 24
FL = 16              # logits fixed point
VOCAB_CHUNK = 16384


def tok():
    from tokenizers import Tokenizer
    return Tokenizer.from_file(os.path.join(os.environ.get("GPTOSS_DIR", "/Users/ember/models/gpt-oss-20b/6cee5e81"), "tokenizer.json"))


def embed(S, ids):
    bits = S.bf16_bits("model.embed_tokens.weight")[np.asarray(ids)]
    m, e = bf16_to_int(bits)
    xi = M.to_scale(np, m, e, Lr.FS)
    return xi, xi.astype(np.float64) / 2.0 ** Lr.FS


def final_norm_int(xp, S, x, fa):
    return Lr.norm_int(xp, x, xp.asarray(Lr.gain_const(S.bf16_bits("model.norm.weight"))), fa)


def final_norm_float(S, x):
    g = (S.bf16_bits("model.norm.weight").astype(np.uint32) << 16).view(np.float32).astype(Lr.FDT)
    return x / np.sqrt((x * x).mean(-1, keepdims=True) + Lr.EPS) * g


def lm_head(xp, kern, S, a_int, fa, a_float=None):
    """Integer logits at 2^-FL for every row of a_int (and float64 logits if a_float is given),
    computed in vocabulary chunks; chunking changes no integer."""
    bits = S.bf16_bits("lm_head.weight")
    outs, fouts = [], []
    for c0 in range(0, bits.shape[0], VOCAB_CHUNK):
        W = M.IntMatrix.from_bf16(np.asarray(bits[c0:c0 + VOCAB_CHUNK]))
        outs.append(np.asarray(M.linear(xp, kern, a_int, fa, W, None, FL)))
        if a_float is not None:
            fouts.append(a_float @ Lr.expert_float(W).T)
    return np.concatenate(outs, axis=1), (np.concatenate(fouts, axis=1) if a_float is not None else None)


def run(S, ids, P, xp=np, kern=None, with_float=True, layers=NL, keep_trace=False):
    kern = kern or M.ExactF64()
    xi, xf = embed(S, ids)
    xi = xp.asarray(xi)
    digests, ftraces, maxima = {}, [], []
    for l in range(layers):
        Wt = Lr.LayerWeights(S, l)
        tr = {}
        xi = Lr.layer_int(xp, kern, Wt, xi, P["layers"][l], tr)
        digests[f"L{l}"] = hashlib.sha256(np.ascontiguousarray(np.asarray(xi), dtype="<i8").tobytes()).hexdigest()
        if with_float:
            ft = {}
            xf = Lr.layer_float(Wt, xf, ft)
            ftraces.append({k: float(np.abs(v).max()) for k, v in ft.items()})
        maxima.append({k: int(np.abs(np.asarray(v)).max()) for k, v in tr.items()})
        del Wt
    a = final_norm_int(xp, S, xi, P["fa_final"])
    af = final_norm_float(S, xf) if with_float else None
    li, lf = lm_head(xp, kern, S, a, P["fa_final"], af)
    digests["logits"] = hashlib.sha256(np.ascontiguousarray(li, dtype="<i8").tobytes()).hexdigest()
    return {"logits_int": li, "logits_float": lf, "digests": digests, "ftraces": ftraces, "int_maxima": maxima,
            "x_float_final": af}


def fit(headroom=1.25):
    """Per-layer power-of-two fixed points from float64 runs over the calib passages: the finest f with
    max|v| * 2^f * headroom <= 32639, maximised over the passages. The float stack alone fixes them."""
    S = Shards()
    T = tok()
    mx = [dict() for _ in range(NL)]
    fin = 0.0
    for text in json.load(open(os.path.join(HERE, "passages.json")))["calib"]:
        ids = T.encode(text).ids
        _, xf = embed(S, ids)
        for l in range(NL):
            Wt = Lr.LayerWeights(S, l)
            ft = {}
            xf = Lr.layer_float(Wt, xf, ft)
            for k in ("a", "q", "k", "v", "m", "x2"):
                mx[l][k] = max(mx[l].get(k, 0.0), float(np.abs(ft[k]).max()))
            del Wt
        fin = max(fin, float(np.abs(final_norm_float(S, xf)).max()))
        print("calib", len(ids), "tokens; residual max", round(mx[NL - 1]["x2"], 1), flush=True)
    f = lambda v: int(np.floor(np.log2(M.ACLAMP_HI / (headroom * v))))
    layers = [{"fa": f(m["a"]), "fqk": min(f(m["q"]), f(m["k"])), "fv": f(m["v"]), "fm": f(m["m"]), "fh": 9} for m in mx]
    rec = {"version": "gptoss-int v0, params-v1", "headroom": headroom, "layers": layers, "fa_final": f(fin),
           "float_maxima": mx, "final_norm_max": fin}
    json.dump(rec, open(os.path.join(HERE, "params-v1.json"), "w"), indent=1)
    return rec


def evaluate(n=None):
    S = Shards()
    T = tok()
    P = json.load(open(os.path.join(HERE, "params-v1.json")))
    texts = json.load(open(os.path.join(HERE, "passages.json")))["eval"][: (int(n) if n else None)]
    out = {"params": "params-v1.json", "passages": []}
    agree = total = 0
    for text in texts:
        ids = T.encode(text).ids
        t0 = time.time()
        r = run(S, ids, P)
        li, lf = r["logits_int"], r["logits_float"]
        ai = li.argmax(1)                      # ties to the lowest id
        af = lf.argmax(1)
        srt = np.sort(lf, axis=1)
        margin = srt[:, -1] - srt[:, -2]
        dis = [int(i) for i in np.nonzero(ai != af)[0]]
        nxt = np.asarray(ids[1:] + [-1])
        rec = {"tokens": len(ids), "seconds": round(time.time() - t0, 1),
               "argmax_agree": int((ai == af).sum()), "positions": len(ids),
               "disagreements": [{"pos": i, "int": int(ai[i]), "float": int(af[i]), "float_margin": float(margin[i])} for i in dis],
               "min_float_margin": float(margin.min()),
               "int_argmax_is_next_token": int((ai[:-1] == nxt[:-1]).sum()),
               "max_abs_logit_err": float(np.abs(li / 2.0 ** FL - lf).max()),
               "digests": r["digests"], "int_maxima_max": {k: max(m[k] for m in r["int_maxima"]) for k in r["int_maxima"][0]},
               "residual_float_max": max(t["x2"] for t in r["ftraces"])}
        out["passages"].append(rec)
        agree += rec["argmax_agree"]; total += rec["positions"]
        print(json.dumps({k: rec[k] for k in ("tokens", "seconds", "argmax_agree", "positions", "min_float_margin", "max_abs_logit_err")}), flush=True)
        if rec["disagreements"]:
            print("  disagree:", rec["disagreements"], flush=True)
    out["argmax_agree"], out["positions"] = agree, total
    json.dump(out, open(os.path.join(HERE, "g3-numpy.json"), "w"), indent=1)
    return out


if __name__ == "__main__":
    {"fit": lambda *a: fit(), "eval": evaluate}[sys.argv[1]](*sys.argv[2:])
