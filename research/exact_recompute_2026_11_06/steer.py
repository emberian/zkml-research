"""G5: a steered transcript that a tolerance checker accepts and the exact recompute refuses, on gpt-oss-20b.

A tolerance checker must accept every honest server whose arithmetic differs from its own, so it accepts
a token y at a position when its own logits put y within tau of the maximum (the acceptance set common to
TOPLOC/DiFR-style thresholds, abstracted to logits; neither tool is reimplemented here). tau is set from
measured honest discrepancies (float32 and the integer model, each against the float64 checker; see
`tau`). The adversary decodes with a KV cache and, wherever that set holds a token that is NEITHER the
integer model's argmax NOR the float64 checker's own argmax, takes the best such token: a choice no
honest backend in the comparison would make (codex round 3: choosing the float64 argmax where the two
models disagree is honest disagreement, not steering). The exact checker recomputes gptoss-int v0 over the committed transcript and
accepts a token only if it is the integer argmax.

    python steer.py tau                   -> g5-tau.json (honest discrepancies on the eval passages)
    python steer.py run PROMPT_INDEX N    -> g5-run-<i>.json (honest and steered transcripts, verdicts)
"""
import json
import os
import sys
import time

import numpy as np

import forward as F
import layer as Lr
import model as M
from weights import Shards

HERE = os.path.dirname(os.path.abspath(__file__))
PROMPTS = [
    "<|start|>user<|message|>Which city is the capital of Australia? Answer in one word.<|end|><|start|>assistant<|channel|>final<|message|>",
    "<|start|>user<|message|>Is it safe to mix bleach and ammonia when cleaning? Answer yes or no, then one sentence.<|end|><|start|>assistant<|channel|>final<|message|>",
    "<|start|>user<|message|>What is 17 times 23?<|end|><|start|>assistant<|channel|>final<|message|>",
]


class Engine:
    """gptoss-int v0 and float references, incrementally, with KV caches."""

    def __init__(self, S, P, floats=(np.float64,)):
        self.S, self.P = S, P
        self.L = [Lr.LayerWeights(S, l) for l in range(F.NL)]
        self.ci = [Lr.KVCache() for _ in range(F.NL)]
        self.cf = {dt: [Lr.KVCache() for _ in range(F.NL)] for dt in floats}
        self.kern = M.ExactF64()
        self.pos = 0

    def feed(self, ids, all_rows=False):
        """Feed tokens; return (int logits at 2^-FL, {dtype: float logits}) for the last position
        (every fed position with all_rows)."""
        sel = slice(None) if all_rows else slice(-1, None)
        xi, xf0 = F.embed(self.S, ids)
        xfs = {dt: xf0 for dt in self.cf}
        for l, Wt in enumerate(self.L):
            xi = Lr.layer_int(np, self.kern, Wt, xi, self.P["layers"][l], None, self.ci[l], self.pos)
            for dt in self.cf:
                Lr.FDT = dt
                xfs[dt] = Lr.layer_float(Wt, xfs[dt], None, self.cf[dt][l], self.pos)
            Wt.drop_experts()
        Lr.FDT = np.float64
        self.pos += len(ids)
        a = F.final_norm_int(np, self.S, xi[sel], self.P["fa_final"])
        outs = {}
        for dt in self.cf:
            Lr.FDT = dt
            outs[dt] = F.final_norm_float(self.S, xfs[dt][sel])
        Lr.FDT = np.float64
        li, _ = F.lm_head(np, self.kern, self.S, a, self.P["fa_final"], None)
        lf = {}
        for dt, af in outs.items():
            Lr.FDT = dt
            _, lf[dt] = F.lm_head(np, self.kern, self.S, a, self.P["fa_final"], af)
        Lr.FDT = np.float64
        if all_rows:
            return li, {dt: v.astype(np.float64) for dt, v in lf.items()}
        return li[0], {dt: v[0].astype(np.float64) for dt, v in lf.items()}


def tau():
    """Honest discrepancy, teacher-forced on the eval passages: max |l - l64| per position for float32 and
    for the integer model; and the float64 gap of each honest argmax (what a token-level check must allow)."""
    S = Shards()
    T = F.tok()
    P = json.load(open(os.path.join(HERE, "params-v1.json")))
    rows = []
    for text in json.load(open(os.path.join(HERE, "passages.json")))["eval"]:
        ids = T.encode(text).ids
        E = Engine(S, P, floats=(np.float64, np.float32))
        LI, LF = E.feed(ids, all_rows=True)
        for i in range(len(ids)):
            li, l64, l32 = LI[i], LF[np.float64][i], LF[np.float32][i]
            lin = li / 2.0 ** F.FL
            m = l64.max()
            rows.append({"inf_f32": float(np.abs(l32 - l64).max()), "inf_int": float(np.abs(lin - l64).max()),
                         "gap_f32": float(m - l64[l32.argmax()]), "gap_int": float(m - l64[li.argmax()]),
                         "margin64": float(np.sort(l64)[-1] - np.sort(l64)[-2])})
        print(len(rows), json.dumps({k: round(max(r[k] for r in rows), 4) for k in rows[-1]}), flush=True)
    keys = rows[0].keys()
    out = {"positions": len(rows), "max": {k: max(r[k] for r in rows) for k in keys},
           "p50": {k: float(np.median([r[k] for r in rows])) for k in keys}, "rows": rows}
    json.dump(out, open(os.path.join(HERE, "g5-tau.json"), "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("positions", "max", "p50")}, indent=1))


def run(pi, n, tau_value=None):
    S = Shards()
    T = F.tok()
    P = json.load(open(os.path.join(HERE, "params-v1.json")))
    if tau_value is None:
        m = json.load(open(os.path.join(HERE, "g5-tau.json")))["max"]
        tv = max(m["inf_f32"], m["inf_int"])     # a logit-vector check must accept both honest backends
    else:
        tv = tau_value
    prompt = T.encode(PROMPTS[pi]).ids
    res = {"prompt": PROMPTS[pi], "tau": tv, "n": n}
    for mode in ("honest", "steered"):
        E = Engine(S, P)
        li, lf = E.feed(prompt)
        toks, steps = [], []
        for k in range(n):
            l64 = lf[np.float64]
            hon = int(li.argmax())
            f64 = int(l64.argmax())
            adm = np.nonzero(l64.max() - l64 <= tv)[0]
            alt = [int(y) for y in adm[np.argsort(-l64[adm])] if int(y) not in (hon, f64)]
            y = alt[0] if (mode == "steered" and alt) else hon
            steps.append({"k": k, "chosen": y, "int_argmax": hon, "f64_argmax": f64,
                          "steered": y not in (hon, f64),
                          "admissible": [int(z) for z in adm[np.argsort(-l64[adm])][:5]],
                          "tolerance_accepts": bool(l64.max() - l64[y] <= tv), "exact_accepts": y == hon,
                          "f64_gap_of_chosen": float(l64.max() - l64[y])})
            toks.append(y)
            if y == 200002:
                break
            li, lf = E.feed([y])
        res[mode] = {"tokens": toks, "text": T.decode(toks), "steps": steps,
                     "tolerance_accepts_all": all(s["tolerance_accepts"] for s in steps),
                     "exact_refusals": [s["k"] for s in steps if not s["exact_accepts"]],
                     "steered_positions": [s["k"] for s in steps if s["steered"]]}
        print(mode, repr(res[mode]["text"]), "tolerance:", res[mode]["tolerance_accepts_all"],
              "exact refusals:", res[mode]["exact_refusals"], "steered at:", res[mode]["steered_positions"],
              flush=True)
    json.dump(res, open(os.path.join(HERE, f"g5-run-{pi}.json"), "w"), indent=1)
    return res


if __name__ == "__main__":
    if sys.argv[1] == "tau":
        tau()
    else:
        run(int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]) if len(sys.argv) > 4 else None)
