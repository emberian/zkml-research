"""The checker an exact-recompute auditor calls: gptoss-int v0 over a committed transcript.

    python recompute.py PROMPT_FILE OUTPUT_FILE      (each: decimal token ids, comma-separated)
    python recompute.py pins                         (the three pins an auditor sets up with)

It recomputes the integer model teacher-forced over prompt + output (one prefill, no sampling) and
reports the integer argmax at every position that predicts an output token (ties to the lowest
id). It decides nothing: the auditor's compiled Lean (`Selvage/AuditExactDecide.lean`) compares
the report with the committed output. Output, exit 0:

    pins spec=<sha256 of the spec sources> params=<sha256 of params-v1.json> weights=<registry commitment>
    shape prompt=<n> output=<m>
    argmax tokens=<a1>,...,<am>
    DONE

Any input it cannot read as tokens exits 3; anything else that goes wrong exits non-zero. Both are
`noVerdict` to the auditor, and fail-closed alarms on them.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC_FILES = ["tables.py", "model.py", "layer.py", "weights.py", "forward.py", "recompute.py"]
WEIGHTS = "3218eb92942a115dcc79ef1acd8778702991be0a034acc5ab55eb26be47db61f"   # registry full-mode commitment
VOCAB = 201088
MAX_TOKENS = 4096


def pins():
    h = hashlib.sha256()
    for f in sorted(SPEC_FILES):
        h.update(f.encode() + b"\0" + open(os.path.join(HERE, f), "rb").read() + b"\0")
    params = hashlib.sha256(open(os.path.join(HERE, "params-v1.json"), "rb").read()).hexdigest()
    return h.hexdigest(), params, WEIGHTS


def read_tokens(path):
    raw = open(path, "rb").read(1 << 20)
    s = raw.decode("ascii").strip()
    toks = [int(w) for w in s.split(",")]
    if any(t < 0 or t >= VOCAB or str(t) != w for t, w in zip(toks, s.split(","))):
        raise ValueError("token out of range or not canonical")
    return toks


def main(argv):
    if argv[:1] == ["pins"]:
        s, p, w = pins()
        print(json.dumps({"spec": s, "params": p, "weights": w}))
        return 0
    try:
        prompt, output = read_tokens(argv[0]), read_tokens(argv[1])
        if not prompt or not output or len(prompt) + len(output) > MAX_TOKENS:
            raise ValueError("empty or too long")
    except Exception as e:
        print(f"input: {e}", file=sys.stderr)
        return 3
    import numpy as np
    import forward as F
    from weights import Shards
    P = json.load(open(os.path.join(HERE, "params-v1.json")))
    seq = prompt + output[:-1]
    r = F.run(Shards(), seq, P, with_float=False)
    li = r["logits_int"]
    am = [int(np.argmax(li[i])) for i in range(len(prompt) - 1, len(seq))]
    s, p, w = pins()
    print(f"pins spec={s} params={p} weights={w}")
    print(f"shape prompt={len(prompt)} output={len(output)}")
    print("argmax tokens=" + ",".join(str(a) for a in am))
    print("DONE")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
