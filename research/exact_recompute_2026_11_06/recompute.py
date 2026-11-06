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

Before computing anything it checks the weights it will read: the SHA-256 of each shard and of the
index equal the registry's full-mode commitment (`WEIGHTS`), else exit 4. The `spec` pin covers the
source files AND the integers of every public table (exp, gate, rotary up to MAX_TOKENS positions),
computed before the run. Input files must be canonical in full: decimal ids without leading zeros
joined by single commas, nothing else, at most 1 MiB; anything else exits 3. Every non-zero exit is
`noVerdict` to the auditor, and fail-closed alarms on it. (Codex round 3, initiative 8.)

What the report claims, and only that: the output tokens are gptoss-int v0's greedy continuation of
the prompt tokens, for exactly that many tokens. Sampling, the stop policy, the chat template and the
text a user saw are outside it; the auditor's own host runs this program (as it ran cp_verify).
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC_FILES = ["tables.py", "model.py", "layer.py", "weights.py", "forward.py", "recompute.py"]
WEIGHTS = "3218eb92942a115dcc79ef1acd8778702991be0a034acc5ab55eb26be47db61f"   # registry full-mode commitment
# the registry's full-mode commitment WEIGHTS pins these file hashes (registry/manifests/
# openai__gpt-oss-20b.6cee5e81ee83.full.json, core.shards[].file_hash and core.aux_files)
FILES = {
    "model-00000-of-00002.safetensors": "16d0f997dcfc4462089d536bffe51b4bcea2f872f5c430be09ef8ed392312427",
    "model-00001-of-00002.safetensors": "4fbe328ab445455d6f58dc73852b85873bd626986310abd91cd4d2ce3245eaea",
    "model-00002-of-00002.safetensors": "a18106b209e9ab35c3406db4f6f12a927364a058b21e9d1373d682e20674b303",
    "model.safetensors.index.json": "0e085b977c4c9942f85938828e8c989ed7d5cdabf852e4da6a67c116cd502cd1",
}
VOCAB = 201088
MAX_TOKENS = 4096
CAP = 1 << 20
CANON = re.compile(rb"(0|[1-9][0-9]*)(,(0|[1-9][0-9]*))*")


def pins():
    """(spec, params, weights). spec covers the sources and the table integers."""
    import numpy as np
    import tables as T
    h = hashlib.sha256()
    for f in sorted(SPEC_FILES):
        h.update(f.encode() + b"\0" + open(os.path.join(HERE, f), "rb").read() + b"\0")
    C, S = T.rope_tables(MAX_TOKENS)
    for name, arr in (("exp", T.exp_table()), ("glu", T.glu_table()), ("rope_cos", C), ("rope_sin", S)):
        h.update(name.encode() + b"\0" + np.ascontiguousarray(arr, dtype="<i8").tobytes() + b"\0")
    params = hashlib.sha256(open(os.path.join(HERE, "params-v1.json"), "rb").read()).hexdigest()
    return h.hexdigest(), params, WEIGHTS


def weights_ok(root):
    for name, want in FILES.items():
        h = hashlib.sha256()
        with open(os.path.join(root, name), "rb") as f:
            for chunk in iter(lambda: f.read(1 << 24), b""):
                h.update(chunk)
        if h.hexdigest() != want:
            return False
    return True


def read_tokens(path):
    raw = open(path, "rb").read(CAP + 1)
    if len(raw) > CAP or not CANON.fullmatch(raw):
        raise ValueError("not a canonical token list")
    toks = [int(w) for w in raw.split(b",")]
    if any(t >= VOCAB for t in toks):
        raise ValueError("token out of range")
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
    from weights import ROOT, Shards
    s, p, w = pins()
    if not weights_ok(ROOT):
        print("weights: a file differs from the registry commitment", file=sys.stderr)
        return 4
    P = json.load(open(os.path.join(HERE, "params-v1.json")))
    seq = prompt + output[:-1]
    r = F.run(Shards(), seq, P, with_float=False)
    li = r["logits_int"]
    am = [int(np.argmax(li[i])) for i in range(len(prompt) - 1, len(seq))]
    print(f"pins spec={s} params={p} weights={w}")
    print(f"shape prompt={len(prompt)} output={len(output)}")
    print("argmax tokens=" + ",".join(str(a) for a in am))
    print("DONE")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
