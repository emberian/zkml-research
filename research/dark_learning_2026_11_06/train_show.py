"""Print a sweep's results (train_sweep.py output): one row per run, sorted by final accuracy.

    python3 -I train_show.py OUT.jsonl [KEYS ...]     # KEYS: cfg fields to show
"""
import json
import sys

rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
keys = sys.argv[2:] or ["hid", "s1a", "s1b", "s2", "s3", "a1", "a2", "ypos", "yneg", "rnd2", "rnd3", "xenc"]
def acc(r):
    return r.get("final_acc_o", r.get("final_acc", -1)) if "error" not in r else -1
for r in sorted(rows, key=acc, reverse=True):
    if "error" in r:
        print("ERROR", {k: r["cfg"].get(k) for k in keys}, r["error"][-200:])
        continue
    c = r["cfg"]
    if r.get("float"):
        curve = " ".join(f"{p['step']}:{p['acc']:.3f}" for p in r["curve"])
        print(f"FLOAT {acc(r):.4f}", {k: c.get(k) for k in keys + ['lrmul']}, curve)
        continue
    curve = " ".join(f"{p['step']}:{p['eval']['acc_o']:.3f}" for p in r["curve"])
    print(f"{acc(r):.4f} z2 {r['final_acc_z2']:.4f} viol {r['violations_train']}/{r['violations_eval']}",
          {k: c.get(k) for k in keys}, curve)
