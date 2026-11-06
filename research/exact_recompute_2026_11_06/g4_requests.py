"""Build the exact-live request list from G5 runs: per prompt, the honest transcript (the integer
model's greedy continuation), the steered one, and the honest one with its last token edited."""
import json
import os
import sys

import forward as F
import steer

HERE = os.path.dirname(os.path.abspath(__file__))
T = F.tok()
out = []
for path in sys.argv[2:]:
    r = json.load(open(path))
    pi = steer.PROMPTS.index(r["prompt"])
    prompt = T.encode(r["prompt"]).ids
    hon, st = r["honest"]["tokens"], r["steered"]["tokens"]
    out.append({"label": f"p{pi}-honest", "prompt": prompt, "output": hon})
    out.append({"label": f"p{pi}-steered", "prompt": prompt, "output": st})
    out.append({"label": f"p{pi}-edited", "prompt": prompt, "output": hon[:-1] + [(hon[-1] + 1) % F.VOCAB_CHUNK]})
json.dump(out, open(sys.argv[1], "w"))
print(len(out), "requests")
