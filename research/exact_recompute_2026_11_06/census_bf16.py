"""Per-row exponent spread of gpt-oss-20b's BF16 matrices: can each row enter as an exact integer
row with one shared exponent, inside an int32 (or int16) significand window?"""
import json
import sys

import numpy as np

from weights import Shards, bf16_to_int

S = Shards()
names = [n for n in S.where if any(k in n for k in ("self_attn.q_proj.weight", "self_attn.k_proj.weight",
         "self_attn.v_proj.weight", "self_attn.o_proj.weight", "mlp.router.weight"))]
names = sorted(names)[:: max(1, len(names) // 20)] + ["model.embed_tokens.weight", "lm_head.weight"]
res = {}
for n in names:
    m, e = bf16_to_int(S.bf16_bits(n))
    nz = m != 0
    big = np.where(nz, e, -10**6).max(axis=1)
    small = np.where(nz, e, 10**6).min(axis=1)
    has = nz.any(axis=1)
    spread = (big - small)[has]
    width = spread + 8  # bits of the aligned significand, sign apart
    res[n] = {"rows": int(has.sum()), "p50": float(np.percentile(width, 50)), "p99": float(np.percentile(width, 99)),
              "max": int(width.max()), "rows_le_31": float((width <= 31).mean()), "rows_le_15": float((width <= 15).mean())}
    print(n, res[n], flush=True)
json.dump(res, open("census_bf16.json", "w"), indent=1)
