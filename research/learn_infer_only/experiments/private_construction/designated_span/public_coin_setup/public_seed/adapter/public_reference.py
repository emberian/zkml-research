#!/usr/bin/env python3
"""Independent public integer-product/transform replay; no private path access."""
from pathlib import Path
import argparse
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "source/public_setup/source/crypto"))
import crypto as c


def replay(root):
    body = c.read_json(root / "context.json", exact=True)
    ctx = {"body": body, "id": c.digest(body)}
    counts = {"original_ciphertexts": 0, "states": 0, "outputs": 0, "expiries": 0}

    def values(path, kind, row=c.NO_ROW):
        raw = path.read_bytes()
        count = c.D+1 if kind == c.STATE else 2
        c.require(len(raw) == c.HEADER.size+count*c.WIDTH, "reference exact width")
        out = [int.from_bytes(raw[i:i+c.WIDTH], "big")
               for i in range(c.HEADER.size, len(raw), c.WIDTH)]
        c.require(all(1 <= v < c.P for v in out), "reference public range")
        c.require(raw == c.pack(ctx, kind, out, row), "reference full envelope identity")
        return out

    zero = values(root / "zero.ct", c.STATE)
    c.require(zero == [1]*(c.D+1), "zero state")
    queue = []
    selected = {1: 0, 16: 1, 32: 2, 33: 3}
    for t in range(1, 34):
        new = values(root / "ciphertexts" / f"c{t:02d}.ct", c.STATE)
        counts["original_ciphertexts"] += 1
        if len(queue) == c.W:
            queue.pop(0)
            counts["expiries"] += 1
        queue.append(new)
        product = [1]*(c.D+1)
        for original in queue:
            product = [a*b % c.P for a, b in zip(product, original, strict=True)]
        actual = values(root / "states" / f"a{t:02d}.ct", c.STATE)
        c.require(actual == product, "exact original FIFO product")
        counts["states"] += 1
        if t in selected:
            row = selected[t]
            query = c.read_json(root / "queries" / f"q{row:02d}.json", exact=True)
            c.require(query == c.query_obj(ctx, row), "reference registered query")
            expected = 1
            for element, coefficient in zip(product[1:], c.ROWS[row], strict=True):
                expected = expected*pow(element, coefficient, c.P) % c.P
            tau = int(body["recipients"][row]["tau"], 16)
            expected = expected*pow(pow(product[0], tau, c.P), -1, c.P) % c.P
            output = values(root / "outputs" / f"o{row:02d}.ct", c.OUTPUT, row)
            c.require(output == [product[0], expected], "reference designated transform")
            counts["outputs"] += 1
    c.require(counts == {"original_ciphertexts": 33, "states": 33, "outputs": 4, "expiries": 1}, "reference totals")
    return {"ok": True, "context_id": ctx["id"], "counts": counts,
            "no_private_files_read": True, "arithmetic": "CPython public integer products/inverses/powers",
            "scope": "normal exact public envelope/arithmetic replay; native refinement and subgroup security not established"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--root", required=True)
    args = parser.parse_args()
    start = time.perf_counter_ns()
    result = replay(Path(args.root))
    result["elapsed_ns"] = time.perf_counter_ns()-start
    print(json.dumps(result), flush=True)
